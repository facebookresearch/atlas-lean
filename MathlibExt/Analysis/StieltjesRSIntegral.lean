/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannPartition
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Riemann–Stieltjes integral

For an integrand `f` and an integrator `h` on `[a, b]` (in the intended application `[0, τ]`
with `h` regulated, e.g. càdlàg), the Riemann–Stieltjes sum over a tagged partition
`a = x₀ < ⋯ < xₙ = b` with tags `ξₖ ∈ [xₖ, xₖ₊₁]` is `∑ₖ f(ξₖ) (h(xₖ₊₁) - h(xₖ))`, and
`∫ₐᵇ f dh = I` means: for every `ε > 0` there is a partition `P_ε` such that every tagged partition
refining `P_ε` has sum within `ε` of `I` (the refinement, or Moore–Pollard, definition). This file
defines the sums and the integral, proves uniqueness, linearity in the integrand and in the
integrator, the standard bounds, a Cauchy criterion, and existence for continuous integrands
against monotone or bounded-variation integrators.

The bound `abs_rsSum_le_of_abs_le` / `HasRSIntegral.abs_le_of_abs_le` uses only `|h| ≤ B`, not any
regularity of `h`: for a bounded-variation integrand `f`, summation by parts gives
`|∫ f dh| ≤ ‖h‖_∞ (2‖f‖_∞ + V(f))`. This is the estimate that makes `h ↦ ∫ f dh` Lipschitz for the
uniform norm (`HasRSIntegral.abs_sub_le_of_abs_sub_le`), the input needed to extend the Duhamel
operator of `ContinuousProductIntegral.lean` from bounded-variation to regulated integrators.

Partitions, tagged partitions and point-set refinement are the canonical ones of
`MathlibExt.Analysis.Integration.RiemannPartition`; against `h = id` the sum is `riemannSum`
(`rsSum_id`). The common refinement used here (`Partition.common`) is a point-set refinement of
both partitions; `TaggedPartition.exists_commonRefinement` only provides tagged-refinement data,
whose telescoping is stated for lengths and not for increments of a general integrator.
Mathlib has no one-dimensional Riemann–Stieltjes integral (its Stieltjes integrals are
Lebesgue integrals against `StieltjesFunction.measure`, which need a right-continuous monotone
integrator) and no notion of regulated function.

## Main definitions

* `rsSum f h T`: the Riemann–Stieltjes sum.
* `HasRSIntegral f h a b I`, `RSIntegrable f h a b`, `rsIntegral f h a b`: the integral in the
  refinement sense (`rsIntegral` is `0` when the integral does not exist).
* `Partition.leftTag`, `Partition.rightTag`, `Partition.ofFinset`, `Partition.common`,
  `Partition.uniform`: partition constructions; `Partition.pointN`, `TaggedPartition.tagN`:
  `ℕ`-indexed points and tags.

## Main results

* `HasRSIntegral.unique`, `HasRSIntegral.rsIntegral_eq`: uniqueness.
* `HasRSIntegral.add_left`, `smul_left`, `sub_left`, `add_right`, `smul_right`, `sub_right`
  and `rsIntegral_add_left`, …: linearity in the integrand and in the integrator.
* `hasRSIntegral_const`: `∫ₐᵇ c dh = c (h b - h a)`.
* `HasRSIntegral.abs_le_mul_variation`: `|∫ f dh| ≤ M · V(h)` for `|f| ≤ M`.
* `HasRSIntegral.abs_le_of_monotoneOn`: `|∫ f dh| ≤ M (h b - h a)` for monotone `h`.
* `HasRSIntegral.abs_le_of_abs_le`: `|∫ f dh| ≤ B (2M + V(f))` for `|h| ≤ B`, `|f| ≤ M`.
* `HasRSIntegral.abs_sub_le_of_abs_sub_le`: Lipschitz dependence on the integrator.
* `abs_rsSum_sub_le_of_isRefinement`: refinement estimate for a monotone integrator.
* `rsIntegrable_of_cauchy`: Cauchy criterion.
* `rsIntegrable_of_continuousOn_of_monotoneOn`,
  `rsIntegrable_of_continuousOn_of_boundedVariationOn`: existence.

## Not covered

* Integration by parts `∫ f dh + ∫ h df = f(b)h(b) - f(a)h(a)`, and existence of `∫ f dh` for a
  bounded-variation integrand against a regulated integrator without common discontinuities.
* Additivity over adjacent intervals.
* The Duhamel operator `Ψ` and its continuity (the Ψ-CLM bridge), deferred until the product
  integral tasks T77/T78 merge.

Source: T. M. Apostol, *Mathematical Analysis*, 2nd ed. (1974), Chapter 7: Definition 7.1 (the
Riemann–Stieltjes integral, refinement form), Theorems 7.2 and 7.3 (linearity in the integrand and
in the integrator), and Theorem 7.27 (existence for `f` continuous and `α` of bounded variation).
The uniform-norm bound is Abel summation applied to the Riemann–Stieltjes sums, the
"integration-by-parts bound" referred to in `ContinuousProductIntegral.lean` (Gill–Johansen 1990;
van der Vaart, *Asymptotic Statistics* (1998), §20.3).
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration

open Finset Set

variable {a b : ℝ}

/-- The **Riemann–Stieltjes sum** `∑ₖ f(ξₖ) (h(xₖ₊₁) - h(xₖ))` of an integrand `f` against an
integrator `h`, with respect to a tagged partition `T` of `[a, b]`. -/
noncomputable def rsSum (f h : ℝ → ℝ) (T : TaggedPartition a b) : ℝ :=
  ∑ i : Fin T.n, f (T.tags i) * (h (T.points i.succ) - h (T.points i.castSucc))

/-- Against the identity integrator, the Riemann–Stieltjes sum is the Riemann sum. -/
theorem rsSum_id (f : ℝ → ℝ) (T : TaggedPartition a b) : rsSum f id T = riemannSum f T := rfl

theorem rsSum_add_left (f g h : ℝ → ℝ) (T : TaggedPartition a b) :
    rsSum (f + g) h T = rsSum f h T + rsSum g h T := by
  simp only [rsSum, Pi.add_apply, add_mul, sum_add_distrib]

theorem rsSum_smul_left (c : ℝ) (f h : ℝ → ℝ) (T : TaggedPartition a b) :
    rsSum (c • f) h T = c * rsSum f h T := by
  simp only [rsSum, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

theorem rsSum_add_right (f g h : ℝ → ℝ) (T : TaggedPartition a b) :
    rsSum f (g + h) T = rsSum f g T + rsSum f h T := by
  simp only [rsSum, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

theorem rsSum_smul_right (c : ℝ) (f h : ℝ → ℝ) (T : TaggedPartition a b) :
    rsSum f (c • h) T = c * rsSum f h T := by
  simp only [rsSum, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-! ### `ℕ`-indexed form of a tagged partition -/

/-- The points of a partition extended to `ℕ`, constant equal to `b` past the last index. -/
noncomputable def Partition.pointN (P : Partition a b) (i : ℕ) : ℝ :=
  if hi : i ≤ P.n then P.points ⟨i, Nat.lt_succ_of_le hi⟩ else b

/-- The tags of a tagged partition extended to `ℕ`, constant equal to `b` past the last index. -/
noncomputable def TaggedPartition.tagN (T : TaggedPartition a b) (i : ℕ) : ℝ :=
  if hi : i < T.n then T.tags ⟨i, hi⟩ else b

theorem Partition.pointN_zero (P : Partition a b) : P.pointN 0 = a := by
  simp only [Partition.pointN, Nat.zero_le, dite_true]
  exact P.first

theorem Partition.pointN_of_le (P : Partition a b) {i : ℕ} (hi : P.n ≤ i) : P.pointN i = b := by
  unfold Partition.pointN
  split_ifs with h
  · have : i = P.n := le_antisymm h hi
    subst this
    exact P.last
  · rfl

theorem Partition.pointN_fin (P : Partition a b) (i : Fin (P.n + 1)) :
    P.pointN i = P.points i := by
  simp [Partition.pointN, Nat.le_of_lt_succ i.isLt]

theorem TaggedPartition.tagN_fin (T : TaggedPartition a b) (i : Fin T.n) :
    T.tagN i = T.tags i := by
  simp [TaggedPartition.tagN, i.isLt]

theorem Partition.monotone_pointN (P : Partition a b) : Monotone P.pointN := by
  intro i j hij
  unfold Partition.pointN
  split_ifs with hi hj hj
  · exact P.ordered.monotone (Fin.mk_le_mk.mpr hij)
  · have := P.ordered.monotone (Fin.le_last ⟨i, Nat.lt_succ_of_le hi⟩)
    rwa [P.last] at this
  · omega
  · rfl

theorem Partition.pointN_mem_Icc (P : Partition a b) (i : ℕ) : P.pointN i ∈ Icc a b := by
  refine ⟨?_, ?_⟩
  · calc a = P.pointN 0 := P.pointN_zero.symm
      _ ≤ P.pointN i := P.monotone_pointN (Nat.zero_le i)
  · calc P.pointN i ≤ P.pointN (max i P.n) := P.monotone_pointN (le_max_left _ _)
      _ = b := P.pointN_of_le (le_max_right _ _)

theorem TaggedPartition.tagN_mem (T : TaggedPartition a b) {i : ℕ} (hi : i < T.n) :
    T.pointN i ≤ T.tagN i ∧ T.tagN i ≤ T.pointN (i + 1) := by
  have h := T.tag_mem ⟨i, hi⟩
  have h1 := T.toPartition.pointN_fin (⟨i, hi⟩ : Fin T.n).castSucc
  have h2 := T.toPartition.pointN_fin (⟨i, hi⟩ : Fin T.n).succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
  rw [h1, h2, T.tagN_fin ⟨i, hi⟩]
  exact h

theorem TaggedPartition.monotone_tagN (T : TaggedPartition a b) : Monotone T.tagN := by
  refine monotone_nat_of_le_succ fun i => ?_
  rcases lt_or_ge (i + 1) T.n with h | h
  · calc T.tagN i ≤ T.pointN (i + 1) := (T.tagN_mem (by omega)).2
      _ ≤ T.tagN (i + 1) := (T.tagN_mem h).1
  · have hb : T.tagN (i + 1) = b := by simp [TaggedPartition.tagN, not_lt.mpr h]
    rw [hb]
    rcases lt_or_ge i T.n with h' | h'
    · calc T.tagN i ≤ T.pointN (i + 1) := (T.tagN_mem h').2
        _ ≤ b := (T.toPartition.pointN_mem_Icc _).2
    · simp [TaggedPartition.tagN, not_lt.mpr h']

theorem TaggedPartition.tagN_mem_Icc (T : TaggedPartition a b) (i : ℕ) : T.tagN i ∈ Icc a b := by
  rcases lt_or_ge i T.n with h | h
  · exact ⟨(T.toPartition.pointN_mem_Icc i).1.trans (T.tagN_mem h).1,
      (T.tagN_mem h).2.trans (T.toPartition.pointN_mem_Icc _).2⟩
  · simp only [TaggedPartition.tagN, not_lt.mpr h, dite_false]
    exact ⟨T.a_le_b, le_rfl⟩

/-- The Riemann–Stieltjes sum as a sum over `Finset.range T.n` of the `ℕ`-indexed points and
tags. -/
theorem rsSum_eq_sum_range (f h : ℝ → ℝ) (T : TaggedPartition a b) :
    rsSum f h T = ∑ i ∈ range T.n,
      f (T.tagN i) * (h (T.pointN (i + 1)) - h (T.pointN i)) := by
  rw [rsSum, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  have h1 := T.toPartition.pointN_fin i.castSucc
  have h2 := T.toPartition.pointN_fin i.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
  rw [T.tagN_fin, h1, h2]

/-- The increments of any function along a partition telescope to `h b - h a`. -/
theorem Partition.sum_range_sub_pointN (P : Partition a b) (h : ℝ → ℝ) :
    ∑ i ∈ range P.n, (h (P.pointN (i + 1)) - h (P.pointN i)) = h b - h a := by
  rw [sum_range_sub (fun i => h (P.pointN i)), P.pointN_of_le le_rfl, P.pointN_zero]

/-- The Riemann–Stieltjes sum of a constant integrand. -/
theorem rsSum_const (c : ℝ) (h : ℝ → ℝ) (T : TaggedPartition a b) :
    rsSum (fun _ => c) h T = c * (h b - h a) := by
  rw [rsSum_eq_sum_range, ← mul_sum, T.toPartition.sum_range_sub_pointN]

/-! ### Bounds on Riemann–Stieltjes sums -/

/-- The absolute increments of `h` along a partition are bounded by the total variation of `h` on
`[a, b]`. -/
theorem Partition.sum_abs_sub_le_variation (P : Partition a b) {h : ℝ → ℝ}
    (hh : BoundedVariationOn h (Icc a b)) :
    ∑ i ∈ range P.n, |h (P.pointN (i + 1)) - h (P.pointN i)| ≤
      (eVariationOn h (Icc a b)).toReal := by
  have hle := eVariationOn.sum_le (f := h) (n := P.n) P.monotone_pointN P.pointN_mem_Icc
  have hne : ∀ i ∈ range P.n, edist (h (P.pointN (i + 1))) (h (P.pointN i)) ≠ ⊤ :=
    fun _ _ => edist_ne_top _ _
  calc ∑ i ∈ range P.n, |h (P.pointN (i + 1)) - h (P.pointN i)|
      = (∑ i ∈ range P.n, edist (h (P.pointN (i + 1))) (h (P.pointN i))).toReal := by
        rw [ENNReal.toReal_sum hne]
        refine sum_congr rfl fun i _ => ?_
        rw [edist_dist, Real.dist_eq, ENNReal.toReal_ofReal (abs_nonneg _)]
    _ ≤ (eVariationOn h (Icc a b)).toReal := ENNReal.toReal_mono hh hle

/-- **Bound against a bounded-variation integrator.** If `|f| ≤ M` on `[a, b]`, then every
Riemann–Stieltjes sum of `f` against `h` is at most `M` times the total variation of `h` on
`[a, b]`. -/
theorem abs_rsSum_le_mul_variation {f h : ℝ → ℝ} {M : ℝ} (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hh : BoundedVariationOn h (Icc a b)) (T : TaggedPartition a b) :
    |rsSum f h T| ≤ M * (eVariationOn h (Icc a b)).toReal := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf a ⟨le_rfl, T.a_le_b⟩)
  rw [rsSum_eq_sum_range]
  calc |∑ i ∈ range T.n, f (T.tagN i) * (h (T.pointN (i + 1)) - h (T.pointN i))|
      ≤ ∑ i ∈ range T.n, |f (T.tagN i) * (h (T.pointN (i + 1)) - h (T.pointN i))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range T.n, M * |h (T.pointN (i + 1)) - h (T.pointN i)| := by
        refine sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hf _ (T.tagN_mem_Icc i)) (abs_nonneg _)
    _ ≤ M * (eVariationOn h (Icc a b)).toReal := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (T.sum_abs_sub_le_variation hh) hM

/-- **Bound against a monotone integrator.** If `|f| ≤ M` on `[a, b]` and `h` is monotone on
`[a, b]`, then every Riemann–Stieltjes sum is at most `M * (h b - h a)`. -/
theorem abs_rsSum_le_of_monotoneOn {f h : ℝ → ℝ} {M : ℝ} (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hh : MonotoneOn h (Icc a b)) (T : TaggedPartition a b) :
    |rsSum f h T| ≤ M * (h b - h a) := by
  have hinc : ∀ i, 0 ≤ h (T.pointN (i + 1)) - h (T.pointN i) := fun i =>
    sub_nonneg.mpr (hh (T.toPartition.pointN_mem_Icc _) (T.toPartition.pointN_mem_Icc _)
      (T.monotone_pointN (Nat.le_succ i)))
  rw [rsSum_eq_sum_range]
  calc |∑ i ∈ range T.n, f (T.tagN i) * (h (T.pointN (i + 1)) - h (T.pointN i))|
      ≤ ∑ i ∈ range T.n, |f (T.tagN i) * (h (T.pointN (i + 1)) - h (T.pointN i))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range T.n, M * (h (T.pointN (i + 1)) - h (T.pointN i)) := by
        refine sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hinc i)]
        exact mul_le_mul_of_nonneg_right (hf _ (T.tagN_mem_Icc i)) (hinc i)
    _ = M * (h b - h a) := by rw [← mul_sum, T.toPartition.sum_range_sub_pointN]

/-- Abel summation by parts, in the form used for Riemann–Stieltjes sums. Mathlib's
`Finset.sum_range_by_parts` writes the partial sums as `H (i + 1) - H 0`, which would double the
constant in `abs_rsSum_le_of_abs_le`. -/
private theorem sum_range_succ_mul_sub_eq (F H : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), F i * (H (i + 1) - H i) =
      F n * H (n + 1) - F 0 * H 0 - ∑ i ∈ range n, (F (i + 1) - F i) * H (i + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- **Summation-by-parts bound against a bounded integrator.** If `|h| ≤ B` and `|f| ≤ M` on
`[a, b]` and `f` has bounded variation there, then every Riemann–Stieltjes sum of `f` against `h`
is at most `B * (2 * M + V(f))`, where `V(f)` is the total variation of `f` on `[a, b]`. The
integrator `h` need not have bounded variation; this is the estimate that makes `h ↦ ∫ f dh`
continuous for the uniform norm, e.g. on regulated integrators. -/
theorem abs_rsSum_le_of_abs_le {f h : ℝ → ℝ} {B M : ℝ} (hh : ∀ x ∈ Icc a b, |h x| ≤ B)
    (hfM : ∀ x ∈ Icc a b, |f x| ≤ M) (hf : BoundedVariationOn f (Icc a b))
    (T : TaggedPartition a b) :
    |rsSum f h T| ≤ B * (2 * M + (eVariationOn f (Icc a b)).toReal) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hh a ⟨le_rfl, T.a_le_b⟩)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfM a ⟨le_rfl, T.a_le_b⟩)
  have hV : 0 ≤ (eVariationOn f (Icc a b)).toReal := ENNReal.toReal_nonneg
  rw [rsSum_eq_sum_range]
  rcases Nat.eq_zero_or_eq_succ_pred T.n with hn | hn
  · rw [hn, sum_range_zero, abs_zero]; positivity
  set F : ℕ → ℝ := fun i => f (T.tagN i)
  set H : ℕ → ℝ := fun i => h (T.pointN i)
  set m := T.n - 1
  have hF : ∀ i, |F i| ≤ M := fun i => hfM _ (T.tagN_mem_Icc i)
  have hH : ∀ i, |H i| ≤ B := fun i => hh _ (T.toPartition.pointN_mem_Icc i)
  have hvar : ∑ i ∈ range m, |F (i + 1) - F i| ≤ (eVariationOn f (Icc a b)).toReal := by
    have hle := eVariationOn.sum_le (f := f) (n := m) T.monotone_tagN T.tagN_mem_Icc
    have hne : ∀ i ∈ range m, edist (f (T.tagN (i + 1))) (f (T.tagN i)) ≠ ⊤ :=
      fun _ _ => edist_ne_top _ _
    calc ∑ i ∈ range m, |F (i + 1) - F i|
        = (∑ i ∈ range m, edist (f (T.tagN (i + 1))) (f (T.tagN i))).toReal := by
          rw [ENNReal.toReal_sum hne]
          refine sum_congr rfl fun i _ => ?_
          rw [edist_dist, Real.dist_eq, ENNReal.toReal_ofReal (abs_nonneg _)]
      _ ≤ _ := ENNReal.toReal_mono hf hle
  change |∑ i ∈ range T.n, F i * (H (i + 1) - H i)| ≤ _
  rw [hn, sum_range_succ_mul_sub_eq]
  calc |F m * H (m + 1) - F 0 * H 0 - ∑ i ∈ range m, (F (i + 1) - F i) * H (i + 1)|
      ≤ |F m * H (m + 1)| + |F 0 * H 0| + ∑ i ∈ range m, |(F (i + 1) - F i) * H (i + 1)| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans le_rfl)
          (abs_sum_le_sum_abs _ _))
    _ ≤ M * B + M * B + ∑ i ∈ range m, |F (i + 1) - F i| * B := by
        gcongr
        · rw [abs_mul]; exact mul_le_mul (hF _) (hH _) (abs_nonneg _) hM
        · rw [abs_mul]; exact mul_le_mul (hF _) (hH _) (abs_nonneg _) hM
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hH _) (abs_nonneg _)
    _ ≤ B * (2 * M + (eVariationOn f (Icc a b)).toReal) := by
        rw [← sum_mul]; nlinarith [mul_le_mul_of_nonneg_right hvar hB]

/-! ### Partitions: tagging and common refinements -/

/-- The left-endpoint tagging of a partition. -/
def Partition.leftTag (P : Partition a b) : TaggedPartition a b where
  toPartition := P
  tags i := P.points i.castSucc
  tag_mem _ := ⟨le_rfl, P.ordered.monotone Fin.castSucc_lt_succ.le⟩

/-- The right-endpoint tagging of a partition. -/
def Partition.rightTag (P : Partition a b) : TaggedPartition a b where
  toPartition := P
  tags i := P.points i.succ
  tag_mem _ := ⟨P.ordered.monotone Fin.castSucc_lt_succ.le, le_rfl⟩

theorem Partition.leftTag_tagN (P : Partition a b) {k : ℕ} (hk : k < P.n) :
    P.leftTag.tagN k = P.pointN k := by
  rw [P.leftTag.tagN_fin ⟨k, hk⟩]
  exact (P.pointN_fin (⟨k, hk⟩ : Fin P.n).castSucc).symm

theorem Partition.rightTag_tagN (P : Partition a b) {k : ℕ} (hk : k < P.n) :
    P.rightTag.tagN k = P.pointN (k + 1) := by
  rw [P.rightTag.tagN_fin ⟨k, hk⟩]
  exact (P.pointN_fin (⟨k, hk⟩ : Fin P.n).succ).symm

theorem Partition.isRefinement_refl (P : Partition a b) : P.IsRefinement P := subset_rfl

theorem Partition.IsRefinement.trans {P Q R : Partition a b} (hRQ : R.IsRefinement Q)
    (hQP : Q.IsRefinement P) : R.IsRefinement P :=
  Set.Subset.trans hQP hRQ

/-- The partition of `[a, b]` whose points are the elements of a finite set `S ⊆ [a, b]`
containing `a` and `b`. -/
noncomputable def Partition.ofFinset (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Icc a b) (ha : a ∈ S)
    (hb : b ∈ S) : Partition a b where
  n := S.card - 1
  points := S.orderEmbOfFin (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨a, ha⟩)).symm
  ordered := (S.orderEmbOfFin _).strictMono
  first := by
    have hpos : 0 < S.card - 1 + 1 := Nat.succ_pos _
    rw [show (0 : Fin (S.card - 1 + 1)) = ⟨0, hpos⟩ from rfl, Finset.orderEmbOfFin_zero _ hpos]
    exact le_antisymm (Finset.min'_le S a ha) (Finset.le_min' _ _ _ fun x hx => (hS x hx).1)
  last := by
    have hpos : 0 < S.card - 1 + 1 := Nat.succ_pos _
    rw [show Fin.last (S.card - 1) = ⟨S.card - 1 + 1 - 1, by omega⟩ from Fin.ext (by simp),
      Finset.orderEmbOfFin_last _ hpos]
    exact le_antisymm (Finset.max'_le _ _ _ fun x hx => (hS x hx).2) (Finset.le_max' S b hb)

theorem Partition.pointSet_ofFinset (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Icc a b) (ha : a ∈ S)
    (hb : b ∈ S) : (Partition.ofFinset S hS ha hb).pointSet = S := by
  simp only [Partition.pointSet, Partition.ofFinset]
  exact Finset.range_orderEmbOfFin _ _

theorem Partition.points_mem_Icc (P : Partition a b) (i : Fin (P.n + 1)) :
    P.points i ∈ Icc a b := by
  rw [← P.pointN_fin]; exact P.pointN_mem_Icc i

/-- The common refinement of two partitions: the partition whose points are the union of their
points. -/
noncomputable def Partition.common (P Q : Partition a b) : Partition a b :=
  Partition.ofFinset (Finset.image P.points univ ∪ Finset.image Q.points univ)
    (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;>
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact Partition.points_mem_Icc _ i)
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, mem_univ _, P.first⟩))
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Fin.last P.n, mem_univ _, P.last⟩))

theorem Partition.common_isRefinement_left (P Q : Partition a b) :
    (P.common Q).IsRefinement P := by
  rintro x ⟨i, rfl⟩
  rw [Partition.common, Partition.pointSet_ofFinset]
  exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ _)))

theorem Partition.common_isRefinement_right (P Q : Partition a b) :
    (P.common Q).IsRefinement Q := by
  rintro x ⟨i, rfl⟩
  rw [Partition.common, Partition.pointSet_ofFinset]
  exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ _)))

/-! ### The Riemann–Stieltjes integral -/

/-- `HasRSIntegral f h a b I`: the Riemann–Stieltjes integral `∫ₐᵇ f dh` exists in the
refinement (Moore–Pollard) sense and equals `I`. For every `ε > 0` there is a partition `P` of
`[a, b]` such that every tagged partition refining `P` has Riemann–Stieltjes sum within `ε` of
`I`. For `b < a` there are no partitions of `[a, b]`, so this never holds. -/
def HasRSIntegral (f h : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ ε > 0, ∃ P : Partition a b, ∀ T : TaggedPartition a b,
    T.toPartition.IsRefinement P → |rsSum f h T - I| < ε

/-- `f` is Riemann–Stieltjes integrable against `h` on `[a, b]` (refinement sense). -/
def RSIntegrable (f h : ℝ → ℝ) (a b : ℝ) : Prop := ∃ I, HasRSIntegral f h a b I

open Classical in
/-- The **Riemann–Stieltjes integral** `∫ₐᵇ f dh` (refinement sense); `0` when `f` is not
integrable against `h` on `[a, b]`. -/
noncomputable def rsIntegral (f h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if hf : RSIntegrable f h a b then hf.choose else 0

/-- The Riemann–Stieltjes integral is unique. -/
theorem HasRSIntegral.unique {f h : ℝ → ℝ} {I J : ℝ} (hI : HasRSIntegral f h a b I)
    (hJ : HasRSIntegral f h a b J) : I = J := by
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  obtain ⟨P, hP⟩ := hI (ε / 2) (by linarith)
  obtain ⟨Q, hQ⟩ := hJ (ε / 2) (by linarith)
  set T := (P.common Q).leftTag
  have h1 := hP T (P.common_isRefinement_left Q)
  have h2 := hQ T (P.common_isRefinement_right Q)
  calc |I - J| = |(rsSum f h T - J) - (rsSum f h T - I)| := by ring_nf
    _ ≤ |rsSum f h T - J| + |rsSum f h T - I| := abs_sub _ _
    _ ≤ ε := by linarith

theorem HasRSIntegral.rsIntegrable {f h : ℝ → ℝ} {I : ℝ} (hI : HasRSIntegral f h a b I) :
    RSIntegrable f h a b := ⟨I, hI⟩

theorem RSIntegrable.hasRSIntegral {f h : ℝ → ℝ} (hf : RSIntegrable f h a b) :
    HasRSIntegral f h a b (rsIntegral f h a b) := by
  rw [rsIntegral]; split_ifs; exact hf.choose_spec

theorem HasRSIntegral.rsIntegral_eq {f h : ℝ → ℝ} {I : ℝ} (hI : HasRSIntegral f h a b I) :
    rsIntegral f h a b = I :=
  hI.rsIntegrable.hasRSIntegral.unique hI

/-- A bound on all Riemann–Stieltjes sums is inherited by the integral. -/
theorem HasRSIntegral.abs_le {f h : ℝ → ℝ} {I C : ℝ} (hI : HasRSIntegral f h a b I)
    (hC : ∀ T : TaggedPartition a b, |rsSum f h T| ≤ C) : |I| ≤ C := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨P, hP⟩ := hI ε hε
  have h1 := hP P.leftTag P.isRefinement_refl
  have h2 := hC P.leftTag
  calc |I| = |rsSum f h P.leftTag - (rsSum f h P.leftTag - I)| := by ring_nf
    _ ≤ |rsSum f h P.leftTag| + |rsSum f h P.leftTag - I| := abs_sub _ _
    _ < C + ε := by linarith

/-! ### Linearity -/

theorem HasRSIntegral.add_left {f g h : ℝ → ℝ} {I J : ℝ} (hf : HasRSIntegral f h a b I)
    (hg : HasRSIntegral g h a b J) : HasRSIntegral (f + g) h a b (I + J) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hf (ε / 2) (by linarith)
  obtain ⟨Q, hQ⟩ := hg (ε / 2) (by linarith)
  refine ⟨P.common Q, fun T hT => ?_⟩
  have h1 := hP T (hT.trans (P.common_isRefinement_left Q))
  have h2 := hQ T (hT.trans (P.common_isRefinement_right Q))
  rw [rsSum_add_left]
  calc |rsSum f h T + rsSum g h T - (I + J)| = |(rsSum f h T - I) + (rsSum g h T - J)| := by
        ring_nf
    _ ≤ |rsSum f h T - I| + |rsSum g h T - J| := abs_add_le _ _
    _ < ε := by linarith

theorem HasRSIntegral.add_right {f g h : ℝ → ℝ} {I J : ℝ} (hg : HasRSIntegral f g a b I)
    (hh : HasRSIntegral f h a b J) : HasRSIntegral f (g + h) a b (I + J) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hg (ε / 2) (by linarith)
  obtain ⟨Q, hQ⟩ := hh (ε / 2) (by linarith)
  refine ⟨P.common Q, fun T hT => ?_⟩
  have h1 := hP T (hT.trans (P.common_isRefinement_left Q))
  have h2 := hQ T (hT.trans (P.common_isRefinement_right Q))
  rw [rsSum_add_right]
  calc |rsSum f g T + rsSum f h T - (I + J)| = |(rsSum f g T - I) + (rsSum f h T - J)| := by
        ring_nf
    _ ≤ |rsSum f g T - I| + |rsSum f h T - J| := abs_add_le _ _
    _ < ε := by linarith

private theorem hasRSIntegral_smul_aux {S : TaggedPartition a b → ℝ} {I : ℝ} (c : ℝ)
    (hS : ∀ ε > 0, ∃ P : Partition a b, ∀ T : TaggedPartition a b,
      T.toPartition.IsRefinement P → |S T - I| < ε) :
    ∀ ε > 0, ∃ P : Partition a b, ∀ T : TaggedPartition a b,
      T.toPartition.IsRefinement P → |c * S T - c * I| < ε := by
  intro ε hε
  obtain ⟨P, hP⟩ := hS (ε / (|c| + 1)) (by positivity)
  refine ⟨P, fun T hT => ?_⟩
  have h1 := hP T hT
  rw [← mul_sub, abs_mul]
  calc |c| * |S T - I| ≤ (|c| + 1) * |S T - I| := by gcongr; linarith
    _ < (|c| + 1) * (ε / (|c| + 1)) := by gcongr
    _ = ε := by field_simp

theorem HasRSIntegral.smul_left {f h : ℝ → ℝ} {I : ℝ} (c : ℝ) (hf : HasRSIntegral f h a b I) :
    HasRSIntegral (c • f) h a b (c * I) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hasRSIntegral_smul_aux c hf ε hε
  exact ⟨P, fun T hT => by rw [rsSum_smul_left]; exact hP T hT⟩

theorem HasRSIntegral.smul_right {f h : ℝ → ℝ} {I : ℝ} (c : ℝ) (hh : HasRSIntegral f h a b I) :
    HasRSIntegral f (c • h) a b (c * I) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hasRSIntegral_smul_aux c hh ε hε
  exact ⟨P, fun T hT => by rw [rsSum_smul_right]; exact hP T hT⟩

theorem HasRSIntegral.neg_left {f h : ℝ → ℝ} {I : ℝ} (hf : HasRSIntegral f h a b I) :
    HasRSIntegral (-f) h a b (-I) := by
  simpa [neg_one_smul] using hf.smul_left (-1)

theorem HasRSIntegral.neg_right {f h : ℝ → ℝ} {I : ℝ} (hh : HasRSIntegral f h a b I) :
    HasRSIntegral f (-h) a b (-I) := by
  simpa [neg_one_smul] using hh.smul_right (-1)

theorem HasRSIntegral.sub_left {f g h : ℝ → ℝ} {I J : ℝ} (hf : HasRSIntegral f h a b I)
    (hg : HasRSIntegral g h a b J) : HasRSIntegral (f - g) h a b (I - J) := by
  simpa [sub_eq_add_neg] using hf.add_left hg.neg_left

theorem HasRSIntegral.sub_right {f g h : ℝ → ℝ} {I J : ℝ} (hg : HasRSIntegral f g a b I)
    (hh : HasRSIntegral f h a b J) : HasRSIntegral f (g - h) a b (I - J) := by
  simpa [sub_eq_add_neg] using hg.add_right hh.neg_right

/-- The integral of a constant integrand: `∫ₐᵇ c dh = c (h b - h a)`, for every integrator `h`. -/
theorem hasRSIntegral_const (c : ℝ) (h : ℝ → ℝ) (hab : a ≤ b) :
    HasRSIntegral (fun _ => c) h a b (c * (h b - h a)) := by
  intro ε hε
  refine ⟨Partition.ofFinset {a, b} (by simp [hab]) (by simp) (by simp), fun T _ => ?_⟩
  rw [rsSum_const, sub_self, abs_zero]; exact hε

theorem rsIntegral_add_left {f g h : ℝ → ℝ} (hf : RSIntegrable f h a b)
    (hg : RSIntegrable g h a b) :
    rsIntegral (f + g) h a b = rsIntegral f h a b + rsIntegral g h a b :=
  (hf.hasRSIntegral.add_left hg.hasRSIntegral).rsIntegral_eq

theorem rsIntegral_add_right {f g h : ℝ → ℝ} (hg : RSIntegrable f g a b)
    (hh : RSIntegrable f h a b) :
    rsIntegral f (g + h) a b = rsIntegral f g a b + rsIntegral f h a b :=
  (hg.hasRSIntegral.add_right hh.hasRSIntegral).rsIntegral_eq

theorem rsIntegral_smul_left {f h : ℝ → ℝ} (c : ℝ) (hf : RSIntegrable f h a b) :
    rsIntegral (c • f) h a b = c * rsIntegral f h a b :=
  (hf.hasRSIntegral.smul_left c).rsIntegral_eq

theorem rsIntegral_smul_right {f h : ℝ → ℝ} (c : ℝ) (hh : RSIntegrable f h a b) :
    rsIntegral f (c • h) a b = c * rsIntegral f h a b :=
  (hh.hasRSIntegral.smul_right c).rsIntegral_eq

/-! ### Bounds on the integral -/

/-- `|∫ₐᵇ f dh| ≤ M · V(h)` for `|f| ≤ M` on `[a, b]` and `h` of bounded variation there. -/
theorem HasRSIntegral.abs_le_mul_variation {f h : ℝ → ℝ} {I M : ℝ}
    (hI : HasRSIntegral f h a b I) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hh : BoundedVariationOn h (Icc a b)) :
    |I| ≤ M * (eVariationOn h (Icc a b)).toReal :=
  hI.abs_le (abs_rsSum_le_mul_variation hf hh)

/-- `|∫ₐᵇ f dh| ≤ M (h b - h a)` for `|f| ≤ M` on `[a, b]` and `h` monotone there. -/
theorem HasRSIntegral.abs_le_of_monotoneOn {f h : ℝ → ℝ} {I M : ℝ}
    (hI : HasRSIntegral f h a b I) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hh : MonotoneOn h (Icc a b)) : |I| ≤ M * (h b - h a) :=
  hI.abs_le (abs_rsSum_le_of_monotoneOn hf hh)

/-- **Uniform-norm bound in the integrator.** `|∫ₐᵇ f dh| ≤ B (2M + V(f))` for `|h| ≤ B` and
`|f| ≤ M` on `[a, b]` with `f` of bounded variation there; no regularity of `h` is used. -/
theorem HasRSIntegral.abs_le_of_abs_le {f h : ℝ → ℝ} {I B M : ℝ}
    (hI : HasRSIntegral f h a b I) (hh : ∀ x ∈ Icc a b, |h x| ≤ B)
    (hfM : ∀ x ∈ Icc a b, |f x| ≤ M) (hf : BoundedVariationOn f (Icc a b)) :
    |I| ≤ B * (2 * M + (eVariationOn f (Icc a b)).toReal) :=
  hI.abs_le (abs_rsSum_le_of_abs_le hh hfM hf)

/-- **Lipschitz dependence on the integrator.** For a bounded-variation integrand `f` with
`|f| ≤ M` on `[a, b]`, if `∫ f dg = I` and `∫ f dh = J` and `|g - h| ≤ δ` on `[a, b]`, then
`|I - J| ≤ δ (2M + V(f))`. -/
theorem HasRSIntegral.abs_sub_le_of_abs_sub_le {f g h : ℝ → ℝ} {I J δ M : ℝ}
    (hI : HasRSIntegral f g a b I) (hJ : HasRSIntegral f h a b J)
    (hgh : ∀ x ∈ Icc a b, |g x - h x| ≤ δ) (hfM : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hf : BoundedVariationOn f (Icc a b)) :
    |I - J| ≤ δ * (2 * M + (eVariationOn f (Icc a b)).toReal) :=
  (hI.sub_right hJ).abs_le_of_abs_le (fun x hx => hgh x hx) hfM hf

/-! ### Refinement estimate and existence -/

/-- Along a partition, `pointN` reflects the order on indices up to `P.n`. -/
theorem Partition.le_of_pointN_le (P : Partition a b) {i j : ℕ} (hi : i ≤ P.n) (hj : j ≤ P.n)
    (hij : P.pointN i ≤ P.pointN j) : i ≤ j := by
  by_contra hlt
  have hlt' := P.ordered (show (⟨j, by omega⟩ : Fin (P.n + 1)) < ⟨i, by omega⟩ from
    Fin.mk_lt_mk.mpr (by omega))
  rw [← P.pointN_fin, ← P.pointN_fin] at hlt'
  simp only at hlt'
  linarith

/-- The positions of the points of `P` among the points of a refinement `Q`. -/
private theorem Partition.exists_index_of_isRefinement {P Q : Partition a b}
    (href : Q.IsRefinement P) :
    ∃ ψ : ℕ → ℕ, Monotone ψ ∧ ψ 0 = 0 ∧ ψ P.n = Q.n ∧ ∀ k, Q.pointN (ψ k) = P.pointN k := by
  have hex : ∀ k : ℕ, ∃ j : ℕ, j ≤ Q.n ∧ Q.pointN j = P.pointN k := by
    intro k
    rcases le_or_gt k P.n with hk | hk
    · obtain ⟨j, hj⟩ := href ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
      refine ⟨j, Nat.le_of_lt_succ j.isLt, ?_⟩
      rw [Q.pointN_fin, hj, ← P.pointN_fin]
    · exact ⟨Q.n, le_rfl, by rw [Q.pointN_of_le le_rfl, P.pointN_of_le hk.le]⟩
  choose ψ hψle hψ using hex
  refine ⟨ψ, fun k k' hkk' => Q.le_of_pointN_le (hψle k) (hψle k') ?_, ?_, ?_, hψ⟩
  · rw [hψ, hψ]; exact P.monotone_pointN hkk'
  · exact Nat.le_zero.mp (Q.le_of_pointN_le (hψle 0) (Nat.zero_le _)
      (by rw [hψ, P.pointN_zero, Q.pointN_zero]))
  · refine le_antisymm (hψle _) (Q.le_of_pointN_le le_rfl (hψle _) ?_)
    rw [hψ, P.pointN_of_le le_rfl, Q.pointN_of_le le_rfl]

private theorem sum_range_eq_sum_sum_Ico (G : ℕ → ℝ) {ψ : ℕ → ℕ} (hψ : Monotone ψ)
    (h0 : ψ 0 = 0) (m : ℕ) :
    ∑ j ∈ range (ψ m), G j = ∑ k ∈ range m, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), G j := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [sum_range_succ, ← ih, sum_range_add_sum_Ico _ (hψ (Nat.le_succ m))]

private theorem sum_Ico_sub_eq (g : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ j ∈ Ico m n, (g (j + 1) - g j) = g n - g m := by
  rw [sum_Ico_eq_sub _ hmn, sum_range_sub, sum_range_sub]; ring

/-- **Refinement estimate.** Let `h` be monotone on `[a, b]` and let `T` refine the tagged
partition `P`. If `|f (ξₖ) - f x| ≤ ω` whenever `x` lies in the `k`-th subinterval of `P` (with
tag `ξₖ`), then the Riemann–Stieltjes sums over `P` and `T` differ by at most `ω (h b - h a)`. -/
theorem abs_rsSum_sub_le_of_isRefinement {f h : ℝ → ℝ} {ω : ℝ} (hh : MonotoneOn h (Icc a b))
    (P T : TaggedPartition a b) (href : T.toPartition.IsRefinement P.toPartition)
    (hω : ∀ k < P.n, ∀ x ∈ Icc (P.pointN k) (P.pointN (k + 1)), |f (P.tagN k) - f x| ≤ ω) :
    |rsSum f h P - rsSum f h T| ≤ ω * (h b - h a) := by
  obtain ⟨ψ, hψ, hψ0, hψn, hψpt⟩ := Partition.exists_index_of_isRefinement href
  set Δ : ℕ → ℝ := fun j => h (T.pointN (j + 1)) - h (T.pointN j)
  have hΔ : ∀ j, 0 ≤ Δ j := fun j =>
    sub_nonneg.mpr (hh (T.toPartition.pointN_mem_Icc _) (T.toPartition.pointN_mem_Icc _)
      (T.monotone_pointN (Nat.le_succ j)))
  have hblock : ∀ k, h (P.pointN (k + 1)) - h (P.pointN k) =
      ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), Δ j := by
    intro k
    rw [sum_Ico_sub_eq (fun j => h (T.pointN j)) (hψ (Nat.le_succ k)), hψpt, hψpt]
  have hT : rsSum f h T =
      ∑ k ∈ range P.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), f (T.tagN j) * Δ j := by
    rw [rsSum_eq_sum_range, ← hψn, sum_range_eq_sum_sum_Ico _ hψ hψ0]
  have hP : rsSum f h P =
      ∑ k ∈ range P.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), f (P.tagN k) * Δ j := by
    rw [rsSum_eq_sum_range]
    refine sum_congr rfl fun k _ => ?_
    rw [hblock, mul_sum]
  have htag : ∀ k ∈ range P.n, ∀ j ∈ Finset.Ico (ψ k) (ψ (k + 1)),
      T.tagN j ∈ Icc (P.pointN k) (P.pointN (k + 1)) := by
    intro k hk j hj
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico] at hj
    have hjn : j < T.n := by
      have := hψ (show k + 1 ≤ P.n by omega); rw [hψn] at this; omega
    obtain ⟨h1, h2⟩ := T.tagN_mem hjn
    rw [← hψpt, ← hψpt]
    exact ⟨(T.monotone_pointN hj.1).trans h1, h2.trans (T.monotone_pointN hj.2)⟩
  rw [hP, hT, ← sum_sub_distrib]
  calc |∑ k ∈ range P.n, (∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), f (P.tagN k) * Δ j -
          ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), f (T.tagN j) * Δ j)|
      ≤ ∑ k ∈ range P.n, |∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), f (P.tagN k) * Δ j -
          ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), f (T.tagN j) * Δ j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range P.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), ω * Δ j := by
        refine sum_le_sum fun k hk => ?_
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
        rw [← sub_mul, abs_mul, abs_of_nonneg (hΔ j)]
        exact mul_le_mul_of_nonneg_right (hω k (Finset.mem_range.mp hk) _ (htag k hk j hj)) (hΔ j)
    _ = ω * (h b - h a) := by
        simp_rw [← mul_sum, ← hblock]
        rw [P.toPartition.sum_range_sub_pointN]

/-- **Cauchy criterion.** If for every `ε > 0` there is a partition `P` such that any two tagged
refinements of `P` have Riemann–Stieltjes sums within `ε`, then `f` is integrable against `h`. -/
theorem rsIntegrable_of_cauchy {f h : ℝ → ℝ}
    (hC : ∀ ε > 0, ∃ P : Partition a b, ∀ T T' : TaggedPartition a b,
      T.toPartition.IsRefinement P → T'.toPartition.IsRefinement P →
        |rsSum f h T - rsSum f h T'| ≤ ε) :
    RSIntegrable f h a b := by
  choose P hP using fun n : ℕ => hC (1 / (n + 1)) (by positivity)
  let Q : ℕ → Partition a b := fun n => Nat.rec (P 0) (fun k Qk => Qk.common (P (k + 1))) n
  have hQP : ∀ n, (Q n).IsRefinement (P n) := by
    intro n
    cases n with
    | zero => exact (P 0).isRefinement_refl
    | succ k => exact Partition.common_isRefinement_right _ _
  have hQmono : ∀ n m, n ≤ m → (Q m).IsRefinement (Q n) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact (Q n).isRefinement_refl
    | succ m _ ih => exact (Partition.common_isRefinement_left (Q m) (P (m + 1))).trans ih
  set s : ℕ → ℝ := fun n => rsSum f h (Q n).leftTag
  have hs : ∀ n m, n ≤ m → |s m - s n| ≤ 1 / (n + 1) := fun n m hnm =>
    hP n _ _ ((hQmono n m hnm).trans (hQP n)) (hQP n)
  have hcauchy : CauchySeq s := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact (hs N n hn).trans_lt hN⟩
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hsI : ∀ n, |s n - I| ≤ 1 / (n + 1) := by
    intro n
    have hlim : Filter.Tendsto (fun m => |s m - s n|) Filter.atTop (nhds |I - s n|) :=
      (hI.sub_const _).abs
    rw [abs_sub_comm]
    exact le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨n, fun m hm => hs n m hm⟩)
  refine ⟨I, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨P N, fun T hT => ?_⟩
  have h1 := hP N T (Q N).leftTag hT (hQP N)
  have h2 := hsI N
  calc |rsSum f h T - I| = |(rsSum f h T - s N) + (s N - I)| := by ring_nf
    _ ≤ |rsSum f h T - s N| + |s N - I| := abs_add_le _ _
    _ < ε := by linarith

/-- The uniform partition of `[a, b]` into `N` subintervals. -/
noncomputable def Partition.uniform (hab : a < b) (N : ℕ) (hN : 0 < N) : Partition a b where
  n := N
  points i := a + i * ((b - a) / N)
  ordered := by
    intro i j hij
    have : (0 : ℝ) < (b - a) / N := div_pos (by linarith) (by exact_mod_cast hN)
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    simp only
    nlinarith
  first := by simp
  last := by
    simp only [Fin.val_last]
    field_simp
    ring

theorem Partition.uniform_pointN (hab : a < b) (N : ℕ) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) :
    (Partition.uniform hab N hN).pointN k = a + k * ((b - a) / N) := by
  have h := (Partition.uniform hab N hN).pointN_fin ⟨k, by simp [Partition.uniform]; omega⟩
  simp only at h
  rw [h]
  rfl

theorem Partition.uniform_pointN_succ_sub (hab : a < b) (N : ℕ) (hN : 0 < N) {k : ℕ}
    (hk : k < N) :
    (Partition.uniform hab N hN).pointN (k + 1) - (Partition.uniform hab N hN).pointN k =
      (b - a) / N := by
  have h1 := (Partition.uniform hab N hN).pointN_fin ⟨k + 1, by simp [Partition.uniform]; omega⟩
  have h2 := (Partition.uniform hab N hN).pointN_fin ⟨k, by simp [Partition.uniform]; omega⟩
  simp only at h1 h2
  rw [h1, h2]
  simp only [Partition.uniform]
  push_cast
  ring

/-- **Existence (Stieltjes).** A function continuous on `[a, b]` is Riemann–Stieltjes integrable
against an integrator monotone on `[a, b]`. -/
theorem rsIntegrable_of_continuousOn_of_monotoneOn {f h : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hh : MonotoneOn h (Icc a b)) : RSIntegrable f h a b := by
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨0, fun ε hε => ⟨(Partition.ofFinset {a} (by simp) (by simp) (by simp)), fun T _ => ?_⟩⟩
    have hn : T.n = 0 := by
      by_contra hn
      have hlt : (0 : Fin (T.n + 1)) < Fin.last T.n := Fin.lt_def.mpr (by simp; omega)
      have := T.ordered hlt
      rw [T.first, T.last] at this
      exact lt_irrefl _ this
    rw [rsSum, show (Finset.univ : Finset (Fin T.n)) = ∅ from by
      rw [Finset.univ_eq_empty_iff]; rw [hn]; infer_instance]
    simpa using hε
  have hU : UniformContinuousOn f (Icc a b) := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hU
  have hV : 0 ≤ h b - h a := sub_nonneg.mpr (hh ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le)
  refine rsIntegrable_of_cauchy fun ε hε => ?_
  set ε' := ε / (2 * (h b - h a) + 1)
  have hε' : 0 < ε' := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hfδ⟩ := hU ε' hε'
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hδ (sub_pos.mpr hab))
  set U := Partition.uniform hab (N + 1) N.succ_pos
  have hmesh : (b - a) / (N + 1 : ℕ) < δ := by
    have := mul_lt_mul_of_pos_left hN (sub_pos.mpr hab)
    rw [mul_div_cancel₀ _ (sub_pos.mpr hab).ne'] at this
    push_cast
    calc (b - a) / (N + 1) = (b - a) * (1 / (N + 1)) := by ring
      _ < δ := this
  have hU' : ∀ T : TaggedPartition a b, T.toPartition.IsRefinement U →
      |rsSum f h U.leftTag - rsSum f h T| ≤ ε' * (h b - h a) := by
    intro T hT
    refine abs_rsSum_sub_le_of_isRefinement hh U.leftTag T hT fun k hk x hx => ?_
    change k < U.n at hk
    change x ∈ Icc (U.pointN k) (U.pointN (k + 1)) at hx
    have hxmem : x ∈ Icc a b := ⟨(U.pointN_mem_Icc k).1.trans hx.1,
      hx.2.trans (U.pointN_mem_Icc (k + 1)).2⟩
    rw [U.leftTag_tagN hk]
    have hlen : U.pointN (k + 1) - U.pointN k = (b - a) / (N + 1 : ℕ) :=
      Partition.uniform_pointN_succ_sub hab (N + 1) N.succ_pos hk
    have hd : dist (U.pointN k) x < δ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    exact (hfδ _ (U.pointN_mem_Icc k) _ hxmem hd).le
  refine ⟨U, fun T T' hT hT' => ?_⟩
  have h1 := hU' T hT
  have h2 := hU' T' hT'
  calc |rsSum f h T - rsSum f h T'|
      = |(rsSum f h U.leftTag - rsSum f h T') - (rsSum f h U.leftTag - rsSum f h T)| := by
        ring_nf
    _ ≤ |rsSum f h U.leftTag - rsSum f h T'| + |rsSum f h U.leftTag - rsSum f h T| :=
        abs_sub _ _
    _ ≤ 2 * (ε' * (h b - h a)) := by linarith
    _ ≤ ε := by
        rw [← mul_assoc, mul_comm 2 ε', mul_assoc]
        calc ε' * (2 * (h b - h a)) ≤ ε' * (2 * (h b - h a) + 1) := by gcongr; linarith
          _ = ε := div_mul_cancel₀ _ (by linarith)

/-- **Existence for bounded-variation integrators.** A function continuous on `[a, b]` is
Riemann–Stieltjes integrable against any integrator of bounded variation on `[a, b]`. -/
theorem rsIntegrable_of_continuousOn_of_boundedVariationOn {f h : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hh : BoundedVariationOn h (Icc a b)) :
    RSIntegrable f h a b := by
  obtain ⟨p, q, hp, hq, rfl, -⟩ :=
    hh.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'
  obtain ⟨I, hI⟩ := rsIntegrable_of_continuousOn_of_monotoneOn hab hf hp
  obtain ⟨J, hJ⟩ := rsIntegrable_of_continuousOn_of_monotoneOn hab hf hq
  exact (hI.sub_right hJ).rsIntegrable

end MathlibExt.Analysis.Integration
