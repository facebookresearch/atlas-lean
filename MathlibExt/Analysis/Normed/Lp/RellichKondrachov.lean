/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Rellich–Kondrachov compactness in Fourier coordinates

The **Rellich–Kondrachov theorem** says that the embedding of the Sobolev
space `H¹` into `L²` is compact: a bounded set of functions with bounded
derivatives is relatively compact in `L²`. In Fourier coordinates this is
the statement that a ball of the weighted `ℓ²` space with weights
`1 + n ^ 2` is relatively compact in `ℓ²`: the weight forces the tails of
the sequences to be uniformly small, and a truncation to the first `N`
coordinates lives in a finite-dimensional space.

Concretely, for `𝕜 = ℝ` or `ℂ`, we show that the set

```
rellichBall M = {x : ℓ²(ℕ, 𝕜) | ∀ F : Finset ℕ, ∑ n ∈ F, (1 + n ^ 2) * ‖x n‖ ^ 2 ≤ M ^ 2}
```

is totally bounded, closed, compact, and sequentially compact in `ℓ²(ℕ, 𝕜)`.
The finite-sum form of the defining bound is used instead of a `tsum`
bound, so no summability hypothesis is needed in the definition (for
nonnegative terms the two forms are equivalent). The truncation argument
is the content of `norm_sub_rellichTrunc_sq_le`.

Companion to the `L^p`-space and compact-operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`.
Not one of the 72 v1 targets. Classical background: see e.g.
L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010,
Section 5.7, Theorem 1 (Rellich–Kondrachov), or H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Springer, 2011, Theorem 9.16.
-/

namespace MathlibExt.Analysis.Normed.Lp.RellichKondrachov

open scoped lp ENNReal Topology

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Rellich weight `1 + n ^ 2`. -/
def rellichWeight (n : ℕ) : ℝ := 1 + (n : ℝ) ^ 2

theorem rellichWeight_nonneg (n : ℕ) : 0 ≤ rellichWeight n := by
  unfold rellichWeight
  positivity

theorem rellichWeight_pos (n : ℕ) : 0 < rellichWeight n := by
  unfold rellichWeight
  positivity

theorem one_le_rellichWeight (n : ℕ) : 1 ≤ rellichWeight n := by
  unfold rellichWeight
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem rellichWeight_mono {m n : ℕ} (h : m ≤ n) : rellichWeight m ≤ rellichWeight n := by
  unfold rellichWeight
  have h2 : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr h) 2
  linarith

/-- Membership in the Rellich ball: every finite weighted partial sum is
bounded by `M ^ 2`. -/
def memRellichBall (x : ℓ²(ℕ, 𝕜)) (M : ℝ) : Prop :=
  ∀ F : Finset ℕ, ∑ n ∈ F, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 ≤ M ^ 2

/-- The Rellich ball of radius `M`: sequences in `ℓ²(ℕ, 𝕜)` whose weighted
`ℓ²` energy is at most `M ^ 2`. -/
def rellichBall (M : ℝ) : Set (ℓ²(ℕ, 𝕜)) := {x | memRellichBall x M}

/-- The coercion of `(2 : ℝ≥0∞)` to `ℝ` is `2`. -/
private theorem toReal_two : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by simp

theorem summable_norm_sq (x : ℓ²(ℕ, 𝕜)) :
    Summable fun n => ‖(x : ℕ → 𝕜) n‖ ^ 2 := by
  have h := (lp.memℓp x).summable (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num)
  simpa only [toReal_two, Real.rpow_two] using h

/-- The `ℓ²` norm squared is the sum of the squared coordinate norms. -/
theorem norm_sq_eq_tsum (x : ℓ²(ℕ, 𝕜)) :
    ‖x‖ ^ 2 = ∑' n, ‖(x : ℕ → 𝕜) n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
    (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) x
  simpa only [toReal_two, Real.rpow_two] using h

theorem summable_weighted {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M) :
    Summable fun n => rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 :=
  summable_of_sum_le (fun n => mul_nonneg (rellichWeight_nonneg n) (sq_nonneg _)) hx

theorem tsum_weighted_le {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M) :
    ∑' n, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 ≤ M ^ 2 :=
  Real.tsum_le_of_sum_le (fun n => mul_nonneg (rellichWeight_nonneg n) (sq_nonneg _)) hx

theorem norm_sq_le_of_memRellichBall {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M) :
    ‖x‖ ^ 2 ≤ M ^ 2 := by
  rw [norm_sq_eq_tsum]
  exact (summable_norm_sq x).tsum_le_of_sum_le fun F =>
    (Finset.sum_le_sum fun n _ =>
      le_mul_of_one_le_left (sq_nonneg _) (one_le_rellichWeight n)).trans (hx F)

theorem norm_le_of_memRellichBall {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hM : 0 ≤ M)
    (hx : memRellichBall x M) : ‖x‖ ≤ M := by
  have h := norm_sq_le_of_memRellichBall hx
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt h
    _ = M := Real.sqrt_sq hM

/-- If `x` is supported in a finite set `S` and its weighted sum over `S` is
at most `M ^ 2`, then `x` lies in the Rellich ball. -/
theorem memRellichBall_of_support {x : ℓ²(ℕ, 𝕜)} {S : Finset ℕ} {M : ℝ}
    (hS : ∀ n, (x : ℕ → 𝕜) n ≠ 0 → n ∈ S)
    (h : ∑ n ∈ S, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 ≤ M ^ 2) :
    memRellichBall x M := by
  intro F
  calc ∑ n ∈ F, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2
      = ∑ n ∈ F ∩ S, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 := by
        apply (Finset.sum_subset Finset.inter_subset_left _).symm
        intro n hnF hnnotin
        have hnS : n ∉ S := fun h => hnnotin (Finset.mem_inter.mpr ⟨hnF, h⟩)
        have hxn : (x : ℕ → 𝕜) n = 0 := by
          by_contra hne
          exact hnS (hS n hne)
        simp [hxn]
    _ ≤ ∑ n ∈ S, rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          fun n _ _ => mul_nonneg (rellichWeight_nonneg n) (sq_nonneg _)
    _ ≤ M ^ 2 := h

/-- The truncation of `x` to its first `N` coordinates. -/
noncomputable def rellichTrunc (N : ℕ) (x : ℓ²(ℕ, 𝕜)) : ℓ²(ℕ, 𝕜) :=
  ∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i)

/-- The tail norm identity: the distance from `x` to its truncation is the
`ℓ²` norm of the tail. -/
theorem norm_sub_rellichTrunc_sq_eq {x : ℓ²(ℕ, 𝕜)} (N : ℕ) :
    ‖x - rellichTrunc N x‖ ^ 2 = ∑' n, ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 := by
  show ‖x - (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i))‖ ^ 2 = _
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_sub_norm_compl_sub_single hp x (Finset.range N)
  have h2 := (summable_norm_sq x).sum_add_tsum_nat_add N
  have h3 := norm_sq_eq_tsum x
  simp only [toReal_two, Real.rpow_two] at h1
  linarith

/-- The tail estimate: the squared distance from `x` to its truncation is at
most `M ^ 2 / (1 + N ^ 2)`. -/
theorem norm_sub_rellichTrunc_sq_le {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M)
    (N : ℕ) : ‖x - rellichTrunc N x‖ ^ 2 ≤ M ^ 2 / rellichWeight N := by
  rw [norm_sub_rellichTrunc_sq_eq]
  have hw : Summable fun n => rellichWeight n * ‖(x : ℕ → 𝕜) n‖ ^ 2 :=
    summable_weighted hx
  have hinj : Function.Injective (. + N : ℕ → ℕ) := fun a b h => Nat.add_right_cancel h
  have hshift : Summable fun n => rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 :=
    hw.comp_injective hinj
  have hshift_unweighted : Summable fun n => ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 :=
    (summable_norm_sq x).comp_injective hinj
  have hle1 : ∑' n, ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 ≤
      ∑' n, (rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2) / rellichWeight N := by
    refine hshift_unweighted.tsum_le_tsum (fun n => ?_) (hshift.div_const _)
    rw [le_div_iff₀ (rellichWeight_pos N)]
    calc ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 * rellichWeight N
        ≤ ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 * rellichWeight (n + N) :=
          mul_le_mul_of_nonneg_left (rellichWeight_mono (Nat.le_add_left N n)) (sq_nonneg _)
      _ = rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 := mul_comm _ _
  have hle2 : ∑' n, (rellichWeight (n + N) * ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2) /
        rellichWeight N ≤ M ^ 2 / rellichWeight N := by
    rw [tsum_div_const]
    apply div_le_div_of_nonneg_right _ (rellichWeight_nonneg N)
    have hsplit := hw.sum_add_tsum_nat_add N
    have hfin : 0 ≤ ∑ i ∈ Finset.range N,
        rellichWeight i * ‖(x : ℕ → 𝕜) i‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (rellichWeight_nonneg i) (sq_nonneg _)
    have htot := tsum_weighted_le hx
    linarith
  exact hle1.trans hle2

/-- The span of the first `N` standard basis vectors of `ℓ²(ℕ, 𝕜)`. -/
noncomputable def rellichSpan (N : ℕ) : Submodule 𝕜 (ℓ²(ℕ, 𝕜)) :=
  Submodule.span 𝕜 (Set.image (fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)) ↑(Finset.range N))

instance (N : ℕ) : FiniteDimensional 𝕜 (rellichSpan (𝕜 := 𝕜) N) :=
  FiniteDimensional.span_of_finite 𝕜
    ((Finset.range N).finite_toSet.image (fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)))

/-- Truncations land in the span of the first `N` basis vectors. -/
theorem rellichTrunc_mem_rellichSpan (N : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    rellichTrunc N x ∈ rellichSpan N := by
  show (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i)) ∈ rellichSpan N
  have hspan : rellichSpan N =
      Submodule.span 𝕜 (Set.image (fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)) ↑(Finset.range N)) := rfl
  rw [hspan]
  apply Submodule.sum_mem
  intro i hi
  have hiS : lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜) ∈
      Submodule.span 𝕜 (Set.image (fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)) ↑(Finset.range N)) := by
    apply Submodule.subset_span
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hi)
  have hsmul : lp.single 2 i ((x : ℕ → 𝕜) i) = (x : ℕ → 𝕜) i • lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜) := by
    rw [← lp.single_smul]
    simp
  rw [hsmul]
  exact Submodule.smul_mem _ _ hiS

/-- The Rellich ball only depends on `|M|`, since the bound is on `M ^ 2`. -/
theorem rellichBall_abs (M : ℝ) :
    rellichBall (𝕜 := 𝕜) M = rellichBall (𝕜 := 𝕜) |M| := by
  ext x
  simp only [rellichBall, Set.mem_ofPred_eq, memRellichBall, sq_abs]

/-- **Rellich–Kondrachov, total boundedness form.** The Rellich ball is
totally bounded in `ℓ²(ℕ, 𝕜)`. -/
theorem totallyBounded_rellichBall (M : ℝ) :
    TotallyBounded (rellichBall (𝕜 := 𝕜) M) := by
  rw [rellichBall_abs]
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Choose `N` so large that the tail estimate beats `ε / 2`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |M| ^ 2 / rellichWeight N < (ε / 2) ^ 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((|M| ^ 2 + 1) / (ε / 2) ^ 2)
    refine ⟨N, ?_⟩
    have hε2 : (0 : ℝ) < (ε / 2) ^ 2 := by positivity
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have hpos : (0 : ℝ) < (|M| ^ 2 + 1) / (ε / 2) ^ 2 := by positivity
      have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans hpos hN
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hNpos)
    have hNw : (|M| ^ 2 + 1) / (ε / 2) ^ 2 < rellichWeight N := by
      have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      calc (|M| ^ 2 + 1) / (ε / 2) ^ 2 < (N : ℝ) := hN
        _ ≤ (N : ℝ) ^ 2 := h2
        _ ≤ rellichWeight N := by
          unfold rellichWeight
          have hsq : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
          linarith
    calc |M| ^ 2 / rellichWeight N
        ≤ (|M| ^ 2 + 1) / rellichWeight N :=
          div_le_div_of_nonneg_right (by linarith) (rellichWeight_nonneg N)
      _ < (|M| ^ 2 + 1) / ((|M| ^ 2 + 1) / (ε / 2) ^ 2) :=
          div_lt_div_of_pos_left (by positivity) (by positivity) hNw
      _ = (ε / 2) ^ 2 := by field_simp
  -- The truncated set is compact: it sits in the `|M|`-ball of the
  -- finite-dimensional span of the first `N` basis vectors.
  have hproperK : ProperSpace 𝕜 := FiniteDimensional.proper_real 𝕜
  have hlc : LocallyCompactSpace 𝕜 := by infer_instance
  have hproperS : ProperSpace (rellichSpan (𝕜 := 𝕜) N) :=
    FiniteDimensional.proper 𝕜 (rellichSpan (𝕜 := 𝕜) N)
  set K : Set (ℓ²(ℕ, 𝕜)) :=
    ((↑) : rellichSpan (𝕜 := 𝕜) N → ℓ²(ℕ, 𝕜)) ''
      Metric.closedBall (0 : rellichSpan (𝕜 := 𝕜) N) |M| with hK
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : rellichSpan (𝕜 := 𝕜) N) |M|).image continuous_subtype_val
  obtain ⟨t, htfin, hcover⟩ :=
    Metric.totallyBounded_iff.mp hKcompact.totallyBounded (ε / 2) (by linarith)
  refine ⟨t, htfin, fun x hx => ?_⟩
  have hx' : memRellichBall x |M| := hx
  -- The truncation of `x` lies in `K`.
  have htruncNorm : ‖rellichTrunc N x‖ ≤ |M| := by
    have h1 : ‖rellichTrunc N x‖ ≤ ‖x‖ := by
      have hsq : ‖rellichTrunc N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
        have hsum : ‖rellichTrunc N x‖ ^ 2 =
            ∑ i ∈ Finset.range N, ‖(x : ℕ → 𝕜) i‖ ^ 2 := by
          have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
          have h := lp.norm_sum_single hp (fun i => (x : ℕ → 𝕜) i) (Finset.range N)
          simpa only [toReal_two, Real.rpow_two, rellichTrunc] using h
        rw [hsum, norm_sq_eq_tsum]
        exact (summable_norm_sq x).sum_le_tsum _ (fun i _ => sq_nonneg _)
      calc ‖rellichTrunc N x‖ = Real.sqrt (‖rellichTrunc N x‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
        _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)
    exact h1.trans (norm_le_of_memRellichBall (abs_nonneg _) hx')
  have htruncK : rellichTrunc N x ∈ K := by
    refine ⟨⟨rellichTrunc N x, rellichTrunc_mem_rellichSpan N x⟩, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact htruncNorm
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (hcover htruncK)
  have hdist1 : dist x (rellichTrunc N x) < ε / 2 := by
    rw [dist_eq_norm]
    have htail := norm_sub_rellichTrunc_sq_le hx' N
    have hlt : ‖x - rellichTrunc N x‖ ^ 2 < (ε / 2) ^ 2 := lt_of_le_of_lt htail hN
    have habs := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos (by linarith : (0 : ℝ) < ε / 2)] at habs
  have hdist2 : dist (rellichTrunc N x) y < ε / 2 := Metric.mem_ball.mp hy
  refine Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩
  rw [Metric.mem_ball]
  calc dist x y ≤ dist x (rellichTrunc N x) + dist (rellichTrunc N x) y :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hdist1 hdist2
    _ = ε := add_halves ε

/-- **Rellich–Kondrachov, closedness form.** The Rellich ball is closed. -/
theorem isClosed_rellichBall (M : ℝ) : IsClosed (rellichBall (𝕜 := 𝕜) M) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u y hu hlim
  show memRellichBall y M
  intro F
  have hcoord : ∀ n : ℕ, Filter.Tendsto
      (fun k => ((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n) Filter.atTop (𝓝 ((y : ℕ → 𝕜) n)) := by
    intro n
    have h0 : Filter.Tendsto (fun k => ‖u k - y‖) Filter.atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlim
    have hbound : ∀ k, ‖((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n - (y : ℕ → 𝕜) n‖ ≤ ‖u k - y‖ := by
      intro k
      have h := lp.norm_apply_le_norm (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (u k - y) n
      simpa [lp.coeFn_sub, Pi.sub_apply] using h
    have hsqueeze : Filter.Tendsto
        (fun k => ‖((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n - (y : ℕ → 𝕜) n‖)
        Filter.atTop (𝓝 0) :=
      squeeze_zero (fun k => norm_nonneg _) hbound h0
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hsqueeze
  have hsum : Filter.Tendsto
      (fun k => ∑ n ∈ F, rellichWeight n * ‖((u k : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) n‖ ^ 2)
      Filter.atTop (𝓝 (∑ n ∈ F, rellichWeight n * ‖(y : ℕ → 𝕜) n‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro n _
    exact ((hcoord n).norm.pow 2).const_mul (rellichWeight n)
  exact le_of_tendsto_of_tendsto' hsum tendsto_const_nhds (fun k => hu k F)

/-- **Rellich–Kondrachov, compactness form.** The Rellich ball is compact in
`ℓ²(ℕ, 𝕜)`. -/
theorem isCompact_rellichBall (M : ℝ) : IsCompact (rellichBall (𝕜 := 𝕜) M) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_rellichBall M, (isClosed_rellichBall M).isComplete⟩

/-- **Rellich–Kondrachov, sequential form.** Every sequence in the Rellich
ball has a subsequence converging in `ℓ²(ℕ, 𝕜)` to a point of the ball. -/
theorem exists_subseq_tendsto_of_memRellichBall (M : ℝ) {u : ℕ → ℓ²(ℕ, 𝕜)}
    (hu : ∀ n, u n ∈ rellichBall (𝕜 := 𝕜) M) :
    ∃ y ∈ rellichBall (𝕜 := 𝕜) M, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 y) := by
  obtain ⟨y, hy, φ, hφ, hlim⟩ := (isCompact_rellichBall M).tendsto_subseq hu
  exact ⟨y, hy, φ, hφ, hlim⟩

end MathlibExt.Analysis.Normed.Lp.RellichKondrachov
