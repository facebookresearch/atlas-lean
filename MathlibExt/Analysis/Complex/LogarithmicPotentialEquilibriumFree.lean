/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# The equilibrium-free logarithmic potential conjecture is false

AMR-022-7078 (Problem 7.78, Rubel): Equilibrium-free logarithmic
potentials. Is there a distinct sequence {z_n} with Σ1/|z_n| < ∞ and
Σ1/(z-z_n) ≠ 0 for all z? Resolved negatively: Clunie–Eremenko–Rossi
proved the field always has (infinitely many) zeros.

The main result, `conjecture_refuted`, proves that `conjecture` is false: for every sequence
$(z_n)$ of pairwise distinct nonzero complex numbers with $\sum_n 1/|z_n| < \infty$, the field
$\sum_n 1/(z - z_n)$ vanishes at some point $z$ that is not one of the $z_n$.

## Main declarations

* `ChargeSeq`, `PointsDistinct`, `IsSummable`, `FieldSum`: charge sequences, their hypotheses and
  their fields.
* `conjecture`: the existence of a charge sequence whose field has no zero off the charges.
* `conjecture_refuted`: `conjecture` is false.

## Proof

The canonical product $P(z) = \prod_n (1 - z/z_n)$ converges locally uniformly on $\mathbb{C}$,
so it is entire; it vanishes exactly at the $z_n$, and away from them its logarithmic derivative
is the field. Splitting off finitely many factors, so that the remaining tail of
$\sum_n 1/|z_n|$ is small, gives $|P(z)| \le C_\varepsilon e^{\varepsilon |z|}$ for every
$\varepsilon > 0$, and Cauchy's estimate gives the same bound for $P'$.

Suppose that the field has no zero off the $z_n$. Then $P'$ vanishes nowhere: off the $z_n$
because $P' = P \cdot \sum_n 1/(z - z_n)$ there, and at each $z_m$ because the zero of $P$ at
$z_m$ is simple. A zero-free entire function is $e^h$ for an entire function $h$, a primitive of
its logarithmic derivative, and the growth bound gives
$\operatorname{Re} h(z) \le \varepsilon |z| + K_\varepsilon$. The Borel–Carathéodory theorem
turns this into $|h(z)| \le \varepsilon |z| + K'_\varepsilon$, and Cauchy's estimate then gives
$h' = 0$. Hence $P'$ is constant and $P$ is affine, which is impossible because $P$ vanishes at
the two distinct points $z_0$ and $z_1$.
-/

@[expose] public section

namespace MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted

/-! Source record `AMR-022-7078` (Problem 7.78). -/

/-- **Charge sequences.** A charge sequence is an arbitrary sequence $(z_n)_{n \in \mathbb{N}}$ of
complex numbers, read as the positions of the charges. -/
abbrev ChargeSeq := ℕ → ℂ

/-- **Distinct charge positions.** A charge sequence $(z_n)$ has distinct positions when its terms
are pairwise distinct: $z_m \neq z_n$ whenever $m \neq n$. -/
def PointsDistinct (c : ChargeSeq) : Prop :=
  Function.Injective c

/-- **Summable charge sequences.** A charge sequence $(z_n)$ is summable when $z_n \neq 0$ for every
$n$ and $\sum_n 1/|z_n| < \infty$. -/
def IsSummable (c : ChargeSeq) : Prop :=
  (∀ n, c n ≠ 0) ∧ Summable (fun n => 1 / ‖c n‖)

/-- **Field of a charge sequence.** For a charge sequence $(z_n)$ and a point $z \in \mathbb{C}$,
the field at $z$ is the sum $\sum_n 1/(z - z_n)$, where a term with $z_n = z$ counts as $0$ and the
sum is taken to be $0$ when the family $\bigl(1/(z - z_n)\bigr)_n$ is not summable.

The sum converges absolutely when $z_n \neq 0$ for every $n$ and $\sum_n 1/|z_n| < \infty$. -/
noncomputable def FieldSum (c : ChargeSeq) (z : ℂ) : ℂ :=
  ∑' n, 1 / (z - c n)

/-- **Equilibrium-free logarithmic potential conjecture.** The conjecture states that there exists
a charge sequence $(z_n)$ whose positions are pairwise distinct, which is summable ($z_n \neq 0$
for every $n$ and $\sum_n 1/|z_n| < \infty$), and whose field $\sum_n 1/(z - z_n)$ is nonzero at
every point $z \in \mathbb{C}$ that is not one of the $z_n$.

Source: record AMR-022-7078 (Problem 7.78, Rubel). -/
def conjecture : Prop :=
  ∃ c : ChargeSeq, PointsDistinct c ∧ IsSummable c ∧
    ∀ z : ℂ, (∀ n, z ≠ c n) → FieldSum c z ≠ 0

open Complex Metric Set

/-! ### Zero-free entire functions of exponential type zero -/

/-- A zero-free entire function `F` with `‖F z‖ ≤ C * exp (ε * ‖z‖)` for every `ε > 0` (and some
`C` depending on `ε`) has vanishing derivative: `F = exp ∘ h` for an entire `h`, the growth bound
controls `Re h`, the Borel–Carathéodory theorem then controls `‖h‖`, and Cauchy's estimate gives
`h' = 0`. -/
private lemma deriv_eq_zero_of_forall_norm_le_exp {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∀ z, F z ≠ 0)
    (hgrowth : ∀ ε > 0, ∃ C, ∀ z, ‖F z‖ ≤ C * Real.exp (ε * ‖z‖)) (c : ℂ) :
    deriv F c = 0 := by
  have hL : Differentiable ℂ (fun z => deriv F z / F z) := fun z =>
    ((hF.analyticAt z).deriv.differentiableAt).div (hF z) (hF0 z)
  obtain ⟨H, hH⟩ := hL.isExactOn_univ
  have hH' : ∀ z, HasDerivAt H (deriv F z / F z) z := fun z => hH z (mem_univ z)
  have hFexp : ∀ z, F z = F 0 * cexp (H z - H 0) := by
    have hG : ∀ z, HasDerivAt (fun w => F w * cexp (-H w)) 0 z := by
      intro z
      have h1 := (hF z).hasDerivAt
      have h2 := ((hH' z).neg).cexp
      convert h1.mul h2 using 1
      field_simp [hF0 z]
      ring
    have hGc : ∀ z, F z * cexp (-H z) = F 0 * cexp (-H 0) := fun z =>
      is_const_of_deriv_eq_zero (fun w => (hG w).differentiableAt) (fun w => (hG w).deriv) z 0
    intro z
    calc F z = F z * cexp (-H z) * cexp (H z) := by
          rw [mul_assoc, ← Complex.exp_add]; simp
      _ = F 0 * cexp (-H 0) * cexp (H z) := by rw [hGc z]
      _ = F 0 * cexp (H z - H 0) := by
          rw [mul_assoc, ← Complex.exp_add]; ring_nf
  set h : ℂ → ℂ := fun z => H z - H 0
  have hhd : Differentiable ℂ h := fun z => ((hH' z).differentiableAt).sub_const _
  have hh0 : h 0 = 0 := by simp [h]
  have hre : ∀ ε > 0, ∃ K, ∀ z, (h z).re ≤ K + ε * ‖z‖ := by
    intro ε hε
    obtain ⟨C, hC⟩ := hgrowth ε hε
    have hF0pos : 0 < ‖F 0‖ := norm_pos_iff.mpr (hF0 0)
    have hCpos : 0 < C := by
      have := hC 0
      simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at this
      linarith
    refine ⟨Real.log (C / ‖F 0‖), fun z => ?_⟩
    have h1 : ‖F z‖ = ‖F 0‖ * Real.exp (h z).re := by
      rw [hFexp z, norm_mul, Complex.norm_exp]
    have h2 : Real.exp (h z).re ≤ (C / ‖F 0‖) * Real.exp (ε * ‖z‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hF0pos, mul_comm, ← h1]
      exact hC z
    calc (h z).re = Real.log (Real.exp (h z).re) := (Real.log_exp _).symm
      _ ≤ Real.log ((C / ‖F 0‖) * Real.exp (ε * ‖z‖)) :=
          Real.log_le_log (Real.exp_pos _) h2
      _ = Real.log (C / ‖F 0‖) + ε * ‖z‖ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hnorm : ∀ ε > 0, ∃ K, ∀ z, ‖h z‖ ≤ K + ε * ‖z‖ := by
    intro ε hε
    obtain ⟨K, hK⟩ := hre (ε / 4) (by positivity)
    refine ⟨2 * (|K| + 1), fun z => ?_⟩
    rcases eq_or_ne z 0 with rfl | hz
    · simp only [hh0, norm_zero, mul_zero, add_zero]; positivity
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hM : 0 < |K| + 1 + ε / 4 * (2 * ‖z‖) := by positivity
    have hBC := Complex.borelCaratheodory_zero hM hhd.differentiableOn (R := 2 * ‖z‖)
      (fun w hw => ?_) (by positivity) (by rw [mem_ball_zero_iff]; linarith) hh0
    · calc ‖h z‖ ≤ 2 * (|K| + 1 + ε / 4 * (2 * ‖z‖)) * ‖z‖ / (2 * ‖z‖ - ‖z‖) := hBC
        _ = 2 * (|K| + 1) + ε * ‖z‖ := by field_simp; ring
    · have hw' : ‖w‖ < 2 * ‖z‖ := mem_ball_zero_iff.mp hw
      rw [Set.mem_ofPred_eq]
      have := hK w
      have := le_abs_self K
      nlinarith
  have hderiv : deriv h c = 0 := by
    refine norm_le_zero_iff.1 (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
    obtain ⟨K, hK⟩ := hnorm (ε / 2) (by positivity)
    set R := 2 * (|K| + ε / 2 * ‖c‖) / ε + 1 with hRdef
    have hR : 0 < R := by positivity
    have hεR : ε * R = 2 * (|K| + ε / 2 * ‖c‖) + ε := by
      rw [hRdef]; field_simp
    have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := c) hR
      hhd.diffContOnCl (C := K + ε / 2 * (‖c‖ + R)) (fun w hw => ?_)
    · calc ‖deriv h c‖ ≤ (K + ε / 2 * (‖c‖ + R)) / R := hCauchy
        _ ≤ ε := by
          rw [div_le_iff₀ hR]
          have := le_abs_self K
          nlinarith
    · have hwc : ‖w‖ ≤ ‖c‖ + R := by
        have hd := mem_sphere_iff_norm.mp hw
        calc ‖w‖ = ‖(w - c) + c‖ := by ring_nf
          _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
          _ = ‖c‖ + R := by rw [hd]; ring
      calc ‖h w‖ ≤ K + ε / 2 * ‖w‖ := hK w
        _ ≤ K + ε / 2 * (‖c‖ + R) := by gcongr
  have hdh : deriv h c = deriv F c / F c := ((hH' c).sub_const (H 0)).deriv
  rw [hdh] at hderiv
  exact (div_eq_zero_iff.mp hderiv).resolve_right (hF0 c)

/-! ### The canonical product -/

/-- The norm of `∏' i, (1 + f i)` is at most `exp (∑' i, ‖f i‖)`. -/
private lemma norm_tprod_one_add_le_exp {ι : Type*} {f : ι → ℂ} (hf : Summable (‖f ·‖)) :
    ‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖) := by
  have hm := (multipliable_one_add_of_summable hf).hasProd
  refine le_of_tendsto' hm.norm fun s => ?_
  calc ‖∏ i ∈ s, (1 + f i)‖ ≤ ∏ i ∈ s, ‖1 + f i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i ∈ s, (1 + ‖f i‖) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
          simpa using norm_add_le 1 (f i)
    _ ≤ Real.exp (∑ i ∈ s, ‖f i‖) := Real.prod_one_add_le_exp_sum _ fun _ => norm_nonneg _
    _ ≤ Real.exp (∑' i, ‖f i‖) :=
        Real.exp_le_exp.mpr (hf.sum_le_tsum _ fun _ _ => norm_nonneg _)

/-- The canonical product `z ↦ ∏' n, (1 - z * a n)`; for `a n = 1 / z n` it vanishes exactly at
the points `z n`. -/
private noncomputable def prodFn (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n, (1 - z * a n)

/-- Scaling a summable sequence by `z` keeps it summable. -/
private lemma summable_norm_mul {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (z : ℂ) :
    Summable (fun n => ‖z * a n‖) := by
  simpa [norm_mul] using ha.mul_left ‖z‖

/-- The canonical product converges locally uniformly on `ℂ`. -/
private lemma hasProdLocallyUniformlyOn_prodFn {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    HasProdLocallyUniformlyOn (fun n z => 1 - z * a n) (prodFn a) univ := by
  have h1 : (fun n (z : ℂ) => 1 - z * a n) = fun n z => 1 + -(z * a n) := by
    funext n z; ring
  have h2 : prodFn a = fun z => ∏' n, (1 + -(z * a n)) := by
    funext z; simp only [prodFn, sub_eq_add_neg]
  rw [h1, h2]
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine Summable.hasProdUniformlyOn_one_add hK (ha.mul_left R) (.of_forall fun n z hz => ?_)
    fun n => by fun_prop
  have hz' := mem_closedBall_zero_iff.mp (hR hz)
  rw [norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_right hz' (norm_nonneg _)

/-- The canonical product is entire. -/
private lemma differentiable_prodFn {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    Differentiable ℂ (prodFn a) := by
  rw [← differentiableOn_univ]
  exact (hasProdLocallyUniformlyOn_prodFn ha).differentiableOn
    (.of_forall fun _ => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun _ _ => by fun_prop))
    isOpen_univ

/-- The canonical product does not vanish at `z` when no factor does. -/
private lemma prodFn_ne_zero {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {z : ℂ}
    (hz : ∀ n, z * a n ≠ 1) : prodFn a z ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable (f := fun n => -(z * a n))
    (fun n h => hz n (by linear_combination -h)) (by simpa using summable_norm_mul ha z)
  simpa [prodFn, sub_eq_add_neg] using this

/-- The canonical product vanishes at `z` when one factor does. -/
private lemma prodFn_eq_zero {a : ℕ → ℂ} {z : ℂ} {m : ℕ} (hm : z * a m = 1) :
    prodFn a z = 0 :=
  tprod_of_exists_eq_zero ⟨m, by rw [hm, sub_self]⟩

/-- The logarithmic derivative of one factor. -/
private lemma logDeriv_one_sub_mul (b z : ℂ) :
    logDeriv (fun w : ℂ => 1 - w * b) z = -b / (1 - z * b) := by
  rw [logDeriv_apply, (((hasDerivAt_id' z).mul_const b).const_sub 1).deriv]
  simp

/-- Off its zeros, the logarithmic derivative of the canonical product is the sum of those of its
factors. -/
private lemma logDeriv_prodFn {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {z : ℂ}
    (hz : ∀ n, z * a n ≠ 1) :
    logDeriv (prodFn a) z = ∑' n, -a n / (1 - z * a n) := by
  have hsum : Summable fun n => logDeriv (fun w : ℂ => 1 - w * a n) z := by
    simp only [logDeriv_one_sub_mul]
    refine (ha.mul_left 2).of_norm_bounded_eventually ?_
    filter_upwards [(summable_norm_mul ha z).tendsto_cofinite_zero.eventually_le_const
      one_half_pos] with n hn
    have h1 : 1 / 2 ≤ ‖1 - z * a n‖ := by
      have := norm_sub_norm_le (1 : ℂ) (z * a n)
      rw [norm_one] at this
      linarith
    rw [norm_div, norm_neg, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (a n)]
  have h := logDeriv_tprod_eq_tsum isOpen_univ (mem_univ z) (f := fun n w => 1 - w * a n)
    (fun n => sub_ne_zero.mpr (hz n).symm) (fun n => by fun_prop) hsum
    (hasProdLocallyUniformlyOn_prodFn ha).multipliableLocallyUniformlyOn (prodFn_ne_zero ha hz)
  simp only [logDeriv_one_sub_mul] at h
  exact h

/-- Removing one factor from the canonical product. -/
private lemma prodFn_eq_mul_prodFn_update {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) (m : ℕ)
    (z : ℂ) : prodFn a z = (1 - z * a m) * prodFn (Function.update a m 0) z := by
  classical
  have hupd : Function.update (fun n => 1 - z * a n) m 1 =
      fun n => 1 - z * Function.update a m 0 n := by
    funext n
    rcases eq_or_ne n m with rfl | hn
    · simp
    · simp [Function.update_of_ne hn]
  have ha' : Summable (fun n => ‖Function.update a m 0 n‖) := by
    refine ha.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rcases eq_or_ne n m with rfl | hn
    · simp
    · simp [Function.update_of_ne hn]
  have hmult : Multipliable (Function.update (fun n => 1 - z * a n) m 1) := by
    rw [hupd]
    exact multipliable_one_sub_of_summable (summable_norm_mul ha' z)
  rw [prodFn, Multipliable.tprod_eq_mul_tprod_ite' m hmult, prodFn]
  congr 1
  refine tprod_congr fun n => ?_
  rcases eq_or_ne n m with rfl | hn
  · simp
  · simp [hn]

/-! ### Growth of the canonical product -/

/-- `1 + t ≤ exp (δ * t) / δ` for `0 < δ ≤ 1`. -/
private lemma one_add_le_exp_mul_div {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 + t ≤ Real.exp (δ * t) / δ := by
  rw [le_div_iff₀ hδ]
  have := Real.add_one_le_exp (δ * t)
  nlinarith

/-- The canonical product has exponential type zero. -/
private lemma norm_prodFn_le {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {ε : ℝ}
    (hε : 0 < ε) : ∃ C, ∀ z, ‖prodFn a z‖ ≤ C * Real.exp (ε * ‖z‖) := by
  obtain ⟨N, hN⟩ : ∃ N, ∑' k, ‖a (k + N)‖ ≤ ε / 2 :=
    ((tendsto_sum_nat_add fun n => ‖a n‖).eventually
      (ge_mem_nhds (by linarith : (0 : ℝ) < ε / 2))).exists
  set A := ∑' n, ‖a n‖
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  set δ := min 1 (ε / (2 * (A + 1)))
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδA : δ * A ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * (A + 1)) := min_le_right _ _
    calc δ * A ≤ ε / (2 * (A + 1)) * A := by gcongr
      _ ≤ ε / (2 * (A + 1)) * (A + 1) := by gcongr; linarith
      _ = ε / 2 := by field_simp
  refine ⟨(δ ^ N)⁻¹, fun z => ?_⟩
  have hmult : Multipliable (fun n => 1 - z * a (n + N)) :=
    multipliable_one_sub_of_summable ((summable_nat_add_iff N).mpr (summable_norm_mul ha z))
  rw [prodFn, ← Multipliable.prod_mul_tprod_nat_mul' (f := fun n => 1 - z * a n) hmult,
    norm_mul]
  have hhead : ‖∏ i ∈ Finset.range N, (1 - z * a i)‖ ≤
      (δ ^ N)⁻¹ * Real.exp (ε / 2 * ‖z‖) := by
    calc ‖∏ i ∈ Finset.range N, (1 - z * a i)‖
        ≤ ∏ i ∈ Finset.range N, ‖1 - z * a i‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ i ∈ Finset.range N, (Real.exp (δ * (‖z‖ * ‖a i‖)) / δ) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
          calc ‖1 - z * a i‖ ≤ 1 + ‖z‖ * ‖a i‖ := by
                simpa [norm_mul] using norm_sub_le (1 : ℂ) (z * a i)
            _ ≤ Real.exp (δ * (‖z‖ * ‖a i‖)) / δ :=
                one_add_le_exp_mul_div hδ0 hδ1
      _ = (δ ^ N)⁻¹ * Real.exp (δ * ‖z‖ * ∑ i ∈ Finset.range N, ‖a i‖) := by
          rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_range,
            Finset.mul_sum, div_eq_inv_mul]
          simp only [mul_assoc]
      _ ≤ (δ ^ N)⁻¹ * Real.exp (ε / 2 * ‖z‖) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          calc δ * ‖z‖ * ∑ i ∈ Finset.range N, ‖a i‖ ≤ δ * ‖z‖ * A := by
                gcongr
                exact ha.sum_le_tsum _ fun _ _ => norm_nonneg _
            _ = δ * A * ‖z‖ := by ring
            _ ≤ ε / 2 * ‖z‖ := by gcongr
  have htail : ‖∏' i, (1 - z * a (i + N))‖ ≤ Real.exp (ε / 2 * ‖z‖) := by
    have hs : Summable (fun i => ‖-(z * a (i + N))‖) := by
      simpa using (summable_nat_add_iff N).mpr (summable_norm_mul ha z)
    have := norm_tprod_one_add_le_exp hs
    simp only [← sub_eq_add_neg, norm_neg, norm_mul] at this
    refine this.trans (Real.exp_le_exp.mpr ?_)
    rw [tsum_mul_left, mul_comm]
    gcongr
  calc ‖∏ i ∈ Finset.range N, (1 - z * a i)‖ * ‖∏' i, (1 - z * a (i + N))‖
      ≤ (δ ^ N)⁻¹ * Real.exp (ε / 2 * ‖z‖) * Real.exp (ε / 2 * ‖z‖) :=
        mul_le_mul hhead htail (norm_nonneg _) (by positivity)
    _ = (δ ^ N)⁻¹ * Real.exp (ε * ‖z‖) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- The derivative of the canonical product has exponential type zero. -/
private lemma norm_deriv_prodFn_le {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {ε : ℝ}
    (hε : 0 < ε) : ∃ C, ∀ z, ‖deriv (prodFn a) z‖ ≤ C * Real.exp (ε * ‖z‖) := by
  obtain ⟨C, hC⟩ := norm_prodFn_le ha hε
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨C * Real.exp ε, fun z => ?_⟩
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) one_pos
    (differentiable_prodFn ha).diffContOnCl (C := C * Real.exp ε * Real.exp (ε * ‖z‖))
    (fun w hw => ?_)
  · simpa using hCauchy
  · have hwz : ‖w‖ ≤ ‖z‖ + 1 := by
      have hd := mem_sphere_iff_norm.mp hw
      calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z‖ + 1 := by rw [hd]; ring
    calc ‖prodFn a w‖ ≤ C * Real.exp (ε * ‖w‖) := hC w
      _ ≤ C * Real.exp (ε * (‖z‖ + 1)) := by gcongr
      _ = C * Real.exp ε * Real.exp (ε * ‖z‖) := by
          rw [mul_add, mul_one, Real.exp_add]; ring

/-! ### The refutation -/

/--
**The equilibrium-free logarithmic potential conjecture is false.** There is no charge sequence
$(z_n)$ whose positions are pairwise distinct, which is summable ($z_n \neq 0$ for every $n$ and
$\sum_n 1/|z_n| < \infty$), and whose field $\sum_n 1/(z - z_n)$ is nonzero at every point
$z \in \mathbb{C}$ that is not one of the $z_n$.

Clunie, Eremenko and Rossi proved more: under these hypotheses the field has infinitely many
zeros.

Source: J. Clunie, A. Eremenko and J. Rossi, On equilibrium points of logarithmic and
Newtonian potentials, J. London Math. Soc. (2) 47 (1993), 309-320. Moved from
`OpenConjectures/Analysis/LogarithmicPotentialEquilibriumFree`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  rintro ⟨c, hinj, ⟨hc0, hcs⟩, hfield⟩
  set a : ℕ → ℂ := fun n => (c n)⁻¹
  have ha : Summable (fun n => ‖a n‖) := by simpa [a, norm_inv, one_div] using hcs
  have hca : ∀ m, c m * a m = 1 := fun m => mul_inv_cancel₀ (hc0 m)
  set P := prodFn a
  have hPd : Differentiable ℂ P := differentiable_prodFn ha
  have hP'ne : ∀ z, deriv P z ≠ 0 := by
    intro z
    by_cases hz : ∃ m, z = c m
    · obtain ⟨m, rfl⟩ := hz
      set a' := Function.update a m 0
      have ha' : Summable (fun n => ‖a' n‖) := by
        refine ha.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
        rcases eq_or_ne n m with rfl | hn
        · simp [a']
        · simp [a', Function.update_of_ne hn]
      have hsplit : P = fun z => (1 - z * a m) * prodFn a' z :=
        funext fun z => prodFn_eq_mul_prodFn_update ha m z
      have hQ : prodFn a' (c m) ≠ 0 := by
        refine prodFn_ne_zero ha' fun n => ?_
        rcases eq_or_ne n m with rfl | hn
        · simp [a']
        · simp only [a', Function.update_of_ne hn, a]
          intro h
          exact hn (hinj ((mul_inv_eq_one₀ (hc0 n)).mp h).symm)
      have hder : HasDerivAt P (-(1 * a m) * prodFn a' (c m) +
          (1 - c m * a m) * deriv (prodFn a') (c m)) (c m) := by
        rw [hsplit]
        exact (((hasDerivAt_id' (c m)).mul_const (a m)).const_sub 1).mul
          (differentiable_prodFn ha' (c m)).hasDerivAt
      rw [hder.deriv, hca m, sub_self, zero_mul, add_zero, one_mul, neg_mul]
      exact neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero (hc0 m)) hQ)
    · push Not at hz
      have hza : ∀ n, z * a n ≠ 1 := fun n h =>
        hz n ((mul_inv_eq_one₀ (hc0 n)).mp h)
      have hPz : P z ≠ 0 := prodFn_ne_zero ha hza
      have hlog : logDeriv P z = FieldSum c z := by
        rw [logDeriv_prodFn ha hza, FieldSum]
        refine tsum_congr fun n => ?_
        have h1 : c n - z ≠ 0 := sub_ne_zero.mpr (hz n).symm
        have h2 : z - c n ≠ 0 := sub_ne_zero.mpr (hz n)
        have h3 := hc0 n
        simp only [a]
        field_simp
        ring
      have : deriv P z = P z * FieldSum c z := by
        rw [← hlog, logDeriv_apply]
        field_simp
      rw [this]
      exact mul_ne_zero hPz (hfield z hz)
  have hP'd : Differentiable ℂ (deriv P) := fun z => (hPd.analyticAt z).deriv.differentiableAt
  have hP'' : ∀ z, deriv (deriv P) z = 0 :=
    deriv_eq_zero_of_forall_norm_le_exp hP'd hP'ne fun ε hε => norm_deriv_prodFn_le ha hε
  have hconst : ∀ z, deriv P z = deriv P 0 := fun z => is_const_of_deriv_eq_zero hP'd hP'' z 0
  have hP0 : P 0 = 1 := by simp [P, prodFn]
  have haff : ∀ z, P z = 1 + deriv P 0 * z := by
    have hgd : Differentiable ℂ (fun w => P w - deriv P 0 * w) :=
      hPd.sub (differentiable_id.const_mul _)
    have hg : ∀ z, deriv (fun w => P w - deriv P 0 * w) z = 0 := by
      intro z
      have h : HasDerivAt (fun w => P w - deriv P 0 * w) (deriv P z - deriv P 0 * 1) z :=
        (hPd z).hasDerivAt.sub ((hasDerivAt_id' z).const_mul (deriv P 0))
      rw [h.deriv, hconst z, mul_one, sub_self]
    intro z
    have := is_const_of_deriv_eq_zero hgd hg z 0
    simp only [mul_zero, sub_zero, hP0] at this
    linear_combination this
  have hzero : ∀ m, P (c m) = 0 := fun m => prodFn_eq_zero (hca m)
  have h0 := haff (c 0)
  have h1 := haff (c 1)
  rw [hzero] at h0 h1
  have hne : c 0 - c 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by norm_num))
  have hα : deriv P 0 * (c 0 - c 1) = 0 := by linear_combination h1 - h0
  have hα0 : deriv P 0 = 0 := (mul_eq_zero.mp hα).resolve_right hne
  rw [hα0, zero_mul, add_zero] at h0
  exact zero_ne_one h0

end MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted
