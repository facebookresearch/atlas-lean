/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Instances.Matrix

/-!
# The confluent limit of `det (f_k(z_l)) / ∏_{k<l} (z_l - z_k)`

Let `f_0, …, f_{g-1}` be holomorphic near a point `a` of `ℂ`. As the pairwise distinct points
`z_0, …, z_{g-1}` tend to `a`, the quotient `det (f_k(z_l))_{k,l} / ∏_{k<l} (z_l - z_k)` tends to
the Wronskian-type determinant `det (f_k^{(l)}(a) / l!)_{k,l}`. This is the limit used by
R. de Jong, *Arakelov invariants of Riemann surfaces*, Doc. Math. 10 (2005), 311–329, in the proof
of Lemma 3.2 (p. 317, the second equality of the limit display), where the determinant
`W_z(ψ) = det((1/(l-1)!) d^{l-1}f_k/dz^{l-1})_{1≤k,l≤g}` is the one introduced on p. 314.

## Main results

* `Complex.tendsto_det_div_prod_sub`: the limit, along pairwise distinct tuples of points of an
  open set `U` on which the `f_k` are holomorphic.
* `Complex.tendsto_det_div_prod_sub_of_injective`: the same limit along all pairwise distinct
  tuples, for functions holomorphic on a neighbourhood of `a`.

## Proof

Write `f_k[z_0, …, z_j]` for divided differences, defined here by the Cauchy integral
`(2πi)⁻¹ ∮ f_k(ζ) / ∏_{i≤j} (ζ - z_i) dζ` over a fixed circle around `a`. Partial fractions and
Cauchy's integral formula give the Newton form
`f_k(z_l) = ∑_j f_k[z_0, …, z_j] ∏_{i<j} (z_l - z_i)`,
that is, `(f_k(z_l)) = D · N` with `D = (f_k[z_0, …, z_j])` and `N = (∏_{i<j} (z_l - z_i))` upper
triangular of determinant `∏_{k<l} (z_l - z_k)`. The integral is continuous in the nodes by
dominated convergence, and at the constant tuple it is the Taylor coefficient `f_k^{(j)}(a) / j!`.
-/

@[expose] public section

open Complex Finset Filter Topology Metric
open scoped Nat Real

namespace Complex.ConfluentDeterminant

/-- Telescoping identity behind the Newton form: for `ζ` different from every `y i`,
`(ζ - w) * ∑_{j<n} ∏_{i<j} (w - y i) / ∏_{i≤j} (ζ - y i) = 1 - ∏_{i<n} (w - y i) / (ζ - y i)`. -/
private theorem sub_mul_sum_prod_div_prod (w ζ : ℂ) (y : ℕ → ℂ) (hy : ∀ i, ζ ≠ y i) (n : ℕ) :
    (ζ - w) * ∑ j ∈ range n, (∏ i ∈ range j, (w - y i)) / ∏ i ∈ range (j + 1), (ζ - y i) =
      1 - ∏ i ∈ range n, ((w - y i) / (ζ - y i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∏ i ∈ range n, (ζ - y i) ≠ 0 :=
      prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (hy i)
    have h2 : ζ - y n ≠ 0 := sub_ne_zero.2 (hy n)
    rw [sum_range_succ, mul_add, ih, prod_range_succ (fun i => ζ - y i), prod_range_succ,
      prod_div_distrib]
    field_simp
    ring

/-- Partial fractions for the Cauchy kernel at a node: if `ζ` differs from all `z i`, then
`(ζ - z l)⁻¹ = ∑_j ∏_{i<j} (z l - z i) / ∏_{i≤j} (ζ - z i)`. -/
private theorem inv_sub_eq_sum {g : ℕ} (z : Fin g → ℂ) (ζ : ℂ) (hζ : ∀ i, ζ ≠ z i) (l : Fin g) :
    (ζ - z l)⁻¹ = ∑ j, (∏ i ∈ Iio j, (z l - z i)) / ∏ i ∈ Iic j, (ζ - z i) := by
  set y : ℕ → ℂ := fun i => if h : i < g then z ⟨i, h⟩ else ζ + 1
  have hyz : ∀ i : Fin g, y i = z i := fun i => by simp [y, i.isLt]
  have hy : ∀ i, ζ ≠ y i := by
    intro i
    by_cases h : i < g
    · simpa [y, h] using hζ ⟨i, h⟩
    · simp [y, h]
  have hIio : ∀ (j : Fin g) (F : ℕ → ℂ), ∏ i ∈ Iio j, F i = ∏ i ∈ range j, F i := by
    intro j F
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, prod_map]
    rfl
  have hIic : ∀ (j : Fin g) (F : ℕ → ℂ), ∏ i ∈ Iic j, F i = ∏ i ∈ range (j + 1), F i := by
    intro j F
    rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, prod_map]
    rfl
  have key := sub_mul_sum_prod_div_prod (z l) ζ y hy g
  have hzero : ∏ i ∈ range g, ((z l - y i) / (ζ - y i)) = 0 :=
    prod_eq_zero (mem_range.2 l.isLt) (by rw [hyz]; simp)
  have hsum : ∑ j : Fin g, (∏ i ∈ Iio j, (z l - z i)) / ∏ i ∈ Iic j, (ζ - z i) =
      ∑ j ∈ range g, (∏ i ∈ range j, (z l - y i)) / ∏ i ∈ range (j + 1), (ζ - y i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun j _ => ?_
    have e1 := hIio j (fun n => z l - y n)
    have e2 := hIic j (fun n => ζ - y n)
    simp only [hyz] at e1 e2
    rw [e1, e2]
  exact (eq_inv_of_mul_eq_one_right (by rw [hsum, key, hzero, sub_zero])).symm

/-- The circle integral of a finite sum of functions continuous on the circle is the sum of the
circle integrals. -/
private theorem circleIntegral_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hF : ∀ i ∈ s, ContinuousOn (F i) (sphere c R)) :
    ∮ z in C(c, R), ∑ i ∈ s, F i z = ∑ i ∈ s, ∮ z in C(c, R), F i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, ContinuousOn (F j) (sphere c R) := fun j hj => hF j (mem_insert_of_mem hj)
    simp only [sum_insert hi]
    rw [circleIntegral.integral_add ((hF i (mem_insert_self i s)).circleIntegrable hR)
      ((continuousOn_finsetSum s hs).circleIntegrable hR), ih hs]

/-- The divided difference `f[z 0, …, z j]` of `f`, given by the Cauchy integral
`(2πi)⁻¹ ∮_{|ζ - c| = R} f(ζ) / ∏_{i ≤ j} (ζ - z i) dζ`; it is meaningful when all `z i` lie
in the open disc `|z - c| < R` and `f` is holomorphic on the closed disc. -/
private noncomputable def dividedDiff (f : ℂ → ℂ) (c : ℂ) (R : ℝ) {g : ℕ} (z : Fin g → ℂ)
    (j : Fin g) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(c, R), f ζ / ∏ i ∈ Iic j, (ζ - z i)

/-- **Newton form.** If `f` is holomorphic on the closed disc `|z - c| ≤ R` and all `z i` lie in
the open disc, then `f (z l) = ∑_j f[z 0, …, z j] * ∏_{i<j} (z l - z i)`. -/
private theorem eq_sum_dividedDiff_mul {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) {g : ℕ} {z : Fin g → ℂ}
    (hz : ∀ i, z i ∈ ball c R) (l : Fin g) :
    f (z l) = ∑ j, dividedDiff f c R z j * ∏ i ∈ Iio j, (z l - z i) := by
  have hR : 0 < R := pos_of_mem_ball (hz l)
  have hne : ∀ ζ ∈ sphere c R, ∀ i, ζ ≠ z i := by
    intro ζ hζ i h
    have h1 := mem_ball.1 (hz i)
    rw [mem_sphere] at hζ
    rw [← h] at h1
    linarith
  have hcont : ∀ j : Fin g, ContinuousOn (fun ζ => f ζ / ∏ i ∈ Iic j, (ζ - z i)) (sphere c R) :=
    fun j => (hf.continuousOn.mono sphere_subset_closedBall).div
      (by fun_prop) (fun ζ hζ => prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (hne ζ hζ i))
  have hcauchy := hf.circleIntegral_sub_inv_smul (hz l)
  have hint : ∮ ζ in C(c, R), (ζ - z l)⁻¹ • f ζ =
      ∮ ζ in C(c, R), ∑ j, (∏ i ∈ Iio j, (z l - z i)) * (f ζ / ∏ i ∈ Iic j, (ζ - z i)) := by
    refine circleIntegral.integral_congr hR.le fun ζ hζ => ?_
    simp only [smul_eq_mul]
    rw [inv_sub_eq_sum z ζ (hne ζ hζ) l, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hint, circleIntegral_finset_sum
    (F := fun j ζ => (∏ i ∈ Iio j, (z l - z i)) * (f ζ / ∏ i ∈ Iic j, (ζ - z i))) _ hR.le
    (fun j _ => continuousOn_const.mul (hcont j))]
    at hcauchy
  simp only [circleIntegral.integral_const_mul, smul_eq_mul] at hcauchy
  have h2pi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  have : f (z l) = (2 * π * I)⁻¹ * ∑ j, (∏ i ∈ Iio j, (z l - z i)) *
      ∮ ζ in C(c, R), f ζ / ∏ i ∈ Iic j, (ζ - z i) := by
    rw [hcauchy]; field_simp
  rw [this, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  unfold dividedDiff
  ring

/-- The divided difference `f[z 0, …, z j]` is continuous in `z` at the constant tuple `c`. -/
private theorem continuousAt_dividedDiff {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere c R)) {g : ℕ} (j : Fin g) :
    ContinuousAt (fun z : Fin g → ℂ => dividedDiff f c R z j) (fun _ => c) := by
  unfold dividedDiff circleIntegral
  refine continuousAt_const.mul ?_
  obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hf
  have hev : ∀ᶠ z : Fin g → ℂ in 𝓝 (fun _ => c), ∀ i, z i ∈ ball c (R / 2) :=
    eventually_all.2 fun i =>
      (continuous_apply i).continuousAt.preimage_mem_nhds (ball_mem_nhds c (half_pos hR))
  have hlow : ∀ z : Fin g → ℂ, (∀ i, z i ∈ ball c (R / 2)) → ∀ θ : ℝ, ∀ i,
      R / 2 ≤ ‖circleMap c R θ - z i‖ := by
    intro z hz θ i
    have h1 : ‖circleMap c R θ - c‖ = R := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
    have h2 : ‖z i - c‖ < R / 2 := by simpa [dist_eq_norm] using hz i
    have h3 := norm_sub_norm_le (circleMap c R θ - c) (z i - c)
    rw [sub_sub_sub_cancel_right] at h3
    linarith
  have hfθ : Continuous fun θ => f (circleMap c R θ) :=
    hf.comp_continuous (continuous_circleMap c R) (fun θ => circleMap_mem_sphere c hR.le θ)
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => R * (M / (R / 2) ^ #(Iic j))) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hev] with z hz
    refine Continuous.aestronglyMeasurable ?_
    simp only [deriv_circleMap]
    refine ((continuous_circleMap 0 R).mul continuous_const).smul (hfθ.div (by fun_prop) ?_)
    intro θ
    exact prod_ne_zero_iff.2 fun i _ => norm_pos_iff.1 ((half_pos hR).trans_le (hlow z hz θ i))
  · filter_upwards [hev] with z hz
    refine MeasureTheory.ae_of_all _ fun θ _ => ?_
    rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one,
      abs_of_pos hR, norm_div, norm_prod]
    refine mul_le_mul_of_nonneg_left (div_le_div₀ ((norm_nonneg _).trans (hM _
      (circleMap_mem_sphere c hR.le θ))) (hM _ (circleMap_mem_sphere c hR.le θ))
      (pow_pos (half_pos hR) _) ?_) hR.le
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => (half_pos hR).le) fun i _ => hlow z hz θ i
  · refine MeasureTheory.ae_of_all _ fun θ _ => ?_
    have hden : ContinuousAt (fun x : Fin g → ℂ =>
        f (circleMap c R θ) / ∏ i ∈ Iic j, (circleMap c R θ - x i)) (fun _ => c) :=
      continuousAt_const.div (by fun_prop : Continuous fun x : Fin g → ℂ =>
        ∏ i ∈ Iic j, (circleMap c R θ - x i)).continuousAt
        (prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (circleMap_ne_center hR.ne'))
    exact hden.const_smul (deriv (circleMap c R) θ)

/-- At the constant tuple `c`, the divided difference `f[c, …, c]` (with `j + 1` entries) is
`f⁽ʲ⁾(c) / j!`. -/
private theorem dividedDiff_const {f : ℂ → ℂ} {c : ℂ} {R : NNReal} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) {g : ℕ} (j : Fin g) :
    dividedDiff f c R (fun _ => c) j = iteratedDeriv j f c / ((j : ℕ)! : ℂ) := by
  have h1 := (hf.hasFPowerSeriesOnBall hR).factorial_smul 1 j
  rw [← iteratedDeriv_eq_iteratedFDeriv, cauchyPowerSeries_apply] at h1
  rw [← h1, nsmul_eq_mul]
  unfold dividedDiff
  have hint : ∮ z in C(c, R), (1 / (z - c)) ^ (j : ℕ) • (z - c)⁻¹ • f z =
      ∮ ζ in C(c, R), f ζ / ∏ i ∈ Iic j, (ζ - c) := by
    congr 1
    ext ζ
    rw [prod_const, Fin.card_Iic]
    simp only [smul_eq_mul]
    generalize ζ - c = w
    ring
  rw [hint, smul_eq_mul]
  have : ((j : ℕ)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- The upper triangular matrix `(∏_{i<j} (z l - z i))_{j,l}` of the Newton basis evaluated at the
nodes has determinant `∏_{k<l} (z l - z k)`. -/
private theorem det_of_prod_Iio {g : ℕ} (z : Fin g → ℂ) :
    (Matrix.of fun j l : Fin g => ∏ i ∈ Iio j, (z l - z i)).det =
      ∏ k, ∏ l ∈ Ioi k, (z l - z k) := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp only [Matrix.of_apply]
    exact prod_comm' fun l i => by simp
  · intro j l hlj
    exact prod_eq_zero (mem_Iio.2 hlj) (sub_self _)

end Complex.ConfluentDeterminant

namespace Complex

open ConfluentDeterminant

/-- Let `f_0, …, f_{g-1}` be functions `ℂ → ℂ` that are holomorphic on a set `U` which is a
neighbourhood of `a`. Then, as `z = (z_0, …, z_{g-1})` tends to `(a, …, a)` through tuples of
pairwise distinct complex numbers (`Function.Injective z`),
`det (f_k(z_l))_{k,l} / ∏_{k<l} (z_l - z_k) → det (f_k^{(l)}(a) / l!)_{k,l}`,
where `f^{(l)} = iteratedDeriv l f` and the indices `k, l` run over `Fin g` (so `l` here is the
`l - 1` of de Jong's 1-based indexing). The points `z_l` are not required to lie in `U`, and
`g = 0` is allowed (both sides are then `1`). This is a slightly stronger form of
`Complex.tendsto_det_div_prod_sub`. -/
theorem tendsto_det_div_prod_sub_of_injective {g : ℕ} {f : Fin g → ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hU : U ∈ 𝓝 a) (hf : ∀ k, DifferentiableOn ℂ (f k) U) :
    Tendsto (fun z : Fin g → ℂ =>
        (Matrix.of fun k l => f k (z l)).det / ∏ k, ∏ l ∈ Ioi k, (z l - z k))
      (𝓝[{z | Function.Injective z}] fun _ => a)
      (𝓝 (Matrix.of fun k l : Fin g => iteratedDeriv l (f k) a / ((l : ℕ)! : ℂ)).det) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  let R : NNReal := ⟨ε / 2, (half_pos hε).le⟩
  have hR' : (0 : ℝ) < R := half_pos hε
  have hR : (0 : NNReal) < R := by exact_mod_cast hR'
  have hRε : (R : ℝ) < ε := half_lt_self hε
  have hfR : ∀ k, DifferentiableOn ℂ (f k) (closedBall a R) :=
    fun k => (hf k).mono ((closedBall_subset_ball hRε).trans hεU)
  let D : (Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun z => Matrix.of fun k j => dividedDiff (f k) a R z j
  have hD : Tendsto D (𝓝 (fun _ => a)) (𝓝 (D fun _ => a)) := by
    have : ContinuousAt D (fun _ => a) := continuousAt_pi.2 fun k => continuousAt_pi.2 fun j =>
      continuousAt_dividedDiff hR' ((hfR k).continuousOn.mono sphere_subset_closedBall) j
    exact this
  have hlim : D (fun _ => a) =
      Matrix.of fun k l : Fin g => iteratedDeriv l (f k) a / ((l : ℕ)! : ℂ) := by
    ext k l
    exact dividedDiff_const hR (hfR k) l
  have h1 : ∀ᶠ z in 𝓝 (fun _ : Fin g => a), ∀ i, z i ∈ ball a R :=
    eventually_all.2 fun i =>
      (continuous_apply i).continuousAt.preimage_mem_nhds (ball_mem_nhds a hR')
  have hev : (fun z => (D z).det) =ᶠ[𝓝[{z | Function.Injective z}] fun _ => a]
      fun z : Fin g → ℂ =>
        (Matrix.of fun k l => f k (z l)).det / ∏ k, ∏ l ∈ Ioi k, (z l - z k) := by
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hinj
    have hmat : (Matrix.of fun k l => f k (z l)) =
        D z * Matrix.of fun j l => ∏ i ∈ Iio j, (z l - z i) := by
      ext k l
      simp only [Matrix.mul_apply, Matrix.of_apply, D]
      exact eq_sum_dividedDiff_mul (hfR k) hz l
    have hne : ∏ k, ∏ l ∈ Ioi k, (z l - z k) ≠ 0 :=
      prod_ne_zero_iff.2 fun k _ => prod_ne_zero_iff.2 fun l hl =>
        sub_ne_zero.2 (hinj.ne (ne_of_gt (mem_Ioi.1 hl)))
    rw [hmat, Matrix.det_mul, det_of_prod_Iio, mul_div_cancel_right₀ _ hne]
  rw [← hlim]
  exact ((continuous_id.matrix_det.tendsto _).comp (hD.mono_left nhdsWithin_le_nhds)).congr' hev

/-- **The confluent determinant limit** (R. de Jong, *Arakelov invariants of Riemann surfaces*,
Doc. Math. 10 (2005), proof of Lemma 3.2, p. 317, second equality of the limit display; the
determinant `W_z` is defined on p. 314).

Let `U ⊆ ℂ` be open, `a ∈ U`, and `f_0, …, f_{g-1}` holomorphic on `U`. Then, as
`z = (z_0, …, z_{g-1})` tends to `(a, …, a)` through tuples of pairwise distinct points of `U`,
`det (f_k(z_l))_{k,l} / ∏_{k<l} (z_l - z_k) → det (f_k^{(l)}(a) / l!)_{k,l}`,
where `f^{(l)} = iteratedDeriv l f` and `k, l` run over `Fin g`, so the column index `l` here is
de Jong's `l - 1`. The hypothesis `g ≥ 1` of the source is not needed (for `g = 0` both sides are
`1`). De Jong states the limit for absolute values, `|det| / ∏_{k<l} |z_k - z_l| → |W_z|`; the
signed limit proved here implies it. -/
theorem tendsto_det_div_prod_sub {g : ℕ} {f : Fin g → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} (ha : a ∈ U) (hf : ∀ k, DifferentiableOn ℂ (f k) U) :
    Tendsto (fun z : Fin g → ℂ =>
        (Matrix.of fun k l => f k (z l)).det / ∏ k, ∏ l with k < l, (z l - z k))
      (𝓝[{z | Function.Injective z ∧ ∀ l, z l ∈ U}] fun _ => a)
      (𝓝 (Matrix.of fun k l : Fin g => iteratedDeriv l (f k) a / ((l : ℕ)! : ℂ)).det) := by
  simp only [filter_lt_eq_Ioi]
  exact (tendsto_det_div_prod_sub_of_injective (hU.mem_nhds ha) hf).mono_left
    (nhdsWithin_mono _ fun z hz => hz.1)

end Complex
