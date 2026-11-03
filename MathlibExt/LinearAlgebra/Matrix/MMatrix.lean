/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Ring.GeomSum

/-!
# Hurwitz matrices and nonsingular M-matrices

A real square matrix is *Hurwitz* (stable) if every complex eigenvalue has negative real part.
A *Z-matrix* has nonpositive off-diagonal entries, and a *nonsingular M-matrix* is a Z-matrix
whose complex eigenvalues all have positive real part, i.e. a Z-matrix `V` with `-V` Hurwitz.
This is condition (G20) in Berman–Plemmons' list of equivalent definitions; the usual
definition `V = s I - P` with `P ≥ 0` entrywise and `s > ρ(P)` is equivalent to it.

The spectral radius of a real matrix `K` is `spectralRadius ℂ (K.map (algebraMap ℝ ℂ))`, the
largest modulus of a complex eigenvalue (an element of `ℝ≥0∞`, finite for matrices; Mathlib
takes the supremum over the quasispectrum, which adds `0` and so changes nothing).

## Main results

* `Matrix.isUnit_one_sub_of_spectralRadius_lt_one`, `Matrix.inv_one_sub_nonneg`: if `K` has
  spectral radius `< 1`, then `1 - K` is invertible, and if moreover `K` is entrywise
  nonnegative, so is `(1 - K)⁻¹` (Neumann series; `Kⁿ → 0` by Gelfand's formula).
* `Matrix.le_spectralRadius_of_smul_le_mulVec`: the Collatz–Wielandt lower bound: if
  `K ≥ 0`, `z ≥ 0`, `z ≠ 0` and `r z ≤ K z` with `r ≥ 0`, then `r ≤ ρ(K)`.
* `Matrix.IsNonsingularMMatrix.isUnit`, `Matrix.IsNonsingularMMatrix.inv_nonneg`: a
  nonsingular M-matrix is invertible and its inverse is entrywise nonnegative.

## References

* A. Berman and R. J. Plemmons, *Nonnegative Matrices in the Mathematical Sciences*, Academic
  Press (1979), Ch. 6, Theorem 2.3.
* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press (1991),
  §2.5.
-/

@[expose] public section

open scoped ENNReal NNReal
open Filter Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real square matrix is **Hurwitz** if every complex eigenvalue has negative real part. -/
def IsHurwitz (A : Matrix ι ι ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), μ.re < 0

/-- A **Z-matrix** has nonpositive off-diagonal entries. -/
def IsZMatrix (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → A i j ≤ 0

/-- A **nonsingular M-matrix** is a Z-matrix all of whose complex eigenvalues have positive
real part (Berman–Plemmons, Ch. 6, Theorem 2.3, condition (G20)). -/
def IsNonsingularMMatrix (A : Matrix ι ι ℝ) : Prop :=
  A.IsZMatrix ∧ (-A).IsHurwitz

/-- If `ρ(a) < r`, then `r⁻ⁿ aⁿ → 0` (Gelfand's formula). -/
private theorem tendsto_smul_pow_zero (a : Matrix ι ι ℂ) {r : ℝ≥0} (hr : 0 < r)
    (h : spectralRadius ℂ a < r) :
    Tendsto (fun n : ℕ => ((r : ℂ)⁻¹) ^ n • a ^ n) atTop (𝓝 0) := by
  let _ : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  obtain ⟨r', hρr, hr1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  have hr1' : r' < r := by exact_mod_cast hr1
  have hev : ∀ᶠ n : ℕ in atTop, (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) < r' :=
    (spectrum.gelfand_formula a).eventually (gt_mem_nhds hρr)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hle : ∀ᶠ n : ℕ in atTop, ‖((r : ℂ)⁻¹) ^ n • a ^ n‖ ≤ ((r' : ℝ) / r) ^ n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h2 : (‖a ^ n‖₊ : ℝ≥0∞) < (r' : ℝ≥0∞) ^ n := by
      have := ENNReal.rpow_lt_rpow hn hnpos
      rwa [← ENNReal.rpow_mul, one_div_mul_cancel hnpos.ne', ENNReal.rpow_one,
        ENNReal.rpow_natCast] at this
    have h3 : ‖a ^ n‖ ≤ (r' : ℝ) ^ n := by
      have : ‖a ^ n‖₊ < r' ^ n := by exact_mod_cast h2
      exact_mod_cast this.le
    rw [norm_smul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrpos, div_pow, div_eq_inv_mul, inv_pow]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  refine squeeze_zero_norm' hle (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_)
  rw [div_lt_one hrpos]
  exact_mod_cast hr1'

/-- The real version: if `ρ(K) < r`, then `r⁻ⁿ Kⁿ → 0`. -/
private theorem tendsto_smul_pow_zero_real (K : Matrix ι ι ℝ) {r : ℝ≥0} (hr : 0 < r)
    (h : spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) < r) :
    Tendsto (fun n : ℕ => ((r : ℝ)⁻¹) ^ n • K ^ n) atTop (𝓝 0) := by
  have hc := tendsto_smul_pow_zero _ hr h
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hcont : Continuous fun M : Matrix ι ι ℂ => (M i j).re :=
    Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))
  have e : ∀ n : ℕ, K.map (algebraMap ℝ ℂ) ^ n = (K ^ n).map (algebraMap ℝ ℂ) := fun n => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  have := (hcont.tendsto _).comp hc
  simp only [Function.comp_def, e, Matrix.smul_apply, Matrix.map_apply] at this
  simpa [← Complex.ofReal_inv, ← Complex.ofReal_pow] using this

/-- If the spectral radius of `K` is `< 1`, then `1` is not an eigenvalue of `K`, so `1 - K`
is invertible. -/
theorem isUnit_one_sub_of_spectralRadius_lt_one {K : Matrix ι ι ℝ}
    (hK : spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) < 1) : IsUnit (1 - K) := by
  have hn : (1 : ℂ) ∉ spectrum ℂ (K.map (algebraMap ℝ ℂ)) := by
    intro h1
    have : ((‖(1 : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) ≤ spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) :=
      le_iSup₂ (f := fun k (_ : k ∈ quasispectrum ℂ (K.map (algebraMap ℝ ℂ))) =>
        ((‖k‖₊ : ℝ≥0) : ℝ≥0∞)) 1 (spectrum_subset_quasispectrum ℂ _ h1)
    rw [nnnorm_one, ENNReal.coe_one] at this
    exact absurd hK (not_lt.2 this)
  rw [spectrum.notMem_iff] at hn
  have hmap : algebraMap ℂ (Matrix ι ι ℂ) 1 - K.map (algebraMap ℝ ℂ) =
      (1 - K).map (algebraMap ℝ ℂ) := by
    rw [map_one, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hmap, Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hn
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  rw [h0, map_zero] at hn
  exact not_isUnit_zero hn

/-- **Neumann series.** If `K` is entrywise nonnegative with spectral radius `< 1`, then
`(1 - K)⁻¹` is entrywise nonnegative (the proof identifies it with the limit of the partial
sums `∑_{n<N} Kⁿ`). -/
theorem inv_one_sub_nonneg {K : Matrix ι ι ℝ} (hK0 : ∀ i j, 0 ≤ K i j)
    (hK : spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) < 1) (i j : ι) :
    0 ≤ (1 - K)⁻¹ i j := by
  have hu := isUnit_one_sub_of_spectralRadius_lt_one hK
  have hdet : IsUnit (1 - K).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  set S : ℕ → Matrix ι ι ℝ := fun N => ∑ k ∈ Finset.range N, K ^ k
  have hS : ∀ N, S N = (1 - K)⁻¹ * (1 - K ^ N) := by
    intro N
    rw [← mul_neg_geom_sum, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hpow : Tendsto (fun n : ℕ => K ^ n) atTop (𝓝 0) := by
    simpa using tendsto_smul_pow_zero_real K one_pos (by simpa using hK)
  have hlim : Tendsto S atTop (𝓝 ((1 - K)⁻¹ * (1 - 0))) := by
    refine Tendsto.congr (fun N => (hS N).symm) ?_
    exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hpow)
  rw [sub_zero, Matrix.mul_one] at hlim
  have hij : Tendsto (fun N => S N i j) atTop (𝓝 ((1 - K)⁻¹ i j)) :=
    have hc : Continuous fun M : Matrix ι ι ℝ => M i j :=
      (continuous_apply j).comp (continuous_apply i)
    (hc.tendsto _).comp hlim
  refine ge_of_tendsto hij (Eventually.of_forall fun N => ?_)
  simp only [S, Matrix.sum_apply]
  exact Finset.sum_nonneg fun k _ => pow_apply_nonneg hK0 k i j

omit [DecidableEq ι] in
/-- **Collatz–Wielandt lower bound.** If `K ≥ 0` entrywise, `z ≥ 0`, `z ≠ 0` and
`r • z ≤ K *ᵥ z` with `r ≥ 0`, then `r` is at most the spectral radius of `K`. -/
theorem le_spectralRadius_of_smul_le_mulVec {K : Matrix ι ι ℝ} (hK0 : ∀ i j, 0 ≤ K i j)
    {z : ι → ℝ} (hz : 0 ≤ z) (hz0 : z ≠ 0) {r : ℝ} (hr : 0 ≤ r) (h : r • z ≤ K *ᵥ z) :
    ENNReal.ofReal r ≤ spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) := by
  classical
  rcases hr.eq_or_lt with rfl | hr
  · simp
  by_contra hlt
  push Not at hlt
  have hmono : ∀ {u w : ι → ℝ}, u ≤ w → K *ᵥ u ≤ K *ᵥ w := fun huw i =>
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (huw l) (hK0 i l)
  have hpow : ∀ n : ℕ, r ^ n • z ≤ K ^ n *ᵥ z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc r ^ (n + 1) • z = r ^ n • (r • z) := by rw [pow_succ, mul_smul]
        _ ≤ r ^ n • (K *ᵥ z) := smul_le_smul_of_nonneg_left h (by positivity)
        _ = K *ᵥ (r ^ n • z) := by rw [Matrix.mulVec_smul]
        _ ≤ K *ᵥ (K ^ n *ᵥ z) := hmono ih
        _ = K ^ (n + 1) *ᵥ z := by rw [Matrix.mulVec_mulVec, pow_succ']
  have hT := tendsto_smul_pow_zero_real K (r := r.toNNReal) (Real.toNNReal_pos.2 hr) hlt
  have hTz : Tendsto (fun n : ℕ => (((r.toNNReal : ℝ))⁻¹ ^ n • K ^ n) *ᵥ z) atTop (𝓝 (0 *ᵥ z)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp hT
  rw [Matrix.zero_mulVec, Real.coe_toNNReal _ hr.le] at hTz
  have hle : ∀ n : ℕ, z ≤ ((r⁻¹ ^ n • K ^ n) *ᵥ z) := by
    intro n
    rw [Matrix.smul_mulVec]
    calc z = r⁻¹ ^ n • (r ^ n • z) := by
          rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_smul]
      _ ≤ r⁻¹ ^ n • (K ^ n *ᵥ z) := smul_le_smul_of_nonneg_left (hpow n) (by positivity)
  apply hz0
  funext i
  have hi : Tendsto (fun n : ℕ => ((r⁻¹ ^ n • K ^ n) *ᵥ z) i) atTop (𝓝 0) :=
    ((continuous_apply i).tendsto _).comp hTz
  exact le_antisymm (ge_of_tendsto' hi fun n => hle n i) (hz i)

/-- For a nonsingular M-matrix `A` there is `h > 0` with `1 - h A ≥ 0` entrywise and of
spectral radius `< 1`. -/
private theorem exists_one_sub_smul_nonneg {A : Matrix ι ι ℝ} (hA : A.IsNonsingularMMatrix) :
    ∃ h : ℝ, 0 < h ∧ (∀ i j, 0 ≤ (1 - h • A) i j) ∧
      spectralRadius ℂ ((1 - h • A).map (algebraMap ℝ ℂ)) < 1 := by
  obtain ⟨hZ, hH⟩ := hA
  set a := A.map (algebraMap ℝ ℂ)
  have hre : ∀ μ ∈ spectrum ℂ a, 0 < μ.re := by
    intro μ hμ
    have hneg : -μ ∈ spectrum ℂ ((-A).map (algebraMap ℝ ℂ)) := by
      rw [Matrix.map_neg _ (map_neg _), ← spectrum.neg_eq]
      exact Set.neg_mem_neg.2 hμ
    have := hH _ hneg
    simp at this
    linarith
  set T := a.charpoly.roots.toFinset
  have hT : ∀ μ, μ ∈ spectrum ℂ a ↔ μ ∈ T := by
    intro μ
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Multiset.mem_toFinset,
      Polynomial.mem_roots a.charpoly_monic.ne_zero]
  set c : ℝ := 1 + ∑ i, |A i i| + ∑ μ ∈ T, ‖μ‖ ^ 2 / μ.re
  have hsumT : 0 ≤ ∑ μ ∈ T, ‖μ‖ ^ 2 / μ.re :=
    Finset.sum_nonneg fun μ hμ => div_nonneg (sq_nonneg _) (hre μ ((hT μ).2 hμ)).le
  have hsumA : 0 ≤ ∑ i, |A i i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hc : 0 < c := by positivity
  refine ⟨1 / c, by positivity, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst hij
      have hle : |A i i| ≤ ∑ i, |A i i| :=
        Finset.single_le_sum (f := fun i => |A i i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      have : c⁻¹ * A i i < 1 := by
        rw [← div_eq_inv_mul, div_lt_one hc]
        linarith [le_abs_self (A i i)]
      simp [Matrix.sub_apply]
      linarith
    · have := hZ i j hij
      simp only [one_div, sub_apply, smul_apply, smul_eq_mul, sub_nonneg, one_apply_ne hij]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  · let _ : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
    have _ : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
    have hcC : ((1 / c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1 / c : ℝ) ≠ 0)
    have hB : (1 - (1 / c) • A).map (algebraMap ℝ ℂ) =
        algebraMap ℂ (Matrix ι ι ℂ) 1 - (Units.mk0 _ hcC) • a := by
      ext i j
      simp [a, Matrix.sub_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [hB]
    refine spectralRadius_lt_of_forall_quasispectrum_lt fun ν hν => ?_
    rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, ← spectrum.singleton_sub_eq,
      spectrum.unit_smul_eq_smul] at hν
    rcases hν with hν | hν
    · obtain ⟨_, rfl, _, ⟨μ, hμ, rfl⟩, rfl⟩ := hν
      have hμre := hre μ hμ
      have hμT : ‖μ‖ ^ 2 / μ.re ≤ ∑ μ ∈ T, ‖μ‖ ^ 2 / μ.re :=
        Finset.single_le_sum (f := fun μ => ‖μ‖ ^ 2 / μ.re)
          (fun μ hμ => div_nonneg (sq_nonneg _) (hre μ ((hT μ).2 hμ)).le) ((hT μ).1 hμ)
      have hlt : ‖μ‖ ^ 2 < c * μ.re := by
        rw [div_le_iff₀ hμre] at hμT
        nlinarith
      have hval : (fun x1 x2 : ℂ => x1 - x2) 1 ((fun x : ℂ => ((Units.mk0 _ hcC : ℂˣ) : ℂ) • x) μ)
          = 1 - ((1 / c : ℝ) : ℂ) * μ := by
        simp
      rw [hval]
      have hnorm : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hns : ‖1 - ((1 / c : ℝ) : ℂ) * μ‖ ^ 2 < 1 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
        have hcinv : 0 < 1 / c := by positivity
        have h1 : 1 / c * ‖μ‖ ^ 2 < μ.re := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hc]; linarith
        have h2 := mul_lt_mul_of_pos_left h1 hcinv
        rw [hnorm] at h2
        nlinarith [mul_pos hcinv hμre]
      have : ‖1 - ((1 / c : ℝ) : ℂ) * μ‖ < 1 := (sq_lt_one_iff₀ (norm_nonneg _)).1 hns
      rw [← NNReal.coe_lt_coe, coe_nnnorm]
      simpa using this
    · rw [Set.mem_singleton_iff] at hν
      simp [hν]

/-- A nonsingular M-matrix is invertible. -/
theorem IsNonsingularMMatrix.isUnit {A : Matrix ι ι ℝ} (hA : A.IsNonsingularMMatrix) :
    IsUnit A := by
  obtain ⟨h, hh, -, hBρ⟩ := exists_one_sub_smul_nonneg hA
  have hu := isUnit_one_sub_of_spectralRadius_lt_one hBρ
  rw [show 1 - (1 - h • A) = h • A by abel, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul,
    isUnit_iff_ne_zero] at hu
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact right_ne_zero_of_mul hu

/-- **Inverse positivity of M-matrices.** The inverse of a nonsingular M-matrix is entrywise
nonnegative (Berman–Plemmons, Ch. 6, Theorem 2.3, (G20) ⇒ (N38)). -/
theorem IsNonsingularMMatrix.inv_nonneg {A : Matrix ι ι ℝ} (hA : A.IsNonsingularMMatrix)
    (i j : ι) : 0 ≤ A⁻¹ i j := by
  obtain ⟨h, hh, hB0, hBρ⟩ := exists_one_sub_smul_nonneg hA
  have hu := isUnit_one_sub_of_spectralRadius_lt_one hBρ
  have e : 1 - (1 - h • A) = h • A := by abel
  rw [e] at hu
  have hdet : IsUnit (h • A).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hinv : A⁻¹ = h • (1 - (1 - h • A))⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [e, Matrix.smul_mul, ← Matrix.mul_smul, Matrix.nonsing_inv_mul _ hdet]
  rw [hinv, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg hh.le (inv_one_sub_nonneg hB0 hBρ i j)

end Matrix
