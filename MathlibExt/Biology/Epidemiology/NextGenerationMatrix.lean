/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.LinearizedStability
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Matrix.Normed

/-!
# The next-generation matrix and the threshold `R₀ = ρ(F V⁻¹)`

In a compartmental epidemic model `x' = f(x)` with `m` infected compartments, write the
infected part as `f_i = ℱ_i - 𝒱_i`, where `ℱ_i` is the rate of appearance of new infections in
compartment `i` and `𝒱_i` the net rate of all other transfers. At a disease-free equilibrium
`x₀`, van den Driessche and Watmough (2002) set `F = (∂ℱ_i/∂x_j(x₀))` and
`V = (∂𝒱_i/∂x_j(x₀))` (`1 ≤ i, j ≤ m`); under their assumptions (A1)–(A5), `F` is entrywise
nonnegative, `V` is a nonsingular M-matrix, and (their Lemma 1) the Jacobian at `x₀` is block
lower triangular,

  `Df(x₀) = [[F - V, 0], [C, D]]`,

where the block `D` of the uninfected compartments is Hurwitz by their assumption (A5). The
**next-generation matrix** is `F V⁻¹`, whose `(i, k)` entry is the expected number of new
infections in compartment `i` produced by an individual introduced into compartment `k`, and
the **basic reproduction number** is its spectral radius `R₀ = ρ(F V⁻¹)`.

## Main results

* `R0`: `R₀ = ρ(F V⁻¹)`.
* `mem_spectrum_fromBlocks_zero₁₂`, `isHurwitz_fromBlocks_zero₁₂_iff`: the eigenvalues of a
  block lower-triangular matrix are those of its diagonal blocks.
* `isHurwitz_sub_iff_R0_lt_one`: for `F ≥ 0` and `V` a nonsingular M-matrix, all
  eigenvalues of `F - V` have negative real part iff `R₀ < 1`.
* `exists_re_pos_iff_one_lt_R0`: `F - V` has an eigenvalue with positive real part iff
  `R₀ > 1`.
* `globalSolution_decay_of_R0_lt_one`: Theorem 2 of van den Driessche–Watmough,
  stability half, conditional decay form: if `R₀ < 1`, every global solution starting near
  the disease-free equilibrium decays exponentially. This is not by itself local stability,
  since solution existence is not proved here.
* `exists_re_pos_jacobian_of_one_lt_R0`: Theorem 2, instability half, in spectral form: if
  `R₀ > 1`, the Jacobian at the disease-free equilibrium has an eigenvalue with positive real
  part. The nonlinear conclusion (instability of the equilibrium) additionally needs Lyapunov's
  instability theorem, which is not proved here.

The proofs use the M-matrix facts of `MathlibExt.LinearAlgebra.Matrix.MMatrix` (inverse
positivity, Neumann series, Collatz–Wielandt bound) and need no Perron–Frobenius theorem.

## References

* P. van den Driessche and J. Watmough, *Reproduction numbers and sub-threshold endemic
  equilibria for compartmental models of disease transmission*, Math. Biosci. 180 (2002)
  29–48, Lemma 1 and Theorem 2.
* O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, *On the definition and the computation
  of the basic reproduction ratio `R₀` in models for infectious diseases in heterogeneous
  populations*, J. Math. Biol. 28 (1990) 365–382.
-/

@[expose] public section

open Matrix Filter Topology
open scoped ENNReal NNReal

namespace MathlibExt.Biology.Epidemiology.NextGenerationMatrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### Auxiliary lemmas -/

/-- An eigenvalue of a complex matrix has an eigenvector. -/
private theorem exists_eigenvector {M : Matrix ι ι ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ M) :
    ∃ x : ι → ℂ, x ≠ 0 ∧ M *ᵥ x = μ • x := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  exact ⟨x, hx.2, by simpa [Module.End.mem_eigenspace_iff] using hx.1⟩

/-- The entrywise modulus of a complex vector. -/
private noncomputable def absVec (x : ι → ℂ) : ι → ℝ := fun i => ‖x i‖

omit [Fintype ι] [DecidableEq ι] in
private theorem absVec_nonneg (x : ι → ℂ) : 0 ≤ absVec x := fun _ => norm_nonneg _

omit [Fintype ι] [DecidableEq ι] in
private theorem absVec_ne_zero {x : ι → ℂ} (hx : x ≠ 0) : absVec x ≠ 0 := by
  intro h
  apply hx
  funext i
  simpa [absVec] using congr_fun h i

omit [DecidableEq ι] in
/-- For a real `K ≥ 0` and `K x = μ x`: `‖μ‖ |x| ≤ K |x|` (triangle inequality). -/
private theorem norm_smul_absVec_le {K : Matrix ι ι ℝ} (hK : ∀ i j, 0 ≤ K i j) {x : ι → ℂ}
    {μ : ℂ} (h : K.map (algebraMap ℝ ℂ) *ᵥ x = μ • x) : ‖μ‖ • absVec x ≤ K *ᵥ absVec x := by
  intro i
  have hi := congr_fun h i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hi
  calc (‖μ‖ • absVec x) i = ‖μ * x i‖ := by simp [absVec]
    _ = ‖∑ j, (K i j : ℂ) * x j‖ := by rw [← hi]; rfl
    _ ≤ ∑ j, ‖(K i j : ℂ) * x j‖ := norm_sum_le _ _
    _ = (K *ᵥ absVec x) i := by
      simp [Matrix.mulVec, dotProduct, absVec, Complex.norm_real, abs_of_nonneg (hK _ _)]

omit [DecidableEq ι] in
/-- Multiplication by an entrywise nonnegative matrix is monotone. -/
private theorem mulVec_mono {K : Matrix ι ι ℝ} (hK : ∀ i j, 0 ≤ K i j) {u w : ι → ℝ}
    (h : u ≤ w) : K *ᵥ u ≤ K *ᵥ w := fun i =>
  Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hK i l)

omit [DecidableEq ι] in
/-- The product of entrywise nonnegative matrices is entrywise nonnegative. -/
private theorem mul_nonneg' {A B : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j) (i j : ι) : 0 ≤ (A * B) i j :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hA i l) (hB l j)

omit [DecidableEq ι] in
/-- The spectral radius of a matrix is finite. -/
private theorem spectralRadius_ne_top (M : Matrix ι ι ℂ) : spectralRadius ℂ M ≠ ⊤ := by
  classical
  let _ : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm M)

/-- `ρ(V⁻¹ F) = ρ(F V⁻¹)` for invertible `V`. -/
private theorem spectralRadius_inv_mul {F V : Matrix ι ι ℝ} (hV : IsUnit V) :
    spectralRadius ℂ ((V⁻¹ * F).map (algebraMap ℝ ℂ)) =
      spectralRadius ℂ ((F * V⁻¹).map (algebraMap ℝ ℂ)) := by
  set f := (algebraMap ℝ ℂ).mapMatrix (m := ι)
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).1 hV
  have hW : IsUnit (f V) := hV.map f
  have hinv : f V⁻¹ = (f V)⁻¹ :=
    (Matrix.inv_eq_left_inv (by rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one])).symm
  have hσ : spectrum ℂ (f (V⁻¹ * F)) = spectrum ℂ (f (F * V⁻¹)) := by
    have h : f (V⁻¹ * F) = ((hW.unit⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) * f (F * V⁻¹) *
        ((hW.unit : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) := by
      rw [Matrix.coe_units_inv, IsUnit.unit_spec, map_mul, map_mul, hinv]
      simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hW)]
    rw [h, spectrum.units_conjugate']
  simp only [f, RingHom.mapMatrix_apply] at hσ
  simp only [spectralRadius, quasispectrum_eq_spectrum_union_zero, hσ]

omit [Fintype ι] in
/-- Write a Z-matrix as `V = c 1 - B` with `c > 0` and `B ≥ 0`. -/
private theorem exists_smul_one_sub [Finite ι] {V : Matrix ι ι ℝ} (hV : V.IsZMatrix) :
    ∃ c : ℝ, 0 < c ∧ ∀ i j, 0 ≤ (c • 1 - V) i j := by
  have := Fintype.ofFinite ι
  refine ⟨1 + ∑ i, |V i i|, by positivity, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    have : |V i i| ≤ ∑ i, |V i i| :=
      Finset.single_le_sum (f := fun i => |V i i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    linarith [le_abs_self (V i i)]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul,
      mul_zero, zero_sub, neg_nonneg]
    exact hV i j hij

/-- **Key inequality.** If `(F - V) x = μ x` with `F ≥ 0`, `V = c 1 - B`, `B ≥ 0`, then
`(V + Re μ) |x| ≤ F |x|`. -/
private theorem add_re_smul_le {F V : Matrix ι ι ℝ} (hF : ∀ i j, 0 ≤ F i j) {c : ℝ}
    (hB : ∀ i j, 0 ≤ (c • 1 - V) i j) {x : ι → ℂ} {μ : ℂ}
    (h : (F - V).map (algebraMap ℝ ℂ) *ᵥ x = μ • x) :
    V *ᵥ absVec x + μ.re • absVec x ≤ F *ᵥ absVec x := by
  have hFB : (F + (c • 1 - V)).map (algebraMap ℝ ℂ) *ᵥ x = (μ + c) • x := by
    have : (F + (c • 1 - V)).map (algebraMap ℝ ℂ) = (F - V).map (algebraMap ℝ ℂ) +
        (c : ℂ) • (1 : Matrix ι ι ℂ) := by
      ext i j
      by_cases hij : i = j <;> simp [hij] <;> ring
    rw [this, Matrix.add_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, add_smul]
  have hK : ∀ i j, 0 ≤ (F + (c • 1 - V)) i j := fun i j => add_nonneg (hF i j) (hB i j)
  have key := norm_smul_absVec_le hK hFB
  have hnorm : c + μ.re ≤ ‖μ + c‖ := by
    calc c + μ.re = (μ + c).re := by simp; ring
      _ ≤ ‖μ + c‖ := Complex.re_le_norm _
  intro i
  have hi := key i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.add_mulVec, Pi.add_apply,
    Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec] at hi ⊢
  have := mul_le_mul_of_nonneg_right hnorm (absVec_nonneg x i)
  nlinarith

/-- If `F ≥ 0`, `V` is a nonsingular M-matrix and `F - V` is Hurwitz, then `z ≥ 0` and
`z ≤ F V⁻¹ z` force `z = 0` (because `(1 - F V⁻¹)⁻¹ = 1 + F (V - F)⁻¹ ≥ 0`). -/
private theorem eq_zero_of_le_mulVec {F V : Matrix ι ι ℝ} (hF : ∀ i j, 0 ≤ F i j)
    (hV : V.IsNonsingularMMatrix) (hH : (F - V).IsHurwitz) {z : ι → ℝ} (hz : 0 ≤ z)
    (h : z ≤ (F * V⁻¹) *ᵥ z) : z = 0 := by
  have hVF : (V - F).IsNonsingularMMatrix := by
    refine ⟨fun i j hij => ?_, by rwa [neg_sub]⟩
    simp only [Matrix.sub_apply]
    linarith [hV.1 i j hij, hF i j]
  have hdV : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).1 hV.isUnit
  have hdVF : IsUnit (V - F).det := (Matrix.isUnit_iff_isUnit_det _).1 hVF.isUnit
  set N := 1 + F * (V - F)⁻¹
  have hN : ∀ i j, 0 ≤ N i j := fun i j => by
    refine add_nonneg ?_ (mul_nonneg' hF hVF.inv_nonneg i j)
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  have hNK : N * (1 - F * V⁻¹) = 1 := by
    rw [mul_eq_one_comm]
    have h1 : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul _ hdV
    have h2 : (V - F) * (V - F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdVF
    calc (1 - F * V⁻¹) * N
        = 1 - F * V⁻¹ + (F * (V⁻¹ * V) * (V - F)⁻¹ - F * V⁻¹ * F * (V - F)⁻¹) := by
          rw [h1, Matrix.mul_one]; simp only [N]; noncomm_ring
      _ = 1 - F * V⁻¹ + F * V⁻¹ * ((V - F) * (V - F)⁻¹) := by noncomm_ring
      _ = 1 := by rw [h2]; noncomm_ring
  have hle : (1 - F * V⁻¹) *ᵥ z ≤ 0 := by
    intro i
    have := h i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply]
    linarith
  have hz0 : z ≤ 0 := by
    have := mulVec_mono hN hle
    rwa [Matrix.mulVec_mulVec, hNK, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact le_antisymm hz0 hz

/-- Shifting a matrix whose eigenvalues have nonpositive real part by `-ε` (`ε > 0`) gives a
Hurwitz matrix. -/
private theorem isHurwitz_sub_smul_one {A : Matrix ι ι ℝ}
    (hA : ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), μ.re ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    (A - ε • 1).IsHurwitz := by
  intro μ hμ
  have e : (A - ε • 1).map (algebraMap ℝ ℂ) =
      A.map (algebraMap ℝ ℂ) - algebraMap ℂ (Matrix ι ι ℂ) (ε : ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  rw [e, ← spectrum.sub_singleton_eq] at hμ
  obtain ⟨ν, hν, _, rfl, rfl⟩ := hμ
  have := hA ν hν
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

/-- Adding `ε • 1` (`ε > 0`) to a nonsingular M-matrix gives a nonsingular M-matrix. -/
private theorem isNonsingularMMatrix_add_smul_one {V : Matrix ι ι ℝ}
    (hV : V.IsNonsingularMMatrix) {ε : ℝ} (hε : 0 < ε) : (V + ε • 1).IsNonsingularMMatrix := by
  refine ⟨fun i j hij => by simpa [Matrix.one_apply_ne hij] using hV.1 i j hij, ?_⟩
  rw [neg_add, ← sub_eq_add_neg]
  exact isHurwitz_sub_smul_one (fun μ hμ => (hV.2 μ hμ).le) hε

/-- `‖k‖ ≤ ρ` for every eigenvalue `k`. -/
private theorem nnnorm_le_spectralRadius {M : Matrix ι ι ℂ} {k : ℂ} (hk : k ∈ spectrum ℂ M) :
    (‖k‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ M :=
  le_iSup₂ (f := fun k (_ : k ∈ quasispectrum ℂ M) => (‖k‖₊ : ℝ≥0∞)) k
    (spectrum_subset_quasispectrum ℂ _ hk)

/-- The **basic reproduction number** `R₀ = ρ(F V⁻¹)`: the spectral radius (largest modulus of
a complex eigenvalue) of the next-generation matrix `F V⁻¹` (van den Driessche–Watmough 2002,
Eq. (4)). It is meaningful when `V` is invertible (for a nonsingular M-matrix it is). -/
noncomputable def R0 (F V : Matrix ι ι ℝ) : ℝ :=
  (spectralRadius ℂ ((F * V⁻¹).map (algebraMap ℝ ℂ))).toReal

private theorem R0_lt_one_iff (F V : Matrix ι ι ℝ) :
    R0 F V < 1 ↔ spectralRadius ℂ ((F * V⁻¹).map (algebraMap ℝ ℂ)) < 1 := by
  rw [R0, ← ENNReal.toReal_one,
    ENNReal.toReal_lt_toReal (spectralRadius_ne_top _) ENNReal.one_ne_top]

private theorem one_lt_R0_iff (F V : Matrix ι ι ℝ) :
    1 < R0 F V ↔ 1 < spectralRadius ℂ ((F * V⁻¹).map (algebraMap ℝ ℂ)) := by
  rw [R0, ← ENNReal.toReal_one,
    ENNReal.toReal_lt_toReal ENNReal.one_ne_top (spectralRadius_ne_top _)]

/-- **`R₀` as a threshold for the linearized infected subsystem** (van den Driessche–Watmough
2002, proof of Theorem 2). If `F` is entrywise nonnegative and `V` is a nonsingular M-matrix,
then every eigenvalue of `F - V` has negative real part iff `R₀ = ρ(F V⁻¹) < 1`. -/
theorem isHurwitz_sub_iff_R0_lt_one {F V : Matrix ι ι ℝ} (hF : ∀ i j, 0 ≤ F i j)
    (hV : V.IsNonsingularMMatrix) : (F - V).IsHurwitz ↔ R0 F V < 1 := by
  have hVinv := hV.inv_nonneg
  have hdV : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).1 hV.isUnit
  have hK : ∀ i j, 0 ≤ (F * V⁻¹) i j := mul_nonneg' hF hVinv
  rw [R0_lt_one_iff]
  constructor
  · intro hH
    let _ : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
    have _ : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
    refine spectralRadius_lt_of_forall_quasispectrum_lt fun ν hν => ?_
    rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, Set.mem_singleton_iff] at hν
    rcases hν with hν | rfl
    · by_contra hge
      push Not at hge
      obtain ⟨x, hx0, hx⟩ := exists_eigenvector hν
      have key := norm_smul_absVec_le hK hx
      have hle : absVec x ≤ (F * V⁻¹) *ᵥ absVec x := fun i => by
        have h1 : (1 : ℝ) ≤ ‖ν‖ := by exact_mod_cast hge
        have := key i
        simp only [Pi.smul_apply, smul_eq_mul] at this
        nlinarith [mul_nonneg (sub_nonneg.2 h1) (absVec_nonneg x i)]
      exact absVec_ne_zero hx0 (eq_zero_of_le_mulVec hF hV hH (absVec_nonneg x) hle)
    · simp
  · intro hρ μ hμ
    by_contra hre
    push Not at hre
    obtain ⟨x, hx0, hx⟩ := exists_eigenvector hμ
    obtain ⟨c, -, hB⟩ := exists_smul_one_sub hV.1
    have key := add_re_smul_le hF hB hx
    have h1 : absVec x ≤ (V⁻¹ * F) *ᵥ absVec x := by
      have h2 : V *ᵥ absVec x ≤ F *ᵥ absVec x := fun i => by
        have := key i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        nlinarith [mul_nonneg hre (absVec_nonneg x i)]
      have := mulVec_mono hVinv h2
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdV, Matrix.one_mulVec,
        Matrix.mulVec_mulVec] at this
    have := le_spectralRadius_of_smul_le_mulVec (mul_nonneg' hVinv hF) (absVec_nonneg x)
      (absVec_ne_zero hx0) zero_le_one (by simpa using h1)
    rw [ENNReal.ofReal_one, spectralRadius_inv_mul hV.isUnit] at this
    exact absurd hρ (not_lt.2 this)

/-- **`R₀ > 1` gives an unstable mode** (van den Driessche–Watmough 2002, proof of Theorem 2).
If `F` is entrywise nonnegative and `V` is a nonsingular M-matrix, then `F - V` has an
eigenvalue with positive real part iff `R₀ = ρ(F V⁻¹) > 1`. -/
theorem exists_re_pos_iff_one_lt_R0 {F V : Matrix ι ι ℝ} (hF : ∀ i j, 0 ≤ F i j)
    (hV : V.IsNonsingularMMatrix) :
    (∃ μ ∈ spectrum ℂ ((F - V).map (algebraMap ℝ ℂ)), 0 < μ.re) ↔ 1 < R0 F V := by
  have hVinv := hV.inv_nonneg
  have hdV : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).1 hV.isUnit
  have hK : ∀ i j, 0 ≤ (F * V⁻¹) i j := mul_nonneg' hF hVinv
  constructor
  · rintro ⟨μ, hμ, hre⟩
    obtain ⟨x, hx0, hx⟩ := exists_eigenvector hμ
    obtain ⟨c, hc, hB⟩ := exists_smul_one_sub hV.1
    set z := absVec x
    have key := add_re_smul_le hF hB hx
    -- `c V⁻¹ z = z + V⁻¹ (c 1 - V) z ≥ z`
    have hVz : c⁻¹ • z ≤ V⁻¹ *ᵥ z := by
      have e : c • (V⁻¹ *ᵥ z) = z + (V⁻¹ * (c • 1 - V)) *ᵥ z := by
        rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hdV,
          Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        abel
      have hpos : 0 ≤ (V⁻¹ * (c • 1 - V)) *ᵥ z := by
        simpa using mulVec_mono (mul_nonneg' hVinv hB) (absVec_nonneg x)
      intro i
      have := congr_fun e i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at this ⊢
      have hpi := hpos i
      simp only [Pi.zero_apply] at hpi
      rw [inv_mul_eq_div, div_le_iff₀ hc]
      linarith
    have h1 : (1 + μ.re / c) • z ≤ (V⁻¹ * F) *ᵥ z := by
      have := mulVec_mono hVinv key
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdV,
        Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at this
      intro i
      have h3 := this i
      have h4 := hVz i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3 h4 ⊢
      have : μ.re * (c⁻¹ * z i) ≤ μ.re * (V⁻¹ *ᵥ z) i := mul_le_mul_of_nonneg_left h4 hre.le
      rw [div_eq_mul_inv]
      nlinarith
    have hρ := le_spectralRadius_of_smul_le_mulVec (mul_nonneg' hVinv hF) (absVec_nonneg x)
      (absVec_ne_zero hx0) (by positivity) h1
    rw [spectralRadius_inv_mul hV.isUnit] at hρ
    rw [one_lt_R0_iff]
    refine lt_of_lt_of_le ?_ hρ
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have : 0 < μ.re / c := div_pos hre hc
    linarith
  · intro hR0
    by_contra hcon
    push Not at hcon
    rw [one_lt_R0_iff] at hR0
    -- an eigenvalue of `F V⁻¹` of modulus `> 1`
    obtain ⟨ν, hν, hν1⟩ : ∃ ν ∈ spectrum ℂ ((F * V⁻¹).map (algebraMap ℝ ℂ)), 1 < ‖ν‖ := by
      by_contra hno
      push Not at hno
      refine absurd hR0 (not_lt.2 ?_)
      refine iSup₂_le fun k hk => ?_
      rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, Set.mem_singleton_iff] at hk
      rcases hk with hk | rfl
      · exact_mod_cast hno k hk
      · simp
    obtain ⟨x, hx0, hx⟩ := exists_eigenvector hν
    set z := absVec x
    have hz := absVec_nonneg x
    have key := norm_smul_absVec_le hK hx
    set b := V⁻¹ *ᵥ z
    set d := (F * V⁻¹) *ᵥ b
    -- choose `ε > 0` with `ε dᵢ ≤ (‖ν‖ - 1) zᵢ` whenever `zᵢ > 0`
    have hev : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), z i = 0 ∨ ε * d i ≤ (‖ν‖ - 1) * z i := by
      intro i
      rcases (hz i).eq_or_lt with h0 | hpos
      · exact Eventually.of_forall fun _ => Or.inl h0.symm
      · have ht : Tendsto (fun ε : ℝ => ε * d i) (𝓝[>] 0) (𝓝 0) := by
          have : Tendsto (fun ε : ℝ => ε * d i) (𝓝 0) (𝓝 (0 * d i)) := tendsto_id.mul_const _
          simpa using tendsto_nhdsWithin_of_tendsto_nhds this
        have hlt : (0 : ℝ) < (‖ν‖ - 1) * z i := mul_pos (by linarith) hpos
        exact (ht.eventually (eventually_le_nhds hlt)).mono fun _ h => Or.inr h
    obtain ⟨ε, hεall, hε⟩ := ((eventually_all.2 hev).and self_mem_nhdsWithin).exists
    have hε : 0 < ε := hε
    have hVε := isNonsingularMMatrix_add_smul_one hV hε
    have hHε : (F - (V + ε • 1)).IsHurwitz := by
      rw [← sub_sub]
      exact isHurwitz_sub_smul_one hcon hε
    have hdVε : IsUnit (V + ε • 1).det := (Matrix.isUnit_iff_isUnit_det _).1 hVε.isUnit
    set a := (V + ε • 1)⁻¹ *ᵥ z
    have ha : 0 ≤ a := by simpa using mulVec_mono hVε.inv_nonneg hz
    -- resolvent identity: `b - a = ε V⁻¹ a`
    have hres : b - a = ε • (V⁻¹ *ᵥ a) := by
      have hVa : V *ᵥ a + ε • a = z := by
        have : (V + ε • 1) *ᵥ a = z := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdVε, Matrix.one_mulVec]
        rwa [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      have : b = a + ε • (V⁻¹ *ᵥ a) := by
        change V⁻¹ *ᵥ z = _
        rw [← hVa, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdV,
          Matrix.one_mulVec, Matrix.mulVec_smul]
      rw [this]; abel
    have hab : a ≤ b := by
      have : 0 ≤ ε • (V⁻¹ *ᵥ a) := smul_nonneg hε.le (by simpa using mulVec_mono hVinv ha)
      rw [← hres] at this
      exact fun i => by simpa using this i
    have hlow : b - ε • (V⁻¹ *ᵥ b) ≤ a := by
      have h1 : V⁻¹ *ᵥ a ≤ V⁻¹ *ᵥ b := mulVec_mono hVinv hab
      intro i
      have h2 := congr_fun hres i
      have h3 := h1 i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
      nlinarith
    have hzle : z ≤ (F * (V + ε • 1)⁻¹) *ᵥ z := by
      rw [← Matrix.mulVec_mulVec]
      have hFa : F *ᵥ (b - ε • (V⁻¹ *ᵥ b)) ≤ F *ᵥ a := mulVec_mono hF hlow
      have hFa0 : 0 ≤ F *ᵥ a := by simpa using mulVec_mono hF ha
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at hFa
      intro i
      have hd : (F *ᵥ (V⁻¹ *ᵥ b)) i = d i := by simp only [d, Matrix.mulVec_mulVec]
      rcases hεall i with h0 | hεi
      · change z i ≤ (F *ᵥ a) i
        rw [h0]; exact hFa0 i
      · have h1 := hFa i
        have h2 : ‖ν‖ * z i ≤ ((F * V⁻¹) *ᵥ z) i := key i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
        rw [hd] at h1
        change z i ≤ (F *ᵥ a) i
        nlinarith
    exact absVec_ne_zero hx0 (eq_zero_of_le_mulVec hF hVε hHε hz hzle)

/-- The complex eigenvalues of a block lower-triangular real matrix `[[A, 0], [C, D]]` are
those of `A` together with those of `D`. -/
theorem mem_spectrum_fromBlocks_zero₁₂ {A : Matrix ι ι ℝ} {C : Matrix κ ι ℝ}
    {D : Matrix κ κ ℝ} {μ : ℂ} :
    μ ∈ spectrum ℂ ((fromBlocks A 0 C D).map (algebraMap ℝ ℂ)) ↔
      μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) ∨ μ ∈ spectrum ℂ (D.map (algebraMap ℝ ℂ)) := by
  rw [fromBlocks_map, Matrix.map_zero _ (map_zero _), mem_spectrum_iff_isRoot_charpoly,
    charpoly_fromBlocks_zero₁₂, Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero,
    mem_spectrum_iff_isRoot_charpoly, mem_spectrum_iff_isRoot_charpoly]
  rfl

/-- A block lower-triangular real matrix `[[A, 0], [C, D]]` is Hurwitz iff both diagonal
blocks are. -/
theorem isHurwitz_fromBlocks_zero₁₂_iff {A : Matrix ι ι ℝ} {C : Matrix κ ι ℝ}
    {D : Matrix κ κ ℝ} : (fromBlocks A 0 C D).IsHurwitz ↔ A.IsHurwitz ∧ D.IsHurwitz := by
  constructor
  · intro h
    exact ⟨fun μ hμ => h μ (mem_spectrum_fromBlocks_zero₁₂.2 (Or.inl hμ)),
      fun μ hμ => h μ (mem_spectrum_fromBlocks_zero₁₂.2 (Or.inr hμ))⟩
  · rintro ⟨hA, hD⟩ μ hμ
    rcases mem_spectrum_fromBlocks_zero₁₂.1 hμ with h | h
    exacts [hA μ h, hD μ h]

/-- **Threshold theorem, stability half, conditional decay form** (van den Driessche–Watmough
2002, Theorem 2). Let `x₀` be an equilibrium of `x' = f(x)` on `ℝ^{ι ⊕ κ}` (infected
compartments `ι`, the others `κ`), with `f` differentiable at `x₀` and Jacobian
`[[F - V, 0], [C, D]]` as in their Lemma 1, where `F ≥ 0`, `V` is a nonsingular M-matrix and
`D` is Hurwitz. If `R₀ = ρ(F V⁻¹) < 1`, then every solution defined on all of `[0, ∞)`
starting near `x₀` decays exponentially. Conditional on global solutions; solution
existence is not proved here, so this is not by itself local exponential stability. -/
theorem globalSolution_decay_of_R0_lt_one {f : (ι ⊕ κ → ℝ) → ι ⊕ κ → ℝ}
    {x₀ : ι ⊕ κ → ℝ} {F V : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} {D : Matrix κ κ ℝ}
    (hf : f x₀ = 0)
    (hfJ : HasFDerivAt f
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (fromBlocks (F - V) 0 C D))) x₀)
    (hF : ∀ i j, 0 ≤ F i j) (hV : V.IsNonsingularMMatrix) (hD : D.IsHurwitz)
    (hR0 : R0 F V < 1) :
    ∃ δ K α : ℝ, 0 < δ ∧ 0 < K ∧ 0 < α ∧ ∀ x : ℝ → ι ⊕ κ → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t) → ‖x 0 - x₀‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - x₀‖ ≤ K * Real.exp (-(α * t)) * ‖x 0 - x₀‖ :=
  MathlibExt.Analysis.ODE.LinearizedStability.globalSolution_decay_of_hasFDerivAt
    hf hfJ (isHurwitz_fromBlocks_zero₁₂_iff.2 ⟨(isHurwitz_sub_iff_R0_lt_one hF hV).2 hR0, hD⟩)

/-- **Threshold theorem, instability half, spectral form** (van den Driessche–Watmough 2002,
Theorem 2). With `F ≥ 0` and `V` a nonsingular M-matrix, if `R₀ = ρ(F V⁻¹) > 1` then the
Jacobian `[[F - V, 0], [C, D]]` at the disease-free equilibrium has an eigenvalue with positive
real part (whatever `C` and `D`). -/
theorem exists_re_pos_jacobian_of_one_lt_R0 {F V : Matrix ι ι ℝ} (C : Matrix κ ι ℝ)
    (D : Matrix κ κ ℝ) (hF : ∀ i j, 0 ≤ F i j) (hV : V.IsNonsingularMMatrix)
    (hR0 : 1 < R0 F V) :
    ∃ μ ∈ spectrum ℂ ((fromBlocks (F - V) 0 C D).map (algebraMap ℝ ℂ)), 0 < μ.re := by
  obtain ⟨μ, hμ, hpos⟩ := (exists_re_pos_iff_one_lt_R0 hF hV).2 hR0
  exact ⟨μ, mem_spectrum_fromBlocks_zero₁₂.2 (Or.inl hμ), hpos⟩

end MathlibExt.Biology.Epidemiology.NextGenerationMatrix
