/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBetti
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

namespace MetaMathlibExt

/--
**Base change of a homogeneous element along zero evaluation.** Let $K$ be a field,
$R = K[x_1, \dots, x_n]$, and let $F$ be a multigraded free $R$-module with basis
$(b_j)_{j \in \iota}$, where each $b_j$ is homogeneous of degree $d_j \in \mathbb{Z}^n$.
Make $K$ an $R$-algebra through the zero evaluation $R \to K$, which sends every
variable to $0$. If $x \in F$ is homogeneous of degree $\alpha \in \mathbb{Z}^n$, then
$1 \otimes x \in K \otimes_R F$ lies in the $K$-linear span of the vectors $1 \otimes b_j$
with $d_j = \alpha$.

Proves `Wanted` entry `MultigradedFreeModule.baseChange_mem_degreeSpan`.

Source: Benjamin Braun and Brian Davis, "Antichain Simplices,"
Journal of Integer Sequences 23 (2020), lines 862–867,
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`, which split a
graded free resolution and take the degree-`α` component after tensoring with `K`.
-/
theorem MultigradedFreeModule.baseChange_mem_degreeSpan
    {K : Type*} [Field K] {n : ℕ} {F : Type*} [AddCommGroup F]
    [Module (MvPolynomial (Fin n) K) F] [Module K F] {ι : Type*}
    (free : MultigradedFreeModule K n F ι) (α : Fin n →₀ Int) {x : F}
    (hx : x ∈ free.graded.component α) :
    letI : Algebra (MvPolynomial (Fin n) K) K := zeroEval.toAlgebra;
    (1 ⊗ₜ[MvPolynomial (Fin n) K] x : TensorProduct (MvPolynomial (Fin n) K) K F) ∈
      Submodule.span K {y | ∃ j : ι, free.degree j = α ∧ y = free.basis.baseChange K j} := by
  let _ : Algebra (MvPolynomial (Fin n) K) K := zeroEval.toAlgebra
  let _ : DirectSum.Decomposition free.graded.component := free.graded.decomposition
  have hnat (a : Fin n →₀ ℕ) : natDegreeToInt a = 0 ↔ a = 0 := by
    constructor
    · intro h
      ext i
      have hi := DFunLike.congr_fun h i
      simpa [natDegreeToInt] using hi
    · rintro rfl
      simp [natDegreeToInt]
  have heval (p : MvPolynomial (Fin n) K) : zeroEval p = p.coeff 0 := by
    simp [zeroEval, MvPolynomial.constantCoeff]
  let _ : IsScalarTower K (MvPolynomial (Fin n) K) F := ⟨by
    intro c p z
    rw [free.graded.smul_via_C]
    simp [Algebra.smul_def, mul_smul]
  ⟩
  let bK : Module.Basis ((Fin n →₀ ℕ) × ι) K F :=
    (MvPolynomial.basisMonomials (Fin n) K).smulTower free.basis
  have bK_mem (aj : (Fin n →₀ ℕ) × ι) :
      bK aj ∈ free.graded.component (free.degree aj.2 + natDegreeToInt aj.1) := by
    rw [show bK aj =
        (MvPolynomial.monomial aj.1 (1 : K) : MvPolynomial (Fin n) K) • free.basis aj.2 by
      simp [bK, Module.Basis.smulTower_apply]]
    exact free.graded.monomial_mem aj.1 1 (free.degree aj.2) _
      (free.basis_mem aj.2)
  let proj (β : Fin n →₀ ℤ) : F →ₗ[K] F :=
    (free.graded.component β).subtype.comp
      ((DFinsupp.lapply β).comp
        (DirectSum.decomposeLinearEquiv free.graded.component).toLinearMap)
  have proj_of_mem_same (β : Fin n →₀ ℤ) {z : F}
      (hz : z ∈ free.graded.component β) : proj β z = z := by
    simp [proj, DirectSum.decomposeLinearEquiv_apply,
      DirectSum.decompose_of_mem_same _ hz]
  have proj_of_mem_ne (β γ : Fin n →₀ ℤ) {z : F}
      (hz : z ∈ free.graded.component γ) (hγβ : γ ≠ β) : proj β z = 0 := by
    simp [proj, DirectSum.decomposeLinearEquiv_apply,
      DirectSum.decompose_of_mem_ne _ hz hγβ]
  let coord (aj : (Fin n →₀ ℕ) × ι) : F →ₗ[K] K :=
    (Finsupp.lapply aj).comp bK.repr.toLinearMap
  have coord_proj (aj : (Fin n →₀ ℕ) × ι) :
      (coord aj).comp (proj (free.degree aj.2 + natDegreeToInt aj.1)) = coord aj := by
    apply bK.ext
    intro bk
    by_cases hdeg : free.degree bk.2 + natDegreeToInt bk.1 =
        free.degree aj.2 + natDegreeToInt aj.1
    · simp only [LinearMap.comp_apply]
      have hmem : bK bk ∈ free.graded.component
          (free.degree aj.2 + natDegreeToInt aj.1) := hdeg ▸ bK_mem bk
      rw [proj_of_mem_same _ hmem]
    · simp only [LinearMap.comp_apply]
      rw [proj_of_mem_ne _ _ (bK_mem bk) hdeg]
      have hne : bk ≠ aj := by
        intro h
        exact hdeg (congrArg (fun q => free.degree q.2 + natDegreeToInt q.1) h)
      simp [coord, hne]
  have coeff_zero_of_degree_ne (j : ι) (hj : free.degree j ≠ α) :
      (free.basis.repr x j).coeff 0 = 0 := by
    have hp : proj (free.degree j) x = 0 :=
      proj_of_mem_ne (free.degree j) α hx (Ne.symm hj)
    have hc := LinearMap.congr_fun (coord_proj (0, j)) x
    simp only [LinearMap.comp_apply] at hc
    simp only [natDegreeToInt, Finsupp.mapRange_zero, add_zero] at hc
    rw [hp] at hc
    simpa [coord, bK, Module.Basis.smulTower_repr, MvPolynomial.basisMonomials] using hc.symm
  let bt := free.basis.baseChange K
  let y : TensorProduct (MvPolynomial (Fin n) K) K F :=
    1 ⊗ₜ[MvPolynomial (Fin n) K] x
  have repr_y (j : ι) : (bt.repr y) j = zeroEval (free.basis.repr x j) := by
    rw [show (bt.repr y) j = (free.basis.repr x j) • (1 : K) by
      simp [bt, y, Module.Basis.baseChange_repr_tmul]]
    change zeroEval (free.basis.repr x j) * 1 = _
    simp
  have hy : (bt.repr y).sum (fun j c => c • bt j) = y := by
    rw [← Finsupp.linearCombination_apply, ← Module.Basis.repr_symm_apply]
    exact bt.repr.symm_apply_apply y
  change y ∈ Submodule.span K
    {z | ∃ j : ι, free.degree j = α ∧ z = bt j}
  rw [← hy]
  change ∑ j ∈ (bt.repr y).support, (bt.repr y) j • bt j ∈
    Submodule.span K {y | ∃ j : ι, free.degree j = α ∧ y = free.basis.baseChange K j}
  apply Submodule.sum_mem
  intro j hj
  by_cases hdegree : free.degree j = α
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hdegree, rfl⟩)
  · rw [repr_y, heval, coeff_zero_of_degree_ne j hdegree, zero_smul]
    exact Submodule.zero_mem _

end MetaMathlibExt
