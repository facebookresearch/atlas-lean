/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexFamilyReindex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Tactic.Ring

/-!
# Coordinates for two-generator Koszul complexes

The second exterior power of the standard rank-two free module is identified
with the base ring by the ordered standard wedge.  This supplies the top
coordinate needed for explicit two-generator Koszul differentials.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace KoszulComplex

universe u

variable (R : Type u) [CommRing R]

/-- The unique two-element subset of `Fin 2`. -/
def pairTopIndex : Set.powersetCard (Fin 2) 2 :=
  ⟨Finset.univ, by simp⟩

/-- Every two-element subset of `Fin 2` is the full set. -/
theorem pairTopIndex_unique (s : Set.powersetCard (Fin 2) 2) :
    s = pairTopIndex := by
  apply Subtype.ext
  exact Finset.eq_univ_of_card s.val (by simp)

/-- The ordered embedding of the full two-element subset is the identity. -/
theorem pairTopIndex_orderEmb (i : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm pairTopIndex i = i := by
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  have h := Finset.orderEmbOfFin_unique'
    (s := (pairTopIndex : Set.powersetCard (Fin 2) 2).val)
    pairTopIndex.prop (f := OrderEmbedding.id (Fin 2))
    (fun _ => Finset.mem_univ _)
  exact congrArg (fun e : Fin 2 ↪o Fin 2 => e i) h.symm

/-- Standard basis of the rank-two free module. -/
noncomputable def pairBasis : Module.Basis (Fin 2) R (Fin 2 → R) :=
  Pi.basisFun R (Fin 2)

/-- Coefficient of the ordered standard wedge in the second exterior power. -/
noncomputable def pairTopCoeff : (⋀[R]^2 (Fin 2 → R)) →ₗ[R] R :=
  exteriorPower.ιMultiDual R 2 (pairBasis R) pairTopIndex

/-- The ordered standard basis wedge. -/
noncomputable def pairTopWedge : ⋀[R]^2 (Fin 2 → R) :=
  exteriorPower.ιMulti_family R 2 (pairBasis R) pairTopIndex

/-- The top-wedge coefficient is a linear equivalence in rank two. -/
noncomputable def pairTopEquiv :
    (⋀[R]^2 (Fin 2 → R)) ≃ₗ[R] R := by
  apply LinearEquiv.ofBijective (pairTopCoeff R)
  constructor
  · intro z w hzw
    apply (pairBasis R).exteriorPower 2 |>.repr.injective
    ext s
    rw [pairTopIndex_unique s]
    rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
    exact hzw
  · intro r
    refine ⟨r • pairTopWedge R, ?_⟩
    rw [map_smul, pairTopWedge, pairTopCoeff,
      exteriorPower.ιMultiDual_apply_diag, smul_eq_mul, mul_one]

/-- The top coordinate of a decomposable rank-two wedge is the usual
two-by-two determinant. -/
theorem pairTopEquiv_apply_ιMulti (a : Fin 2 → (Fin 2 → R)) :
    pairTopEquiv R (exteriorPower.ιMulti R 2 a) =
      a 0 0 * a 1 1 - a 0 1 * a 1 0 := by
  change pairTopCoeff R (exteriorPower.ιMulti R 2 a) = _
  rw [pairTopCoeff, exteriorPower.ιMultiDual_apply_ιMulti,
    Matrix.det_fin_two]
  simp [pairBasis, pairTopIndex_orderEmb]

/-- Coordinate vector of the top two-generator Koszul differential. -/
def pairTopBoundaryVector (f g : R) : Fin 2 → R :=
  Fin.cases (-g) (fun _ => f)

@[simp]
theorem pairTopBoundaryVector_zero (f g : R) :
    pairTopBoundaryVector R f g 0 = -g :=
  rfl

@[simp]
theorem pairTopBoundaryVector_one (f g : R) :
    pairTopBoundaryVector R f g 1 = f :=
  rfl

/-- Coordinate form of the top differential: the ordered top wedge maps to
`(-g,f)`. -/
theorem pair_differential_one_coordinates (f g : R) :
    (exteriorPower.oneEquiv R (Fin 2 → R)).toLinearMap.comp
        (differential R (Fin 2 → R)
          (familyFunctional R (pairFamily R f g)) 1) =
      (LinearMap.toSpanSingleton R (Fin 2 → R)
        (pairTopBoundaryVector R f g)).comp
          (pairTopEquiv R).toLinearMap := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := 2) (M := Fin 2 → R) (N := Fin 2 → R)
  apply AlternatingMap.ext
  intro a
  funext j
  fin_cases j <;>
    simp [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      differential_apply_ιMulti, Fin.sum_univ_two,
      pairTopEquiv_apply_ιMulti] <;>
    simp [familyFunctional, Fintype.linearCombination_apply,
      pairFamily_zero, pairFamily_one, Fin.sum_univ_two] <;>
    ring

/-- Coordinate form of the bottom differential: dot product with `(f,g)`. -/
theorem pair_differential_zero_coordinates (f g : R) :
    (exteriorPower.zeroEquiv R (Fin 2 → R)).toLinearMap.comp
        (differential R (Fin 2 → R)
          (familyFunctional R (pairFamily R f g)) 0) =
      (familyFunctional R (pairFamily R f g)).comp
        (exteriorPower.oneEquiv R (Fin 2 → R)).toLinearMap :=
  differential_zero_equiv R (Fin 2 → R)
    (familyFunctional R (pairFamily R f g))

/-- The top two-generator Koszul differential is injective when the first
coefficient acts injectively on the ring. -/
theorem pair_differential_one_injective
    (f g : R) (hf : Function.Injective (LinearMap.lsmul R R f)) :
    Function.Injective
      (differential R (Fin 2 → R)
        (familyFunctional R (pairFamily R f g)) 1) := by
  intro z w hzw
  apply (pairTopEquiv R).injective
  apply hf
  have hcoord :
      LinearMap.toSpanSingleton R (Fin 2 → R)
          (pairTopBoundaryVector R f g) (pairTopEquiv R z) =
        LinearMap.toSpanSingleton R (Fin 2 → R)
          (pairTopBoundaryVector R f g) (pairTopEquiv R w) := by
    have hformula := pair_differential_one_coordinates R f g
    have hz := LinearMap.congr_fun hformula z
    have hw := LinearMap.congr_fun hformula w
    exact hz.symm.trans <| (congrArg
      (exteriorPower.oneEquiv R (Fin 2 → R)) hzw).trans hw
  have hcoordOne := congrArg (fun x : Fin 2 → R => x 1) hcoord
  simpa [LinearMap.lsmul_apply, smul_eq_mul, mul_comm] using hcoordOne

/-- Degree-two homology of a two-generator Koszul complex vanishes when the
first coefficient acts injectively. -/
theorem pair_homology_two_isZero
    (f g : R) (hf : Function.Injective (LinearMap.lsmul R R f)) :
    CategoryTheory.Limits.IsZero
      ((familyComplex R (pairFamily R f g)).homology 2) := by
  let K := familyComplex R (pairFamily R f g)
  have hd : Function.Injective ((K.d 2 1).hom) := by
    rw [show K.d 2 1 = ModuleCat.ofHom
      (differential R (Fin 2 → R)
        (familyFunctional R (pairFamily R f g)) 1) by
      exact complex_d_succ R (Fin 2 → R)
        (familyFunctional R (pairFamily R f g)) 1]
    exact pair_differential_one_injective R f g hf
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (K.d 2 ((ComplexShape.down ℕ).next 2)).hom x = 0 at hx
  rw [ChainComplex.next_nat_succ] at hx
  have hx0 : x = 0 := hd <| hx.trans ((K.d 2 1).hom.map_zero).symm
  refine ⟨0, ?_⟩
  simp [hx0]

/-- The coordinate short complex `R → R² → R` for the two-generator
Koszul complex. -/
noncomputable def pairCoordinateShortComplex (f g : R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (LinearMap.toSpanSingleton R (Fin 2 → R)
      (pairTopBoundaryVector R f g))
    (familyFunctional R (pairFamily R f g)) (by
      apply LinearMap.ext
      intro c
      simp [familyFunctional, Fintype.linearCombination_apply,
        Fin.sum_univ_two]
      ring)

/-- The degree-one short complex of the abstract two-generator Koszul
complex is isomorphic to its explicit coordinate short complex. -/
noncomputable def pairCoordinateShortComplexIso (f g : R) :
    (familyComplex R (pairFamily R f g)).sc 1 ≅
      pairCoordinateShortComplex R f g := by
  let K := familyComplex R (pairFamily R f g)
  let e₁ := (pairTopEquiv R).toModuleIso
  let e₂ := (exteriorPower.oneEquiv R (Fin 2 → R)).toModuleIso
  let e₃ := (exteriorPower.zeroEquiv R (Fin 2 → R)).toModuleIso
  refine K.isoSc' 2 1 0 (by simp) (by simp) ≪≫
    ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · apply ModuleCat.hom_ext
    exact (pair_differential_one_coordinates R f g).symm
  · apply ModuleCat.hom_ext
    exact (pair_differential_zero_coordinates R f g).symm

end KoszulComplex
