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
# Ordered coordinates of the two-generator Koszul complex

For f,g in a commutative ring R, use the ordered basis e₀,e₁ of R² and top wedge e₀∧e₁. The
top exterior coordinate is the determinant. In these coordinates the Koszul maps are R → R², c
↦ c(−g,f), and R² → R, x ↦ fx₀+gx₁.

If multiplication by f is injective, the top differential is injective and H₂ of the pair
complex is zero. The coordinate three-term complex is canonically isomorphic to the degree-one
homology short complex of the Koszul complex.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace KoszulComplex

universe u

variable (R : Type u) [CommRing R]

/-- The unique top exterior index for a pair.

The full two-element subset of Fin 2 indexes the ordered top wedge. -/
def pairTopIndex : Set.powersetCard (Fin 2) 2 :=
  ⟨Finset.univ, by simp⟩

/-- Uniqueness of the pair top exterior index.

Every two-element subset of Fin 2 equals pairTopIndex. -/
theorem pairTopIndex_unique (s : Set.powersetCard (Fin 2) 2) :
    s = pairTopIndex := by
  apply Subtype.ext
  exact Finset.eq_univ_of_card s.val (by simp)

/-- The ordered embedding of the pair top index.

The embedding associated to the full subset of Fin 2 is the identity. -/
theorem pairTopIndex_orderEmb (i : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm pairTopIndex i = i := by
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  have h := Finset.orderEmbOfFin_unique'
    (s := (pairTopIndex : Set.powersetCard (Fin 2) 2).val)
    pairTopIndex.prop (f := OrderEmbedding.id (Fin 2))
    (fun _ => Finset.mem_univ _)
  exact congrArg (fun e : Fin 2 ↪o Fin 2 => e i) h.symm

/-- The top exterior-power coordinate equivalence.

The ordered standard wedge identifies Λ²(R²) with R by its native coefficient
functional. The basis and wedge are the standard `Pi.basisFun` and exterior-power
constructions; no parallel coordinate interfaces are introduced. -/
noncomputable def pairTopEquiv :
    (⋀[R]^2 (Fin 2 → R)) ≃ₗ[R] R := by
  let B := Pi.basisFun R (Fin 2)
  apply LinearEquiv.ofBijective (exteriorPower.ιMultiDual R 2 B pairTopIndex)
  constructor
  · intro z w hzw
    apply B.exteriorPower 2 |>.repr.injective
    ext s
    rw [pairTopIndex_unique s]
    rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
    exact hzw
  · intro r
    refine ⟨r • exteriorPower.ιMulti_family R 2 B pairTopIndex, ?_⟩
    rw [map_smul, exteriorPower.ιMultiDual_apply_diag, smul_eq_mul, mul_one]

/-- The determinant formula for a pair wedge.

The top coordinate of the wedge of two vectors is a₀₀a₁₁−a₀₁a₁₀. -/
theorem pairTopEquiv_apply_ιMulti (a : Fin 2 → (Fin 2 → R)) :
    pairTopEquiv R (exteriorPower.ιMulti R 2 a) =
      a 0 0 * a 1 1 - a 0 1 * a 1 0 := by
  change exteriorPower.ιMultiDual R 2 (Pi.basisFun R (Fin 2)) pairTopIndex
    (exteriorPower.ιMulti R 2 a) = _
  rw [exteriorPower.ιMultiDual_apply_ιMulti, Matrix.det_fin_two]
  simp [Pi.basisFun, pairTopIndex_orderEmb]

/-- The top pair differential in ordered coordinates.

After the exterior-power identifications, the differential Λ²(R²) → R² sends c to c(−g,f). -/
theorem pair_differential_one_coordinates (f g : R) :
    (exteriorPower.oneEquiv R (Fin 2 → R)).toLinearMap.comp
        (differential R (Fin 2 → R)
          (familyFunctional R (pairFamily R f g)) 1) =
      (LinearMap.toSpanSingleton R (Fin 2 → R)
        (pairFamily R (-g) f)).comp
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

/-- For arbitrary f,g in a commutative ring R and z in Λ¹(R²), the bottom
Koszul differential has actual scalar value f*x₀ + g*x₁, where x is the vector
obtained from z by the native degree-one exterior equivalence. -/
theorem pair_differential_zero_coordinates (f g : R)
    (z : ⋀[R]^1 (Fin 2 → R)) :
    exteriorPower.zeroEquiv R (Fin 2 → R)
        (differential R (Fin 2 → R) (familyFunctional R (pairFamily R f g)) 0 z) =
      f * exteriorPower.oneEquiv R (Fin 2 → R) z 0 +
        g * exteriorPower.oneEquiv R (Fin 2 → R) z 1 := by
  have h := LinearMap.congr_fun
    (differential_zero_equiv R (Fin 2 → R) (familyFunctional R (pairFamily R f g))) z
  change exteriorPower.zeroEquiv R (Fin 2 → R)
      (differential R (Fin 2 → R) (familyFunctional R (pairFamily R f g)) 0 z) =
    familyFunctional R (pairFamily R f g) (exteriorPower.oneEquiv R (Fin 2 → R) z) at h
  rw [h]
  simp [familyFunctional, Fintype.linearCombination_apply, Fin.sum_univ_two,
    smul_eq_mul, mul_comm]

/-- Regularity of the first element makes the top differential injective.

If multiplication by f on R is injective, the map c ↦ c(−g,f) is injective. -/
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
          (pairFamily R (-g) f) (pairTopEquiv R z) =
        LinearMap.toSpanSingleton R (Fin 2 → R)
          (pairFamily R (-g) f) (pairTopEquiv R w) := by
    have hformula := pair_differential_one_coordinates R f g
    have hz := LinearMap.congr_fun hformula z
    have hw := LinearMap.congr_fun hformula w
    exact hz.symm.trans <| (congrArg
      (exteriorPower.oneEquiv R (Fin 2 → R)) hzw).trans hw
  have hcoordOne := congrArg (fun x : Fin 2 → R => x 1) hcoord
  simpa [LinearMap.lsmul_apply, smul_eq_mul, mul_comm] using hcoordOne

/-- The pair complex has zero top homology for a regular first element.

If multiplication by f is injective, H₂(K(f,g)) is zero. -/
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

/-- The coordinate short complex of a Koszul pair.

Form R → R² → R with maps c ↦ c(−g,f) and x ↦ fx₀+gx₁. -/
noncomputable def pairCoordinateShortComplex (f g : R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (LinearMap.toSpanSingleton R (Fin 2 → R)
      (pairFamily R (-g) f))
    (familyFunctional R (pairFamily R f g)) (by
      apply LinearMap.ext
      intro c
      simp [familyFunctional, Fintype.linearCombination_apply,
        Fin.sum_univ_two]
      ring)

/-- The coordinate comparison for degree-one pair homology.

The degree-one homology short complex of K(f,g) is isomorphic to the coordinate complex
through the ordered exterior identifications. -/
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
    exact (differential_zero_equiv R (Fin 2 → R)
      (familyFunctional R (pairFamily R f g))).symm

end KoszulComplex
