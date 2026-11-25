/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientComplex
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.ULift

/-!
# Degree-zero Chevalley–Eilenberg homology and coinvariants

The degree-zero exterior tensor term identifies with the coefficient module.
The degree-one differential becomes the negative Lie action, so its cokernel
is the coinvariant quotient. Negating the action leaves its relation span
unchanged, giving the same quotient for the right-action convention
`m · x = -⁅x, m⁆`.

The linear comparison allows independent ring, Lie-algebra, and coefficient
universes. The categorical comparison lifts the quotient into the complex's
module-category universe.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w w' z

namespace ChevalleyEilenberg

section Coordinates

variable (R : Type u) [CommRing R]
variable (L : Type v) [AddCommGroup L] [Module R L]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- Canonical coefficient coordinates in exterior degree zero. -/
def coefficientZeroEquiv : (⋀[R]^0 L) ⊗[R] M ≃ₗ[R] M :=
  ((exteriorPower.zeroEquiv R L).rTensor M).trans (TensorProduct.lid R M)

/-- The empty exterior word has its given coefficient coordinate. -/
theorem coefficientZeroEquiv_ι_tmul (m : M) :
    coefficientZeroEquiv R L M
      (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m) = m := by
  change TensorProduct.lid R M
    ((exteriorPower.zeroEquiv R L).rTensor M
      (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)) = m
  rw [LinearEquiv.rTensor_tmul, exteriorPower.zeroEquiv_ιMulti,
    TensorProduct.lid_tmul, one_smul]

private def coefficientOneEquiv : (⋀[R]^1 L) ⊗[R] M ≃ₗ[R] L ⊗[R] M :=
  (exteriorPower.oneEquiv R L).rTensor M

private theorem coefficientOneEquiv_ι_tmul (x : L) (m : M) :
    coefficientOneEquiv R L M
      (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] m) = x ⊗ₜ[R] m := by
  change (exteriorPower.oneEquiv R L).rTensor M
    (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] m) = x ⊗ₜ[R] m
  rw [LinearEquiv.rTensor_tmul, exteriorPower.oneEquiv_ιMulti]

private theorem coefficientOneEquiv_symm_tmul (x : L) (m : M) :
    (coefficientOneEquiv R L M).symm (x ⊗ₜ[R] m) =
      exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] m := by
  apply (coefficientOneEquiv R L M).injective
  rw [LinearEquiv.apply_symm_apply, coefficientOneEquiv_ι_tmul]

end Coordinates

section DegreeOne

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- The degree-one coefficient differential is the negative native tensor
action after the canonical degree-zero and degree-one coordinate changes. -/
theorem coefficientDifferential_zero_coordinates :
    (coefficientZeroEquiv R L M).toLinearMap.comp
        (coefficientDifferential R L M 0) =
      (-(LieModule.toModuleHom R L M).toLinearMap).comp
        ((exteriorPower.oneEquiv R L).rTensor M).toLinearMap := by
  have hd (x : L) (m : M) :
      coefficientDifferential R L M 0
          (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] m) =
        (-1 : R) •
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] ⁅x, m⁆) :=
    (coefficientDifferential_ι_tmul R L M x m).trans
      (neg_one_smul R
        (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] ⁅x, m⁆)).symm
  have h : ((coefficientZeroEquiv R L M).toLinearMap.comp
      (coefficientDifferential R L M 0)).comp
        (coefficientOneEquiv R L M).symm.toLinearMap =
      -(LieModule.toModuleHom R L M).toLinearMap := by
    apply TensorProduct.ext' (R := R)
    intro x m
    change coefficientZeroEquiv R L M
        (coefficientDifferential R L M 0
          ((coefficientOneEquiv R L M).symm (x ⊗ₜ[R] m))) =
      -((LieModule.toModuleHom R L M).toLinearMap (x ⊗ₜ[R] m))
    rw [coefficientOneEquiv_symm_tmul, hd, map_smul,
      coefficientZeroEquiv_ι_tmul, neg_one_smul]
    simp only [LieModuleHom.coe_toLinearMap, LieModule.toModuleHom_apply]
  apply LinearMap.ext
  intro a
  have ha := LinearMap.congr_fun h (coefficientOneEquiv R L M a)
  change coefficientZeroEquiv R L M
      (coefficientDifferential R L M 0
        ((coefficientOneEquiv R L M).symm (coefficientOneEquiv R L M a))) =
    -((LieModule.toModuleHom R L M).toLinearMap (coefficientOneEquiv R L M a)) at ha
  rw [LinearEquiv.symm_apply_apply] at ha
  exact ha

/-- Native coefficient action relations are the image of the native tensor action. -/
theorem coefficientActionRelations_eq_range :
    (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule =
      (LieModule.toModuleHom R L M).toLinearMap.range := by
  let incl := TensorProduct.LieModule.mapIncl
    (⊤ : LieIdeal R L) (⊤ : LieSubmodule R L M)
  have hsurj : Function.Surjective incl.toLinearMap := by
    change Function.Surjective (TensorProduct.map
      (⊤ : LieIdeal R L).incl.toLinearMap
      (⊤ : LieSubmodule R L M).incl.toLinearMap)
    exact TensorProduct.map_surjective
      (fun x => ⟨⟨x, by trivial⟩, rfl⟩)
      (fun m => ⟨⟨m, by trivial⟩, rfl⟩)
  simp only [LieSubmodule.lieIdeal_oper_eq_tensor_map_range,
    LieModuleHom.toSubmodule_range, LieModuleHom.toLinearMap_comp]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj)

/-- Degree-zero coefficient coordinates identify the incoming boundary
image with the native action relation submodule. -/
theorem coefficientDifferential_zero_range :
    (coefficientDifferential R L M 0).range.map
        (coefficientZeroEquiv R L M).toLinearMap =
      (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule := by
  rw [← LinearMap.range_comp, coefficientDifferential_zero_coordinates,
    LinearEquiv.range_comp, LinearMap.range_neg]
  exact (coefficientActionRelations_eq_range R L M).symm

private theorem coefficientIncomingRange_zeroCoordinates :
    ((coefficientComplex R L M).sc 0).f.hom.range.map
        (coefficientZeroEquiv R L M).toLinearMap =
      (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule := by
  change ((coefficientComplex R L M).d ((ComplexShape.down ℕ).prev 0) 0).hom.range.map
    (coefficientZeroEquiv R L M).toLinearMap = _
  rw [ChainComplex.prev, coefficientComplex_d_succ R L M 0]
  change (coefficientDifferential R L M 0).range.map
    (coefficientZeroEquiv R L M).toLinearMap = _
  exact coefficientDifferential_zero_range R L M

end DegreeOne

section NativeHomology

variable {R : Type u} [Ring R]

private def coefficientHomologyZeroRangeEquiv (K : ChainComplex (ModuleCat.{z} R) ℕ) :
    K.homology 0 ≃ₗ[R] K.X 0 ⧸ (K.sc 0).f.hom.range :=
  let e : K.homology 0 ≅ (K.sc 0).opcycles := K.isoHomologyι₀
  (e ≪≫ (K.sc 0).moduleCatOpcyclesIso).toLinearEquiv

private theorem coefficientHomologyZeroRangeEquiv_class
    (K : ChainComplex (ModuleCat.{z} R) ℕ) (a : K.X 0) :
    coefficientHomologyZeroRangeEquiv K
        (K.isoHomologyι₀.inv (K.pOpcycles 0 a)) = Submodule.Quotient.mk a := by
  let e : K.homology 0 ≅ (K.sc 0).opcycles := K.isoHomologyι₀
  let q := (K.sc 0).moduleCatOpcyclesIso
  have h : (K.sc 0).pOpcycles ≫ e.inv ≫ (e ≪≫ q).hom =
      ModuleCat.ofHom (LinearMap.range (K.sc 0).f.hom).mkQ := by
    rw [Iso.trans_hom, Iso.inv_hom_id_assoc]
    exact (K.sc 0).pOpcycles_comp_moduleCatOpcyclesIso_hom
  change (e ≪≫ q).hom (e.inv ((K.sc 0).pOpcycles a)) = _
  exact congrArg (fun f : (K.sc 0).X₂ ⟶
    ModuleCat.of R ((K.sc 0).X₂ ⧸ (K.sc 0).f.hom.range) => f a) h

end NativeHomology

section Coinvariants

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- Degree-zero homology of the coefficient CE complex is canonically
equivalent to the native coefficient coinvariants. -/
def coefficientHomologyZeroLinearEquiv :
    (coefficientComplex R L M).homology 0 ≃ₗ[R]
      M ⧸ ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆ :=
  let K := coefficientComplex R L M
  let e0 : (K.sc 0).X₂ ≃ₗ[R] M := coefficientZeroEquiv R L M
  ((K.isoHomologyι₀ ≪≫ (K.sc 0).moduleCatOpcyclesIso).toLinearEquiv).trans
    (Submodule.Quotient.equiv (K.sc 0).f.hom.range
      (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule
      e0 (by exact coefficientIncomingRange_zeroCoordinates R L M))

/-- The class of an empty exterior word maps to its coefficient coinvariant class. -/
theorem coefficientHomologyZeroLinearEquiv_class (m : M) :
    coefficientHomologyZeroLinearEquiv R L M
        ((coefficientComplex R L M).isoHomologyι₀.inv
          ((coefficientComplex R L M).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))) =
      LieSubmodule.Quotient.mk
        (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆) m := by
  let K := coefficientComplex R L M
  let e0 : (K.sc 0).X₂ ≃ₗ[R] M := coefficientZeroEquiv R L M
  let Q := Submodule.Quotient.equiv (K.sc 0).f.hom.range
    (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule
    e0 (by exact coefficientIncomingRange_zeroCoordinates R L M)
  let a : K.X 0 := exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m
  have h := congrArg Q (coefficientHomologyZeroRangeEquiv_class K a)
  have hQ : Q (Submodule.Quotient.mk a) =
      LieSubmodule.Quotient.mk
        (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆) m := by
    change LieSubmodule.Quotient.mk
        (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆)
        (coefficientZeroEquiv R L M
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)) = _
    rw [coefficientZeroEquiv_ι_tmul]
  exact h.trans hQ

/-- Coinvariant classes have the empty-word homology representatives. -/
@[simp]
theorem coefficientHomologyZeroLinearEquiv_symm_mk (m : M) :
    (coefficientHomologyZeroLinearEquiv R L M).symm
        (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆) m) =
      (coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)) := by
  apply (coefficientHomologyZeroLinearEquiv R L M).injective
  rw [LinearEquiv.apply_symm_apply, coefficientHomologyZeroLinearEquiv_class]

/-- The categorical coinvariant comparison uses the native universe lift of
the coefficient quotient into the universe of the complex. -/
def coefficientHomologyZeroIso :
    (coefficientComplex R L M).homology 0 ≅
      ModuleCat.of R
        (ULift.{max u v w, w}
          (M ⧸ ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆)) :=
  ((coefficientHomologyZeroLinearEquiv R L M).trans ULift.moduleEquiv.symm).toModuleIso

/-- The categorical comparison takes an representative to its lifted
native coefficient coinvariant class. -/
theorem coefficientHomologyZeroIso_class (m : M) :
    (coefficientHomologyZeroIso R L M).hom
        ((coefficientComplex R L M).isoHomologyι₀.inv
          ((coefficientComplex R L M).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))) =
      ULift.up (LieSubmodule.Quotient.mk
        (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆) m) := by
  exact congrArg ULift.up (coefficientHomologyZeroLinearEquiv_class R L M m)


section Maps

variable {N : Type w'} [AddCommGroup N] [Module R N]
  [LieRingModule L N] [LieModule R L N]

private theorem coefficientActionRelations_le_comap (f : M →ₗ⁅R,L⁆ N) :
    (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule ≤
      (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L N)⁆).toSubmodule.comap
        f.toLinearMap := by
  have h : (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).map f ≤
      ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L N)⁆ := by
    rw [LieSubmodule.map_bracket_eq]
    exact LieSubmodule.mono_lie_right (⊤ : LieIdeal R L) le_top
  exact (LieSubmodule.map_le_iff_le_comap).1 h

/-- The native quotient map induced by a coefficient Lie-module morphism.
The coefficient universes are independent. -/
def coefficientCoinvariantsMap (f : M →ₗ⁅R,L⁆ N) :
    M ⧸ ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆ →ₗ[R]
      N ⧸ ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L N)⁆ :=
  (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule.mapQ
    (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L N)⁆).toSubmodule f.toLinearMap
    (by exact coefficientActionRelations_le_comap R L M f)

/-- The induced quotient map applies the coefficient morphism to a representative. -/
theorem coefficientCoinvariantsMap_mk (f : M →ₗ⁅R,L⁆ N) (m : M) :
    coefficientCoinvariantsMap R L M f
        (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆) m) =
      LieSubmodule.Quotient.mk
        (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L N)⁆) (f m) :=
  rfl

end Maps

section Naturality

-- Native chain maps and homology maps share one ModuleCat universe.
variable {N : Type w} [AddCommGroup N] [Module R N]
  [LieRingModule L N] [LieModule R L N]

/-- The native homology map takes an empty-word representative to the
representative obtained by applying its coefficient morphism. -/
theorem coefficientHomologyMap_zero_class (f : M →ₗ⁅R,L⁆ N) (m : M) :
    (HomologicalComplex.homologyMap (coefficientComplexMap R L M f) 0).hom
        ((coefficientComplex R L M).isoHomologyι₀.inv
          ((coefficientComplex R L M).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))) =
      (coefficientComplex R L N).isoHomologyι₀.inv
        ((coefficientComplex R L N).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] f m)) := by
  let K := coefficientComplex R L M
  let K' := coefficientComplex R L N
  let F := coefficientComplexMap R L M f
  let a : K.X 0 := exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m
  have hι := congrArg
    (fun g : K.opcycles 0 ⟶ K'.homology 0 => g.hom (K.pOpcycles 0 a))
    (ChainComplex.isoHomologyι₀_inv_naturality F)
  have hp := congrArg
    (fun g : K.X 0 ⟶ K'.opcycles 0 => g.hom a)
    (HomologicalComplex.p_opcyclesMap F 0)
  have hf := congrArg
    (fun b : K'.X 0 => (K'.pOpcycles 0).hom b)
    (coefficientComplexMap_f_tmul R L M f 0
      (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L)) m)
  exact hι.trans (congrArg (fun b : K'.opcycles 0 => K'.isoHomologyι₀.inv.hom b)
    (hp.trans hf))

/-- The degree-zero homology comparison is natural for coefficient
morphisms, and its quotient map is the native map on the action relations. -/
theorem coefficientHomologyZeroLinearEquiv_naturality (f : M →ₗ⁅R,L⁆ N)
    (a : (coefficientComplex R L M).homology 0) :
    coefficientHomologyZeroLinearEquiv R L N
        ((HomologicalComplex.homologyMap (coefficientComplexMap R L M f) 0).hom a) =
      coefficientCoinvariantsMap R L M f (coefficientHomologyZeroLinearEquiv R L M a) := by
  obtain ⟨m, hm⟩ := LieSubmodule.Quotient.surjective_mk'
    ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆
      (coefficientHomologyZeroLinearEquiv R L M a)
  change LieSubmodule.Quotient.mk
    (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆) m =
      coefficientHomologyZeroLinearEquiv R L M a at hm
  have ha : a = (coefficientComplex R L M).isoHomologyι₀.inv
      ((coefficientComplex R L M).pOpcycles 0
        (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)) := by
    apply (coefficientHomologyZeroLinearEquiv R L M).injective
    rw [coefficientHomologyZeroLinearEquiv_class]
    exact hm.symm
  rw [ha, coefficientHomologyMap_zero_class, coefficientHomologyZeroLinearEquiv_class,
    coefficientHomologyZeroLinearEquiv_class, coefficientCoinvariantsMap_mk]

end Naturality

/-- Every native action value represents zero in degree-zero homology. -/
theorem coefficientHomologyZero_lie_class (x : L) (m : M) :
    (coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] ⁅x, m⁆)) = 0 := by
  apply (coefficientHomologyZeroLinearEquiv R L M).injective
  rw [coefficientHomologyZeroLinearEquiv_class, map_zero]
  apply (Submodule.Quotient.mk_eq_zero
    (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).2
  rw [coefficientActionRelations_eq_range]
  refine ⟨x ⊗ₜ[R] m, ?_⟩
  simp only [LieModuleHom.coe_toLinearMap, LieModule.toModuleHom_apply]

section Trivial

variable [LieModule.IsTrivial L M]

omit [LieModule R L M] in
private theorem coefficientActionRelations_eq_bot :
    (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule = ⊥ := by
  have h : ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆ = ⊥ := by
    apply (LieSubmodule.lie_eq_bot_iff
      (⊤ : LieSubmodule R L M) (⊤ : LieIdeal R L)).2
    intro x hx m hm
    exact trivial_lie_zero L M x m
  exact congrArg LieSubmodule.toSubmodule h

/-- A trivial coefficient action specializes the general coinvariant comparison
by the native quotient equivalence for the zero relation submodule. -/
def coefficientHomologyZeroTrivialLinearEquiv :
    (coefficientComplex R L M).homology 0 ≃ₗ[R] M :=
  (coefficientHomologyZeroLinearEquiv R L M).trans
    ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule.quotEquivOfEqBot
      (by exact coefficientActionRelations_eq_bot R L M))

/-- The representative has its given coefficient under a trivial action. -/
theorem coefficientHomologyZeroTrivialLinearEquiv_class (m : M) :
    coefficientHomologyZeroTrivialLinearEquiv R L M
        ((coefficientComplex R L M).isoHomologyι₀.inv
          ((coefficientComplex R L M).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))) = m := by
  change (⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule.quotEquivOfEqBot
      (by exact coefficientActionRelations_eq_bot R L M)
      (coefficientHomologyZeroLinearEquiv R L M
        ((coefficientComplex R L M).isoHomologyι₀.inv
          ((coefficientComplex R L M).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)))) = _
  rw [coefficientHomologyZeroLinearEquiv_class]
  exact Submodule.quotEquivOfEqBot_apply_mk _ _ m

end Trivial

end Coinvariants

end ChevalleyEilenberg
