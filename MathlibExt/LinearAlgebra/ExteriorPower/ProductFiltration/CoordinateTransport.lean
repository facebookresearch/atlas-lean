/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.ProductFiltration.AssociatedGradedMap

/-!
# Transporting exterior filtrations through module coordinates

A module equivalence with a product transports the mixed-weight filtration
and its successive quotient coordinates. A triangular linear map respects
these transported stages, and its quotient map is the tensor of the two
diagonal exterior maps. The carrier universes remain independent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x v' w' x'

namespace exteriorPower.ProductFiltration.CoordinateTransport

-- Reuse the stage group selected by the original native quotient-coordinate API.
attribute [local instance] exteriorPower.ProductFiltration.filtration_addCommGroup

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]
  {X : Type x} [AddCommGroup X] [Module R X]
  (m : ℕ) (e : X ≃ₗ[R] (⋀[R]^m (M × N)))

def filtration (q : ℕ) : Submodule R X :=
  (ProductFiltration.filtration R M N m q).comap e.toLinearMap

def stageEquiv (q : ℕ) :
    filtration R M N m e q ≃ₗ[R] ProductFiltration.filtration R M N m q :=
  e.ofSubmodule' (ProductFiltration.filtration R M N m q)

def nextStage (q : ℕ) : Submodule R (filtration R M N m e q) :=
  (filtration R M N m e (q + 1)).comap (filtration R M N m e q).subtype

theorem nextStage_image (q : ℕ) :
    (nextStage R M N m e q).map (stageEquiv R M N m e q).toLinearMap =
      ProductFiltration.nextStage R M N m q := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact hz
  · intro y hy
    refine ⟨(stageEquiv R M N m e q).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
    change e (e.symm y.val) ∈ ProductFiltration.filtration R M N m (q + 1)
    rw [LinearEquiv.apply_symm_apply]
    exact hy

abbrev associatedGraded (q : ℕ) := filtration R M N m e q ⧸ nextStage R M N m e q

def quotientEquiv (q : ℕ) :
    associatedGraded R M N m e q ≃ₗ[R] ProductFiltration.associatedGraded R M N m q :=
  by
    let P : Submodule R (filtration R M N m e q) := nextStage R M N m e q
    let Q : Submodule R (ProductFiltration.filtration R M N m q) :=
      ProductFiltration.nextStage R M N m q
    let E : filtration R M N m e q ≃ₗ[R] ProductFiltration.filtration R M N m q :=
      stageEquiv R M N m e q
    have hE : P.map E.toLinearMap = Q := nextStage_image R M N m e q
    exact Submodule.Quotient.equiv P Q E hE

def coordinateEquiv (q : ℕ) (hq : q ≤ m) :
    associatedGraded R M N m e q ≃ₗ[R] (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) :=
  (quotientEquiv R M N m e q).trans (ProductFiltration.associatedGradedEquiv R M N m q hq)

theorem quotientEquiv_mk (q : ℕ) (z : filtration R M N m e q) :
    quotientEquiv R M N m e q (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (stageEquiv R M N m e q z) := rfl

/-- The actual transported stage inclusion has a native coordinate-clipping retraction. -/
def retraction (q : ℕ) : X →ₗ[R] filtration R M N m e q :=
  (stageEquiv R M N m e q).symm.toLinearMap.comp
    ((ProductFiltration.projectionToFiltration R M N m q).comp e.toLinearMap)

theorem retraction_subtype (q : ℕ) (z : filtration R M N m e q) :
    retraction R M N m e q z.val = z := by
  apply (stageEquiv R M N m e q).injective
  change stageEquiv R M N m e q
    ((stageEquiv R M N m e q).symm
      (ProductFiltration.projectionToFiltration R M N m q (e z.val))) =
    stageEquiv R M N m e q z
  rw [LinearEquiv.apply_symm_apply]
  exact ProductFiltration.projectionToFiltration_subtype R M N m q
    (stageEquiv R M N m e q z)

variable {R M N m}
  {M' : Type v'} [AddCommGroup M'] [Module R M']
  {N' : Type w'} [AddCommGroup N'] [Module R N']
  {X' : Type x'} [AddCommGroup X'] [Module R X']
  (e' : X' ≃ₗ[R] (⋀[R]^m (M' × N')))
  (f : FirstSummandMap (R := R) (M := M) (N := N) (M' := M') (N' := N'))

def operator : X →ₗ[R] X' :=
  e'.symm.toLinearMap.comp ((exteriorPower.map m f.map).comp e.toLinearMap)

def stageMap (q : ℕ) :
    filtration R M N m e q →ₗ[R] filtration R M' N' m e' q :=
  (stageEquiv R M' N' m e' q).symm.toLinearMap.comp
    ((f.stageMap m q).comp (stageEquiv R M N m e q).toLinearMap)

theorem stageMap_value (q : ℕ) (z : filtration R M N m e q) :
    (stageMap e e' f q z : X') = operator e e' f z.val := by
  change e'.symm (exteriorPower.map m f.map (e z.val)) = operator e e' f z.val
  rfl

theorem stageMap_coordinates (q : ℕ) (z : filtration R M N m e q) :
    stageEquiv R M' N' m e' q (stageMap e e' f q z) =
      f.stageMap m q (stageEquiv R M N m e q z) := by
  change stageEquiv R M' N' m e' q
    ((stageEquiv R M' N' m e' q).symm
      (f.stageMap m q (stageEquiv R M N m e q z))) =
    f.stageMap m q (stageEquiv R M N m e q z)
  exact (stageEquiv R M' N' m e' q).apply_symm_apply _

theorem stageMap_next (q : ℕ) :
    nextStage R M N m e q ≤ (nextStage R M' N' m e' q).comap (stageMap e e' f q) := by
  intro z hz
  change e' ((stageMap e e' f q z).val) ∈ ProductFiltration.filtration R M' N' m (q + 1)
  rw [stageMap_value]
  change e' (e'.symm (exteriorPower.map m f.map (e z.val))) ∈
    ProductFiltration.filtration R M' N' m (q + 1)
  rw [LinearEquiv.apply_symm_apply]
  exact f.map_mem_filtration m (q + 1) (e z.val) hz

def gradeMap (q : ℕ) :
    associatedGraded R M N m e q →ₗ[R] associatedGraded R M' N' m e' q :=
  (nextStage R M N m e q).mapQ (nextStage R M' N' m e' q)
    (stageMap e e' f q) (stageMap_next e e' f q)

theorem gradeMap_mk (q : ℕ) (z : filtration R M N m e q) :
    gradeMap e e' f q (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (stageMap e e' f q z) := by
  rw [gradeMap, Submodule.mapQ_apply]

/-- The ACTUAL quotient map retains the diagonal exterior tensor coordinate. -/
theorem coordinateEquiv_gradeMap (q : ℕ) (hq : q ≤ m)
    (z : associatedGraded R M N m e q) :
    coordinateEquiv R M' N' m e' q hq (gradeMap e e' f q z) =
      TensorProduct.map (exteriorPower.map q f.first) (exteriorPower.map (m - q) f.relative)
        (coordinateEquiv R M N m e q hq z) := by
  refine Submodule.Quotient.induction_on _ z (fun x => ?_)
  rw [gradeMap_mk]
  change ProductFiltration.associatedGradedEquiv R M' N' m q hq
      (Submodule.Quotient.mk (stageEquiv R M' N' m e' q (stageMap e e' f q x))) =
    TensorProduct.map (exteriorPower.map q f.first) (exteriorPower.map (m - q) f.relative)
      (ProductFiltration.associatedGradedEquiv R M N m q hq
        (Submodule.Quotient.mk (stageEquiv R M N m e q x)))
  rw [stageMap_coordinates]
  exact f.associatedGradedEquiv_gradeMap m q hq
    (Submodule.Quotient.mk (stageEquiv R M N m e q x))

end exteriorPower.ProductFiltration.CoordinateTransport

end
