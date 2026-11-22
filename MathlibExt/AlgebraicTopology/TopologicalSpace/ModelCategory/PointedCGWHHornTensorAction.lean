/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHornIntervalAction
public import MathlibExt.CategoryTheory.Monoidal.IntervalAction
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Free
public import MathlibExt.Topology.Category.PointedCGWH.Closed

/-!
# Freely based horn interval actions and arbitrary smash coefficients

The actual geometric horn homotopy is transported through the existing
computed costar CoreMonoidal data. Its complete zero/one and relative-fix
maps are then tensored with an arbitrary pointed CGWH object using the
selected inverse associator. No coefficient cofibrancy, local compactness,
model axiom or supplied deformation-retract dictionary is required.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace PointedCGWH

/-- The original native horn retraction after freely adjoining its basepoint. -/
noncomputable def freePointHornRetraction (n : ℕ) (i : Fin (n + 2)) :
    (Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})) ⟶
      (Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i)) :=
  (Under.costar CGWH.point).map (CGWH.realizedHornRetraction n i)

/-- The complete actual free-point interval action uses the existing computed
costar tensor isomorphism, followed by the map of the original horn homotopy. -/
noncomputable def freePointHornIntervalAction (n : ℕ) (i : Fin (n + 2)) :
    (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval ⊗
        (Under.costar CGWH.point.{u, v}).obj
          (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})) ⟶
      (Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})) := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  exact Functor.CoreMonoidal.intervalActionImage F hF
    (CGWH.realizedHornIntervalAction.{u, v} n i)

/-- The actual time endpoint of the freely based interval, with the selected unit map. -/
noncomputable def freePointIntervalEndpoint (t : unitInterval) :
    𝟙_ PointedCGWH.{u, v} ⟶
      (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  exact hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint t)

/-- Collapse the actual freely based interval to the selected smash unit. -/
noncomputable def freePointIntervalCollapse :
    (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval ⟶
      𝟙_ PointedCGWH.{u, v} := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  exact Functor.CoreMonoidal.intervalCollapseImage F hF
    (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval)

/-- The original free-point horn inclusion has the complete original retraction. -/
theorem freePointHorn_inclusion_ret (n : ℕ) (i : Fin (n + 2)) :
    (Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} n i) ≫
        freePointHornRetraction n i = 𝟙 _ := by
  dsimp only [freePointHornRetraction]
  rw [← Functor.map_comp, CGWH.realizedHornInclusion_ret]
  exact CategoryTheory.Functor.map_id (Under.costar CGWH.point) _

/-- At zero, the actual complete free-point horn action is the identity. -/
theorem freePointHornIntervalAction_zero (n : ℕ) (i : Fin (n + 2)) :
    (λ_ ((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})))).inv ≫
        (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫
        freePointHornIntervalAction n i = 𝟙 _ := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  change (λ_ _).inv ≫
      ((hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint 0)) ⊗ₘ 𝟙 _) ≫
        Functor.CoreMonoidal.intervalActionImage F hF
          (CGWH.realizedHornIntervalAction.{u, v} n i) = 𝟙 _
  rw [Functor.CoreMonoidal.intervalActionImage_endpoint F hF
    (CGWH.realizedHornIntervalAction.{u, v} n i) (CGWH.homotopyIntervalEndpoint 0)
    (𝟙 _) (CGWH.realizedHornIntervalAction_zero n i), F.map_id]

/-- At one, the complete free-point action is inclusion after the original retraction. -/
theorem freePointHornIntervalAction_one (n : ℕ) (i : Fin (n + 2)) :
    (λ_ ((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})))).inv ≫
        (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫
        freePointHornIntervalAction n i =
      freePointHornRetraction n i ≫
        (Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} n i) := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  change (λ_ _).inv ≫
      ((hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint 1)) ⊗ₘ 𝟙 _) ≫
        Functor.CoreMonoidal.intervalActionImage F hF
          (CGWH.realizedHornIntervalAction.{u, v} n i) = _
  rw [Functor.CoreMonoidal.intervalActionImage_endpoint F hF
    (CGWH.realizedHornIntervalAction.{u, v} n i) (CGWH.homotopyIntervalEndpoint 1)
    (CGWH.realizedHornRetraction n i ≫ CGWH.realizedHornInclusion.{v, u} n i)
    (CGWH.realizedHornIntervalAction_one n i), F.map_comp]
  rfl

/-- The free-point horn action fixes the complete original included subspace. -/
theorem freePointHornIntervalAction_fix (n : ℕ) (i : Fin (n + 2)) :
    (𝟙 _ ⊗ₘ (Under.costar CGWH.point.{u, v}).map
      (CGWH.realizedHornInclusion.{v, u} n i)) ≫ freePointHornIntervalAction n i =
      (freePointIntervalCollapse ⊗ₘ 𝟙 _) ≫
        (λ_ ((Under.costar CGWH.point.{u, v}).obj
          (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i)))).hom ≫
        (Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} n i) := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  change (𝟙 _ ⊗ₘ F.map (CGWH.realizedHornInclusion.{v, u} n i)) ≫
      Functor.CoreMonoidal.intervalActionImage F hF
        (CGWH.realizedHornIntervalAction.{u, v} n i) =
      (Functor.CoreMonoidal.intervalCollapseImage F hF
        (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval) ⊗ₘ 𝟙 _) ≫
          (λ_ _).hom ≫ F.map (CGWH.realizedHornInclusion.{v, u} n i)
  exact Functor.CoreMonoidal.intervalActionImage_fix F hF
    (CGWH.realizedHornIntervalAction.{u, v} n i) (CGWH.realizedHornInclusion.{v, u} n i)
    (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval)
    (CGWH.realizedHornIntervalAction_fix n i)

/-- Tensor the actual freely based horn homotopy with an arbitrary pointed object. -/
noncomputable def freePointHornTensorIntervalAction (n : ℕ) (i : Fin (n + 2))
    (K : PointedCGWH.{u, v}) :
    (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval ⊗
        ((Under.costar CGWH.point.{u, v}).obj
          (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})) ⊗ K) ⟶
      (Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})) ⊗ K :=
  tensorIntervalMap (freePointHornIntervalAction n i) K

/-- The original free-point horn retraction still retracts after tensoring with K. -/
theorem freePointHornTensor_inclusion_ret (n : ℕ) (i : Fin (n + 2))
    (K : PointedCGWH.{u, v}) :
    ((Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K) ≫
        (freePointHornRetraction n i ⊗ₘ 𝟙 K) = 𝟙 _ := by
  rw [tensorHom_comp_tensorHom, freePointHorn_inclusion_ret,
    Category.id_comp, id_tensorHom_id]

/-- The tensor action is the full identity at time zero. -/
theorem freePointHornTensorIntervalAction_zero (n : ℕ) (i : Fin (n + 2))
    (K : PointedCGWH.{u, v}) :
    (λ_ (((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))) ⊗ K)).inv ≫
        (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫
        freePointHornTensorIntervalAction n i K = 𝟙 _ := by
  change (λ_ _).inv ≫ (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫
    tensorIntervalMap (freePointHornIntervalAction n i) K = 𝟙 _
  rw [tensorIntervalMap_endpoint, freePointHornIntervalAction_zero,
    id_tensorHom_id]

/-- The tensor action at one is the original tensor retraction followed by inclusion. -/
theorem freePointHornTensorIntervalAction_one (n : ℕ) (i : Fin (n + 2))
    (K : PointedCGWH.{u, v}) :
    (λ_ (((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))) ⊗ K)).inv ≫
        (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫
        freePointHornTensorIntervalAction n i K =
      (freePointHornRetraction n i ⊗ₘ 𝟙 K) ≫
        ((Under.costar CGWH.point.{u, v}).map
          (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K) := by
  change (λ_ _).inv ≫ (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫
    tensorIntervalMap (freePointHornIntervalAction n i) K = _
  rw [tensorIntervalMap_endpoint, freePointHornIntervalAction_one]
  simpa only [Category.id_comp] using
    (tensorHom_comp_tensorHom (freePointHornRetraction n i) (𝟙 K)
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} n i))
      (𝟙 K)).symm

/-- The complete tensor action fixes the whole original included free-point horn tensor K. -/
theorem freePointHornTensorIntervalAction_fix (n : ℕ) (i : Fin (n + 2))
    (K : PointedCGWH.{u, v}) :
    (𝟙 _ ⊗ₘ ((Under.costar CGWH.point.{u, v}).map
      (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K)) ≫
        freePointHornTensorIntervalAction n i K =
      (freePointIntervalCollapse ⊗ₘ 𝟙 _) ≫
        (λ_ (((Under.costar CGWH.point.{u, v}).obj
          (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i))) ⊗ K)).hom ≫
        ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K) := by
  change (𝟙 _ ⊗ₘ ((Under.costar CGWH.point).map
      (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K)) ≫
      tensorIntervalMap (freePointHornIntervalAction n i) K = _
  exact tensorIntervalMap_fix _ _ _ (freePointHornIntervalAction_fix n i) K

end PointedCGWH
