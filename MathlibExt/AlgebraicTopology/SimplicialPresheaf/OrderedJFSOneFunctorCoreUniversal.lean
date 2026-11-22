/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorCoreMapping
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreMappingComponents

/-!
# The universal original one-fold functor core

The constructed core adjunction classifies maps from each original groupoidal
source into the full functor object. Its actual zero adjunct, followed by the
specified weak derived-end comparison, is the scalar homotopy-category map.
Independent scalar replacement conventions retain the same Hom function.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen MonoidalCategory
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialPresheaf.OrderedJFS.OneFunctor.Core

private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

/-- The original baseline groupoidal source, with its unchanged unit and functor action. -/
abbrev groupoidal : SSet.{u} ⥤ Original.{u} 1 :=
  BaselineConstantCoreComparison.constantReplacement

/-- The genuine universal core Hom function, with the actual derived scalar end as target. -/
def homEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) ≃
    (scalarHo.obj K ⟶ scalarHo.obj (((localDerivedEnd family.{u}).obj (op A)).obj Z)) :=
  (SimplicialPresheaf.CoreDerivedAdjunction.homEquiv family.{u}
    (ConstantEvaluation.zeroIsTerminal 1) K (object A Z) (object_localFibrant A Z hZ)).trans
    (Iso.homCongr (Iso.refl _) (rawMappingIso A Z hZ))

/-- The universal function uses the original zero adjunct and the actual forward derived-end leg. -/
theorem homEquiv_apply (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) :
    homEquiv A K Z hZ h =
      SimplicialPresheaf.CoreDerivedAdjunction.homEquiv family.{u}
        (ConstantEvaluation.zeroIsTerminal 1) K (object A Z)
        (object_localFibrant A Z hZ) h ≫ scalarHo.map ((derivedComparison A).app Z) := by
  change (𝟙 _) ≫ _ ≫ (rawMappingIso A Z hZ).hom = _
  rw [Category.id_comp]
  rfl

/-- Every strict representative has its original baseline-unit and zero-evaluation characteristic. -/
theorem homEquiv_map (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (g : groupoidal.obj K ⟶ object A Z) :
    homEquiv A K Z hZ ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map g) =
      scalarHo.map (((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K).app
        (op (ConstantEvaluation.zeroTuple 1)) ≫ g.app (op (ConstantEvaluation.zeroTuple 1)) ≫
          (derivedComparison A).app Z) := by
  rw [homEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_map,
    ← scalarHo.map_comp]
  rfl

/-- The universal function retains the same full Cartesian transpose. -/
theorem homEquiv_currying (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (f : A ⊗ groupoidal.obj K ⟶ Z) :
    homEquiv A K Z hZ ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (curry f)) =
      scalarHo.map (((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K).app
        (op (ConstantEvaluation.zeroTuple 1)) ≫ (curry f).app (op (ConstantEvaluation.zeroTuple 1)) ≫
          (derivedComparison A).app Z) :=
  homEquiv_map A K Z hZ (curry f)

/-- Original target maps act through the same actual derived R action. -/
theorem homEquiv_target (A : Original.{u} 1) (K : SSet.{u}) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (g : Z ⟶ V)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) :
    homEquiv A K V hV (h ≫
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (targetMap A g)) =
      homEquiv A K Z hZ h ≫ scalarHo.map (localDerivedPostcomp family.{u} A g) := by
  rw [homEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_target family.{u}
    (ConstantEvaluation.zeroIsTerminal 1) K (object_localFibrant A Z hZ)
      (object_localFibrant A V hV) h (targetMap A g), homEquiv_apply]
  rw [Category.assoc, ← scalarHo.map_comp, derivedComparison_target_app, scalarHo.map_comp,
    ← Category.assoc]

/-- Scalar source maps retain the actual original groupoidal source action. -/
theorem homEquiv_scalar (A : Original.{u} 1) {K L : SSet.{u}} (k : K ⟶ L)
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj L) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) :
    homEquiv A K Z hZ
      ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (groupoidal.map k) ≫ h) =
      scalarHo.map k ≫ homEquiv A L Z hZ h := by
  rw [homEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_source, homEquiv_apply,
    Category.assoc]

/-- Source contravariance retains the same actual full functor map and derived Q action. -/
theorem homEquiv_source {A B : Original.{u} 1} (f : A ⟶ B) (K : SSet.{u})
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object B Z)) :
    homEquiv A K Z hZ
      (h ≫ (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (sourceMap f Z)) =
      homEquiv B K Z hZ h ≫ scalarHo.map (localDerivedPrecomp family.{u} f Z) := by
  rw [homEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_target family.{u}
    (ConstantEvaluation.zeroIsTerminal 1) K (object_localFibrant B Z hZ)
      (object_localFibrant A Z hZ) h (sourceMap f Z), homEquiv_apply]
  rw [Category.assoc, ← scalarHo.map_comp, derivedComparison_source_app, scalarHo.map_comp,
    ← Category.assoc]

private abbrev fixedScalarHomEquiv (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K L : SSet.{u}) :
    SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj L)) ≃ (scalarHo.obj K ⟶ scalarHo.obj L) :=
  CoreMappingComponents.fixedHomEquiv (ConstantEvaluation.zeroTuple 1) e K (scalarConst.obj L)

/-- Core mapping components classify the same scalar-derived Hom in any fixed scalar convention. -/
def componentEquiv (A : Original.{u} 1) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.π₀ (((localDerivedEnd family.{u}).obj (op (groupoidal.obj K))).obj (object A Z)) ≃
      SSet.π₀ ((ihom (e.Q.obj K)).obj
        (e.R.obj (((localDerivedEnd family.{u}).obj (op A)).obj Z))) := by
  let _ : ModelCategory (Original.{u} 1) := (originalLocalSmithData family.{u}).model
  exact (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv family.{u}
    (groupoidal.obj K) (object A Z)).trans ((homEquiv A K Z hZ).trans
      (fixedScalarHomEquiv e K _).symm)

/-- Independent scalar factors retain the same genuine universal Hom function. -/
theorem componentEquiv_ho (A : Original.{u} 1) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (c : SSet.π₀ (((localDerivedEnd family.{u}).obj
      (op (groupoidal.obj K))).obj (object A Z))) :
    let _ : ModelCategory (Original.{u} 1) := (originalLocalSmithData family.{u}).model
    fixedScalarHomEquiv e K _ (componentEquiv A e K Z hZ c) =
      homEquiv A K Z hZ (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv family.{u}
        (groupoidal.obj K) (object A Z) c) := by
  let _ : ModelCategory (Original.{u} 1) := (originalLocalSmithData family.{u}).model
  exact (fixedScalarHomEquiv e K _).apply_symm_apply _

end SimplicialPresheaf.OrderedJFS.OneFunctor.Core
