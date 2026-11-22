/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionDerivedMaps

/-!
# The actual closed comparison for every allowed first-JT source replacement

A supplied categorical weak map into the original first right image is kept
in the actual derived counit. Restricting the full CSS power by this counit
and applying the entire first-left power Iso gives the native functor object
of that supplied source. Its comparison, categorical weakness and core map
are proved from the original model and maps, without fibrancy of the source.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.FirstProjection

/-- The whole comparison uses the supplied source map in the original derived counit. -/
def replacementComparison (W V : SimplicialSpace.{u}) (Q : SSet.{u}) (q : Q ⟶ right.obj W) :
    right.obj ((ihom W).obj V) ⟶ (ihom Q).obj (right.obj V) :=
  right.map ((pre (derivedCounit W Q q)).app V) ≫ (functorObjectIso Q).hom.app V

/-- Its factorization retains precisely the original comparison and the supplied native restriction. -/
theorem replacementComparison_factor (W V : SimplicialSpace.{u}) (Q : SSet.{u})
    (q : Q ⟶ right.obj W) :
    replacementComparison W V Q q = comparison W V ≫ (pre q).app (right.obj V) := by
  have h := comparison_restriction Q W V (derivedCounit W Q q)
  have hq : adjunction.homEquiv Q W (derivedCounit W Q q) = q := derivedCounit_transpose W Q q
  rw [hq] at h
  exact h

/-- Every allowed source replacement gives a genuine categorical equivalence to its actual native power. -/
theorem replacementComparison_categoricalWeak (W V : SimplicialSpace.{u}) (Q : SSet.{u})
    (q : Q ⟶ right.obj W) (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hq : SSet.categoricalEquivalences q) : SSet.categoricalEquivalences (replacementComparison W V Q q) := by
  unfold replacementComparison
  exact SSet.categoricalEquivalences.comp_mem _ _
    (right_categoricalWeak _ (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal W V hV)
      (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal (left.obj Q) V hV)
      (power_source_rezkWeak (derivedCounit W Q q) (derivedCounit_rezkWeak W hW Q q hq) V hV))
    (SSet.categoricalEquivalences.of_isIso _)

/-- Every scalar source gives a genuine native functor quasicategory at a complete CSS target. -/
theorem replacementFunctor_quasicategory (Q : SSet.{u}) (V : SimplicialSpace.{u})
    (hV : completeSegalSpaces V) : SSet.Quasicategory ((ihom Q).obj (right.obj V)) := by
  let e := (functorObjectIso Q).app V
  have hq := comparison_source_quasicategory (left.obj Q) V hV
  let a : Arrow.mk (terminal.from (right.obj ((ihom (left.obj Q)).obj V))) ≅
      Arrow.mk (terminal.from ((ihom Q).obj (right.obj V))) :=
    Arrow.isoMk e (Iso.refl _) (by exact terminal.hom_ext _ _)
  exact (SSet.categoricalFibrations.terminalFrom_iff_quasicategory _).mp
    ((SSet.categoricalFibrations.arrow_mk_iso_iff a).mp
      ((SSet.categoricalFibrations.terminalFrom_iff_quasicategory _).mpr hq))

/-- The same replacement comparison restricts to a weak map of its actual native cores. -/
theorem replacementComparison_coreWeak (W V : SimplicialSpace.{u}) (Q : SSet.{u})
    (q : Q ⟶ right.obj W) (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hq : SSet.categoricalEquivalences q) :
    SSet.realizationWeakEquivalences (SSet.coreFunctor.map (replacementComparison W V Q q)) := by
  let _ : SSet.Quasicategory (right.obj ((ihom W).obj V)) := comparison_source_quasicategory W V hV
  let _ : SSet.Quasicategory ((ihom Q).obj (right.obj V)) := replacementFunctor_quasicategory Q V hV
  change SSet.realizationWeakEquivalences (SSet.core.map (replacementComparison W V Q q))
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    (SSet.core_map_mem_W_of_categoricalEquivalence
      (replacementComparison_categoricalWeak W V Q q hW hV hq))

/-- Changing the supplied source map retains its exact native restriction composite. -/
theorem replacementComparison_source (W V : SimplicialSpace.{u}) {Q P : SSet.{u}}
    (q : Q ⟶ right.obj W) (k : P ⟶ Q) :
    replacementComparison W V P (k ≫ q) = replacementComparison W V Q q ≫ (pre k).app (right.obj V) := by
  rw [replacementComparison_factor, replacementComparison_factor, pre_map, NatTrans.comp_app,
    Category.assoc]

/-- Target naturality uses the same original CSS power map and the same supplied source. -/
theorem replacementComparison_target (W : SimplicialSpace.{u}) {V U : SimplicialSpace.{u}}
    (g : V ⟶ U) (Q : SSet.{u}) (q : Q ⟶ right.obj W) :
    right.map ((ihom W).map g) ≫ replacementComparison W U Q q =
      replacementComparison W V Q q ≫ (ihom Q).map (right.map g) := by
  rw [replacementComparison_factor, replacementComparison_factor, ← Category.assoc,
    comparison_target, Category.assoc, (pre q).naturality (right.map g)]
  simp only [Category.assoc]

/-- The unchanged right image recovers the original canonical comparison. -/
theorem replacementComparison_id (W V : SimplicialSpace.{u}) :
    replacementComparison W V (right.obj W) (𝟙 _) = comparison W V := by
  rw [replacementComparison_factor, pre_id, NatTrans.id_app, Category.comp_id]

/-- A supplied target replacement retains its actual derived unit as the source of this comparison. -/
theorem replacementComparison_from_unit (Q : SSet.{u}) (W V : SimplicialSpace.{u})
    (r : left.obj Q ⟶ W) :
    replacementComparison W V Q (derivedUnit Q W r) =
      right.map ((pre r).app V) ≫ (functorObjectIso Q).hom.app V := by
  unfold replacementComparison
  rw [derivedUnit_counit]

end SimplicialSpace.FirstProjection
