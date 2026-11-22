/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorComparison

/-!
# The original first-JT derived unit and counit maps

Each supplied weak replacement map is retained. The actual Hovey criterion
proves weakness of its unit transpose, and the original left weak-preservation
and counit prove weakness of the derived counit. Both native triangles and
all endpoint naturality equations use these same maps.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.FirstProjection

/-- The actual unit followed by the right image of the supplied target replacement. -/
def derivedUnit (Q : SSet.{u}) (W : SimplicialSpace.{u}) (r : left.obj Q ⟶ W) :
    Q ⟶ right.obj W := adjunction.homEquiv Q W r

/-- The unit retains its literal original first-JT factorization. -/
theorem derivedUnit_eq (Q : SSet.{u}) (W : SimplicialSpace.{u}) (r : left.obj Q ⟶ W) :
    derivedUnit Q W r = adjunction.unit.app Q ≫ right.map r := rfl

private theorem derivedUnit_wrapped (Q : SSet.{u}) (W : SimplicialSpace.{u})
    (r : left.obj Q ⟶ W) :
    derivedUnit Q W r = JoyalSSet.forget.map
      (comparisonAdjunction.homEquiv (JoyalSSet.ofSSet.obj Q) W r) := by
  ext m x
  rfl

/-- A genuine fibrant replacement gives the actual derived categorical unit equivalence. -/
theorem derivedUnit_categoricalWeak (Q : SSet.{u}) (W : SimplicialSpace.{u})
    (r : left.obj Q ⟶ W) (hW : completeSegalSpaces W) (hr : rezkWeakEquivalences r) :
    SSet.categoricalEquivalences (derivedUnit Q W r) := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let _ : comparisonAdjunction.{u}.IsQuillenEquivalence := comparisonAdjunction_isQuillenEquivalence
  let _ : IsCofibrant (JoyalSSet.ofSSet.obj Q) := JoyalSSet.isCofibrant _
  let _ : IsFibrant W := (RezkModel.isFibrant_iff_completeSegalSpaces W).mpr hW
  have hw : WeakEquivalence r := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences r
    rwa [RezkModel.modelCategory_weakEquivalences]
  have h := (weakEquivalence_iff _).mp
    ((Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
      (adj := comparisonAdjunction) r).mp hw)
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (comparisonAdjunction.homEquiv (JoyalSSet.ofSSet.obj Q) W r) at h
  rw [JoyalSSet.modelCategory_weakEquivalences] at h
  rwa [derivedUnit_wrapped]

/-- The actual left replacement map followed by the original target counit. -/
def derivedCounit (W : SimplicialSpace.{u}) (P : SSet.{u}) (q : P ⟶ right.obj W) :
    left.obj P ⟶ W := left.map q ≫ counit W

/-- The supplied source replacement gives the actual Rezk weak derived counit. -/
theorem derivedCounit_rezkWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W)
    (P : SSet.{u}) (q : P ⟶ right.obj W) (hq : SSet.categoricalEquivalences q) :
    rezkWeakEquivalences (derivedCounit W P q) := by
  have hl : rezkWeakEquivalences (left.map q) :=
    comparisonLeft_rezkWeak_of_categoricalEquivalence (JoyalSSet.ofSSet.map q) hq
  exact rezkWeakEquivalences.comp_mem _ _ hl (counit_rezkWeak W hW)

/-- Transposing the actual derived counit recovers the supplied source map itself. -/
theorem derivedCounit_transpose (W : SimplicialSpace.{u}) (P : SSet.{u}) (q : P ⟶ right.obj W) :
    derivedUnit P W (derivedCounit W P q) = q := by
  change adjunction.homEquiv P W (left.map q ≫ adjunction.counit.app W) = q
  rw [← adjunction.homEquiv_counit]
  exact (adjunction.homEquiv P W).apply_symm_apply q

/-- The actual unit's counit triangle recovers the original target replacement map. -/
theorem derivedUnit_counit (Q : SSet.{u}) (W : SimplicialSpace.{u}) (r : left.obj Q ⟶ W) :
    derivedCounit W Q (derivedUnit Q W r) = r := by
  change left.map (adjunction.homEquiv Q W r) ≫ adjunction.counit.app W = r
  exact (adjunction.homEquiv Q W).symm_apply_apply r

/-- Target maps commute with the actual derived unit transpose. -/
theorem derivedUnit_target (Q : SSet.{u}) {W V : SimplicialSpace.{u}}
    (r : left.obj Q ⟶ W) (g : W ⟶ V) :
    derivedUnit Q V (r ≫ g) = derivedUnit Q W r ≫ right.map g :=
  adjunction.homEquiv_naturality_right r g

/-- Source maps commute with the original derived unit. -/
theorem derivedUnit_source {Q P : SSet.{u}} (f : P ⟶ Q) (W : SimplicialSpace.{u})
    (r : left.obj Q ⟶ W) :
    derivedUnit P W (left.map f ≫ r) = f ≫ derivedUnit Q W r :=
  adjunction.homEquiv_naturality_left f r

/-- The derived counit retains the exact supplied source-map composition. -/
theorem derivedCounit_source (W : SimplicialSpace.{u}) {Q P : SSet.{u}}
    (f : P ⟶ Q) (q : Q ⟶ right.obj W) :
    derivedCounit W P (f ≫ q) = left.map f ≫ derivedCounit W Q q := by
  simp only [derivedCounit, Functor.map_comp, Category.assoc]

/-- Target maps retain the original counit naturality square. -/
theorem derivedCounit_target {W V : SimplicialSpace.{u}} (g : W ⟶ V)
    (P : SSet.{u}) (q : P ⟶ right.obj W) :
    derivedCounit V P (q ≫ right.map g) = derivedCounit W P q ≫ g := by
  change left.map (q ≫ right.map g) ≫ adjunction.counit.app V =
    (left.map q ≫ adjunction.counit.app W) ≫ g
  have hn : left.map (right.map g) ≫ adjunction.counit.app V =
      adjunction.counit.app W ≫ g := adjunction.counit.naturality g
  exact ((left.map_comp q (right.map g)).symm ▸ Category.assoc
    (left.map q) (left.map (right.map g)) (adjunction.counit.app V)).trans
      ((congrArg (fun t => left.map q ≫ t) hn).trans (Category.assoc _ _ _).symm)

end SimplicialSpace.FirstProjection
