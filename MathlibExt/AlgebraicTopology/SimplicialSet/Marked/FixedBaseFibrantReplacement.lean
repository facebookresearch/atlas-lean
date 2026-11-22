/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseFibrationRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseFactorizationAccessibility
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMappingFibrancy
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.TerminalFunctor

/-!
# The actual native constant-base intrinsic replacements

Apply the proved same-rank fixed-base factorization to each original
terminal base triangle. Its actual middle objects, square maps and left
factor units give accessible replacement functors. Their terminal right
factors prove exactly the original intrinsic Cartesian or cocartesian
marking and projection. Every arbitrary marked source retains its actual
Kan mapping space into these targets.

The original units are monic. Their weakness in the original intrinsic
mapping class, the full marked model and straightening remain separate
required results and are not assumed here.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

local instance fixedBaseReplacementCardinalRegular (B : SSet.{u}) : Fact (FixedBaseSmallObject.cardinal B).IsRegular :=
  FixedBaseSmallObject.cardinal_regular B

/-- The actual original cartesian fixed-base middle factors give this native replacement functor. -/
def cartesianFixedBaseReplacementFunctor (B : SSet.{u}) : Over (max B) ⥤ Over (max B) :=
  (FixedBaseSmallObject.cartesianFunctorialFactorization B).terminalReplacementFunctor
    (Over.mkIdTerminal (X := max B))

/-- The original cartesian replacement unit is the same native left factor component. -/
def cartesianFixedBaseReplacementUnit (B : SSet.{u}) :
    𝟭 (Over (max B)) ⟶ cartesianFixedBaseReplacementFunctor B :=
  (FixedBaseSmallObject.cartesianFunctorialFactorization B).terminalReplacementUnit
    (Over.mkIdTerminal (X := max B))

/-- The actual original cartesian replacement unit belongs to the same native generated left class. -/
theorem cartesianFixedBaseReplacementUnit_left (B : SSet.{u}) (X : Over (max B)) :
    (cartesianFixedBaseCells B).rlp.llp ((cartesianFixedBaseReplacementUnit B).app X) :=
  (FixedBaseSmallObject.cartesianFunctorialFactorization B).terminalReplacementUnit_mem_left _ X

/-- The actual original cartesian replacement unit is a marked slice monomorphism. -/
theorem cartesianFixedBaseReplacementUnit_mono (B : SSet.{u}) (X : Over (max B)) :
    Mono ((cartesianFixedBaseReplacementUnit B).app X) :=
  FixedBaseSmallObject.cartesian_left_le_monomorphisms B _ (cartesianFixedBaseReplacementUnit_left B X)

/-- The actual native cartesian replacement target has its original terminal map in the true fixed-base right class. -/
theorem cartesianFixedBaseReplacement_right (B : SSet.{u}) (X : Over (max B)) :
    (cartesianFixedBaseCells B).rlp (Over.mkIdTerminal.from ((cartesianFixedBaseReplacementFunctor B).obj X)) :=
  (FixedBaseSmallObject.cartesianFunctorialFactorization B).terminalReplacement_mem_right _ X

/-- Over an arbitrary original quasicategory, the same cartesian target is an intrinsic fibration with
  exactly its original markings. -/
theorem cartesianFixedBaseReplacement_intrinsic {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) : cartesianObjects B ((cartesianFixedBaseReplacementFunctor B).obj X) :=
  (cartesianFixedBaseCells_terminal_rlp_iff _).mp (cartesianFixedBaseReplacement_right B X)

/-- The SAME actual cartesian replacement functor is accessible at its proved original fixed-base rank. -/
theorem cartesianFixedBaseReplacementFunctor_isCardinalAccessible (B : SSet.{u}) :
    (cartesianFixedBaseReplacementFunctor B).IsCardinalAccessible (FixedBaseSmallObject.cardinal B) := by
  let _ : (FixedBaseSmallObject.cartesianFunctorialFactorization B).Z.IsCardinalAccessible
      (FixedBaseSmallObject.cardinal B) :=
    FixedBaseSmallObject.cartesianFunctorialFactorization_Z_isCardinalAccessible B
  exact (FixedBaseSmallObject.cartesianFunctorialFactorization B).terminalReplacementFunctor_isCardinalAccessible _ _

/-- Bundle the actual same native cartesian replacement targets, retaining every original source map and
  base triangle. -/
def cartesianFixedBaseIntrinsicReplacementFunctor (B : SSet.{u}) [Quasicategory B] :
    Over (max B) ⥤ CartesianOver B where
  obj X := ⟨(cartesianFixedBaseReplacementFunctor B).obj X, cartesianFixedBaseReplacement_intrinsic X⟩
  map f := ObjectProperty.homMk ((cartesianFixedBaseReplacementFunctor B).map f)
  map_id X := ObjectProperty.hom_ext _ ((cartesianFixedBaseReplacementFunctor B).map_id X)
  map_comp f g := ObjectProperty.hom_ext _ ((cartesianFixedBaseReplacementFunctor B).map_comp f g)

/-- Every arbitrary original marked source has a genuine Kan mapping space into the same native cartesian
  replacement. -/
theorem cartesianFixedBaseIntrinsicReplacement_mapping_kan {B : SSet.{u}} [Quasicategory B]
    (X Y : Over (max B)) :
    KanComplex ((overMappingFunctor .maximal (max B)
      ((cartesianFixedBaseIntrinsicReplacementFunctor B).obj Y).obj).obj (Opposite.op X)) :=
  overMappingFunctor_cartesian_kan X _

/-- The actual original cocartesian fixed-base middle factors give this native replacement functor. -/
def cocartesianFixedBaseReplacementFunctor (B : SSet.{u}) : Over (max B) ⥤ Over (max B) :=
  (FixedBaseSmallObject.cocartesianFunctorialFactorization B).terminalReplacementFunctor
    (Over.mkIdTerminal (X := max B))

/-- The original cocartesian replacement unit is the same native left factor component. -/
def cocartesianFixedBaseReplacementUnit (B : SSet.{u}) :
    𝟭 (Over (max B)) ⟶ cocartesianFixedBaseReplacementFunctor B :=
  (FixedBaseSmallObject.cocartesianFunctorialFactorization B).terminalReplacementUnit
    (Over.mkIdTerminal (X := max B))

/-- The actual original cocartesian replacement unit belongs to the same native generated left class. -/
theorem cocartesianFixedBaseReplacementUnit_left (B : SSet.{u}) (X : Over (max B)) :
    (cocartesianFixedBaseCells B).rlp.llp ((cocartesianFixedBaseReplacementUnit B).app X) :=
  (FixedBaseSmallObject.cocartesianFunctorialFactorization B).terminalReplacementUnit_mem_left _ X

/-- The actual original cocartesian replacement unit is a marked slice monomorphism. -/
theorem cocartesianFixedBaseReplacementUnit_mono (B : SSet.{u}) (X : Over (max B)) :
    Mono ((cocartesianFixedBaseReplacementUnit B).app X) :=
  FixedBaseSmallObject.cocartesian_left_le_monomorphisms B _ (cocartesianFixedBaseReplacementUnit_left B X)

/-- The actual native cocartesian replacement target has its original terminal map in the true fixed-base
  right class. -/
theorem cocartesianFixedBaseReplacement_right (B : SSet.{u}) (X : Over (max B)) :
    (cocartesianFixedBaseCells B).rlp (Over.mkIdTerminal.from ((cocartesianFixedBaseReplacementFunctor B).obj X)) :=
  (FixedBaseSmallObject.cocartesianFunctorialFactorization B).terminalReplacement_mem_right _ X

/-- Over an arbitrary original quasicategory, the same cocartesian target is an intrinsic fibration with
  exactly its original markings. -/
theorem cocartesianFixedBaseReplacement_intrinsic {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) : cocartesianObjects B ((cocartesianFixedBaseReplacementFunctor B).obj X) :=
  (cocartesianFixedBaseCells_terminal_rlp_iff _).mp (cocartesianFixedBaseReplacement_right B X)

/-- The SAME actual cocartesian replacement functor is accessible at its proved original fixed-base rank. -/
theorem cocartesianFixedBaseReplacementFunctor_isCardinalAccessible (B : SSet.{u}) :
    (cocartesianFixedBaseReplacementFunctor B).IsCardinalAccessible (FixedBaseSmallObject.cardinal B) := by
  let _ : (FixedBaseSmallObject.cocartesianFunctorialFactorization B).Z.IsCardinalAccessible
      (FixedBaseSmallObject.cardinal B) :=
    FixedBaseSmallObject.cocartesianFunctorialFactorization_Z_isCardinalAccessible B
  exact (FixedBaseSmallObject.cocartesianFunctorialFactorization B).terminalReplacementFunctor_isCardinalAccessible _ _

/-- Bundle the actual same native cocartesian replacement targets, retaining every original source map and
  base triangle. -/
def cocartesianFixedBaseIntrinsicReplacementFunctor (B : SSet.{u}) [Quasicategory B] :
    Over (max B) ⥤ CocartesianOver B where
  obj X := ⟨(cocartesianFixedBaseReplacementFunctor B).obj X, cocartesianFixedBaseReplacement_intrinsic X⟩
  map f := ObjectProperty.homMk ((cocartesianFixedBaseReplacementFunctor B).map f)
  map_id X := ObjectProperty.hom_ext _ ((cocartesianFixedBaseReplacementFunctor B).map_id X)
  map_comp f g := ObjectProperty.hom_ext _ ((cocartesianFixedBaseReplacementFunctor B).map_comp f g)

/-- Every arbitrary original marked source has a genuine Kan mapping space into the same native cocartesian
  replacement. -/
theorem cocartesianFixedBaseIntrinsicReplacement_mapping_kan {B : SSet.{u}} [Quasicategory B]
    (X Y : Over (max B)) :
    KanComplex ((overMappingFunctor .maximal (max B)
      ((cocartesianFixedBaseIntrinsicReplacementFunctor B).obj Y).obj).obj (Opposite.op X)) :=
  overMappingFunctor_cocartesian_kan X _

end SSet.Marked
