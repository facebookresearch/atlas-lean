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

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMapReindex

/-!
# Tests for outer-reindex coherence of exact-functor Stage-grid maps

The clients exercise arbitrary outer simplex morphisms, the exact transported
simplex-comparison square, raw agreements, full-subcategory lifts, identity
and nested reindexing, low degrees, and asymmetric universes.  They do not
claim exact-functor identity/composition or construct a nerve, diagonal,
realization, weak equivalence, group comparison, spectrum map, or Q/S map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenStageGridMapReindexTests

open AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

section InstanceNonleak

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing C

end InstanceNonleak

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

section Symbolic

variable {a b c : SimplexCategory}

example (α : a ⟶ b) :
    quillenQSimplexDiscreteReindex (C := C) α ⋙
        quillenQSimplexDiscreteMap F a =
      quillenQSimplexDiscreteMap F b ⋙
        quillenQSimplexDiscreteReindex (C := D) α :=
  quillenQSimplexDiscreteMap_reindex F α

example (α : a ⟶ b) :
    edgewiseStageWeakReindex (C := C) α ⋙
          mapStageWeak C D F (edgewiseQ.obj a).len ⋙
            edgewiseStageQuillenSimplexFunctor D a =
      mapStageWeak C D F (edgewiseQ.obj b).len ⋙
          edgewiseStageQuillenSimplexFunctor D b ⋙
            edgewiseQuillenSimplexReindex (C := D) α :=
  edgewiseStageQuillenSimplexFunctor_mapIso_reindex_source F α

example (α : a ⟶ b) :
    edgewiseStageWeakReindex (C := C) α ⋙
          edgewiseStageQuillenSimplexFunctor C a ⋙
            (QuillenQ.map F).mapComposableArrows a.len =
      edgewiseStageQuillenSimplexFunctor C b ⋙
          (QuillenQ.map F).mapComposableArrows b.len ⋙
            edgewiseQuillenSimplexReindex (C := D) α :=
  edgewiseStageQuillenSimplexFunctor_mapIso_reindex_target F α

example (α : a ⟶ b) :
    Functor.whiskerLeft (edgewiseStageWeakReindex (C := C) α)
          (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom ≫
        eqToHom
          (edgewiseStageQuillenSimplexFunctor_mapIso_reindex_target F α) =
      eqToHom
          (edgewiseStageQuillenSimplexFunctor_mapIso_reindex_source F α) ≫
        Functor.whiskerRight
          (edgewiseStageQuillenSimplexFunctor_mapIso F b).hom
          (edgewiseQuillenSimplexReindex (C := D) α) :=
  edgewiseStageQuillenSimplexFunctor_mapIso_reindex F α

example (α : a ⟶ b) :
    reindexQuillenStageGridAgreement (C := C) α ⋙
        quillenStageGridAgreementMap F a =
      quillenStageGridAgreementMap F b ⋙
        reindexQuillenStageGridAgreement (C := D) α :=
  quillenStageGridAgreementMap_reindex F α

example (α : a ⟶ b) :
    reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridLiftMap F a =
      quillenStageGridLiftMap F b ⋙
        reindexQuillenStageGridLift (C := D) α :=
  quillenStageGridLiftMap_reindex F α

example (a : SimplexCategory) :
    𝟭 (QuillenStageGridLift C a) ⋙ quillenStageGridLiftMap F a =
      quillenStageGridLiftMap F a ⋙ 𝟭 (QuillenStageGridLift D a) := by
  have h := quillenStageGridLiftMap_reindex F (𝟙 a)
  simpa only [reindexQuillenStageGridLift_id] using h

example (α : a ⟶ b) (β : b ⟶ c) :
    (reindexQuillenStageGridLift (C := C) β ⋙
          reindexQuillenStageGridLift (C := C) α) ⋙
        quillenStageGridLiftMap F a =
      quillenStageGridLiftMap F c ⋙
        (reindexQuillenStageGridLift (C := D) β ⋙
          reindexQuillenStageGridLift (C := D) α) := by
  rw [← reindexQuillenStageGridLift_comp,
    quillenStageGridLiftMap_reindex,
    reindexQuillenStageGridLift_comp]

end Symbolic

section Degrees

example :
    reindexQuillenStageGridLift (C := C) (𝟙 ⦋0⦌) ⋙
        quillenStageGridLiftMap F ⦋0⦌ =
      quillenStageGridLiftMap F ⦋0⦌ ⋙
        reindexQuillenStageGridLift (C := D) (𝟙 ⦋0⦌) :=
  quillenStageGridLiftMap_reindex F (𝟙 ⦋0⦌)

example :
    reindexQuillenStageGridLift (C := C) (𝟙 ⦋1⦌) ⋙
        quillenStageGridLiftMap F ⦋1⦌ =
      quillenStageGridLiftMap F ⦋1⦌ ⋙
        reindexQuillenStageGridLift (C := D) (𝟙 ⦋1⦌) :=
  quillenStageGridLiftMap_reindex F (𝟙 ⦋1⦌)

end Degrees

section AsymmetricUniverses

variable {C₀ : Type 0} [Category.{0} C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]
variable {D₁ : Type 1} [Category.{1} D₁] [Preadditive D₁]
  [HasZeroObject D₁] [HasBinaryBiproducts D₁] [ExactCategory D₁]
variable (G : C₀ ⥤ D₁) [G.Additive] [G.IsExact]

local instance : WaldhausenCategoryWithoutGluing C₀ :=
  ExactCategory.waldhausenCategory C₀

local instance : WaldhausenCategoryWithoutGluing D₁ :=
  ExactCategory.waldhausenCategory D₁

example {a b : SimplexCategory} (α : a ⟶ b) :
    reindexQuillenStageGridLift (C := C₀) α ⋙
        quillenStageGridLiftMap G a =
      quillenStageGridLiftMap G b ⋙
        reindexQuillenStageGridLift (C := D₁) α :=
  quillenStageGridLiftMap_reindex G α

end AsymmetricUniverses

section Nonclaims

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridLiftMap_id

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridLiftMap_comp

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridNerveMap

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridDiagonalMap

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenQSPointedEquiv

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridToStageSpectrumMap

end Nonclaims

#print axioms AlgebraicKTheory.quillenQSimplexDiscreteMap_reindex
#print axioms
  AlgebraicKTheory.edgewiseStageQuillenSimplexFunctor_mapIso_reindex_source
#print axioms
  AlgebraicKTheory.edgewiseStageQuillenSimplexFunctor_mapIso_reindex_target
#print axioms
  AlgebraicKTheory.edgewiseStageQuillenSimplexFunctor_mapIso_reindex
#print axioms AlgebraicKTheory.quillenStageGridAgreementMap_reindex
#print axioms AlgebraicKTheory.quillenStageGridLiftMap_reindex

end QuillenStageGridMapReindexTests
end MathlibExtTest.KTheory.Categorical
