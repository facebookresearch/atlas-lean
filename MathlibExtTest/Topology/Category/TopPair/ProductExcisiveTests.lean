/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ProductExcisive

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory
open _root_.AlgebraicTopology
open _root_.TopPair
open _root_.TopPair.ProductExcisivePair

universe u

namespace MathlibExtTest.Topology.Category.TopPair.ProductExcisiveTests

theorem productAdmissibility_domain_client
    (T : ProductExcisivePair.{u}) :
    IsRelativeCupExcisive
      (productAY T.obj.1 T.obj.2)
      (productXB T.obj.1 T.obj.2) :=
  (isProductUnionExcisive_iff_isRelativeCupExcisive _ _).mp T.property

theorem projectionNaturality_ambient_client
    {S T : ProductExcisivePair.{u}} (f : S ⟶ T)
    (x : (S.obj.1.fst ⊗ S.obj.2.fst : TopCat.{u})) :
    TopPair.Hom.fst
        (leftSupportFunctor.map f ≫ leftProjection.app T) x =
        TopPair.Hom.fst
          (leftProjection.app S ≫ leftFactorFunctor.map f) x ∧
      TopPair.Hom.fst
          (leftProjection.app S ≫ leftFactorFunctor.map f) x =
        TopPair.Hom.fst f.hom.1 x.1 ∧
      TopPair.Hom.fst
          (rightSupportFunctor.map f ≫ rightProjection.app T) x =
        TopPair.Hom.fst
          (rightProjection.app S ≫ rightFactorFunctor.map f) x ∧
      TopPair.Hom.fst
          (rightProjection.app S ≫ rightFactorFunctor.map f) x =
        TopPair.Hom.fst f.hom.2 x.2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem unionProductComparison_client
    (T : ProductExcisivePair.{u})
    (x : (unionSupportFunctor.obj T).snd) :
    TopPair.Hom.fst (unionProductNatIso.hom.app T) =
        𝟙 (T.obj.1.fst ⊗ T.obj.2.fst) ∧
      (TopPair.Hom.snd (unionProductNatIso.hom.app T) x).1 = x.1 := by
  exact ⟨productCupUnionIso_hom_fst T, rfl⟩

theorem openRanges_excisive_client
    (P Q : TopPair.{u})
    (hP : IsOpen (Set.range P.map)) (hQ : IsOpen (Set.range Q.map)) :
    IsProductUnionExcisive P Q :=
  isProductUnionExcisive_of_isOpen_ranges P Q hP hQ

theorem openRange_selfExcisive_client
    (P : TopPair.{u}) (hP : IsOpen (Set.range P.map)) :
    IsProductUnionExcisive P P :=
  isProductUnionExcisive_self_of_isOpen_range P hP

theorem univSubset_excisive_client (X Y : TopCat.{u}) :
    IsProductUnionExcisive (TopPair.ofSubset (Set.univ : Set X))
      (TopPair.ofSubset (Set.univ : Set Y)) := by
  apply isProductUnionExcisive_of_isOpen_ranges
  · have h : Set.range (TopPair.ofSubset (Set.univ : Set X)).map =
        Set.univ := by
      ext x
      exact ⟨fun _ => trivial, fun _ => ⟨⟨x, trivial⟩, rfl⟩⟩
    rw [h]
    exact isOpen_univ
  · have h : Set.range (TopPair.ofSubset (Set.univ : Set Y)).map =
        Set.univ := by
      ext x
      exact ⟨fun _ => trivial, fun _ => ⟨⟨x, trivial⟩, rfl⟩⟩
    rw [h]
    exact isOpen_univ

end MathlibExtTest.Topology.Category.TopPair.ProductExcisiveTests
