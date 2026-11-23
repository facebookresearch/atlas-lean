/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCoproductPushoutProperty

@[expose] public section

/-!
# Horn-coproduct Arrow-iso pushout bridge clients

Public clients for direct horn-coproduct pushouts, family extraction, the
caller-supplied `Arrow`-iso bridge, and the final pushout-property containment.
The symbolic, universe-one, and universe-zero clients add no instance,
transfinite theorem, model structure, or #4615 dependency.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductPushoutPropertyTests

/-- Pointwise horn-family extraction client, by direct term application. -/
theorem hornFamily_arrow_eq_client {J : Type 0} {A B : J → TopCat.{0}}
    {m : ∀ j, A j ⟶ B j} (hm : ∀ j, TopCat.realizedHornInclusions.{0} (m j)) :
    ∃ (N : J → ℕ) (K : ∀ j, Fin (N j + 1)), ∀ j, Arrow.mk (m j) =
      Arrow.mk (SSet.toTop.map (SSet.horn (N j) (K j)).ι) :=
  TopCat.hornFamily_arrow_eq hm

/-- Arrow-iso pushout bridge client, forwarding the iso and pushout data. -/
theorem hornCoproduct_pushout_of_arrow_iso_client {J : Type 0} {N : J → ℕ}
    {K : ∀ j, Fin (N j + 1)} {hn : ∀ j, 0 < N j} {A B X Y : TopCat.{0}}
    {p : A ⟶ B} {f : A ⟶ X} {g : B ⟶ Y} {q : X ⟶ Y}
    (e : Arrow.mk p ≅
      Arrow.mk (Limits.Sigma.map (fun j => TopCat.hornSDRIncl J N K j)))
    (h : IsPushout p f g q) : TopCat.weakHomotopyEquivalences q :=
  TopCat.hornCoproduct_pushout_of_arrow_iso (hn := hn) e h

#print axioms TopCat.hornFamily_arrow_eq
#print axioms hornFamily_arrow_eq_client
#print axioms TopCat.hornCoproduct_pushout_of_arrow_iso
#print axioms hornCoproduct_pushout_of_arrow_iso_client

theorem hornCoproductPushout_symbolic
    {J : Type u} {n : J → ℕ} {k : ∀ j, Fin (n j + 1)}
    {hn : ∀ j, 0 < n j} {Y P : TopCat.{u}}
    {f : (∐ fun j => TopCat.hornSDRDomain J n k j) ⟶ Y}
    {g : (∐ fun j => TopCat.hornSDRSimplex J n j) ⟶ P}
    {j : Y ⟶ P}
    (h : IsPushout
      (Limits.Sigma.map (fun j => TopCat.hornSDRIncl J n k j)) f g j) :
    TopCat.weakHomotopyEquivalences j :=
  TopCat.hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences
    (hn := hn) h

theorem hornCoproductPushout_u1
    {J : Type 1} {n : J → ℕ} {k : ∀ j, Fin (n j + 1)}
    {hn : ∀ j, 0 < n j} {Y P : TopCat.{1}}
    {f : (∐ fun j => TopCat.hornSDRDomain J n k j) ⟶ Y}
    {g : (∐ fun j => TopCat.hornSDRSimplex J n j) ⟶ P}
    {j : Y ⟶ P}
    (h : IsPushout
      (Limits.Sigma.map (fun j => TopCat.hornSDRIncl J n k j)) f g j) :
    TopCat.weakHomotopyEquivalences j :=
  TopCat.hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences
    (hn := hn) h

theorem hornFamily_symbolic
    {J : Type u} {A B : J → TopCat.{u}} {m : ∀ j, A j ⟶ B j}
    (hm : ∀ j, TopCat.realizedHornInclusions.{u} (m j)) :
    ∃ (N : J → ℕ) (K : ∀ j, Fin (N j + 1)), ∀ j,
      Arrow.mk (m j) =
        Arrow.mk (SSet.toTop.{u}.map (SSet.horn.{u} (N j) (K j)).ι) :=
  TopCat.hornFamily_arrow_eq hm

theorem arrowIsoPushout_symbolic
    {J : Type u} {N : J → ℕ} {K : ∀ j, Fin (N j + 1)}
    {hn : ∀ j, 0 < N j} {A B X Y : TopCat.{u}}
    {p : A ⟶ B} {f : A ⟶ X} {g : B ⟶ Y} {q : X ⟶ Y}
    (e : Arrow.mk p ≅
      Arrow.mk (Limits.Sigma.map
        (fun j => TopCat.hornSDRIncl J N K j)))
    (h : IsPushout p f g q) :
    TopCat.weakHomotopyEquivalences q :=
  TopCat.hornCoproduct_pushout_of_arrow_iso (hn := hn) e h

theorem finalProperty_symbolic :
    (MorphismProperty.coproducts.{u}
      TopCat.realizedHornInclusions.{u}).pushouts ≤
      TopCat.weakHomotopyEquivalences.{u} :=
  TopCat.coproducts_pushouts_le_weakHomotopyEquivalences

theorem finalProperty_u1 :
    (MorphismProperty.coproducts.{1}
      TopCat.realizedHornInclusions.{1}).pushouts ≤
      TopCat.weakHomotopyEquivalences.{1} :=
  TopCat.coproducts_pushouts_le_weakHomotopyEquivalences

theorem finalProperty_u0 :
    (MorphismProperty.coproducts.{0}
      TopCat.realizedHornInclusions.{0}).pushouts ≤
      TopCat.weakHomotopyEquivalences.{0} :=
  TopCat.coproducts_pushouts_le_weakHomotopyEquivalences

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.bkHocolimMap_mem_realizationWeakEquivalences

/-- error: Unknown identifier -/
#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_map_of_isPushouts_of_cofibrant

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isPushout_mono

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isColimit_nat_mono

#print axioms TopCat.hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences
#print axioms TopCat.coproducts_pushouts_le_weakHomotopyEquivalences

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductPushoutPropertyTests
