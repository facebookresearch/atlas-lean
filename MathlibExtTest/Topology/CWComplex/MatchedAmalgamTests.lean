/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.MatchedAmalgam

/-!
# Importing clients of classical CW matched amalgams

The maps and degree-preserving matching data below are arbitrary. The tests
use the constructed CW structure and its public characteristic and subcomplex
laws, including the right cells in the matching image.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open Topology.CWComplex.MatchedAmalgam

universe u

variable {C A B : TopCat.{u}}
variable [Topology.CWComplex (Set.univ : Set C)]
variable [Topology.CWComplex (Set.univ : Set A)]
variable [Topology.CWComplex (Set.univ : Set B)]
variable {f : C ⟶ A} {g : C ⟶ B}
variable (d : MatchingCharacteristicData f g)
variable (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)

#check Topology.CWComplex.MatchedAmalgam.classicalCWComplex
#print axioms Topology.CWComplex.MatchedAmalgam.classicalCWComplex
#check Topology.CWComplex.MatchedAmalgam.right_characteristicDiskMap
#print axioms Topology.CWComplex.MatchedAmalgam.right_characteristicDiskMap
#check Topology.CWComplex.MatchedAmalgam.matchingRightSubcomplex
#print axioms Topology.CWComplex.MatchedAmalgam.matchingRightSubcomplex

example : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
  Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg

example (n : ℕ) (a : Topology.CWComplex.cell (Set.univ : Set A) n)
    (x : Fin n → ℝ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
    Topology.CWComplex.map (C := (Set.univ : Set ((pushout f g : TopCat.{u})))) n (Sum.inl a) x =
      pushout.inl f g (Topology.CWComplex.map (C := (Set.univ : Set A)) n a x) :=
  left_characteristic d hf hg n a x

example (n : ℕ) (a : Topology.CWComplex.cell (Set.univ : Set A) n) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
    Topology.CWComplex.characteristicDiskMap (X := (pushout f g : TopCat.{u})) n (Sum.inl a) =
      Topology.CWComplex.characteristicDiskMap (X := A) n a ≫ pushout.inl f g :=
  left_characteristicDiskMap d hf hg n a

example (n : ℕ) (b : Topology.CWComplex.cell (Set.univ : Set B) n) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
    Topology.CWComplex.characteristicDiskMap (X := (pushout f g : TopCat.{u})) n (rightCellTransfer d n b) =
      Topology.CWComplex.characteristicDiskMap (X := B) n b ≫ pushout.inr f g :=
  right_characteristicDiskMap d hf hg n b

example (n : ℕ)
    (b : {b : Topology.CWComplex.cell (Set.univ : Set B) n //
      b ∉ Set.range (d.rightLabels n)}) (x : Fin n → ℝ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
    Topology.CWComplex.map (C := (Set.univ : Set ((pushout f g : TopCat.{u})))) n (Sum.inr b) x =
      pushout.inr f g (Topology.CWComplex.map (C := (Set.univ : Set B)) n b.val x) :=
  newRight_characteristic d hf hg n b x

example (n : ℕ) :
    (matchingLeftSubcomplex d hf : Set A) = Set.range f ∧
    (matchingLeftSubcomplex d hf).I n = Set.range (d.leftLabels n) ∧
    (matchingRightSubcomplex d hg : Set B) = Set.range g ∧
    (matchingRightSubcomplex d hg).I n = Set.range (d.rightLabels n) :=
  ⟨matchingLeftSubcomplex_carrier d hf, matchingLeftSubcomplex_I d hf n,
    matchingRightSubcomplex_carrier d hg, matchingRightSubcomplex_I d hg n⟩

example (n : ℕ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
    (leftSubcomplex d hf hg : Set ((pushout f g : TopCat.{u}))) = Set.range (pushout.inl f g) ∧
    (leftSubcomplex d hf hg).I n = Set.range (leftCellEmbedding d n) ∧
    (rightSubcomplex d hf hg : Set ((pushout f g : TopCat.{u}))) = Set.range (pushout.inr f g) ∧
    (rightSubcomplex d hf hg).I n = Set.range (rightCellEmbedding d n) := by
  let : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
    Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
  exact ⟨leftSubcomplex_carrier d hf hg, leftSubcomplex_I d hf hg n,
    rightSubcomplex_carrier d hf hg, rightSubcomplex_I d hf hg n⟩

example (n : ℕ) :
    letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
      Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
    (Topology.CWComplex.cell (Set.univ : Set A) n ↪
      Topology.CWComplex.cell (Set.univ : Set ((pushout f g : TopCat.{u}))) n) ×
    (Topology.CWComplex.cell (Set.univ : Set B) n ↪
      Topology.CWComplex.cell (Set.univ : Set ((pushout f g : TopCat.{u}))) n) := by
  letI : Topology.CWComplex (Set.univ : Set ((pushout f g : TopCat.{u}))) :=
    Topology.CWComplex.MatchedAmalgam.classicalCWComplex d hf hg
  exact ⟨leftCellEmbedding d n, rightCellEmbedding d n⟩

example (X : TopCat.{u}) [Topology.CWComplex (Set.univ : Set X)] :
    Topology.CWComplex (Set.univ : Set ((pushout (𝟙 X) (𝟙 X) : TopCat.{u}))) := by
  let m : MatchingCharacteristicData (𝟙 X) (𝟙 X) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := fun _ => Function.Embedding.refl _
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun _ _ _ => rfl }
  exact Topology.CWComplex.MatchedAmalgam.classicalCWComplex m
    IsClosedEmbedding.id IsClosedEmbedding.id
