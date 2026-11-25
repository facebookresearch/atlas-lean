/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Topology.Category.PointedCGWH.Smash

/-!
# Tests for native pointed CGWH wedge and smash
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory Topology

namespace MathlibExtTest.PointedCGWHSmashTests

section PublicSurface

#check PointedCGWH.wedge
#check PointedCGWH.wedgeToProduct_isClosedEmbedding
#check PointedCGWH.smash
#check PointedCGWH.smashQuotient_eq_iff
#check PointedCGWH.sphereZero
#check PointedCGWH.instMonoidalCategory
#check PointedCGWH.instSymmetricCategory

#check @PointedCGWH.wedge.{u, v}
#check @PointedCGWH.wedge.{0, 0}
#check @PointedCGWH.wedge.{1, 1}
#check @PointedCGWH.wedge.{0, 1}
#check @PointedCGWH.wedge.{1, 0}

#check @PointedCGWH.wedgeToProduct_isClosedEmbedding.{u, v}
#check @PointedCGWH.wedgeToProduct_isClosedEmbedding.{0, 0}
#check @PointedCGWH.wedgeToProduct_isClosedEmbedding.{1, 1}
#check @PointedCGWH.wedgeToProduct_isClosedEmbedding.{0, 1}
#check @PointedCGWH.wedgeToProduct_isClosedEmbedding.{1, 0}

#check @PointedCGWH.smash.{u, v}
#check @PointedCGWH.smash.{0, 0}
#check @PointedCGWH.smash.{1, 1}
#check @PointedCGWH.smash.{0, 1}
#check @PointedCGWH.smash.{1, 0}

#check @PointedCGWH.smashQuotient_eq_iff.{u, v}
#check @PointedCGWH.smashQuotient_eq_iff.{0, 0}
#check @PointedCGWH.smashQuotient_eq_iff.{1, 1}
#check @PointedCGWH.smashQuotient_eq_iff.{0, 1}
#check @PointedCGWH.smashQuotient_eq_iff.{1, 0}

#check @PointedCGWH.sphereZero.{u, v}
#check @PointedCGWH.sphereZero.{0, 0}
#check @PointedCGWH.sphereZero.{1, 1}
#check @PointedCGWH.sphereZero.{0, 1}
#check @PointedCGWH.sphereZero.{1, 0}

#synth MonoidalCategory PointedCGWH.{0, 0}
#synth MonoidalCategory PointedCGWH.{1, 1}
#synth MonoidalCategory PointedCGWH.{0, 1}
#synth MonoidalCategory PointedCGWH.{1, 0}
#synth SymmetricCategory PointedCGWH.{0, 0}
#synth SymmetricCategory PointedCGWH.{1, 1}
#synth SymmetricCategory PointedCGWH.{0, 1}
#synth SymmetricCategory PointedCGWH.{1, 0}

end PublicSurface

section LiteralFactories

example : PointedCGWH.wedge.{u, v} =
    CategoryTheory.Pointed.wedge CGWH.point.{u, v} := rfl

example : PointedCGWH.smash.{u, v} =
    (by
      letI : BraidedCategory CGWH.{u, v} :=
        BraidedCategory.ofCartesianMonoidalCategory
      letI : SymmetricCategory CGWH.{u, v} := inferInstance
      exact CategoryTheory.Pointed.smash
        CGWH.point CGWH.point_isTerminal) := rfl

example : PointedCGWH.sphereZero.{u, v} =
    CategoryTheory.Pointed.smashUnit CGWH.point.{u, v} := rfl

example : (inferInstance : MonoidalCategory PointedCGWH.{u, v}) =
    (by
      letI : BraidedCategory CGWH.{u, v} :=
        BraidedCategory.ofCartesianMonoidalCategory
      letI : SymmetricCategory CGWH.{u, v} := inferInstance
      exact CategoryTheory.Pointed.smashMonoidalCategory
        CGWH.point CGWH.point_isTerminal) := rfl

example : (inferInstance : SymmetricCategory PointedCGWH.{u, v}) =
    (by
      letI : BraidedCategory CGWH.{u, v} :=
        BraidedCategory.ofCartesianMonoidalCategory
      letI : SymmetricCategory CGWH.{u, v} := inferInstance
      exact CategoryTheory.Pointed.smashSymmetricCategory
        CGWH.point CGWH.point_isTerminal) := rfl

example (X Y : PointedCGWH.{u, v}) :
    X ⊗ Y = (PointedCGWH.smash.{u, v}.obj X).obj Y := rfl

end LiteralFactories

section WedgeAndQuotient

variable (X Y : PointedCGWH.{u, v})

private abbrev p := CategoryTheory.Pointed.smashPresentation
  CGWH.point CGWH.point_isTerminal X Y

#check PointedCGWH.wedgeToProduct_isClosedEmbedding X Y

example : IsClosedEmbedding (ConcreteCategory.hom (p X Y).1.right) :=
  PointedCGWH.wedgeToProduct_isClosedEmbedding X Y

example : (p X Y).2.1.inl ≫ 𝟙 _ = (p X Y).2.1.inl := by simp

example : (p X Y).1.right ≫ (p X Y).2.1.inl =
    CGWH.point_isTerminal.from (((PointedCGWH.wedge).obj X).obj Y).right ≫
      (p X Y).2.1.inr :=
  (p X Y).2.1.condition

example (z : (((PointedCGWH.wedge).obj X).obj Y).right) :
    let a := (p X Y).1.right z
    (p X Y).2.1.inl a = (p X Y).2.1.inl a := by simp

example (z z' : (((PointedCGWH.wedge).obj X).obj Y).right) :
    let a := (p X Y).1.right z
    let b := (p X Y).1.right z'
    (p X Y).2.1.inl a = (p X Y).2.1.inl b := by
  dsimp
  exact (PointedCGWH.smashQuotient_eq_iff X Y _ _).2
    (Or.inr ⟨⟨z, rfl⟩, ⟨z', rfl⟩⟩)

example (a b : (Under.mk
    (CartesianMonoidalCategory.lift X.hom Y.hom) :
      PointedCGWH.{u, v}).right)
    (h : (p X Y).2.1.inl a = (p X Y).2.1.inl b) :
    a = b ∨
      (a ∈ Set.range (ConcreteCategory.hom
          ((forget TopCat).map (CGWH.cgwhToTop.map (p X Y).1.right))) ∧
        b ∈ Set.range (ConcreteCategory.hom
          ((forget TopCat).map (CGWH.cgwhToTop.map (p X Y).1.right)))) :=
  (PointedCGWH.smashQuotient_eq_iff X Y a b).1 h

example (a b : (Under.mk
    (CartesianMonoidalCategory.lift X.hom Y.hom) :
      PointedCGWH.{u, v}).right)
    (h : a = b ∨
      (a ∈ Set.range (ConcreteCategory.hom
          ((forget TopCat).map (CGWH.cgwhToTop.map (p X Y).1.right))) ∧
        b ∈ Set.range (ConcreteCategory.hom
          ((forget TopCat).map (CGWH.cgwhToTop.map (p X Y).1.right))))) :
    (p X Y).2.1.inl a = (p X Y).2.1.inl b :=
  (PointedCGWH.smashQuotient_eq_iff X Y a b).2 h

example :
    let A : CGWH.{u, v} := (Under.mk
      (CartesianMonoidalCategory.lift X.hom Y.hom) :
        PointedCGWH.{u, v}).right
    let B : CGWH.{u, v} := (p X Y).2.1.pt
    let q : A ⟶ B := (p X Y).2.1.inl
    let R0 : Setoid A := Setoid.ker (ConcreteCategory.hom q)
    CGWH.closedEquivalenceRelation
        (CGWH.cgwhToCompactlyGenerated.obj A) R0 ∧
      UWeakHausdorffSpace.{u} (Quotient R0) ∧
      IsHomeomorph
        (ConcreteCategory.hom (CGWH.quotientComparisonFromTop A R0)) := by
  let A : CGWH.{u, v} := (Under.mk
    (CartesianMonoidalCategory.lift X.hom Y.hom) :
      PointedCGWH.{u, v}).right
  let B : CGWH.{u, v} := (p X Y).2.1.pt
  let q : A ⟶ B := (p X Y).2.1.inl
  let R0 : Setoid A := Setoid.ker (ConcreteCategory.hom q)
  change CGWH.closedEquivalenceRelation
      (CGWH.cgwhToCompactlyGenerated.obj A) R0 ∧
    UWeakHausdorffSpace.{u} (Quotient R0) ∧
    IsHomeomorph
      (ConcreteCategory.hom (CGWH.quotientComparisonFromTop A R0))
  let A' := CGWH.cgwhToCompactlyGenerated.obj A
  let B' := CGWH.cgwhToCompactlyGenerated.obj B
  let q' : A' ⟶ B' := CGWH.cgwhToCompactlyGenerated.map q
  let R : Setoid A' := Setoid.ker (ConcreteCategory.hom q')
  let q2 : A' ⊗ A' ⟶ B' ⊗ B' := q' ⊗ₘ q'
  let diagonal : Set ↥((B' ⊗ B').toTop) :=
    {z | (ConcreteCategory.hom
          (CartesianMonoidalCategory.fst B' B')) z =
      (ConcreteCategory.hom
          (CartesianMonoidalCategory.snd B' B')) z}
  have hdiag : IsClosed diagonal :=
    (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal B').mp
      B.is_weakHausdorff
  have hclosed : CGWH.closedEquivalenceRelation A' R := by
    unfold CGWH.closedEquivalenceRelation
    rw [show {z : ↥((A' ⊗ A').toTop) |
        R ((ConcreteCategory.hom
            (CartesianMonoidalCategory.fst A' A')) z)
          ((ConcreteCategory.hom
            (CartesianMonoidalCategory.snd A' A')) z)} =
        (ConcreteCategory.hom q2) ⁻¹' diagonal by
      ext z
      change q' (CartesianMonoidalCategory.fst A' A' z) =
          q' (CartesianMonoidalCategory.snd A' A' z) ↔
        CartesianMonoidalCategory.fst B' B' (q2 z) =
          CartesianMonoidalCategory.snd B' B' (q2 z)
      rw [show CartesianMonoidalCategory.fst B' B' (q2 z) =
          q' (CartesianMonoidalCategory.fst A' A' z) by
        exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst q' q') z]
      rw [show CartesianMonoidalCategory.snd B' B' (q2 z) =
          q' (CartesianMonoidalCategory.snd A' A' z) by
        exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd q' q') z]]
    exact hdiag.preimage (ConcreteCategory.hom q2).continuous
  have hclosed0 : CGWH.closedEquivalenceRelation
      (CGWH.cgwhToCompactlyGenerated.obj A) R0 := by
    change CGWH.closedEquivalenceRelation A' R
    exact hclosed
  refine ⟨hclosed0, ?_, ?_⟩
  · exact (CGWH.quotient_isWeakHausdorff_iff_isClosed
      (CGWH.cgwhToCompactlyGenerated.obj A) R0).2 hclosed0
  · exact (CGWH.quotientComparisonFromTop_isHomeomorph_iff A R0).2 hclosed0

end WedgeAndQuotient

section SphereZero

example : PointedCGWH.sphereZero.{u, v}.right =
    ((Under.costar CGWH.point.{u, v}).obj CGWH.point).right := rfl

example : PointedCGWH.sphereZero.{u, v}.hom =
    ((Under.costar CGWH.point.{u, v}).obj CGWH.point).hom := rfl

example : PointedCGWH.sphereZero.{u, v}.right =
    Limits.coprod CGWH.point.{u, v} CGWH.point := rfl

end SphereZero

section NegativeSurface

example : True := by
  fail_if_success
    have _ : IsHomeomorph
        (CGWH.prodComparisonToTop CGWH.point.{u, v} CGWH.point) := by
      infer_instance
  trivial

example : True := by
  fail_if_success
    let _ : MonoidalClosed PointedCGWH.{u, v} := inferInstance
  trivial

#guard_msgs (error, substring := true) in
#check PointedCGWH.modelCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.basedInternalHom

#guard_msgs (error, substring := true) in
#check PointedCGWH.instMonoidalClosed

#guard_msgs (error, substring := true) in
#check PointedCGWH.smashModelCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.adj_isQuillenEquivalence

#guard_msgs (error, substring := true) in
#check PointedCGWH.sphereOne

#guard_msgs (error, substring := true) in
#check PointedCGWH.spectrum

#guard_msgs (error, substring := true) in
#check PointedCGWH.pointElement

#guard_msgs (error, substring := true) in
#check PointedCGWH.pointElement_ext

#guard_msgs (error, substring := true) in
#check PointedCGWH.rawPoint_ext

#guard_msgs (error, substring := true) in
#check PointedCGWH.pointMap_isClosedEmbedding

#guard_msgs (error, substring := true) in
#check PointedCGWH.nativeProduct_point_ext

#guard_msgs (error, substring := true) in
#check PointedCGWH.leftAxis_isClosedEmbedding

#guard_msgs (error, substring := true) in
#check PointedCGWH.rightAxis_isClosedEmbedding

#guard_msgs (error, substring := true) in
#check PointedCGWH.nativeWedgeToProduct

#guard_msgs (error, substring := true) in
#check PointedCGWH.rawWedgeToProduct

#guard_msgs (error, substring := true) in
#check PointedCGWH.rawWedgeToProduct_inl

#guard_msgs (error, substring := true) in
#check PointedCGWH.rawWedgeToProduct_inr

#guard_msgs (error, substring := true) in
#check PointedCGWH.rawWedgeToProduct_injective

#guard_msgs (error, substring := true) in
#check PointedCGWH.rawWedgeToProduct_isClosedEmbedding

#guard_msgs (error, substring := true) in
#check PointedCGWH.pushout_inl_eq_inl_iff_of_constant

end NegativeSurface

#print axioms PointedCGWH.wedge
#print axioms PointedCGWH.wedgeToProduct_isClosedEmbedding
#print axioms PointedCGWH.smash
#print axioms PointedCGWH.smashQuotient_eq_iff
#print axioms PointedCGWH.sphereZero
#print axioms PointedCGWH.instMonoidalCategory
#print axioms PointedCGWH.instSymmetricCategory

end MathlibExtTest.PointedCGWHSmashTests
