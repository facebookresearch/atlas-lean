/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.FlatMapFunctoriality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.Int
public meta import Mathlib.Tactic.NormNum

/-!
# A nonconstant homogeneous cochain through two group projections

The groups are G = C₂, H = ULift(G × G), and K = ULift(H × H), in universes
zero, one and two. Both group maps are first projections. The coefficient is
ULift ℤ in universe three, with trivial action; the coefficient maps multiply
by two and three.

In degree one, the invariant cochain has value one when its two group coordinates
agree and value two otherwise. A selected K-tuple has equal coordinates after
the two projections. The direct composite and the two-step cochain map both
give coefficient six there. This tests tuple-level composition on a nonconstant
cochain with independently sized groups, without assuming it is a cocycle.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory ContinuousCohomology

namespace MathlibExtTest.FlatMapFunctoriality

private abbrev G : ProfiniteGrp.{0} :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2)))

private abbrev H : ProfiniteGrp.{1} :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (ULift.{1} (G × G)))

private abbrev K : ProfiniteGrp.{2} :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (ULift.{2} (H × H)))

private def φ : H →ₜ* G where
  toFun h := h.down.1
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

private def ψ : K →ₜ* H where
  toFun k := k.down.1
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

private abbrev Coeff := ULift.{3} ℤ

private abbrev X : TopRep.{3, 0, 0} ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G Coeff)

private abbrev Y : TopRep.{3, 0, 1} ℤ H :=
  TopRep.of (ContRepresentation.trivial ℤ H Coeff)

private abbrev Z : TopRep.{3, 0, 2} ℤ K :=
  TopRep.of (ContRepresentation.trivial ℤ K Coeff)

private def f : TopRep.res φ X ⟶ Y :=
  TopRep.ofHom
    { toContinuousLinearMap := (2 : ℤ) • ContinuousLinearMap.id ℤ Coeff
      isIntertwining' _ := by
        apply ContinuousLinearMap.ext
        intro x
        rfl }

private def g : TopRep.res ψ Y ⟶ Z :=
  TopRep.ofHom
    { toContinuousLinearMap := (3 : ℤ) • ContinuousLinearMap.id ℤ Coeff
      isIntertwining' _ := by
        apply ContinuousLinearMap.ext
        intro x
        rfl }

private def tuple₂ {T : Type*} (x y : T) : Fin 2 → T :=
  fun i => if i = 0 then x else y

private def nonconstant : flatHomogeneousCochains.{0, 0, 3} X 1 :=
  ⟨⟨fun t => if t 0 = t 1 then ULift.up (1 : ℤ) else ULift.up (2 : ℤ),
    continuous_of_discreteTopology⟩, by
      intro h t
      change (if h * t 0 = h * t 1 then ULift.up (1 : ℤ) else ULift.up (2 : ℤ)) =
        if t 0 = t 1 then ULift.up (1 : ℤ) else ULift.up (2 : ℤ)
      simp only [mul_left_cancel_iff]⟩

private abbrev s : G := Multiplicative.ofAdd (1 : ZMod 2)

private abbrev h₀ : H := ULift.up ((1 : G), (1 : G))
private abbrev h₁ : H := ULift.up ((1 : G), s)
private abbrev h₂ : H := ULift.up (s, (1 : G))
private abbrev k₀ : K := ULift.up (h₀, h₀)
private abbrev k₁ : K := ULift.up (h₁, h₂)
private def targetTuple : Fin 2 → K := tuple₂ k₀ k₁

private abbrev directMap :=
  nativeFlatGroupCoefficientMap.{0, 0, 2, 3} (φ.comp ψ)
    ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g)

private abbrev firstMap := nativeFlatGroupCoefficientMap.{0, 0, 1, 3} φ f
private abbrev secondMap := nativeFlatGroupCoefficientMap.{0, 1, 2, 3} ψ g

private lemma direct_value :
    ((directMap.f 1 nonconstant).val targetTuple) = ULift.up (6 : ℤ) := by
  change (nativeFlatGroupCoefficientTerm.{0, 0, 2, 3} (φ.comp ψ)
    ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g) 1 nonconstant).val targetTuple = _
  rw [nativeFlatGroupCoefficientTerm_apply]
  change (3 : ℤ) • ((2 : ℤ) • (ULift.up (1 : ℤ) : Coeff)) = ULift.up (6 : ℤ)
  apply ULift.ext
  change (3 : ℤ) • ((2 : ℤ) • (1 : ℤ)) = 6
  norm_num

example : nonconstant.val (tuple₂ (1 : G) (1 : G)) = ULift.up (1 : ℤ) := rfl

example : nonconstant.val (tuple₂ (1 : G) s) = ULift.up (2 : ℤ) := by
  have h : (1 : G) ≠ s := by decide
  change (if (1 : G) = s then ULift.up (1 : ℤ) else ULift.up (2 : ℤ)) = _
  simp only [h, if_false]

example : (φ.comp ψ) (targetTuple 0) = 1 ∧ (φ.comp ψ) (targetTuple 1) = 1 :=
  ⟨rfl, rfl⟩

example : (directMap.f 1 nonconstant).val targetTuple = ULift.up (6 : ℤ) := direct_value

example : ((firstMap ≫ secondMap).f 1 nonconstant).val targetTuple =
    ULift.up (6 : ℤ) := by
  rw [← nativeFlatGroupCoefficientMap_comp.{0, 0, 1, 2, 3} φ ψ f g]
  exact direct_value

example : ((firstMap ≫ secondMap).f 1 nonconstant).val targetTuple ≠ 0 := by
  rw [← nativeFlatGroupCoefficientMap_comp.{0, 0, 1, 2, 3} φ ψ f g, direct_value]
  intro h
  have hz := congrArg ULift.down h
  norm_num at hz

end MathlibExtTest.FlatMapFunctoriality
