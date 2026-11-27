/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientNaturality
public import MathlibExt.CategoryTheory.Action.Trivial
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.Abel
public meta import Mathlib.Tactic.NormNum

/-!
# Unequal coefficient maps on a split exact sequence

The group is the finite cyclic group C₂, regarded as a profinite group in universe
zero. The coefficient group is ULift ℤ in universe one, with trivial action.
The sequence A → A × A → A is the first inclusion and second projection.

Its endomorphism doubles the first term, acts by (x,y) ↦ (2x,3y) on the middle
term, and triples the last term. The degree-zero class with coefficient one
maps to the nonzero coefficient two in the first term. The complete exact-window
comparison gives the same value after mapping on the native cochain-homology
side. The natural connecting transformation commutes with these unequal maps
in every degree. No nonzero connecting-map assertion is made for this split
sequence.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory ContinuousCohomology

namespace MathlibExtTest.ContinuousCoefficientNaturality

private abbrev G : ProfiniteGrp.{0} :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2)))

private abbrev Coeff := ULift.{1} ℤ

private abbrev A : DiscreteAbelianAction.{0, 1} G :=
  DiscreteAbelianAction.trivialObject G (AddCommGrpCat.of Coeff)

private abbrev B : DiscreteAbelianAction.{0, 1} G :=
  DiscreteAbelianAction.trivialObject G (AddCommGrpCat.of (Coeff × Coeff))

private def inclusionAdd : Coeff →+ Coeff × Coeff where
  toFun x := (x, 0)
  map_zero' := rfl
  map_add' _ _ := rfl

private def inclusion : A ⟶ B :=
  DiscreteAbelianAction.trivialMap G (AddCommGrpCat.ofHom inclusionAdd)

private def projection : B ⟶ A :=
  DiscreteAbelianAction.trivialMap G
    (AddCommGrpCat.ofHom (AddMonoidHom.snd Coeff Coeff))

private lemma range_kernel :
    (discreteCoefficientHom inclusion).range =
      (discreteCoefficientHom projection).ker := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hz
    change z.2 = 0 at hz
    refine ⟨z.1, ?_⟩
    change (z.1, (0 : Coeff)) = z
    exact Prod.ext rfl hz.symm

private def sequence :
    ShortComplex (DiscreteContAction (TopModuleCat.{1} ℤ) G) :=
  discreteCoefficientShortComplex.{0, 1} inclusion projection range_kernel

private lemma sequence_exact : DiscreteCoefficientExact.{0, 1} sequence := by
  refine ⟨?_, range_kernel, ?_⟩
  · intro x y h
    exact congrArg Prod.fst h
  · intro y
    exact ⟨(0, y), rfl⟩

private def twice : A ⟶ A := 𝟙 A + 𝟙 A

private def thrice : A ⟶ A := (𝟙 A + 𝟙 A) + 𝟙 A

private def middleAdd : Coeff × Coeff →+ Coeff × Coeff where
  toFun p := (p.1 + p.1, p.2 + p.2 + p.2)
  map_zero' := by simp
  map_add' p q := by
    apply Prod.ext
    · change (p.1 + q.1) + (p.1 + q.1) = (p.1 + p.1) + (q.1 + q.1)
      abel
    · change (p.2 + q.2) + (p.2 + q.2) + (p.2 + q.2) =
        (p.2 + p.2 + p.2) + (q.2 + q.2 + q.2)
      abel

private def middle : B ⟶ B :=
  DiscreteAbelianAction.trivialMap G (AddCommGrpCat.ofHom middleAdd)

private def coefficientDiagram : sequence ⟶ sequence where
  τ₁ := twice
  τ₂ := middle
  τ₃ := thrice
  comm₁₂ := by
    apply (DiscreteAbelianAction.forget G).map_injective
    apply ConcreteCategory.ext_apply
    intro x
    change (x + x, (0 : Coeff)) = (x + x, 0 + 0 + 0)
    simp only [add_zero]
  comm₂₃ := by
    apply (DiscreteAbelianAction.forget G).map_injective
    apply ConcreteCategory.ext_apply
    intro x
    rfl

private def exactSequence : DiscreteCoefficientExactSequences.{0, 1} G :=
  ⟨sequence, sequence_exact⟩

private def diagram : exactSequence ⟶ exactSequence :=
  ObjectProperty.homMk coefficientDiagram

private abbrev H₀ := discreteCoefficientCohomologyFunctor.{0, 1} G 0

private abbrev zeroIso := discreteCoefficientZeroIso.{0, 1} G A

private def invariantOne :
    discreteCoefficientForget.{1}.obj
      (TopRep.invariants (inhomogeneousOriginalTopRep.{0, 0, 1} G A)) :=
  ⟨ULift.up (1 : ℤ), fun _ => rfl⟩

private def classOne : H₀.obj A := zeroIso.inv.hom invariantOne

private def coordinate (x : H₀.obj A) : Coeff := (zeroIso.hom.hom x).val

private lemma coordinate_one : coordinate classOne = ULift.up (1 : ℤ) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom zeroIso.inv_hom_id invariantOne)

private lemma coordinate_zero : coordinate 0 = 0 := by
  simp [coordinate]

private lemma twice_cohomology_map :
    H₀.map twice = 𝟙 (H₀.obj A) + 𝟙 (H₀.obj A) := by
  simp only [twice, Functor.map_add, Functor.map_id]

private lemma mapped_coordinate :
    coordinate (H₀.map twice classOne) = ULift.up (2 : ℤ) := by
  rw [twice_cohomology_map]
  change (zeroIso.hom.hom (classOne + classOne)).val = ULift.up (2 : ℤ)
  rw [map_add]
  change coordinate classOne + coordinate classOne = ULift.up (2 : ℤ)
  rw [coordinate_one]
  rfl

private abbrev homologyIso := discreteCoefficientHomologyIso.{0, 1} G A 0

private abbrev nativeH₀ :=
  ((discreteCoefficientCochainFunctor.{0, 1} G).obj A).homology 0

private def nativeClassOne : nativeH₀ := homologyIso.hom.hom classOne

private def nativeCoordinate (x : nativeH₀) : Coeff := coordinate (homologyIso.inv.hom x)

private lemma nativeCoordinate_comparison (x : H₀.obj A) :
    nativeCoordinate (homologyIso.hom x) = coordinate x :=
  congrArg coordinate (ConcreteCategory.congr_hom homologyIso.hom_inv_id x)

private lemma nativeCoordinate_zero : nativeCoordinate 0 = 0 := by
  simp [nativeCoordinate, coordinate]

private abbrev nativeWindow :=
  discreteCoefficientShortExactCochainFunctor.{0, 1} G ⋙
    HomologicalComplex.HomologySequence.exactSequenceFunctor
      0 1 (discreteCoefficientUpRel 0)

private abbrev comparison := discreteCoefficientExactWindowNatIso.{0, 1} G 0

private lemma native_mapped_coordinate :
    nativeCoordinate ((nativeWindow.map diagram).hom.app 0 nativeClassOne) =
      ULift.up (2 : ℤ) := by
  have h := comparison.hom.naturality diagram
  have h₀ := congrArg (fun f => f.hom.app 0) h
  change H₀.map twice ≫ homologyIso.hom =
    homologyIso.hom ≫ (nativeWindow.map diagram).hom.app 0 at h₀
  have hx := ConcreteCategory.congr_hom h₀ classOne
  calc
    nativeCoordinate ((nativeWindow.map diagram).hom.app 0 nativeClassOne) =
        nativeCoordinate (homologyIso.hom (H₀.map twice classOne)) :=
      congrArg nativeCoordinate hx.symm
    _ = coordinate (H₀.map twice classOne) := nativeCoordinate_comparison _
    _ = ULift.up (2 : ℤ) := mapped_coordinate

example : twice ≠ 𝟙 A := by
  intro h
  have hx := congrArg (fun f : A ⟶ A =>
    discreteCoefficientHom f (ULift.up (1 : ℤ))) h
  change ULift.up (2 : ℤ) = ULift.up (1 : ℤ) at hx
  have hz := congrArg ULift.down hx
  norm_num at hz

example : coordinate classOne = ULift.up (1 : ℤ) := coordinate_one

example : classOne ≠ 0 := by
  intro h
  have hc := coordinate_one
  rw [h, coordinate_zero] at hc
  have hz := congrArg ULift.down hc
  norm_num at hz

example : coordinate (H₀.map twice classOne) = ULift.up (2 : ℤ) := mapped_coordinate

example : H₀.map twice classOne ≠ classOne := by
  intro h
  have hc := congrArg coordinate h
  rw [mapped_coordinate, coordinate_one] at hc
  have hz := congrArg ULift.down hc
  norm_num at hz

example : nativeCoordinate nativeClassOne = ULift.up (1 : ℤ) :=
  (nativeCoordinate_comparison classOne).trans coordinate_one

example : nativeCoordinate ((nativeWindow.map diagram).hom.app 0 nativeClassOne) =
    ULift.up (2 : ℤ) := native_mapped_coordinate

example : (nativeWindow.map diagram).hom.app 0 nativeClassOne ≠ 0 := by
  intro h
  have hc := native_mapped_coordinate
  rw [h, nativeCoordinate_zero] at hc
  have hz := congrArg ULift.down hc
  norm_num at hz

example (n : ℕ) :
    (discreteCoefficientConnectingNatTrans.{0, 1} G n).app exactSequence ≫
        (discreteCoefficientCohomologyFunctor.{0, 1} G (n + 1)).map twice =
      (discreteCoefficientCohomologyFunctor.{0, 1} G n).map thrice ≫
        (discreteCoefficientConnectingNatTrans.{0, 1} G n).app exactSequence :=
  ((discreteCoefficientConnectingNatTrans.{0, 1} G n).naturality diagram).symm

end MathlibExtTest.ContinuousCoefficientNaturality
