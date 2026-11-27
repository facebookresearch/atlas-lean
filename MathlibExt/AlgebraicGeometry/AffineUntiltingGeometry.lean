/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import MathlibExt.AlgebraicGeometry.IntegralTiltModels
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites

/-!
# Actual affine untilts and normalized relative tilting

Objects retain the actual perfectoid ring, its native integral inverse
limit, localized tilt and all-rank point comparison. An arrow retains
both actual ring maps; its sharp equation on every integral numerator
fixes the tilted map. Identity and composition retain these equations.

Relative tilting is the native induced functor on the categories over
a fixed untilt. Its source v-covers use the original all-rank point
spaces, so cover/site equivalence remains a substantive comparison.
Native sheaf restriction and its chosen adjoint supply the actual
global tilting maps and their unit/counit normalization.

Sources: Scholze, arXiv:1111.4914v1, Theorems 1.7--1.11 and 6.3;
arXiv:1709.07343v4, Definition 8.1 and Theorem 3.12.
The field-base hypotheses belong to the comparison theorems, not to
the construction of the actual relative functors.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MathlibExt.RingTheory.CompleteHuberPairModels
open IntegralTiltModels AffinePerfectoidVSite

variable (p : ℕ) [Fact p.Prime]

/-- An actual perfectoid affine with its prescribed local tilt model. -/
structure AffineUntilting where
  pair : PerfectoidPair p
  input : IntegralInput p pair
  tilt : TiltModel p pair (D := input)
  points : TiltingPoints p pair tilt

attribute [instance] AffineUntilting.input

/-- A map of untilts: actual maps of the original and tilted pairs together with the induced map
of integral tilt rings, which the tilted map extends and along which the original map commutes
with `sharp`. -/
structure Hom (P Q : AffineUntilting p) where
  original : RingMap Q.pair.toHuberPair P.pair.toHuberPair
  tilted : P.tilt.pair ⟶ Q.tilt.pair
  integral : IntegralRing p Q.pair →+* IntegralRing p P.pair
  tilted_integral : tilted.hom.comp (TiltModel.integralMap p Q.pair Q.tilt) =
    (TiltModel.integralMap p P.pair P.tilt).comp integral
  sharp_integral : ∀ a : IntegralRing p Q.pair,
    original.hom (sharp p Q.pair (D := Q.input) a) = sharp p P.pair (D := P.input) (integral a)

namespace Hom

variable {p}

@[ext] theorem ext {P Q : AffineUntilting p} (f g : Hom p P Q)
    (h : f.original = g.original) (h' : f.tilted = g.tilted) (h'' : f.integral = g.integral) :
    f = g := by
  cases f
  cases g
  cases h
  cases h'
  cases h''
  rfl

/-- Every integral element satisfies the sharp equations through the integral map. -/
theorem sharp {P Q : AffineUntilting p} (f : Hom p P Q) (a : IntegralRing p Q.pair) :
    f.tilted.hom (TiltModel.integralMap p Q.pair Q.tilt a) =
        TiltModel.integralMap p P.pair P.tilt (f.integral a) ∧
      f.original.hom (sharp p Q.pair (D := Q.input) a) =
        sharp p P.pair (D := P.input) (f.integral a) :=
  ⟨congrArg (fun φ : IntegralRing p Q.pair →+* P.tilt.pair.ring ↦ φ a) f.tilted_integral,
    f.sharp_integral a⟩

/-- The actual identity, including its sharp normalization. -/
def id (P : AffineUntilting p) : Hom p P P where
  original := ⟨RingHom.id _, continuous_id, fun _ h ↦ h⟩
  tilted := 𝟙 P.tilt.pair
  integral := RingHom.id _
  tilted_integral := rfl
  sharp_integral _ := rfl

/-- Compose actual maps and the corresponding integral sharp equations. -/
def comp {P Q R : AffineUntilting p} (f : Hom p P Q) (g : Hom p Q R) :
    Hom p P R where
  original :=
    ⟨f.original.hom.comp g.original.hom,
      f.original.continuous.comp g.original.continuous,
      fun a h ↦ f.original.plus _ (g.original.plus _ h)⟩
  tilted := f.tilted ≫ g.tilted
  integral := f.integral.comp g.integral
  tilted_integral := by
    ext a
    change f.tilted.hom (g.tilted.hom _) = _
    rw [(g.sharp a).1, (f.sharp (g.integral a)).1]
    rfl
  sharp_integral a := by
    change f.original.hom (g.original.hom _) = _
    rw [g.sharp_integral a, f.sharp_integral]
    rfl

end Hom

instance : Category (AffineUntilting p) where
  Hom := Hom p
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    · apply RingMap.ext; ext a; rfl
    · exact Category.id_comp f.tilted
    · ext a; rfl
  comp_id f := by
    apply Hom.ext
    · apply RingMap.ext; ext a; rfl
    · exact Category.comp_id f.tilted
    · ext a; rfl
  assoc f g h := by
    apply Hom.ext
    · apply RingMap.ext; ext a; rfl
    · exact Category.assoc f.tilted g.tilted h.tilted
    · ext a; rfl

/-- The actual local tilting functor, on rings and on normalized maps. -/
def tiltFunctor : AffineUntilting p ⥤ Affine p where
  obj P := P.tilt.pair
  map f := f.tilted
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Perfectoid affine objects over the fixed actual untilt. -/
abbrev RelativeAffine (K : AffineUntilting p) := Over K

/-- Relative tilting is the native functor induced on over categories. -/
def relativeTilting (K : AffineUntilting p) : RelativeAffine p K ⥤ Over K.tilt.pair :=
  Over.post (tiltFunctor p)

/-- An original-space v-cover, with the exact finite compact-open rule. -/
def IsOriginalVCover {I : Type 1} (P : AffineUntilting p)
    (U : I → AffineUntilting p) (f : ∀ i, U i ⟶ P) : Prop :=
  ∀ W : Opens P.pair.toHuberPair.Space, IsCompact (W : Set P.pair.toHuberPair.Space) →
    ∃ J : Finset I, ∃ V : ∀ i, Opens (U i).pair.toHuberPair.Space,
      (∀ i ∈ J, IsCompact (V i : Set (U i).pair.toHuberPair.Space)) ∧
      (W : Set P.pair.toHuberPair.Space) = ⋃ i ∈ J,
        (f i).original.spa '' (V i : Set (U i).pair.toHuberPair.Space)

/-- The original v-topology is generated before applying the tilt functor. -/
def originalVTopology : GrothendieckTopology (AffineUntilting p) :=
  sInf {J | ∀ (I : Type 1) (P : AffineUntilting p)
    (U : I → AffineUntilting p) (f : ∀ i, U i ⟶ P),
    IsOriginalVCover p P U f → Sieve.ofArrows U f ∈ J P}

/-- The actual relative original v-site. -/
def relativeVTopology (K : AffineUntilting p) :
    GrothendieckTopology (RelativeAffine p K) := (originalVTopology p).over K

section Global

variable (K : AffineUntilting p)
  [(relativeTilting p K).IsContinuous (relativeVTopology p K)
    ((topology p).over K.tilt.pair)]

/-- Native restriction from the tilted site, with every affine section fixed. -/
def untiltSheaves : Sheaf ((topology p).over K.tilt.pair) (Type 1) ⥤
    Sheaf (relativeVTopology p K) (Type 1) :=
  (relativeTilting p K).sheafPushforwardContinuous (Type 1) _ _

variable [(untiltSheaves p K).IsRightAdjoint]

/-- The actual left adjoint of the fixed affine-site restriction. -/
def tiltSheaves : Sheaf (relativeVTopology p K) (Type 1) ⥤
    Sheaf ((topology p).over K.tilt.pair) (Type 1) :=
  (untiltSheaves p K).leftAdjoint

/-- Its actual tilting/restriction adjunction. -/
def tiltingAdjunction : tiltSheaves p K ⊣ untiltSheaves p K :=
  Adjunction.ofIsRightAdjoint (untiltSheaves p K)

/-- The prescribed global tilting unit, at every actual sheaf. -/
def tiltingUnit : 𝟭 _ ⟶ tiltSheaves p K ⋙ untiltSheaves p K :=
  (tiltingAdjunction p K).unit

/-- The prescribed global tilting counit, at every actual sheaf. -/
def tiltingCounit : untiltSheaves p K ⋙ tiltSheaves p K ⟶ 𝟭 _ :=
  (tiltingAdjunction p K).counit

end Global

end MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
