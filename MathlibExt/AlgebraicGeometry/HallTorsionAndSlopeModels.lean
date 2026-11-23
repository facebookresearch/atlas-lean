/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.InfiniteHallStackFunctions
public import MathlibExt.AlgebraicGeometry.HallNumericalGradingModels

/-!
# Native torsion-pair cuts and the corrected slope-window filtration condition

The zero-dimensional and pure cuts are predicates on the actual
geometric sheaf fibres. An open cut retains its complete native
family image and actual represented open-immersion fibres.

Slopes use χ(F)/(β(F)·L) for the actual ample line bundle, with
zero-dimensional slope infinity. Bounds test actual coherent
subobjects and actual epimorphic quotients. Three-step filtrations
retain both original short exact sequences and their shared middle
term comparison. These operations express the corrected source
argument; unrestricted equation (49) is not requested.

Reference: Bridgeland, arXiv:1002.4374v3, §2.2, §4.3,
§6.1 and the second correction §7.4, equations (51) and its filtration.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallTorsionAndSlopeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open GeometricHallStackFunctions HallFamilyStackModels HallNumericalGradingModels
open HallExactSequenceFamilies StablePairFamilies StablePairParameterPullbacks
open StackCycleGeometry StackFibreModels ProjectiveLineSystems

variable {X : Over base}

def ZeroDimensional {T : Over base} (F : HallExactSequenceFamilies.Family X T) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] (p : geometricParameter Ω ⟶ T),
    supportDimension (geometricModule X F Ω p) ≤ (0 : ℕ)

def NoZeroDimensionalSubobjects {T : Over base} (F : HallExactSequenceFamilies.Family X T) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] (p : geometricParameter Ω ⟶ T)
    (A : Subobject (geometricModule X F Ω p)),
    StablePairFamilies.coherent (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) →
    supportDimension (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) ≤ (0 : ℕ) →
      IsZero (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules)

/-- An open locus is normalized by the actual complete family predicate on all scheme tests. -/
structure OpenFamilyCut (H : HallStacks X)
    (predicate : ∀ T : Over base, HallExactSequenceFamilies.Family X T → Prop) where
  carrier : LocallyFiniteTypeStack
  inclusion : StackHom carrier.stack H.moduli
  fullyFaithful : ∀ T : Over base, (component inclusion T).FullyFaithful
  image : ∀ (T : Over base) (F : H.moduli.Fibre T),
    (∃ q : carrier.stack.Fibre T, Nonempty ((component inclusion T).obj q ≅ F)) ↔
      predicate T ((H.families.fibre T).functor.obj F)
  fibre : ∀ (T : Over base) (F : H.moduli.Fibre T), SchemeFibreModel inclusion T F
  openImmersion : ∀ (T : Over base) (F : H.moduli.Fibre T), IsOpenImmersion (fibre T F).scheme.hom

abbrev ZeroDimensionalCut (H : HallStacks X) :=
  OpenFamilyCut H (fun _T F => ZeroDimensional F)

abbrev PureCut (H : HallStacks X) :=
  OpenFamilyCut H (fun _T F => NoZeroDimensionalSubobjects F)

def cutGenerator {H : HallStacks X}
    {predicate : ∀ T : Over base, HallExactSequenceFamilies.Family X T → Prop}
    (P : OpenFamilyCut H predicate) : InfiniteHallStackFunctions.Generator H.moduli :=
  ⟨P.carrier,P.inclusion⟩

def fullGenerator (H : HallStacks X) : InfiniteHallStackFunctions.Generator H.moduli :=
  ⟨H.families.carrier,Pseudofunctor.StrongTrans.id H.moduli.toPseudofunctor⟩

/-- The two-term slope `twoTermEuler F / twoTermCurveProfile F L` (`⊤` when the profile vanishes);
it is the slope of `F` for coherent sheaves of support dimension at most one and ample `L`. -/
def twoTermSlope (L : LineBundle X.left) (Ω : Type) [Field Ω] [Algebra ℂ Ω]
    (F : (StablePairFamilies.total X (geometricParameter Ω)).Modules) : WithTop ℝ := by
  classical
  let r := twoTermCurveProfile X Ω F L
  exact if r=0 then ⊤ else ((twoTermEuler X Ω F : ℝ)/(r : ℝ) : ℝ)

def UpperSlopes (L : LineBundle X.left) (Ω : Type) [Field Ω] [Algebra ℂ Ω]
    (F : (StablePairFamilies.total X (geometricParameter Ω)).Modules) (u : ℝ) : Prop :=
  ∀ A : Subobject F,
    StablePairFamilies.coherent (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) →
    ¬IsZero (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) →
    twoTermSlope L Ω (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) ≤ (u : WithTop ℝ)

def StrictUpperSlopes (L : LineBundle X.left) (Ω : Type) [Field Ω] [Algebra ℂ Ω]
    (F : (StablePairFamilies.total X (geometricParameter Ω)).Modules) (u : ℝ) : Prop :=
  ∀ A : Subobject F,
    StablePairFamilies.coherent (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) →
    ¬IsZero (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) →
    twoTermSlope L Ω (A : (StablePairFamilies.total X (geometricParameter Ω)).Modules) < (u : WithTop ℝ)

def LowerSlopes (L : LineBundle X.left) (Ω : Type) [Field Ω] [Algebra ℂ Ω]
    (F : (StablePairFamilies.total X (geometricParameter Ω)).Modules) (l : ℝ) : Prop :=
  ∀ Q : (StablePairFamilies.total X (geometricParameter Ω)).Modules,
    StablePairFamilies.coherent Q → ∀ q : F ⟶ Q, Epi q → ¬IsZero Q →
      (l : WithTop ℝ) ≤ twoTermSlope L Ω Q

def SlopeWindow (L : LineBundle X.left) {T : Over base}
    (F : HallExactSequenceFamilies.Family X T) (l u : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] (p : geometricParameter Ω ⟶ T),
    LowerSlopes L Ω (geometricModule X F Ω p) l ∧ UpperSlopes L Ω (geometricModule X F Ω p) u

def StrictUpperWindow (L : LineBundle X.left) {T : Over base}
    (F : HallExactSequenceFamilies.Family X T) (l u : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] (p : geometricParameter Ω ⟶ T),
    LowerSlopes L Ω (geometricModule X F Ω p) l ∧ StrictUpperSlopes L Ω (geometricModule X F Ω p) u

/-- The actual filtration 0⊂E1⊂E2⊂E, with both original module-map sequences. -/
structure ThreeStepFiltration (T : Over base) where
  first : Sequence (X := X) (T := T)
  second : Sequence (X := X) (T := T)
  shared : first.middle.module ≅ second.sub.module

/-- The ample degree in the correction is computed from the actual total sheaf class. -/
def filtrationDegree {HX : Threefold X} (N : NumericalData X HX) (L : LineBundle X.left)
    (F : ThreeStepFiltration (X := X) complexPoint) : ℤ :=
  (familyClass N F.second.middle).val.1.val L

end MathlibExt.AlgebraicGeometry.HallTorsionAndSlopeModels
