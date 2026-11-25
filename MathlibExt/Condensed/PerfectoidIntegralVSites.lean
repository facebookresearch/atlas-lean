/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
public import MathlibExt.AlgebraicGeometry.IntegralTiltModels
public import MathlibExt.Condensed.GeometricTopologicalRestriction
public import MathlibExt.Condensed.PerfectoidSolidCoefficientModels
public import Mathlib.Tactic.FunProp

/-!
# Untilting data and actual geometric integral coefficients on v-tests

An untilting diagram specifies actual perfectoid pairs on the affine
tests of a v-sheaf, their local integral tilt identifications and actual
continuous restriction maps, together with functorial restriction maps of
the integral tilt rings. These are extended by the characteristic-p chart
maps and commute with `sharp`, which fixes the restrictions of untilts
against the characteristic-p chart maps.
The integral coefficient ring is the plus ring of this actual untilt.
It is not the plus ring of the characteristic-p test unless that is
the specified untilt.

The coefficient site is the product of the affine v-test site and
compact Hausdorff tests. Its two generating covering rules are the
actual v-covers and the native compact coherent covers. Its structural
presheaf is C(S,A^+) with the actual continuous coefficient maps.
Module restrictions to charts are native restriction along the fixed
compact-test inclusion and identity map on these coefficient rings.

Sources: Scholze, arXiv:1709.07343v4, Definition 15.5; Anschuetz--Mann,
arXiv:2403.01951v2, Theorem 1.1 and Definition 4.2. The untilt is
geometric input; descent and modified DG realization are separate work.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.PerfectoidIntegralVSites

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
open MathlibExt.AlgebraicGeometry.IntegralTiltModels
open GeometricScalarRestriction SolidAnalyticModules

variable (p : ℕ) [Fact p.Prime]

/-- A compatible family of actual untilts of all the specified affine tests. -/
structure UntiltingDiagram (F : VSheaf p) where
  pair : AffineTest p F → PerfectoidPair p
  input : ∀ T, IntegralInput p (pair T)
  tilt : ∀ T, TiltModel p (pair T) (D := input T)
  identification : ∀ T, (tilt T).pair ≅ T.left
  restriction : ∀ {T U : AffineTest p F} (_f : T ⟶ U),
    RingMap (pair U).toHuberPair (pair T).toHuberPair
  restriction_id : ∀ T, (restriction (𝟙 T)).hom = RingHom.id _
  restriction_comp : ∀ {T U V : AffineTest p F} (f : T ⟶ U) (g : U ⟶ V),
    (restriction (f ≫ g)).hom = (restriction f).hom.comp (restriction g).hom
  /-- The integral tilt rings restrict functorially along every map of tests, as the integral map
  of `AffineUntiltingGeometry.Hom` does. -/
  integral : ∀ {T U : AffineTest p F} (_f : T ⟶ U),
    IntegralRing p (pair U) →+* IntegralRing p (pair T)
  integral_id : ∀ T, integral (𝟙 T) = RingHom.id _
  integral_comp : ∀ {T U V : AffineTest p F} (f : T ⟶ U) (g : U ⟶ V),
    integral (f ≫ g) = (integral f).comp (integral g)
  /-- The projected characteristic-`p` chart map extends the integral map. -/
  tilted_integral : ∀ {T U : AffineTest p F} (f : T ⟶ U),
    ((identification T).hom ≫ (projection p F).map f ≫ (identification U).inv).hom.comp
        (TiltModel.integralMap p (pair U) (tilt U)) =
      (TiltModel.integralMap p (pair T) (tilt T)).comp (integral f)
  /-- The restriction of untilts commutes with `sharp` along the integral map. -/
  sharp_integral : ∀ {T U : AffineTest p F} (f : T ⟶ U) (a : IntegralRing p (pair U)),
    (restriction f).hom (sharp p (pair U) (D := input U) a) =
      sharp p (pair T) (D := input T) (integral f a)

variable {p}

/-- Every integral numerator has a compatible restriction, given by the integral map: its tilt
is the projected characteristic-`p` restriction, and its `sharp` is the restriction of `sharp`. -/
theorem UntiltingDiagram.sharp_naturality {F : VSheaf p} (D : UntiltingDiagram p F)
    {T U : AffineTest p F} (f : T ⟶ U) (a : IntegralRing p (D.pair U)) :
    ∃ b : IntegralRing p (D.pair T),
      ((D.identification T).hom ≫ (projection p F).map f ≫
        (D.identification U).inv).hom
          (TiltModel.integralMap p (D.pair U) (D := D.input U) (D.tilt U) a) =
            TiltModel.integralMap p (D.pair T) (D := D.input T) (D.tilt T) b ∧
      (D.restriction f).hom (sharp p (D.pair U) (D := D.input U) a) =
        sharp p (D.pair T) (D := D.input T) b :=
  ⟨D.integral f a, congrArg (fun φ ↦ φ a) (D.tilted_integral f), D.sharp_integral f a⟩

/-- The actual plus ring of the geometric untilt on a chart. -/
abbrev IntegralCoefficient {F : VSheaf p} (D : UntiltingDiagram p F)
    (T : AffineTest p F) := ULift.{1} (D.pair T).plus

/-- The actual continuous integral coefficient restriction. -/
def integralRestriction {F : VSheaf p} (D : UntiltingDiagram p F)
    {T U : AffineTest p F} (f : T ⟶ U) :
    IntegralCoefficient D U →+* IntegralCoefficient D T where
  toFun a := ULift.up ⟨(D.restriction f).hom a.down,
    (D.restriction f).plus _ a.down.2⟩
  map_zero' := ULift.ext (Subtype.ext (map_zero _))
  map_one' := ULift.ext (Subtype.ext (map_one _))
  map_add' _a _b := ULift.ext (Subtype.ext (map_add _ _ _))
  map_mul' _a _b := ULift.ext (Subtype.ext (map_mul _ _ _))

/-- Continuity is inherited from the actual bounded map of untilts. -/
theorem continuous_integralRestriction {F : VSheaf p} (D : UntiltingDiagram p F)
    {T U : AffineTest p F} (f : T ⟶ U) : Continuous (integralRestriction D f) := by
  have h := (D.restriction f).continuous
  change Continuous (fun a : IntegralCoefficient D U ↦
    ULift.up (⟨(D.restriction f).hom a.down,
      (D.restriction f).plus _ a.down.2⟩ : (D.pair T).plus))
  fun_prop

variable (p)

/-- Geometric and compact test objects, with both actual map directions. -/
abbrev CondensedTest (F : VSheaf p) := AffineTest p F × CompHaus.{0}

variable {p}

/-- Include every compact Hausdorff test over one fixed geometric chart. -/
def compactTests {F : VSheaf p} (T : AffineTest p F) :
    CompHaus.{0} ⥤ CondensedTest p F where
  obj S := (T, S)
  map f := (𝟙 T, f)

/-- The native scalar map on continuous sections of every actual untilt. -/
def sectionRestriction {F : VSheaf p} (D : UntiltingDiagram p F)
    {X Y : CondensedTest p F} (f : X ⟶ Y) :
    C(Y.2, IntegralCoefficient D Y.1) →+* C(X.2, IntegralCoefficient D X.1) where
  toFun a := ⟨fun s ↦ integralRestriction D f.1 (a (f.2.hom.hom s)),
    (continuous_integralRestriction D f.1).comp
      (a.continuous.comp f.2.hom.hom.continuous)⟩
  map_zero' := by ext s; exact map_zero _
  map_one' := by ext s; exact map_one _
  map_add' a b := by ext s; exact map_add _ _ _
  map_mul' a b := by ext s; exact map_mul _ _ _

/-- The structural presheaf is literally C(S,A^+) for the chosen geometric untilt. -/
def integralPresheaf {F : VSheaf p} (D : UntiltingDiagram p F) :
    (CondensedTest p F)ᵒᵖ ⥤ CommRingCat.{1} where
  obj X := CommRingCat.of C(X.unop.2, IntegralCoefficient D X.unop.1)
  map f := CommRingCat.ofHom (sectionRestriction D f.unop)
  map_id X := by
    apply CommRingCat.hom_ext
    ext a s
    exact congrArg (fun q : (D.pair X.unop.1).ring →+* (D.pair X.unop.1).ring ↦
      q (a s).down) (D.restriction_id X.unop.1)
  map_comp f g := by
    apply CommRingCat.hom_ext
    ext a s
    exact congrArg (fun q ↦ q (a (f.unop.2.hom.hom (g.unop.2.hom.hom s))).down)
      (D.restriction_comp g.unop.1 f.unop.1)

/-- The product-site topology generated by the actual two covering rules. -/
def coefficientTopology (F : VSheaf p) : GrothendieckTopology (CondensedTest p F) :=
  sInf {J |
    (∀ (I : Type 1) (T : AffineTest p F) (U : I → AffineTest p F)
      (a : ∀ i, U i ⟶ T) (S : CompHaus.{0}),
      IsVCover p ((projection p F).obj T)
        (fun i ↦ (projection p F).obj (U i))
        (fun i ↦ (projection p F).map (a i)) →
      Sieve.ofArrows (fun i ↦ (U i, S)) (fun i ↦ (a i, 𝟙 S)) ∈ J (T, S)) ∧
    (∀ (T : AffineTest p F) (S : CompHaus.{0}) (R : Sieve S),
      R ∈ coherentTopology CompHaus.{0} S →
        R.functorPushforward (compactTests T) ∈ J (T, S))}

/-- The actual structural ring sheaf, after proving the specific presheaf's descent. -/
def integralRingSheaf {F : VSheaf p} (D : UntiltingDiagram p F)
    (h : Presheaf.IsSheaf (coefficientTopology F) (integralPresheaf D)) :
    Sheaf (coefficientTopology F) RingCat.{1} where
  obj := integralPresheaf D ⋙ forget₂ CommRingCat.{1} RingCat.{1}
  property := Presheaf.isSheaf_comp_of_isSheaf _ _ _ h

/-- Actual global geometric modules on the displayed ringed product site. -/
abbrev GeometricModules {F : VSheaf p} (D : UntiltingDiagram p F)
    (h : Presheaf.IsSheaf (coefficientTopology F) (integralPresheaf D)) :=
  SheafOfModules.{1} (integralRingSheaf D h)

section Restriction

variable {F : VSheaf p} (D : UntiltingDiagram p F)
  (h : Presheaf.IsSheaf (coefficientTopology F) (integralPresheaf D))
  (T : AffineTest p F)
  [(compactTests T).IsContinuous (coherentTopology CompHaus.{0}) (coefficientTopology F)]

/-- The chart coefficient map is the identity on the actual continuous sections. -/
def chartRingMap : TopologicalRings.ringSheaf (IntegralCoefficient D T) ⟶
    ((compactTests T).sheafPushforwardContinuous RingCat.{1}
      (coherentTopology CompHaus.{0}) (coefficientTopology F)).obj
        (integralRingSheaf D h) where
  hom.app S := 𝟙 _
  hom.naturality S U f := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    let a' : C(S.unop, IntegralCoefficient D T) := a
    change a'.comp f.unop.hom.hom =
      sectionRestriction D (X := (T, U.unop)) (Y := (T, S.unop)) (𝟙 T, f.unop) a'
    apply ContinuousMap.ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    exact congrArg (fun q : (D.pair T).ring →+* (D.pair T).ring ↦
      q (a' (f.unop.hom.hom s)).down) (D.restriction_id T).symm

/-- Literal chart restriction from the global module sheaf to C(-,A^+) modules. -/
def chartRestriction : GeometricModules D h ⥤
    GeometricScalarRestriction.GeometricModules (IntegralCoefficient D T) :=
  SheafOfModules.pushforward.{1} (chartRingMap D h T)

instance chartRestriction_additive : (chartRestriction D h T).Additive where
  map_add := rfl

/-- The actual cochain restriction, retaining every term and differential. -/
def chartCochainRestriction : CochainComplex (GeometricModules D h) ℤ ⥤
    CochainComplex (GeometricScalarRestriction.GeometricModules
      (IntegralCoefficient D T)) ℤ :=
  (chartRestriction D h T).mapHomologicalComplex (ComplexShape.up ℤ)

end Restriction

end MathlibExt.Condensed.PerfectoidIntegralVSites
