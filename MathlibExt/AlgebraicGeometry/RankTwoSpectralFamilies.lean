/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoHitchinModels
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The total canonical line and universal rank-two spectral family

The total line represents sections of K on every coefficient scheme, by
pullback of its actual tautological section. This fixes the convention
V(K) = Spec Sym(K dual). The spectral scheme is the native closed scheme
of the ideal of y squared minus s1 y plus s2. The ideal is fixed in every
actual affine line frame without taking its radical. No smoothness or
reducedness of the spectral curve is imposed.

Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2,
Section 1.3.2, equations (1.3.4)--(1.3.5).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RankTwoSpectralFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHitchinModels GeometricHiggsFamilies
open CoherentCurveLinearSeries LineBundleTaskContracts RelativeLambdaReindexing

def pullGlobal {X Y : Scheme.{0}} (f : X ⟶ Y) (E : Y.Modules) (s : Γ(E, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj E, ⊤) := by
  change ((Scheme.Modules.pullback f).obj E).val.obj (op ⊤)
  simpa using pullSection f E ⊤ s

def pulledTautological {C T V : ComplexScheme} (pi : V ⟶ C)
    (y : Section ((Scheme.Modules.pullback pi.left).obj (canonicalLine C)))
    (f : T ⟶ C) (g : T ⟶ V) (h : g ≫ pi = f) :
    Section ((Scheme.Modules.pullback f.left).obj (canonicalLine C)) :=
  pullbackSection g.left y ≫
    (Scheme.Modules.pullbackComp g.left pi.left).hom.app (canonicalLine C) ≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).hom.app (canonicalLine C)

/-- The actual section-representing total space, with its tautological section. -/
structure TotalLine (C : ComplexScheme) where
  scheme : ComplexScheme
  projection : scheme ⟶ C
  tautological : Section ((Scheme.Modules.pullback projection.left).obj (canonicalLine C))
  universal : ∀ (T : ComplexScheme) (f : T ⟶ C)
      (s : Section ((Scheme.Modules.pullback f.left).obj (canonicalLine C))),
    ∃! g : T ⟶ scheme, ∃ h : g ≫ projection = f,
      pulledTautological projection tautological f g h = s

def totalWithBase (C : ComplexScheme) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (V : TotalLine C) : ComplexScheme :=
  prod V.scheme (base C)

def toCurveBase (C : ComplexScheme) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (V : TotalLine C) :
    totalWithBase C V ⟶ prod C (base C) := prod.map V.projection (𝟙 (base C))

def toCurve (C : ComplexScheme) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (V : TotalLine C) : totalWithBase C V ⟶ C :=
  (prod.fst : prod V.scheme (base C) ⟶ V.scheme) ≫ V.projection

theorem toCurveBase_first (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (V : TotalLine C) :
    toCurveBase C V ≫ (prod.fst : prod C (base C) ⟶ C) = toCurve C V := by
  simp [toCurveBase, toCurve]

def tautologicalLine (C : ComplexScheme) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (V : TotalLine C) : (totalWithBase C V).left.Modules :=
  (Scheme.Modules.pullback (toCurve C V).left).obj (canonicalLine C)

def universalTautological (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (V : TotalLine C) :
    Section (tautologicalLine C V) :=
  pulledTautological V.projection V.tautological (toCurve C V)
    (prod.fst : totalWithBase C V ⟶ V.scheme) rfl

/-- Pull the actual Hitchin coefficient through the literal total-line product. -/
def coefficientOnTotal (C : ComplexScheme) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (V : TotalLine C)
    (P : PullbackPowers (toCurve C V).left) (n : ℕ)
    (s : Γ(relativeLinePower C (base C) n, ⊤)) :
    Γ(power (tautologicalLine C V) n, ⊤) :=
  let a := (Scheme.Modules.pullbackComp (toCurveBase C V).left
    (prod.fst : prod C (base C) ⟶ C).left).hom.app (power (canonicalLine C) n)
  let b := (Scheme.Modules.pullbackCongr
    (congrArg Over.Hom.left (toCurveBase_first C V))).hom.app
      (power (canonicalLine C) n)
  ((a ≫ b ≫ (P.comparison n).hom.app (canonicalLine C)).val.app (op ⊤)).hom
    (pullGlobal (toCurveBase C V).left (relativeLinePower C (base C) n) s)

/-- The actual line-power equation, using native pure tensors and tautological y. -/
def spectralEquation (C : ComplexScheme) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (S : SectionBases C) (V : TotalLine C)
    (P : PullbackPowers (toCurve C V).left) : Γ(power (tautologicalLine C V) 2, ⊤) :=
  let L := tautologicalLine C V
  let y := (((universalTautological C V).val.app (op ⊤)).hom
    (1 : Γ((totalWithBase C V).left, ⊤)))
  let linearTerm : Γ(power L 2, ⊤) := localTensor (power L 1) L ⊤
    (coefficientOnTotal C V P 1 (parameterSections C S (base C) (𝟙 (base C))).one) y
  localPower L ⊤ y 2 - linearTerm +
    coefficientOnTotal C V P 2 (parameterSections C S (base C) (𝟙 (base C))).two

/-- The actual ideal of a line section, fixed in all frames rather than by support. -/
structure LineSectionIdeal (X : Scheme.{0}) (L : X.Modules) (s : Γ(L, ⊤)) where
  ideal : X.IdealSheafData
  frameCover : ∀ x : X, ∃ (U : X.Opens) (_h : IsAffineOpen U), x ∈ U ∧
    Nonempty (Module.Basis Unit Γ(X, U) Γ(L, U))
  normalized : ∀ (U : X.Opens) (h : IsAffineOpen U)
      (F : Module.Basis Unit Γ(X, U) Γ(L, U)),
    ideal.ideal ⟨U, h⟩ = Ideal.span
      {F.repr ((L.val.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s) ()}

structure SpectralIdeal (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (S : SectionBases C) (V : TotalLine C)
    (P : PullbackPowers (toCurve C V).left) where
  equation : LineSectionIdeal (totalWithBase C V).left
    (power (tautologicalLine C V) 2) (spectralEquation C S V P)

/-- The spectral family is the native subscheme of its genuine equation ideal. -/
def spectralScheme {C : ComplexScheme} [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    {S : SectionBases C} {V : TotalLine C}
    {P : PullbackPowers (toCurve C V).left} (I : SpectralIdeal C S V P) : ComplexScheme :=
  Over.mk (I.equation.ideal.subschemeι ≫ (totalWithBase C V).hom)

def spectralInclusion {C : ComplexScheme} [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    {S : SectionBases C} {V : TotalLine C}
    {P : PullbackPowers (toCurve C V).left} (I : SpectralIdeal C S V P) :
    spectralScheme I ⟶ totalWithBase C V := Over.homMk I.equation.ideal.subschemeι rfl

def spectralProjection {C : ComplexScheme} [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    {S : SectionBases C} {V : TotalLine C}
    {P : PullbackPowers (toCurve C V).left} (I : SpectralIdeal C S V P) :
    spectralScheme I ⟶ prod C (base C) := spectralInclusion I ≫ toCurveBase C V

def parameterProjection {C : ComplexScheme} [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] {S : SectionBases C} {V : TotalLine C}
    {P : PullbackPowers (toCurve C V).left} (I : SpectralIdeal C S V P) :
    spectralScheme I ⟶ base C := spectralProjection I ≫ prod.snd

/-- The finite flat double-cover theorem applies to the full equation scheme. -/
structure SpectralFamily (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (S : SectionBases C) where
  totalLine : TotalLine C
  powers : PullbackPowers (toCurve C totalLine).left
  ideal : SpectralIdeal C S totalLine powers
  finite : IsFinite (spectralProjection ideal).left
  flat : Flat (spectralProjection ideal).left
  rank : CurveVectorBundles.IsVectorBundle
    ((Scheme.Modules.pushforward (spectralProjection ideal).left).obj
      (structureModule (spectralScheme ideal).left)) 2

def baseChangedSpectral {C T : ComplexScheme} [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] {S : SectionBases C}
    (F : SpectralFamily C S) (s : T ⟶ base C) : ComplexScheme :=
  pullback (spectralProjection F.ideal) (prod.map (𝟙 C) s)

def baseChangedProjection {C T : ComplexScheme} [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] {S : SectionBases C}
    (F : SpectralFamily C S) (s : T ⟶ base C) : baseChangedSpectral F s ⟶ prod C T :=
  pullback.snd (spectralProjection F.ideal) (prod.map (𝟙 C) s)

end MathlibExt.AlgebraicGeometry.RankTwoSpectralFamilies
