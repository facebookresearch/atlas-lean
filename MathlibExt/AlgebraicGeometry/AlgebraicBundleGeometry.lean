/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Constructions/VectorBundleOfModule.lean` and
`StacksFrontier/AlgebraicGeometry/Chow/ProjectiveBundleFormula/Formula.lean`
(AxiomMath/Stacks, https://github.com/AxiomMath/Stacks,
revision c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source files carry no individual author or copyright notice.
Modification notice: exposed only characterized positive-rank bundle data over
smooth bases, kept Mathlib's module pullbacks and the canonical unit comparison
in the section and quotient formulas, and proved no global relative-Proj or
total-space existence.
-/

module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import MathlibExt.AlgebraicGeometry.PerverseSheaves
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-!
# Geometric bundle inputs with actual universal properties

The projective bundle represents invertible quotients of the given actual
sheaf of modules; the quotient compatibility is included in its uniqueness
condition. The total space of a line bundle represents actual pulled-back
sections, and its zero section is fixed by the zero section of that same
universal property. These are characterized input constructions already
available in the cited source, not arbitrary carriers or extra Betti laws.

Both structures are stated over a smooth base of pure dimension `dx`, which is
recorded as a hypothesis on the base. The smoothness of both total spaces is a
derived instance, and so is the properness of a projective bundle over a proper
base; the total space of a line bundle is not proper (its zero section is).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

/-- The canonical isomorphism `f^* 𝒪_Y ≅ 𝒪_X`. -/
def pullbackUnit (X Y : Scheme.{0}) (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : (TopologicalSpace.Opens.map f.base).Final := by infer_instance
  letI := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

/-- The pullback `f^* s` of a global section `s : 𝒪_Y ⟶ M`. -/
def pullbackSection {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnit X Y f).inv ≫ (Scheme.Modules.pullback f).map s

open MathlibExt.AlgebraicGeometry.PerverseSheaves

/-- `E` is locally free of rank `r`: `CurveVectorBundles.IsVectorBundle`. -/
abbrev IsBundle {X : Scheme.{0}} (E : X.Modules) (r : ℕ) : Prop :=
  CurveVectorBundles.IsVectorBundle E r

/-- `L` is invertible, locally isomorphic to the structure sheaf:
`CoherentCurveLinearSeries.IsLineBundle`. -/
abbrev IsLine {X : Scheme.{0}} (L : X.Modules) : Prop :=
  CoherentCurveLinearSeries.IsLineBundle L

/-- The pullback along `f = g ≫ p` of a quotient `q : p^* E ⟶ L`, followed by
an identification `g^* L ≅ M`. -/
def pulledQuotient {X T V : ComplexScheme} (E : X.left.Modules) (L : V.left.Modules)
    (p : V ⟶ X) (q : (Scheme.Modules.pullback p.left).obj E ⟶ L)
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) (M : T.left.Modules)
    (e : (Scheme.Modules.pullback g.left).obj L ≅ M) :
    (Scheme.Modules.pullback f.left).obj E ⟶ M :=
  (Scheme.Modules.pullbackCongr (congrArg (fun v : T ⟶ X => v.left) h).symm).hom.app E ≫
    (Scheme.Modules.pullbackComp g.left p.left).inv.app E ≫
      (Scheme.Modules.pullback g.left).map q ≫ e.hom

/-- The projective bundle `ℙ(E)` of invertible quotients of a locally free
sheaf `E` of rank `r + 1` on a smooth complex variety `X` of pure dimension
`dx`, characterized by its universal property: morphisms `T ⟶ ℙ(E)` over `X`
correspond to invertible quotients of the pullback of `E` to `T`. -/
structure ProjectiveBundle (X : ComplexScheme) (dx r : ℕ) (E : X.left.Modules) where
  /-- `E` is locally free of rank `r + 1`. -/
  isBundle : IsBundle E (r + 1)
  /-- The base is smooth of pure dimension `dx`. -/
  baseSmooth : SmoothOfRelativeDimension dx X.hom
  /-- The total space. -/
  total : ComplexScheme
  /-- The bundle projection. -/
  projection : total ⟶ X
  /-- The total space is a complex variety. -/
  [variety : IsComplexVariety total]
  /-- The projection is proper. -/
  [proper : IsProper projection.left]
  /-- The projection is smooth of relative dimension `r`. -/
  [relativeSmooth : SmoothOfRelativeDimension r projection.left]
  /-- The tautological invertible quotient `𝒪(1)`. -/
  tautological : total.left.Modules
  /-- It is invertible. -/
  isLine : IsLine tautological
  /-- The tautological quotient map `p^* E ⟶ 𝒪(1)`. -/
  quotient : (Scheme.Modules.pullback projection.left).obj E ⟶ tautological
  /-- It is an epimorphism. -/
  [epiQuotient : Epi quotient]
  /-- The universal property of invertible quotients. -/
  universal : ∀ (T : ComplexScheme) (f : T ⟶ X) (M : T.left.Modules)
    (_hM : IsLine M) (q : (Scheme.Modules.pullback f.left).obj E ⟶ M) (_hq : Epi q),
    ∃! g : T ⟶ total, ∃ (h : g ≫ projection = f)
      (e : (Scheme.Modules.pullback g.left).obj tautological ≅ M),
      q = pulledQuotient E tautological projection quotient f g h M e

attribute [instance] ProjectiveBundle.variety ProjectiveBundle.proper
  ProjectiveBundle.relativeSmooth ProjectiveBundle.epiQuotient

/-- The total space of a projective bundle is smooth of dimension `dx + r`. -/
instance ProjectiveBundle.smooth {X : ComplexScheme} {dx r : ℕ} {E : X.left.Modules}
    (B : ProjectiveBundle X dx r E) : SmoothOfRelativeDimension (dx + r) B.total.hom := by
  have := B.baseSmooth
  rw [← Over.w B.projection, Nat.add_comm]
  infer_instance

/-- Over a proper base, the total space of a projective bundle is proper. -/
instance ProjectiveBundle.properTotal {X : ComplexScheme} {dx r : ℕ} {E : X.left.Modules}
    [IsProper X.hom] (B : ProjectiveBundle X dx r E) : IsProper B.total.hom := by
  rw [← Over.w B.projection]
  infer_instance

/-- The pullback along `f = g ≫ p` of a section `s : 𝒪_V ⟶ p^* L`. -/
def pulledCompositeSection {X T V : ComplexScheme} (L : X.left.Modules)
    (p : V ⟶ X) (s : SheafOfModules.unit V.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback p.left).obj L)
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) :
    SheafOfModules.unit T.left.ringCatSheaf ⟶ (Scheme.Modules.pullback f.left).obj L :=
  pullbackSection g.left ((Scheme.Modules.pullback p.left).obj L) s ≫
    (Scheme.Modules.pullbackComp g.left p.left).hom.app L ≫
      (Scheme.Modules.pullbackCongr (congrArg (fun v : T ⟶ X => v.left) h)).hom.app L

/-- The total space of an invertible sheaf `L` on a smooth complex variety `X`
of pure dimension `dx`, characterized by its universal property: morphisms
`T ⟶ V(L)` over `X` correspond to sections of the pullback of `L` to `T`. The
zero section corresponds to the zero section of `L`. -/
structure LineTotalSpace (X : ComplexScheme) (dx : ℕ) (L : X.left.Modules) where
  /-- `L` is invertible. -/
  isLine : IsLine L
  /-- The base is smooth of pure dimension `dx`. -/
  baseSmooth : SmoothOfRelativeDimension dx X.hom
  /-- The total space. -/
  total : ComplexScheme
  /-- The bundle projection. -/
  projection : total ⟶ X
  /-- The total space is a complex variety. -/
  [variety : IsComplexVariety total]
  /-- The projection is smooth of relative dimension one. -/
  [relativeSmooth : SmoothOfRelativeDimension 1 projection.left]
  /-- The universal section of the pullback of `L`. -/
  universalSection : SheafOfModules.unit total.left.ringCatSheaf ⟶
    (Scheme.Modules.pullback projection.left).obj L
  /-- The universal property of sections. -/
  universal : ∀ (T : ComplexScheme) (f : T ⟶ X)
    (s : SheafOfModules.unit T.left.ringCatSheaf ⟶ (Scheme.Modules.pullback f.left).obj L),
    ∃! g : T ⟶ total, ∃ h : g ≫ projection = f,
      s = pulledCompositeSection L projection universalSection f g h
  /-- The zero section. -/
  zero : X ⟶ total
  /-- It is a section of the projection. -/
  zero_projection : zero ≫ projection = 𝟙 X
  /-- It classifies the zero section of `L`. -/
  zero_section : pulledCompositeSection L projection universalSection (𝟙 X) zero zero_projection = 0
  /-- It is a closed immersion. -/
  [closedZero : IsClosedImmersion zero.left]

attribute [instance] LineTotalSpace.variety LineTotalSpace.relativeSmooth LineTotalSpace.closedZero

/-- The total space of an invertible sheaf is smooth of dimension `dx + 1`. -/
instance LineTotalSpace.smooth {X : ComplexScheme} {dx : ℕ} {L : X.left.Modules}
    (V : LineTotalSpace X dx L) : SmoothOfRelativeDimension (dx + 1) V.total.hom := by
  have := V.baseSmooth
  rw [← Over.w V.projection, Nat.add_comm]
  infer_instance

end MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
