/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeDerivedSpectrumModels
public import MathlibExt.AlgebraicTopology.BGTIndKappaModels
public import MathlibExt.AlgebraicTopology.NativeDiagramFamilies
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# Native spectrum zero, cofiber and loop sources

The diagrams use the actual native point-set spectrum maps before the
stable localization. Cofibers are the universal coherent cocones on
`E → F` and the native map `E → 0`. Loops are the universal coherent
cones on `0 → G ← 0`, with apex the actual derived circle function
spectrum. A cofiber extension is an arrow in that same cocone category,
so it retains the original nullhomotopy on the entire source diagram.

These are construction interfaces. No K-theory localization equivalence,
swindle vanishing or motive comparison is assumed in any source.

Sources: Hovey--Shipley--Smith, *Symmetric spectra*, Sections 3.1--3.4;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 7.1 and 9.1.
Native Mathlib walking-span/cospan maps at revision
56a005855ea17e0b0958f73ec801ae140b0a1679 are used directly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumConeSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityFilteredColimits
open NativeDiagramFamilies BGTIndKappaModels StableSpectraInfinitySource
open NativeDerivedSpectrumModels
open MathlibExt.SpectraSource
open scoped Simplicial

universe v u

/-- The actual nerve map from a small index to a possibly larger category. -/
def liftedNerveMap {J : Type} [Category.{0} J]
    {C : Type u} [Category.{v} C] (F : J ⥤ C) :
    indexNerve.{max u v} J ⟶ nerve C where
  app n := ↾fun x => (F.mapComposableArrows n.unop.len).obj x.down
  naturality n m f := by
    ext x
    rfl

/-- A zero spectrum map sends every original level simplex to the native basepoint. -/
def IsPointsetZeroMap {E F : SymmetricSpectrum} (f : E ⟶ F) : Prop :=
  ∀ (q : ℕ) (n : SimplexCategoryᵒᵖ) (x : (level E q).right.obj n),
    ((SymmetricSpectrum.evaluation q).map f).right.app n x = (level F q).point n

/-- The point-set zero is the original free-zero spectrum, also after localization. -/
structure SpectrumZeroSource (S : SpectrumInfinitySource) where
  terminal : IsTerminal zeroSpectrum
  source_zero : IsZeroObject S.category.toSSet (S.vertex zeroSpectrum)
  level_zero : ∀ E F : SymmetricSpectrum,
    IsPointsetZeroMap (terminal.from E ≫ initialSpectrumMap F)

/-- The actual terminal native map, without an opaque zero-morphism callback. -/
def toZeroSpectrum {S : SpectrumInfinitySource} (Z : SpectrumZeroSource S)
    (E : SymmetricSpectrum) : E ⟶ zeroSpectrum := Z.terminal.from E

/-- Its composite with the original free-spectrum initial map is the actual zero map. -/
def zeroMap {S : SpectrumInfinitySource} (Z : SpectrumZeroSource S)
    (E F : SymmetricSpectrum) : E ⟶ F := toZeroSpectrum Z E ≫ initialSpectrumMap F

/-- This is the literal native spectrum span, followed by the fixed localization. -/
def cofiberSpan (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S)
    {E F : SymmetricSpectrum} (f : E ⟶ F) : indexNerve.{1} WalkingSpan ⟶ S.category.toSSet :=
  liftedNerveMap (span f (toZeroSpectrum Z E)) ≫ S.source

/-- The apex functor evaluates every original parameter simplex and cone arrow. -/
def coconeApexMap {J : Type} [Category.{0} J] (C : SSet.{u})
    (d : indexNerve J ⟶ C) : rightCones C d ⟶ C :=
  pullback.fst (precomposition (indexMap (WithTerminal.incl (C := J))) C)
    (diagramPoint C d) ≫ evaluateAt (indexNerve (WithTerminal J)) C
      (ULift.up (ComposableArrows.mk₀ WithTerminal.star))

/-- A source cocone retains the whole native diagram and its actual spectrum apex. -/
structure SpectrumCocone (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S)
    {E F : SymmetricSpectrum} (f : E ⟶ F) where
  spectrum : SymmetricSpectrum
  cocone : (rightCones S.category.toSSet (cofiberSpan S Z f)) _⦋0⦌
  apex : (coconeApexMap S.category.toSSet (cofiberSpan S Z f)).app (op ⦋0⦌) cocone =
    S.vertex spectrum

/-- The derived cofiber is the actual universal cocone on this fixed span. -/
structure SpectrumCofiber (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S)
    {E F : SymmetricSpectrum} (f : E ⟶ F) extends SpectrumCocone S Z f where
  universal : IsInitialObject (rightCones S.category.toSSet (cofiberSpan S Z f)) cocone

/-- The entire cofiber cocone is extracted from the native restriction fibre. -/
def SpectrumCocone.diagram {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F : SymmetricSpectrum} {f : E ⟶ F} (P : SpectrumCocone S Z f) :
    indexNerve.{1} (WithTerminal WalkingSpan) ⟶ S.category.toSSet :=
  coconeDiagram S.category.toSSet (cofiberSpan S Z f) P.cocone

/-- The original native left-summand injection is the derived cofiber edge. -/
def SpectrumCofiber.inclusion {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F : SymmetricSpectrum} {f : E ⟶ F} (P : SpectrumCofiber S Z f) :
    S.category.toSSet _⦋1⦌ :=
  P.toSpectrumCocone.diagram.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (WithTerminal.homFrom WalkingSpan.left)).edge)

/-- A cofiber extension keeps the original full nullhomotopy in its cocone edge. -/
structure CofiberExtension {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F : SymmetricSpectrum} {f : E ⟶ F} (P : SpectrumCofiber S Z f)
    (Q : SpectrumCocone S Z f) where
  edge : (rightCones S.category.toSSet (cofiberSpan S Z f)) _⦋1⦌
  source : (rightCones S.category.toSSet (cofiberSpan S Z f)).δ 1 edge = P.cocone
  target : (rightCones S.category.toSSet (cofiberSpan S Z f)).δ 0 edge = Q.cocone

/-- The extension map is the actual apex of the same coherent cocone arrow. -/
def CofiberExtension.map {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F : SymmetricSpectrum} {f : E ⟶ F} {P : SpectrumCofiber S Z f}
    {Q : SpectrumCocone S Z f} (a : CofiberExtension P Q) : S.category.toSSet _⦋1⦌ :=
  (coconeApexMap S.category.toSSet (cofiberSpan S Z f)).app (op ⦋1⦌) a.edge

/-- The loop cospan is fixed by the two actual native initial spectrum maps. -/
def loopCospan (S : SpectrumInfinitySource) (G : SymmetricSpectrum) :
    indexNerve.{1} WalkingCospan ⟶ S.category.toSSet :=
  liftedNerveMap (cospan (initialSpectrumMap G) (initialSpectrumMap G)) ≫ S.source

/-- The native cone apex functor retains every coherent arrow. -/
def coneApexMap {J : Type} [Category.{0} J] (C : SSet.{u})
    (d : indexNerve J ⟶ C) : leftCones C d ⟶ C :=
  pullback.fst (precomposition (indexMap (WithInitial.incl (C := J))) C)
    (diagramPoint C d) ≫ evaluateAt (indexNerve (WithInitial J)) C
      (ULift.up (ComposableArrows.mk₀ WithInitial.star))

/-- Extract the original whole coherent cone from its native fibre vertex. -/
def coneDiagram {J : Type} [Category.{0} J] (C : SSet.{u})
    (d : indexNerve J ⟶ C) (c : (leftCones C d) _⦋0⦌) :
    indexNerve (WithInitial J) ⟶ C :=
  (mappingZero (indexNerve (WithInitial J)) C).symm
    ((pullback.fst (precomposition (indexMap (WithInitial.incl (C := J))) C)
      (diagramPoint C d)).app (op ⦋0⦌) c)

/-- Derived loops are normalized to the actual universal native zero cospan. -/
structure SpectrumLoop (S : SpectrumInfinitySource) (R : SpectrumReplacements S)
    (G : SymmetricSpectrum) where
  cone : (leftCones S.category.toSSet (loopCospan S G)) _⦋0⦌
  apex : (coneApexMap S.category.toSSet (loopCospan S G)).app (op ⦋0⦌) cone =
    S.vertex ((derivedLoopFunctor R).obj G)
  universal : IsTerminalObject (leftCones S.category.toSSet (loopCospan S G)) cone

/-- The map into native derived loops is an arrow of the same full cone category. -/
structure LoopConeMap {S : SpectrumInfinitySource} {R : SpectrumReplacements S}
    {G : SymmetricSpectrum} (L : SpectrumLoop S R G)
    (c : (leftCones S.category.toSSet (loopCospan S G)) _⦋0⦌) where
  edge : (leftCones S.category.toSSet (loopCospan S G)) _⦋1⦌
  source : (leftCones S.category.toSSet (loopCospan S G)).δ 1 edge = c
  target : (leftCones S.category.toSSet (loopCospan S G)).δ 0 edge = L.cone

/-- The loop map is evaluated on that same native cone arrow. -/
def LoopConeMap.map {S : SpectrumInfinitySource} {R : SpectrumReplacements S}
    {G : SymmetricSpectrum} {L : SpectrumLoop S R G}
    {c : (leftCones S.category.toSSet (loopCospan S G)) _⦋0⦌}
    (a : LoopConeMap L c) : S.category.toSSet _⦋1⦌ :=
  (coneApexMap S.category.toSSet (loopCospan S G)).app (op ⦋1⦌) a.edge

end MathlibExt.AlgebraicTopology.NativeSpectrumConeSources
