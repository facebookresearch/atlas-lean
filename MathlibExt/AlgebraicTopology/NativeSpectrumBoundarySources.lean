/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectrumConeSources

/-!
# The boundary of the original coherent spectrum square

A zero-middle boundary first replaces the middle object in the entire
original square by the native zero object. The replacement is an actual
natural equivalence of full square diagrams, identity on the other
three corners. The resulting cone over `0 → G ← 0` maps to the native
terminal loop cone. Its apex arrow is the boundary.

This retains the original commutation homotopy, including all higher
parameter simplices. An arbitrary map to loops cannot satisfy the
normalization by substituting a different nullhomotopy.

Sources: Schlichting, *Negative K-theory of derived categories*, Section 12;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Definition 9.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumBoundarySources

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityFilteredColimits
open NativeDiagramFamilies NativeSpectrumConeSources
open StableSpectraInfinitySource NativeDerivedSpectrumModels
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The coordinate-origin is below every actual square corner. -/
theorem originLE (p : SquareCorner) : SquareCorner.origin ≤ p := by
  change (0 : Fin 2) ≤ p.coordinate.1 ∧ (0 : Fin 2) ≤ p.coordinate.2
  exact ⟨Fin.zero_le _, Fin.zero_le _⟩

/-- Every actual corner is below the coordinate-final corner. -/
theorem finalLE (p : SquareCorner) : p ≤ SquareCorner.final := by
  change p.coordinate.1 ≤ (1 : Fin 2) ∧ p.coordinate.2 ≤ (1 : Fin 2)
  exact ⟨Fin.le_last _, Fin.le_last _⟩

/-- The original three span vertices are the lower punctured square. -/
def spanSquareIndex : WalkingSpan ⥤ SquareCorner :=
  span (homOfLE (originLE .horizontal)) (homOfLE (originLE .vertical))

/-- The original cospan vertices are the upper punctured square. -/
def cospanSquareIndex : WalkingCospan ⥤ SquareCorner :=
  cospan (homOfLE (finalLE .horizontal)) (homOfLE (finalLE .vertical))

/-- Adjoin the original lower-left corner to the actual native cospan. -/
def coneSquareIndex : WithInitial WalkingCospan ⥤ SquareCorner :=
  WithInitial.lift (Z := SquareCorner.origin) cospanSquareIndex
    (fun p => homOfLE (originLE (cospanSquareIndex.obj p))) (by
      intro x y f
      apply Subsingleton.elim)

/-- Evaluation of every coherent parameter arrow at the specified original corner. -/
def squareCornerEvaluation (C : SSet.{1}) (p : SquareCorner) :
    mapping (indexNerve SquareCorner) C ⟶ C :=
  evaluateAt _ C (ULift.up (ComposableArrows.mk₀ p))

/-- A nullhomotopy square retains the original native maps and zero side. -/
structure SpectrumZeroTriangle (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S)
    {E F G : SymmetricSpectrum} (f : E ⟶ F) (g : F ⟶ G) where
  square : indexNerve.{1} SquareCorner ⟶ S.category.toSSet
  span_normalization : indexMap spanSquareIndex ≫ square = cofiberSpan S Z f
  final : cornerValue square .final = S.vertex G
  second_map : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk
      (homOfLE (finalLE .horizontal))).edge) = S.edge g
  zero_map : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk
      (homOfLE (finalLE .vertical))).edge) =
        S.edge (initialSpectrumMap G)

/-- The actual equivalence which contracts this particular middle spectrum. -/
structure MiddleZeroEquivalence (S : SpectrumInfinitySource) (F : SymmetricSpectrum) where
  edge : S.category.toSSet _⦋1⦌
  source : S.category.toSSet.δ 1 edge = S.vertex F
  target : S.category.toSSet.δ 0 edge = S.vertex zeroSpectrum
  equivalence : IsEquivalenceEdge S.category.toSSet edge

/-- Replacing the entire original square retains its precise nullhomotopy. -/
structure ZeroSquareReduction {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F G : SymmetricSpectrum} {f : E ⟶ F} {g : F ⟶ G}
    (Q : SpectrumZeroTriangle S Z f g) (h : MiddleZeroEquivalence S F) where
  reduced_square : indexNerve.{1} SquareCorner ⟶ S.category.toSSet
  cone : (leftCones S.category.toSSet (loopCospan S G)) _⦋0⦌
  cone_normalization : indexMap coneSquareIndex ≫ reduced_square =
    coneDiagram S.category.toSSet (loopCospan S G) cone
  cone_apex : (coneApexMap S.category.toSSet (loopCospan S G)).app (op ⦋0⦌) cone = S.vertex E
  replacement : (mapping (indexNerve SquareCorner) S.category.toSSet) _⦋1⦌
  replacement_equivalence : IsEquivalenceEdge _ replacement
  replacement_source : (mapping (indexNerve SquareCorner) S.category.toSSet).δ 1 replacement =
    mappingZero _ _ Q.square
  replacement_target : (mapping (indexNerve SquareCorner) S.category.toSSet).δ 0 replacement =
    mappingZero _ _ reduced_square
  middle : (squareCornerEvaluation S.category.toSSet .horizontal).app (op ⦋1⦌) replacement = h.edge
  fixed_corners : ∀ p : SquareCorner, p ≠ .horizontal →
    (squareCornerEvaluation S.category.toSSet p).app (op ⦋1⦌) replacement =
      S.category.toSSet.σ 0 (cornerValue Q.square p)

/-- The source boundary is the universal map of the normalized reduced loop cone. -/
structure SpectrumBoundary {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {R : SpectrumReplacements S} {E F G : SymmetricSpectrum}
    {f : E ⟶ F} {g : F ⟶ G} (Q : SpectrumZeroTriangle S Z f g)
    (L : SpectrumLoop S R G) where
  contraction : MiddleZeroEquivalence S F
  reduction : ZeroSquareReduction Q contraction
  map : LoopConeMap L reduction.cone

/-- The boundary arrow is fixed by the original square and the native terminal cone. -/
def SpectrumBoundary.edge {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {R : SpectrumReplacements S} {E F G : SymmetricSpectrum}
    {f : E ⟶ F} {g : F ⟶ G} {Q : SpectrumZeroTriangle S Z f g}
    {L : SpectrumLoop S R G} (B : SpectrumBoundary Q L) : S.category.toSSet _⦋1⦌ := B.map.map

/-- An elementary homotopy is relative to the same target and actual identity edge. -/
def SameArrow (C : SSet.{1}) (e f : C _⦋1⦌) : Prop :=
  ∃ t : C _⦋2⦌, C.δ 2 t = e ∧ C.δ 0 t = C.σ 0 (C.δ 0 e) ∧ C.δ 1 t = f

/-- A strict native representative is compared to that same source boundary arrow. -/
structure PointsetBoundary {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {R : SpectrumReplacements S} {E F G : SymmetricSpectrum}
    {f : E ⟶ F} {g : F ⟶ G} {Q : SpectrumZeroTriangle S Z f g}
    {L : SpectrumLoop S R G} (B : SpectrumBoundary Q L) where
  map : E ⟶ (derivedLoopFunctor R).obj G
  normalization : SameArrow S.category.toSSet B.edge (S.edge map)

end MathlibExt.AlgebraicTopology.NativeSpectrumBoundarySources
