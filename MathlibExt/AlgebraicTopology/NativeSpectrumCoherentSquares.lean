/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectrumBoundarySources
public import MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource

/-!
# Source function homotopies in actual coherent spectrum squares

The top triangle of the whole square is normalized as a complete map
on the actual two-step rigid Hom. A path refinement is sent to zero or
one according to whether it includes the middle vertex. The resulting
map to Delta[1] pulls back the specified native function-spectrum
homotopy. This fixes all parameter simplices, not only the three edges.

The triangle through the zero corner is the ordinary two-simplex
`E ⟶ 0 ⟶ G`, whose two-cell is constant at the actual zero map. Otherwise it
could carry any based loop in `Map(E, G)` and change the boundary map.

Stable zero triangles are then the image of that entire coherent source
square under the fixed coherent stable localization.

Sources: Lurie, *Higher Topos Theory*, Section 1.1.5;
BGT1001.2282v4, Sections 7.1 and 9.1. The completed native rigid-path
and coherent-nerve source retains its Tau Ceti/Mathlib attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityFiniteDiagrams
open NativeSpectrumFunctionEvaluation NativeSpectraSimplicialSource
open NativeSpectrumConeSources NativeSpectrumBoundarySources
open StableSpectraInfinitySource NativeDerivedSpectrumModels
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The original rigid two-step index of the native coherent nerve. -/
abbrev RigidTwo := SimplicialThickening (ULift.{0} (Fin 3))

def rigidFirst : RigidTwo := ⟨ULift.up 0⟩
def rigidLast : RigidTwo := ⟨ULift.up 2⟩

/-- A refinement records exactly whether the actual middle source vertex is present. -/
def refinementStep (p : SimplicialThickening.Path rigidFirst.as rigidLast.as) : Fin 2 :=
  by
    classical
    exact if ULift.up (1 : Fin 3) ∈ p.I then 1 else 0

/-- Inclusion of actual source paths preserves this literal refinement coordinate. -/
theorem refinementStep_mono {p q : SimplicialThickening.Path rigidFirst.as rigidLast.as}
    (h : p.I ≤ q.I) : refinementStep p ≤ refinementStep q := by
  classical
  unfold refinementStep
  split_ifs with hp hq
  · exact le_rfl
  · exact False.elim (hq (h hp))
  · exact Fin.zero_le _
  · exact le_rfl

/-- The entire native rigid Hom maps to Delta[1] by the original path-refinement coordinate. -/
def refinementLine : (rigidFirst ⟶[SSet.{0}] rigidLast) ⟶ (Δ[1] : SSet.{0}) where
  app n := ↾fun c => SSet.stdSimplex.objMk
    { toFun := fun i => refinementStep (c.obj i)
      monotone' := fun i j h => refinementStep_mono ((c.map (homOfLE h)).hom.le) }
  naturality n m f := by
    ext c
    rfl

/-- The actual top source chain is the horizontal two-arrow composite. -/
def topSourceChain : (indexNerve.{1} SquareCorner) _⦋2⦌ :=
  ULift.up (ComposableArrows.mk₂ (homOfLE (originLE .horizontal))
    (homOfLE (finalLE .horizontal)))

/-- The actual zero source chain is the vertical two-arrow composite through the zero corner. -/
def zeroSourceChain : (indexNerve.{1} SquareCorner) _⦋2⦌ :=
  ULift.up (ComposableArrows.mk₂ (homOfLE (originLE .vertical))
    (homOfLE (finalLE .vertical)))

/-- The actual coherent source vertex of the specified native spectrum. -/
def coherentVertex (N : SpectrumSimplicialEnrichment) (E : SymmetricSpectrum) :
    (spectrumCoherentNerve N) _⦋0⦌ :=
  (spectrumOrdinaryToCoherent N).app (op ⦋0⦌) (ComposableArrows.mk₀ E)

/-- The complete top triangle is the original square evaluated on its two-arrow source chain. -/
def topTriangle (N : SpectrumSimplicialEnrichment)
    (d : indexNerve.{1} SquareCorner ⟶ spectrumCoherentNerve N) :
    (spectrumCoherentNerve N) _⦋2⦌ := d.app (op ⦋2⦌) topSourceChain

def topFirst (N : SpectrumSimplicialEnrichment)
    (d : indexNerve.{1} SquareCorner ⟶ spectrumCoherentNerve N) : SymmetricSpectrum :=
  letI := N.ordinary
  (topTriangle N d).obj rigidFirst

def topLast (N : SpectrumSimplicialEnrichment)
    (d : indexNerve.{1} SquareCorner ⟶ spectrumCoherentNerve N) : SymmetricSpectrum :=
  letI := N.ordinary
  (topTriangle N d).obj rigidLast

/-- The original entire enriched two-step Hom, transported to the actual native function space. -/
def topFunctionMap (N : SpectrumSimplicialEnrichment)
    (d : indexNerve.{1} SquareCorner ⟶ spectrumCoherentNerve N) :
    (rigidFirst ⟶[SSet.{0}] rigidLast) ⟶ nativeFunctionSpace (topFirst N d) (topLast N d) :=
  letI := N.ordinary
  (topTriangle N d).map rigidFirst rigidLast ≫
    eqToHom (N.hom_normalization (topFirst N d) (topLast N d))

/-- The actual native point-set map determines its source function-space vertex. -/
def functionVertex (N : SpectrumSimplicialEnrichment)
    {E F : SymmetricSpectrum} (f : E ⟶ F) : (nativeFunctionSpace E F) _⦋0⦌ :=
  letI := N.ordinary
  SSet.unitHomEquiv _ (eHomEquiv SSet.{0} f ≫ eqToHom (N.hom_normalization E F))

/-- The actual coherent zero square retains the entire prescribed function homotopy. -/
structure CoherentZeroSquare (N : SpectrumSimplicialEnrichment)
    (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S)
    {E F G : SymmetricSpectrum} (f : E ⟶ F) (g : F ⟶ G)
    (t : (nativeFunctionSpace E G) _⦋1⦌) where
  diagram : indexNerve.{1} SquareCorner ⟶ spectrumCoherentNerve N
  span_normalization : indexMap spanSquareIndex ≫ diagram =
    liftedNerveMap (span f (toZeroSpectrum Z E)) ≫ spectrumOrdinaryToCoherent N
  final : cornerValue diagram .final = coherentVertex N G
  second_map : diagram.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (finalLE .horizontal))).edge) = spectrumCoherentEdge N g
  zero_map : diagram.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (finalLE .vertical))).edge) =
      spectrumCoherentEdge N (initialSpectrumMap G)
  /-- The triangle through the zero corner is the ordinary composable pair
  `E ⟶ 0 ⟶ G`: its diagonal is the actual zero map and its two-cell is constant,
  so it carries no loop in `Map(E, G)` and the null-homotopy of the composite is
  exactly the prescribed `t`. -/
  zero_triangle : diagram.app (op ⦋2⦌) zeroSourceChain =
    (spectrumOrdinaryToCoherent N).app (op ⦋2⦌)
      (ComposableArrows.mk₂ (toZeroSpectrum Z E) (initialSpectrumMap G))
  top_first : topFirst N diagram = E
  top_last : topLast N diagram = G
  whole_homotopy : topFunctionMap N diagram ≫
      eqToHom (congrArg₂ nativeFunctionSpace top_first top_last) =
    refinementLine ≫ (SSet.yonedaEquiv (X := nativeFunctionSpace E G)).symm t

/-- Native coherent localization sends the same source vertex to the original stable source vertex. -/
theorem coherentVertex_image {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource}
    (L : SpectrumCoherentLocalization N S) (E : SymmetricSpectrum) :
    L.map.app (op ⦋0⦌) (coherentVertex N E) = S.vertex E := by
  have h := congrArg (fun a => a.app (op ⦋0⦌) (ComposableArrows.mk₀ E)) L.ordinary_normalization
  exact h

/-- Native coherent localization sends every original spectrum map to its original stable edge. -/
theorem coherentEdge_image {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource}
    (L : SpectrumCoherentLocalization N S) {E F : SymmetricSpectrum} (f : E ⟶ F) :
    L.map.app (op ⦋1⦌) (spectrumCoherentEdge N f) = S.edge f := by
  have h := congrArg (fun a => a.app (op ⦋1⦌) (nerve.edgeMk f).edge) L.ordinary_normalization
  exact h

/-- The stable triangle is defined by the image of the entire source-normalized coherent square. -/
def CoherentZeroSquare.stableTriangle {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F G : SymmetricSpectrum} {f : E ⟶ F} {g : F ⟶ G}
    {t : (nativeFunctionSpace E G) _⦋1⦌} (Q : CoherentZeroSquare N S Z f g t)
    (L : SpectrumCoherentLocalization N S) : SpectrumZeroTriangle S Z f g where
  square := Q.diagram ≫ L.map
  span_normalization := by
    rw [← Category.assoc, Q.span_normalization, Category.assoc, L.ordinary_normalization]
    rfl
  final := by
    change L.map.app (op ⦋0⦌) (cornerValue Q.diagram .final) = _
    rw [Q.final, coherentVertex_image]
  second_map := by
    exact (congrArg (fun x => L.map.app (op ⦋1⦌) x) Q.second_map).trans
      (coherentEdge_image L g)
  zero_map := by
    exact (congrArg (fun x => L.map.app (op ⦋1⦌) x) Q.zero_map).trans
      (coherentEdge_image L (initialSpectrumMap G))

end MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares
