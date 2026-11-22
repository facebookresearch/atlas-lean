/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCompositionTriangles
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPrismCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAdjunction

/-!
# The original two-root-triangle composition marking cell

The entire original root coefficient of the two-simplex is retained.
Its source additionally marks the original first and middle edges;
its target additionally marks the original direct edge. The original
constant-maximum edge stays marked throughout. The two original
triangles, tensored with the whole marked parameter edge, prove the
actual Cartesian mapping restriction is an isomorphism by composition
and cancellation. No weak image or native filler is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The same full original root coefficient, with its first and middle edges marked in addition to all inherited
marks. -/
def rootTriangleCompositionSource : Marked.{u} where
  toSSet := (coneWeight rootTriangleZero).toSSet
  marking := (coneWeight rootTriangleZero).marking ∪
    {(nerve.edgeMk rootTriangleFirst).edge, (nerve.edgeMk rootTriangleMiddle).edge}
  degenerate_mem x := Or.inl ((coneWeight rootTriangleZero).degenerate_mem x)

/-- The same full original root coefficient additionally marks its original direct edge. -/
def rootTriangleCompositionTarget : Marked.{u} where
  toSSet := (coneWeight rootTriangleZero).toSSet
  marking := rootTriangleCompositionSource.marking ∪ {(nerve.edgeMk rootTriangleDirect).edge}
  degenerate_mem x := Or.inl (rootTriangleCompositionSource.degenerate_mem x)

/-- The original root marking cell is literally the identity on every original simplex. -/
def rootTriangleCompositionCell : rootTriangleCompositionSource.{u} ⟶ rootTriangleCompositionTarget where
  hom := 𝟙 _
  preserve he := Or.inl he

/-- The original first edge is marked in the source. -/
theorem rootTriangleComposition_first_marked :
    (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ rootTriangleCompositionSource.marking := Or.inr (Or.inl rfl)

/-- The original middle edge is marked in the source. -/
theorem rootTriangleComposition_middle_marked :
    (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈ rootTriangleCompositionSource.marking := Or.inr (Or.inr rfl)

/-- The original constant-maximum edge remains marked in the source. -/
theorem rootTriangleComposition_constant_marked :
    (nerve.edgeMk rootTriangleConstant.{u}).edge ∈ rootTriangleCompositionSource.marking :=
  Or.inl rootTriangle_constant_marked

/-- The original direct edge is marked in the target. -/
theorem rootTriangleComposition_direct_marked :
    (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ rootTriangleCompositionTarget.marking := Or.inr rfl

/-- Enlarging these marks retains the same original coefficient identity and is a mono. -/
theorem rootTriangleCompositionCell_mono : Mono rootTriangleCompositionCell.{u} := by
  let _ : Mono rootTriangleCompositionCell.{u}.hom := inferInstanceAs (Mono (𝟙 _))
  exact Hom.mono_of_underlying _

/-- Both original triangles tensor with the entire original marked parameter edge; composition and cancellation mark
the same mixed direct edge. -/
theorem rootTriangleComposition_mixed_cartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P rootTriangleCompositionSource.{u} ⟶ cartesian p)
    (a : P.toSSet _⦋1⦌) (ha : a ∈ P.marking) :
    CartesianEdge.IsPCartesian p (yonedaEquiv.symm
      (f.hom.app (op ⦋1⦌) (a, (nerve.edgeMk rootTriangleDirect.{u}).edge))) := by
  let F : P.toSSet ⊗ (coneWeight rootTriangleZero.{u}).toSSet ⟶ E := f.hom
  let e := Edge.mk' a
  let v := (e.tensor (nerve.edgeMk rootTriangleFirst.{u})).map F
  let w := ((Edge.id (P.toSSet.δ 0 a)).tensor (nerve.edgeMk rootTriangleMiddle.{u})).map F
  let z := (e.tensor (nerve.edgeMk rootTriangleFull.{u})).map F
  have hv : CartesianEdge.IsPCartesian p (yonedaEquiv.symm v.edge) :=
    @f.preserve (a, (nerve.edgeMk rootTriangleFirst.{u}).edge) ⟨ha, rootTriangleComposition_first_marked⟩
  have hw : CartesianEdge.IsPCartesian p (yonedaEquiv.symm w.edge) :=
    @f.preserve (P.toSSet.σ (0 : Fin 1) (P.toSSet.δ 0 a), (nerve.edgeMk rootTriangleMiddle.{u}).edge)
      ⟨P.degenerate_mem _, rootTriangleComposition_middle_marked⟩
  let T : Edge.CompStruct v w z := ((Edge.CompStruct.compId e).tensor rootTriangleFirstComp).map F
  have hz := CartesianEdge.isPCartesian_of_compStruct p T hv hw
  let d := (e.tensor (nerve.edgeMk rootTriangleDirect.{u})).map F
  let c := ((Edge.id (P.toSSet.δ 0 a)).tensor (nerve.edgeMk rootTriangleConstant.{u})).map F
  have hc : CartesianEdge.IsPCartesian p (yonedaEquiv.symm c.edge) :=
    @f.preserve (P.toSSet.σ (0 : Fin 1) (P.toSSet.δ 0 a), (nerve.edgeMk rootTriangleConstant.{u}).edge)
      ⟨P.degenerate_mem _, rootTriangleComposition_constant_marked⟩
  let U : Edge.CompStruct d c z := ((Edge.CompStruct.compId e).tensor rootTriangleSecondComp).map F
  exact (CartesianEdge.isPCartesian_iff_of_compStruct p U hc).mpr hz

/-- The full original marked prism extends the root direct-edge marking without changing any original simplex. -/
def extendRootTriangleCompositionCartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P rootTriangleCompositionSource.{u} ⟶ cartesian p) :
    prod P rootTriangleCompositionTarget.{u} ⟶ cartesian p where
  hom := f.hom
  preserve {e} he := by
    rcases he.2 with hs | hd
    · exact @f.preserve e ⟨he.1, hs⟩
    · change CartesianEdge.IsPCartesian p (yonedaEquiv.symm (f.hom.app (op ⦋1⦌) (e.1, e.2)))
      rw [show e.2 = (nerve.edgeMk rootTriangleDirect.{u}).edge from hd]
      exact rootTriangleComposition_mixed_cartesian p f e.1 he.1

/-- The same original whole root marking restriction is an actual maximal mapping-complex isomorphism. -/
def rootTriangleCompositionCartesianMappingIso {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    mappingComplex .maximal rootTriangleCompositionTarget.{u} (cartesian p) ≅
      mappingComplex .maximal rootTriangleCompositionSource.{u} (cartesian p) where
  hom := mappingComplexPre .maximal rootTriangleCompositionCell.{u} (cartesian p)
  inv :=
    { app n := ↾fun f => extendRootTriangleCompositionCartesian p f
      naturality n m a := by ext f; apply Hom.ext; rfl }
  hom_inv_id := by ext n f; apply Hom.ext; ext q a; rfl
  inv_hom_id := by ext n f; apply Hom.ext; ext q a; rfl

end SSet.Marked.CoherentWeight
