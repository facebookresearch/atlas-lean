/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentRootTriangleCompositionCell

/-!
# Cancellation marking on the same two original root triangles

The entire original root coefficient and its inherited marks are kept.
The source additionally marks the original direct and middle edges;
the target additionally marks the original first edge. The original
second triangle composes the direct edge with the constant-maximum
edge. The original first triangle then cancels the middle edge. Both
triangles tensor with the same whole original marked parameter edge,
so the actual maximal mapping restriction is an isomorphism.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original full root coefficient marks its direct and middle edges and retains every inherited mark. -/
def rootTriangleCancellationSource : Marked.{u} where
  toSSet := (coneWeight rootTriangleZero).toSSet
  marking := (coneWeight rootTriangleZero).marking ∪
    {(nerve.edgeMk rootTriangleDirect).edge, (nerve.edgeMk rootTriangleMiddle).edge}
  degenerate_mem x := Or.inl ((coneWeight rootTriangleZero).degenerate_mem x)

/-- The same full original coefficient additionally marks its first edge. -/
def rootTriangleCancellationTarget : Marked.{u} where
  toSSet := (coneWeight rootTriangleZero).toSSet
  marking := rootTriangleCancellationSource.marking ∪ {(nerve.edgeMk rootTriangleFirst).edge}
  degenerate_mem x := Or.inl (rootTriangleCancellationSource.degenerate_mem x)

/-- The cancellation marking cell keeps the original identity on all simplices. -/
def rootTriangleCancellationCell : rootTriangleCancellationSource.{u} ⟶ rootTriangleCancellationTarget where
  hom := 𝟙 _
  preserve he := Or.inl he

/-- The original direct edge is marked in the source. -/
theorem rootTriangleCancellation_direct_marked :
    (nerve.edgeMk rootTriangleDirect.{u}).edge ∈ rootTriangleCancellationSource.marking := Or.inr (Or.inl rfl)

/-- The original middle edge is marked in the source. -/
theorem rootTriangleCancellation_middle_marked :
    (nerve.edgeMk rootTriangleMiddle.{u}).edge ∈ rootTriangleCancellationSource.marking := Or.inr (Or.inr rfl)

/-- The unchanged constant-maximum edge remains marked in the source. -/
theorem rootTriangleCancellation_constant_marked :
    (nerve.edgeMk rootTriangleConstant.{u}).edge ∈ rootTriangleCancellationSource.marking :=
  Or.inl rootTriangle_constant_marked

/-- The original first edge is marked in the target. -/
theorem rootTriangleCancellation_first_marked :
    (nerve.edgeMk rootTriangleFirst.{u}).edge ∈ rootTriangleCancellationTarget.marking := Or.inr rfl

/-- The same original coefficient identity is a mono. -/
theorem rootTriangleCancellationCell_mono : Mono rootTriangleCancellationCell.{u} := by
  let _ : Mono rootTriangleCancellationCell.{u}.hom := inferInstanceAs (Mono (𝟙 _))
  exact Hom.mono_of_underlying _

/-- The original second triangle composes and the original first triangle cancels, with the same full marked
parameter edge. -/
theorem rootTriangleCancellation_mixed_cartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P rootTriangleCancellationSource.{u} ⟶ cartesian p)
    (a : P.toSSet _⦋1⦌) (ha : a ∈ P.marking) :
    CartesianEdge.IsPCartesian p (yonedaEquiv.symm
      (f.hom.app (op ⦋1⦌) (a, (nerve.edgeMk rootTriangleFirst.{u}).edge))) := by
  let F : P.toSSet ⊗ (coneWeight rootTriangleZero.{u}).toSSet ⟶ E := f.hom
  let e := Edge.mk' a
  let d := (e.tensor (nerve.edgeMk rootTriangleDirect.{u})).map F
  let c := ((Edge.id (P.toSSet.δ 0 a)).tensor (nerve.edgeMk rootTriangleConstant.{u})).map F
  let z := (e.tensor (nerve.edgeMk rootTriangleFull.{u})).map F
  have hd : CartesianEdge.IsPCartesian p (yonedaEquiv.symm d.edge) :=
    @f.preserve (a, (nerve.edgeMk rootTriangleDirect.{u}).edge) ⟨ha, rootTriangleCancellation_direct_marked⟩
  have hc : CartesianEdge.IsPCartesian p (yonedaEquiv.symm c.edge) :=
    @f.preserve (P.toSSet.σ (0 : Fin 1) (P.toSSet.δ 0 a), (nerve.edgeMk rootTriangleConstant.{u}).edge)
      ⟨P.degenerate_mem _, rootTriangleCancellation_constant_marked⟩
  let T : Edge.CompStruct d c z := ((Edge.CompStruct.compId e).tensor rootTriangleSecondComp).map F
  have hz := CartesianEdge.isPCartesian_of_compStruct p T hd hc
  let v := (e.tensor (nerve.edgeMk rootTriangleFirst.{u})).map F
  let w := ((Edge.id (P.toSSet.δ 0 a)).tensor (nerve.edgeMk rootTriangleMiddle.{u})).map F
  have hw : CartesianEdge.IsPCartesian p (yonedaEquiv.symm w.edge) :=
    @f.preserve (P.toSSet.σ (0 : Fin 1) (P.toSSet.δ 0 a), (nerve.edgeMk rootTriangleMiddle.{u}).edge)
      ⟨P.degenerate_mem _, rootTriangleCancellation_middle_marked⟩
  let U : Edge.CompStruct v w z := ((Edge.CompStruct.compId e).tensor rootTriangleFirstComp).map F
  exact (CartesianEdge.isPCartesian_iff_of_compStruct p U hw).mpr hz

/-- The original full marked prism extends its first-edge mark by the same underlying map. -/
def extendRootTriangleCancellationCartesian {P : Marked.{u}} {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (f : prod P rootTriangleCancellationSource.{u} ⟶ cartesian p) :
    prod P rootTriangleCancellationTarget.{u} ⟶ cartesian p where
  hom := f.hom
  preserve {e} he := by
    rcases he.2 with hs | hf
    · exact @f.preserve e ⟨he.1, hs⟩
    · change CartesianEdge.IsPCartesian p (yonedaEquiv.symm (f.hom.app (op ⦋1⦌) (e.1, e.2)))
      rw [show e.2 = (nerve.edgeMk rootTriangleFirst.{u}).edge from hf]
      exact rootTriangleCancellation_mixed_cartesian p f e.1 he.1

/-- The actual original maximal mapping restriction across the cancellation root cell is a whole simplicial
isomorphism. -/
def rootTriangleCancellationCartesianMappingIso {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    mappingComplex .maximal rootTriangleCancellationTarget.{u} (cartesian p) ≅
      mappingComplex .maximal rootTriangleCancellationSource.{u} (cartesian p) where
  hom := mappingComplexPre .maximal rootTriangleCancellationCell.{u} (cartesian p)
  inv :=
    { app n := ↾fun f => extendRootTriangleCancellationCartesian p f
      naturality n m a := by ext f; apply Hom.ext; rfl }
  hom_inv_id := by ext n f; apply Hom.ext; ext q a; rfl
  inv_hom_id := by ext n f; apply Hom.ext; ext q a; rfl

end SSet.Marked.CoherentWeight
