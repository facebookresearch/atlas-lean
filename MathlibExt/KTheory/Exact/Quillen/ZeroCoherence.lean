/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso
public import MathlibExt.KTheory.Exact.Quillen.Nerve
public import MathlibExt.KTheory.Exact.Quillen.NQConnected
public import MathlibExt.KTheory.Exact.Quillen.Realization
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
import MathlibExt.Topology.Homotopy.TopCat.Path

/-!
# Zero comparison in the Quillen Q-construction

For an additive exact functor `F : C ⥤ D`, compare the image of the selected
zero object with the selected zero object in the target via the lift of
`F.mapZeroObject`:

`QuillenQ.zeroComparisonIso F : (QuillenQ.map F).obj ⟨0⟩ ≅ ⟨0⟩`.

Orientation: from the mapped zero object to the target chosen zero object,
through the underlying-iso lift with apex `F.obj 0`. The simplicial edge
`NQ.zeroComparisonEdge F` in `NQ D` is built with
`CategoryTheory.nerve.edgeMk`, with source the mapped `NQ.zeroVertex C`
and target `NQ.zeroVertex D`.

Realized basepoint bridge: `NQReal.basepoint C` equals the realized zero
vertex, and `NQReal.map F (NQReal.basepoint C)` equals the realized mapped
vertex via `realizedVertex_naturality`. Transporting the realized comparison
edge yields the mapped-to-target path `NQReal.zeroComparisonPath F :
(NQReal D).Path (NQReal.map F (NQReal.basepoint C)) (NQReal.basepoint D)`.

Nonclaims: no strict pointed functoriality (no strict equality of mapped and
selected basepoints, only the comparison path); no general realized
homotopies, loops, or groups; no zero object on `QuillenQ`; natural-isomorphism
coherence of the comparison iso proved, but no nerve-edge or realized-path
naturality; no proved path-level identity/concatenation
coherence; no parallel simplex representation.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- Comparison iso from the mapped zero object to the target zero object,
as the lift of `F.mapZeroObject`. -/
noncomputable def QuillenQ.zeroComparisonIso {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type u₂} [Category.{v₂} D]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (QuillenQ.map F).obj ⟨0⟩ ≅ (⟨0⟩ : QuillenQ D) :=
  QuillenQ.underlyingIso F.mapZeroObject

/-- Simplicial edge in `NQ D` from the mapped zero vertex to the target
zero vertex, via `nerve.edgeMk`. -/
noncomputable def NQ.zeroComparisonEdge (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQ D).Edge ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C)) (NQ.zeroVertex D) :=
  SSet.Edge.ofEq (CategoryTheory.nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom)
    (by simp [NQ.zeroVertex, NQ.map_app_mk₀]; rfl)
    (by simp [NQ.zeroVertex]; rfl)

/-- Edge formula for the zero comparison edge. -/
@[simp]
theorem NQ.zeroComparisonEdge_edge (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQ.zeroComparisonEdge F).edge =
      ComposableArrows.mk₁ (QuillenQ.zeroComparisonIso F).hom :=
  rfl

/-- Mapped-zero vertex as the image of the zero vertex. -/
@[simp]
theorem NQ.map_zeroVertex (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C) =
      ComposableArrows.mk₀ ((QuillenQ.map F).obj ⟨0⟩) := by
  simp [NQ.zeroVertex, NQ.map_app_mk₀]; rfl

/-- Source of the zero comparison edge. -/
theorem NQ.zeroComparisonEdge_src (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQ D).δ 1 (NQ.zeroComparisonEdge F).edge =
      (NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C) :=
  SSet.Edge.src_eq _

/-- Target of the zero comparison edge. -/
theorem NQ.zeroComparisonEdge_tgt (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQ D).δ 0 (NQ.zeroComparisonEdge F).edge = NQ.zeroVertex D :=
  SSet.Edge.tgt_eq _

/-- Realized basepoint equals the realized zero vertex, via `realizedVertex_eq_const`. -/
@[simp]
theorem NQReal.basepoint_eq_realizedVertex (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    NQReal.basepoint C = SSet.realizedVertex (NQ.zeroVertex C) := by
  simpa [NQReal.basepoint, NQ.zeroVertexInclusion] using
    (SSet.realizedVertex_eq_const (NQ.zeroVertex C)).symm

/-- Mapped basepoint equals the realized mapped vertex, via basepoint bridge and
`realizedVertex_naturality`. -/
theorem NQReal.map_basepoint_eq_realizedVertex (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQReal.map F (NQReal.basepoint C) =
      SSet.realizedVertex ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C)) := by
  simp [NQReal.map, NQReal.basepoint_eq_realizedVertex,
    ← SSet.realizedVertex_naturality]

/-- Realized zero-comparison path from the mapped basepoint to the target basepoint,
by transporting the realized comparison edge. -/
noncomputable def NQReal.zeroComparisonPath (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQReal D).Path (NQReal.map F (NQReal.basepoint C)) (NQReal.basepoint D) :=
  TopCat.Path.cast (SSet.realizedEdgePath (NQ.zeroComparisonEdge F))
    (NQReal.map_basepoint_eq_realizedVertex F)
    (NQReal.basepoint_eq_realizedVertex D)

/-- Realized zero-to-vertex path from the basepoint to the realized `X` vertex,
by transporting the realized zero-to-vertex edge. -/
noncomputable def NQReal.zeroToVertexPath (X : C) :
    (NQReal C).Path (NQReal.basepoint C)
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨X⟩ : QuillenQ C))) :=
  TopCat.Path.cast (SSet.realizedEdgePath (NQ.zeroToVertexEdge X))
    (NQReal.basepoint_eq_realizedVertex C) rfl

/-- Realized vertex-to-vertex path from the realized `X` vertex to the realized
`Y` vertex, by reversing `NQReal.zeroToVertexPath X` and composing with
`NQReal.zeroToVertexPath Y` through `TopCat.pathEquiv`.

This is vertex-level path data only, not path-connectedness of every
realization point. -/
noncomputable def NQReal.vertexPath (X Y : C) :
    (NQReal C).Path
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨X⟩ : QuillenQ C)))
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨Y⟩ : QuillenQ C))) :=
  TopCat.pathEquiv.symm
    ((TopCat.pathEquiv (NQReal.zeroToVertexPath X)).symm.trans
      (TopCat.pathEquiv (NQReal.zeroToVertexPath Y)))

variable {E : Type u} [Category.{v} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Identity coherence for the zero comparison iso: over the identity functor,
the comparison is the identity isomorphism. -/
@[simp]
theorem QuillenQ.zeroComparisonIso_id :
    QuillenQ.zeroComparisonIso (𝟭 C) = Iso.refl (⟨0⟩ : QuillenQ C) := by
  have hmap : (𝟭 C).mapZeroObject = Iso.refl (0 : C) := by
    apply Iso.ext
    exact HasZeroObject.to_zero_ext _ _
  unfold QuillenQ.zeroComparisonIso
  rw [hmap]
  exact QuillenQ.underlyingIso_refl 0

/-- Composition coherence for the zero comparison iso: the comparison over a
composite is the mapped comparison followed by the target comparison. -/
theorem QuillenQ.zeroComparisonIso_comp {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type u₂} [Category.{v₂} D]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {E : Type u₃} [Category.{v₃} E]
    [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.IsExact] [G.IsExact] :
    QuillenQ.zeroComparisonIso (F ⋙ G) =
      ((QuillenQ.map G).mapIso (QuillenQ.zeroComparisonIso F)).trans
        (QuillenQ.zeroComparisonIso G) := by
  have hmap : (F ⋙ G).mapZeroObject =
      (G.mapIso (F.mapZeroObject)).trans (G.mapZeroObject) := by
    apply Iso.ext
    exact HasZeroObject.to_zero_ext _ _
  unfold QuillenQ.zeroComparisonIso
  rw [hmap, QuillenQ.underlyingIso_trans, ← QuillenQ.underlyingIso_map]; rfl

/-- Naturality coherence for the zero comparison iso: transporting along a
natural isomorphism and then comparing equals comparing directly. -/
theorem QuillenQ.zeroComparisonIso_naturality {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type u₂} [Category.{v₂} D]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    ((QuillenQ.mapNatIso F G e).app (⟨0⟩ : QuillenQ C)).trans
      (QuillenQ.zeroComparisonIso G) = QuillenQ.zeroComparisonIso F := by
  have huniq : (e.app 0).trans (G.mapZeroObject) = F.mapZeroObject := by
    apply Iso.ext
    exact HasZeroObject.to_zero_ext _ _
  change (QuillenQ.underlyingIso (e.app 0)).trans
      (QuillenQ.underlyingIso G.mapZeroObject)
    = QuillenQ.underlyingIso F.mapZeroObject
  rw [← QuillenQ.underlyingIso_trans, huniq]

end AlgebraicKTheory
