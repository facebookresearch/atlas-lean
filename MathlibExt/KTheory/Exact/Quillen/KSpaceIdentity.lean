/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import MathlibExt.Topology.Homotopy.PathConjugationHomotopic
import MathlibExt.Topology.Homotopy.TopCat.Path

/-!
# Identity homotopy for Quillen Q loop-space maps

For an exact category `C`, the loop-space map induced by the identity exact
functor is pointwise endpoint-fixed homotopic to the identity. The proof does
not assume that the identity zero-comparison root path is reflexive. Instead,
it identifies the underlying comparison edge with the degenerate zero edge,
realizes its null homotopy, transports the endpoints explicitly, and then
collapses conjugation by that null path.

Only the pointwise identity law is proved. There is no strict path or map
equality, bundled continuity, composition law, equivalence invariance,
`π₀`/`K₀`, Q/S comparison, or spectrum claim.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory

open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The identity realization map sends the chosen basepoint to itself. -/
theorem NQReal.map_id_basepoint :
    NQReal.map (𝟭 C) (NQReal.basepoint C) = NQReal.basepoint C := by
  rw [NQReal.map_id]
  rfl

/-- The identity functor's zero-comparison edge has the same underlying edge
as the degenerate edge at the zero vertex. Endpoint proof transports are not
part of this stable statement. -/
@[simp 1100]
theorem NQ.zeroComparisonEdge_id_edge :
    (NQ.zeroComparisonEdge (𝟭 C)).edge =
      (SSet.Edge.id (NQ.zeroVertex C)).edge := by
  rw [NQ.zeroComparisonEdge_edge, QuillenQ.zeroComparisonIso_id,
    SSet.Edge.id_edge]
  change ComposableArrows.mk₁ (𝟙 (⟨0⟩ : QuillenQ C)) =
    (CategoryTheory.nerve (QuillenQ C)).σ (0 : Fin 1)
      (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C))
  exact (CategoryTheory.nerve.σ₀_mk₀_eq (⟨0⟩ : QuillenQ C)).symm

/-- After the explicit identity-basepoint endpoint cast, the identity
zero-comparison root path is null-homotopic. It is not claimed equal to the
reflexive path. -/
theorem NQKSpace.zeroComparisonRootPath_id_homotopic :
    ((NQKSpace.zeroComparisonRootPath C C (𝟭 C)).cast
      (NQReal.map_id_basepoint C).symm rfl).Homotopic
        (Path.refl (NQReal.basepoint C)) := by
  have hMappedBasepoint :
      NQReal.map (𝟭 C) (NQReal.basepoint C) =
        SSet.realizedVertex ((NQ.map (𝟭 C)).app (op ⦋0⦌) (NQ.zeroVertex C)) :=
    NQReal.map_basepoint_eq_realizedVertex (𝟭 C)
  have hBaseVertex :
      NQReal.basepoint C = SSet.realizedVertex (NQ.zeroVertex C) :=
    NQReal.basepoint_eq_realizedVertex C
  have hIdHomotopic :
      (TopCat.pathEquiv
        (SSet.realizedEdgePath (SSet.Edge.id (NQ.zeroVertex C)))).Homotopic
          (Path.refl (SSet.realizedVertex (NQ.zeroVertex C))) :=
    SSet.realizedEdgePath_id_homotopic _
  have hUnfold :
      NQKSpace.zeroComparisonRootPath C C (𝟭 C) =
        (TopCat.pathEquiv
          (SSet.realizedEdgePath (NQ.zeroComparisonEdge (𝟭 C)))).cast
            hMappedBasepoint hBaseVertex := by
    simp only [NQKSpace.zeroComparisonRootPath,
      NQReal.zeroComparisonPath, TopCat.Path.pathEquiv_cast]
  rw [hUnfold]
  have hCasted := Path.Homotopic.pathCast hIdHomotopic hBaseVertex hBaseVertex
  convert hCasted using 1
  · apply Path.ext
    ext t
    simp only [Path.cast_coe]
    change (SSet.realizedEdgePath
        (NQ.zeroComparisonEdge (𝟭 C))).hom.hom
          (TopCat.I.homeomorph.symm t) =
      (SSet.realizedEdgePath
        (SSet.Edge.id (NQ.zeroVertex C))).hom.hom
          (TopCat.I.homeomorph.symm t)
    rw [SSet.realizedEdgePath_hom, SSet.realizedEdgePath_hom,
      NQ.zeroComparisonEdge_id_edge]
  · apply Path.ext
    ext t
    simp [Path.cast_coe]

/-- The identity exact functor induces a Quillen K-space map pointwise
homotopic to the identity. -/
theorem NQKSpaceMap_id_homotopic (γ : NQKSpace C) :
    (NQKSpaceMap C C (𝟭 C) γ).Homotopic γ := by
  have hSrc := NQReal.map_id_basepoint C
  have hMapId : NQReal.map (𝟭 C) = 𝟙 (NQReal C) := NQReal.map_id
  have hLoop :
      ((NQKSpace.mapLoop C C (𝟭 C) γ).cast
        hSrc.symm hSrc.symm).Homotopic γ := by
    have hLoopEq :
        (NQKSpace.mapLoop C C (𝟭 C) γ).cast
          hSrc.symm hSrc.symm = γ := by
      apply Path.ext
      funext t
      change (NQReal.map (𝟭 C)).hom (γ t) = γ t
      rw [hMapId]
      rfl
    rw [hLoopEq]
    exact Path.Homotopic.refl _
  have hShape :
      NQKSpaceMap C C (𝟭 C) γ =
        (((NQKSpace.zeroComparisonRootPath C C (𝟭 C)).cast
          hSrc.symm rfl).symm.trans
          ((((NQKSpace.mapLoop C C (𝟭 C) γ).cast
            hSrc.symm hSrc.symm).trans
            ((NQKSpace.zeroComparisonRootPath C C (𝟭 C)).cast
              hSrc.symm rfl)))) := by
    simp only [NQKSpaceMap, NQKSpace.zeroComparisonRootPath,
      NQKSpace.mapLoop]
    rfl
  let p : Path (NQReal.basepoint C) (NQReal.basepoint C) :=
    (NQKSpace.zeroComparisonRootPath C C (𝟭 C)).cast hSrc.symm rfl
  have hNull : p.Homotopic (Path.refl (NQReal.basepoint C)) :=
    NQKSpace.zeroComparisonRootPath_id_homotopic C
  have hConj : (p.symm.trans (γ.trans p)).Homotopic γ :=
    Path.Homotopic.conj_null hNull
  rw [hShape]
  exact (Path.Homotopic.pathCast
    ((Path.Homotopic.refl _).hcomp (hLoop.hcomp (Path.Homotopic.refl _)))
      rfl rfl).trans
    (Path.Homotopic.pathCast hConj rfl rfl)

end AlgebraicKTheory
