/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeSourceFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectZeroFibre

/-!
# The leading-edge fixed-source target retains the original source-edge family

The complete fixed-source pullback of the leading-edge/tail row target
is the same original source-edge family pulled back at the tail's
first vertex. Both maps retain the entire original tail simplex and
leading edge, together with the same original source point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.InitialEdgeTailMapping

/-- The actual target is the original source-edge object pulled back at the first tail vertex. -/
abbrev sourceEdgeTarget (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) : SSet.{u} :=
  pullback (LeftDecalageObject.sourceEdgesTarget W x) (tailFirstVertex W n)

/-- The whole original fixed-source leading-edge target maps to its literal source-edge pullback. -/
def toSourceEdges (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    sourceFibreTarget W x n ⟶ sourceEdgeTarget W x n :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
      (by rw [Category.assoc, ← rowSource, pullback.condition]))
    (pullback.fst _ _ ≫ pullback.fst _ _) (by
      rw [LeftDecalageObject.sourceEdgesTarget, ← Category.assoc, pullback.lift_fst,
        Category.assoc, ← pullback.condition]
      exact (Category.assoc _ _ _).symm)

/-- The inverse retains the same original leading edge, whole tail and fixed source point. -/
def fromSourceEdges (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    sourceEdgeTarget W x n ⟶ sourceFibreTarget W x n :=
  pullback.lift
    (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.fst _ _)
      (by rw [← pullback.condition]; rfl))
    (pullback.fst _ _ ≫ pullback.snd _ _) (by
      rw [rowSource, ← Category.assoc, pullback.lift_snd, Category.assoc, pullback.condition]
      exact (Category.assoc _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The complete original leading-edge source target is the same original source-edge pullback. -/
def sourceEdgeTargetIso (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    sourceFibreTarget W x n ≅ sourceEdgeTarget W x n where
  hom := toSourceEdges W x n
  inv := fromSourceEdges W x n
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [toSourceEdges, fromSourceEdges, Category.assoc, pullback.lift_fst,
          pullback.lift_snd, Category.id_comp]
      · simp only [toSourceEdges, fromSourceEdges, Category.assoc, pullback.lift_fst,
          pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [toSourceEdges, fromSourceEdges, Category.assoc, pullback.lift_fst,
          pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]
      · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    · simp only [toSourceEdges, fromSourceEdges, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The whole target isomorphism retains its complete original tail projection. -/
theorem sourceEdgeTargetIso_tail (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (sourceEdgeTargetIso W x n).hom ≫ pullback.snd _ _ =
      pullback.fst (rowSource W n) (SSet.yonedaEquiv.symm x) ≫
        pullback.fst (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2)) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The whole target isomorphism retains its entire original leading edge. -/
theorem sourceEdgeTargetIso_edge (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (sourceEdgeTargetIso W x n).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst (rowSource W n) (SSet.yonedaEquiv.symm x) ≫
        pullback.snd (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2)) := by
  change (toSourceEdges W x n ≫ pullback.fst _ _) ≫ pullback.fst _ _ = _
  rw [toSourceEdges, pullback.lift_fst, pullback.lift_fst]

end SimplicialSpace.InitialEdgeTailMapping
