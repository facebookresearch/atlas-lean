/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathMappingFibreWeak
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingComposition

/-!
# The original Segal path transition over an entire simplex operator

Every original ordinal operator induces the literal path row map and
the actual map of fibres over the same entire tail simplex. The
prescribed source object and original target simplex remain fixed.
These original maps are the data compared to composition by the
operator's actual initial edge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The whole original path-row map at the supplied original simplex operator. -/
def rowOperator {m n : ℕ} (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌)
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (diagram W x).obj (op (SimplexCategory.mk n)) ⟶
      (diagram W x).obj (op (SimplexCategory.mk m)) :=
  (diagram W x).map f.op

/-- The actual whole path map on fibres retains the entire prescribed original tail simplex. -/
def rowPointOperator {m n : ℕ} (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌)
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointFibre W x n b ⟶ rowPointFibre W x m (b ≫ W.diagram.map f.op) :=
  pullback.map ((projection W x).app (op (SimplexCategory.mk n))) b
    ((projection W x).app (op (SimplexCategory.mk m))) (b ≫ W.diagram.map f.op)
    (rowOperator W x f) (𝟙 (Δ[0] : SSet.{u})) (W.diagram.map f.op)
    ((projection W x).naturality f.op).symm (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Every whole original path fibre transition retains the original shifted simplex map. -/
theorem rowPointOperator_fst {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointOperator W x f b ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ rowOperator W x f := pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Every whole original path fibre transition retains the same point leg. -/
theorem rowPointOperator_snd {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    rowPointOperator W x f b ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold rowPointOperator
  change (pullback.lift _ _ _) ≫ _ = _
  rw [pullback.lift_snd]
  exact Category.comp_id _

end SimplicialSpace.LeftDecalageObject
