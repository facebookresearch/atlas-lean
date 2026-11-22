/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DiscreteSourceCoproductMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.FirstFaceVertexUnion
import MathlibExt.AlgebraicTopology.SimplicialObject.LeftDecalageOperators

/-!
# The original right-face and first-vertex restriction is a Kan fibration

The whole coproduct of the original right face and original first vertex
is monic. Reedy mapping restriction along that same inclusion is a Kan
fibration. The actual coproduct mapping product and both whole Yoneda
isomorphisms retain the exact original pair of restriction maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.LeftDecalageRows

/-- The whole original pair map retains the right face and original first vertex. -/
def pairMap (W : SimplicialSpace.{u}) (n : ℕ) :
    W.diagram.obj (op (SimplexCategory.mk (n + 1))) ⟶
      W.diagram.obj (op (SimplexCategory.mk n)) ⨯ W.diagram.obj (op (SimplexCategory.mk 0)) :=
  prod.lift (W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op)
    (W.diagram.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk (n + 1)) 0).op)

/-- The entire original coproduct mapping target identifies with the same right-row and first-object product. -/
def pairTargetIso (W : SimplicialSpace.{u}) (n : ℕ) :
    (discreteSourceMapping W).obj (op ((Δ[n] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}))) ≅
      W.diagram.obj (op (SimplexCategory.mk n)) ⨯ W.diagram.obj (op (SimplexCategory.mk 0)) :=
  discreteSourceCoproductIso W _ _ ≪≫ prod.mapIso (discreteYonedaIso W n) (discreteYonedaIso W 0)

/-- The whole original mapping comparison retains both original face and vertex restrictions. -/
theorem restriction_pairTargetIso (W : SimplicialSpace.{u}) (n : ℕ) :
    (discreteSourceMapping W).map (SSet.FirstFaceVertexUnion.inclusion.{u} n).op ≫
        (pairTargetIso W n).hom =
      (discreteYonedaIso W (n + 1)).hom ≫ pairMap W n := by
  apply prod.hom_ext
  · simp only [pairTargetIso, Iso.trans_hom, prod.mapIso_hom, Category.assoc,
      prod.map_fst, pairMap, prod.lift_fst]
    rw [← Category.assoc (discreteSourceCoproductIso W _ _).hom prod.fst,
      discreteSourceCoproductIso_fst, ← Category.assoc, ← Functor.map_comp, ← op_comp,
      (SSet.FirstFaceVertexUnion.inclusion_legs n).1]
    exact discreteYonedaIso_naturality_index W _
  · simp only [pairTargetIso, Iso.trans_hom, prod.mapIso_hom, Category.assoc,
      prod.map_snd, pairMap, prod.lift_snd]
    rw [← Category.assoc (discreteSourceCoproductIso W _ _).hom prod.snd,
      discreteSourceCoproductIso_snd, ← Category.assoc, ← Functor.map_comp, ← op_comp,
      (SSet.FirstFaceVertexUnion.inclusion_legs n).2]
    exact discreteYonedaIso_naturality_index W _

/-- Actual Reedy fibrancy makes the original full right-face/first-object pair a Kan fibration. -/
theorem pairMap_fibration (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, Fibration (pairMap W n) := by
  intro hW n
  let i := SSet.FirstFaceVertexUnion.inclusion.{u} n
  let _ : Mono i := SSet.FirstFaceVertexUnion.inclusion_mono n
  let _ := VertexRestriction.discreteRestriction_fibration i W hW
  let e : Arrow.mk ((discreteSourceMapping W).map i.op) ≅ Arrow.mk (pairMap W n) :=
    Arrow.isoMk (discreteYonedaIso W (n + 1)) (pairTargetIso W n)
      (restriction_pairTargetIso W n).symm
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact ((fibrations SSet.{u}).arrow_mk_iso_iff e).mp
    ((HomotopicalAlgebra.fibration_iff _).mp (inferInstanceAs (Fibration ((discreteSourceMapping W).map i.op))))

end SimplicialSpace.LeftDecalageRows
