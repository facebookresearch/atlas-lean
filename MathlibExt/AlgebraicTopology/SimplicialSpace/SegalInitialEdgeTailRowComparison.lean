/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeTailMapping

/-!
# The actual leading-edge and tail row comparison in a Segal space

Whole original Yoneda isomorphisms identify the cover mapping pullback
with the original leading edge and tail-simplex endpoint pullback.
The actual initial-interval restriction is a trivial fibration under
the existing Segal-space condition. Its full row comparison therefore
retains both original maps and is genuinely weak.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.InitialEdgeTailMapping

/-- The original first-vertex map of the entire tail simplex. -/
def tailFirstVertex (W : SimplicialSpace.{u}) (n : ℕ) : W.diagram _⦋n⦌ ⟶ W.diagram _⦋0⦌ :=
  W.diagram.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) 0).op

/-- The whole original tail-simplex and leading-edge endpoint pullback. -/
abbrev rowTarget (W : SimplicialSpace.{u}) (n : ℕ) : SSet.{u} :=
  pullback (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2))

set_option backward.isDefEq.respectTransparency false in
/-- Both original Yoneda target comparisons retain the entire endpoint cospan. -/
def rowPullbackIso (W : SimplicialSpace.{u}) (n : ℕ) :
    pullback
        ((discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.vertexToTail.{u} n).op)
        ((discreteSourceMapping W).map (SSet.stdSimplex.δ (0 : Fin 2)).op) ≅ rowTarget W n := by
  let f := (discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.vertexToTail.{u} n).op
  let g := (discreteSourceMapping W).map (SSet.stdSimplex.δ (0 : Fin 2)).op
  let h₁ := discreteYonedaIso_naturality_index W
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) 0)
  let h₂ := discreteYonedaIso_naturality_index W (SimplexCategory.δ (0 : Fin 2))
  let p := pullback.map f g (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2))
    (discreteYonedaIso W n).hom (discreteYonedaIso W 1).hom (discreteYonedaIso W 0).hom h₁ h₂
  let _ : IsIso p := pullback.map_isIso f g (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2))
    (discreteYonedaIso W n).hom (discreteYonedaIso W 1).hom (discreteYonedaIso W 0).hom h₁ h₂
  exact asIso p

/-- The actual whole original leading-edge/tail row comparison. -/
def rowComparison (W : SimplicialSpace.{u}) (n : ℕ) : W.diagram _⦋n + 1⦌ ⟶ rowTarget W n :=
  (discreteYonedaIso W (n + 1)).inv ≫
    (discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover.{u} (n + 1)).ι.op ≫
      (coverIso W n).hom ≫ (rowPullbackIso W n).hom

set_option backward.isDefEq.respectTransparency false in
/-- The whole original row comparison retains its exact original tail face. -/
theorem rowComparison_fst (W : SimplicialSpace.{u}) (n : ℕ) :
    rowComparison W n ≫ pullback.fst _ _ = W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op := by
  unfold rowComparison rowPullbackIso
  rw [Category.assoc, Category.assoc, Category.assoc, asIso_hom, pullback.map, pullback.lift_fst,
    ← Category.assoc (coverIso W n).hom, coverIso_fst,
    ← Category.assoc ((discreteSourceMapping W).map _), ← Functor.map_comp, ← op_comp,
    SSet.Rezk.InitialEdgeTail.tailInclusion_ambient, discreteYonedaIso_naturality_index,
    Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The whole original row comparison retains its exact original leading edge. -/
theorem rowComparison_snd (W : SimplicialSpace.{u}) (n : ℕ) :
    rowComparison W n ≫ pullback.snd _ _ =
      W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))).op := by
  unfold rowComparison rowPullbackIso
  rw [Category.assoc, Category.assoc, Category.assoc, asIso_hom, pullback.map, pullback.lift_snd,
    ← Category.assoc (coverIso W n).hom, coverIso_snd,
    ← Category.assoc ((discreteSourceMapping W).map _), ← Functor.map_comp, ← op_comp,
    SSet.Rezk.InitialEdgeTail.edgeInclusion_ambient, discreteYonedaIso_naturality_index,
    Iso.inv_hom_id_assoc]

/-- Every whole original Segal-space leading-edge/tail comparison is genuinely weak. -/
theorem rowComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W) (n : ℕ) :
    SSet.realizationWeakEquivalences (rowComparison W n) := by
  have h := (initialIntervalCover_trivialFibration W (n + 1) hW).2
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (discreteYonedaIso W (n + 1)).inv)
    (SSet.realizationWeakEquivalences.comp_mem _ _ h
      (SSet.realizationWeakEquivalences.comp_mem _ _
        (SSet.realizationWeakEquivalences.of_isIso (coverIso W n).hom)
        (SSet.realizationWeakEquivalences.of_isIso (rowPullbackIso W n).hom)))

end SimplicialSpace.InitialEdgeTailMapping
