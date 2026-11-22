/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRealizedNativeContraction

/-!
# Pointwise readback of the actual realized native contraction

The original constant/identity endpoint descriptions retain the same
whole realized homotopy map, including every original point and time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

private theorem transported_first_apply {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {f g f' : C(A, B)} (hf : f = f') (H : ContinuousMap.Homotopy f g)
    (ht : ContinuousMap.Homotopy f g = ContinuousMap.Homotopy f' g) (z : unitInterval × A) :
    Eq.mp ht H z = H z := by
  cases hf
  have he : ht = rfl := Subsingleton.elim _ _
  rw [he]
  rfl

private theorem transported_second_apply {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {f g g' : C(A, B)} (hg : g = g') (H : ContinuousMap.Homotopy f g)
    (ht : ContinuousMap.Homotopy f g = ContinuousMap.Homotopy f g') (z : unitInterval × A) :
    Eq.mp ht H z = H z := by
  cases hg
  have he : ht = rfl := Subsingleton.elim _ _
  rw [he]
  rfl

/-- The original realized native contraction retains the literal actual cylinder formula. -/
theorem realizedNativePointContraction_apply (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (t : unitInterval)
    (z : SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x))) :
    realizedNativePointContraction W x (t, z) =
      SSet.realizeHomotopyMap _ _ (SSet.const (diagonalBasepoint W x))
        (𝟙 (SSet.simplicialDiagonalFunctor.obj (diagram W x))) (nativeDiagonalPointContraction W x)
          ((TopCat.prodIsoProd TopCat.I.{u}
            (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)))).inv
              (TopCat.I.homeomorph.symm t, z)) := by
  unfold realizedNativePointContraction
  dsimp only
  have hg : (SSet.toTop.map (𝟙 (SSet.simplicialDiagonalFunctor.obj (diagram W x)))).hom =
      ContinuousMap.id (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x))) := by
    rw [SSet.toTop.map_id]
    rfl
  have hf : (SSet.toTop.map (SSet.const (diagonalBasepoint W x))).hom =
      ContinuousMap.const (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)))
        (SSet.realizedVertex (diagonalBasepoint W x)) := by
    apply ContinuousMap.ext
    intro a
    have hf : (SSet.const (diagonalBasepoint W x) :
        SSet.simplicialDiagonalFunctor.obj (diagram W x) ⟶ _) =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.yonedaEquiv.symm (diagonalBasepoint W x) := by
      ext n b
      rfl
    rw [hf, SSet.toTop.map_comp, SSet.toTop_map_point]
    rfl
  exact (transported_second_apply hg _ _ _).trans (transported_first_apply hf _ _ _)

end SimplicialSpace.LeftDecalageObject
