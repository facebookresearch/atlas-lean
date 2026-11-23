/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.RawLoopCWPointModel

noncomputable section
set_option autoImplicit false

open CategoryTheory Topology PointedTopCat
open scoped unitInterval

universe u v

#check PointedTopCat.rawLoopCWPointModel
#print axioms PointedTopCat.rawLoopCWPointModel
#check PointedTopCat.hasRawLoopCWPointModel
#print axioms PointedTopCat.hasRawLoopCWPointModel
#check PointedTopCat.rawLoopCWPointModel_constantLoopNDR
#print axioms PointedTopCat.rawLoopCWPointModel_constantLoopNDR

section Clients

variable (X : PointedTopCat.{u})
    (dX : TopPair.StandardNDRData (PointedTopCat.pointedPair.obj X))
    (C : TopCat.{v}) [T2Space C] [Topology.CWComplex (Set.univ : Set C)]
    (c : C) (j : Topology.CWComplex.cell (Set.univ : Set C) 0)
    (hj : Topology.CWComplex.map (C := (Set.univ : Set C)) 0 j ![] = c)
    (r : C(X.right, C)) (s : C(C, X.right))
    (hr : r (X.hom PUnit.unit) = c) (hs : s c = X.hom PUnit.unit)
    (HX : ContinuousMap.HomotopyRel (s.comp r) (ContinuousMap.id X.right)
      {X.hom PUnit.unit})
    (HC : ContinuousMap.HomotopyRel (r.comp s) (ContinuousMap.id C) {c})

example : Nonempty (RawLoopCWPointModelData.{u, max u v} X) :=
  hasRawLoopCWPointModel X dX C c j hj r s hr hs HX HC

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    Topology.CWComplex (Set.univ : Set D.model) := by
  exact (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).cw

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    T2Space D.model := by
  exact (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).hausdorff

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    ∀ q : Fin 0 → ℝ, D.cw.map 0 D.zeroCell q = D.point := by
  exact (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).zeroCell_value

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    D.toModel (Path.refl (X.hom PUnit.unit)) = D.point ∧
      D.fromModel D.point = Path.refl (X.hom PUnit.unit) := by
  exact ⟨(rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).toModel_point,
    (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).fromModel_point⟩

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    ∀ gamma : LoopSpace X.right (X.hom PUnit.unit),
      D.originalHomotopy (0, gamma) = D.fromModel (D.toModel gamma) ∧
        D.originalHomotopy (1, gamma) = gamma := by
  dsimp only
  intro gamma
  exact ⟨(rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).originalHomotopy.apply_zero gamma,
    (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).originalHomotopy.apply_one gamma⟩

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    ∀ z₀ : D.model,
      D.modelHomotopy (0, z₀) = D.toModel (D.fromModel z₀) ∧
        D.modelHomotopy (1, z₀) = z₀ := by
  dsimp only
  intro z₀
  exact ⟨(rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).modelHomotopy.apply_zero z₀,
    (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).modelHomotopy.apply_one z₀⟩

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    ∀ t : unitInterval,
      D.originalHomotopy (t, Path.refl (X.hom PUnit.unit)) =
          Path.refl (X.hom PUnit.unit) ∧
        D.modelHomotopy (t, D.point) = D.point := by
  dsimp only
  intro t
  exact
    ⟨(rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).originalHomotopy.eq_snd t
        (Set.mem_singleton_iff.mpr rfl),
      (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).modelHomotopy.eq_snd t
        (Set.mem_singleton_iff.mpr rfl)⟩

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    D.constantLoopNDR = dX.loop := by
  exact PointedTopCat.rawLoopCWPointModel_constantLoopNDR
    X dX C c j hj r s hr hs HX HC

example :
    let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
    D.constantLoopNDR.control (Path.refl (X.hom PUnit.unit)) = 0 := by
  let D := rawLoopCWPointModel X dX C c j hj r s hr hs HX HC
  exact (D.constantLoopNDR.control_eq_zero_iff _).mpr ⟨PUnit.unit, rfl⟩

end Clients

end
