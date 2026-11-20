/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectEvenRowTranslation



open Set SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectEvenRowTranslatedConnectionEvent
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) (shift : Nat) :
    Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectEvenRowTranslationSet R shift S)
    (fkRectEvenRowTranslationSetEquiv R shift S x)
    (fkRectEvenRowTranslationSetEquiv R shift S y)}

theorem fkRectEvenRowTranslatedConnectionEvent_isIncreasing
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) (shift : Nat) :
    IsIncreasing
      (fkRectEvenRowTranslatedConnectionEvent R S x y shift) :=
  fkRectConnectedWithin_isIncreasing R
    (fkRectEvenRowTranslationSet R shift S)
    (fkRectEvenRowTranslationSetEquiv R shift S x)
    (fkRectEvenRowTranslationSetEquiv R shift S y)



theorem fkRectCritical_evenRowTranslatedConnectionMass
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (shift : Nat) (hshift : Even shift) (q : Real) :
    fkRectCriticalEventMass R q
        (fkRectEvenRowTranslatedConnectionEvent R S x y shift) =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  exact fkRectCritical_connectedWithinMass_evenRowTranslation
    R shift hshift q S x y



def fkRectEvenRowBlockIntersection
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (step blocks : Nat) : Set R.Configuration :=
  fkRectFiniteEventIntersection (Finset.range blocks) fun i =>
    fkRectEvenRowTranslatedConnectionEvent R S x y (i * step)

theorem fkRectEvenRowBlockIntersection_isIncreasing
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (step blocks : Nat) :
    IsIncreasing (fkRectEvenRowBlockIntersection
      R S x y step blocks) := by
  apply fkRectFiniteEventIntersection_isIncreasing
  intro i hi
  exact fkRectEvenRowTranslatedConnectionEvent_isIncreasing
    R S x y (i * step)


theorem fkRectCritical_evenRowBlockLower_pow_le_intersection
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (step blocks : Nat) (hstep : Even step)
    {q a : Real} (hq : 1 ≤ q) (ha : 0 ≤ a)
    (hlower : a ≤ fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega S x y}) :
    a ^ blocks ≤ fkRectCriticalEventMass R q
      (fkRectEvenRowBlockIntersection R S x y step blocks) := by
  have hmass (i : Nat) (hi : i ∈ Finset.range blocks) :
      a ≤ fkRectCriticalEventMass R q
        (fkRectEvenRowTranslatedConnectionEvent R S x y (i * step)) := by
    rw [fkRectCritical_evenRowTranslatedConnectionMass
      R S x y (i * step) (hstep.mul_left i) q]
    exact hlower
  calc
    a ^ blocks = ∏ i ∈ Finset.range blocks, a := by simp
    _ ≤ ∏ i ∈ Finset.range blocks,
          fkRectCriticalEventMass R q
            (fkRectEvenRowTranslatedConnectionEvent
              R S x y (i * step)) :=
      Finset.prod_le_prod (fun _ _ => ha) hmass
    _ ≤ fkRectCriticalEventMass R q
          (fkRectEvenRowBlockIntersection R S x y step blocks) :=
      fkRectCriticalEventMass_prod_le_finiteIntersection
        R hq (Finset.range blocks)
          (fun i => fkRectEvenRowTranslatedConnectionEvent
            R S x y (i * step))
          (fun i _ =>
            fkRectEvenRowTranslatedConnectionEvent_isIncreasing
              R S x y (i * step))


theorem fkRectEvenRowTranslationSet_column_bounds
    (R : FKRectTorus) (S : Set R.Vertex) (shift left right : Nat)
    (hS : ∀ v ∈ S, left ≤ v.1.val ∧ v.1.val ≤ right)
    {v : R.Vertex} (hv : v ∈ fkRectEvenRowTranslationSet R shift S) :
    left ≤ v.1.val ∧ v.1.val ≤ right := by
  rcases hv with ⟨w, hw, rfl⟩
  simpa using hS w hw



theorem FKRectConnectedWithin.reachable
    (R : FKRectTorus) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S)
    (hxy : FKRectConnectedWithin R omega S x y) :
    (fkRectOpenGraph R omega).Reachable x.1 y.1 := by
  let inclusion : (fkRectOpenGraph R omega).induce S →g
      fkRectOpenGraph R omega :=
    { toFun := Subtype.val
      map_rel' := fun {_ _} h => h }
  exact hxy.map inclusion

theorem fkRectEvenRowTranslatedConnection_start
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (shift : Nat) (omega : R.Configuration)
    (hmem : omega ∈
      fkRectEvenRowTranslatedConnectionEvent R S x y shift) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectEvenRowTranslationVertexEquiv R shift x.1)
      (fkRectEvenRowTranslationVertexEquiv R shift y.1) := by
  exact FKRectConnectedWithin.reachable R omega
    (fkRectEvenRowTranslationSet R shift S)
    (fkRectEvenRowTranslationSetEquiv R shift S x)
    (fkRectEvenRowTranslationSetEquiv R shift S y) hmem



theorem fkRectEvenRowBlockIntersection_reachable
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S)
    (step blocks : Nat)
    (hxy : fkRectEvenRowTranslationVertexEquiv R step x.1 = y.1)
    (omega : R.Configuration)
    (hmem : omega ∈ fkRectEvenRowBlockIntersection
      R S x y step blocks) :
    (fkRectOpenGraph R omega).Reachable x.1
      (fkRectEvenRowTranslationVertexEquiv R (blocks * step) x.1) := by
  induction blocks with
  | zero =>
      simpa using (SimpleGraph.Reachable.refl x.1 :
        (fkRectOpenGraph R omega).Reachable x.1 x.1)
  | succ blocks ih =>
      have hprevious : omega ∈ fkRectEvenRowBlockIntersection
          R S x y step blocks := by
        intro i hi
        exact hmem i (Finset.mem_range.mpr
          ((Finset.mem_range.mp hi).trans (Nat.lt_succ_self blocks)))
      have hreach := ih hprevious
      have hlast := fkRectEvenRowTranslatedConnection_start
        R S x y (blocks * step) omega
        (hmem blocks (Finset.mem_range.mpr (Nat.lt_succ_self blocks)))
      have hend :
          fkRectEvenRowTranslationVertexEquiv R (blocks * step) y.1 =
            fkRectEvenRowTranslationVertexEquiv R
              ((blocks + 1) * step) x.1 := by
        rw [← hxy, fkRectEvenRowTranslationVertexEquiv_add]
        congr 2
        rw [Nat.add_mul]
        simp
      rw [hend] at hlast
      exact hreach.trans hlast

end

end StatMech.FrontierD
