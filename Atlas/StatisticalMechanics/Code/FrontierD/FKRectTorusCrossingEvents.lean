/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRandomClusterEventFKG
import Code.FrontierD.FKRectTorusNetMonotonicity



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



def FKRectConnectedWithin (R : FKRectTorus) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) : Prop :=
  ((fkRectOpenGraph R omega).induce S).Reachable x y



theorem FKRectConnectedWithin.mono_configuration
    (R : FKRectTorus) {omega tau : R.Configuration}
    (hopen : omega ≤ tau) (S : Set R.Vertex) {x y : S}
    (hxy : FKRectConnectedWithin R omega S x y) :
    FKRectConnectedWithin R tau S x y := by
  apply hxy.mono
  intro u v huv
  exact fkRectOpenGraph_mono R (omega := omega) (tau := tau) (by
    intro e he
    cases het : tau e
    · have hle := hopen e
      rw [he, het] at hle
      exact ((by decide : ¬ (true ≤ false)) hle).elim
    · rfl) huv



theorem fkRectConnectedWithin_isIncreasing
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) :
    IsIncreasing
      {omega : R.Configuration | FKRectConnectedWithin R omega S x y} := by
  intro omega tau hopen hxy
  exact hxy.mono_configuration R hopen S



theorem FKRectConnectedWithin.mono_set
    (R : FKRectTorus) (omega : R.Configuration)
    {S T : Set R.Vertex} (hST : S ⊆ T) {x y : S}
    (hxy : FKRectConnectedWithin R omega S x y) :
    FKRectConnectedWithin R omega T
      ⟨x, hST x.2⟩ ⟨y, hST y.2⟩ := by
  exact hxy.map
    ((fkRectOpenGraph R omega).induceHomOfLE hST).toHom


theorem FKRectConnectedWithin.trans_union
    (R : FKRectTorus) (omega : R.Configuration)
    {S T : Set R.Vertex} {x y z : R.Vertex}
    (hx : x ∈ S) (hyS : y ∈ S) (hyT : y ∈ T) (hz : z ∈ T)
    (hxy : FKRectConnectedWithin R omega S ⟨x, hx⟩ ⟨y, hyS⟩)
    (hyz : FKRectConnectedWithin R omega T ⟨y, hyT⟩ ⟨z, hz⟩) :
    FKRectConnectedWithin R omega (S ∪ T)
      ⟨x, Or.inl hx⟩ ⟨z, Or.inr hz⟩ := by
  have hxy' := hxy.mono_set R omega
    (T := S ∪ T) (fun _ h => Or.inl h)
  have hyz' := hyz.mono_set R omega
    (T := S ∪ T) (fun _ h => Or.inr h)
  exact hxy'.trans hyz'




def fkRectVertexRectangle (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) : Set R.Vertex :=
  {v | x0 ≤ v.1.val ∧ v.1.val ≤ x1 ∧
    y0 ≤ v.2.val ∧ v.2.val ≤ y1}


def fkRectVerticalCrossingEvent (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) : Set R.Configuration :=
  {omega | ∃ (x y : fkRectVertexRectangle R x0 x1 y0 y1),
    x.1.2.val = y0 ∧ y.1.2.val = y1 ∧
      FKRectConnectedWithin R omega
        (fkRectVertexRectangle R x0 x1 y0 y1) x y}


def fkRectHorizontalCrossingEvent (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) : Set R.Configuration :=
  {omega | ∃ (x y : fkRectVertexRectangle R x0 x1 y0 y1),
    x.1.1.val = x0 ∧ y.1.1.val = x1 ∧
      FKRectConnectedWithin R omega
        (fkRectVertexRectangle R x0 x1 y0 y1) x y}

theorem fkRectVerticalCrossingEvent_isIncreasing
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat) :
    IsIncreasing (fkRectVerticalCrossingEvent R x0 x1 y0 y1) := by
  intro omega tau hopen
  rintro ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx, hy, hxy.mono_configuration R hopen _⟩

theorem fkRectHorizontalCrossingEvent_isIncreasing
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat) :
    IsIncreasing (fkRectHorizontalCrossingEvent R x0 x1 y0 y1) := by
  intro omega tau hopen
  rintro ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx, hy, hxy.mono_configuration R hopen _⟩


def fkRectVerticalEndpointPairs (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat) :
    Finset ((fkRectVertexRectangle R x0 x1 y0 y1) ×
      (fkRectVertexRectangle R x0 x1 y0 y1)) :=
  Finset.univ.filter fun p =>
    p.1.1.2.val = y0 ∧ p.2.1.2.val = y1


def fkRectVerticalEndpointConnectionEvent (R : FKRectTorus)
    (x0 x1 y0 y1 : Nat)
    (p : (fkRectVertexRectangle R x0 x1 y0 y1) ×
      (fkRectVertexRectangle R x0 x1 y0 y1)) : Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectVertexRectangle R x0 x1 y0 y1) p.1 p.2}

theorem fkRectVerticalCrossingEvent_eq_finiteEndpointUnion
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat) :
    fkRectVerticalCrossingEvent R x0 x1 y0 y1 =
      fkRectFiniteEventUnion
        (fkRectVerticalEndpointPairs R x0 x1 y0 y1)
        (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1) := by
  ext omega
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨(x, y), by simp [fkRectVerticalEndpointPairs, hx, hy], hxy⟩
  · rintro ⟨p, hp, hconn⟩
    have hend : p.1.1.2.val = y0 ∧ p.2.1.2.val = y1 := by
      simpa [fkRectVerticalEndpointPairs] using hp
    exact ⟨p.1, p.2, hend.1, hend.2, hconn⟩

theorem fkRectVerticalEndpointPairs_nonempty
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat)
    (hxx : x0 ≤ x1) (hx1 : x1 < R.width)
    (hyy : y0 ≤ y1) (hy1 : y1 < R.height) :
    (fkRectVerticalEndpointPairs R x0 x1 y0 y1).Nonempty := by
  let xb : R.Vertex := (⟨x0, hxx.trans_lt hx1⟩, ⟨y0, hyy.trans_lt hy1⟩)
  let xt : R.Vertex := (⟨x0, hxx.trans_lt hx1⟩, ⟨y1, hy1⟩)
  have hxb : xb ∈ fkRectVertexRectangle R x0 x1 y0 y1 := by
    simp [xb, fkRectVertexRectangle, hxx, hyy]
  have hxt : xt ∈ fkRectVertexRectangle R x0 x1 y0 y1 := by
    simp [xt, fkRectVertexRectangle, hxx, hyy]
  refine ⟨(⟨xb, hxb⟩, ⟨xt, hxt⟩), ?_⟩
  simp [fkRectVerticalEndpointPairs, xb, xt]



theorem exists_verticalEndpoint_eventMass_ge
    (R : FKRectTorus) {q c : Real} (hq : 0 < q)
    (x0 x1 y0 y1 : Nat)
    (hxx : x0 ≤ x1) (hx1 : x1 < R.width)
    (hyy : y0 ≤ y1) (hy1 : y1 < R.height)
    (hc : c ≤ fkRectCriticalEventMass R q
      (fkRectVerticalCrossingEvent R x0 x1 y0 y1)) :
    ∃ p ∈ fkRectVerticalEndpointPairs R x0 x1 y0 y1,
      c ≤ ((fkRectVerticalEndpointPairs R x0 x1 y0 y1).card : Real) *
        fkRectCriticalEventMass R q
          (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1 p) := by
  rw [fkRectVerticalCrossingEvent_eq_finiteEndpointUnion] at hc
  exact exists_card_mul_eventMass_ge_of_finiteUnion_ge R hq
    (fkRectVerticalEndpointPairs_nonempty R x0 x1 y0 y1
      hxx hx1 hyy hy1)
    (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1) hc

end

end StatMech.FrontierD
