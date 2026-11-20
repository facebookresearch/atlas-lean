/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzPfisterGhostLift

open Finset
open scoped BigOperators

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


abbrev LPTwoGhostVertex (W : Type*) := W ⊕ Bool



def lpTwoGhostPinnedConfig (tau : ConfigSpace W) :
    ConfigSpace (LPTwoGhostVertex W)
  | .inl x => tau x
  | .inr b => !b

@[simp] theorem lpTwoGhostPinnedConfig_inl
    (tau : ConfigSpace W) (x : W) :
    lpTwoGhostPinnedConfig tau (.inl x) = tau x := rfl

@[simp] theorem lpTwoGhostPinnedConfig_inr
    (tau : ConfigSpace W) (b : Bool) :
    lpTwoGhostPinnedConfig tau (.inr b) = !b := rfl

@[simp] theorem spin_lpTwoGhostPinnedConfig_inl
    (tau : ConfigSpace W) (x : W) :
    spin (lpTwoGhostPinnedConfig tau) (.inl x) = spin tau x := rfl

@[simp] theorem spin_lpTwoGhostPinnedConfig_inr_false
    (tau : ConfigSpace W) :
    spin (lpTwoGhostPinnedConfig tau) (.inr false) = 1 := by
  simp [spin, lpTwoGhostPinnedConfig]

@[simp] theorem spin_lpTwoGhostPinnedConfig_inr_true
    (tau : ConfigSpace W) :
    spin (lpTwoGhostPinnedConfig tau) (.inr true) = -1 := by
  simp [spin, lpTwoGhostPinnedConfig]


def lpTwoGhostBaseEdges (E : Finset (Sym2 W)) :
    Finset (Sym2 (LPTwoGhostVertex W)) :=
  E.image (Sym2.map Sum.inl)


def lpTwoGhostStarEdges (side : W -> Bool) :
    Finset (Sym2 (LPTwoGhostVertex W)) :=
  Finset.univ.image (fun x => s(Sum.inl x, Sum.inr (side x)))

def lpTwoGhostEdges (E : Finset (Sym2 W)) (side : W -> Bool) :
    Finset (Sym2 (LPTwoGhostVertex W)) :=
  lpTwoGhostBaseEdges E ∪ lpTwoGhostStarEdges side

theorem lpTwoGhostStarEdge_injective (side : W -> Bool) :
    Function.Injective ((fun x : W =>
      s(Sum.inl x, Sum.inr (side x))) :
        W -> Sym2 (LPTwoGhostVertex W)) := by
  intro x y h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact Sum.inl.inj h.1
  · exact absurd h.1 (by simp)

theorem lpTwoGhostBaseEdges_disjoint_star
    (E : Finset (Sym2 W)) (side : W -> Bool) :
    Disjoint (lpTwoGhostBaseEdges E) (lpTwoGhostStarEdges side) := by
  rw [Finset.disjoint_left]
  intro e he hs
  simp only [lpTwoGhostBaseEdges, lpTwoGhostStarEdges,
    Finset.mem_image, Finset.mem_univ, true_and] at he hs
  obtain ⟨e0, _, rfl⟩ := he
  obtain ⟨x, hx⟩ := hs
  induction e0 with
  | h a b =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hx
      rcases hx with h | h <;> simp at h


def lpTwoGhostCoupling
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool) :
    Sym2 (LPTwoGhostVertex W) -> Real :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | .inl x, .inl y => J s(x, y)
    | .inl x, .inr g => if side x = g then h x else 0
    | .inr g, .inl x => if side x = g then h x else 0
    | .inr _, .inr _ => 0,
    by rintro (_ | g) (_ | k) <;> simp only [] <;> rw [Sym2.eq_swap]⟩

@[simp] theorem lpTwoGhostCoupling_base
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool)
    (x y : W) :
    lpTwoGhostCoupling J h side s(Sum.inl x, Sum.inl y) = J s(x, y) := rfl

@[simp] theorem lpTwoGhostCoupling_star
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool)
    (x : W) :
    lpTwoGhostCoupling J h side
        s(Sum.inl x, Sum.inr (side x)) = h x := by
  simp [lpTwoGhostCoupling]

theorem lpTwoGhostCoupling_nonneg
    (J : Sym2 W -> Real) (h : W -> Real) (side : W -> Bool)
    (hJ : forall e, 0 <= J e) (hh : forall x, 0 <= h x) :
    forall e, 0 <= lpTwoGhostCoupling J h side e := by
  intro e
  induction e with
  | h a b =>
      rcases a with x | g <;> rcases b with y | k
      · exact hJ _
      · change 0 <= if side x = k then h x else 0
        split <;> simp [hh]
      · change 0 <= if side y = g then h y else 0
        split <;> simp [hh]
      · simp [lpTwoGhostCoupling]


def lpTwoGhostMixedField (h : W -> Real) (side : W -> Bool) : W -> Real :=
  fun x => if side x then -h x else h x

theorem lpTwoGhost_bondSum_pinned
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool) (tau : ConfigSpace W) :
    (∑ e ∈ lpTwoGhostEdges E side,
        lpTwoGhostCoupling J h side e *
          bond (lpTwoGhostPinnedConfig tau) e) =
      (∑ e ∈ E, J e * bond tau e) +
        ∑ x : W, lpTwoGhostMixedField h side x * spin tau x := by
  rw [lpTwoGhostEdges,
    Finset.sum_union (lpTwoGhostBaseEdges_disjoint_star E side)]
  congr 1
  · rw [lpTwoGhostBaseEdges, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e _
      induction e with
      | h x y =>
          rw [Sym2.map_mk, lpTwoGhostCoupling_base, bond_mk, bond_mk]
          rfl
    · intro a _ b _ hab
      exact Sym2.map.injective Sum.inl_injective hab
  · rw [lpTwoGhostStarEdges,
      Finset.sum_image (lpTwoGhostStarEdge_injective side).injOn]
    apply Finset.sum_congr rfl
    intro x _
    rw [lpTwoGhostCoupling_star, bond_mk]
    by_cases hs : side x
    · simp [lpTwoGhostMixedField, hs]
    · simp [lpTwoGhostMixedField, hs]




theorem lpTwoGhost_weight_pinned_eq
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool) (tau : ConfigSpace W) :
    wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
        (fun _ => 0) (lpTwoGhostPinnedConfig tau) =
      wJ E J (lpTwoGhostMixedField h side) tau := by
  unfold wJ
  rw [lpTwoGhost_bondSum_pinned]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]



theorem lpTwoGhost_pinnedPartition_eq
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool) :
    (∑ tau : ConfigSpace W,
      wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
        (fun _ => 0) (lpTwoGhostPinnedConfig tau)) =
      ZJ E J (lpTwoGhostMixedField h side) := by
  unfold ZJ
  apply Finset.sum_congr rfl
  intro tau _
  exact lpTwoGhost_weight_pinned_eq E J h side tau


theorem lpTwoGhost_pinnedExp_eq
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (h : W -> Real) (side : W -> Bool)
    (F : ConfigSpace W -> Real) :
    (∑ tau : ConfigSpace W,
        F tau *
          wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
            (fun _ => 0) (lpTwoGhostPinnedConfig tau)) /
      (∑ tau : ConfigSpace W,
        wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side)
          (fun _ => 0) (lpTwoGhostPinnedConfig tau)) =
      expJ E J (lpTwoGhostMixedField h side) F := by
  rw [lpTwoGhost_pinnedPartition_eq]
  unfold expJ
  congr 1
  apply Finset.sum_congr rfl
  intro tau _
  rw [lpTwoGhost_weight_pinned_eq]



def lpReplicaSide : V ⊕ V -> Bool
  | .inl _ => false
  | .inr _ => true

def lpReplicaFieldMagnitude (hf : V -> Real) : V ⊕ V -> Real :=
  Sum.elim hf hf

@[simp] theorem lpTwoGhost_replicaMixedField_inl
    (hf : V -> Real) (x : V) :
    lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide (.inl x) =
      hf x := rfl

@[simp] theorem lpTwoGhost_replicaMixedField_inr
    (hf : V -> Real) (x : V) :
    lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide (.inr x) =
      -hf x := rfl

theorem lpTwoGhost_replicaMixedField_eq
    (hf : V -> Real) :
    lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide =
      Sum.elim hf (fun x => -hf x) := by
  funext x
  rcases x with x | x <;> rfl




theorem lpReplicaMixedField_nonneg_iff_zero
    (hf : V -> Real) (hhf : forall x, 0 <= hf x) :
    (forall w, 0 <=
      lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide w) <->
      forall x, hf x = 0 := by
  constructor
  · intro hm x
    have hp := hhf x
    have hn := hm (Sum.inr x)
    simp only [lpTwoGhost_replicaMixedField_inr] at hn
    linarith
  · intro hz w
    rcases w with x | x
    · simp [hz x]
    · simp [hz x]

end

end StatMech.Ising
