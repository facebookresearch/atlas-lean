/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFiveCurrentPairing









open Finset

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

abbrev LPReplicaCurrentVertex (V : Type*) := (V ⊕ V) ⊕ Bool


def lpReplicaCurrentReflect : Equiv.Perm (LPReplicaCurrentVertex V) where
  toFun
    | .inl (.inl x) => .inl (.inr x)
    | .inl (.inr x) => .inl (.inl x)
    | .inr b => .inr (!b)
  invFun
    | .inl (.inl x) => .inl (.inr x)
    | .inl (.inr x) => .inl (.inl x)
    | .inr b => .inr (!b)
  left_inv := by
    intro x
    rcases x with (x | b)
    · rcases x with x | x <;> rfl
    · simp
  right_inv := by
    intro x
    rcases x with (x | b)
    · rcases x with x | x <;> rfl
    · simp

@[simp] theorem lpReplicaCurrentReflect_left (x : V) :
    lpReplicaCurrentReflect (.inl (.inl x)) = .inl (.inr x) := rfl

@[simp] theorem lpReplicaCurrentReflect_right (x : V) :
    lpReplicaCurrentReflect (.inl (.inr x)) = .inl (.inl x) := rfl

@[simp] theorem lpReplicaCurrentReflect_ghost (b : Bool) :
    lpReplicaCurrentReflect (.inr b : LPReplicaCurrentVertex V) =
      .inr (!b) := rfl

theorem lpReplicaCurrentReflect_involutive :
    Function.Involutive (lpReplicaCurrentReflect (V := V)) := by
  intro x
  rcases x with (x | b)
  · rcases x with x | x <;> rfl
  · simp


def lpReplicaCurrentRel
    (G : SimpleGraph V) (sites : I -> V) :
    LPReplicaCurrentVertex V -> LPReplicaCurrentVertex V -> Prop
  | .inl (.inl x), .inl (.inl y) => G.Adj x y
  | .inl (.inr x), .inl (.inr y) => G.Adj x y
  | .inl (.inl x), .inl (.inr y) => ∃ i, sites i = x ∧ sites i = y
  | .inl (.inr x), .inl (.inl y) => ∃ i, sites i = x ∧ sites i = y
  | .inl (.inl _), .inr false => True
  | .inr false, .inl (.inl _) => True
  | .inl (.inr _), .inr true => True
  | .inr true, .inl (.inr _) => True
  | _, _ => False


def lpReplicaCurrentGraph
    (G : SimpleGraph V) (sites : I -> V) :
    SimpleGraph (LPReplicaCurrentVertex V) :=
  SimpleGraph.fromRel (lpReplicaCurrentRel G sites)

theorem lpReplicaCurrentRel_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (x y : LPReplicaCurrentVertex V) :
    lpReplicaCurrentRel G sites (lpReplicaCurrentReflect x)
        (lpReplicaCurrentReflect y) <->
      lpReplicaCurrentRel G sites x y := by
  rcases x with (x | b) <;> rcases y with (y | c)
  · rcases x with x | x <;> rcases y with y | y <;>
      simp only [lpReplicaCurrentReflect_left, lpReplicaCurrentReflect_right,
        lpReplicaCurrentRel]
  · rcases x with x | x <;> cases c <;>
      simp [lpReplicaCurrentRel]
  · cases b <;> rcases y with y | y <;>
      simp [lpReplicaCurrentRel]
  · cases b <;> cases c <;> simp [lpReplicaCurrentRel]

theorem lpReplicaCurrentGraph_adj_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (x y : LPReplicaCurrentVertex V) :
    (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) <->
      (lpReplicaCurrentGraph G sites).Adj x y := by
  unfold lpReplicaCurrentGraph
  rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel⟩
    refine ⟨fun hxy => hne (congrArg lpReplicaCurrentReflect hxy), ?_⟩
    rcases hrel with hrel | hrel
    · exact Or.inl ((lpReplicaCurrentRel_reflect G sites x y).mp hrel)
    · exact Or.inr ((lpReplicaCurrentRel_reflect G sites y x).mp hrel)
  · rintro ⟨hne, hrel⟩
    refine ⟨lpReplicaCurrentReflect.injective.ne hne, ?_⟩
    rcases hrel with hrel | hrel
    · exact Or.inl ((lpReplicaCurrentRel_reflect G sites x y).mpr hrel)
    · exact Or.inr ((lpReplicaCurrentRel_reflect G sites y x).mpr hrel)


def lpReplicaCurrentCoupling
    (J : Sym2 V -> Real) (hf : V -> Real) (r : Real) :
    Sym2 (LPReplicaCurrentVertex V) -> Real :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | .inl (.inl x), .inl (.inl y) => J s(x, y)
    | .inl (.inr x), .inl (.inr y) => J s(x, y)
    | .inl (.inl _), .inl (.inr _) => r
    | .inl (.inr _), .inl (.inl _) => r
    | .inl (.inl x), .inr false => hf x
    | .inr false, .inl (.inl x) => hf x
    | .inl (.inr x), .inr true => hf x
    | .inr true, .inl (.inr x) => hf x
    | _, _ => 0,
    by
      intro a b
      rcases a with (a | g) <;> rcases b with (b | h)
      · rcases a with a | a <;> rcases b with b | b <;>
          simp only [] <;> rw [Sym2.eq_swap]
      · rcases a with a | a <;> cases h <;> simp
      · cases g <;> rcases b with b | b <;> simp
      · cases g <;> cases h <;> simp⟩

theorem lpReplicaCurrentCoupling_reflect
    (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (e : Sym2 (LPReplicaCurrentVertex V)) :
    lpReplicaCurrentCoupling J hf r
        (Sym2.map lpReplicaCurrentReflect e) =
      lpReplicaCurrentCoupling J hf r e := by
  induction e with
  | h a b =>
      rcases a with (a | g) <;> rcases b with (b | h)
      · rcases a with a | a <;> rcases b with b | b <;> rfl
      · rcases a with a | a <;> cases h <;> rfl
      · cases g <;> rcases b with b | b <;> rfl
      · cases g <;> cases h <;> rfl

omit [Fintype V] [DecidableEq V] in
theorem lpReplicaCurrentCoupling_nonneg
    (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hJ : ∀ e, 0 <= J e) (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (e : Sym2 (LPReplicaCurrentVertex V)) :
    0 <= lpReplicaCurrentCoupling J hf r e := by
  induction e with
  | h a b =>
      rcases a with (a | g) <;> rcases b with (b | h)
      · rcases a with a | a <;> rcases b with b | b
        · exact hJ _
        · exact hr
        · exact hr
        · exact hJ _
      · rcases a with a | a <;> cases h <;>
          simp only [lpReplicaCurrentCoupling, Sym2.lift_mk]
        · exact hhf _
        · exact le_rfl
        · exact le_rfl
        · exact hhf _
      · cases g <;> rcases b with b | b <;>
          simp only [lpReplicaCurrentCoupling, Sym2.lift_mk]
        · exact hhf _
        · exact le_rfl
        · exact le_rfl
        · exact hhf _
      · cases g <;> cases h <;> exact le_rfl

def lpReplicaCurrentLeft (sites : I -> V) (i : I) :
    LPReplicaCurrentVertex V := .inl (.inl (sites i))

def lpReplicaCurrentRight (sites : I -> V) (i : I) :
    LPReplicaCurrentVertex V := .inl (.inr (sites i))

def lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V := .inr false
def lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V := .inr true



theorem lpReplicaCurrentGraph_adj_left_right_iff
    (G : SimpleGraph V) (sites : I -> V) (x y : V) :
    (lpReplicaCurrentGraph G sites).Adj
        (.inl (.inl x)) (.inl (.inr y)) <->
      ∃ i, sites i = x ∧ sites i = y := by
  unfold lpReplicaCurrentGraph
  rw [SimpleGraph.fromRel_adj]
  simp only [lpReplicaCurrentRel]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · obtain ⟨i, hy, hx⟩ := h
      exact ⟨i, hx, hy⟩
  · intro h
    exact ⟨by simp, Or.inl h⟩


def lpReplicaCurrentSeamEdge (sites : I -> V) (i : I) :
    Sym2 (LPReplicaCurrentVertex V) :=
  s(lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i)

theorem lpReplicaCurrentSeamEdge_injective
    (sites : I -> V) (hsite : Function.Injective sites) :
    Function.Injective (lpReplicaCurrentSeamEdge sites) := by
  intro i j h
  unfold lpReplicaCurrentSeamEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact hsite (Sum.inl.inj (Sum.inl.inj h.1))
  · exact absurd h.1 (by simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])

theorem lpReplicaCurrentSeamEdge_mem
    (G : SimpleGraph V) (sites : I -> V) (i : I) :
    lpReplicaCurrentSeamEdge sites i ∈
      (lpReplicaCurrentGraph G sites).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  unfold lpReplicaCurrentSeamEdge
  rw [SimpleGraph.mem_edgeSet]
  unfold lpReplicaCurrentLeft lpReplicaCurrentRight
  rw [lpReplicaCurrentGraph_adj_left_right_iff]
  exact ⟨i, rfl, rfl⟩


def lpReplicaCurrent_reflectedMatchingCut
    (G : SimpleGraph V) (J : Sym2 V -> Real) (hf : V -> Real)
    (sites : I -> V) (r : Real) :
    LPReflectedMatchingCut
      (lpReplicaCurrentGraph G sites)
      (lpReplicaCurrentCoupling J hf r)
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 where
  reflect := lpReplicaCurrentReflect
  involutive := lpReplicaCurrentReflect_involutive
  reflect_left := fun _ => rfl
  reflect_right := fun _ => rfl
  reflect_g0 := rfl
  reflect_g1 := rfl
  adj_iff := lpReplicaCurrentGraph_adj_reflect G sites
  coupling := lpReplicaCurrentCoupling_reflect J hf r

end

end StatMech.Ising
