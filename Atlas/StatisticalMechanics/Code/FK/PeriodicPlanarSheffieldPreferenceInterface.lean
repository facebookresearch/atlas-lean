/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldRectanglePreference
import Code.Lattice.InterfaceConnected











open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice




theorem reachable_of_only_two_odd_degree
    {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (l r : W)
    (hl : Odd (G.degree l))
    (hodd : ∀ v, Odd (G.degree v) → v = l ∨ v = r) :
    G.Reachable l r := by
  classical
  let C := G.connectedComponentMk l
  let S := C.supp
  let H := G.induce S
  have hlS : l ∈ S := by
    exact (C.mem_supp_iff l).2 (by simp [C])
  let lS : S := ⟨l, hlS⟩
  have hdegree (v : S) : H.degree v = G.degree (v : W) := by
    have hneighbor : (H.neighborFinset v).image Subtype.val =
        G.neighborFinset (v : W) := by
      ext w
      simp only [Finset.mem_image, mem_neighborFinset]
      constructor
      · rintro ⟨u, huv, rfl⟩
        exact induce_adj.mp huv
      · intro hvw
        have hwS : w ∈ S := by
          apply (C.mem_supp_iff w).2
          have hvC : G.connectedComponentMk (v : W) = C :=
            (C.mem_supp_iff (v : W)).mp v.2
          exact (ConnectedComponent.sound hvw.reachable).symm.trans hvC
        exact ⟨⟨w, hwS⟩, induce_adj.mpr hvw, rfl⟩
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      ← hneighbor]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  have hlOdd : Odd (H.degree lS) := by
    rw [hdegree]
    exact hl
  obtain ⟨w, hwl, hwOdd⟩ :=
    H.exists_ne_odd_degree_of_exists_odd_degree lS hlOdd
  have hwOddG : Odd (G.degree (w : W)) := by
    rw [← hdegree]
    exact hwOdd
  rcases hodd (w : W) hwOddG with hw | hw
  · exact (hwl (Subtype.ext hw)).elim
  · apply ConnectedComponent.exact
    change G.connectedComponentMk l = G.connectedComponentMk r
    have hwr : r ∈ C.supp := by simpa [hw] using w.2
    simpa [C] using ((C.mem_supp_iff r).mp hwr).symm


def boolTransitionCount : List Bool → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: xs => (if a = b then 0 else 1) +
      boolTransitionCount (b :: xs)

theorem boolTransitionCount_parity (a : Bool) (xs : List Bool) :
    boolTransitionCount (a :: xs) % 2 =
      if a = (a :: xs).getLastD a then 0 else 1 := by
  induction xs generalizing a with
  | nil => simp [boolTransitionCount]
  | cons b xs ih =>
      have ihb := ih b
      rw [boolTransitionCount]
      rw [Nat.add_mod]
      simp only [List.getLastD_cons] at ihb ⊢
      generalize xs.getLastD b = z at ihb ⊢
      cases a <;> cases b <;> cases z <;>
        simp only [Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true,
          Nat.zero_mod, Nat.one_mod] at ihb ⊢ <;> omega



theorem boolTransitionCount_odd_of_ne_last (a : Bool) (xs : List Bool)
    (hne : a ≠ (a :: xs).getLastD a) :
    Odd (boolTransitionCount (a :: xs)) := by
  rw [Nat.odd_iff, boolTransitionCount_parity, if_neg hne]

def finBoolTransitionCount {n : Nat} (f : Fin (n + 1) → Bool) : Nat :=
  ∑ i : Fin n, if f i.castSucc = f i.succ then 0 else 1

theorem finBoolTransitionCount_parity {n : Nat}
    (f : Fin (n + 1) → Bool) :
    finBoolTransitionCount f % 2 =
      if f 0 = f (Fin.last n) then 0 else 1 := by
  induction n with
  | zero => simp [finBoolTransitionCount]
  | succ n ih =>
      unfold finBoolTransitionCount
      rw [Fin.sum_univ_succ, Nat.add_mod]
      simp only [← Fin.succ_castSucc]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      have iht := ih (fun i => f i.succ)
      unfold finBoolTransitionCount at iht
      dsimp only at iht
      have iht' : (∑ i : Fin n,
          if f i.castSucc.succ = f i.succ.succ then 0 else 1) % 2 =
          (if f 1 = f (Fin.last n).succ then 0 else 1) := by
        convert iht using 1
      calc
        _ = ((if f 0 = f 1 then 0 else 1) % 2 +
            (if f 1 = f (Fin.last n).succ then 0 else 1)) % 2 := by
          congr 2
        _ = _ := by
          rw [hlast]
          generalize f 0 = a
          generalize f 1 = b
          generalize f (Fin.last (n + 1)) = z
          cases a <;> cases b <;> cases z <;> simp

theorem finBoolTransitionCount_odd {n : Nat}
    (f : Fin (n + 1) → Bool) (hne : f 0 ≠ f (Fin.last n)) :
    Odd (finBoolTransitionCount f) := by
  rw [Nat.odd_iff, finBoolTransitionCount_parity, if_neg hne]


def boolTriangleTransitionCount (a b c : Bool) : Nat :=
  (if a = b then 0 else 1) + (if b = c then 0 else 1) +
    (if c = a then 0 else 1)


theorem boolTriangleTransitionCount_even (a b c : Bool) :
    Even (boolTriangleTransitionCount a b c) := by
  cases a <;> cases b <;> cases c <;>
    simp [boolTriangleTransitionCount]



abbrev PreferenceGridVertex (n m : Nat) := Fin (n + 1) × Fin (m + 1)

structure PreferenceTriangle (n m : Nat) where
  col : Fin n
  row : Fin m
  upper : Bool
deriving DecidableEq, Fintype

inductive PreferenceInterfaceNode (n m : Nat)
  | left
  | right
  | bottom
  | top
  | triangle (t : PreferenceTriangle n m)
deriving DecidableEq, Fintype

def preferenceTriangleVertex {n m : Nat} (t : PreferenceTriangle n m) :
    Fin 3 → PreferenceGridVertex n m
  | 0 => (t.col.castSucc, t.row.castSucc)
  | 1 => if t.upper then (t.col.succ, t.row.succ)
      else (t.col.succ, t.row.castSucc)
  | 2 => if t.upper then (t.col.castSucc, t.row.succ)
      else (t.col.succ, t.row.succ)

def preferenceTriangleNext : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

def preferenceTriangleSideActive {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) : Prop :=
  color (preferenceTriangleVertex t k) ≠
    color (preferenceTriangleVertex t (preferenceTriangleNext k))




def preferenceTriangleOther {n m : Nat}
    (t : PreferenceTriangle n m) : Fin 3 → PreferenceInterfaceNode n m
  | 0 =>
      if t.upper then
        .triangle ⟨t.col, t.row, false⟩
      else if h : t.row.val = 0 then
        .bottom
      else
        .triangle ⟨t.col, ⟨t.row.val - 1, by omega⟩, true⟩
  | 1 =>
      if t.upper then
        if h : t.row.val + 1 = m then
          .top
        else
          .triangle ⟨t.col, ⟨t.row.val + 1, by omega⟩, false⟩
      else if h : t.col.val + 1 = n then
        .right
      else
        .triangle ⟨⟨t.col.val + 1, by omega⟩, t.row, true⟩
  | 2 =>
      if t.upper then
        if h : t.col.val = 0 then
          .left
        else
          .triangle ⟨⟨t.col.val - 1, by omega⟩, t.row, false⟩
      else
        .triangle ⟨t.col, t.row, true⟩

def preferenceInterfaceAdj {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (u v : PreferenceInterfaceNode n m) : Prop :=
  ∃ (t : PreferenceTriangle n m) (k : Fin 3),
    preferenceTriangleSideActive color t k ∧
      ((u = .triangle t ∧ v = preferenceTriangleOther t k) ∨
       (v = .triangle t ∧ u = preferenceTriangleOther t k))

theorem preferenceTriangleOther_ne_self {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k ≠ .triangle t := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp

private theorem fin_succ_ne_self {n : Nat} (i : Fin n)
    (h : i.val + 1 < n) : (⟨i.val + 1, h⟩ : Fin n) ≠ i := by
  intro hi
  have := congrArg Fin.val hi
  change i.val + 1 = i.val at this
  omega

private theorem fin_pred_ne_self {n : Nat} (i : Fin n)
    (h0 : i.val ≠ 0) (h : i.val - 1 < n) :
    (⟨i.val - 1, h⟩ : Fin n) ≠ i := by
  intro hi
  have := congrArg Fin.val hi
  change i.val - 1 = i.val at this
  omega

private theorem fin_self_ne_succ {n : Nat} (i : Fin n)
    (h : i.val + 1 < n) : i ≠ (⟨i.val + 1, h⟩ : Fin n) :=
  (fin_succ_ne_self i h).symm

private theorem fin_self_ne_pred {n : Nat} (i : Fin n)
    (h0 : i.val ≠ 0) (h : i.val - 1 < n) :
    i ≠ (⟨i.val - 1, h⟩ : Fin n) :=
  (fin_pred_ne_self i h0 h).symm

theorem preferenceTriangleOther_zero_ne_one {n m : Nat}
    (t : PreferenceTriangle n m) :
    preferenceTriangleOther t 0 ≠ preferenceTriangleOther t 1 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp_all [fin_succ_ne_self, fin_pred_ne_self,
      fin_self_ne_succ, fin_self_ne_pred]

theorem preferenceTriangleOther_zero_ne_two {n m : Nat}
    (t : PreferenceTriangle n m) :
    preferenceTriangleOther t 0 ≠ preferenceTriangleOther t 2 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp_all [fin_succ_ne_self, fin_pred_ne_self,
      fin_self_ne_succ, fin_self_ne_pred]

theorem preferenceTriangleOther_one_ne_two {n m : Nat}
    (t : PreferenceTriangle n m) :
    preferenceTriangleOther t 1 ≠ preferenceTriangleOther t 2 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp_all [fin_succ_ne_self, fin_pred_ne_self,
      fin_self_ne_succ, fin_self_ne_pred]

theorem preferenceTriangleOther_injective {n m : Nat}
    (t : PreferenceTriangle n m) :
    Function.Injective (preferenceTriangleOther t) := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> try rfl
  · exact (preferenceTriangleOther_zero_ne_one t hkl).elim
  · exact (preferenceTriangleOther_zero_ne_two t hkl).elim
  · exact (preferenceTriangleOther_zero_ne_one t hkl.symm).elim
  · exact (preferenceTriangleOther_one_ne_two t hkl).elim
  · exact (preferenceTriangleOther_zero_ne_two t hkl.symm).elim
  · exact (preferenceTriangleOther_one_ne_two t hkl.symm).elim

theorem preferenceTriangleOther_reciprocal {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t s : PreferenceTriangle n m) (k : Fin 3)
    (h : preferenceTriangleOther t k = .triangle s) :
    ∃ l : Fin 3,
      preferenceTriangleOther s l = .triangle t ∧
      (preferenceTriangleSideActive color s l ↔
        preferenceTriangleSideActive color t k) := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] at h
  all_goals (try split_ifs at h)
  all_goals (try simp at h)
  all_goals subst s
  · refine ⟨1, ?_, ?_⟩
    · have hjm : j.val - 1 + 1 ≠ m := by omega
      have hj : (⟨j.val - 1 + 1, by omega⟩ : Fin m) = j := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleOther, hjm, hj]
    · have hj : (⟨j.val - 1, by omega⟩ : Fin m).succ = j.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Bool.false_eq_true, if_false, if_true]
      rw [hj]
      constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨2, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Fin.ext_iff]
      have hi : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = i.succ := by
        apply Fin.ext
        rfl
      rw [hi]
      constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨0, by simp [preferenceTriangleOther], ?_⟩
    simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
      preferenceTriangleNext, Bool.false_eq_true, if_true, if_false]
    constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨2, by simp [preferenceTriangleOther], ?_⟩
    simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
      preferenceTriangleNext, Bool.false_eq_true, if_true, if_false]
    constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨0, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Fin.ext_iff]
      have hj : (⟨j.val + 1, by omega⟩ : Fin (m + 1)) = j.succ := by
        apply Fin.ext
        rfl
      rw [hj]
      constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨1, ?_, ?_⟩
    · have hin : i.val - 1 + 1 ≠ n := by omega
      have hi : (⟨i.val - 1 + 1, by omega⟩ : Fin n) = i := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleOther, hin, hi]
    · have hi : (⟨i.val - 1, by omega⟩ : Fin n).succ = i.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Bool.false_eq_true, if_true, if_false]
      rw [hi]
      constructor <;> exact fun hne heq => hne heq.symm

def preferenceInterfaceGraph {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    SimpleGraph (PreferenceInterfaceNode n m) where
  Adj := preferenceInterfaceAdj color
  symm := by
    rintro u v ⟨t, k, hk, huv | hvu⟩
    · exact ⟨t, k, hk, Or.inr huv⟩
    · exact ⟨t, k, hk, Or.inl hvu⟩
  loopless := ⟨by
    rintro u ⟨t, k, _hk, huu | huu⟩
    · exact preferenceTriangleOther_ne_self t k (huu.2.symm.trans huu.1)
    · exact preferenceTriangleOther_ne_self t k (huu.2.symm.trans huu.1)⟩

theorem preferenceInterfaceAdj_triangle_iff {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (v : PreferenceInterfaceNode n m) :
    preferenceInterfaceAdj color (.triangle t) v ↔
      ∃ k : Fin 3, preferenceTriangleSideActive color t k ∧
        v = preferenceTriangleOther t k := by
  constructor
  · rintro ⟨s, k, hk, hforward | hbackward⟩
    · have hst : s = t := by simpa using hforward.1.symm
      subst s
      exact ⟨k, hk, hforward.2⟩
    · obtain ⟨l, hother, hactive⟩ :=
        preferenceTriangleOther_reciprocal color s t k hbackward.2.symm
      exact ⟨l, hactive.2 hk, hbackward.1.trans hother.symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨t, k, hk, Or.inl ⟨rfl, rfl⟩⟩

noncomputable def preferenceActiveSides {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) : Finset (Fin 3) :=
  by
    classical
    exact Finset.univ.filter (preferenceTriangleSideActive color t)

noncomputable instance preferenceInterfaceGraph_decidableAdj {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    DecidableRel (preferenceInterfaceGraph color).Adj :=
  Classical.decRel _

theorem preferenceInterface_neighborFinset_triangle {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    (preferenceInterfaceGraph color).neighborFinset (.triangle t) =
      (preferenceActiveSides color t).image (preferenceTriangleOther t) := by
  classical
  ext v
  simp only [mem_neighborFinset, Finset.mem_image, preferenceActiveSides,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change preferenceInterfaceAdj color (.triangle t) v ↔ _
  rw [preferenceInterfaceAdj_triangle_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem preferenceInterface_degree_triangle {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    (preferenceInterfaceGraph color).degree (.triangle t) =
      (preferenceActiveSides color t).card := by
  classical
  rw [← card_neighborFinset_eq_degree,
    preferenceInterface_neighborFinset_triangle]
  exact Finset.card_image_of_injective _
    (preferenceTriangleOther_injective t)

theorem preferenceActiveSides_card {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    (preferenceActiveSides color t).card =
      boolTriangleTransitionCount
        (color (preferenceTriangleVertex t 0))
        (color (preferenceTriangleVertex t 1))
        (color (preferenceTriangleVertex t 2)) := by
  classical
  unfold preferenceActiveSides
  rw [Finset.card_filter]
  rw [Fin.sum_univ_three]
  unfold preferenceTriangleSideActive preferenceTriangleNext
    boolTriangleTransitionCount
  by_cases h01 : color (preferenceTriangleVertex t 0) =
      color (preferenceTriangleVertex t 1) <;>
    by_cases h12 : color (preferenceTriangleVertex t 1) =
      color (preferenceTriangleVertex t 2) <;>
    by_cases h20 : color (preferenceTriangleVertex t 2) =
      color (preferenceTriangleVertex t 0) <;> simp_all

theorem preferenceInterface_triangle_even_degree {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    Even ((preferenceInterfaceGraph color).degree (.triangle t)) := by
  rw [preferenceInterface_degree_triangle, preferenceActiveSides_card]
  exact boolTriangleTransitionCount_even _ _ _

theorem preferenceTriangleOther_eq_left_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .left ↔
      t.upper = true ∧ t.col.val = 0 ∧ k = 2 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceTriangleOther_eq_right_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .right ↔
      t.upper = false ∧ t.col.val + 1 = n ∧ k = 1 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceTriangleOther_eq_bottom_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .bottom ↔
      t.upper = false ∧ t.row.val = 0 ∧ k = 0 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceTriangleOther_eq_top_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .top ↔
      t.upper = true ∧ t.row.val + 1 = m ∧ k = 1 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceInterfaceAdj_exterior_iff {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (side : PreferenceInterfaceNode n m)
    (hside : ∀ t : PreferenceTriangle n m, side ≠ .triangle t)
    (v : PreferenceInterfaceNode n m) :
    preferenceInterfaceAdj color side v ↔
      ∃ (t : PreferenceTriangle n m) (k : Fin 3),
        preferenceTriangleSideActive color t k ∧
        preferenceTriangleOther t k = side ∧ v = .triangle t := by
  constructor
  · rintro ⟨t, k, hk, hforward | hbackward⟩
    · exact (hside t hforward.1).elim
    · exact ⟨t, k, hk, hbackward.2.symm, hbackward.1⟩
  · rintro ⟨t, k, hk, hother, rfl⟩
    exact ⟨t, k, hk, Or.inr ⟨rfl, hother.symm⟩⟩

def preferenceLeftTriangle {n m : Nat} (hn : 0 < n) (j : Fin m) :
    PreferenceTriangle n m :=
  ⟨⟨0, hn⟩, j, true⟩

noncomputable def preferenceLeftActiveRows {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j =>
    preferenceTriangleSideActive color (preferenceLeftTriangle hn j) 2

theorem preferenceInterface_neighborFinset_left {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) :
    (preferenceInterfaceGraph color).neighborFinset (.left) =
      (preferenceLeftActiveRows color hn).image fun j =>
        .triangle (preferenceLeftTriangle hn j) := by
  classical
  ext v
  simp only [mem_neighborFinset, Finset.mem_image, preferenceLeftActiveRows,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change preferenceInterfaceAdj color .left v ↔ _
  rw [preferenceInterfaceAdj_exterior_iff color .left (by simp)]
  constructor
  · rintro ⟨t, k, hk, hother, hv⟩
    obtain ⟨hupper, hcol, rfl⟩ :=
      (preferenceTriangleOther_eq_left_iff t k).1 hother
    rcases t with ⟨i, j, upper⟩
    dsimp at hupper hcol hk hv
    subst upper
    have hi : i = (⟨0, hn⟩ : Fin n) := Fin.ext hcol
    subst i
    exact ⟨j, hk, hv.symm⟩
  · rintro ⟨j, hj, hv⟩
    exact ⟨preferenceLeftTriangle hn j, 2, hj,
      (preferenceTriangleOther_eq_left_iff _ _).2 ⟨rfl, rfl, rfl⟩,
      hv.symm⟩

theorem preferenceInterface_degree_left {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) :
    (preferenceInterfaceGraph color).degree (.left) =
      (preferenceLeftActiveRows (n := n) (m := m) color hn).card := by
  classical
  rw [← card_neighborFinset_eq_degree,
    preferenceInterface_neighborFinset_left (hn := hn)]
  apply Finset.card_image_of_injective
  intro i j hij
  have ht : preferenceLeftTriangle hn i = preferenceLeftTriangle hn j := by
    injection hij
  exact congrArg PreferenceTriangle.row ht

def preferenceLeftColor {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) : Fin (m + 1) → Bool :=
  fun j => color (⟨0, by omega⟩, j)

theorem preferenceLeftActiveRows_card {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) :
    (preferenceLeftActiveRows (n := n) (m := m) color hn).card =
      finBoolTransitionCount
        (preferenceLeftColor (n := n) (m := m) color) := by
  unfold finBoolTransitionCount
  unfold preferenceLeftActiveRows
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  have hside :
      preferenceTriangleSideActive color (preferenceLeftTriangle hn j) 2 ↔
        preferenceLeftColor color j.castSucc ≠
          preferenceLeftColor color j.succ := by
    simp only [preferenceTriangleSideActive, preferenceLeftTriangle,
      preferenceTriangleVertex, preferenceTriangleNext, preferenceLeftColor,
      Bool.true_eq_false, if_false]
    constructor <;> exact fun hne heq => hne heq.symm
  by_cases hs : preferenceTriangleSideActive color
      (preferenceLeftTriangle hn j) 2
  · have hne := hside.1 hs
    simp [hs, hne]
  · have heq : preferenceLeftColor color j.castSucc =
        preferenceLeftColor color j.succ := by
      by_contra hne
      exact hs (hside.2 hne)
    simp [hs, heq]

theorem preferenceInterface_left_odd_degree {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n)
    (hend : preferenceLeftColor (n := n) (m := m) color 0 ≠
      preferenceLeftColor (n := n) (m := m) color (Fin.last m)) :
    Odd ((preferenceInterfaceGraph color).degree (.left)) := by
  rw [preferenceInterface_degree_left (hn := hn),
    preferenceLeftActiveRows_card (hn := hn)]
  exact finBoolTransitionCount_odd _ hend

theorem preferenceInterface_exterior_degree_zero {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (side : PreferenceInterfaceNode n m)
    (hside : ∀ t : PreferenceTriangle n m, side ≠ .triangle t)
    (hinactive : ∀ (t : PreferenceTriangle n m) (k : Fin 3),
      preferenceTriangleOther t k = side →
        ¬preferenceTriangleSideActive color t k) :
    (preferenceInterfaceGraph color).degree side = 0 := by
  rw [degree_eq_zero]
  intro v hadj
  change preferenceInterfaceAdj color side v at hadj
  rw [preferenceInterfaceAdj_exterior_iff color side hside] at hadj
  obtain ⟨t, k, hk, hother, _hv⟩ := hadj
  exact hinactive t k hother hk

theorem preferenceInterface_bottom_degree_zero {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (b : Bool)
    (hbottom : ∀ i : Fin (n + 1), color (i, 0) = b) :
    (preferenceInterfaceGraph color).degree (.bottom) = 0 := by
  apply preferenceInterface_exterior_degree_zero color .bottom (by simp)
  intro t k hother
  obtain ⟨hupper, hrow, rfl⟩ :=
    (preferenceTriangleOther_eq_bottom_iff t k).1 hother
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hrow ⊢
  subst upper
  have hj : j.castSucc = (0 : Fin (m + 1)) := Fin.ext hrow
  simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
    preferenceTriangleNext, Bool.false_eq_true, if_false]
  rw [hj, hbottom, hbottom]
  simp

theorem preferenceInterface_top_degree_zero {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (b : Bool)
    (htop : ∀ i : Fin (n + 1), color (i, Fin.last m) = b) :
    (preferenceInterfaceGraph color).degree (.top) = 0 := by
  apply preferenceInterface_exterior_degree_zero color .top (by simp)
  intro t k hother
  obtain ⟨hupper, hrow, rfl⟩ :=
    (preferenceTriangleOther_eq_top_iff t k).1 hother
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hrow ⊢
  subst upper
  have hj : j.succ = Fin.last m := by
    apply Fin.ext
    exact hrow
  simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
    preferenceTriangleNext, if_true]
  rw [hj, htop, htop]
  simp

theorem preferenceInterface_left_reachable_right {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n)
    (bottomColor topColor : Bool)
    (hbottom : ∀ i : Fin (n + 1), color (i, 0) = bottomColor)
    (htop : ∀ i : Fin (n + 1),
      color (i, Fin.last m) = topColor)
    (hne : bottomColor ≠ topColor) :
    (preferenceInterfaceGraph color).Reachable (.left) (.right) := by
  classical
  apply reachable_of_only_two_odd_degree
    (preferenceInterfaceGraph color) .left .right
  · apply preferenceInterface_left_odd_degree color hn
    simpa [preferenceLeftColor, hbottom, htop] using hne
  · intro v hv
    cases v with
    | left => exact Or.inl rfl
    | right => exact Or.inr rfl
    | bottom =>
        have hz := preferenceInterface_bottom_degree_zero
          color bottomColor hbottom
        rw [hz] at hv
        simp at hv
    | top =>
        have hz := preferenceInterface_top_degree_zero color topColor htop
        rw [hz] at hv
        simp at hv
    | triangle t =>
        exact ((Nat.not_even_iff_odd.mpr hv)
          (preferenceInterface_triangle_even_degree color t)).elim

inductive PreferenceRightFlagChain {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    PreferenceTriangle n m → Prop
  | last {t : PreferenceTriangle n m} {k : Fin 3}
      (active : preferenceTriangleSideActive color t k)
      (toRight : preferenceTriangleOther t k = .right) :
      PreferenceRightFlagChain color t
  | cons {t s : PreferenceTriangle n m} {k : Fin 3}
      (active : preferenceTriangleSideActive color t k)
      (toNext : preferenceTriangleOther t k = .triangle s)
      (tail : PreferenceRightFlagChain color s) :
      PreferenceRightFlagChain color t

def PreferenceFlagCrossing {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) : Prop :=
  ∃ (firstTriangle : PreferenceTriangle n m) (firstSide : Fin 3),
    preferenceTriangleSideActive color firstTriangle firstSide ∧
    preferenceTriangleOther firstTriangle firstSide = .left ∧
    PreferenceRightFlagChain color firstTriangle

theorem preferenceRightFlagChain_of_path {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (hbottom : (preferenceInterfaceGraph color).degree (.bottom) = 0)
    (htop : (preferenceInterfaceGraph color).degree (.top) = 0) :
    ∀ {u z : PreferenceInterfaceNode n m}
      (p : (preferenceInterfaceGraph color).Walk u z),
      z = .right → p.IsPath → .left ∉ p.support →
      ∀ t : PreferenceTriangle n m, u = .triangle t →
        PreferenceRightFlagChain color t := by
  intro u z p
  induction p with
  | nil =>
      intro hz _hp _hleft t hut
      have : False := by simpa using hut.symm.trans hz
      exact this.elim
  | @cons u v w huv q ih =>
      intro hw hp hleft t hut
      subst u
      obtain ⟨k, hk, hv⟩ :=
        (preferenceInterfaceAdj_triangle_iff color t v).1 huv
      have hpq : q.IsPath := (Walk.cons_isPath_iff huv q).1 hp |>.1
      have hleftq : PreferenceInterfaceNode.left ∉ q.support := by
        intro hmem
        exact hleft (by simp [hmem])
      cases hnode : preferenceTriangleOther t k with
      | left =>
          have hvl : v = PreferenceInterfaceNode.left := hv.trans hnode
          have hmem : v ∈ q.support := by simp
          exact (hleftq (hvl ▸ hmem)).elim
      | right =>
          exact PreferenceRightFlagChain.last hk hnode
      | bottom =>
          have hiso := (degree_eq_zero
            (preferenceInterfaceGraph color) (.bottom)).1 hbottom
          exact (hiso _ ((hv.trans hnode) ▸ huv.symm)).elim
      | top =>
          have hiso := (degree_eq_zero
            (preferenceInterfaceGraph color) (.top)).1 htop
          exact (hiso _ ((hv.trans hnode) ▸ huv.symm)).elim
      | triangle s =>
          exact PreferenceRightFlagChain.cons hk hnode
            (ih hw hpq hleftq s (hv.trans hnode))

theorem preferenceFlagCrossing_of_reachable {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (hbottom : (preferenceInterfaceGraph color).degree (.bottom) = 0)
    (htop : (preferenceInterfaceGraph color).degree (.top) = 0)
    (hreach : (preferenceInterfaceGraph color).Reachable (.left) (.right)) :
    PreferenceFlagCrossing color := by
  classical
  obtain ⟨w⟩ := hreach
  rcases w.toPath with ⟨p, hp⟩
  cases p with
  | @cons u v z huv q =>
      have hpath := (Walk.cons_isPath_iff huv q).1 hp
      change preferenceInterfaceAdj color .left v at huv
      obtain ⟨t, k, hk, hother, hv⟩ :=
        (preferenceInterfaceAdj_exterior_iff color .left (by simp) v).1 huv
      refine ⟨t, k, hk, hother, ?_⟩
      exact preferenceRightFlagChain_of_path color hbottom htop q rfl
        hpath.1 hpath.2 t hv

def preferenceGridSite {n m : Nat} (x : PreferenceGridVertex n m) : Site 2
  | 0 => x.1.val
  | 1 => x.2.val

def preferenceTriangleSideTrue {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) : PreferenceGridVertex n m :=
  if color (preferenceTriangleVertex t k) = true then
    preferenceTriangleVertex t k
  else
    preferenceTriangleVertex t (preferenceTriangleNext k)

def preferenceTriangleSideFalse {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) : PreferenceGridVertex n m :=
  if color (preferenceTriangleVertex t k) = true then
    preferenceTriangleVertex t (preferenceTriangleNext k)
  else
    preferenceTriangleVertex t k

theorem preferenceTriangleSideTrueFalse_color {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hactive : preferenceTriangleSideActive color t k) :
    color (preferenceTriangleSideTrue color t k) = true ∧
      color (preferenceTriangleSideFalse color t k) = false := by
  unfold preferenceTriangleSideActive at hactive
  by_cases ha : color (preferenceTriangleVertex t k) = true
  · have hb : color (preferenceTriangleVertex t (preferenceTriangleNext k)) =
        false := by
      cases hbc : color (preferenceTriangleVertex t (preferenceTriangleNext k)) <;>
        simp_all
    simp [preferenceTriangleSideTrue, preferenceTriangleSideFalse, ha, hb]
  · have ha' : color (preferenceTriangleVertex t k) = false := by
      cases hac : color (preferenceTriangleVertex t k) <;> simp_all
    have hb : color (preferenceTriangleVertex t (preferenceTriangleNext k)) =
        true := by
      cases hbc : color (preferenceTriangleVertex t (preferenceTriangleNext k)) <;>
        simp_all
    simp [preferenceTriangleSideTrue, preferenceTriangleSideFalse, ha, ha', hb]

theorem preferenceTriangleSide_king {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    KingAdj
      (preferenceGridSite (preferenceTriangleVertex t k))
      (preferenceGridSite
        (preferenceTriangleVertex t (preferenceTriangleNext k))) := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleVertex, preferenceTriangleNext,
      preferenceGridSite, KingAdj] <;> norm_num
  all_goals
    intro h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    simp [preferenceGridSite] at h0 h1

theorem preferenceTriangleSideTrueFalse_king {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) :
    KingAdj
      (preferenceGridSite (preferenceTriangleSideTrue color t k))
      (preferenceGridSite (preferenceTriangleSideFalse color t k)) := by
  unfold preferenceTriangleSideTrue preferenceTriangleSideFalse
  split_ifs
  · exact preferenceTriangleSide_king t k
  · exact (preferenceTriangleSide_king t k).symm

theorem preferenceTriangleVertex_king_or_eq {n m : Nat}
    (t : PreferenceTriangle n m) (k l : Fin 3) :
    preferenceTriangleVertex t k = preferenceTriangleVertex t l ∨
      KingAdj
        (preferenceGridSite (preferenceTriangleVertex t k))
        (preferenceGridSite (preferenceTriangleVertex t l)) := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;> fin_cases l <;>
    simp [preferenceTriangleVertex, preferenceGridSite, KingAdj] <;> norm_num
  all_goals
    right
    intro h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    simp [preferenceGridSite] at h0 h1

theorem preferenceTriangleSideTrue_king_or_eq {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k l : Fin 3) :
    preferenceTriangleSideTrue color t k =
        preferenceTriangleSideTrue color t l ∨
      KingAdj
        (preferenceGridSite (preferenceTriangleSideTrue color t k))
        (preferenceGridSite (preferenceTriangleSideTrue color t l)) := by
  unfold preferenceTriangleSideTrue
  split_ifs <;> apply preferenceTriangleVertex_king_or_eq

theorem preferenceTriangleOther_reciprocal_vertices {n m : Nat}
    (t s : PreferenceTriangle n m) (k : Fin 3)
    (hforward : preferenceTriangleOther t k = .triangle s) :
    ∃ l : Fin 3,
      preferenceTriangleOther s l = .triangle t ∧
      preferenceTriangleVertex s l =
        preferenceTriangleVertex t (preferenceTriangleNext k) ∧
      preferenceTriangleVertex s (preferenceTriangleNext l) =
        preferenceTriangleVertex t k := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] at hforward
  all_goals (try split_ifs at hforward)
  all_goals (try simp at hforward)
  all_goals subst s
  · refine ⟨1, ?_, ?_, ?_⟩
    · have hjm : j.val - 1 + 1 ≠ m := by omega
      have hj : (⟨j.val - 1 + 1, by omega⟩ : Fin m) = j := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleOther, hjm, hj]
    · have hj : (⟨j.val - 1, by omega⟩ : Fin m).succ = j.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hj]
    · have hj : (⟨j.val - 1, by omega⟩ : Fin m).succ = j.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hj]
  · refine ⟨2, ?_, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
  · refine ⟨0, by simp [preferenceTriangleOther], ?_, ?_⟩ <;>
      simp [preferenceTriangleVertex, preferenceTriangleNext]
  · refine ⟨2, by simp [preferenceTriangleOther], ?_, ?_⟩ <;>
      simp [preferenceTriangleVertex, preferenceTriangleNext]
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
  · refine ⟨1, ?_, ?_, ?_⟩
    · have hin : i.val - 1 + 1 ≠ n := by omega
      have hi : (⟨i.val - 1 + 1, by omega⟩ : Fin n) = i := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleOther, hin, hi]
    · have hi : (⟨i.val - 1, by omega⟩ : Fin n).succ = i.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hi]
    · have hi : (⟨i.val - 1, by omega⟩ : Fin n).succ = i.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hi]

theorem preferenceTriangleSideTrue_swap {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (a b : PreferenceGridVertex n m) (h : color a ≠ color b) :
    (if color a = true then a else b) =
      (if color b = true then b else a) := by
  cases ha : color a <;> cases hb : color b <;> simp_all

theorem preferenceTriangleSideTrue_reciprocal_exists {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t s : PreferenceTriangle n m) (k : Fin 3)
    (hforward : preferenceTriangleOther t k = .triangle s)
    (hactive : preferenceTriangleSideActive color t k) :
    ∃ l : Fin 3,
      preferenceTriangleOther s l = .triangle t ∧
      preferenceTriangleSideActive color s l ∧
      preferenceTriangleSideTrue color t k =
        preferenceTriangleSideTrue color s l := by
  obtain ⟨l, hback, hfirst, hsecond⟩ :=
    preferenceTriangleOther_reciprocal_vertices t s k hforward
  obtain ⟨l', hback', hactive'⟩ :=
    preferenceTriangleOther_reciprocal color t s k hforward
  have hll : l' = l := preferenceTriangleOther_injective s
    (hback'.trans hback.symm)
  subst l'
  refine ⟨l, hback, hactive'.2 hactive, ?_⟩
  unfold preferenceTriangleSideTrue
  rw [hfirst, hsecond]
  exact preferenceTriangleSideTrue_swap color _ _ hactive

def preferenceGridBoundary {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    Set (PreferenceGridVertex n m) :=
  {x | ∃ (t : PreferenceTriangle n m) (k : Fin 3),
    preferenceTriangleSideActive color t k ∧
      x = preferenceTriangleSideTrue color t k}

def preferenceGridBoundaryGraph {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    SimpleGraph {x // x ∈ preferenceGridBoundary color} where
  Adj x y := KingAdj
    (preferenceGridSite (n := n) (m := m) x)
    (preferenceGridSite (n := n) (m := m) y)
  symm := fun _ _ h => h.symm
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

def preferenceSideBoundaryPoint {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hactive : preferenceTriangleSideActive color t k) :
    {x // x ∈ preferenceGridBoundary color} :=
  ⟨preferenceTriangleSideTrue color t k, ⟨t, k, hactive, rfl⟩⟩

theorem preferenceSideBoundaryPoint_reachable_sameTriangle {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k l : Fin 3)
    (hk : preferenceTriangleSideActive color t k)
    (hl : preferenceTriangleSideActive color t l) :
    (preferenceGridBoundaryGraph color).Reachable
      (preferenceSideBoundaryPoint color t k hk)
      (preferenceSideBoundaryPoint color t l hl) := by
  rcases preferenceTriangleSideTrue_king_or_eq color t k l with heq | hadj
  · have hpoint : preferenceSideBoundaryPoint color t k hk =
        preferenceSideBoundaryPoint color t l hl := Subtype.ext heq
    rw [hpoint]
  · apply Adj.reachable
    change KingAdj
      (preferenceGridSite (n := n) (m := m)
        (preferenceTriangleSideTrue color t k))
      (preferenceGridSite (n := n) (m := m)
      (preferenceTriangleSideTrue color t l))
    exact hadj

theorem PreferenceRightFlagChain.boundaryReachable {n m : Nat}
    {color : PreferenceGridVertex n m → Bool}
    {t : PreferenceTriangle n m}
    (chain : PreferenceRightFlagChain color t) :
    ∀ (incoming : Fin 3)
      (hincoming : preferenceTriangleSideActive color t incoming),
      ∃ (lastTriangle : PreferenceTriangle n m) (lastSide : Fin 3)
        (hlast : preferenceTriangleSideActive color lastTriangle lastSide),
        preferenceTriangleOther lastTriangle lastSide = .right ∧
        (preferenceGridBoundaryGraph color).Reachable
          (preferenceSideBoundaryPoint color t incoming hincoming)
          (preferenceSideBoundaryPoint color lastTriangle lastSide hlast) := by
  induction chain with
  | @last t k hk hright =>
      intro incoming hincoming
      exact ⟨t, k, hk, hright,
        preferenceSideBoundaryPoint_reachable_sameTriangle
          color t incoming k hincoming hk⟩
  | @cons t s k hk hnext tail ih =>
      intro incoming hincoming
      obtain ⟨l, hback, hl, heq⟩ :=
        preferenceTriangleSideTrue_reciprocal_exists
          color t s k hnext hk
      obtain ⟨lastTriangle, lastSide, hlast, hright, htail⟩ := ih l hl
      have hlocal := preferenceSideBoundaryPoint_reachable_sameTriangle
        color t incoming k hincoming hk
      have hbridge : (preferenceGridBoundaryGraph color).Reachable
          (preferenceSideBoundaryPoint color t k hk)
          (preferenceSideBoundaryPoint color s l hl) := by
        have hp : preferenceSideBoundaryPoint color t k hk =
            preferenceSideBoundaryPoint color s l hl := Subtype.ext heq
        rw [hp]
      exact ⟨lastTriangle, lastSide, hlast, hright,
        hlocal.trans (hbridge.trans htail)⟩

theorem preferenceTriangleSideTrue_col_zero_of_left {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hleft : preferenceTriangleOther t k = .left) :
    (preferenceTriangleSideTrue color t k).1.val = 0 := by
  obtain ⟨hupper, hcol, rfl⟩ :=
    (preferenceTriangleOther_eq_left_iff t k).1 hleft
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hcol ⊢
  subst upper
  unfold preferenceTriangleSideTrue
  simp only [preferenceTriangleVertex, preferenceTriangleNext,
    Bool.true_eq_false, if_false]
  split_ifs <;> simpa using hcol

theorem preferenceTriangleSideTrue_col_right_of_right {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hright : preferenceTriangleOther t k = .right) :
    (preferenceTriangleSideTrue color t k).1.val = n := by
  obtain ⟨hupper, hcol, rfl⟩ :=
    (preferenceTriangleOther_eq_right_iff t k).1 hright
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hcol ⊢
  subst upper
  unfold preferenceTriangleSideTrue
  simp only [preferenceTriangleVertex, preferenceTriangleNext,
    Bool.false_eq_true, if_false]
  split_ifs <;> simpa using hcol

theorem preferenceGridBoundary_color_data {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (x : PreferenceGridVertex n m) (hx : x ∈ preferenceGridBoundary color) :
    color x = true ∧
      ∃ y : PreferenceGridVertex n m,
        KingAdj (preferenceGridSite x) (preferenceGridSite y) ∧
        color y = false := by
  obtain ⟨t, k, hk, rfl⟩ := hx
  obtain ⟨htrue, hfalse⟩ := preferenceTriangleSideTrueFalse_color color t k hk
  exact ⟨htrue, preferenceTriangleSideFalse color t k,
    preferenceTriangleSideTrueFalse_king color t k, hfalse⟩

theorem preferenceGridBoundary_reachable_left_right_of_flagCrossing
    {n m : Nat} (color : PreferenceGridVertex n m → Bool)
    (hcross : PreferenceFlagCrossing color) :
    ∃ (leftPoint rightPoint : {x // x ∈ preferenceGridBoundary color}),
      leftPoint.val.1.val = 0 ∧ rightPoint.val.1.val = n ∧
      (preferenceGridBoundaryGraph color).Reachable leftPoint rightPoint := by
  obtain ⟨t, k, hk, hleft, chain⟩ := hcross
  obtain ⟨lastTriangle, lastSide, hlast, hright, hreach⟩ :=
    chain.boundaryReachable k hk
  exact ⟨preferenceSideBoundaryPoint color t k hk,
    preferenceSideBoundaryPoint color lastTriangle lastSide hlast,
    preferenceTriangleSideTrue_col_zero_of_left color t k hleft,
    preferenceTriangleSideTrue_col_right_of_right
      color lastTriangle lastSide hright,
    hreach⟩

theorem preferenceGridSite_injective {n m : Nat} :
    Function.Injective (preferenceGridSite : PreferenceGridVertex n m → Site 2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  apply Prod.ext
  · apply Fin.ext
    have h0 := congrFun h (0 : Fin 2)
    simp [preferenceGridSite] at h0
    exact_mod_cast h0
  · apply Fin.ext
    have h1 := congrFun h (1 : Fin 2)
    simp [preferenceGridSite] at h1
    exact_mod_cast h1

def preferenceGridRectangle (n m : Nat) : Set (Site 2) :=
  preferenceGridSite '' (Set.univ : Set (PreferenceGridVertex n m))

def preferenceGridTrueSet {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) : Set (Site 2) :=
  preferenceGridSite '' {x | color x = true}



def preferenceInnerBoundary (rectangle X : Set (Site 2)) : Set (Site 2) :=
  {x | x ∈ rectangle ∧ x ∈ X ∧
    ∃ y ∈ rectangle, KingAdj x y ∧ y ∉ X}


def preferenceBoundaryGraph (rectangle X : Set (Site 2)) :
    SimpleGraph {x // x ∈ preferenceInnerBoundary rectangle X} where
  Adj x y := KingAdj (x : Site 2) (y : Site 2)
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem preferenceGridBoundary_site_mem_inner {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    ∀ x : {x // x ∈ preferenceGridBoundary color},
      preferenceGridSite (n := n) (m := m) (x : PreferenceGridVertex n m) ∈
        preferenceInnerBoundary
        (preferenceGridRectangle n m) (preferenceGridTrueSet color) := by
  intro x
  have hdata := preferenceGridBoundary_color_data color x x.2
  obtain ⟨htrue, y, hxy, hfalse⟩ := hdata
  refine ⟨?_, ?_, preferenceGridSite y, ?_, hxy, ?_⟩
  · exact ⟨x, Set.mem_univ _, rfl⟩
  · exact ⟨x, htrue, rfl⟩
  · exact ⟨y, Set.mem_univ _, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hzy : z = y := preferenceGridSite_injective heq
    subst z
    simp_all

def preferenceGridBoundaryToSite {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    {x // x ∈ preferenceGridBoundary color} →
      {z // z ∈ preferenceInnerBoundary
        (preferenceGridRectangle n m) (preferenceGridTrueSet color)} :=
  fun x => ⟨preferenceGridSite (n := n) (m := m)
      (x : PreferenceGridVertex n m),
    preferenceGridBoundary_site_mem_inner (n := n) (m := m) color x⟩

def preferenceGridBoundaryGraphHom {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    preferenceGridBoundaryGraph color →g
      preferenceBoundaryGraph
        (preferenceGridRectangle n m) (preferenceGridTrueSet color) where
  toFun := preferenceGridBoundaryToSite (n := n) (m := m) color
  map_rel' := by
    intro x y hxy
    unfold preferenceBoundaryGraph preferenceGridBoundaryToSite
    change KingAdj
      (preferenceGridSite (n := n) (m := m) x)
      (preferenceGridSite (n := n) (m := m) y)
    exact hxy



theorem walk_exists_last_mem_adj_notMem
    {W : Type*} {G : SimpleGraph W} (Y : Set W) {l r : W}
    (p : G.Walk l r) (hl : l ∈ Y) (hr : r ∉ Y) :
    ∃ x y : W, x ∈ p.support ∧ y ∈ p.support ∧
      G.Adj x y ∧ x ∈ Y ∧ y ∉ Y := by
  induction p with
  | nil => exact (hr hl).elim
  | @cons l m r hlm q ih =>
      by_cases hm : m ∈ Y
      · obtain ⟨x, y, hxq, hyq, hxy, hxY, hyY⟩ := ih hm hr
        exact ⟨x, y, by simp [hxq], by simp [hyq], hxy, hxY, hyY⟩
      · exact ⟨l, m, by simp, by simp, hlm, hl, hm⟩



theorem exists_preference_witness_of_boundary_walk
    (rectangle X Y : Set (Site 2))
    {l r : {x // x ∈ preferenceInnerBoundary rectangle X}}
    (p : (preferenceBoundaryGraph rectangle X).Walk l r)
    (hl : (l : Site 2) ∈ Y) (hr : (r : Site 2) ∉ Y) :
    ∃ x ∈ rectangle, x ∈ X ∧ x ∈ Y ∧
      (∃ x' ∈ rectangle, KingAdj x x' ∧ x' ∉ X) ∧
      (∃ x'' ∈ rectangle, KingAdj x x'' ∧ x'' ∉ Y) := by
  let Yb : Set {x // x ∈ preferenceInnerBoundary rectangle X} :=
    {x | (x : Site 2) ∈ Y}
  obtain ⟨x, y, _hxp, _hyp, hxy, hxY, hyY⟩ :=
    walk_exists_last_mem_adj_notMem Yb p hl hr
  obtain ⟨hxRect, hxX, x', hx'Rect, hxx', hx'X⟩ := x.2
  exact ⟨x, hxRect, hxX, hxY, ⟨x', hx'Rect, hxx', hx'X⟩,
    ⟨y, y.2.1, hxy, hyY⟩⟩

theorem exists_preference_witness_of_grid_boundary {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n)
    (hbottom : ∀ i : Fin (n + 1), color (i, 0) = true)
    (htop : ∀ i : Fin (n + 1), color (i, Fin.last m) = false)
    (Y : Set (Site 2))
    (hYleft : ∀ x : {x // x ∈ preferenceGridBoundary color},
      x.val.1.val = 0 →
        (preferenceGridBoundaryToSite color x : Site 2) ∈ Y)
    (hYright : ∀ x : {x // x ∈ preferenceGridBoundary color},
      x.val.1.val = n →
        (preferenceGridBoundaryToSite color x : Site 2) ∉ Y) :
    ∃ x ∈ preferenceGridRectangle n m,
      x ∈ preferenceGridTrueSet color ∧ x ∈ Y ∧
      (∃ x' ∈ preferenceGridRectangle n m, KingAdj x x' ∧
        x' ∉ preferenceGridTrueSet color) ∧
      (∃ x'' ∈ preferenceGridRectangle n m, KingAdj x x'' ∧ x'' ∉ Y) := by
  have hreach := preferenceInterface_left_reachable_right color hn true false
    hbottom htop (by decide)
  have hbottomZero := preferenceInterface_bottom_degree_zero color true hbottom
  have htopZero := preferenceInterface_top_degree_zero color false htop
  have hflag := preferenceFlagCrossing_of_reachable
    color hbottomZero htopZero hreach
  obtain ⟨leftPoint, rightPoint, hleft, hright, hgridReach⟩ :=
    preferenceGridBoundary_reachable_left_right_of_flagCrossing color hflag
  have hsiteReach := hgridReach.map (preferenceGridBoundaryGraphHom color)
  obtain ⟨p⟩ := hsiteReach
  exact exists_preference_witness_of_boundary_walk
    (preferenceGridRectangle n m) (preferenceGridTrueSet color) Y p
    (hYleft leftPoint hleft) (hYright rightPoint hright)

end StatMech.FK.PeriodicPlanar
