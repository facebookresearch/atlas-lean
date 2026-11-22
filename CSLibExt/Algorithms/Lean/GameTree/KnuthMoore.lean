/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.AlphaBeta

/-!
# Alpha-beta on a perfectly ordered uniform tree (Knuth and Moore)

Knuth and Moore (*An analysis of alpha-beta pruning*, Artificial Intelligence 6 (1975)) count the
leaves alpha-beta evaluates when the moves are perfectly ordered: on a uniform tree of branching
factor `k` and depth `d` in which the first move at every position is a best one, procedure F2
evaluates exactly `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` leaves. This file proves that count for the
Atlas `alphaBeta` (one time unit per leaf evaluated), with the full window `[⊥, ⊤]`.

* `Uniform k d t`: every inner node of `t` has exactly `k` children and every leaf is at depth `d`.
* `PerfectlyOrdered p t`: at every inner node of `t` the first child attains the node's minimax
  value for the player to move there (`p` at the root, alternating below).
* `alphaBeta_leafCount_perfect`: if `t` is uniform and perfectly ordered and its minimax value lies
  strictly between `⊥` and `⊤`, then
  `(alphaBeta p ⊥ ⊤ t).time = k ^ ((d + 1) / 2) + k ^ (d / 2) - 1`.

Ties between leaf values are allowed: the cutoff test `b ≤ a` of `alphaBeta` already fires on
equality. The hypothesis `minimax p t < ⊤` (and `⊥ < minimax p t`) is needed: a root value equal to
`⊤` makes the maximizer cut off after its first move.

## Proof

The count splits by Knuth and Moore's node types, each proved by induction on the depth for a
window `a < b`:

* a *cut* node (the value already fails the window, `minimax false t ≤ a` for the minimizer,
  `b ≤ minimax true t` for the maximizer) evaluates only its first child, an *all* node, then cuts:
  `cutLeaves k d = k ^ (d / 2)` leaves (`alphaBeta_time_cut_false`, `alphaBeta_time_cut_true`);
* an *all* node (`minimax true t ≤ a`, or `b ≤ minimax false t`) evaluates every child, each a
  cut node with the same window: `allLeaves k d = k ^ ((d + 1) / 2)` leaves;
* a *principal* node (value strictly inside the window) evaluates its first child as a principal
  node, which returns the value exactly, and the remaining `k - 1` children as cut nodes:
  `pvLeaves k d = allLeaves k d + cutLeaves k d - 1` leaves (`alphaBeta_time_pv`).

## Scope

This file proves the exact count for alpha-beta. Knuth and Moore's matching lower bound, that every
algorithm that determines the minimax value reads at least this many leaves, is proved for adaptive
leaf-query algorithms in `CSLibExt.Algorithms.Lean.GameTree.KnuthMooreLowerBound`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

open Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-- `Uniform k d t`: every inner node of `t` has exactly `k` children and every leaf of `t` is at
depth `d`. -/
inductive Uniform (k : ℕ) : ℕ → GameTree α → Prop
  | leaf (x : α) : Uniform k 0 (.leaf x)
  | node {d : ℕ} {ts : List (GameTree α)} (hlen : ts.length = k) (hts : ∀ t ∈ ts, Uniform k d t) :
      Uniform k (d + 1) (.node ts)

/-- Leaves alpha-beta evaluates at a cut node of height `d`: `k ^ ⌊d / 2⌋`. -/
def cutLeaves (k d : ℕ) : ℕ := k ^ (d / 2)

/-- Leaves alpha-beta evaluates at an all node of height `d`: `k ^ ⌈d / 2⌉`. -/
def allLeaves (k d : ℕ) : ℕ := k ^ ((d + 1) / 2)

/-- The Knuth–Moore count at a principal node of height `d`: `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1`. -/
def pvLeaves (k d : ℕ) : ℕ := k ^ ((d + 1) / 2) + k ^ (d / 2) - 1

theorem cutLeaves_zero (k : ℕ) : cutLeaves k 0 = 1 := by simp [cutLeaves]

theorem allLeaves_zero (k : ℕ) : allLeaves k 0 = 1 := by simp [allLeaves]

theorem pvLeaves_zero (k : ℕ) : pvLeaves k 0 = 1 := by simp [pvLeaves]

theorem cutLeaves_succ (k d : ℕ) : cutLeaves k (d + 1) = allLeaves k d := rfl

theorem allLeaves_succ (k d : ℕ) : allLeaves k (d + 1) = k * cutLeaves k d := by
  rw [allLeaves, cutLeaves, show (d + 1 + 1) / 2 = d / 2 + 1 by omega, Nat.pow_succ,
    Nat.mul_comm]

/-- The principal-node recurrence: `pvLeaves (j + 1) (d + 1) = pvLeaves (j + 1) d + j *
cutLeaves (j + 1) d`. -/
theorem pvLeaves_succ_succ (j d : ℕ) :
    pvLeaves (j + 1) (d + 1) = pvLeaves (j + 1) d + j * cutLeaves (j + 1) d := by
  have hA : 1 ≤ (j + 1) ^ ((d + 1) / 2) := Nat.one_le_pow _ _ (Nat.succ_pos j)
  have hC : 1 ≤ (j + 1) ^ (d / 2) := Nat.one_le_pow _ _ (Nat.succ_pos j)
  have h := allLeaves_succ (j + 1) d
  simp only [pvLeaves, allLeaves, cutLeaves] at h ⊢
  rw [h, Nat.add_mul, Nat.one_mul]
  omega

/-! ## Minimax facts -/

section Minimax

variable [LinearOrder α] [BoundedOrder α]

/-- `PerfectlyOrdered p t`: at every inner node of `t` the first child attains the node's minimax
value for the player to move there (`p` at the root). A node without moves is not perfectly
ordered. -/
inductive PerfectlyOrdered : Bool → GameTree α → Prop
  | leaf (p : Bool) (x : α) : PerfectlyOrdered p (.leaf x)
  | node {p : Bool} {t : GameTree α} {ts : List (GameTree α)}
      (hfirst : minimax p (.node (t :: ts)) = minimax (!p) t)
      (hchildren : ∀ u ∈ t :: ts, PerfectlyOrdered (!p) u) :
      PerfectlyOrdered p (.node (t :: ts))

theorem minimaxList_true_le_iff {a : α} :
    ∀ {ts : List (GameTree α)}, minimaxList true ts ≤ a ↔ ∀ u ∈ ts, minimax false u ≤ a
  | [] => by simp [minimaxList]
  | t :: ts => by simp [minimaxList, minimaxList_true_le_iff]

theorem le_minimaxList_false_iff {b : α} :
    ∀ {ts : List (GameTree α)}, b ≤ minimaxList false ts ↔ ∀ u ∈ ts, b ≤ minimax true u
  | [] => by simp [minimaxList]
  | t :: ts => by simp [minimaxList, le_minimaxList_false_iff]

/-! ## Scans over children that all fail the window -/

/-- If every child fails low (`minimax false u ≤ a`), the maximizer's scan keeps `a`, never cuts,
and evaluates every child with the window `[a, b]`. -/
theorem alphaBetaList_true_time_of_le {a b : α} (hab : a < b) {c : ℕ} :
    ∀ {us : List (GameTree α)}, (∀ u ∈ us, minimax false u ≤ a) →
      (∀ u ∈ us, (alphaBeta false a b u).time = c) →
      (alphaBetaList true a b us).time = us.length * c
  | [], _, _ => by simp [alphaBetaList]
  | u :: us, hle, htime => by
      have hv : (alphaBeta false a b u).ret ≤ a :=
        alphaBeta_le_of_minimax_le hab (hle u List.mem_cons_self)
      have ih := alphaBetaList_true_time_of_le hab (us := us)
        (fun w hw => hle w (List.mem_cons_of_mem u hw))
        (fun w hw => htime w (List.mem_cons_of_mem u hw))
      simp only [alphaBetaList, TimeM.time_bind, max_eq_left hv, not_le.2 hab, ite_false]
      rw [htime u List.mem_cons_self, ih, List.length_cons, Nat.add_mul, Nat.one_mul,
        Nat.add_comm]

/-- If every child fails high (`b ≤ minimax true u`), the minimizer's scan keeps `b`, never cuts,
and evaluates every child with the window `[a, b]`. -/
theorem alphaBetaList_false_time_of_le {a b : α} (hab : a < b) {c : ℕ} :
    ∀ {us : List (GameTree α)}, (∀ u ∈ us, b ≤ minimax true u) →
      (∀ u ∈ us, (alphaBeta true a b u).time = c) →
      (alphaBetaList false a b us).time = us.length * c
  | [], _, _ => by simp [alphaBetaList]
  | u :: us, hle, htime => by
      have hv : b ≤ (alphaBeta true a b u).ret :=
        le_alphaBeta_of_le_minimax hab (hle u List.mem_cons_self)
      have ih := alphaBetaList_false_time_of_le hab (us := us)
        (fun w hw => hle w (List.mem_cons_of_mem u hw))
        (fun w hw => htime w (List.mem_cons_of_mem u hw))
      simp only [alphaBetaList, TimeM.time_bind, min_eq_left hv, not_le.2 hab, ite_false]
      rw [htime u List.mem_cons_self, ih, List.length_cons, Nat.add_mul, Nat.one_mul,
        Nat.add_comm]

/-! ## Cut and all nodes -/

/-- Cut and all nodes, by induction on the height: for a window `a < b`, an all node evaluates
`allLeaves k d` leaves and a cut node `cutLeaves k d`. -/
theorem alphaBeta_time_cut_all (k : ℕ) : ∀ (d : ℕ) (t : GameTree α) (a b : α),
    Uniform k d t → a < b →
    (PerfectlyOrdered true t → minimax true t ≤ a →
      (alphaBeta true a b t).time = allLeaves k d) ∧
    (PerfectlyOrdered false t → b ≤ minimax false t →
      (alphaBeta false a b t).time = allLeaves k d) ∧
    (PerfectlyOrdered false t → minimax false t ≤ a →
      (alphaBeta false a b t).time = cutLeaves k d) ∧
    (PerfectlyOrdered true t → b ≤ minimax true t →
      (alphaBeta true a b t).time = cutLeaves k d)
  | 0, t, a, b, hu, _ => by
      cases hu
      simp [alphaBeta, allLeaves, cutLeaves]
  | d + 1, t, a, b, hu, hab => by
      cases hu with
      | node hlen hts =>
      rename_i ts
      have ih := fun u (hu : u ∈ ts) => alphaBeta_time_cut_all k d u a b (hts u hu) hab
      refine ⟨fun hpo hle => ?_, fun hpo hle => ?_, fun hpo hle => ?_, fun hpo hle => ?_⟩
      · -- all node, maximizer: every child is a cut node of the minimizer
        cases hpo with
        | node hfirst hchildren =>
        rename_i u us
        simp only [minimax, minimaxList_true_le_iff] at hle
        simp only [alphaBeta]
        rw [alphaBetaList_true_time_of_le hab hle
          (fun w hw => (ih w hw).2.2.1 (hchildren w hw) (hle w hw)), hlen, allLeaves_succ]
      · -- all node, minimizer: every child is a cut node of the maximizer
        cases hpo with
        | node hfirst hchildren =>
        rename_i u us
        simp only [minimax, le_minimaxList_false_iff] at hle
        simp only [alphaBeta]
        rw [alphaBetaList_false_time_of_le hab hle
          (fun w hw => (ih w hw).2.2.2 (hchildren w hw) (hle w hw)), hlen, allLeaves_succ]
      · -- cut node, minimizer: the first child is an all node that fails low, then a cutoff
        cases hpo with
        | node hfirst hchildren =>
        rename_i u us
        have hu : minimax true u ≤ a := hfirst ▸ hle
        have htu := (ih u List.mem_cons_self).1 (hchildren u List.mem_cons_self) hu
        have hv : (alphaBeta true a b u).ret ≤ a := alphaBeta_le_of_minimax_le hab hu
        have hc : min b (alphaBeta true a b u).ret ≤ a := (min_le_right _ _).trans hv
        simp only [alphaBeta, alphaBetaList, TimeM.time_bind, hc, ite_true, TimeM.time_pure, htu,
          cutLeaves_succ]
        rfl
      · -- cut node, maximizer: the first child is an all node that fails high, then a cutoff
        cases hpo with
        | node hfirst hchildren =>
        rename_i u us
        have hu : b ≤ minimax false u := hfirst ▸ hle
        have htu := (ih u List.mem_cons_self).2.1 (hchildren u List.mem_cons_self) hu
        have hv : b ≤ (alphaBeta false a b u).ret := le_alphaBeta_of_le_minimax hab hu
        have hc : b ≤ max a (alphaBeta false a b u).ret := hv.trans (le_max_right _ _)
        simp only [alphaBeta, alphaBetaList, TimeM.time_bind, hc, ite_true, TimeM.time_pure, htu,
          cutLeaves_succ]
        rfl

/-- **Cut node of the minimizer.** -/
theorem alphaBeta_time_cut_false {k d : ℕ} {t : GameTree α} {a b : α} (hu : Uniform k d t)
    (hpo : PerfectlyOrdered false t) (hab : a < b) (hle : minimax false t ≤ a) :
    (alphaBeta false a b t).time = cutLeaves k d :=
  (alphaBeta_time_cut_all k d t a b hu hab).2.2.1 hpo hle

/-- **Cut node of the maximizer.** -/
theorem alphaBeta_time_cut_true {k d : ℕ} {t : GameTree α} {a b : α} (hu : Uniform k d t)
    (hpo : PerfectlyOrdered true t) (hab : a < b) (hle : b ≤ minimax true t) :
    (alphaBeta true a b t).time = cutLeaves k d :=
  (alphaBeta_time_cut_all k d t a b hu hab).2.2.2 hpo hle

/-! ## Principal nodes -/

/-- **Principal node.** A uniform perfectly ordered tree whose value lies strictly inside the
window `[a, b]` costs `pvLeaves k d` leaves. -/
theorem alphaBeta_time_pv (k : ℕ) : ∀ (d : ℕ) (p : Bool) (t : GameTree α) (a b : α),
    Uniform k d t → PerfectlyOrdered p t → a < minimax p t → minimax p t < b →
    (alphaBeta p a b t).time = pvLeaves k d
  | 0, p, t, a, b, hu, _, _, _ => by
      cases hu
      simp [alphaBeta, pvLeaves]
  | d + 1, p, t, a, b, hu, hpo, ha, hb => by
      cases hu with
      | node hlen hts =>
      rename_i ts
      cases hpo with
      | node hfirst hchildren =>
      rename_i u us
      obtain rfl : k = us.length + 1 := by simp [← hlen]
      have hus : ∀ w ∈ us, w ∈ u :: us := fun w hw => List.mem_cons_of_mem u hw
      cases p with
      | true =>
        -- the first child returns the value `m` exactly; the rest fail low against `[m, b]`
        have hm : minimax true (.node (u :: us)) = minimax false u := hfirst
        have htu := alphaBeta_time_pv (us.length + 1) d false u a b
          (hts u List.mem_cons_self) (hchildren u List.mem_cons_self) (hm ▸ ha) (hm ▸ hb)
        have hret : (alphaBeta false a b u).ret = minimax false u :=
          alphaBeta_eq_of_mem_window (hm ▸ ha) (hm ▸ hb)
        have hmax : max a (alphaBeta false a b u).ret = minimax false u := by
          rw [hret, max_eq_right (hm ▸ ha).le]
        have hnc : ¬ b ≤ max a (alphaBeta false a b u).ret := by
          rw [hmax]; exact not_le.2 (hm ▸ hb)
        have hrest : ∀ w ∈ us, minimax false w ≤ minimax false u := by
          have h : minimaxList true (u :: us) ≤ minimax false u := by
            rw [← hm]; simp [minimax]
          rw [minimaxList_true_le_iff] at h
          exact fun w hw => h w (hus w hw)
        have hlist := alphaBetaList_true_time_of_le (hm ▸ hb) hrest
          (fun w hw => alphaBeta_time_cut_false (hts w (hus w hw)) (hchildren w (hus w hw))
            (hm ▸ hb) (hrest w hw))
        simp only [alphaBeta, alphaBetaList, TimeM.time_bind, hnc, ite_false]
        rw [hmax, htu, hlist, pvLeaves_succ_succ]
      | false =>
        -- the first child returns the value `m` exactly; the rest fail high against `[a, m]`
        have hm : minimax false (.node (u :: us)) = minimax true u := hfirst
        have htu := alphaBeta_time_pv (us.length + 1) d true u a b
          (hts u List.mem_cons_self) (hchildren u List.mem_cons_self) (hm ▸ ha) (hm ▸ hb)
        have hret : (alphaBeta true a b u).ret = minimax true u :=
          alphaBeta_eq_of_mem_window (hm ▸ ha) (hm ▸ hb)
        have hmin : min b (alphaBeta true a b u).ret = minimax true u := by
          rw [hret, min_eq_right (hm ▸ hb).le]
        have hnc : ¬ min b (alphaBeta true a b u).ret ≤ a := by
          rw [hmin]; exact not_le.2 (hm ▸ ha)
        have hrest : ∀ w ∈ us, minimax true u ≤ minimax true w := by
          have h : minimax true u ≤ minimaxList false (u :: us) := by
            rw [← hm]; simp [minimax]
          rw [le_minimaxList_false_iff] at h
          exact fun w hw => h w (hus w hw)
        have hlist := alphaBetaList_false_time_of_le (hm ▸ ha) hrest
          (fun w hw => alphaBeta_time_cut_true (hts w (hus w hw)) (hchildren w (hus w hw))
            (hm ▸ ha) (hrest w hw))
        simp only [alphaBeta, alphaBetaList, TimeM.time_bind, hnc, ite_false]
        rw [hmin, htu, hlist, pvLeaves_succ_succ]

/-- **Knuth and Moore's best case.** On a uniform tree of branching factor `k` and depth `d` with
perfectly ordered moves and a minimax value strictly between `⊥` and `⊤`, alpha-beta with the full
window evaluates exactly `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` leaves. -/
theorem alphaBeta_leafCount_perfect {k d : ℕ} {p : Bool} {t : GameTree α} (hu : Uniform k d t)
    (hpo : PerfectlyOrdered p t) (hbot : ⊥ < minimax p t) (htop : minimax p t < ⊤) :
    (alphaBeta p ⊥ ⊤ t).time = k ^ ((d + 1) / 2) + k ^ (d / 2) - 1 :=
  alphaBeta_time_pv k d p t ⊥ ⊤ hu hpo hbot htop

end Minimax

end Cslib.Algorithms.Lean.AlphaBeta
