/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Defs

/-!
# Completeness of d-separation

The global Markov property (`BayesNet.condIndep_of_dSeparated` in
`CSLibExt/MachineLearning/GraphicalModels/GlobalMarkov.lean`) says that d-separation in the
graph of a Bayesian network implies conditional independence under its joint law. The converse
direction, completeness, says that d-separation is the strongest such graphical test: every
triple that is not d-separated is conditionally dependent under some network on the same graph.

## Main results

* `BayesNet.exists_not_condIndep_of_not_dSeparated`: **completeness of d-separation**. If
  pairwise disjoint sets `X`, `Y`, `Z` of nodes are not d-separated in the graph of a Bayesian
  network with a finite state space of at least two values, then some network with the same
  parent sets and the same state space makes `X` and `Y` conditionally dependent given `Z`.

## Proof

Take an active path from `x ∈ X` to `y ∈ Y`. Each of its colliders has a descendant in `Z`, and
its *route* is a shortest directed path from it into `Z`, built with one fixed choice of next
node for every node, so that two routes that meet go on together. Among the active paths from
`x` to `y`, one with the least sum, over its colliders, of the lengths of their routes is
*clean*: no route meets the path again after leaving it, since replacing the part of the path
between a collider and the first node where its route comes back by that route gives an active
path with a smaller sum.

On a clean path `π` the edges of `π` and of the routes are the *active* edges. The witness
network has the parent sets of the given one: a node with an active parent takes the value `a₁`
exactly when an odd number of its active parents do, and `a₀` otherwise, where `a₀ ≠ a₁`; every
other node is a fair coin on `{a₀, a₁}`. Summing these parity constraints over the nodes, each
node is counted once for having active parents and once for each active child; outside `Z` this
count is odd exactly at `x` and at `y`. So every configuration of positive probability with all
of `Z` at `a₀` takes the same value at `x` and at `y`, while the configuration with every node at
`a₀` and the one with the non-colliders of `π` at `a₁` and every other node at `a₀` both have
positive probability. With `x` at `a₀` and `y` at `a₁` this breaks the product formula of
`CondIndep` for `x`, `y` and `Z`, and decomposition carries the dependence to `X` and `Y`.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–710, §2.1.
* D. Geiger, T. Verma and J. Pearl, *Identifying independence in Bayesian networks*, Networks
  20(5) (1990), 507–534.
* C. Meek, *Strong completeness and faithfulness in Bayesian networks*, Proc. 11th Conference on
  Uncertainty in Artificial Intelligence (1995); arXiv:1302.4973, §2.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity MetaMathlibExt.FiniteWeight

namespace BayesNet

section Witness

variable {α : Type*} {n : ℕ} (b : BayesNet α n)

/-! ### Edges -/

private lemma edge_lt {i j : Fin n} (h : b.Edge i j) : i < j := Fin.lt_def.2 h.1

private lemma edge_asymm {i j : Fin n} (h : b.Edge i j) : ¬b.Edge j i := fun h' =>
  lt_asymm (b.edge_lt h) (b.edge_lt h')

/-! ### Distance to the conditioning set along directed paths -/

/-- `Reach Z d v`: a directed path with at most `d` edges leads from `v` into `Z`. -/
private def Reach (Z : Finset (Fin n)) : ℕ → Fin n → Prop
  | 0, v => v ∈ Z
  | d + 1, v => v ∈ Z ∨ ∃ w, b.Edge v w ∧ Reach Z d w

private lemma reach_of_isDescendant {Z : Finset (Fin n)} {m z : Fin n} (hz : z ∈ Z)
    (h : b.IsDescendant m z) : ∃ d, b.Reach Z d m := by
  unfold IsDescendant at h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, hz⟩
  | head hmm' _ ih =>
    obtain ⟨d, hd⟩ := ih
    exact ⟨d + 1, Or.inr ⟨_, hmm', hd⟩⟩

private lemma isDescendant_of_reach {Z : Finset (Fin n)} (d : ℕ) :
    ∀ {v : Fin n}, b.Reach Z d v → ∃ z ∈ Z, b.IsDescendant v z := by
  induction d with
  | zero => exact fun {v} h => ⟨v, h, Relation.ReflTransGen.refl⟩
  | succ d ih =>
    intro v h
    rcases h with h | ⟨w, hvw, hw⟩
    · exact ⟨v, h, Relation.ReflTransGen.refl⟩
    · obtain ⟨z, hz, hwz⟩ := ih hw
      exact ⟨z, hz, Relation.ReflTransGen.head hvw hwz⟩

open Classical in
/-- The length of a shortest directed path from `v` into `Z` (`0` if there is none). -/
private noncomputable def dist (Z : Finset (Fin n)) (v : Fin n) : ℕ :=
  if h : ∃ d, b.Reach Z d v then Nat.find h else 0

open Classical in
/-- The next node on a shortest directed path from `v ∉ Z` into `Z`, when there is one (a fixed
choice for each node). -/
private noncomputable def next (Z : Finset (Fin n)) (v : Fin n) : Fin n :=
  if h : ∃ w, b.Edge v w ∧ b.Reach Z (b.dist Z v - 1) w then h.choose else v

private lemma reach_dist {Z : Finset (Fin n)} {v : Fin n} (h : ∃ d, b.Reach Z d v) :
    b.Reach Z (b.dist Z v) v := by
  classical
  rw [dist, dite_eq_left h]
  exact Nat.find_spec h

private lemma dist_le {Z : Finset (Fin n)} {d : ℕ} {v : Fin n} (h : b.Reach Z d v) :
    b.dist Z v ≤ d := by
  classical
  rw [dist, dite_eq_left ⟨d, h⟩]
  exact Nat.find_min' _ h

private lemma dist_eq_zero_iff {Z : Finset (Fin n)} {v : Fin n} (h : ∃ d, b.Reach Z d v) :
    b.dist Z v = 0 ↔ v ∈ Z := by
  constructor
  · intro h0
    have := b.reach_dist h
    rw [h0] at this
    exact this
  · intro hv
    exact Nat.le_zero.1 (b.dist_le (d := 0) hv)

private lemma next_spec {Z : Finset (Fin n)} {v : Fin n} (h : ∃ d, b.Reach Z d v) (hv : v ∉ Z) :
    b.Edge v (b.next Z v) ∧ (∃ d, b.Reach Z d (b.next Z v)) ∧
      b.dist Z (b.next Z v) + 1 = b.dist Z v := by
  classical
  have hD := b.reach_dist h
  obtain ⟨D, hD'⟩ : ∃ D, b.dist Z v = D + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h0 => hv ((b.dist_eq_zero_iff h).1 h0)
  rw [hD'] at hD
  rcases hD with hvZ | hex
  · exact absurd hvZ hv
  have hex' : ∃ w, b.Edge v w ∧ b.Reach Z (b.dist Z v - 1) w := by
    rw [hD']
    simpa using hex
  have hn : b.next Z v = hex'.choose := by rw [next, dite_eq_left hex']
  obtain ⟨h1, h2⟩ := hex'.choose_spec
  rw [← hn] at h1 h2
  refine ⟨h1, ⟨_, h2⟩, ?_⟩
  have hle : b.dist Z (b.next Z v) ≤ D := by
    have := b.dist_le h2
    rw [hD'] at this
    simpa using this
  have hge : b.dist Z v ≤ b.dist Z (b.next Z v) + 1 :=
    b.dist_le (d := b.dist Z (b.next Z v) + 1) (Or.inr ⟨_, h1, b.reach_dist ⟨_, h2⟩⟩)
  omega

private lemma iter_spec {Z : Finset (Fin n)} {c : Fin n} (hc : ∃ d, b.Reach Z d c) (m : ℕ)
    (hm : m ≤ b.dist Z c) :
    (∃ d, b.Reach Z d ((b.next Z)^[m] c)) ∧ b.dist Z ((b.next Z)^[m] c) + m = b.dist Z c := by
  induction m with
  | zero => exact ⟨hc, by simp⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hnz : (b.next Z)^[m] c ∉ Z := fun hz => by
      have := (b.dist_eq_zero_iff h1).2 hz
      omega
    obtain ⟨-, h3, h4⟩ := b.next_spec h1 hnz
    rw [Function.iterate_succ_apply']
    exact ⟨h3, by omega⟩

private lemma iter_notMem {Z : Finset (Fin n)} {c : Fin n} (hc : ∃ d, b.Reach Z d c) {m : ℕ}
    (hm : m < b.dist Z c) : (b.next Z)^[m] c ∉ Z := by
  obtain ⟨h1, h2⟩ := b.iter_spec hc m hm.le
  intro hz
  have := (b.dist_eq_zero_iff h1).2 hz
  omega

private lemma iter_edge {Z : Finset (Fin n)} {c : Fin n} (hc : ∃ d, b.Reach Z d c) {m : ℕ}
    (hm : m < b.dist Z c) : b.Edge ((b.next Z)^[m] c) ((b.next Z)^[m + 1] c) := by
  rw [Function.iterate_succ_apply']
  exact (b.next_spec (b.iter_spec hc m hm.le).1 (b.iter_notMem hc hm)).1

/-- The route from `c` towards `Z`, up to its `m`-th node, avoiding a list `S` in between. -/
private lemma exists_route {Z : Finset (Fin n)} {c : Fin n} (hc : ∃ d, b.Reach Z d c)
    (S : List (Fin n)) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ b.dist Z c)
    (hS : ∀ j, 1 ≤ j → j < m → (b.next Z)^[j] c ∉ S) :
    ∃ R : List (Fin n), List.IsChain b.Edge (c :: R ++ [(b.next Z)^[m] c]) ∧
      ∀ r ∈ R, r ∉ Z ∧ r ∉ S := by
  induction m, hm1 using Nat.le_induction with
  | base =>
    refine ⟨[], ?_, by simp⟩
    simpa using b.iter_edge hc (m := 0) (by omega)
  | succ m hm1 ih =>
    obtain ⟨R, hR, hRS⟩ := ih (by omega) fun j hj1 hj2 => hS j hj1 (by omega)
    refine ⟨R ++ [(b.next Z)^[m] c], ?_, ?_⟩
    · have e : c :: (R ++ [(b.next Z)^[m] c]) ++ [(b.next Z)^[m + 1] c] =
          (c :: R ++ [(b.next Z)^[m] c]) ++ [(b.next Z)^[m + 1] c] := by simp
      rw [e]
      refine hR.append (List.isChain_singleton _) ?_
      intro u hu v hv
      rw [List.getLast?_concat, Option.mem_some_iff] at hu
      rw [List.head?_cons, Option.mem_some_iff] at hv
      subst hu hv
      exact b.iter_edge hc (by omega)
    · intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hRS r hr
      · rw [List.mem_singleton.1 hr]
        exact ⟨b.iter_notMem hc (by omega), hS m hm1 (by omega)⟩


/-! ### Active lists and the sum of collider distances -/

/-- No three consecutive nodes of the list are blocked by `Z`. -/
private def ActiveL (Z : Finset (Fin n)) : List (Fin n) → Prop
  | u :: m :: w :: l => ¬b.BlockedAt (Z : Set (Fin n)) u m w ∧ ActiveL Z (m :: w :: l)
  | _ => True

private lemma pathBlocked_cons3 (Z : Set (Fin n)) (u m w : Fin n) (l : List (Fin n)) :
    b.PathBlocked Z (u :: m :: w :: l) ↔ b.BlockedAt Z u m w ∨ b.PathBlocked Z (m :: w :: l) := by
  constructor
  · rintro ⟨i, hi, hb⟩
    cases i with
    | zero => exact Or.inl hb
    | succ i => exact Or.inr ⟨i, by simp at hi ⊢; omega, by simpa using hb⟩
  · rintro (hb | ⟨i, hi, hb⟩)
    · exact ⟨0, by simp, hb⟩
    · exact ⟨i + 1, by simp at hi ⊢; omega, by simpa using hb⟩

private lemma activeL_iff (Z : Finset (Fin n)) :
    ∀ p : List (Fin n), b.ActiveL Z p ↔ ¬b.PathBlocked (Z : Set (Fin n)) p
  | [] => by simp [ActiveL, PathBlocked]
  | [_] => by simp [ActiveL, PathBlocked]
  | [_, _] => by simp [ActiveL, PathBlocked]
  | u :: m :: w :: l => by
    rw [ActiveL, pathBlocked_cons3, activeL_iff Z (m :: w :: l)]
    tauto

private lemma activeL_reverse {Z : Finset (Fin n)} {p : List (Fin n)} (h : b.ActiveL Z p) :
    b.ActiveL Z p.reverse := by
  rw [activeL_iff] at h ⊢
  exact fun hb => h (by simpa using b.pathBlocked_reverse hb)

private lemma activeL_cons (Z : Finset (Fin n)) (a : Fin n) (l : List (Fin n)) :
    b.ActiveL Z (a :: l) ↔
      (∀ m ∈ l.head?, ∀ w ∈ l.tail.head?, ¬b.BlockedAt (Z : Set (Fin n)) a m w) ∧
        b.ActiveL Z l := by
  match l with
  | [] => simp [ActiveL]
  | [_] => simp [ActiveL]
  | m :: w :: l' => simp [ActiveL]

private lemma activeL_append (Z : Finset (Fin n)) (m : Fin n) (l₂ : List (Fin n))
    (l₁ : List (Fin n)) : b.ActiveL Z (l₁ ++ m :: l₂) ↔
      b.ActiveL Z (l₁ ++ [m]) ∧ b.ActiveL Z (m :: l₂) ∧
        ∀ u ∈ l₁.getLast?, ∀ w ∈ l₂.head?, ¬b.BlockedAt (Z : Set (Fin n)) u m w := by
  induction l₁ with
  | nil => simp [ActiveL, and_comm]
  | cons a L ih =>
    rw [List.cons_append, List.cons_append, activeL_cons, activeL_cons, ih]
    cases L with
    | nil => simp [ActiveL, and_comm]
    | cons c L' =>
      have e : (L' ++ m :: l₂).head? = (L' ++ [m]).head? := by simp [List.head?_append]
      simp only [List.cons_append, List.head?_cons, List.tail_cons, e, List.getLast?_cons_cons]
      tauto

/-- The term of a collider `u → m ← w` in `cSum`: the distance from `m` to `Z`. -/
private noncomputable def J (Z : Finset (Fin n)) (u m w : Fin n) : ℕ :=
  if b.Edge u m ∧ b.Edge w m then b.dist Z m else 0

/-- The term of the middle node `m`, with optional neighbours, in `cSum`. -/
private noncomputable def jt (Z : Finset (Fin n)) : Option (Fin n) → Fin n → Option (Fin n) → ℕ
  | some u, m, some w => b.J Z u m w
  | _, _, _ => 0

/-- The sum, over the colliders of a list, of their distances to `Z`. -/
private noncomputable def cSum (Z : Finset (Fin n)) : List (Fin n) → ℕ
  | u :: m :: w :: l => b.J Z u m w + cSum Z (m :: w :: l)
  | _ => 0

private lemma J_comm (Z : Finset (Fin n)) (u m w : Fin n) : b.J Z u m w = b.J Z w m u := by
  unfold J
  simp only [and_comm]

private lemma jt_le (Z : Finset (Fin n)) (o₁ : Option (Fin n)) (m : Fin n)
    (o₂ : Option (Fin n)) : b.jt Z o₁ m o₂ ≤ b.dist Z m := by
  rcases o₁ with _ | u <;> rcases o₂ with _ | w <;> simp only [jt, zero_le]
  unfold J
  split_ifs <;> simp

private lemma cSum_cons_cons (Z : Finset (Fin n)) (a c : Fin n) (L : List (Fin n)) :
    b.cSum Z (a :: c :: L) = b.jt Z (some a) c L.head? + b.cSum Z (c :: L) := by
  cases L with
  | nil => simp [cSum, jt]
  | cons e L' => simp [cSum, jt]

private lemma cSum_append (Z : Finset (Fin n)) (m : Fin n) (l₂ : List (Fin n))
    (l₁ : List (Fin n)) : b.cSum Z (l₁ ++ m :: l₂) =
      b.cSum Z (l₁ ++ [m]) + b.jt Z l₁.getLast? m l₂.head? + b.cSum Z (m :: l₂) := by
  induction l₁ with
  | nil => simp [cSum, jt]
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.getLast?_singleton]
      rw [cSum_cons_cons]
      simp [cSum]
    | cons c L' =>
      simp only [List.cons_append] at ih ⊢
      rw [cSum_cons_cons, cSum_cons_cons, ih, List.getLast?_cons_cons]
      have e : (L' ++ m :: l₂).head? = (L' ++ [m]).head? := by simp [List.head?_append]
      rw [e]
      ring

private lemma cSum_reverse (Z : Finset (Fin n)) (l : List (Fin n)) :
    b.cSum Z l.reverse = b.cSum Z l := by
  induction l with
  | nil => rfl
  | cons a L ih =>
    cases L with
    | nil => rfl
    | cons c L' =>
      have e : (c :: L').reverse ++ [a] = L'.reverse ++ c :: [a] := by simp
      rw [List.reverse_cons, e, cSum_append, List.getLast?_reverse,
        show b.cSum Z [c, a] = 0 from rfl, b.cSum_cons_cons Z a c L',
        show L'.reverse ++ [c] = (c :: L').reverse by simp, ih]
      rcases L'.head? with _ | e'
      · simp [jt]
      · simp only [jt, List.head?_cons]
        rw [J_comm]
        ring

private lemma cSum_chain (Z : Finset (Fin n)) :
    ∀ l : List (Fin n), List.IsChain b.Edge l → b.cSum Z l = 0
  | u :: m :: w :: l, h => by
    rw [List.isChain_cons_cons] at h
    have h2 := List.isChain_cons_cons.1 h.2
    rw [cSum, cSum_chain Z (m :: w :: l) h.2]
    simp [J, b.edge_asymm h2.1]
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl


/-! ### Colliders and the shortening step -/

/-- `c` is a collider of the list `π`: its two neighbours in `π` are parents of `c`. -/
private def IsCollOn (π : List (Fin n)) (c : Fin n) : Prop :=
  ∃ s u w t, π = s ++ u :: c :: w :: t ∧ b.Edge u c ∧ b.Edge w c

/-- A list is clean (for `Z`) when no route from one of its colliders towards `Z` returns to
it. -/
private def Clean (Z : Finset (Fin n)) (π : List (Fin n)) : Prop :=
  ∀ c, b.IsCollOn π c → ∀ m, 1 ≤ m → m ≤ b.dist Z c → (b.next Z)^[m] c ∉ π

private lemma hasDesc_of_isCollOn {Z : Finset (Fin n)} {π : List (Fin n)} {c : Fin n}
    (ha : b.ActiveL Z π) (hc : b.IsCollOn π c) : ∃ k, b.Reach Z k c := by
  obtain ⟨s, u, w, t, rfl, huc, hwc⟩ := hc
  rw [show s ++ u :: c :: w :: t = (s ++ [u]) ++ c :: w :: t by simp, activeL_append] at ha
  have hb := ha.2.2 u (by simp) w rfl
  simp only [BlockedAt, not_or, not_and, not_forall, not_not] at hb
  obtain ⟨z, hcz, hz⟩ := hb.1 huc hwc
  exact b.reach_of_isDescendant hz hcz

private lemma nodup_of_chain {l : List (Fin n)} (h : List.IsChain b.Edge l) : l.Nodup := by
  have h' : List.IsChain (· < ·) l := h.imp fun _ _ hab => b.edge_lt hab
  exact (List.isChain_iff_pairwise.1 h').nodup

private lemma activeL_chain {Z : Finset (Fin n)} (a e : Fin n) :
    ∀ l : List (Fin n), List.IsChain b.Edge (a :: l ++ [e]) → (∀ r ∈ l, r ∉ Z) →
      b.ActiveL Z (a :: l ++ [e])
  | [], _, _ => by simp [ActiveL]
  | r :: l, h, hZ => by
    have h' : List.IsChain b.Edge (a :: r :: (l ++ [e])) := by simpa using h
    obtain ⟨har, hr⟩ := List.isChain_cons_cons.1 h'
    have ih := activeL_chain r e l (by simpa using hr) fun q hq => hZ q (by simp [hq])
    rw [List.cons_append, List.cons_append, activeL_cons]
    refine ⟨fun m hm w hw => ?_, by simpa using ih⟩
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm
    subst hm
    have hw' : (l ++ [e]).head? = some w := by simpa using hw
    have hrw : b.Edge r w := by
      cases l with
      | nil =>
        obtain rfl : e = w := by simpa using hw'
        simpa using hr
      | cons q l' =>
        obtain rfl : q = w := by simpa using hw'
        exact (List.isChain_cons_cons.1 (by simpa using hr)).1
    rintro (⟨-, hwr, -⟩ | ⟨-, hrZ⟩)
    · exact b.edge_asymm hrw hwr
    · exact hZ r (by simp) hrZ

private lemma nodup_swap_mid {A M M' D : List (Fin n)} (h : (A ++ M ++ D).Nodup)
    (h' : M'.Nodup) (hM' : ∀ r ∈ M', r ∉ A ++ M ++ D) : (A ++ M' ++ D).Nodup := by
  simp only [List.nodup_append, List.mem_append, not_or] at h hM' ⊢
  obtain ⟨⟨hA, hM, hAM⟩, hD, hAMD⟩ := h
  refine ⟨⟨hA, h', fun a ha r hr => ?_⟩, hD, fun a ha d hd => ?_⟩
  · exact fun e => (hM' r hr).1.1 (e ▸ ha)
  · rcases ha with ha | ha
    · exact hAMD a (Or.inl ha) d hd
    · exact fun e => (hM' a ha).2 (e ▸ hd)

/-- **The shortening step.** If the route from a collider `c ∉ Z` of an active path reaches the
path again at a later node `d`, replacing the part of the path between `c` and `d` by the route
gives an active path with a smaller sum of collider distances. -/
private lemma surgery {Z : Finset (Fin n)} {x y u c w d : Fin n} {s t B C R : List (Fin n)}
    (hp : b.IsPath x y (s ++ u :: c :: w :: t)) (ha : b.ActiveL Z (s ++ u :: c :: w :: t))
    (hwt : w :: t = B ++ d :: C) (huc : b.Edge u c) (hwc : b.Edge w c) (hcZ : c ∉ Z)
    (hR : List.IsChain b.Edge (c :: R ++ [d])) (hRZ : ∀ r ∈ R, r ∉ Z)
    (hRp : ∀ r ∈ R, r ∉ s ++ u :: c :: w :: t) (hd : ∃ k, b.Reach Z k d)
    (hdist : b.dist Z d < b.dist Z c) :
    b.IsPath x y (s ++ u :: c :: (R ++ d :: C)) ∧ b.ActiveL Z (s ++ u :: c :: (R ++ d :: C)) ∧
      b.cSum Z (s ++ u :: c :: (R ++ d :: C)) < b.cSum Z (s ++ u :: c :: w :: t) := by
  have hcw : (w :: t).head? = some w := rfl
  rw [hwt] at hp ha hRp hcw ⊢
  obtain ⟨hnd, hch, hhd, hlast⟩ := hp
  -- the first and the last link of the route
  obtain ⟨r, hr, hcr⟩ : ∃ r, (R ++ d :: C).head? = some r ∧ b.Edge c r := by
    cases R with
    | nil => exact ⟨d, rfl, by simpa using hR⟩
    | cons r R' => exact ⟨r, rfl, (List.isChain_cons_cons.1 (by simpa using hR)).1⟩
  obtain ⟨hR1, -, hR3⟩ := List.isChain_append.1 hR
  obtain ⟨p, hpl⟩ : ∃ p, (c :: R).getLast? = some p := ⟨_, List.getLast?_eq_getLast_of_ne_nil
    (List.cons_ne_nil c R)⟩
  have hpd : b.Edge p d := hR3 p hpl d rfl
  -- the pieces of the old path
  have e1 : ∀ M : List (Fin n), s ++ u :: c :: (M ++ d :: C) = (s ++ [u]) ++ c :: (M ++ d :: C) :=
    fun M => by simp
  have e2 : ∀ M : List (Fin n), s ++ u :: c :: (M ++ d :: C) = (s ++ u :: c :: M) ++ d :: C :=
    fun M => by simp
  have hpre := (b.activeL_append Z c _ _).1 (by rw [← e1]; exact ha)
  have hsuf := (b.activeL_append Z d _ _).1 (by rw [← e2]; exact ha)
  obtain ⟨p', hp'⟩ : ∃ p', (s ++ u :: c :: B).getLast? = some p' :=
    ⟨_, List.getLast?_eq_getLast_of_ne_nil (by simp)⟩
  -- `d ∉ Z` when `d` is not a collider of the new path
  have hdZ : ∀ q ∈ C.head?, ¬b.Edge q d → d ∉ Z := by
    intro q hq hqd hdZ
    exact hsuf.2.2 p' hp' q hq (Or.inr ⟨fun h => hqd h.2, hdZ⟩)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- no repeated node
    have e3 : ∀ M : List (Fin n), s ++ u :: c :: (M ++ d :: C) = (s ++ [u, c]) ++ M ++ d :: C :=
      fun M => by simp
    rw [e3] at hnd hRp ⊢
    refine nodup_swap_mid hnd ?_ hRp
    have := b.nodup_of_chain hR
    rw [List.cons_append, List.nodup_cons] at this
    exact this.2.sublist (List.sublist_append_left R [d])
  · -- consecutive nodes are adjacent
    rw [e1] at hch ⊢
    obtain ⟨h1, h2, h3⟩ := List.isChain_append.1 hch
    refine List.isChain_append.2 ⟨h1, ?_, fun a ha' q hq => ?_⟩
    · rw [show c :: (R ++ d :: C) = (c :: R) ++ d :: C by simp]
      rw [show c :: (B ++ d :: C) = (c :: B) ++ d :: C by simp] at h2
      obtain ⟨-, h22, -⟩ := List.isChain_append.1 h2
      refine List.isChain_append.2 ⟨hR1.imp fun _ _ h => Or.inl h, h22, fun a ha q hq => ?_⟩
      rw [hpl, Option.mem_some_iff] at ha
      rw [List.head?_cons, Option.mem_some_iff] at hq
      subst ha hq
      exact Or.inl hpd
    · exact h3 a ha' q (by simpa using hq)
  · rw [List.head?_append] at hhd ⊢
    simpa using hhd
  · rw [e2, List.getLast?_append_cons] at hlast ⊢
    exact hlast
  · -- the new path is active
    rw [e1, activeL_append]
    refine ⟨hpre.1, ?_, fun a ha' q hq => ?_⟩
    · rw [show c :: (R ++ d :: C) = (c :: R) ++ d :: C by simp, activeL_append]
      refine ⟨b.activeL_chain c d R hR hRZ, hsuf.2.1, fun a ha' q hq => ?_⟩
      rw [hpl, Option.mem_some_iff] at ha'
      subst ha'
      rintro (⟨-, hqd, hdesc⟩ | ⟨hcol, hdZ'⟩)
      · obtain ⟨z, hz, hdz⟩ := b.isDescendant_of_reach _ (b.reach_dist hd)
        exact hdesc z hdz hz
      · exact hdZ q hq (fun h => hcol ⟨hpd, h⟩) hdZ'
    · rw [hr, Option.mem_some_iff] at hq
      subst hq
      rintro (⟨-, hrc, -⟩ | ⟨-, hcZ'⟩)
      · exact b.edge_asymm hcr hrc
      · exact hcZ hcZ'
  · -- the sum of collider distances decreases
    rw [e1, e1, b.cSum_append Z c (R ++ d :: C) (s ++ [u]),
      b.cSum_append Z c (B ++ d :: C) (s ++ [u]), hcw, hr,
      show c :: (R ++ d :: C) = (c :: R) ++ d :: C by simp,
      show c :: (B ++ d :: C) = (c :: B) ++ d :: C by simp,
      b.cSum_append Z d C (c :: R), b.cSum_append Z d C (c :: B), b.cSum_chain Z _ hR]
    have h1 : b.jt Z (s ++ [u]).getLast? c (some r) = 0 := by
      simp [jt, J, b.edge_asymm hcr]
    have h2 : b.jt Z (s ++ [u]).getLast? c (some w) = b.dist Z c := by
      simp [jt, J, huc, hwc]
    have h3 := b.jt_le Z (c :: R).getLast? d C.head?
    rw [h1, h2]
    have h4 : 0 < b.dist Z c := by omega
    omega


/-- **A clean active path.** Every active path from `x` to `y` can be replaced by an active path
from `x` to `y` none of whose collider routes towards `Z` returns to it: shorten along the routes
while the sum of collider distances decreases. -/
private lemma exists_clean (Z : Finset (Fin n)) {x y : Fin n} (N : ℕ) :
    ∀ π : List (Fin n), b.cSum Z π < N → b.IsPath x y π → b.ActiveL Z π →
      ∃ π', b.IsPath x y π' ∧ b.ActiveL Z π' ∧ b.Clean Z π' := by
  classical
  induction N with
  | zero => intro π h; omega
  | succ N ih =>
    intro π hN hp ha
    by_cases hcl : b.Clean Z π
    · exact ⟨π, hp, ha, hcl⟩
    simp only [Clean, not_forall, not_not, exists_prop] at hcl
    obtain ⟨c, hc, m, hm1, hm2, hmπ⟩ := hcl
    have hex : ∃ m, 1 ≤ m ∧ m ≤ b.dist Z c ∧ (b.next Z)^[m] c ∈ π := ⟨m, hm1, hm2, hmπ⟩
    obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
    have hmin : ∀ j, 1 ≤ j → j < Nat.find hex → (b.next Z)^[j] c ∉ π :=
      fun j hj1 hj2 hjπ => Nat.find_min hex hj2 ⟨hj1, by omega, hjπ⟩
    have hcD : ∃ k, b.Reach Z k c := b.hasDesc_of_isCollOn ha hc
    obtain ⟨R, hR, hRZπ⟩ := b.exists_route hcD π (Nat.find hex) h1 h2 hmin
    have hdD := (b.iter_spec hcD (Nat.find hex) h2).1
    have hdist : b.dist Z ((b.next Z)^[Nat.find hex] c) < b.dist Z c := by
      have := (b.iter_spec hcD (Nat.find hex) h2).2
      omega
    have hcZ : c ∉ Z := fun hz => by
      have := (b.dist_eq_zero_iff hcD).2 hz
      omega
    have hdc : (b.next Z)^[Nat.find hex] c ≠ c := fun h => by rw [h] at hdist; omega
    generalize (b.next Z)^[Nat.find hex] c = d at hR hdD hdist hdc h3
    obtain ⟨s, u, w, t, rfl, huc, hwc⟩ := hc
    have hmem : d ∈ s ++ [u] ∨ d ∈ w :: t := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h3 ⊢
      tauto
    rcases hmem with hds | hdt
    · -- the route returns before `c`: shorten the reversed path
      obtain ⟨A, B, hAB⟩ := List.mem_iff_append.1 hds
      have hrev : (s ++ u :: c :: w :: t).reverse = t.reverse ++ w :: c :: u :: s.reverse := by
        simp
      have hut : u :: s.reverse = B.reverse ++ d :: A.reverse := by
        have := congrArg List.reverse hAB
        simpa using this
      have hp' := b.isPath_reverse hp
      have ha' := b.activeL_reverse ha
      rw [hrev] at hp' ha'
      obtain ⟨hp'', ha'', hc''⟩ := b.surgery hp' ha' hut hwc huc hcZ hR
        (fun r hr => (hRZπ r hr).1)
        (fun r hr hr' => (hRZπ r hr).2 (by rw [← List.mem_reverse, hrev]; exact hr')) hdD hdist
      refine ih _ ?_ (b.isPath_reverse hp'') (b.activeL_reverse ha'')
      rw [cSum_reverse]
      rw [← hrev, cSum_reverse] at hc''
      omega
    · obtain ⟨B, C, hBC⟩ := List.mem_iff_append.1 hdt
      obtain ⟨hp', ha', hc'⟩ := b.surgery hp ha hBC huc hwc hcZ hR
        (fun r hr => (hRZπ r hr).1) (fun r hr => (hRZπ r hr).2) hdD hdist
      exact ih _ (by omega) hp' ha'


/-! ### Neighbours on a path without repeated nodes -/

private lemma notMem_of_nodup {s t : List (Fin n)} {u : Fin n} (h : (s ++ u :: t).Nodup) :
    u ∉ s ∧ u ∉ t := by
  rw [List.nodup_append] at h
  exact ⟨fun hu => h.2.2 u hu u (by simp) rfl, (List.nodup_cons.1 h.2.1).1⟩

private lemma eq_of_nodup {s t s' t' : List (Fin n)} {u : Fin n} (h : (s ++ u :: t).Nodup)
    (e : s ++ u :: t = s' ++ u :: t') : s = s' ∧ t = t' := by
  obtain ⟨h1, h2⟩ := notMem_of_nodup h
  have := (List.append_cons_inj_of_notMem h1 h2).1 e
  exact ⟨this.1, this.2.2⟩

private lemma infix_right_iff {π s t : List (Fin n)} {u v : Fin n} (hnd : π.Nodup)
    (hπ : π = s ++ u :: t) : [u, v] <:+: π ↔ v ∈ t.head? := by
  subst hπ
  constructor
  · rintro ⟨s', t', h⟩
    have e : s ++ u :: t = s' ++ u :: (v :: t') := by rw [← h]; simp
    rw [(eq_of_nodup hnd e).2]
    rfl
  · intro hv
    obtain ⟨t', rfl⟩ := List.head?_eq_some_iff.1 hv
    exact ⟨s, t', by simp⟩

private lemma infix_left_iff {π s t : List (Fin n)} {u v : Fin n} (hnd : π.Nodup)
    (hπ : π = s ++ u :: t) : [v, u] <:+: π ↔ v ∈ s.getLast? := by
  subst hπ
  constructor
  · rintro ⟨s', t', h⟩
    have e : s ++ u :: t = (s' ++ [v]) ++ u :: t' := by rw [← h]; simp
    rw [(eq_of_nodup hnd e).1]
    simp
  · intro hv
    obtain ⟨s', rfl⟩ := List.getLast?_eq_some_iff.1 hv
    exact ⟨s', t, by simp⟩

private lemma isCollOn_iff {π s t : List (Fin n)} {u : Fin n} (hnd : π.Nodup)
    (hπ : π = s ++ u :: t) :
    b.IsCollOn π u ↔ (∃ v ∈ s.getLast?, b.Edge v u) ∧ ∃ w ∈ t.head?, b.Edge w u := by
  constructor
  · rintro ⟨s', v, w, t', h, hvu, hwu⟩
    have e : s ++ u :: t = (s' ++ [v]) ++ u :: (w :: t') := by rw [← hπ, h]; simp
    rw [hπ] at hnd
    obtain ⟨rfl, rfl⟩ := eq_of_nodup hnd e
    exact ⟨⟨v, by simp, hvu⟩, w, rfl, hwu⟩
  · rintro ⟨⟨v, hv, hvu⟩, w, hw, hwu⟩
    obtain ⟨s', rfl⟩ := List.getLast?_eq_some_iff.1 hv
    obtain ⟨t', rfl⟩ := List.head?_eq_some_iff.1 hw
    exact ⟨s', v, w, t', by rw [hπ]; simp, hvu, hwu⟩

/-- Both neighbours of a collider of a path are its parents. -/
private lemma edge_of_isCollOn {π : List (Fin n)} {u k : Fin n} (hnd : π.Nodup)
    (hu : b.IsCollOn π u) (hk : [u, k] <:+: π ∨ [k, u] <:+: π) : b.Edge k u := by
  obtain ⟨s', v, w, t', h, hvu, hwu⟩ := hu
  have hπ : π = (s' ++ [v]) ++ u :: (w :: t') := by rw [h]; simp
  rcases hk with hk | hk
  · rw [infix_right_iff hnd hπ] at hk
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hk
    exact hk ▸ hwu
  · rw [infix_left_iff hnd hπ] at hk
    simp only [List.getLast?_concat, Option.mem_def, Option.some.injEq] at hk
    exact hk ▸ hvu

private lemma eq_head_iff {π s t : List (Fin n)} {u x : Fin n} (hnd : π.Nodup)
    (hπ : π = s ++ u :: t) (hx : π.head? = some x) : s.getLast? = none ↔ u = x := by
  subst hπ
  rw [List.getLast?_eq_none_iff]
  constructor
  · rintro rfl
    simpa using hx
  · rintro rfl
    cases s with
    | nil => rfl
    | cons a s =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hx
      subst hx
      exact absurd (List.mem_cons_self) (notMem_of_nodup hnd).1

private lemma eq_last_iff {π s t : List (Fin n)} {u y : Fin n} (hnd : π.Nodup)
    (hπ : π = s ++ u :: t) (hy : π.getLast? = some y) : t.head? = none ↔ u = y := by
  subst hπ
  rw [List.head?_eq_none_iff]
  constructor
  · rintro rfl
    simpa using hy
  · rintro rfl
    by_contra ht
    rw [List.getLast?_append_cons, List.getLast?_cons, List.getLast?_eq_getLast_of_ne_nil ht]
      at hy
    simp only [Option.getD_some, Option.some.injEq] at hy
    exact (notMem_of_nodup hnd).2 (hy ▸ List.getLast_mem ht)


/-! ### The routes of a clean path -/

open Classical in
/-- The nodes of the routes from the colliders of `π` towards `Z`, before they reach `Z`. -/
private noncomputable def routeSet (Z : Finset (Fin n)) (π : List (Fin n)) : Finset (Fin n) :=
  (univ.filter (b.IsCollOn π)).biUnion fun c => (range (b.dist Z c)).image fun m => (b.next Z)^[m] c

private lemma mem_routeSet {Z : Finset (Fin n)} {π : List (Fin n)} {v : Fin n} :
    v ∈ b.routeSet Z π ↔ ∃ c, b.IsCollOn π c ∧ ∃ m < b.dist Z c, (b.next Z)^[m] c = v := by
  classical
  simp [routeSet]

private lemma isCollOn_mem {π : List (Fin n)} {c : Fin n} (h : b.IsCollOn π c) : c ∈ π := by
  obtain ⟨s, u, w, t, rfl, -, -⟩ := h
  simp

private lemma routeSet_spec {Z : Finset (Fin n)} {π : List (Fin n)} (ha : b.ActiveL Z π)
    {v : Fin n} (hv : v ∈ b.routeSet Z π) :
    v ∉ Z ∧ b.Edge v (b.next Z v) ∧ (b.next Z v ∈ b.routeSet Z π ∨ b.next Z v ∈ Z) := by
  obtain ⟨c, hc, m, hm, rfl⟩ := b.mem_routeSet.1 hv
  have hcD := b.hasDesc_of_isCollOn ha hc
  refine ⟨b.iter_notMem hcD hm, ?_, ?_⟩
  · have := b.iter_edge hcD hm
    rwa [Function.iterate_succ_apply'] at this
  · rw [← Function.iterate_succ_apply' (b.next Z)]
    by_cases hm' : m + 1 < b.dist Z c
    · exact Or.inl (b.mem_routeSet.2 ⟨c, hc, m + 1, hm', rfl⟩)
    · have := b.iter_spec hcD (m + 1) (by omega)
      exact Or.inr ((b.dist_eq_zero_iff this.1).1 (by omega))

private lemma next_notMem {Z : Finset (Fin n)} {π : List (Fin n)} (hcl : b.Clean Z π)
    {v : Fin n} (hv : v ∈ b.routeSet Z π) : b.next Z v ∉ π := by
  obtain ⟨c, hc, m, hm, rfl⟩ := b.mem_routeSet.1 hv
  rw [← Function.iterate_succ_apply' (b.next Z)]
  exact hcl c hc (m + 1) (by omega) (by omega)

private lemma isCollOn_of_mem_routeSet {Z : Finset (Fin n)} {π : List (Fin n)}
    (hcl : b.Clean Z π) {v : Fin n} (hv : v ∈ b.routeSet Z π) (hvπ : v ∈ π) :
    b.IsCollOn π v := by
  obtain ⟨c, hc, m, hm, rfl⟩ := b.mem_routeSet.1 hv
  cases m with
  | zero => simpa using hc
  | succ m => exact absurd hvπ (hcl c hc (m + 1) (by omega) hm.le)

private lemma exists_pred_of_mem_routeSet {Z : Finset (Fin n)} {π : List (Fin n)} {v : Fin n}
    (hv : v ∈ b.routeSet Z π) (hvπ : v ∉ π) : ∃ w ∈ b.routeSet Z π, b.next Z w = v := by
  obtain ⟨c, hc, m, hm, rfl⟩ := b.mem_routeSet.1 hv
  cases m with
  | zero => exact absurd (b.isCollOn_mem hc) hvπ
  | succ m =>
    exact ⟨_, b.mem_routeSet.2 ⟨c, hc, m, by omega, rfl⟩,
      (Function.iterate_succ_apply' _ _ _).symm⟩

private lemma mem_routeSet_of_isCollOn {Z : Finset (Fin n)} {π : List (Fin n)}
    (ha : b.ActiveL Z π) {v : Fin n} (hv : b.IsCollOn π v) (hvZ : v ∉ Z) :
    v ∈ b.routeSet Z π := by
  have hD := b.hasDesc_of_isCollOn ha hv
  exact b.mem_routeSet.2 ⟨v, hv, 0,
    Nat.pos_of_ne_zero fun h => hvZ ((b.dist_eq_zero_iff hD).1 h), rfl⟩

/-- The active edges of the witness network: the edges of the path `π` and the route edges from
its colliders towards `Z`. -/
private def AEdge (Z : Finset (Fin n)) (π : List (Fin n)) (u w : Fin n) : Prop :=
  (([u, w] <:+: π ∨ [w, u] <:+: π) ∧ b.Edge u w) ∨ (u ∈ b.routeSet Z π ∧ w = b.next Z u)

private lemma edge_of_aEdge {Z : Finset (Fin n)} {π : List (Fin n)} (ha : b.ActiveL Z π)
    {u w : Fin n} (h : b.AEdge Z π u w) : b.Edge u w := by
  rcases h with ⟨-, h⟩ | ⟨hu, rfl⟩
  · exact h
  · exact (b.routeSet_spec ha hu).2.1

/-! ### Parity -/

open Classical in
/-- `1` in `ZMod 2` when `P` holds, `0` otherwise. -/
private noncomputable def ind (P : Prop) : ZMod 2 := if P then 1 else 0

private lemma ind_pos {P : Prop} (h : P) : ind P = 1 := ite_eq_left h

private lemma ind_neg {P : Prop} (h : ¬P) : ind P = 0 := ite_eq_right h

private lemma ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by rw [propext h]

private lemma sum_option (o : Option (Fin n)) (Q : Fin n → Prop) :
    (∑ w, ind (w ∈ o ∧ Q w)) = ind (∃ v ∈ o, Q v) := by
  rcases o with _ | v
  · simp [ind_neg]
  · rw [Finset.sum_eq_single v (fun w _ hw => ind_neg (by simp [Ne.symm hw])) (by simp)]
    exact ind_congr (by simp)

private lemma sum_three (o₁ o₂ : Option (Fin n)) (Q₁ Q₂ : Fin n → Prop) (A : Prop) (e : Fin n)
    (P : Fin n → Prop) (hP : ∀ w, P w ↔ (w ∈ o₁ ∧ Q₁ w) ∨ (w ∈ o₂ ∧ Q₂ w) ∨ (A ∧ w = e))
    (h12 : ∀ v ∈ o₁, ∀ w ∈ o₂, v ≠ w) (h1e : A → e ∉ o₁) (h2e : A → e ∉ o₂) :
    (∑ w, ind (P w)) = ind (∃ v ∈ o₁, Q₁ v) + ind (∃ v ∈ o₂, Q₂ v) + ind A := by
  have pw : ∀ w, ind (P w) = ind (w ∈ o₁ ∧ Q₁ w) + ind (w ∈ o₂ ∧ Q₂ w) + ind (A ∧ w = e) := by
    intro w
    rw [ind_congr (hP w)]
    by_cases h1 : w ∈ o₁ ∧ Q₁ w <;> by_cases h2 : w ∈ o₂ ∧ Q₂ w <;> by_cases h3 : A ∧ w = e
    · exact absurd rfl (h12 w h1.1 w h2.1)
    · exact absurd rfl (h12 w h1.1 w h2.1)
    · exact absurd (h3.2 ▸ h1.1) (h1e h3.1)
    · rw [ind_pos (Or.inl h1), ind_pos h1, ind_neg h2, ind_neg h3]
      decide
    · exact absurd (h3.2 ▸ h2.1) (h2e h3.1)
    · rw [ind_pos (Or.inr (Or.inl h2)), ind_neg h1, ind_pos h2, ind_neg h3]
      decide
    · rw [ind_pos (Or.inr (Or.inr h3)), ind_neg h1, ind_neg h2, ind_pos h3]
      decide
    · rw [ind_neg (by tauto), ind_neg h1, ind_neg h2, ind_neg h3]
      decide
  rw [Finset.sum_congr rfl fun w _ => pw w, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_option, sum_option]
  congr 1
  by_cases hA : A
  · rw [Finset.sum_eq_single e (fun w _ hw => ind_neg fun h => hw h.2) (by simp), ind_pos hA,
      ind_pos ⟨hA, rfl⟩]
  · rw [ind_neg hA]
    exact Finset.sum_eq_zero fun w _ => ind_neg fun h => hA h.1

/-- **The parity identity.** Let every node `w` with an `E`-parent carry the sum (in `ZMod 2`) of
the values at its `E`-parents. Then the values, each weighted by "has an `E`-parent" plus the
number of its `E`-children, sum to zero. -/
private lemma parity (E : Fin n → Fin n → Prop) (a : Fin n → ZMod 2)
    (h : ∀ w, (∃ u, E u w) → a w = ∑ u, ind (E u w) * a u) :
    ∑ u, (ind (∃ v, E v u) + ∑ w, ind (E u w)) * a u = 0 := by
  have h1 : ∀ u, ind (∃ v, E v u) * a u = ∑ v, ind (E v u) * a v := by
    intro u
    by_cases hu : ∃ v, E v u
    · rw [ind_pos hu, one_mul, h u hu]
    · rw [ind_neg hu, zero_mul]
      exact (Finset.sum_eq_zero fun v _ => by rw [ind_neg fun hv => hu ⟨v, hv⟩, zero_mul]).symm
  have h2 : ∀ u, (∑ w, ind (E u w)) * a u = ∑ w, ind (E u w) * a u := fun u =>
    Finset.sum_mul _ _ _
  simp only [add_mul, Finset.sum_add_distrib, h1, h2]
  rw [Finset.sum_comm]
  exact (by decide : ∀ z : ZMod 2, z + z = 0) _

private lemma coef_arith (A A' B B' C X Y : Prop) (hC : C ↔ A ∧ B)
    (hX : X → ¬A ∧ ¬A') (hX' : ¬X → (A' ↔ ¬A)) (hY : Y → ¬B ∧ ¬B') (hY' : ¬Y → (B' ↔ ¬B)) :
    ind (A ∨ B) + (ind A' + ind B' + ind C) = ind X + ind Y := by
  have eA' : A' ↔ ¬X ∧ ¬A := by
    by_cases hx : X
    · simp [hx, (hX hx).2]
    · simp [hx, hX' hx]
  have eB' : B' ↔ ¬Y ∧ ¬B := by
    by_cases hy : Y
    · simp [hy, (hY hy).2]
    · simp [hy, hY' hy]
  have hXA : X → ¬A := fun hx => (hX hx).1
  have hYB : Y → ¬B := fun hy => (hY hy).1
  rw [ind_congr eA', ind_congr eB', ind_congr hC]
  by_cases hx : X <;> by_cases hy : Y <;> by_cases ha : A <;> by_cases hb : B
  all_goals first
    | exact absurd ha (hXA hx)
    | exact absurd hb (hYB hy)
    | (simp only [ind_pos, ind_neg, ha, hb, hx, hy, not_true_eq_false, not_false_eq_true,
        and_true, and_false, or_true, or_false, and_self]; decide)

private lemma adj_of_infix {π : List (Fin n)} (hch : List.IsChain b.Adj π) {v w : Fin n}
    (h : [v, w] <:+: π) : b.Adj v w :=
  List.isChain_pair.1 (hch.infix h)

/-- **The coefficient of a node in the parity identity**, for the active edges of a clean active
path from `x` to `y`: outside `Z` it is `1` exactly at `x` and at `y`. -/
private lemma coef_eq {Z : Finset (Fin n)} {π : List (Fin n)} {x y : Fin n}
    (hp : b.IsPath x y π) (ha : b.ActiveL Z π) (hcl : b.Clean Z π) {u : Fin n} (huZ : u ∉ Z) :
    ind (∃ v, b.AEdge Z π v u) + ∑ w, ind (b.AEdge Z π u w) = ind (u = x) + ind (u = y) := by
  obtain ⟨hnd, hch, hhd, hlast⟩ := hp
  by_cases huπ : u ∈ π
  · obtain ⟨s, t, hπ⟩ := List.mem_iff_append.1 huπ
    have hnd' : (s ++ u :: t).Nodup := hπ ▸ hnd
    have hin : (∃ v, b.AEdge Z π v u) ↔
        (∃ v ∈ s.getLast?, b.Edge v u) ∨ ∃ w ∈ t.head?, b.Edge w u := by
      constructor
      · rintro ⟨v, ⟨hvu | hvu, he⟩ | ⟨hv, rfl⟩⟩
        · exact Or.inl ⟨v, (infix_left_iff hnd hπ).1 hvu, he⟩
        · exact Or.inr ⟨v, (infix_right_iff hnd hπ).1 hvu, he⟩
        · exact absurd huπ (b.next_notMem hcl hv)
      · rintro (⟨v, hv, he⟩ | ⟨w, hw, he⟩)
        · exact ⟨v, Or.inl ⟨Or.inl ((infix_left_iff hnd hπ).2 hv), he⟩⟩
        · exact ⟨w, Or.inl ⟨Or.inr ((infix_right_iff hnd hπ).2 hw), he⟩⟩
    have hs : ∀ v ∈ s.getLast?, v ∈ π := fun v hv => by
      rw [hπ]; exact List.mem_append_left _ (List.mem_of_getLast? hv)
    have ht : ∀ w ∈ t.head?, w ∈ π := fun w hw => by
      rw [hπ]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_head? hw))
    have hout := sum_three s.getLast? t.head? (b.Edge u ·) (b.Edge u ·)
      (u ∈ b.routeSet Z π) (b.next Z u) (b.AEdge Z π u ·)
      (fun w => by
        simp only [AEdge, infix_right_iff hnd hπ, infix_left_iff hnd hπ]
        tauto)
      (fun v hv w hw e => by
        rw [List.nodup_append] at hnd'
        exact hnd'.2.2 v (List.mem_of_getLast? hv) w
          (List.mem_cons_of_mem _ (List.mem_of_head? hw)) e)
      (fun hR h => b.next_notMem hcl hR (hs _ h))
      (fun hR h => b.next_notMem hcl hR (ht _ h))
    rw [hout, ind_congr hin]
    refine coef_arith _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · rw [← isCollOn_iff b hnd hπ]
      exact ⟨fun h => b.isCollOn_of_mem_routeSet hcl h huπ,
        fun h => b.mem_routeSet_of_isCollOn ha h huZ⟩
    · intro hx
      rw [← eq_head_iff hnd hπ hhd] at hx
      simp [hx]
    · intro hx
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (mt (eq_head_iff hnd hπ hhd).1 hx)
      have hadj := b.adj_of_infix hch ((infix_left_iff (v := v) hnd hπ).2 (by simp [hv]))
      simp only [hv, Option.mem_def, Option.some.injEq, exists_eq_left']
      rcases hadj with h | h
      · exact ⟨fun h' => absurd h (b.edge_asymm h'), fun h' => absurd h h'⟩
      · exact ⟨fun _ h' => b.edge_asymm h h', fun _ => h⟩
    · intro hy
      rw [← eq_last_iff hnd hπ hlast] at hy
      simp [hy]
    · intro hy
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (mt (eq_last_iff hnd hπ hlast).1 hy)
      have hadj := b.adj_of_infix hch ((infix_right_iff (v := w) hnd hπ).2 (by simp [hw]))
      simp only [hw, Option.mem_def, Option.some.injEq, exists_eq_left']
      rcases hadj with h | h
      · exact ⟨fun _ h' => b.edge_asymm h h', fun _ => h⟩
      · exact ⟨fun h' => absurd h (b.edge_asymm h'), fun h' => absurd h h'⟩
  · have hxu : u ≠ x := fun e => huπ (e ▸ List.mem_of_head? hhd)
    have hyu : u ≠ y := fun e => huπ (e ▸ List.mem_of_getLast? hlast)
    have hin : (∃ v, b.AEdge Z π v u) ↔ ∃ v ∈ b.routeSet Z π, b.next Z v = u := by
      constructor
      · rintro ⟨v, ⟨hvu | hvu, -⟩ | ⟨hv, rfl⟩⟩
        · exact absurd (hvu.subset (by simp)) huπ
        · exact absurd (hvu.subset (by simp)) huπ
        · exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, Or.inr ⟨hv, rfl⟩⟩
    have hout := sum_three none none (fun _ => False) (fun _ => False)
      (u ∈ b.routeSet Z π) (b.next Z u) (b.AEdge Z π u ·)
      (fun w => by
        simp only [AEdge, Option.mem_def, reduceCtorEq, false_and, false_or]
        constructor
        · rintro (⟨hw | hw, -⟩ | h)
          · exact absurd (hw.subset (by simp)) huπ
          · exact absurd (hw.subset (by simp)) huπ
          · exact h
        · exact Or.inr)
      (by simp) (by simp) (by simp)
    rw [hout, ind_congr hin, ind_neg hxu, ind_neg hyu,
      ind_neg (by simp : ¬∃ v ∈ (none : Option (Fin n)), False)]
    by_cases hR : u ∈ b.routeSet Z π
    · rw [ind_pos (b.exists_pred_of_mem_routeSet hR huπ), ind_pos hR]
      decide
    · rw [ind_neg hR]
      refine (congrArg (· + _) (ind_neg fun ⟨v, hv, hvu⟩ => ?_)).trans (by decide)
      rcases (b.routeSet_spec ha hv).2.2 with h | h
      · exact hR (hvu ▸ h)
      · exact huZ (hvu ▸ h)

/-! ### The witness network -/

/-- The elements `0` and `1` of `ZMod 2` as the values `a₀` and `a₁`. -/
private def enc (a₀ a₁ : α) (t : ZMod 2) : α := if t = 0 then a₀ else a₁

private lemma ind_enc {a₀ a₁ : α} (h : a₀ ≠ a₁) (t : ZMod 2) : ind (enc a₀ a₁ t = a₁) = t := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
  · rw [ind_neg (by simpa [enc] using h)]
  · rw [ind_pos (by simp [enc, (by decide : (1 : ZMod 2) ≠ 0)])]

private lemma enc_ind {a₀ a₁ a : α} (h : a = a₀ ∨ a = a₁) : enc a₀ a₁ (ind (a = a₁)) = a := by
  by_cases ha : a = a₁
  · rw [ind_pos ha]
    simp [enc, ha, (by decide : (1 : ZMod 2) ≠ 0)]
  · rw [ind_neg ha]
    simp [enc, h.resolve_right ha]

open Classical in
/-- **The witness network** on the graph of `b`: a node with active parents (edges of the path
`π` and route edges from its colliders towards `Z`) takes the value `a₀` or `a₁` according to
the parity of the number of its active parents with value `a₁`; every other node is a fair coin
on `{a₀, a₁}`. -/
private noncomputable def witness (Z : Finset (Fin n)) (π : List (Fin n)) (a₀ a₁ : α) :
    BayesNet α n where
  pa := b.pa
  cpt k z := if ∃ u, b.AEdge Z π u k then
      StdSimplex.single (enc a₀ a₁ (∑ j : b.pa k,
        ind (b.AEdge Z π (Fin.castLE k.2.le j) k) * ind (z j = a₁)))
    else StdSimplex.duple a₀ a₁ (s := 1 / 2) (t := 1 / 2) (div_nonneg zero_le_one zero_le_two)
      (div_nonneg zero_le_one zero_le_two) (add_halves 1)

private lemma sum_pa {Z : Finset (Fin n)} {π : List (Fin n)} (ha : b.ActiveL Z π) (k : Fin n)
    (f : Fin n → ZMod 2) :
    ∑ j : b.pa k, ind (b.AEdge Z π (Fin.castLE k.2.le j) k) * f (Fin.castLE k.2.le j) =
      ∑ u, ind (b.AEdge Z π u k) * f u := by
  refine Fintype.sum_of_injective (fun j : b.pa k => Fin.castLE k.2.le (j : Fin k)) ?_ _ _ ?_
    fun _ => rfl
  · intro i j hij
    exact Subtype.ext (Fin.castLE_injective _ hij)
  · intro u hu
    rw [ind_neg, zero_mul]
    intro hE
    obtain ⟨hlt, hmem⟩ := b.edge_of_aEdge ha hE
    exact hu ⟨⟨⟨u.val, hlt⟩, hmem⟩, Fin.ext rfl⟩

open Classical in
private lemma witness_weights_of_aEdge {Z : Finset (Fin n)} {π : List (Fin n)}
    (ha : b.ActiveL Z π) (a₀ a₁ : α) (ω : Fin n → α) {k : Fin n}
    (hk : ∃ u, b.AEdge Z π u k) :
    ((b.witness Z π a₀ a₁).cpt k fun j => ω (Fin.castLE k.2.le j)).weights (ω k) =
      if enc a₀ a₁ (∑ u, ind (b.AEdge Z π u k) * ind (ω u = a₁)) = ω k then 1 else 0 := by
  classical
  simp only [witness, ite_eq_left hk, StdSimplex.weights_single, Finsupp.single_apply]
  rw [b.sum_pa ha k fun u => ind (ω u = a₁)]

open Classical in
private lemma witness_weights_of_not {Z : Finset (Fin n)} {π : List (Fin n)} (a₀ a₁ : α)
    (ω : Fin n → α) {k : Fin n} (hk : ¬∃ u, b.AEdge Z π u k) :
    ((b.witness Z π a₀ a₁).cpt k fun j => ω (Fin.castLE k.2.le j)).weights (ω k) =
      (if a₀ = ω k then 1 / 2 else 0) + if a₁ = ω k then 1 / 2 else 0 := by
  classical
  simp only [witness, ite_eq_right hk, StdSimplex.weights_duple, Finsupp.add_apply,
    Finsupp.single_apply]

/-- A configuration of positive probability under the witness network satisfies every parity
constraint. -/
private lemma witness_constraint [Nonempty α] {Z : Finset (Fin n)} {π : List (Fin n)}
    (ha : b.ActiveL Z π) {a₀ a₁ : α} (hne : a₀ ≠ a₁) {ω : Fin n → α}
    (hω : (b.witness Z π a₀ a₁).joint ω ≠ 0) (k : Fin n) (hk : ∃ u, b.AEdge Z π u k) :
    ind (ω k = a₁) = ∑ u, ind (b.AEdge Z π u k) * ind (ω u = a₁) := by
  rw [joint_eq_prod, Finset.prod_ne_zero_iff] at hω
  have h := hω k (mem_univ k)
  rw [b.witness_weights_of_aEdge ha a₀ a₁ ω hk] at h
  split_ifs at h with heq
  · rw [← heq, ind_enc hne]
  · exact absurd rfl h

/-- A configuration with values in `{a₀, a₁}` satisfying every parity constraint has positive
probability under the witness network. -/
private lemma witness_joint_pos [Nonempty α] {Z : Finset (Fin n)} {π : List (Fin n)}
    (ha : b.ActiveL Z π) {a₀ a₁ : α} (hne : a₀ ≠ a₁) {ω : Fin n → α}
    (h1 : ∀ k, (∃ u, b.AEdge Z π u k) →
      ind (ω k = a₁) = ∑ u, ind (b.AEdge Z π u k) * ind (ω u = a₁))
    (h2 : ∀ k, ω k = a₀ ∨ ω k = a₁) : 0 < (b.witness Z π a₀ a₁).joint ω := by
  rw [joint_eq_prod]
  refine Finset.prod_pos fun k _ => ?_
  by_cases hk : ∃ u, b.AEdge Z π u k
  · rw [b.witness_weights_of_aEdge ha a₀ a₁ ω hk, ← h1 k hk, enc_ind (h2 k), ite_eq_left rfl]
    exact one_pos
  · rw [b.witness_weights_of_not a₀ a₁ ω hk]
    rcases h2 k with h | h
    · rw [h, ite_eq_left rfl, ite_eq_right hne.symm, add_zero]
      exact half_pos one_pos
    · rw [h, ite_eq_right hne, ite_eq_left rfl, zero_add]
      exact half_pos one_pos

/-! ### Completeness -/

private lemma aEdge_iff_of_mem {Z : Finset (Fin n)} {π s t : List (Fin n)} {k u : Fin n}
    (hnd : π.Nodup) (hcl : b.Clean Z π) (hπ : π = s ++ k :: t) :
    b.AEdge Z π u k ↔ (u ∈ s.getLast? ∨ u ∈ t.head?) ∧ b.Edge u k := by
  have hkπ : k ∈ π := by rw [hπ]; simp
  constructor
  · rintro (⟨huk | huk, he⟩ | ⟨hu, rfl⟩)
    · exact ⟨Or.inl ((infix_left_iff hnd hπ).1 huk), he⟩
    · exact ⟨Or.inr ((infix_right_iff hnd hπ).1 huk), he⟩
    · exact absurd hkπ (b.next_notMem hcl hu)
  · rintro ⟨hu | hu, he⟩
    · exact Or.inl ⟨Or.inl ((infix_left_iff hnd hπ).2 hu), he⟩
    · exact Or.inl ⟨Or.inr ((infix_right_iff hnd hπ).2 hu), he⟩

/-- A node of `Z` on an active path between nodes outside `Z` is a collider of the path. -/
private lemma isCollOn_of_mem {Z : Finset (Fin n)} {π : List (Fin n)} {x y z : Fin n}
    (hp : b.IsPath x y π) (ha : b.ActiveL Z π) (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hzπ : z ∈ π)
    (hzZ : z ∈ Z) : b.IsCollOn π z := by
  obtain ⟨hnd, -, hhd, hlast⟩ := hp
  obtain ⟨s, t, hπ⟩ := List.mem_iff_append.1 hzπ
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1
    (mt (eq_head_iff hnd hπ hhd).1 fun e => hxZ (e ▸ hzZ))
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1
    (mt (eq_last_iff hnd hπ hlast).1 fun e => hyZ (e ▸ hzZ))
  rw [hπ, activeL_append] at ha
  have hb := ha.2.2 v hv w hw
  rw [isCollOn_iff b hnd hπ]
  by_contra hc
  exact hb (Or.inr ⟨fun ⟨h1, h2⟩ => hc ⟨⟨v, hv, h1⟩, w, hw, h2⟩, hzZ⟩)

private lemma not_isCollOn_last {π : List (Fin n)} {x y : Fin n} (hp : b.IsPath x y π) :
    ¬b.IsCollOn π y := by
  obtain ⟨hnd, -, -, hlast⟩ := hp
  intro hc
  obtain ⟨s, t, hπ⟩ := List.mem_iff_append.1 (b.isCollOn_mem hc)
  obtain ⟨-, w, hw, -⟩ := (isCollOn_iff b hnd hπ).1 hc
  rw [(eq_last_iff hnd hπ hlast).2 rfl] at hw
  simp at hw

end Witness

variable {n : ℕ}

/-- **Completeness of d-separation** (Geiger, Verma and Pearl 1990; Pearl 1995, §2.1: the
conditional independencies implied by the factorization over a DAG are exactly the
d-separations; Meek 1995, Theorem 1 and footnote 1, for a fixed discrete state space): if
pairwise disjoint sets `X, Y, Z` of nodes are not d-separated in the graph of `b`, then some
Bayesian network on the same graph and the same finite state space, with at least two states,
makes `X` and `Y` conditionally dependent given `Z`. -/
theorem exists_not_condIndep_of_not_dSeparated {α : Type*} [Fintype α] [Nontrivial α]
    (b : BayesNet α n) (X Y Z : Finset (Fin n)) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (h : ¬b.DSeparated ↑X ↑Y ↑Z) :
    ∃ b' : BayesNet α n, b'.pa = b.pa ∧ ¬CondIndep b'.joint ↑X ↑Y ↑Z := by
  classical
  obtain ⟨a₀, a₁, hne⟩ := exists_pair_ne α
  simp only [DSeparated, not_forall, exists_prop] at h
  obtain ⟨x, hx, y, hy, π₀, hπ₀, hb⟩ := h
  rw [Finset.mem_coe] at hx hy
  obtain ⟨π, hp, ha, hcl⟩ := b.exists_clean Z (b.cSum Z π₀ + 1) π₀ (Nat.lt_succ_self _) hπ₀
    ((b.activeL_iff Z π₀).2 hb)
  have hxy : x ≠ y := fun e => Finset.disjoint_left.1 hXY hx (e ▸ hy)
  have hxZ : x ∉ Z := Finset.disjoint_left.1 hXZ hx
  have hyZ : y ∉ Z := Finset.disjoint_left.1 hYZ hy
  refine ⟨b.witness Z π a₀ a₁, rfl, fun hci => ?_⟩
  -- reduce to the single nodes `x` and `y`
  have h1 : CondIndep (b.witness Z π a₀ a₁).joint ↑({x} : Finset (Fin n)) ↑Y ↑Z :=
    condIndep_mono_left hci (Finset.singleton_subset_iff.2 hx) hXY
  have h2 : CondIndep (b.witness Z π a₀ a₁).joint ↑({y} : Finset (Fin n))
      ↑({x} : Finset (Fin n)) ↑Z :=
    condIndep_mono_left (condIndep_symm h1) (Finset.singleton_subset_iff.2 hy)
      (Finset.disjoint_singleton_right.2 fun hxY => Finset.disjoint_left.1 hXY hx hxY)
  set x' : Fin n → α := fun v => if v = y then a₁ else a₀ with hx'
  have h3 := condIndep_symm h2 x'
  have hnn : ∀ ω, 0 ≤ (b.witness Z π a₀ a₁).joint ω := fun ω =>
    (b.witness Z π a₀ a₁).toChain.joint_nonneg n ω
  have hpos : ∀ (U : Set (Fin n)) (ω : Fin n → α), (∀ v ∈ U, ω v = x' v) →
      0 < (b.witness Z π a₀ a₁).joint ω → 0 < marginal (b.witness Z π a₀ a₁).joint U x' := by
    intro U ω hω hPω
    unfold marginal
    exact lt_of_lt_of_le hPω (Finset.single_le_sum (fun ω' _ => hnn ω') (by simpa using hω))
  have hx'Z : ∀ v ∈ Z, x' v = a₀ := fun v hv => by
    simp only [hx']
    exact ite_eq_right fun (e : v = y) => hyZ (e ▸ hv)
  have hx'x : x' x = a₀ := ite_eq_right hxy
  have hx'y : x' y = a₁ := ite_eq_left rfl
  -- under a law of the witness, `Z` at `a₀` forces equal values at `x` and `y`
  have hzero : marginal (b.witness Z π a₀ a₁).joint
      (↑({x} : Finset (Fin n)) ∪ ↑({y} : Finset (Fin n)) ∪ ↑Z) x' = 0 := by
    unfold marginal
    refine Finset.sum_eq_zero fun ω hω => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton,
      Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe] at hω
    by_contra hPω
    have hpar := parity (b.AEdge Z π) (fun u => ind (ω u = a₁))
      fun k hk => b.witness_constraint ha hne hPω k hk
    have hsum : ∑ u, (ind (∃ v, b.AEdge Z π v u) + ∑ w, ind (b.AEdge Z π u w)) *
        ind (ω u = a₁) = ∑ u, (ind (u = x) + ind (u = y)) * ind (ω u = a₁) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases huZ : u ∈ Z
      · rw [hω u (Or.inr huZ), hx'Z u huZ, ind_neg hne, mul_zero, mul_zero]
      · rw [b.coef_eq hp ha hcl huZ]
    have hxy' : ∑ u, (ind (u = x) + ind (u = y)) * ind (ω u = a₁) =
        ind (ω x = a₁) + ind (ω y = a₁) := by
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_eq_single x (fun u _ hu => by rw [ind_neg hu, zero_mul]) (by simp),
          ind_pos rfl, one_mul]
      · rw [Finset.sum_eq_single y (fun u _ hu => by rw [ind_neg hu, zero_mul]) (by simp),
          ind_pos rfl, one_mul]
    rw [hsum, hxy', hω x (Or.inl (Or.inl rfl)), hω y (Or.inl (Or.inr rfl)), hx'x, hx'y,
      ind_neg hne, ind_pos rfl] at hpar
    exact absurd hpar (by decide)
  -- the configuration with every node at `a₀`
  have hP0 : 0 < (b.witness Z π a₀ a₁).joint fun _ => a₀ := by
    refine b.witness_joint_pos ha hne (fun k _ => ?_) fun _ => Or.inl rfl
    rw [ind_neg hne]
    exact (Finset.sum_eq_zero fun u _ => mul_zero _).symm
  -- the configuration with the non-colliders of `π` at `a₁`, every other node at `a₀`
  set ω₁ : Fin n → α := fun v => if v ∈ π ∧ ¬b.IsCollOn π v then a₁ else a₀ with hω₁def
  have hω₁ : ∀ v, ind (ω₁ v = a₁) = ind (v ∈ π ∧ ¬b.IsCollOn π v) := fun v => by
    refine ind_congr ?_
    simp only [hω₁def]
    split_ifs with hv
    · exact ⟨fun _ => hv, fun _ => rfl⟩
    · exact ⟨fun e => absurd e hne, fun h' => absurd h' hv⟩
  have hP1 : 0 < (b.witness Z π a₀ a₁).joint ω₁ := by
    refine b.witness_joint_pos ha hne (fun k hk => ?_) fun v => ?_
    · simp only [hω₁]
      by_cases hkπ : k ∈ π
      · obtain ⟨s, t, hπ⟩ := List.mem_iff_append.1 hkπ
        have hnd := hp.1
        have hterm : ∀ u, ind (b.AEdge Z π u k) * ind (u ∈ π ∧ ¬b.IsCollOn π u) =
            ind ((u ∈ s.getLast? ∧ b.Edge u k) ∨ (u ∈ t.head? ∧ b.Edge u k) ∨
              (False ∧ u = k)) := by
          intro u
          by_cases hu : b.AEdge Z π u k
          · obtain ⟨hnb, hek⟩ := (b.aEdge_iff_of_mem hnd hcl hπ).1 hu
            have huπ : u ∈ π := by
              rw [hπ]
              rcases hnb with hnb | hnb
              · exact List.mem_append_left _ (List.mem_of_getLast? hnb)
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_head? hnb))
            have hnc : ¬b.IsCollOn π u := fun hc => b.edge_asymm hek (b.edge_of_isCollOn hnd hc
              (by
                rcases hnb with hnb | hnb
                · exact Or.inl ((infix_left_iff hnd hπ).2 hnb)
                · exact Or.inr ((infix_right_iff hnd hπ).2 hnb)))
            rw [ind_pos hu, ind_pos ⟨huπ, hnc⟩, one_mul, ind_pos (by tauto)]
          · rw [ind_neg hu, zero_mul, ind_neg]
            rw [b.aEdge_iff_of_mem hnd hcl hπ] at hu
            tauto
        rw [Finset.sum_congr rfl fun u _ => hterm u, sum_three _ _ _ _ _ _ _ (fun _ => Iff.rfl)
          (fun v hv w hw e => by
            rw [hπ, List.nodup_append] at hnd
            exact hnd.2.2 v (List.mem_of_getLast? hv) w
              (List.mem_cons_of_mem _ (List.mem_of_head? hw)) e)
          (fun h => h.elim) (fun h => h.elim), ind_neg not_false]
        have hAB : (∃ v ∈ s.getLast?, b.Edge v k) ∨ ∃ w ∈ t.head?, b.Edge w k := by
          obtain ⟨u, hu⟩ := hk
          obtain ⟨hu1 | hu1, hu2⟩ := (b.aEdge_iff_of_mem hnd hcl hπ).1 hu
          · exact Or.inl ⟨u, hu1, hu2⟩
          · exact Or.inr ⟨u, hu1, hu2⟩
        rw [ind_congr (show k ∈ π ∧ ¬b.IsCollOn π k ↔
          ¬((∃ v ∈ s.getLast?, b.Edge v k) ∧ ∃ w ∈ t.head?, b.Edge w k) by
            rw [← isCollOn_iff b hnd hπ]; exact ⟨fun h => h.2, fun h => ⟨hkπ, h⟩⟩)]
        by_cases hA : ∃ v ∈ s.getLast?, b.Edge v k <;>
          by_cases hB : ∃ w ∈ t.head?, b.Edge w k
        · rw [ind_neg (not_not.2 ⟨hA, hB⟩), ind_pos hA, ind_pos hB]
          decide
        · rw [ind_pos fun h => hB h.2, ind_pos hA, ind_neg hB]
          decide
        · rw [ind_pos fun h => hA h.1, ind_neg hA, ind_pos hB]
          decide
        · exact absurd hAB fun h => h.elim hA hB
      · rw [ind_neg fun h => hkπ h.1]
        refine (Finset.sum_eq_zero fun u _ => ?_).symm
        by_cases hu : b.AEdge Z π u k
        · rcases hu with ⟨huk | huk, -⟩ | ⟨hu, rfl⟩
          · exact absurd (huk.subset (by simp)) hkπ
          · exact absurd (huk.subset (by simp)) hkπ
          · rw [ind_neg (show ¬(u ∈ π ∧ ¬b.IsCollOn π u) from
              fun h => h.2 (b.isCollOn_of_mem_routeSet hcl hu h.1)), mul_zero]
        · rw [ind_neg hu, zero_mul]
    · simp only [hω₁def]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  -- conclusion
  have hyπ : y ∈ π := List.mem_of_getLast? hp.2.2.2
  have hm1 := hpos _ (fun _ => a₀) (fun v hv => by
    rw [Finset.mem_coe] at hv
    exact (hx'Z v hv).symm) hP0
  have hm2 := hpos (↑({x} : Finset (Fin n)) ∪ ↑Z) (fun _ => a₀) (fun v hv => by
    simp only [Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff,
      Finset.mem_coe] at hv
    rcases hv with rfl | hv
    · exact hx'x.symm
    · exact (hx'Z v hv).symm) hP0
  have hm3 := hpos (↑({y} : Finset (Fin n)) ∪ ↑Z) ω₁ (fun v hv => by
    simp only [Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff,
      Finset.mem_coe] at hv
    rcases hv with rfl | hv
    · rw [hx'y]
      exact ite_eq_left ⟨hyπ, b.not_isCollOn_last hp⟩
    · simp only [hω₁def]
      rw [hx'Z v hv]
      refine ite_eq_right fun h => h.2 ?_
      exact b.isCollOn_of_mem hp ha hxZ hyZ h.1 hv) hP1
  rw [hzero, zero_mul] at h3
  exact (mul_pos hm2 hm3).ne' h3.symm

end BayesNet

end Cslib.MachineLearning.GraphicalModels
