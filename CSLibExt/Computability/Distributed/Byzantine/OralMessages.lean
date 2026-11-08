/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Byzantine generals with oral messages
-/
module

public import Mathlib.Data.Fintype.Card

/-!
# The oral messages algorithm `OM(m)` solves the Byzantine generals problem

The oral messages algorithm of L. Lamport, R. Shostak and M. Pease (*The Byzantine Generals
Problem*, ACM TOPLAS 4(3), 1982). A commander sends a value (an order) to the lieutenants; the
loyal lieutenants must agree on a value (IC1), and if the commander is loyal they must all decide
the value it sent (IC2). Messages are oral: a traitor may relay anything, and a recipient knows
who sent it a message. With at most `m` traitors among more than `3 m` generals, `OM(m)` achieves
both.

Traitors are fully arbitrary. A traitor `s` relaying along the path `σ` of commanders above it,
ending with `s`, sends `adv σ r` to the recipient `r`; the theorems hold for every `adv`. Each
message of the algorithm is determined by its path and recipient, so every adaptive strategy of
the traitors is such a function for the value the commander starts from.

## Main definitions

* `majority`: the value filling more than half of a multiset of values, and `default` (retreat)
  if there is none.
* `received`: the value a lieutenant receives from a commander, given the commander's value.
* `om`: the algorithm `OM(m)`; `om loyal adv m c S v path p` is the value lieutenant `p` decides
  when commander `c` holds `v` and the lieutenants are `S`.

## Main results

* `om_eq_of_loyal`: Lemma 1 of LSP. If the commander is loyal, there are more than `2 k + m`
  generals and at most `k` traitors, every loyal lieutenant decides the commander's value.
* `om_agree` and `om_valid`: the two halves of Theorem 1 of LSP. With more than `3 m` generals
  and at most `m` traitors, the loyal lieutenants decide the same value (IC1), which is the
  commander's value if it is loyal (IC2). `om_interactive_consistency` combines them.
* `byzantine_generals`: Theorem 1 for all the generals of a finite type, starting from an empty
  path.

## References

* L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM Transactions on
  Programming Languages and Systems 4(3), 1982: algorithm `OM(m)`, Lemma 1, Theorem 1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.Byzantine.OralMessages

variable {G V : Type*} [DecidableEq G] [DecidableEq V] [Inhabited V]

omit [Inhabited V] in
/-- Two different values cannot together fill more than all of a multiset. -/
private theorem count_add_count_le {s : Multiset V} {x y : V} (hxy : x ≠ y) :
    s.count x + s.count y ≤ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.count_cons, Multiset.card_cons]
    split_ifs with hx hy hy
    · exact absurd (hx.trans hy.symm) hxy
    all_goals omega

/-- The majority of a multiset of values: the value that fills more than half of it, and
`default` (retreat) if there is none. -/
def majority (s : Multiset V) : V :=
  haveI := Multiset.decidableExistsMultiset (m := s) (p := fun x ↦ Multiset.card s < 2 * s.count x)
  if h : ∃ x ∈ s, Multiset.card s < 2 * s.count x then
    s.choose (fun x ↦ Multiset.card s < 2 * s.count x) (by
      obtain ⟨x, hx, hc⟩ := h
      refine ⟨x, ⟨hx, hc⟩, fun y ⟨_, hy⟩ ↦ ?_⟩
      by_contra hyx
      have := count_add_count_le (s := s) hyx
      omega)
  else default

/-- A value that fills more than half of a multiset is its majority. -/
theorem majority_eq_of_lt_count {s : Multiset V} {x : V} (h : Multiset.card s < 2 * s.count x) :
    majority s = x := by
  have hx : x ∈ s := Multiset.count_pos.mp (by omega)
  have hex : ∃ y ∈ s, Multiset.card s < 2 * s.count y := ⟨x, hx, h⟩
  rw [majority, dite_eq_left hex]
  generalize_proofs hp
  by_contra hne
  have := Multiset.choose_property _ s hp
  have := count_add_count_le (s := s) hne
  omega

/-- Without a value filling more than half of the multiset, the majority is `default`
(retreat). -/
theorem majority_eq_default {s : Multiset V} (h : ∀ x, 2 * s.count x ≤ Multiset.card s) :
    majority s = default := by
  unfold majority
  split
  · next hex =>
    obtain ⟨x, _, hx⟩ := hex
    exact absurd hx (not_lt.mpr (h x))
  · rfl

variable (loyal : G → Prop) [DecidablePred loyal] (adv : List G → G → V)

/-- The value lieutenant `p` receives from commander `c`, who holds the value `v` and has the
superiors `path`: a loyal commander sends `v`, a traitor sends `adv (path ++ [c]) p`. -/
def received (c : G) (v : V) (path : List G) (p : G) : V :=
  if loyal c then v else adv (path ++ [c]) p

/-- The oral messages algorithm `OM(m)`: the value lieutenant `p` decides when commander `c`,
with superiors `path`, holds the value `v` and sends it to the lieutenants `S`. In `OM(0)`, `p`
takes the value it receives. In `OM(m + 1)`, every lieutenant `q` relays the value it received
to the others by `OM(m)`, as the commander of the lieutenants `S.erase q`, and `p` takes the
majority of the value it received itself and the values it decided for the other lieutenants. -/
def om : ℕ → G → Finset G → V → List G → G → V
  | 0, c, _, v, path, p => received loyal adv c v path p
  | m + 1, c, S, v, path, p => majority (S.val.map fun q ↦
      if q = p then received loyal adv c v path p
      else om m q (S.erase q) (received loyal adv c v path q) (path ++ [c]) p)

variable {loyal adv}

omit [DecidableEq G] [DecidableEq V] [Inhabited V] in
/-- A loyal commander sends its value. -/
@[simp]
theorem received_of_loyal {c : G} (hc : loyal c) (v : V) (path : List G) (p : G) :
    received loyal adv c v path p = v := by
  simp [received, hc]

omit [DecidableEq G] [DecidableEq V] [Inhabited V] in
/-- A traitorous commander sends what the adversary chooses for its path and the recipient. -/
@[simp]
theorem received_of_not_loyal {c : G} (hc : ¬ loyal c) (v : V) (path : List G) (p : G) :
    received loyal adv c v path p = adv (path ++ [c]) p := by
  simp [received, hc]

/-- **Lemma 1** (Lamport–Shostak–Pease). If the commander `c` is loyal, there are more than
`2 k + m` generals (the lieutenants `S` and the commander) and at most `k` of them are traitors,
every loyal lieutenant decides the commander's value `v` under `OM(m)`. -/
theorem om_eq_of_loyal {m k : ℕ} {c : G} {S : Finset G} (v : V) (path : List G)
    (hc : loyal c) (hS : 2 * k + m < S.card + 1)
    (hk : ((insert c S).filter (¬ loyal ·)).card ≤ k) {p : G} (hp : p ∈ S) (hpl : loyal p) :
    om loyal adv m c S v path p = v := by
  induction m generalizing c S v path p with
  | zero => simp [om, received, hc]
  | succ m ih =>
    rw [om]
    apply majority_eq_of_lt_count
    rw [Multiset.card_map, Multiset.count_map, ← Finset.filter_val, Finset.card_val,
      Finset.card_val]
    have htr : (S.filter (¬ loyal ·)).card ≤ k :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert c S))).trans hk
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) loyal
    refine lt_of_lt_of_le (by omega) (Nat.mul_le_mul_left 2 (Finset.card_le_card
      (s := S.filter loyal) fun q hq ↦ ?_))
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    by_cases hqp : q = p
    · simp [hqp, received, hc]
    rw [ite_eq_right hqp, received, ite_eq_left hc]
    refine (ih v (path ++ [c]) hq.2 ?_ ?_ (Finset.mem_erase.mpr ⟨Ne.symm hqp, hp⟩) hpl).symm
    · rw [Finset.card_erase_of_mem hq.1]
      omega
    · rw [Finset.insert_erase hq.1]
      exact htr

/-- **Validity** (IC2 of Theorem 1, Lamport–Shostak–Pease). With more than `3 m` generals and at
most `m` traitors, if the commander is loyal, every loyal lieutenant decides its value under
`OM(m)`. -/
theorem om_valid {m : ℕ} {c : G} {S : Finset G} (v : V) (path : List G)
    (hS : 3 * m < S.card + 1) (hm : ((insert c S).filter (¬ loyal ·)).card ≤ m)
    (hc : loyal c) {p : G} (hp : p ∈ S) (hpl : loyal p) :
    om loyal adv m c S v path p = v :=
  om_eq_of_loyal v path hc (by omega) hm hp hpl

/-- **Agreement** (IC1 of Theorem 1, Lamport–Shostak–Pease). With more than `3 m` generals and
at most `m` traitors, any two loyal lieutenants decide the same value under `OM(m)`. -/
theorem om_agree {m : ℕ} {c : G} {S : Finset G} (v : V) (path : List G) (hcS : c ∉ S)
    (hS : 3 * m < S.card + 1) (hm : ((insert c S).filter (¬ loyal ·)).card ≤ m)
    {p p' : G} (hp : p ∈ S) (hp' : p' ∈ S) (hpl : loyal p) (hpl' : loyal p') :
    om loyal adv m c S v path p = om loyal adv m c S v path p' := by
  induction m generalizing c S v path p p' with
  | zero =>
    by_cases hc : loyal c
    · rw [om_valid v path hS hm hc hp hpl, om_valid v path hS hm hc hp' hpl']
    · have : c ∈ (insert c S).filter (¬ loyal ·) := by simp [hc]
      have := Finset.card_pos.mpr ⟨c, this⟩
      omega
  | succ m ih =>
    by_cases hc : loyal c
    · rw [om_valid v path hS hm hc hp hpl, om_valid v path hS hm hc hp' hpl']
    have hSm : (S.filter (¬ loyal ·)).card ≤ m := by
      rw [Finset.filter_insert, ite_eq_left hc, Finset.card_insert_of_notMem
        (fun h ↦ hcS (Finset.mem_filter.mp h).1)] at hm
      omega
    have hsub : ∀ q ∈ S, ((insert q (S.erase q)).filter (¬ loyal ·)).card ≤ m := by
      intro q hq
      rwa [Finset.insert_erase hq]
    have hcard : ∀ q ∈ S, (S.erase q).card + 1 = S.card := fun q hq ↦
      Finset.card_erase_add_one hq
    rw [om, om]
    congr 1
    refine Multiset.map_congr rfl fun q hq ↦ ?_
    have hq : q ∈ S := hq
    by_cases hqp : q = p <;> by_cases hqp' : q = p'
    · subst hqp hqp'
      rfl
    · subst hqp
      rw [ite_eq_left rfl, ite_eq_right hqp']
      refine (om_eq_of_loyal _ _ hpl ?_ (hsub q hq) ?_ hpl').symm
      · have := hcard q hq
        omega
      · exact Finset.mem_erase.mpr ⟨Ne.symm hqp', hp'⟩
    · subst hqp'
      rw [ite_eq_right hqp, ite_eq_left rfl]
      refine om_eq_of_loyal _ _ hpl' ?_ (hsub q hq) ?_ hpl
      · have := hcard q hq
        omega
      · exact Finset.mem_erase.mpr ⟨Ne.symm hqp, hp⟩
    · rw [ite_eq_right hqp, ite_eq_right hqp']
      refine ih _ _ (Finset.notMem_erase q S) ?_ (hsub q hq)
        (Finset.mem_erase.mpr ⟨Ne.symm hqp, hp⟩) (Finset.mem_erase.mpr ⟨Ne.symm hqp', hp'⟩)
        hpl hpl'
      have := hcard q hq
      omega

/-- **Theorem 1** (Lamport–Shostak–Pease). With more than `3 m` generals and at most `m`
traitors, `OM(m)` satisfies the interactive consistency conditions: any two loyal lieutenants
decide the same value (IC1), and if the commander is loyal, every loyal lieutenant decides the
value it sent (IC2). -/
theorem om_interactive_consistency {m : ℕ} {c : G} {S : Finset G} (v : V) (path : List G)
    (hcS : c ∉ S) (hS : 3 * m < S.card + 1)
    (hm : ((insert c S).filter (¬ loyal ·)).card ≤ m) :
    (∀ p ∈ S, ∀ p' ∈ S, loyal p → loyal p' →
        om loyal adv m c S v path p = om loyal adv m c S v path p') ∧
      (loyal c → ∀ p ∈ S, loyal p → om loyal adv m c S v path p = v) :=
  ⟨fun _ hp _ hp' hpl hpl' ↦ om_agree v path hcS hS hm hp hp' hpl hpl',
    fun hc _ hp hpl ↦ om_valid v path hS hm hc hp hpl⟩

/-- **The Byzantine generals problem is solved by `OM(m)`** (Theorem 1 of Lamport–Shostak–Pease
for all generals). If there are more than `3 m` generals of a finite type, at most `m` of them
traitors, and commander `c` runs `OM(m)` with all the other generals as lieutenants, then any two
loyal lieutenants decide the same value, and if `c` is loyal, every loyal lieutenant decides
`v`. -/
theorem byzantine_generals [Fintype G] {m : ℕ} (c : G) (v : V) (hG : 3 * m < Fintype.card G)
    (hm : (Finset.univ.filter (¬ loyal ·)).card ≤ m) :
    (∀ p p', p ≠ c → p' ≠ c → loyal p → loyal p' →
        om loyal adv m c (Finset.univ.erase c) v [] p =
          om loyal adv m c (Finset.univ.erase c) v [] p') ∧
      (loyal c → ∀ p, p ≠ c → loyal p → om loyal adv m c (Finset.univ.erase c) v [] p = v) := by
  have hcS : c ∉ Finset.univ.erase c := Finset.notMem_erase c _
  have hS : 3 * m < (Finset.univ.erase c).card + 1 := by
    rw [Finset.card_erase_add_one (Finset.mem_univ c)]
    exact hG
  have hm' : ((insert c (Finset.univ.erase c)).filter (¬ loyal ·)).card ≤ m := by
    rwa [Finset.insert_erase (Finset.mem_univ c)]
  obtain ⟨h1, h2⟩ := om_interactive_consistency (adv := adv) v [] hcS hS hm'
  exact ⟨fun p p' hp hp' ↦ h1 p (by simpa using hp) p' (by simpa using hp'),
    fun hc p hp ↦ h2 hc p (by simpa using hp)⟩

end Cslib.Distributed.Byzantine.OralMessages
