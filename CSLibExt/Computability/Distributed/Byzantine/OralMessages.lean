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

/-- **Majority of a multiset.** The majority of a finite multiset $s$ of values is the value $x$
such that more than half of the elements of $s$ are equal to $x$ (counted with multiplicity),
if there is one (there is at most one), and a fixed default value (retreat) otherwise. -/
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

/-- **A value filling more than half of a multiset is its majority.** If more than half of the
elements of a multiset $s$ of values are equal to $x$ (counted with multiplicity), then the
majority of $s$ is $x$. -/
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

/-- **Majority falls back to the default value.** If, for every value $x$, at most half of the
elements of a multiset $s$ of values are equal to $x$ (counted with multiplicity), then the
majority of $s$ is the default value (retreat). -/
theorem majority_eq_default {s : Multiset V} (h : ∀ x, 2 * s.count x ≤ Multiset.card s) :
    majority s = default := by
  unfold majority
  split
  · next hex =>
    obtain ⟨x, _, hx⟩ := hex
    exact absurd hx (not_lt.mpr (h x))
  · rfl

variable (loyal : G → Prop) [DecidablePred loyal] (adv : List G → G → V)

/-- **Value received from a commander.** Fix a predicate saying which generals are loyal and an
adversary $\mathrm{adv}$ that assigns a value to each pair of a finite sequence of generals and a
recipient. The value that lieutenant $p$ receives from commander $c$, who holds the value $v$ and
whose superiors form the sequence $\sigma$, is $v$ if $c$ is loyal, and is
$\mathrm{adv}(\sigma c, p)$ if $c$ is a traitor, where $\sigma c$ is $\sigma$ followed by $c$. -/
def received (c : G) (v : V) (path : List G) (p : G) : V :=
  if loyal c then v else adv (path ++ [c]) p

/-- **The oral messages algorithm.** Fix which generals are loyal and a strategy for the traitors,
which assigns a value to each list of generals and each recipient. Let $c$ be a commander holding
the value $v$, let $\sigma$ be the list of the commanders above $c$, and let $S$ be a finite set
of lieutenants. For a general $q$, let $r_q$ be the value $q$ receives from $c$: $v$ if $c$ is
loyal, and otherwise the value the strategy assigns to the list $\sigma c$ ($\sigma$ followed by
$c$) and the recipient $q$. The value that a general $p$ decides under $\mathrm{OM}(m)$ is defined
by recursion on $m$. Under $\mathrm{OM}(0)$, $p$ decides $r_p$. Under $\mathrm{OM}(m + 1)$, $p$
decides the majority of the multiset of values $w_q$ for $q \in S$, where $w_p = r_p$ and, for
$q \ne p$, $w_q$ is the value $p$ decides under $\mathrm{OM}(m)$ when $q$, holding $r_q$ with the
superiors $\sigma c$, sends it to the lieutenants $S \setminus \{q\}$. -/
def om : ℕ → G → Finset G → V → List G → G → V
  | 0, c, _, v, path, p => received loyal adv c v path p
  | m + 1, c, S, v, path, p => majority (S.val.map fun q ↦
      if q = p then received loyal adv c v path p
      else om m q (S.erase q) (received loyal adv c v path q) (path ++ [c]) p)

variable {loyal adv}

omit [DecidableEq G] [DecidableEq V] [Inhabited V] in
/-- **A loyal commander sends its value.** If the commander $c$ is loyal, then for every value $v$,
every list of superiors of $c$ and every general $p$, the value $p$ receives from $c$ is $v$. -/
@[simp]
theorem received_of_loyal {c : G} (hc : loyal c) (v : V) (path : List G) (p : G) :
    received loyal adv c v path p = v := by
  simp [received, hc]

omit [DecidableEq G] [DecidableEq V] [Inhabited V] in
/-- **A traitorous commander sends the adversary's value.** Fix which generals are loyal and an
adversary $\mathrm{adv}$ that assigns a value to each pair of a list of generals and a recipient.
If the commander $c$ is a traitor, then for every value $v$, every list $\sigma$ of superiors of
$c$ and every general $p$, the value $p$ receives from $c$ is $\mathrm{adv}(\sigma c, p)$, where
$\sigma c$ is $\sigma$ followed by $c$. -/
@[simp]
theorem received_of_not_loyal {c : G} (hc : ¬ loyal c) (v : V) (path : List G) (p : G) :
    received loyal adv c v path p = adv (path ++ [c]) p := by
  simp [received, hc]

/-- **A loyal commander is obeyed under oral messages.** Let $m$ and $k$ be natural numbers, and
let a loyal commander $c$ run $\mathrm{OM}(m)$ with a value $v$ and any list of superiors, sending
to a finite set $S$ of lieutenants. If $2k + m < |S| + 1$ (more than $2k + m$ generals when
$c \notin S$) and at most $k$ of the generals in $S \cup \{c\}$ are traitors, then, whatever the
traitors send, every loyal lieutenant $p \in S$ decides $v$.

This is Lemma 1 of Lamport–Shostak–Pease. -/
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

/-- **Validity under oral messages (IC2).** Let a loyal commander $c$ run $\mathrm{OM}(m)$ with a
value $v$ and any list of superiors, sending to a finite set $S$ of lieutenants. If
$3m < |S| + 1$ (more than $3m$ generals when $c \notin S$) and at most $m$ of the generals in
$S \cup \{c\}$ are traitors, then, whatever the traitors send, every loyal lieutenant $p \in S$
decides $v$.

This is condition IC2 of Theorem 1 of Lamport–Shostak–Pease. -/
theorem om_valid {m : ℕ} {c : G} {S : Finset G} (v : V) (path : List G)
    (hS : 3 * m < S.card + 1) (hm : ((insert c S).filter (¬ loyal ·)).card ≤ m)
    (hc : loyal c) {p : G} (hp : p ∈ S) (hpl : loyal p) :
    om loyal adv m c S v path p = v :=
  om_eq_of_loyal v path hc (by omega) hm hp hpl

/-- **Agreement under oral messages (IC1).** Let a commander $c$ run $\mathrm{OM}(m)$ with a value
$v$ and any list of superiors, sending to a finite set $S$ of lieutenants with $c \notin S$. If
there are more than $3m$ generals, that is $3m < |S| + 1$, and at most $m$ of the generals in
$S \cup \{c\}$ are traitors, then, whatever the traitors send, any two loyal lieutenants
$p, p' \in S$ decide the same value.

This is condition IC1 of Theorem 1 of Lamport–Shostak–Pease. -/
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

/-- **Oral messages achieve interactive consistency.** Let a commander $c$ run $\mathrm{OM}(m)$
with a value $v$ and any list of superiors, sending to a finite set $S$ of lieutenants with
$c \notin S$. If there are more than $3m$ generals, that is $3m < |S| + 1$, and at most $m$ of
the generals in $S \cup \{c\}$ are traitors, then, whatever the traitors send, any two loyal
lieutenants in $S$ decide the same value (IC1), and if $c$ is loyal, every loyal lieutenant in
$S$ decides $v$ (IC2).

This is Theorem 1 of Lamport–Shostak–Pease. -/
theorem om_interactive_consistency {m : ℕ} {c : G} {S : Finset G} (v : V) (path : List G)
    (hcS : c ∉ S) (hS : 3 * m < S.card + 1)
    (hm : ((insert c S).filter (¬ loyal ·)).card ≤ m) :
    (∀ p ∈ S, ∀ p' ∈ S, loyal p → loyal p' →
        om loyal adv m c S v path p = om loyal adv m c S v path p') ∧
      (loyal c → ∀ p ∈ S, loyal p → om loyal adv m c S v path p = v) :=
  ⟨fun _ hp _ hp' hpl hpl' ↦ om_agree v path hcS hS hm hp hp' hpl hpl',
    fun hc _ hp hpl ↦ om_valid v path hS hm hc hp hpl⟩

/-- **The oral messages algorithm solves the Byzantine generals problem.** Let $G$ be a finite set
of more than $3m$ generals, at most $m$ of whom are traitors, and let the commander $c \in G$ run
$\mathrm{OM}(m)$ with the value $v$, with no superiors and with all the other generals as
lieutenants. Then, whatever the traitors send, any two loyal lieutenants decide the same value,
and if $c$ is loyal, every loyal lieutenant decides $v$.

This is Theorem 1 of Lamport–Shostak–Pease, applied to all the generals. -/
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
