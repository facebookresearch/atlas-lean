/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Byzantine generals: impossibility with at least a third of the generals traitors
-/
module

public import Mathlib.Data.Fintype.EquivFin

/-!
# No oral-message protocol solves the Byzantine generals problem with one traitor in three

A commander sends an order (a value of `V`) to its lieutenants, and the generals exchange
oral messages for a fixed number `T` of synchronous rounds; afterwards every lieutenant
decides a value. Some generals may be traitors. A protocol solves the Byzantine generals
problem (Lamport, Shostak and Pease) when, whatever the traitors do,

* (IC1) all loyal lieutenants decide the same value, and
* (IC2) if the commander is loyal, every loyal lieutenant decides its order.

With three generals and one traitor this is impossible, for any protocol, any state and
message types, and any number of rounds, as soon as `V` has two distinct values.

The proof is a commander version of the hexagon argument of Fischer, Lynch and Merritt, who
treat agreement with an input at every process; here two copies of the commander take the
place of the inputs. Six copies of the code run on a ring of nodes `Fin 6`, node `k` running
the code of general `k mod 3`; nodes `0` and `3` are commanders, with orders `v₀ ≠ v₁`, and
each node hears the other two generals from its two ring neighbours. Two adjacent nodes
cannot tell the ring from a three-general execution in which they are loyal and the third
general is a traitor that replays to each of them what its other neighbour sends it on the
ring. The nodes `0, 1` force node `1` to decide `v₀` (IC2), the nodes `2, 3` force node `2`
to decide `v₁` (IC2), and the nodes `1, 2`, whose commander is the traitor, force nodes `1`
and `2` to agree (IC1): a contradiction.

The simulation argument of Lamport, Shostak and Pease extends this to `n` generals and `m`
traitors whenever `3 ≤ n ≤ 3 m`: split the generals into three groups of at most `m`, the
commander in the first; three generals simulating one group each would otherwise solve the
problem with one traitor, which plays a whole group of traitors. With fewer than three
generals there is at most one lieutenant and the problem is trivially solvable.

## Main definitions

* `OralProtocol G V σ M`: a synchronous oral-message protocol for the generals `G` with
  orders in `V`, states `σ` and messages `M`, given by per-general code. Only the commander's
  initial state depends on the order.
* `OralProtocol.state`: the states of the generals in an execution with a commander, an order,
  a set of traitors and the traitors' messages.
* `OralProtocol.Agreement`, `OralProtocol.Validity`: the conditions IC1 and IC2 after `T`
  rounds.
* `OralProtocol.Solves P c m T`: `P` satisfies IC1 and IC2 for every order and every
  behaviour of at most `m` traitors.
* `OralProtocol.simulate`: three generals simulating three groups of generals.

## Main results

* `OralProtocol.states_eq_of_inbox_eq`: what a node computes depends only on its own code,
  its initial state and the messages it receives.
* `OralProtocol.exists_violation_three`: for every protocol for three generals there are an
  order, a single traitor and a traitor behaviour violating IC1 or IC2.
* `OralProtocol.not_solves_three`: no protocol for three generals tolerates one traitor.
* `OralProtocol.solves_simulate`: a protocol tolerating `m` traitors yields, by simulation, a
  protocol for three generals tolerating one traitor if every group has at most `m` generals.
* `OralProtocol.not_solves_of_card_le_three_mul`: no protocol for `n` generals tolerates `m`
  traitors when `3 ≤ n ≤ 3 m`.

## Implementation notes

Protocols are deterministic and run on a complete network; all generals share one state
type, which loses no generality (take a sum type). Randomized protocols are not covered.
Messages are oral: a receiver knows the sender of every message, and a traitor may send
anything to anyone, independently to each recipient in each round. The traitors' messages
are a fixed function of the round, the sender and the recipient. This loses nothing against
an adaptive traitor: the function is chosen after the order and the set of traitors, and since
protocols are deterministic these determine every message an adaptive traitor could react to.
A general also receives its own message, which it can compute itself. The hexagon is private
to the proof.

## References

* L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM Transactions on
  Programming Languages and Systems 4(3), 1982: §2 (impossibility results) and §3 (oral
  messages).
* M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of faults*, Journal
  of the ACM 27(2), 1980, 228–234 (the rigorous three-general proof to which §2 of the above
  refers).
* M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed
  consensus problems*, Distributed Computing 1, 1986 (the hexagon argument, for agreement with
  an input at every process, adapted here to a commander).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.Byzantine.Impossibility

/-- A synchronous oral-message protocol for the generals `G`, with orders in `V`, local states
`σ` and messages `M`. In each round `r` every general `j` sends `send r j s i` to every general `i`,
where `s` is its state, and then moves to `recv r i s msg`, where `msg j` is the message it
received from `j`. Only the commander's initial state depends on the order. -/
structure OralProtocol (G V σ M : Type*) where
  /-- The initial state of each general other than the commander. -/
  init : G → σ
  /-- The initial state of the commander, given its order. -/
  initCommander : V → σ
  /-- `send r j s i` is the message general `j`, in state `s`, sends to general `i` in round
  `r`. -/
  send : ℕ → G → σ → G → M
  /-- `recv r i s msg` is the state of general `i` after round `r`, from its state `s` and the
  message `msg j` it received from each general `j`. -/
  recv : ℕ → G → σ → (G → M) → σ
  /-- `decide i s` is the value general `i` decides in its final state `s`. -/
  decide : G → σ → V

namespace OralProtocol

variable {G V σ M : Type*} (P : OralProtocol G V σ M)

/-- Local views. Let nodes `N` run the code of the generals `role k`, with two families of
states `s` and `s'` advanced by the protocol's `recv` from the messages `inb` and `inb'`. If
the nodes satisfying `L` start in equal states, and receive equal messages whenever they are
in equal states, then they stay in equal states. -/
theorem states_eq_of_inbox_eq {N : Type*} (role : N → G) (L : N → Prop) (s s' : ℕ → N → σ)
    (inb inb' : ℕ → N → G → M)
    (hs : ∀ r k, L k → s (r + 1) k = P.recv r (role k) (s r k) (inb r k))
    (hs' : ∀ r k, L k → s' (r + 1) k = P.recv r (role k) (s' r k) (inb' r k))
    (h0 : ∀ k, L k → s 0 k = s' 0 k)
    (hinb : ∀ r, (∀ k, L k → s r k = s' r k) → ∀ k, L k → inb r k = inb' r k) :
    ∀ r k, L k → s r k = s' r k := by
  intro r
  induction r with
  | zero => exact h0
  | succ r ih =>
      intro k hk
      rw [hs r k hk, hs' r k hk, ih k hk, hinb r ih k hk]

variable [DecidableEq G]

/-- The initial state of general `i` when the commander `c` has the order `v`. -/
def initState (c : G) (v : V) (i : G) : σ :=
  if i = c then P.initCommander v else P.init i

/-- The commander starts from the state given by its order. -/
theorem initState_self (c : G) (v : V) : P.initState c v c = P.initCommander v := by
  simp [initState]

/-- A general other than the commander starts from a state independent of the order. -/
theorem initState_of_ne {c i : G} (v : V) (h : i ≠ c) : P.initState c v i = P.init i := by
  simp [initState, h]

/-- `P.state c v traitors adv r i` is the state of general `i` after `r` rounds of `P` with
commander `c`, order `v` and traitors `traitors`, where a traitor `j` sends `adv r j i` to
general `i` in round `r`. Loyal generals follow the protocol. -/
def state (c : G) (v : V) (traitors : Finset G) (adv : ℕ → G → G → M) : ℕ → G → σ
  | 0, i => P.initState c v i
  | r + 1, i => P.recv r i (state c v traitors adv r i) fun j =>
      if j ∈ traitors then adv r j i else P.send r j (state c v traitors adv r j) i

/-- The messages general `i` receives in round `r` of `P.state c v traitors adv`, indexed by
the sender. -/
def inbox (c : G) (v : V) (traitors : Finset G) (adv : ℕ → G → G → M) (r : ℕ) (i : G) :
    G → M := fun j =>
  if j ∈ traitors then adv r j i else P.send r j (P.state c v traitors adv r j) i

section Execution

variable (c : G) (v : V) (traitors : Finset G) (adv : ℕ → G → G → M)

/-- Every general starts from its initial state. -/
theorem state_zero : P.state c v traitors adv 0 = P.initState c v := rfl

/-- In each round every general moves by its code on the messages it receives. -/
theorem state_succ (r : ℕ) (i : G) :
    P.state c v traitors adv (r + 1) i =
      P.recv r i (P.state c v traitors adv r i) (P.inbox c v traitors adv r i) := rfl

/-- The value general `i` decides after `T` rounds. -/
def decision (T : ℕ) (i : G) : V := P.decide i (P.state c v traitors adv T i)

/-- Condition IC1 (agreement) after `T` rounds: all loyal lieutenants decide the same
value. -/
def Agreement (T : ℕ) : Prop :=
  ∀ i j, i ≠ c → j ≠ c → i ∉ traitors → j ∉ traitors →
    P.decision c v traitors adv T i = P.decision c v traitors adv T j

/-- Condition IC2 (validity) after `T` rounds: if the commander is loyal, every loyal
lieutenant decides its order. -/
def Validity (T : ℕ) : Prop :=
  c ∉ traitors → ∀ i, i ≠ c → i ∉ traitors → P.decision c v traitors adv T i = v

/-- IC1 is decidable for finitely many generals and decidable equality of orders. -/
instance [Fintype G] [DecidableEq V] (T : ℕ) :
    Decidable (P.Agreement c v traitors adv T) := by
  unfold Agreement; infer_instance

/-- IC2 is decidable for finitely many generals and decidable equality of orders. -/
instance [Fintype G] [DecidableEq V] (T : ℕ) :
    Decidable (P.Validity c v traitors adv T) := by
  unfold Validity; infer_instance

end Execution

/-- `P` solves the Byzantine generals problem with commander `c` and at most `m` traitors in
`T` rounds: IC1 and IC2 hold for every order, every set of at most `m` traitors and every
behaviour of the traitors. -/
def Solves (c : G) (m T : ℕ) : Prop :=
  ∀ (v : V) (traitors : Finset G), traitors.card ≤ m → ∀ adv : ℕ → G → G → M,
    P.Agreement c v traitors adv T ∧ P.Validity c v traitors adv T

/-! ### The hexagon

A commander version of the hexagon of Fischer, Lynch and Merritt: their processes each have an
input, while here nodes `0` and `3` are two copies of the commander with different orders. -/

section Hexagon

variable (P : OralProtocol (Fin 3) V σ M)

/-- The general whose code node `k` of the hexagon runs: `k mod 3`. -/
private def role (k : Fin 6) : Fin 3 := ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩

/-- The node from which node `k` of the hexagon hears general `h`: the ring neighbour running
the code of `h`, or `k` itself when `h` is its own general. -/
private def nbr (k : Fin 6) (h : Fin 3) : Fin 6 :=
  if h = role (k + 1) then k + 1 else if h = role (k - 1) then k - 1 else k

/-- Node `k` hears general `h` from a node running the code of `h`. -/
private theorem role_nbr : ∀ (k : Fin 6) (h : Fin 3), role (nbr k h) = h := by decide

/-- For adjacent nodes `a`, `a + 1`, the general played by one of them determines it. -/
private theorem node_of_role : ∀ a k : Fin 6, (k = a ∨ k = a + 1) →
    (if role k = role a then a else a + 1) = k := by decide

/-- For adjacent nodes `a`, `a + 1`, the generals other than the third one, `role (a + 2)`,
are heard from `a` or `a + 1`. -/
private theorem nbr_mem : ∀ a k : Fin 6, (k = a ∨ k = a + 1) → ∀ h : Fin 3,
    h ≠ role (a + 2) → nbr k h = a ∨ nbr k h = a + 1 := by decide

/-- The hexagon execution: node `k` runs the code of general `role k` and hears general `h`
from `nbr k h`; nodes `0` and `3` are commanders with orders `v₀` and `v₁`. -/
private def hexState (v₀ v₁ : V) : ℕ → Fin 6 → σ
  | 0, k => P.initState 0 (if k = 0 then v₀ else v₁) (role k)
  | r + 1, k => P.recv r (role k) (hexState v₀ v₁ r k) fun h =>
      P.send r h (hexState v₀ v₁ r (nbr k h)) (role k)

/-- The traitor of the three-general execution simulating the nodes `a`, `a + 1`: to the
general played by one of these nodes it sends what that node hears from it on the hexagon. -/
private def hexAdv (v₀ v₁ : V) (a : Fin 6) (r : ℕ) (j i : Fin 3) : M :=
  P.send r j (hexState P v₀ v₁ r (nbr (if i = role a then a else a + 1) j)) i

/-- Indistinguishability: in the three-general execution with order `v`, traitor
`role (a + 2)` behaving as `hexAdv`, the loyal generals played by the adjacent nodes `a` and
`a + 1` are in the states of these nodes on the hexagon, provided they start so. -/
private theorem state_eq_hexState (v₀ v₁ v : V) (a : Fin 6)
    (h0 : ∀ k, (k = a ∨ k = a + 1) → P.initState 0 v (role k) = hexState P v₀ v₁ 0 k)
    (r : ℕ) (k : Fin 6) (hk : k = a ∨ k = a + 1) :
    P.state 0 v {role (a + 2)} (hexAdv P v₀ v₁ a) r (role k) = hexState P v₀ v₁ r k := by
  refine P.states_eq_of_inbox_eq role (fun k => k = a ∨ k = a + 1)
    (fun r k => P.state 0 v {role (a + 2)} (hexAdv P v₀ v₁ a) r (role k)) (hexState P v₀ v₁)
    (fun r k => P.inbox 0 v {role (a + 2)} (hexAdv P v₀ v₁ a) r (role k))
    (fun r k h => P.send r h (hexState P v₀ v₁ r (nbr k h)) (role k))
    (fun r k _ => P.state_succ _ _ _ _ r (role k)) (fun _ _ _ => rfl) h0 ?_ r k hk
  intro r ih k hk
  funext h
  simp only [inbox, Finset.mem_singleton]
  split_ifs with ht
  · subst ht
    simp only [hexAdv, node_of_role a k hk]
  · have e := ih _ (nbr_mem a k hk h ht)
    rw [role_nbr] at e
    rw [e]

/-- The hexagon argument: if IC1 and IC2 held for every order, every single traitor and
every behaviour, nodes `1` and `2` of the hexagon would decide `v₀` and `v₁` and agree. -/
private theorem false_of_forall [Nontrivial V] (T : ℕ)
    (h : ∀ (v : V) (t : Fin 3) (adv : ℕ → Fin 3 → Fin 3 → M),
      P.Agreement 0 v {t} adv T ∧ P.Validity 0 v {t} adv T) : False := by
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  -- Nodes `0, 1`: the commander is loyal with order `v₀`, so node `1` decides `v₀`.
  have d₁ : P.decide 1 (hexState P v₀ v₁ T 1) = v₀ := by
    have e := state_eq_hexState P v₀ v₁ v₀ 0 (by
      rintro k (rfl | rfl)
      · rfl
      · exact (P.initState_of_ne _ (by decide)).trans (P.initState_of_ne _ (by decide)).symm)
      T 1 (Or.inr rfl)
    have := (h v₀ (role (0 + 2)) (hexAdv P v₀ v₁ 0)).2 (by decide) 1 (by decide) (by decide)
    rwa [decision, show (1 : Fin 3) = role 1 from rfl, e] at this
  -- Nodes `2, 3`: the commander is loyal with order `v₁`, so node `2` decides `v₁`.
  have d₂ : P.decide 2 (hexState P v₀ v₁ T 2) = v₁ := by
    have e := state_eq_hexState P v₀ v₁ v₁ 2 (by
      rintro k (rfl | rfl)
      · exact (P.initState_of_ne _ (by decide)).trans (P.initState_of_ne _ (by decide)).symm
      · rfl)
      T 2 (Or.inl rfl)
    have := (h v₁ (role (2 + 2)) (hexAdv P v₀ v₁ 2)).2 (by decide) 2 (by decide) (by decide)
    rwa [decision, show (2 : Fin 3) = role 2 from rfl, e] at this
  -- Nodes `1, 2`: the commander is the traitor, and nodes `1` and `2` agree.
  have d₁₂ : P.decide 1 (hexState P v₀ v₁ T 1) = P.decide 2 (hexState P v₀ v₁ T 2) := by
    have h0 : ∀ k : Fin 6, (k = 1 ∨ k = 1 + 1) →
        P.initState 0 v₀ (role k) = hexState P v₀ v₁ 0 k := by
      rintro k (rfl | rfl) <;>
        exact (P.initState_of_ne _ (by decide)).trans (P.initState_of_ne _ (by decide)).symm
    have e₁ := state_eq_hexState P v₀ v₁ v₀ 1 h0 T 1 (Or.inl rfl)
    have e₂ := state_eq_hexState P v₀ v₁ v₀ 1 h0 T 2 (Or.inr rfl)
    have := (h v₀ (role (1 + 2)) (hexAdv P v₀ v₁ 1)).1 1 2 (by decide) (by decide) (by decide)
      (by decide)
    rwa [decision, decision, show (1 : Fin 3) = role 1 from rfl,
      show (2 : Fin 3) = role 2 from rfl, e₁, e₂] at this
  exact hne (d₁.symm.trans (d₁₂.trans d₂))

end Hexagon

/-- **No protocol for three generals tolerates one traitor** (Pease, Shostak and Lamport;
proved by a commander version of the hexagon argument of Fischer, Lynch and Merritt). For
every protocol for the generals `Fin 3` with commander `0`, and every number of rounds `T`,
there are an order, a single traitor and a behaviour of the traitor for which IC1 or IC2
fails. -/
theorem exists_violation_three [Nontrivial V] (P : OralProtocol (Fin 3) V σ M) (T : ℕ) :
    ∃ (v : V) (t : Fin 3) (adv : ℕ → Fin 3 → Fin 3 → M),
      ¬ (P.Agreement 0 v {t} adv T ∧ P.Validity 0 v {t} adv T) := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact false_of_forall P T h

/-- **No protocol for three generals solves the Byzantine generals problem with one
traitor**, in any number of rounds. -/
theorem not_solves_three [Nontrivial V] (P : OralProtocol (Fin 3) V σ M) (T : ℕ) :
    ¬ P.Solves 0 1 T := fun h =>
  false_of_forall P T fun v t adv => h v {t} (Finset.card_singleton t).le adv

/-! ### More generals: the simulation argument -/

section Simulation

/-- The protocol for three generals in which general `g` simulates the generals `i` of `P`
with `grp i = g`. Its state holds a state for every general of `P`, of which it updates those
of its group; its message lists the messages of every general of `P` to every general of `P`,
of which the receiver reads those sent by the senders' groups; it decides what its
representative `rep g` decides. -/
def simulate (c : G) (grp : G → Fin 3) (rep : Fin 3 → G) :
    OralProtocol (Fin 3) V (G → σ) (G → G → M) where
  init _ := P.init
  initCommander v := P.initState c v
  send r _ s _ j i := P.send r j (s j) i
  recv r g s msg i := if grp i = g then P.recv r i (s i) (fun j => msg (grp j) j i) else s i
  decide g s := P.decide (rep g) (s (rep g))

variable [Fintype G]

/-- The simulation is faithful. In an execution of `P.simulate c grp rep` with traitors
`traitors`, each loyal general holds, for each general of `P` of its group, the state of that
general in the execution of `P` in which the generals of the traitors' groups are traitors
relaying the messages of the simulating traitors. -/
theorem state_simulate (c : G) (grp : G → Fin 3) (rep : Fin 3 → G) (hc : grp c = 0) (v : V)
    (traitors : Finset (Fin 3)) (adv : ℕ → Fin 3 → Fin 3 → G → G → M) (r : ℕ) (i : G)
    (hi : grp i ∉ traitors) :
    (P.simulate c grp rep).state 0 v traitors adv r (grp i) i =
      P.state c v {j | grp j ∈ traitors} (fun r j i => adv r (grp j) (grp i) j i) r i := by
  refine P.states_eq_of_inbox_eq id (fun i => grp i ∉ traitors)
    (fun r i => (P.simulate c grp rep).state 0 v traitors adv r (grp i) i) (P.state c v _ _)
    (fun r i j => (P.simulate c grp rep).inbox 0 v traitors adv r (grp i) (grp j) j i)
    (P.inbox c v _ _) (fun r i _ => ?_) (fun r i _ => P.state_succ _ _ _ _ r i)
    (fun i _ => ?_) ?_ r i hi
  · simp only [state_succ, simulate, ↓reduceIte, id]
  · by_cases h : grp i = 0
    · simp [state_zero, initState, simulate, h]
    · have hic : i ≠ c := fun e => h (e ▸ hc)
      simp [state_zero, initState, simulate, h, hic]
  · intro r ih i _
    funext j
    simp only [inbox, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hj
    · rfl
    · exact congrArg (P.send r j · i) (ih j hj)

/-- If `P` solves the problem with commander `c` and at most `m` traitors, then
`P.simulate c grp rep` solves it for three generals and one traitor, provided the commander is
in group `0`, each group `g ≠ 0` contains its representative and each group has at most `m`
generals. -/
theorem solves_simulate {c : G} {m T : ℕ} (hP : P.Solves c m T) (grp : G → Fin 3)
    (rep : Fin 3 → G) (hc : grp c = 0) (hrep : ∀ g, g ≠ 0 → grp (rep g) = g)
    (hcard : ∀ g, ({i | grp i = g} : Finset G).card ≤ m) :
    (P.simulate c grp rep).Solves 0 1 T := by
  intro v traitors ht adv
  have hTP : ({j | grp j ∈ traitors} : Finset G).card ≤ m := by
    obtain ⟨t, ht⟩ := Finset.card_le_one_iff_subset_singleton.1 ht
    refine le_trans (Finset.card_le_card fun j hj => ?_) (hcard t)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact Finset.mem_singleton.1 (ht hj)
  obtain ⟨hA, hV⟩ := hP v _ hTP (fun r j i => adv r (grp j) (grp i) j i)
  have hdec : ∀ g, g ≠ 0 → g ∉ traitors →
      (P.simulate c grp rep).decision 0 v traitors adv T g =
        P.decision c v {j | grp j ∈ traitors} (fun r j i => adv r (grp j) (grp i) j i) T
          (rep g) := by
    intro g hg hgt
    have e := P.state_simulate c grp rep hc v traitors adv T (rep g) (by rwa [hrep g hg])
    rw [hrep g hg] at e
    exact congrArg (P.decide (rep g)) e
  have hne : ∀ g, g ≠ 0 → rep g ≠ c := fun g hg h => hg (by rw [← hrep g hg, h, hc])
  have hnt : ∀ g, g ≠ 0 → g ∉ traitors → rep g ∉ ({j | grp j ∈ traitors} : Finset G) := by
    intro g hg hgt
    simpa [hrep g hg] using hgt
  refine ⟨fun g g' hg hg' hgt hg't => ?_, fun h0 g hg hgt => ?_⟩
  · rw [hdec g hg hgt, hdec g' hg' hg't]
    exact hA _ _ (hne g hg) (hne g' hg') (hnt g hg hgt) (hnt g' hg' hg't)
  · rw [hdec g hg hgt]
    exact hV (by simpa [hc] using h0) _ (hne g hg) (hnt g hg hgt)

/-- **No protocol for `n` generals tolerates `m` traitors when `3 ≤ n ≤ 3 m`** (Lamport,
Shostak and Pease, by reduction to three generals): for every protocol, every commander and
every number of rounds there are an order, at most `m` traitors and a behaviour of the
traitors for which IC1 or IC2 fails. -/
theorem not_solves_of_card_le_three_mul [Nontrivial V] (c : G) {m : ℕ}
    (h3 : 3 ≤ Fintype.card G) (hm : Fintype.card G ≤ 3 * m) (T : ℕ) : ¬ P.Solves c m T := by
  intro hP
  have hn : 0 < Fintype.card G := by omega
  -- Number the generals so that the commander is `0`, and group them by their number mod 3.
  let e : G ≃ Fin (Fintype.card G) :=
    (Fintype.equivFin G).trans (Equiv.swap (Fintype.equivFin G c) ⟨0, hn⟩)
  have he : (e c).val = 0 := by simp [e]
  let grp : G → Fin 3 := fun i => ⟨(e i).val % 3, Nat.mod_lt _ (by decide)⟩
  let rep : Fin 3 → G := fun g => e.symm ⟨g.val, by omega⟩
  refine (P.simulate c grp rep).not_solves_three T (P.solves_simulate hP grp rep ?_ ?_ ?_)
  · ext
    simp [grp, he]
  · intro g _
    ext
    simp only [grp, rep, Equiv.apply_symm_apply]
    omega
  · intro g
    calc ({i | grp i = g} : Finset G).card ≤ (Finset.range m).card :=
          Finset.card_le_card_of_injOn (fun i => (e i).val / 3) (fun i _ => ?_) ?_
      _ = m := Finset.card_range m
    · have := (e i).isLt
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro i hi i' hi' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, grp,
        Fin.ext_iff] at hi hi' h
      apply e.injective
      ext
      omega

end Simulation

end OralProtocol

end Cslib.Distributed.Byzantine.Impossibility
