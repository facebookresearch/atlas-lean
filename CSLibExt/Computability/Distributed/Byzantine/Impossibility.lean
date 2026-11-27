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

/-- **Oral-message protocol.** A synchronous oral-message protocol for a set $G$ of generals, with
orders in $V$, local states in $\sigma$ and messages in $M$, consists of an initial state for
each general in $G$, used by the generals other than the commander; an initial state of the
commander for each order in $V$; a sending function giving, for each round $r$, each general $j$
in each state $s$ and each general $i$, the message in $M$ that $j$ sends to $i$ in round $r$; a
transition function giving, for each round $r$, each general $i$ in each state $s$ and each
assignment of a message to every sender $j$, the state of $i$ after round $r$; and a decision
function giving the value in $V$ that each general decides in each state.

The commander is not part of the protocol: it is chosen when the protocol is run. In each round
every general sends its messages from its current state and then moves to the state given by the
transition function on the messages it received. Only the commander's initial state depends on
the order. -/
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

/-- **Local views determine states.** Let $P$ be an oral-message protocol for the generals $G$
with states $\sigma$ and messages $M$. Let $N$ be a type of nodes, node $k$ running the code of
the general $\rho(k) \in G$, and let $L$ be a property of nodes. For each round $r$ and node
$k$, let $s_r(k), s'_r(k) \in \sigma$ be two states and $\mu_r(k), \mu'_r(k) : G \to M$ two
families of received messages. Suppose that for every $r$ and every node $k$ satisfying $L$,
$s_{r+1}(k)$ is the state to which general $\rho(k)$ of $P$ moves in round $r$ from $s_r(k)$ on
the messages $\mu_r(k)$, and $s'_{r+1}(k)$ the one to which it moves from $s'_r(k)$ on
$\mu'_r(k)$; that $s_0(k) = s'_0(k)$ for every $k$ satisfying $L$; and that for every $r$, if
$s_r(k) = s'_r(k)$ for all $k$ satisfying $L$, then $\mu_r(k) = \mu'_r(k)$ for all $k$
satisfying $L$. Then $s_r(k) = s'_r(k)$ for every $r$ and every $k$ satisfying $L$. -/
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

/-- **Initial state of a general.** When the commander $c$ has order $v$, the initial state of
general $i$ is the initial state that the protocol assigns to a commander with order $v$ if
$i = c$, and the initial state that the protocol assigns to $i$ as a general other than the
commander if $i \ne c$. -/
def initState (c : G) (v : V) (i : G) : σ :=
  if i = c then P.initCommander v else P.init i

/-- **Initial state of the commander.** When the commander $c$ has order $v$, the initial state of
$c$ is the initial state that the protocol assigns to a commander with order $v$. -/
theorem initState_self (c : G) (v : V) : P.initState c v c = P.initCommander v := by
  simp [initState]

/-- **Initial state of a lieutenant.** If general $i$ is not the commander $c$, then the initial
state of $i$ when $c$ has order $v$ is the initial state that the protocol assigns to $i$ as a
general other than the commander; in particular, it does not depend on $v$. -/
theorem initState_of_ne {c i : G} (v : V) (h : i ≠ c) : P.initState c v i = P.init i := by
  simp [initState, h]

/-- **Executions of an oral-message protocol.** Let $P$ be an oral-message protocol for the
generals $G$, let $c \in G$ be the commander, $v$ its order and $S \subseteq G$ a finite set of
traitors, and let $a_r(j, i)$ be the message a traitor $j$ sends general $i$ in round $r$. The
state of general $i$ after $r$ rounds is defined by recursion on $r$. After $0$ rounds it is
the initial state of $i$ for commander $c$ and order $v$. After $r + 1$ rounds it is the state
to which $i$ moves by its code for round $r$ from its state after $r$ rounds, on receiving
$a_r(j, i)$ from each traitor $j \in S$ and, from each other general $j$, the message that $P$
has $j$ send to $i$ in round $r$ from the state of $j$ after $r$ rounds. -/
def state (c : G) (v : V) (traitors : Finset G) (adv : ℕ → G → G → M) : ℕ → G → σ
  | 0, i => P.initState c v i
  | r + 1, i => P.recv r i (state c v traitors adv r i) fun j =>
      if j ∈ traitors then adv r j i else P.send r j (state c v traitors adv r j) i

/-- **Messages received in a round.** In the execution of a protocol $P$ with commander $c$,
order $v$, a set of traitors and a behaviour $\mathrm{adv}$ of the traitors, the messages that
general $i$ receives in round $r$ form the function of the sender $j$ whose value is
$\mathrm{adv}(r, j, i)$ if $j$ is a traitor, and otherwise the message that $P$ has $j$ send to
$i$ in round $r$ from the state of $j$ after $r$ rounds. -/
def inbox (c : G) (v : V) (traitors : Finset G) (adv : ℕ → G → G → M) (r : ℕ) (i : G) :
    G → M := fun j =>
  if j ∈ traitors then adv r j i else P.send r j (P.state c v traitors adv r j) i

section Execution

variable (c : G) (v : V) (traitors : Finset G) (adv : ℕ → G → G → M)

/-- **The start of an execution.** In the execution of an oral-message protocol $P$ with
commander $c$, order $v$, any set of traitors and any traitor behaviour, every general is in
its initial state after $0$ rounds: the commander in the initial state given by the order $v$,
and every other general in its order-independent initial state. -/
theorem state_zero : P.state c v traitors adv 0 = P.initState c v := rfl

/-- **One round of an execution.** In the execution of an oral-message protocol $P$ with a given
commander, order, set of traitors and traitor behaviour, for every round $r$ and every general
$i$, the state of $i$ after $r + 1$ rounds is the state to which $i$ moves by its code for round
$r$ from its state after $r$ rounds on the messages it receives in round $r$. -/
theorem state_succ (r : ℕ) (i : G) :
    P.state c v traitors adv (r + 1) i =
      P.recv r i (P.state c v traitors adv r i) (P.inbox c v traitors adv r i) := rfl

/-- **Decision of a general.** In the execution of a protocol $P$ with commander $c$, order $v$, a
set of traitors and a behaviour of the traitors, the decision of general $i$ after $T$ rounds is
the value that the decision function of $P$ assigns to $i$ in its state after $T$ rounds. -/
def decision (T : ℕ) (i : G) : V := P.decide i (P.state c v traitors adv T i)

/-- **Agreement condition (IC1).** Consider the execution of a protocol $P$ with commander $c$,
order $v$, a set of traitors and a behaviour of the traitors. Condition IC1 holds after $T$
rounds when any two generals $i$ and $j$, neither of which is the commander or a traitor, decide
the same value after $T$ rounds of this execution. -/
def Agreement (T : ℕ) : Prop :=
  ∀ i j, i ≠ c → j ≠ c → i ∉ traitors → j ∉ traitors →
    P.decision c v traitors adv T i = P.decision c v traitors adv T j

/-- **Validity in the Byzantine generals problem.** In the execution of an oral-message protocol
with commander $c$, order $v$, a set of traitors and a traitor behaviour, condition IC2
(validity) holds after $T$ rounds if, provided the commander is loyal, every loyal general
other than the commander decides $v$ after $T$ rounds. -/
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

/-- **Solving the Byzantine generals problem.** An oral-message protocol $P$ for the generals
$G$ solves the Byzantine generals problem with commander $c \in G$ and at most $m$ traitors in
$T$ rounds if, for every order $v$, every set of at most $m$ traitors and every behaviour of
the traitors (the message each traitor sends to each general in each round), conditions IC1
(agreement) and IC2 (validity) hold after $T$ rounds. -/
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

/-- **No protocol for three generals tolerates one traitor.** Suppose there are at least two
possible orders. For every oral-message protocol for three generals $0$, $1$, $2$ with commander
$0$ and every number of rounds $T$, there are an order $v$, a general $t$ and a behaviour of $t$
such that, in the execution with order $v$ in which $t$ is the only traitor, the agreement
condition (IC1) or the validity condition (IC2) fails after $T$ rounds.

This is the theorem of Pease, Shostak and Lamport, proved here by a commander version of the
hexagon argument of Fischer, Lynch and Merritt. -/
theorem exists_violation_three [Nontrivial V] (P : OralProtocol (Fin 3) V σ M) (T : ℕ) :
    ∃ (v : V) (t : Fin 3) (adv : ℕ → Fin 3 → Fin 3 → M),
      ¬ (P.Agreement 0 v {t} adv T ∧ P.Validity 0 v {t} adv T) := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact false_of_forall P T h

/-- **No protocol for three generals solves the Byzantine generals problem with one
traitor.** Suppose there are at least two possible orders. For every oral-message protocol for
three generals $0$, $1$, $2$ with commander $0$ and every number of rounds $T$, the protocol does
not solve the Byzantine generals problem with commander $0$ and at most one traitor in $T$
rounds. -/
theorem not_solves_three [Nontrivial V] (P : OralProtocol (Fin 3) V σ M) (T : ℕ) :
    ¬ P.Solves 0 1 T := fun h =>
  false_of_forall P T fun v t adv => h v {t} (Finset.card_singleton t).le adv

/-! ### More generals: the simulation argument -/

section Simulation

/-- **Three generals simulating a protocol.** Let $P$ be an oral-message protocol for the
generals $G$ with orders in $V$, states $\sigma$ and messages $M$, let $c \in G$, let
$\mathrm{grp} : G \to \{0, 1, 2\}$ split the generals into three groups and let
$\mathrm{rep} : \{0, 1, 2\} \to G$. The simulation of $P$ with $c$, $\mathrm{grp}$ and
$\mathrm{rep}$ is the oral-message protocol for the generals $\{0, 1, 2\}$ with orders in $V$,
whose states are families $(s(i))_{i \in G}$ of states of $\sigma$ and whose messages are
families $(\mu(j, i))_{j, i \in G}$ of messages of $M$, defined as follows. A general other
than the commander starts from the family of the initial states that $P$ gives each general of
$G$ as a non-commander; the commander, with order $v$, starts from the family of the initial
states of the generals of $G$ in $P$ when $c$ is the commander with order $v$. In round $r$, a
general in state $s$ sends every general the family whose entry $(j, i)$ is the message that
general $j$ of $P$, in state $s(j)$, sends to general $i$ in round $r$. In round $r$, general
$g$ in state $s$, having received $\mu_h$ from each general $h$, moves to the family that keeps
$s(i)$ for each $i$ with $\mathrm{grp}(i) \ne g$ and, for each $i$ with $\mathrm{grp}(i) = g$,
holds the state to which general $i$ of $P$ moves in round $r$ from $s(i)$ on receiving
$\mu_{\mathrm{grp}(j)}(j, i)$ from each $j \in G$. General $g$ in final state $s$ decides
what general $\mathrm{rep}(g)$ of $P$ decides in state $s(\mathrm{rep}(g))$. -/
def simulate (c : G) (grp : G → Fin 3) (rep : Fin 3 → G) :
    OralProtocol (Fin 3) V (G → σ) (G → G → M) where
  init _ := P.init
  initCommander v := P.initState c v
  send r _ s _ j i := P.send r j (s j) i
  recv r g s msg i := if grp i = g then P.recv r i (s i) (fun j => msg (grp j) j i) else s i
  decide g s := P.decide (rep g) (s (rep g))

variable [Fintype G]

/-- **The simulation is faithful.** Let $P$ be an oral-message protocol for a finite set $G$ of
generals with messages $M$, let $c \in G$, and let $\mathrm{grp} : G \to \{0, 1, 2\}$ and
$\mathrm{rep} : \{0, 1, 2\} \to G$ with $\mathrm{grp}(c) = 0$. Fix an order $v$, a set
$S \subseteq \{0, 1, 2\}$ of traitors and a traitor behaviour $a$ for the simulation of $P$
with $c$, $\mathrm{grp}$ and $\mathrm{rep}$: in round $r$ a traitor $h$ sends general $g$ the
family $(a_r(h, g)(j, i))_{j, i \in G}$ of messages of $M$. Compare the execution of the
simulation with commander $0$, order $v$, traitors $S$ and behaviour $a$ with the execution of
$P$ with commander $c$, order $v$ and traitors $\{j \in G : \mathrm{grp}(j) \in S\}$, in which
a traitor $j$ sends general $i$ the message $a_r(\mathrm{grp}(j), \mathrm{grp}(i))(j, i)$ in
round $r$. Then for every $r \in \mathbb{N}$ and every $i \in G$ with $\mathrm{grp}(i) \notin S$,
the entry at $i$ of the state of general $\mathrm{grp}(i)$ after $r$ rounds of the first
execution equals the state of general $i$ after $r$ rounds of the second. -/
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

/-- **Simulation reduces many generals to three.** Let $P$ be an oral-message protocol for a
finite set $G$ of generals, let $c \in G$ and $m, T \in \mathbb{N}$, and suppose that $P$ solves
the Byzantine generals problem with commander $c$ and at most $m$ traitors in $T$ rounds. Let
$\mathrm{grp} : G \to \{0, 1, 2\}$ and $\mathrm{rep} : \{0, 1, 2\} \to G$ satisfy
$\mathrm{grp}(c) = 0$, $\mathrm{grp}(\mathrm{rep}(g)) = g$ for every $g \ne 0$, and
$|\{i \in G : \mathrm{grp}(i) = g\}| \le m$ for every $g$. Then the simulation of $P$ with $c$,
$\mathrm{grp}$ and $\mathrm{rep}$ solves the Byzantine generals problem for the generals
$\{0, 1, 2\}$ with commander $0$ and at most one traitor in $T$ rounds. -/
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

/-- **No protocol for $n$ generals tolerates $m$ traitors when $3 \le n \le 3m$.** Suppose there
are at least two possible orders and the set of generals is finite with $n$ elements, where
$3 \le n \le 3m$. Then for every oral-message protocol, every commander $c$ and every number of
rounds $T$, the protocol does not solve the Byzantine generals problem with commander $c$ and at
most $m$ traitors in $T$ rounds: there are an order, a set of at most $m$ traitors and a
behaviour of the traitors for which the agreement condition (IC1) or the validity condition
(IC2) fails after $T$ rounds.

This is the theorem of Lamport, Shostak and Pease, proved by reduction to three generals. -/
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
