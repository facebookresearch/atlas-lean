/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The LOCAL model

The LOCAL model of distributed computing (Linial 1992): the network is a finite simple graph
whose nodes are processors with distinct identifiers. Computation proceeds in synchronous rounds;
in each round every node sends a message to each neighbour, receives its neighbours' messages and
performs a local computation. States and messages range over arbitrary types and the local maps
are arbitrary functions, so message size and local computation are unrestricted.

## Model

* **Network.** A simple graph `G` on a finite type `V` of `n = Fintype.card V` nodes.
* **Identifiers.** An `IdAssignment V c` gives the nodes distinct identifiers in
  `{1, …, n ^ c}`, a range polynomial in `n` (Suomela, §5.1). For `c = 0` the range is `{1}`, so
  only networks of at most one node have an identifier assignment.
* **Inputs.** Each node also has an input from a type `I`; a one-point type models problems
  without inputs.
* **Algorithms.** A `LocalAlgorithm I S M O` runs at every node: a node with identifier `i` and
  input `x` starts in state `init i x`; a node in state `s` sends `send s j` to its neighbour with
  identifier `j`, and moves to `update s m`, where `m` is the multiset of messages its neighbours
  sent it; a node in state `s` outputs `out s`. The multiset does not record the senders; a node
  can include its identifier in its messages.
* **Knowledge.** A node starts knowing only its identifier and its input; unlike in Suomela's
  port-numbering model, it does not know its degree, and there are no ports. The maps of a
  `LocalAlgorithm` do not take `n`, but the algorithm is a parameter, so a statement may choose it
  depending on `n` or on the graph (Linial's lower bounds hold even if every processor knows the
  graph in advance, and only the identifiers are unknown). Choosing it after seeing the
  identifiers or the inputs is a different matter: such an algorithm could store a colouring for
  the given identifiers and output it in zero rounds. The locality theorems keep the algorithm and
  the number of rounds fixed.
* **Addressing.** Addressing a message by its recipient's identifier is no stronger than sending
  every neighbour the same message: `LocalAlgorithm.broadcast` sends the map `j ↦ send s j` and
  lets the recipient apply it to its own identifier, with the same outputs
  (`LocalAlgorithm.broadcast_output`). This is an equality of outputs in the abstract round model,
  where a message may be any value, a function included; it is not a finite-bit encoding or an
  effective implementation. When states can be encoded and `send` is computable, a node can send
  its encoded state instead, and the recipient evaluates `send` at its own identifier.
* **Execution.** `LocalAlgorithm.stateAfter` gives the state of every node after `k` rounds.
* **Rounds.** For `t : ℕ → ℕ`, the algorithm run as a `t`-round algorithm outputs at each node
  after `t n` rounds (`LocalAlgorithm.output`); its complexity is `t`. The run is stopped from
  outside, so the output can depend on `t n`: a node that counts rounds outputs `t n`, which is
  `n` for `t = id`, even on a graph with no edges.

## Main definitions

* `Cslib.Distributed.LocalModel.IdAssignment`, `Cslib.Distributed.LocalModel.LocalAlgorithm`.
* `Cslib.Distributed.LocalModel.LocalAlgorithm.stateAfter`,
  `Cslib.Distributed.LocalModel.LocalAlgorithm.output`.

`IdAssignment` and `LocalAlgorithm.stateAfter` carry comments instead of docstrings
(`nolint docBlame`): the docstring of `LocalAlgorithm.output` states the whole model.

## Main results

* `Cslib.Distributed.LocalModel.LocalAlgorithm.broadcast_output`: sending every neighbour the same
  message loses nothing.
* `Cslib.Distributed.LocalModel.LocalAlgorithm.stateAfter_congr_ball`: locality. After `k`
  rounds the state of a node `v` is determined by the identifiers and inputs of the nodes at
  distance at most `k` from `v` and by the neighbours of the nodes at distance less than `k`.
* `Cslib.Distributed.LocalModel.LocalAlgorithm.output_congr_ball`: the same for the output of a
  `t`-round algorithm, with radius `t n`.

## References

* N. Linial, *Locality in distributed graph algorithms*, SIAM Journal on Computing 21(1), 1992,
  pp. 193–201: §1 (the model) and §2 (what a node can know after `t` rounds).
* J. Suomela, *Distributed Algorithms*, online textbook, 2014–2019, Aalto University (PDF
  version of 2 January 2021), <https://jukkasuomela.fi/da/>: §4.3.1–4.3.2 (algorithms as state
  machines and their execution, adapted here without degrees, ports or stopping states) and §5.1
  (identifiers in `{1, …, n ^ c}`).
-/

@[expose] public section

namespace Cslib.Distributed.LocalModel

/- Identifiers from a polynomial range: an assignment of identifiers to the `n` nodes of a finite
type `V`, with exponent `c ∈ ℕ`, is an injective map from `V` to `{1, …, n ^ c}`. For `c = 0` the
range is `{1}`, so only types with at most one element have an identifier assignment. -/
@[nolint docBlame]
structure IdAssignment (V : Type*) [Fintype V] (c : ℕ) where
  /-- The identifier of each node. -/
  toFun : V → ℕ
  /-- Distinct nodes have distinct identifiers. -/
  injective : Function.Injective toFun
  /-- Identifiers lie in `{1, …, n ^ c}`, where `n` is the number of nodes. -/
  mem_Icc : ∀ v, toFun v ∈ Set.Icc 1 (Fintype.card V ^ c)

namespace IdAssignment

variable {V : Type*} [Fintype V] {c : ℕ}

instance : FunLike (IdAssignment V c) V ℕ where
  coe := toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

@[simp]
theorem toFun_eq_coe (ids : IdAssignment V c) : ids.toFun = ⇑ids :=
  rfl

theorem coe_mem_Icc (ids : IdAssignment V c) (v : V) :
    ids v ∈ Set.Icc 1 (Fintype.card V ^ c) :=
  ids.mem_Icc v

end IdAssignment

/-- **Algorithm in the LOCAL model.** An algorithm with inputs in `I`, states in `S`, messages in
`M` and outputs in `O`, the same at every node. A node with identifier `i` and input `x` starts in
state `init i x`; in each round a node in state `s` sends the message `send s j` to its neighbour
with identifier `j`, and then moves to the state `update s m`, where `m` is the multiset of
messages its neighbours sent it; a node in state `s` outputs `out s`.

Source: N. Linial, *Locality in distributed graph algorithms*, SIAM Journal on Computing
21(1), 1992, 193–201, §1. -/
structure LocalAlgorithm (I S M O : Type*) where
  /-- `init i x` is the initial state of a node with identifier `i` and input `x`. -/
  init : ℕ → I → S
  /-- `send s j` is the message a node in state `s` sends to its neighbour with identifier
  `j`. -/
  send : S → ℕ → M
  /-- `update s m` is the next state of a node in state `s` that receives the multiset `m` of
  its neighbours' messages. -/
  update : S → Multiset M → S
  /-- `out s` is the output of a node in state `s`. -/
  out : S → O

namespace LocalAlgorithm

variable {I S M O : Type*} {V : Type*} [Fintype V]

/- Execution in the LOCAL model: `A.stateAfter G ids x k v` is the state of the node `v` after `k`
synchronous rounds of the algorithm `A` on the graph `G`, where the node `u` has
identifier `ids u` and input `x u`. After `0` rounds the node `v` is in state
`A.init (ids v) (x v)`. If after `k` rounds every node `u` is in state `s u`, then after `k + 1`
rounds the node `v` is in state `A.update (s v) m`, where `m` is the multiset of the messages
`A.send (s u) (ids v)` over the neighbours `u` of `v`. -/
@[nolint docBlame]
def stateAfter (A : LocalAlgorithm I S M O) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ids : V → ℕ) (x : V → I) : ℕ → V → S
  | 0 => fun v => A.init (ids v) (x v)
  | k + 1 =>
      let s := A.stateAfter G ids x k
      fun v => A.update (s v) ((G.neighborFinset v).val.map fun u => A.send (s u) (ids v))

/-- **The LOCAL model.** The output at the node `v` of the algorithm `A` run as a `t`-round
algorithm, for a function `t : ℕ → ℕ`, on the network formed by the simple graph `G` on the
finite type `V` of `n` nodes, with the identifiers `ids` (distinct, in `{1, …, n ^ c}`) and the
inputs `x`. Each node `u` starts in the state `A.init (ids u) (x u)`. In each synchronous round,
every node in state `s` sends the message `A.send s (ids w)` to each neighbour `w`; then every
node in state `s` receives the multiset `m` of the messages its neighbours sent it and moves to
the state `A.update s m`. The output at `v` is `A.out s`, where `s` is the state of `v` after
`t n` rounds. The complexity of the algorithm is `t`, a function of the number `n` of nodes. -/
def output (A : LocalAlgorithm I S M O) (t : ℕ → ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : ℕ} (ids : IdAssignment V c) (x : V → I) (v : V) : O :=
  A.out (A.stateAfter G ids x (t (Fintype.card V)) v)

@[simp]
theorem stateAfter_zero (A : LocalAlgorithm I S M O) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ids : V → ℕ) (x : V → I) (v : V) :
    A.stateAfter G ids x 0 v = A.init (ids v) (x v) :=
  rfl

theorem stateAfter_succ (A : LocalAlgorithm I S M O) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ids : V → ℕ) (x : V → I) (k : ℕ) (v : V) :
    A.stateAfter G ids x (k + 1) v =
      A.update (A.stateAfter G ids x k v)
        ((G.neighborFinset v).val.map fun u => A.send (A.stateAfter G ids x k u) (ids v)) :=
  rfl

/- Sending every neighbour the same message loses nothing: `A.broadcast` keeps its identifier in its
state, sends every neighbour the same message, the map `j ↦ A.send s j`, and applies each map it
receives to its own identifier. The outputs are equal in this abstract round model, where messages
may be functions; this is not a finite-bit encoding. -/
@[nolint docBlame]
def broadcast (A : LocalAlgorithm I S M O) : LocalAlgorithm I (ℕ × S) (ℕ → M) O where
  init i x := (i, A.init i x)
  send p _ := A.send p.2
  update p m := (p.1, A.update p.2 (m.map fun f => f p.1))
  out p := A.out p.2

/- `A.broadcast` sends the same message to every neighbour. -/
theorem broadcast_send (A : LocalAlgorithm I S M O) (p : ℕ × S) (j j' : ℕ) :
    A.broadcast.send p j = A.broadcast.send p j' :=
  rfl

/- After `k` rounds, every node of `A.broadcast` holds its identifier and its state in `A`. -/
theorem broadcast_stateAfter (A : LocalAlgorithm I S M O) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ids : V → ℕ) (x : V → I) (k : ℕ) (v : V) :
    A.broadcast.stateAfter G ids x k v = (ids v, A.stateAfter G ids x k v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
      rw [stateAfter_succ, stateAfter_succ]
      simp only [ih]
      simp only [broadcast, Multiset.map_map, Function.comp_def]

/- `A.broadcast` has the same outputs as `A`. -/
theorem broadcast_output (A : LocalAlgorithm I S M O) (t : ℕ → ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] {c : ℕ} (ids : IdAssignment V c) (x : V → I) (v : V) :
    A.broadcast.output t G ids x v = A.output t G ids x v := by
  unfold output
  rw [broadcast_stateAfter]
  rfl

omit [Fintype V] in
/-- A walk step: a node within distance `r` of a neighbour of `v` is within distance `r + 1`
of `v`. -/
private theorem edist_lt_succ_of_adj {G : SimpleGraph V} {v u w : V} {r : ℕ} (huv : G.Adj v u)
    (h : G.edist u w < r) : G.edist v w < (r + 1 : ℕ) := by
  have htri : G.edist v w ≤ G.edist v u + G.edist u w := SimpleGraph.edist_triangle
  rw [SimpleGraph.edist_eq_one_iff_adj.mpr huv] at htri
  have hne : G.edist u w ≠ ⊤ := ne_top_of_lt h
  lift G.edist u w to ℕ using hne with d hd
  refine lt_of_le_of_lt htri ?_
  norm_cast at h ⊢
  omega

omit [Fintype V] in
/-- A walk step: a node within distance at most `r` of a neighbour of `v` is within distance
at most `r + 1` of `v`. -/
private theorem edist_le_succ_of_adj {G : SimpleGraph V} {v u w : V} {r : ℕ} (huv : G.Adj v u)
    (h : G.edist u w ≤ r) : G.edist v w ≤ (r + 1 : ℕ) := by
  have htri : G.edist v w ≤ G.edist v u + G.edist u w := SimpleGraph.edist_triangle
  rw [SimpleGraph.edist_eq_one_iff_adj.mpr huv] at htri
  have hne : G.edist u w ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top r) h
  lift G.edist u w to ℕ using hne with d hd
  refine le_trans htri ?_
  norm_cast at h ⊢
  omega

/- Locality in the LOCAL model: after `k` rounds, the state of a node `v` depends only on its
radius-`k` ball, in this sense: the identifiers and inputs of the nodes at distance at most `k`
from `v`, and the edges at the nodes at distance less than `k`. Let `G` and `G'` be simple graphs
on the same finite set of nodes, and let the identifiers `ids`, `ids'` and the inputs `x`, `x'`
agree at every node at distance at most `k` from `v` in `G`, and the neighbours of every node at
distance less than `k` from `v` be the same in `G` and `G'`. Then `v` is in the same state after
`k` rounds of the same algorithm `A` in both executions. Edges between two nodes at distance at
least `k` from `v` are not constrained. -/
theorem stateAfter_congr_ball (A : LocalAlgorithm I S M O) {G G' : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] {ids ids' : V → ℕ} {x x' : V → I} (k : ℕ)
    (v : V) (hadj : ∀ u, G.edist v u < k → ∀ w, G.Adj u w ↔ G'.Adj u w)
    (hids : ∀ u, G.edist v u ≤ k → ids u = ids' u)
    (hx : ∀ u, G.edist v u ≤ k → x u = x' u) :
    A.stateAfter G ids x k v = A.stateAfter G' ids' x' k v := by
  induction k generalizing v with
  | zero =>
      have h0 : G.edist v v ≤ ((0 : ℕ) : ℕ∞) := by simp
      simp [hids v h0, hx v h0]
  | succ k ih =>
      have hself : G.edist v v < ((k + 1 : ℕ) : ℕ∞) := by
        rw [SimpleGraph.edist_self]
        exact_mod_cast Nat.succ_pos k
      have hN : G'.neighborFinset v = G.neighborFinset v := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset]
        exact (hadj v hself w).symm
      have hle : ((k : ℕ) : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ k
      have hv : A.stateAfter G ids x k v = A.stateAfter G' ids' x' k v :=
        ih v (fun u hu => hadj u (lt_of_lt_of_le hu hle)) (fun u hu => hids u (hu.trans hle))
          (fun u hu => hx u (hu.trans hle))
      have hnb : ∀ u ∈ G.neighborFinset v,
          A.stateAfter G ids x k u = A.stateAfter G' ids' x' k u := by
        intro u hu
        have huv : G.Adj v u := (G.mem_neighborFinset v u).mp hu
        exact ih u (fun w hw => hadj w (edist_lt_succ_of_adj huv hw))
          (fun w hw => hids w (edist_le_succ_of_adj huv hw))
          (fun w hw => hx w (edist_le_succ_of_adj huv hw))
      rw [stateAfter_succ, stateAfter_succ, hN, hv, hids v hself.le]
      congr 1
      exact Multiset.map_congr rfl fun u hu => by rw [hnb u hu]

/-- **Locality of the output of a `t`-round algorithm.** Let `G` and `G'` be simple graphs on
the same finite set of `n` nodes, `ids` and `ids'` identifier assignments in `{1, …, n ^ c}`, and
`x`, `x'` inputs. If the identifiers and the inputs agree at every node at distance at most
`t n` from `v` in `G`, and the neighbours of every node at distance less than `t n` from `v` are
the same in `G` and `G'`, then the algorithm `A` run as a `t`-round algorithm outputs the same
at `v` in both networks.

Source: N. Linial, *Locality in distributed graph algorithms*, SIAM Journal on Computing
21(1), 1992, 193–201, §2. -/
theorem output_congr_ball (A : LocalAlgorithm I S M O) (t : ℕ → ℕ) {G G' : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] {c : ℕ} {ids ids' : IdAssignment V c}
    {x x' : V → I} (v : V)
    (hadj : ∀ u, G.edist v u < t (Fintype.card V) → ∀ w, G.Adj u w ↔ G'.Adj u w)
    (hids : ∀ u, G.edist v u ≤ t (Fintype.card V) → ids u = ids' u)
    (hx : ∀ u, G.edist v u ≤ t (Fintype.card V) → x u = x' u) :
    A.output t G ids x v = A.output t G' ids' x' v := by
  unfold output
  rw [A.stateAfter_congr_ball (t (Fintype.card V)) v hadj hids hx]

end LocalAlgorithm

end Cslib.Distributed.LocalModel
