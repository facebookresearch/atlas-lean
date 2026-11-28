/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.CookLevin
public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
public import MathlibExt.Computability.Complexity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# Cooper's reduction: SAT to positive-probability inference in Bayesian networks

Cooper (1990, Section 4) showed that deciding whether a variable of a Bayesian
network is true with positive probability is NP-hard, by reducing SAT: one fair
root per variable, a deterministic clause component built from binary OR nodes,
and a conjunctive output joined by small AND tables give a network whose output
is true with positive probability exactly on the satisfiable formulas.

Networks travel as rational Boolean networks (`RatNet`: parent lists and
numerator/denominator tables) with a unary bit-string encoding in the style of
the neighbouring Karp modules. The decode bridge `RatNet.toBayesNet` turns one
into a `BayesNet` with the same joint law. The construction walks the clauses
from the last one and, in each, the literals from the last one (the order in
which an emitter meets them on the SAT token stack), hands out node numbers in
that order, gives each variable one root created at its first occurrence, and
lists the nodes from last to first in the encoding.

Main results: `cnfSat_iff_outProb_pos` (the output probability is positive iff
the formula is satisfiable), `satDec_eq_bnPosDec_reduceBN` (the bit-string map
preserves the decision), polynomial size bounds, and Cooper's worked example
with output probability 5/8.

Scope: this module formalizes Cooper's construction, its semantic correctness
and output-size bounds only. It proves no polynomial running-time bound for the
map and does not package a `PolyManyOneRed` instance or an NP-hardness
corollary; the emission function and its polynomial-time machine are separate
follow-on work that will consume this construction.
-/

@[expose] public section

namespace Cslib.Complexity.Cooper

open Convexity Cslib.CookLevin Cslib.MachineLearning.GraphicalModels

/-! ### Rational Boolean networks and the decode bridge -/

/-- **Node of a rational Boolean network.** A raw pair of lists: the parent list and the table,
given as rows `(u, (num, den))`, where `u` lists the parents' values in the order of the parent
list. In general `num / den` is a rational table value; it is the probability
`P(node = true | u)` only in a well-formed row (`RatNode.WellFormed`: `0 < den` and
`num ≤ den`). A parentless node with the row `([], 2, 1)` has table entry `2`. -/
abbrev RatNode := List ℕ × List (List Bool × ℕ × ℕ)

/-- **Rational Boolean network.** A raw list of nodes: node `k` is the `k`-th entry and the output
node is the last one, so the empty network has no output node. The nodes are in topological order
(every parent of node `k` below `k`) only in a well-formed network (`RatNet.WellFormed`). -/
abbrev RatNet := List RatNode

/-- **Well-formed node.** Node `k` has distinct parents below `k`, exactly one row for each
instantiation of its parents (rows with distinct parent values of the right length, `2 ^ |pa|`
of them), and every row has `0 < den` and `num ≤ den`. -/
def RatNode.WellFormed (k : ℕ) (v : RatNode) : Prop :=
  v.1.Nodup ∧ (∀ j ∈ v.1, j < k) ∧ (v.2.map Prod.fst).Nodup ∧ v.2.length = 2 ^ v.1.length ∧
    ∀ row ∈ v.2, row.1.length = v.1.length ∧ 0 < row.2.2 ∧ row.2.1 ≤ row.2.2

/-- **Well-formed network.** The network has a node (the output) and every node is well
formed. -/
def RatNet.WellFormed (r : RatNet) : Prop :=
  r ≠ [] ∧ ∀ k (hk : k < r.length), RatNode.WellFormed k r[k]

/-- **Table entry.** The rational `num / den` of the first row with parent values `u`, and `0`
when there is none. It is the probability `P(node = true | u)` only for a well-formed node or
network; for the parentless row `([], 2, 1)` it is `2`. -/
def RatNode.prob (v : RatNode) (u : List Bool) : ℚ :=
  match v.2.find? (fun row => row.1 == u) with
  | some row => (row.2.1 : ℚ) / row.2.2
  | none => 0

/-- **Parent values.** The values under `x` of the parents of node `k`, in the order of its parent
list; a parent outside the network reads `false`. -/
def RatNet.parentVals (r : RatNet) (k : Fin r.length) (x : Fin r.length → Bool) : List Bool :=
  (r.get k).1.map fun j => if h : j < r.length then x ⟨j, h⟩ else false

/-- **Rational joint.** The product over the nodes of one factor per node: with `p` the table entry
`(r.get k).prob` at the node's parent values, the factor is `p` when node `k` is true and `1 - p`
when it is false. The empty product, for the empty network, is `1`. -/
def RatNet.ratJoint (r : RatNet) (x : Fin r.length → Bool) : ℚ :=
  ∏ k, if x k then (r.get k).prob (r.parentVals k x) else 1 - (r.get k).prob (r.parentVals k x)

/-- **Parent set.** The listed parents of node `k` that lie below `k`. -/
def RatNet.pa (r : RatNet) (k : Fin r.length) : Finset (Fin k) :=
  ((r.get k).1.filterMap fun j => if h : j < k.val then some ⟨j, h⟩ else none).toFinset

/-- **Parent values from an instantiation of the parent set**, in the order of the parent list;
a listed parent outside the parent set reads `false`. -/
def RatNet.paVals (r : RatNet) (k : Fin r.length) (y : r.pa k → Bool) : List Bool :=
  (r.get k).1.map fun j =>
    if h : j < k.val then
      if hm : (⟨j, h⟩ : Fin k) ∈ r.pa k then y ⟨⟨j, h⟩, hm⟩ else false
    else false

/-- **Bernoulli distribution.** The distribution on `Bool` with `P(true) = q`, for `q` clamped to
`[0, 1]`. -/
noncomputable def bernoulliQ (q : ℚ) : StdSimplex ℝ Bool :=
  StdSimplex.duple (s := ((max 0 (min 1 q) : ℚ) : ℝ)) (t := 1 - ((max 0 (min 1 q) : ℚ) : ℝ))
    true false
    (by exact_mod_cast le_max_left 0 (min 1 q))
    (sub_nonneg.mpr (by exact_mod_cast max_le zero_le_one (min_le_left 1 q)))
    (by ring)

/-- **The decoded network as an Atlas `BayesNet` over `ℝ`.** Node `k` has the parent set
`r.pa k`. Given values `y` of that set, the parent-value list `r.paVals k y` is formed from the
full listed parent list, in order, writing `false` at listed indices excluded from the parent set;
node `k` then has the Bernoulli distribution with `P(true) = (r.get k).prob (r.paVals k y)`, the
first matching row's `num / den` or `0` when no row matches, clamped to `[0, 1]` (which changes
nothing on a well-formed network). -/
noncomputable def RatNet.toBayesNet (r : RatNet) : BayesNet Bool r.length where
  pa := r.pa
  cpt k y := bernoulliQ ((r.get k).prob (r.paVals k y))

/-- **Probability that a node is true** in a Boolean network. -/
noncomputable def probTrue {n : ℕ} (b : BayesNet Bool n) (k : Fin n) : ℝ :=
  ∑ x : Fin n → Bool with x k = true, b.joint x

/-- **Output probability.** `P(out = true)` for the last node `out` of the decoded network, and
`0` for the empty network. -/
noncomputable def RatNet.outProb (r : RatNet) : ℝ :=
  if h : 0 < r.length then probTrue r.toBayesNet ⟨r.length - 1, Nat.sub_lt h Nat.one_pos⟩
  else 0

/-! ### Bit-string encoding (numbers in unary, as in `Cslib.Complexity.Karp.encodeE`) -/

/-- **Unary code.** `k` ones followed by a zero. -/
def unary (k : ℕ) : List Bool :=
  List.replicate k true ++ [false]

/-- **Code of a row.** The number of parent values in unary (`k` ones then a zero), the values as
bits, then `num` and `den` in unary. The row is raw: `num / den` is a rational table value, a
probability only in a well-formed row. -/
def encodeRow (row : List Bool × ℕ × ℕ) : List Bool :=
  unary row.1.length ++ row.1 ++ unary row.2.1 ++ unary row.2.2

/-- **Code of a node.** The number of parents, each parent index and the number of rows, every one
in unary (`k` ones then a zero), then the rows (`encodeRow`). -/
def encodeRatNode (v : RatNode) : List Bool :=
  unary v.1.length ++ v.1.flatMap unary ++ unary v.2.length ++ v.2.flatMap encodeRow

/-- **Code of a network.** The number of nodes in unary (`k` ones then a zero), then the nodes
from the last (the output) to the first: the order in which a machine that creates the nodes in
index order pushes them. -/
def encodeRatNet (r : RatNet) : List Bool :=
  unary r.length ++ r.reverse.flatMap encodeRatNode

/-- **Decoding a fixed number of items.** Read `n` items with `dec`, one after another, and return
them in order with the unconsumed suffix. -/
def decodeMany {α : Type} (dec : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, input => some ([], input)
  | n + 1, input => do
      let (a, rest) ← dec input
      let (items, tail) ← decodeMany dec n rest
      some (a :: items, tail)

/-- **Decoding a row.** -/
def decodeRow (input : List Bool) : Option ((List Bool × ℕ × ℕ) × List Bool) := do
  let (len, r₁) ← readUnaryLength input
  let (num, r₂) ← readUnaryLength (r₁.drop len)
  let (den, r₃) ← readUnaryLength r₂
  if len ≤ r₁.length then some ((r₁.take len, num, den), r₃) else none

/-- **Decoding a node.** -/
def decodeRatNode (input : List Bool) : Option (RatNode × List Bool) := do
  let (np, r₁) ← readUnaryLength input
  let (ps, r₂) ← decodeMany readUnaryLength np r₁
  let (nr, r₃) ← readUnaryLength r₂
  let (rows, r₄) ← decodeMany decodeRow nr r₃
  some ((ps, rows), r₄)

/-- **Decoding a network**, rejecting missing or trailing bits: the number of nodes in unary, then
that many nodes; on success the parsed list is reversed, since `encodeRatNet` writes the nodes
from last to first. Success is syntactic acceptance only: the decoded network need not be well
formed (`RatNet.WellFormed`). -/
def decodeRatNet (input : List Bool) : Option RatNet := do
  let (n, rest) ← readUnaryLength input
  let (vs, tail) ← decodeMany decodeRatNode n rest
  if tail.isEmpty then some vs.reverse else none

open Classical in
/-- **BN positivity (Cooper's PIBNETD).** The decision problem accepts the bit strings that decode
to a well-formed network whose output node is true with positive probability. -/
noncomputable def bnPosDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match decodeRatNet x with
  | some r => decide (r.WellFormed ∧ 0 < r.outProb)
  | none => false

/-! ### Cooper's construction and the reduction map -/

/-- **Root node** (truth-setting component): no parents, `P(true) = 1/2`. -/
def rootNode : RatNode := ([], [([], 1, 2)])

/-- **Constant node**: no parents; true with probability `1` for `true` and `0` for `false`. -/
def constNode (b : Bool) : RatNode := ([], [([], b.toNat, 1)])

/-- **Deterministic gate** computing `f` from the parents `i, j`; rows in the order
`ff, ft, tf, tt`. -/
def gateNode (f : Bool → Bool → Bool) (i j : ℕ) : RatNode :=
  ([i, j], [([false, false], (f false false).toNat, 1), ([false, true], (f false true).toNat, 1),
    ([true, false], (f true false).toNat, 1), ([true, true], (f true true).toNat, 1)])

/-- **OR node for a literal.** The parents are the chain output `o` and the root `v` of the
literal's variable; the node is true iff `o` is true or the root has the literal's polarity
`b`. -/
def orNode (o v : ℕ) (b : Bool) : RatNode := gateNode (fun a c => a || c == b) o v

/-- **AND node.** -/
def andNode (i j : ℕ) : RatNode := gateNode (fun a c => a && c) i j

/-- **State of the construction.** -/
structure CoopSt where
  /-- The nodes emitted so far; node `k` is the `k`-th. -/
  nodes : List RatNode
  /-- Pairs `(variable, root node)` for the variables met so far, latest first. -/
  roots : List (ℕ × ℕ)
  /-- The current output node of the AND chain. -/
  acc : ℕ

/-- **Root of a variable.** The root in the first pair of `s.roots` whose variable is `x`
(`List.lookup`), or, when there is none, a fresh root node appended now and recorded for `x`.
The definition takes an arbitrary state. -/
def coopRoot (x : ℕ) (s : CoopSt) : CoopSt × ℕ :=
  match List.lookup x s.roots with
  | some v => (s, v)
  | none =>
      ({ s with nodes := s.nodes ++ [rootNode], roots := (x, s.nodes.length) :: s.roots },
        s.nodes.length)

/-- **Adding a literal.** The root of the literal's variable, then an OR node joining it to the
chain output `o`; the OR node is the new chain output. -/
def coopLit (l : ℕ × Bool) (o : ℕ) (s : CoopSt) : CoopSt × ℕ :=
  let r := coopRoot l.1 s
  ({ r.1 with nodes := r.1.nodes ++ [orNode o r.2 l.2] }, r.1.nodes.length)

/-- **Adding literals** in list order, from the chain output `o`. -/
def coopLits : List (ℕ × Bool) → ℕ → CoopSt → CoopSt × ℕ
  | [], o, s => (s, o)
  | l :: ls, o, s =>
      let r := coopLit l o s
      coopLits ls r.2 r.1

/-- **Adding a clause.** A constant-false node, the literals of the clause from the last one, then
an AND node joining the clause output to the AND chain. The empty clause keeps its
constant-false node as its output. -/
def coopClause (C : CNFClause) (s : CoopSt) : CoopSt :=
  let s₀ : CoopSt := { s with nodes := s.nodes ++ [constNode false] }
  let r := coopLits C.reverse s.nodes.length s₀
  { r.1 with nodes := r.1.nodes ++ [andNode s.acc r.2], acc := r.1.nodes.length }

/-- **The construction.** Start from a constant-true node `0` (the output for the empty formula)
and add the clauses from the last one. -/
def coopSt (φ : CNF) : CoopSt :=
  φ.reverse.foldl (fun s C => coopClause C s) ⟨[constNode true], [], 0⟩

/-- **Cooper's network of a CNF formula.** -/
def cooperNet (φ : CNF) : RatNet :=
  (coopSt φ).nodes

/-- **The fixed no-instance**: one constant-false node. -/
def noBN : RatNet := [constNode false]

/-- **The reduction map on bit strings.** A bit string that decodes to a CNF formula `φ` goes to
the code of `cooperNet φ`; any other bit string goes to the code of `noBN`. -/
def reduceBN (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => encodeRatNet (cooperNet φ)
  | none => encodeRatNet noBN

/-- **Cooper's example `3SAT_ex`** (p. 397), with `u_i` as variable `i`:
`(u₁ ∨ u₂ ∨ u₃) ∧ (¬u₁ ∨ ¬u₂ ∨ u₃) ∧ (u₂ ∨ ¬u₃ ∨ u₄)`. -/
def cooperEx : CNF :=
  [[(1, true), (2, true), (3, true)], [(1, false), (2, false), (3, true)],
    [(2, true), (3, false), (4, true)]]

/-- **Unsatisfiable three-clause control**: `u₁ ∧ (¬u₁ ∨ u₂) ∧ ¬u₂`. -/
def cooperUnsat : CNF :=
  [[(1, true)], [(1, false), (2, true)], [(2, false)]]

/-! ### Target statements -/

theorem RatNode.prob_nonneg (k : ℕ) (v : RatNode) (h : v.WellFormed k) (u : List Bool) :
    0 ≤ v.prob u := by
  unfold RatNode.prob RatNode.WellFormed at *
  obtain ⟨_, _, _, _, hrows⟩ := h
  match hm : v.2.find? (fun row => row.1 == u) with
  | none =>
    simp [hm]
  | some row =>
    have hmem : row ∈ v.2 := List.mem_of_find?_eq_some hm
    obtain ⟨_, hpos, _⟩ := hrows row hmem
    simp [hm]
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem RatNode.prob_le_one (k : ℕ) (v : RatNode) (h : v.WellFormed k) (u : List Bool) :
    v.prob u ≤ 1 := by
  unfold RatNode.prob RatNode.WellFormed at *
  obtain ⟨_, _, _, _, hrows⟩ := h
  match hm : v.2.find? (fun row => row.1 == u) with
  | none =>
    simp [hm, zero_le_one]
  | some row =>
    have hmem : row ∈ v.2 := List.mem_of_find?_eq_some hm
    obtain ⟨_, hpos, hle⟩ := hrows row hmem
    simp only [hm]
    have hposQ : (0 : ℚ) < row.2.2 := by exact_mod_cast hpos
    have hleQ : (row.2.1 : ℚ) ≤ row.2.2 := by exact_mod_cast hle
    calc (row.2.1 : ℚ) / row.2.2 ≤ row.2.2 / row.2.2 := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hposQ)
            exact hleQ
      _ = 1 := div_self (ne_of_gt hposQ)

theorem clamp_eq (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : max 0 (min 1 q) = q := by
  have hmin : min (1 : ℚ) q = q := min_eq_right h1
  rw [hmin]
  exact max_eq_right h0

theorem bernoulliQ_weights_true (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (bernoulliQ q).weights true = (q : ℝ) := by
  have hclamp : max (0 : ℚ) (min 1 q) = q := clamp_eq q h0 h1
  have h : (bernoulliQ q).weights true = ((max 0 (min 1 q) : ℚ) : ℝ) := by
    simp [bernoulliQ, StdSimplex.weights_duple]
  rw [h, hclamp]

theorem bernoulliQ_weights_false (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (bernoulliQ q).weights false = 1 - (q : ℝ) := by
  have h : (bernoulliQ q).weights false = 1 - ((max 0 (min 1 q) : ℚ) : ℝ) := by
    simp [bernoulliQ, StdSimplex.weights_duple]
  rw [h, clamp_eq q h0 h1]

theorem RatNet.paVals_eq_parentVals (r : RatNet) (hr : r.WellFormed)
    (k : Fin r.length) (x : Fin r.length → Bool) :
    r.paVals k (fun j => (fun j => x (Fin.castLE k.2.le j)) ↑j) = r.parentVals k x := by
  have hnode : RatNode.WellFormed k.val (r.get k) := hr.2 k.val k.isLt
  obtain ⟨_, hlt, _, _, _⟩ := hnode
  unfold RatNet.paVals RatNet.parentVals
  apply List.map_eq_map_iff.mpr
  intro j hj
  have hjlt : j < k.val := hlt j hj
  have hjlen : j < r.length := lt_trans hjlt k.isLt
  have hmem : (⟨j, hjlt⟩ : Fin k.val) ∈ r.pa k := by
    unfold RatNet.pa
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨j, hj, by simp [hjlt]⟩
  simp [hjlt, hjlen, hmem, Fin.castLE]

/-- **Decode bridge.** A well-formed rational network denotes an Atlas `BayesNet` over `ℝ` whose
joint is the rational product of its table entries. -/
theorem RatNet.joint_toBayesNet (r : RatNet) (hr : r.WellFormed) (x : Fin r.length → Bool) :
    r.toBayesNet.joint x = ((r.ratJoint x : ℚ) : ℝ) := by
  have hnode : ∀ k : Fin r.length, RatNode.WellFormed k.val (r.get k) :=
    fun k => hr.2 k.val k.isLt
  have hjoint : r.toBayesNet.joint x = r.toBayesNet.toChain.joint r.length x := rfl
  have hchain := r.toBayesNet.toChain.joint_eq_prod r.length x
  have hrat : r.ratJoint x = ∏ k : Fin r.length,
      (if x k then (r.get k).prob (r.parentVals k x) else 1 - (r.get k).prob (r.parentVals k x)) := rfl
  have hcast : ((r.ratJoint x : ℚ) : ℝ) = ∏ k : Fin r.length,
      (((if x k then (r.get k).prob (r.parentVals k x)
        else 1 - (r.get k).prob (r.parentVals k x) : ℚ)) : ℝ) := by
    rw [hrat]
    exact Rat.cast_prod Finset.univ _
  rw [hjoint, hchain, hcast]
  apply Finset.prod_congr rfl
  intro k _
  have hk : k.val < r.length := k.isLt
  have hcond : r.toBayesNet.toChain.cond k.val (fun j => x (Fin.castLE k.2.le j)) =
      r.toBayesNet.cpt ⟨k.val, hk⟩ (fun j => (fun j => x (Fin.castLE k.2.le j)) ↑j) := by
    simp [BayesNet.toChain, hk]
  have hcpt : r.toBayesNet.cpt ⟨k.val, hk⟩ (fun j => (fun j => x (Fin.castLE k.2.le j)) ↑j) =
      bernoulliQ ((r.get ⟨k.val, hk⟩).prob
        (r.paVals ⟨k.val, hk⟩ (fun j => (fun j => x (Fin.castLE k.2.le j)) ↑j))) := rfl
  have hget : (r.get ⟨k.val, hk⟩) = r.get k := rfl
  have hpa : r.paVals ⟨k.val, hk⟩ (fun j => (fun j => x (Fin.castLE k.2.le j)) ↑j) =
      r.paVals k (fun j => (fun j => x (Fin.castLE k.2.le j)) ↑j) := rfl
  have hpaEq : r.paVals k (fun j => (fun j => x (Fin.castLE k.2.le j)) ↑j) = r.parentVals k x :=
    r.paVals_eq_parentVals hr k x
  have hq0 : 0 ≤ (r.get k).prob (r.parentVals k x) :=
    RatNode.prob_nonneg k.val (r.get k) (hnode k) (r.parentVals k x)
  have hq1 : (r.get k).prob (r.parentVals k x) ≤ 1 :=
    RatNode.prob_le_one k.val (r.get k) (hnode k) (r.parentVals k x)
  rw [hcond, hcpt, hget, hpa, hpaEq]
  cases hx : x k with
  | true =>
    simp only [bernoulliQ_weights_true _ hq0 hq1]
    simp
  | false =>
    simp only [bernoulliQ_weights_false _ hq0 hq1]
    simp [Rat.cast_sub, Rat.cast_one]

theorem readUnaryLength_unary_append (k : ℕ) (rest : List Bool) :
    readUnaryLength (unary k ++ rest) = some (k, rest) := by
  induction k generalizing rest with
  | zero =>
    simp [unary, readUnaryLength]
  | succ k ih =>
    have h : unary (k + 1) ++ rest = true :: (unary k ++ rest) := by
      simp [unary, List.replicate_succ]
    rw [h]
    simp [readUnaryLength, ih]

theorem decodeMany_append
    {α : Type} (dec : List Bool → Option (α × List Bool))
    (enc : α → List Bool)
    (h : ∀ (a : α) (rest : List Bool), dec (enc a ++ rest) = some (a, rest))
    (xs : List α) (rest : List Bool) :
    decodeMany dec xs.length (xs.flatMap enc ++ rest) = some (xs, rest) := by
  induction xs generalizing rest with
  | nil => simp [decodeMany]
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_cons]
    have h1 : (enc x ++ List.flatMap enc xs ++ rest) = (enc x ++ (List.flatMap enc xs ++ rest)) := by
      simp [List.append_assoc]
    rw [h1]
    simp [decodeMany, h x (List.flatMap enc xs ++ rest), ih]

theorem decodeRow_encodeRow_aux (row : List Bool × ℕ × ℕ) (rest : List Bool) :
    decodeRow (encodeRow row ++ rest) = some (row, rest) := by
  obtain ⟨bits, num, den⟩ := row
  simp only [encodeRow]
  have happend : (unary bits.length ++ bits ++ unary num ++ unary den ++ rest)
      = (unary bits.length ++ (bits ++ unary num ++ unary den ++ rest)) := by
    simp [List.append_assoc]
  rw [happend]
  simp [decodeRow, readUnaryLength_unary_append]

theorem decodeRatNode_encodeRatNode_aux (v : RatNode) (rest : List Bool) :
    decodeRatNode (encodeRatNode v ++ rest) = some (v, rest) := by
  obtain ⟨ps, rows⟩ := v
  simp only [encodeRatNode]
  have hps : decodeMany readUnaryLength ps.length
      (List.flatMap unary ps ++ (unary rows.length ++
        (List.flatMap encodeRow rows ++ rest)))
      = some (ps, unary rows.length ++ (List.flatMap encodeRow rows ++ rest)) := by
    have h := decodeMany_append readUnaryLength unary readUnaryLength_unary_append ps
      (unary rows.length ++ (List.flatMap encodeRow rows ++ rest))
    simpa [List.append_assoc] using h
  have hrows : decodeMany decodeRow rows.length (List.flatMap encodeRow rows ++ rest)
      = some (rows, rest) :=
    decodeMany_append decodeRow encodeRow decodeRow_encodeRow_aux rows rest
  have h1 : (unary ps.length ++ List.flatMap unary ps ++ unary rows.length ++
      List.flatMap encodeRow rows ++ rest)
      = (unary ps.length ++ (List.flatMap unary ps ++ (unary rows.length ++
        (List.flatMap encodeRow rows ++ rest)))) := by
    simp [List.append_assoc]
  rw [h1]
  unfold decodeRatNode
  rw [readUnaryLength_unary_append]
  simp [hps]
  rw [readUnaryLength_unary_append]
  simp [hrows]

/-- **The decoder inverts the encoding.** -/
theorem decodeRatNet_encodeRatNet (r : RatNet) : decodeRatNet (encodeRatNet r) = some r := by
  have hvs : decodeMany decodeRatNode r.length (r.reverse.flatMap encodeRatNode)
      = some (r.reverse, []) := by
    have h := decodeMany_append decodeRatNode encodeRatNode
      decodeRatNode_encodeRatNode_aux r.reverse []
    simpa using h
  simp only [encodeRatNet]
  unfold decodeRatNet
  rw [readUnaryLength_unary_append]
  simp [hvs]


/-- **Construction invariant**: every emitted node is well formed at its index, the AND-chain
output is in range, and every recorded root points at a root node. -/
structure CoopSt.Good (s : CoopSt) : Prop where
  nodes_wf : ∀ k (hk : k < s.nodes.length), RatNode.WellFormed k s.nodes[k]
  acc_lt : s.acc < s.nodes.length
  roots_ok : ∀ p ∈ s.roots, ∃ h : p.2 < s.nodes.length, s.nodes[p.2] = rootNode

theorem coop_mem_of_lookup {x v : ℕ} {l : List (ℕ × ℕ)}
    (h : List.lookup x l = some v) : (x, v) ∈ l := by
  obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp h
  rw [heq]
  simp

theorem coop_append_get_last {α : Type} (l : List α) (a : α)
    {h : l.length < (l ++ [a]).length} : (l ++ [a])[l.length] = a := by
  have hr := List.getElem_append_right (as := l) (bs := [a]) (i := l.length)
    (le_refl l.length) (h₂ := h)
  simp only [Nat.sub_self] at hr
  exact hr

theorem wf_rootNode (k : ℕ) : RatNode.WellFormed k rootNode := by
  unfold RatNode.WellFormed rootNode
  refine ⟨by decide, by simp, by decide, by decide, ?_⟩
  intro row hr
  simp at hr
  subst hr
  exact ⟨rfl, by decide, by decide⟩

theorem wf_constNode (k : ℕ) (b : Bool) : RatNode.WellFormed k (constNode b) := by
  cases b <;> unfold RatNode.WellFormed constNode
  · refine ⟨by decide, by simp, by decide, by decide, ?_⟩
    intro row hr
    simp at hr
    subst hr
    exact ⟨rfl, by decide, by decide⟩
  · refine ⟨by decide, by simp, by decide, by decide, ?_⟩
    intro row hr
    simp at hr
    subst hr
    exact ⟨rfl, by decide, by decide⟩

theorem wf_gateNode (f : Bool → Bool → Bool) {i j k : ℕ} (hij : i ≠ j) (hi : i < k)
    (hj : j < k) : RatNode.WellFormed k (gateNode f i j) := by
  unfold RatNode.WellFormed gateNode
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hne : i ∉ [j] := by simp [hij]
    exact List.Nodup.cons hne (List.nodup_singleton j)
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl
    · exact hi
    · exact hj
  · show List.Nodup [[false, false], [false, true], [true, false], [true, true]]
    decide
  · show (4 : ℕ) = 2 ^ 2
    decide
  · intro row hr
    simp at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨rfl, Nat.zero_lt_one, Bool.toNat_le _⟩
    · exact ⟨rfl, Nat.zero_lt_one, Bool.toNat_le _⟩
    · exact ⟨rfl, Nat.zero_lt_one, Bool.toNat_le _⟩
    · exact ⟨rfl, Nat.zero_lt_one, Bool.toNat_le _⟩

theorem good_init : CoopSt.Good ⟨[constNode true], [], 0⟩ := by
  refine ⟨?_, by decide, ?_⟩
  · intro k hk
    have hk1 : k < 1 := hk
    have hkeq : k = 0 := Nat.lt_one_iff.mp hk1
    subst hkeq
    exact wf_constNode 0 true
  · intro p hp
    simp at hp

theorem good_coopRoot (x : ℕ) {s : CoopSt} (hs : s.Good) :
    (coopRoot x s).1.Good ∧ ∃ h : (coopRoot x s).2 < (coopRoot x s).1.nodes.length,
      (coopRoot x s).1.nodes[(coopRoot x s).2] = rootNode := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    dsimp only
    refine ⟨hs, ?_⟩
    have hmem : (x, v) ∈ s.roots := coop_mem_of_lookup hlook
    obtain ⟨h, heq⟩ := hs.roots_ok (x, v) hmem
    exact ⟨h, heq⟩
  | none =>
    dsimp only
    have hlen : (s.nodes ++ [rootNode]).length = s.nodes.length + 1 := by simp
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have hk' : k < (s.nodes ++ [rootNode]).length := hk
        have hklen : k < s.nodes.length + 1 := by omega
        by_cases hkold : k < s.nodes.length
        · have hget : (s.nodes ++ [rootNode])[k]'hk' = s.nodes[k]'hkold :=
            List.getElem_append_left hkold
          have hgoal : RatNode.WellFormed k ((s.nodes ++ [rootNode])[k]'hk') := by
            rw [hget]
            exact hs.nodes_wf k hkold
          exact hgoal
        · have hkeq : k = s.nodes.length := by omega
          subst hkeq
          have hget : (s.nodes ++ [rootNode])[s.nodes.length]'hk' = rootNode :=
            coop_append_get_last s.nodes rootNode
          have hgoal :
              RatNode.WellFormed s.nodes.length
                ((s.nodes ++ [rootNode])[s.nodes.length]'hk') := by
            rw [hget]
            exact wf_rootNode _
          exact hgoal
      · have hacc := hs.acc_lt
        have h' : s.acc < (s.nodes ++ [rootNode]).length := by
          rw [hlen]
          omega
        exact h'
      · intro p hp
        have hp' : p ∈ (x, s.nodes.length) :: s.roots := hp
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hmem
        · have hlt : s.nodes.length < (s.nodes ++ [rootNode]).length := by
            rw [hlen]
            omega
          have hget : (s.nodes ++ [rootNode])[s.nodes.length]'hlt = rootNode :=
            coop_append_get_last s.nodes rootNode
          exact ⟨hlt, hget⟩
        · obtain ⟨h, heq⟩ := hs.roots_ok p hmem
          have hlt : p.2 < (s.nodes ++ [rootNode]).length := by
            rw [hlen]
            omega
          have hget : (s.nodes ++ [rootNode])[p.2]'hlt = s.nodes[p.2]'h :=
            List.getElem_append_left h
          exact ⟨hlt, by rw [hget]; exact heq⟩
    · have hlt : s.nodes.length < (s.nodes ++ [rootNode]).length := by
        rw [hlen]
        omega
      have hget : (s.nodes ++ [rootNode])[s.nodes.length]'hlt = rootNode :=
        coop_append_get_last s.nodes rootNode
      exact ⟨hlt, hget⟩

theorem coopRoot_o_lt (x o : ℕ) {s : CoopSt} (ho : o < s.nodes.length) :
    o < (coopRoot x s).1.nodes.length := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    dsimp only
    exact ho
  | none =>
    dsimp only
    have h' : o < (s.nodes ++ [rootNode]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    exact h'

theorem coopRoot_ne_of_ne_root (x o : ℕ) {s : CoopSt} (hs : s.Good)
    (ho : o < s.nodes.length) (hnode : s.nodes[o] ≠ rootNode) :
    o ≠ (coopRoot x s).2 := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    dsimp only
    show o ≠ v
    intro heq
    subst o
    have hmem : (x, v) ∈ s.roots := coop_mem_of_lookup hlook
    obtain ⟨h, heq2⟩ := hs.roots_ok (x, v) hmem
    exact hnode heq2
  | none =>
    dsimp only
    have h' : o ≠ s.nodes.length := by omega
    exact h'

theorem orNode_ne_rootNode (o v : ℕ) (b : Bool) : orNode o v b ≠ rootNode := by
  unfold orNode gateNode rootNode
  intro heq
  have hfst : [o, v] = ([] : List ℕ) := congrArg Prod.fst heq
  simp at hfst

theorem good_coopLit (l : ℕ × Bool) {o : ℕ} {s : CoopSt} (hs : s.Good)
    (ho : o < s.nodes.length) (hnode : s.nodes[o] ≠ rootNode) :
    (coopLit l o s).1.Good ∧ ∃ h : (coopLit l o s).2 < (coopLit l o s).1.nodes.length,
      (coopLit l o s).1.nodes[(coopLit l o s).2] ≠ rootNode := by
  obtain ⟨hr, hv, hveq⟩ := good_coopRoot l.1 hs
  have hne_ov : o ≠ (coopRoot l.1 s).2 := coopRoot_ne_of_ne_root l.1 o hs ho hnode
  have ho_lt : o < (coopRoot l.1 s).1.nodes.length := coopRoot_o_lt l.1 o ho
  unfold coopLit
  dsimp only
  have hlen : ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length =
      (coopRoot l.1 s).1.nodes.length + 1 := by simp
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have hk' : k < ((coopRoot l.1 s).1.nodes ++
          [orNode o (coopRoot l.1 s).2 l.2]).length := hk
      have hklen : k < (coopRoot l.1 s).1.nodes.length + 1 := by omega
      by_cases hkold : k < (coopRoot l.1 s).1.nodes.length
      · have hget : ((coopRoot l.1 s).1.nodes ++
              [orNode o (coopRoot l.1 s).2 l.2])[k]'hk' =
            (coopRoot l.1 s).1.nodes[k]'hkold :=
          List.getElem_append_left hkold
        have hgoal : RatNode.WellFormed k
            (((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2])[k]'hk') := by
          rw [hget]
          exact hr.nodes_wf k hkold
        exact hgoal
      · have hkeq : k = (coopRoot l.1 s).1.nodes.length := by omega
        subst hkeq
        have hget : ((coopRoot l.1 s).1.nodes ++
            [orNode o (coopRoot l.1 s).2 l.2])[(coopRoot l.1 s).1.nodes.length]'hk' =
            orNode o (coopRoot l.1 s).2 l.2 :=
          coop_append_get_last _ _
        have hgoal : RatNode.WellFormed (coopRoot l.1 s).1.nodes.length
            (((coopRoot l.1 s).1.nodes ++
              [orNode o (coopRoot l.1 s).2 l.2])[(coopRoot l.1 s).1.nodes.length]'hk') := by
          rw [hget]
          unfold orNode
          exact wf_gateNode _ hne_ov ho_lt hv
        exact hgoal
    · have hacc := hr.acc_lt
      have h' : (coopRoot l.1 s).1.acc <
          ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length := by
        rw [hlen]
        omega
      exact h'
    · intro p hp
      have hp' : p ∈ (coopRoot l.1 s).1.roots := hp
      obtain ⟨h, heq⟩ := hr.roots_ok p hp'
      have hlt : p.2 < ((coopRoot l.1 s).1.nodes ++
          [orNode o (coopRoot l.1 s).2 l.2]).length := by
        rw [hlen]
        omega
      have hget : ((coopRoot l.1 s).1.nodes ++
          [orNode o (coopRoot l.1 s).2 l.2])[p.2]'hlt =
          (coopRoot l.1 s).1.nodes[p.2]'h :=
        List.getElem_append_left h
      exact ⟨hlt, by rw [hget]; exact heq⟩
  · have hlt : (coopRoot l.1 s).1.nodes.length <
        ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length := by
      rw [hlen]
      omega
    refine ⟨hlt, ?_⟩
    have hget : ((coopRoot l.1 s).1.nodes ++
        [orNode o (coopRoot l.1 s).2 l.2])[(coopRoot l.1 s).1.nodes.length]'hlt =
        orNode o (coopRoot l.1 s).2 l.2 :=
      coop_append_get_last _ _
    have hne := orNode_ne_rootNode o (coopRoot l.1 s).2 l.2
    have hgoal : ((coopRoot l.1 s).1.nodes ++
        [orNode o (coopRoot l.1 s).2 l.2])[(coopRoot l.1 s).1.nodes.length]'hlt ≠ rootNode := by
      rw [hget]
      exact hne
    exact hgoal

theorem good_coopLits (ls : List (ℕ × Bool)) {o : ℕ} {s : CoopSt} (hs : s.Good)
    (ho : o < s.nodes.length) (hnode : s.nodes[o] ≠ rootNode) :
    (coopLits ls o s).1.Good ∧ ∃ h : (coopLits ls o s).2 < (coopLits ls o s).1.nodes.length,
      (coopLits ls o s).1.nodes[(coopLits ls o s).2] ≠ rootNode := by
  induction ls generalizing o s with
  | nil =>
    simp only [coopLits]
    exact ⟨hs, ho, hnode⟩
  | cons l ls ih =>
    simp only [coopLits]
    obtain ⟨hr, h2, hne2⟩ := good_coopLit l hs ho hnode
    exact ih hr h2 hne2

theorem coopRoot_nodes_length_le (x : ℕ) (s : CoopSt) :
    s.nodes.length ≤ (coopRoot x s).1.nodes.length := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    have hgoal : s.nodes.length ≤ s.nodes.length := Nat.le_refl _
    exact hgoal
  | none =>
    have hlen : (s.nodes ++ [rootNode]).length = s.nodes.length + 1 := by simp
    have hgoal : s.nodes.length ≤ (s.nodes ++ [rootNode]).length := by omega
    exact hgoal

theorem coopLit_nodes_length_le (l : ℕ × Bool) (o : ℕ) (s : CoopSt) :
    s.nodes.length ≤ (coopLit l o s).1.nodes.length := by
  have h := coopRoot_nodes_length_le l.1 s
  have hlen : ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length =
      (coopRoot l.1 s).1.nodes.length + 1 := by simp
  have hgoal : s.nodes.length ≤
      ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length := by omega
  exact hgoal

theorem coopLits_nodes_length_le (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt) :
    s.nodes.length ≤ (coopLits ls o s).1.nodes.length := by
  induction ls generalizing o s with
  | nil => simp [coopLits]
  | cons l ls ih =>
    simp only [coopLits]
    exact le_trans (coopLit_nodes_length_le l o s) (ih _ _)

theorem coopLit_o_le (l : ℕ × Bool) (o : ℕ) (s : CoopSt) (ho : o < s.nodes.length) :
    o ≤ (coopLit l o s).2 := by
  have h := coopRoot_nodes_length_le l.1 s
  have hgoal : o ≤ (coopRoot l.1 s).1.nodes.length := by omega
  exact hgoal

theorem coopLit_out_lt (l : ℕ × Bool) (o : ℕ) (s : CoopSt) :
    (coopLit l o s).2 < (coopLit l o s).1.nodes.length := by
  have hlen : ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length =
      (coopRoot l.1 s).1.nodes.length + 1 := by simp
  have hgoal : (coopRoot l.1 s).1.nodes.length <
      ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length := by omega
  exact hgoal

theorem coopLits_o_le (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt)
    (ho : o < s.nodes.length) : o ≤ (coopLits ls o s).2 := by
  induction ls generalizing o s with
  | nil => simp [coopLits]
  | cons l ls ih =>
    simp only [coopLits]
    have h1 : o ≤ (coopLit l o s).2 := coopLit_o_le l o s ho
    have h2 : (coopLit l o s).2 < (coopLit l o s).1.nodes.length := coopLit_out_lt l o s
    exact le_trans h1 (ih _ _ h2)

theorem good_append_constNode_false {s : CoopSt} (hs : s.Good) :
    ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).Good := by
  have hlen : (s.nodes ++ [constNode false]).length = s.nodes.length + 1 := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hk' : k < (s.nodes ++ [constNode false]).length := hk
    have hklen : k < s.nodes.length + 1 := by omega
    by_cases hkold : k < s.nodes.length
    · have hget : (s.nodes ++ [constNode false])[k]'hk' = s.nodes[k]'hkold :=
        List.getElem_append_left hkold
      have hgoal : RatNode.WellFormed k ((s.nodes ++ [constNode false])[k]'hk') := by
        rw [hget]
        exact hs.nodes_wf k hkold
      exact hgoal
    · have hkeq : k = s.nodes.length := by omega
      subst hkeq
      have hget : (s.nodes ++ [constNode false])[s.nodes.length]'hk' = constNode false :=
        coop_append_get_last s.nodes (constNode false)
      have hgoal : RatNode.WellFormed s.nodes.length
          ((s.nodes ++ [constNode false])[s.nodes.length]'hk') := by
        rw [hget]
        exact wf_constNode _ _
      exact hgoal
  · have hacc := hs.acc_lt
    have h' : s.acc < (s.nodes ++ [constNode false]).length := by omega
    exact h'
  · intro p hp
    have hp' : p ∈ s.roots := hp
    obtain ⟨h, heq⟩ := hs.roots_ok p hp'
    have hlt : p.2 < (s.nodes ++ [constNode false]).length := by omega
    have hget : (s.nodes ++ [constNode false])[p.2]'hlt = s.nodes[p.2]'h :=
      List.getElem_append_left h
    exact ⟨hlt, by rw [hget]; exact heq⟩

theorem good_append_andNode {t : CoopSt} (ht : t.Good) (a b : ℕ)
    (ha : a < t.nodes.length) (hb : b < t.nodes.length) (hab : a ≠ b) :
    ({ t with nodes := t.nodes ++ [andNode a b], acc := t.nodes.length } : CoopSt).Good := by
  have hlen : (t.nodes ++ [andNode a b]).length = t.nodes.length + 1 := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hk' : k < (t.nodes ++ [andNode a b]).length := hk
    have hklen : k < t.nodes.length + 1 := by omega
    by_cases hkold : k < t.nodes.length
    · have hget : (t.nodes ++ [andNode a b])[k]'hk' = t.nodes[k]'hkold :=
        List.getElem_append_left hkold
      have hgoal : RatNode.WellFormed k ((t.nodes ++ [andNode a b])[k]'hk') := by
        rw [hget]
        exact ht.nodes_wf k hkold
      exact hgoal
    · have hkeq : k = t.nodes.length := by omega
      subst hkeq
      have hget : (t.nodes ++ [andNode a b])[t.nodes.length]'hk' = andNode a b :=
        coop_append_get_last t.nodes (andNode a b)
      have hgoal : RatNode.WellFormed t.nodes.length
          ((t.nodes ++ [andNode a b])[t.nodes.length]'hk') := by
        rw [hget]
        unfold andNode
        exact wf_gateNode _ hab ha hb
      exact hgoal
  · have h' : t.nodes.length < (t.nodes ++ [andNode a b]).length := by omega
    exact h'
  · intro p hp
    have hp' : p ∈ t.roots := hp
    obtain ⟨h, heq⟩ := ht.roots_ok p hp'
    have hlt : p.2 < (t.nodes ++ [andNode a b]).length := by omega
    have hget : (t.nodes ++ [andNode a b])[p.2]'hlt = t.nodes[p.2]'h :=
      List.getElem_append_left h
    exact ⟨hlt, by rw [hget]; exact heq⟩

theorem good_coopClause (C : CNFClause) {s : CoopSt} (hs : s.Good) :
    (coopClause C s).Good := by
  have hs0 := good_append_constNode_false hs
  have ho0 : s.nodes.length <
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length := by
    show s.nodes.length < (s.nodes ++ [constNode false]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hnode0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes[s.nodes.length]'ho0 ≠
      rootNode := by
    show (s.nodes ++ [constNode false])[s.nodes.length]'ho0 ≠ rootNode
    have hget : (s.nodes ++ [constNode false])[s.nodes.length]'ho0 = constNode false :=
      coop_append_get_last s.nodes (constNode false)
    rw [hget]
    decide
  obtain ⟨hr, h2, _⟩ := good_coopLits C.reverse hs0 ho0 hnode0
  have hacc : s.acc <
      (coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).1.nodes.length := by
    have hle := coopLits_nodes_length_le C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }
    have hlen : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length =
        s.nodes.length + 1 := by
      show (s.nodes ++ [constNode false]).length = s.nodes.length + 1
      simp
    have halt := hs.acc_lt
    omega
  have hne : s.acc ≠
      (coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).2 := by
    have ho_le := coopLits_o_le C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] } ho0
    have halt := hs.acc_lt
    omega
  exact good_append_andNode hr _ _ hacc h2 hne

theorem good_coopSt (φ : CNF) : (coopSt φ).Good := by
  have h : ∀ (l : List CNFClause) (s : CoopSt),
      s.Good → (l.foldl (fun s C => coopClause C s) s).Good := by
    intro l
    induction l with
    | nil =>
      intro s hs
      simpa
    | cons C l ih =>
      intro s hs
      simp only [List.foldl_cons]
      exact ih _ (good_coopClause C hs)
  exact h φ.reverse _ good_init


/-- **Cooper's network is well formed.** -/
theorem cooperNet_wellFormed (φ : CNF) : (cooperNet φ).WellFormed := by
  have hg := good_coopSt φ
  have hacc := hg.acc_lt
  unfold cooperNet RatNet.WellFormed
  refine ⟨?_, hg.nodes_wf⟩
  intro hemp
  have hlen : (coopSt φ).nodes.length = 0 := by simp [hemp]
  omega

/-- **Forced value of a deterministic node** given the values of earlier nodes: `true`
exactly when the table gives probability `1` to `true` at those parent values. -/
def forcedVal (vals : List Bool) (v : RatNode) : Bool :=
  decide (v.prob (v.1.map (fun j => vals.getD j false)) = 1)

/-- **Evaluation of a construction state** under a variable assignment `σ`: node values
in emission order. A node whose index occurs in `s.roots` takes the value under `σ` of
the variable in the first pair matching that index; every other node takes its forced
value from the earlier values. The definition takes an arbitrary state. -/
def CoopSt.evalList (s : CoopSt) (σ : ℕ → Bool) : List Bool :=
  s.nodes.foldl (fun (vals : List Bool) (v : RatNode) =>
    vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
      | some p => σ p.1
      | none => forcedVal vals v]) []

/-- Value of node `k` under `σ`. -/
def CoopSt.eval (s : CoopSt) (σ : ℕ → Bool) (k : Fin s.nodes.length) : Bool :=
  (s.evalList σ).getD k.val false

/-- Truth of a clause under `σ`, as a Boolean. -/
def clauseVal (σ : ℕ → Bool) (C : CNFClause) : Bool :=
  C.any (fun l => σ l.1 == l.2)

theorem evalList_foldl_length_aux (s : CoopSt) (σ : ℕ → Bool) (l : List RatNode)
    (vals : List Bool) :
    (l.foldl (fun (vals : List Bool) (v : RatNode) =>
      vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ p.1
        | none => forcedVal vals v]) vals).length = vals.length + l.length := by
  induction l generalizing vals with
  | nil => simp
  | cons v l ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem evalList_length (s : CoopSt) (σ : ℕ → Bool) :
    (s.evalList σ).length = s.nodes.length := by
  have h := evalList_foldl_length_aux s σ s.nodes []
  simpa [CoopSt.evalList] using h

theorem evalList_append_singleton (s : CoopSt) (σ : ℕ → Bool) (v : RatNode) :
    (({ s with nodes := s.nodes ++ [v] } : CoopSt).evalList σ) =
      s.evalList σ ++ [match s.roots.find? (fun p => p.2 == s.nodes.length) with
        | some p => σ p.1
        | none => forcedVal (s.evalList σ) v] := by
  have hlen := evalList_length s σ
  have hLHS : (({ s with nodes := s.nodes ++ [v] } : CoopSt).evalList σ)
      = List.foldl (fun (vals : List Bool) (v : RatNode) =>
          vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
            | some p => σ p.1
            | none => forcedVal vals v]) [] (s.nodes ++ [v]) := rfl
  have hvals : List.foldl (fun (vals : List Bool) (v : RatNode) =>
          vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
            | some p => σ p.1
            | none => forcedVal vals v]) [] s.nodes = s.evalList σ := rfl
  rw [hLHS, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, hvals, hlen]

theorem evalList_foldl_getD_aux (s : CoopSt) (σ : ℕ → Bool) (l : List RatNode) :
    ∀ (vals : List Bool) (j : ℕ) (d : Bool), j < vals.length →
    (l.foldl (fun (vals : List Bool) (v : RatNode) =>
      vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ p.1
        | none => forcedVal vals v]) vals).getD j d = vals.getD j d := by
  induction l with
  | nil =>
    intro vals j d hj
    simp
  | cons v l ih =>
    intro vals j d hj
    simp only [List.foldl_cons]
    rw [ih _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    exact List.getD_append vals _ d j hj

theorem evalList_foldl_some_aux (s : CoopSt) (σ : ℕ → Bool) (l : List RatNode) :
    ∀ (vals : List Bool) (j x : ℕ), vals.length ≤ j → j < vals.length + l.length →
    s.roots.find? (fun p => p.2 == j) = some (x, j) →
    (l.foldl (fun (vals : List Bool) (v : RatNode) =>
      vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ p.1
        | none => forcedVal vals v]) vals).getD j false = σ x := by
  induction l with
  | nil =>
    intro vals j x hle hlt hfind
    simp only [List.length_nil] at hlt
    omega
  | cons v l ih =>
    intro vals j x hle hlt hfind
    simp only [List.foldl_cons, List.length_cons] at hlt ⊢
    by_cases heq : vals.length = j
    · subst heq
      set m : Bool := match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ p.1
        | none => forcedVal vals v with hm
      have hmem : vals.length < (vals ++ [m]).length := by simp
      rw [evalList_foldl_getD_aux _ _ _ _ _ _ hmem,
        List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      have h0 : ([m].getD 0 false) = m := by simp
      rw [h0, hm, hfind]
    · refine ih _ _ _ ?_ ?_ hfind
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega

theorem eval_root {s : CoopSt} (σ : ℕ → Bool) {x k : ℕ} (hk : k < s.nodes.length)
    (h : s.roots.find? (fun p => p.2 == k) = some (x, k)) :
    s.eval σ ⟨k, hk⟩ = σ x := by
  have hmain := evalList_foldl_some_aux s σ s.nodes [] k x (by simp)
    (by simp only [List.length_nil, Nat.zero_add]; exact hk) h
  exact hmain

theorem forcedVal_constNode (vals : List Bool) (b : Bool) :
    forcedVal vals (constNode b) = b := by
  cases b <;> simp [forcedVal, constNode, RatNode.prob]

theorem forcedVal_gateNode (vals : List Bool) (f : Bool → Bool → Bool) (i j : ℕ) :
    forcedVal vals (gateNode f i j) = f (vals.getD i false) (vals.getD j false) := by
  cases ha : vals.getD i false <;> cases hb : vals.getD j false <;>
    simp [forcedVal, gateNode, RatNode.prob, ha, hb, -List.getD_eq_getElem?_getD]

theorem coop_find?_eq_none_of_all_lt (roots : List (ℕ × ℕ)) (n : ℕ)
    (h : ∀ p ∈ roots, p.2 < n) :
    roots.find? (fun p => p.2 == n) = none := by
  apply List.find?_eq_none.mpr
  intro x hx
  show ¬ (x.2 == n) = true
  rw [beq_iff_eq]
  exact Nat.ne_of_lt (h x hx)

theorem coop_find?_cons_of_ne (x n m : ℕ) (roots : List (ℕ × ℕ)) (hm : m < n) :
    (((x, n) :: roots).find? (fun p => p.2 == m)) = roots.find? (fun p => p.2 == m) := by
  have h : ((x, n).2 == m) = false := by
    have h1 : (x, n).2 = n := rfl
    rw [h1, beq_eq_false_iff_ne]
    omega
  simp only [List.find?_cons, h]

theorem coop_find?_fresh_head (x n : ℕ) (roots : List (ℕ × ℕ)) :
    (((x, n) :: roots).find? (fun p => p.2 == n)) = some (x, n) := by
  have h : ((x, n).2 == n) = true := by
    have h1 : (x, n).2 = n := rfl
    rw [h1]
    exact beq_self_eq_true n
  simp only [List.find?_cons, h]

theorem coop_foldl_congr (g g' : List Bool → RatNode → Bool) (n : ℕ) (l : List RatNode) :
    ∀ (vals : List Bool), vals.length + l.length ≤ n →
    (∀ (w : List Bool) (a : RatNode), w.length < n → g' w a = g w a) →
    l.foldl (fun w a => w ++ [g' w a]) vals = l.foldl (fun w a => w ++ [g w a]) vals := by
  induction l with
  | nil =>
    intro vals h heq
    rfl
  | cons a t ih =>
    intro vals hlen heq
    have hlt : vals.length < n := by
      simp only [List.length_cons] at hlen
      omega
    simp only [List.foldl_cons]
    rw [heq vals a hlt]
    refine ih _ ?_ heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
    omega

theorem coop_evalList_getD_append (s : CoopSt) (σ : ℕ → Bool) (extra : List RatNode) (j : ℕ)
    (hj : j < s.nodes.length) :
    (({ s with nodes := s.nodes ++ extra } : CoopSt).evalList σ).getD j false =
      (s.evalList σ).getD j false := by
  have hfold : (({ s with nodes := s.nodes ++ extra } : CoopSt).evalList σ)
      = List.foldl (fun (vals : List Bool) (v : RatNode) =>
          vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
            | some p => σ p.1
            | none => forcedVal vals v]) (s.evalList σ) extra := by
    have hLHS : (({ s with nodes := s.nodes ++ extra } : CoopSt).evalList σ)
        = List.foldl (fun (vals : List Bool) (v : RatNode) =>
            vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
              | some p => σ p.1
              | none => forcedVal vals v]) [] (s.nodes ++ extra) := rfl
    have hvals : List.foldl (fun (vals : List Bool) (v : RatNode) =>
            vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
              | some p => σ p.1
              | none => forcedVal vals v]) [] s.nodes = s.evalList σ := rfl
    rw [hLHS, List.foldl_append, hvals]
  rw [hfold]
  have hjlen : j < (s.evalList σ).length := by
    rw [evalList_length]
    exact hj
  exact evalList_foldl_getD_aux s σ extra (s.evalList σ) j false hjlen

theorem coop_evalList_getD_coopRoot (x j : ℕ) (s : CoopSt) (σ : ℕ → Bool)
    (hj : j < s.nodes.length) :
    (((coopRoot x s).1.evalList σ).getD j false) = (s.evalList σ).getD j false := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    dsimp only
  | none =>
    dsimp only
    set s' : CoopSt := ({ s with nodes := s.nodes ++ [rootNode], roots := (x, s.nodes.length) :: s.roots })
    have hcongr : List.foldl (fun (w : List Bool) (a : RatNode) =>
            w ++ [match ((x, s.nodes.length) :: s.roots).find? (fun p => p.2 == w.length) with
              | some p => σ p.1
              | none => forcedVal w a]) [] s.nodes
        = s.evalList σ := by
      have h := coop_foldl_congr
        (fun (w : List Bool) (a : RatNode) =>
          match s.roots.find? (fun p => p.2 == w.length) with
          | some p => σ p.1
          | none => forcedVal w a)
        (fun (w : List Bool) (a : RatNode) =>
          match ((x, s.nodes.length) :: s.roots).find? (fun p => p.2 == w.length) with
          | some p => σ p.1
          | none => forcedVal w a)
        s.nodes.length s.nodes [] (by simp) (fun w a hw => by
          show (match ((x, s.nodes.length) :: s.roots).find? (fun p => p.2 == w.length) with
            | some p => σ p.1
            | none => forcedVal w a)
            = (match s.roots.find? (fun p => p.2 == w.length) with
            | some p => σ p.1
            | none => forcedVal w a)
          rw [coop_find?_cons_of_ne x s.nodes.length w.length s.roots hw])
      have hrfl : List.foldl (fun (w : List Bool) (a : RatNode) =>
            w ++ [match s.roots.find? (fun p => p.2 == w.length) with
              | some p => σ p.1
              | none => forcedVal w a]) [] s.nodes = s.evalList σ := rfl
      rw [hrfl] at h
      exact h
    have hmain : (s'.evalList σ)
        = List.foldl (fun (w : List Bool) (a : RatNode) =>
            w ++ [match ((x, s.nodes.length) :: s.roots).find? (fun p => p.2 == w.length) with
              | some p => σ p.1
              | none => forcedVal w a]) (s.evalList σ) [rootNode] := by
      have hLHS : (s'.evalList σ)
          = List.foldl (fun (w : List Bool) (a : RatNode) =>
              w ++ [match ((x, s.nodes.length) :: s.roots).find? (fun p => p.2 == w.length) with
                | some p => σ p.1
                | none => forcedVal w a]) [] (s.nodes ++ [rootNode]) := rfl
      rw [hLHS, List.foldl_append, hcongr]
    rw [hmain]
    simp only [List.foldl_cons, List.foldl_nil]
    have hjlen : j < (s.evalList σ).length := by
      rw [evalList_length]
      exact hj
    exact List.getD_append _ _ _ _ hjlen

theorem coop_evalList_getD_coopLits (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt)
    (σ : ℕ → Bool) (j : ℕ) (hj : j < s.nodes.length) :
    (((coopLits ls o s).1.evalList σ).getD j false) = (s.evalList σ).getD j false := by
  induction ls generalizing o s with
  | nil =>
    simp only [coopLits]
  | cons l ls ih =>
    have h1 : j < (coopLit l o s).1.nodes.length :=
      lt_of_lt_of_le hj (coopLit_nodes_length_le l o s)
    have hr : j < (coopRoot l.1 s).1.nodes.length :=
      lt_of_lt_of_le hj (coopRoot_nodes_length_le l.1 s)
    have e1 : (((coopLit l o s).1.evalList σ).getD j false)
        = (((coopRoot l.1 s).1.evalList σ).getD j false) :=
      coop_evalList_getD_append (coopRoot l.1 s).1 σ [orNode o (coopRoot l.1 s).2 l.2] j hr
    have e2 := coop_evalList_getD_coopRoot l.1 j s σ hj
    have hstep : (((coopLit l o s).1.evalList σ).getD j false) = (s.evalList σ).getD j false := by
      rw [e1]
      exact e2
    show (((coopLits ls (coopLit l o s).2 (coopLit l o s).1).1.evalList σ).getD j false)
      = (s.evalList σ).getD j false
    rw [ih _ _ h1, hstep]

theorem coop_find?_of_lookup (roots : List (ℕ × ℕ)) :
    ∀ (x v : ℕ), roots.lookup x = some v → (roots.map Prod.snd).Nodup →
    roots.find? (fun p => p.2 == v) = some (x, v) := by
  induction roots with
  | nil =>
    intro x v h hnd
    simp at h
  | cons p ps ih =>
    intro x v hlookup hnd
    simp only [List.lookup] at hlookup
    by_cases hx : (x == p.1) = true
    · simp only [hx] at hlookup
      have hp2 : p.2 = v := by simpa using hlookup
      have hp1 : p.1 = x := (beq_iff_eq.mp hx).symm
      have hye : (p.2 == v) = true := by
        rw [hp2]
        exact beq_self_eq_true v
      have hp : p = (x, v) := by
        obtain ⟨a, b⟩ := p
        dsimp only at hp1 hp2 ⊢
        rw [hp1, hp2]
      simp only [List.find?_cons, hp, beq_self_eq_true]
    · have hfalse : (x == p.1) = false := by
        revert hx
        cases h : x == p.1
        case false => intro _; rfl
        case true => intro hx; simp at hx
      simp only [hfalse] at hlookup
      have hnd' : (p.2 :: ps.map Prod.snd).Nodup := hnd
      have htail : (ps.map Prod.snd).Nodup := (List.nodup_cons.mp hnd').2
      have hnin : p.2 ∉ ps.map Prod.snd := (List.nodup_cons.mp hnd').1
      have hmem2 : (x, v) ∈ ps := coop_mem_of_lookup hlookup
      have hvin : v ∈ ps.map Prod.snd := List.mem_map.mpr ⟨(x, v), hmem2, rfl⟩
      have hp2ne : p.2 ≠ v := by
        intro hcontra
        rw [hcontra] at hnin
        exact hnin hvin
      have hmiss : (p.2 == v) = false := by
        rw [beq_eq_false_iff_ne]
        exact hp2ne
      have hih := ih x v hlookup htail
      simp only [List.find?_cons, hmiss]
      exact hih

theorem coop_nodup_coopRoot (x : ℕ) (s : CoopSt) (hs : s.Good)
    (hnd : (s.roots.map Prod.snd).Nodup) :
    (((coopRoot x s).1.roots.map Prod.snd).Nodup) := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    dsimp only
    exact hnd
  | none =>
    dsimp only
    have hnil : ∀ y ∈ s.roots.map Prod.snd, y ≠ s.nodes.length := by
      intro y hy
      obtain ⟨p, hpmem, hpeq⟩ := List.mem_map.mp hy
      obtain ⟨hlt, -⟩ := hs.roots_ok p hpmem
      omega
    show (s.nodes.length :: s.roots.map Prod.snd).Nodup
    refine List.Nodup.cons ?_ hnd
    intro hmem
    exact (hnil _ hmem) rfl

theorem coop_nodup_coopLit (l : ℕ × Bool) (o : ℕ) (s : CoopSt) (hs : s.Good)
    (hnd : (s.roots.map Prod.snd).Nodup) :
    (((coopLit l o s).1.roots.map Prod.snd).Nodup) := by
  have h := coop_nodup_coopRoot l.1 s hs hnd
  exact h

theorem coop_nodup_coopLits (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt)
    (hs : s.Good) (hnd : (s.roots.map Prod.snd).Nodup)
    (ho : o < s.nodes.length) (hnode : s.nodes[o] ≠ rootNode) :
    (((coopLits ls o s).1.roots.map Prod.snd).Nodup) := by
  induction ls generalizing o s with
  | nil =>
    simp only [coopLits]
    exact hnd
  | cons l ls ih =>
    simp only [coopLits]
    obtain ⟨hr, h2, hne2⟩ := good_coopLit l hs ho hnode
    exact ih _ _ hr (coop_nodup_coopLit l o s hs hnd) h2 hne2

theorem coop_nodup_coopClause (C : CNFClause) (s : CoopSt) (hs : s.Good)
    (hnd : (s.roots.map Prod.snd).Nodup) :
    (((coopClause C s).roots.map Prod.snd).Nodup) := by
  have hs0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).Good :=
    good_append_constNode_false hs
  have ho0 : s.nodes.length <
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length := by
    show s.nodes.length < (s.nodes ++ [constNode false]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hnode0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes[s.nodes.length] ≠
      rootNode := by
    show (s.nodes ++ [constNode false])[s.nodes.length]'ho0 ≠ rootNode
    have hget : (s.nodes ++ [constNode false])[s.nodes.length]'ho0 = constNode false :=
      coop_append_get_last s.nodes (constNode false)
    rw [hget]
    decide
  have hnd0 : ((({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).roots.map Prod.snd).Nodup) :=
    hnd
  exact coop_nodup_coopLits C.reverse s.nodes.length
    { s with nodes := s.nodes ++ [constNode false] } hs0 hnd0 ho0 hnode0

theorem coop_eval_coopLit (l : ℕ × Bool) (o : ℕ) (s : CoopSt) (σ : ℕ → Bool)
    (hs : s.Good) (hnd : (s.roots.map Prod.snd).Nodup) (ho : o < s.nodes.length) :
    (((coopLit l o s).1.evalList σ).getD (coopLit l o s).2 false) =
      (((s.evalList σ).getD o false) || ((σ l.1) == l.2)) := by
  obtain ⟨hrg, -, -⟩ := good_coopRoot l.1 hs
  have hfind : (coopRoot l.1 s).1.roots.find?
      (fun p => p.2 == (coopRoot l.1 s).1.nodes.length) = none := by
    apply coop_find?_eq_none_of_all_lt
    intro p hp
    obtain ⟨hlt, -⟩ := hrg.roots_ok p hp
    exact hlt
  have happ := evalList_append_singleton (coopRoot l.1 s).1 σ
    (orNode o (coopRoot l.1 s).2 l.2)
  have hgoal : ((coopLit l o s).1.evalList σ)
      = (((coopRoot l.1 s).1.evalList σ) ++
        [match (coopRoot l.1 s).1.roots.find? (fun p => p.2 == (coopRoot l.1 s).1.nodes.length) with
          | some p => σ p.1
          | none => forcedVal ((coopRoot l.1 s).1.evalList σ)
              (orNode o (coopRoot l.1 s).2 l.2)]) := happ
  have hacc : (coopLit l o s).2 = (coopRoot l.1 s).1.nodes.length := rfl
  rw [hgoal, hacc, hfind]
  dsimp only
  have hlen := evalList_length (coopRoot l.1 s).1 σ
  rw [← hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  have h0 : ([forcedVal ((coopRoot l.1 s).1.evalList σ)
      (orNode o (coopRoot l.1 s).2 l.2)].getD 0 false)
      = forcedVal ((coopRoot l.1 s).1.evalList σ) (orNode o (coopRoot l.1 s).2 l.2) := by simp
  rw [h0]
  simp only [orNode, forcedVal_gateNode]
  have hstab := coop_evalList_getD_coopRoot l.1 o s σ ho
  rw [hstab]
  have hroot : (((coopRoot l.1 s).1.evalList σ).getD (coopRoot l.1 s).2 false) = σ l.1 := by
    unfold coopRoot
    cases hlook : List.lookup l.1 s.roots with
    | some v =>
      dsimp only
      have hv : v < s.nodes.length := by
        have hmem : (l.1, v) ∈ s.roots := coop_mem_of_lookup hlook
        obtain ⟨hlt, -⟩ := hs.roots_ok (l.1, v) hmem
        exact hlt
      have hfindv : s.roots.find? (fun p => p.2 == v) = some (l.1, v) :=
        coop_find?_of_lookup s.roots l.1 v hlook hnd
      exact eval_root σ hv hfindv
    | none =>
      dsimp only
      have hlen2 : s.nodes.length < (s.nodes ++ [rootNode]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hfindn : ((l.1, s.nodes.length) :: s.roots).find? (fun p => p.2 == s.nodes.length)
          = some (l.1, s.nodes.length) :=
        coop_find?_fresh_head l.1 s.nodes.length s.roots
      exact eval_root σ hlen2 hfindn
  rw [hroot]

theorem coop_eval_coopLits (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt) (σ : ℕ → Bool)
    (hs : s.Good) (hnd : (s.roots.map Prod.snd).Nodup)
    (ho : o < s.nodes.length) (hnode : s.nodes[o] ≠ rootNode) :
    (((coopLits ls o s).1.evalList σ).getD (coopLits ls o s).2 false) =
      (((s.evalList σ).getD o false) || (ls.any (fun l => (σ l.1) == l.2))) := by
  induction ls generalizing o s with
  | nil =>
    simp only [coopLits]
    simp only [List.any_nil, Bool.or_false]
  | cons l ls ih =>
    obtain ⟨hr, h2, hne2⟩ := good_coopLit l hs ho hnode
    have hnd' := coop_nodup_coopLit l o s hs hnd
    have hstep := ih _ _ hr hnd' h2 hne2
    have hlit := coop_eval_coopLit l o s σ hs hnd ho
    show (((coopLits ls (coopLit l o s).2 (coopLit l o s).1).1.evalList σ).getD
        (coopLits ls (coopLit l o s).2 (coopLit l o s).1).2 false)
      = (((s.evalList σ).getD o false) || (((l :: ls).any (fun l => (σ l.1) == l.2))))
    rw [hstep, hlit]
    simp only [List.any_cons]
    exact Bool.or_assoc _ _ _

theorem coop_any_reverse (l : List (ℕ × Bool)) (f : (ℕ × Bool) → Bool) :
    (l.reverse.any f) = (l.any f) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.reverse_cons, List.any_append, ih]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    exact Bool.or_comm _ _

theorem coop_eval_coopClause_nodup (C : CNFClause) (s : CoopSt) (σ : ℕ → Bool)
    (hs : s.Good) (hnd : (s.roots.map Prod.snd).Nodup) :
    (((coopClause C s).evalList σ).getD (coopClause C s).acc false) =
      ((((s.evalList σ).getD s.acc false) && (clauseVal σ C))) := by
  have hs0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).Good :=
    good_append_constNode_false hs
  have ho0 : s.nodes.length <
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length := by
    show s.nodes.length < (s.nodes ++ [constNode false]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hnode0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes[s.nodes.length] ≠
      rootNode := by
    show (s.nodes ++ [constNode false])[s.nodes.length]'ho0 ≠ rootNode
    have hget : (s.nodes ++ [constNode false])[s.nodes.length]'ho0 = constNode false :=
      coop_append_get_last s.nodes (constNode false)
    rw [hget]
    decide
  have hnd0 : ((({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).roots.map Prod.snd).Nodup) :=
    hnd
  obtain ⟨hr, h2, hne2⟩ :=
    good_coopLits C.reverse hs0 ho0 hnode0
  have hndR := coop_nodup_coopLits C.reverse s.nodes.length
    { s with nodes := s.nodes ++ [constNode false] } hs0 hnd0 ho0 hnode0
  have hfind : (coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).1.roots.find?
        (fun p => p.2 == (coopLits C.reverse s.nodes.length
          { s with nodes := s.nodes ++ [constNode false] }).1.nodes.length) = none := by
    apply coop_find?_eq_none_of_all_lt
    intro p hp
    obtain ⟨hlt, -⟩ := hr.roots_ok p hp
    exact hlt
  have happ := evalList_append_singleton
    (coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).1 σ
    (andNode s.acc (coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).2)
  have hgoal : ((coopClause C s).evalList σ)
      = (((coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).1.evalList σ) ++
        [match (coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).1.roots.find?
          (fun p => p.2 == (coopLits C.reverse s.nodes.length
            { s with nodes := s.nodes ++ [constNode false] }).1.nodes.length) with
          | some p => σ p.1
          | none => forcedVal ((coopLits C.reverse s.nodes.length
              { s with nodes := s.nodes ++ [constNode false] }).1.evalList σ)
              (andNode s.acc (coopLits C.reverse s.nodes.length
                { s with nodes := s.nodes ++ [constNode false] }).2)]) := happ
  have hacc : (coopClause C s).acc
      = (coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).1.nodes.length :=
    rfl
  rw [hgoal, hacc, hfind]
  dsimp only
  have hlen := evalList_length
    (coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).1 σ
  rw [← hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  have h0 : ([forcedVal ((coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).1.evalList σ)
      (andNode s.acc (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).2)].getD 0 false)
      = forcedVal ((coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.evalList σ)
        (andNode s.acc (coopLits C.reverse s.nodes.length
          { s with nodes := s.nodes ++ [constNode false] }).2) := by simp
  rw [h0]
  simp only [andNode, forcedVal_gateNode]
  have hsacc0 : s.acc < ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length := by
    show s.acc < (s.nodes ++ [constNode false]).length
    have halt := hs.acc_lt
    simp only [List.length_append, List.length_singleton]
    omega
  have e1 := coop_evalList_getD_coopLits C.reverse s.nodes.length
    { s with nodes := s.nodes ++ [constNode false] } σ s.acc hsacc0
  have e2 := coop_evalList_getD_append s σ [constNode false] s.acc hs.acc_lt
  have hstab : (((coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).1.evalList σ).getD s.acc false)
      = ((s.evalList σ).getD s.acc false) := by
    rw [e2] at e1
    exact e1
  have hlits := coop_eval_coopLits C.reverse s.nodes.length
    { s with nodes := s.nodes ++ [constNode false] } σ hs0 hnd0 ho0 hnode0
  have hstart : ((({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).evalList σ).getD
      s.nodes.length false) = false := by
    have g0 : (({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).evalList σ)
        = (s.evalList σ) ++ [forcedVal (s.evalList σ) (constNode false)] := by
      have g0a := evalList_append_singleton s σ (constNode false)
      have gfind : s.roots.find? (fun p => p.2 == s.nodes.length) = none := by
        apply coop_find?_eq_none_of_all_lt
        intro p hp
        obtain ⟨hlt, -⟩ := hs.roots_ok p hp
        exact hlt
      rw [gfind] at g0a
      dsimp only at g0a
      exact g0a
    rw [g0]
    have hlen0 := evalList_length s σ
    rw [← hlen0, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    have h0a : ([forcedVal (s.evalList σ) (constNode false)].getD 0 false)
        = forcedVal (s.evalList σ) (constNode false) := by simp
    rw [h0a]
    exact forcedVal_constNode _ _
  have hclause : (((coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).1.evalList σ).getD
      (coopLits C.reverse s.nodes.length { s with nodes := s.nodes ++ [constNode false] }).2 false)
      = clauseVal σ C := by
    rw [hlits, hstart]
    have hany := coop_any_reverse C (fun l => (σ l.1) == l.2)
    simp only [clauseVal]
    rw [hany]
    simp
  rw [hstab, hclause]

/-- **The built network evaluates the formula.** Under assignment `σ`, the accumulator
node of the constructed network for `φ` evaluates to `φ.all (clauseVal σ)`: every clause
node reads its clause's value, and the AND chain collects them. The clause step needs the
duplicate-free root-index invariant (`coop_eval_coopClause_nodup`), which the construction
maintains. -/
theorem eval_coopSt_acc (φ : CNF) (σ : ℕ → Bool) :
    (coopSt φ).eval σ ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩ =
      φ.all (clauseVal σ) := by
  have hgen : ∀ (l : List CNFClause) (s : CoopSt), s.Good → (s.roots.map Prod.snd).Nodup →
      (((l.foldl (fun s C => coopClause C s) s).evalList σ).getD
        (l.foldl (fun s C => coopClause C s) s).acc false)
        = ((((s.evalList σ).getD s.acc false) && (l.all (clauseVal σ)))) := by
    intro l
    induction l with
    | nil =>
      intro s hs hnd
      simp only [List.foldl_nil, List.all_nil, Bool.and_true]
    | cons C l ih =>
      intro s hs hnd
      have hs1 := good_coopClause C hs
      have hnd1 := coop_nodup_coopClause C s hs hnd
      have hstep := ih (coopClause C s) hs1 hnd1
      have hclause := coop_eval_coopClause_nodup C s σ hs hnd
      show (((l.foldl (fun s C => coopClause C s) (coopClause C s)).evalList σ).getD
          (l.foldl (fun s C => coopClause C s) (coopClause C s)).acc false)
        = ((((s.evalList σ).getD s.acc false) && (((C :: l).all (clauseVal σ)))))
      rw [hstep, hclause]
      simp only [List.all_cons]
      exact Bool.and_assoc _ _ _
  have hnodup_init : (((⟨[constNode true], [], 0⟩ : CoopSt).roots.map Prod.snd).Nodup) :=
    List.nodup_nil
  have hinit : (((⟨[constNode true], [], 0⟩ : CoopSt).evalList σ).getD
      (⟨[constNode true], [], 0⟩ : CoopSt).acc false) = true := by
    have heval : ((⟨[constNode true], [], 0⟩ : CoopSt).evalList σ) = [true] := by
      show ([constNode true].foldl (fun (vals : List Bool) (v : RatNode) =>
        vals ++ [match ([] : List (ℕ × ℕ)).find? (fun p => p.2 == vals.length) with
          | some p => σ p.1 | none => forcedVal vals v]) []) = [true]
      simp only [List.foldl_cons, List.foldl_nil, List.find?_nil, forcedVal_constNode]
      rfl
    rw [heval]
    rfl
  have hmain := hgen φ.reverse _ good_init hnodup_init
  rw [hinit] at hmain
  simp only [Bool.true_and] at hmain
  rw [List.all_reverse] at hmain
  exact hmain

/-- **Reachable-state shape**: root nodes are exactly the registered roots (each
variable and index used at most once), and every non-root node's table has all
denominators `1`. Denominator `1` alone does not make a table deterministic: that also
needs `num ≤ den`, which this predicate does not ask. -/
def CoopSt.WellShaped (s : CoopSt) : Prop :=
  (∀ k (hk : k < s.nodes.length), s.nodes[k] = rootNode ∨
    ∀ row ∈ (s.nodes[k]).2, row.2.2 = 1) ∧
  (s.roots.map Prod.snd).Nodup ∧ (s.roots.map Prod.fst).Nodup ∧
  ∀ k (hk : k < s.nodes.length), s.nodes[k] = rootNode → ∃ x, (x, k) ∈ s.roots

theorem constNode_ne_rootNode (b : Bool) : constNode b ≠ rootNode := by
  cases b <;> decide

theorem andNode_ne_rootNode (i j : ℕ) : andNode i j ≠ rootNode := by
  unfold andNode gateNode rootNode
  intro heq
  have hfst : [i, j] = ([] : List ℕ) := congrArg Prod.fst heq
  simp at hfst

theorem coop_lookup_none_fst {x : ℕ} {roots : List (ℕ × ℕ)}
    (h : List.lookup x roots = none) : x ∉ roots.map Prod.fst := by
  induction roots with
  | nil => simp
  | cons p ps ih =>
    simp only [List.lookup] at h
    by_cases hx : (x == p.1) = true
    · simp only [hx] at h
      simp at h
    · have hfalse : (x == p.1) = false := by
        revert hx
        cases h : x == p.1
        case false => intro _; rfl
        case true => intro hx; simp at hx
      simp only [hfalse] at h
      have htail := ih h
      intro hmem
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp at hx
      · exact htail hmem

theorem wellShaped_init : (⟨[constNode true], [], 0⟩ : CoopSt).WellShaped := by
  unfold CoopSt.WellShaped
  dsimp only
  refine ⟨?_, by simp, by simp, ?_⟩
  · intro k hk
    simp at hk
    subst hk
    right
    show ∀ row ∈ (constNode true).2, row.2.2 = 1
    unfold constNode
    dsimp only
    intro row hr
    simp at hr
    obtain rfl := hr
    rfl
  · intro k hk hroot
    simp at hk
    subst hk
    have hroot2 : constNode true = rootNode := hroot
    exact absurd hroot2 (constNode_ne_rootNode true)

theorem wellShaped_coopRoot (x : ℕ) {s : CoopSt} (hs : s.Good)
    (hws : s.WellShaped) : (coopRoot x s).1.WellShaped := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    dsimp only
    exact hws
  | none =>
    dsimp only
    unfold CoopSt.WellShaped
    dsimp only
    have hlen : (s.nodes ++ [rootNode]).length = s.nodes.length + 1 := by simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hkold : k < s.nodes.length
      · have hget : (s.nodes ++ [rootNode])[k]'hk = s.nodes[k]'hkold :=
          List.getElem_append_left hkold
        rw [hget]
        exact hws.1 k hkold
      · have hkeq : k = s.nodes.length := by omega
        subst hkeq
        exact Or.inl (coop_append_get_last _ _)
    · show (s.nodes.length :: s.roots.map Prod.snd).Nodup
      have hnil : ∀ y ∈ s.roots.map Prod.snd, y ≠ s.nodes.length := by
        intro y hy
        obtain ⟨p, hpmem, hpeq⟩ := List.mem_map.mp hy
        obtain ⟨hlt, -⟩ := hs.roots_ok p hpmem
        omega
      refine List.Nodup.cons ?_ hws.2.1
      intro hmem
      exact (hnil _ hmem) rfl
    · show (x :: s.roots.map Prod.fst).Nodup
      refine List.Nodup.cons ?_ hws.2.2.1
      exact coop_lookup_none_fst hlook
    · intro k hk hroot
      by_cases hkold : k < s.nodes.length
      · have hget : (s.nodes ++ [rootNode])[k]'hk = s.nodes[k]'hkold :=
          List.getElem_append_left hkold
        rw [hget] at hroot
        obtain ⟨x', hmem⟩ := hws.2.2.2 k hkold hroot
        exact ⟨x', List.mem_cons_of_mem _ hmem⟩
      · have hkeq : k = s.nodes.length := by omega
        subst hkeq
        exact ⟨x, by simp⟩

theorem wellShaped_coopLit (l : ℕ × Bool) (o : ℕ) (s : CoopSt) (hs : s.Good)
    (hws : s.WellShaped) : (coopLit l o s).1.WellShaped := by
  have hwr := wellShaped_coopRoot l.1 hs hws
  unfold coopLit
  dsimp only
  unfold CoopSt.WellShaped
  dsimp only
  have hlen : ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length =
      (coopRoot l.1 s).1.nodes.length + 1 := by simp
  refine ⟨?_, hwr.2.1, hwr.2.2.1, ?_⟩
  · intro k hk
    by_cases hkold : k < (coopRoot l.1 s).1.nodes.length
    · have hget : ((coopRoot l.1 s).1.nodes ++
            [orNode o (coopRoot l.1 s).2 l.2])[k]'hk =
          (coopRoot l.1 s).1.nodes[k]'hkold :=
        List.getElem_append_left hkold
      rw [hget]
      exact hwr.1 k hkold
    · have hkeq : k = (coopRoot l.1 s).1.nodes.length := by omega
      subst hkeq
      right
      intro row hrw
      have hget : ((coopRoot l.1 s).1.nodes ++
          [orNode o (coopRoot l.1 s).2 l.2])[(coopRoot l.1 s).1.nodes.length]'hk =
          orNode o (coopRoot l.1 s).2 l.2 :=
        coop_append_get_last _ _
      rw [hget] at hrw
      unfold orNode at hrw
      unfold gateNode at hrw
      dsimp only at hrw
      simp at hrw
      rcases hrw with rfl | rfl | rfl | rfl <;> rfl
  · intro k hk hroot
    by_cases hkold : k < (coopRoot l.1 s).1.nodes.length
    · have hget : ((coopRoot l.1 s).1.nodes ++
            [orNode o (coopRoot l.1 s).2 l.2])[k]'hk =
          (coopRoot l.1 s).1.nodes[k]'hkold :=
        List.getElem_append_left hkold
      rw [hget] at hroot
      obtain ⟨x', hmem⟩ := hwr.2.2.2 k hkold hroot
      exact ⟨x', hmem⟩
    · have hkeq : k = (coopRoot l.1 s).1.nodes.length := by omega
      subst hkeq
      have hget : ((coopRoot l.1 s).1.nodes ++
          [orNode o (coopRoot l.1 s).2 l.2])[(coopRoot l.1 s).1.nodes.length]'hk =
          orNode o (coopRoot l.1 s).2 l.2 :=
        coop_append_get_last _ _
      rw [hget] at hroot
      exact absurd hroot (orNode_ne_rootNode _ _ _)

theorem wellShaped_coopLits (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt)
    (hs : s.Good) (hws : s.WellShaped)
    (ho : o < s.nodes.length) (hnode : s.nodes[o] ≠ rootNode) :
    (coopLits ls o s).1.WellShaped := by
  induction ls generalizing o s with
  | nil =>
    simp only [coopLits]
    exact hws
  | cons l ls ih =>
    simp only [coopLits]
    obtain ⟨hr, h2, hne2⟩ := good_coopLit l hs ho hnode
    have hwr := wellShaped_coopLit l o s hs hws
    exact ih _ _ hr hwr h2 hne2

theorem wellShaped_append_constNode_false {s : CoopSt} (hws : s.WellShaped) :
    ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).WellShaped := by
  unfold CoopSt.WellShaped
  dsimp only
  refine ⟨?_, hws.2.1, hws.2.2.1, ?_⟩
  · intro k hk
    have hlen : (s.nodes ++ [constNode false]).length = s.nodes.length + 1 := by simp
    by_cases hkold : k < s.nodes.length
    · have hget : (s.nodes ++ [constNode false])[k]'hk = s.nodes[k]'hkold :=
        List.getElem_append_left hkold
      rw [hget]
      exact hws.1 k hkold
    · have hkeq : k = s.nodes.length := by omega
      subst hkeq
      right
      intro row hrw
      have hget : (s.nodes ++ [constNode false])[s.nodes.length]'hk = constNode false :=
        coop_append_get_last _ _
      rw [hget] at hrw
      unfold constNode at hrw
      dsimp only at hrw
      simp at hrw
      obtain rfl := hrw
      rfl
  · intro k hk hroot
    have hlen : (s.nodes ++ [constNode false]).length = s.nodes.length + 1 := by simp
    by_cases hkold : k < s.nodes.length
    · have hget : (s.nodes ++ [constNode false])[k]'hk = s.nodes[k]'hkold :=
        List.getElem_append_left hkold
      rw [hget] at hroot
      obtain ⟨x', hmem⟩ := hws.2.2.2 k hkold hroot
      exact ⟨x', hmem⟩
    · have hkeq : k = s.nodes.length := by omega
      subst hkeq
      have hget : (s.nodes ++ [constNode false])[s.nodes.length]'hk = constNode false :=
        coop_append_get_last _ _
      rw [hget] at hroot
      exact absurd hroot (constNode_ne_rootNode _)

theorem wellShaped_append_andNode {t : CoopSt} (htw : t.WellShaped) (a b : ℕ) :
    ({ t with nodes := t.nodes ++ [andNode a b], acc := t.nodes.length } : CoopSt).WellShaped := by
  unfold CoopSt.WellShaped
  dsimp only
  refine ⟨?_, htw.2.1, htw.2.2.1, ?_⟩
  · intro k hk
    have hlen : (t.nodes ++ [andNode a b]).length = t.nodes.length + 1 := by simp
    by_cases hkold : k < t.nodes.length
    · have hget : (t.nodes ++ [andNode a b])[k]'hk = t.nodes[k]'hkold :=
        List.getElem_append_left hkold
      rw [hget]
      exact htw.1 k hkold
    · have hkeq : k = t.nodes.length := by omega
      subst hkeq
      right
      intro row hrw
      have hget : (t.nodes ++ [andNode a b])[t.nodes.length]'hk = andNode a b :=
        coop_append_get_last _ _
      rw [hget] at hrw
      unfold andNode at hrw
      unfold gateNode at hrw
      dsimp only at hrw
      simp at hrw
      rcases hrw with rfl | rfl | rfl | rfl <;> rfl
  · intro k hk hroot
    have hlen : (t.nodes ++ [andNode a b]).length = t.nodes.length + 1 := by simp
    by_cases hkold : k < t.nodes.length
    · have hget : (t.nodes ++ [andNode a b])[k]'hk = t.nodes[k]'hkold :=
        List.getElem_append_left hkold
      rw [hget] at hroot
      obtain ⟨x', hmem⟩ := htw.2.2.2 k hkold hroot
      exact ⟨x', hmem⟩
    · have hkeq : k = t.nodes.length := by omega
      subst hkeq
      have hget : (t.nodes ++ [andNode a b])[t.nodes.length]'hk = andNode a b :=
        coop_append_get_last _ _
      rw [hget] at hroot
      exact absurd hroot (andNode_ne_rootNode _ _)

theorem wellShaped_coopClause (C : CNFClause) {s : CoopSt} (hs : s.Good)
    (hws : s.WellShaped) : (coopClause C s).WellShaped := by
  have hs0 := good_append_constNode_false hs
  have hws0 := wellShaped_append_constNode_false hws
  have ho0 : s.nodes.length <
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length := by
    show s.nodes.length < (s.nodes ++ [constNode false]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hnode0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes[s.nodes.length]'ho0 ≠
      rootNode := by
    show (s.nodes ++ [constNode false])[s.nodes.length]'ho0 ≠ rootNode
    have hget : (s.nodes ++ [constNode false])[s.nodes.length]'ho0 = constNode false :=
      coop_append_get_last s.nodes (constNode false)
    rw [hget]
    exact constNode_ne_rootNode _
  have hwr := wellShaped_coopLits C.reverse s.nodes.length
    { s with nodes := s.nodes ++ [constNode false] } hs0 hws0 ho0 hnode0
  exact wellShaped_append_andNode hwr _ _

theorem wellShaped_coopSt (φ : CNF) : (coopSt φ).WellShaped := by
  have h : ∀ (l : List CNFClause) (s : CoopSt),
      s.Good → s.WellShaped → (l.foldl (fun s C => coopClause C s) s).WellShaped := by
    intro l
    induction l with
    | nil =>
      intro s hs hws
      simpa
    | cons C l ih =>
      intro s hs hws
      simp only [List.foldl_cons]
      exact ih _ (good_coopClause C hs) (wellShaped_coopClause C hs hws)
  exact h φ.reverse _ good_init wellShaped_init

theorem coop_evalList_take_length (s : CoopSt) (σ : ℕ → Bool) (m : ℕ)
    (hm : m ≤ s.nodes.length) :
    (({ s with nodes := s.nodes.take m } : CoopSt).evalList σ).length = m := by
  calc (({ s with nodes := s.nodes.take m } : CoopSt).evalList σ).length
      = (s.nodes.take m).length := evalList_length _ _
    _ = m := by rw [List.length_take, Nat.min_eq_left hm]

theorem coop_evalList_getD_take_eq (s : CoopSt) (σ : ℕ → Bool) (m j : ℕ)
    (hj : j < m) (hm : m ≤ s.nodes.length) :
    (s.evalList σ).getD j false =
      (({ s with nodes := s.nodes.take m } : CoopSt).evalList σ).getD j false := by
  have hfull : s.evalList σ = List.foldl (fun (vals : List Bool) (v : RatNode) =>
      vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ p.1
        | none => forcedVal vals v]) [] (s.nodes.take m ++ s.nodes.drop m) := by
    calc s.evalList σ
        = List.foldl (fun (vals : List Bool) (v : RatNode) =>
            vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
              | some p => σ p.1
              | none => forcedVal vals v]) [] s.nodes := rfl
      _ = List.foldl (fun (vals : List Bool) (v : RatNode) =>
            vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
              | some p => σ p.1
              | none => forcedVal vals v]) [] (s.nodes.take m ++ s.nodes.drop m) := by
          rw [List.take_append_drop]
  have h3 : (({ s with nodes := s.nodes.take m } : CoopSt).evalList σ) =
      List.foldl (fun (vals : List Bool) (v : RatNode) =>
        vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
          | some p => σ p.1
          | none => forcedVal vals v]) [] (s.nodes.take m) := rfl
  rw [hfull, List.foldl_append, ← h3]
  have hjlen : j < (({ s with nodes := s.nodes.take m } : CoopSt).evalList σ).length := by
    rw [coop_evalList_take_length s σ m hm]
    exact hj
  exact evalList_foldl_getD_aux s σ (s.nodes.drop m) _ j false hjlen

theorem coop_evalList_getD_take_succ (s : CoopSt) (σ : ℕ → Bool) (k : ℕ)
    (hk : k < s.nodes.length)
    (hfind : s.roots.find? (fun p => p.2 == k) = none) :
    (({ s with nodes := s.nodes.take (k + 1) } : CoopSt).evalList σ).getD k false =
      forcedVal (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ) s.nodes[k] := by
  have htake : s.nodes.take (k + 1) = s.nodes.take k ++ [s.nodes[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  have hlen : (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ).length = k :=
    coop_evalList_take_length s σ k (le_of_lt hk)
  have hfold : (({ s with nodes := s.nodes.take (k + 1) } : CoopSt).evalList σ) =
      (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ) ++
        [forcedVal (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ) s.nodes[k]] := by
    have h1 : (({ s with nodes := s.nodes.take (k + 1) } : CoopSt).evalList σ) =
        List.foldl (fun (vals : List Bool) (v : RatNode) =>
          vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
            | some p => σ p.1
            | none => forcedVal vals v]) [] (s.nodes.take (k + 1)) := rfl
    have h3 : (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ) =
        List.foldl (fun (vals : List Bool) (v : RatNode) =>
          vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
            | some p => σ p.1
            | none => forcedVal vals v]) [] (s.nodes.take k) := rfl
    rw [h1, htake, List.foldl_append, ← h3]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hlen, hfind]
  have hlek : (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ).length ≤ k := by
    omega
  have h0 : ([forcedVal (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ)
      s.nodes[k]].getD 0 false) =
      forcedVal (({ s with nodes := s.nodes.take k } : CoopSt).evalList σ) s.nodes[k] := by
    simp
  rw [hfold, List.getD_append_right _ _ _ _ hlek, hlen, Nat.sub_self, h0]

theorem ratJoint_factor_eval {s : CoopSt} (hs : s.Good) (hws : s.WellShaped) (σ : ℕ → Bool)
    (k : Fin s.nodes.length) :
    (if s.eval σ k then (s.nodes.get k).prob (RatNet.parentVals s.nodes k (s.eval σ))
      else 1 - (s.nodes.get k).prob (RatNet.parentVals s.nodes k (s.eval σ))) =
    if s.nodes[k] = rootNode then (1 / 2 : ℚ) else 1 := by
  have hwf : RatNode.WellFormed k.val (s.nodes.get k) := hs.nodes_wf k.val k.isLt
  obtain ⟨-, hlt, _, _, hrows⟩ := hwf
  by_cases hroot : s.nodes[k] = rootNode
  · have hget : s.nodes.get k = rootNode := hroot
    have hpv : RatNet.parentVals s.nodes k (s.eval σ) = [] := by
      unfold RatNet.parentVals
      rw [hget]
      exact rfl
    have hprob : (s.nodes.get k).prob (RatNet.parentVals s.nodes k (s.eval σ)) = 1 / 2 := by
      rw [hpv, hget]
      simp [RatNode.prob, rootNode]
    rw [hprob, ite_eq_left hroot]
    cases s.eval σ k
    · simp
      norm_num
    · simp
  · rw [ite_eq_right hroot]
    have hfindnone : s.roots.find? (fun p => p.2 == k.val) = none := by
      apply List.find?_eq_none.mpr
      intro q hq hcon
      rw [beq_iff_eq] at hcon
      have hmem := hs.roots_ok q hq
      obtain ⟨_hqk, hqroot⟩ := hmem
      simp only [hcon] at hqroot
      exact hroot hqroot
    have hbridge : RatNet.parentVals s.nodes k (s.eval σ) =
        (s.nodes.get k).1.map (fun j =>
          ((({ s with nodes := s.nodes.take k.val } : CoopSt).evalList σ)).getD j false) := by
      unfold RatNet.parentVals
      apply List.map_eq_map_iff.mpr
      intro j hj
      have hjlt : j < k.val := hlt j hj
      have hjlen : j < s.nodes.length := lt_trans hjlt k.isLt
      simp only [dite_eq_left hjlen]
      exact coop_evalList_getD_take_eq s σ k.val j hjlt (le_of_lt k.isLt)
    have heval : s.eval σ k = forcedVal
        ((({ s with nodes := s.nodes.take k.val } : CoopSt).evalList σ)) (s.nodes.get k) := by
      have hstep := coop_evalList_getD_take_succ s σ k.val k.isLt hfindnone
      have hagree2 := coop_evalList_getD_take_eq s σ (k.val + 1) k.val
        (Nat.lt_succ_self k.val) (by have h := k.isLt; omega)
      exact hagree2.trans hstep
    have hforced : forcedVal ((({ s with nodes := s.nodes.take k.val } : CoopSt).evalList σ))
          (s.nodes.get k) =
        decide ((s.nodes.get k).prob (RatNet.parentVals s.nodes k (s.eval σ)) = 1) := by
      unfold forcedVal
      rw [← hbridge]
    rw [heval, hforced]
    set u : List Bool := RatNet.parentVals s.nodes k (s.eval σ) with hu
    have hcases : (s.nodes.get k).prob u = 0 ∨ (s.nodes.get k).prob u = 1 := by
      match hfind : (s.nodes.get k).2.find? (fun row => row.1 == u) with
      | none =>
        left
        unfold RatNode.prob
        rw [hfind]
      | some row =>
        have hmem : row ∈ (s.nodes.get k).2 := List.mem_of_find?_eq_some hfind
        obtain ⟨-, -, hnumle⟩ := hrows row hmem
        have hws_k : s.nodes.get k = rootNode ∨
            ∀ row_ ∈ (s.nodes.get k).2, row_.2.2 = 1 := hws.1 k.val k.isLt
        rcases hws_k with hroot2 | hden1
        · exact absurd hroot2 hroot
        · have hden : row.2.2 = 1 := hden1 row hmem
          rw [hden] at hnumle
          have hprob_eq : (s.nodes.get k).prob u = (row.2.1 : ℚ) := by
            simp only [RatNode.prob, hfind, hden, Nat.cast_one, div_one]
          have h01 : row.2.1 = 0 ∨ row.2.1 = 1 := by omega
          rcases h01 with h0 | h1
          · left
            rw [hprob_eq, h0]
            simp
          · right
            rw [hprob_eq, h1]
            simp
    rcases hcases with hp0 | hp1
    · rw [hp0]
      by_cases hdec : (0 : ℚ) = 1
      · norm_num at hdec
      · simp [hdec]
    · rw [hp1]
      by_cases hdec : (1 : ℚ) = 1
      · simp
      · simp at hdec

theorem ratJoint_eval {s : CoopSt} (hs : s.Good) (hws : s.WellShaped) (σ : ℕ → Bool) :
    RatNet.ratJoint s.nodes (s.eval σ) = (1 / 2 : ℚ) ^ s.roots.length := by
  have hcard : (Finset.univ.filter (fun k : Fin s.nodes.length => s.nodes[k] = rootNode)).card
      = s.roots.length := by
    have hT : ((s.roots.map Prod.snd).toFinset).card = s.roots.length := by
      rw [List.toFinset_card_of_nodup hws.2.1, List.length_map]
    rw [← hT]
    refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hk_lt : k.val < s.nodes.length := k.isLt
      have hk' : s.nodes[k.val] = rootNode := hk
      obtain ⟨x, hx⟩ := hws.2.2.2 k.val hk_lt hk'
      rw [List.mem_toFinset]
      exact List.mem_map_of_mem hx
    · intro k1 _ k2 _ h
      exact Fin.ext h
    · intro m hm
      rw [List.mem_toFinset, List.mem_map] at hm
      obtain ⟨p, hp, hpm⟩ := hm
      obtain ⟨hlt, hroot⟩ := hs.roots_ok p hp
      have hmem : s.nodes[(⟨p.2, hlt⟩ : Fin s.nodes.length)] = rootNode := hroot
      exact ⟨(⟨p.2, hlt⟩ : Fin s.nodes.length),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, hpm⟩
  have hrat : RatNet.ratJoint s.nodes (s.eval σ) = ∏ k : Fin s.nodes.length,
      (if s.eval σ k then (s.nodes.get k).prob (RatNet.parentVals s.nodes k (s.eval σ))
        else 1 - (s.nodes.get k).prob (RatNet.parentVals s.nodes k (s.eval σ))) := rfl
  rw [hrat, Finset.prod_congr rfl (fun k _ => ratJoint_factor_eval hs hws σ k)]
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  rw [hcard]

/-- Lookup finds the unique entry for a registered variable. -/
theorem coop_lookup_of_mem_fst_nodup {roots : List (ℕ × ℕ)} {v k : ℕ}
    (hmem : (v, k) ∈ roots) (hnd : (roots.map Prod.fst).Nodup) :
    List.lookup v roots = some k := by
  induction roots with
  | nil => simp at hmem
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hndtail⟩ := hnd
    simp only [List.mem_cons] at hmem
    simp only [List.lookup]
    by_cases heq : (v == p.1) = true
    · simp only [heq]
      show (some p.2) = some k
      have hveq : v = p.1 := beq_iff_eq.mp heq
      rcases hmem with hmem | hmem
      · have hkk : k = p.2 := congrArg Prod.snd hmem
        rw [← hkk]
      · exfalso
        apply hnotin
        rw [← hveq]
        exact List.mem_map_of_mem hmem
    · have hfalse : (v == p.1) = false := by
        revert heq
        cases h : v == p.1
        case false => intro _; rfl
        case true => intro heq; simp at heq
      simp only [hfalse]
      show List.lookup v ps = some k
      apply ih
      · rcases hmem with hmem | hmem
        · exfalso
          have hveq : v = p.1 := congrArg Prod.fst hmem
          rw [hveq] at heq
          simp at heq
        · exact hmem
      · exact hndtail

/-- `find?` on the index finds the unique entry for a registered node. -/
theorem coop_find?_of_mem_snd_nodup {roots : List (ℕ × ℕ)} {v k : ℕ}
    (hmem : (v, k) ∈ roots) (hnd : (roots.map Prod.snd).Nodup) :
    roots.find? (fun p => p.2 == k) = some (v, k) := by
  induction roots with
  | nil => simp at hmem
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hndtail⟩ := hnd
    simp only [List.mem_cons] at hmem
    simp only [List.find?_cons]
    by_cases heq : (p.2 == k) = true
    · simp only [heq]
      show (some p) = some (v, k)
      have hkeq : p.2 = k := beq_iff_eq.mp heq
      rcases hmem with hmem | hmem
      · rw [← hmem]
      · exfalso
        apply hnotin
        rw [hkeq]
        exact List.mem_map_of_mem hmem
    · have hfalse : (p.2 == k) = false := by
        revert heq
        cases h : p.2 == k
        case false => intro _; rfl
        case true => intro heq; simp at heq
      simp only [hfalse]
      show List.find? (fun p => p.2 == k) ps = some (v, k)
      apply ih
      · rcases hmem with hmem | hmem
        · exfalso
          have hkeq : k = p.2 := congrArg Prod.snd hmem
          rw [← hkeq] at heq
          simp at heq
        · exact hmem
      · exact hndtail

theorem eval_eq_of_ratJoint_ne {s : CoopSt} (hs : s.Good) (hws : s.WellShaped)
    (x : Fin s.nodes.length → Bool) (hx : RatNet.ratJoint s.nodes x ≠ 0) :
    x = s.eval (fun v => match s.roots.lookup v with
      | some j => if h : j < s.nodes.length then x ⟨j, h⟩ else false
      | none => false) := by
  set σ : ℕ → Bool := fun v => match s.roots.lookup v with
    | some j => if h : j < s.nodes.length then x ⟨j, h⟩ else false
    | none => false with hσdef
  have hσ_of_lookup : ∀ (v j : ℕ) (hj : j < s.nodes.length),
      s.roots.lookup v = some j → σ v = x ⟨j, hj⟩ := by
    intro v j hj hlook
    simp [hσdef, hlook, hj]
  have hfac : ∀ k : Fin s.nodes.length,
      (if x k then (s.nodes.get k).prob (RatNet.parentVals s.nodes k x)
        else 1 - (s.nodes.get k).prob (RatNet.parentVals s.nodes k x)) ≠ 0 := by
    intro k
    have hx' : (∏ k : Fin s.nodes.length, (if x k then (s.nodes.get k).prob
        (RatNet.parentVals s.nodes k x)
        else 1 - (s.nodes.get k).prob (RatNet.parentVals s.nodes k x))) ≠ 0 := hx
    exact Finset.prod_ne_zero_iff.mp hx' k (Finset.mem_univ k)
  have main : ∀ (m : ℕ) (k : Fin s.nodes.length),
      k.val < m → x k = s.eval σ k := by
    intro m
    induction m with
    | zero =>
      intro k hkm
      exact False.elim (Nat.not_lt_zero k.val hkm)
    | succ m ih =>
      intro k hkm
      have hwf : RatNode.WellFormed k.val (s.nodes.get k) := hs.nodes_wf k.val k.isLt
      obtain ⟨-, hlt, -, -, hrows⟩ := hwf
      by_cases hroot : s.nodes[k] = rootNode
      · obtain ⟨v, hmem⟩ := hws.2.2.2 k.val k.isLt hroot
        have hlook : s.roots.lookup v = some k.val :=
          coop_lookup_of_mem_fst_nodup hmem hws.2.2.1
        have hfind : s.roots.find? (fun p => p.2 == k.val) = some (v, k.val) :=
          coop_find?_of_mem_snd_nodup hmem hws.2.1
        have heval : s.eval σ k = σ v := eval_root σ k.isLt hfind
        have hσv : σ v = x k := hσ_of_lookup v k.val k.isLt hlook
        rw [heval, hσv]
      · have hfindnone : s.roots.find? (fun p => p.2 == k.val) = none := by
          apply List.find?_eq_none.mpr
          intro q hq hcon
          rw [beq_iff_eq] at hcon
          obtain ⟨_, hqroot⟩ := hs.roots_ok q hq
          simp only [hcon] at hqroot
          exact hroot hqroot
        have heval : s.eval σ k = forcedVal
            ((({ s with nodes := s.nodes.take k.val } : CoopSt).evalList σ))
            (s.nodes.get k) := by
          have hstep := coop_evalList_getD_take_succ s σ k.val k.isLt hfindnone
          have hagree := coop_evalList_getD_take_eq s σ (k.val + 1) k.val
            (Nat.lt_succ_self k.val) (by have h := k.isLt; omega)
          exact hagree.trans hstep
        have hbridge : RatNet.parentVals s.nodes k x =
            (s.nodes.get k).1.map (fun j =>
              ((({ s with nodes := s.nodes.take k.val } : CoopSt).evalList σ)).getD
                j false) := by
          unfold RatNet.parentVals
          apply List.map_eq_map_iff.mpr
          intro j hj
          have hjlt : j < k.val := hlt j hj
          have hjlen : j < s.nodes.length := lt_trans hjlt k.isLt
          simp only [dite_eq_left hjlen]
          have hIH := ih ⟨j, hjlen⟩ (by show j < m; omega)
          have htake := coop_evalList_getD_take_eq s σ k.val j hjlt (le_of_lt k.isLt)
          rw [hIH]
          exact htake
        have hforced : forcedVal
              ((({ s with nodes := s.nodes.take k.val } : CoopSt).evalList σ))
              (s.nodes.get k) =
            decide ((s.nodes.get k).prob (RatNet.parentVals s.nodes k x) = 1) := by
          unfold forcedVal
          rw [← hbridge]
        have hcases : (s.nodes.get k).prob (RatNet.parentVals s.nodes k x) = 0 ∨
            (s.nodes.get k).prob (RatNet.parentVals s.nodes k x) = 1 := by
          match hfind : (s.nodes.get k).2.find?
              (fun row => row.1 == RatNet.parentVals s.nodes k x) with
          | none =>
            left
            unfold RatNode.prob
            rw [hfind]
          | some row =>
            have hmem : row ∈ (s.nodes.get k).2 := List.mem_of_find?_eq_some hfind
            obtain ⟨-, -, hnumle⟩ := hrows row hmem
            have hws_k : s.nodes.get k = rootNode ∨
                ∀ row_ ∈ (s.nodes.get k).2, row_.2.2 = 1 := hws.1 k.val k.isLt
            rcases hws_k with hroot2 | hden1
            · exact absurd hroot2 hroot
            · have hden : row.2.2 = 1 := hden1 row hmem
              rw [hden] at hnumle
              have hprob_eq : (s.nodes.get k).prob (RatNet.parentVals s.nodes k x) =
                  (row.2.1 : ℚ) := by
                simp only [RatNode.prob, hfind, hden, Nat.cast_one, div_one]
              have h01 : row.2.1 = 0 ∨ row.2.1 = 1 := by omega
              rcases h01 with h0 | h1
              · left
                rw [hprob_eq, h0]
                simp
              · right
                rw [hprob_eq, h1]
                simp
        cases hxkk : x k with
        | true =>
          have hfacT : (s.nodes.get k).prob (RatNet.parentVals s.nodes k x) ≠ 0 := by
            simpa [hxkk] using hfac k
          rcases hcases with hp0 | hp1
          · exact absurd hp0 hfacT
          · rw [heval, hforced, hp1]
            simp
        | false =>
          have hfacF : 1 - (s.nodes.get k).prob (RatNet.parentVals s.nodes k x) ≠ 0 := by
            simpa [hxkk] using hfac k
          rcases hcases with hp0 | hp1
          · rw [heval, hforced, hp0]
            simp
          · rw [hp1] at hfacF
            norm_num at hfacF
  funext k
  exact main (k.val + 1) k (Nat.lt_succ_self k.val)

/-- A clause with a true literal evaluates to true. -/
theorem clauseVal_true_of_mem {σ : ℕ → Bool} {C : CNFClause} {x : ℕ} {b : Bool}
    (hmem : (x, b) ∈ C) (hval : σ x = b) : clauseVal σ C = true := by
  unfold clauseVal
  rw [List.any_eq_true]
  exact ⟨(x, b), hmem, by show (σ x == b) = true; rw [hval]; exact beq_self_eq_true b⟩

/-- A clause evaluating to true has a true literal. -/
theorem exists_mem_of_clauseVal_true {σ : ℕ → Bool} {C : CNFClause}
    (h : clauseVal σ C = true) : ∃ x b, (x, b) ∈ C ∧ σ x = b := by
  unfold clauseVal at h
  rw [List.any_eq_true] at h
  obtain ⟨l, hmem, hbeq⟩ := h
  obtain ⟨x, b⟩ := l
  exact ⟨x, b, hmem, beq_iff_eq.mp hbeq⟩

/-- The rational joint is nonnegative on a well-formed network. -/
theorem ratJoint_nonneg {r : RatNet} (hr : r.WellFormed) (x : Fin r.length → Bool) :
    0 ≤ r.ratJoint x := by
  have hx' : r.ratJoint x = ∏ k : Fin r.length, (if x k then (r.get k).prob
      (r.parentVals k x) else 1 - (r.get k).prob (r.parentVals k x)) := rfl
  rw [hx']
  apply Finset.prod_nonneg
  intro k _
  have h0 := RatNode.prob_nonneg k.val (r.get k) (hr.2 k.val k.isLt) (r.parentVals k x)
  have h1 := RatNode.prob_le_one k.val (r.get k) (hr.2 k.val k.isLt) (r.parentVals k x)
  by_cases hxk : x k = true
  · rw [ite_eq_left hxk]
    exact h0
  · rw [ite_eq_right hxk]
    exact sub_nonneg.mpr h1

/-- Adding a clause leaves the accumulator as the last node. -/
theorem coopClause_acc (C : CNFClause) (s : CoopSt) :
    (coopClause C s).acc = (coopClause C s).nodes.length - 1 := by
  unfold coopClause
  simp

/-- The construction leaves the accumulator as the last node. -/
theorem coopSt_acc (φ : CNF) : (coopSt φ).acc = (coopSt φ).nodes.length - 1 := by
  have h : ∀ (l : List CNFClause) (s : CoopSt),
      s.acc = s.nodes.length - 1 → (l.foldl (fun s C => coopClause C s) s).acc =
        (l.foldl (fun s C => coopClause C s) s).nodes.length - 1 := by
    intro l
    induction l with
    | nil =>
      intro s hs
      simpa
    | cons C l ih =>
      intro s hs
      simp only [List.foldl_cons]
      exact ih _ (coopClause_acc C s)
  exact h φ.reverse _ rfl

/-- The output probability is the probability that the accumulator is true. -/
theorem outProb_coopSt_acc (φ : CNF) :
    (cooperNet φ).outProb =
      probTrue (cooperNet φ).toBayesNet ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩ := by
  have hlen : 0 < (cooperNet φ).length := by
    have h := (good_coopSt φ).acc_lt
    show 0 < (coopSt φ).nodes.length
    omega
  unfold RatNet.outProb
  rw [dite_eq_left hlen]
  congr 1
  apply Fin.ext
  show (cooperNet φ).length - 1 = (coopSt φ).acc
  unfold cooperNet
  exact (coopSt_acc φ).symm

/-- **Reduction correctness**: a CNF formula is satisfiable iff the output of its network is true
with positive probability. This extends Cooper's 3SAT construction (Cooper 1990, Sections 4.1
and 4.2) to arbitrary CNF formulas, each clause built as a chain of binary OR nodes. -/
theorem cnfSat_iff_outProb_pos (φ : CNF) : CNFSat φ ↔ 0 < (cooperNet φ).outProb := by
  have hsG := good_coopSt φ
  have hsW := wellShaped_coopSt φ
  have hwf : (cooperNet φ).WellFormed := cooperNet_wellFormed φ
  rw [outProb_coopSt_acc φ]
  show CNFSat φ ↔ 0 < probTrue (RatNet.toBayesNet ((coopSt φ).nodes))
    ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩
  unfold probTrue
  have hwf' : RatNet.WellFormed ((coopSt φ).nodes) := hwf
  have hnn : ∀ x : Fin ((coopSt φ).nodes).length → Bool,
      0 ≤ (RatNet.toBayesNet ((coopSt φ).nodes)).joint x := by
    intro x
    rw [RatNet.joint_toBayesNet _ hwf']
    rw [Rat.cast_nonneg]
    exact ratJoint_nonneg hwf' x
  constructor
  · intro hsat
    obtain ⟨v, hsat⟩ := hsat
    have hcl : ∀ C ∈ φ, clauseVal v C = true := by
      intro C hC
      obtain ⟨x, b, hmem, hval⟩ := hsat C hC
      exact clauseVal_true_of_mem hmem hval
    have hall : φ.all (clauseVal v) = true :=
      List.all_eq_true.mpr (fun C hC => hcl C hC)
    have htacc : (coopSt φ).eval v ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩ = true := by
      rw [eval_coopSt_acc]
      exact hall
    have hterm : (0 : ℝ) < (RatNet.toBayesNet ((coopSt φ).nodes)).joint ((coopSt φ).eval v) := by
      rw [RatNet.joint_toBayesNet _ hwf']
      rw [ratJoint_eval hsG hsW v]
      have hq : (0 : ℚ) < (1 / 2) ^ ((coopSt φ).roots.length) := by positivity
      rw [Rat.cast_pos]
      exact hq
    have hmem : (coopSt φ).eval v ∈ Finset.univ.filter
        (fun x : Fin ((coopSt φ).nodes).length → Bool =>
          x ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩ = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, htacc⟩
    have hle := Finset.single_le_sum (fun x _ => hnn x) hmem
    exact lt_of_lt_of_le hterm hle
  · intro hpos
    have hex : ∃ x ∈ Finset.univ.filter
        (fun x : Fin ((coopSt φ).nodes).length → Bool =>
          x ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩ = true),
        0 < (RatNet.toBayesNet ((coopSt φ).nodes)).joint x := by
      by_contra hcon
      push Not at hcon
      have hzero : (∑ x ∈ Finset.univ.filter
          (fun x : Fin ((coopSt φ).nodes).length → Bool =>
            x ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩ = true),
          (RatNet.toBayesNet ((coopSt φ).nodes)).joint x) = 0 :=
        Finset.sum_eq_zero (fun x hx => le_antisymm (hcon x hx) (hnn x))
      rw [hzero] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨x, hxmem, hxpos⟩ := hex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxmem
    have hxne : RatNet.ratJoint ((coopSt φ).nodes) x ≠ 0 := by
      intro h0
      rw [RatNet.joint_toBayesNet _ hwf', h0, Rat.cast_zero] at hxpos
      exact lt_irrefl 0 hxpos
    have heq := eval_eq_of_ratJoint_ne hsG hsW x hxne
    rw [heq] at hxmem
    have hall : φ.all (clauseVal (fun v => match (coopSt φ).roots.lookup v with
        | some j => if h : j < (coopSt φ).nodes.length then x ⟨j, h⟩ else false
        | none => false)) = true := by
      have h := eval_coopSt_acc φ (fun v => match (coopSt φ).roots.lookup v with
        | some j => if h : j < (coopSt φ).nodes.length then x ⟨j, h⟩ else false
        | none => false)
      have hxmem2 : (coopSt φ).eval (fun v => match (coopSt φ).roots.lookup v with
        | some j => if h : j < (coopSt φ).nodes.length then x ⟨j, h⟩ else false
        | none => false) ⟨(coopSt φ).acc, (good_coopSt φ).acc_lt⟩ = true := hxmem
      rw [h] at hxmem2
      exact hxmem2
    refine ⟨(fun v => match (coopSt φ).roots.lookup v with
      | some j => if h : j < (coopSt φ).nodes.length then x ⟨j, h⟩ else false
      | none => false), fun C hC => ?_⟩
    have hcl : clauseVal (fun v => match (coopSt φ).roots.lookup v with
        | some j => if h : j < (coopSt φ).nodes.length then x ⟨j, h⟩ else false
        | none => false) C = true :=
      List.all_eq_true.mp hall C hC
    exact exists_mem_of_clauseVal_true hcl

theorem encodeClause_length_eq (C : CNFClause) :
    (encodeClause C).length = C.length + 1 + (C.flatMap encodeLit).length := by
  rw [Cslib.CookLevin.encodeClause_length, List.length_flatMap]

theorem flatMap_encodeLit_length_ge (C : CNFClause) :
    C.length ≤ (C.flatMap encodeLit).length := by
  rw [List.length_flatMap, ← List.length_map (fun l => (encodeLit l).length)]
  apply List.length_le_sum_of_one_le
  intro i hi
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hi
  rw [Cslib.CookLevin.encodeLit_length]
  omega

theorem encodeClause_ge (C : CNFClause) : 1 + 2 * C.length ≤ (encodeClause C).length := by
  have h1 := flatMap_encodeLit_length_ge C
  have h2 := encodeClause_length_eq C
  omega

theorem encodeCNF_length_eq (φ : CNF) :
    (encodeCNF φ).length = φ.length + 1 + (φ.flatMap encodeClause).length := by
  rw [Cslib.CookLevin.encodeCNF_length, List.length_flatMap]
theorem coopRoot_len_le_succ (x : ℕ) (s : CoopSt) :
    (coopRoot x s).1.nodes.length ≤ s.nodes.length + 1 := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v => simp
  | none => simp

theorem coopLit_len_le_add2 (l : ℕ × Bool) (o : ℕ) (s : CoopSt) :
    (coopLit l o s).1.nodes.length ≤ s.nodes.length + 2 := by
  have h := coopRoot_len_le_succ l.1 s
  unfold coopLit
  simp only
  have hlen : ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length =
      (coopRoot l.1 s).1.nodes.length + 1 := by simp
  omega

theorem coopLits_len_le (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt) :
    (coopLits ls o s).1.nodes.length ≤ s.nodes.length + 2 * ls.length := by
  induction ls generalizing o s with
  | nil => simp [coopLits]
  | cons l ls ih =>
    simp only [coopLits]
    have h1 := coopLit_len_le_add2 l o s
    have h2 := ih (coopLit l o s).2 (coopLit l o s).1
    simp only [List.length_cons] at h2 ⊢
    omega

theorem coopClause_len_le (C : CNFClause) (s : CoopSt) :
    (coopClause C s).nodes.length ≤ s.nodes.length + 2 + 2 * C.length := by
  have h := coopLits_len_le C.reverse s.nodes.length
    ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt)
  unfold coopClause
  simp only
  have hlen0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length =
      s.nodes.length + 1 := by simp
  have hlen1 : (coopLits C.reverse s.nodes.length
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt)).1.nodes.length + 1 =
      ((coopLits C.reverse s.nodes.length
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt)).1.nodes ++
      [andNode s.acc (coopLits C.reverse s.nodes.length
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt)).2]).length := by simp
  have hrev : C.reverse.length = C.length := List.length_reverse
  omega

theorem flatMap_reverse_len_eq {α β : Type} (l : List α) (f : α → List β) :
    (l.reverse.flatMap f).length = (l.flatMap f).length := by
  rw [List.length_flatMap, List.length_flatMap, List.map_reverse, List.sum_reverse]

theorem fold_coopClause_len_le (l : List CNFClause) (s : CoopSt) :
    (l.foldl (fun s C => coopClause C s) s).nodes.length ≤
      s.nodes.length + (l.flatMap encodeClause).length + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons C l ih =>
    simp only [List.foldl_cons]
    have hIH := ih (coopClause C s)
    have hC := coopClause_len_le C s
    have hE := encodeClause_ge C
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at hIH ⊢
    omega

/-- **Polynomial size: nodes.** The network has at most as many nodes as the SAT input has
bits. -/
theorem cooperNet_length_le (φ : CNF) : (cooperNet φ).length ≤ (encodeCNF φ).length := by
  have hfold := fold_coopClause_len_le φ.reverse ⟨[constNode true], [], 0⟩
  have hCNF := encodeCNF_length_eq φ
  have hflat : (φ.reverse.flatMap encodeClause).length = (φ.flatMap encodeClause).length :=
    flatMap_reverse_len_eq φ encodeClause
  have hrevlen : φ.reverse.length = φ.length := List.length_reverse
  have hinit : (⟨[constNode true], [], 0⟩ : CoopSt).nodes.length = 1 := rfl
  unfold cooperNet coopSt
  omega

theorem unary_length_eq (k : ℕ) : (unary k).length = k + 1 := by
  unfold unary
  simp [List.length_append, List.length_replicate]

theorem encodeRow_length_eq (row : List Bool × ℕ × ℕ) :
    (encodeRow row).length = 2 * row.1.length + row.2.1 + row.2.2 + 3 := by
  unfold encodeRow
  have h1 := unary_length_eq row.1.length
  have h2 := unary_length_eq row.2.1
  have h3 := unary_length_eq row.2.2
  simp only [List.length_append] at h1 h2 h3 ⊢
  omega

theorem encodeRatNode_rootNode_eq : (encodeRatNode rootNode).length = 9 := by
  decide

theorem encodeRatNode_constNode_le (b : Bool) : (encodeRatNode (constNode b)).length ≤ 8 := by
  cases b <;> decide

theorem andNode_rows_length0 : ((andNode 0 0).2.flatMap encodeRow).length = 33 := by
  decide

theorem orNode_rows_true0 : ((orNode 0 0 true).2.flatMap encodeRow).length = 35 := by
  decide

theorem orNode_rows_false0 : ((orNode 0 0 false).2.flatMap encodeRow).length = 35 := by
  decide

theorem andNode_rows_length (i j : ℕ) :
    ((andNode i j).2.flatMap encodeRow).length = 33 := by
  have h : (andNode i j).2 = (andNode 0 0).2 := rfl
  rw [h, andNode_rows_length0]

theorem orNode_rows_length (o v : ℕ) (b : Bool) :
    ((orNode o v b).2.flatMap encodeRow).length = 35 := by
  cases b with
  | true =>
    have h : (orNode o v true).2 = (orNode 0 0 true).2 := rfl
    rw [h, orNode_rows_true0]
  | false =>
    have h : (orNode o v false).2 = (orNode 0 0 false).2 := rfl
    rw [h, orNode_rows_false0]

theorem encodeRatNode_andNode_eq (i j : ℕ) :
    (encodeRatNode (andNode i j)).length = i + j + 43 := by
  have h1 : (andNode i j).1 = [i, j] := rfl
  have h1len : (andNode i j).1.length = 2 := rfl
  have h2len : (andNode i j).2.length = 4 := rfl
  have hrows := andNode_rows_length i j
  have hflat : ((andNode i j).1.flatMap unary).length = i + j + 2 := by
    rw [h1]
    simp [List.flatMap_cons, List.length_append, unary_length_eq]
    omega
  have hu1 : (unary (andNode i j).1.length).length = 3 := by
    rw [h1len]
    exact unary_length_eq 2
  have hu2 : (unary (andNode i j).2.length).length = 5 := by
    rw [h2len]
    exact unary_length_eq 4
  unfold encodeRatNode
  simp only [List.length_append]
  omega

theorem encodeRatNode_orNode_eq (o v : ℕ) (b : Bool) :
    (encodeRatNode (orNode o v b)).length = o + v + 45 := by
  have h1 : (orNode o v b).1 = [o, v] := rfl
  have h1len : (orNode o v b).1.length = 2 := rfl
  have h2len : (orNode o v b).2.length = 4 := rfl
  have hrows := orNode_rows_length o v b
  have hflat : ((orNode o v b).1.flatMap unary).length = o + v + 2 := by
    rw [h1]
    simp [List.flatMap_cons, List.length_append, unary_length_eq]
    omega
  have hu1 : (unary (orNode o v b).1.length).length = 3 := by
    rw [h1len]
    exact unary_length_eq 2
  have hu2 : (unary (orNode o v b).2.length).length = 5 := by
    rw [h2len]
    exact unary_length_eq 4
  unfold encodeRatNode
  simp only [List.length_append]
  omega

def encodeBound (s : CoopSt) : Prop :=
  ∀ v ∈ s.nodes, (encodeRatNode v).length ≤ 2 * s.nodes.length + 41

theorem encodeBound_init : encodeBound ⟨[constNode true], [], 0⟩ := by
  intro v hv
  have heq : v = constNode true := by
    simpa using hv
  subst heq
  have hle := encodeRatNode_constNode_le true
  simp
  omega

theorem encodeBound_coopRoot (x : ℕ) (s : CoopSt) (hs : encodeBound s) :
    encodeBound (coopRoot x s).1 := by
  unfold coopRoot
  cases hlook : List.lookup x s.roots with
  | some v =>
    dsimp only
    exact hs
  | none =>
    dsimp only
    intro w hw
    have hmem : w ∈ s.nodes ∨ w ∈ [rootNode] := by
      simpa using hw
    rcases hmem with hOld | hNew
    · have hle := hs w hOld
      have hlen : (s.nodes ++ [rootNode]).length = s.nodes.length + 1 := by simp
      have hgoal : (encodeRatNode w).length ≤ 2 * (s.nodes ++ [rootNode]).length + 41 := by
        omega
      exact hgoal
    · have heq : w = rootNode := by simpa using hNew
      subst heq
      rw [encodeRatNode_rootNode_eq]
      have hlen : (s.nodes ++ [rootNode]).length = s.nodes.length + 1 := by simp
      have hgoal : 9 ≤ 2 * (s.nodes ++ [rootNode]).length + 41 := by
        omega
      exact hgoal

theorem encodeBound_coopLit (l : ℕ × Bool) (o : ℕ) (s : CoopSt)
    (hs : encodeBound s) (hg : s.Good) (ho : o < s.nodes.length) :
    encodeBound (coopLit l o s).1 := by
  obtain ⟨_, hv, _⟩ := good_coopRoot l.1 hg
  have hrBound := encodeBound_coopRoot l.1 s hs
  have hmono := coopRoot_nodes_length_le l.1 s
  have ho_lt : o < (coopRoot l.1 s).1.nodes.length := by omega
  unfold coopLit
  dsimp only
  intro w hw
  have hmem : w ∈ (coopRoot l.1 s).1.nodes ∨
      w ∈ [orNode o (coopRoot l.1 s).2 l.2] := by
    simpa using hw
  rcases hmem with hOld | hNew
  · have hle := hrBound w hOld
    have hlen : ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length =
        (coopRoot l.1 s).1.nodes.length + 1 := by simp
    have hgoal : (encodeRatNode w).length ≤
        2 * ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length + 41 := by
      omega
    exact hgoal
  · have heq : w = orNode o (coopRoot l.1 s).2 l.2 := by simpa using hNew
    subst heq
    rw [encodeRatNode_orNode_eq]
    have hlen : ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length =
        (coopRoot l.1 s).1.nodes.length + 1 := by simp
    have hgoal : o + (coopRoot l.1 s).2 + 45 ≤
        2 * ((coopRoot l.1 s).1.nodes ++ [orNode o (coopRoot l.1 s).2 l.2]).length + 41 := by
      omega
    exact hgoal

theorem encodeBound_coopLits (ls : List (ℕ × Bool)) (o : ℕ) (s : CoopSt)
    (hs : encodeBound s) (hg : s.Good)
    (ho : o < s.nodes.length) (hnode : s.nodes[o] ≠ rootNode) :
    encodeBound (coopLits ls o s).1 := by
  induction ls generalizing o s with
  | nil => simpa [coopLits] using hs
  | cons l ls ih =>
    simp only [coopLits]
    obtain ⟨hrGood, hout, hnode'⟩ := good_coopLit l hg ho hnode
    have hrBound := encodeBound_coopLit l o s hs hg ho
    exact ih (coopLit l o s).2 (coopLit l o s).1 hrBound hrGood hout hnode'

theorem encodeBound_append_constFalse (s : CoopSt) (hs : encodeBound s) :
    encodeBound ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt) := by
  intro w hw
  have hmem : w ∈ s.nodes ∨ w ∈ [constNode false] := by
    simpa using hw
  rcases hmem with hOld | hNew
  · have hle := hs w hOld
    have hlen : (s.nodes ++ [constNode false]).length = s.nodes.length + 1 := by simp
    have hgoal : (encodeRatNode w).length ≤ 2 * (s.nodes ++ [constNode false]).length + 41 := by
      omega
    exact hgoal
  · have heq : w = constNode false := by simpa using hNew
    subst heq
    have hle := encodeRatNode_constNode_le false
    have hlen : (s.nodes ++ [constNode false]).length = s.nodes.length + 1 := by simp
    have hgoal : (encodeRatNode (constNode false)).length ≤
        2 * (s.nodes ++ [constNode false]).length + 41 := by
      omega
    exact hgoal

theorem encodeBound_coopClause (C : CNFClause) (s : CoopSt)
    (hs : encodeBound s) (hg : s.Good) :
    encodeBound (coopClause C s) := by
  have hs0 := encodeBound_append_constFalse s hs
  have hg0 := good_append_constNode_false hg
  have ho0 : s.nodes.length <
      ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length := by
    show s.nodes.length < (s.nodes ++ [constNode false]).length
    simp only [List.length_append, List.length_singleton]
    omega
  have hnode0 : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes[s.nodes.length]'ho0 ≠
      rootNode := by
    show (s.nodes ++ [constNode false])[s.nodes.length]'ho0 ≠ rootNode
    have hget : (s.nodes ++ [constNode false])[s.nodes.length]'ho0 = constNode false :=
      coop_append_get_last s.nodes (constNode false)
    rw [hget]
    decide
  have hrBound := encodeBound_coopLits C.reverse s.nodes.length
    ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt) hs0 hg0 ho0 hnode0
  obtain ⟨hrGood, h2, _⟩ := good_coopLits C.reverse hg0 ho0 hnode0
  have hacc : s.acc <
      (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.nodes.length := by
    have hle := coopLits_nodes_length_le C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }
    have hlen : ({ s with nodes := s.nodes ++ [constNode false] } : CoopSt).nodes.length =
        s.nodes.length + 1 := by
      show (s.nodes ++ [constNode false]).length = s.nodes.length + 1
      simp
    have halt := hg.acc_lt
    omega
  unfold coopClause
  dsimp only
  intro w hw
  have hmem : w ∈ (coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).1.nodes ∨
      w ∈ [andNode s.acc (coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).2] := by
    simpa using hw
  rcases hmem with hOld | hNew
  · have hle := hrBound w hOld
    have hlen : ((coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.nodes ++
        [andNode s.acc (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).2]).length =
        (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.nodes.length + 1 := by simp
    have hgoal : (encodeRatNode w).length ≤ 2 *
        ((coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.nodes ++
        [andNode s.acc (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).2]).length + 41 := by
      omega
    exact hgoal
  · have heq : w = andNode s.acc (coopLits C.reverse s.nodes.length
      { s with nodes := s.nodes ++ [constNode false] }).2 := by simpa using hNew
    subst heq
    rw [encodeRatNode_andNode_eq]
    have hlen : ((coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.nodes ++
        [andNode s.acc (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).2]).length =
        (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.nodes.length + 1 := by simp
    have hgoal : s.acc + (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).2 + 43 ≤ 2 *
        ((coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).1.nodes ++
        [andNode s.acc (coopLits C.reverse s.nodes.length
        { s with nodes := s.nodes ++ [constNode false] }).2]).length + 41 := by
      omega
    exact hgoal

theorem encodeBound_fold (l : List CNFClause) (s : CoopSt)
    (hs : encodeBound s) (hg : s.Good) :
    encodeBound (l.foldl (fun s C => coopClause C s) s) := by
  induction l generalizing s with
  | nil => simpa using hs
  | cons C l ih =>
    simp only [List.foldl_cons]
    have hs' := encodeBound_coopClause C s hs hg
    have hg' := good_coopClause C hg
    exact ih _ hs' hg'

theorem encodeBound_coopSt (φ : CNF) : encodeBound (coopSt φ) := by
  unfold coopSt
  exact encodeBound_fold φ.reverse _ encodeBound_init good_init

theorem encodeRatNet_length_eq (r : RatNet) :
    (encodeRatNet r).length = r.length + 1 + (r.flatMap encodeRatNode).length := by
  have hflat : (r.reverse.flatMap encodeRatNode).length =
      (r.flatMap encodeRatNode).length :=
    flatMap_reverse_len_eq r encodeRatNode
  have hu := unary_length_eq r.length
  unfold encodeRatNet
  simp only [List.length_append] at hu ⊢
  omega

theorem flatMap_encodeRatNode_le (r : RatNet) (B : ℕ)
    (h : ∀ v ∈ r, (encodeRatNode v).length ≤ B) :
    (r.flatMap encodeRatNode).length ≤ r.length * B := by
  induction r with
  | nil => simp
  | cons v r ih =>
    have hv : (encodeRatNode v).length ≤ B := h v List.mem_cons_self
    have hr : ∀ w ∈ r, (encodeRatNode w).length ≤ B := fun w hw =>
      h w (List.mem_cons_of_mem v hw)
    have hih := ih hr
    have he : (r.length + 1) * B = r.length * B + B := by ring
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at hih ⊢
    omega

/-- **Polynomial size: encoding.** -/
theorem encodeRatNet_cooperNet_length_le (φ : CNF) :
    (encodeRatNet (cooperNet φ)).length ≤
      2 * (encodeCNF φ).length ^ 2 + 42 * (encodeCNF φ).length + 1 := by
  have hBound := encodeBound_coopSt φ
  have hLen : (cooperNet φ).length ≤ (encodeCNF φ).length := cooperNet_length_le φ
  have hEq := encodeRatNet_length_eq (cooperNet φ)
  have hB : ∀ v ∈ cooperNet φ, (encodeRatNode v).length ≤ 2 * (cooperNet φ).length + 41 :=
    hBound
  have hFlat := flatMap_encodeRatNode_le (cooperNet φ) (2 * (cooperNet φ).length + 41) hB
  have heq : (cooperNet φ).length + 1 + (cooperNet φ).length * (2 * (cooperNet φ).length + 41) =
      2 * (cooperNet φ).length ^ 2 + 42 * (cooperNet φ).length + 1 := by ring
  have h1 : (encodeRatNet (cooperNet φ)).length ≤
      2 * (cooperNet φ).length ^ 2 + 42 * (cooperNet φ).length + 1 := by
    calc (encodeRatNet (cooperNet φ)).length
        = (cooperNet φ).length + 1 + ((cooperNet φ).flatMap encodeRatNode).length := hEq
      _ ≤ (cooperNet φ).length + 1 + (cooperNet φ).length * (2 * (cooperNet φ).length + 41) :=
        Nat.add_le_add_left hFlat _
      _ = 2 * (cooperNet φ).length ^ 2 + 42 * (cooperNet φ).length + 1 := heq
  have hSq : (cooperNet φ).length ^ 2 ≤ (encodeCNF φ).length ^ 2 :=
    Nat.pow_le_pow_left hLen 2
  have h2a : 2 * (cooperNet φ).length ^ 2 ≤ 2 * (encodeCNF φ).length ^ 2 :=
    Nat.mul_le_mul_left 2 hSq
  have h2b : 42 * (cooperNet φ).length ≤ 42 * (encodeCNF φ).length :=
    Nat.mul_le_mul_left 42 hLen
  have h3 : 2 * (cooperNet φ).length ^ 2 + 42 * (cooperNet φ).length ≤
      2 * (encodeCNF φ).length ^ 2 + 42 * (encodeCNF φ).length :=
    Nat.add_le_add h2a h2b
  have h2 : 2 * (cooperNet φ).length ^ 2 + 42 * (cooperNet φ).length + 1 ≤
      2 * (encodeCNF φ).length ^ 2 + 42 * (encodeCNF φ).length + 1 :=
    Nat.add_le_add h3 (le_refl 1)
  exact le_trans h1 h2

/-- Values read off at the roots of `cooperEx`: entry `i` holds the root of var `i + 1`. -/
def coopExRootRead (x : Fin (coopSt cooperEx).nodes.length → Bool) : Fin 4 → Bool :=
  ![x ⟨12, by decide⟩, x ⟨6, by decide⟩, x ⟨4, by decide⟩, x ⟨2, by decide⟩]

/-- Evaluation depends only on the assignment at the recorded roots' variables. -/
theorem evalList_congr_of_forall_roots_eq {s : CoopSt} {σ₁ σ₂ : ℕ → Bool}
    (h : ∀ p ∈ s.roots, σ₁ p.1 = σ₂ p.1) :
    s.evalList σ₁ = s.evalList σ₂ := by
  have hstep : (fun (vals : List Bool) (v : RatNode) =>
      vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ₁ p.1
        | none => forcedVal vals v]) =
      (fun (vals : List Bool) (v : RatNode) =>
      vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ₂ p.1
        | none => forcedVal vals v]) := by
    funext vals v
    show vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ₁ p.1
        | none => forcedVal vals v] =
      vals ++ [match s.roots.find? (fun p => p.2 == vals.length) with
        | some p => σ₂ p.1
        | none => forcedVal vals v]
    cases hfind : s.roots.find? (fun p => p.2 == vals.length) with
    | none => rfl
    | some p =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hp := h p hmem
      show vals ++ [σ₁ p.1] = vals ++ [σ₂ p.1]
      rw [hp]
  unfold CoopSt.evalList
  rw [hstep]

/-- Pointwise version of `evalList_congr_of_forall_roots_eq`. -/
theorem eval_congr_of_forall_roots_eq {s : CoopSt} {σ₁ σ₂ : ℕ → Bool}
    (h : ∀ p ∈ s.roots, σ₁ p.1 = σ₂ p.1) (k : Fin s.nodes.length) :
    s.eval σ₁ k = s.eval σ₂ k := by
  unfold CoopSt.eval
  rw [evalList_congr_of_forall_roots_eq h]

/-- **Instance evaluation on `3SAT_ex`**: 10 of the 16 assignments of `u₁, …, u₄` satisfy it. -/
theorem outProb_cooperEx_card :
    (cooperNet cooperEx).outProb =
      (((Finset.univ : Finset (Fin 4 → Bool)).filter (fun r =>
        (coopSt cooperEx).eval (fun v => match v with
          | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) ⟨19, by decide⟩)).card : ℝ) *
        (1 / 2) ^ 4 := by
  have hsG : (coopSt cooperEx).Good := good_coopSt cooperEx
  have hsW : (coopSt cooperEx).WellShaped := wellShaped_coopSt cooperEx
  have hwf : (cooperNet cooperEx).WellFormed := cooperNet_wellFormed cooperEx
  have hroots : (coopSt cooperEx).roots = [(1, 12), (2, 6), (3, 4), (4, 2)] := rfl
  have hrootslen : (coopSt cooperEx).roots.length = 4 := rfl
  have hagree : ∀ (x : Fin (coopSt cooperEx).nodes.length → Bool) (p : ℕ × ℕ),
      p ∈ (coopSt cooperEx).roots →
      (match (coopSt cooperEx).roots.lookup p.1 with
        | some j => if h : j < (coopSt cooperEx).nodes.length then x ⟨j, h⟩ else false
        | none => false) =
      (fun v => match v with
        | 1 => (coopExRootRead x) 0 | 2 => (coopExRootRead x) 1
        | 3 => (coopExRootRead x) 2 | 4 => (coopExRootRead x) 3
        | _ => false) p.1 := by
    intro x p hp
    rw [hroots] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> rfl
  have hx_eq : ∀ x : Fin (coopSt cooperEx).nodes.length → Bool,
      RatNet.ratJoint (coopSt cooperEx).nodes x ≠ 0 →
      x = (coopSt cooperEx).eval (fun v => match v with
        | 1 => (coopExRootRead x) 0 | 2 => (coopExRootRead x) 1
        | 3 => (coopExRootRead x) 2 | 4 => (coopExRootRead x) 3
        | _ => false) := by
    intro x hxne
    have heq := eval_eq_of_ratJoint_ne hsG hsW x hxne
    have hcongr : (coopSt cooperEx).eval (fun v => match (coopSt cooperEx).roots.lookup v with
        | some j => if h : j < (coopSt cooperEx).nodes.length then x ⟨j, h⟩ else false
        | none => false) =
        (coopSt cooperEx).eval (fun v => match v with
        | 1 => (coopExRootRead x) 0 | 2 => (coopExRootRead x) 1
        | 3 => (coopExRootRead x) 2 | 4 => (coopExRootRead x) 3
        | _ => false) := by
      funext k
      exact eval_congr_of_forall_roots_eq (fun p hp => hagree x p hp) k
    exact heq.trans hcongr
  have hρ0 : ∀ x : Fin (coopSt cooperEx).nodes.length → Bool,
      coopExRootRead x 0 = x ⟨12, by decide⟩ := fun x => rfl
  have hρ1 : ∀ x : Fin (coopSt cooperEx).nodes.length → Bool,
      coopExRootRead x 1 = x ⟨6, by decide⟩ := fun x => rfl
  have hρ2 : ∀ x : Fin (coopSt cooperEx).nodes.length → Bool,
      coopExRootRead x 2 = x ⟨4, by decide⟩ := fun x => rfl
  have hρ3 : ∀ x : Fin (coopSt cooperEx).nodes.length → Bool,
      coopExRootRead x 3 = x ⟨2, by decide⟩ := fun x => rfl
  rw [outProb_coopSt_acc cooperEx]
  simp only [cooperNet]
  have hfin : (⟨(coopSt cooperEx).acc, (good_coopSt cooperEx).acc_lt⟩ :
      Fin (coopSt cooperEx).nodes.length) = ⟨19, by decide⟩ := rfl
  rw [hfin]
  unfold probTrue
  have hwf' : RatNet.WellFormed ((coopSt cooperEx).nodes) := hwf
  have hjoint : ∀ x : Fin (coopSt cooperEx).nodes.length → Bool,
      ((RatNet.toBayesNet ((coopSt cooperEx).nodes)).joint x) =
        ((RatNet.ratJoint ((coopSt cooperEx).nodes) x : ℚ) : ℝ) :=
    fun x => RatNet.joint_toBayesNet _ hwf' x
  simp only [hjoint]
  have hB : (Finset.univ.filter (fun x : Fin (coopSt cooperEx).nodes.length → Bool =>
        x ⟨19, by decide⟩ = true ∧ RatNet.ratJoint (coopSt cooperEx).nodes x ≠ 0))
      ⊆ Finset.univ.filter (fun x : Fin (coopSt cooperEx).nodes.length → Bool =>
        x ⟨19, by decide⟩ = true) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  have hB0 : ∀ x ∈ Finset.univ.filter (fun x : Fin (coopSt cooperEx).nodes.length → Bool =>
        x ⟨19, by decide⟩ = true),
      x ∉ Finset.univ.filter (fun x : Fin (coopSt cooperEx).nodes.length → Bool =>
        x ⟨19, by decide⟩ = true ∧ RatNet.ratJoint (coopSt cooperEx).nodes x ≠ 0) →
      (((RatNet.ratJoint ((coopSt cooperEx).nodes) x : ℚ)) : ℝ) = 0 := by
    intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnx
    have hz : RatNet.ratJoint (coopSt cooperEx).nodes x = 0 := by
      by_contra hne
      exact hnx ⟨hx, hne⟩
    rw [hz]
    simp
  rw [← Finset.sum_subset hB hB0]
  have hbij : (∑ x ∈ Finset.univ.filter (fun x : Fin (coopSt cooperEx).nodes.length → Bool =>
        x ⟨19, by decide⟩ = true ∧ RatNet.ratJoint (coopSt cooperEx).nodes x ≠ 0),
        ((RatNet.ratJoint ((coopSt cooperEx).nodes) x : ℚ) : ℝ)) =
      ∑ r ∈ Finset.univ.filter (fun r : Fin 4 → Bool =>
        (coopSt cooperEx).eval (fun v => match v with
          | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) ⟨19, by decide⟩),
        ((((1 / 2 : ℚ) ^ 4 : ℚ)) : ℝ) := by
    refine Finset.sum_bij
      (s := Finset.univ.filter (fun x : Fin (coopSt cooperEx).nodes.length → Bool =>
        x ⟨19, by decide⟩ = true ∧ RatNet.ratJoint (coopSt cooperEx).nodes x ≠ 0))
      (t := Finset.univ.filter (fun r : Fin 4 → Bool =>
        (coopSt cooperEx).eval (fun v => match v with
          | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) ⟨19, by decide⟩))
      (f := fun x : Fin (coopSt cooperEx).nodes.length → Bool =>
        ((RatNet.ratJoint ((coopSt cooperEx).nodes) x : ℚ) : ℝ))
      (g := fun _ : Fin 4 → Bool => ((((1 / 2 : ℚ) ^ 4 : ℚ)) : ℝ))
      (fun x _ => coopExRootRead x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨hx19, hxne⟩ := hx
      have hxeq := hx_eq x hxne
      rw [hxeq] at hx19
      simpa using hx19
    · intro x hx y hy hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      obtain ⟨hx19, hxne⟩ := hx
      obtain ⟨hy19, hyne⟩ := hy
      have hxy' : coopExRootRead x = coopExRootRead y := hxy
      have hex := hx_eq x hxne
      have hey := hx_eq y hyne
      rw [hxy'] at hex
      rw [hex]
      exact hey.symm
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      have hr19 : (coopSt cooperEx).eval (fun v => match v with
          | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)
          ⟨19, by decide⟩ = true := by
        simpa using hr
      refine ⟨(coopSt cooperEx).eval (fun v => match v with
        | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact hr19
        · have hrj := ratJoint_eval hsG hsW (fun v => match v with
              | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)
          rw [hrootslen] at hrj
          rw [hrj]
          norm_num
      · have hk12 : 12 < (coopSt cooperEx).nodes.length := by decide
        have hf12 : (coopSt cooperEx).roots.find? (fun p => p.2 == 12) = some (1, 12) := rfl
        have hk6 : 6 < (coopSt cooperEx).nodes.length := by decide
        have hf6 : (coopSt cooperEx).roots.find? (fun p => p.2 == 6) = some (2, 6) := rfl
        have hk4 : 4 < (coopSt cooperEx).nodes.length := by decide
        have hf4 : (coopSt cooperEx).roots.find? (fun p => p.2 == 4) = some (3, 4) := rfl
        have hk2 : 2 < (coopSt cooperEx).nodes.length := by decide
        have hf2 : (coopSt cooperEx).roots.find? (fun p => p.2 == 2) = some (4, 2) := rfl
        show coopExRootRead ((coopSt cooperEx).eval (fun v => match v with
          | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)) = r
        funext i
        fin_cases i
        · show coopExRootRead ((coopSt cooperEx).eval (fun v => match v with
              | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)) 0 = r 0
          rw [hρ0]
          exact eval_root (fun v => match v with
            | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) hk12 hf12
        · show coopExRootRead ((coopSt cooperEx).eval (fun v => match v with
              | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)) 1 = r 1
          rw [hρ1]
          exact eval_root (fun v => match v with
            | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) hk6 hf6
        · show coopExRootRead ((coopSt cooperEx).eval (fun v => match v with
              | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)) 2 = r 2
          rw [hρ2]
          exact eval_root (fun v => match v with
            | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) hk4 hf4
        · show coopExRootRead ((coopSt cooperEx).eval (fun v => match v with
              | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)) 3 = r 3
          rw [hρ3]
          exact eval_root (fun v => match v with
            | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) hk2 hf2
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨hx19, hxne⟩ := hx
      have heq := eval_eq_of_ratJoint_ne hsG hsW x hxne
      have hrj := ratJoint_eval hsG hsW (fun v => match (coopSt cooperEx).roots.lookup v with
        | some j => if h : j < (coopSt cooperEx).nodes.length then x ⟨j, h⟩ else false
        | none => false)
      rw [hrootslen] at hrj
      rw [heq, hrj]
  rw [hbij, Finset.sum_const, nsmul_eq_mul]
  have hC : ((((1 / 2 : ℚ) ^ 4 : ℚ)) : ℝ) = (1 / 2 : ℝ) ^ 4 := by norm_num
  rw [hC]

/-- **Instance evaluation on `3SAT_ex`**: 10 of the 16 assignments of `u₁, …, u₄` satisfy it. -/
theorem outProb_cooperEx : (cooperNet cooperEx).outProb = 5 / 8 := by
  rw [outProb_cooperEx_card]
  have hsem : ∀ r : Fin 4 → Bool, (coopSt cooperEx).eval (fun v => match v with
      | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) ⟨19, by decide⟩ =
      cooperEx.all (clauseVal (fun v => match v with
        | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)) := by
    intro r
    have h := eval_coopSt_acc cooperEx (fun v => match v with
      | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)
    exact h
  have hset : ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun r =>
      (coopSt cooperEx).eval (fun v => match v with
        | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false) ⟨19, by decide⟩)) =
      ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun r =>
        cooperEx.all (clauseVal (fun v => match v with
          | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)))) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsem r]
  rw [hset]
  have hcard : ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun r =>
      cooperEx.all (clauseVal (fun v => match v with
        | 1 => r 0 | 2 => r 1 | 3 => r 2 | 4 => r 3 | _ => false)))).card = 10 := by
    decide
  rw [hcard]
  norm_num

/-- **Instance evaluation on the unsatisfiable control.** -/
theorem outProb_cooperUnsat : (cooperNet cooperUnsat).outProb = 0 := by
  have hnet : cooperNet cooperUnsat = [constNode true, constNode false, rootNode,
      orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode,
      orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true,
      andNode 9 11] := rfl
  have hwf : (cooperNet cooperUnsat).WellFormed := cooperNet_wellFormed _
  rw [hnet] at hwf ⊢
  have h0len : (0:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h1len : (1:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h2len : (2:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h3len : (3:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h4len : (4:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h5len : (5:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h6len : (6:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h7len : (7:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h8len : (8:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h9len : (9:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h10len : (10:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h11len : (11:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have h12len : (12:ℕ) < [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length := by decide
  have hget1 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨1, h1len⟩ = constNode false := rfl
  have hget3 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨3, h3len⟩ = orNode 1 2 false := rfl
  have hget4 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨4, h4len⟩ = andNode 0 3 := rfl
  have hget5 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨5, h5len⟩ = constNode false := rfl
  have hget6 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨6, h6len⟩ = orNode 5 2 true := rfl
  have hget8 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨8, h8len⟩ = orNode 6 7 false := rfl
  have hget9 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨9, h9len⟩ = andNode 4 8 := rfl
  have hget10 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨10, h10len⟩ = constNode false := rfl
  have hget11 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨11, h11len⟩ = orNode 10 7 true := rfl
  have hget12 : [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].get ⟨12, h12len⟩ = andNode 9 11 := rfl
  have hpv1 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨1, h1len⟩ x = [] :=
    fun x => rfl
  have hpv3 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨3, h3len⟩ x =
      [x ⟨1, h1len⟩, x ⟨2, h2len⟩] := fun x => rfl
  have hpv4 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨4, h4len⟩ x =
      [x ⟨0, h0len⟩, x ⟨3, h3len⟩] := fun x => rfl
  have hpv5 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨5, h5len⟩ x = [] :=
    fun x => rfl
  have hpv6 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨6, h6len⟩ x =
      [x ⟨5, h5len⟩, x ⟨2, h2len⟩] := fun x => rfl
  have hpv8 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨8, h8len⟩ x =
      [x ⟨6, h6len⟩, x ⟨7, h7len⟩] := fun x => rfl
  have hpv9 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨9, h9len⟩ x =
      [x ⟨4, h4len⟩, x ⟨8, h8len⟩] := fun x => rfl
  have hpv10 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨10, h10len⟩ x = [] :=
    fun x => rfl
  have hpv11 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨11, h11len⟩ x =
      [x ⟨10, h10len⟩, x ⟨7, h7len⟩] := fun x => rfl
  have hpv12 : ∀ x : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length → Bool, RatNet.parentVals [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11] ⟨12, h12len⟩ x =
      [x ⟨9, h9len⟩, x ⟨11, h11len⟩] := fun x => rfl
  have hConstF : RatNode.prob (constNode false) [] = 0 := by simp [RatNode.prob, constNode]
  have hAndFF : ∀ i j, RatNode.prob (andNode i j) [false, false] = 0 := by
    intro i j; simp [RatNode.prob, andNode, gateNode]
  have hAndFT : ∀ i j, RatNode.prob (andNode i j) [false, true] = 0 := by
    intro i j; simp [RatNode.prob, andNode, gateNode]
  have hAndTF : ∀ i j, RatNode.prob (andNode i j) [true, false] = 0 := by
    intro i j; simp [RatNode.prob, andNode, gateNode]
  have hOrTFF : ∀ o v, RatNode.prob (orNode o v true) [false, false] = 0 := by
    intro o v; simp [RatNode.prob, orNode, gateNode]
  have hOrFFT : ∀ o v, RatNode.prob (orNode o v false) [false, true] = 0 := by
    intro o v; simp [RatNode.prob, orNode, gateNode]
  show probTrue (RatNet.toBayesNet [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11]) ⟨12, h12len⟩ = 0
  unfold probTrue
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [RatNet.joint_toBayesNet _ hwf]
  rw [Rat.cast_eq_zero]
  unfold RatNet.ratJoint
  by_cases h2 : x ⟨2, h2len⟩ = true
  · by_cases h7 : x ⟨7, h7len⟩ = true
    · by_cases h1 : x ⟨1, h1len⟩ = true
      · refine Finset.prod_eq_zero (i := (⟨1, h1len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
        simp only [hget1, hpv1, hConstF, h1, ite_true]
      · have h1f : x ⟨1, h1len⟩ = false := Bool.eq_false_of_ne_true h1
        by_cases h3 : x ⟨3, h3len⟩ = true
        · refine Finset.prod_eq_zero (i := (⟨3, h3len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
          simp only [hget3, hpv3, h1f, h2, h3, hOrFFT, ite_true]
        · have h3f : x ⟨3, h3len⟩ = false := Bool.eq_false_of_ne_true h3
          by_cases h4 : x ⟨4, h4len⟩ = true
          · refine Finset.prod_eq_zero (i := (⟨4, h4len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
            simp only [hget4, hpv4, h4, h3f, ite_true]
            cases hx0 : x ⟨0, h0len⟩
            · exact hAndFF _ _
            · exact hAndTF _ _
          · have h4f : x ⟨4, h4len⟩ = false := Bool.eq_false_of_ne_true h4
            by_cases h9 : x ⟨9, h9len⟩ = true
            · refine Finset.prod_eq_zero (i := (⟨9, h9len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
              simp only [hget9, hpv9, h9, h4f, ite_true]
              cases hx8 : x ⟨8, h8len⟩
              · exact hAndFF _ _
              · exact hAndFT _ _
            · have h9f : x ⟨9, h9len⟩ = false := Bool.eq_false_of_ne_true h9
              refine Finset.prod_eq_zero (i := (⟨12, h12len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
              simp only [hget12, hpv12, hx, h9f, ite_true]
              cases hx11 : x ⟨11, h11len⟩
              · exact hAndFF _ _
              · exact hAndFT _ _
    · have h7f : x ⟨7, h7len⟩ = false := Bool.eq_false_of_ne_true h7
      by_cases h10 : x ⟨10, h10len⟩ = true
      · refine Finset.prod_eq_zero (i := (⟨10, h10len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
        simp only [hget10, hpv10, hConstF, h10, ite_true]
      · have h10f : x ⟨10, h10len⟩ = false := Bool.eq_false_of_ne_true h10
        by_cases h11 : x ⟨11, h11len⟩ = true
        · refine Finset.prod_eq_zero (i := (⟨11, h11len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
          simp only [hget11, hpv11, h10f, h7f, h11, hOrTFF, ite_true]
        · have h11f : x ⟨11, h11len⟩ = false := Bool.eq_false_of_ne_true h11
          refine Finset.prod_eq_zero (i := (⟨12, h12len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
          simp only [hget12, hpv12, hx, h11f, ite_true]
          cases hx9 : x ⟨9, h9len⟩
          · exact hAndFF _ _
          · exact hAndTF _ _
  · have h2f : x ⟨2, h2len⟩ = false := Bool.eq_false_of_ne_true h2
    by_cases h7 : x ⟨7, h7len⟩ = true
    · by_cases h5 : x ⟨5, h5len⟩ = true
      · refine Finset.prod_eq_zero (i := (⟨5, h5len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
        simp only [hget5, hpv5, hConstF, h5, ite_true]
      · have h5f : x ⟨5, h5len⟩ = false := Bool.eq_false_of_ne_true h5
        by_cases h6 : x ⟨6, h6len⟩ = true
        · refine Finset.prod_eq_zero (i := (⟨6, h6len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
          simp only [hget6, hpv6, h5f, h2f, h6, hOrTFF, ite_true]
        · have h6f : x ⟨6, h6len⟩ = false := Bool.eq_false_of_ne_true h6
          by_cases h8 : x ⟨8, h8len⟩ = true
          · refine Finset.prod_eq_zero (i := (⟨8, h8len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
            simp only [hget8, hpv8, h6f, h7, h8, hOrFFT, ite_true]
          · have h8f : x ⟨8, h8len⟩ = false := Bool.eq_false_of_ne_true h8
            by_cases h9 : x ⟨9, h9len⟩ = true
            · refine Finset.prod_eq_zero (i := (⟨9, h9len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
              simp only [hget9, hpv9, h9, h8f, ite_true]
              cases hx4 : x ⟨4, h4len⟩
              · exact hAndFF _ _
              · exact hAndTF _ _
            · have h9f : x ⟨9, h9len⟩ = false := Bool.eq_false_of_ne_true h9
              refine Finset.prod_eq_zero (i := (⟨12, h12len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
              simp only [hget12, hpv12, hx, h9f, ite_true]
              cases hx11 : x ⟨11, h11len⟩
              · exact hAndFF _ _
              · exact hAndFT _ _
    · have h7f : x ⟨7, h7len⟩ = false := Bool.eq_false_of_ne_true h7
      by_cases h10 : x ⟨10, h10len⟩ = true
      · refine Finset.prod_eq_zero (i := (⟨10, h10len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
        simp only [hget10, hpv10, hConstF, h10, ite_true]
      · have h10f : x ⟨10, h10len⟩ = false := Bool.eq_false_of_ne_true h10
        by_cases h11 : x ⟨11, h11len⟩ = true
        · refine Finset.prod_eq_zero (i := (⟨11, h11len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
          simp only [hget11, hpv11, h10f, h7f, h11, hOrTFF, ite_true]
        · have h11f : x ⟨11, h11len⟩ = false := Bool.eq_false_of_ne_true h11
          refine Finset.prod_eq_zero (i := (⟨12, h12len⟩ : Fin [constNode true, constNode false, rootNode, orNode 1 2 false, andNode 0 3, constNode false, orNode 5 2 true, rootNode, orNode 6 7 false, andNode 4 8, constNode false, orNode 10 7 true, andNode 9 11].length)) (Finset.mem_univ _) ?_
          simp only [hget12, hpv12, hx, h11f, ite_true]
          cases hx9 : x ⟨9, h9len⟩
          · exact hAndFF _ _
          · exact hAndTF _ _

theorem noBN_wellFormed : noBN.WellFormed := by
  show RatNet.WellFormed [constNode false]
  unfold RatNet.WellFormed
  refine ⟨by decide, fun k hk => ?_⟩
  have hk0 : k = 0 := Nat.lt_one_iff.mp (by simpa using hk)
  subst hk0
  show RatNode.WellFormed 0 (constNode false)
  exact wf_constNode 0 false

theorem outProb_noBN : noBN.outProb = 0 := by
  show RatNet.outProb [constNode false] = 0
  have hwf : RatNet.WellFormed [constNode false] := noBN_wellFormed
  have h0len : (0 : ℕ) < [constNode false].length := by decide
  show probTrue (RatNet.toBayesNet [constNode false]) ⟨0, h0len⟩ = 0
  unfold probTrue
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [RatNet.joint_toBayesNet _ hwf]
  rw [Rat.cast_eq_zero]
  have hget0 : [constNode false].get ⟨0, h0len⟩ = constNode false := rfl
  have hpv0 : ∀ x : Fin [constNode false].length → Bool,
      RatNet.parentVals [constNode false] ⟨0, h0len⟩ x = [] := fun x => rfl
  have hprob : RatNode.prob (constNode false) [] = 0 := by simp [RatNode.prob, constNode]
  unfold RatNet.ratJoint
  refine Finset.prod_eq_zero (i := (⟨0, h0len⟩ : Fin [constNode false].length)) (Finset.mem_univ _) ?_
  simp only [hget0, hpv0, hprob, hx, ite_true]

/-- **Decision preservation on bit strings**: the bit-string map agrees with the SAT decider,
`satDec x = bnPosDec (reduceBN x)` for every `x`. No running-time bound is proved here. -/
theorem satDec_eq_bnPosDec_reduceBN (x : List Bool) : satDec x = bnPosDec (reduceBN x) := by
  classical
  simp only [satDec, bnPosDec, reduceBN]
  cases hdec : decodeCNF x with
  | none =>
      show (if x ∈ SATLang then true else false) = bnPosDec (encodeRatNet noBN)
      have hbn : bnPosDec (encodeRatNet noBN) = false := by
        unfold bnPosDec
        rw [decodeRatNet_encodeRatNet]
        show decide (noBN.WellFormed ∧ 0 < noBN.outProb) = false
        have hneg : ¬ (noBN.WellFormed ∧ 0 < noBN.outProb) := by
          rw [outProb_noBN]
          simp
        exact decide_eq_false hneg
      have hnotmem : x ∉ SATLang := by
        intro hmem
        simp only [SATLang, IsSATEncoded, Set.mem_ofPred_eq] at hmem
        obtain ⟨ψ, henc, -⟩ := hmem
        have hde := Cslib.CookLevin.decodeCNF_encodeCNF ψ
        rw [henc, hdec] at hde
        simp at hde
      rw [ite_eq_right hnotmem, hbn]
  | some φ =>
      show (if x ∈ SATLang then true else false) = bnPosDec (encodeRatNet (cooperNet φ))
      have hmem : x ∈ SATLang ↔ CNFSat φ := by
        constructor
        · intro hmem
          simp only [SATLang, IsSATEncoded, Set.mem_ofPred_eq] at hmem
          obtain ⟨ψ, henc, hsat⟩ := hmem
          have hde := Cslib.CookLevin.decodeCNF_encodeCNF ψ
          rw [henc, hdec] at hde
          simp at hde
          subst hde
          exact hsat
        · intro hsat
          simp only [SATLang, IsSATEncoded, Set.mem_ofPred_eq]
          exact ⟨φ, ((Cslib.CookLevin.decodeCNF_eq_some_iff x φ).mp hdec).symm, hsat⟩
      have hdecr : decodeRatNet (encodeRatNet (cooperNet φ)) = some (cooperNet φ) :=
        decodeRatNet_encodeRatNet _
      by_cases hsat : CNFSat φ
      · have hpos : 0 < (cooperNet φ).outProb := (cnfSat_iff_outProb_pos φ).mp hsat
        have hwf : (cooperNet φ).WellFormed := cooperNet_wellFormed φ
        rw [ite_eq_left (hmem.mpr hsat)]
        unfold bnPosDec
        rw [hdecr]
        show true = decide ((cooperNet φ).WellFormed ∧ 0 < (cooperNet φ).outProb)
        exact (decide_eq_true ⟨hwf, hpos⟩).symm
      · have hnpos : ¬ 0 < (cooperNet φ).outProb :=
          fun hp => hsat ((cnfSat_iff_outProb_pos φ).mpr hp)
        have hneg : ¬ ((cooperNet φ).WellFormed ∧ 0 < (cooperNet φ).outProb) :=
          fun h => hnpos h.2
        rw [ite_eq_right (fun h => hsat (hmem.mp h))]
        unfold bnPosDec
        rw [hdecr]
        show false = decide ((cooperNet φ).WellFormed ∧ 0 < (cooperNet φ).outProb)
        exact (decide_eq_false hneg).symm

/-- The empty formula gives a constant-true output. -/
theorem outProb_cooperNet_nil : (cooperNet []).outProb = 1 := by
  have hnet : cooperNet [] = [constNode true] := rfl
  have hwf : (cooperNet []).WellFormed := cooperNet_wellFormed []
  rw [hnet] at hwf ⊢
  show probTrue (RatNet.toBayesNet [constNode true]) ⟨0, zero_lt_one⟩ = 1
  unfold probTrue
  show (∑ x : Fin 1 → Bool with x ⟨0, zero_lt_one⟩ = true, (RatNet.toBayesNet [constNode true]).joint x) = 1
  have hfil : Finset.univ.filter (fun x : Fin 1 → Bool => x ⟨0, zero_lt_one⟩ = true)
      = {(fun _ => true)} := by decide
  rw [hfil]
  rw [Finset.sum_singleton]
  rw [RatNet.joint_toBayesNet _ hwf]
  have h0len : (0:ℕ) < [constNode true].length := by decide
  have hget0 : [constNode true].get ⟨0, h0len⟩ = constNode true := rfl
  have hpv0 : ∀ x : Fin [constNode true].length → Bool,
      RatNet.parentVals [constNode true] ⟨0, h0len⟩ x = [] := fun x => rfl
  have hprob : RatNode.prob (constNode true) [] = 1 := by simp [RatNode.prob, constNode]
  have hrat : RatNet.ratJoint [constNode true] (fun _ => true : Fin 1 → Bool) = 1 := by
    unfold RatNet.ratJoint
    apply Finset.prod_eq_one
    intro b _
    have hb0 : b.val = 0 := Nat.lt_one_iff.mp b.isLt
    have hb : b = ⟨0, h0len⟩ := by ext; exact hb0
    simp only [hb, hget0, hpv0, hprob, ite_true]
  rw [hrat]
  norm_num

/-- The empty clause gives a constant-false clause output. -/
theorem outProb_cooperNet_emptyClause : (cooperNet [[]]).outProb = 0 := by
  have hnet : cooperNet [[]] = [constNode true, constNode false, andNode 0 1] := rfl
  have hwf : (cooperNet [[]]).WellFormed := cooperNet_wellFormed _
  rw [hnet] at hwf ⊢
  have h0len : (0:ℕ) < [constNode true, constNode false, andNode 0 1].length := by decide
  have h1len : (1:ℕ) < [constNode true, constNode false, andNode 0 1].length := by decide
  have h2len : (2:ℕ) < [constNode true, constNode false, andNode 0 1].length := by decide
  show probTrue (RatNet.toBayesNet [constNode true, constNode false, andNode 0 1]) ⟨2, h2len⟩ = 0
  unfold probTrue
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [RatNet.joint_toBayesNet _ hwf]
  rw [Rat.cast_eq_zero]
  have hget1 : [constNode true, constNode false, andNode 0 1].get ⟨1, h1len⟩ = constNode false := rfl
  have hpv1 : ∀ x : Fin [constNode true, constNode false, andNode 0 1].length → Bool,
      RatNet.parentVals [constNode true, constNode false, andNode 0 1] ⟨1, h1len⟩ x = [] :=
    fun x => rfl
  have hprob1 : RatNode.prob (constNode false) [] = 0 := by simp [RatNode.prob, constNode]
  have hget2 : [constNode true, constNode false, andNode 0 1].get ⟨2, h2len⟩ = andNode 0 1 := rfl
  have hpv2 : ∀ x : Fin [constNode true, constNode false, andNode 0 1].length → Bool,
      RatNet.parentVals [constNode true, constNode false, andNode 0 1] ⟨2, h2len⟩ x =
        [x ⟨0, h0len⟩, x ⟨1, h1len⟩] := fun x => rfl
  have hprobFF : RatNode.prob (andNode 0 1) [false, false] = 0 := by simp [RatNode.prob, andNode, gateNode]
  have hprobTF : RatNode.prob (andNode 0 1) [true, false] = 0 := by simp [RatNode.prob, andNode, gateNode]
  unfold RatNet.ratJoint
  by_cases h1 : x ⟨1, h1len⟩ = true
  · refine Finset.prod_eq_zero (i := (⟨1, h1len⟩ : Fin [constNode true, constNode false, andNode 0 1].length)) (Finset.mem_univ _) ?_
    simp only [hget1, hpv1, hprob1, h1, ite_true]
  · have h1f : x ⟨1, h1len⟩ = false := Bool.eq_false_of_ne_true h1
    refine Finset.prod_eq_zero (i := (⟨2, h2len⟩ : Fin [constNode true, constNode false, andNode 0 1].length)) (Finset.mem_univ _) ?_
    simp only [hget2, hpv2, hx, ite_true, h1f]
    cases hx0 : x ⟨0, h0len⟩
    · exact hprobFF
    · exact hprobTF

end Cslib.Complexity.Cooper
