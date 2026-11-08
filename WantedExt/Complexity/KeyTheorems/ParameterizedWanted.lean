/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Parameterized complexity: FPT and W[1]-completeness of Clique

Source:
R. G. Downey and M. R. Fellows, Parameterized Complexity, Springer, 1999 (W[1]-completeness
of Clique); J. Flum and M. Grohe, Parameterized Complexity Theory, Springer, 2006.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.Partrec
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Parameterized complexity: FPT and W[1]-completeness of Clique

A *parameterized problem* is a decision problem with a natural-number parameter `k`. It
is *fixed-parameter tractable* (`FPT`) if it is decidable in time `f(k) · poly(n)` for some
computable `f`, formalized as ordinary polynomial time on the computably
unary-padded input `(x, 1 ^ (f k))` with `f` `Computable` (an unconstrained padding
function would be vacuous: for an undecidable predicate `U` on parameters,
`f k = 1` iff `U k` would make `U` FPT). This is equivalent to the `f(k) · poly(n)`
bound: the padded encoding has length `6 * n + 1 + 3 * f k`, so a padded machine
running in time `p(L)` runs in time at most `F(k) * (n + 1) ^ d` for a computable
`F` (absorbing the padding polynomial into the parameter factor), and conversely
an `f(k) · poly(n)` bound is polynomial in the padded length, since both `f k`
and `n` are at most the padded length. The bound is deliberately *not* stated
as `M.time.eval L ≤ (f k + 1) * (n + 1) ^ c`: `M.time` is a single global
polynomial in the total encoded length, so for `x = []` that would force
`p(f k) ≤ f k + 1` for unbounded `f k`, collapsing the model to globally
linear-time padded machines. An `FPT`-reduction is an `FPT`-time map with the
output parameter bounded by a function of `k` alone.

`W[t]` is the closure under `FPT` reductions of weighted circuit satisfiability for
circuits of weft at most `t` (and depth at most `d`, for some `d`). The output-parameter
bound `g` of an `FPT`-reduction is required to be `Computable`: without this, total
computable reductions whose finite per-parameter output ranges have no computable
uniform bound would enlarge the levels beyond the cited hierarchy: the circuit's
*weft* is the maximum number of large gates (AND/OR gates with fan-in `> 2`) on any
input-to-output path. In particular `W[1]` is the closure of weighted satisfiability for
weft-`1` circuits, and Clique is `W[1]`-complete. Bounded-width CNF does not define the
hierarchy (it collapses), so the circuit-weft definition is used. `FPT ⊆ W[1]`, and the
hierarchy is monotone; whether `FPT = W[1]` (equivalently, whether Clique is in `FPT`)
is open.
-/

/-- A parameterized problem: a decision problem with a natural-number parameter. -/
abbrev ParamProblem := List Bool → ℕ → Bool

/-- `FPT` time: decidable by a polynomial-time Turing machine on the computably
unary-padded input `(x, 1 ^ (f k))`, for a computable `f`. See the module
docstring for why this is equivalent to the `f(k) · poly(n)` bound and why the
bound is not stated as a constraint on the machine's global polynomial
`M.time`. -/
def FPTTime {β : Type} [MetaMathlibExt.BitstringEncoding β]
    (R : List Bool × ℕ → β) : Prop :=
  ∃ (f : ℕ → ℕ), Computable f ∧ ∃ (A : List Bool × List Bool → β),
    IsPolyTime A ∧
    ∀ (x : List Bool) (k : ℕ), R (x, k) = A (x, List.replicate (f k) true)

/-- Fixed-parameter tractability: decidable in `FPT` time. -/
def FPT (P : ParamProblem) : Prop :=
  ∃ D : List Bool × ℕ → Bool, FPTTime D ∧ ∀ x k, P x k = D (x, k)

/-- `FPT`-reduction: an `FPT`-time map with the output parameter bounded by a function
of `k` alone, preserving the answer. -/
def FPTReduces (P Q : ParamProblem) : Prop :=
  ∃ R : List Bool × ℕ → List Bool × ℕ, FPTTime R ∧ ∃ g : ℕ → ℕ, Computable g ∧
    ∀ x k, (R (x, k)).2 ≤ g k ∧ (P x k ↔ Q (R (x, k)).1 (R (x, k)).2)

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`. -/
abbrev WCGate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates, with input count `assign.length`.
The decode is semantics-preserving: out-of-range input indices read as `false`,
as in the previous local evaluator. -/
def wcCircuitEval (C : List WCGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- Predecessors of a gate: only NOT/AND/OR gates (`kind = 2, 3, 4`) have gate
references as payload. Variable (`kind = 0`) and constant (`kind = 1`) payloads are
a variable index and a constant value, not predecessor gates; folding over them would
attribute unrelated gates' weft/depth (e.g. an input gate `(0, [0])` inheriting gate
`0`'s depth). -/
def wcGatePreds : WCGate → List ℕ
  | (2, l) => l
  | (3, l) => l
  | (4, l) => l
  | _ => []

/-- Weft contribution of one gate given the wefts of earlier gates: `1` for a large
AND/OR gate (fan-in `> 2`), `0` otherwise, plus the maximum weft of its predecessor
gates. Input and constant gates have weft `0`. -/
def wcGateWeft (ws : List ℕ) : WCGate → ℕ
  | (k, l) => (if (k = 3 ∨ k = 4) ∧ 2 < l.length then 1 else 0) +
      (wcGatePreds (k, l)).foldr (fun a acc => max (ws.getD a 0) acc) 0

/-- Depth of one gate given the depths of earlier gates: input and constant gates
have base depth `0`; other gates have one plus the maximum predecessor depth. -/
def wcGateDepth (ds : List ℕ) : WCGate → ℕ
  | (0, _) => 0
  | (1, _) => 0
  | (_, l) => l.foldr (fun a acc => max (ds.getD a 0) acc) 0 + 1

/-- Wefts of all gates of an encoded circuit, in order. -/
def wcCircuitWefts (C : List WCGate) : List ℕ :=
  C.foldl (fun ws g => ws ++ [wcGateWeft ws g]) []

/-- Depths of all gates of an encoded circuit, in order. -/
def wcCircuitDepths (C : List WCGate) : List ℕ :=
  C.foldl (fun ds g => ds ++ [wcGateDepth ds g]) []

/-- Well-formedness: every non-input gate references only strictly earlier gates. -/
def WCWellFormed (C : List WCGate) : Prop :=
  ∀ j (h : j < C.length), ∀ a ∈ (C[j]'h).2,
    (C[j]'h).1 = 2 ∨ (C[j]'h).1 = 3 ∨ (C[j]'h).1 = 4 → a < j

open Classical in
/-- Weighted circuit satisfiability for circuits of weft at most `t` and depth at most
`d`: the circuit (on `n` inputs) has a satisfying assignment of Hamming weight exactly `k`. -/
noncomputable def WeightedCircuitSat (t d : ℕ) : ParamProblem := fun x k =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List WCGate) x with
  | some (n, C) => decide (
      WCWellFormed C ∧ (∀ w ∈ wcCircuitWefts C, w ≤ t) ∧
      (∀ dep ∈ wcCircuitDepths C, dep ≤ d) ∧
      ∃ assign : List Bool, assign.length = n ∧
        (assign.filter id).length = k ∧
        (wcCircuitEval C assign).getLast? = some true)
  | none => false

open Classical in
/-- The `k`-Clique problem: the graph (on `n` vertices, with the given directed edge
list) has a clique of size `k`. -/
noncomputable def CliqueParam : ParamProblem := fun x k =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List (ℕ × ℕ)) x with
  | some (n, edges) => decide (
      ∃ S : List ℕ, S.Nodup ∧ S.length = k ∧ (∀ v ∈ S, v < n) ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (u, v) ∈ edges ∨ (v, u) ∈ edges)
  | none => false

/-- `W[t]`: the closure under `FPT` reductions of weighted circuit satisfiability for
circuits of weft at most `t` (and depth at most `d`, for some `d`). -/
def WLevel (t : ℕ) : Set ParamProblem :=
  {P | ∃ d, FPTReduces P (WeightedCircuitSat t d)}

/-- **Parameterized complexity: FPT and W[1]-completeness of Clique.** Source: R. G.
Downey and M. R. Fellows, Parameterized Complexity, Springer, 1999 (W[1]-completeness of
Clique); J. Flum and M. Grohe, Parameterized Complexity Theory, Springer, 2006. -/
public theorem_wanted parameterized_clique_w1_complete :
    (CliqueParam ∈ WLevel 1 ∧ ∀ P ∈ WLevel 1, FPTReduces P CliqueParam) ∧
    (∀ P : ParamProblem, FPT P → P ∈ WLevel 1) ∧
    ∀ t : ℕ, WLevel t ⊆ WLevel (t + 1)

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
