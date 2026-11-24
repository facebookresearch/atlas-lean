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

/-- **Parameterized problems.** A parameterized problem is a function that assigns a boolean
answer to every pair of a bitstring (a finite list of booleans) $x$ and a natural-number
parameter $k$. -/
abbrev ParamProblem := List Bool → ℕ → Bool

/-- **FPT time.** Let $\beta$ be a type with a canonical bitstring encoding. A function $R$
from pairs $(x, k)$ of a bitstring $x$ and a natural number $k$ to $\beta$ is computable in FPT
time when there are a computable function $f : \mathbb{N} \to \mathbb{N}$ and a
polynomial-time computable function $A$ from pairs of bitstrings to $\beta$ such that
$R(x, k) = A(x, 1^{f(k)})$ for every bitstring $x$ and every $k \in \mathbb{N}$, where
$1^{f(k)}$ is the list of $f(k)$ booleans all equal to true.

Padding the input with $f(k)$ entries in this way is equivalent to a running time of
$F(k) \cdot p(n)$ for a computable $F$ and a polynomial $p$, where $n$ is the length of $x$;
the padding function must be computable, since otherwise every predicate on the parameter would
be fixed-parameter tractable. -/
def FPTTime {β : Type} [MetaMathlibExt.BitstringEncoding β]
    (R : List Bool × ℕ → β) : Prop :=
  ∃ (f : ℕ → ℕ), Computable f ∧ ∃ (A : List Bool × List Bool → β),
    IsPolyTime A ∧
    ∀ (x : List Bool) (k : ℕ), R (x, k) = A (x, List.replicate (f k) true)

/-- **Fixed-parameter tractable problems.** A parameterized problem $P$ is fixed-parameter
tractable when there is a function $D$, from pairs $(x, k)$ of a bitstring $x$ and a natural
number $k$ to booleans, that is computable in FPT time and satisfies $P(x, k) = D(x, k)$ for
every bitstring $x$ and every $k \in \mathbb{N}$. -/
def FPT (P : ParamProblem) : Prop :=
  ∃ D : List Bool × ℕ → Bool, FPTTime D ∧ ∀ x k, P x k = D (x, k)

/-- **FPT-reductions.** A parameterized problem $P$ FPT-reduces to a parameterized problem $Q$
when there are a map $R$, sending each pair $(x, k)$ of a bitstring $x$ and a natural number
$k$ to such a pair $R(x, k) = (x', k')$, that is computable in FPT time, and a computable
function $g : \mathbb{N} \to \mathbb{N}$, such that for every bitstring $x$ and every
$k \in \mathbb{N}$, $k' \le g(k)$ and $P(x, k)$ is true if and only if $Q(x', k')$ is true. -/
def FPTReduces (P Q : ParamProblem) : Prop :=
  ∃ R : List Bool × ℕ → List Bool × ℕ, FPTTime R ∧ ∃ g : ℕ → ℕ, Computable g ∧
    ∀ x k, (R (x, k)).2 ≤ g k ∧ (P x k ↔ Q (R (x, k)).1 (R (x, k)).2)

/-- **Encoded gates for weighted circuit satisfiability.** An encoded gate is a pair $(k, r)$ of a
natural number $k$, its kind, and a list $r$ of natural numbers, its references.

Gates are read as in the shared (kind, references) encoding of flat Boolean circuits on $n$
inputs: $(0, [i])$ is the input variable $x_i$ when $i < n$, $(1, [b])$ is the constant that is
true exactly when $b = 1$, $(2, [a])$ is the negation of gate $a$, and $(3, r)$ and $(4, r)$ are
the AND and the OR of the gates listed in $r$; every other pair, including $(0, [i])$ with
$i \ge n$ and $(2, r)$ with $r$ not of length one, evaluates to false. -/
abbrev WCGate := ℕ × List ℕ

/-- **Gate values of an encoded circuit.** Let $C = (g_0, \dots, g_{m-1})$ be a list of gates
encoded as (kind, references) pairs and let $a = (a_0, \dots, a_{n-1})$ be a list of booleans.
The gate values of $C$ under $a$ are the values $(v_0, \dots, v_{m-1})$ of the flat Boolean
circuit on $n$ inputs obtained by decoding each $g_j$ to a gate on $n$ inputs, evaluated at the
assignment that gives input $i$ the value $a_i$.

Decoding turns an input gate with index $i \ge n$ into the constant false, so such inputs read
as false. -/
def wcCircuitEval (C : List WCGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Predecessors of an encoded gate.** The predecessor list of an encoded gate $(k, r)$ is $r$
when $k$ is $2$, $3$ or $4$ (a NOT, AND or OR gate), and the empty list for every other kind.

Variable (kind $0$) and constant (kind $1$) payloads are a variable index and a constant value,
not predecessor gates; folding over them would attribute unrelated gates' weft or depth (for
example, an input gate $(0, [0])$ inheriting gate $0$'s depth). -/
def wcGatePreds : WCGate → List ℕ
  | (2, l) => l
  | (3, l) => l
  | (4, l) => l
  | _ => []

/-- **Weft of an encoded gate.** Given a list $w$ of wefts of earlier gates, where $w_a$ reads as
$0$ when $a$ is not a position of $w$, the weft of an encoded gate $(k, r)$ is $1$ if it is a
large AND or OR gate ($k \in \{3, 4\}$ and $r$ has more than $2$ entries) and $0$ otherwise,
plus the maximum of $w_a$ over the entries $a$ of its predecessor list (the maximum over an
empty list is $0$). In particular, input and constant gates have weft $0$. -/
def wcGateWeft (ws : List ℕ) : WCGate → ℕ
  | (k, l) => (if (k = 3 ∨ k = 4) ∧ 2 < l.length then 1 else 0) +
      (wcGatePreds (k, l)).foldr (fun a acc => max (ws.getD a 0) acc) 0

/-- **Depth of one encoded gate.** Let $d = (d_0, d_1, \dots)$ be a list of natural numbers
(the depths of earlier gates), where $d_a$ is read as $0$ when $a$ is out of range, and let
$(c, r)$ be a gate encoded as a (kind, references) pair. Its depth is $0$ if $c = 0$ or $c = 1$
(an input or constant gate), and otherwise one plus the maximum of $d_a$ over the entries $a$ of
$r$, the maximum over no entries being $0$. -/
def wcGateDepth (ds : List ℕ) : WCGate → ℕ
  | (0, _) => 0
  | (1, _) => 0
  | (_, l) => l.foldr (fun a acc => max (ds.getD a 0) acc) 0 + 1

/-- **Wefts of the gates of an encoded circuit.** For a list
$C = (g_0, \dots, g_{m-1})$ of gates encoded as (kind, references) pairs, the list of wefts is
$(w_0, \dots, w_{m-1})$, where $w_j$ is computed from $w_0, \dots, w_{j-1}$ as follows. Write
$g_j = (c, r)$. The weft $w_j$ is $1$ if $c = 3$ or $c = 4$ (an AND or OR gate) and $r$ has
more than $2$ entries, and $0$ otherwise, plus, when $c = 2$, $c = 3$ or $c = 4$, the maximum of
$w_a$ over the entries $a$ of $r$, where $w_a$ is read as $0$ for $a \ge j$ and the maximum
over no entries is $0$. -/
def wcCircuitWefts (C : List WCGate) : List ℕ :=
  C.foldl (fun ws g => ws ++ [wcGateWeft ws g]) []

/-- **Depths of the gates of an encoded circuit.** For a list
$C = (g_0, \dots, g_{m-1})$ of gates encoded as (kind, references) pairs, the list of depths is
$(d_0, \dots, d_{m-1})$, where $d_j$ is computed from $d_0, \dots, d_{j-1}$ as follows. Write
$g_j = (c, r)$. If $c = 0$ or $c = 1$ (an input or constant gate), then $d_j = 0$; otherwise
$d_j$ is one plus the maximum of $d_a$ over the entries $a$ of $r$, where $d_a$ is read as $0$
for $a \ge j$ and the maximum over no entries is $0$. -/
def wcCircuitDepths (C : List WCGate) : List ℕ :=
  C.foldl (fun ds g => ds ++ [wcGateDepth ds g]) []

/-- **Well-formed encoded circuits.** A list $C = (g_0, \dots, g_{m-1})$ of encoded gates is
well-formed when every NOT, AND or OR gate references only strictly earlier gates: for every
$j < m$ such that $g_j = (k, r)$ has kind $k \in \{2, 3, 4\}$, every entry $a$ of $r$ satisfies
$a < j$. -/
def WCWellFormed (C : List WCGate) : Prop :=
  ∀ j (h : j < C.length), ∀ a ∈ (C[j]'h).2,
    (C[j]'h).1 = 2 ∨ (C[j]'h).1 = 3 ∨ (C[j]'h).1 = 4 → a < j

open Classical in
/-- **Weighted circuit satisfiability with bounded weft and depth.** For natural numbers $t$ and
$d$, weighted circuit satisfiability is the parameterized problem that, on a bitstring $x$ and a
parameter $k$, answers true exactly when $x$ decodes to a pair $(n, C)$ of a natural number $n$
and a list $C$ of encoded gates such that: every NOT, AND or OR gate of $C$ references only
strictly earlier gates; every gate of $C$ has weft at most $t$ and depth at most $d$; and there
is an assignment of $n$ Boolean values to the inputs, exactly $k$ of them true, under which $C$
has a last gate and that gate evaluates to true. -/
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
/-- **Parameterized Clique.** The parameterized $k$-Clique problem answers a bitstring $x$ and
a parameter $k \in \mathbb{N}$ as follows. If $x$ decodes, under the canonical bitstring
encoding, to a pair $(n, E)$ of a natural number $n$ and a list $E$ of pairs of natural numbers,
the answer is true exactly when there is a list of $k$ distinct natural numbers, each less than
$n$, such that for any two distinct entries $u$ and $v$ of the list, $(u, v) \in E$ or
$(v, u) \in E$. If $x$ decodes to no such pair, the answer is false.

That is, on a well-formed input the answer says whether the graph on the vertices
$0, \dots, n - 1$ whose edges are the pairs in $E$, with direction ignored, has a clique of
size $k$. -/
noncomputable def CliqueParam : ParamProblem := fun x k =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List (ℕ × ℕ)) x with
  | some (n, edges) => decide (
      ∃ S : List ℕ, S.Nodup ∧ S.length = k ∧ (∀ v ∈ S, v < n) ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (u, v) ∈ edges ∨ (v, u) ∈ edges)
  | none => false

/-- **The level $\mathrm{W}[t]$ of the W-hierarchy.** For a natural number $t$, $\mathrm{W}[t]$ is
the set of parameterized problems $P$ for which there is a natural number $d$ such that $P$
FPT-reduces to weighted circuit satisfiability for circuits of weft at most $t$ and depth at
most $d$. -/
def WLevel (t : ℕ) : Set ParamProblem :=
  {P | ∃ d, FPTReduces P (WeightedCircuitSat t d)}

/-- **Parameterized complexity: FPT and W[1]-completeness of Clique.** Write $W[t]$ for the
$t$-th level of the W-hierarchy. The parameterized $k$-Clique problem lies in $W[1]$, and every
parameterized problem in $W[1]$ has an FPT-reduction to it. Every fixed-parameter tractable
parameterized problem lies in $W[1]$. For every $t \in \mathbb{N}$, $W[t] \subseteq W[t + 1]$.

Source: R. G.
Downey and M. R. Fellows, Parameterized Complexity, Springer, 1999 (W[1]-completeness of
Clique); J. Flum and M. Grohe, Parameterized Complexity Theory, Springer, 2006. -/
public theorem_wanted parameterized_clique_w1_complete :
    (CliqueParam ∈ WLevel 1 ∧ ∀ P ∈ WLevel 1, FPTReduces P CliqueParam) ∧
    (∀ P : ParamProblem, FPT P → P ∈ WLevel 1) ∧
    ∀ t : ℕ, WLevel t ⊆ WLevel (t + 1)

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
