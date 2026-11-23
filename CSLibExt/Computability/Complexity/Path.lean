/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color

/-!
# PATH: reachability in a directed graph (spec)

Specification module for PATH ∈ P (Sipser, Theorem 7.14) on `MetaMathlibExt.ComplexityTheory`.
It fixes the instance encoding, the language and the marking algorithm as a pure function; the
correctness proof (`pathDec = pathCheck`), the marking machine and the assembly `pathDec ∈ P`
(through `Host.isPolyTime_decider`) are separate components.

* Instances: source `s` and target `t` in unary, then the digraph as the edge list
  `Karp.encodeE n es` of `Karp.Color` (`encodeP s t n es`); `decodeP` reads one back with
  `Karp.decodeE`.
* `arc n es u v`: the pair `(u, v)` is listed and both ends are below `n` (other pairs are ignored).
* `pathDec`: `s < n`, `t < n`, and `t` is reachable from `s` along arcs
  (`Relation.ReflTransGen`, so `s = t` is reachable).
* The algorithm (Sipser's marking): `initMarks n s` marks `s` among `0, …, n - 1`; `markPass n es`
  scans the edge list once in order, marking `v` for each arc `(u, v)` with `u` marked (a mark set
  during the pass is seen later in the same pass); `reachMarks n s es` runs `n` passes;
  `pathCheck x` parses `x`, checks `s, t < n` and reads the mark of `t`.
-/

@[expose] public section

namespace Cslib.Complexity.Path

open Cslib.CookLevin

/-- **Encoding of a PATH instance.** Writing $1$ for true and $0$ for false, the instance with
source $s$, target $t$ and the digraph given by $n$ and the edge list $E$ is encoded as $s$ ones,
a zero, $t$ ones, a zero, then $n$ ones and a zero, followed, for each pair $(u, v)$ of $E$ in
order, by $u$ ones, a zero, $v$ ones and a zero. -/
def encodeP (s t n : ℕ) (es : List (ℕ × ℕ)) : List Bool :=
  List.replicate s true ++ false :: (List.replicate t true ++ false :: Karp.encodeE n es)

/-- **Decoding a PATH instance.** Writing $1$ for true and $0$ for false, a bit string $x$ is parsed
by reading a unary number $s$ (a run of ones ended by a zero), then a unary number $t$ from the
rest, then a graph from what remains: a unary number $n$ followed by pairs $(u, v)$ of unary
numbers until the input ends. The result is $(s, t, n, E)$, with $E$ the list of these pairs in
order; there is no result unless the input ends right after $n$ or right after a complete pair. -/
def decodeP (x : List Bool) : Option (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  match readUnaryLength x with
  | none => none
  | some (s, r) =>
      match readUnaryLength r with
      | none => none
      | some (t, r') => (Karp.decodeE r').map fun p => (s, t, p.1, p.2)

/-- **Arcs of the PATH digraph.** For $n \in \mathbb{N}$ and a list $E$ of pairs of natural
numbers, there is an arc from $u$ to $v$ when the pair $(u, v)$ occurs in $E$, $u < n$ and $v < n$;
listed pairs with an end at least $n$ give no arc. -/
def arc (n : ℕ) (es : List (ℕ × ℕ)) (u v : ℕ) : Prop := (u, v) ∈ es ∧ u < n ∧ v < n

open Classical in
/-- **The PATH problem.** PATH is the decision problem that accepts a bit string $x$ exactly when
$x$ is the encoding of some instance $(s, t, n, E)$ with $s < n$, $t < n$ and a sequence
$s = v_0, v_1, \dots, v_k = t$ with $k \ge 0$ such that each $(v_i, v_{i+1})$ is an arc, that is,
a pair listed in $E$ with both ends below $n$. -/
noncomputable def pathDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ s t n es, encodeP s t n es = x ∧ s < n ∧ t < n ∧
    Relation.ReflTransGen (arc n es) s t)

/-- **Initial marks.** For $n, s \in \mathbb{N}$, the initial marks are the list of $n$ booleans
whose entry at position $i < n$ is true exactly when $i = s$; all entries are false when
$s \ge n$. -/
def initMarks (n s : ℕ) : List Bool := (List.range n).map (· == s)

/-- **One marking pass.** Given $n \in \mathbb{N}$, an edge list $E$ and a list $m$ of booleans
(the marks), the pass scans the pairs $(u, v)$ of $E$ in order and, whenever $u < n$, $v < n$
and position $u$ of the current marks is true, sets position $v$ to true. A position beyond the
end of the list counts as false and setting it changes nothing. Marks set earlier in the pass
are seen by later pairs. -/
def markPass (n : ℕ) : List (ℕ × ℕ) → List Bool → List Bool
  | [], m => m
  | (u, v) :: es, m =>
      markPass n es (if u < n ∧ v < n ∧ m.getD u false = true then m.set v true else m)

/-- **Reach marks.** For $n, s \in \mathbb{N}$ and an edge list $E$, the reach marks are obtained
from the initial marks of $s$ among $0, \dots, n - 1$ by applying the marking pass over $E$ with
bound $n$ exactly $n$ times. -/
def reachMarks (n s : ℕ) (es : List (ℕ × ℕ)) : List Bool := (markPass n es)^[n] (initMarks n s)

/-- **The marking algorithm for PATH.** On a bit string $x$, the check decodes $x$ as a PATH
instance. If decoding fails it returns false; if it yields $(s, t, n, E)$ it returns true exactly
when $s < n$, $t < n$ and position $t$ of the marks after $n$ marking passes from $s$ over $E$
is true. -/
def pathCheck (x : List Bool) : Bool :=
  match decodeP x with
  | some (s, t, n, es) => decide (s < n) && decide (t < n) && (reachMarks n s es).getD t false
  | none => false

end Cslib.Complexity.Path
