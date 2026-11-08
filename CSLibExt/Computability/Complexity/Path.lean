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

/-- A PATH instance: `s` and `t` in unary, then the digraph `Karp.encodeE n es`. -/
def encodeP (s t n : ℕ) (es : List (ℕ × ℕ)) : List Bool :=
  List.replicate s true ++ false :: (List.replicate t true ++ false :: Karp.encodeE n es)

/-- Parse a PATH instance. -/
def decodeP (x : List Bool) : Option (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  match readUnaryLength x with
  | none => none
  | some (s, r) =>
      match readUnaryLength r with
      | none => none
      | some (t, r') => (Karp.decodeE r').map fun p => (s, t, p.1, p.2)

/-- The arcs of the digraph on `0, …, n - 1`: listed pairs with both ends below `n`. -/
def arc (n : ℕ) (es : List (ℕ × ℕ)) (u v : ℕ) : Prop := (u, v) ∈ es ∧ u < n ∧ v < n

open Classical in
/-- PATH: `t` is reachable from `s` in the digraph, both below `n`. -/
noncomputable def pathDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ s t n es, encodeP s t n es = x ∧ s < n ∧ t < n ∧
    Relation.ReflTransGen (arc n es) s t)

/-- The initial marks: `s` only, among `0, …, n - 1`. -/
def initMarks (n s : ℕ) : List Bool := (List.range n).map (· == s)

/-- One pass over the edge list, in order: an arc `(u, v)` with `u` marked marks `v`. -/
def markPass (n : ℕ) : List (ℕ × ℕ) → List Bool → List Bool
  | [], m => m
  | (u, v) :: es, m =>
      markPass n es (if u < n ∧ v < n ∧ m.getD u false = true then m.set v true else m)

/-- The marks after `n` passes. -/
def reachMarks (n s : ℕ) (es : List (ℕ × ℕ)) : List Bool := (markPass n es)^[n] (initMarks n s)

/-- The marking algorithm on bit strings: parse, check `s, t < n`, read the mark of `t`. -/
def pathCheck (x : List Bool) : Bool :=
  match decodeP x with
  | some (s, t, n, es) => decide (s < n) && decide (t < n) && (reachMarks n s es).getD t false
  | none => false

end Cslib.Complexity.Path
