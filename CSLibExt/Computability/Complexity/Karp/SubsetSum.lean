/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Clique

/-!
# Karp reductions on the canonical classes: SUBSET-SUM

Specification module for VERTEX-COVER ≤ SUBSET-SUM on `MetaMathlibExt.ComplexityTheory`. It
fixes the instance encoding, the language and the pure reduction; the correctness proof, the
machines and NP membership are separate components. Once those are in place, the chain
SAT ≤ CLIQUE ≤ INDEPENDENT-SET ≤ VERTEX-COVER (`Karp.Clique`) extends to SUBSET-SUM.

* Instances: a target `t` and numbers `as`, each in binary (`Computability.encodeNat`, least
  significant bit first) and framed by `MetaMathlibExt.BitstringEncoding.delimit`
  (`encodeSS as t`). Binary matters: with unary numbers the problem is in P.
* `subsetSumDec`: some sublist of `as` sums to `t`.
* `ssNums`, `ssTarget`: for a valid VERTEX-COVER instance `(k, G)` with `m = (pairs n).length`
  pairs, numbers in base 4 with one digit per vertex pair (`pairDigit`): vertex `v` gives
  `4 ^ m + Σ {4 ^ q | pair q is an edge containing v}` (`vtxNum`), pair `q` gives `4 ^ q` if it is
  an edge and `0` otherwise (`edgeNum`), and the target is
  `k * 4 ^ m + Σ {2 * 4 ^ q | pair q is an edge}` (`ssTarget`). Digit sums stay below 4, so a
  subset hits the target exactly when its vertex numbers form a cover of `k` vertices (each edge
  digit gets 1 or 2 from chosen endpoints, topped up to 2 by its edge number).
  `reduceSS` is the reduction on bit strings; inputs that are not valid instances go to `noSS`
  (no numbers, target 1).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Computability MetaMathlibExt.BitstringEncoding

/-- A SUBSET-SUM instance: the target, then the numbers, each in binary and delimited. -/
def encodeSS (as : List ℕ) (t : ℕ) : List Bool :=
  delimit (encodeNat t) ++ as.flatMap fun a => delimit (encodeNat a)

open Classical in
/-- SUBSET-SUM: some sublist of the numbers sums to the target. -/
noncomputable def subsetSumDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ as t, encodeSS as t = x ∧ ∃ l : List ℕ, l.Sublist as ∧ l.sum = t)

/-- The base-4 digit of pair number `q` in a number of the reduction. -/
def pairDigit (q : ℕ) : ℕ := 4 ^ q

/-- Whether pair number `q` of `pairs n` is an edge containing vertex `v`. -/
def touches (n : ℕ) (bits : List Bool) (v q : ℕ) : Bool :=
  bits.getD q false && (((pairs n).getD q (0, 0)).1 == v || ((pairs n).getD q (0, 0)).2 == v)

/-- The number of vertex `v`: a top digit `1`, and digit `q` set for the edges at `v`. -/
def vtxNum (n : ℕ) (bits : List Bool) (v : ℕ) : ℕ :=
  4 ^ (pairs n).length +
    (((List.range (pairs n).length).filter fun q => touches n bits v q).map pairDigit).sum

/-- The number of pair `q`: its digit if it is an edge, else `0`. -/
def edgeNum (bits : List Bool) (q : ℕ) : ℕ := if bits.getD q false then pairDigit q else 0

/-- The target: `k` on top, digit `2` on every edge. -/
def ssTarget (k n : ℕ) (bits : List Bool) : ℕ :=
  k * 4 ^ (pairs n).length +
    (((List.range (pairs n).length).filter fun q => bits.getD q false).map
      fun q => 2 * pairDigit q).sum

/-- The numbers of the instance: vertices first, then pairs. -/
def ssNums (n : ℕ) (bits : List Bool) : List ℕ :=
  (List.range n).map (vtxNum n bits) ++ (List.range (pairs n).length).map (edgeNum bits)

/-- A fixed no-instance: no numbers, target `1`. -/
def noSS : List Bool := encodeSS [] 1

/-- VERTEX-COVER ≤ SUBSET-SUM on bit strings. -/
def reduceSS (x : List Bool) : List Bool :=
  match decodeKG x with
  | some (k, n, bits) =>
      if bits.length = (pairs n).length then encodeSS (ssNums n bits) (ssTarget k n bits)
      else noSS
  | none => noSS

end Cslib.Complexity.Karp
