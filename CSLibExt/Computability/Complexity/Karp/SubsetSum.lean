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

/-- **Bit-string encoding of SUBSET-SUM instances.** The instance with numbers $a_1, \dots, a_r$
and target $t$ is encoded as the block of $t$ followed by the blocks of $a_1, \dots, a_r$ in
order. The block of a number is its binary expansion, least significant bit first and empty for
the number $0$, made self-delimiting by writing each bit $c$ as $1c$ and appending a final $0$. -/
def encodeSS (as : List ℕ) (t : ℕ) : List Bool :=
  delimit (encodeNat t) ++ as.flatMap fun a => delimit (encodeNat a)

open Classical in
/-- **The SUBSET-SUM problem.** The decision problem that accepts a bit string $x$ exactly when
$x$ encodes a SUBSET-SUM instance with a list of numbers $a_1, \dots, a_r$ and a target $t$ such
that some sublist of $a_1, \dots, a_r$ sums to $t$. A sublist keeps some of the entries in their
order, so a number may be used as often as it occurs in the list. -/
noncomputable def subsetSumDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ as t, encodeSS as t = x ∧ ∃ l : List ℕ, l.Sublist as ∧ l.sum = t)

/-- **Place value of a vertex pair in the SUBSET-SUM reduction.** The place value of pair number
$q$ is $4^q$. The numbers of the reduction from VERTEX-COVER to SUBSET-SUM are written in base
$4$, with the digit at position $q$ belonging to pair $q$. -/
def pairDigit (q : ℕ) : ℕ := 4 ^ q

/-- **Pairs touching a vertex.** Let $p_0, \dots, p_{m-1}$ be the vertex pairs $(i, j)$ with
$i < j < n$ in encoding order (rows $i$ ascending, within a row $j$ descending). For a list $b$
of pair bits, a vertex $v$ and an index $q$, the test is true when bit $b_q$ is set and $v$ is one
of the two entries of $p_q$. An index past the end of $b$ counts as an unset bit, and for
$q \ge m$ the pair $p_q$ is taken to be $(0, 0)$. -/
def touches (n : ℕ) (bits : List Bool) (v q : ℕ) : Bool :=
  bits.getD q false && (((pairs n).getD q (0, 0)).1 == v || ((pairs n).getD q (0, 0)).2 == v)

/-- **Vertex numbers of the SUBSET-SUM reduction.** Let $p_0, \dots, p_{m-1}$ be the vertex pairs
$(i, j)$ with $i < j < n$ in encoding order (rows $i$ ascending, within a row $j$ descending),
and let $b$ be a list of pair bits. The number of a vertex $v$ is $4^m + \sum 4^q$, the sum over
the indices $q < m$ such that bit $b_q$ is set and $v$ is an entry of $p_q$, where an index past
the end of $b$ counts as unset. In base $4$ it has digit $1$ at position $m$ and at each such
$q$, and $0$ elsewhere. -/
def vtxNum (n : ℕ) (bits : List Bool) (v : ℕ) : ℕ :=
  4 ^ (pairs n).length +
    (((List.range (pairs n).length).filter fun q => touches n bits v q).map pairDigit).sum

/-- **Edge numbers of the SUBSET-SUM reduction.** Given a list $b$ of pair bits and a pair index
$q$, the number of pair $q$ is $4^q$ if bit $b_q$ is set and $0$ otherwise; an index past the end
of $b$ counts as an unset bit. -/
def edgeNum (bits : List Bool) (q : ℕ) : ℕ := if bits.getD q false then pairDigit q else 0

/-- **Target of the SUBSET-SUM reduction.** Let $m = n(n-1)/2$ be the number of vertex pairs
$(i, j)$ with $i < j < n$, and let $b$ be a list of pair bits. For $k \in \mathbb{N}$ the target
is $k \cdot 4^m + \sum 2 \cdot 4^q$, the sum over the indices $q < m$ such that bit $b_q$ is set
(an index past the end of $b$ counts as unset). So the quotient of the target by $4^m$ is $k$, and
its base-$4$ digit at position $q < m$ is $2$ when $b_q$ is set and $0$ otherwise. -/
def ssTarget (k n : ℕ) (bits : List Bool) : ℕ :=
  k * 4 ^ (pairs n).length +
    (((List.range (pairs n).length).filter fun q => bits.getD q false).map
      fun q => 2 * pairDigit q).sum

/-- **Numbers of the SUBSET-SUM reduction.** For $n$ vertices and a list $b$ of pair bits, with
$m = n(n-1)/2$ vertex pairs, the numbers of the instance are the vertex numbers of
$v = 0, \dots, n - 1$, in this order, followed by the edge numbers of the pairs
$q = 0, \dots, m - 1$, in this order. -/
def ssNums (n : ℕ) (bits : List Bool) : List ℕ :=
  (List.range n).map (vtxNum n bits) ++ (List.range (pairs n).length).map (edgeNum bits)

/-- **Fixed no-instance of SUBSET-SUM.** The encoding of the SUBSET-SUM instance with no numbers
and target $1$. It is a no-instance, because the only sublist of the empty list sums to $0$. -/
def noSS : List Bool := encodeSS [] 1

/-- **Reduction from VERTEX-COVER to SUBSET-SUM.** The map on bit strings reads $x$ as $k$ ones, a
zero, $n$ ones, a zero and a remaining list $b$ of pair bits. If this parse succeeds and $b$ has
exactly $n(n-1)/2$ bits, one per vertex pair, then $x$ is sent to the encoding of the SUBSET-SUM
instance whose numbers are the numbers of the reduction for $n$ and $b$ and whose target is the
target for $k$, $n$ and $b$. Otherwise $x$ is sent to the fixed no-instance with no numbers and
target $1$. -/
def reduceSS (x : List Bool) : List Bool :=
  match decodeKG x with
  | some (k, n, bits) =>
      if bits.length = (pairs n).length then encodeSS (ssNums n bits) (ssTarget k n bits)
      else noSS
  | none => noSS

end Cslib.Complexity.Karp
