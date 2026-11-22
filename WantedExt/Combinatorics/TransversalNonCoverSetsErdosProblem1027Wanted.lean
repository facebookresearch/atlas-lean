/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Many sets meeting but not containing members of a family (Erdős Problem 1027)

Erdős Problem 1027: let `c > 0` and `n` be large depending on `c`, and let `𝓕` be a family of at
most `c 2ⁿ` sets of size `n` with union `X`. Must there be `≫_c 2^{|X|}` sets `B ⊆ X` which meet
every set in `𝓕` but contain none of them?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.TransversalNonCoverSetsErdosProblem1027Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1027, https://www.erdosproblems.com/1027 (status
PROVED). UnsolvedMath record UM-30007134 (`EP-1027`), dataset ulamai/UnsolvedMath v1.8.0.

The sets are finite sets of natural numbers, which loses nothing for finite families. `≫_c 2^{|X|}`
is `≥ δ 2^{|X|}` with `δ > 0` depending only on `c`. Compared with the formal-conjectures statement
`ErdosProblems/1027.lean` (equivalent; no code imported).
-/

/-- **Sets meeting but not containing the members of a family.** For a finite family $F$ of finite
sets of natural numbers with union $X$, this is the finite set of all $B \subseteq X$ that meet
every member of $F$ and contain none of them. -/
def transversalNonCoverSets (F : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (F.biUnion id).powerset.filter fun B => ∀ A ∈ F, (A ∩ B).Nonempty ∧ ¬ A ⊆ B

/-- **Erdős Problem 1027 (sets meeting but not containing members of a family).** For every real
$c > 0$ there is a real $\delta > 0$ such that, for all sufficiently large $n$, every finite family
$F$ of finite sets of natural numbers, each of size $n$, with $|F| \le c \cdot 2^n$ and with union
$X$, has at least $\delta \cdot 2^{|X|}$ subsets $B \subseteq X$ that meet every member of $F$ and
contain none of them. -/
def manyTransversalNonCoverSets : Prop :=
  ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset ℕ),
    (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
      δ * 2 ^ (F.biUnion id).card ≤ (transversalNonCoverSets F).card

/--
**Erdős Problem 1027 holds.** For every real $c > 0$ there is a real $\delta > 0$ such that, for
all sufficiently large $n$, every finite family $F$ of finite sets of natural numbers, each of
size $n$, with $|F| \le c \cdot 2^n$ and with union $X$, has at least $\delta \cdot 2^{|X|}$
subsets $B \subseteq X$ that meet every member of $F$ and contain none of them.

Source: T.
F. Bloom, Erdős Problems, Problem #1027, https://www.erdosproblems.com/1027 (status PROVED);
resolution: K. Chan, proof in the erdosproblems.com/1027 comments; formal proof plby/lean-proofs,
src/latest/ErdosProblems/Erdos1027.lean, erdosproblems.com/1027: 'This is true, and a proof was
given in the comment section by Koishi Chan',
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1027.lean#L209.
-/
public theorem_wanted manyTransversalNonCoverSets_holds : manyTransversalNonCoverSets

end MathlibExt.Combinatorics.TransversalNonCoverSetsErdosProblem1027Wanted
