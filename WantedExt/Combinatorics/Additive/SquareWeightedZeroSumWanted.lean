/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Squarefree.Basic
public import MathlibExt.Combinatorics.Additive.WeightedDavenport

namespace MetaMathlibExt

@[expose] public section

open Pointwise

/-! This file formalizes statements, not proofs, from Paul and Paul. -/

/-- **Units modulo n.** For a natural number $n$, $U(n)$ is the set of units of the ring
$\mathbb{Z}/n\mathbb{Z}$ of integers modulo $n$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def unitSet (n : ℕ) : Set (ZMod n) := {x | IsUnit x}

/-- **Squares of units modulo n.** For a natural number $n$, $U(n)^2$ is the set of elements of
$\mathbb{Z}/n\mathbb{Z}$ of the form $u^2$ with $u$ a unit of $\mathbb{Z}/n\mathbb{Z}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def unitSquareSet (n : ℕ) : Set (ZMod n) := {x | ∃ u, IsUnit u ∧ x = u ^ 2}

/-- **Nonzero squares modulo $n$.** For a natural number $n$, $S(n)$ is the set of elements $x$
of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ with $x \neq 0$ and $x = y^2$ for some
$y \in \mathbb{Z}_n$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def squareSet (n : ℕ) : Set (ZMod n) := {x | x ≠ 0 ∧ ∃ y, x = y ^ 2}

/-- **Weighted zero-sum sequences.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and let
$S = (x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$. Then $S$ is an $A$-weighted
zero-sum sequence if there are weights $a_1, \dots, a_k \in A$ with
$a_1 x_1 + a_2 x_2 + \dots + a_k x_k = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasWeightedZeroSum {n k : ℕ} (A : Set (ZMod n)) (S : Fin k → ZMod n) : Prop :=
  ∃ a : Fin k → ZMod n, (∀ i, a i ∈ A) ∧ ∑ i, a i * S i = 0

/-- **Weighted zero-sum subsequences.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and let
$S = (x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$. Then $S$ has an $A$-weighted
zero-sum subsequence if there are a nonempty set $J \subseteq \{1, \dots, k\}$ of indices and
weights $a_i \in A$ for $i \in J$ with $\sum_{i \in J} a_i x_i = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasWeightedZeroSumSubseq {n k : ℕ} (A : Set (ZMod n))
    (S : Fin k → ZMod n) : Prop :=
  ∃ J : Finset (Fin k), J.Nonempty ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ J, a i ∈ A) ∧ ∑ i ∈ J, a i * S i = 0

/-- **Consecutive weighted zero-sum subsequences.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and let
$S = (x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$. Then $S$ has an $A$-weighted
zero-sum consecutive subsequence if there are indices $1 \le l \le h \le k$ and weights
$a_l, \dots, a_h \in A$ with $\sum_{i=l}^{h} a_i x_i = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasConsecutiveWeightedZeroSumSubseq {n k : ℕ} (A : Set (ZMod n))
    (S : Fin k → ZMod n) : Prop :=
  ∃ J : Finset (Fin k), J.Nonempty ∧
    (∃ lo hi : ℕ, J = Finset.univ.filter fun i => lo ≤ i.1 ∧ i.1 ≤ hi) ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ J, a i ∈ A) ∧ ∑ i ∈ J, a i * S i = 0

/-- **Representatives of a set of residues.** Let $n$ be a natural number and $A$ a subset of
$\mathbb{Z}_n$. The representatives of $A$ form the finite set of natural numbers $a$ with
$0 \le a < n$ whose residue modulo $n$ lies in $A$.

A natural number $a$ acts on $\mathbb{Z}_n$ by $x \mapsto a x$. For $n \ge 1$ every residue has
exactly one representative below $n$, so the weighted Davenport constant of $\mathbb{Z}_n$ with
the representatives of $A$ as weights is the paper's $D_A$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public noncomputable def zmodWeightReps {n : ℕ} (A : Set (ZMod n)) : Finset ℕ :=
  open Classical in (Finset.range n).filter fun a => (a : ZMod n) ∈ A

/-- **Membership in the weight representatives.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$.
A natural number $a$ lies in the set of weight representatives of $A$ if and only if $a < n$ and
the residue of $a$ modulo $n$ lies in $A$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public theorem mem_zmodWeightReps {n : ℕ} {A : Set (ZMod n)} {a : ℕ} :
    a ∈ zmodWeightReps A ↔ a < n ∧ (a : ZMod n) ∈ A := by
  classical
  simp [zmodWeightReps]

/-- **Lengths forcing a consecutive weighted zero sum.** Let $n$ be a natural number and $A$ a
subset of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$. This is the set of positive integers $k$ such
that every sequence $(x_1, \dots, x_k)$ of elements of $\mathbb{Z}_n$ has a nonempty block of
consecutive terms $x_i, \dots, x_j$ with weights $a_i, \dots, a_j \in A$ such that
$a_i x_i + \dots + a_j x_j = 0$. Its least element, or $0$ when it is empty, is the $A$-weighted
consecutive constant $C_A$ of $\mathbb{Z}_n$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def weightedConsecutiveDefiningSet (n : ℕ) (A : Set (ZMod n)) : Set ℕ :=
  {k | 0 < k ∧ ∀ S : Fin k → ZMod n, HasConsecutiveWeightedZeroSumSubseq A S}

/-- **Weighted consecutive zero-sum constant.** Let $n$ be a natural number and $A$ a subset of
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$. The $A$-weighted consecutive constant $C_A$ of
$\mathbb{Z}_n$ is the least positive integer $k$ such that every sequence $(x_1, \dots, x_k)$ of
elements of $\mathbb{Z}_n$ has a nonempty block of consecutive terms $x_i, \dots, x_j$ with
weights $a_i, \dots, a_j \in A$ such that $a_i x_i + \dots + a_j x_j = 0$; it is $0$ when no
such $k$ exists.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public noncomputable def weightedConsecutiveConstant (n : ℕ) (A : Set (ZMod n)) : ℕ :=
  sInf (weightedConsecutiveDefiningSet n A)

/-- **Weighted zero-sum subsequences are monotone in the weight set.** Let
$A \subseteq B \subseteq \mathbb{Z}/n\mathbb{Z}$ and let $S$ be a finite sequence in
$\mathbb{Z}/n\mathbb{Z}$. If $S$ has an $A$-weighted zero-sum subsequence, then $S$ has a
$B$-weighted zero-sum subsequence.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public theorem HasWeightedZeroSumSubseq.mono {n k : ℕ} {A B : Set (ZMod n)}
    {S : Fin k → ZMod n} (hAB : A ⊆ B) (h : HasWeightedZeroSumSubseq A S) :
    HasWeightedZeroSumSubseq B S := by
  rcases h with ⟨J, hJ, a, ha, hsum⟩
  exact ⟨J, hJ, a, fun i hi => hAB (ha i hi), hsum⟩

/-- **The one-term zero sequence has a square-weighted zero sum.** Let $n \ge 2$ and let $S(n)$ be
the set of nonzero squares in $\mathbb{Z}_n$. The sequence over $\mathbb{Z}_n$ whose only term is
$0$ has an $S(n)$-weighted zero sum: there is a weight $a \in S(n)$ with $a \cdot 0 = 0$.

The weight $a = 1$ works; it lies in $S(n)$ because $1 \ne 0$ in $\mathbb{Z}_n$ when $n \ge 2$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public theorem zeroSingleton_hasWeightedZeroSum (n : ℕ) (hn : 2 ≤ n) :
    HasWeightedZeroSum (squareSet n) (fun _ : Fin 1 => 0) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro i
    refine ⟨?_, 1, by simp⟩
    intro h
    have h' : ((1 : ℕ) : ZMod n) = 0 := by simpa only [Nat.cast_one] using h
    have hd : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp h'
    have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hd
    omega
  · simp

/-- **Decomposition of the nonzero squares modulo a prime power.** Let $p$ be a prime, let
$r \ge 1$, and let $l = \lfloor (r - 1)/2 \rfloor$. Write $S(p^r)$ for the set of nonzero squares
in $\mathbb{Z}_{p^r}$, $U(p^r)^2$ for the set of squares of units in $\mathbb{Z}_{p^r}$, and
$p^{2k} U(p^r)^2 = \{p^{2k} x : x \in U(p^r)^2\}$. Then
$$S(p^r) = \bigcup_{k=0}^{l} p^{2k} U(p^r)^2,$$
and the sets $p^{2k} U(p^r)^2$ for $k = 0, \dots, l$ are pairwise disjoint.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 4. -/
public theorem_wanted squareSet_primePower_decomposition (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    let l := (r - 1) / 2
    let pieces : Fin (l + 1) → Set (ZMod (p ^ r)) := fun k =>
      ((p : ZMod (p ^ r)) ^ (2 * (k : ℕ))) • unitSquareSet (p ^ r)
    squareSet (p ^ r) = ⋃ k, pieces k ∧ Set.PairwiseDisjoint Set.univ pieces

/-- **Scaled unit squares modulo a prime power.** Let $p$ be a prime and $r, k$ natural numbers
with $k = 0$ or $2k < r$, and write $U(m)^2$ for the set of squares of units of
$\mathbb{Z}/m\mathbb{Z}$. Then the set $p^{2k} U(p^r)^2 = \{p^{2k} x : x \in U(p^r)^2\}$ in
$\mathbb{Z}/p^r\mathbb{Z}$ has the same number of elements as $U(p^{r-2k})^2$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 5. -/
public theorem_wanted ncard_scale_unitSquares_primePower (p r k : ℕ) (hp : p.Prime)
    (hk : k ≤ (r - 1) / 2) :
    (((p : ZMod (p ^ r)) ^ (2 * k)) • unitSquareSet (p ^ r)).ncard =
      (unitSquareSet (p ^ (r - 2 * k))).ncard

/-- **Number of nonzero squares modulo a prime power.** Let $p$ be a prime and $r \ge 1$, and write
$S(m)$ for the set of nonzero squares and $U(m)^2$ for the set of squares of units in
$\mathbb{Z}/m\mathbb{Z}$. If $r$ is even, then
$|S(p^r)| = \sum_{k=0}^{r/2-1} |U(p^{r-2k})^2|$, and if $r$ is odd, then
$|S(p^r)| = \sum_{k=0}^{(r-1)/2} |U(p^{r-2k})^2|$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 6. -/
public theorem_wanted ncard_squareSet_primePower (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    (Even r → (squareSet (p ^ r)).ncard =
      ∑ k ∈ Finset.range (r / 2), (unitSquareSet (p ^ (r - 2 * k))).ncard) ∧
    (Odd r → (squareSet (p ^ r)).ncard =
      ∑ k ∈ Finset.range ((r + 1) / 2), (unitSquareSet (p ^ (r - 2 * k))).ncard)

/-- **Square-weighted zero sums lift from a prime-power component.** Let $n \ge 2$, let $p$ be a
prime dividing $n$, and let $r$ be the exponent of $p$ in $n$. Write $S(m)$ for the set of
nonzero squares in $\mathbb{Z}_m$. Let $x_1, \dots, x_k$ be a sequence in $\mathbb{Z}_n$ whose
reduction $\bar x_1, \dots, \bar x_k$ modulo $p^r$ has an $S(p^r)$-weighted zero sum, that is,
there are $b_1, \dots, b_k \in S(p^r)$ with $\sum_i b_i \bar x_i = 0$. Then there are
$a_1, \dots, a_k \in S(n)$ with $\sum_i a_i x_i = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 7. -/
public theorem_wanted squareWeightedZeroSum_of_primePower_reduction (n p r k : ℕ)
    (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) (hval : n.factorization p = r)
    (S : Fin k → ZMod n)
    (hS : HasWeightedZeroSum (squareSet (p ^ r))
      (fun i => (ZMod.cast (S i) : ZMod (p ^ r)))) :
    HasWeightedZeroSum (squareSet n) S

/-- **Prime-power bound for the square-weighted consecutive constant.** Let $n \ge 2$, let $p$ be a
prime dividing $n$ and let $r = v_p(n)$ be the exponent of $p$ in $n$. For a natural number $m$,
write $S(m)$ for the set of nonzero squares in $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$ and
$C_{S(m)}$ for the $S(m)$-weighted consecutive constant of $\mathbb{Z}_m$. Then
$C_{S(n)} \le C_{S(p^r)}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 8. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_le_primePower (n p r : ℕ)
    (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) (hval : n.factorization p = r) :
    weightedConsecutiveConstant n (squareSet n) ≤
      weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r))

/-- **Square-weighted zero sums lift from $p$ to odd powers $p^r$.** Let $p \ge 2$ be a natural
number and $r$ an odd natural number. Write $S(m)$ for the set of nonzero squares in
$\mathbb{Z}_m$. Let $x_1, \dots, x_k$ be a sequence in $\mathbb{Z}_{p^r}$ whose reduction
$\bar x_1, \dots, \bar x_k$ modulo $p$ has an $S(p)$-weighted zero sum, that is, there are
$b_1, \dots, b_k \in S(p)$ with $\sum_i b_i \bar x_i = 0$. Then there are
$a_1, \dots, a_k \in S(p^r)$ with $\sum_i a_i x_i = 0$.

This is at least as strong as the reading with weights in $U(p)^2$, the squares of units of
$\mathbb{Z}_p$, because $U(p)^2 \subseteq S(p)$; the two agree for prime $p$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 9. -/
public theorem_wanted squareWeightedZeroSum_of_reduction_oddPower (p r k : ℕ)
    (hp : 2 ≤ p) (hr : Odd r) (T : Fin k → ZMod (p ^ r))
    (hT : HasWeightedZeroSum (squareSet p) (fun i => (ZMod.cast (T i) : ZMod p))) :
    HasWeightedZeroSum (squareSet (p ^ r)) T

/-- **Square-weighted zero-sum free unit triples modulo even powers of two.** Let $r$ be a nonzero
even natural number, and let $x_1, x_2, x_3$ be units of $\mathbb{Z}_{2^r}$ that are each
congruent to $1$ modulo $4$. Write $S(2^r)$ for the set of nonzero squares in $\mathbb{Z}_{2^r}$.
Then $(x_1, x_2, x_3)$ has no $S(2^r)$-weighted zero-sum subsequence: there are no non-empty set
$J$ of indices and weights $a_j \in S(2^r)$ for $j \in J$ with $\sum_{j \in J} a_j x_j = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 10. -/
public theorem_wanted no_squareWeightedSubseq_three_units_twoPower (r : ℕ)
    (hr0 : r ≠ 0) (hrEven : Even r) (S : Fin 3 → ZMod (2 ^ r))
    (hunit : ∀ i, IsUnit (S i))
    (hred : ∀ i, (ZMod.cast (S i) : ZMod 4) = 1) :
    ¬HasWeightedZeroSumSubseq (squareSet (2 ^ r)) S

/-- **Three-term sequences without square-weighted zero-sum subsequences.** Let $p$ be a prime and
$r$ a nonzero even natural number, and write $S(m)$ for the set of nonzero squares in
$\mathbb{Z}/m\mathbb{Z}$. Let $z_1, z_2$ be units of $\mathbb{Z}/p^2\mathbb{Z}$ whose reduction
$(z_1 \bmod p, z_2 \bmod p)$ is not an $S(p)$-weighted zero-sum sequence. Let $T = (x_1, x_2, y_1)$
be a sequence in $\mathbb{Z}/p^r\mathbb{Z}$ whose reduction modulo $p^2$ is $(z_1, z_2, p)$. Then
$T$ has no $S(p^r)$-weighted zero-sum subsequence.

The paper states the lemma for sequences of units modulo $p^r$, which no $y_1$ reducing to the
nonunit $p$ can be; following the paper's proof and its application in Theorem 12, the sequence is
taken in $\mathbb{Z}/p^r\mathbb{Z}$. Then $x_1, x_2$ are automatically units, since $z_1, z_2$ are.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 11. -/
public theorem_wanted no_squareWeightedSubseq_pair_and_prime_of_reduction (p r : ℕ)
    (hp : p.Prime) (hr0 : r ≠ 0) (hrEven : Even r) (z : Fin 2 → ZMod (p ^ 2))
    (hz : ∀ i, IsUnit (z i))
    (hzred : ¬HasWeightedZeroSum (squareSet p) (fun i => (ZMod.cast (z i) : ZMod p)))
    (S : Fin 3 → ZMod (p ^ r))
    (hS : ∀ i, (ZMod.cast (S i) : ZMod (p ^ 2)) = ![z 0, z 1, (p : ZMod (p ^ 2))] i) :
    ¬HasWeightedZeroSumSubseq (squareSet (p ^ r)) S

/-- **Square-weighted Davenport constant of even squares is at least four.** Let $n \ge 2$ be an
even perfect square. Write $S(n)$ for the set of nonzero squares in
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ and $D_{S(n)} \in \mathbb{N} \cup \{\infty\}$ for the
weighted Davenport constant of $\mathbb{Z}_n$ with weight set $S(n)$, a weight acting by
multiplication. Then $D_{S(n)} \ge 4$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 12. -/
public theorem_wanted weightedDavenport_squareSet_evenSquare_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (heven : Even n) (hsquare : IsSquare n) :
    4 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- **Lifting weighted zero sums from p² to an even power of p.** Let $p \ge 2$, $r \ne 0$
and $k$ be natural numbers with $r$ even, and let $t_1, \dots, t_k$ be elements of
$\mathbb{Z}/p^r\mathbb{Z}$, with reductions $\bar t_1, \dots, \bar t_k$ modulo $p^2$. Write
$U(p^2)^2$ for the set of squares of units of $\mathbb{Z}/p^2\mathbb{Z}$ and $S(p^r)$ for the
set of nonzero squares of $\mathbb{Z}/p^r\mathbb{Z}$. If there are
$a_1, \dots, a_k \in U(p^2)^2$ with $a_1 \bar t_1 + \dots + a_k \bar t_k = 0$ in
$\mathbb{Z}/p^2\mathbb{Z}$, then there are $b_1, \dots, b_k \in S(p^r)$ with
$b_1 t_1 + \dots + b_k t_k = 0$ in $\mathbb{Z}/p^r\mathbb{Z}$.

The paper states the lemma for $p > 0$; the stronger hypothesis $p \ge 2$ is deliberate.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 13. -/
public theorem_wanted squareWeightedZeroSum_of_reduction_square (p r k : ℕ)
    (hp : 2 ≤ p) (hr0 : r ≠ 0) (hrEven : Even r)
    (T : Fin k → ZMod (p ^ r))
    (hT : HasWeightedZeroSum (unitSquareSet (p ^ 2))
      (fun i => (ZMod.cast (T i) : ZMod (p ^ 2)))) :
    HasWeightedZeroSum (squareSet (p ^ r)) T

/-- **Square-weighted constants modulo $p^r$, for $p \ge 2$ and nonzero even $r$, are at most
unit-square constants modulo $p^2$.** Let $p \ge 2$ be a natural number and let $r$ be a nonzero
even natural number. Write $S(p^r)$ for the set of nonzero squares in $\mathbb{Z}_{p^r}$ and
$U(p^2)^2$ for the set of squares of units in $\mathbb{Z}_{p^2}$. For a weight set
$A \subseteq \mathbb{Z}_m$, write $D_A(\mathbb{Z}_m)$ for the $A$-weighted Davenport constant of
$\mathbb{Z}_m$, where $A$ acts through its representatives in $\{0, \dots, m - 1\}$ and the value
lies in $\mathbb{N} \cup \{\infty\}$, and write $C_A$ for the least positive length $k$ such that
every sequence of length $k$ in $\mathbb{Z}_m$ has a non-empty consecutive $A$-weighted zero-sum
subsequence, or $0$ if there is no such length. Then
$D_{S(p^r)}(\mathbb{Z}_{p^r}) \le D_{U(p^2)^2}(\mathbb{Z}_{p^2})$ and
$C_{S(p^r)} \le C_{U(p^2)^2}$, the first constant in each inequality taken in $\mathbb{Z}_{p^r}$
and the second in $\mathbb{Z}_{p^2}$.

The paper says $p$ positive; $p = 1$ is excluded (the paper assumes throughout that the modulus is
at least $2$), since then $S(1)$ is empty, so $D_{S(1)}(\mathbb{Z}_1) = \infty$, while
$D_{U(1)^2}(\mathbb{Z}_1) = 1$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 14. -/
public theorem_wanted squareSet_constants_le_unitSquares_modSquare (p r : ℕ)
    (hp : 2 ≤ p) (hr0 : r ≠ 0) (hrEven : Even r) :
    weightedDavenport (zmodWeightReps (squareSet (p ^ r))) (ZMod (p ^ r)) ≤
        weightedDavenport (zmodWeightReps (unitSquareSet (p ^ 2))) (ZMod (p ^ 2)) ∧
      weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r)) ≤
        weightedConsecutiveConstant (p ^ 2) (unitSquareSet (p ^ 2))

/-- **Consecutive square-weighted constant of an even power of two is at most four.** For every
even natural number $r \ne 0$, the consecutive $S(2^r)$-weighted zero-sum constant satisfies
$C_{S(2^r)} \le 4$, where $S(2^r)$ is the set of nonzero squares of $\mathbb{Z}/2^r\mathbb{Z}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 15. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_twoPower_le_four (r : ℕ)
    (hr0 : r ≠ 0) (hrEven : Even r) :
    weightedConsecutiveConstant (2 ^ r) (squareSet (2 ^ r)) ≤ 4

/-- **Square-weighted constants of even squares.** Let $n \ge 2$ be an even perfect square and let
$S(n)$ be the set of nonzero squares in $\mathbb{Z}_n$. Then the $S(n)$-weighted Davenport
constant of $\mathbb{Z}_n$, with weights the representatives in $\{0, \dots, n - 1\}$ of the
elements of $S(n)$, equals $4$. Moreover, some positive length $k$ forces every sequence of
length $k$ in $\mathbb{Z}_n$ to have a non-empty consecutive $S(n)$-weighted zero-sum
subsequence, and the least such length, the consecutive constant $C_{S(n)}$, equals $4$.

Since the infimum of the empty set of natural numbers is $0$, the existence clause makes the
equality $C_{S(n)} = 4$ nonvacuous.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 16. -/
public theorem_wanted squareSet_constants_evenSquare (n : ℕ) (hn : 2 ≤ n)
    (heven : Even n) (hsquare : IsSquare n) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 4 ∧
      weightedConsecutiveConstant n (squareSet n) = 4

/-- **Two units without square-weighted zero sums modulo any prime divisor.** Let $n \ge 2$ be
odd, and write $S(m)$ for the set of nonzero squares in $\mathbb{Z}/m\mathbb{Z}$. Then there are
units $u, v$ of $\mathbb{Z}/n\mathbb{Z}$ such that for every prime $p$ dividing $n$, the sequence
$(u \bmod p, v \bmod p)$ in $\mathbb{Z}/p\mathbb{Z}$ has no $S(p)$-weighted zero-sum subsequence.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Proposition 17. -/
public theorem_wanted exists_pair_units_avoiding_prime_squareWeights (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) :
    ∃ u v : ZMod n, IsUnit u ∧ IsUnit v ∧
      ∀ p : ℕ, p.Prime → p ∣ n →
        ¬HasWeightedZeroSumSubseq (squareSet p)
          (fun i : Fin 2 => (ZMod.cast (![u, v] i) : ZMod p))

/-- **Square-weighted zero-sum free unit pairs lift to odd prime powers.** Let $p$ be an odd
prime, let $r \ge 1$, and let $x_1, x_2$ be units of $\mathbb{Z}_{p^r}$. Write $S(m)$ for the set
of nonzero squares in $\mathbb{Z}_m$, and say that a sequence $(y_i)$ in $\mathbb{Z}_m$ has an
$A$-weighted zero-sum subsequence when there are a non-empty set $J$ of indices and weights
$a_j \in A$ for $j \in J$ with $\sum_{j \in J} a_j y_j = 0$. If the reduction
$(\bar x_1, \bar x_2)$ of $(x_1, x_2)$ modulo $p$ has no $S(p)$-weighted zero-sum subsequence,
then $(x_1, x_2)$ has no $S(p^r)$-weighted zero-sum subsequence.

The paper states the hypothesis with $Q_p$, the set of nonzero quadratic residues modulo $p$,
which equals $S(p)$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 18. -/
public theorem_wanted no_squareWeightedSubseq_pair_of_reduction (p r : ℕ)
    (hp : p.Prime) (hpOdd : Odd p) (hr : 0 < r) (S : Fin 2 → ZMod (p ^ r))
    (hunit : ∀ i, IsUnit (S i))
    (hred : ¬HasWeightedZeroSumSubseq (squareSet p)
      (fun i => (ZMod.cast (S i) : ZMod p))) :
    ¬HasWeightedZeroSumSubseq (squareSet (p ^ r)) S

/-- **The square-weighted Davenport constant of an odd modulus is at least three.** Let $n \ge 2$
be odd, let $S(n)$ be the set of nonzero squares in $\mathbb{Z}_n$, and let $A$ be the set of
integers $a$ with $0 \le a < n$ whose residue modulo $n$ lies in $S(n)$. Then the $A$-weighted
Davenport constant $D_{S(n)}$ of $\mathbb{Z}_n$ is at least $3$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 19. -/
public theorem_wanted weightedDavenport_squareSet_odd_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) :
    3 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- **Square-weighted Davenport constant for an even 2-adic valuation of at least two.** Let
$n \ge 2$ be a natural number whose exponent $v_2(n)$ of $2$ is even and at least $2$. Write
$S(n)$ for the set of nonzero squares in $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ and
$D_{S(n)} \in \mathbb{N} \cup \{\infty\}$ for the weighted Davenport constant of $\mathbb{Z}_n$
with weight set $S(n)$, a weight acting by multiplication. Then $D_{S(n)} \ge 3$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 20. -/
public theorem_wanted weightedDavenport_squareSet_even_twoValuation_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (hvalEven : Even (n.factorization 2))
    (hval : 2 ≤ n.factorization 2) :
    3 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- **Consecutive square-weighted constant of an odd prime to an odd power is at most three.**
For every odd prime $p$ and every odd natural number $r$, the consecutive $S(p^r)$-weighted
zero-sum constant satisfies $C_{S(p^r)} \le 3$, where $S(p^r)$ is the set of nonzero squares of
$\mathbb{Z}/p^r\mathbb{Z}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 21. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_oddPrimePower_le_three
    (p r : ℕ) (hp : p.Prime) (hpOdd : Odd p) (hrOdd : Odd r) :
    weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r)) ≤ 3

/-- **Square-weighted constants of nonsquares with even $2$-adic valuation.** Let $n \ge 2$ be a
natural number that is not a perfect square and whose $2$-adic valuation $v_2(n)$ is even
(possibly zero), and let $S(n)$ be the set of nonzero squares in $\mathbb{Z}_n$. Then the
$S(n)$-weighted Davenport constant of $\mathbb{Z}_n$, with weights the representatives in
$\{0, \dots, n - 1\}$ of the elements of $S(n)$, equals $3$. Moreover, some positive length $k$
forces every sequence of length $k$ in $\mathbb{Z}_n$ to have a non-empty consecutive
$S(n)$-weighted zero-sum subsequence, and the least such length, the consecutive constant
$C_{S(n)}$, equals $3$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 22. -/
public theorem_wanted squareSet_constants_nonsquare_even_twoValuation (n : ℕ)
    (hn : 2 ≤ n) (hnotSquare : ¬IsSquare n)
    (hvalEven : Even (n.factorization 2)) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 3 ∧
      weightedConsecutiveConstant n (squareSet n) = 3

/-- **Consecutive square-weighted constant of an odd power of two is at most two.** For every
odd natural number $r$, the consecutive $S(2^r)$-weighted zero-sum constant satisfies
$C_{S(2^r)} \le 2$, where $S(2^r)$ is the set of nonzero squares of $\mathbb{Z}/2^r\mathbb{Z}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 23. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_odd_twoPower_le_two (r : ℕ)
    (hrOdd : Odd r) :
    weightedConsecutiveConstant (2 ^ r) (squareSet (2 ^ r)) ≤ 2

/-- **Square-weighted constants of numbers with odd $2$-adic valuation.** Let $n$ be a positive
even natural number whose $2$-adic valuation $v_2(n)$ is odd, and let $S(n)$ be the set of
nonzero squares in $\mathbb{Z}_n$. Then the $S(n)$-weighted Davenport constant of
$\mathbb{Z}_n$, with weights the representatives in $\{0, \dots, n - 1\}$ of the elements of
$S(n)$, equals $2$. Moreover, some positive length $k$ forces every sequence of length $k$ in
$\mathbb{Z}_n$ to have a non-empty consecutive $S(n)$-weighted zero-sum subsequence, and the
least such length, the consecutive constant $C_{S(n)}$, equals $2$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 24. -/
public theorem_wanted squareSet_constants_odd_twoValuation (n : ℕ) (hn : 0 < n)
    (hnEven : Even n) (hvalOdd : Odd (n.factorization 2)) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 2 ∧
      weightedConsecutiveConstant n (squareSet n) = 2

/-- **Four-term sequences without square-weighted zero-sum subsequences.** Let $p$ be a prime and
$r$ a nonzero even natural number, and write $S(m)$ for the set of nonzero squares in
$\mathbb{Z}/m\mathbb{Z}$. Let $w_1, w_2, u$ be units of $\mathbb{Z}/p^r\mathbb{Z}$ such that the
reduction $(w_1 \bmod p, w_2 \bmod p)$ has no $S(p)$-weighted zero-sum subsequence. Then the
sequence $(u w_1, u w_2, p w_1, p w_2)$ in $\mathbb{Z}/p^r\mathbb{Z}$ has no $S(p^r)$-weighted
zero-sum subsequence.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 25. -/
public theorem_wanted no_squareWeightedSubseq_fourTerm_pattern (p r : ℕ)
    (hp : p.Prime) (hr0 : r ≠ 0) (hrEven : Even r)
    (w₁ w₂ u : ZMod (p ^ r)) (hw₁ : IsUnit w₁) (hw₂ : IsUnit w₂)
    (hu : IsUnit u)
    (hred : ¬HasWeightedZeroSumSubseq (squareSet p)
      (fun i : Fin 2 => (ZMod.cast (![w₁, w₂] i) : ZMod p))) :
    ¬HasWeightedZeroSumSubseq (squareSet (p ^ r))
      ![u * w₁, u * w₂, (p : ZMod (p ^ r)) * w₁, (p : ZMod (p ^ r)) * w₂]

/-- **The square-weighted Davenport constant of an odd square is at least five.** Let $n \ge 2$
be an odd perfect square, let $S(n)$ be the set of nonzero squares in $\mathbb{Z}_n$, and let $A$
be the set of integers $a$ with $0 \le a < n$ whose residue modulo $n$ lies in $S(n)$. Then the
$A$-weighted Davenport constant $D_{S(n)}$ of $\mathbb{Z}_n$ is at least $5$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 26. -/
public theorem_wanted weightedDavenport_squareSet_oddSquare_lowerBound (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) (hsquare : IsSquare n) :
    5 ≤ weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n)

/-- **Three unit-square cosets sum to every residue modulo an odd prime power.** Let $p$ be an
odd prime, let $r \ge 1$, and let $A = U(p^r)^2$ be the set of squares of units of
$\mathbb{Z}/p^r\mathbb{Z}$; for $y \in \mathbb{Z}/p^r\mathbb{Z}$ write $Ay = \{ay : a \in A\}$.
For all units $y_1, y_2, y_3$ of $\mathbb{Z}/p^r\mathbb{Z}$, every element of
$\mathbb{Z}/p^r\mathbb{Z}$ is a sum $x_1 + x_2 + x_3$ with $x_1 \in Ay_1$,
$x_2 \in Ay_2 \cup \{0\}$ and $x_3 \in Ay_3 \cup \{0\}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 27. -/
public theorem_wanted three_unitSquare_cosets_cover (p r : ℕ) (hp : p.Prime)
    (hpOdd : Odd p) (hr : 0 < r) (y₁ y₂ y₃ : ZMod (p ^ r))
    (hy₁ : IsUnit y₁) (hy₂ : IsUnit y₂) (hy₃ : IsUnit y₃) :
    unitSquareSet (p ^ r) * {y₁} +
      (unitSquareSet (p ^ r) * {y₂} ∪ {0} + (unitSquareSet (p ^ r) * {y₃} ∪ {0})) =
        Set.univ

/-- **The square-weighted Davenport constant of an even power of an odd prime is at most five.**
Let $p$ be an odd prime, let $r$ be a nonzero even natural number, let $S(p^r)$ be the set of
nonzero squares in $\mathbb{Z}_{p^r}$, and let $A$ be the set of integers $a$ with $0 \le a < p^r$
whose residue modulo $p^r$ lies in $S(p^r)$. Then the $A$-weighted Davenport constant
$D_{S(p^r)}$ of $\mathbb{Z}_{p^r}$ is at most $5$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 28. -/
public theorem_wanted weightedDavenport_squareSet_oddPrimePower_le_five (p r : ℕ)
    (hp : p.Prime) (hpOdd : Odd p) (hr0 : r ≠ 0) (hrEven : Even r) :
    weightedDavenport (zmodWeightReps (squareSet (p ^ r))) (ZMod (p ^ r)) ≤ 5

/-- **The square-weighted Davenport constant of an odd square is five.** Let $n \ge 2$ be an odd
perfect square, let $S(n)$ be the set of nonzero squares in $\mathbb{Z}_n$, and let $A$ be the set
of integers $a$ with $0 \le a < n$ whose residue modulo $n$ lies in $S(n)$. Then the $A$-weighted
Davenport constant $D_{S(n)}$ of $\mathbb{Z}_n$ equals $5$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 29. -/
public theorem_wanted weightedDavenport_squareSet_oddSquare (n : ℕ) (hn : 2 ≤ n)
    (hnOdd : Odd n) (hsquare : IsSquare n) :
    weightedDavenport (zmodWeightReps (squareSet n)) (ZMod n) = 5

/-- **Unit-square-weighted consecutive constant modulo 25 equals nine.** Let $U(25)^2$ be the set
of squares of units of $\mathbb{Z}_{25} = \mathbb{Z}/25\mathbb{Z}$. Some positive length $k$ has the
property that every sequence of $k$ elements of $\mathbb{Z}_{25}$ has a nonempty block of
consecutive terms with a $U(25)^2$-weighted sum equal to zero, and the least such length, the
$U(25)^2$-weighted consecutive constant $C_{U(25)^2}$ of $\mathbb{Z}_{25}$, equals $9$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 30. -/
public theorem_wanted weightedConsecutiveConstant_unitSquares_twentyFive :
    (weightedConsecutiveDefiningSet 25 (unitSquareSet 25)).Nonempty ∧
      weightedConsecutiveConstant 25 (unitSquareSet 25) = 9

/-- **Consecutive square-weighted constant of an odd square is at most nine.** For every odd
natural number $n \ge 2$ that is a perfect square, the consecutive $S(n)$-weighted zero-sum
constant satisfies $C_{S(n)} \le 9$, where $S(n)$ is the set of nonzero squares of
$\mathbb{Z}/n\mathbb{Z}$.

The hypothesis $n \ge 2$ is the paper's standing convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 31. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_oddSquare_le_nine (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) (hsquare : IsSquare n) :
    weightedConsecutiveConstant n (squareSet n) ≤ 9

/-- **Square-weighted consecutive constant of $p^r$ for prime $p \ge 7$ and even $r \ge 4$ is at
most five.** Let $p \ge 7$ be a prime and $r \ge 4$ an even natural number. Write $S(p^r)$ for the
set of nonzero squares in $\mathbb{Z}_{p^r} = \mathbb{Z}/p^r\mathbb{Z}$ and $C_{S(p^r)}$ for the
$S(p^r)$-weighted consecutive constant of $\mathbb{Z}_{p^r}$. Then $C_{S(p^r)} \le 5$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 34. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_largePrimePower_le_five
    (p r : ℕ) (hp : p.Prime) (hpSeven : 7 ≤ p) (hrEven : Even r)
    (hrFour : 4 ≤ r) :
    weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r)) ≤ 5

/-- **Square-weighted consecutive constant five for odd squares with a large prime fourth power.**
Let $n \ge 2$ be an odd perfect square and let $p \ge 7$ be a prime with $p^4 \mid n$. Write $S(n)$
for the set of nonzero squares in $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$. Then some positive length
$k$ has the property that every sequence of $k$ elements of $\mathbb{Z}_n$ has a nonempty block of
consecutive terms with an $S(n)$-weighted sum equal to zero, and the least such length, the
$S(n)$-weighted consecutive constant $C_{S(n)}$ of $\mathbb{Z}_n$, equals $5$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 35. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_oddSquare_largePrime (n p : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) (hnSquare : IsSquare n)
    (hp : p.Prime) (hpSeven : 7 ≤ p) (hdiv : p ^ 4 ∣ n) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedConsecutiveConstant n (squareSet n) = 5

/-- **Four unit terms force a unit-square-weighted zero sum modulo a power of 5.** Let $r \ge 1$
and let $U(5^r)^2$ be the set of squares of units of $\mathbb{Z}/5^r\mathbb{Z}$. If a sequence
$s_1, \dots, s_k$ in $\mathbb{Z}/5^r\mathbb{Z}$ has at least four terms, at distinct positions,
that are units, then there are $a_1, \dots, a_k \in U(5^r)^2$ with
$a_1 s_1 + \dots + a_k s_k = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 36. -/
public theorem_wanted unitSquareWeightedZeroSum_modFivePower_of_four_units (r k : ℕ)
    (hr : 0 < r) (S : Fin k → ZMod (5 ^ r))
    (hunits : ∃ J : Finset (Fin k), 4 ≤ J.card ∧ ∀ i ∈ J, IsUnit (S i)) :
    HasWeightedZeroSum (unitSquareSet (5 ^ r)) S

/-- **Square-weighted consecutive constant of $5^r$ for even $r \ge 4$ is at most seven.** Let
$r \ge 4$ be an even natural number. Write $S(5^r)$ for the set of nonzero squares in
$\mathbb{Z}_{5^r} = \mathbb{Z}/5^r\mathbb{Z}$ and $C_{S(5^r)}$ for the $S(5^r)$-weighted consecutive
constant of $\mathbb{Z}_{5^r}$. Then $C_{S(5^r)} \le 7$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 37. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_fivePower_le_seven (r : ℕ)
    (hrEven : Even r) (hrFour : 4 ≤ r) :
    weightedConsecutiveConstant (5 ^ r) (squareSet (5 ^ r)) ≤ 7

/-- **Square-weighted consecutive constant of squares divisible by 625 is at most seven.** Let
$n \ge 2$ be a perfect square with $5^4 \mid n$. Write $S(n)$ for the set of nonzero squares in
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ and $C_{S(n)}$ for the $S(n)$-weighted consecutive constant
of $\mathbb{Z}_n$. Then $C_{S(n)} \le 7$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 38. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_square_divisible_fiveFourth
    (n : ℕ) (hn : 2 ≤ n) (hnSquare : IsSquare n) (hdiv : 5 ^ 4 ∣ n) :
    weightedConsecutiveConstant n (squareSet n) ≤ 7

/-- **Consecutive square-weighted constant of the square of an odd squarefree number.** Let $m$
be an odd squarefree natural number and let $n = m^2$ with $n \ge 2$. Write $S(n)$ for the set
of nonzero squares of $\mathbb{Z}/n\mathbb{Z}$. Then there is a positive length $k$ such that
every sequence $x_1, \dots, x_k$ in $\mathbb{Z}/n\mathbb{Z}$ has a nonempty block of
consecutive terms $x_i, \dots, x_j$ and weights $a_i, \dots, a_j \in S(n)$ with
$a_i x_i + \dots + a_j x_j = 0$, and the consecutive $S(n)$-weighted zero-sum constant
$C_{S(n)}$, the least such $k$, equals $9$.

The hypothesis $n \ge 2$ is the paper's standing convention.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Theorem 39. -/
public theorem_wanted weightedConsecutiveConstant_squareSet_square_oddSquarefree
    (n m : ℕ) (hn : 2 ≤ n) (hnm : n = m ^ 2) (hmOdd : Odd m)
    (hmSquarefree : Squarefree m) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty ∧
      weightedConsecutiveConstant n (squareSet n) = 9

end

end MetaMathlibExt
