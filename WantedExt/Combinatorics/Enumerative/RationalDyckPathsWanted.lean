/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Logic.Equiv.Defs

/-!
# Rational Dyck paths and `Q`-bonacci paths

Statements from Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*,
Journal of Integer Sequences 28 (2025), Article 25.3.2 (arXiv:2409.20210). The
paths are Mathlib's `DyckWord`s of height at most `2`. Such a path `P ≠ ε` of
semilength `n` factorizes as `U X₁ ⋯ X_{n-1} D` with each `Xᵢ` a `1`-peak `UD`
or a `0`-valley `DU`, and the source's factorization
`P = U (UD)^{p₁} (DU)^{v₁} ⋯ (UD)^{p_k} (DU)^{v_k} D` reads the maximal runs of
this block word. Here the block word is a `List Bool` (`true` for `UD`), its
maximal runs are `boolRuns`, and the parameters `r, s` of `q = r/s` are natural
numbers.
-/

namespace MetaMathlibExt

@[expose] public section

open DyckStep

/-- **Dyck words of height at most $2$.** A Dyck word has height at most $2$ when no prefix of it
has more than two more up steps $U$ than down steps $D$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 2. -/
public def IsDyckHeightAtMostTwo (p : DyckWord) : Prop :=
  ∀ i ≤ p.toList.length, (p.toList.take i).count U ≤ (p.toList.take i).count D + 2

/-- Height at most `2` is decidable.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 2. -/
public instance : DecidablePred IsDyckHeightAtMostTwo := fun p => by
  unfold IsDyckHeightAtMostTwo
  infer_instance

/-- **Block word of a Dyck path of height at most $2$.** For a Dyck word
$P = P_0 P_1 \cdots P_{2n-1}$ of semilength $n$, with steps indexed from $0$, the block word of
$P$ is the Boolean word of length $n - 1$ (empty when $n = 0$) whose entry $i$, for
$0 \le i < n - 1$, is true exactly when $P_{2i+1} = U$.

When $P$ has height at most $2$ and $n \ge 1$, it factorizes as $P = U X_1 \cdots X_{n-1} D$
with each $X_{i+1} = P_{2i+1} P_{2i+2}$ a $1$-peak $UD$ or a $0$-valley $DU$, so entry $i$ is
true for a $1$-peak and false for a $0$-valley.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3, factorization (1). -/
public def dyckHeightTwoBlockWord (p : DyckWord) : List Bool :=
  (List.range (p.semilength - 1)).map fun i => decide (p.toList[2 * i + 1]? = some U)

/-- **Maximal runs of a Boolean word.** The run decomposition of a Boolean word is the list,
from left to right, of its maximal runs of equal consecutive letters, each recorded as the pair
(letter, length of the run).

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3 (blocks of maximal
length of consecutive `1`-peaks and `0`-valleys). -/
public def boolRuns : List Bool → List (Bool × ℕ)
  | [] => []
  | b :: l =>
    match boolRuns l with
    | [] => [(b, 1)]
    | (c, m) :: rest => if b = c then (c, m + 1) :: rest else (b, 1) :: (c, m) :: rest

/-- **Maximal runs of the word $1001100$.** Writing $1$ for true and $0$ for false, the maximal
runs of the Boolean word $1001100$, listed from left to right as pairs (letter, length), are
$(1, 1), (0, 2), (1, 2), (0, 2)$.

This word is the block word of the source's example path $U\,(UD)\,(DU)^2\,(UD)^2\,(DU)^2\,D$.
In the source's factorization $U\,(UD)^{p_1}\,(DU)^{v_1}\,(UD)^{p_2}\,(DU)^{v_2}\,D$ of that path
into maximal blocks of $1$-peaks $UD$ and $0$-valleys $DU$, the block lengths are $p_1 = 1$,
$v_1 = 2$, $p_2 = 2$, $v_2 = 2$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3, Example. -/
public theorem boolRuns_example :
    boolRuns [true, false, false, true, true, false, false] =
      [(true, 1), (false, 2), (true, 2), (false, 2)] := by
  decide

/-- **Valleys following a run.** Let $R = ((b_0, m_0), \dots, (b_{k-1}, m_{k-1}))$ be a list of
pairs of a Boolean letter and a natural number, read as the maximal runs of a block word in which
the letter $\mathrm{false}$ stands for a $0$-valley $DU$. For $i \in \mathbb{N}$, the number of
$0$-valleys immediately after run $i$ is $m_{i+1}$ if $i + 1 < k$ and $b_{i+1} = \mathrm{false}$,
and $0$ otherwise.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3 (`vᵢ` after `pᵢ`). -/
public def runFollowingValleys (R : List (Bool × ℕ)) (i : ℕ) : ℕ :=
  match R[i + 1]? with
  | some (false, v) => v
  | _ => 0

/-- **The rational Dyck path run condition.** Let $r, s \in \mathbb{N}$ and let $R$ be a list of
runs, each a pair (letter, length) with a Boolean letter. For the run at position $i$, let $v_i$
be the length of the run at position $i + 1$ if that run exists and has letter false, and
$v_i = 0$ otherwise. Then $R$ satisfies the rational run condition for $q = r/s$ when every run
of letter true, say of length $p$ at position $i$, has $p \le r$ and $p s \le r v_i$.

Applied to the maximal runs of the block word of a Dyck path, this says that every block of $p$
consecutive $1$-peaks has $p \le r$ and is followed by $v$ consecutive $0$-valleys with
$p s \le r v$, that is, $v \ge \lceil p s / r \rceil$ when $r \ge 1$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 3. -/
public def IsTildeRationalRuns (r s : ℕ) (R : List (Bool × ℕ)) : Prop :=
  ∀ i < R.length, (R.getD i (false, 0)).1 = true →
    (R.getD i (false, 0)).2 ≤ r ∧ (R.getD i (false, 0)).2 * s ≤ r * runFollowingValleys R i

/-- **The $Q$-bonacci run condition.** Let $r, s \in \mathbb{N}$ and let $R$ be a list of runs,
each a pair (letter, length) with a Boolean letter. For the run at position $i$, let $v_i$ be the
length of the run at position $i + 1$ if that run exists and has letter false, and $v_i = 0$
otherwise. Then $R$ satisfies the $Q$-bonacci run condition for $q = r/s$ when every run of
letter true, say of length $p$ at position $i$, has $p \le r$ and also $p s \le r v_i$, except
that $p s \le r v_i$ may fail when both this run is the last run of letter true in $R$ and
either $p = r$ or $v_i = 0$.

Applied to the maximal runs of the block word of a Dyck path, the runs of letter true are the
blocks of $p$ consecutive $1$-peaks and $v_i$ counts the $0$-valleys that follow them: every
block but the last needs $p s \le r v_i$, and the last block, of $p_k$ peaks followed by $v_k$
valleys, needs it only when $p_k < r$ and $v_k \ne 0$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 4. -/
public def IsQBonacciRuns (r s : ℕ) (R : List (Bool × ℕ)) : Prop :=
  ∀ i < R.length, (R.getD i (false, 0)).1 = true →
    (R.getD i (false, 0)).2 ≤ r ∧
      ((R.getD i (false, 0)).2 * s ≤ r * runFollowingValleys R i ∨
        ((∀ j < R.length, i < j → (R.getD j (false, 0)).1 = false) ∧
          ((R.getD i (false, 0)).2 = r ∨ runFollowingValleys R i = 0)))

/-- The `R̃` run condition is decidable.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 3. -/
public instance (r s : ℕ) : DecidablePred (IsTildeRationalRuns r s) := fun R => by
  unfold IsTildeRationalRuns
  infer_instance

/-- The `Q` run condition is decidable.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 4. -/
public instance (r s : ℕ) : DecidablePred (IsQBonacciRuns r s) := fun R => by
  unfold IsQBonacciRuns
  infer_instance

/-- **Examples of the $Q$-bonacci run condition for $q = 4/5$.** Writing $1$ for true and $0$ for
false, for $r = 4$ and $s = 5$ the maximal runs of the Boolean word $1001100$ do not satisfy the
$Q$-bonacci run condition, while the maximal runs of $100111100$ and of $100111$ do.

These are the block words of the source's paths $U\,(UD)\,(DU)^2\,(UD)^2\,(DU)^2\,D$, which is
not in the set $Q^{4/5}$ of $Q$-bonacci paths for $q = 4/5$, and
$U\,(UD)\,(DU)^2\,(UD)^4\,(DU)^2\,D$ and $U\,(UD)\,(DU)^2\,(UD)^3\,D$, which are. Writing each
path as $U\,(UD)^{p_1}\,(DU)^{v_1}\,(UD)^{p_2}\,(DU)^{v_2}\,D$ with maximal blocks, the second
has last block $p_2 = 4 = r$ and the third has $p_2 = 3 < r$ and $v_2 = 0$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Example after Definition 4. -/
public theorem isQBonacciRuns_examples :
    ¬ IsQBonacciRuns 4 5 (boolRuns [true, false, false, true, true, false, false]) ∧
      IsQBonacciRuns 4 5
        (boolRuns [true, false, false, true, true, true, true, false, false]) ∧
      IsQBonacciRuns 4 5 (boolRuns [true, false, false, true, true, true]) := by
  decide

/-- **The path sets $\tilde R_n^{r/s}$.** For natural numbers $r$, $s$ and $n$,
$\tilde R_n^{r/s}$ is the finite set of Dyck paths of semilength $n$ and height at most $2$
that satisfy the following run condition. For $n \ge 1$ such a path factors as
$U X_1 \cdots X_{n-1} D$ with each $X_i$ either a $1$-peak $UD$ or a $0$-valley $DU$, and its
block word $X_1 \cdots X_{n-1}$ (empty for $n = 0$) splits into maximal runs of equal blocks.
Every run of $p$ consecutive $1$-peaks must have $p \le r$ and $p s \le r v$, where $v$ is the
length of the run of $0$-valleys immediately after it ($v = 0$ if no run follows it).

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 3. -/
public def tildeRationalDyckPaths (r s n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  Finset.univ.filter fun p =>
    IsDyckHeightAtMostTwo p.1 ∧ IsTildeRationalRuns r s (boolRuns (dyckHeightTwoBlockWord p.1))

/-- **The $Q$-bonacci paths $Q_n^{r/s}$.** For natural numbers $r$, $s$ and $n$, $Q_n^{r/s}$ is
the finite set of Dyck paths of semilength $n$ and height at most $2$ that satisfy the following
run condition. For $n \ge 1$ such a path factors as $U X_1 \cdots X_{n-1} D$ with each $X_i$
either a $1$-peak $UD$ or a $0$-valley $DU$, and its block word $X_1 \cdots X_{n-1}$ (empty for
$n = 0$) splits into maximal runs of equal blocks. Every run of $p$ consecutive $1$-peaks must
have $p \le r$, and also $p s \le r v$, where $v$ is the length of the run of $0$-valleys
immediately after it ($v = 0$ if no run follows it); for the last run of $1$-peaks, the
inequality $p s \le r v$ is required only when $p < r$ and $v \ne 0$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 4. -/
public def qBonacciDyckPaths (r s n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  Finset.univ.filter fun p =>
    IsDyckHeightAtMostTwo p.1 ∧ IsQBonacciRuns r s (boolRuns (dyckHeightTwoBlockWord p.1))

/-- **Path counts for $q = 3/2$.** Let $r = 3$ and $s = 2$. The set $Q_4^{3/2}$ of $Q$-bonacci
paths of semilength $4$, that is, the Dyck paths of semilength $4$ and height at most $2$ whose
block word's maximal runs satisfy the $Q$-bonacci run condition, has $7$ elements, while the set
$\tilde R_5^{3/2}$ of Dyck paths of semilength $5$ and height at most $2$ whose block word's
maximal runs satisfy the rational run condition has $6$ elements.

Here $t = \lfloor (s - 1)/r \rfloor = 0$ and $s \ne t r + 1$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definitions 3 and 4. -/
public theorem card_qBonacciDyckPaths_three_two_four :
    (qBonacciDyckPaths 3 2 4).card = 7 ∧ (tildeRationalDyckPaths 3 2 5).card = 6 := by
  decide +kernel

/-- **$Q$-bonacci and rational-run paths are in bijection when $s = t r + 1$.** Let $r \ge 1$
and $t$ be natural numbers and $s = t r + 1$. Then for every $n \ge 0$ the set $Q_n^{r/s}$ of
$Q$-bonacci paths of semilength $n$ is in bijection with the set $\tilde R_{n+t+1}^{r/s}$ of Dyck
paths of semilength $n + t + 1$ and height at most $2$ whose block word's maximal runs satisfy
the rational run condition for $q = r/s$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Proposition 6
(`jis-2025-25.3.2-prop-6`). -/
public theorem_wanted nonempty_equiv_qBonacci_tildeRational {r s t : ℕ} (hr : 0 < r)
    (hs : s = t * r + 1) (n : ℕ) :
    Nonempty (qBonacciDyckPaths r s n ≃ tildeRationalDyckPaths r s (n + t + 1))

/-- **$Q$-bonacci and rational-run paths correspond exactly when $s \equiv 1 \pmod r$.** Let
$r, s \ge 1$ be coprime natural numbers and let $t = \lfloor (s - 1)/r \rfloor$, so that
$t r + 1 \le s \le (t + 1) r$. For $m \in \mathbb{N}$ write $Q_m^{r/s}$ for the set of $Q$-bonacci
paths of semilength $m$ and $\tilde R_m^{r/s}$ for the set of Dyck paths of semilength $m$ and
height at most $2$ whose block word's maximal runs satisfy the rational run condition for
$q = r/s$. Then $\tilde R_{n+t+1}^{r/s}$ and $Q_n^{r/s}$ are in bijection for every $n \ge 0$ if
and only if $s = t r + 1$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Proposition 7
(`jis-2025-25.3.2-prop-7`). -/
public theorem_wanted forall_nonempty_equiv_qBonacci_tildeRational_iff {r s : ℕ} (hr : 0 < r)
    (hs : 0 < s) (hrs : Nat.Coprime r s) :
    (∀ n : ℕ, Nonempty (tildeRationalDyckPaths r s (n + (s - 1) / r + 1) ≃
      qBonacciDyckPaths r s n)) ↔ s = (s - 1) / r * r + 1

end

end MetaMathlibExt
