/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith

/-!
# Rational Dyck paths and `Q`-bonacci paths

This module proves the shifted bijection between the two path families studied by
Barcucci, Bernini, Bilotta, and Pinzani in *Rational Dyck Paths*,
Journal of Integer Sequences 28 (2025), Article 25.3.2 (arXiv:2409.20210), and the
criterion `forall_nonempty_equiv_qBonacci_tildeRational_iff` saying when the shifted
path sets are equinumerous at every semilength. The
paths are Mathlib's `DyckWord`s of height at most `2`. Such a path `P ≠ ε` of
semilength `n` factorizes as `U X₁ ⋯ X_{n-1} D` with each `Xᵢ` a `1`-peak `UD`
or a `0`-valley `DU`, and the source's factorization
`P = U (UD)^{p₁} (DU)^{v₁} ⋯ (UD)^{p_k} (DU)^{v_k} D` reads the maximal runs of
this block word. Here the block word is a `List Bool` (`true` for `UD`), its
maximal runs are `boolRuns`, and the parameters `r, s` of `q = r/s` are natural
numbers.

The proof of `forall_nonempty_equiv_qBonacci_tildeRational_iff` fixes the prefix before the last
peak run. If the remaining block word has length `z`, the ordinary number of choices for the
peak run is `min r (r * z / (r + s))`. The final-run exception contributes one more choice
when `0 < z < r + s`. In the noncongruent case, a length with `r * z % (r + s) = 1` witnesses
a strict deficit in the shifted rational paths.
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

end

namespace nonempty_equiv_qBonacci_tildeRational

open DyckStep

-- After the initial up step the height is one. Each pair of steps returns to
-- height one, until a single down step closes the path.
private def steps : List Bool → List DyckStep
  | [] => [D]
  | true :: w => U :: D :: steps w
  | false :: w => D :: U :: steps w

private def BalancedTail (l : List DyckStep) : Prop :=
  l.count D = l.count U + 1 ∧ ∀ i,
    (l.take i).count D ≤ (l.take i).count U + 1 ∧
    (l.take i).count U ≤ (l.take i).count D + 1

private theorem balanced_pair (x y : DyckStep) (l : List DyckStep) :
    BalancedTail (x :: y :: l) ↔ x ≠ y ∧ BalancedTail l := by
  constructor
  · rintro ⟨h, hpre⟩
    have hne : x ≠ y := by
      rintro rfl
      have := hpre 2
      cases x <;> simp at this
    refine ⟨hne, ?_, fun i => ?_⟩
    · cases x <;> cases y <;> simp_all
    · have := hpre (i + 2)
      cases x <;> cases y <;> simp_all
  · rintro ⟨hne, h, hpre⟩
    refine ⟨?_, fun i => ?_⟩
    · cases x <;> cases y <;> simp_all
    · rcases i with _ | _ | i
      · simp
      · cases x <;> simp
      · have := hpre i
        cases x <;> cases y <;> simp_all

private theorem balanced_steps (w : List Bool) : BalancedTail (steps w) := by
  induction w with
  | nil =>
    refine ⟨rfl, fun i => ?_⟩
    cases i <;> simp [steps]
  | cons b w ih => cases b <;> exact (balanced_pair ..).2 ⟨by decide, ih⟩

private theorem exists_steps : ∀ l, BalancedTail l → ∃ w, steps w = l
  | [], h => by simp [BalancedTail] at h
  | [x], h => by
    cases x
    · simp [BalancedTail] at h
    · exact ⟨[], rfl⟩
  | x :: y :: l, h => by
    obtain ⟨hne, hl⟩ := (balanced_pair ..).1 h
    obtain ⟨w, rfl⟩ := exists_steps l hl
    cases x <;> cases y <;> first
      | contradiction
      | exact ⟨true :: w, rfl⟩
      | exact ⟨false :: w, rfl⟩

private def path (w : List Bool) : DyckWord where
  toList := U :: steps w
  count_U_eq_count_D := by simpa [List.count_cons] using (balanced_steps w).1.symm
  count_D_le_count_U i := by
    cases i with
    | zero => simp
    | succ i => simpa [List.count_cons] using ((balanced_steps w).2 i).1

private theorem height_path (w : List Bool) : IsDyckHeightAtMostTwo (path w) := by
  intro i _
  cases i with
  | zero => simp
  | succ i =>
    have := ((balanced_steps w).2 i).2
    simp [path]
    omega

private theorem semilength_path (w : List Bool) : (path w).semilength = w.length + 1 := by
  suffices (steps w).count U = w.length by simp [DyckWord.semilength, path, this]
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [steps, ih]

private theorem steps_get (w : List Bool) (i : ℕ) (hi : i < w.length) :
    decide ((steps w)[2 * i]? = some U) = w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons b w ih =>
    cases i with
    | zero => cases b <;> rfl
    | succ i =>
      have h := ih i (by simpa using hi)
      rw [Bool.eq_iff_iff, decide_eq_true_eq] at h ⊢
      cases b <;> simpa only [steps, Nat.mul_succ, List.getElem?_cons_succ,
        List.getElem_cons_succ] using h

private theorem blockWord_path (w : List Bool) : dyckHeightTwoBlockWord (path w) = w := by
  apply List.ext_getElem
  · simp [dyckHeightTwoBlockWord, semilength_path]
  · intro i _ hi
    simpa [dyckHeightTwoBlockWord, path] using steps_get w i hi

private theorem exists_path {p : DyckWord} (hp : IsDyckHeightAtMostTwo p)
    (h : p ≠ 0) : ∃ w, path w = p := by
  have hn := DyckWord.toList_ne_nil.mpr h
  obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil hn
  have hhead := p.head_eq_U hn
  simp only [hx, List.head_cons] at hhead
  subst x
  have hb : BalancedTail l := by
    constructor
    · simpa [hx, List.count_cons] using p.count_U_eq_count_D.symm
    · intro i
      have hu := hp (min (i + 1) p.toList.length) (min_le_right ..)
      rw [← List.take_take, List.take_length] at hu
      have hd := p.count_D_le_count_U (i + 1)
      simp [hx] at hu hd
      omega
  obtain ⟨w, hw⟩ := exists_steps l hb
  exact ⟨w, DyckWord.ext (by simp [path, hw, hx])⟩

-- A nonempty sequence of peak runs. Each stored peak count is one less
-- than its length. Only the final valley count may be zero.
private inductive Peaks
  | last (p v : ℕ)
  | more (p v : ℕ) (tail : Peaks)

private abbrev Code := ℕ × Option Peaks

private def Peaks.bump : Peaks → Peaks
  | .last p v => .last (p + 1) v
  | .more p v a => .more (p + 1) v a

private def prepend : Bool → Code → Code
  | false, (z, a) => (z + 1, a)
  | true, (z, none) => (0, some (.last 0 z))
  | true, (0, some a) => (0, some a.bump)
  | true, (z + 1, some a) => (0, some (.more 0 z a))

private def parse : List Bool → Code
  | [] => (0, none)
  | b :: w => prepend b (parse w)

private def Peaks.word : Peaks → List Bool
  | .last p v => List.replicate (p + 1) true ++ List.replicate v false
  | .more p v a => List.replicate (p + 1) true ++ List.replicate (v + 1) false ++ a.word

private def word (c : Code) : List Bool :=
  List.replicate c.1 false ++ c.2.elim [] Peaks.word

private theorem word_prepend (b : Bool) (c : Code) : word (prepend b c) = b :: word c := by
  obtain ⟨z, _ | a⟩ := c <;> cases b <;> cases z <;>
    simp [word, prepend, Peaks.word, List.replicate_succ]
  cases a <;> simp [Peaks.bump, Peaks.word, List.replicate_succ]

private theorem word_parse (w : List Bool) : word (parse w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [parse, word_prepend, ih]

private theorem parse_zeros (z : ℕ) (w : List Bool) :
    parse (List.replicate z false ++ w) = (z + (parse w).1, (parse w).2) := by
  induction z with
  | zero => simp
  | succ z ih => simp [List.replicate_succ, parse, ih, prepend, Nat.succ_add]

private theorem parse_peaks (a : Peaks) : parse a.word = (0, some a) := by
  induction a with
  | last p v =>
    induction p with
    | zero =>
      simpa [Peaks.word, parse, prepend] using
        congrArg (prepend true) (parse_zeros v [])
    | succ p ih =>
      simpa [Peaks.word, List.replicate_succ, parse, prepend, Peaks.bump] using
        congrArg (prepend true) ih
  | more p v a h =>
    induction p with
    | zero => simp [Peaks.word, parse, parse_zeros, h, prepend]
    | succ p ih =>
      simpa [Peaks.word, List.replicate_succ, parse, prepend, Peaks.bump] using
        congrArg (prepend true) ih

private theorem parse_word (c : Code) : parse (word c) = c := by
  obtain ⟨z, _ | a⟩ := c
  · simpa [word, parse] using parse_zeros z []
  · simp [word, parse_zeros, parse_peaks]

private def Peaks.runs : Peaks → List (Bool × ℕ)
  | .last p 0 => [(true, p + 1)]
  | .last p (v + 1) => [(true, p + 1), (false, v + 1)]
  | .more p v a => (true, p + 1) :: (false, v + 1) :: a.runs

private def runs : Code → List (Bool × ℕ)
  | (0, a) => a.elim [] Peaks.runs
  | (z + 1, a) => (false, z + 1) :: a.elim [] Peaks.runs

private theorem runs_parse (w : List Bool) : runs (parse w) = boolRuns w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [boolRuns, ← ih, parse]
    obtain ⟨z, _ | a⟩ := parse w
    · cases b <;> cases z <;> rfl
    · cases a with
      | last p v => cases v <;> cases b <;> cases z <;> rfl
      | more p v a => cases b <;> cases z <;> rfl

private abbrev Run := Bool × ℕ

private def FinalPeak (R : List Run) (i : ℕ) : Prop :=
  ∀ j < R.length, i < j → (R.getD j (false, 0)).1 = false

-- The Boolean flag enables the exception for the final peak run.
private def Valid (q : Bool) (r s : ℕ) (R : List Run) : Prop :=
  ∀ i < R.length, (R.getD i (false, 0)).1 = true →
    (R.getD i (false, 0)).2 ≤ r ∧
      ((R.getD i (false, 0)).2 * s ≤ r * runFollowingValleys R i ∨
        q = true ∧ FinalPeak R i ∧ ((R.getD i (false, 0)).2 = r ∨ runFollowingValleys R i = 0))

private theorem valid_cons (q b : Bool) (r s m : ℕ) (R : List Run) :
    Valid q r s ((b, m) :: R) ↔
      (b = true → m ≤ r ∧ (m * s ≤ r * runFollowingValleys ((b, m) :: R) 0 ∨
        q = true ∧ FinalPeak ((b, m) :: R) 0 ∧ (m = r ∨ runFollowingValleys ((b, m) :: R) 0 = 0)))
        ∧ Valid q r s R := by
  simp [Valid, FinalPeak, runFollowingValleys, Nat.forall_lt_succ_left]

private theorem valid_nil (q : Bool) (r s : ℕ) : Valid q r s [] := by simp [Valid]

private theorem valid_valleys (q : Bool) (r s z : ℕ) (R : List Run) :
    Valid q r s ((false, z) :: R) ↔ Valid q r s R := by simp [valid_cons]

private theorem min_valleys {r t p v : ℕ} (hp : 0 < p) (hr : p ≤ r) :
    p * (t * r + 1) ≤ r * v ↔ t * p < v := by
  rw [Nat.mul_add, Nat.mul_one, show p * (t * r) = r * (t * p) by ac_rfl]
  constructor
  · intro h
    by_contra! h'
    have := Nat.mul_le_mul_left r h'
    omega
  · intro h
    have := Nat.mul_le_mul_left r (show t * p + 1 ≤ v from h)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

private def Peaks.OK (q : Bool) (r t : ℕ) : Peaks → Prop
  | .last p v => p + 1 ≤ r ∧ (t * (p + 1) < v ∨ q = true ∧ (p + 1 = r ∨ v = 0))
  | .more p v a => (p + 1 ≤ r ∧ t * (p + 1) < v + 1) ∧ a.OK q r t

private theorem peaks_head (a : Peaks) :
    a.runs ≠ [] ∧ (a.runs.getD 0 (false, 0)).1 = true := by
  cases a with
  | last p v => cases v <;> simp [Peaks.runs]
  | more => simp [Peaks.runs]

private theorem peaks_valid (q : Bool) (r t : ℕ) (a : Peaks) :
    Valid q r (t * r + 1) a.runs ↔ a.OK q r t := by
  induction a with
  | last p v =>
    have lone : FinalPeak [(true, p + 1)] 0 := by simp [FinalPeak]
    have lastPair (v : ℕ) : FinalPeak [(true, p + 1), (false, v)] 0 := by
      simp [FinalPeak, Nat.forall_lt_succ_left]
    cases v <;>
      simp +contextual [Peaks.runs, valid_cons, valid_nil, runFollowingValleys, lone, lastPair,
        Peaks.OK, min_valleys]
  | more p v a ih =>
    have hn : ¬ FinalPeak ((true, p + 1) :: (false, v + 1) :: a.runs) 0 := by
      intro h
      have := h 2 (by simpa using List.length_pos_iff.mpr (peaks_head a).1) (by decide)
      change (a.runs.getD 0 (false, 0)).1 = false at this
      rw [(peaks_head a).2] at this
      contradiction
    simp +contextual [Peaks.runs, valid_cons, hn, runFollowingValleys, ih, Peaks.OK, min_valleys]

private def OK (q : Bool) (r t : ℕ) (c : Code) : Prop :=
  ∀ a ∈ c.2, a.OK q r t

private theorem runs_valid (q : Bool) (r t : ℕ) (c : Code) :
    Valid q r (t * r + 1) (runs c) ↔ OK q r t c := by
  obtain ⟨z, _ | a⟩ := c <;> cases z <;>
    simp [runs, OK, valid_valleys, valid_nil, peaks_valid]

-- Keep the length of the final peak/valley pair plus t + 1. At each fixed
-- length the maximal possible Q peak run maps to one peak; every smaller
-- admissible run gains one peak. This cycles through the rational choices.
private def Peaks.extend (r t : ℕ) : Peaks → Peaks
  | .last p v =>
    if p + 1 = r ∨ v = 0 then .last 0 (p + v + t + 1) else .last (p + 1) (v + t)
  | .more p v a => .more p v (a.extend r t)

private def Peaks.shorten (r t : ℕ) : Peaks → Peaks
  | .last 0 v =>
    let k := v - t
    .last (min r k - 1) (k - min r k)
  | .last (p + 1) v => .last p (v - t)
  | .more p v a => .more p v (a.shorten r t)

private theorem extend_length (r t : ℕ) (a : Peaks) :
    (a.extend r t).word.length = a.word.length + t + 1 := by
  induction a with
  | last p v => simp [Peaks.extend]; split <;> simp [Peaks.word] <;> omega
  | more p v a ih => simp [Peaks.extend, Peaks.word, ih]; omega

private theorem extend_ok {r t : ℕ} (hr : 0 < r) (a : Peaks) (h : a.OK true r t) :
    (a.extend r t).OK false r t := by
  induction a with
  | last p v =>
    simp only [Peaks.OK] at h
    unfold Peaks.extend
    split <;> simp_all [Peaks.OK, Nat.mul_succ] <;> omega
  | more p v a ih => exact ⟨h.1, ih h.2⟩

private theorem shorten_extend {r t : ℕ} (a : Peaks) (h : a.OK true r t) :
    (a.extend r t).shorten r t = a := by
  induction a with
  | last p v =>
    simp only [Peaks.OK] at h
    simp only [Peaks.extend]
    split <;> simp [Peaks.shorten]
    omega
  | more p v a ih => simp [Peaks.extend, Peaks.shorten, ih h.2]

private theorem shorten_ok {r t : ℕ} (hr : 0 < r) (a : Peaks) (h : a.OK false r t) :
    (a.shorten r t).OK true r t := by
  induction a with
  | last p v =>
    cases p <;> simp [Peaks.shorten, Peaks.OK, Nat.mul_succ] at h ⊢ <;> omega
  | more p v a ih => exact ⟨h.1, ih h.2⟩

private theorem extend_shorten {r t : ℕ} (hr : 0 < r) (a : Peaks) (h : a.OK false r t) :
    (a.shorten r t).extend r t = a := by
  induction a with
  | last p v =>
    cases p <;> simp [Peaks.shorten, Peaks.extend, Peaks.OK, Nat.mul_succ] at h ⊢ <;>
      split <;> simp <;> omega
  | more p v a ih => simp [Peaks.shorten, Peaks.extend, ih h.2]

private def extend (r t : ℕ) : Code → Code
  | (z, none) => (z + t + 1, none)
  | (z, some a) => (z, some (a.extend r t))

private def shorten (r t : ℕ) : Code → Code
  | (z, none) => (z - (t + 1), none)
  | (z, some a) => (z, some (a.shorten r t))

private abbrev Codes (q : Bool) (r t k : ℕ) :=
  {c : Code // (word c).length = k ∧ OK q r t c}

private def codeEquiv {r t : ℕ} (hr : 0 < r) (k : ℕ) :
    Codes true r t k ≃ Codes false r t (k + t + 1) where
  toFun := fun ⟨c, hl, h⟩ => ⟨extend r t c, by
    obtain ⟨z, _ | a⟩ := c <;> simp_all [OK, extend, word, extend_length, extend_ok hr]
    omega⟩
  invFun := fun ⟨c, hl, h⟩ => ⟨shorten r t c, by
    obtain ⟨z, _ | a⟩ := c
    · simp_all [OK, shorten, word]
    · have ha := h a rfl
      have he := extend_length r t (a.shorten r t)
      rw [extend_shorten hr a ha] at he
      simp_all [OK, shorten, word, shorten_ok hr]
      omega⟩
  left_inv := by
    rintro ⟨⟨z, _ | a⟩, hl, h⟩ <;> apply Subtype.ext
    · simp [extend, shorten]
    · simp [OK] at h
      simp [extend, shorten, shorten_extend a h]
  right_inv := by
    rintro ⟨⟨z, _ | a⟩, hl, h⟩ <;> apply Subtype.ext
    · simp [word] at hl
      simp [extend, shorten, hl]
    · simp [OK] at h
      simp [shorten, extend, extend_shorten hr a h]

private noncomputable def pathEquiv (q : Bool) (r t k : ℕ)
    (S : Finset {p : DyckWord // p.semilength = k + 1})
    (hS : ∀ p, p ∈ S ↔ IsDyckHeightAtMostTwo p.1 ∧
      Valid q r (t * r + 1) (boolRuns (dyckHeightTwoBlockWord p.1))) :
    Codes q r t k ≃ S := by
  let f (c : Codes q r t k) : S := ⟨⟨path (word c.val), by
    rw [semilength_path, c.property.1]⟩, (hS _).2 ⟨height_path _, by
      rw [blockWord_path, ← runs_parse, parse_word, runs_valid]
      exact c.property.2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro c d he
    have he' := congrArg (fun p : S => parse (dyckHeightTwoBlockWord p.val.val)) he
    apply Subtype.ext
    simpa [f, blockWord_path, parse_word] using he'
  · rintro ⟨⟨p, hp⟩, hm⟩
    obtain ⟨hh, hv⟩ := (hS _).1 hm
    have hn : p ≠ 0 := by rintro rfl; simp at hp
    obtain ⟨w, rfl⟩ := exists_path hh hn
    refine ⟨⟨parse w, ?_, ?_⟩, ?_⟩
    · simpa [word_parse, semilength_path] using hp
    · simpa [← runs_valid, runs_parse, blockWord_path] using hv
    · apply Subtype.ext
      apply Subtype.ext
      simp [f, word_parse]

private noncomputable def rationalEquiv (r t k : ℕ) :
    Codes false r t k ≃ tildeRationalDyckPaths r (t * r + 1) (k + 1) :=
  pathEquiv false r t k _ fun _ => by
    simp [tildeRationalDyckPaths, Valid, IsTildeRationalRuns]

private noncomputable def bonacciEquiv (r t k : ℕ) :
    Codes true r t k ≃ qBonacciDyckPaths r (t * r + 1) (k + 1) :=
  pathEquiv true r t k _ fun _ => by
    simp [qBonacciDyckPaths, Valid, IsQBonacciRuns, FinalPeak]

private theorem peaks_length_gt (r t : ℕ) (a : Peaks) (h : a.OK false r t) :
    t < a.word.length := by
  cases a <;> simp [Peaks.OK, Peaks.word, Nat.mul_succ] at h ⊢ <;> omega

-- At semilength zero the empty Dyck word corresponds to the word of t valleys.
private def zeroEquiv (r t : ℕ) : qBonacciDyckPaths r (t * r + 1) 0 ≃ Codes false r t t where
  toFun _ := ⟨(t, none), by simp [word, OK]⟩
  invFun _ := ⟨⟨0, rfl⟩, by
    simp [qBonacciDyckPaths, IsDyckHeightAtMostTwo, dyckHeightTwoBlockWord, boolRuns,
      IsQBonacciRuns, show (0 : DyckWord).toList = [] from rfl]⟩
  left_inv := by
    rintro ⟨⟨p, hp⟩, _⟩
    apply Subtype.ext
    apply Subtype.ext
    have := p.two_mul_semilength_eq_length
    rw [hp] at this
    exact (DyckWord.toList_eq_nil.mp (List.length_eq_zero_iff.mp this.symm)).symm
  right_inv := by
    rintro ⟨⟨z, _ | a⟩, hl, h⟩ <;> apply Subtype.ext
    · simpa [word] using congrArg (fun n : ℕ => (n, (none : Option Peaks))) hl.symm
    · have := peaks_length_gt r t a (h a rfl)
      simp [word] at hl
      omega

end nonempty_equiv_qBonacci_tildeRational

open nonempty_equiv_qBonacci_tildeRational in
/-- **$Q$-bonacci and rational-run paths are in bijection when $s = t r + 1$.** Let $r \ge 1$
and $t$ be natural numbers and $s = t r + 1$. Then for every $n \ge 0$ the set $Q_n^{r/s}$ of
$Q$-bonacci paths of semilength $n$ is in bijection with the set $\tilde R_{n+t+1}^{r/s}$ of Dyck
paths of semilength $n + t + 1$ and height at most $2$ whose block word's maximal runs satisfy
the rational run condition for $q = r/s$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Proposition 6
(`jis-2025-25.3.2-prop-6`). -/
public theorem nonempty_equiv_qBonacci_tildeRational {r s t : ℕ} (hr : 0 < r)
    (hs : s = t * r + 1) (n : ℕ) :
    Nonempty (qBonacciDyckPaths r s n ≃ tildeRationalDyckPaths r s (n + t + 1)) := by
  subst s
  cases n with
  | zero =>
    rw [Nat.zero_add]
    exact ⟨(zeroEquiv r t).trans (rationalEquiv r t t)⟩
  | succ k =>
    rw [Nat.succ_add]
    exact ⟨((bonacciEquiv r t k).symm.trans (codeEquiv hr k)).trans (rationalEquiv r t _)⟩

namespace forall_nonempty_equiv_qBonacci_tildeRational_iff

open DyckStep
open nonempty_equiv_qBonacci_tildeRational
  (path height_path semilength_path blockWord_path exists_path)

/- Separate the final peak run, where the two path conditions differ. The two
parameters of an interior pair are stored one below their positive lengths. -/
private inductive Tail
  | last (p v : ℕ)
  | more (p v : ℕ) (rest : Tail)

private inductive Form
  | zeros (z : ℕ)
  | peaks (z : ℕ) (tail : Tail)

private def Tail.word : Tail → List Bool
  | .last p v => List.replicate (p + 1) true ++ List.replicate v false
  | .more p v t => List.replicate (p + 1) true ++ List.replicate (v + 1) false ++ t.word

private def Form.word : Form → List Bool
  | .zeros z => List.replicate z false
  | .peaks z t => List.replicate z false ++ t.word

private lemma form_surj (w : List Bool) : ∃ f : Form, f.word = w := by
  induction w with
  | nil => exact ⟨.zeros 0, rfl⟩
  | cons b w ih =>
    obtain ⟨f, rfl⟩ := ih
    cases b with
    | false =>
      cases f with
      | zeros z => exact ⟨.zeros (z + 1), rfl⟩
      | peaks z t => exact ⟨.peaks (z + 1) t, rfl⟩
    | true =>
      cases f with
      | zeros z => exact ⟨.peaks 0 (.last 0 z), rfl⟩
      | peaks z t =>
        cases z with
        | zero =>
          cases t with
          | last p v => exact ⟨.peaks 0 (.last (p + 1) v), rfl⟩
          | more p v t => exact ⟨.peaks 0 (.more (p + 1) v t), rfl⟩
        | succ z => exact ⟨.peaks 0 (.more 0 z t), rfl⟩

private abbrev Runs := List (Bool × ℕ)

private def zerosRun : ℕ → Runs
  | 0 => []
  | n + 1 => [(false, n + 1)]

private def Tail.runs : Tail → Runs
  | .last p v => (true, p + 1) :: zerosRun v
  | .more p v t => (true, p + 1) :: (false, v + 1) :: t.runs

private def Form.runs : Form → Runs
  | .zeros z => zerosRun z
  | .peaks z t => zerosRun z ++ t.runs

private lemma tail_head (t : Tail) : ∃ p l, t.runs = (true, p + 1) :: l := by
  cases t <;> exact ⟨_, _, rfl⟩

private lemma runs_replicate (b : Bool) (n : ℕ) (w : List Bool)
    (h : ∀ x ∈ (boolRuns w).head?, x.1 ≠ b) :
    boolRuns (List.replicate (n + 1) b ++ w) = (b, n + 1) :: boolRuns w := by
  induction n with
  | zero =>
    change boolRuns (b :: w) = (b, 1) :: boolRuns w
    rw [boolRuns]
    generalize hr : boolRuns w = l at *
    cases l with
    | nil => rfl
    | cons x xs =>
      obtain ⟨c, m⟩ := x
      simp_all [ne_comm]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, boolRuns, ih]
    simp

private lemma runs_zeros (z : ℕ) : boolRuns (List.replicate z false) = zerosRun z := by
  cases z with
  | zero => rfl
  | succ n => simpa [zerosRun, boolRuns] using runs_replicate false n [] (by simp [boolRuns])

private lemma tail_runs_word (t : Tail) : boolRuns t.word = t.runs := by
  induction t with
  | last p v =>
    simp only [Tail.word, Tail.runs]
    rw [runs_replicate, runs_zeros]
    rw [runs_zeros]
    cases v <;> simp [zerosRun]
  | more p v t ih =>
    obtain ⟨a, l, hl⟩ := tail_head t
    have hv := runs_replicate false v t.word (by simp [ih, hl])
    simp only [Tail.word, List.append_assoc, Tail.runs]
    rw [runs_replicate, hv, ih]
    simp [hv]

private lemma form_runs_word (f : Form) : boolRuns f.word = f.runs := by
  cases f with
  | zeros z => exact runs_zeros z
  | peaks z t =>
    cases z with
    | zero => simpa [Form.word, Form.runs, zerosRun] using tail_runs_word t
    | succ z =>
      obtain ⟨a, l, hl⟩ := tail_head t
      simp [Form.word, Form.runs, zerosRun, runs_replicate false z t.word
        (by simp [tail_runs_word, hl]), tail_runs_word]

private lemma tail_runs_inj {t u : Tail} (h : t.runs = u.runs) : t = u := by
  induction t generalizing u with
  | last p v =>
    cases u with
    | last q w => cases v <;> cases w <;> simp_all [Tail.runs, zerosRun]
    | more q w u =>
      obtain ⟨a, l, hl⟩ := tail_head u
      cases v <;> simp_all [Tail.runs, zerosRun]
  | more p v t ih =>
    cases u with
    | last q w =>
      obtain ⟨a, l, hl⟩ := tail_head t
      cases w <;> simp_all [Tail.runs, zerosRun]
    | more q w u =>
      obtain ⟨rfl, rfl, hu⟩ : p = q ∧ v = w ∧ t.runs = u.runs := by simpa [Tail.runs] using h
      rw [ih hu]

private lemma form_word_inj : Function.Injective Form.word := by
  intro f g h
  have he : f.runs = g.runs := by simpa only [← form_runs_word] using congrArg boolRuns h
  cases f with
  | zeros z =>
    cases g with
    | zeros k => cases z <;> cases k <;> simp_all [Form.runs, zerosRun]
    | peaks k t =>
      obtain ⟨a, l, hl⟩ := tail_head t
      cases z <;> cases k <;> simp_all [Form.runs, zerosRun]
  | peaks z t =>
    obtain ⟨a, l, hl⟩ := tail_head t
    cases g with
    | zeros k => cases z <;> cases k <;> simp_all [Form.runs, zerosRun]
    | peaks k u =>
      obtain ⟨b, m, hm⟩ := tail_head u
      have ht := @tail_runs_inj t u
      cases z <;> cases k <;> simp_all [Form.runs, zerosRun]

private def acceptable (q : Bool) (r s : ℕ) (l : Runs) : Prop :=
  if q then IsQBonacciRuns r s l else IsTildeRationalRuns r s l

private lemma later_cons (x : Bool × ℕ) (l : Runs) (i : ℕ) :
    (∀ j < (x :: l).length, i + 1 < j → ((x :: l).getD j (false, 0)).1 = false) ↔
    (∀ j < l.length, i < j → (l.getD j (false, 0)).1 = false) := by
  rw [List.length_cons, Nat.forall_lt_succ_left]
  simp [List.getD]

private lemma rational_cons (r s : ℕ) (x : Bool × ℕ) (l : Runs) :
    IsTildeRationalRuns r s (x :: l) ↔
      (x.1 = true → x.2 ≤ r ∧ x.2 * s ≤ r * runFollowingValleys (x :: l) 0) ∧
      IsTildeRationalRuns r s l := by
  unfold IsTildeRationalRuns
  rw [List.length_cons, Nat.forall_lt_succ_left]
  simp [List.getD, runFollowingValleys]

private lemma bonacci_cons (r s : ℕ) (x : Bool × ℕ) (l : Runs) :
    IsQBonacciRuns r s (x :: l) ↔
      (x.1 = true → x.2 ≤ r ∧ (x.2 * s ≤ r * runFollowingValleys (x :: l) 0 ∨
        ((∀ i < l.length, (l.getD i (false, 0)).1 = false) ∧
        (x.2 = r ∨ runFollowingValleys (x :: l) 0 = 0)))) ∧ IsQBonacciRuns r s l := by
  unfold IsQBonacciRuns
  rw [List.length_cons, Nat.forall_lt_succ_left]
  have h₀ : (∀ j < l.length + 1, 0 < j → ((x :: l).getD j (false, 0)).1 = false) ↔
      (∀ i < l.length, (l.getD i (false, 0)).1 = false) := by
    rw [Nat.forall_lt_succ_left]
    simp [List.getD]
  simp only [h₀]
  simp only [show ∀ i, (∀ j < l.length + 1, i + 1 < j →
    ((x :: l).getD j (false, 0)).1 = false) ↔ _ from later_cons x l]
  simp [List.getD, runFollowingValleys]

private lemma acceptable_false (q : Bool) (r s z : ℕ) (l : Runs) :
    acceptable q r s ((false, z) :: l) ↔ acceptable q r s l := by
  cases q <;> simp [acceptable, rational_cons, bonacci_cons]

private lemma acceptable_nil (q : Bool) (r s : ℕ) : acceptable q r s [] := by
  cases q <;> simp [acceptable, IsQBonacciRuns, IsTildeRationalRuns]

private def finalOK (q : Bool) (r s p v : ℕ) : Prop :=
  p ≤ r ∧ (p * s ≤ r * v ∨ q = true ∧ (p = r ∨ v = 0))

private def Tail.good (q : Bool) (r s : ℕ) : Tail → Prop
  | .last p v => finalOK q r s (p + 1) v
  | .more p v t => (p + 1 ≤ r ∧ (p + 1) * s ≤ r * (v + 1)) ∧ t.good q r s

private lemma tail_good (q : Bool) (r s : ℕ) (t : Tail) :
    acceptable q r s t.runs ↔ t.good q r s := by
  cases t with
  | last p v =>
    cases v <;> cases q <;> simp [Tail.runs, zerosRun, acceptable, rational_cons, bonacci_cons,
      runFollowingValleys, List.getD, Tail.good, finalOK,
      show IsTildeRationalRuns r s [] by simp [IsTildeRationalRuns],
      show IsQBonacciRuns r s [] by simp [IsQBonacciRuns]]
  | more p v t =>
    rw [Tail.runs, Tail.good, ← tail_good q r s t]
    obtain ⟨a, l, hl⟩ := tail_head t
    have h : ¬ ∀ i < ((false, v + 1) :: t.runs).length,
        (((false, v + 1) :: t.runs).getD i (false, 0)).1 = false := by
      intro h
      simpa [hl, List.getD] using h 1 (by simp [hl])
    cases q <;> simp only [acceptable, Bool.false_eq_true, ite_false, ite_true,
      rational_cons, bonacci_cons, h] <;> simp [runFollowingValleys]

private def Form.good (q : Bool) (r s : ℕ) : Form → Prop
  | .zeros _ => True
  | .peaks _ t => t.good q r s

private lemma form_good (q : Bool) (r s : ℕ) (f : Form) :
    acceptable q r s (boolRuns f.word) ↔ f.good q r s := by
  rw [form_runs_word]
  cases f with
  | zeros z => cases z <;> simp [Form.runs, zerosRun, Form.good, acceptable_false, acceptable_nil]
  | peaks z t => cases z <;> simp [Form.runs, zerosRun, Form.good, acceptable_false, tail_good]

private def paths (q : Bool) (r s n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  if q then qBonacciDyckPaths r s n else tildeRationalDyckPaths r s n

private lemma mem_paths {q : Bool} {r s n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    p ∈ paths q r s n ↔ IsDyckHeightAtMostTwo p.val ∧
      acceptable q r s (boolRuns (dyckHeightTwoBlockWord p.val)) := by
  cases q <;> simp [paths, acceptable, tildeRationalDyckPaths, qBonacciDyckPaths]

private abbrev Forms (q : Bool) (r s m : ℕ) := {f : Form // f.word.length = m ∧ f.good q r s}

private lemma eq_zero_of_length {p : DyckWord} (h : p.semilength = 0) : p = 0 := by
  apply DyckWord.toList_eq_nil.mp
  apply List.length_eq_zero_iff.mp
  simpa [h] using p.two_mul_semilength_eq_length.symm

private noncomputable def pathsEquiv (q : Bool) (r s n : ℕ) :
    Forms q r s (n - 1) ≃ paths q r s n := by
  cases n with
  | zero =>
    have hf (f : Forms q r s (0 - 1)) : f.val = .zeros 0 := by
      apply form_word_inj
      exact List.length_eq_zero_iff.mp f.property.1
    have hp (p : ↥(paths q r s 0)) : p.val.val = 0 := eq_zero_of_length p.val.property
    exact {
      toFun := fun _ => ⟨⟨0, rfl⟩, mem_paths _ |>.mpr
        ⟨by intro i _; change (([] : List DyckStep).take i).count U ≤ _; simp,
          acceptable_nil ..⟩⟩
      invFun := fun _ => ⟨.zeros 0, rfl, trivial⟩
      left_inv := fun f => Subtype.ext (hf f).symm
      right_inv := fun p => Subtype.ext (Subtype.ext (hp p).symm) }
  | succ m =>
    change Forms q r s m ≃ _
    let build (f : Forms q r s m) : ↥(paths q r s (m + 1)) :=
      ⟨⟨path f.val.word, by rw [semilength_path, f.property.1]⟩,
        (mem_paths _).2 ⟨height_path _, by
          rw [blockWord_path, form_good]
          exact f.property.2⟩⟩
    apply Equiv.ofBijective build
    constructor
    · intro f g he
      apply Subtype.ext
      apply form_word_inj
      simpa only [build, blockWord_path] using
        congrArg (fun p : ↥(paths q r s (m + 1)) => dyckHeightTwoBlockWord p.val.val) he
    · rintro ⟨⟨p, hm⟩, hp⟩
      obtain ⟨hh, ha⟩ := (mem_paths _).1 hp
      obtain ⟨w, rfl⟩ := exists_path hh (by rintro rfl; simp at hm)
      obtain ⟨f, rfl⟩ := form_surj w
      rw [blockWord_path, form_good] at ha
      exact ⟨⟨f, by simpa [semilength_path] using hm, ha⟩, rfl⟩

/- A prefix consists of initial valleys and all the completed, nonfinal peak/valley pairs. -/
private abbrev Prefix := ℕ × List (ℕ × ℕ)

private def attachTail (l : List (ℕ × ℕ)) (p v : ℕ) : Tail :=
  l.foldr (fun x t => Tail.more x.1 x.2 t) (.last p v)

private def attach (a : Prefix) (p v : ℕ) : Form := .peaks a.1 (attachTail a.2 p v)

private lemma attach_inj {a b : Prefix} {p v j w : ℕ}
    (h : attach a p v = attach b j w) : a = b ∧ p = j ∧ v = w := by
  obtain ⟨z, l⟩ := a
  obtain ⟨y, k⟩ := b
  injection h with hz ht
  dsimp at hz ht
  subst y
  suffices l = k ∧ p = j ∧ v = w by simpa using this
  induction l generalizing k with
  | nil => cases k <;> simp_all [attachTail]
  | cons x l ih =>
    cases k with
    | nil => simp [attachTail] at ht
    | cons b k =>
      obtain ⟨h₁, h₂, hu⟩ := Tail.more.inj ht
      obtain ⟨rfl, rfl, rfl⟩ := ih k hu
      simp [Prod.ext h₁ h₂]

private lemma form_cases (f : Form) : (∃ z, f = .zeros z) ∨ ∃ a p v, f = attach a p v := by
  cases f with
  | zeros z => exact Or.inl ⟨z, rfl⟩
  | peaks z t =>
    right
    suffices ∃ l p v, t = attachTail l p v by
      obtain ⟨l, p, v, rfl⟩ := this
      exact ⟨(z, l), p, v, rfl⟩
    induction t with
    | last p v => exact ⟨[], p, v, rfl⟩
    | more p v t ih =>
      obtain ⟨l, a, b, rfl⟩ := ih
      exact ⟨(p, v) :: l, a, b, rfl⟩

private def weight (a : Prefix) : ℕ := a.1 + (a.2.map (fun x => x.1 + x.2 + 2)).sum

private def goodPrefix (r s : ℕ) (a : Prefix) : Prop :=
  ∀ x ∈ a.2, x.1 + 1 ≤ r ∧ (x.1 + 1) * s ≤ r * (x.2 + 1)

private lemma attach_length (a : Prefix) (p v : ℕ) :
    (attach a p v).word.length = weight a + (p + 1) + v := by
  obtain ⟨z, l⟩ := a
  simp only [attach, Form.word, List.length_append, List.length_replicate, weight]
  induction l with
  | nil => simp [attachTail, Tail.word, Nat.add_assoc]
  | cons x l ih =>
    change z + (Tail.more x.1 x.2 (attachTail l p v)).word.length = _
    simp [Tail.word] at *
    omega

private lemma attach_good (q : Bool) (r s : ℕ) (a : Prefix) (p v : ℕ) :
    (attach a p v).good q r s ↔ goodPrefix r s a ∧ finalOK q r s (p + 1) v := by
  obtain ⟨z, l⟩ := a
  change (attachTail l p v).good q r s ↔ (∀ x ∈ l, _) ∧ _
  induction l with
  | nil => simp [attachTail, Tail.good]
  | cons x l ih =>
    change (Tail.more x.1 x.2 (attachTail l p v)).good q r s ↔ _
    simp [Tail.good, ih, and_assoc]

/- For a final pair of total length z, the ordinary choices for the number of
peaks form an initial interval. The exceptional choice is its largest possible
value, min r z. Give this choice the next index when it is genuinely additional. -/
private def ordinary (r s z : ℕ) : ℕ := min r (r * z / (r + s))

private def capacity (q : Bool) (r s z : ℕ) : ℕ :=
  ordinary r s z + if q = true ∧ ordinary r s z < min r z then 1 else 0

private lemma ordinary_le (r s z : ℕ) : ordinary r s z ≤ min r z := by
  have h : r * z / (r + s) ≤ z := by
    exact Nat.div_le_of_le_mul (by nlinarith : r * z ≤ (r + s) * z)
  unfold ordinary
  omega

private lemma final_iff {q : Bool} {r s p v : ℕ} (hs : 0 < s) :
    finalOK q r s p v ↔
      p ≤ ordinary r s (p + v) ∨ q = true ∧ p = min r (p + v) := by
  unfold ordinary finalOK
  rw [le_min_iff, Nat.le_div_iff_mul_le (by omega)]
  have h : p * (r + s) ≤ r * (p + v) ↔ p * s ≤ r * v := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm p r, Nat.add_le_add_iff_left]
  rw [h]
  cases q <;> simp
  omega

private def select (r s z j : ℕ) : ℕ := if j ≤ ordinary r s z then j else min r z

private lemma selected {q : Bool} {r s z j : ℕ} (hs : 0 < s) (hj : 0 < j)
    (hc : j ≤ capacity q r s z) :
    0 < select r s z j ∧ select r s z j ≤ z ∧
      finalOK q r s (select r s z j) (z - select r s z j) := by
  have hb := ordinary_le r s z
  unfold capacity at hc
  have hz : select r s z j ≤ z := by unfold select; split <;> omega
  rw [final_iff hs, Nat.add_sub_of_le hz]
  unfold select at *
  split_ifs at * <;> grind

private lemma select_inj {q : Bool} {r s z i j : ℕ}
    (hi : i ≤ capacity q r s z) (hj : j ≤ capacity q r s z)
    (h : select r s z i = select r s z j) : i = j := by
  unfold select at h
  unfold capacity at hi hj
  split_ifs at * <;> omega

private lemma select_surj {q : Bool} {r s p v : ℕ} (hs : 0 < s) (hp : 0 < p)
    (h : finalOK q r s p v) :
    ∃ j, 0 < j ∧ j ≤ capacity q r s (p + v) ∧ select r s (p + v) j = p := by
  rw [final_iff hs] at h
  have hb := ordinary_le r s (p + v)
  by_cases ho : p ≤ ordinary r s (p + v)
  · exact ⟨p, hp, by simp [capacity]; omega, by simp [select, ho]⟩
  · refine ⟨ordinary r s (p + v) + 1, by omega, ?_, ?_⟩
    · have ha := h.resolve_left ho
      exact le_of_eq (by rw [capacity, ite_eq_left ⟨ha.1, by omega⟩])
    · simp [select]; omega

private abbrev Codes (r s : ℕ) (count : Prefix → ℕ) :=
  Unit ⊕ (Σ a : {a : Prefix // goodPrefix r s a}, Fin (count a.val))

private noncomputable def codesEquiv (q : Bool) (r s m : ℕ) (hs : 0 < s) :
    Codes r s (fun a => capacity q r s (m - weight a)) ≃ Forms q r s m := by
  let build : Codes r s (fun a => capacity q r s (m - weight a)) → Forms q r s m
    | .inl _ => ⟨.zeros m, by simp [Form.word], trivial⟩
    | .inr ⟨a, i⟩ => by
      let z := m - weight a.val
      let p := select r s z (i.val.succ)
      obtain ⟨hp, hz, ha⟩ := selected hs (Nat.succ_pos i.val) i.isLt
      have he : p - 1 + 1 = p := Nat.sub_add_cancel hp
      refine ⟨attach a.val (p - 1) (z - p), ?_, ?_⟩
      · rw [attach_length, he]
        change p ≤ z at hz
        change 0 < p at hp
        dsimp [z] at *
        omega
      · rw [attach_good, he]
        exact ⟨a.property, ha⟩
  apply Equiv.ofBijective build
  constructor
  · rintro (u | ⟨a, i⟩) (v | ⟨b, j⟩) he
    · have : u = v := Subsingleton.elim ..; simp [this]
    · exact nomatch congrArg Subtype.val he
    · exact nomatch congrArg Subtype.val he
    · obtain ⟨hab, hp, _⟩ := attach_inj (congrArg Subtype.val he)
      obtain rfl : a = b := Subtype.ext hab
      congr 2
      apply Fin.ext
      have hi := selected hs (Nat.succ_pos i.val) i.isLt
      have hj := selected hs (Nat.succ_pos j.val) j.isLt
      dsimp only [build] at hp
      have h := select_inj i.isLt j.isLt (by omega)
      omega
  · rintro ⟨f, hm, hg⟩
    rcases form_cases f with ⟨z, rfl⟩ | ⟨a, p, v, rfl⟩
    · obtain rfl : z = m := by simpa [Form.word] using hm
      exact ⟨.inl (), rfl⟩
    · rw [attach_length] at hm
      rw [attach_good] at hg
      obtain ⟨j, hj, hc, hp⟩ := select_surj hs (Nat.succ_pos p) hg.2
      have hz : m - weight a = p.succ + v := by omega
      let i : Fin (capacity q r s (m - weight a)) := ⟨j - 1, by rw [hz]; omega⟩
      refine ⟨.inr ⟨⟨a, hg.1⟩, i⟩, Subtype.ext ?_⟩
      change attach a (_ - 1) (_ - _) = attach a p v
      have hi : i.val.succ = j := by dsimp [i]; omega
      rw [hi, hz, hp]
      simp

private def shift (r s : ℕ) : ℕ := (s - 1) / r + 1

private lemma shift_lt {r s : ℕ} (hs : 0 < s) : r * shift r s < r + s := by
  have := Nat.mul_div_le (s - 1) r
  unfold shift
  rw [Nat.mul_add, Nat.mul_one]
  omega

private lemma extra_iff {r s z : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ordinary r s z < min r z ↔ 0 < z ∧ z < r + s := by
  have hd : 0 < r + s := by omega
  by_cases h : r + s ≤ z
  · have h' : r ≤ r * z / (r + s) :=
      (Nat.le_div_iff_mul_le hd).2 (Nat.mul_le_mul_left r h)
    simp [ordinary, min_eq_left h', min_eq_left (show r ≤ z by omega), h.not_gt]
  · rcases Nat.eq_zero_or_pos z with rfl | hz
    · simp [ordinary]
    · have h₁ : r * z / (r + s) < r :=
        (Nat.div_lt_iff_lt_mul hd).2 (Nat.mul_lt_mul_of_pos_left (by omega) hr)
      have h₂ : r * z / (r + s) < z :=
        (Nat.div_lt_iff_lt_mul hd).2 (by nlinarith [Nat.mul_pos hs hz])
      simp [ordinary, min_eq_right h₁.le, lt_min_iff, h₁, h₂, hz, Nat.lt_of_not_ge h]

private lemma count_short {r s m : ℕ} (hs : 0 < s) (hm : m ≤ shift r s) :
    capacity false r s m = 0 := by
  have h := (Nat.mul_le_mul_left r hm).trans_lt (shift_lt hs)
  simp [capacity, ordinary, Nat.div_eq_of_lt h]

private lemma shifted_div {r s : ℕ} (hs : 0 < s) (z : ℕ) :
    r * (z + shift r s) / (r + s) = r * z / (r + s) +
      if r + s ≤ r * z % (r + s) + r * shift r s then 1 else 0 := by
  have h := shift_lt (r := r) hs
  rw [Nat.mul_add, Nat.add_div (by omega : 0 < r + s),
    Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Nat.add_zero]

private lemma count_shift {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (z : ℕ) :
    capacity false r s (z + shift r s) ≤ capacity true r s z := by
  simp only [capacity, Bool.false_eq_true, false_and, ite_false, true_and, extra_iff hr hs,
    Nat.add_zero]
  simp only [ordinary, shifted_div hs]
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [(shift_lt (r := r) hs).not_ge]
  · by_cases h : z < r + s
    · simp only [hz, h, and_self, ite_true]
      split <;> omega
    · have hh : r ≤ r * z / (r + s) :=
        (Nat.le_div_iff_mul_le (by omega)).2 (Nat.mul_le_mul_left r (by omega))
      simp [h, min_eq_left hh]

private lemma count_shift_eq {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s)
    (he : s = (s - 1) / r * r + 1) (z : ℕ) :
    capacity false r s (z + shift r s) = capacity true r s z := by
  have hd : r + s = r * shift r s + 1 := by
    unfold shift
    rw [Nat.mul_add, Nat.mul_comm r ((s - 1) / r)]
    omega
  have hcop := (Nat.coprime_self_add_right.mpr hrs).symm
  have hu := count_shift hr hs z
  apply le_antisymm hu
  simp only [capacity, Bool.false_eq_true, false_and, ite_false, true_and, extra_iff hr hs,
    Nat.add_zero]
  simp only [ordinary, shifted_div hs]
  by_cases h : 0 < z ∧ z < r + s
  · have hm : r * z % (r + s) ≠ 0 := by
      intro hm
      have hdvd := hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hm)
      exact h.2.not_ge (Nat.le_of_dvd h.1 hdvd)
    have hc : r * z / (r + s) < r :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (Nat.mul_lt_mul_of_pos_left h.2 hr)
    rw [ite_eq_left h, ite_eq_left (show r + s ≤ r * z % (r + s) + r * shift r s by omega)]
    omega
  · rw [ite_eq_right h]
    split <;> omega

private lemma count_shift_strict {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s)
    (he : s ≠ (s - 1) / r * r + 1) : ∃ z,
    capacity false r s (z + shift r s) < capacity true r s z := by
  have h := shift_lt (r := r) hs
  have hd : 1 + r * shift r s < r + s := by
    unfold shift at *
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm r ((s - 1) / r)] at *
    omega
  obtain ⟨z, hz, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.coprime_self_add_right.mpr hrs) (by omega)
  have hz₀ : 0 < z := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hm
  refine ⟨z, ?_⟩
  simp only [capacity, Bool.false_eq_true, false_and, ite_false, extra_iff hr hs,
    hz₀, hz, and_self, ite_true, Nat.add_zero]
  simp [ordinary, shifted_div hs, hm, hd.not_ge]

private def width (q : Bool) (r s n : ℕ) (a : Prefix) : ℕ :=
  capacity q r s (n - 1 - weight a)

private noncomputable def codePaths (q : Bool) (r s n : ℕ) (hs : 0 < s) :
    Codes r s (width q r s n) ≃ paths q r s n :=
  (codesEquiv q r s (n - 1) hs).trans (pathsEquiv q r s n)

private lemma compare_width {r s : ℕ} (hs : 0 < s) (n : ℕ) (a : Prefix) (rel : ℕ → ℕ → Prop)
    (h₀ : rel 0 0)
    (h : ∀ z, rel (capacity false r s (z + shift r s)) (capacity true r s z)) :
    rel (width false r s (n + shift r s) a) (width true r s n a) := by
  unfold width
  by_cases hw : weight a < n
  · rw [show n + shift r s - 1 - weight a = n - 1 - weight a + shift r s by omega]
    exact h _
  · rw [count_short hs (by omega), show n - 1 - weight a = 0 by omega]
    simpa [capacity, ordinary] using h₀

/- The inclusion of all the smaller fibers into the corresponding larger fibers
is onto whenever the two finite sums are equinumerous. -/
private lemma width_le_of_equiv {r s : ℕ} {f g : Prefix → ℕ} [Finite (Codes r s g)]
    (e : Codes r s f ≃ Codes r s g) (hle : ∀ a, f a ≤ g a)
    (a : {a : Prefix // goodPrefix r s a}) : g a.val ≤ f a.val := by
  let inc : Codes r s f → Codes r s g
    | .inl u => .inl u
    | .inr ⟨b, i⟩ => .inr ⟨b, i.castLE (hle b.val)⟩
  have hi : Function.Injective inc := by
    rintro (u | ⟨b, i⟩) (v | ⟨c, j⟩) h
    · exact congrArg Sum.inl (Subsingleton.elim u v)
    · exact nomatch h
    · exact nomatch h
    · obtain ⟨rfl, h'⟩ := Sigma.mk.inj (Sum.inr.inj h)
      obtain rfl := Fin.castLE_injective (hle b.val) (eq_of_heq h')
      rfl
  have onto := Finite.surjective_of_injective (hi.comp e.symm.injective)
  by_contra! hlt
  let j : Fin (g a.val) := ⟨f a.val, hlt⟩
  obtain ⟨y, hy⟩ := onto (.inr ⟨a, j⟩)
  change inc (e.symm y) = _ at hy
  generalize e.symm y = x at hy
  obtain u | ⟨b, i⟩ := x
  · exact nomatch hy
  · obtain ⟨rfl, hij⟩ := Sigma.mk.inj (Sum.inr.inj hy)
    have hv := congrArg Fin.val (eq_of_heq hij)
    exact (Nat.ne_of_lt i.isLt) hv

private theorem path_criterion {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s) :
    (∀ n, Nonempty (paths false r s (n + shift r s) ≃ paths true r s n)) ↔
      s = (s - 1) / r * r + 1 := by
  constructor
  · intro hall
    by_contra he
    obtain ⟨z, hz⟩ := count_shift_strict hr hs hrs he
    let n := z + 1
    obtain ⟨e⟩ := hall n
    let eqv := (codePaths false r s (n + shift r s) hs).trans
      (e.trans (codePaths true r s n hs).symm)
    let _ := Finite.of_equiv _ (codePaths true r s n hs).symm
    let emptyPrefix : {a : Prefix // goodPrefix r s a} := ⟨(0, []), by simp [goodPrefix]⟩
    have h := width_le_of_equiv eqv
      (fun a => compare_width hs n a (· ≤ ·) (by rfl) (count_shift hr hs)) emptyPrefix
    have hw : weight emptyPrefix.val = 0 := rfl
    simp [width, n, hw] at h
    omega
  · intro he n
    have hw (a : Prefix) := compare_width hs n a (· = ·) rfl (count_shift_eq hr hs hrs he)
    have hcodes : Codes r s (width false r s (n + shift r s)) ≃ Codes r s (width true r s n) :=
      Equiv.cast (congrArg (Codes r s) (funext hw))
    exact ⟨((codePaths false r s (n + shift r s) hs).symm.trans hcodes).trans
      (codePaths true r s n hs)⟩

end forall_nonempty_equiv_qBonacci_tildeRational_iff

open forall_nonempty_equiv_qBonacci_tildeRational_iff in
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
public theorem forall_nonempty_equiv_qBonacci_tildeRational_iff {r s : ℕ} (hr : 0 < r)
    (hs : 0 < s) (hrs : Nat.Coprime r s) :
    (∀ n : ℕ, Nonempty (tildeRationalDyckPaths r s (n + (s - 1) / r + 1) ≃
      qBonacciDyckPaths r s n)) ↔ s = (s - 1) / r * r + 1 := by
  refine Iff.trans (forall_congr' fun n => ?_) (path_criterion hr hs hrs)
  exact iff_of_eq (congrArg (fun m =>
    Nonempty (tildeRationalDyckPaths r s m ≃ qBonacciDyckPaths r s n))
    (Nat.add_assoc n ((s - 1) / r) 1))

end MetaMathlibExt
