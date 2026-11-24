/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Logic.Equiv.Defs

/-!
# Rational Dyck paths and `Q`-bonacci paths

This module proves the shifted bijection between the two path families studied by
Barcucci, Bernini, Bilotta, and Pinzani in *Rational Dyck Paths*,
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

end MetaMathlibExt
