/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Permutation Wordle

Statements from Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer
Sequences 29 (2026), Article 26.1.7 (arXiv:2506.23452).

A guesser tries to find a secret permutation `π` of `Fin n`. The first guess is the identity;
after each guess the set of incorrect positions `I` is revealed, the correct positions are
locked, and the next guess permutes the entries on `I` by the strategy component `S |I|`: with
`I = {i₀ < i₁ < ⋯ < i_{m-1}}`, the entry at `i_j` moves to `i_{S m j}`. Positions are zero-based,
so the paper's one-line component `[2, 3, …, m, 1]` (cyclic shift) is `finRotate m`, and the
paper's guess `γ_{r+1}` is `permWordleGuess S π r`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Permuting the entries of a map along a set of positions.** Let $I$ be a subset of
$\{0, \dots, n-1\}$ with $k$ elements, listed in increasing order as
$i_0 < i_1 < \dots < i_{k-1}$, let $\sigma$ be a permutation of $\{0, \dots, k-1\}$, and let $g$
be a map from $\{0, \dots, n-1\}$ to itself. Applying $\sigma$ to $g$ along $I$ gives the map that
takes the value $g(i_j)$ at $i_{\sigma(j)}$ for every $j < k$ and agrees with $g$ outside $I$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2 (the action of a strategy component on `𝓘_r`). -/
def permuteAlong {n k : ℕ} (I : Finset (Fin n)) (h : I.card = k) (σ : Equiv.Perm (Fin k))
    (g : Fin n → Fin n) : Fin n → Fin n :=
  fun i => if hi : i ∈ I then g (I.orderIsoOfFin h (σ.symm ((I.orderIsoOfFin h).symm ⟨i, hi⟩))).1
    else g i

/-- **Permuting along all positions.** Let $\sigma$ be a permutation of $\{0, \dots, n-1\}$ and
let $g$ be a map from $\{0, \dots, n-1\}$ to itself. Applying $\sigma$ to the entries of $g$
along the set of all positions $\{0, \dots, n-1\}$, listed in increasing order, gives the map
$g \circ \sigma^{-1}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Proposition 4 (`γ₂ = S[n]⁻¹`). -/
theorem permuteAlong_univ {n : ℕ} (h : (Finset.univ : Finset (Fin n)).card = n)
    (σ : Equiv.Perm (Fin n)) (g : Fin n → Fin n) :
    permuteAlong Finset.univ h σ g = g ∘ σ.symm := by
  have he : ∀ k, ((Finset.univ : Finset (Fin n)).orderIsoOfFin h k).1 = k := fun k =>
    (congrFun (Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin n))) h
      (f := id) (fun x => Finset.mem_univ _) strictMono_id) k).symm
  funext i
  have hs : ((Finset.univ : Finset (Fin n)).orderIsoOfFin h).symm ⟨i, Finset.mem_univ i⟩ = i := by
    apply ((Finset.univ : Finset (Fin n)).orderIsoOfFin h).injective
    ext; simp [he]
  simp [permuteAlong, hs, he]

/-- **One round of permutation Wordle.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of $\{0, \dots, n-1\}$ (the
secret), and let $g$ be a map from $\{0, \dots, n-1\}$ to itself (the current guess). Let $I$ be
the set of incorrect positions, the $k$ with $g(k) \ne \pi(k)$, and let $m$ be the number of
elements of $I$. The next guess agrees with $g$ at every position outside $I$ and permutes the
entries of $g$ on $I$ by $S_m$: writing $I = \{i_0 < i_1 < \dots < i_{m-1}\}$, it takes the value
$g(i_j)$ at $i_{S_m(j)}$ for every $j < m$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def permWordleNextGuess {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n))
    (g : Fin n → Fin n) : Fin n → Fin n :=
  permuteAlong (Finset.univ.filter fun k => g k ≠ π k) rfl (S _) g

/-- **Correct positions stay locked.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of $\{0, \dots, n-1\}$, and let
$g$ be a map from $\{0, \dots, n-1\}$ to itself. If $g(i) = \pi(i)$ at a position $i$, then the
guess that one round of permutation Wordle with strategy $S$ and secret $\pi$ produces from $g$
also takes the value $g(i)$ at $i$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem permWordleNextGuess_of_eq {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (g : Fin n → Fin n) (i : Fin n) (h : g i = π i) :
    permWordleNextGuess S π g i = g i := by
  simp [permWordleNextGuess, permuteAlong, h]

/-- **Guesses of permutation Wordle.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, and let $\pi$ be a permutation of $\{0, \dots, n-1\}$. The
guesses $\gamma_1, \gamma_2, \dots$ of permutation Wordle with strategy $S$ and secret $\pi$ are
the maps from $\{0, \dots, n-1\}$ to itself defined recursively: $\gamma_1$ is the identity, and
$\gamma_{r+1}$ is the guess that one round of the game with strategy $S$ and secret $\pi$
produces from $\gamma_r$. The sequence is indexed from $0$: its term at index $r$ is
$\gamma_{r+1}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def permWordleGuess {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n)) :
    ℕ → Fin n → Fin n
  | 0 => id
  | r + 1 => permWordleNextGuess S π (permWordleGuess S π r)

/-- **Recurrence for the guesses of permutation Wordle.** Let $S$ be a strategy, that is, a
permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of
$\{0, \dots, n-1\}$, and let $\gamma_1, \gamma_2, \dots$ be the guesses of permutation Wordle with
strategy $S$ and secret $\pi$. For every $r \ge 1$, the guess $\gamma_{r+1}$ is the guess that one
round of the game with strategy $S$ and secret $\pi$ produces from $\gamma_r$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem permWordleGuess_succ {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (r : ℕ) :
    permWordleGuess S π (r + 1) = permWordleNextGuess S π (permWordleGuess S π r) :=
  rfl

/-- **The second guess against a derangement.** Let $S$ be a strategy for permutation Wordle,
that is, a permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, and let $\pi$ be a permutation
of $\{0, \dots, n-1\}$ with no fixed point. Then the second guess $\gamma_2$ of permutation Wordle
with strategy $S$ and secret $\pi$ is the inverse permutation $S_n^{-1}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Proposition 4. -/
theorem permWordleGuess_one_of_forall_ne {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (hπ : ∀ k, π k ≠ k) :
    permWordleGuess S π 1 = ⇑(S n).symm := by
  have key : ∀ (I : Finset (Fin n)) (hI : I = Finset.univ),
      permuteAlong I rfl (S I.card) id = ⇑(S n).symm := by
    intro I hI
    subst hI
    have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
    have gen : ∀ (k : ℕ) (hk : (Finset.univ : Finset (Fin n)).card = k) (hkn : k = n),
        permuteAlong Finset.univ hk (S k) id = ⇑(S n).symm := by
      intro k hk hkn
      subst hkn
      rw [permuteAlong_univ]; rfl
    exact gen _ rfl hc
  exact key _ (Finset.eq_univ_of_forall fun k =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (hπ k).symm⟩)

/-- **Permutation Wordle games solved in a given number of guesses.** Let $S$ be a strategy, that
is, a permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of
$\{0, \dots, n-1\}$, and let $\gamma_1, \gamma_2, \dots$ be the guesses of permutation Wordle with
strategy $S$ and secret $\pi$. For a natural number $r$, the game ends after exactly $r$ guesses
when $r \ge 1$, $\gamma_r = \pi$, and $\gamma_j \ne \pi$ for every $j$ with $1 \le j < r$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
def PermWordleSolvedIn {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n))
    (r : ℕ) : Prop :=
  1 ≤ r ∧ permWordleGuess S π (r - 1) = ⇑π ∧ ∀ j < r - 1, permWordleGuess S π j ≠ ⇑π

/-- **Games won with the first guess.** Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, and let $\pi$ be a permutation of $\{0, \dots, n-1\}$. Then
permutation Wordle with strategy $S$ and secret $\pi$ ends after exactly one guess if and only if
$\pi$ is the identity.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Theorem 5. -/
theorem permWordleSolvedIn_one_iff {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) : PermWordleSolvedIn S π 1 ↔ π = 1 := by
  simp only [PermWordleSolvedIn, le_refl, Nat.sub_self, permWordleGuess, Nat.not_lt_zero,
    IsEmpty.forall_iff, implies_true, and_true, true_and]
  constructor
  · intro h; ext i; simp [← h]
  · rintro rfl; rfl

/-- **Coefficients of the guess-count generating function.** For a strategy $S$ and natural
numbers $n$ and $r$, the coefficient $[x^r] f_S(x)$ of the generating function of $S$ at length
$n$ is the number of secret permutations of $\{0, \dots, n-1\}$ that $S$ guesses in exactly $r$
guesses.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
noncomputable def permWordleCoeff (S : (m : ℕ) → Equiv.Perm (Fin m)) (n r : ℕ) : ℕ :=
  Nat.card {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π r}

/-- **No permutation is guessed in zero guesses.** For every strategy $S$ and every $n$, write
$f_S$ for the generating function whose coefficient $[x^r] f_S$ is the number of permutations of
$\{0, \dots, n-1\}$ that $S$ guesses in exactly $r$ guesses. Then the constant coefficient
$[x^0] f_S$ vanishes.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
theorem permWordleCoeff_zero (S : (m : ℕ) → Equiv.Perm (Fin m)) (n : ℕ) :
    permWordleCoeff S n 0 = 0 := by
  have : IsEmpty {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π 0} :=
    ⟨fun π => absurd π.2.1 (by norm_num)⟩
  simp [permWordleCoeff]

/-- **First guess with a correct position in permutation Wordle.** Let $S$ be a strategy, that
is, a permutation $S_m$ of $\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of
$\{0, \dots, n-1\}$, and let $\gamma_1, \gamma_2, \dots$ be the guesses of permutation Wordle with
strategy $S$ and secret $\pi$. For a natural number $r$, $\rho_S(\pi) = r$ means that $r \ge 1$,
that $\gamma_r(k) = \pi(k)$ for some position $k$, and that for every $j$ with $1 \le j < r$ there
is no position $k$ with $\gamma_j(k) = \pi(k)$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.2. -/
def PermWordleFirstCorrectAt {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  1 ≤ r ∧ (∃ k, permWordleGuess S π (r - 1) k = π k) ∧
    ∀ j < r - 1, ∀ k, permWordleGuess S π j k ≠ π k

/-- **Permutations with a correct entry in the first guess.** For $n \in \mathbb{N}$, a strategy
$S$ and a permutation $\pi$ of $\{0, \dots, n-1\}$, write $\rho_S(\pi) = r$ when the $r$-th guess
is the first guess with a correct position for the secret $\pi$. Then $\rho_S(\pi) = 1$, that is,
the first guess (the identity) already has a correct position, exactly when $\pi$ has a fixed
point.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Theorem 10. -/
theorem permWordleFirstCorrectAt_one_iff {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) : PermWordleFirstCorrectAt S π 1 ↔ ∃ k, π k = k := by
  simp only [PermWordleFirstCorrectAt, le_refl, Nat.sub_self, permWordleGuess, id,
    Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true, true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- **Cyclic shift strategy.** A strategy assigns to each $m$ a permutation of $m$ positions, used
to rearrange the entries on the $m$ incorrect positions of a guess. The cyclic shift strategy
$\mathrm{CS}$ has component $\mathrm{CS}[m] = [2, 3, \dots, m, 1]$ in one-line notation, that is,
the rotation $i \mapsto i + 1 \pmod m$ of $\{0, 1, \dots, m-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def cyclicShiftStrategy : (m : ℕ) → Equiv.Perm (Fin m) :=
  fun m => finRotate m

/-- **Components of the cyclic shift strategy.** For every $m$, the component of the cyclic shift
strategy on $m$ positions is the rotation $i \mapsto i + 1 \pmod m$ of $\{0, 1, \dots, m-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem cyclicShiftStrategy_apply (m : ℕ) : cyclicShiftStrategy m = finRotate m :=
  rfl

/-- **Cyclic shift left strategy.** For $n \in \mathbb{N}$, the strategy $\mathrm{CSL}_n$ assigns
to each $m$ a permutation of $m$ positions: for $m = n$ the left cyclic shift
$[m, 1, 2, \dots, m-1]$ in one-line notation, that is, $i \mapsto i - 1 \pmod m$, and for every
$m \ne n$ the right cyclic shift $[2, 3, \dots, m, 1]$, that is, $i \mapsto i + 1 \pmod m$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
def cyclicShiftLeftStrategy (n : ℕ) : (m : ℕ) → Equiv.Perm (Fin m) :=
  fun m => if m = n then (finRotate m).symm else finRotate m

/-- **Top component of the left-shift strategy.** For every $n$, the component on $n$ positions
of the left-shift strategy $\mathrm{CSL}_n$ is the left cyclic shift $j \mapsto j - 1 \bmod n$
of $\{0, \dots, n-1\}$, the inverse of the cyclic shift $j \mapsto j + 1 \bmod n$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
theorem cyclicShiftLeftStrategy_self (n : ℕ) :
    cyclicShiftLeftStrategy n n = (finRotate n).symm := by
  simp [cyclicShiftLeftStrategy]

/-- **Non-top components of the left-shift strategy.** For all $n$ and $m$ with $m \ne n$, the
component on $m$ positions of the left-shift strategy $\mathrm{CSL}_n$ is the cyclic shift
$j \mapsto j + 1 \bmod m$ of $\{0, \dots, m-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
theorem cyclicShiftLeftStrategy_of_ne {n m : ℕ} (h : m ≠ n) :
    cyclicShiftLeftStrategy n m = finRotate m := by
  simp [cyclicShiftLeftStrategy, h]

/-- **Inductive strategy.** A strategy $S$ (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each
$m$) is inductive of length $n$ when $S[m]$ is the rotation $i \mapsto i + 1 \pmod m$ for every
$m < n$, and $S[n]$ is an $n$-cycle, that is, a single cycle moving every element of
$\{0, \dots, n-1\}$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 3.1. -/
def IsInductivePermWordleStrategy (n : ℕ) (S : (m : ℕ) → Equiv.Perm (Fin m)) : Prop :=
  (∀ m < n, S m = finRotate m) ∧ (S n).IsCycle ∧ (S n).support = Finset.univ

/-- **Average number of correct positions in the second guess.** Let $n \ge 2$ and let $S$ be a
permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) whose
component $S[n]$ has no fixed point. For a secret permutation $\pi$ of $\{0, \dots, n-1\}$ let
$\gamma_2$ be the second guess of $S$. The sum, over all derangements $\pi$ of
$\{0, \dots, n-1\}$, of the number of positions $i$ with $\gamma_2(i) = \pi(i)$, divided by the
number of derangements of $\{0, \dots, n-1\}$, equals $n/(n-1)$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Proposition 4 (`jis-2026-26.1.7-prop-4`). -/
public theorem_wanted avg_card_correct_second_guess_derangements (n : ℕ) (hn : 2 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ k, S n k ≠ k) :
    (∑ d ∈ Finset.univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k),
        ((Finset.univ.filter fun i => permWordleGuess S d 1 i = d i).card : ℚ)) /
      (Finset.univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k)).card =
      (n : ℚ) / (n - 1)

/-- **One- and two-guess counts for deranged strategies.** Let $n \in \mathbb{N}$ and let $S$ be
a strategy whose component $S[m]$ has no fixed point for every $2 \le m \le n$, and write
$[x^r] f_S$ for the number of permutations of $\{0, \dots, n-1\}$ that $S$ guesses in exactly $r$
guesses. Then $[x^1] f_S = 1$ and $[x^2] f_S = 2^n - n - 1$, the Eulerian number $A(n, 1)$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 5 (`jis-2026-26.1.7-thm-5`). -/
public theorem_wanted permWordleCoeff_one_and_two (n : ℕ) (S : (m : ℕ) → Equiv.Perm (Fin m))
    (hS : ∀ m, 2 ≤ m → m ≤ n → ∀ k : Fin m, S m k ≠ k) :
    permWordleCoeff S n 1 = 1 ∧ permWordleCoeff S n 2 = 2 ^ n - n - 1

/-- **Cyclic shift maximizes three-guess solves among inductive strategies.** Let $n \ge 4$ and let
$S$ be an inductive strategy of length $n$ whose component $S[n]$ is not the rotation
$i \mapsto i + 1 \pmod n$. Then strictly fewer permutations of $\{0, \dots, n-1\}$ are guessed in
exactly three guesses with $S$ than with the cyclic shift strategy.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 7 (`jis-2026-26.1.7-thm-7`). -/
public theorem_wanted permWordleCoeff_three_lt_cyclicShift (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ finRotate n) :
    permWordleCoeff S n 3 < permWordleCoeff cyclicShiftStrategy n 3

/-- **Derangements solved in three guesses by cyclic shift.** For $n \ge 3$, exactly
$2^n - (2n + 1)$ derangements $\pi$ of $\{0, \dots, n-1\}$ are guessed by the cyclic shift
strategy in exactly three guesses.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Lemma 9 (`jis-2026-26.1.7-lem-9`). -/
public theorem_wanted card_derangements_solvedIn_three_cyclicShift (n : ℕ) (hn : 3 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      (∀ k, π k ≠ k) ∧ PermWordleSolvedIn cyclicShiftStrategy π 3} = 2 ^ n - (2 * n + 1)

/-- **Three-guess solves of permutations with a fixed point.** Let $n \ge 4$ and let $S$ be a
permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) with
$S[m]$ equal to the cyclic shift $j \mapsto j + 1 \bmod m$ for every $m < n$. The number of
permutations $\pi$ of $\{0, \dots, n-1\}$ that $S$ guesses in exactly three guesses and whose
first guess (the identity) has a correct position, that is, $\pi$ has a fixed point, is
$1 - 2^{n+1} + 3^n + n^2/2 + 5n/2 - n \cdot 2^n$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 10 (`jis-2026-26.1.7-thm-10`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_one (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ m < n, S m = finRotate m) :
    (Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 1} : ℚ) =
      1 - 2 ^ (n + 1) + 3 ^ n + (n : ℚ) ^ 2 / 2 + 5 * (n : ℚ) / 2 - n * 2 ^ n

/-- **A unique three-guess solve with no early correct position.** Let $n \ge 4$ and let $S$ be
a permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) whose
component $S[n]$ is an $n$-cycle. Exactly one permutation $\pi$ of $\{0, \dots, n-1\}$ is
guessed by $S$ in exactly three guesses with the third guess being the first guess that has a
correct position.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 11 (`jis-2026-26.1.7-thm-11`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_three (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hcyc : (S n).IsCycle)
    (hsupp : (S n).support = Finset.univ) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 3} = 1

/-- **Three-guess solves of cyclic shift first correct at guess two.** For $n \ge 4$, the number
of permutations $\pi$ of $\{0, \dots, n-1\}$ that the cyclic shift strategy guesses in exactly
three guesses, with the second guess being the first guess that has a correct position, is
$2^n - 2n - 2$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 12 (`jis-2026-26.1.7-thm-12`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_two_cyclicShift (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn cyclicShiftStrategy π 3 ∧
        PermWordleFirstCorrectAt cyclicShiftStrategy π 2} = 2 ^ n - 2 * n - 2

/-- **Upper bound on three-guess solves first correct at guess two.** Let $n \ge 4$ and let $S$
be an inductive strategy of length $n$ whose component $S[n]$ is not the cyclic shift
$j \mapsto j + 1 \bmod n$ of $\{0, \dots, n-1\}$. Then fewer than $2^n - 2n - 2$ permutations
$\pi$ of $\{0, \dots, n-1\}$ are guessed by $S$ in exactly three guesses with the second guess
being the first guess that has a correct position.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 13 (`jis-2026-26.1.7-thm-13`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_two_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ finRotate n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 2} < 2 ^ n - 2 * n - 2

/-- **Cyclic shift left minimizes three-guess solves among inductive strategies.** Let $n \ge 4$
and let $S$ be an inductive strategy of length $n$ whose component $S[n]$ is not the left cyclic
shift $i \mapsto i - 1 \pmod n$. Then strictly fewer permutations of $\{0, \dots, n-1\}$ are
guessed in exactly three guesses with the cyclic shift left strategy $\mathrm{CSL}_n$ than with
$S$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 14 (`jis-2026-26.1.7-thm-14`). -/
public theorem_wanted permWordleCoeff_three_cyclicShiftLeft_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ (finRotate n).symm) :
    permWordleCoeff (cyclicShiftLeftStrategy n) n 3 < permWordleCoeff S n 3

/-- **Lucas-number count for the left-shift strategy.** Let $n \ge 4$ and let $\mathrm{CSL}_n$
be the strategy whose component on $n$ positions is the left cyclic shift
$j \mapsto j - 1 \bmod n$ and whose component on $m \ne n$ positions is the cyclic shift
$j \mapsto j + 1 \bmod m$. The number of permutations $\pi$ of $\{0, \dots, n-1\}$ that
$\mathrm{CSL}_n$ guesses in exactly three guesses, with the second guess being the first guess
that has a correct position, is $L_n - n - 1$, where $L_n$ is the $n$-th Lucas number
($L_0 = 2$, $L_1 = 1$, $L_{k+2} = L_{k+1} + L_k$).

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 15 (`jis-2026-26.1.7-thm-15`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_two_cyclicShiftLeft (n : ℕ)
    (hn : 4 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn (cyclicShiftLeftStrategy n) π 3 ∧
        PermWordleFirstCorrectAt (cyclicShiftLeftStrategy n) π 2} = lucasNumber n - n - 1

/-- **Among inductive strategies, cyclic shift left minimizes three-guess solves first correct at
guess two.** Let $n \ge 4$ and let $S$ be an inductive strategy of length $n$ whose component
$S[n]$ is not the left cyclic shift $i \mapsto i - 1 \pmod n$ of $\{0, \dots, n-1\}$. Let
$\mathrm{CSL}_n$ be the cyclic shift left strategy, whose component on $n$ positions is the left
cyclic shift and whose component on $m \ne n$ positions is the rotation $i \mapsto i + 1 \pmod m$.
Then the number of permutations $\pi$ of $\{0, \dots, n-1\}$ that $\mathrm{CSL}_n$ guesses in
exactly three guesses, with the second guess being the first guess that has a correct position,
is strictly smaller than the number of permutations $\pi$ that $S$ guesses in exactly three
guesses with the second guess being the first guess that has a correct position.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 16 (`jis-2026-26.1.7-thm-16`). -/
public theorem_wanted card_firstCorrectAt_two_cyclicShiftLeft_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ (finRotate n).symm) :
    Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn (cyclicShiftLeftStrategy n) π 3 ∧
          PermWordleFirstCorrectAt (cyclicShiftLeftStrategy n) π 2} <
      Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 2}

end

end MetaMathlibExt
