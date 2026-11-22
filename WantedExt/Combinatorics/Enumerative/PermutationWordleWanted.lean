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

/-- Apply `σ : Equiv.Perm (Fin k)` to the entries of `g` on the positions in `I`, listed in
increasing order (`I.card = k`): the entry at the `j`-th position of `I` moves to the
`σ j`-th position of `I`; positions outside `I` are unchanged.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2 (the action of a strategy component on `𝓘_r`). -/
def permuteAlong {n k : ℕ} (I : Finset (Fin n)) (h : I.card = k) (σ : Equiv.Perm (Fin k))
    (g : Fin n → Fin n) : Fin n → Fin n :=
  fun i => if hi : i ∈ I then g (I.orderIsoOfFin h (σ.symm ((I.orderIsoOfFin h).symm ⟨i, hi⟩))).1
    else g i

/-- On all of `Fin n` (enumerated in its natural order), `permuteAlong` is precomposition with
`σ⁻¹`.

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

/-- One round of permutation Wordle with strategy `S` (component `S m` acts on `m` incorrect
positions) and secret `π`: from the current guess `g`, keep the positions where `g` agrees with
`π` and permute the remaining positions by `S |𝓘|` via `permuteAlong`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def permWordleNextGuess {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n))
    (g : Fin n → Fin n) : Fin n → Fin n :=
  permuteAlong (Finset.univ.filter fun k => g k ≠ π k) rfl (S _) g

/-- Correct positions are locked: a round never changes an entry that already agrees with the
secret.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem permWordleNextGuess_of_eq {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (g : Fin n → Fin n) (i : Fin n) (h : g i = π i) :
    permWordleNextGuess S π g i = g i := by
  simp [permWordleNextGuess, permuteAlong, h]

/-- The guess sequence of permutation Wordle: `permWordleGuess S π r` is the paper's
`γ_{r+1}`; the first guess `γ₁` is the identity.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def permWordleGuess {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n)) :
    ℕ → Fin n → Fin n
  | 0 => id
  | r + 1 => permWordleNextGuess S π (permWordleGuess S π r)

/-- The recurrence of the guess sequence.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem permWordleGuess_succ {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (r : ℕ) :
    permWordleGuess S π (r + 1) = permWordleNextGuess S π (permWordleGuess S π r) :=
  rfl

/-- For a derangement secret, the second guess is `S[n]⁻¹`.

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

/-- The game with secret `π` ends after exactly `r` guesses: `γ_r = π` and `γ_j ≠ π` for
`1 ≤ j < r`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
def PermWordleSolvedIn {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin n))
    (r : ℕ) : Prop :=
  1 ≤ r ∧ permWordleGuess S π (r - 1) = ⇑π ∧ ∀ j < r - 1, permWordleGuess S π j ≠ ⇑π

/-- Only the identity is guessed in one guess.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Theorem 5. -/
theorem permWordleSolvedIn_one_iff {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) : PermWordleSolvedIn S π 1 ↔ π = 1 := by
  simp only [PermWordleSolvedIn, le_refl, Nat.sub_self, permWordleGuess, Nat.not_lt_zero,
    IsEmpty.forall_iff, implies_true, and_true, true_and]
  constructor
  · intro h; ext i; simp [← h]
  · rintro rfl; rfl

/-- The coefficient `[x^r] f_S(x)` of the paper's generating function of a strategy `S` of
length `n`: the number of secret permutations of `Fin n` guessed in exactly `r` guesses.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
noncomputable def permWordleCoeff (S : (m : ℕ) → Equiv.Perm (Fin m)) (n r : ℕ) : ℕ :=
  Nat.card {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π r}

/-- The constant coefficient of `f_S` vanishes.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4. -/
theorem permWordleCoeff_zero (S : (m : ℕ) → Equiv.Perm (Fin m)) (n : ℕ) :
    permWordleCoeff S n 0 = 0 := by
  have : IsEmpty {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π 0} :=
    ⟨fun π => absurd π.2.1 (by norm_num)⟩
  simp [permWordleCoeff]

/-- The paper's `ρ_S(π) = r`: guess `γ_r` is the first guess with a correct position.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.2. -/
def PermWordleFirstCorrectAt {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  1 ≤ r ∧ (∃ k, permWordleGuess S π (r - 1) k = π k) ∧
    ∀ j < r - 1, ∀ k, permWordleGuess S π j k ≠ π k

/-- `ρ_S(π) = 1` exactly when `π` has a fixed point.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, proof of Theorem 10. -/
theorem permWordleFirstCorrectAt_one_iff {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin n)) : PermWordleFirstCorrectAt S π 1 ↔ ∃ k, π k = k := by
  simp only [PermWordleFirstCorrectAt, le_refl, Nat.sub_self, permWordleGuess, id,
    Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true, true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- The cyclic shift strategy `CS`, with components `CS[m] = [2, 3, …, m, 1]`, i.e.
`finRotate m`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
def cyclicShiftStrategy : (m : ℕ) → Equiv.Perm (Fin m) :=
  fun m => finRotate m

/-- Every component of `CS` is `finRotate`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 2. -/
theorem cyclicShiftStrategy_apply (m : ℕ) : cyclicShiftStrategy m = finRotate m :=
  rfl

/-- The inductive strategy `CSL` of length `n`: left shift `[n, 1, 2, …, n-1]` on `n`
incorrect positions and right cyclic shift on fewer.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
def cyclicShiftLeftStrategy (n : ℕ) : (m : ℕ) → Equiv.Perm (Fin m) :=
  fun m => if m = n then (finRotate m).symm else finRotate m

/-- The top component of `CSL` is the left shift.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
theorem cyclicShiftLeftStrategy_self (n : ℕ) :
    cyclicShiftLeftStrategy n n = (finRotate n).symm := by
  simp [cyclicShiftLeftStrategy]

/-- The lower components of `CSL` are right cyclic shifts.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 4.3. -/
theorem cyclicShiftLeftStrategy_of_ne {n m : ℕ} (h : m ≠ n) :
    cyclicShiftLeftStrategy n m = finRotate m := by
  simp [cyclicShiftLeftStrategy, h]

/-- An inductive strategy of length `n`: `S[m] = CS[m]` for `m < n` and `S[n]` an `n`-cycle.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Section 3.1. -/
def IsInductivePermWordleStrategy (n : ℕ) (S : (m : ℕ) → Equiv.Perm (Fin m)) : Prop :=
  (∀ m < n, S m = finRotate m) ∧ (S n).IsCycle ∧ (S n).support = Finset.univ

/-- **Proposition 4.** For a deranged strategy component `S[n]` (`n ≥ 2`), the average number
of correct positions in the second guess, over all derangement secrets of length `n`, is
`n / (n - 1)`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Proposition 4 (`jis-2026-26.1.7-prop-4`). -/
public theorem_wanted avg_card_correct_second_guess_derangements (n : ℕ) (hn : 2 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ k, S n k ≠ k) :
    (∑ d ∈ Finset.univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k),
        ((Finset.univ.filter fun i => permWordleGuess S d 1 i = d i).card : ℚ)) /
      (Finset.univ.filter (fun d : Equiv.Perm (Fin n) => ∀ k, d k ≠ k)).card =
      (n : ℚ) / (n - 1)

/-- **Theorem 5.** For every deranged strategy `S` of length `n` (each component `S m`,
`2 ≤ m ≤ n`, fixed-point-free), `[x¹] f_S = 1` and `[x²] f_S = A(n, 1) = 2ⁿ - n - 1`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 5 (`jis-2026-26.1.7-thm-5`). -/
public theorem_wanted permWordleCoeff_one_and_two (n : ℕ) (S : (m : ℕ) → Equiv.Perm (Fin m))
    (hS : ∀ m, 2 ≤ m → m ≤ n → ∀ k : Fin m, S m k ≠ k) :
    permWordleCoeff S n 1 = 1 ∧ permWordleCoeff S n 2 = 2 ^ n - n - 1

/-- **Theorem 7.** For `n ≥ 4`, cyclic shift guesses strictly more permutations in exactly three
guesses than any other inductive strategy.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 7 (`jis-2026-26.1.7-thm-7`). -/
public theorem_wanted permWordleCoeff_three_lt_cyclicShift (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ finRotate n) :
    permWordleCoeff S n 3 < permWordleCoeff cyclicShiftStrategy n 3

/-- **Lemma 9.** For `n ≥ 3`, exactly `2ⁿ - (2n + 1)` derangements of length `n` are guessed by
cyclic shift in exactly three guesses.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Lemma 9 (`jis-2026-26.1.7-lem-9`). -/
public theorem_wanted card_derangements_solvedIn_three_cyclicShift (n : ℕ) (hn : 3 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      (∀ k, π k ≠ k) ∧ PermWordleSolvedIn cyclicShiftStrategy π 3} = 2 ^ n - (2 * n + 1)

/-- **Theorem 10.** If `S[m] = CS[m]` for all `m < n` and `n ≥ 4`, the number of permutations
guessed in exactly three guesses with `ρ_S(π) = 1` is
`1 - 2^{n+1} + 3ⁿ + n²/2 + 5n/2 - n 2ⁿ`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 10 (`jis-2026-26.1.7-thm-10`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_one (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ m < n, S m = finRotate m) :
    (Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 1} : ℚ) =
      1 - 2 ^ (n + 1) + 3 ^ n + (n : ℚ) ^ 2 / 2 + 5 * (n : ℚ) / 2 - n * 2 ^ n

/-- **Theorem 11.** If `S[n]` is an `n`-cycle and `n ≥ 4`, exactly one permutation is guessed
in exactly three guesses with `ρ_S(π) = 3`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 11 (`jis-2026-26.1.7-thm-11`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_three (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hcyc : (S n).IsCycle)
    (hsupp : (S n).support = Finset.univ) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 3} = 1

/-- **Theorem 12.** For cyclic shift and `n ≥ 4`, the number of permutations guessed in exactly
three guesses with `ρ_CS(π) = 2` is `2ⁿ - 2n - 2`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 12 (`jis-2026-26.1.7-thm-12`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_two_cyclicShift (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn cyclicShiftStrategy π 3 ∧
        PermWordleFirstCorrectAt cyclicShiftStrategy π 2} = 2 ^ n - 2 * n - 2

/-- **Theorem 13.** For an inductive strategy `S ≠ CS` of length `n ≥ 4`, fewer than
`2ⁿ - 2n - 2` permutations are guessed in exactly three guesses with `ρ_S(π) = 2`.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 13 (`jis-2026-26.1.7-thm-13`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_two_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ finRotate n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 2} < 2 ^ n - 2 * n - 2

/-- **Theorem 14.** For `n ≥ 4`, `CSL` guesses strictly fewer permutations in exactly three
guesses than any other inductive strategy.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 14 (`jis-2026-26.1.7-thm-14`). -/
public theorem_wanted permWordleCoeff_three_cyclicShiftLeft_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ (finRotate n).symm) :
    permWordleCoeff (cyclicShiftLeftStrategy n) n 3 < permWordleCoeff S n 3

/-- **Theorem 15.** For `CSL` of length `n ≥ 4`, the number of permutations guessed in exactly
three guesses with `ρ_CSL(π) = 2` is `L_n - n - 1`, `L_n` the `n`-th Lucas number.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 15 (`jis-2026-26.1.7-thm-15`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_two_cyclicShiftLeft (n : ℕ)
    (hn : 4 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn (cyclicShiftLeftStrategy n) π 3 ∧
        PermWordleFirstCorrectAt (cyclicShiftLeftStrategy n) π 2} = lucasNumber n - n - 1

/-- **Theorem 16.** For an inductive strategy `S ≠ CSL` of length `n ≥ 4`, strictly more
permutations are guessed in exactly three guesses with `ρ_S(π) = 2` than with `CSL`.

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
