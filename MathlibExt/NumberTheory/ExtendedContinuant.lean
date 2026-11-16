/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Extended continuants

Results from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73.

For a bi-infinite integer sequence `x : ℤ → ℤ`, `extendedContinuant x a b` is
the paper's extended continuant `K_a(x)_b^{a+b}` of order `a ∈ ℤ` on the
consecutive terms starting at index `b` (Definitions 3 and 4, right-adjusting
recurrence): `K_{-2} = 0`, `K_{-1} = 1`, and `K_a = x_{b+a} K_{a-1} + K_{a-2}`
for every integer order `a` (`extendedContinuant_recurrence`). For `a ≥ 0` it
is the classical continuant of `x_b, …, x_{b+a}`.

In Sections 4–6 a bi-infinite sequence `x` has raw rational convergents
`k_n = K_n(x)_0 / K_{n-1}(x)_1` (numerator and denominator kept separately);
`c_i` and `d_i` are the raw convergents `K_i(y)_0 / K_{i-1}(y)_1` and
`K_i(z)_0 / K_{i-1}(z)_1` of the eastbound SCF terms `y` of `α` and `z` of `ᾱ`.
Strict equivalence of raw rationals is equality of numerators and of
denominators. The statements keep only the strict-equivalence hypotheses on the
convergents; the periodicity and limit conditions of a BpCF (Definition 5) are
dropped, so each statement applies to every bi-infinite integer sequence.

## Proof outline

* Write `P(i, n) = K_{n-i-2}(x)_i`, the continuant of `x_i, …, x_{n-2}`. For
  every `i`, `n ↦ P(i, n)` satisfies `P(i, n) = x_{n-2} P(i, n-1) + P(i, n-2)`,
  so the Casoratian `P(i, n) P(j, n-1) - P(i, n-1) P(j, n)` changes sign with
  `n`; at `n = j + 1` it is `-P(i, j)` (`extendedContinuant_casoratian`).
* Exchanging `i` and `j` in the Casoratian gives the reflection formula
  `extendedContinuant_reflect`, which is Theorem 1. Taking `i = b`, `j = b + 1`
  gives Corollary 2 at any start index (`extendedContinuant_det_start`).
  Reflection and the right-adjusting recurrence give the left-adjusting one
  (`extendedContinuant_left_recurrence`).
* Three solutions of the same recurrence are linearly dependent, with their
  Casoratians as coefficients; for `P(k, ·)`, `P(ℓ, ·)`, `P(m, ·)` this is
  Bennett's identity (Theorems 2 and 3). Corollary 1 is Bennett's identity
  combined with reflection. Proposition 1 is induction on `n`.
* By `extendedContinuant_det_start`, `K_{a-1}(x)_b` and `K_{a-2}(x)_{b+1}` are
  never both zero, so the recurrence determines `x_{b+a}` from three
  consecutive pairs of continuants (`eq_of_mul_extendedContinuant_eq`). This
  gives the eastbound and westbound comparisons
  `eq_of_forall_extendedContinuant_eq` and
  `neg_eq_of_forall_extendedContinuant_eq` used in Theorems 5–7. In Theorem 4
  the determinant identity for `x` at `n = -σ - 1` evaluates to `-1` on the
  convergents of `z`, while it equals `(-1)^σ`. The special terms in
  Theorems 6 and 7 come from Lemma 1, reflection, the left-adjusting recurrence
  and determinants.
* In Proposition 3 the table (33) repeats a block `p, q, r` (a rotation of
  `-1, 1, 1`) with `pqr + p + q + r = 0`. The matrix of such a block squares
  to the identity, so blocks of six terms can be dropped from the front of a
  continuant (`extendedContinuant_eq_sub_six`,
  `extendedContinuant_eq_sub_six_mul`), leaving continuants of at most eight
  explicit terms.

Three hypotheses are kept so that the statements match the source, although
the proofs do not need them: `1 ≤ n` in Proposition 1 (for `n = 0` both sides
are the identity matrix), `5 ≤ σ` in Theorem 7 (oddness of `σ` suffices), and
`c₁ ≠ c₂` in the case `σ ≡ 5 (mod 6)` of Proposition 3 (there `w = -1`).

Lemma 3 of the paper (the conjugate of a quadratic irrational has a
non-purely-periodic continued fraction) is not proved here; it stays in
`WantedExt.NumberTheory.ExtendedContinuantWanted`.

## Main results

* `extendedContinuant_westbound_matrix_prod` (Proposition 1).
* `extendedContinuant_neg_order` (Theorem 1), `extendedContinuant_det`
  (Corollary 2).
* `extendedContinuant_bennett_nat` (Theorem 2), `extendedContinuant_bennett`
  (Theorem 3), `extendedContinuant_euler` (Corollary 1).
* `not_silent_of_even` (Theorem 4), `oneSilent_terms` (Theorem 5),
  `threeSilent_terms` (Theorem 6), `oddSilent_terms` (Theorem 7).
* `silentTerms_table_one_mod_six`, `silentTerms_table_five_mod_six`
  (Proposition 3).

## References

* Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
  Fractions*, INTEGERS 26 (2026), Article A73.
-/

namespace MetaMathlibExt

@[expose] public section

/-! ### Definition and first values -/

/-- Forward branch of the extended continuant with start index `b`: the value
at `n` is `K_{n-2}(x)_b`, so `0 ↦ 0`, `1 ↦ 1`, and
`n + 2 ↦ x_{b+n} K_{n-1} + K_{n-2}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Definition 3
(right-adjusting recurrence). -/
def extendedContinuantFwd (x : ℤ → ℤ) (b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    x (b + n) * extendedContinuantFwd x b (n + 1) + extendedContinuantFwd x b n

/-- Backward branch of the extended continuant with start index `b`: the value
at `m` is `K_{-1-m}(x)_b`, so `0 ↦ 1`, `1 ↦ 0`, and
`m + 2 ↦ -x_{b-1-m} K_{-2-m} + K_{-1-m}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Definition 4
(right-adjusting recurrence). -/
def extendedContinuantBwd (x : ℤ → ℤ) (b : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | m + 2 =>
    -x (b - 1 - m) * extendedContinuantBwd x b (m + 1) +
      extendedContinuantBwd x b m

/-- The extended continuant `K_a(x)_b^{a+b}` of order `a ∈ ℤ` with start index
`b` (Definitions 3 and 4 of the paper, right-adjusting form).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
def extendedContinuant (x : ℤ → ℤ) (a b : ℤ) : ℤ :=
  if 0 ≤ a + 2 then extendedContinuantFwd x b (a + 2).toNat
  else extendedContinuantBwd x b (-1 - a).toNat

private theorem extendedContinuant_eq_fwd (x : ℤ → ℤ) (b : ℤ) {a : ℤ} {n : ℕ}
    (h : a + 2 = n) :
    extendedContinuant x a b = extendedContinuantFwd x b n := by
  unfold extendedContinuant
  split_ifs
  · congr 1
    omega
  · omega

private theorem extendedContinuant_eq_bwd (x : ℤ → ℤ) (b : ℤ) {a : ℤ} {m : ℕ}
    (h : a = -1 - m) :
    extendedContinuant x a b = extendedContinuantBwd x b m := by
  rcases m with _ | _ | m
  · rw [extendedContinuant_eq_fwd x b (n := 1) (by omega)]
    rfl
  · rw [extendedContinuant_eq_fwd x b (n := 0) (by omega)]
    rfl
  · unfold extendedContinuant
    split_ifs
    · omega
    · congr 1
      omega

/-- `K_{-2}(x)_b = 0`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
theorem extendedContinuant_neg_two (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x (-2) b = 0 :=
  extendedContinuant_eq_fwd x b (n := 0) (by omega)

/-- `K_{-1}(x)_b = 1`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
theorem extendedContinuant_neg_one (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x (-1) b = 1 :=
  extendedContinuant_eq_fwd x b (n := 1) (by omega)

/-- `K_0(x)_b^b = x_b`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Section 3.4 and
Equation (13). -/
theorem extendedContinuant_zero (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x 0 b = x b := by
  rw [extendedContinuant_eq_fwd x b (n := 2) (by omega)]
  simp [extendedContinuantFwd]

/-- The right-adjusting recurrence
`K_a(x)_b = x_{b+a} K_{a-1}(x)_b + K_{a-2}(x)_b` holds for every integer order
`a` (for `a ≤ -1` it is the paper's backward recurrence of Definition 4).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Definitions 3 and 4
(RA versions). -/
theorem extendedContinuant_recurrence (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x a b =
      x (b + a) * extendedContinuant x (a - 1) b +
        extendedContinuant x (a - 2) b := by
  rcases le_or_gt 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [extendedContinuant_eq_fwd x b (n := n + 2) (by omega),
      extendedContinuant_eq_fwd x b (n := n + 1) (by omega),
      extendedContinuant_eq_fwd x b (n := n) (by omega)]
    rfl
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, a = -1 - m := ⟨(-1 - a).toNat, by omega⟩
    rw [extendedContinuant_eq_bwd x b (m := m) hm,
      extendedContinuant_eq_bwd x b (m := m + 1) (by omega),
      extendedContinuant_eq_bwd x b (m := m + 2) (by omega)]
    have hx : b + a = b - 1 - m := by omega
    simp only [extendedContinuantBwd, hx]
    ring

/-- Lemma 1: `K_{-3}(x)_h = 1`, `K_{-4}(x)_h = -x_{h-2}`,
`K_{-5}(x)_h = 1 + x_{h-3} x_{h-2}`, and
`K_{-6}(x)_h = -(x_{h-4} + x_{h-2} + x_{h-4} x_{h-3} x_{h-2})`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic
Continued Fractions*, INTEGERS 26 (2026), Article A73, Lemma 1. -/
theorem extendedContinuant_neg_three_to_six (x : ℤ → ℤ) (h : ℤ) :
    extendedContinuant x (-3) h = 1 ∧ extendedContinuant x (-4) h = -x (h - 2) ∧
      extendedContinuant x (-5) h = 1 + x (h - 3) * x (h - 2) ∧
      extendedContinuant x (-6) h =
        -(x (h - 4) + x (h - 2) + x (h - 4) * x (h - 3) * x (h - 2)) := by
  have r := extendedContinuant_recurrence x
  have k1 := extendedContinuant_neg_one x h
  have k2 := extendedContinuant_neg_two x h
  have e1 := r (-1) h
  have e2 := r (-2) h
  have e3 := r (-3) h
  have e4 := r (-4) h
  norm_num at e1 e2 e3 e4
  rw [show h + -1 = h - 1 by ring] at e1
  rw [show h + -2 = h - 2 by ring] at e2
  rw [show h + -3 = h - 3 by ring] at e3
  rw [show h + -4 = h - 4 by ring] at e4
  have h3 : extendedContinuant x (-3) h = 1 := by rw [k1, k2] at e1; linarith
  have h4 : extendedContinuant x (-4) h = -x (h - 2) := by
    rw [k2, h3] at e2; linarith
  have h5 : extendedContinuant x (-5) h = 1 + x (h - 3) * x (h - 2) := by
    rw [h3, h4] at e3; linarith
  refine ⟨h3, h4, h5, ?_⟩
  rw [h4, h5] at e4
  linear_combination -e4

/-! ### Casoratians and the reflection formula -/

/-- The recurrence `extendedContinuant_recurrence` with the derived indices
given by equations, for use at index expressions that are not syntactically of
the form `a - 1`, `a - 2`, `b + a`. -/
private theorem recurrence_of_eq (x : ℤ → ℤ) {a b a₁ a₂ c : ℤ}
    (h₁ : a₁ = a - 1) (h₂ : a₂ = a - 2) (hc : c = b + a) :
    extendedContinuant x a b =
      x c * extendedContinuant x a₁ b + extendedContinuant x a₂ b := by
  subst h₁ h₂ hc
  exact extendedContinuant_recurrence x a b

/-- An integer sequence that changes sign at every step is
`(-1) ^ (n - n₀)` times its value at `n₀`. -/
theorem eq_negOnePow_sub_mul_of_forall_eq_neg {W : ℤ → ℤ}
    (hW : ∀ n, W n = -W (n - 1)) (n₀ n : ℤ) :
    W n = (n - n₀).negOnePow * W n₀ := by
  refine Int.inductionOn' n n₀ ?_ (fun k _ ih => ?_) (fun k _ ih => ?_)
  · rw [sub_self, Int.negOnePow_zero, Units.val_one, one_mul]
  · rw [hW (k + 1), add_sub_cancel_right, ih,
      show k + 1 - n₀ = k - n₀ + 1 by ring, Int.negOnePow_succ, Units.val_neg,
      neg_mul]
  · have h := hW k
    rw [ih, show k - n₀ = k - 1 - n₀ + 1 by ring, Int.negOnePow_succ,
      Units.val_neg, neg_mul] at h
    exact (neg_inj.mp h).symm

/-- The Casoratian of two extended continuants with a common end: for all
integers `i, j, n`, with `P(i, n) = K_{n-i-2}(x)_i` (the continuant of
`x_i, …, x_{n-2}`),
`P(i, n) P(j, n - 1) - P(i, n - 1) P(j, n) = (-1)^(n-j) P(i, j)`. -/
theorem extendedContinuant_casoratian (x : ℤ → ℤ) (i j n : ℤ) :
    extendedContinuant x (n - i - 2) i * extendedContinuant x (n - j - 3) j -
        extendedContinuant x (n - i - 3) i *
          extendedContinuant x (n - j - 2) j =
      (n - j).negOnePow * extendedContinuant x (j - i - 2) i := by
  have hW : ∀ n : ℤ,
      extendedContinuant x (n - i - 2) i * extendedContinuant x (n - j - 3) j -
          extendedContinuant x (n - i - 3) i *
            extendedContinuant x (n - j - 2) j =
        -(extendedContinuant x (n - 1 - i - 2) i *
            extendedContinuant x (n - 1 - j - 3) j -
          extendedContinuant x (n - 1 - i - 3) i *
            extendedContinuant x (n - 1 - j - 2) j) := by
    intro n
    rw [show n - 1 - i - 2 = n - i - 3 by ring,
      show n - 1 - j - 3 = n - j - 4 by ring,
      show n - 1 - i - 3 = n - i - 4 by ring,
      show n - 1 - j - 2 = n - j - 3 by ring,
      recurrence_of_eq x (a := n - i - 2) (a₁ := n - i - 3) (a₂ := n - i - 4)
        (c := n - 2) (by ring) (by ring) (by ring),
      recurrence_of_eq x (a := n - j - 2) (a₁ := n - j - 3) (a₂ := n - j - 4)
        (c := n - 2) (by ring) (by ring) (by ring)]
    ring
  rw [eq_negOnePow_sub_mul_of_forall_eq_neg (W := fun n =>
      extendedContinuant x (n - i - 2) i * extendedContinuant x (n - j - 3) j -
        extendedContinuant x (n - i - 3) i *
          extendedContinuant x (n - j - 2) j)
    hW (j + 1) n]
  rw [show j + 1 - i - 2 = j - i - 1 by ring, show j + 1 - j - 3 = -2 by ring,
    show j + 1 - i - 3 = j - i - 2 by ring, show j + 1 - j - 2 = -1 by ring,
    extendedContinuant_neg_two, extendedContinuant_neg_one,
    show n - (j + 1) = n - j + -1 by ring, Int.negOnePow_add,
    Int.negOnePow_neg, Int.negOnePow_one, Units.val_mul, Units.val_neg,
    Units.val_one]
  ring

/-- Two signs `(-1)^b (-1)^c` multiply to `(-1)^a` when `a - b - c` is even. -/
private theorem negOnePow_eq_mul {a b c : ℤ} (h : Even (a - b - c)) :
    (a.negOnePow : ℤ) = b.negOnePow * c.negOnePow := by
  rw [← Units.val_mul, ← Int.negOnePow_add,
    (Int.negOnePow_eq_iff a (b + c)).mpr (by convert h using 1; ring)]

/-- The reflection formula `K_a(x)_b = (-1)^(a+1) K_{-a-4}(x)_{b+a+2}` for all
integers `a, b` (Theorem 1 with `n = -a`). -/
theorem extendedContinuant_reflect (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x a b =
      (a + 1).negOnePow * extendedContinuant x (-a - 4) (b + a + 2) := by
  have h₁ := extendedContinuant_casoratian x b (b + a + 2) (b + a + 2)
  have h₂ := extendedContinuant_casoratian x (b + a + 2) b (b + a + 2)
  have hs : (b + a + 2 - b).negOnePow = -(a + 1).negOnePow := by
    rw [show b + a + 2 - b = a + 1 + 1 by ring, Int.negOnePow_succ]
  simp only [sub_self, show b + a + 2 - b - 2 = a by ring,
    show b - (b + a + 2) - 2 = -a - 4 by ring, hs, Int.negOnePow_zero,
    Units.val_one, Units.val_neg] at h₁ h₂
  linear_combination -h₁ - h₂

/-- Theorem 1: for all `h, n ∈ ℤ`,
`K_{-n}(x)_h^{h-n} = (-1)^{n+1} K_{n-4}(x)_{h-n+2}^{h-2}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Theorem 1.

Proves `Wanted` entry `extendedContinuant_neg_order`. -/
theorem extendedContinuant_neg_order (x : ℤ → ℤ) (h n : ℤ) :
    extendedContinuant x (-n) h =
      ((n + 1).negOnePow : ℤ) * extendedContinuant x (n - 4) (h - n + 2) := by
  rw [extendedContinuant_reflect, neg_neg, show h + -n + 2 = h - n + 2 by ring,
    (Int.negOnePow_eq_iff (-n + 1) (n + 1)).mpr ⟨-n, by ring⟩]

/-- Corollary 2 at an arbitrary start index `b`:
`K_n(x)_b K_{n-2}(x)_{b+1} - K_{n-1}(x)_{b+1} K_{n-1}(x)_b = (-1)^{n+1}`. -/
theorem extendedContinuant_det_start (x : ℤ → ℤ) (n b : ℤ) :
    extendedContinuant x n b * extendedContinuant x (n - 2) (b + 1) -
        extendedContinuant x (n - 1) (b + 1) * extendedContinuant x (n - 1) b =
      ((n + 1).negOnePow : ℤ) := by
  have h := extendedContinuant_casoratian x b (b + 1) (b + n + 2)
  rw [show b + n + 2 - b - 2 = n by ring,
    show b + n + 2 - (b + 1) - 3 = n - 2 by ring,
    show b + n + 2 - b - 3 = n - 1 by ring,
    show b + n + 2 - (b + 1) - 2 = n - 1 by ring,
    show b + n + 2 - (b + 1) = n + 1 by ring,
    show b + 1 - b - 2 = -1 by ring, extendedContinuant_neg_one] at h
  linear_combination h

/-- Corollary 2: for all `n ∈ ℤ`,
`K_n(x)_0 K_{n-2}(x)_1 - K_{n-1}(x)_1 K_{n-1}(x)_0 = (-1)^{n+1}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Corollary 2.

Proves `Wanted` entry `extendedContinuant_det`. -/
theorem extendedContinuant_det (x : ℤ → ℤ) (n : ℤ) :
    extendedContinuant x n 0 * extendedContinuant x (n - 2) 1 -
        extendedContinuant x (n - 1) 1 * extendedContinuant x (n - 1) 0 =
      ((n + 1).negOnePow : ℤ) :=
  extendedContinuant_det_start x n 0

/-- Theorem 3: Bennett's symmetric identity (Theorem 2) holds for all integers
`k, ℓ, m, n`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Theorem 3.

Proves `Wanted` entry `extendedContinuant_bennett`. -/
theorem extendedContinuant_bennett (x : ℤ → ℤ) (k ℓ m n : ℤ) :
    ((k + ℓ).negOnePow : ℤ) * extendedContinuant x (n - k - 2) k *
        extendedContinuant x (m - ℓ - 2) ℓ +
      ((ℓ + m).negOnePow : ℤ) * extendedContinuant x (n - ℓ - 2) ℓ *
        extendedContinuant x (k - m - 2) m +
      ((m + k).negOnePow : ℤ) * extendedContinuant x (n - m - 2) m *
        extendedContinuant x (ℓ - k - 2) k = 0 := by
  have h₁ := extendedContinuant_casoratian x ℓ m n
  have h₂ := extendedContinuant_casoratian x m k n
  have h₃ := extendedContinuant_casoratian x k ℓ n
  have s₁ : ((k + ℓ).negOnePow : ℤ) =
      (n + k + ℓ + m).negOnePow * (n - m).negOnePow :=
    negOnePow_eq_mul ⟨-n, by ring⟩
  have s₂ : ((ℓ + m).negOnePow : ℤ) =
      (n + k + ℓ + m).negOnePow * (n - k).negOnePow :=
    negOnePow_eq_mul ⟨-n, by ring⟩
  have s₃ : ((m + k).negOnePow : ℤ) =
      (n + k + ℓ + m).negOnePow * (n - ℓ).negOnePow :=
    negOnePow_eq_mul ⟨-n, by ring⟩
  rw [s₁, s₂, s₃]
  linear_combination
    (-((n + k + ℓ + m).negOnePow : ℤ)) *
      (extendedContinuant x (n - k - 2) k * h₁ +
        extendedContinuant x (n - ℓ - 2) ℓ * h₂ +
        extendedContinuant x (n - m - 2) m * h₃)

/-- Theorem 2 (Bennett): for nonnegative integers `k, ℓ, m, n`,
`(-1)^{k+ℓ} K_{n-k-2}(x)_k K_{m-ℓ-2}(x)_ℓ
+ (-1)^{ℓ+m} K_{n-ℓ-2}(x)_ℓ K_{k-m-2}(x)_m
+ (-1)^{m+k} K_{n-m-2}(x)_m K_{ℓ-k-2}(x)_k = 0`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Theorem 2 (after G. T. Bennett,
1939).

Proves `Wanted` entry `extendedContinuant_bennett_nat`. -/
theorem extendedContinuant_bennett_nat (x : ℤ → ℤ) (k ℓ m n : ℕ) :
    ((k + ℓ : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - k - 2) k *
        extendedContinuant x ((m : ℤ) - ℓ - 2) ℓ +
      ((ℓ + m : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - ℓ - 2) ℓ *
        extendedContinuant x ((k : ℤ) - m - 2) m +
      ((m + k : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - m - 2) m *
        extendedContinuant x ((ℓ : ℤ) - k - 2) k = 0 :=
  extendedContinuant_bennett x k ℓ m n

/-- Corollary 1 (Euler's continuant identity, extended): for all
`h, k, ℓ, m ∈ ℤ`,
`K_{ℓ+m}(x)_h K_{k-1}(x)_{ℓ+h+1} - K_{m-1}(x)_{ℓ+h+1} K_{k+ℓ}(x)_h
= (-1)^k K_{m-k-2}(x)_{k+ℓ+h+2} K_{ℓ-1}(x)_h`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Corollary 1.

Proves `Wanted` entry `extendedContinuant_euler`. -/
theorem extendedContinuant_euler (x : ℤ → ℤ) (h k ℓ m : ℤ) :
    extendedContinuant x (ℓ + m) h * extendedContinuant x (k - 1) (ℓ + h + 1) -
        extendedContinuant x (m - 1) (ℓ + h + 1) *
          extendedContinuant x (k + ℓ) h =
      (k.negOnePow : ℤ) * extendedContinuant x (m - k - 2) (k + ℓ + h + 2) *
        extendedContinuant x (ℓ - 1) h := by
  have hB := extendedContinuant_bennett x h (ℓ + h + 1) (k + ℓ + h + 2)
    (m + ℓ + h + 2)
  have hR := extendedContinuant_reflect x (k + ℓ) h
  rw [show m + ℓ + h + 2 - h - 2 = ℓ + m by ring,
    show k + ℓ + h + 2 - (ℓ + h + 1) - 2 = k - 1 by ring,
    show m + ℓ + h + 2 - (ℓ + h + 1) - 2 = m - 1 by ring,
    show h - (k + ℓ + h + 2) - 2 = -(k + ℓ) - 4 by ring,
    show m + ℓ + h + 2 - (k + ℓ + h + 2) - 2 = m - k - 2 by ring,
    show ℓ + h + 1 - h - 2 = ℓ - 1 by ring] at hB
  rw [show h + (k + ℓ) + 2 = k + ℓ + h + 2 by ring] at hR
  have s₁ : ((h + (ℓ + h + 1)).negOnePow : ℤ) * (h + (ℓ + h + 1)).negOnePow =
      1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have s₂ : ((ℓ + h + 1 + (k + ℓ + h + 2)).negOnePow : ℤ) =
      (h + (ℓ + h + 1)).negOnePow * (k + ℓ + 1 + 1).negOnePow :=
    negOnePow_eq_mul ⟨0, by ring⟩
  have s₃ : ((k + ℓ + h + 2 + h).negOnePow : ℤ) =
      (h + (ℓ + h + 1)).negOnePow * (k + 1).negOnePow :=
    negOnePow_eq_mul ⟨0, by ring⟩
  rw [s₂, s₃] at hB
  rw [Int.negOnePow_succ (k + ℓ + 1), Int.negOnePow_succ k, Units.val_neg,
    Units.val_neg] at hB
  linear_combination ((h + (ℓ + h + 1)).negOnePow : ℤ) * hB -
    (extendedContinuant x (ℓ + m) h * extendedContinuant x (k - 1) (ℓ + h + 1) -
      extendedContinuant x (m - 1) (ℓ + h + 1) *
        extendedContinuant x (k + ℓ) h -
      (k.negOnePow : ℤ) * extendedContinuant x (m - k - 2) (k + ℓ + h + 2) *
        extendedContinuant x (ℓ - 1) h) * s₁ -
    ((h + (ℓ + h + 1)).negOnePow : ℤ) * (h + (ℓ + h + 1)).negOnePow *
      extendedContinuant x (m - 1) (ℓ + h + 1) * hR

/-! ### The left-adjusting recurrence -/

/-- The left-adjusting recurrence
`K_a(x)_b = x_b K_{a-1}(x)_{b+1} + K_{a-2}(x)_{b+2}`, valid for every integer
order `a`. -/
theorem extendedContinuant_left_recurrence (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x a b =
      x b * extendedContinuant x (a - 1) (b + 1) +
        extendedContinuant x (a - 2) (b + 2) := by
  have h₁ := extendedContinuant_reflect x a b
  have h₂ := extendedContinuant_reflect x (a - 1) (b + 1)
  have h₃ := extendedContinuant_reflect x (a - 2) (b + 2)
  have hr := recurrence_of_eq x (a := -a - 2) (b := b + a + 2) (a₁ := -a - 3)
    (a₂ := -a - 4) (c := b) (by ring) (by ring) (by ring)
  rw [show -(a - 1) - 4 = -a - 3 by ring,
    show b + 1 + (a - 1) + 2 = b + a + 2 by ring,
    show a - 1 + 1 = a by ring] at h₂
  rw [show -(a - 2) - 4 = -a - 2 by ring,
    show b + 2 + (a - 2) + 2 = b + a + 2 by ring,
    (Int.negOnePow_eq_iff (a - 2 + 1) (a + 1)).mpr ⟨-1, by ring⟩] at h₃
  rw [Int.negOnePow_succ, Units.val_neg] at h₁ h₃
  linear_combination h₁ - x b * h₂ - h₃ + (a.negOnePow : ℤ) * hr

/-- The left-adjusting recurrence with the derived indices given by
equations. -/
private theorem left_recurrence_of_eq (x : ℤ → ℤ) {a b a₁ a₂ b₁ b₂ : ℤ}
    (h₁ : a₁ = a - 1) (h₂ : a₂ = a - 2) (h₃ : b₁ = b + 1) (h₄ : b₂ = b + 2) :
    extendedContinuant x a b =
      x b * extendedContinuant x a₁ b₁ + extendedContinuant x a₂ b₂ := by
  subst h₁ h₂ h₃ h₄
  exact extendedContinuant_left_recurrence x a b

/-- The reflection formula with the reflected indices given by equations. -/
private theorem reflect_of_eq (x : ℤ → ℤ) {a b c d : ℤ} (h₁ : c = -a - 4)
    (h₂ : d = b + a + 2) :
    extendedContinuant x a b =
      (a + 1).negOnePow * extendedContinuant x c d := by
  subst h₁ h₂
  exact extendedContinuant_reflect x a b

/-! ### Westbound matrix products -/

/-- `extendedContinuant_westbound_matrix_prod` for every `n`, including the
empty product `n = 0`. -/
private theorem westbound_matrix_prod_aux (x : ℤ → ℤ) (n : ℕ) :
    (List.ofFn fun i : Fin n => !![0, 1; 1, -x (-((n : ℤ) - i))]).prod =
      !![extendedContinuant x (-n - 1) 0, extendedContinuant x (-n - 2) 1;
        extendedContinuant x (-n - 2) 0, extendedContinuant x (-n - 3) 1] := by
  induction n with
  | zero =>
    rw [List.ofFn_zero, List.prod_nil, Matrix.one_fin_two]
    simp only [Nat.cast_zero, neg_zero, zero_sub, extendedContinuant_neg_one,
      extendedContinuant_neg_two, (extendedContinuant_neg_three_to_six x 1).1]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one,
      add_sub_add_right_eq_sub, ih, Fin.val_zero, Nat.cast_zero, sub_zero,
      Matrix.mul_fin_two]
    have e₁ := recurrence_of_eq x (a := -(n : ℤ) - 1) (b := 0)
      (a₁ := -(n : ℤ) - 2) (a₂ := -(n : ℤ) - 3) (c := -((n : ℤ) + 1))
      (by ring) (by ring) (by ring)
    have e₂ := recurrence_of_eq x (a := -(n : ℤ) - 2) (b := 1)
      (a₁ := -(n : ℤ) - 3) (a₂ := -(n : ℤ) - 4) (c := -((n : ℤ) + 1))
      (by ring) (by ring) (by ring)
    rw [show -((n : ℤ) + 1) - 1 = -n - 2 by ring,
      show -((n : ℤ) + 1) - 2 = -n - 3 by ring,
      show -((n : ℤ) + 1) - 3 = -n - 4 by ring, eq_sub_of_add_eq' e₁.symm,
      eq_sub_of_add_eq' e₂.symm]
    simp only [zero_mul, one_mul, zero_add, neg_mul, ← sub_eq_add_neg]

-- `hn` is part of the source statement but is not needed: for `n = 0` both
-- sides are the identity matrix.
set_option linter.unusedVariables false in
/-- Proposition 1: for `n ≥ 1`, the westbound matrix product
`∏_{i=n}^{1} [[0, 1], [1, -x_{-i}]]` (factor `i = n` leftmost) equals
`[[K_{-n-1}(x)_0, K_{-n-2}(x)_1], [K_{-n-2}(x)_0, K_{-n-3}(x)_1]]`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Proposition 1.

Proves `Wanted` entry `extendedContinuant_westbound_matrix_prod`. -/
theorem extendedContinuant_westbound_matrix_prod (x : ℤ → ℤ) (n : ℕ)
    (hn : 1 ≤ n) :
    (List.ofFn fun i : Fin n => !![0, 1; 1, -x (-((n : ℤ) - i))]).prod =
      !![extendedContinuant x (-n - 1) 0, extendedContinuant x (-n - 2) 1;
        extendedContinuant x (-n - 2) 0, extendedContinuant x (-n - 3) 1] :=
  westbound_matrix_prod_aux x n

/-! ### Terms determined by continuants -/

/-- If `c` and `d` have the same products with the two consecutive continuants
`K_{a-1}(x)_b` and `K_{a-2}(x)_{b+1}`, then `c = d`: these continuants are never
both zero, by `extendedContinuant_det_start`. -/
theorem eq_of_mul_extendedContinuant_eq {x : ℤ → ℤ} {a b c d : ℤ}
    (h₁ : c * extendedContinuant x (a - 1) b =
      d * extendedContinuant x (a - 1) b)
    (h₂ : c * extendedContinuant x (a - 2) (b + 1) =
      d * extendedContinuant x (a - 2) (b + 1)) :
    c = d := by
  by_contra hcd
  have hcd' : c - d ≠ 0 := sub_ne_zero.mpr hcd
  have e₁ : extendedContinuant x (a - 1) b = 0 :=
    (mul_eq_zero.mp (by linear_combination h₁ :
      (c - d) * extendedContinuant x (a - 1) b = 0)).resolve_left hcd'
  have e₂ : extendedContinuant x (a - 2) (b + 1) = 0 :=
    (mul_eq_zero.mp (by linear_combination h₂ :
      (c - d) * extendedContinuant x (a - 2) (b + 1) = 0)).resolve_left hcd'
  have hdet := extendedContinuant_det_start x (a - 1) b
  rw [show a - 1 - 1 = a - 2 by ring, e₁, e₂, zero_mul, zero_mul,
    sub_zero] at hdet
  exact Units.ne_zero _ hdet.symm

/-- Eastbound comparison: if two integer sequences have the same continuants
`K_i(·)_0` and `K_{i-1}(·)_1` for all `i ≥ 0` (strictly equivalent raw
convergents), then they agree at every index `n ≥ 0`. -/
theorem eq_of_forall_extendedContinuant_eq {x y : ℤ → ℤ}
    (h : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 =
        extendedContinuant y ((i : ℤ) - 1) 1)
    (n : ℕ) : x n = y n := by
  have hE : ∀ a : ℤ, -2 ≤ a →
      extendedContinuant x a 0 = extendedContinuant y a 0 ∧
        extendedContinuant x (a - 1) 1 = extendedContinuant y (a - 1) 1 := by
    intro a ha
    rcases (by omega : a = -2 ∨ a = -1 ∨ 0 ≤ a) with rfl | rfl | ha
    · rw [show (-2 : ℤ) - 1 = -3 by norm_num, extendedContinuant_neg_two,
        extendedContinuant_neg_two, (extendedContinuant_neg_three_to_six x 1).1,
        (extendedContinuant_neg_three_to_six y 1).1]
      exact ⟨rfl, rfl⟩
    · rw [show (-1 : ℤ) - 1 = -2 by norm_num, extendedContinuant_neg_one,
        extendedContinuant_neg_one, extendedContinuant_neg_two,
        extendedContinuant_neg_two]
      exact ⟨rfl, rfl⟩
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      exact h i
  refine eq_of_mul_extendedContinuant_eq (x := x) (a := n) (b := 0) ?_ ?_
  · have hx := recurrence_of_eq x (a := n) (b := 0) (a₁ := n - 1)
      (a₂ := n - 2) (c := n) rfl rfl (by ring)
    have hy := recurrence_of_eq y (a := n) (b := 0) (a₁ := n - 1)
      (a₂ := n - 2) (c := n) rfl rfl (by ring)
    rw [← (hE n (by omega)).1, ← (hE (n - 1) (by omega)).1,
      ← (hE (n - 2) (by omega)).1] at hy
    linear_combination hy - hx
  · have hx := recurrence_of_eq x (a := n - 1) (b := 1) (a₁ := n - 2)
      (a₂ := n - 3) (c := n) (by ring) (by ring) (by ring)
    have hy := recurrence_of_eq y (a := n - 1) (b := 1) (a₁ := n - 2)
      (a₂ := n - 3) (c := n) (by ring) (by ring) (by ring)
    have e₂ : extendedContinuant x ((n : ℤ) - 2) 1 =
        extendedContinuant y ((n : ℤ) - 2) 1 := by
      rw [show (n : ℤ) - 2 = n - 1 - 1 by ring]
      exact (hE (n - 1) (by omega)).2
    have e₃ : extendedContinuant x ((n : ℤ) - 3) 1 =
        extendedContinuant y ((n : ℤ) - 3) 1 := by
      rw [show (n : ℤ) - 3 = n - 2 - 1 by ring]
      exact (hE (n - 2) (by omega)).2
    rw [← (hE n (by omega)).2, ← e₂, ← e₃] at hy
    rw [zero_add]
    linear_combination hy - hx

/-- One westbound comparison step: if `K_{-i-σ-t}(x)_0 = K_{i+t-1}(z)_0` for
`t = 0, 1, 2` and `K_{-i-σ-t}(x)_1 = K_{i+t-3}(z)_1` for `t = 1, 2, 3`, then
`x_{-i-σ} = -z_{i+1}`. -/
private theorem neg_eq_of_extendedContinuant_eq {x z : ℤ → ℤ} {σ i : ℤ}
    (e₀ : extendedContinuant x (-i - σ) 0 = extendedContinuant z (i - 1) 0)
    (e₁ : extendedContinuant x (-i - σ - 1) 0 = extendedContinuant z i 0)
    (e₂ : extendedContinuant x (-i - σ - 2) 0 = extendedContinuant z (i + 1) 0)
    (f₀ : extendedContinuant x (-i - σ - 1) 1 = extendedContinuant z (i - 2) 1)
    (f₁ : extendedContinuant x (-i - σ - 2) 1 = extendedContinuant z (i - 1) 1)
    (f₂ : extendedContinuant x (-i - σ - 3) 1 = extendedContinuant z i 1) :
    x (-i - σ) = -z (i + 1) := by
  have key : z (i + 1) = -x (-i - σ) := by
    refine eq_of_mul_extendedContinuant_eq (x := z) (a := i + 1) (b := 0) ?_ ?_
    · have hx := recurrence_of_eq x (a := -i - σ) (b := 0) (a₁ := -i - σ - 1)
        (a₂ := -i - σ - 2) (c := -i - σ) rfl (by ring) (by ring)
      have hz := recurrence_of_eq z (a := i + 1) (b := 0) (a₁ := i)
        (a₂ := i - 1) (c := i + 1) (by ring) (by ring) (by ring)
      rw [show i + 1 - 1 = i by ring]
      rw [e₀, e₁, e₂] at hx
      linear_combination -hz - hx
    · have hx := recurrence_of_eq x (a := -i - σ - 1) (b := 1)
        (a₁ := -i - σ - 2) (a₂ := -i - σ - 3) (c := -i - σ) (by ring) (by ring)
        (by ring)
      have hz := recurrence_of_eq z (a := i) (b := 1) (a₁ := i - 1)
        (a₂ := i - 2) (c := i + 1) rfl rfl (by ring)
      rw [show i + 1 - 2 = i - 1 by ring, zero_add]
      rw [f₀, f₁, f₂] at hx
      linear_combination -hz - hx
  linear_combination key

/-- Westbound comparison: if `K_{-i-σ-1}(x)_0 = K_i(z)_0` and
`K_{-i-σ-2}(x)_1 = K_{i-1}(z)_1` for all `i ≥ 0` (the raw westbound convergents
`k_{-i-σ-1}` of `x` are strictly equivalent to the raw convergents of `z`), then
`x_{-i-σ} = -z_{i+1}` for every `i ≥ 1`. -/
theorem neg_eq_of_forall_extendedContinuant_eq {x z : ℤ → ℤ} {σ : ℤ}
    (h : ∀ i : ℕ,
      extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
        extendedContinuant x (-(i : ℤ) - σ - 2) 1 =
          extendedContinuant z ((i : ℤ) - 1) 1)
    {i : ℕ} (hi : 1 ≤ i) : x (-(i : ℤ) - σ) = -z ((i : ℤ) + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  refine neg_eq_of_extendedContinuant_eq ?_ ?_ ?_ ?_ ?_ ?_
  · convert (h j).1 using 2 <;> push_cast <;> ring
  · convert (h (j + 1)).1 using 2
  · convert (h (j + 2)).1 using 2 <;> push_cast <;> ring
  · convert (h j).2 using 2 <;> push_cast <;> ring
  · convert (h (j + 1)).2 using 2
  · convert (h (j + 2)).2 using 2 <;> push_cast <;> ring

/-- Theorem 4: for even `σ ≥ 0` there is no `σ`-silent bi-infinite sequence: no
`x : ℤ → ℤ` has raw westbound convergents `k_{-i-σ-1}` strictly equivalent to
the raw convergents `d_i` of `z` for all `i ≥ 0`. Stated for every pair of
integer sequences `x`, `z` (the BpCF conditions are not needed).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Theorem 4.

Proves `Wanted` entry `not_silent_of_even`. -/
theorem not_silent_of_even (x z : ℤ → ℤ) (σ : ℕ) (hσ : Even σ) :
    ¬ ∀ i : ℕ,
      extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
        extendedContinuant x (-(i : ℤ) - σ - 2) 1 =
          extendedContinuant z ((i : ℤ) - 1) 1 := by
  intro h
  obtain ⟨a₀, b₀⟩ := h 0
  obtain ⟨a₁, b₁⟩ := h 1
  simp only [Nat.cast_zero, neg_zero, zero_sub] at a₀ b₀
  simp only [Nat.cast_one, sub_self] at a₁ b₁
  have hz₁ := recurrence_of_eq z (a := 1) (b := 0) (a₁ := 0) (a₂ := -1) (c := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hdet := extendedContinuant_det x (-(σ : ℤ) - 1)
  rw [show -1 - (σ : ℤ) - 1 = -σ - 2 by ring] at a₁
  rw [show -1 - (σ : ℤ) - 2 = -σ - 3 by ring] at b₁
  rw [show -(σ : ℤ) - 1 - 2 = -σ - 3 by ring,
    show -(σ : ℤ) - 1 - 1 = -σ - 2 by ring, show -(σ : ℤ) - 1 + 1 = -σ by ring,
    Int.negOnePow_even _ ((Int.even_coe_nat σ).mpr hσ).neg, Units.val_one, a₀,
    b₀, a₁, b₁, hz₁, extendedContinuant_zero, extendedContinuant_zero,
    extendedContinuant_neg_one, extendedContinuant_neg_one] at hdet
  have : (0 : ℤ) = 2 := by linear_combination hdet
  omega

/-- Theorem 5 (1-silent BpCFs): if `k_i ≐ c_i` and `k_{-i-2} ≐ d_i` for all
`i ≥ 0`, then `x_n = y_n` for `n ≥ 0`, `x_{-n} = -z_n` for `n ≥ 1`, and
`z_0 = 0` (the paper's `0 < ᾱ < 1` for the EA-generated SCF of the irrational
`ᾱ`).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Theorem 5.

Proves `Wanted` entry `oneSilent_terms`. -/
theorem oneSilent_terms (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 =
        extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ,
      extendedContinuant x (-(i : ℤ) - 2) 0 = extendedContinuant z i 0 ∧
        extendedContinuant x (-(i : ℤ) - 3) 1 =
          extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧ (∀ n : ℕ, 1 ≤ n → x (-(n : ℤ)) = -z n) ∧
      z 0 = 0 := by
  have hw : ∀ i : ℕ,
      extendedContinuant x (-(i : ℤ) - 1 - 1) 0 = extendedContinuant z i 0 ∧
        extendedContinuant x (-(i : ℤ) - 1 - 2) 1 =
          extendedContinuant z ((i : ℤ) - 1) 1 := by
    intro i
    rw [show -(i : ℤ) - 1 - 1 = -(i : ℤ) - 2 by ring,
      show -(i : ℤ) - 1 - 2 = -(i : ℤ) - 3 by ring]
    exact hwest i
  obtain ⟨a₀, b₀⟩ := hwest 0
  obtain ⟨a₁, b₁⟩ := hwest 1
  simp only [Nat.cast_zero, neg_zero, zero_sub] at a₀ b₀
  simp only [Nat.cast_one] at a₁ b₁
  refine ⟨eq_of_forall_extendedContinuant_eq heast, fun n hn => ?_, ?_⟩
  · rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn
    · have h := neg_eq_of_extendedContinuant_eq (x := x) (z := z) (σ := 1)
        (i := 0) ?_ ?_ ?_ ?_ ?_ ?_
      · simpa using h
      · rw [show -(0 : ℤ) - 1 = -1 by norm_num,
          show (0 : ℤ) - 1 = -1 by norm_num, extendedContinuant_neg_one,
          extendedContinuant_neg_one]
      · rwa [show -(0 : ℤ) - 1 - 1 = -2 by norm_num]
      · rwa [show -(0 : ℤ) - 1 - 2 = -1 - 2 by norm_num,
          show (0 : ℤ) + 1 = 1 by norm_num]
      · rw [show -(0 : ℤ) - 1 - 1 = -2 by norm_num,
          show (0 : ℤ) - 2 = -2 by norm_num, extendedContinuant_neg_two,
          extendedContinuant_neg_two]
      · rwa [show -(0 : ℤ) - 1 - 2 = -3 by norm_num,
          show (0 : ℤ) - 1 = -1 by norm_num]
      · rwa [show -(0 : ℤ) - 1 - 3 = -1 - 3 by norm_num]
    · have h := neg_eq_of_forall_extendedContinuant_eq hw (i := n - 1)
        (by omega)
      rw [show -((n - 1 : ℕ) : ℤ) - 1 = -n by omega,
        show ((n - 1 : ℕ) : ℤ) + 1 = n by omega] at h
      exact h
  · rw [extendedContinuant_neg_two, extendedContinuant_zero] at a₀
    exact a₀.symm

/-- Theorem 6 (3-silent BpCFs), with the paper's choice `x_{-1} = 0`: if
`k_i ≐ c_i` and `k_{-i-4} ≐ d_i` for all `i ≥ 0` and `x_{-1} = 0`, then
`x_n = y_n` for `n ≥ 0` and `x_{-n} = -z_{n-2}` for `n ≥ 2`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Theorem 6 and its proof (option 2,
`x_{-1} = 0`).

Proves `Wanted` entry `threeSilent_terms`. -/
theorem threeSilent_terms (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 =
        extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ,
      extendedContinuant x (-(i : ℤ) - 4) 0 = extendedContinuant z i 0 ∧
        extendedContinuant x (-(i : ℤ) - 5) 1 =
          extendedContinuant z ((i : ℤ) - 1) 1)
    (hx : x (-1) = 0) :
    (∀ n : ℕ, x n = y n) ∧
      ∀ n : ℕ, 2 ≤ n → x (-(n : ℤ)) = -z ((n : ℤ) - 2) := by
  have hw : ∀ i : ℕ,
      extendedContinuant x (-(i : ℤ) - 3 - 1) 0 = extendedContinuant z i 0 ∧
        extendedContinuant x (-(i : ℤ) - 3 - 2) 1 =
          extendedContinuant z ((i : ℤ) - 1) 1 := by
    intro i
    rw [show -(i : ℤ) - 3 - 1 = -(i : ℤ) - 4 by ring,
      show -(i : ℤ) - 3 - 2 = -(i : ℤ) - 5 by ring]
    exact hwest i
  refine ⟨eq_of_forall_extendedContinuant_eq heast, fun n hn => ?_⟩
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn
  · have h := (hwest 0).1
    rw [Nat.cast_zero, neg_zero, zero_sub,
      (extendedContinuant_neg_three_to_six x 0).2.1,
      extendedContinuant_zero] at h
    rw [show ((2 : ℕ) : ℤ) - 2 = 0 by norm_num, ← h]
    norm_num
  · have h := (hwest 1).2
    rw [Nat.cast_one, show -(1 : ℤ) - 5 = -6 by norm_num, sub_self,
      (extendedContinuant_neg_three_to_six x 1).2.2.2,
      extendedContinuant_zero] at h
    rw [show ((3 : ℕ) : ℤ) - 2 = 1 by norm_num, ← h]
    norm_num [hx]
  · have h := neg_eq_of_forall_extendedContinuant_eq hw (i := n - 3) (by omega)
    rw [show -((n - 3 : ℕ) : ℤ) - 3 = -n by omega,
      show ((n - 3 : ℕ) : ℤ) + 1 = n - 2 by omega] at h
    exact h

-- `h5` is part of the source statement but is not needed: the proof only uses
-- that `σ` is odd.
set_option linter.unusedVariables false in
/-- Theorem 7 (`σ`-silent BpCFs, `σ = 2j + 1 ≥ 5`): if `k_i ≐ c_i` and
`k_{-i-σ-1} ≐ d_i` for all `i ≥ 0`, then `x_n = y_n` for `n ≥ 0`,
`x_{-σ+2} x_{-σ+1}` equals `-1 + K_{σ-6}(x)_{-σ+4} + z_0 K_{σ-5}(x)_{-σ+4}` (the
paper's quotient formula multiplied out),
`x_{-σ+1} = -K_{σ-5}(x)_{-σ+3} - z_0 K_{σ-4}(x)_{-σ+3}`,
`x_{-σ} = -K_{σ-3}(x)_{-σ+2} - z_1`, and `x_{-n} = -z_{n-σ+1}` for `n ≥ σ + 1`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Theorem 7.

Proves `Wanted` entry `oddSilent_terms`. -/
theorem oddSilent_terms (x y z : ℤ → ℤ) (σ : ℤ) (hσ : Odd σ) (h5 : 5 ≤ σ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 =
        extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ,
      extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
        extendedContinuant x (-(i : ℤ) - σ - 2) 1 =
          extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧
      x (-σ + 2) * x (-σ + 1) = -1 + extendedContinuant x (σ - 6) (-σ + 4) +
        z 0 * extendedContinuant x (σ - 5) (-σ + 4) ∧
      x (-σ + 1) = -extendedContinuant x (σ - 5) (-σ + 3) -
        z 0 * extendedContinuant x (σ - 4) (-σ + 3) ∧
      x (-σ) = -extendedContinuant x (σ - 3) (-σ + 2) - z 1 ∧
      ∀ n : ℤ, σ + 1 ≤ n → x (-n) = -z (n - σ + 1) := by
  obtain ⟨t, ht⟩ := hσ
  obtain ⟨a₀, b₀⟩ := hwest 0
  obtain ⟨-, b₁⟩ := hwest 1
  simp only [Nat.cast_zero, neg_zero, zero_sub, extendedContinuant_zero,
    extendedContinuant_neg_one] at a₀ b₀
  rw [Nat.cast_one, sub_self, extendedContinuant_zero,
    show -1 - σ - 2 = -σ - 3 by ring] at b₁
  -- The westbound values, read as eastbound continuants ending at `x_{-1}`.
  have F₁ : extendedContinuant x (σ - 2) (-σ + 1) = 1 := by
    have h := reflect_of_eq x (a := -σ - 2) (b := 1) (c := σ - 2) (d := -σ + 1)
      (by ring) (by ring)
    rw [Int.negOnePow_even _ ⟨-t - 1, by omega⟩, Units.val_one, one_mul,
      b₀] at h
    exact h.symm
  have F₂ : extendedContinuant x (σ - 3) (-σ + 1) = -z 0 := by
    have h := reflect_of_eq x (a := -σ - 1) (b := 0) (c := σ - 3) (d := -σ + 1)
      (by ring) (by ring)
    rw [Int.negOnePow_odd _ ⟨-t - 1, by omega⟩, Units.val_neg, Units.val_one,
      a₀] at h
    linear_combination h
  have F₃ : extendedContinuant x (σ - 1) (-σ) = -z 1 := by
    have h := reflect_of_eq x (a := -σ - 3) (b := 1) (c := σ - 1) (d := -σ)
      (by ring) (by ring)
    rw [Int.negOnePow_odd _ ⟨-t - 2, by omega⟩, Units.val_neg, Units.val_one,
      b₁] at h
    linear_combination h
  have G₁ := left_recurrence_of_eq x (a := σ - 1) (b := -σ) (a₁ := σ - 2)
    (a₂ := σ - 3) (b₁ := -σ + 1) (b₂ := -σ + 2)
    (by ring) (by ring) (by ring) (by ring)
  have G₂ := left_recurrence_of_eq x (a := σ - 2) (b := -σ + 1) (a₁ := σ - 3)
    (a₂ := σ - 4) (b₁ := -σ + 2) (b₂ := -σ + 3)
    (by ring) (by ring) (by ring) (by ring)
  have G₃ := left_recurrence_of_eq x (a := σ - 3) (b := -σ + 1) (a₁ := σ - 4)
    (a₂ := σ - 5) (b₁ := -σ + 2) (b₂ := -σ + 3)
    (by ring) (by ring) (by ring) (by ring)
  have G₄ := left_recurrence_of_eq x (a := σ - 3) (b := -σ + 2) (a₁ := σ - 4)
    (a₂ := σ - 5) (b₁ := -σ + 3) (b₂ := -σ + 4)
    (by ring) (by ring) (by ring) (by ring)
  have G₅ := left_recurrence_of_eq x (a := σ - 4) (b := -σ + 2) (a₁ := σ - 5)
    (a₂ := σ - 6) (b₁ := -σ + 3) (b₂ := -σ + 4)
    (by ring) (by ring) (by ring) (by ring)
  have D₁ := extendedContinuant_det_start x (σ - 3) (-σ + 2)
  rw [show σ - 3 - 2 = σ - 5 by ring, show -σ + 2 + 1 = -σ + 3 by ring,
    show σ - 3 - 1 = σ - 4 by ring, show σ - 3 + 1 = σ - 2 by ring,
    Int.negOnePow_odd _ ⟨t - 1, by omega⟩, Units.val_neg, Units.val_one] at D₁
  have D₂ := extendedContinuant_det_start x (σ - 2) (-σ + 1)
  rw [show σ - 2 - 2 = σ - 4 by ring, show -σ + 1 + 1 = -σ + 2 by ring,
    show σ - 2 - 1 = σ - 3 by ring, show σ - 2 + 1 = σ - 1 by ring,
    Int.negOnePow_even _ ⟨t, by omega⟩, Units.val_one] at D₂
  have hx₁ : x (-σ + 1) = -extendedContinuant x (σ - 5) (-σ + 3) -
      z 0 * extendedContinuant x (σ - 4) (-σ + 3) := by
    linear_combination extendedContinuant x (σ - 4) (-σ + 3) * (F₂ - G₃) +
      extendedContinuant x (σ - 5) (-σ + 3) * (G₂ - F₁) + x (-σ + 1) * D₁
  refine ⟨eq_of_forall_extendedContinuant_eq heast, ?_, hx₁, ?_, fun n hn => ?_⟩
  · linear_combination x (-σ + 2) * hx₁ - D₂ +
      extendedContinuant x (σ - 4) (-σ + 2) * F₁ -
      extendedContinuant x (σ - 3) (-σ + 2) * F₂ + G₅ + z 0 * G₄
  · linear_combination -G₁ + F₃ - x (-σ) * F₁
  · have h := neg_eq_of_forall_extendedContinuant_eq hwest
      (i := (n - σ).toNat) (by omega)
    rw [show -((n - σ).toNat : ℤ) - σ = -n by omega,
      show ((n - σ).toNat : ℤ) + 1 = n - σ + 1 by omega] at h
    exact h

/-! ### Periodic stretches with silent blocks -/

/-- If `x_b, …, x_{b+5}` is a block `p, q, r, p, q, r` with
`pqr + p + q + r = 0`, then the block can be dropped from the front of a
continuant: `K_a(x)_b = K_{a-6}(x)_{b+6}`. (The matrix
`[[p, 1], [1, 0]] [[q, 1], [1, 0]] [[r, 1], [1, 0]]` has trace
`pqr + p + q + r` and determinant `-1`, so its square is the identity.) -/
theorem extendedContinuant_eq_sub_six (x : ℤ → ℤ) {a b : ℤ}
    (h₃ : x (b + 3) = x b) (h₄ : x (b + 4) = x (b + 1))
    (h₅ : x (b + 5) = x (b + 2))
    (ht : x b * x (b + 1) * x (b + 2) + x b + x (b + 1) + x (b + 2) = 0) :
    extendedContinuant x a b = extendedContinuant x (a - 6) (b + 6) := by
  have e₀ := extendedContinuant_left_recurrence x a b
  have e₁ := left_recurrence_of_eq x (a := a - 1) (b := b + 1) (a₁ := a - 2)
    (a₂ := a - 3) (b₁ := b + 2) (b₂ := b + 3) (by ring) (by ring) (by ring)
    (by ring)
  have e₂ := left_recurrence_of_eq x (a := a - 2) (b := b + 2) (a₁ := a - 3)
    (a₂ := a - 4) (b₁ := b + 3) (b₂ := b + 4) (by ring) (by ring) (by ring)
    (by ring)
  have e₃ := left_recurrence_of_eq x (a := a - 3) (b := b + 3) (a₁ := a - 4)
    (a₂ := a - 5) (b₁ := b + 4) (b₂ := b + 5) (by ring) (by ring) (by ring)
    (by ring)
  have e₄ := left_recurrence_of_eq x (a := a - 4) (b := b + 4) (a₁ := a - 5)
    (a₂ := a - 6) (b₁ := b + 5) (b₂ := b + 6) (by ring) (by ring) (by ring)
    (by ring)
  have e₅ := left_recurrence_of_eq x (a := a - 5) (b := b + 5) (a₁ := a - 6)
    (a₂ := a - 7) (b₁ := b + 6) (b₂ := b + 7) (by ring) (by ring) (by ring)
    (by ring)
  rw [h₃] at e₃
  rw [h₄] at e₄
  rw [h₅] at e₅
  set p := x b
  set q := x (b + 1)
  set r := x (b + 2)
  set L₆ := extendedContinuant x (a - 6) (b + 6)
  set L₇ := extendedContinuant x (a - 7) (b + 7)
  have k₄ : extendedContinuant x (a - 4) (b + 4) =
      (q * r + 1) * L₆ + q * L₇ := by
    linear_combination e₄ + q * e₅
  have k₃ : extendedContinuant x (a - 3) (b + 3) =
      -q * L₆ + (p * q + 1) * L₇ := by
    linear_combination e₃ + p * k₄ + e₅ + L₆ * ht
  have k₂ : extendedContinuant x (a - 2) (b + 2) = L₆ - p * L₇ := by
    linear_combination e₂ + r * k₃ + k₄ + L₇ * ht
  have k₁ : extendedContinuant x (a - 1) (b + 1) = L₇ := by
    linear_combination e₁ + q * k₂ + k₃
  linear_combination e₀ + p * k₁ + k₂

/-- Dropping `k` silent blocks: if each block `x_{b+6t}, …, x_{b+6t+5}`
(`t < k`) satisfies the hypotheses of `extendedContinuant_eq_sub_six`, then
`K_a(x)_b = K_{a-6k}(x)_{b+6k}`. -/
theorem extendedContinuant_eq_sub_six_mul (x : ℤ → ℤ) {a b : ℤ} (k : ℕ)
    (hblock : ∀ t : ℕ, t < k →
      x (b + 6 * t + 3) = x (b + 6 * t) ∧
        x (b + 6 * t + 4) = x (b + 6 * t + 1) ∧
        x (b + 6 * t + 5) = x (b + 6 * t + 2) ∧
        x (b + 6 * t) * x (b + 6 * t + 1) * x (b + 6 * t + 2) + x (b + 6 * t) +
          x (b + 6 * t + 1) + x (b + 6 * t + 2) = 0) :
    extendedContinuant x a b =
      extendedContinuant x (a - 6 * k) (b + 6 * k) := by
  induction k with
  | zero => simp only [Nat.cast_zero, mul_zero, sub_zero, add_zero]
  | succ k ih =>
    obtain ⟨h₃, h₄, h₅, ht⟩ := hblock k (by omega)
    rw [ih fun t ht => hblock t (by omega),
      extendedContinuant_eq_sub_six x h₃ h₄ h₅ ht]
    congr 1 <;> push_cast <;> ring

/-- The tables (33) of Proposition 3 drop silent blocks: if
`x_j = -1` for `j ≡ -σ (mod 3)` and `x_j = 1` otherwise, for
`-σ + 3 ≤ j ≤ -4`, then continuants starting in this range drop `k` blocks of
six terms as long as the blocks stay in the range. -/
private theorem silentTable_reduce (x : ℤ → ℤ) {σ b : ℤ}
    (htab : ∀ j : ℤ, -σ + 3 ≤ j → j ≤ -4 →
      x j = if (j + σ) % 3 = 0 then -1 else 1)
    (hb : -σ + 3 ≤ b) (k : ℕ) (hk : b + 6 * k ≤ -3) (a : ℤ) :
    extendedContinuant x a b =
      extendedContinuant x (a - 6 * k) (b + 6 * k) := by
  refine extendedContinuant_eq_sub_six_mul x k fun t ht => ?_
  have hv : ∀ i : ℤ, 0 ≤ i → i ≤ 5 → x (b + 6 * t + i) =
      if (b + 6 * t + i + σ) % 3 = 0 then -1 else 1 :=
    fun i h₀ h₅ => htab _ (by omega) (by omega)
  have v₀ := hv 0 le_rfl (by norm_num)
  rw [add_zero] at v₀
  rw [hv 1 (by norm_num) (by norm_num), hv 2 (by norm_num) (by norm_num),
    hv 3 (by norm_num) (by norm_num), hv 4 (by norm_num) (by norm_num),
    hv 5 (by norm_num) (by norm_num), v₀]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-- The continuants left over in Proposition 3 when `σ ≡ 1 (mod 6)`. -/
private theorem silentTable_eval_one (x : ℤ → ℤ) {X : ℤ} (h₄ : x (-4) = -1)
    (h₃ : x (-3) = X) (h₂ : x (-2) = 1) (h₁ : x (-1) = -1) :
    extendedContinuant x 2 (-4) = -X ∧ extendedContinuant x 3 (-4) = 1 ∧
      extendedContinuant x 1 (-3) = X + 1 ∧
      extendedContinuant x 2 (-3) = -1 := by
  simp only [extendedContinuant_recurrence x 3 (-4),
    extendedContinuant_recurrence x 2 (-4),
    extendedContinuant_recurrence x 1 (-4),
    extendedContinuant_recurrence x 2 (-3),
    extendedContinuant_recurrence x 1 (-3), extendedContinuant_zero,
    extendedContinuant_neg_one, Int.reduceAdd, Int.reduceSub, h₄, h₃, h₂, h₁]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The continuants left over in Proposition 3 when `σ ≡ 5 (mod 6)`. -/
private theorem silentTable_eval_five (x : ℤ → ℤ) {X : ℤ} (h₈ : x (-8) = -1)
    (h₇ : x (-7) = 1) (h₆ : x (-6) = 1) (h₅ : x (-5) = -1) (h₄ : x (-4) = 1)
    (h₃ : x (-3) = X) (h₂ : x (-2) = 1) (h₁ : x (-1) = -1) :
    extendedContinuant x 6 (-8) = 1 ∧ extendedContinuant x 7 (-8) = 0 ∧
      extendedContinuant x 5 (-7) = X ∧ extendedContinuant x 6 (-7) = -1 := by
  simp only [extendedContinuant_recurrence x 7 (-8),
    extendedContinuant_recurrence x 6 (-8),
    extendedContinuant_recurrence x 5 (-8),
    extendedContinuant_recurrence x 4 (-8),
    extendedContinuant_recurrence x 3 (-8),
    extendedContinuant_recurrence x 2 (-8),
    extendedContinuant_recurrence x 1 (-8),
    extendedContinuant_recurrence x 6 (-7),
    extendedContinuant_recurrence x 5 (-7),
    extendedContinuant_recurrence x 4 (-7),
    extendedContinuant_recurrence x 3 (-7),
    extendedContinuant_recurrence x 2 (-7),
    extendedContinuant_recurrence x 1 (-7), extendedContinuant_zero,
    extendedContinuant_neg_one, Int.reduceAdd, Int.reduceSub, h₈, h₇, h₆, h₅,
    h₄, h₃, h₂, h₁]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- Proposition 3, case `σ ≡ 1 (mod 6)`, `σ ≥ 7`: with `x_{-3} = x_0 + c₁`,
`x_{-2} = 1`, `x_{-1} = -1`, `z_0 = x_0 + c₂` (`c₁ ≠ c₂`) and, for
`4 ≤ m ≤ σ - 3`, `x_{-m} = -1` if `m ≡ 1 (mod 3)` and `x_{-m} = 1` otherwise
(table (33)), the value `w = -K_{σ-5}(x)_{-σ+3} - z_0 K_{σ-4}(x)_{-σ+3}` that
formula (29) assigns to `x_{-σ+1}` is nonzero and formula (29) gives
`x_{-σ+2} = 1`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Proposition 3 (case `σ ≡ 1 mod 6`).

Proves `Wanted` entry `silentTerms_table_one_mod_six`. -/
theorem silentTerms_table_one_mod_six (x : ℤ → ℤ) (σ : ℤ) (hσ : σ % 6 = 1)
    (h7 : 7 ≤ σ) (c₁ c₂ : ℤ) (hc : c₁ ≠ c₂) (h3 : x (-3) = x 0 + c₁)
    (h2 : x (-2) = 1)
    (h1 : x (-1) = -1)
    (htab : ∀ m : ℤ, 4 ≤ m → m ≤ σ - 3 → x (-m) = if m % 3 = 1 then -1 else 1) :
    -extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3) ≠ 0 ∧
      -1 + extendedContinuant x (σ - 6) (-σ + 4) +
          (x 0 + c₂) * extendedContinuant x (σ - 5) (-σ + 4) =
        1 * (-extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, σ = 6 * q + 7 := ⟨((σ - 7) / 6).toNat, by omega⟩
  have htab' : ∀ j : ℤ, -σ + 3 ≤ j → j ≤ -4 →
      x j = if (j + σ) % 3 = 0 then -1 else 1 := by
    intro j hj₁ hj₂
    rw [← neg_neg j, htab (-j) (by omega) (by omega), neg_neg]
    split_ifs <;> omega
  have h4 := htab 4 (by norm_num) (by omega)
  rw [ite_eq_left (by norm_num)] at h4
  obtain ⟨e₁, e₂, e₃, e₄⟩ := silentTable_eval_one x h4 h3 h2 h1
  rw [silentTable_reduce x htab' le_rfl q (by omega) (σ - 5),
    silentTable_reduce x htab' le_rfl q (by omega) (σ - 4),
    silentTable_reduce x htab' (b := -σ + 4) (by omega) q (by omega) (σ - 6),
    silentTable_reduce x htab' (b := -σ + 4) (by omega) q (by omega) (σ - 5),
    show σ - 5 - 6 * (q : ℤ) = 2 by omega,
    show -σ + 3 + 6 * (q : ℤ) = -4 by omega,
    show σ - 4 - 6 * (q : ℤ) = 3 by omega,
    show σ - 6 - 6 * (q : ℤ) = 1 by omega,
    show -σ + 4 + 6 * (q : ℤ) = -3 by omega, e₁, e₂, e₃, e₄]
  constructor
  · intro h
    exact hc (by linear_combination h)
  · ring

-- `hc` is part of the source statement but is not needed in this case: the
-- value `w` is `-1` whatever `c₁` and `c₂` are.
set_option linter.unusedVariables false in
/-- Proposition 3, case `σ ≡ 5 (mod 6)`, `σ ≥ 7`: with `x_{-3} = x_0 + c₁`,
`x_{-2} = 1`, `x_{-1} = -1`, `z_0 = x_0 + c₂` (`c₁ ≠ c₂`) and, for
`4 ≤ m ≤ σ - 3`, `x_{-m} = -1` if `m ≡ 2 (mod 3)` and `x_{-m} = 1` otherwise
(table (33)), the value `w = -K_{σ-5}(x)_{-σ+3} - z_0 K_{σ-4}(x)_{-σ+3}` that
formula (29) assigns to `x_{-σ+1}` is nonzero and formula (29) gives
`x_{-σ+2} = 1 + c₂ - c₁`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73, Proposition 3 (case `σ ≡ 5 mod 6`).

Proves `Wanted` entry `silentTerms_table_five_mod_six`. -/
theorem silentTerms_table_five_mod_six (x : ℤ → ℤ) (σ : ℤ) (hσ : σ % 6 = 5)
    (h7 : 7 ≤ σ) (c₁ c₂ : ℤ) (hc : c₁ ≠ c₂) (h3 : x (-3) = x 0 + c₁)
    (h2 : x (-2) = 1)
    (h1 : x (-1) = -1)
    (htab : ∀ m : ℤ, 4 ≤ m → m ≤ σ - 3 → x (-m) = if m % 3 = 2 then -1 else 1) :
    -extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3) ≠ 0 ∧
      -1 + extendedContinuant x (σ - 6) (-σ + 4) +
          (x 0 + c₂) * extendedContinuant x (σ - 5) (-σ + 4) =
        (1 + c₂ - c₁) * (-extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, σ = 6 * q + 11 := ⟨((σ - 11) / 6).toNat, by omega⟩
  have htab' : ∀ j : ℤ, -σ + 3 ≤ j → j ≤ -4 →
      x j = if (j + σ) % 3 = 0 then -1 else 1 := by
    intro j hj₁ hj₂
    rw [← neg_neg j, htab (-j) (by omega) (by omega), neg_neg]
    split_ifs <;> omega
  have hv : ∀ m : ℤ, 4 ≤ m → m ≤ 8 → x (-m) = if m % 3 = 2 then -1 else 1 :=
    fun m hm₁ hm₂ => htab m hm₁ (by omega)
  have h8 := hv 8 (by norm_num) le_rfl
  have h7' := hv 7 (by norm_num) (by norm_num)
  have h6 := hv 6 (by norm_num) (by norm_num)
  have h5 := hv 5 (by norm_num) (by norm_num)
  have h4 := hv 4 le_rfl (by norm_num)
  rw [ite_eq_left (by norm_num)] at h8 h5
  rw [ite_eq_right (by norm_num)] at h7' h6 h4
  obtain ⟨e₁, e₂, e₃, e₄⟩ := silentTable_eval_five x h8 h7' h6 h5 h4 h3 h2 h1
  rw [silentTable_reduce x htab' le_rfl q (by omega) (σ - 5),
    silentTable_reduce x htab' le_rfl q (by omega) (σ - 4),
    silentTable_reduce x htab' (b := -σ + 4) (by omega) q (by omega) (σ - 6),
    silentTable_reduce x htab' (b := -σ + 4) (by omega) q (by omega) (σ - 5),
    show σ - 5 - 6 * (q : ℤ) = 6 by omega,
    show -σ + 3 + 6 * (q : ℤ) = -8 by omega,
    show σ - 4 - 6 * (q : ℤ) = 7 by omega,
    show σ - 6 - 6 * (q : ℤ) = 5 by omega,
    show -σ + 4 + 6 * (q : ℤ) = -7 by omega, e₁, e₂, e₃, e₄]
  constructor
  · norm_num
  · ring

end

end MetaMathlibExt
