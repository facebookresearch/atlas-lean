/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

/-!
# Extended continuants and bi-infinite periodic continued fractions

Statements from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73.

For a bi-infinite integer sequence `x : ℤ → ℤ`, `extendedContinuant x a b` is the paper's
extended continuant `K_a(x)_b^{a+b}` of order `a ∈ ℤ` on the consecutive terms starting at
index `b` (Definitions 3 and 4, right-adjusting recurrence): `K_{-2} = 0`, `K_{-1} = 1`, and
`K_a = x_{b+a} K_{a-1} + K_{a-2}` for every integer order `a`
(`extendedContinuant_recurrence`).

In Sections 4–6 a bi-infinite sequence `x` has raw rational convergents
`k_n = K_n(x)_0 / K_{n-1}(x)_1` (numerator and denominator kept separately); `c_i` and `d_i`
are the raw convergents `K_i(y)_0 / K_{i-1}(y)_1` and `K_i(z)_0 / K_{i-1}(z)_1` of the
eastbound SCF terms `y` of `α` and `z` of `ᾱ` (only indices `≥ 0` of `y`, `z` matter).
Strict equivalence of raw rationals is equality of numerators and of denominators. The
statements below keep only the strict-equivalence hypotheses on the convergents; the
periodicity and limit conditions of a BpCF (Definition 5) are not used by the paper's proofs
and are dropped, so each statement applies to every bi-infinite integer sequence.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Forward branch of the extended continuant with start index `b`: the value at `n` is
`K_{n-2}(x)_b`, so `0 ↦ 0`, `1 ↦ 1`, and `n + 2 ↦ x_{b+n} K_{n-1} + K_{n-2}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definition 3 (right-adjusting recurrence). -/
public def extendedContinuantFwd (x : ℤ → ℤ) (b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => x (b + n) * extendedContinuantFwd x b (n + 1) + extendedContinuantFwd x b n

/-- Backward branch of the extended continuant with start index `b`: the value at `m` is
`K_{-1-m}(x)_b`, so `0 ↦ 1`, `1 ↦ 0`, and `m + 2 ↦ -x_{b-1-m} K_{-2-m} + K_{-1-m}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definition 4 (right-adjusting recurrence). -/
public def extendedContinuantBwd (x : ℤ → ℤ) (b : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | m + 2 => -x (b - 1 - m) * extendedContinuantBwd x b (m + 1) + extendedContinuantBwd x b m

/-- The extended continuant `K_a(x)_b^{a+b}` of order `a ∈ ℤ` with start index `b`
(Definitions 3 and 4 of the paper, right-adjusting form).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
public def extendedContinuant (x : ℤ → ℤ) (a b : ℤ) : ℤ :=
  if 0 ≤ a + 2 then extendedContinuantFwd x b (a + 2).toNat
  else extendedContinuantBwd x b (-1 - a).toNat

private theorem extendedContinuant_eq_fwd (x : ℤ → ℤ) (b : ℤ) {a : ℤ} {n : ℕ}
    (h : a + 2 = n) : extendedContinuant x a b = extendedContinuantFwd x b n := by
  unfold extendedContinuant
  split_ifs
  · congr 1
    omega
  · omega

private theorem extendedContinuant_eq_bwd (x : ℤ → ℤ) (b : ℤ) {a : ℤ} {m : ℕ}
    (h : a = -1 - m) : extendedContinuant x a b = extendedContinuantBwd x b m := by
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

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
public theorem extendedContinuant_neg_two (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x (-2) b = 0 :=
  extendedContinuant_eq_fwd x b (n := 0) (by omega)

/-- `K_{-1}(x)_b = 1`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4. -/
public theorem extendedContinuant_neg_one (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x (-1) b = 1 :=
  extendedContinuant_eq_fwd x b (n := 1) (by omega)

/-- `K_0(x)_b^b = x_b`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Section 3.4 and Equation (13). -/
public theorem extendedContinuant_zero (x : ℤ → ℤ) (b : ℤ) :
    extendedContinuant x 0 b = x b := by
  rw [extendedContinuant_eq_fwd x b (n := 2) (by omega)]
  simp [extendedContinuantFwd]

/-- The right-adjusting recurrence `K_a(x)_b = x_{b+a} K_{a-1}(x)_b + K_{a-2}(x)_b` holds for
every integer order `a` (for `a ≤ -1` it is the paper's backward recurrence of Definition 4).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Definitions 3 and 4 (RA versions). -/
public theorem extendedContinuant_recurrence (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x a b =
      x (b + a) * extendedContinuant x (a - 1) b + extendedContinuant x (a - 2) b := by
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

/-- Lemma 1: `K_{-3}(x)_h = 1`, `K_{-4}(x)_h = -x_{h-2}`, `K_{-5}(x)_h = 1 + x_{h-3} x_{h-2}`, and
`K_{-6}(x)_h = -(x_{h-4} + x_{h-2} + x_{h-4} x_{h-3} x_{h-2})`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Lemma 1. -/
public theorem extendedContinuant_neg_three_to_six (x : ℤ → ℤ) (h : ℤ) :
    extendedContinuant x (-3) h = 1 ∧ extendedContinuant x (-4) h = -x (h - 2) ∧
      extendedContinuant x (-5) h = 1 + x (h - 3) * x (h - 2) ∧
      extendedContinuant x (-6) h = -(x (h - 4) + x (h - 2) + x (h - 4) * x (h - 3) * x (h - 2)) := by
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
  have h4 : extendedContinuant x (-4) h = -x (h - 2) := by rw [k2, h3] at e2; linarith
  have h5 : extendedContinuant x (-5) h = 1 + x (h - 3) * x (h - 2) := by
    rw [h3, h4] at e3; linarith
  refine ⟨h3, h4, h5, ?_⟩
  rw [h4, h5] at e4
  linear_combination -e4

/-- Proposition 1: for `n ≥ 1`, the westbound matrix product
`∏_{i=n}^{1} [[0, 1], [1, -x_{-i}]]` (factor `i = n` leftmost) equals
`[[K_{-n-1}(x)_0, K_{-n-2}(x)_1], [K_{-n-2}(x)_0, K_{-n-3}(x)_1]]`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Proposition 1. -/
public theorem_wanted extendedContinuant_westbound_matrix_prod (x : ℤ → ℤ) (n : ℕ)
    (hn : 1 ≤ n) :
    (List.ofFn fun i : Fin n => !![0, 1; 1, -x (-((n : ℤ) - i))]).prod =
      !![extendedContinuant x (-n - 1) 0, extendedContinuant x (-n - 2) 1;
        extendedContinuant x (-n - 2) 0, extendedContinuant x (-n - 3) 1]

/-- Theorem 1: for all `h, n ∈ ℤ`, `K_{-n}(x)_h^{h-n} = (-1)^{n+1} K_{n-4}(x)_{h-n+2}^{h-2}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 1. -/
public theorem_wanted extendedContinuant_neg_order (x : ℤ → ℤ) (h n : ℤ) :
    extendedContinuant x (-n) h =
      ((n + 1).negOnePow : ℤ) * extendedContinuant x (n - 4) (h - n + 2)

/-- Theorem 2 (Bennett): for nonnegative integers `k, ℓ, m, n`,
`(-1)^{k+ℓ} K_{n-k-2}(x)_k K_{m-ℓ-2}(x)_ℓ + (-1)^{ℓ+m} K_{n-ℓ-2}(x)_ℓ K_{k-m-2}(x)_m
+ (-1)^{m+k} K_{n-m-2}(x)_m K_{ℓ-k-2}(x)_k = 0`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 2 (after G. T. Bennett, 1939). -/
public theorem_wanted extendedContinuant_bennett_nat (x : ℤ → ℤ) (k ℓ m n : ℕ) :
    ((k + ℓ : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - k - 2) k *
        extendedContinuant x ((m : ℤ) - ℓ - 2) ℓ +
      ((ℓ + m : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - ℓ - 2) ℓ *
        extendedContinuant x ((k : ℤ) - m - 2) m +
      ((m + k : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - m - 2) m *
        extendedContinuant x ((ℓ : ℤ) - k - 2) k = 0

/-- Theorem 3: Bennett's symmetric identity (Theorem 2) holds for all integers `k, ℓ, m, n`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 3. -/
public theorem_wanted extendedContinuant_bennett (x : ℤ → ℤ) (k ℓ m n : ℤ) :
    ((k + ℓ).negOnePow : ℤ) * extendedContinuant x (n - k - 2) k *
        extendedContinuant x (m - ℓ - 2) ℓ +
      ((ℓ + m).negOnePow : ℤ) * extendedContinuant x (n - ℓ - 2) ℓ *
        extendedContinuant x (k - m - 2) m +
      ((m + k).negOnePow : ℤ) * extendedContinuant x (n - m - 2) m *
        extendedContinuant x (ℓ - k - 2) k = 0

/-- Corollary 1 (Euler's continuant identity, extended): for all `h, k, ℓ, m ∈ ℤ`,
`K_{ℓ+m}(x)_h K_{k-1}(x)_{ℓ+h+1} - K_{m-1}(x)_{ℓ+h+1} K_{k+ℓ}(x)_h
= (-1)^k K_{m-k-2}(x)_{k+ℓ+h+2} K_{ℓ-1}(x)_h`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Corollary 1. -/
public theorem_wanted extendedContinuant_euler (x : ℤ → ℤ) (h k ℓ m : ℤ) :
    extendedContinuant x (ℓ + m) h * extendedContinuant x (k - 1) (ℓ + h + 1) -
        extendedContinuant x (m - 1) (ℓ + h + 1) * extendedContinuant x (k + ℓ) h =
      (k.negOnePow : ℤ) * extendedContinuant x (m - k - 2) (k + ℓ + h + 2) *
        extendedContinuant x (ℓ - 1) h

/-- Corollary 2: for all `n ∈ ℤ`,
`K_n(x)_0 K_{n-2}(x)_1 - K_{n-1}(x)_1 K_{n-1}(x)_0 = (-1)^{n+1}`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Corollary 2. -/
public theorem_wanted extendedContinuant_det (x : ℤ → ℤ) (n : ℤ) :
    extendedContinuant x n 0 * extendedContinuant x (n - 2) 1 -
        extendedContinuant x (n - 1) 1 * extendedContinuant x (n - 1) 0 =
      ((n + 1).negOnePow : ℤ)

/-- Theorem 4: for even `σ ≥ 0` there is no `σ`-silent bi-infinite sequence: no `x : ℤ → ℤ`
has raw westbound convergents `k_{-i-σ-1}` strictly equivalent to the raw convergents `d_i`
of `z` for all `i ≥ 0`. Stated for every pair of integer sequences `x`, `z` (the BpCF
conditions are not needed).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 4. -/
public theorem_wanted not_silent_of_even (x z : ℤ → ℤ) (σ : ℕ) (hσ : Even σ) :
    ¬ ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - σ - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1

/-- Theorem 5 (1-silent BpCFs): if `k_i ≐ c_i` and `k_{-i-2} ≐ d_i` for all `i ≥ 0`, then
`x_n = y_n` for `n ≥ 0`, `x_{-n} = -z_n` for `n ≥ 1`, and `z_0 = 0` (the paper's `0 < ᾱ < 1`
for the EA-generated SCF of the irrational `ᾱ`).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 5. -/
public theorem_wanted oneSilent_terms (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 2) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 3) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧ (∀ n : ℕ, 1 ≤ n → x (-(n : ℤ)) = -z n) ∧ z 0 = 0

/-- Theorem 6 (3-silent BpCFs), with the paper's choice `x_{-1} = 0`: if `k_i ≐ c_i` and
`k_{-i-4} ≐ d_i` for all `i ≥ 0` and `x_{-1} = 0`, then `x_n = y_n` for `n ≥ 0` and
`x_{-n} = -z_{n-2}` for `n ≥ 2`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 6 and its proof (option 2, `x_{-1} = 0`). -/
public theorem_wanted threeSilent_terms (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 4) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 5) 1 = extendedContinuant z ((i : ℤ) - 1) 1)
    (hx : x (-1) = 0) :
    (∀ n : ℕ, x n = y n) ∧ ∀ n : ℕ, 2 ≤ n → x (-(n : ℤ)) = -z ((n : ℤ) - 2)

/-- Theorem 7 (`σ`-silent BpCFs, `σ = 2j + 1 ≥ 5`): if `k_i ≐ c_i` and `k_{-i-σ-1} ≐ d_i` for
all `i ≥ 0`, then `x_n = y_n` for `n ≥ 0`, `x_{-σ+2} x_{-σ+1}` equals
`-1 + K_{σ-6}(x)_{-σ+4} + z_0 K_{σ-5}(x)_{-σ+4}` (the paper's quotient formula multiplied out),
`x_{-σ+1} = -K_{σ-5}(x)_{-σ+3} - z_0 K_{σ-4}(x)_{-σ+3}`,
`x_{-σ} = -K_{σ-3}(x)_{-σ+2} - z_1`, and `x_{-n} = -z_{n-σ+1}` for `n ≥ σ + 1`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 7. -/
public theorem_wanted oddSilent_terms (x y z : ℤ → ℤ) (σ : ℤ) (hσ : Odd σ) (h5 : 5 ≤ σ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - σ - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧
      x (-σ + 2) * x (-σ + 1) = -1 + extendedContinuant x (σ - 6) (-σ + 4) +
        z 0 * extendedContinuant x (σ - 5) (-σ + 4) ∧
      x (-σ + 1) = -extendedContinuant x (σ - 5) (-σ + 3) -
        z 0 * extendedContinuant x (σ - 4) (-σ + 3) ∧
      x (-σ) = -extendedContinuant x (σ - 3) (-σ + 2) - z 1 ∧
      ∀ n : ℤ, σ + 1 ≤ n → x (-n) = -z (n - σ + 1)

/-- Proposition 3, case `σ ≡ 1 (mod 6)`, `σ ≥ 7`: with `x_{-3} = x_0 + c₁`, `x_{-2} = 1`,
`x_{-1} = -1`, `z_0 = x_0 + c₂` (`c₁ ≠ c₂`) and, for `4 ≤ m ≤ σ - 3`, `x_{-m} = -1` if
`m ≡ 1 (mod 3)` and `x_{-m} = 1` otherwise (table (33)), the value
`w = -K_{σ-5}(x)_{-σ+3} - z_0 K_{σ-4}(x)_{-σ+3}` that formula (29) assigns to `x_{-σ+1}` is
nonzero and formula (29) gives `x_{-σ+2} = 1`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Proposition 3 (case `σ ≡ 1 mod 6`). -/
public theorem_wanted silentTerms_table_one_mod_six (x : ℤ → ℤ) (σ : ℤ) (hσ : σ % 6 = 1)
    (h7 : 7 ≤ σ) (c₁ c₂ : ℤ) (hc : c₁ ≠ c₂) (h3 : x (-3) = x 0 + c₁) (h2 : x (-2) = 1)
    (h1 : x (-1) = -1)
    (htab : ∀ m : ℤ, 4 ≤ m → m ≤ σ - 3 → x (-m) = if m % 3 = 1 then -1 else 1) :
    -extendedContinuant x (σ - 5) (-σ + 3) - (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)
        ≠ 0 ∧
      -1 + extendedContinuant x (σ - 6) (-σ + 4) +
          (x 0 + c₂) * extendedContinuant x (σ - 5) (-σ + 4) =
        1 * (-extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3))

/-- Proposition 3, case `σ ≡ 5 (mod 6)`, `σ ≥ 7`: with `x_{-3} = x_0 + c₁`, `x_{-2} = 1`,
`x_{-1} = -1`, `z_0 = x_0 + c₂` (`c₁ ≠ c₂`) and, for `4 ≤ m ≤ σ - 3`, `x_{-m} = -1` if
`m ≡ 2 (mod 3)` and `x_{-m} = 1` otherwise (table (33)), the value
`w = -K_{σ-5}(x)_{-σ+3} - z_0 K_{σ-4}(x)_{-σ+3}` that formula (29) assigns to `x_{-σ+1}` is
nonzero and formula (29) gives `x_{-σ+2} = 1 + c₂ - c₁`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Proposition 3 (case `σ ≡ 5 mod 6`). -/
public theorem_wanted silentTerms_table_five_mod_six (x : ℤ → ℤ) (σ : ℤ) (hσ : σ % 6 = 5)
    (h7 : 7 ≤ σ) (c₁ c₂ : ℤ) (hc : c₁ ≠ c₂) (h3 : x (-3) = x 0 + c₁) (h2 : x (-2) = 1)
    (h1 : x (-1) = -1)
    (htab : ∀ m : ℤ, 4 ≤ m → m ≤ σ - 3 → x (-m) = if m % 3 = 2 then -1 else 1) :
    -extendedContinuant x (σ - 5) (-σ + 3) - (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)
        ≠ 0 ∧
      -1 + extendedContinuant x (σ - 6) (-σ + 4) +
          (x 0 + c₂) * extendedContinuant x (σ - 5) (-σ + 4) =
        (1 + c₂ - c₁) * (-extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3))

/-- Lemma 3: for conjugate real quadratic irrationals `α = (P + √D)/Q > ᾱ = (P - √D)/Q`
(`D > 0` not a square, `Q > 0`), the simple continued fraction of `ᾱ` is not purely periodic,
i.e. it has at least one nonperiodic term (`ṙ ≥ 1`). The terms are the integer parts `b` of
Mathlib's continued-fraction stream `GenContFract.IntFractPair.stream`.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Lemma 3. -/
public theorem_wanted conjugate_continuedFraction_not_purelyPeriodic (P Q D : ℤ) (hD : 0 < D)
    (hsq : ¬ IsSquare D) (hQ : 0 < Q) :
    ¬ ∃ s : ℕ, 0 < s ∧ ∀ n : ℕ,
      (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) (n + s)).map (·.b) =
        (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) n).map (·.b)

end

end MetaMathlibExt
