/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Basic.Real.Basic

/-!
# Kamano, generalized Landen connection formula and poly-Bernoulli numbers — wishlist

Statement-only records for Ken Kamano's INTEGERS 24 (2024) paper. Everything is
formal: power series live in `ℝ⟦X⟧`, and the iterated integrals
`∫₀^z G_{g_i}(u) f(u) du` of the paper are realised coefficientwise.

* For `g = (a b; c d) ∈ GL₂(ℝ)` the paper's `G_g(t) = c/(a - c t) - d/(b - d t)`
  has at most a simple pole at `0` (when `a = 0` or `b = 0`), so we store the
  power series `u · G_g(u)` (`landenFormSeries`).
* For `h` with zero constant term, `∫₀^z h(u) du / u` has coefficients
  `[z^n] = [u^n] h / n` (`integralDivX`); every integration step of the paper is
  `integralDivX (u G(u) · f(u))` because each polylogarithm has no constant term.
* Indices `k ∈ ℤ_{>0}^r` are the blocks of a `Composition` (so `|k|` is the
  composition's total and `d(k)` its length). The arrow notation of the paper is
  `k↑ = k.modifyLast (· + 1)` and `k→ = k ++ [1]`.
* Substituting a series into a series is `PowerSeries.subst`; the variable
  `z(t) = (e^t - 1)/(c₀ e^t + d₀)` is `landenExpVariable`.

Theorem 5 is false as printed with the paper's own definitions (see the
docstring of `generalizedPolyBernoulliC_landen`); it is stated in the reading
its proof establishes.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- The power series of `c u / (a - c u)` for `(a, c) ≠ (0, 0)`: for `a ≠ 0` it is
`∑_{n ≥ 1} (c/a)^n u^n`, and for `a = 0` it is the constant `-1`. (For
`a = c = 0` it is `0`, a junk value.) It is `u` times the summand `c/(a - c u)` of
the paper's `G_g(u)`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the function `G_g(t)` before Table 1. -/
public noncomputable def linearFractionalPoleSeries (a c : ℝ) : ℝ⟦X⟧ :=
  if a = 0 then (if c = 0 then 0 else -1)
  else mk fun n => if n = 0 then 0 else (c / a) ^ n

/-- `linearFractionalPoleSeries a c` solves `(a - c u) · F(u) = c u`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the function `G_g(t)` before Table 1. -/
public theorem linearFractionalPoleSeries_spec (a c : ℝ) :
    (C a - C c * X) * linearFractionalPoleSeries a c = C c * X := by
  unfold linearFractionalPoleSeries
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · simp [ha, hc]
    · simp [ha, hc]
  · simp only [ha, ite_false]
    ext n
    rw [sub_mul, map_sub, coeff_C_mul, mul_assoc, coeff_C_mul]
    rcases n with _ | _ | n
    · simp
    · simp [coeff_succ_X_mul]
      field_simp
    · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_C_mul, coeff_X]
      have h1 : n + 1 + 1 ≠ 1 := by omega
      simp only [Nat.succ_ne_zero, ite_false, h1, mul_zero]
      rw [pow_succ (c / a) (n + 1)]
      field_simp
      ring

/-- The power series `u · G_g(u) = c u/(a - c u) - d u/(b - d u)` attached to a
matrix `g = (a b; c d) ∈ GL₂(ℝ)`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the function `G_g(t)` before Table 1. -/
public noncomputable def landenFormSeries (a b c d : ℝ) : ℝ⟦X⟧ :=
  linearFractionalPoleSeries a c - linearFractionalPoleSeries b d

/-- For the identity matrix, `G_g(t) = 1/t` (Table 1), i.e. `u · G_g(u) = 1`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Table 1. -/
public theorem landenFormSeries_identity : landenFormSeries 1 0 0 1 = 1 := by
  ext n
  rcases n with _ | n <;> simp [landenFormSeries, linearFractionalPoleSeries]

/-- The formal integral `h ↦ ∫₀^z h(u) du / u`, coefficientwise
`[z^n] = [u^n] h / n` (and `[z^0] = 0`); it is the integral of the paper when `h`
has zero constant term.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the integrals defining `Li_k(g; (β, γ); z)`. -/
public noncomputable def integralDivX (h : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  mk fun n => coeff n h / n

/-- `integralDivX h` has no constant term and `z · d/dz (integralDivX h) = h`
whenever `h` has no constant term.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the integrals defining `Li_k(g; (β, γ); z)`. -/
public theorem integralDivX_spec (h : ℝ⟦X⟧) (h0 : constantCoeff h = 0) :
    constantCoeff (integralDivX h) = 0 ∧ X * derivative (integralDivX h) = h := by
  refine ⟨by rw [← coeff_zero_eq_constantCoeff_apply]; simp [integralDivX], ?_⟩
  ext n
  rcases n with _ | n
  · rw [coeff_zero_eq_constantCoeff_apply] at *
    simp [h0]
  · rw [coeff_succ_X_mul, coeff_derivative, integralDivX, coeff_mk]
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at this ⊢
    field_simp

/-- The data `g = (g₀, g₁, …, g_s)` of the paper: `g₀ = (1 -1; c₀ d₀)` and
`g_i = (a_i b_i; c_i d_i)` for `1 ≤ i ≤ s` (indexed here by `Fin s`).

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public structure LandenData where
  /-- The number `s` of matrices `g_1, …, g_s`. -/
  s : ℕ
  /-- The entry `c₀` of `g₀ = (1 -1; c₀ d₀)`. -/
  c₀ : ℝ
  /-- The entry `d₀` of `g₀ = (1 -1; c₀ d₀)`. -/
  d₀ : ℝ
  /-- The upper-left entries `a_i` of `g_i`. -/
  a : Fin s → ℝ
  /-- The upper-right entries `b_i` of `g_i`. -/
  b : Fin s → ℝ
  /-- The lower-left entries `c_i` of `g_i`. -/
  c : Fin s → ℝ
  /-- The lower-right entries `d_i` of `g_i`. -/
  d : Fin s → ℝ

namespace LandenData

/-- The transformed data `g̃`, with `g̃_i = (1 0; c₀ - d₀ -1) g_i`; thus
`g̃₀ = (1 -1; -d₀ -c₀)` and `g̃_i = (a_i b_i; (c₀ - d₀) a_i - c_i (c₀ - d₀) b_i - d_i)`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
display before Theorem 2. -/
public def tilde (D : LandenData) : LandenData where
  s := D.s
  c₀ := -D.d₀
  d₀ := -D.c₀
  a := D.a
  b := D.b
  c := fun i => (D.c₀ - D.d₀) * D.a i - D.c i
  d := fun i => (D.c₀ - D.d₀) * D.b i - D.d i

/-- The operation `g ↦ g̃` is an involution.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
remark before Theorem 2. -/
public theorem tilde_tilde (D : LandenData) : D.tilde.tilde = D := by
  cases D
  simp only [tilde, mk.injEq, neg_neg, heq_eq_eq, true_and]
  constructor <;> funext i <;> ring

/-- The power series `u · ∑_i w_i G_{g_i}(u)` of the weighted differential form.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
definition of `Li_k(g; (β, γ); z)`. -/
public noncomputable def formSeries (D : LandenData) (w : Fin D.s → ℝ) : ℝ⟦X⟧ :=
  ∑ i, C (w i) * landenFormSeries (D.a i) (D.b i) (D.c i) (D.d i)

/-- Auxiliary recursion for `generalizedMultiplePolylog`, on the reversed index
(head = last entry `k_r`). Lists with a zero entry, and the empty list, give `0`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
display (6) and the two inductive integrals before it. -/
public noncomputable def polylogRev (D : LandenData) (β γ : Fin D.s → ℝ) :
    List ℕ → ℝ⟦X⟧
  | [] => 0
  | 0 :: _ => 0
  | [1] => integralDivX (landenFormSeries 1 (-1) D.c₀ D.d₀)
  | 1 :: r :: rs => integralDivX (D.formSeries γ * polylogRev D β γ (r :: rs))
  | (n + 2) :: rs => integralDivX (D.formSeries β * polylogRev D β γ ((n + 1) :: rs))
termination_by l => l.sum

end LandenData

/-- Kamano's generalized multiple polylogarithm `Li_k(g; (β, γ); z) ∈ ℝ[[z]]`:
`Li_{(1)} = ∫₀^z (c₀/(1 - c₀u) + d₀/(1 + d₀u)) du`,
`Li_{k↑} = ∫₀^z ∑_i β_i G_{g_i}(u) Li_k(u) du` and
`Li_{k→} = ∫₀^z ∑_i γ_i G_{g_i}(u) Li_k(u) du`, where
`k↑ = (k₁, …, k_r + 1)` and `k→ = (k₁, …, k_r, 1)`. Lists that are not indices
(empty, or with a zero entry) give `0`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
display (6). -/
public noncomputable def generalizedMultiplePolylog (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) : ℝ⟦X⟧ :=
  D.polylogRev β γ k.reverse

/-- Initial condition: `Li_{(1)}(g; (β, γ); z) = ∫₀^z G_{g₀}(u) du`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, display (6). -/
public theorem generalizedMultiplePolylog_one (D : LandenData) (β γ : Fin D.s → ℝ) :
    generalizedMultiplePolylog D β γ [1] =
      integralDivX (landenFormSeries 1 (-1) D.c₀ D.d₀) := by
  simp [generalizedMultiplePolylog, LandenData.polylogRev]

/-- Recurrence for `k↑`: `Li_{(k₁, …, k_r + 1)} = ∫₀^z ∑ β_i G_{g_i}(u) Li_k(u) du`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public theorem generalizedMultiplePolylog_up (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (m : ℕ) :
    generalizedMultiplePolylog D β γ (k ++ [m + 2]) =
      integralDivX (D.formSeries β * generalizedMultiplePolylog D β γ (k ++ [m + 1])) := by
  simp [generalizedMultiplePolylog, LandenData.polylogRev]

/-- Recurrence for `k→`: `Li_{(k₁, …, k_r, 1)} = ∫₀^z ∑ γ_i G_{g_i}(u) Li_k(u) du`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public theorem generalizedMultiplePolylog_right (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (hk : k ≠ []) :
    generalizedMultiplePolylog D β γ (k ++ [1]) =
      integralDivX (D.formSeries γ * generalizedMultiplePolylog D β γ k) := by
  obtain ⟨r, rs, h⟩ : ∃ r rs, k.reverse = r :: rs := by
    cases hr : k.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp hr) hk
    | cons r rs => exact ⟨r, rs, rfl⟩
  simp [generalizedMultiplePolylog, h, LandenData.polylogRev]

/-- Auxiliary recursion for the coefficients of `multiplePolylog`, on the reversed
index: `c_{[]}(m) = [m = 0]` and `c_{a :: k'}(m) = m^{-a} ∑_{m' < m} c_{k'}(m')`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1,
definition of `Li_k(z)`. -/
public noncomputable def multiplePolylogCoeffRev : List ℕ → ℕ → ℝ
  | [], m => if m = 0 then 1 else 0
  | a :: rs, m => (∑ m' ∈ Finset.range m, multiplePolylogCoeffRev rs m') / (m : ℝ) ^ a

/-- The multiple polylogarithm
`Li_k(z) = ∑_{0 < m₁ < ⋯ < m_r} z^{m_r} / (m₁^{k₁} ⋯ m_r^{k_r}) ∈ ℝ[[z]]`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public noncomputable def multiplePolylog (k : List ℕ) : ℝ⟦X⟧ :=
  mk (multiplePolylogCoeffRev k.reverse)

/-- Depth one: `Li_{(a)}(z) = ∑_{m ≥ 1} z^m / m^a`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public theorem coeff_multiplePolylog_singleton (a : ℕ) {m : ℕ} (hm : 0 < m) :
    coeff m (multiplePolylog [a]) = 1 / (m : ℝ) ^ a := by
  simp [multiplePolylog, multiplePolylogCoeffRev, Finset.sum_ite_eq', hm]

/-- Auxiliary recursion for the coefficients of `multiplePolylogStar`, on the
reversed index: `c_{[]}(m) = [m = 0]` and
`c_{a :: k'}(m) = m^{-a} ∑_{m' ≤ m} c_{k'}(m')`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1,
definition of `Li⋆_k(z)`. -/
public noncomputable def multiplePolylogStarCoeffRev : List ℕ → ℕ → ℝ
  | [], m => if m = 0 then 1 else 0
  | a :: rs, m =>
      (∑ m' ∈ Finset.range (m + 1), multiplePolylogStarCoeffRev rs m') / (m : ℝ) ^ a

/-- The non-strict multiple polylogarithm
`Li⋆_k(z) = ∑_{0 < m₁ ≤ ⋯ ≤ m_r} z^{m_r} / (m₁^{k₁} ⋯ m_r^{k_r})`; for an index
(all `k_i ≥ 1`) the `m_i = 0` terms vanish since `1/0 = 0`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public noncomputable def multiplePolylogStar (k : List ℕ) : ℝ⟦X⟧ :=
  mk (multiplePolylogStarCoeffRev k.reverse)

/-- Depth one: `Li⋆_{(a)}(z) = ∑_{m ≥ 1} z^m / m^a` for `a ≥ 1`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public theorem coeff_multiplePolylogStar_singleton (a m : ℕ) :
    coeff m (multiplePolylogStar [a]) = 1 / (m : ℝ) ^ a := by
  simp [multiplePolylogStar, multiplePolylogStarCoeffRev, Finset.sum_ite_eq']

/-- Auxiliary recursion for `hoffmanDual`, on reversed indices:
`(1)^∨ = (1)`, `(k→)^∨ = (k^∨)↑` and `(k↑)^∨ = (k^∨)→`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
definition of Hoffman's dual index. -/
public def hoffmanDualRev : List ℕ → List ℕ
  | [] => []
  | 0 :: _ => []
  | [1] => [1]
  | 1 :: r :: rs => (hoffmanDualRev (r :: rs)).modifyHead (· + 1)
  | (n + 2) :: rs => 1 :: hoffmanDualRev ((n + 1) :: rs)
termination_by l => l.sum

/-- Hoffman's dual index `k^∨`, defined by `(1)^∨ = (1)`, `(k↑)^∨ = (k^∨)→` and
`(k→)^∨ = (k^∨)↑`. Lists that are not indices give `[]`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public def hoffmanDual (k : List ℕ) : List ℕ :=
  (hoffmanDualRev k.reverse).reverse

/-- Small values: `(1)^∨ = (1)`, `(3)^∨ = (1, 1, 1)`, `(1, 2)^∨ = (2, 1)`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public theorem hoffmanDual_small_values :
    hoffmanDual [1] = [1] ∧ hoffmanDual [3] = [1, 1, 1] ∧ hoffmanDual [1, 2] = [2, 1] := by
  simp [hoffmanDual, hoffmanDualRev]

/-- The variable `z(t) = (e^t - 1)/(c₀ e^t + d₀)` as a power series in `t`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4,
definition of `C_n^{(k, g, (β, γ))}`. -/
public noncomputable def landenExpVariable (D : LandenData) : ℝ⟦X⟧ :=
  (exp ℝ - 1) * (C D.c₀ * exp ℝ + C D.d₀)⁻¹

/-- For `c₀ + d₀ ≠ 0`, `(c₀ e^t + d₀) z(t) = e^t - 1`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public theorem landenExpVariable_spec (D : LandenData) (h : D.c₀ + D.d₀ ≠ 0) :
    (C D.c₀ * exp ℝ + C D.d₀) * landenExpVariable D = exp ℝ - 1 := by
  have h0 : constantCoeff (C D.c₀ * exp ℝ + C D.d₀) ≠ 0 := by simpa using h
  rw [landenExpVariable, mul_comm, mul_assoc, PowerSeries.inv_mul_cancel _ h0, mul_one]

/-- Kamano's generalized poly-Bernoulli numbers of the first kind:
`d/dt Li_{k↑}(g; (β, γ); z(t)) = ∑_n C_n^{(k, g, (β, γ))} tⁿ / n!`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public noncomputable def generalizedPolyBernoulliC (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (n : ℕ) : ℝ :=
  n.factorial * coeff n (derivative (subst (landenExpVariable D)
    (generalizedMultiplePolylog D β γ (k.modifyLast (· + 1)))))

/-- Kamano's generalized poly-Bernoulli numbers of the second kind:
`d/dt Li_{k→}(g; (β, γ); z(t)) = ∑_n B_n^{(k, g, (β, γ))} tⁿ / n!`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public noncomputable def generalizedPolyBernoulliB (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (n : ℕ) : ℝ :=
  n.factorial * coeff n (derivative (subst (landenExpVariable D)
    (generalizedMultiplePolylog D β γ (k ++ [1]))))

/-- `C_n^{(k, g, (β, γ))} = (n + 1)! [t^{n+1}] Li_{k↑}(g; (β, γ); z(t))`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public theorem generalizedPolyBernoulliC_eq_coeff (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (n : ℕ) :
    generalizedPolyBernoulliC D β γ k n = (n + 1).factorial * coeff (n + 1)
      (subst (landenExpVariable D) (generalizedMultiplePolylog D β γ (k.modifyLast (· + 1)))) := by
  rw [generalizedPolyBernoulliC, coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

/-- **Landen connection formula** (Okuda–Ueno): for every index `k`,
`Li_k(z/(z - 1)) = (-1)^{d(k)} ∑_{k ⪯ k'} Li_{k'}(z)`, the sum over all indices
`k'` of the same weight from which `k` is obtained by combining consecutive
entries, i.e. compositions `k'` whose boundary set contains that of `k`. Here
`z/(z - 1) = -∑_{n ≥ 1} zⁿ`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 1
(quoting Okuda and Ueno, Prop. 9). -/
public theorem_wanted multiplePolylog_landen_connection {n : ℕ} (k : Composition n) :
    subst (-(X * mk fun _ => (1 : ℝ))) (multiplePolylog k.blocks) =
      (-1 : ℝ) ^ k.length •
        ∑ k' : Composition n with k.boundaries ⊆ k'.boundaries, multiplePolylog k'.blocks

/-- **Sum formula**: for `k ≥ 1`, every real `μ` and every `δ`,
`∑_{|k| = k} μ^{d(k) - 1} Li_k(g; (β, γ); z) = Li_{(k)}(g; (β + μγ, δ); z)`.
The paper takes `μ` an indeterminate; both sides are polynomials in `μ`, so this
is equivalent.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 1,
Identity (7). -/
public theorem_wanted generalizedMultiplePolylog_sum_formula (D : LandenData)
    (β γ δ : Fin D.s → ℝ) (μ : ℝ) (k : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) • generalizedMultiplePolylog D β γ c.blocks =
      generalizedMultiplePolylog D (β + μ • γ) δ [k]

/-- **Generalized Landen connection formula**: for `g_i ∈ GL₂(ℝ)` (`1 ≤ i ≤ s`)
and every index `k`,
`Li_k(g; (β, γ); z/((c₀ - d₀) z - 1)) = Li_k(g̃; (β, γ); z)`, where
`z/((c₀ - d₀) z - 1) = -∑_{n ≥ 0} (c₀ - d₀)ⁿ z^{n+1}`. The hypothesis
`g₀ ∈ GL₂(ℝ)` (`c₀ + d₀ ≠ 0`) is not needed; the invertibility of `g_i` is (with
`a_i = c_i = 0` the identity fails).

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 2,
Identity (8). -/
public theorem_wanted generalizedMultiplePolylog_landen_connection (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (β γ : Fin D.s → ℝ) {n : ℕ}
    (k : Composition n) :
    subst (-(X * mk fun m => (D.c₀ - D.d₀) ^ m)) (generalizedMultiplePolylog D β γ k.blocks) =
      generalizedMultiplePolylog D.tilde β γ k.blocks

/-- **Landen formula in the classical case**: for the data (9),
`g₀ = g₂ = (1 -1; 1 0)` and `g₁ = (1 0; 0 1)` (so `G_{g₁}(t) = 1/t` and
`G_{g₂}(t) = 1/(1 - t)`), and every index `k`,
`Li_k(g; ((β₁, β₂), (γ₁, γ₂)); z/(z - 1)) = -Li_k(g; ((β₁, β₁ - β₂), (γ₁, γ₁ - γ₂)); z)`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 3,
Identity (10). -/
public theorem_wanted generalizedMultiplePolylog_landen_connection_classical
    (β₁ β₂ γ₁ γ₂ : ℝ) {n : ℕ} (k : Composition n) :
    subst (-(X * mk fun _ => (1 : ℝ)))
        (generalizedMultiplePolylog ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩
          ![β₁, β₂] ![γ₁, γ₂] k.blocks) =
      -generalizedMultiplePolylog ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩
          ![β₁, β₁ - β₂] ![γ₁, γ₁ - γ₂] k.blocks

/-- **Duality of multi-poly-Bernoulli-star numbers** (Imatomi): with
`Li⋆_k(1 - e^{-t})/(e^t - 1) = ∑ C_{n,⋆}^{(k)} tⁿ/n!` and
`Li⋆_k(1 - e^{-t})/(1 - e^{-t}) = ∑ B_{n,⋆}^{(k)} tⁿ/n!`, every index `k` and
`n ≥ 0` satisfy `C_{n,⋆}^{(k)} = (-1)ⁿ B_{n,⋆}^{(k^∨)}`. The two generating
functions are the series `F`, `G` determined by the displayed products (the
divisors are non-zero-divisors in `ℝ⟦t⟧`), and `1 - e^{-t}` is
`1 - rescale (-1) (exp ℝ)`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 4
(quoting Imatomi, Theorem 3.2), with generating functions (13) and (14). -/
public theorem_wanted multiPolyBernoulliStar_duality {m : ℕ} (k : Composition m)
    (F G : ℝ⟦X⟧)
    (hF : (exp ℝ - 1) * F =
      subst (1 - rescale (-1 : ℝ) (exp ℝ)) (multiplePolylogStar k.blocks))
    (hG : (1 - rescale (-1 : ℝ) (exp ℝ)) * G =
      subst (1 - rescale (-1 : ℝ) (exp ℝ)) (multiplePolylogStar (hoffmanDual k.blocks)))
    (n : ℕ) :
    n.factorial * coeff n F = (-1 : ℝ) ^ n * (n.factorial * coeff n G)

/-- **Sum formula for `C_n`**, Identity (16): for `k ≥ 1` and every real `μ`,
`∑_{|k| = k} μ^{d(k) - 1} C_n^{(k, g, (β, γ))} = B_n^{((k), g, (β + μγ, β))}
= C_n^{({1}^k, g, (β, β + μγ))}`, with `{1}^k = (1, …, 1)` (`k` ones).

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 2,
Identity (16). -/
public theorem_wanted generalizedPolyBernoulliC_sum_formula (D : LandenData)
    (β γ : Fin D.s → ℝ) (μ : ℝ) (k n : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) * generalizedPolyBernoulliC D β γ c.blocks n =
        generalizedPolyBernoulliB D (β + μ • γ) β [k] n ∧
      generalizedPolyBernoulliB D (β + μ • γ) β [k] n =
        generalizedPolyBernoulliC D β (β + μ • γ) (List.replicate k 1) n

/-- **Sum formula for `B_n`**, Identity (17): for `k ≥ 1` and every real `μ`,
`∑_{|k| = k} μ^{d(k) - 1} B_n^{(k, g, (β, γ))} = B_n^{((k), g, (β + μγ, γ))}
= C_n^{({1}^k, g, (γ, β + μγ))}`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 2,
Identity (17). -/
public theorem_wanted generalizedPolyBernoulliB_sum_formula (D : LandenData)
    (β γ : Fin D.s → ℝ) (μ : ℝ) (k n : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) * generalizedPolyBernoulliB D β γ c.blocks n =
        generalizedPolyBernoulliB D (β + μ • γ) γ [k] n ∧
      generalizedPolyBernoulliB D (β + μ • γ) γ [k] n =
        generalizedPolyBernoulliC D γ (β + μ • γ) (List.replicate k 1) n

/-- **Landen formula for `C_n`**, in the reading its proof establishes: for
`g_i ∈ GL₂(ℝ)`, every index `k` and `n ≥ 0`,
`C_n^{(k, g, (β, γ))} = (-1)^{n-1} n! [tⁿ] d/dt Li_{k↑}(g̃; (β, γ); z(t))`, where
`z(t) = (e^t - 1)/(c₀ e^t + d₀)` is the variable of `g` (the proof differentiates
`Li_{k↑}(g; z(t)) = Li_{k↑}(g̃; z(-t))`). The sign `(-1)^{n-1}` is written
`(-1)^{n+1}`, equal for all `n ≥ 0`.

As printed, with `C_n^{(k, g̃, (β, γ))}` formed from `g̃`'s own variable
`(e^t - 1)/(-d₀ e^t - c₀) = z(-t)`, the theorem is false: then
`C_n^{(k, g̃, (β, γ))} = C_n^{(k, g, (β, γ))}` for all `n`. For instance
`g₀ = (1 -1; 1 0)`, `g₁ = (1 0; 0 1)`, `β = γ = (1)`, `k = (1)`, `n = 0` gives
`C_0^{(k, g, (β, γ))} = C_0^{(k, g̃, (β, γ))} = 1`, while the printed identity asks
for `1 = -1`.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 5. -/
public theorem_wanted generalizedPolyBernoulliC_landen (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (β γ : Fin D.s → ℝ) {m : ℕ}
    (k : Composition m) (n : ℕ) :
    generalizedPolyBernoulliC D β γ k.blocks n =
      (-1 : ℝ) ^ (n + 1) * (n.factorial * coeff n (derivative (subst (landenExpVariable D)
        (generalizedMultiplePolylog D.tilde β γ (k.blocks.modifyLast (· + 1))))))

end

end MetaMathlibExt
