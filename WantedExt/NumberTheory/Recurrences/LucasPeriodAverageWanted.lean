/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Recurrences.NondegenerateLucasPair
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Period lengths modulo `n` and averages of second-order recurrences

Statements from Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of
Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36
(sections 1-4, partial: some clauses of Theorem 1.3, Corollary 3.1 (iv) and the main
chain characterization of Theorem 4.3 are omitted, and false clauses are corrected or
omitted as recorded in the source audit).

The paper writes the recurrence as `W (n + 2) = a * W (n + 1) + b * W n` with discriminant
`D = a ^ 2 + 4 * b`. This module uses the repository convention of `lucasU`: parameters
`P = a` and `Q = -b`, so `b = -params.q`, `D = params.p ^ 2 - 4 * params.q`,
`a + b - 1 = params.p - params.q - 1` and `-b - 1 = params.q - 1`. The paper's `B_W(n)` is
`∑ i ∈ Finset.Icc 1 n, w i`, and "`A_W(n) = B_W(n) / n` is an integer" is
`(n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, w i`. Nondegeneracy (`ab ≠ 0` and `α / β` not a root of
unity) is `IsNondegenerateLucasPair params.p params.q`; `Q ≠ 0` is built into
`LucasSequenceParams`, and `a = 0` is excluded because then `α / β = -1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The (least) period `π_U(m)` of the Lucas sequence `U(a, b)` modulo `m`: the minimal period
of `(0, 1)` under the step `(x, y) ↦ (y, a * y + b * x)` on `ZMod m × ZMod m`, that is, the
least positive `r` with `U r ≡ 0` and `U (r + 1) ≡ 1` modulo `m` (equation (1.11)). For
`m > 0` it is `0` exactly when `U` is not purely periodic modulo `m`, i.e. when
`gcd(m, b) > 1` (Remark 1.1); at `m = 0` the step acts on `ZMod 0 = ℤ` and the value carries
no meaning for the paper (for Fibonacci it is `0` although `gcd(0, 1) = 1`).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 1, equation
(1.11). -/
noncomputable def lucasUPeriod (params : LucasSequenceParams) (m : ℕ) : ℕ :=
  Function.minimalPeriod
    (fun x : ZMod m × ZMod m => (x.2, (params.p : ZMod m) * x.2 - (params.q : ZMod m) * x.1))
    (0, 1)

/-- The (least) restricted period `ρ_U(m)` of `U(a, b)` modulo `m`: the least positive `s`
with `U s ≡ 0` and `U (s + 1) ≡ M` modulo `m` for a multiplier `M` coprime to `m`
(equation (1.12)); `U (s + 1)` is then the multiplier `M_U(m)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 1, equations
(1.10) and (1.12). -/
noncomputable def lucasURestrictedPeriod (params : LucasSequenceParams) (m : ℕ) : ℕ :=
  sInf {s : ℕ | 0 < s ∧ (m : ℤ) ∣ lucasU params s ∧ IsCoprime (lucasU params (s + 1)) (m : ℤ)}

/-- The set `S(U)` of positive integers `n` with `gcd(n, b) = 1` and `π_U(n) ∣ n`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
def lucasPeriodSet (params : LucasSequenceParams) : Set ℕ :=
  {n | 0 < n ∧ IsCoprime (n : ℤ) params.q ∧ lucasUPeriod params n ∣ n}

/-- The set `S'(U)` of `n ∈ S(U)` with `B_U(n) ≡ 0 (mod n)`, i.e. `A_U(n)` an integer.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
def lucasAverageSet (params : LucasSequenceParams) : Set ℕ :=
  {n | n ∈ lucasPeriodSet params ∧ (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i}

/-- "`A_W(n)` is an integer for all recurrences `W(a, b)`": every integer sequence `w`
satisfying `w (k + 2) = a * w (k + 1) + b * w k` has `n ∣ w 1 + ⋯ + w n`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 2 (definition of
`B_W(n)` and `A_W(n)`). -/
def lucasAllAveragesIntegral (params : LucasSequenceParams) (n : ℕ) : Prop :=
  ∀ w : ℕ → ℤ, (∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) →
    (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, w i

/-- `π_U(1) = 1`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.4 (ix). -/
theorem lucasUPeriod_one (params : LucasSequenceParams) : lucasUPeriod params 1 = 1 :=
  Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (Subsingleton.elim _ _)

/-- The Fibonacci sequence has period `3` modulo `2`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.4 (i)
(`π_U(2) = 3` when `2 ∤ bD`). -/
theorem lucasUPeriod_fibonacciLucasParams_two : lucasUPeriod fibonacciLucasParams 2 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply Function.minimalPeriod_eq_prime
  · show (_ : ZMod 2 × ZMod 2) = _
    simp [fibonacciLucasParams]
  · intro h
    have := congrArg Prod.fst h
    simp at this

/-- `ρ_U(1) = 1`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.4 (ix). -/
theorem lucasURestrictedPeriod_one (params : LucasSequenceParams) :
    lucasURestrictedPeriod params 1 = 1 := by
  have h1 : 1 ∈ {s : ℕ | 0 < s ∧ ((1 : ℕ) : ℤ) ∣ lucasU params s ∧
      IsCoprime (lucasU params (s + 1)) ((1 : ℕ) : ℤ)} :=
    ⟨Nat.one_pos, by simp, by simp [isCoprime_one_right]⟩
  exact le_antisymm (Nat.sInf_le h1) (Nat.sInf_mem ⟨1, h1⟩).1

/-- The Fibonacci sequence has restricted period `3` modulo `2` (`F 3 = 2`).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, equation (1.12). -/
theorem lucasURestrictedPeriod_fibonacciLucasParams_two :
    lucasURestrictedPeriod fibonacciLucasParams 2 = 3 := by
  unfold lucasURestrictedPeriod
  have hU : ∀ n, lucasU fibonacciLucasParams n = (Nat.fib n : ℤ) := lucasU_fibonacciLucasParams
  have h3 : 3 ∈ {s : ℕ | 0 < s ∧ ((2 : ℕ) : ℤ) ∣ lucasU fibonacciLucasParams s ∧
      IsCoprime (lucasU fibonacciLucasParams (s + 1)) ((2 : ℕ) : ℤ)} := by
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [hU]; decide
    · rw [hU, Int.isCoprime_iff_gcd_eq_one]
      decide
  refine le_antisymm (Nat.sInf_le h3) ?_
  set S := {s : ℕ | 0 < s ∧ ((2 : ℕ) : ℤ) ∣ lucasU fibonacciLucasParams s ∧
      IsCoprime (lucasU fibonacciLucasParams (s + 1)) ((2 : ℕ) : ℤ)} with hS
  obtain ⟨hpos, hdvd, -⟩ : sInf S ∈ S := Nat.sInf_mem ⟨3, h3⟩
  by_contra hlt
  have hlt' : sInf S < 3 := by omega
  generalize sInf S = k at hpos hdvd hlt'
  interval_cases k <;> simp [hU] at hdvd

/-- `1 ∈ S(U)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
theorem one_mem_lucasPeriodSet (params : LucasSequenceParams) : 1 ∈ lucasPeriodSet params :=
  ⟨Nat.one_pos, by simp [isCoprime_one_left], by simp [lucasUPeriod_one]⟩

/-- `1 ∈ S'(U)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
theorem one_mem_lucasAverageSet (params : LucasSequenceParams) :
    1 ∈ lucasAverageSet params :=
  ⟨one_mem_lucasPeriodSet params, by simp⟩

/-- The set `T(U)` of positive integers `n` coprime to `b` with `n ∣ U n`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
def lucasIndexDivisibleSet (params : LucasSequenceParams) : Set ℕ :=
  {n | 0 < n ∧ IsCoprime (n : ℤ) params.q ∧ (n : ℤ) ∣ lucasU params n}

/-- `1 ∈ T(U)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.2. -/
theorem one_mem_lucasIndexDivisibleSet (params : LucasSequenceParams) :
    1 ∈ lucasIndexDivisibleSet params :=
  ⟨Nat.one_pos, by simp [isCoprime_one_left], by simp⟩

/-- `A_W(1) = W 1` is an integer for every recurrence.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 2. -/
theorem lucasAllAveragesIntegral_one (params : LucasSequenceParams) :
    lucasAllAveragesIntegral params 1 :=
  fun _ _ => by simp

/-- Lemma 1.1: `U (2 n) = U n * V n`, `U (2 n + 1) = b * U n ^ 2 + U (n + 1) ^ 2`, and
`U m ∣ U n` whenever `m ∣ n`. The record's trailing expository text on pure periodicity is not
part of the lemma.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Lemma 1.1
(`integers-2024-A36-lem-1-1`). -/
public theorem_wanted lucasU_two_mul_and_lucasU_dvd (params : LucasSequenceParams) :
    (∀ n, lucasU params (2 * n) = lucasU params n * lucasV params n) ∧
    (∀ n, lucasU params (2 * n + 1) =
      -params.q * lucasU params n ^ 2 + lucasU params (n + 1) ^ 2) ∧
    (∀ m n, m ∣ n → lucasU params m ∣ lucasU params n)

/-- Theorem 1.1: if `gcd(m, b) = 1` then `U(a, b)` is purely periodic modulo `m`, `π_U(m)` is
a period of every recurrence `W(a, b)` modulo `m`, and `ρ_U(m)` is a restricted period of every
`W(a, b)` modulo `m` (with the multiplier `U (ρ_U(m) + 1)`). "General period" replaces the
paper's divisibilities `π_W(m) ∣ π_U(m)` and `ρ_W(m) ∣ ρ_U(m)`, which are equivalent by Remark
1.2.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.1
(`integers-2024-A36-thm-1-1`). -/
public theorem_wanted lucasUPeriod_isPeriod_of_secondOrder (params : LucasSequenceParams)
    (m : ℕ) (hm : 0 < m) (hmb : IsCoprime (m : ℤ) params.q) (w : ℕ → ℤ)
    (hw : ∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) :
    0 < lucasUPeriod params m ∧ 0 < lucasURestrictedPeriod params m ∧
    (∀ n, w (n + lucasUPeriod params m) ≡ w n [ZMOD m]) ∧
    (∀ n, w (n + lucasURestrictedPeriod params m) ≡
      lucasU params (lucasURestrictedPeriod params m + 1) * w n [ZMOD m])

/-- Theorem 1.2: for `gcd(m n, b) = 1`, `π_U(lcm(m, n)) = lcm(π_U(m), π_U(n))` and
`ρ_U(lcm(m, n)) = lcm(ρ_U(m), ρ_U(n))` (1.17), and the same for the iterates
`π_U^i` and `ρ_U^i` (1.18), where `π_U^0(m) = m` and `π_U^(i+1)(m) = π_U(π_U^i(m))`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.2
(`integers-2024-A36-thm-1-2`). -/
public theorem_wanted lucasUPeriod_lcm (params : LucasSequenceParams) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hmn : IsCoprime ((m * n : ℕ) : ℤ) params.q) :
    lucasUPeriod params (Nat.lcm m n) =
        Nat.lcm (lucasUPeriod params m) (lucasUPeriod params n) ∧
    lucasURestrictedPeriod params (Nat.lcm m n) =
        Nat.lcm (lucasURestrictedPeriod params m) (lucasURestrictedPeriod params n) ∧
    ∀ i, 1 ≤ i →
      (lucasUPeriod params)^[i] (Nat.lcm m n) =
          Nat.lcm ((lucasUPeriod params)^[i] m) ((lucasUPeriod params)^[i] n) ∧
      (lucasURestrictedPeriod params)^[i] (Nat.lcm m n) =
          Nat.lcm ((lucasURestrictedPeriod params)^[i] m)
            ((lucasURestrictedPeriod params)^[i] n)

/-- Theorem 1.3 (ii)-(ix): closed forms of the degenerate recurrences with `b = ±1` or
`(a, b) = (±1, 0)`, for the pairs `(0, 1)`, `(0, -1)`, `(1, -1)`, `(-1, -1)`, `(2, -1)`,
`(-2, -1)`, `(1, 0)`, `(-1, 0)`. Part (i) (the list of degenerate pairs) and the root and
discriminant values in (vi)-(vii) are not formalized. The recurrences are written directly,
since `b = 0` is outside `LucasSequenceParams`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.3
(`integers-2024-A36-thm-1-3`). -/
public theorem_wanted degenerate_secondOrder_closedForms :
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w k) →
      ∀ n, w (2 * n) = w 0 ∧ w (2 * n + 1) = w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w k) →
      ∀ n, w (4 * n) = w 0 ∧ w (4 * n + 1) = w 1 ∧ w (4 * n + 2) = -w 0 ∧
        w (4 * n + 3) = -w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1) - w k) →
      ∀ n, w (6 * n) = w 0 ∧ w (6 * n + 1) = w 1 ∧ w (6 * n + 2) = w 1 - w 0 ∧
        w (6 * n + 3) = -w 0 ∧ w (6 * n + 4) = -w 1 ∧ w (6 * n + 5) = w 0 - w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1) - w k) →
      ∀ n, w (3 * n) = w 0 ∧ w (3 * n + 1) = w 1 ∧ w (3 * n + 2) = -w 1 - w 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = 2 * w (k + 1) - w k) →
      ∀ n : ℕ, w n = n * w 1 - ((n : ℤ) - 1) * w 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -2 * w (k + 1) - w k) →
      ∀ n : ℕ, w n = (-1) ^ (n + 1) * (n * w 1 + ((n : ℤ) - 1) * w 0)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1)) → ∀ n, 1 ≤ n → w n = w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1)) →
      ∀ n, 1 ≤ n → w n = (-1) ^ (n + 1) * w 1)

/-- Theorem 2.1: sums of the degenerate recurrences of Theorem 1.3. For `(a, b) = (0, 1)`,
`B_U(n) = ⌈n / 2⌉` and all `A_W(n)` are integers iff `n = 1`; for `(0, -1)`, `(1, -1)`,
`(-1, -1)`, `(-1, 0)`, `B_W` vanishes at multiples of `4`, `6`, `3`, `2`; for `(2, -1)`,
`2 B_W(n) = (W 1 - W 0) n (n + 1) + 2 W 0 n`, all `A_W(n)` are integers iff `n` is odd, and
`B_W(2 n - 1) = (2 n - 1) (n (W 1 - W 0) + W 0)`; for `(-2, -1)`,
`B_U(n) = (-1) ^ (n + 1) ⌈n / 2⌉` and all `A_W(n)` are integers iff `n = 1`; for `(1, 0)`,
`B_W(n) = n W 1`. The statements `A_W(kn) = 0` are the vanishing sums.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.1
(`integers-2024-A36-thm-2-1`). -/
public theorem_wanted degenerate_secondOrder_sums :
    (∀ n, 1 ≤ n → ∑ i ∈ Finset.Icc 1 n, lucasU ⟨0, -1, by decide⟩ i = ((n + 1) / 2 : ℕ)) ∧
    (∀ n, 1 ≤ n → (lucasAllAveragesIntegral ⟨0, -1, by decide⟩ n ↔ n = 1)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w k) → ∀ n, ∑ i ∈ Finset.Icc 1 (4 * n), w i = 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1) - w k) →
      ∀ n, ∑ i ∈ Finset.Icc 1 (6 * n), w i = 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1) - w k) →
      ∀ n, ∑ i ∈ Finset.Icc 1 (3 * n), w i = 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = 2 * w (k + 1) - w k) →
      ∀ n : ℕ, 2 * ∑ i ∈ Finset.Icc 1 n, w i = (w 1 - w 0) * n * (n + 1) + 2 * w 0 * n) ∧
    (∀ n, 1 ≤ n → (lucasAllAveragesIntegral ⟨2, 1, by decide⟩ n ↔ Odd n)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = 2 * w (k + 1) - w k) →
      ∀ n : ℕ, 1 ≤ n → ∑ i ∈ Finset.Icc 1 (2 * n - 1), w i =
        ((2 * n - 1 : ℕ) : ℤ) * (n * (w 1 - w 0) + w 0)) ∧
    (∀ n, 1 ≤ n → ∑ i ∈ Finset.Icc 1 n, lucasU ⟨-2, 1, by decide⟩ i =
      (-1) ^ (n + 1) * ((n + 1) / 2 : ℕ)) ∧
    (∀ n, 1 ≤ n → (lucasAllAveragesIntegral ⟨-2, 1, by decide⟩ n ↔ n = 1)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1)) → ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, w i = n * w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1)) → ∀ n, ∑ i ∈ Finset.Icc 1 (2 * n), w i = 0)

/-- Theorem 2.2 (i) and the formula (2.2) of part (ii): for `b D ≠ 0`, if `a + b - 1 ≠ 0`
then `(a + b - 1) B_W(n) = J(n) := W (n + 1) - W 1 + b (W n - W 0)`, and `n ∣ J(r)` whenever
`gcd(n, b) = 1` and `π_U(n) ∣ r`; if `a + b - 1 = 0` then
`(-b - 1) B_W(n) = (W 1 - W 0) U (n + 1) - n (W 1 + b W 0) + W 0 - W 1`. The congruence
`K(s) ≡ 0 (mod n)` claimed in part (ii) is false as printed and omitted: for
`(a, b) = (-6, 7)`, `W = U`, `n = 3`, one has `gcd(3, 7) = 1`, `π_U(3) = 2`, and `K(2) = 40`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.2
(`integers-2024-A36-thm-2-2`). -/
public theorem_wanted secondOrder_sum_formula (params : LucasSequenceParams)
    (hD : params.p ^ 2 - 4 * params.q ≠ 0) (w : ℕ → ℤ)
    (hw : ∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) :
    (params.p - params.q - 1 ≠ 0 →
      (∀ n, (params.p - params.q - 1) * ∑ i ∈ Finset.Icc 1 n, w i =
        w (n + 1) - w 1 - params.q * (w n - w 0)) ∧
      ∀ n r : ℕ, 0 < n → IsCoprime (n : ℤ) params.q → lucasUPeriod params n ∣ r →
        (n : ℤ) ∣ w (r + 1) - w 1 - params.q * (w r - w 0)) ∧
    (params.p - params.q - 1 = 0 →
      ∀ n : ℕ, (params.q - 1) * ∑ i ∈ Finset.Icc 1 n, w i =
        (w 1 - w 0) * lucasU params (n + 1) - n * (w 1 - params.q * w 0) + w 0 - w 1)

/-- Corollary 2.1: for `b ≠ 0`, `(a + b - 1) B_U(n) = U (n + 1) - 1 + b U n` if
`a + b - 1 ≠ 0`, and `(-b - 1) B_U(n) = U (n + 1) - 1 - n` if `a + b - 1 = 0`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.1
(`integers-2024-A36-cor-2-1`). -/
public theorem_wanted lucasU_sum_formula (params : LucasSequenceParams) (n : ℕ) :
    (params.p - params.q - 1 ≠ 0 →
      (params.p - params.q - 1) * ∑ i ∈ Finset.Icc 1 n, lucasU params i =
        lucasU params (n + 1) - 1 - params.q * lucasU params n) ∧
    (params.p - params.q - 1 = 0 →
      (params.q - 1) * ∑ i ∈ Finset.Icc 1 n, lucasU params i = lucasU params (n + 1) - 1 - n)

/-- Corollary 2.2 (i): if `a + b - 1 ≠ 0`, `gcd(n, b (a + b - 1)) = 1` and `π_U(n) ∣ r`, then
`U` is purely periodic modulo `n` and `B_W(r) ≡ 0 (mod n)` for all recurrences `W(a, b)`.
`b ≠ 0` is built into `LucasSequenceParams` (for `b = 0` the hypothesis forces `n = 1`).
Part (ii) is false as printed and omitted: for `(a, b) = (-6, 7)` (so `a + b - 1 = 0`),
`n = 3` has `gcd(3, 7 · (-8)) = 1` and `π_U(3) = 2`, but `B_U(2) = 1 - 6 = -5`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.2
(`integers-2024-A36-cor-2-2`). -/
public theorem_wanted secondOrder_sum_dvd_of_period_dvd (params : LucasSequenceParams)
    (hab : params.p - params.q - 1 ≠ 0) (n : ℕ) (hn : 0 < n)
    (hcop : IsCoprime (n : ℤ) (params.q * (params.p - params.q - 1))) :
    0 < lucasUPeriod params n ∧
    ∀ r, lucasUPeriod params n ∣ r → ∀ w : ℕ → ℤ,
      (∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) →
      (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 r, w i

/-- Theorem 2.3: if `n ∈ S(U)` and the prime `ℓ` divides `n`, then `ℓ n ∈ S(U)`; if moreover
`a + b - 1 ≠ 0` and `gcd(a + b - 1, n) = 1`, or `a + b - 1 = 0` and `gcd(-b - 1, n) = 1`,
then `ℓ n ∈ S'(U)` and `A_W(ℓ n)` is an integer for all recurrences `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.3
(`integers-2024-A36-thm-2-3`). -/
public theorem_wanted prime_mul_mem_lucasPeriodSet (params : LucasSequenceParams) (n ℓ : ℕ)
    (hn : n ∈ lucasPeriodSet params) (hℓ : ℓ.Prime) (hℓn : ℓ ∣ n) :
    ℓ * n ∈ lucasPeriodSet params ∧
    ((params.p - params.q - 1 ≠ 0 ∧ IsCoprime (params.p - params.q - 1) (n : ℤ)) ∨
        (params.p - params.q - 1 = 0 ∧ IsCoprime (params.q - 1) (n : ℤ)) →
      ℓ * n ∈ lucasAverageSet params ∧ lucasAllAveragesIntegral params (ℓ * n))

/-- Corollary 2.3: if `n ∈ S(U)` and every prime divisor of `m` divides `n`, then
`m n ∈ S(U)`; under the coprimality condition of Theorem 2.3 also `m n ∈ S'(U)` and `A_W(m n)`
is an integer for all recurrences `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.3
(`integers-2024-A36-cor-2-3`). -/
public theorem_wanted mul_mem_lucasPeriodSet_of_primeFactors (params : LucasSequenceParams)
    (m n : ℕ) (hm : 0 < m) (hn : n ∈ lucasPeriodSet params)
    (hmn : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ n) :
    m * n ∈ lucasPeriodSet params ∧
    ((params.p - params.q - 1 ≠ 0 ∧ IsCoprime (params.p - params.q - 1) (n : ℤ)) ∨
        (params.p - params.q - 1 = 0 ∧ IsCoprime (params.q - 1) (n : ℤ)) →
      m * n ∈ lucasAverageSet params ∧ lucasAllAveragesIntegral params (m * n))

/-- Theorem 2.4: `S(U)` is closed under `lcm` and products; under the coprimality condition
for `m n`, all of `m`, `n`, `lcm(m, n)`, `m n` lie in `S'(U)` with integral averages for all
`W(a, b)`. In particular, if `C(r)`, the least multiple of `r` in `S(U)`, exists and satisfies
the coprimality condition, then `C'(r) = C(r)` (the least multiple of `r` in `S'(U)`) and
`A_W(C(r))` is an integer for all `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.4
(`integers-2024-A36-thm-2-4`). -/
public theorem_wanted lcm_mem_lucasPeriodSet (params : LucasSequenceParams) :
    (∀ m n, m ∈ lucasPeriodSet params → n ∈ lucasPeriodSet params →
      Nat.lcm m n ∈ lucasPeriodSet params ∧ m * n ∈ lucasPeriodSet params ∧
      ((params.p - params.q - 1 ≠ 0 ∧ IsCoprime (params.p - params.q - 1) ((m * n : ℕ) : ℤ)) ∨
          (params.p - params.q - 1 = 0 ∧ IsCoprime (params.q - 1) ((m * n : ℕ) : ℤ)) →
        ∀ x ∈ ({m, n, Nat.lcm m n, m * n} : Finset ℕ),
          x ∈ lucasAverageSet params ∧ lucasAllAveragesIntegral params x)) ∧
    (∀ r c : ℕ, 0 < r → IsLeast {x | r ∣ x ∧ x ∈ lucasPeriodSet params} c →
      ((params.p - params.q - 1 ≠ 0 ∧ IsCoprime (params.p - params.q - 1) (c : ℤ)) ∨
          (params.p - params.q - 1 = 0 ∧ IsCoprime (params.q - 1) (c : ℤ))) →
      IsLeast {x | r ∣ x ∧ x ∈ lucasAverageSet params} c ∧ lucasAllAveragesIntegral params c)

/-- Theorem 2.5: if `m, n ∈ S'(U)` and `m ∣ r`, then `B_U(r) ≡ 0 (mod m)`,
`lcm(m, n) ∈ S'(U)`, `A_W(m)`, `A_W(n)`, `A_W(lcm(m, n))` are integers for all `W(a, b)`, and
`B_W(r) ≡ 0 (mod m)` for all `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.5
(`integers-2024-A36-thm-2-5`). -/
public theorem_wanted lcm_mem_lucasAverageSet (params : LucasSequenceParams) (m n r : ℕ)
    (hm : m ∈ lucasAverageSet params) (hn : n ∈ lucasAverageSet params) (hmr : m ∣ r) :
    (m : ℤ) ∣ ∑ i ∈ Finset.Icc 1 r, lucasU params i ∧
    Nat.lcm m n ∈ lucasAverageSet params ∧
    lucasAllAveragesIntegral params m ∧ lucasAllAveragesIntegral params n ∧
    lucasAllAveragesIntegral params (Nat.lcm m n) ∧
    ∀ w : ℕ → ℤ, (∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) →
      (m : ℤ) ∣ ∑ i ∈ Finset.Icc 1 r, w i

/-- Theorem 2.6: for `a = 1`, `b ≠ 0` and `gcd(n, b) = 1`, `B_U(n) ≡ 0 (mod n)` if and only if
`U (n + 2) ≡ 1 (mod n)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.6
(`integers-2024-A36-thm-2-6`). -/
public theorem_wanted lucasU_sum_dvd_iff_of_p_eq_one (params : LucasSequenceParams)
    (hp : params.p = 1) (n : ℕ) (hn : 0 < n) (hnb : IsCoprime (n : ℤ) params.q) :
    (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i ↔ lucasU params (n + 2) ≡ 1 [ZMOD n]

/-- Theorem 2.7: suppose every recurrence `W(a, b)` is purely periodic modulo `n` from the term
`W 1` on with period dividing `n` (that is, `W (k + n) ≡ W k (mod n)` for `k ≥ 1`), and
`A_W(n)` is an integer for all `W(a, b)`. If `m ∈ S'(U)`, then `A_W(lcm(m, n))` is an integer
for all `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.7
(`integers-2024-A36-thm-2-7`). -/
public theorem_wanted lucasAllAveragesIntegral_lcm (params : LucasSequenceParams) (m n : ℕ)
    (hn : 0 < n)
    (hper : ∀ w : ℕ → ℤ, (∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) →
      ∀ k, 1 ≤ k → w (k + n) ≡ w k [ZMOD n])
    (havg : lucasAllAveragesIntegral params n) (hm : m ∈ lucasAverageSet params) :
    lucasAllAveragesIntegral params (Nat.lcm m n)

/-- Theorem 2.10: let `n > 1` and `m ∈ S'(U)`. If `n ∣ b` and `a ≡ 1 (mod n)`, or `n` is even,
`n ∣ b` and `a ≡ -1 (mod n)`, then `A_W(n)` and `A_W(m n)` are integers for all `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.10
(`integers-2024-A36-thm-2-10`). -/
public theorem_wanted lucasAllAveragesIntegral_of_dvd_q (params : LucasSequenceParams)
    (m n : ℕ) (hn : 1 < n) (hm : m ∈ lucasAverageSet params) (hnq : (n : ℤ) ∣ params.q)
    (hp : params.p ≡ 1 [ZMOD n] ∨ (Even n ∧ params.p ≡ -1 [ZMOD n])) :
    lucasAllAveragesIntegral params n ∧ lucasAllAveragesIntegral params (m * n)

/-- Theorem 2.13: for nondegenerate `U(a, b)` with `d = gcd(a, b) > 1` and
`gcd(n, d) > 1`, `A_U(n)` is not an integer.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.13
(`integers-2024-A36-thm-2-13`). -/
public theorem_wanted not_dvd_lucasU_sum_of_gcd (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hd : 1 < Int.gcd params.p params.q) (n : ℕ)
    (hn : 1 < Nat.gcd n (Int.gcd params.p params.q)) :
    ¬ (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i

/-- Theorem 2.14: for nondegenerate `U(a, b)` with `a` even and `b` odd, `B_U(n)` is odd and
`A_U(n)` is not an integer when `n ≡ 2 (mod 4)`, and `C(2 ^ k) = 2 ^ k` for `k ≥ 0`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.14
(`integers-2024-A36-thm-2-14`). -/
public theorem_wanted lucasU_sum_odd_of_even_p (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : Even params.p) (hq : Odd params.q) :
    (∀ n, n % 4 = 2 → Odd (∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
      ¬ (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    ∀ k, IsLeast {x | 2 ^ k ∣ x ∧ x ∈ lucasPeriodSet params} (2 ^ k)

/-- Theorem 2.15: for nondegenerate `U(a, b)` with `a ≡ 2 (mod 4)` and `b ≡ 1 (mod 4)`:
`2 ^ i ∈ S(U)` for `i ≥ 1`; `B_U(n) ≡ 0 (mod 2 ^ k)` when `2 ^ k ∥ n` with `k ≥ 2`;
`C'(2) = 4` while `C(2) = 2`; `C'(2 ^ k) = C(2 ^ k) = 2 ^ k` and all `A_W(2 ^ k)` are integers
for `k ≥ 2`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.15
(`integers-2024-A36-thm-2-15`). -/
public theorem_wanted lucasAverageSet_two_pow_of_p_two_mod_four (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p ≡ 2 [ZMOD 4]) (hq : -params.q
        ≡ 1 [ZMOD 4]) :
    (∀ i, 1 ≤ i → 2 ^ i ∈ lucasPeriodSet params) ∧
    (∀ n k : ℕ, 2 ≤ k → 2 ^ k ∣ n → ¬ 2 ^ (k + 1) ∣ n →
      ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    IsLeast {x | 2 ∣ x ∧ x ∈ lucasAverageSet params} 4 ∧
    IsLeast {x | 2 ∣ x ∧ x ∈ lucasPeriodSet params} 2 ∧
    ∀ k, 2 ≤ k → IsLeast {x | 2 ^ k ∣ x ∧ x ∈ lucasAverageSet params} (2 ^ k) ∧
      IsLeast {x | 2 ^ k ∣ x ∧ x ∈ lucasPeriodSet params} (2 ^ k) ∧
      lucasAllAveragesIntegral params (2 ^ k)

/-- Theorem 2.16: for nondegenerate `U(a, b)` with `a ≡ 0 (mod 4)` and `b ≡ 1 (mod 4)`:
`B_U(n) ≢ 0 (mod 2 ^ k)` when `2 ^ k ∥ n` with `k ≥ 1`, so `C'(n)` does not exist for even
`n`, and `A_U(m)` is an integer only if `m` is odd.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.16
(`integers-2024-A36-thm-2-16`). -/
public theorem_wanted lucasU_sum_not_dvd_of_p_zero_mod_four (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p ≡ 0 [ZMOD 4]) (hq : -params.q
        ≡ 1 [ZMOD 4]) :
    (∀ n k : ℕ, 1 ≤ k → 2 ^ k ∣ n → ¬ 2 ^ (k + 1) ∣ n →
      ¬ ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    (∀ n, 0 < n → Even n → ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params) ∧
    ∀ m : ℕ, 0 < m → (m : ℤ) ∣ ∑ i ∈ Finset.Icc 1 m, lucasU params i → Odd m

/-- Theorem 2.17: for nondegenerate `U(a, b)` with `a ≡ 0 (mod 4)` and `b ≡ -1 (mod 4)`:
`2 ^ i ∈ S(U)` for `i ≥ 1`; `B_U(n) ≡ 0 (mod 2 ^ k)` when `2 ^ k ∥ n` with `k ≥ 2`;
`C'(2) = 4` while `C(2) = 2`; `C'(2 ^ k) = C(2 ^ k) = 2 ^ k` and all `A_W(2 ^ k)` are integers
for `k ≥ 2`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.17
(`integers-2024-A36-thm-2-17`). -/
public theorem_wanted lucasAverageSet_two_pow_of_p_zero_mod_four (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p ≡ 0 [ZMOD 4]) (hq : -params.q
        ≡ -1 [ZMOD 4]) :
    (∀ i, 1 ≤ i → 2 ^ i ∈ lucasPeriodSet params) ∧
    (∀ n k : ℕ, 2 ≤ k → 2 ^ k ∣ n → ¬ 2 ^ (k + 1) ∣ n →
      ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    IsLeast {x | 2 ∣ x ∧ x ∈ lucasAverageSet params} 4 ∧
    IsLeast {x | 2 ∣ x ∧ x ∈ lucasPeriodSet params} 2 ∧
    ∀ k, 2 ≤ k → IsLeast {x | 2 ^ k ∣ x ∧ x ∈ lucasAverageSet params} (2 ^ k) ∧
      IsLeast {x | 2 ^ k ∣ x ∧ x ∈ lucasPeriodSet params} (2 ^ k) ∧
      lucasAllAveragesIntegral params (2 ^ k)

/-- Theorem 2.18: for nondegenerate `U(a, b)` with `a ≡ 2 (mod 4)` and `b ≡ -1 (mod 4)`:
`B_U(n) ≢ 0 (mod 2 ^ k)` when `2 ^ k ∥ n` with `k ≥ 1`, so `C'(n)` does not exist for even
`n`, and `A_U(n)` is an integer only if `n` is odd.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.18
(`integers-2024-A36-thm-2-18`). -/
public theorem_wanted lucasU_sum_not_dvd_of_p_two_mod_four (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p ≡ 2 [ZMOD 4]) (hq : -params.q
        ≡ -1 [ZMOD 4]) :
    (∀ n k : ℕ, 1 ≤ k → 2 ^ k ∣ n → ¬ 2 ^ (k + 1) ∣ n →
      ¬ ((2 ^ k : ℕ) : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    (∀ n, 0 < n → Even n → ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params) ∧
    ∀ m : ℕ, 0 < m → (m : ℤ) ∣ ∑ i ∈ Finset.Icc 1 m, lucasU params i → Odd m

/-- Theorem 3.1 (Wyler): for nondegenerate `U(a, b)` and `m ≥ 2` with `gcd(m, b) = 1`, let
`h = ord_m(-b)`, `ρ = ρ_U(m)`, `π = π_U(m)` and `H = lcm(h, ρ)`. Then `π = H` or `π = 2 H`.
If `m = ℓ ^ i` for an odd prime `ℓ` and `i ≥ 1`, then `π = 2 H` when the `2`-adic valuations of
`h` and `ρ` differ, and `π = H` when they are equal and positive.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 3.1
(`integers-2024-A36-thm-3-1`). -/
public theorem_wanted lucasUPeriod_eq_lcm_orderOf (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (m : ℕ) (hm : 2 ≤
        m) (hmb : IsCoprime (m : ℤ) params.q) :
    (lucasUPeriod params m =
        Nat.lcm (orderOf (params.q : ZMod m)) (lucasURestrictedPeriod params m) ∨
      lucasUPeriod params m =
        2 * Nat.lcm (orderOf (params.q : ZMod m)) (lucasURestrictedPeriod params m)) ∧
    ∀ ℓ i : ℕ, ℓ.Prime → ℓ ≠ 2 → 1 ≤ i → m = ℓ ^ i →
      (padicValNat 2 (orderOf (params.q : ZMod m)) ≠
          padicValNat 2 (lucasURestrictedPeriod params m) →
        lucasUPeriod params m =
          2 * Nat.lcm (orderOf (params.q : ZMod m)) (lucasURestrictedPeriod params m)) ∧
      (padicValNat 2 (orderOf (params.q : ZMod m)) =
          padicValNat 2 (lucasURestrictedPeriod params m) →
        0 < padicValNat 2 (lucasURestrictedPeriod params m) →
        lucasUPeriod params m =
          Nat.lcm (orderOf (params.q : ZMod m)) (lucasURestrictedPeriod params m))

/-- Corollary 3.1 (i)-(iii): for nondegenerate `U(a, 1)` and `m ≥ 2`, with `π = π_U(m)`,
`ρ = ρ_U(m)` and `E = π / ρ`: `E ∈ {1, 2, 4}`; if `m = ℓ ^ i` with `ℓ` an odd prime and
`i ≥ 1`, then `E = 1`, `2`, `4` according as `ρ ≡ 2 (mod 4)`, `ρ ≡ 0 (mod 4)`, `ρ` odd; and `π`
is even unless `m = 2` and `a` is odd. Part (iv), about `L(m)`, is not formalized.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 3.1
(`integers-2024-A36-cor-3-1`). -/
public theorem_wanted lucasUPeriod_of_q_eq_neg_one (params : LucasSequenceParams)
    (hq : params.q = -1) (hnd : IsNondegenerateLucasPair params.p params.q) (m : ℕ) (hm : 2 ≤ m) :
    (lucasUPeriod params m = lucasURestrictedPeriod params m ∨
      lucasUPeriod params m = 2 * lucasURestrictedPeriod params m ∨
      lucasUPeriod params m = 4 * lucasURestrictedPeriod params m) ∧
    (∀ ℓ i : ℕ, ℓ.Prime → ℓ ≠ 2 → 1 ≤ i → m = ℓ ^ i →
      (lucasURestrictedPeriod params m % 4 = 2 →
          lucasUPeriod params m = lucasURestrictedPeriod params m) ∧
      (lucasURestrictedPeriod params m % 4 = 0 →
          lucasUPeriod params m = 2 * lucasURestrictedPeriod params m) ∧
      (lucasURestrictedPeriod params m % 2 = 1 →
          lucasUPeriod params m = 4 * lucasURestrictedPeriod params m)) ∧
    (¬ (m = 2 ∧ Odd params.p) → Even (lucasUPeriod params m))

/-- Corollary 3.2: for nondegenerate `U(a, -1)` and `m ≥ 2`, `E_U(m) = π_U(m) / ρ_U(m)` is
`1` or `2`, and if `m = ℓ ^ i` with `ℓ` an odd prime, `i ≥ 1` and `ρ_U(m)` even, then
`E_U(m) = 2`. Part (ii)(b) (`E = 1` or `2` when `ρ` is odd) is the case of part (i).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 3.2
(`integers-2024-A36-cor-3-2`). -/
public theorem_wanted lucasUPeriod_of_q_eq_one (params : LucasSequenceParams)
    (hq : params.q = 1) (hnd : IsNondegenerateLucasPair params.p params.q) (m : ℕ) (hm : 2 ≤ m) :
    (lucasUPeriod params m = lucasURestrictedPeriod params m ∨
      lucasUPeriod params m = 2 * lucasURestrictedPeriod params m) ∧
    ∀ ℓ i : ℕ, ℓ.Prime → ℓ ≠ 2 → 1 ≤ i → m = ℓ ^ i →
      Even (lucasURestrictedPeriod params m) →
        lucasUPeriod params m = 2 * lucasURestrictedPeriod params m

/-- Theorem 3.2: let `b = ±1` and let the prime `ℓ` divide `D`. If `b = 1` then `ℓ = 2` or
`ℓ ≡ 1 (mod 4)`. If `b = -1` then `a ≡ ±2 (mod ℓ)`; if `a ≡ 2 (mod ℓ)` then
`E_U(ℓ ^ i) = 1` for `i ≥ 1`, and if `a ≡ -2 (mod ℓ)` and `ℓ > 2` then `E_U(ℓ ^ i) = 2`.
The `a ≡ 2 (mod ℓ)` claim is restricted to odd `ℓ`: it is false as printed for `ℓ = 2`, e.g.
`(a, b) = (4, -1)` has `D = 12`, `a ≡ 2 (mod 2)`, but `π_U(4) = 4` and `ρ_U(4) = 2`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 3.2
(`integers-2024-A36-thm-3-2`). -/
public theorem_wanted lucasUPeriod_prime_dvd_discr (params : LucasSequenceParams) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (hD : (ℓ : ℤ) ∣ params.p ^ 2 - 4 * params.q) :
    (params.q = -1 → ℓ = 2 ∨ ℓ % 4 = 1) ∧
    (params.q = 1 →
      (params.p ≡ 2 [ZMOD ℓ] ∨ params.p ≡ -2 [ZMOD ℓ]) ∧
      (params.p ≡ 2 [ZMOD ℓ] → 2 < ℓ → ∀ i, 1 ≤ i →
        lucasUPeriod params (ℓ ^ i) = lucasURestrictedPeriod params (ℓ ^ i)) ∧
      (params.p ≡ -2 [ZMOD ℓ] → 2 < ℓ → ∀ i, 1 ≤ i →
        lucasUPeriod params (ℓ ^ i) = 2 * lucasURestrictedPeriod params (ℓ ^ i)))

/-- Theorem 3.3: for nondegenerate `U(a, b) = U(-b + 1, b)` with `b ≠ ±1`, the discriminant is
`D = (-b - 1) ^ 2`, `U n = ((-b) ^ n - 1) / (-b - 1)` (roots `-b` and `1`),
`U (n + 1) = (-b) U n + 1`, `U i ≡ 1 (mod b)` for `i ≥ 1`, and for `gcd(n, b) = 1`,
`E_U(n) = 1`, i.e. `π_U(n) = ρ_U(n)`. The root identification is stated through the closed
form.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 3.3
(`integers-2024-A36-thm-3-3`). -/
public theorem_wanted lucasUPeriod_eq_restricted_of_p_eq_q_add_one
    (params : LucasSequenceParams) (hp : params.p = params.q + 1) (hq1 : params.q ≠ 1)
    (hq2 : params.q ≠ -1) (hnd : IsNondegenerateLucasPair params.p params.q) :
    params.p ^ 2 - 4 * params.q = (params.q - 1) ^ 2 ∧
    (∀ n, (params.q - 1) * lucasU params n = params.q ^ n - 1) ∧
    (∀ n, lucasU params (n + 1) = params.q * lucasU params n + 1) ∧
    (∀ i, 1 ≤ i → lucasU params i ≡ 1 [ZMOD params.q]) ∧
    ∀ n : ℕ, 0 < n → IsCoprime (n : ℤ) params.q →
      lucasUPeriod params n = lucasURestrictedPeriod params n

/-- Theorem 3.4: for nondegenerate `U(a, b) = U(b - 1, b)` with `b ≠ ±1`, the discriminant is
`D = (b + 1) ^ 2`, `U n = (b ^ n - (-1) ^ n) / (b + 1)` (roots `b` and `-1`),
`U (n + 1) = b U n + (-1) ^ n`, and for `gcd(n, b) = 1`: if `ρ_U(n)` is even then
`π_U(n) = ρ_U(n)` and the multiplier `M_U(n) = U (ρ_U(n) + 1) ≡ 1 (mod n)`; if `ρ_U(n)` is odd
and `n > 1` then `π_U(n) = 2 ρ_U(n)` and `M_U(n) ≡ -1 (mod n)`; and `π_U(n)` is even for
`n > 1`. The hypothesis `n > 1` in the odd case is added: as printed the claim fails at `n = 1`,
where `ρ_U(1) = π_U(1) = 1` (Theorem 1.4 (ix)).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 3.4
(`integers-2024-A36-thm-3-4`). -/
public theorem_wanted lucasUPeriod_of_p_eq_neg_q_sub_one
    (params : LucasSequenceParams) (hp : params.p = -params.q - 1) (hq1 : params.q ≠ 1)
    (hq2 : params.q ≠ -1) (hnd : IsNondegenerateLucasPair params.p params.q) :
    params.p ^ 2 - 4 * params.q = (params.q - 1) ^ 2 ∧
    (∀ n, (1 - params.q) * lucasU params n = (-params.q) ^ n - (-1) ^ n) ∧
    (∀ n, lucasU params (n + 1) = -params.q * lucasU params n + (-1) ^ n) ∧
    ∀ n : ℕ, 0 < n → IsCoprime (n : ℤ) params.q →
      (Even (lucasURestrictedPeriod params n) →
        lucasUPeriod params n = lucasURestrictedPeriod params n ∧
        lucasU params (lucasURestrictedPeriod params n + 1) ≡ 1 [ZMOD n]) ∧
      (1 < n → Odd (lucasURestrictedPeriod params n) →
        lucasUPeriod params n = 2 * lucasURestrictedPeriod params n ∧
        lucasU params (lucasURestrictedPeriod params n + 1) ≡ -1 [ZMOD n]) ∧
      (1 < n → Even (lucasUPeriod params n))

/-- Lemma 2.1: for nondegenerate `U(a, b)`, an odd prime `ℓ` with `ℓ ^ e ∥ a` (`e ≥ 1`) and
`b ≡ 1 (mod ℓ ^ (e + 1))`, one has `ℓ ^ e ∥ a + b - 1`, and `B_U(2 m ℓ ^ i) ≡ 0 (mod ℓ ^ i)`
for `m ≥ 1` and `i ≥ 1`. The paper's hypothesis `a + b - 1 ≠ 0` is implied by the others and
is dropped; `a ≠ 0` is part of nondegeneracy.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Lemma 2.1
(`integers-2024-A36-lem-2-1`). -/
public theorem_wanted lucasU_sum_two_mul_prime_pow_dvd (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (ℓ e : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠
        2) (he : 1 ≤ e)
    (hae : (ℓ : ℤ) ^ e ∣ params.p) (hae' : ¬ (ℓ : ℤ) ^ (e + 1) ∣ params.p)
    (hb : -params.q ≡ 1 [ZMOD (ℓ : ℤ) ^ (e + 1)]) :
    ((ℓ : ℤ) ^ e ∣ params.p - params.q - 1 ∧ ¬ (ℓ : ℤ) ^ (e + 1) ∣ params.p - params.q - 1) ∧
    ∀ m i : ℕ, 1 ≤ m → 1 ≤ i →
      (ℓ : ℤ) ^ i ∣ ∑ k ∈ Finset.Icc 1 (2 * m * ℓ ^ i), lucasU params k

/-- Theorem 2.12: for nondegenerate `U(a, b)` with `b (a + b - 1) ≠ 0`, `n ∈ S(U)` and `A_W(n)`
is an integer for all `W(a, b)` in the cases (`i, j ≥ 0`): (i) `a ≡ ±1`, `b ≡ 1 (mod 6)`,
`n = 1` or `n = 2 ^ (i + 3) 3 ^ (j + 1)`; (ii) `a ≡ 1`, `b ≡ -1 (mod 6)`, `n = 1` or
`n = 2 ^ (i + 1) 3 ^ (j + 1)`; (iii) `a ≡ 3`, `b ≡ -1 (mod 6)`, `n = 1` or
`n = 2 ^ (i + 2) 3 ^ (j + 1)`; (iv) `a ≡ 3 (mod 6)`, `3 ^ e ∥ a` with `e ≥ 1`,
`b ≡ 1 (mod 2 · 3 ^ (e + 1))`, `n = 1` or `n = 2 ^ (i + 1) 3 ^ (j + 1)`. The paper's
`rad(n) ∣ 6` is implied by the displayed forms of `n`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.12
(`integers-2024-A36-thm-2-12`). -/
public theorem_wanted mem_lucasPeriodSet_of_two_three_smooth (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hab : params.p - params.q - 1 ≠ 0) :
    ((params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) → -params.q ≡ 1 [ZMOD 6] →
      ∀ n, (n = 1 ∨ ∃ i j : ℕ, n = 2 ^ (i + 3) * 3 ^ (j + 1)) →
        n ∈ lucasPeriodSet params ∧ lucasAllAveragesIntegral params n) ∧
    (params.p ≡ 1 [ZMOD 6] → -params.q ≡ -1 [ZMOD 6] →
      ∀ n, (n = 1 ∨ ∃ i j : ℕ, n = 2 ^ (i + 1) * 3 ^ (j + 1)) →
        n ∈ lucasPeriodSet params ∧ lucasAllAveragesIntegral params n) ∧
    (params.p ≡ 3 [ZMOD 6] → -params.q ≡ -1 [ZMOD 6] →
      ∀ n, (n = 1 ∨ ∃ i j : ℕ, n = 2 ^ (i + 2) * 3 ^ (j + 1)) →
        n ∈ lucasPeriodSet params ∧ lucasAllAveragesIntegral params n) ∧
    (∀ e : ℕ, 1 ≤ e → params.p ≡ 3 [ZMOD 6] → (3 : ℤ) ^ e ∣ params.p →
      ¬ (3 : ℤ) ^ (e + 1) ∣ params.p → -params.q ≡ 1 [ZMOD 2 * 3 ^ (e + 1)] →
      ∀ n, (n = 1 ∨ ∃ i j : ℕ, n = 2 ^ (i + 1) * 3 ^ (j + 1)) →
        n ∈ lucasPeriodSet params ∧ lucasAllAveragesIntegral params n)

/-- Theorem 2.19: for nondegenerate `U(a, b)` with `a + b - 1 ≠ 0` and odd `n` with
`a ≡ 2`, `b ≡ -1 (mod rad(n))`: `rad(n) ∣ D`, `C'(n) = C(n) = n`, and `A_W(n)` is an integer
for all `W(a, b)`. Congruences modulo `rad(n)` are stated prime by prime (equivalent by the
Chinese remainder theorem), and `C`, `C'` as `IsLeast`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.19
(`integers-2024-A36-thm-2-19`). -/
public theorem_wanted isLeast_lucasAverageSet_of_odd (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hab : params.p - params.q - 1 ≠
        0) (n : ℕ) (hn : 0 < n)
    (hodd : Odd n)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → params.p ≡ 2 [ZMOD ℓ] ∧ -params.q ≡ -1 [ZMOD ℓ]) :
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → (ℓ : ℤ) ∣ params.p ^ 2 - 4 * params.q) ∧
    IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} n ∧
    IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} n ∧ lucasAllAveragesIntegral params n

/-- Theorem 2.20: for nondegenerate `U(a, b)` with `a + b - 1 ≠ 0`, `n = 2 ^ k n₁` with
`k ≥ 1`, odd `n₁ > 1`, `a` even, `a ≡ -2 (mod rad(n₁))` and `b ≡ -1 (mod 4 rad(n₁))`:
`rad(n₁) ∣ D` and `C(n) = n`; if `a ≡ 2 (mod 4)` then `C'(n)` does not exist; if
`a ≡ 0 (mod 4)` then `C'(n) = 2 n` with `A_W(2 n)` integral when `n ≡ 2 (mod 4)`, and
`C'(n) = n` with `A_W(n)` integral when `n ≡ 0 (mod 4)`. The paper's "for all recurrences
`W(a, -1)`" is read as `W(a, b)`, the recurrences of the theorem's sequence. Congruences
modulo `rad(n₁)` are stated prime by prime.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.20
(`integers-2024-A36-thm-2-20`). -/
public theorem_wanted lucasPeriodSet_isLeast_of_even_p (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hab : params.p - params.q - 1 ≠
        0) (k n₁ : ℕ)
    (hk : 1 ≤ k) (hn₁ : 1 < n₁) (hodd : Odd n₁) (hp : Even params.p)
    (hq4 : -params.q ≡ -1 [ZMOD 4])
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n₁ → params.p ≡ -2 [ZMOD ℓ] ∧ -params.q ≡ -1 [ZMOD ℓ]) :
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n₁ → (ℓ : ℤ) ∣ params.p ^ 2 - 4 * params.q) ∧
    IsLeast {x | 2 ^ k * n₁ ∣ x ∧ x ∈ lucasPeriodSet params} (2 ^ k * n₁) ∧
    (params.p ≡ 2 [ZMOD 4] → ¬ ∃ x, 2 ^ k * n₁ ∣ x ∧ x ∈ lucasAverageSet params) ∧
    (params.p ≡ 0 [ZMOD 4] →
      (k = 1 → IsLeast {x | 2 ^ k * n₁ ∣ x ∧ x ∈ lucasAverageSet params} (2 * (2 ^ k * n₁)) ∧
        lucasAllAveragesIntegral params (2 * (2 ^ k * n₁))) ∧
      (2 ≤ k → IsLeast {x | 2 ^ k * n₁ ∣ x ∧ x ∈ lucasAverageSet params} (2 ^ k * n₁) ∧
        lucasAllAveragesIntegral params (2 ^ k * n₁)))

/-- Theorem 2.21: for nondegenerate `U(a, b)` and `n` with `6 ∣ n`, `a ≡ 1` and
`b ≡ -1 (mod rad(n))`: `C'(n) = C(n) = n` and `A_W(n)` is an integer for all `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.21
(`integers-2024-A36-thm-2-21`). -/
public theorem_wanted isLeast_lucasAverageSet_of_six_dvd (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → params.p ≡ 1 [ZMOD ℓ] ∧ -params.q ≡ -1 [ZMOD ℓ]) :
    IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} n ∧
    IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} n ∧ lucasAllAveragesIntegral params n

/-- Theorem 2.22: for nondegenerate `U(a, b)` and `n` with `3 ∣ n`, `a ≡ -1` and
`b ≡ -1 (mod rad(n))`: `C'(n) = C(n) = n` and `A_W(n)` is an integer for all `W(a, b)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.22
(`integers-2024-A36-thm-2-22`). -/
public theorem_wanted isLeast_lucasAverageSet_of_three_dvd (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → params.p ≡ -1 [ZMOD ℓ] ∧ -params.q ≡ -1 [ZMOD ℓ]) :
    IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} n ∧
    IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} n ∧ lucasAllAveragesIntegral params n

/-- Theorem 2.23: for nondegenerate `U(a, b)` and `n = 2 ^ k n₁` with `k ≥ 2`, `n₁` odd,
`a ≡ 0` and `b ≡ -1 (mod 4 rad(n₁))`: `C'(n) = C(n) = n` and `A_W(n)` is an integer for all
`W(a, b)`. The modulus `4 rad(n₁)` is split into `4` and the primes of `n₁`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.23
(`integers-2024-A36-thm-2-23`). -/
public theorem_wanted isLeast_lucasAverageSet_of_four_dvd (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (k n₁ : ℕ) (hk : 2 ≤ k) (hodd : Odd n₁)
    (hp4 : params.p ≡ 0 [ZMOD 4]) (hq4 : -params.q ≡ -1 [ZMOD 4])
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n₁ → params.p ≡ 0 [ZMOD ℓ] ∧ -params.q ≡ -1 [ZMOD ℓ]) :
    IsLeast {x | 2 ^ k * n₁ ∣ x ∧ x ∈ lucasAverageSet params} (2 ^ k * n₁) ∧
    IsLeast {x | 2 ^ k * n₁ ∣ x ∧ x ∈ lucasPeriodSet params} (2 ^ k * n₁) ∧
    lucasAllAveragesIntegral params (2 ^ k * n₁)

/-- Theorem 4.2: for nondegenerate `U(a, b)` with `a = -b + 1`, `S(U) = T(U)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 4.2
(`integers-2024-A36-thm-4-2`). -/
public theorem_wanted lucasPeriodSet_eq_lucasIndexDivisibleSet (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p = params.q + 1) :
    lucasPeriodSet params = lucasIndexDivisibleSet params

/-- `LucasPeriodOrbitCloses params n k`: the iterated periods `π_U^i(n)` (with `π_U^0(n) = n`)
are coprime to `b` for `0 ≤ i ≤ k`, and `π_U^(k+1)(n) = π_U^j(n)` for some `j ≤ k`. The least such
`k` is the paper's `ω(n)`, and "`ω(n)` exists" is `∃ k, LucasPeriodOrbitCloses params n k`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.4. -/
def LucasPeriodOrbitCloses (params : LucasSequenceParams) (n k : ℕ) : Prop :=
  (∃ j ≤ k, (lucasUPeriod params)^[k + 1] n = (lucasUPeriod params)^[j] n) ∧
    ∀ i ≤ k, IsCoprime (((lucasUPeriod params)^[i] n : ℕ) : ℤ) params.q

/-- The index `ω(n)`: the least `k` with `LucasPeriodOrbitCloses params n k` (`0` when no such
`k` exists).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.4. -/
noncomputable def lucasPeriodOrbitIndex (params : LucasSequenceParams) (n : ℕ) : ℕ :=
  sInf {k | LucasPeriodOrbitCloses params n k}

/-- `L(n) = lcm(π_U^0(n), π_U^1(n), …, π_U^ω(n)(n))`, equation (2.14). It is meaningful when
`ω(n)` exists.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.8, equation
(2.14). -/
noncomputable def lucasPeriodOrbitLcm (params : LucasSequenceParams) (n : ℕ) : ℕ :=
  (Finset.range (lucasPeriodOrbitIndex params n + 1)).lcm fun i => (lucasUPeriod params)^[i] n

/-- The orbit of `1` closes at once: `π_U(1) = 1`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.4 and Theorem 1.4
(ix). -/
theorem lucasPeriodOrbitCloses_one_zero (params : LucasSequenceParams) :
    LucasPeriodOrbitCloses params 1 0 :=
  ⟨⟨0, le_rfl, by simp [lucasUPeriod_one]⟩, fun i hi => by
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp [isCoprime_one_left]⟩

/-- `ω(1) = 0`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.4. -/
theorem lucasPeriodOrbitIndex_one (params : LucasSequenceParams) :
    lucasPeriodOrbitIndex params 1 = 0 :=
  Nat.le_zero.mp (Nat.sInf_le (lucasPeriodOrbitCloses_one_zero params))

/-- `L(1) = 1`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, equation (2.14). -/
theorem lucasPeriodOrbitLcm_one (params : LucasSequenceParams) :
    lucasPeriodOrbitLcm params 1 = 1 := by
  simp [lucasPeriodOrbitLcm, lucasPeriodOrbitIndex_one]

/-- `n ∣ L(n)` (Remark 2.6).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.6. -/
theorem dvd_lucasPeriodOrbitLcm (params : LucasSequenceParams) (n : ℕ) :
    n ∣ lucasPeriodOrbitLcm params n :=
  Finset.dvd_lcm (f := fun i => (lucasUPeriod params)^[i] n)
    (Finset.mem_range.2 (Nat.succ_pos _))

/-- Theorem 1.4: for nondegenerate `U(a, b)` and a prime `p`, writing `E_U(p) = π_U(p) / ρ_U(p)`:
(i) if `p ∤ 2 b D` then `ρ_U(p) > 1`, `ρ_U(p) ∣ p - (D / p)`, `ρ_U(p) ∣ π_U(p)` and
`E_U(p) ∣ p - 1`; if `p = 2 ∤ b D` then `π_U(2) = 3`; (ii) if `p ∤ 2 b D` then
`ρ_U(p) ∣ (p - (D / p)) / 2` iff `(-b / p) = 1`; (iii) if `p ∤ b`, `p ∣ D` then `ρ_U(p) = p` and
`π_U(p) ∣ p (p - 1)`; (iv) if `p ∤ 2 b` and `(D / p) = 1` then `π_U(p) ∣ p - 1`; (v) if `p ∤ 2 b`
and `(D / p) = -1` then `π_U(p) ∣ p ^ 2 - 1` and every prime factor `ℓ` of `π_U(p)` has
`ℓ ≤ (p + 1) / 2`; (vi) if `p ∤ b`, `p ∣ D` then the largest prime factor of `π_U(p)` is `p`;
(vii)-(viii) for `p ∤ b`, the largest `c` (resp. `e`) with `ρ_U(p ^ c) = ρ_U(p)` (resp.
`π_U(p ^ e) = π_U(p)`) exists and gives `ρ_U(p ^ i) = p ^ max(i - c, 0) ρ_U(p)` (resp. the same
for `π_U`) for `i ≥ 1` when `p ^ c ≠ 2`, and `ρ_U(2 ^ i) = 2 ^ max(i + 1 - d, 1) ρ_U(2)` for
`i ≥ 2` with `d` the largest index with `ρ_U(2 ^ d) = ρ_U(4)` when `p ^ c = 2`; (ix)
`ρ_U(1) = π_U(1) = 1`. Legendre symbols are `jacobiSym`; `-b = Q`. The claim
`E_U(p) ∣ p - 1`, printed under "if `p ≥ 2`", is stated under the hypothesis `p ∤ 2 b D` of (i).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.4
(`integers-2024-A36-thm-1-4`). -/
public theorem_wanted lucasUPeriod_prime_properties (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (p : ℕ) (hp : p.Prime) :
    (¬ (p : ℤ) ∣ 2 * params.q * (params.p ^ 2 - 4 * params.q) →
      1 < lucasURestrictedPeriod params p ∧
      ((lucasURestrictedPeriod params p : ℕ) : ℤ) ∣
        p - jacobiSym (params.p ^ 2 - 4 * params.q) p ∧
      lucasURestrictedPeriod params p ∣ lucasUPeriod params p ∧
      lucasUPeriod params p / lucasURestrictedPeriod params p ∣ p - 1) ∧
    (p = 2 → ¬ (2 : ℤ) ∣ params.q * (params.p ^ 2 - 4 * params.q) →
      lucasUPeriod params 2 = 3) ∧
    (¬ (p : ℤ) ∣ 2 * params.q * (params.p ^ 2 - 4 * params.q) →
      (((lucasURestrictedPeriod params p : ℕ) : ℤ) ∣
          (p - jacobiSym (params.p ^ 2 - 4 * params.q) p) / 2 ↔
        jacobiSym params.q p = 1)) ∧
    (¬ (p : ℤ) ∣ params.q → (p : ℤ) ∣ params.p ^ 2 - 4 * params.q →
      lucasURestrictedPeriod params p = p ∧ lucasUPeriod params p ∣ p * (p - 1)) ∧
    (¬ (p : ℤ) ∣ 2 * params.q → jacobiSym (params.p ^ 2 - 4 * params.q) p = 1 →
      lucasUPeriod params p ∣ p - 1) ∧
    (¬ (p : ℤ) ∣ 2 * params.q → jacobiSym (params.p ^ 2 - 4 * params.q) p = -1 →
      lucasUPeriod params p ∣ p ^ 2 - 1 ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ lucasUPeriod params p → 2 * ℓ ≤ p + 1) ∧
    (¬ (p : ℤ) ∣ params.q → (p : ℤ) ∣ params.p ^ 2 - 4 * params.q →
      p ∣ lucasUPeriod params p ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ lucasUPeriod params p → ℓ ≤ p) ∧
    (¬ (p : ℤ) ∣ params.q →
      ∃ c, IsGreatest {c | 1 ≤ c ∧
          lucasURestrictedPeriod params (p ^ c) = lucasURestrictedPeriod params p} c ∧
        (p ^ c ≠ 2 → ∀ i, 1 ≤ i →
          lucasURestrictedPeriod params (p ^ i) = p ^ (i - c) * lucasURestrictedPeriod params p) ∧
        (p ^ c = 2 → ∃ d, IsGreatest {d | 2 ≤ d ∧
            lucasURestrictedPeriod params (2 ^ d) = lucasURestrictedPeriod params 4} d ∧
          ∀ i, 2 ≤ i → lucasURestrictedPeriod params (2 ^ i) =
            2 ^ max (i + 1 - d) 1 * lucasURestrictedPeriod params 2)) ∧
    (¬ (p : ℤ) ∣ params.q →
      ∃ e, IsGreatest {e | 1 ≤ e ∧ lucasUPeriod params (p ^ e) = lucasUPeriod params p} e ∧
        (p ^ e ≠ 2 → ∀ i, 1 ≤ i →
          lucasUPeriod params (p ^ i) = p ^ (i - e) * lucasUPeriod params p) ∧
        (p ^ e = 2 → ∃ g, IsGreatest {g | 2 ≤ g ∧
            lucasUPeriod params (2 ^ g) = lucasUPeriod params 4} g ∧
          ∀ i, 2 ≤ i → lucasUPeriod params (2 ^ i) =
            2 ^ max (i + 1 - g) 1 * lucasUPeriod params 2)) ∧
    lucasURestrictedPeriod params 1 = 1 ∧ lucasUPeriod params 1 = 1

/-- Theorem 1.5: for nondegenerate `U(a, b)` and a prime `p` with `p ∤ b` and `p ∣ D`, writing
`E_U(p) = π_U(p) / ρ_U(p)`: (i) `ρ_U(p) = p` and each residue modulo `p` appears exactly
`E_U(p)` times among `U 0, …, U (π_U(p) - 1)`; (ii) for `p ≥ 5`, `i ≥ 1`: `ρ_U(p ^ i) = p ^ i`,
`π_U(p ^ i) = p ^ i E_U(p)`, and each residue modulo `p ^ i` appears exactly `E_U(p)` times in a
least period; (iii) for `p = 2`: `a` is even, `ρ_U(2 ^ i) = 2 ^ i` if `a ≡ 2 (mod 4)`, and if also
`b ≡ -1 (mod 4)` each residue modulo `2 ^ i` appears once; (iv) for `p = 3`:
`3 ∣ U 3 = a ^ 2 + b`, and if `9 ∤ a ^ 2 + b` then `ρ_U(3 ^ i) = 3 ^ i` with each residue modulo
`3 ^ i` appearing `E_U(3)` times; (v) for `p = 2`, `ν₂(a) = c ≥ 2`:
`ρ_U(2 ^ i) = 2 ^ max(i + 1 - c, 1)`; (vi) for `p = 3`, `ν₃(a ^ 2 + b) = d ≥ 2`:
`ρ_U(3 ^ i) = 3 ^ max(i + 1 - d, 1)`. The paper's hypothesis `p ∤ gcd(a, b)` follows from
`p ∤ b` and is dropped; `a ^ 2 + b = P ^ 2 - Q`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.5
(`integers-2024-A36-thm-1-5`). -/
public theorem_wanted lucasU_uniform_of_prime_dvd_discr (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (p : ℕ) (hp : p.Prime)
    (hpb : ¬ (p : ℤ) ∣ params.q)
    (hpD : (p : ℤ) ∣ params.p ^ 2 - 4 * params.q) :
    (lucasURestrictedPeriod params p = p ∧
      lucasURestrictedPeriod params p ∣ lucasUPeriod params p ∧
      ∀ r : ZMod p, ((Finset.range (lucasUPeriod params p)).filter
          fun k => (lucasU params k : ZMod p) = r).card =
        lucasUPeriod params p / lucasURestrictedPeriod params p) ∧
    (5 ≤ p → ∀ i, 1 ≤ i →
      lucasURestrictedPeriod params (p ^ i) = p ^ i ∧
      lucasUPeriod params (p ^ i) =
        p ^ i * (lucasUPeriod params p / lucasURestrictedPeriod params p) ∧
      ∀ r : ZMod (p ^ i), ((Finset.range (lucasUPeriod params (p ^ i))).filter
          fun k => (lucasU params k : ZMod (p ^ i)) = r).card =
        lucasUPeriod params p / lucasURestrictedPeriod params p) ∧
    (p = 2 → (2 : ℤ) ∣ params.p ∧
      (params.p ≡ 2 [ZMOD 4] → ∀ i, 1 ≤ i →
        lucasURestrictedPeriod params (2 ^ i) = 2 ^ i ∧
        (-params.q ≡ -1 [ZMOD 4] → ∀ r : ZMod (2 ^ i),
          ((Finset.range (lucasUPeriod params (2 ^ i))).filter
            fun k => (lucasU params k : ZMod (2 ^ i)) = r).card = 1))) ∧
    (p = 3 → (3 : ℤ) ∣ params.p ^ 2 - params.q ∧
      (¬ (9 : ℤ) ∣ params.p ^ 2 - params.q → ∀ i, 1 ≤ i →
        lucasURestrictedPeriod params (3 ^ i) = 3 ^ i ∧
        ∀ r : ZMod (3 ^ i), ((Finset.range (lucasUPeriod params (3 ^ i))).filter
            fun k => (lucasU params k : ZMod (3 ^ i)) = r).card =
          lucasUPeriod params 3 / lucasURestrictedPeriod params 3)) ∧
    (p = 2 → ∀ c, 2 ≤ c → padicValInt 2 params.p = c → ∀ i, 1 ≤ i →
      lucasURestrictedPeriod params (2 ^ i) = 2 ^ max (i + 1 - c) 1) ∧
    (p = 3 → ∀ d, 2 ≤ d → padicValInt 3 (params.p ^ 2 - params.q) = d → ∀ i, 1 ≤ i →
      lucasURestrictedPeriod params (3 ^ i) = 3 ^ max (i + 1 - d) 1)

/-- Theorem 2.8: if `gcd(n, b) = 1` and `ω(n)` exists, then `C(n)` exists and equals `L(n)`.
Further, whenever `C(n) = c` exists and `a + b - 1 ≠ 0` with `gcd(c, a + b - 1) = 1`, or
`a + b - 1 = 0` with `gcd(c, -b - 1) = 1`, then `C'(n) = c` and `A_W(c)` is an integer for all
`W(a, b)`. `gcd(n, b) = 1` is the `i = 0` case of `LucasPeriodOrbitCloses`; `C`, `C'` are stated
as `IsLeast`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.8
(`integers-2024-A36-thm-2-8`). -/
public theorem_wanted isLeast_lucasPeriodSet_eq_lucasPeriodOrbitLcm
    (params : LucasSequenceParams) (n : ℕ) (hn : 0 < n) :
    ((∃ k, LucasPeriodOrbitCloses params n k) →
      IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} (lucasPeriodOrbitLcm params n)) ∧
    ∀ c, IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c →
      ((params.p - params.q - 1 ≠ 0 ∧ IsCoprime (c : ℤ) (params.p - params.q - 1)) ∨
          (params.p - params.q - 1 = 0 ∧ IsCoprime (c : ℤ) (params.q - 1))) →
      IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} c ∧ lucasAllAveragesIntegral params c

/-- Corollary 2.4: (i) if `ω(n)` exists and `m ∣ n`, then `ω(m)` exists and `L(m) ∣ L(n)`;
(ii) if `ω(n)` exists and `g ∣ π_U^i(n)`, then `ω(g)` exists and `L(g) ∣ L(n)`; (iii) if
`gcd(r, s) = 1` and `ω(r)`, `ω(s)` exist, then `ω(r s)` exists and
`L(r s) = lcm(L(r), L(s))`; (iv) if `p` is prime, `ω(p)` exists and `i ≥ 1`, then `ω(p ^ i)`
exists and `L(p ^ i) = lcm(p ^ i, L(p))`. The coprimality to `b` of `n`, `r`, `s`, `p` is part of
the existence of `ω`; existence of `ω(g)` in (ii) and of `ω(r s)` in (iii) is implicit in the
paper's statements about `L(g)` and `L(r s)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.4
(`integers-2024-A36-cor-2-4`). -/
public theorem_wanted lucasPeriodOrbitLcm_dvd_of_dvd (params : LucasSequenceParams) :
    (∀ m n : ℕ, 0 < n → (∃ k, LucasPeriodOrbitCloses params n k) → m ∣ n →
      (∃ k, LucasPeriodOrbitCloses params m k) ∧
        lucasPeriodOrbitLcm params m ∣ lucasPeriodOrbitLcm params n) ∧
    (∀ n g i : ℕ, 0 < n → 0 < g → (∃ k, LucasPeriodOrbitCloses params n k) →
      g ∣ (lucasUPeriod params)^[i] n →
      (∃ k, LucasPeriodOrbitCloses params g k) ∧
        lucasPeriodOrbitLcm params g ∣ lucasPeriodOrbitLcm params n) ∧
    (∀ r s : ℕ, 0 < r → 0 < s → Nat.Coprime r s → (∃ k, LucasPeriodOrbitCloses params r k) →
      (∃ k, LucasPeriodOrbitCloses params s k) →
      (∃ k, LucasPeriodOrbitCloses params (r * s) k) ∧
        lucasPeriodOrbitLcm params (r * s) =
          Nat.lcm (lucasPeriodOrbitLcm params r) (lucasPeriodOrbitLcm params s)) ∧
    ∀ p i : ℕ, p.Prime → 1 ≤ i → (∃ k, LucasPeriodOrbitCloses params p k) →
      (∃ k, LucasPeriodOrbitCloses params (p ^ i) k) ∧
        lucasPeriodOrbitLcm params (p ^ i) = Nat.lcm (p ^ i) (lucasPeriodOrbitLcm params p)

/-- Theorem 2.9: `L(2)` and `L(3)`. (i) for `a`, `b` odd, `L(2)` exists iff `gcd(b, 3) = 1`;
(ii) for `a` even, `L(2)` exists iff `b` is odd; (iii) `L(3) = 3` or `6 ∣ L(3)` when it exists;
(iv) `L(3) = 3` iff `a ≡ b ≡ -1 (mod 3)`; (v) `6 ∣ L(3)` iff `gcd(b, 6) = 1` and not both
`a ≡ -1 (mod 3)`, `b ≡ -1 (mod 6)`; (vi) `a` even, `b` odd give `L(2) = 2`; (vii)
`a ≡ ±1`, `b ≡ 1 (mod 6)` give `L(2) = L(3) = 24`; (viii) `a ≡ 1`, `b ≡ -1` or `a ≡ 3`,
`b ≡ 1 (mod 6)` give `L(2) = L(3) = 6`; (ix) `a ≡ b ≡ -1 (mod 6)` give `L(2) = 6`, `L(3) = 3`;
(x) `a ≡ 0 (mod 6)` gives `L(3) = 6` for `b ≡ 1` and `L(3) = 12` for `b ≡ -1 (mod 6)`; (xi)
`a ≡ 3`, `b ≡ -1 (mod 6)` give `L(2) = L(3) = 12`; (xii) `a ≡ ±2`, `b ≡ 1 (mod 6)` give
`L(3) = 24`, and `a ≡ -2`, `b ≡ -1 (mod 6)` give `L(3) = 6`; (xiii) if `rad(n) ∣ 6` and `L(n)`
exists then `rad(L(n)) ∣ 6`. "`L(m)` exists" means `ω(m)` exists. The second half of (xii) is
false as printed for `a ≡ 2 (mod 6)` and is restricted to `a ≡ -2 (mod 6)`: for
`(a, b) = (2, 5)` (nondegenerate) one has `π_U(3) = 3`, so `L(3) = 3`, in line with (iv).

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.9
(`integers-2024-A36-thm-2-9`). -/
public theorem_wanted lucasPeriodOrbitLcm_two_three (params : LucasSequenceParams) :
    (Odd params.p → Odd params.q →
      ((∃ k, LucasPeriodOrbitCloses params 2 k) ↔ IsCoprime params.q 3)) ∧
    (Even params.p → ((∃ k, LucasPeriodOrbitCloses params 2 k) ↔ Odd params.q)) ∧
    ((∃ k, LucasPeriodOrbitCloses params 3 k) →
      lucasPeriodOrbitLcm params 3 = 3 ∨ 6 ∣ lucasPeriodOrbitLcm params 3) ∧
    (((∃ k, LucasPeriodOrbitCloses params 3 k) ∧ lucasPeriodOrbitLcm params 3 = 3) ↔
      params.p ≡ -1 [ZMOD 3] ∧ -params.q ≡ -1 [ZMOD 3]) ∧
    (((∃ k, LucasPeriodOrbitCloses params 3 k) ∧ 6 ∣ lucasPeriodOrbitLcm params 3) ↔
      IsCoprime params.q 6 ∧ ¬ (params.p ≡ -1 [ZMOD 3] ∧ -params.q ≡ -1 [ZMOD 6])) ∧
    (Even params.p → Odd params.q →
      (∃ k, LucasPeriodOrbitCloses params 2 k) ∧ lucasPeriodOrbitLcm params 2 = 2) ∧
    ((params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) → -params.q ≡ 1 [ZMOD 6] →
      (∃ k, LucasPeriodOrbitCloses params 2 k) ∧ (∃ k, LucasPeriodOrbitCloses params 3 k) ∧
      lucasPeriodOrbitLcm params 2 = 24 ∧ lucasPeriodOrbitLcm params 3 = 24) ∧
    ((params.p ≡ 1 [ZMOD 6] ∧ -params.q ≡ -1 [ZMOD 6] ∨
        params.p ≡ 3 [ZMOD 6] ∧ -params.q ≡ 1 [ZMOD 6]) →
      (∃ k, LucasPeriodOrbitCloses params 2 k) ∧ (∃ k, LucasPeriodOrbitCloses params 3 k) ∧
      lucasPeriodOrbitLcm params 2 = 6 ∧ lucasPeriodOrbitLcm params 3 = 6) ∧
    (params.p ≡ -1 [ZMOD 6] → -params.q ≡ -1 [ZMOD 6] →
      (∃ k, LucasPeriodOrbitCloses params 2 k) ∧ (∃ k, LucasPeriodOrbitCloses params 3 k) ∧
      lucasPeriodOrbitLcm params 2 = 6 ∧ lucasPeriodOrbitLcm params 3 = 3) ∧
    (params.p ≡ 0 [ZMOD 6] → -params.q ≡ 1 [ZMOD 6] →
      (∃ k, LucasPeriodOrbitCloses params 3 k) ∧ lucasPeriodOrbitLcm params 3 = 6) ∧
    (params.p ≡ 0 [ZMOD 6] → -params.q ≡ -1 [ZMOD 6] →
      (∃ k, LucasPeriodOrbitCloses params 3 k) ∧ lucasPeriodOrbitLcm params 3 = 12) ∧
    (params.p ≡ 3 [ZMOD 6] → -params.q ≡ -1 [ZMOD 6] →
      (∃ k, LucasPeriodOrbitCloses params 2 k) ∧ (∃ k, LucasPeriodOrbitCloses params 3 k) ∧
      lucasPeriodOrbitLcm params 2 = 12 ∧ lucasPeriodOrbitLcm params 3 = 12) ∧
    ((params.p ≡ 2 [ZMOD 6] ∨ params.p ≡ -2 [ZMOD 6]) → -params.q ≡ 1 [ZMOD 6] →
      (∃ k, LucasPeriodOrbitCloses params 3 k) ∧ lucasPeriodOrbitLcm params 3 = 24) ∧
    (params.p ≡ -2 [ZMOD 6] → -params.q ≡ -1 [ZMOD 6] →
      (∃ k, LucasPeriodOrbitCloses params 3 k) ∧ lucasPeriodOrbitLcm params 3 = 6) ∧
    ∀ n : ℕ, 0 < n → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ∣ 6) →
      (∃ k, LucasPeriodOrbitCloses params n k) →
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ lucasPeriodOrbitLcm params n → ℓ ∣ 6

/-- Theorem 2.11: for nondegenerate `U(a, b)`, `C(1) = 1`. If `Q(b) ≥ 5` (the least prime factor
of `b`, with `Q(±1) = 1`), then `C(n)` exists for `n ≥ 2` with `P(n) < Q(b)` (`P` the largest
prime factor); if moreover `gcd(C(n), a + b - 1) = 1`, then `A_W(C(n))` is an integer for all
`W(a, b)`, and the same holds when `a + b - 1 ≠ 0`, `Q(a + b - 1) ≥ 5` and
`P(n) < Q(b (a + b - 1))`. If `b = ±1` then `C(n)` exists for all `n`, and for
`(a, b) ∈ {(1, 1), (-1, 1), (3, -1)}` `A_W(C(n))` is an integer for all `n` and all `W(a, b)`.
`P(n) < Q(r)` is "every prime factor of `n` is below every prime factor of `r`"; the claims for
`b = ±1` are stated without `Q(b) ≥ 5`, which they contradict under the convention `Q(±1) = 1`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.11
(`integers-2024-A36-thm-2-11`). -/
public theorem_wanted exists_lucasPeriodSet_multiple (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) :
    IsLeast {x | 1 ∣ x ∧ x ∈ lucasPeriodSet params} 1 ∧
    ((params.q ≠ 1 ∧ params.q ≠ -1 ∧ ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ params.q → 5 ≤ ℓ) →
      (∀ n : ℕ, 2 ≤ n →
        (∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ∣ n → (ℓ' : ℤ) ∣ params.q → ℓ < ℓ') →
        ∃ x, n ∣ x ∧ x ∈ lucasPeriodSet params) ∧
      (∀ n c : ℕ, 0 < n →
        (∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ∣ n → (ℓ' : ℤ) ∣ params.q → ℓ < ℓ') →
        IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c →
        IsCoprime (c : ℤ) (params.p - params.q - 1) → lucasAllAveragesIntegral params c) ∧
      (params.p - params.q - 1 ≠ 1 → params.p - params.q - 1 ≠ -1 →
        params.p - params.q - 1 ≠ 0 →
        (∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ params.p - params.q - 1 → 5 ≤ ℓ) →
        ∀ n c : ℕ, 0 < n →
          (∀ ℓ ℓ' : ℕ, ℓ.Prime → ℓ'.Prime → ℓ ∣ n →
            (ℓ' : ℤ) ∣ params.q * (params.p - params.q - 1) → ℓ < ℓ') →
          IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c →
          lucasAllAveragesIntegral params c)) ∧
    ((params.q = 1 ∨ params.q = -1) → ∀ n : ℕ, 0 < n → ∃ x, n ∣ x ∧ x ∈ lucasPeriodSet params) ∧
    ((params.p = 1 ∧ params.q = -1 ∨ params.p = -1 ∧ params.q = -1 ∨
        params.p = 3 ∧ params.q = 1) →
      ∀ n c : ℕ, 0 < n → IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c →
        lucasAllAveragesIntegral params c)

/-- Corollary 2.5: for `U(a, 1)` (`D = a ^ 2 + 4`) and `q > 1` with `Q(q) ≥ 5` and
`rad(q) ∣ D`, `n ∈ S'(U)` and `A_W(n)` is an integer for all `W(a, 1)` when (`i, j ≥ 0`):
(i) `a ≡ ±1 (mod 6)`, `n = 2 ^ (i + 3) 3 ^ (j + 1) q`; (ii) `a ≡ 3 (mod 6)`,
`n = 2 ^ (i + 1) 3 ^ (j + 1)` or `n = 2 ^ (i + 2) 3 ^ (j + 1) q`; (iii) `a ≡ ±2 (mod 12)`,
`n = 2 ^ (i + 2) q` or `n = 2 ^ (i + 3) 3 ^ (j + 1) q`; (iv) `a ≡ ±6 (mod 12)`,
`n = 2 ^ (i + 2) 3 ^ j q`. `q ≠ 1` is the convention `Q(1) = 1`; the paper's `n > 1` and
`rad(n) ∣ 6 D` follow from the displayed forms.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.5
(`integers-2024-A36-cor-2-5`). -/
public theorem_wanted mem_lucasAverageSet_of_q_eq_neg_one (params : LucasSequenceParams)
    (hq : params.q = -1) (t : ℕ) (ht1 : t ≠ 1) (ht5 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ t → 5 ≤ ℓ)
    (htD : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ t → (ℓ : ℤ) ∣ params.p ^ 2 + 4) (i j : ℕ) :
    ((params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) →
      2 ^ (i + 3) * 3 ^ (j + 1) * t ∈ lucasAverageSet params ∧
      lucasAllAveragesIntegral params (2 ^ (i + 3) * 3 ^ (j + 1) * t)) ∧
    (params.p ≡ 3 [ZMOD 6] →
      2 ^ (i + 1) * 3 ^ (j + 1) ∈ lucasAverageSet params ∧
      lucasAllAveragesIntegral params (2 ^ (i + 1) * 3 ^ (j + 1)) ∧
      2 ^ (i + 2) * 3 ^ (j + 1) * t ∈ lucasAverageSet params ∧
      lucasAllAveragesIntegral params (2 ^ (i + 2) * 3 ^ (j + 1) * t)) ∧
    ((params.p ≡ 2 [ZMOD 12] ∨ params.p ≡ -2 [ZMOD 12]) →
      2 ^ (i + 2) * t ∈ lucasAverageSet params ∧
      lucasAllAveragesIntegral params (2 ^ (i + 2) * t) ∧
      2 ^ (i + 3) * 3 ^ (j + 1) * t ∈ lucasAverageSet params ∧
      lucasAllAveragesIntegral params (2 ^ (i + 3) * 3 ^ (j + 1) * t)) ∧
    (params.p ≡ 6 [ZMOD 12] →
      2 ^ (i + 2) * 3 ^ j * t ∈ lucasAverageSet params ∧
      lucasAllAveragesIntegral params (2 ^ (i + 2) * 3 ^ j * t))

/-- Corollary 2.6: for nondegenerate `U(a, -1)` (`D = (a - 2) (a + 2)`), `n ∈ S'(U)` and
`A_W(n)` is an integer for all `W(a, -1)` when (`i, j ≥ 0`): (i) `n = q₁ > 1` odd with
`rad(q₁) ∣ a - 2`; (ii) `a ≡ ±1 (mod 6)`, `n = 2 ^ (i + 1) 3 ^ (j + 1) q₂`; (iii)
`a ≡ 3 (mod 6)`, `n = 2 ^ (i + 2) 3 ^ (j + 1) q₂`; (iv) `a ≡ 0 (mod 4)`, `n = 2 ^ (i + 2) q₃`;
(v) `a ≡ 0 (mod 12)`, `n = 2 ^ (i + 2) 3 ^ (j + 1) q₂`; here `q₂ ≠ 1` is odd with `Q(q₂) ≥ 5`,
`rad(q₂) ∣ D`, and `q₃` is odd with `rad(q₃) ∣ D`. The paper's "for all recurrences `W(a, 1)`"
is read as `W(a, -1)`, the recurrences of `U(a, -1)` (Theorem 2.5); as printed it is false:
for `a = 5`, `n = q₁ = 3` and `W = U(5, 1)`, `W 1 + W 2 + W 3 = 1 + 5 + 26 = 32`, which `3`
does not divide. The condition `a ≠ 0, ±1, ±2` of (i) is nondegeneracy.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.6
(`integers-2024-A36-cor-2-6`). -/
public theorem_wanted mem_lucasAverageSet_of_q_eq_one (params : LucasSequenceParams)
    (hq : params.q = 1) (hnd : IsNondegenerateLucasPair params.p params.q) :
    (∀ t : ℕ, 1 < t → Odd t → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ t → (ℓ : ℤ) ∣ params.p - 2) →
      t ∈ lucasAverageSet params ∧ lucasAllAveragesIntegral params t) ∧
    (∀ t : ℕ, Odd t → t ≠ 1 → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ t → 5 ≤ ℓ) →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ t → (ℓ : ℤ) ∣ params.p ^ 2 - 4) → ∀ i j : ℕ,
      ((params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) →
        2 ^ (i + 1) * 3 ^ (j + 1) * t ∈ lucasAverageSet params ∧
        lucasAllAveragesIntegral params (2 ^ (i + 1) * 3 ^ (j + 1) * t)) ∧
      (params.p ≡ 3 [ZMOD 6] →
        2 ^ (i + 2) * 3 ^ (j + 1) * t ∈ lucasAverageSet params ∧
        lucasAllAveragesIntegral params (2 ^ (i + 2) * 3 ^ (j + 1) * t)) ∧
      (params.p ≡ 0 [ZMOD 12] →
        2 ^ (i + 2) * 3 ^ (j + 1) * t ∈ lucasAverageSet params ∧
        lucasAllAveragesIntegral params (2 ^ (i + 2) * 3 ^ (j + 1) * t))) ∧
    ∀ t : ℕ, Odd t → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ t → (ℓ : ℤ) ∣ params.p ^ 2 - 4) → ∀ i : ℕ,
      params.p ≡ 0 [ZMOD 4] →
      2 ^ (i + 2) * t ∈ lucasAverageSet params ∧
      lucasAllAveragesIntegral params (2 ^ (i + 2) * t)

/-- Theorem 2.24: for nondegenerate `U(a, 1)`: (i) `C(n) = L(n)` exists for all `n ≥ 1`;
`C(n)` is even and `L(2) ∣ C(n)` for `n > 1`; `π_U(n)` is even for `n ≥ 3`, and `π_U(2)` is even
if `a` is even. (ii) For odd `a`, `C'(n) = C(n)` with `A_W(C(n))` integral for all `W(a, 1)`;
`L(2) = 24` if `a ≡ ±1 (mod 6)` and `L(2) = 6` if `a ≡ 3 (mod 6)`. (iii) For `a ≡ 2 (mod 4)`,
`C'(n) = C(n)` with `A_W(C(n))` integral unless `C(n) ≡ 2 (mod 4)`, in which case
`C'(n) = 2 C(n)` with `A_W(2 C(n))` integral; `L(2) = 2`. (iv) For `a ≡ 0 (mod 4)` and `n ≥ 2`,
`n ∉ S'(U)` and `C'(n)` does not exist; `B_U(n) ≢ 0 (mod n)` for even `n`; `A_U(n)` is an
integer only for odd `n`. The case split in (iii) is printed on `n` ("`n` odd or `4 ∣ n`" versus
"`n ≡ 2 (mod 4)`") and is false in that form: for `a = 6`, `n = 3` one has `C(3) = 6` but
`C'(3) = 12`, and for `a = 2`, `n = 6`, `C(6) = 24 = C'(6)`. The paper's proof ((5.6), (5.7))
splits on `2 ^ k ∥ C(n)`, which is the reading formalized.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.24
(`integers-2024-A36-thm-2-24`). -/
public theorem_wanted lucasPeriodSet_of_q_eq_neg_one (params : LucasSequenceParams)
    (hq : params.q = -1) (hnd : IsNondegenerateLucasPair params.p params.q) :
    (∀ n : ℕ, 0 < n → (∃ k, LucasPeriodOrbitCloses params n k) ∧
      IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} (lucasPeriodOrbitLcm params n)) ∧
    (∀ n : ℕ, 1 < n → Even (lucasPeriodOrbitLcm params n) ∧
      lucasPeriodOrbitLcm params 2 ∣ lucasPeriodOrbitLcm params n) ∧
    (∀ n : ℕ, 3 ≤ n → Even (lucasUPeriod params n)) ∧
    (Even params.p → Even (lucasUPeriod params 2)) ∧
    (Odd params.p →
      (∀ n : ℕ, 0 < n →
        IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} (lucasPeriodOrbitLcm params n) ∧
        lucasAllAveragesIntegral params (lucasPeriodOrbitLcm params n)) ∧
      ((params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) → lucasPeriodOrbitLcm params 2 = 24) ∧
      (params.p ≡ 3 [ZMOD 6] → lucasPeriodOrbitLcm params 2 = 6)) ∧
    (params.p ≡ 2 [ZMOD 4] →
      (∀ n : ℕ, 0 < n →
        (lucasPeriodOrbitLcm params n % 4 ≠ 2 →
          IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} (lucasPeriodOrbitLcm params n) ∧
          lucasAllAveragesIntegral params (lucasPeriodOrbitLcm params n)) ∧
        (lucasPeriodOrbitLcm params n % 4 = 2 →
          IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} (2 * lucasPeriodOrbitLcm params n) ∧
          lucasAllAveragesIntegral params (2 * lucasPeriodOrbitLcm params n))) ∧
      lucasPeriodOrbitLcm params 2 = 2) ∧
    (params.p ≡ 0 [ZMOD 4] →
      (∀ n : ℕ, 2 ≤ n → n ∉ lucasAverageSet params ∧ ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params) ∧
      (∀ n : ℕ, 0 < n → Even n → ¬ (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
      ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i → Odd n)

/-- Theorem 2.25: for nondegenerate `U(a, -1)` (`D = (a - 2) (a + 2)`): (i) `C(n)` exists for all
`n ≥ 1`, and for `n > 1`, `C(n) > 1` and `C(n)` shares a prime with `6 D`; (ii) for odd `n₁` with
`rad(n₁) ∣ a - 2`, `C(n₁) = n₁ = C'(n₁)` and `A_W(n₁)` is an integer for all `W(a, -1)`; if
`C(n)` is odd then `n` is odd, `C'(n) = C(n)` and `A_W(C(n))` is integral; (iii) for odd `a`,
`C'(n) = C(n)` and `A_W(C(n))` is integral; (iv) for `a ≡ 0 (mod 4)`, `C'(n) = 2 C(n)` with
`A_W(2 C(n))` integral if `C(n) ≡ 2 (mod 4)`, and `C'(n) = C(n)` with `A_W(C(n))` integral if
`4 ∣ C(n)`; (v) for `a ≡ 2 (mod 4)`, `C'(n)` does not exist when `C(n)` is even, in particular
when `n` is even or `gcd(n, a + 2) > 1`. The paper's decomposition `n = 2 ^ k n₁ n₂` serves only
to name `n₁`; `a ≠ 0, ±1, ±2` is nondegeneracy.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.25
(`integers-2024-A36-thm-2-25`). -/
public theorem_wanted lucasPeriodSet_of_q_eq_one (params : LucasSequenceParams)
    (hq : params.q = 1) (hnd : IsNondegenerateLucasPair params.p params.q) :
    (∀ n : ℕ, 0 < n → ∃ x, n ∣ x ∧ x ∈ lucasPeriodSet params) ∧
    (∀ n c : ℕ, 1 < n → IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c →
      1 < c ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : ℤ) ∣ 6 * (params.p ^ 2 - 4) ∧ ℓ ∣ c) ∧
    (∀ n₁ : ℕ, Odd n₁ → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n₁ → (ℓ : ℤ) ∣ params.p - 2) →
      IsLeast {x | n₁ ∣ x ∧ x ∈ lucasPeriodSet params} n₁ ∧
      IsLeast {x | n₁ ∣ x ∧ x ∈ lucasAverageSet params} n₁ ∧
      lucasAllAveragesIntegral params n₁) ∧
    (∀ n c : ℕ, 0 < n → IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c → Odd c →
      Odd n ∧ IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} c ∧
      lucasAllAveragesIntegral params c) ∧
    (Odd params.p → ∀ n c : ℕ, 0 < n → IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c →
      IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} c ∧ lucasAllAveragesIntegral params c) ∧
    (params.p ≡ 0 [ZMOD 4] → ∀ n c : ℕ, 0 < n →
      IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c →
      (c % 4 = 2 → IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} (2 * c) ∧
        lucasAllAveragesIntegral params (2 * c)) ∧
      (4 ∣ c → IsLeast {x | n ∣ x ∧ x ∈ lucasAverageSet params} c ∧
        lucasAllAveragesIntegral params c)) ∧
    (params.p ≡ 2 [ZMOD 4] → ∀ n c : ℕ, 0 < n →
      IsLeast {x | n ∣ x ∧ x ∈ lucasPeriodSet params} c → Even c →
      ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params) ∧
    (params.p ≡ 2 [ZMOD 4] → ∀ n : ℕ, 0 < n → (Even n ∨ 1 < Int.gcd n (params.p + 2)) →
      ¬ ∃ x, n ∣ x ∧ x ∈ lucasAverageSet params)

/-- Theorem 2.26: for nondegenerate `U(a, -a + 1)` (roots `a - 1` and `1`,
`D = (a - 2) ^ 2`): (i) `E_U(n) = 1` when `gcd(n, b) = 1`; (ii) if `n ∣ b` and `m ∈ S'(U)` then
`A_W(m n)` is an integer for all `W(a, -a + 1)`; (iii) `S(U) = T(U)`; (iv) for odd `a`,
`S'(U) = S(U) = T(U)`, `A_W(n)` is integral for `n ∈ S(U)` and for `n ∣ b`, and for `a = 3`,
`D = 1` and `S(U) = {1}`; (v) for even `a`, `n ∈ S'(U)` iff `n` is odd and `n ∈ S(U)`, `A_W(n)`
is integral for odd `n ∈ S(U)`, and if `a = 2 + 2 ^ k` with `k ≥ 1` then `n ∉ S'(U)` for
`n > 1`. In the repository convention `a = -b + 1` is `P = Q + 1`; `a ≠ 0, 1, 2` follows from
nondegeneracy. The extracted "`a = 2 + 2k`" is read as `a = 2 + 2 ^ k` (the exponent is set as a
superscript in the paper); the linear reading is false: for `a = 8` (`b = -7`) one has
`π_U(3) = 3` and `3 ∣ B_U(3) = 1 + 8 + 57 = 66`, so `3 ∈ S'(U)`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.26
(`integers-2024-A36-thm-2-26`). -/
public theorem_wanted lucasAverageSet_of_p_eq_q_add_one (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p = params.q + 1) :
    (∀ n : ℕ, 0 < n → IsCoprime (n : ℤ) params.q →
      lucasUPeriod params n = lucasURestrictedPeriod params n) ∧
    (∀ m n : ℕ, 0 < n → (n : ℤ) ∣ params.q → m ∈ lucasAverageSet params →
      lucasAllAveragesIntegral params (m * n)) ∧
    lucasPeriodSet params = lucasIndexDivisibleSet params ∧
    (Odd params.p →
      (∀ n, n ∈ lucasAverageSet params ↔ n ∈ lucasPeriodSet params) ∧
      (∀ n, n ∈ lucasPeriodSet params → lucasAllAveragesIntegral params n) ∧
      (params.p = 3 → params.p ^ 2 - 4 * params.q = 1 ∧ ∀ n, n ∈ lucasPeriodSet params ↔ n = 1) ∧
      ∀ n : ℕ, 0 < n → (n : ℤ) ∣ params.q → lucasAllAveragesIntegral params n) ∧
    (Even params.p →
      (∀ n, n ∈ lucasAverageSet params ↔ Odd n ∧ n ∈ lucasPeriodSet params) ∧
      (∀ k : ℕ, 1 ≤ k → params.p = 2 + 2 ^ k → ∀ n, 1 < n → n ∉ lucasAverageSet params) ∧
      ∀ n, Odd n → n ∈ lucasPeriodSet params → lucasAllAveragesIntegral params n)

/-- Theorem 2.27: for nondegenerate `U(b - 1, b)` (roots `b` and `-1`, `D = (b + 1) ^ 2`):
`π_U(n)` is even for `n > 1` with `gcd(n, b) = 1`; (i) if `b` and `n` are even and `n ∣ b`, then
`A_W(n)` is an integer for all `W(b - 1, b)`; (ii) if `a` is even, `n > 1` and `n ∈ S(U)`, then
`A_U(n)` is not an integer, so `S'(U) = {1}`, and `S(U) = {1}` if `a` is odd; (iii) if `a` is odd,
then `b` is even, and for even `m ∣ b` and `t ∈ T(U)`, `t` is odd and `A_W(m t)` is an integer
for all `W(b - 1, b)`. In the repository convention `a = b - 1` is `P = -Q - 1`;
`a ≠ 0, -1, -2` follows from nondegeneracy.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.27
(`integers-2024-A36-thm-2-27`). -/
public theorem_wanted lucasAverageSet_of_p_eq_neg_q_sub_one (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hp : params.p = -params.q - 1) :
    (∀ n : ℕ, 1 < n → IsCoprime (n : ℤ) params.q → Even (lucasUPeriod params n)) ∧
    (Even params.q → ∀ n : ℕ, (n : ℤ) ∣ params.q → Even n → lucasAllAveragesIntegral params n) ∧
    (Even params.p → ∀ n : ℕ, 1 < n → n ∈ lucasPeriodSet params →
      ¬ (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i) ∧
    (Even params.p → lucasAverageSet params = {1}) ∧
    (Odd params.p → lucasPeriodSet params = {1}) ∧
    (Odd params.p → Even params.q ∧ ∀ m t : ℕ, Even m → (m : ℤ) ∣ params.q →
      t ∈ lucasIndexDivisibleSet params → Odd t ∧ lucasAllAveragesIntegral params (m * t))

/-- Theorem 4.1 (Smyth): for nondegenerate `U(a, b)` with `gcd(a, b) = 1`, let the admissible
`q₀` be `1`, together with `6` if `a ≡ 3`, `b ≡ ±1 (mod 6)`, and `12` if `a ≡ ±1`,
`b ≡ 1 (mod 6)`. Then each admissible `q₀ ∈ T(U)`; `n ∈ T(U)` iff `n = q₀ q₁ ⋯ q_r` for an
admissible `q₀` and primes `q_i ∣ D U_(q₀ ⋯ q_(i-1))` (repetitions allowed); every prefix
product `q₀ ⋯ q_i` of such a chain lies in `T(U)`; and if `D = 1` then `T(U) = {1}`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 4.1
(`integers-2024-A36-thm-4-1`). -/
public theorem_wanted mem_lucasIndexDivisibleSet_iff_chain (params : LucasSequenceParams)
    (hnd : IsNondegenerateLucasPair params.p params.q) (hcop : IsCoprime params.p params.q) :
    let Q₀ : ℕ → Prop := fun q₀ => q₀ = 1 ∨
      (params.p ≡ 3 [ZMOD 6] ∧ (-params.q ≡ 1 [ZMOD 6] ∨ -params.q ≡ -1 [ZMOD 6]) ∧ q₀ = 6) ∨
      ((params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) ∧ -params.q ≡ 1 [ZMOD 6] ∧ q₀ = 12)
    let Chain : ℕ → List ℕ → Prop := fun q₀ qs => ∀ i (hi : i < qs.length),
      qs[i].Prime ∧
        (qs[i] : ℤ) ∣ (params.p ^ 2 - 4 * params.q) * lucasU params (q₀ * (qs.take i).prod)
    (∀ q₀, Q₀ q₀ → q₀ ∈ lucasIndexDivisibleSet params) ∧
    (∀ n, n ∈ lucasIndexDivisibleSet params ↔ ∃ q₀ qs, Q₀ q₀ ∧ Chain q₀ qs ∧ n = q₀ * qs.prod) ∧
    (∀ q₀ qs, Q₀ q₀ → Chain q₀ qs → ∀ i ≤ qs.length,
      q₀ * (qs.take i).prod ∈ lucasIndexDivisibleSet params) ∧
    (params.p ^ 2 - 4 * params.q = 1 → ∀ n, n ∈ lucasIndexDivisibleSet params ↔ n = 1)

/-- Theorem 4.3, the parts on `E_U(p)` and on `s₀`: for nondegenerate `U(a, b)` with `b = ±1`, or
`b` odd and `a = b - 1`, `E_U(p) = π_U(p) / ρ_U(p)` divides `4` if `b = 1` and `2` otherwise, for
primes `p ∤ b` (where `E_U(p)` is defined). Let the admissible `s₀` be `1`, together with `6` if
`a ≡ 3 (mod 6)`, `b = 1` or `a ≡ ±1 (mod 6)`, `b = -1`; `24` if `a ≡ ±1 (mod 6)`, `b = 1`; `12`
if `a ≡ 3 (mod 6)`, `b = -1`; `2` if `b` is odd and `a = b - 1`. Then each admissible
`s₀ ∈ S(U)`.

The characterization of `S(U)` by chains `n₀ = s₀`, `n_i = n_(i-1) s_i 2 ^ ε(s_i)` (primes
`s_i ∣ D U_(n_(i-1))`, `ε(s_i) = max(ν₂(π_U(s_i)) - ν₂(n_(i-1)), 0)`) is false as printed in both
directions and is omitted. For `(a, b) = (-10, -1)` only `s₀ = 1` is admissible and
`π_U(2) = 2`, so `2 ∈ S(U)`, but the only chain that could end at `2` has `s₁ = 2`, and then
`ε(2) = ν₂(π_U(2)) = 1` gives `n₁ = 4`. For `(a, b) = (-11, -1)` (`D = 117`) the chain `s₀ = 1`,
`s₁ = 13`,
`s₂ = 53 ∣ U 13 = 2862615066961` gives `ε(53) = ν₂(26) = 1` and `n₂ = 1378`, while
`π_U(1378) = 78 ∤ 1378`.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 4.3
(`integers-2024-A36-thm-4-3`). -/
public theorem_wanted lucasUPeriod_quotient_dvd_and_seed_mem_lucasPeriodSet
    (params : LucasSequenceParams) (hnd : IsNondegenerateLucasPair params.p params.q)
    (hcase : params.q = -1 ∨ params.q = 1 ∨ (Odd params.q ∧ params.p = -params.q - 1)) :
    (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ params.q →
      lucasURestrictedPeriod params p ∣ lucasUPeriod params p ∧
      (params.q = -1 → lucasUPeriod params p / lucasURestrictedPeriod params p ∣ 4) ∧
      (params.q ≠ -1 → lucasUPeriod params p / lucasURestrictedPeriod params p ∣ 2)) ∧
    (∀ s₀ : ℕ, (s₀ = 1 ∨
        ((params.p ≡ 3 [ZMOD 6] ∧ params.q = -1 ∨
            (params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) ∧ params.q = 1) ∧ s₀ = 6) ∨
        ((params.p ≡ 1 [ZMOD 6] ∨ params.p ≡ -1 [ZMOD 6]) ∧ params.q = -1 ∧ s₀ = 24) ∨
        (params.p ≡ 3 [ZMOD 6] ∧ params.q = 1 ∧ s₀ = 12) ∨
        (Odd params.q ∧ params.p = -params.q - 1 ∧ s₀ = 2)) →
      s₀ ∈ lucasPeriodSet params)

end

end MetaMathlibExt
