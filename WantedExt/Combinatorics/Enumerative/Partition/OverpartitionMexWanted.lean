/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# A minimal excludant over overpartitions (statements)

Statement-only targets from Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over
Overpartitions*, Journal of Integer Sequences 27 (2024), Article 24.7.1. `σ_r mex̄(n)` sums, over
the repo's `Nat.Overpartition n`,
the least positive integer occurring fewer than `r` times among the non-overlined parts;
`σmex̄ = σ_1 mex̄`. q-series are over ℂ with `‖q‖ < 1` and the repo `qPochhammerInfRaw`.
The quoted modular-form results (Theorems 14, 15, 18 and Proposition 17) are not stated.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The number `p̄(n)` of overpartitions of `n` (`p̄(3) = 8`).

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Section 1. -/
public noncomputable def overpartitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Overpartition n)


open Filter
open QPochhammer

/--
`nonOverlinedCount O a` is the multiplicity of `a` among the non-overlined
parts of `O`: it subtracts one exactly when the size `a` is selected in
`O.overlines`.  This maps the paper's “first occurrence may be overlined”
convention to the repository representation, where overlining is stored once
per distinct size.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `mex̄_r`.
-/
public def nonOverlinedCount {n : ℕ} (O : Nat.Overpartition n) (a : ℕ) : ℕ :=
  O.toPartition.parts.count a - if a ∈ O.overlines then 1 else 0

/--
`leastGapOverpartition r O` is the least positive size occurring fewer than
`r` times among the non-overlined parts of `O`, formalizing `mex̄_r(O)`.
For positive `r`, existence uses `n + 1`, which cannot occur in a partition
of `n`.  The paper only uses positive `r`; the otherwise undefined case
`r = 0` is totalized to `0`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `mex̄_r`.
-/
public def leastGapOverpartition (r : ℕ) {n : ℕ} (O : Nat.Overpartition n) : ℕ :=
  if hr : r = 0 then 0
  else
    Nat.find (show ∃ k : ℕ,
        1 ≤ k ∧ nonOverlinedCount O k < r from by
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hnotmem : n + 1 ∉ O.toPartition.parts := by
        intro hmem
        have hle : n + 1 ≤ O.toPartition.parts.sum :=
          Multiset.le_sum_of_mem hmem
        rw [O.toPartition.parts_sum] at hle
        omega
      have hcount : O.toPartition.parts.count (n + 1) = 0 :=
        Multiset.count_eq_zero.mpr hnotmem
      exact ⟨n + 1, Nat.zero_lt_succ n, by
        simp [nonOverlinedCount, hcount, hrpos]⟩)

/--
`D3 n` counts three-colored distinct-part partitions of `n` as triples
`(A, B, C)` of subsets of `{1, …, n}`, one set per color, whose three sums
add to `n`.  Distinctness is enforced within each color by `Finset`; the
same size may occur in different colors, exactly as in the product
`(-q;q)_∞^3`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public def D3 (n : ℕ) : ℕ :=
  ((((Finset.Icc 1 n).powerset.product (Finset.Icc 1 n).powerset).product
    (Finset.Icc 1 n).powerset).filter fun p =>
      p.1.1.sum id + p.1.2.sum id + p.2.sum id = n).card

/-- `σ_r mex̄(n) = Σ_{π ∈ P̄(n)} mex̄_r(π)`; `σmex̄(n)` is `r = 1`. For positive `r`, the
empty overpartition gives `σ_r mex̄(0) = 1`; for the totalized `r = 0`, every value is `0`.
Values (by direct enumeration): `σmex̄(0..4) = 1, 3, 6, 13, 24` (the paper's
`σmex̄(3) = 13`), `σ_2 mex̄(2) = 5`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definitions of `σmex̄` and `σ_r mex̄`. -/
public noncomputable def sigmaMexOverpartition (r n : ℕ) : ℕ :=
  ∑ O : Nat.Overpartition n, leastGapOverpartition r O

/-- There is exactly one overpartition of `0`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Section 1 (`p̄(0) = 1`). -/
public theorem overpartitionCount_zero : overpartitionCount 0 = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨Nat.Overpartition.ofPartition default, fun _ =>
    Nat.Overpartition.eq_of_zero _ _⟩

/--
The empty triple of colored distinct-part sets is the unique object counted by
`D_3(0)`, so the finite-set encoding `D3 0` equals `1`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_zero : D3 0 = 1 := by
  decide

/--
A partition of `1` into three-colored distinct parts chooses one of three
colors, so the finite-set encoding `D3 1` equals `3`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_one : D3 1 = 3 := by
  decide

/--
The coefficient of `q^2` in `(-q;q)_∞^3` is `6`, represented by the six
triples of colored distinct-part sets in the finite-set encoding `D3 2`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_two : D3 2 = 6 := by
  decide

/--
For every positive `n`, the sum `σmex̄(n)`, encoded as
`sigmaMexOverpartition 1 n`, equals the number `D_3(n)` of three-colored
distinct-part partitions, encoded as `D3 n`.  This is a direct equality with
no deviation from the theorem.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 2.
-/
public theorem_wanted sigmaMexOverpartition_eq_D3 (n : ℕ) (hn : 0 < n) :
    sigmaMexOverpartition 1 n = D3 n

/--
As `n → ∞`, `σmex̄(n)` is asymptotic to
`exp(π√n) / (8 n^(3/4))`.  The limit is encoded by
`Asymptotics.IsEquivalent atTop`, with natural values coerced to reals;
there is no mathematical deviation.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 3.
-/
public theorem_wanted sigmaMexOverpartition_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (sigmaMexOverpartition 1 n : ℝ))
      (fun n => Real.exp (Real.pi * Real.sqrt n) /
        (8 * (n : ℝ) ^ ((3 : ℝ) / 4)))

/--
For positive `n`, `σmex̄(n)` is odd exactly when `n = T_j` for some
`j : ℕ`, and is even otherwise.  The two implications encode the
triangular and non-triangular cases without requiring a classical decision
procedure for the unbounded existential; `j * (j + 1) / 2` (the triangular number `T_j`) encodes
`j(j+1)/2`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 4.
-/
public theorem_wanted sigmaMexOverpartition_parity (n : ℕ) (hn : 0 < n) :
    ((∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 1) ∧
    ((¬∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 0)

/--
For positive `r` and complex `q` with `‖q‖ < 1`, the generating series
of `σ_r mex̄(n)` equals
`(-q;q)_∞ (q^(2r);q^(2r))_∞ / ((q;q)_∞ (q^r;q^(2r))_∞)`.
Each infinite product is represented by `qPochhammerInfRaw`, and the left
side by a complex `tsum`; these are the requested analytic encodings.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 6.
-/
public theorem_wanted sigmaMexOverpartition_generating_function
    (r : ℕ) (hr : 0 < r) (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (sigmaMexOverpartition r n : ℂ) * q ^ n) =
      qPochhammerInfRaw (-q) q * qPochhammerInfRaw (q ^ (2 * r)) (q ^ (2 * r)) /
        (qPochhammerInfRaw q q *
          qPochhammerInfRaw (q ^ r) (q ^ (2 * r)))

/--
For every positive `r`, `σ_r mex̄(n)` is asymptotic to
`exp(π√n) / (8 √r n^(3/4))` as `n → ∞`.  This uses the published
`√r` denominator (also supported by the requester's numerical check), not
the `r` denominator printed in arXiv v1; the limit is formalized with
`Asymptotics.IsEquivalent atTop`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 7.
-/
public theorem_wanted sigmaMexOverpartition_r_asymptotic (r : ℕ) (hr : 0 < r) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (sigmaMexOverpartition r n : ℝ))
      (fun n => Real.exp (Real.pi * Real.sqrt n) /
        (8 * Real.sqrt r * (n : ℝ) ^ ((3 : ℝ) / 4)))

/--
When `r = 2^m 3^e` with `m,e ≥ 0` and `k ≥ 1`, the natural density of
`n` for which `σ_r mex̄(n) ≡ 0 (mod 2^k)` is one.  Naturality makes the
nonnegativity of `m,e` implicit; `Finset.range (X+1)` encodes `0 ≤ n ≤ X`,
and `Tendsto ... atTop (nhds 1)` encodes the density limit.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 8.
-/
public theorem_wanted sigmaMexOverpartition_power_density
    (m e k : ℕ) (hk : 1 ≤ k) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter fun n =>
          Nat.ModEq (2 ^ k) (sigmaMexOverpartition (2 ^ m * 3 ^ e) n) 0).card : ℝ) /
          (X : ℝ))
      atTop (nhds 1)

/--
Ingham's quoted Tauberian theorem: `A` is represented by coefficients `a`;
“radius of convergence one” is encoded by summability/identification for
`‖q‖ < 1` and nonsummability for `1 < ‖q‖`; `a` is nonnegative and
weakly increasing; the positive-real asymptotic and every conical complex
big-O bound are stated with `nhdsWithin`; and the conclusion is the stated
coefficient asymptotic.  Boundary convergence at `‖q‖ = 1` is intentionally
left unspecified, as radius one permits either behavior.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 9.
-/
public theorem_wanted ingham_tauberian
    (a : ℕ → ℝ) (A : ℂ → ℂ) (α β C : ℝ)
    (hseries : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n : ℕ => (a n : ℂ) * q ^ n) (A q))
    (hradius : ∀ q : ℂ, 1 < ‖q‖ →
      ¬Summable (fun n : ℕ => (a n : ℂ) * q ^ n))
    (hnonneg : ∀ n : ℕ, 0 ≤ a n)
    (hmono : Monotone a)
    (hC : 0 < C)
    (hreal : Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0))
      (fun t : ℝ => A (Real.exp (-t)))
      (fun t : ℝ => (α * t ^ β * Real.exp (C / t) : ℝ)))
    (hcomplex : ∀ Δ : ℝ, 0 < Δ →
      Asymptotics.IsBigO
        (nhdsWithin 0 {z : ℂ | 0 < z.re ∧ |z.im| ≤ Δ * z.re})
        (fun z : ℂ => A (Complex.exp (-z)))
        (fun z : ℂ => ((‖z‖ ^ β * Real.exp (C / ‖z‖) : ℝ) : ℂ))) :
    Asymptotics.IsEquivalent atTop a
      (fun n : ℕ =>
        α / (2 * Real.sqrt Real.pi) * C ^ ((2 * β + 1) / 4) *
          (n : ℝ) ^ (-(2 * β + 3) / 4) *
          Real.exp (2 * Real.sqrt (C * n)))

/--
For `n ≥ 0` and `r ≥ 1`, summing `p̄(n-rT_k)` over exactly the indices
`k` satisfying `rT_k ≤ n` gives `σ_r mex̄(n)`.  The finite filtered sum
implements the infinite sum with negative arguments omitted; `k ≤ n`
suffices because `r ≥ 1`.  (`n ≥ 0` is automatic for `n : ℕ`.)

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 10.
-/
public theorem_wanted sigmaMexOverpartition_eq_sum_shifted_count
    (n r : ℕ) (hr : 1 ≤ r) :
    (∑ k ∈ (Finset.range (n + 1)).filter
      (fun k => r * (k * (k + 1) / 2) ≤ n),
      overpartitionCount (n - r * (k * (k + 1) / 2))) =
      sigmaMexOverpartition r n

/--
For positive `r` and `k`, the eta-quotient congruence is encoded without
modular-form infrastructure.  The raw factors `f_d(q) = (q^d;q^d)_∞` use
`qPochhammerInfRaw`; an integer sequence `c` supplies the power-series
coefficients; the prefactor is `q^(3r)`; and `Int.ModEq (2^k)` states that
only exponents `24n+3r` carry `σ_r mex̄(n)`.  The denominator exponent is
an integer power, so at `k=1` its value `-1` is represented by `zpow`.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 16.
-/
public theorem_wanted etaQuotient_sigmaMexOverpartition_modEq
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ c : ℕ → ℤ,
      (∀ q : ℂ, ‖q‖ < 1 →
        q ^ (3 * r) *
            qPochhammerInfRaw (q ^ 48) (q ^ 48) *
            qPochhammerInfRaw (q ^ (24 * r)) (q ^ (24 * r)) ^
              ((2 : ℕ) ^ k - 1) /
          (qPochhammerInfRaw (q ^ 24) (q ^ 24) ^ 2 *
            qPochhammerInfRaw (q ^ (48 * r)) (q ^ (48 * r)) ^
              ((2 : ℤ) ^ (k - 1) - 2)) =
          ∑' j : ℕ, (c j : ℂ) * q ^ j) ∧
      ∀ j : ℕ,
        Int.ModEq ((2 : ℤ) ^ k) (c j)
          (if 3 * r ≤ j ∧ 24 ∣ j - 3 * r then
            (sigmaMexOverpartition r ((j - 3 * r) / 24) : ℤ)
          else 0)

end

end MetaMathlibExt
