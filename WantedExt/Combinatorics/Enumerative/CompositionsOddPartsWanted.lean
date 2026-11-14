/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Cycle
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.Combinatorics.Enumerative.CompositionIndexSets
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.NStepFibonacciSequence
public import MathlibExt.NumberTheory.NStepLucasSequence

namespace MetaMathlibExt

@[expose] public section

/-- The partial-fraction (roots-of-unity filter) identity
`u ^ α / (1 - u ^ β) = (1 / β) ∑_{k < β} ζ ^ (-k α) / (1 - ζ ^ k u)`
with `ζ = e ^ (2πi / β)`, for `0 ≤ α < β` and `1 - u ^ β ≠ 0`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 7 (`jis-2024-24.3.6-lem-7`). -/
public theorem_wanted pow_div_one_sub_pow_eq_sum (α β : ℕ) (hα : α < β)
    (u : ℂ) (hu : 1 - u ^ β ≠ 0) :
    u ^ α / (1 - u ^ β)
      = (1 / (β : ℂ)) * ∑ k ∈ Finset.range β,
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ (-((k : ℤ) * (α : ℤ)))
            / (1 - (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ k * u)


/-! ### Compositions with a congruence condition on the number of parts

Following Bowman, a multiset of positive integers is given by its multiplicity function
`μ : ℕ → ℕ` (the paper's `ℕ_[μ]`; a set `A` is `setMultiplicity A`, the paper's indicator
`i(A; ·)`). A composition with parts in `ℕ_[μ]` is a composition in which each part `a` carries
one of `μ a` colors. -/

/-- The multiplicity function (indicator sequence `i(A; n)`) of a set `A ⊆ ℕ`: `1` on `A`,
`0` off `A`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 2 (`jis-2024-24.3.6-thm-3`). -/
public def setMultiplicity (A : Set ℕ) [DecidablePred (· ∈ A)] (a : ℕ) : ℕ :=
  if a ∈ A then 1 else 0

/-- `b(ℕ_[μ], m, q; n)`: the number of (linear) compositions of `n` with parts in the multiset
`ℕ_[μ]` whose number of parts is congruent to `q` modulo `m`; a composition with `k` parts is a
`k`-tuple of positive integers summing to `n`, weighted by its `∏ μ(part)` colorings. The empty
composition of `0` has `0` parts.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 3 (`jis-2024-24.3.6-thm-3`). -/
public def compositionCountMod (μ : ℕ → ℕ) (m q n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % m = q % m),
    ∑ c ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun c => ∀ i, 0 < c i), ∏ i, μ (c i)

/-- The size of the part of a circular composition of `n` that starts right after the removed
edge `s`. The cycle graph `C_n` has vertices `0, …, n - 1` and edges `s = {s, s + 1 mod n}`;
a circular composition is a nonempty set `S` of removed edges, and the part after edge `s`
ends at the next removed edge, so its size is the least `d ∈ [1, n]` with `(s + d) % n ∈ S`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 2 (`jis-2024-24.3.6-thm-3`). -/
public def circularPartSize (n : ℕ) (S : Finset ℕ) (s : ℕ) : ℕ :=
  (((Finset.Icc 1 n).filter fun d => (s + d) % n ∈ S).min).untopD 0

/-- `c(ℕ_[μ], m, q; n)`: the number of circular compositions of `n` (nonempty sets of removed
edges of the cycle graph `C_n`, one part per removed edge) with parts in `ℕ_[μ]` whose number
of parts is congruent to `q` modulo `m`, each weighted by its `∏ μ(part size)` colorings.
There are none for `n = 0`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 3 (`jis-2024-24.3.6-thm-3`). -/
public def circularCompositionCountMod (μ : ℕ → ℕ) (m q n : ℕ) : ℕ :=
  ∑ S ∈ (Finset.range n).powerset.filter (fun S => S.Nonempty ∧ S.card % m = q % m),
    ∏ s ∈ S, μ (circularPartSize n S s)

/-- `d(ℕ_[μ], m, q; n)`: the number of cyclic compositions of `n` with parts in `ℕ_[μ]` whose
number of parts is congruent to `q` modulo `m`: classes of nonempty colored compositions
(lists of pairs `(part, color)` with `color < μ part`) under cyclic rotation of the terms.
The paper's convention `d(A; 0) = 0` holds because the empty composition is excluded.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 3 (`jis-2024-24.3.6-thm-3`). -/
public def cyclicCompositionCountMod (μ : ℕ → ℕ) (m q n : ℕ) : ℕ :=
  (((Finset.range n).filter fun k => (k + 1) % m = q % m).biUnion fun k =>
    ((Finset.Nat.antidiagonalTuple (k + 1) n).filter fun c => ∀ i, 0 < c i).biUnion fun c =>
      (Fintype.piFinset fun i => Finset.range (μ (c i))).image fun col =>
        ((List.ofFn fun i => (c i, col i) : List (ℕ × ℕ)) : Cycle (ℕ × ℕ))).card

/-- `b(ℕ; 4) = 2³ = 8` compositions of `4`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 4.3 (`jis-2024-24.3.6-thm-10`). -/
public theorem compositionCountMod_univ_one_zero_four :
    compositionCountMod (setMultiplicity Set.univ) 1 0 4 = 8 := by
  decide

/-- `b(ℕ, 2, 1; 4) = 4`: the compositions `4, 2+1+1, 1+2+1, 1+1+2` have an odd number of parts.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 4.3 (`jis-2024-24.3.6-thm-10`). -/
public theorem compositionCountMod_univ_two_one_four :
    compositionCountMod (setMultiplicity Set.univ) 2 1 4 = 4 := by
  decide

/-- The residue is read modulo `m`: `b(ℕ, 2, 3; 4) = b(ℕ, 2, 1; 4) = 4` since `3 ≡ 1 (mod 2)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 3 (`jis-2024-24.3.6-thm-3`). -/
public theorem compositionCountMod_univ_two_three_four :
    compositionCountMod (setMultiplicity Set.univ) 2 3 4 = 4 := by
  decide

/-- `c(ℕ; 3) = 2³ - 1 = 7` circular compositions of `3`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 4.3 (`jis-2024-24.3.6-thm-10`). -/
public theorem circularCompositionCountMod_univ_one_zero_three :
    circularCompositionCountMod (setMultiplicity Set.univ) 1 0 3 = 7 := by
  decide

/-- `c(O, 2, 0; 4) = 5`: the circular odd-part compositions of `4` with an even number of
parts are the four rotations of `1+3` and the single `1+1+1+1`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 4.5 (`jis-2024-24.3.6-thm-13`). -/
public theorem circularCompositionCountMod_odd_two_zero_four :
    circularCompositionCountMod (setMultiplicity {a | Odd a}) 2 0 4 = 5 := by
  decide

/-- `d(ℕ; 4) = 5` cyclic compositions of `4`: `4, 3+1, 2+2, 2+1+1, 1+1+1+1`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 4.3 (`jis-2024-24.3.6-thm-10`). -/
public theorem cyclicCompositionCountMod_univ_one_zero_four :
    cyclicCompositionCountMod (setMultiplicity Set.univ) 1 0 4 = 5 := by
  decide

/-- There are `6` cyclic `ν`-color compositions of `3` (`ν(a) = a` colors for a part `a`):
`3₁, 3₂, 3₃, 2₁+1₁, 2₂+1₁, 1₁+1₁+1₁`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 5.3 (`jis-2024-24.3.6-thm-22`). -/
public theorem cyclicCompositionCountMod_id_one_zero_three :
    cyclicCompositionCountMod id 1 0 3 = 6 := by
  decide

/-- The generating function `j^M(x) = ∑_{n ≥ 1} i(M; n) xⁿ` of the multiplicity sequence of the
multiset `ℕ_[μ]`, over `ℚ`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 2 (`jis-2024-24.3.6-thm-3`). -/
public noncomputable def partSeries (μ : ℕ → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun a => if a = 0 then 0 else (μ a : ℚ)

/-- The series `L_{m,s}(y) = ∑_{r ≥ 1, r ≡ s (mod m)} yʳ / r` (for any natural `s`; only
`s % m` matters). For `s = 0` this is the expansion
`(1/m) log (1/(1 - y^m)) = ∑_{k ≥ 1} y^{km}/(km)`, and for `1 ≤ s ≤ m - 1` the expansion
`∫₀^y u^{s-1}/(1 - u^m) du = ∑_{k ≥ 0} y^{s+km}/(s+km)`, as recorded in the paper's remark
after Theorem 3.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 3 (`jis-2024-24.3.6-thm-3`). -/
public noncomputable def logSeriesMod (m s : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun r => if r ≠ 0 ∧ r % m = s % m then (r : ℚ)⁻¹ else 0

/-- Coefficient of `logSeriesMod`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 3 (`jis-2024-24.3.6-thm-3`). -/
public theorem coeff_logSeriesMod (m s r : ℕ) :
    PowerSeries.coeff r (logSeriesMod m s) = if r ≠ 0 ∧ r % m = s % m then (r : ℚ)⁻¹ else 0 := by
  simp [logSeriesMod]

/-- Theorem 3 (linear compositions): for `A ⊆ ℕ`, `m ≥ 1` and `0 ≤ q < m`,
`∑ b(A, m, q; n) xⁿ = (j^A(x))^q / (1 - (j^A(x))^m)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 3 (`jis-2024-24.3.6-thm-3`). -/
public theorem_wanted compositionCountMod_generatingFunction (A : Set ℕ) [DecidablePred (· ∈ A)]
    {m q : ℕ} (hq : q < m) :
    PowerSeries.mk (fun n => (compositionCountMod (setMultiplicity A) m q n : ℚ))
      = partSeries (setMultiplicity A) ^ q * (1 - partSeries (setMultiplicity A) ^ m)⁻¹

/-- Theorem 3 (circular compositions): for `A ⊆ ℕ`, `m ≥ 1` and `0 ≤ q < m`,
`∑ c(A, m, q; n) xⁿ = x (j^A(x))^e (d/dx j^A(x)) / (1 - (j^A(x))^m)` with `e = m - 1` if `q = 0`
and `e = q - 1` if `q ≠ 0`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 3 (`jis-2024-24.3.6-thm-3`). -/
public theorem_wanted circularCompositionCountMod_generatingFunction (A : Set ℕ)
    [DecidablePred (· ∈ A)] {m q : ℕ} (hq : q < m) :
    PowerSeries.mk (fun n => (circularCompositionCountMod (setMultiplicity A) m q n : ℚ))
      = PowerSeries.X * partSeries (setMultiplicity A) ^ (if q = 0 then m - 1 else q - 1)
          * PowerSeries.derivative (R := ℚ) (partSeries (setMultiplicity A))
          * (1 - partSeries (setMultiplicity A) ^ m)⁻¹

/-- Theorem 3 (cyclic compositions), coefficient of `xⁿ` in
`h^A_{m,q}(x) = ∑_{k ≥ 1} ∑_{0 ≤ s < m, ks ≡ q (mod m)} (φ(k)/k) L_{m,s}(j^A(x^k))`:
since `L_{m,s}(j^A(x^k))` is `L_{m,s}(j^A(x))` with `x` replaced by `x^k`, its `xⁿ`
coefficient is the `x^{n/k}` coefficient of `L_{m,s}(j^A(x))` when `k ∣ n` and `0` otherwise.
Holds for every `n` (both sides vanish at `n = 0`).

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 3 (`jis-2024-24.3.6-thm-3`). -/
public theorem_wanted cyclicCompositionCountMod_eq_sum_logSeriesMod (A : Set ℕ)
    [DecidablePred (· ∈ A)] {m q : ℕ} (hq : q < m) (n : ℕ) :
    (cyclicCompositionCountMod (setMultiplicity A) m q n : ℚ)
      = ∑ k ∈ n.divisors, ∑ s ∈ (Finset.range m).filter (fun s => k * s % m = q),
          ((Nat.totient k : ℚ) / k)
            * PowerSeries.coeff (n / k)
                ((logSeriesMod m s).subst (partSeries (setMultiplicity A)))

/-- Corollary 6 (linear and circular parts): for `A ⊆ ℕ` and `q ∈ {0, 1}`,
`f^A_{2,q} = f^A/2 + (1/2)(-1)^q/(1 + j^A)` and
`g^A_{2,q} = g^A/2 + (1/2)(-1)^{q+1} x (d/dx j^A)/(1 + j^A)`, with `f^A = 1/(1 - j^A)` and
`g^A = x (d/dx j^A)/(1 - j^A)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Corollary 6 (`jis-2024-24.3.6-cor-6`). -/
public theorem_wanted compositionCountMod_two_generatingFunctions (A : Set ℕ)
    [DecidablePred (· ∈ A)] {q : ℕ} (hq : q < 2) :
    PowerSeries.mk (fun n => (compositionCountMod (setMultiplicity A) 2 q n : ℚ))
        = (1 / 2 : ℚ) • (1 - partSeries (setMultiplicity A))⁻¹
          + (1 / 2 : ℚ) • ((-1) ^ q * (1 + partSeries (setMultiplicity A))⁻¹) ∧
      PowerSeries.mk (fun n => (circularCompositionCountMod (setMultiplicity A) 2 q n : ℚ))
        = (1 / 2 : ℚ) • (PowerSeries.X * PowerSeries.derivative (R := ℚ)
            (partSeries (setMultiplicity A))
              * (1 - partSeries (setMultiplicity A))⁻¹)
          + (1 / 2 : ℚ) • ((-1) ^ (q + 1) * PowerSeries.X
              * PowerSeries.derivative (R := ℚ) (partSeries (setMultiplicity A))
              * (1 + partSeries (setMultiplicity A))⁻¹)

/-- Corollary 6 (cyclic part), coefficient of `xⁿ` in
`h^A_{2,0} = (1/2)∑_{k ≥ 1} (φ(k)/k) log (1/(1 - j^A(x^k)²))
  + (1/2)∑_{r ≥ 1} (φ(2r)/(2r)) log ((1 + j^A(x^{2r}))/(1 - j^A(x^{2r})))` and
`h^A_{2,1} = (1/2)∑_{r ≥ 0} (φ(2r+1)/(2r+1)) log ((1 + j^A(x^{2r+1}))/(1 - j^A(x^{2r+1})))`,
writing `log (1/(1 - y²)) = 2 L_{2,0}(y)` and `log ((1 + y)/(1 - y)) = 2 L_{2,1}(y)` and
extracting the `xⁿ` coefficient of a series in `x^k` as in
`cyclicCompositionCountMod_eq_sum_logSeriesMod`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Corollary 6 (`jis-2024-24.3.6-cor-6`). -/
public theorem_wanted cyclicCompositionCountMod_two_eq_sum (A : Set ℕ)
    [DecidablePred (· ∈ A)] (n : ℕ) :
    (cyclicCompositionCountMod (setMultiplicity A) 2 0 n : ℚ)
        = (1 / 2 : ℚ) * ∑ k ∈ n.divisors, ((Nat.totient k : ℚ) / k)
            * (2 * PowerSeries.coeff (n / k)
                ((logSeriesMod 2 0).subst (partSeries (setMultiplicity A))))
          + (1 / 2 : ℚ) * ∑ k ∈ n.divisors.filter Even, ((Nat.totient k : ℚ) / k)
            * (2 * PowerSeries.coeff (n / k)
                ((logSeriesMod 2 1).subst (partSeries (setMultiplicity A)))) ∧
      (cyclicCompositionCountMod (setMultiplicity A) 2 1 n : ℚ)
        = (1 / 2 : ℚ) * ∑ k ∈ n.divisors.filter Odd, ((Nat.totient k : ℚ) / k)
            * (2 * PowerSeries.coeff (n / k)
                ((logSeriesMod 2 1).subst (partSeries (setMultiplicity A))))

/-- Lemma 9: for `0 ≤ q < m` and `n ≥ 1`, `b(ℕ, m, q; n) = c(ℕ, m, q; n) - c(ℕ, m, q; n - 1)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 9 (`jis-2024-24.3.6-lem-9`). -/
public theorem_wanted compositionCountMod_univ_eq_circular_sub {m q n : ℕ} (hq : q < m)
    (hn : 0 < n) :
    (compositionCountMod (setMultiplicity Set.univ) m q n : ℤ)
      = circularCompositionCountMod (setMultiplicity Set.univ) m q n
        - circularCompositionCountMod (setMultiplicity Set.univ) m q (n - 1)

/-- Lemma 9 (second identity): for `m > 1`, `0 ≤ q < m` and `n ≥ 1`, `b(ℕ, m, q; n)` equals
`c(ℕ, m, m - 1; n - 1)` if `q = 0`, `c(ℕ, m, 0; n - 1) + 1` if `q = 1`, and
`c(ℕ, m, q - 1; n - 1)` otherwise.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 9 (`jis-2024-24.3.6-lem-9`). -/
public theorem_wanted compositionCountMod_univ_eq_circular_pred {m q n : ℕ} (hm : 1 < m)
    (hq : q < m) (hn : 0 < n) :
    compositionCountMod (setMultiplicity Set.univ) m q n
      = if q = 0 then circularCompositionCountMod (setMultiplicity Set.univ) m (m - 1) (n - 1)
        else if q = 1 then
          circularCompositionCountMod (setMultiplicity Set.univ) m 0 (n - 1) + 1
        else circularCompositionCountMod (setMultiplicity Set.univ) m (q - 1) (n - 1)

/-- Theorem 10 (linear compositions):
`b(ℕ, m, q; n) = 2^{n-1}/m + (2/m)∑_{k=1}^{⌊(m-1)/2⌋} (2 cos(πk/m))^{n-1} cos(πk(n+1-2q)/m)`
for `0 ≤ q < m`, under the added hypothesis `n ≥ 2`, or `n ≥ 1` and `m` odd. The paper states
`n ≥ 1`, but at `n = 1` with `m` even the omitted `k = m/2` term `(2 cos(π/2))⁰ cos(…)` is
nonzero: for `m = 2, q = 0, n = 1` the right side is `1/2` while `b(ℕ, 2, 0; 1) = 0`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 10 (`jis-2024-24.3.6-thm-10`). -/
public theorem_wanted compositionCountMod_univ_eq_cos_sum {m q n : ℕ} (hq : q < m)
    (hn : 2 ≤ n ∨ (0 < n ∧ Odd m)) :
    (compositionCountMod (setMultiplicity Set.univ) m q n : ℝ)
      = 2 ^ (n - 1) / m + 2 / m * ∑ k ∈ Finset.Icc 1 ((m - 1) / 2),
          (2 * Real.cos (Real.pi * k / m)) ^ (n - 1)
            * Real.cos (Real.pi * k * ((n : ℝ) + 1 - 2 * q) / m)

/-- Theorem 10 (circular compositions): for `0 ≤ q < m` and `n ≥ 1`,
`c(ℕ, m, q; n) = -[q = 0] + 2ⁿ/m + (2/m)∑_{k=1}^{⌊(m-1)/2⌋} (2 cos(πk/m))ⁿ cos(πk(n-2q)/m)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 10 (`jis-2024-24.3.6-thm-10`). -/
public theorem_wanted circularCompositionCountMod_univ_eq_cos_sum {m q n : ℕ} (hq : q < m)
    (hn : 0 < n) :
    (circularCompositionCountMod (setMultiplicity Set.univ) m q n : ℝ)
      = (if q = 0 then -1 else 0) + 2 ^ n / m + 2 / m * ∑ k ∈ Finset.Icc 1 ((m - 1) / 2),
          (2 * Real.cos (Real.pi * k / m)) ^ n
            * Real.cos (Real.pi * k * ((n : ℝ) - 2 * q) / m)

/-- Theorem 12: for `N ≥ 2` and `n ≥ 1`, with `[N] = {1, …, N}`,
`b([N], 2, 0; n) = F^{(N)}_{n+1}/2 + ε`, `b([N], 2, 1; n) = F^{(N)}_{n+1}/2 - ε` where
`ε = 1/2, -1/2, 0` according as `n ≡ 0, n ≡ 1`, or neither modulo `N + 1`, and
`c([N], 2, 0; n) = L^{(N)}_n/2 + δ`, `c([N], 2, 1; n) = L^{(N)}_n/2 - δ` where `δ = N/2` if
`n ≡ 0 (mod N + 1)` and `δ = -1/2` otherwise. For `n ≥ 1` the paper's `N`-step Lucas number
`L^{(N)}_n` (Noe and Post: `L_0 = N`, `L_{<0} = -1`, sum of the `N` preceding terms) is
`nStepLucas N n` (`2ⁿ - 1` for `1 ≤ n ≤ N`, sum of the `N` preceding terms afterwards).

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 12 (`jis-2024-24.3.6-thm-12`). -/
public theorem_wanted compositionCountMod_Icc_two {N n : ℕ} (hN : 2 ≤ N) (hn : 0 < n) :
    (compositionCountMod (setMultiplicity (Set.Icc 1 N)) 2 0 n : ℚ)
        = (nStepFibonacci N (n + 1) : ℚ) / 2
          + (if n % (N + 1) = 0 then 1 / 2 else if n % (N + 1) = 1 then -1 / 2 else 0) ∧
      (compositionCountMod (setMultiplicity (Set.Icc 1 N)) 2 1 n : ℚ)
        = (nStepFibonacci N (n + 1) : ℚ) / 2
          + (if n % (N + 1) = 0 then -1 / 2 else if n % (N + 1) = 1 then 1 / 2 else 0) ∧
      (circularCompositionCountMod (setMultiplicity (Set.Icc 1 N)) 2 0 n : ℚ)
        = (nStepLucas N n : ℚ) / 2 + (if n % (N + 1) = 0 then (N : ℚ) / 2 else -1 / 2) ∧
      (circularCompositionCountMod (setMultiplicity (Set.Icc 1 N)) 2 1 n : ℚ)
        = (nStepLucas N n : ℚ) / 2 + (if n % (N + 1) = 0 then -(N : ℚ) / 2 else 1 / 2)

/-- Theorem 13: for `m ≥ 1`, `ζ = e^{2πi/m}`, `0 ≤ q < m` and `n ≥ 1`, with Fibonacci and
Lucas polynomials `𝓕_n`, `𝓛_n` (`𝓕_0 = 0, 𝓕_1 = 1`, `𝓛_0 = 2, 𝓛_1 = z`,
`P_{n+2} = z P_{n+1} + P_n`) and `S(m, n, q) = {k : 2k ≡ n - q (mod m), 0 ≤ k ≤ ⌊(n-1)/2⌋}`:
`b(O, m, q; n) = (1/m)∑_{k<m} ζ^{k(1-q)} 𝓕_n(ζ^k) = ∑_{k ∈ S(m,n,q)} C(n-k-1, k)` and
`c(O, m, q; n) = -(1 + (-1)ⁿ)0^q + (1/m)∑_{k<m} ζ^{-kq} 𝓛_n(ζ^k)
  = ∑_{k ∈ S(m,n,q)} (n/(n-k)) C(n-k, k)`, where `O` is the set of odd naturals.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 13 (`jis-2024-24.3.6-thm-13`). -/
public theorem_wanted compositionCountMod_odd_eq {m q n : ℕ} (hq : q < m) (hn : 0 < n) :
    ((compositionCountMod (setMultiplicity {a | Odd a}) m q n : ℂ)
        = (1 / m : ℂ) * ∑ k ∈ Finset.range m,
            Complex.exp (2 * Real.pi * Complex.I / m) ^ ((k : ℤ) * (1 - (q : ℤ)))
              * Polynomial.aeval (Complex.exp (2 * Real.pi * Complex.I / m) ^ k)
                  (generalizedFibonacciPolynomial 0 1 Polynomial.X 1 n) ∧
      compositionCountMod (setMultiplicity {a | Odd a}) m q n
        = ∑ᶠ k ∈ compositionHalfIndexSet m n q, (n - k - 1).choose k) ∧
    ((circularCompositionCountMod (setMultiplicity {a | Odd a}) m q n : ℂ)
        = -(1 + (-1) ^ n) * (0 : ℂ) ^ q + (1 / m : ℂ) * ∑ k ∈ Finset.range m,
            Complex.exp (2 * Real.pi * Complex.I / m) ^ (-((k : ℤ) * q))
              * Polynomial.aeval (Complex.exp (2 * Real.pi * Complex.I / m) ^ k)
                  (generalizedFibonacciPolynomial 2 Polynomial.X Polynomial.X 1 n) ∧
      (circularCompositionCountMod (setMultiplicity {a | Odd a}) m q n : ℚ)
        = ∑ᶠ k ∈ compositionHalfIndexSet m n q,
            ((n : ℚ) / (n - k : ℕ)) * ((n - k).choose k : ℚ))

/-- Theorem 17: for `m ≥ 1`, `0 ≤ q < m` and `n ≥ 1`, with `ν(a) = a` colors for a part `a`
(the multiset `ℕ_[ν]`) and `T(m, n, q) = {k : k ≡ n - q (mod m), 0 ≤ k ≤ n - 1}`:
`b(ℕ_[ν], m, q; n) = b(O, 2m, 2q; 2n) = ∑_{k ∈ T(m,n,q)} C(2n-k-1, k)` and
`c(ℕ_[ν], m, q; n) = c(O, 2m, 2q; 2n) = ∑_{k ∈ T(m,n,q)} (2n/(2n-k)) C(2n-k, k)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 17 (`jis-2024-24.3.6-thm-17`). -/
public theorem_wanted compositionCountMod_id_eq {m q n : ℕ} (hq : q < m) (hn : 0 < n) :
    (compositionCountMod id m q n
        = compositionCountMod (setMultiplicity {a | Odd a}) (2 * m) (2 * q) (2 * n) ∧
      compositionCountMod id m q n
        = ∑ᶠ k ∈ compositionIndexSet m n q, (2 * n - k - 1).choose k) ∧
    (circularCompositionCountMod id m q n
        = circularCompositionCountMod (setMultiplicity {a | Odd a}) (2 * m) (2 * q) (2 * n) ∧
      (circularCompositionCountMod id m q n : ℚ)
        = ∑ᶠ k ∈ compositionIndexSet m n q,
            ((2 * n : ℚ) / (2 * n - k : ℕ)) * ((2 * n - k).choose k : ℚ))

/-- Theorem 22: for `n ≥ 1`, with `n_O` the greatest odd divisor of `n` and
`d*(n) = 2 d(O; 2n) - d(ℕ_[ν]; n)` (the paper's identification of the coefficients of
`h*(x)`), `d*(n) = d(O; n_O) = (1/n_O)∑_{k ∣ n_O} φ(k) L_{n_O/k}` (`L` the Lucas numbers).

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 22 (`jis-2024-24.3.6-thm-22`). -/
public theorem_wanted cyclicCompositionCount_dual_defect_eq {n : ℕ} (hn : 0 < n) :
    (2 * cyclicCompositionCountMod (setMultiplicity {a | Odd a}) 1 0 (2 * n)
        - cyclicCompositionCountMod id 1 0 n : ℤ)
        = cyclicCompositionCountMod (setMultiplicity {a | Odd a}) 1 0
            (n / 2 ^ n.factorization 2) ∧
      (cyclicCompositionCountMod (setMultiplicity {a | Odd a}) 1 0 (n / 2 ^ n.factorization 2)
          : ℚ)
        = (1 / (n / 2 ^ n.factorization 2 : ℕ) : ℚ)
          * ∑ k ∈ (n / 2 ^ n.factorization 2).divisors,
              (Nat.totient k : ℚ) * lucasNumber ((n / 2 ^ n.factorization 2) / k)

end

end MetaMathlibExt
