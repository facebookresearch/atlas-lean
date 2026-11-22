/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arndt compositions with restricted parts

Statements from Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez,
"Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants", *Journal of
Integer Sequences* 28 (2025), Article 25.3.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Ramirez/ramirez19.html>).

An Arndt composition is a composition `(σ₁, σ₂, …, σ_k)` with `σ_{2i-1} > σ_{2i}` for every
`i` with `2i ≤ k` (Hopkins and Tangboonduangjit; notation of D. F. Checa and J. L. Ramírez,
*Arndt compositions: a generating functions approach*, arXiv:2311.15388, Section 1).
`arndtCompositionCount S n k` counts Arndt compositions of `n` with `k` parts, all in the set
`S` (given as a decidable predicate), represented as `k`-tuples of positive integers summing
to `n` (0-based: the pairs are positions `(2i, 2i + 1)`). `arndtGF S` is the bivariate
generating function `A_S(x, y) = ∑ a_S(n, k) xⁿ yᵏ` in `ℤ[y][[x]]`; `S = fun _ => True` gives
the unrestricted `A(x, y)`.

Section 3 (palindromic Arndt compositions) uses trivariate power series in
`MvPowerSeries (Fin 3) ℚ` with `X 0 = x` (weight), `X 1 = y` (number of parts) and `X 2 = z`
(last or middle summand); infinite `q`-series sums are taken in the coefficientwise (pi)
topology. Section 4 counts colored (`n`-color) Arndt compositions, where a part of size `m`
comes in one of `m` colors.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.PadovanSequence

open scoped MvPowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- The number of Arndt compositions of `n` with `k` parts, all parts satisfying `S`: `k`-tuples
`c` of positive integers with `∑ c = n`, every `S (c i)`, and `c (2i) > c (2i + 1)` for each pair
of consecutive positions `2i, 2i + 1 < k`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 1 (definition of Arndt compositions, after
D. F. Checa and J. L. Ramírez, arXiv:2311.15388, Section 1). -/
def arndtCompositionCount (S : ℕ → Prop) [DecidablePred S] (n k : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter fun c =>
    (∀ i, 0 < c i ∧ S (c i)) ∧
      ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i).card

/-- The Arndt compositions of `6` with two parts are `(5,1)` and `(4,2)`.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_two : arndtCompositionCount (fun _ => True) 6 2 = 2 := by
  decide

/-- The Arndt compositions of `6` with three parts are `(4,1,1)`, `(3,2,1)`, `(3,1,2)`,
`(2,1,3)`.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_three : arndtCompositionCount (fun _ => True) 6 3 = 4 := by
  decide

/-- The only Arndt composition of `6` with four parts is `(2,1,2,1)`.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_four : arndtCompositionCount (fun _ => True) 6 4 = 1 := by
  decide

/-- The bivariate generating function `A_S(x, y) = ∑_{n, k} a_S(n, k) xⁿ yᵏ` of Arndt
compositions with parts in `S`, by weight (`x`) and number of parts (`y`), in `ℤ[y][[x]]`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 2. -/
noncomputable def arndtGF (S : ℕ → Prop) [DecidablePred S] : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), (arndtCompositionCount S n k : Polynomial ℤ) * Polynomial.X ^ k

/-- The `xⁿ` coefficient of `arndtGF S` is `∑_k a_S(n, k) yᵏ`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 2. -/
theorem coeff_arndtGF (S : ℕ → Prop) [DecidablePred S] (n : ℕ) :
    PowerSeries.coeff n (arndtGF S) =
      ∑ k ∈ Finset.range (n + 1),
        (arndtCompositionCount S n k : Polynomial ℤ) * Polynomial.X ^ k := by
  simp [arndtGF]

/-- For a set `S` of positive integers,
`A_S(x, y) = (1 + y ∑_{i ∈ S} xⁱ) ∑_{m ≥ 0} (∑_{i, j ∈ S, j < i} x^{i+j})^m y^{2m}`, stated
multiplicatively: `A_S · (1 - y² Q_S) = 1 + y P_S` with `P_S = ∑_{i ∈ S} xⁱ` and
`Q_S = ∑_{i, j ∈ S, j < i} x^{i+j}`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 1 (`jis-2025-25.3.6-thm-1`). -/
public theorem_wanted arndtGF_mul_one_sub_pairs (S : ℕ → Prop) [DecidablePred S]
    (hS : ¬ S 0) :
    arndtGF S *
        (1 - PowerSeries.C (Polynomial.X ^ 2) *
          PowerSeries.mk fun n =>
            ((((Finset.range n) ×ˢ (Finset.range n)).filter fun ij =>
              ij.2 < ij.1 ∧ S ij.1 ∧ S ij.2 ∧ ij.1 + ij.2 = n).card : Polynomial ℤ)) =
      1 + PowerSeries.C Polynomial.X *
        PowerSeries.mk fun i => if S i then (1 : Polynomial ℤ) else 0

/-- The generating function of all Arndt compositions by weight and number of parts is
`A(x, y) = (1 + xy/(1 - x)) ∑_{m ≥ 0} y^{2m} x^{3m} / (x; x)₂^m` with
`(x; x)₂ = (1 - x)(1 - x²)`, stated multiplicatively:
`A(x, y) · ((1 - x)(1 - x²) - y² x³) = (1 - x + xy)(1 - x²)`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 9 (`jis-2025-25.3.6-thm-9`). -/
public theorem_wanted arndtGF_univ_mul :
    arndtGF (fun _ => True) *
        ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) -
          PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ 3) =
      (1 - PowerSeries.X + PowerSeries.C Polynomial.X * PowerSeries.X) *
        (1 - PowerSeries.X ^ 2)

/-- The number of Arndt compositions of `n` into `2ℓ` parts is
`∑_{a₁ + ⋯ + a_ℓ = n, aᵢ ≥ 3} ∏ ⌊(aᵢ - 1)/2⌋`, and into `2ℓ + 1` parts is
`∑_{a₁ + ⋯ + a_{ℓ+1} = n, aᵢ ≥ 3 (i ≤ ℓ), a_{ℓ+1} ≥ 1} ∏_{i ≤ ℓ} ⌊(aᵢ - 1)/2⌋`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 10 (`jis-2025-25.3.6-thm-10`). -/
public theorem_wanted arndtCompositionCount_eq_sum_prod (n ℓ : ℕ) :
    arndtCompositionCount (fun _ => True) n (2 * ℓ) =
        (∑ a ∈ (Finset.Nat.antidiagonalTuple ℓ n).filter (fun a => ∀ i, 3 ≤ a i),
          ∏ i, (a i - 1) / 2) ∧
      arndtCompositionCount (fun _ => True) n (2 * ℓ + 1) =
        (∑ a ∈ (Finset.Nat.antidiagonalTuple (ℓ + 1) n).filter
            (fun a => (∀ i : Fin ℓ, 3 ≤ a i.castSucc) ∧ 1 ≤ a (Fin.last ℓ)),
          ∏ i : Fin ℓ, (a i.castSucc - 1) / 2)


/-- The number of Arndt compositions of `n` with parts in `{1, 2, 3}`, including the empty
composition for `n = 0`, is the Padovan number `P(n)` (`P(0) = P(1) = P(2) = 1`,
`P(n) = P(n - 2) + P(n - 3)`, OEIS A000931), which is `shiftedPadovanSequence (n + 2)`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 2 (`jis-2025-25.3.6-thm-2`). -/
public theorem_wanted sum_arndtCompositionCount_le_three (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), arndtCompositionCount (fun i => i ≤ 3) n k =
      shiftedPadovanSequence (n + 2)

/-- The number of Arndt compositions of `n` with parts in `{1, 2, 3, 4}`, including the empty
composition for `n = 0`, is the Narayana cows number `N(n)` (`N(0) = N(1) = N(2) = 1`,
`N(n) = N(n - 1) + N(n - 3)`, OEIS A000930), which is `narayanaCowsSequence (n + 1)`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 4 (`jis-2025-25.3.6-thm-4`). -/
public theorem_wanted sum_arndtCompositionCount_le_four (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), arndtCompositionCount (fun i => i ≤ 4) n k =
      narayanaCowsSequence (n + 1)

/-- The generating function `A(x, y; ℓ)` of Arndt compositions with largest part at most `ℓ`
is `(1 - x²)(1 - x + x(1 - x^ℓ)y) / (1 - x^{2+2ℓ}y² + x^{2+ℓ}(1 + x)y² - x(1 + x + x²(-1 + y²)))`,
stated multiplicatively. The paper assumes `ℓ ≥ 2`; the identity also holds for `ℓ = 0, 1`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 5 (`jis-2025-25.3.6-cor-5`). -/
public theorem_wanted arndtGF_le_mul (ℓ : ℕ) :
    arndtGF (fun i => i ≤ ℓ) *
        (1 - PowerSeries.X ^ (2 + 2 * ℓ) * PowerSeries.C (Polynomial.X ^ 2) +
          PowerSeries.X ^ (2 + ℓ) * (1 + PowerSeries.X) * PowerSeries.C (Polynomial.X ^ 2) -
          PowerSeries.X * (1 + PowerSeries.X +
            PowerSeries.X ^ 2 * (-1 + PowerSeries.C (Polynomial.X ^ 2)))) =
      (1 - PowerSeries.X ^ 2) *
        (1 - PowerSeries.X + PowerSeries.X * (1 - PowerSeries.X ^ ℓ) * PowerSeries.C Polynomial.X)

/-- The generating function `B(x, y; ℓ)` of Arndt compositions with smallest part at least `ℓ`
is `(1 - x²)(1 - x + x^ℓ y) / (1 - x - x² + x³ - x^{2ℓ+1}y²)` for `ℓ ≥ 1`, stated
multiplicatively.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 6 (`jis-2025-25.3.6-cor-6`). -/
public theorem_wanted arndtGF_ge_mul (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    arndtGF (fun i => ℓ ≤ i) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.X ^ (2 * ℓ + 1) * PowerSeries.C (Polynomial.X ^ 2)) =
      (1 - PowerSeries.X ^ 2) *
        (1 - PowerSeries.X + PowerSeries.X ^ ℓ * PowerSeries.C Polynomial.X)

/-- The generating functions of Arndt compositions with only even parts and with only odd parts
are `A_E(x, y) = (1 - x⁴)(1 - x²(1 - y)) / (1 - x² - x⁴ + x⁶(1 - y²))` and
`A_O(x, y) = (1 - x⁴)(1 - x² + xy) / (1 - x² + x⁶ - x⁴(1 + y²))`, stated multiplicatively.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 7 (`jis-2025-25.3.6-cor-7`). -/
public theorem_wanted arndtGF_even_odd_mul :
    arndtGF (fun i => i % 2 = 0) *
          (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 4 +
            PowerSeries.X ^ 6 * (1 - PowerSeries.C (Polynomial.X ^ 2))) =
        (1 - PowerSeries.X ^ 4) *
          (1 - PowerSeries.X ^ 2 * (1 - PowerSeries.C Polynomial.X)) ∧
      arndtGF (fun i => i % 2 = 1) *
          (1 - PowerSeries.X ^ 2 + PowerSeries.X ^ 6 -
            PowerSeries.X ^ 4 * (1 + PowerSeries.C (Polynomial.X ^ 2))) =
        (1 - PowerSeries.X ^ 4) *
          (1 - PowerSeries.X ^ 2 + PowerSeries.X * PowerSeries.C Polynomial.X)

/-! ### Palindromic Arndt compositions (Section 3) -/

/-- The number of down/up (descending wiggly) compositions `σ₁ > σ₂ < σ₃ > σ₄ < ⋯` of `n` with
`k` parts and last part `j` (`j = 0` for the empty composition): `k`-tuples `c` of positive
integers with `∑ c = n`, `c (i + 1) < c i` for even `i` and `c i < c (i + 1)` for odd `i`
(0-based), and last entry `j`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `W`, OEIS A025049). -/
def downUpCompositionCount (n k j : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter fun c =>
    (∀ i, 0 < c i) ∧
      (∀ i i' : Fin k, (i' : ℕ) = i + 1 →
        ((i : ℕ) % 2 = 0 → c i' < c i) ∧ ((i : ℕ) % 2 = 1 → c i < c i')) ∧
      (if h : 0 < k then c ⟨k - 1, by omega⟩ else 0) = j).card

/-- The down/up compositions of `5` with two parts are `(4,1)` and `(3,2)`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `W`). -/
theorem downUpCompositionCount_five_two : downUpCompositionCount 5 2 1 = 1 ∧
    downUpCompositionCount 5 2 2 = 1 ∧ downUpCompositionCount 5 2 3 = 0 := by
  decide

/-- The down/up compositions of `6` with three parts are `(2,1,3)` and `(3,1,2)`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `W`). -/
theorem downUpCompositionCount_six_three : downUpCompositionCount 6 3 3 = 1 ∧
    downUpCompositionCount 6 3 2 = 1 ∧ downUpCompositionCount 6 3 1 = 0 := by
  decide

/-- `F(x, y, z) = ∑_{k ≥ 0} a_k(x, z) y^{2k}`, the generating function of down/up compositions
with an even number of parts by weight (`x`), number of parts (`y`) and last part (`z`).

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.1 (definition of `F`). -/
noncomputable def downUpEvenGF : MvPowerSeries (Fin 3) ℚ := fun e =>
  if e 1 % 2 = 0 then (downUpCompositionCount (e 0) (e 1) (e 2) : ℚ) else 0

/-- `G(x, y, z)`, the generating function of down/up compositions with an odd number of parts by
weight (`x`), number of parts (`y`) and last part (`z`).

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.1 (definition of `G`). -/
noncomputable def downUpOddGF : MvPowerSeries (Fin 3) ℚ := fun e =>
  if e 1 % 2 = 1 then (downUpCompositionCount (e 0) (e 1) (e 2) : ℚ) else 0

/-- The series `α(x, y, w) = ∑_{n ≥ 0} (-1)ⁿ x^{n²+n} y^{2n} wⁿ / (xw; x)_{2n}` in
`ℚ[[x, y, z]]`, for a series `w` (the paper's third argument; `w = z` and `w = x` occur).

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 12, equation (5). -/
noncomputable def arndtPalAlpha (w : MvPowerSeries (Fin 3) ℚ) : MvPowerSeries (Fin 3) ℚ :=
  ∑' n : ℕ, (-1 : MvPowerSeries (Fin 3) ℚ) ^ n * MvPowerSeries.X 0 ^ (n ^ 2 + n) *
    MvPowerSeries.X 1 ^ (2 * n) * w ^ n *
      (∏ k ∈ Finset.range (2 * n), (1 - MvPowerSeries.X 0 ^ (k + 1) * w))⁻¹

/-- The series
`β(x, y, w) = ∑_{n ≥ 1} (-1)^{n+1} x^{n²+n} y^{2n} wⁿ / ((1 - x)(xw; x)_{2n-1})` in
`ℚ[[x, y, z]]`, for a series `w` (the paper's third argument; `w = z` and `w = x` occur).

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 12, equation (5). -/
noncomputable def arndtPalBeta (w : MvPowerSeries (Fin 3) ℚ) : MvPowerSeries (Fin 3) ℚ :=
  ∑' n : ℕ, (-1 : MvPowerSeries (Fin 3) ℚ) ^ (n + 2) * MvPowerSeries.X 0 ^ ((n + 1) ^ 2 + (n + 1)) *
    MvPowerSeries.X 1 ^ (2 * (n + 1)) * w ^ (n + 1) *
      ((1 - MvPowerSeries.X 0) *
        ∏ k ∈ Finset.range (2 * n + 1), (1 - MvPowerSeries.X 0 ^ (k + 1) * w))⁻¹

/-- `F(x, y, z) = α(x, y, z) + α(x, y, x) β(x, y, z) / (1 - β(x, y, x))`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 12 (`jis-2025-25.3.6-thm-12`). -/
public theorem_wanted downUpEvenGF_eq :
    downUpEvenGF = arndtPalAlpha (MvPowerSeries.X 2) +
      arndtPalAlpha (MvPowerSeries.X 0) * (1 - arndtPalBeta (MvPowerSeries.X 0))⁻¹ *
        arndtPalBeta (MvPowerSeries.X 2)

/-- `G(x, y, z) = xyz / (1 - xz) · F(x, y, xz)`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 13 (`jis-2025-25.3.6-thm-13`). -/
public theorem_wanted downUpOddGF_eq :
    downUpOddGF = MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 *
      (1 - MvPowerSeries.X 0 * MvPowerSeries.X 2)⁻¹ *
        MvPowerSeries.subst
          ![MvPowerSeries.X 0, MvPowerSeries.X 1, MvPowerSeries.X 0 * MvPowerSeries.X 2]
          downUpEvenGF

/-- The number of nonempty palindromic Arndt compositions of `n` with `k` parts and middle
summand `m`: `k`-tuples `c` of positive integers with `∑ c = n`, `0 < k`, the Arndt condition
`c (2i + 1) < c (2i)`, `c i = c (k - 1 - i)`, and `c ⌊k/2⌋ = m` (0-based).

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3 (the set `PA`). -/
def palindromicArndtCount (n k m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter fun c =>
    (∀ i, 0 < c i) ∧
      (∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i) ∧
      (∀ i j : Fin k, (i : ℕ) + j + 1 = k → c i = c j) ∧
      (if h : 0 < k then c ⟨k / 2, by omega⟩ = m else False)).card

/-- The palindromic Arndt compositions of `5` are `(5)` and `(2,1,2)` (the `x⁵` coefficient
`y + y³` of `PA(x, y, 1)`).

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.2 (series expansion of `PA(x, y, 1)`). -/
theorem palindromicArndtCount_five : palindromicArndtCount 5 1 5 = 1 ∧
    palindromicArndtCount 5 3 1 = 1 ∧ palindromicArndtCount 5 3 2 = 0 := by
  decide

/-- `PA(x, y, z)`, the generating function of nonempty palindromic Arndt compositions by
weight (`x`), number of parts (`y`) and middle summand (`z`).

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 3.2 (definition of `PA`). -/
noncomputable def palindromicArndtGF : MvPowerSeries (Fin 3) ℚ := fun e =>
  (palindromicArndtCount (e 0) (e 1) (e 2) : ℚ)

/-- `PA(x, y, z) = xyz/(1 - xz) F(x², y², xz) + x³y³z/((1 - x²)(1 - xz)) F(x², y², x²)
- x³y³z/((1 - xz)(1 - x³z)) F(x², y², x³z)`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 14 (`jis-2025-25.3.6-thm-14`). -/
public theorem_wanted palindromicArndtGF_eq :
    palindromicArndtGF =
      MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2 *
          (1 - MvPowerSeries.X 0 * MvPowerSeries.X 2)⁻¹ *
          MvPowerSeries.subst ![MvPowerSeries.X 0 ^ 2, MvPowerSeries.X 1 ^ 2,
            MvPowerSeries.X 0 * MvPowerSeries.X 2] downUpEvenGF +
        MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 ^ 3 * MvPowerSeries.X 2 *
          ((1 - MvPowerSeries.X 0 ^ 2) * (1 - MvPowerSeries.X 0 * MvPowerSeries.X 2))⁻¹ *
          MvPowerSeries.subst ![MvPowerSeries.X 0 ^ 2, MvPowerSeries.X 1 ^ 2,
            MvPowerSeries.X 0 ^ 2] downUpEvenGF -
        MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 1 ^ 3 * MvPowerSeries.X 2 *
          ((1 - MvPowerSeries.X 0 * MvPowerSeries.X 2) *
            (1 - MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 2))⁻¹ *
          MvPowerSeries.subst ![MvPowerSeries.X 0 ^ 2, MvPowerSeries.X 1 ^ 2,
            MvPowerSeries.X 0 ^ 3 * MvPowerSeries.X 2] downUpEvenGF

/-! ### Colored Arndt compositions (Section 4) -/

/-- The number `c(n, k)` of colored (`n`-color) Arndt compositions of `n` with `k` parts: Arndt
compositions of `n` with `k` parts in which a part of size `m` takes one of `m` colors, so each
Arndt composition `c` contributes `∏ c i`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4 (definition of colored Arndt compositions). -/
def coloredArndtCount (n k : ℕ) : ℕ :=
  ∑ c ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun c =>
      (∀ i, 0 < c i) ∧ ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i),
    ∏ i, c i

/-- The colored Arndt compositions of `4` are `4₁, 4₂, 4₃, 4₄`, `(3_a, 1₁)` for `a ≤ 3` and
`(2_a, 1₁, 1₁)` for `a ≤ 2`: `c(4, 1) = 4`, `c(4, 2) = 3`, `c(4, 3) = 2`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4, list (6). -/
theorem coloredArndtCount_four : coloredArndtCount 4 1 = 4 ∧ coloredArndtCount 4 2 = 3 ∧
    coloredArndtCount 4 3 = 2 := by
  decide

/-- The bivariate generating function `C(x, y) = ∑ c(n, k) xⁿ yᵏ` of colored Arndt compositions
in `ℤ[y][[x]]`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4 (definition of `C(x, y)`). -/
noncomputable def coloredArndtGF : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), (coloredArndtCount n k : Polynomial ℤ) * Polynomial.X ^ k

/-- `C(x, y) = (1 - x)²(1 + x)³(1 + x² + x(y - 2)) /
(1 - x - 3x² - x³(2y² - 3) - x⁴(y² - 3) - x⁵(3 + y²) - x⁶ + x⁷)`, stated multiplicatively.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 17 (`jis-2025-25.3.6-thm-17`). -/
public theorem_wanted coloredArndtGF_mul :
    coloredArndtGF *
        (1 - PowerSeries.X - 3 * PowerSeries.X ^ 2 -
          PowerSeries.X ^ 3 * (2 * PowerSeries.C (Polynomial.X ^ 2) - 3) -
          PowerSeries.X ^ 4 * (PowerSeries.C (Polynomial.X ^ 2) - 3) -
          PowerSeries.X ^ 5 * (3 + PowerSeries.C (Polynomial.X ^ 2)) -
          PowerSeries.X ^ 6 + PowerSeries.X ^ 7) =
      (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 3 *
        (1 + PowerSeries.X ^ 2 + PowerSeries.X * (PowerSeries.C Polynomial.X - 2))

/-- `∑ c(n) xⁿ = (1 - x)²(1 + x)³(1 - x + x²) / (1 - x - 3x² + x³ + 2x⁴ - 4x⁵ - x⁶ + x⁷)`, with
`c(n) = ∑_k c(n, k)`, stated multiplicatively.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 18 (`jis-2025-25.3.6-cor-18`). -/
public theorem_wanted coloredArndt_total_mul :
    (PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1), (coloredArndtCount n k : ℤ)) *
        (1 - PowerSeries.X - 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 -
          4 * PowerSeries.X ^ 5 - PowerSeries.X ^ 6 + PowerSeries.X ^ 7) =
      (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 3 *
        (1 - PowerSeries.X + PowerSeries.X ^ 2)

/-- `C_k(x) = ∑_n c(n, k) xⁿ = x^{k+⌊k/2⌋}(x² + x + 2)^{⌊k/2⌋} / ((1 - x)^{2k}(1 + x)^{3⌊k/2⌋})`,
stated multiplicatively.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 19 (`jis-2025-25.3.6-thm-19`). -/
public theorem_wanted coloredArndt_parts_mul (k : ℕ) :
    (PowerSeries.mk fun n => (coloredArndtCount n k : ℤ)) *
        ((1 - PowerSeries.X) ^ (2 * k) * (1 + PowerSeries.X) ^ (3 * (k / 2))) =
      PowerSeries.X ^ (k + k / 2) * (PowerSeries.X ^ 2 + PowerSeries.X + 2) ^ (k / 2)

/-- For fixed `k ≥ 1`, `c(n, k) ∼ n^{2k-1} / (2^{⌊k/2⌋} (2k - 1)!)` as `n → ∞`.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Corollary 20 (`jis-2025-25.3.6-cor-20`). -/
public theorem_wanted coloredArndtCount_isEquivalent (k : ℕ) (hk : 0 < k) :
    Asymptotics.IsEquivalent Filter.atTop (fun n => (coloredArndtCount n k : ℝ))
      fun n => (n : ℝ) ^ (2 * k - 1) / (2 ^ (k / 2) * (Nat.factorial (2 * k - 1) : ℝ))

end

end MetaMathlibExt
