/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Shade in compositions of integers

Statement from Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6.

A composition `x₁ + ⋯ + x_k` is drawn as a bargraph whose `i`-th column holds `x_i` stacked
unit cells.  With the sun at infinity in the northwest, a cell outside the bargraph (in a column
of the bargraph or to the right of it, at height `≥ 1`) is shaded when the diagonal ray towards
the northwest meets the bargraph: the cell in column `c` at height `h` is shaded iff
`h > x_c` and some earlier column `j < c` has `x_j ≥ h + (c - j)`.  For example the
composition `4` has `3 + 2 + 1 = 6` shaded cells, and the compositions of `4` have `13` shaded
cells in total (Section 1 and Figure 5 of the paper).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The number of shaded cells of the bargraph of a composition given by its list of parts
(columns `0, 1, …`, parts read with `List.getD _ _ 0`, so columns past the last part are
empty): cells `(c, h)` with `h ≥ 1`, `h > x_c` and `x_j ≥ h + (c - j)` for some `j < c`.  All
such cells satisfy `c < length + sum` and `h ≤ sum`.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 1. -/
def compositionShade (x : List ℕ) : ℕ :=
  ∑ c ∈ Finset.range (x.length + x.sum), ∑ h ∈ Finset.Icc 1 x.sum,
    if x.getD c 0 < h ∧ ∃ j < c, h + (c - j) ≤ x.getD j 0 then 1 else 0

/-- The total shade `c(n)` over all compositions of `n`.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 2. -/
def totalCompositionShade (n : ℕ) : ℕ :=
  ∑ x : Composition n, compositionShade x.blocks

/-- The one-part composition `4` has `6` shaded cells.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Figure 5. -/
theorem compositionShade_four : compositionShade [4] = 6 := by decide

/-- The composition `1 + 3` has `3` shaded cells, all to the right of the bargraph.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Figure 5. -/
theorem compositionShade_one_three : compositionShade [1, 3] = 3 := by decide

/-- Each composition of `n` contributes its own shade: the total shade of the compositions of
`n` is at least the shade of any one of them; for example `c(4) ≥ 6`.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 2. -/
theorem compositionShade_le_totalCompositionShade {n : ℕ} (x : Composition n) :
    compositionShade x.blocks ≤ totalCompositionShade n :=
  Finset.single_le_sum (f := fun y : Composition n => compositionShade y.blocks)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

/-- The composition of `0` has no shade.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 2. -/
theorem totalCompositionShade_zero : totalCompositionShade 0 = 0 := by
  simp [totalCompositionShade, compositionShade]

/-- Blecher, Knopfmacher and Mays, Theorem 1: the generating function
`F(q) = ∑ c(n) qⁿ` of the total shade equals `DL(q) + DR(q)`, where `DL(q)` (shade between
successive left-to-right maxima of the skew image) and `DR(q)` (shade to the right of the
leftmost maximum) are the paper's displays (DL(q)) and (DR(q)).

Stated for real `0 < q < 1/4`, where all series converge absolutely; powers with possibly
negative exponents are `zpow`.  Corrected readings: in display (DL(q)) the duplicated outer
double sum `∑_{i₁} ∑_{s₁}` (and the left-hand side `L(x, q, u)`) is a typesetting slip; the
display is read as `DL(q) = ∑_{i₁} ∑_{s₁} …`, which reproduces the printed expansion
`2q⁶ + 6q⁷ + 24q⁸ + ⋯`.  In display (DR(q)) the product in the double sum over `m, j` runs over
`r ≠ j`, as in the paper's display (R) from which it is obtained by setting `x = 1`; with the
product over all `r` as printed, the coefficient of `q⁴` in `DR(q)` is `14` instead of the
printed `13`, and `DL + DR` no longer matches the total shade.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Theorem 1
(`jis-2024-24.5.6-thm-1`). -/
public theorem_wanted totalCompositionShade_generatingFunction {q : ℝ} (hq0 : 0 < q)
    (hq : q < 1 / 4) :
    let DL : ℝ :=
      ∑' i₁ : Set.Ici 1, ∑' s₁ : Set.Ici ((i₁ : ℕ) + 2),
        (1 / (1 - q)) ^ (((i₁ : ℕ) : ℤ) - 2) *
          (∏ r ∈ Finset.Icc 1 ((i₁ : ℕ) - 1), (1 - q ^ ((s₁ : ℕ) - r))) *
          q ^ ((((i₁ : ℕ) : ℤ) * ((i₁ : ℕ) - 1)) / 2 - (i₁ : ℕ) * (s₁ : ℕ)) *
        ∑ i₂ ∈ Finset.Icc ((i₁ : ℕ) + 2) ((s₁ : ℕ) + 1), ∑' s₂ : Set.Ici ((s₁ : ℕ) + 1),
          ∑ i₃ ∈ Finset.Icc ((i₁ : ℕ) + 1) (i₂ - 1), ∑ s₃ ∈ Finset.Icc i₃ ((s₁ : ℕ) - 1),
            q ^ ((i₃ : ℤ) * (s₁ : ℕ) + (s₂ : ℕ) + s₃ - ((i₃ : ℤ) + (i₃ : ℤ) ^ 2) / 2) *
              (1 / (1 - q)) ^ (i₂ - i₃) *
              (((s₁ : ℕ) - (s₃ : ℝ)) *
                  ∏ i ∈ Finset.Icc (i₃ + 1) (i₂ - 1), (1 - q ^ ((s₁ : ℕ) - i + 1)) +
                ∑ j ∈ Finset.Icc (i₃ + 1) (i₂ - 1),
                  (∏ i ∈ (Finset.Icc (i₃ + 1) (i₂ - 1)).erase j,
                      (1 - q ^ ((s₁ : ℕ) - i + 1))) *
                    ((j * (q - 1) + q ^ ((s₁ : ℕ) + 1 - j) + (s₁ : ℕ) -
                      q * (1 + (s₁ : ℕ))) / (1 - q))) *
              (1 + ∑' m : Set.Ici 1,
                q ^ (-((i₂ : ℤ) * (m : ℕ)) - (((m : ℕ) : ℤ) * ((m : ℕ) - 1)) / 2) *
                  (1 - q) ^ (-((m : ℕ) : ℤ)) *
                  q ^ ((((m : ℕ) : ℤ) * (1 + 2 * i₂ + (m : ℕ))) / 2))
    let DR : ℝ :=
      ∑' i : Set.Ici 1, ∑' s : Set.Ici (i : ℕ),
        (∏ r ∈ Finset.Icc 1 ((i : ℕ) - 1), (1 - q ^ ((s : ℕ) - r))) *
          (q ^ (s : ℕ) / (1 - q) ^ ((i : ℕ) - 1)) *
          ((((s : ℕ) - (i : ℕ) + 1).choose 2 : ℝ) *
              ∑ m ∈ Finset.range (s : ℕ),
                q ^ m / (1 - q) ^ m *
                  ∏ r ∈ Finset.Icc 1 m, (1 - q ^ (((s : ℕ) : ℤ) + 1 - (i : ℕ) - r)) +
            1 / (1 - q) ^ 2 *
              ∑ m ∈ Finset.Icc 1 ((s : ℕ) - 1), ∑ j ∈ Finset.Icc 1 m,
                q ^ m / (1 - q) ^ (m - 1) *
                  (∏ r ∈ (Finset.Icc 1 m).erase j,
                    (1 - q ^ (((s : ℕ) : ℤ) + 1 - (i : ℕ) - r))) *
                  (-1 - q ^ (1 - ((i : ℕ) : ℤ) - j + (s : ℕ)) *
                      (-2 + (i : ℕ) + j - (s : ℕ) : ℝ) +
                    q ^ (2 - ((i : ℕ) : ℤ) - j + (s : ℕ)) * (-1 + (i : ℕ) + j - (s : ℕ) : ℝ)))
    ∑' n : ℕ, (totalCompositionShade n : ℝ) * q ^ n = DL + DR

end

end MetaMathlibExt
