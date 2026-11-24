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

/-- **Shade of a composition.** Let $x = (x_0, x_1, \ldots, x_{k-1})$ be a finite list of
natural numbers (the parts of a composition), drawn as a bargraph whose column $c$ has height
$x_c$, with $x_c = 0$ for $c \ge k$. A cell $(c, h)$ with column $c \ge 0$ and height $h \ge 1$
is shaded when $h > x_c$ and $x_j \ge h + (c - j)$ for some column $j < c$. The shade of $x$
is the number of shaded cells.

Every shaded cell satisfies $c < k + s$ and $h \le s$, where $s = x_0 + \cdots + x_{k-1}$,
so the number of shaded cells is finite.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 1. -/
def compositionShade (x : List ℕ) : ℕ :=
  ∑ c ∈ Finset.range (x.length + x.sum), ∑ h ∈ Finset.Icc 1 x.sum,
    if x.getD c 0 < h ∧ ∃ j < c, h + (c - j) ≤ x.getD j 0 then 1 else 0

/-- **Total shade of compositions.** For a natural number $n$, the total shade $c(n)$ is the
sum of the shades of all compositions of $n$.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 2. -/
def totalCompositionShade (n : ℕ) : ℕ :=
  ∑ x : Composition n, compositionShade x.blocks

/-- **Shade of the composition 4.** The one-part composition $4$ has shade $6$: its
bargraph has $6$ shaded cells.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Figure 5. -/
theorem compositionShade_four : compositionShade [4] = 6 := by decide

/-- **Shade of the composition 1 + 3.** The composition $1 + 3$ has shade $3$: its bargraph
has $3$ shaded cells.

All three shaded cells lie to the right of the bargraph.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Figure 5. -/
theorem compositionShade_one_three : compositionShade [1, 3] = 3 := by decide

/-- **The total shade bounds the shade of each composition.** For every natural number $n$
and every composition $x$ of $n$, the shade of $x$ is at most the total shade $c(n)$ of the
compositions of $n$.

For example, since the composition $4$ has shade $6$, this gives $c(4) \ge 6$.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 2. -/
theorem compositionShade_le_totalCompositionShade {n : ℕ} (x : Composition n) :
    compositionShade x.blocks ≤ totalCompositionShade n :=
  Finset.single_le_sum (f := fun y : Composition n => compositionShade y.blocks)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

/-- **Total shade of the compositions of zero.** The total shade $c(0)$ of the compositions
of $0$ is zero: $c(0) = 0$.

The only composition of $0$ is the empty one, whose bargraph has no shaded cells.

Source: Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of
Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Section 2. -/
theorem totalCompositionShade_zero : totalCompositionShade 0 = 0 := by
  simp [totalCompositionShade, compositionShade]

/-- **Generating function for the total shade of compositions.** Let $c(n)$ be the total
shade of the compositions of $n$, and let $q$ be a real number with $0 < q < 1/4$. For natural
numbers $i_2, i_3, s_1, s_3$ put
$$A_{i_2, i_3, s_1, s_3} = (s_1 - s_3) \prod_{i_3 < i < i_2} (1 - q^{s_1 - i + 1}) +
\sum_{i_3 < j < i_2} \Big( \prod_{i_3 < i < i_2, i \ne j} (1 - q^{s_1 - i + 1}) \Big)
\frac{j(q - 1) + q^{s_1 + 1 - j} + s_1 - q(1 + s_1)}{1 - q},$$
$$B_{i_2} = 1 + \sum_{m \ge 1} q^{-i_2 m - m(m - 1)/2} (1 - q)^{-m} q^{m(1 + 2 i_2 + m)/2},$$
and for natural numbers $i, j, s$ put
$$E_{i, j, s} = -1 - q^{1 - i - j + s} (-2 + i + j - s) + q^{2 - i - j + s} (-1 + i + j - s).$$
Let
$$D_L(q) = \sum_{i_1 \ge 1} \sum_{s_1 \ge i_1 + 2} \Big( \frac{1}{1 - q} \Big)^{i_1 - 2}
\Big( \prod_{r=1}^{i_1 - 1} (1 - q^{s_1 - r}) \Big) q^{i_1 (i_1 - 1)/2 - i_1 s_1}
\sum_{i_2 = i_1 + 2}^{s_1 + 1} \sum_{s_2 \ge s_1 + 1} \sum_{i_3 = i_1 + 1}^{i_2 - 1}
\sum_{s_3 = i_3}^{s_1 - 1} q^{i_3 s_1 + s_2 + s_3 - (i_3 + i_3^2)/2}
\Big( \frac{1}{1 - q} \Big)^{i_2 - i_3} A_{i_2, i_3, s_1, s_3} B_{i_2},$$
$$D_R(q) = \sum_{i \ge 1} \sum_{s \ge i} \Big( \prod_{r=1}^{i-1} (1 - q^{s - r}) \Big)
\frac{q^s}{(1 - q)^{i-1}} \Big( \binom{s - i + 1}{2} \sum_{m=0}^{s-1} \frac{q^m}{(1 - q)^m}
\prod_{r=1}^{m} (1 - q^{s + 1 - i - r}) +
\frac{1}{(1 - q)^2} \sum_{m=1}^{s-1} \sum_{j=1}^{m} \frac{q^m}{(1 - q)^{m-1}}
\Big( \prod_{1 \le r \le m, r \ne j} (1 - q^{s + 1 - i - r}) \Big) E_{i, j, s} \Big).$$
Then
$$\sum_{n \ge 0} c(n) q^n = D_L(q) + D_R(q).$$

Empty sums are $0$ and empty products are $1$; all exponents are integers and may be
negative. For $0 < q < 1/4$ all these series converge absolutely.

This is Theorem 1 of the paper with two corrected readings. In the paper's display for
$D_L(q)$ the outer double sum over $i_1, s_1$ (and the left-hand side $L(x, q, u)$) is
duplicated, a typesetting slip; reading it once reproduces the printed expansion
$2q^6 + 6q^7 + 24q^8 + \cdots$. In the display for $D_R(q)$ the product in the double sum
over $m, j$ runs over $r \ne j$, as in the paper's display (R) from which it is obtained by
setting $x = 1$; with the product over all $r$ as printed, the coefficient of $q^4$ in
$D_R(q)$ is $14$ instead of the printed $13$, and $D_L + D_R$ no longer matches the total
shade.

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
