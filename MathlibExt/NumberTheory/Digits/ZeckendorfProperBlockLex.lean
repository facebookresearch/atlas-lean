/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ZeckendorfProperBlockCount

/-!
# Lexicographic characterization of proper Zeckendorf blocks

## References

* Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025),
  Article A25, pp. 1–45, Definitions 15 and 17 and Lemma 8 (Section 3.3.1).
* Sungkon Chang, *The weak converse of Zeckendorf’s theorem*, Research in Number Theory
  7 (2021), Article 48, Definition 10, cited for the real Zeckendorf collection.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Descending lexicographic order.** For coefficient functions
$\varepsilon, \varepsilon' \colon \mathbb{N} \to \mathbb{N}$, $\varepsilon <_d \varepsilon'$
means that there is an index $k$ with $\varepsilon_k < \varepsilon'_k$ and
$\varepsilon_j = \varepsilon'_j$ for all $j < k$: at the smallest index where they differ,
$\varepsilon$ is smaller.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def DescLexLT (ε ε' : ℕ → ℕ) : Prop :=
  ∃ k, ε k < ε' k ∧ ∀ j, j < k → ε j = ε' j

-- The source's standing hypotheses and the vanishing assumption are not needed:
-- strict inequality already puts the first differing index at or above the block start.
set_option linter.unusedVariables false in
/-- **Proper blocks below a maximal block.** Let $L = (e_1, \dots, e_N)$ with $N \ge 2$ and
$e_1 \ne 0$, let $\varepsilon \colon \mathbb{N} \to \mathbb{N}$ and $b \in \mathbb{N}$ with
$\varepsilon_i = 0$ for all $i < b$, and let $\bar\beta$ be the maximal $L^*$-block starting at
index $b$. Then $\varepsilon <_d \bar\beta$ in the descending lexicographic order if and only if
there is $k \ge b$ such that the function equal to $\varepsilon_i$ for $i \le k$ and to $0$ for
$i > k$ is a proper $L^*$-block with support interval $[b, k]$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 8 (`integers-2025-A25-lem-8`; arXiv:2308.12872v1, Section 3.3). -/
public theorem descLexLT_maxLStarBlock_iff (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {ε : ℕ → ℕ} {b : ℕ} (hε : ∀ i, i < b → ε i = 0) :
    DescLexLT ε (maxLStarBlock L b) ↔
      ∃ k, b ≤ k ∧ IsProperLStarBlock L (fun i => if i ≤ k then ε i else 0) b k := by
  unfold DescLexLT IsProperLStarBlock
  constructor
  · rintro ⟨k, hk, hbefore⟩
    have hbk : b ≤ k := Nat.le_of_not_gt fun hkb => by
      simp [maxLStarBlock_of_lt hkb] at hk
    refine ⟨k, hbk, hbk, ?_, ?_, ?_⟩
    · intro i hi
      simpa only [ite_eq_left hi.le] using hbefore i hi
    · simpa using hk
    · intro i hi
      simp [not_le.mpr hi]
  · rintro ⟨k, _, _, hbefore, hk, _⟩
    refine ⟨k, by simpa using hk, ?_⟩
    intro i hi
    simpa only [ite_eq_left hi.le] using hbefore i hi

end

end MetaMathlibExt
