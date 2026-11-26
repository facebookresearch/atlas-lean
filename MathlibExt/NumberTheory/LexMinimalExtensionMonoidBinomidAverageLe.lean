/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LexMinimalExtensionMonoid
import MathlibExt.NumberTheory.BinomidPartialSum

/-!
# The largest average of a lex-minimal extension

`IsLexMinimalExtensionOf.binomidAverage_le` shows that the largest of the first `m` initial
averages of a lex-minimal extension bounds every initial average.

Statements from Caalim and Tanaka, *Generalized Binomial Coefficients and
the Monoid of Lexicographically Minimal Extensions*, INTEGERS 26 (2026),
Article A113 (preprint arXiv:2505.20018, whose text supplies the definitions).
-/

namespace MetaMathlibExt

namespace IsLexMinimalExtensionOf

/-- Beyond a nonempty prefix (`1 ≤ m < n`), the partial sum up to `n` is the sum of the
partial sums up to some positive `a` and `b` with `a + b = n`. -/
private theorem exists_split_eq {η : ℕ → ℕ} {m n : ℕ}
    (hη : IsLexMinimalExtensionOf η m) (hm : 1 ≤ m) (hn : m < n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = n ∧
      ∑ l ∈ Finset.range a, η l + ∑ l ∈ Finset.range b, η l =
        ∑ l ∈ Finset.range n, η l := by
  have hsup := (isBinomidIndex_iff_partialSum η).2 m hη n hn
  have hne : (Finset.Ico 1 n).Nonempty :=
    ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨k, hkmem, hkeq⟩ := Finset.exists_mem_eq_sup (Finset.Ico 1 n) hne
    fun k => ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i
  rw [Finset.mem_Ico] at hkmem
  obtain ⟨hklo, hkhi⟩ := hkmem
  refine ⟨n - k, k, by omega, by omega, Nat.sub_add_cancel (by omega), ?_⟩
  exact hkeq.symm.trans hsup.symm

/-- **The largest of the first $m$ averages is the largest average.** Let $m \ge 0$ and let
$\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of its first $m$ entries, with averages
$A_i = (e_1 + \dots + e_i)/i$ for $i \ge 1$. If $1 \le j \le m$ and
$A_j = \max \{A_i \mid 1 \le i \le m\}$, then $A_i \le A_j$ for every $i \ge 1$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 1 (`integers-2026-A113-lem-1`). -/
public theorem binomidAverage_le {η : ℕ → ℕ} {m : ℕ}
    (hη : IsLexMinimalExtensionOf η m) {i : ℕ} (hi : 1 ≤ i) {j : ℕ}
    (hj : j ∈ maxAverageIndices η m) :
    binomidAverage η i ≤ binomidAverage η j := by
  classical
  simp only [maxAverageIndices, Finset.mem_filter] at hj
  obtain ⟨hjmem, hbest⟩ := hj
  obtain ⟨hjlo, hjm⟩ := Finset.mem_Icc.mp hjmem
  have hm : 1 ≤ m := hjlo.trans hjm
  have bound : ∀ k : ℕ, 0 < k →
      ((∑ l ∈ Finset.range k, η l : ℕ) : ℚ) ≤ binomidAverage η j * k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      by_cases hkm : k ≤ m
      · have hmem := Finset.mem_Icc.mpr ⟨hk, hkm⟩
        have hk' : (0 : ℚ) < k := by exact_mod_cast hk
        exact (div_le_iff₀ hk').mp (hbest k hmem)
      · obtain ⟨a, b, ha, hb, rfl, hs⟩ := hη.exists_split_eq hm (lt_of_not_ge hkm)
        have ha' := ih a (by omega) ha
        have hb' := ih b (by omega) hb
        have hs' : ((∑ l ∈ Finset.range (a + b), η l : ℕ) : ℚ) =
            ((∑ l ∈ Finset.range a, η l : ℕ) : ℚ) +
              ((∑ l ∈ Finset.range b, η l : ℕ) : ℚ) := by
          exact_mod_cast hs.symm
        rw [hs', Nat.cast_add, mul_add]
        exact add_le_add ha' hb'
  have hi' : (0 : ℚ) < i := by exact_mod_cast (show 0 < i from hi)
  exact (div_le_iff₀ hi').mpr (bound i (by omega))

end IsLexMinimalExtensionOf

end MetaMathlibExt
