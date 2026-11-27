/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomidIndex
import MathlibExt.NumberTheory.BinomidAverage
import Mathlib.Data.Rat.Cast.Order

/-!
# Upper average of a binomid index

`IsBinomidIndex.binomidUpperAverage_eq_iSup` shows the upper average of a binomid index
equals the supremum of its initial averages.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 2
(`integers-2024-A53-lem-2`).
-/

namespace MetaMathlibExt

namespace IsBinomidIndex

/-- **The upper average of a binomid index is the supremum of its averages.** Let $\eta$ be a
binomid index, let $s_i$ be the sum of its first $i$ entries, let $A_{i,0}(\eta) = s_i / i$ for
$i \ge 1$, and let $A_0(\eta) = \limsup_{i \to \infty} A_{i,0}(\eta)$ be its upper average.
Then, in the extended real numbers, $A_0(\eta) = \sup_{i \ge 1} A_{i,0}(\eta)$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 2
(`integers-2024-A53-lem-2`). -/
public theorem binomidUpperAverage_eq_iSup {η : ℕ → ℕ}
    (hη : IsBinomidIndex η) :
    binomidUpperAverage η = ⨆ i : ℕ, ⨆ (_ : 1 ≤ i), ((binomidAverage η i : ℝ) : EReal) := by
  have mono {a b : ℚ} (h : a ≤ b) : ((a : ℝ) : EReal) ≤ ((b : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (Rat.cast_le.mpr h)
  rw [binomidUpperAverage, Filter.limsup_eq_iInf_iSup_of_nat]
  apply le_antisymm
  · exact iInf_le _ 1
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    apply le_iInf
    intro n
    have hle : binomidAverage η j ≤ binomidAverage η ((n + 1) * j) :=
      (hη.binomidAverage_props (i := j) (l := 1) hj le_rfl).2.1 (n + 1) (by omega)
    have hmn : (n + 1) * j ≥ n :=
      calc n ≤ n + 1 := Nat.le_succ n
        _ = (n + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (n + 1) * j := Nat.mul_le_mul_left _ hj
    refine (mono hle).trans ?_
    refine le_iSup_of_le ((n + 1) * j) ?_
    refine le_iSup_of_le hmn ?_
    exact le_rfl

end IsBinomidIndex

end MetaMathlibExt
