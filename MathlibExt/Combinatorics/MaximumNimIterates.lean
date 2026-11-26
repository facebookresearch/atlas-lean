/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import MathlibExt.Combinatorics.MaximumNimJosephus
import Mathlib.Logic.Function.Iterate

/-!
# Divergence of the Maximum Nim map iterates

Each application of the Maximum Nim map increases its argument by at least one, so its iterates
from any natural starting value tend to infinity.

## References

* Shoei Takahashi, Hikaru Manabe, and Ryohei Miyadera,
  [*Maximum Nim and the Josephus Problem*][tmm2024], INTEGERS 24 (2024), Article G5, pp. 1–16,
  Section 3, Definition 3.1 and Lemma 6(ii)–(iii).

[tmm2024]: https://math.colgate.edu/~integers/yg5/yg5.pdf
-/

namespace MetaMathlibExt

-- The hypothesis `2 ≤ k` matches the source; the one-step bound does not need it.
set_option linter.unusedVariables false in
/-- **Iterates of the Maximum Nim map $h_k$ tend to infinity.** Let $k \ge 2$ be a natural
number and let $h_k$ be the map $x \mapsto x + \lfloor x/(k-1) \rfloor + 1$ on the natural numbers.
For every natural number $x_0$, the iterates $h_k^p(x_0)$ tend to infinity as $p \to \infty$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 6(iii) (`integers-2024-G5-lem-6`). -/
public theorem maximumNimH_iterate_tendsto_atTop (k x₀ : ℕ) (hk : 2 ≤ k) :
    Filter.Tendsto (fun p => Nat.iterate (maximumNimH k) p x₀)
      Filter.atTop Filter.atTop := by
  have hstep (x : ℕ) : x + 1 ≤ maximumNimH k x := by
    unfold maximumNimH
    exact Nat.succ_le_succ (Nat.le_add_right _ _)
  have hle (p : ℕ) : p ≤ Nat.iterate (maximumNimH k) p x₀ := by
    induction p with
    | zero => exact Nat.zero_le _
    | succ p ih =>
      rw [Function.iterate_succ_apply']
      exact (Nat.succ_le_succ ih).trans (hstep _)
  exact Filter.tendsto_atTop_mono hle Filter.tendsto_id

end MetaMathlibExt
