/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MetaMathlibExt

/-- **Rosser's lower bound for the $n$th prime.** For every positive integer $n$, the $n$th prime
$p_n$ (counting from $p_1 = 2$) satisfies $p_n > n \log n$.

For $n = 1$ the bound reads $2 > 0$.

Source: Christian Axler, "New Estimates for the nth Prime Number",
Journal of Integer Sequences 22 (2019), Article 19.4.2, equation (1.3)
(label `1.3`), line 115, with Rosser's theorem stated at lines 115–120,
attributed there to Rosser,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Axler/axler17.tex>. -/
theorem_wanted rosser_nthPrime_lower_bound_zeroBased (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) < (Nat.nth Nat.Prime k : ℝ)

end MetaMathlibExt
