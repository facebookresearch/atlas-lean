/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-369: For every eps > 0 and k >= 2, all large n admit k consecutive
n^eps-smooth integers in {1,...,n}.

As written this is trivially true (take {1,...,k} with n > k^{1/eps});
following the community formalization, the entry formalizes the
non-trivial location variant: the run lies in [n/2, n].
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Divisors
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.SmoothConsecutiveIntegersWanted

/-! Source record `EP-369`. -/

/-- [EP-369] Smooth runs of any length appear eventually, located in
`[n/2, n]`. Smoothness is via prime factors: every prime factor `p` of
each run element satisfies `p ≤ n^ε`. -/
def conjecture : Prop :=
  ∀ ε : Real, 0 < ε →
    ∀ k : Nat, 2 ≤ k →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∃ a : Nat, n / 2 ≤ a + 1 ∧ a + k ≤ n ∧
          ∀ j : Nat, j < k →
            ∀ p ∈ (a + 1 + j).primeFactors, (p : Real) ≤ (n : Real) ^ ε

/--
Resolved true: EP-369 as written is trivially true; the formalized [n/2,n]-location variant is
proved (Balog-Wooley 1998; Bober-Fretwell-Martin-Wooley 2020; Lean proof). Source: Lean proof of
EP-369 location variant (plby/lean-proofs),
https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos369.lean.
Moved from `OpenConjectures/NumberTheory/SmoothConsecutiveIntegers`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.SmoothConsecutiveIntegersWanted
