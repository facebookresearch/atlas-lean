/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 436, question 1
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem436Question1Wanted

/-! Source record `UM-00002119-Q001`. -/
/-- `r` is a `k`th power residue modulo `p` in the classical sense: a non-zero residue class
that is the `k`th power of a non-zero class (so a run of residues consists of units mod `p`). -/
def IsKthPowerResidue (k p r : ℕ) : Prop :=
  ∃ x : ZMod p, x ≠ 0 ∧ x ^ k = (r : ZMod p)

/-- `Λ(k, 2) = limsup_{p → ∞} r(k, 2, p)` is finite for every `k ≥ 2`: the least start of a pair
of consecutive `k`th power residues is eventually bounded, with `r` ranging over positive integers
(so `r ≥ 1`) and residues taken in the multiplicative group. -/
def conjecture : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ B : ℕ, ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → N ≤ p →
      ∃ r : ℕ, 1 ≤ r ∧ r ≤ B ∧ IsKthPowerResidue k p r ∧ IsKthPowerResidue k p (r + 1)

-- Carried source audit `UM-00002119-Q001` (see the Moved/ record).

/--
Resolved true: Hildebrand (Michigan Math. J. 38 (1991)) proved that Λ(k,2) is finite for every k
≥ 2: for all large p there is a pair of consecutive k-th power residues in [1, O_k(1)]
(erdosproblems.com/436, checked 2026-10-22). The page's remaining questions (Λ(k,3) for odd k ≥
5 and the growth rates) are not formalized here. Source: Adolf Hildebrand, On consecutive kth
power residues. II, Michigan Mathematical Journal 38 (1991), no. 2, 241–253,
https://doi.org/10.1307/mmj/1029004331; T. F. Bloom, Erdős Problem #436, erdosproblems.com,
https://www.erdosproblems.com/436. Moved from
`OpenConjectures/NumberTheory/ErdosProblem436Question1`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem436Question1Wanted
