/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CSLibExt.Logics.Propositional.CNF.ResolutionWidth

/-!
# Ben-Sasson–Wigderson: short resolution proofs are narrow

The size-width relations of E. Ben-Sasson and A. Wigderson (*Short proofs are narrow —
resolution made simple*, J. ACM 48 (2001), 149-169, Section 3): a CNF formula `F` with a
small refutation has a refutation of small width. For tree-like refutations,
`w(F ⊢ 0) ≤ w(F) + log₂ S_T(F)` (Theorem 3.3), that is `S_T(F) ≥ 2 ^ (w(F ⊢ 0) - w(F))`
(Corollary 3.4); for general refutations, `w(F ⊢ 0) ≤ w(F) + O(√(n ln S(F)))` for formulas in
`n` variables (Theorem 3.5), so `S(F) = exp (Ω ((w(F ⊢ 0) - w(F)) ^ 2 / n))` (Corollary 3.6).
Exponential size lower bounds thus follow from linear width lower bounds for formulas of
bounded width, such as Tseitin formulas on expanders, the pigeonhole principle (after a
reduction) and random `3`-CNFs.

Refutations, sizes and widths are those of `CSLibExt.Logics.Propositional.CNF.ResolutionWidth`
(resolution with weakening, widths counting distinct literals).
-/

@[expose] public section

namespace MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted

open Cslib.Logic.PL Cslib.Logic.PL.CNF

/-- **Ben-Sasson–Wigderson for tree-like resolution.** If a CNF formula `φ` has a tree-like
refutation with `S` lines, then it has a resolution refutation of width at most
`w(φ) + log₂ S`, stated as `2 ^ width ≤ 2 ^ w(φ) · S` (E. Ben-Sasson and A. Wigderson, J. ACM 48
(2001), Theorem 3.3; equivalently Corollary 3.4, `S_T(φ) ≥ 2 ^ (w(φ ⊢ 0) - w(φ))`). -/
public theorem_wanted tree_refutation_narrow (φ : CNF) (t : ResolutionTree φ []) :
    ∃ π : List CNFClause, IsResolutionRefutation φ π ∧
      2 ^ derivationWidth π ≤ 2 ^ φ.maxClauseWidth * t.proofSize

/-- **Ben-Sasson–Wigderson for general resolution.** There is an absolute constant `c` such
that if a CNF formula `φ` in `n` variables has a resolution refutation with `S` lines, then it
has a refutation of width at most `w(φ) + c √(n ln S)` (E. Ben-Sasson and A. Wigderson, J. ACM
48 (2001), Theorem 3.5; equivalently Corollary 3.6,
`S(φ) = exp (Ω ((w(φ ⊢ 0) - w(φ)) ^ 2 / n))`). -/
public theorem_wanted refutation_narrow :
    ∃ c : ℝ, 0 < c ∧ ∀ (φ : CNF) (π : List CNFClause), IsResolutionRefutation φ π →
      ∃ π' : List CNFClause, IsResolutionRefutation φ π' ∧
        (derivationWidth π' : ℝ) ≤
          φ.maxClauseWidth + c * Real.sqrt (φ.vars.card * Real.log π.length)

end MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted
