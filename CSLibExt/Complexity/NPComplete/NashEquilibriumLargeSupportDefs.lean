/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NASH EQUILIBRIUM WITH LARGE SUPPORTS: definitions

Source:
V. Bilò and M. Mavronicolas, "The complexity of computational problems about Nash equilibria
in symmetric win-lose games", Algorithmica 83 (2021), 447-530, doi:10.1007/s00453-020-00763-6,
arXiv:1907.10468 (§2.3: ∃ NASH WITH LARGE SUPPORTS; Theorem 7.1: NP-complete already for symmetric
win-lose bimatrix games; §2.3: membership in NP for bimatrix games);
I. Gilboa and E. Zemel, "Nash and correlated equilibria: some complexity considerations",
Games and Economic Behavior 1 (1989), 80-93, doi:10.1016/0899-8256(89)90006-7;
V. Conitzer and T. Sandholm, "New complexity results about Nash equilibria", Games and
Economic Behavior 63 (2008), 621-641, doi:10.1016/j.geb.2008.02.015.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.MixedNashExistence

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NashEquilibriumLargeSupport

open Convexity MathlibExt.GameTheory.MixedNashExistence

/-- A rational number `(a - b) / q`, given as `((a, b), q)`. -/
abbrev RatCode := (ℕ × ℕ) × ℕ

/-- The real value `(a - b) / q` of `((a, b), q)`. -/
noncomputable def ratValue (r : RatCode) : ℝ := ((r.1.1 : ℝ) - r.1.2) / r.2

/-- An instance: the numbers `m₁` and `m₂` of pure strategies, the payoff matrices `R` and `C`
(each a list of `m₁` rows of `m₂` entries), and the integer `k`. -/
abbrev NashEquilibriumLargeSupportInstance :=
  ℕ × ℕ × List (List RatCode) × List (List RatCode) × ℕ

/-- An `m₁ × m₂` matrix of rationals with positive denominators. -/
def IsMatrix (m₁ m₂ : ℕ) (M : List (List RatCode)) : Prop :=
  M.length = m₁ ∧ ∀ row ∈ M, row.length = m₂ ∧ ∀ q ∈ row, 0 < q.2

/-- Well-formedness of an instance: both players have at least one pure strategy, `R` and `C`
are `m₁ × m₂` matrices of rationals, and `k ≥ 1`. -/
def WellFormed (i : NashEquilibriumLargeSupportInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ IsMatrix i.1 i.2.1 i.2.2.1 ∧ IsMatrix i.1 i.2.1 i.2.2.2.1 ∧
    1 ≤ i.2.2.2.2

/-- The pure strategies of player `p` (`0` is player 1, `1` is player 2). -/
abbrev Strategy (i : NashEquilibriumLargeSupportInstance) (p : Fin 2) : Type :=
  Fin (if p = 0 then i.1 else i.2.1)

/-- The payoff of player `p` at the pure profile `a`: the entry of `R` (for player 1) or `C`
(for player 2) in row `a 0` and column `a 1`. -/
noncomputable def utility (i : NashEquilibriumLargeSupportInstance) (p : Fin 2)
    (a : ∀ q, Strategy i q) : ℝ :=
  ratValue (((if p = 0 then i.2.2.1 else i.2.2.2.1).getD (a 0) []).getD (a 1) ((0, 0), 1))

/-- Some mixed Nash equilibrium has supports of size at least `k` for both players (the support
of a mixed strategy is the set of pure strategies with positive probability). -/
def NashEquilibriumLargeSupportFeasible (i : NashEquilibriumLargeSupportInstance) :
    Prop :=
  ∃ σ : ∀ p, StdSimplex ℝ (Strategy i p), IsMixedNash (utility i) σ ∧
    ∀ p, i.2.2.2.2 ≤ (σ p).weights.support.card

open Classical in
/-- NASH EQUILIBRIUM WITH LARGE SUPPORTS as a decision problem over bitstrings. -/
noncomputable def nashEquilibriumLargeSupportDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NashEquilibriumLargeSupportInstance) x with
  | some i => decide (WellFormed i ∧ NashEquilibriumLargeSupportFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NashEquilibriumLargeSupport
