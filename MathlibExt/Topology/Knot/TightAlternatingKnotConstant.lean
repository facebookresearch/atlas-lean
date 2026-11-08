/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The tight alternating knot constant: ropelength versus crossing number
-/
module

public import Mathlib.Data.EReal.Basic
public import MathlibExt.Topology.Knot.RegularProjection

@[expose] public section

open MathlibExt.Topology.Knot.Euclidean

namespace MathlibExt.Topology.Knot.TightAlternatingKnot

/-- A real constant `c` is admissible for the tight alternating-knot
inequality when every oriented labeled link type that admits an
alternating diagram and whose crossing number is a finite natural
`k` has type ropelength at least `c * k`, with the inequality read in
`ℝ≥0∞`. On this domain the finite-crossing restriction costs
nothing: the alternating representative itself has a regular
projection, so every such type has finite crossing number
(`crossingNumber_lt_top_of_admitsAlternatingDiagram` below). -/
def IsAdmissibleAlternating (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ (n : ℕ) (L : ParametrizedLink n),
    L.AdmitsAlternatingDiagram → ∀ k : ℕ,
      L.crossingNumber = (k : ℕ∞) →
        ENNReal.ofReal c * (k : ENNReal) ≤ L.ropelength

/-- The tight alternating knot constant `C₂₂ᵦ = b₀`: the supremal
admissible constant for the linear inequality `L ≥ c * C` over link
types admitting an alternating diagram, without assuming that the
supremum is attained. -/
noncomputable def tightAlternatingKnotConstant : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c : ℝ | IsAdmissibleAlternating c})

/-- Zero is admissible. -/
theorem isAdmissibleAlternating_zero : IsAdmissibleAlternating 0 := by
  refine ⟨le_rfl, fun _ _ _ _ _ => ?_⟩
  simp

/-- Admissible alternating constants are downward closed above
zero. -/
theorem IsAdmissibleAlternating.of_le {c c' : ℝ}
    (hc : IsAdmissibleAlternating c) (h0 : 0 ≤ c') (h : c' ≤ c) :
    IsAdmissibleAlternating c' := by
  refine ⟨h0, fun n L hL k hk => ?_⟩
  calc
    ENNReal.ofReal c' * (k : ENNReal)
        ≤ ENNReal.ofReal c * (k : ENNReal) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl
    _ ≤ L.ropelength := hc.2 n L hL k hk

/-- Every admissible alternating constant is at most the tight
alternating knot constant. -/
theorem le_tightAlternatingKnotConstant {c : ℝ}
    (hc : IsAdmissibleAlternating c) :
    (c : EReal) ≤ tightAlternatingKnotConstant :=
  le_sSup ⟨c, hc, rfl⟩

/-- The tight alternating knot constant is nonnegative. -/
theorem zero_le_tightAlternatingKnotConstant :
    (0 : EReal) ≤ tightAlternatingKnotConstant := by
  simpa using le_tightAlternatingKnotConstant isAdmissibleAlternating_zero

/-- An extended-real upper bound for the tight alternating knot
constant is exactly a bound for every admissible alternating real
constant. This is the characteristic elimination rule for proving
upper bounds on `tightAlternatingKnotConstant` without unfolding its
supremum definition. -/
theorem tightAlternatingKnotConstant_le_iff {b : EReal} :
    tightAlternatingKnotConstant ≤ b ↔
      ∀ c : ℝ, IsAdmissibleAlternating c → (c : EReal) ≤ b := by
  constructor
  · intro hb c hc
    exact (le_tightAlternatingKnotConstant hc).trans hb
  · intro hb
    apply sSup_le
    rintro x ⟨c, hc, rfl⟩
    exact hb c hc

/-- A link type admitting an alternating diagram has finite crossing
number: its alternating representative is itself a regular
projection. -/
theorem crossingNumber_lt_top_of_admitsAlternatingDiagram {n : ℕ}
    {L : ParametrizedLink n} (hL : L.AdmitsAlternatingDiagram) :
    L.crossingNumber < ⊤ := by
  obtain ⟨L', h', hreg, -⟩ := hL
  exact L.crossingNumber_lt_top_of_isotopic_of_isRegularProjection h' hreg

/-- A link type admitting an alternating diagram has a natural-number
crossing number. -/
theorem exists_crossingNumber_eq_natCast_of_admitsAlternatingDiagram
    {n : ℕ} {L : ParametrizedLink n}
    (hL : L.AdmitsAlternatingDiagram) :
    ∃ k : ℕ, L.crossingNumber = (k : ℕ∞) := by
  have hlt := crossingNumber_lt_top_of_admitsAlternatingDiagram hL
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  exact ⟨k, hk.symm⟩

end MathlibExt.Topology.Knot.TightAlternatingKnot
