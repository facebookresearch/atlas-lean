/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The tight knot constant: ropelength versus crossing number
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic
public import MathlibExt.Topology.Knot.RegularProjection

@[expose] public section

open MathlibExt.Topology.Knot.Euclidean

namespace MathlibExt.Topology.Knot.TightKnot

/-- A real constant `c` is admissible for the tight-knot inequality
when every oriented labeled link type whose crossing number is a
finite natural `k` has type ropelength at least `c * k ^ (3 / 4)`,
with the inequality read in `ℝ≥0∞`. Types whose crossing number is
`⊤` (no regular representative is known in this development) impose
no constraint; the classical generic-direction theorem, which rules
that case out, is not proved here. -/
def IsAdmissible (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ (n : ℕ) (L : ParametrizedLink n) (k : ℕ),
    L.crossingNumber = (k : ℕ∞) →
      ENNReal.ofReal c * ENNReal.ofReal ((k : ℝ) ^ (3 / 4 : ℝ)) ≤
        L.ropelength

/-- The tight knot constant `C₂₂ₐ`: the supremal admissible constant
for the inequality `L ≥ c * C ^ (3 / 4)` relating type ropelength to
crossing number, without assuming that the supremum is attained. -/
noncomputable def tightKnotConstant : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c : ℝ | IsAdmissible c})

/-- Zero is admissible. -/
theorem isAdmissible_zero : IsAdmissible 0 := by
  refine ⟨le_rfl, fun _ _ _ _ => ?_⟩
  simp

/-- Admissible constants are downward closed above zero. -/
theorem IsAdmissible.of_le {c c' : ℝ} (hc : IsAdmissible c)
    (h0 : 0 ≤ c') (h : c' ≤ c) : IsAdmissible c' := by
  refine ⟨h0, fun n L k hk => ?_⟩
  calc
    ENNReal.ofReal c' * ENNReal.ofReal ((k : ℝ) ^ (3 / 4 : ℝ))
        ≤ ENNReal.ofReal c * ENNReal.ofReal ((k : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl
    _ ≤ L.ropelength := hc.2 n L k hk

/-- Every admissible constant is at most the tight knot constant. -/
theorem le_tightKnotConstant {c : ℝ} (hc : IsAdmissible c) :
    (c : EReal) ≤ tightKnotConstant :=
  le_sSup ⟨c, hc, rfl⟩

/-- The tight knot constant is nonnegative. -/
theorem zero_le_tightKnotConstant : (0 : EReal) ≤ tightKnotConstant := by
  simpa using le_tightKnotConstant isAdmissible_zero

/-- An extended-real upper bound for the tight knot constant is
exactly a bound for every admissible real constant. This is the
characteristic elimination rule for proving upper bounds on
`tightKnotConstant` without unfolding its supremum definition. -/
theorem tightKnotConstant_le_iff {b : EReal} :
    tightKnotConstant ≤ b ↔
      ∀ c : ℝ, IsAdmissible c → (c : EReal) ≤ b := by
  constructor
  · intro hb c hc
    exact (le_tightKnotConstant hc).trans hb
  · intro hb
    apply sSup_le
    rintro x ⟨c, hc, rfl⟩
    exact hb c hc

end MathlibExt.Topology.Knot.TightKnot
