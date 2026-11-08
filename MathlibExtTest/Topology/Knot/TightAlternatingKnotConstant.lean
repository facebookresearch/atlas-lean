/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Knot.TightAlternatingKnotConstant

@[expose] public section

namespace TightAlternatingKnotConstantTest

open MathlibExt.Topology.Knot.TightAlternatingKnot

/-- Zero is admissible and bounds the tight alternating knot constant
below. -/
example :
    IsAdmissibleAlternating 0 ∧
      (0 : EReal) ≤ tightAlternatingKnotConstant :=
  ⟨isAdmissibleAlternating_zero, zero_le_tightAlternatingKnotConstant⟩

/-- Admissible alternating constants lie below the tight alternating
knot constant, and admissibility propagates downward. -/
example {c c' : ℝ} (hc : IsAdmissibleAlternating c) (h0 : 0 ≤ c')
    (h : c' ≤ c) :
    IsAdmissibleAlternating c' ∧
      (c : EReal) ≤ tightAlternatingKnotConstant :=
  ⟨hc.of_le h0 h, le_tightAlternatingKnotConstant hc⟩

/-- Upper bounds on the tight alternating knot constant are checked
on admissible alternating constants. -/
example {b : EReal} :
    tightAlternatingKnotConstant ≤ b ↔
      ∀ c : ℝ, IsAdmissibleAlternating c → (c : EReal) ≤ b :=
  tightAlternatingKnotConstant_le_iff

/-- Link types in the alternating domain have finite, natural-valued
crossing numbers. -/
example {n : ℕ}
    {L : MathlibExt.Topology.Knot.Euclidean.ParametrizedLink n}
    (hL : L.AdmitsAlternatingDiagram) :
    L.crossingNumber < ⊤ ∧
      ∃ k : ℕ, L.crossingNumber = (k : ℕ∞) :=
  ⟨crossingNumber_lt_top_of_admitsAlternatingDiagram hL,
    exists_crossingNumber_eq_natCast_of_admitsAlternatingDiagram hL⟩

end TightAlternatingKnotConstantTest
