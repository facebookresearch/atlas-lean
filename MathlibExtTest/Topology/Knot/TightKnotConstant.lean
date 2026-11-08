/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Knot.TightKnotConstant

@[expose] public section

namespace TightKnotConstantTest

open MathlibExt.Topology.Knot.TightKnot

/-- Zero is admissible and bounds the tight knot constant below. -/
example : IsAdmissible 0 ∧ (0 : EReal) ≤ tightKnotConstant :=
  ⟨isAdmissible_zero, zero_le_tightKnotConstant⟩

/-- Admissible constants lie below the tight knot constant, and
admissibility propagates downward. -/
example {c c' : ℝ} (hc : IsAdmissible c) (h0 : 0 ≤ c') (h : c' ≤ c) :
    IsAdmissible c' ∧ (c : EReal) ≤ tightKnotConstant :=
  ⟨hc.of_le h0 h, le_tightKnotConstant hc⟩

/-- Upper bounds on the tight knot constant are checked on admissible
constants. -/
example {b : EReal} :
    tightKnotConstant ≤ b ↔
      ∀ c : ℝ, IsAdmissible c → (c : EReal) ≤ b :=
  tightKnotConstant_le_iff

end TightKnotConstantTest
