/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BronzeMetallicIdentities

open MetaMathlibExt

-- At index zero both companions start at 1, but their next terms are 1 and 2.
example :
    (3 + Real.sqrt 13) / 2 = 1 + (13 + Real.sqrt 13) / (2 * Real.sqrt 13) ∧
    (3 + Real.sqrt 13) / 2 = 2 + (13 - Real.sqrt 13) / (2 * Real.sqrt 13) := by
  obtain ⟨_, hC, hD, _⟩ := bronze_mul_metallic_identities 0
  simpa [bronzeCompanionFirst, bronzeCompanionSecond, lucasU, bronzeLucasParams]
    using And.intro hC hD

-- For k = 1 the mixed sum is B₃ + C₄ = 53 and the target term is D₄ = 76.
example : (53 : ℝ) * ((5 + Real.sqrt 13) / 6) =
    76 + (65 - 17 * Real.sqrt 13) / (6 * Real.sqrt 13) * ((Real.sqrt 13 - 3) / 2) ^ 2 := by
  exact (bronze_mul_metallic_identities 1).2.2.2.2.1
