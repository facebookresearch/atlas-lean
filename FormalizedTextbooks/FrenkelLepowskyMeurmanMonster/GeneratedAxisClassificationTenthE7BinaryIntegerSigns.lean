/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardSignFiber

/-! Exact integer signs for the original binary Golay phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The ordinary integer sign attached to an actual binary coordinate. -/
def generatedTenthE7IntegerSign (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

/-- Addition of the complete original binary phases multiplies their integer signs. -/
theorem generatedTenth_e7_integer_sign_add : ∀ a b : ZMod 2,
    generatedTenthE7IntegerSign (a + b) =
      generatedTenthE7IntegerSign a * generatedTenthE7IntegerSign b := by
  decide +kernel

/-- An actual integer sign determines its entire original binary phase. -/
theorem generatedTenth_e7_integer_sign_injective :
    Function.Injective generatedTenthE7IntegerSign := by
  decide +kernel

/-- The entire signed four-coordinate equation is exactly its binary phase equation. -/
theorem generatedTenth_e7_four_sign_phase : ∀ c a b e : ZMod 2,
    (if c = 0 then 4 * generatedTenthE7IntegerSign b
      else -(4 * generatedTenthE7IntegerSign b)) =
        generatedTenthE7IntegerSign e * (4 * generatedTenthE7IntegerSign a) ↔
      c + b = e + a := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
