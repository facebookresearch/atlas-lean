/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.LucasSequenceDivisibilityGcdLucasUTwoMulDivPEqOne

@[expose] public section

namespace MathlibExtTest.NumberTheory.Recurrences.LucasSequenceDivisibilityGcdLucasUTwoMulDivPEqOne

public theorem gcd_lucasU_two_mul_div_p_three_one_one :
    Int.gcd (MetaMathlibExt.lucasU ⟨3, 1, by decide⟩ (2 * 1) / 3) 3 = 1 :=
  MetaMathlibExt.gcd_lucasU_two_mul_div_p_eq_one _ (by decide) (by decide) _ (by decide)
    (by decide)

public theorem quotient_three_one_one :
    MetaMathlibExt.lucasU ⟨3, 1, by decide⟩ (2 * 1) / 3 = 1 := by
  decide

public theorem gcd_lucasU_two_mul_div_p_two_one_three :
    Int.gcd (MetaMathlibExt.lucasU ⟨2, 1, by decide⟩ (2 * 3) / 2) 2 = 1 :=
  MetaMathlibExt.gcd_lucasU_two_mul_div_p_eq_one _ (by decide) (by decide) _ (by decide)
    (by decide)

public theorem quotient_two_one_three :
    MetaMathlibExt.lucasU ⟨2, 1, by decide⟩ (2 * 3) / 2 = 3 := by
  decide

public theorem gcd_lucasU_two_mul_div_p_fibonacci_two :
    Int.gcd (MetaMathlibExt.lucasU ⟨1, -1, by decide⟩ (2 * 2) / 1) 1 = 1 :=
  MetaMathlibExt.gcd_lucasU_two_mul_div_p_eq_one _ (by decide) (by decide) _ (by decide)
    (by decide)

public theorem quotient_fibonacci_two :
    MetaMathlibExt.lucasU ⟨1, -1, by decide⟩ (2 * 2) / 1 = 3 := by
  decide

end MathlibExtTest.NumberTheory.Recurrences.LucasSequenceDivisibilityGcdLucasUTwoMulDivPEqOne
