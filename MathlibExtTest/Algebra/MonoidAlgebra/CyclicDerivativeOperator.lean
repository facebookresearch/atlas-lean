/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MonoidAlgebra.CyclicDerivativeOperator

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

open MonoidAlgebra

-- `ofAdd 1` generates `Multiplicative (ZMod n)`.
private theorem ofAdd_one_generates (n : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) :
    g ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod n)) := by
  refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd g).val : ℤ), ?_⟩
  rw [← ofAdd_zsmul, zsmul_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

-- `ℓ = 3`: in `ℤ[C₄]`, `(σ - 1) (σ + 2σ² + 3σ³) = 4 - Tr`.
example :
    (of ℤ (Multiplicative (ZMod 4)) (Multiplicative.ofAdd 1) - 1) *
        ∑ i ∈ Finset.Icc (1 : ℕ) 3, (i : ℤ) •
          of ℤ (Multiplicative (ZMod 4)) (Multiplicative.ofAdd 1 ^ i) =
      ((3 + 1 : ℕ) : MonoidAlgebra ℤ (Multiplicative (ZMod 4))) -
        ∑ g : Multiplicative (ZMod 4), of ℤ (Multiplicative (ZMod 4)) g :=
  of_sub_one_mul_sum_Icc_smul_pow (ofAdd_one_generates 4) (by rw [Fintype.card_multiplicative, ZMod.card])

-- `ℓ = 1` over `ℚ`: the solutions of `(σ - 1) D = 2 - Tr` in `ℚ[C₂]` are `σ + c Tr`.
example (D : MonoidAlgebra ℚ (Multiplicative (ZMod 2))) :
    (of ℚ _ (Multiplicative.ofAdd (1 : ZMod 2)) - 1) * D =
        ((1 + 1 : ℕ) : MonoidAlgebra ℚ (Multiplicative (ZMod 2))) -
          ∑ g : Multiplicative (ZMod 2), of ℚ _ g ↔
      ∃ c : ℚ, D = ∑ i ∈ Finset.Icc (1 : ℕ) 1,
          (i : ℚ) • of ℚ _ (Multiplicative.ofAdd (1 : ZMod 2) ^ i) +
        c • ∑ g : Multiplicative (ZMod 2), of ℚ _ g :=
  of_sub_one_mul_eq_natCast_sub_sum_iff (ofAdd_one_generates 2) (by rw [Fintype.card_multiplicative, ZMod.card]) D

-- The trace spans the kernel of `σ - 1` in `ℤ[C₅]`.
example (x : MonoidAlgebra ℤ (Multiplicative (ZMod 5))) :
    (of ℤ _ (Multiplicative.ofAdd (1 : ZMod 5)) - 1) * x = 0 ↔
      ∃ c : ℤ, x = c • ∑ g : Multiplicative (ZMod 5), of ℤ _ g :=
  of_sub_one_mul_eq_zero_iff (ofAdd_one_generates 5) x
