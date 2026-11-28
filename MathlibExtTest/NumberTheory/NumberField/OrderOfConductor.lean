/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderOfConductor

@[expose] public section

/-! Tests for `MathlibExt.NumberTheory.NumberField.OrderOfConductor`. -/

namespace NumberField.OrderOfConductorTest

#check @NumberField.orderOfConductor
#check @NumberField.mem_orderOfConductor
#check @NumberField.isOrder_orderOfConductor
#check @NumberField.orderOfConductor_one
#check @NumberField.comap_algebraMap_span_natCast
#check @NumberField.conductorIdeal_orderOfConductor
#check @NumberField.ker_intCastRingHom_quotient_orderOfConductor
#check @NumberField.quotientLift_intCastRingHom_bijective_orderOfConductor
#check @NumberField.natCard_units_quotient_orderOfConductor
#check @NumberField.index_orderOfConductor

-- `ℤ + 6𝒪_ℚ` is an order of `ℚ`, and `ℤ + 1𝒪_ℚ = 𝒪_ℚ`.
example : NumberField.IsOrder ℚ (NumberField.orderOfConductor ℚ 6) :=
  NumberField.isOrder_orderOfConductor 6 (by norm_num)

example : NumberField.orderOfConductor ℚ 1 = integralClosure ℤ ℚ :=
  NumberField.orderOfConductor_one

-- `7 = 1 + 6 · 1` lies in `ℤ + 6𝒪_K` for every number field `K`.
example (K : Type*) [Field K] [NumberField K] : (7 : K) ∈ NumberField.orderOfConductor K 6 :=
  NumberField.mem_orderOfConductor.mpr ⟨1, 1, one_mem _, by norm_num⟩

-- `6𝒪_K ∩ ℤ = 6ℤ`.
example (K : Type*) [Field K] [NumberField K] :
    (Ideal.span {((6 : ℕ) : integralClosure ℤ K)}).comap (algebraMap ℤ (integralClosure ℤ K)) =
      Ideal.span {((6 : ℕ) : ℤ)} :=
  NumberField.comap_algebraMap_span_natCast 6

-- For every number field `K` of degree `n ≥ 2`, the order `ℤ + 6𝒪_K` has conductor `6𝒪_K` and
-- index `6 ^ (n - 1)`, and the unit group of `(ℤ + 6𝒪_K) / 6𝒪_K ≅ ℤ/6ℤ` has `φ(6) = 2` elements.
example (K : Type*) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K) :
    ((NumberField.orderOfConductor K 6).comap (integralClosure ℤ K).val).conductorIdeal =
      Ideal.span {((6 : ℕ) : integralClosure ℤ K)} :=
  NumberField.conductorIdeal_orderOfConductor 6 hK

-- At `f = 0` the subring `ℤ + 0 · 𝒪_K` is the image of `ℤ`, which is not an order when the
-- degree is at least `2`; its conductor in `𝒪_K` is still defined, and it is the zero ideal.
example (K : Type*) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K) :
    ((NumberField.orderOfConductor K 0).comap (integralClosure ℤ K).val).conductorIdeal = ⊥ := by
  rw [NumberField.conductorIdeal_orderOfConductor 0 hK, Nat.cast_zero,
    Ideal.span_singleton_eq_bot]

example (K : Type*) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K) :
    ((NumberField.orderOfConductor K 6).comap
      (integralClosure ℤ K).val).toSubmodule.toAddSubgroup.index =
      6 ^ (Module.finrank ℚ K - 1) :=
  NumberField.index_orderOfConductor 6 (by norm_num) hK

/-- `φ(6) = 2`. -/
theorem totient_six : Nat.totient 6 = 2 := by decide

example (K : Type*) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K) :
    Nat.card ((NumberField.orderOfConductor K 6) ⧸
      (((NumberField.orderOfConductor K 6).comap (integralClosure ℤ K).val).conductorIdeal.comap
        (Subalgebra.inclusion
          (NumberField.isOrder_orderOfConductor (K := K) 6 (by norm_num)).le_integralClosure)))ˣ =
      2 := by
  rw [NumberField.natCard_units_quotient_orderOfConductor 6 (by norm_num) hK, totient_six]

-- `ℤ/6ℤ → (ℤ + 6𝒪_K) / 6𝒪_K` is a ring isomorphism.
example (K : Type*) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K) :
    Function.Bijective (Ideal.Quotient.lift (Ideal.span {((6 : ℕ) : ℤ)})
      (Int.castRingHom ((NumberField.orderOfConductor K 6) ⧸
        (((NumberField.orderOfConductor K 6).comap (integralClosure ℤ K).val).conductorIdeal.comap
          (Subalgebra.inclusion
            (NumberField.isOrder_orderOfConductor (K := K) 6 (by norm_num)).le_integralClosure))))
      fun _ ha => RingHom.mem_ker.mp
        ((NumberField.ker_intCastRingHom_quotient_orderOfConductor 6 (by norm_num) hK).ge ha)) :=
  NumberField.quotientLift_intCastRingHom_bijective_orderOfConductor 6 (by norm_num) hK

end NumberField.OrderOfConductorTest

end
