/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.HeegnerIdealOrder
public import MathlibExt.NumberTheory.NumberField.HeegnerIdeal

open NumberField nonZeroDivisors

-- The order of conductor `1` is the ring of integers.
example : orderOfConductor ℚ 1 = integralClosure ℤ ℚ :=
  orderOfConductor_one ℚ

-- The order of conductor `2` of `ℚ` is an order.
example : NumberField.IsOrder ℚ (orderOfConductor ℚ 2) :=
  isOrder_orderOfConductor ℚ two_ne_zero

-- Integers lie in every order of conductor `n`, and `n 𝓞 K ⊆ 𝒪_n`.
example : (3 : ℚ) ∈ orderOfConductor ℚ 5 :=
  mem_orderOfConductor.mpr ⟨3, 0, zero_mem _, by simp⟩

example : (5 : ℚ) * 7 ∈ orderOfConductor ℚ 5 := by
  exact_mod_cast natCast_mul_mem_orderOfConductor 5 ((integralClosure ℤ ℚ).natCast_mem 7)

-- The canonical map `ℤ → ZMod 6` is surjective, from cyclicity of `ZMod 6`.
example : Function.Surjective (Int.cast : ℤ → ZMod 6) :=
  IsAddCyclic.intCast_surjective (ZMod 6)

-- The main theorem for `K = ℚ`, `𝒩 = 𝓞 ℚ`, `N = 1` and `n = 3`.
example : Nonempty (orderOfConductor ℚ 3 ⧸
      (⊤ : Ideal (𝓞 ℚ)).comap (orderOfConductor.toRingOfIntegers ℚ 3) ≃+* ZMod 1) ∧
    IsUnit (((⊤ : Ideal (𝓞 ℚ)).comap (orderOfConductor.toRingOfIntegers ℚ 3) :
      Ideal (orderOfConductor ℚ 3)) : FractionalIdeal (orderOfConductor ℚ 3)⁰ ℚ) := by
  have : Subsingleton (𝓞 ℚ ⧸ (⊤ : Ideal (𝓞 ℚ))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have : Nonempty (𝓞 ℚ ⧸ (⊤ : Ideal (𝓞 ℚ))) := ⟨0⟩
  exact orderOfConductor.nonempty_ringEquiv_zmod_and_isUnit inferInstance
    (Nat.card_unique (α := 𝓞 ℚ ⧸ (⊤ : Ideal (𝓞 ℚ)))) le_rfl (by norm_num)

-- The quotient statement needs no hypothesis on `n` and `N`: here `n = 0`, `𝒩 = ⊥` and `N = 0`.
example : Nonempty (orderOfConductor ℚ 0 ⧸
      (⊥ : Ideal (𝓞 ℚ)).comap (orderOfConductor.toRingOfIntegers ℚ 0) ≃+* ZMod 0) := by
  let e : 𝓞 ℚ ⧸ (⊥ : Ideal (𝓞 ℚ)) ≃+* ℤ :=
    (RingEquiv.quotientBot (𝓞 ℚ)).trans Rat.ringOfIntegersEquiv
  exact orderOfConductor.nonempty_quotient_ringEquiv_zmod 0
    (isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective)
    ((Nat.card_congr e.toEquiv).trans Nat.card_eq_zero_of_infinite)

-- The two results chain: under the Heegner hypothesis, the ideal `𝒩` of index `N` gives an
-- invertible ideal `𝒩 ∩ 𝒪_n` of index `N` in every order `𝒪_n` of conductor `n` prime to `N`.
example {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) {N : ℕ} (hN : 1 ≤ N)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ N → ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) {n : ℕ} (hcop : n.Coprime N) :
    ∃ 𝒩 : Ideal (𝓞 K),
      Nonempty (orderOfConductor K n ⧸ 𝒩.comap (orderOfConductor.toRingOfIntegers K n) ≃+*
        ZMod N) ∧
      IsUnit ((𝒩.comap (orderOfConductor.toRingOfIntegers K n) : Ideal (orderOfConductor K n)) :
        FractionalIdeal (orderOfConductor K n)⁰ K) := by
  obtain ⟨𝒩, hcyc, hcard⟩ :=
    RingOfIntegers.exists_ideal_isAddCyclic_quotient_of_heegnerHypothesis hK hN hsplit
  exact ⟨𝒩, orderOfConductor.nonempty_ringEquiv_zmod_and_isUnit hcyc hcard hN hcop⟩
