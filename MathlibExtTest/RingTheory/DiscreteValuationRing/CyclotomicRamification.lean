/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.CyclotomicRamification
public import MathlibExt.RingTheory.DiscreteValuationRing.IntegralClosureComplete
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for ramification of cyclotomic extensions of complete DVRs

The supporting lemmas are exercised at the trivial extension
`ℚ_[3] / ℚ_[3]` with `B = A = ℤ_[3]`, and the main theorem is exercised at
the genuine cyclotomic extension
`CyclotomicField 3 ℚ_[3] / ℚ_[3]` with `B` the integral closure of `ℤ_[3]`.
The key arithmetic input, that `ℚ_[3]` contains no primitive cube root of
unity, is proved from scratch: a cube root `u ∈ ℤ_[3]` would have
`u ≡ 1 (mod 3)`, so `δ = 1 - u` is divisible by `3`, while
`δ ^ 2 - 3 * δ + 3 = 0` gives `3 = δ * (3 - δ)`, forcing `3` to be a unit.
-/

open IsLocalRing
open Polynomial

/-- `ℚ_[3]` contains no primitive cube root of unity. -/
private theorem no_isPrimitiveRoot_three_of_padic_three :
    ∀ ω : ℚ_[3], ¬IsPrimitiveRoot ω 3 := by
  intro ω hω
  have hne : ω ≠ 1 := hω.ne_one (by norm_num)
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hint : IsIntegral ℤ_[3] ω :=
    ⟨X ^ 3 - C 1, monic_X_pow_sub_C 1 (by norm_num), by simp [h3]⟩
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hu3 : u ^ 3 = 1 := by
    apply FaithfulSMul.algebraMap_injective ℤ_[3] ℚ_[3]
    rw [map_pow, hu, map_one]; exact h3
  have hne1 : u ≠ 1 := by
    intro h; apply hne; rw [← hu, h, map_one]
  have hquad : u ^ 2 + u + 1 = 0 := by
    have h : (u - 1) * (u ^ 2 + u + 1) = 0 := by
      have h3' : u ^ 3 - 1 = 0 := by rw [hu3, sub_self]
      calc (u - 1) * (u ^ 2 + u + 1) = u ^ 3 - 1 := by ring
        _ = 0 := h3'
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne1)
  have hto : PadicInt.toZMod (p := 3) u = 1 := by
    have h0 : (PadicInt.toZMod (p := 3) u) ^ 2 +
        PadicInt.toZMod (p := 3) u + 1 = 0 := by
      have h := congrArg (PadicInt.toZMod (p := 3)) hquad
      simpa using h
    have hdec : ∀ a : ZMod 3, a ^ 2 + a + 1 = 0 → a = 1 := by decide
    exact hdec _ h0
  have hres : residue ℤ_[3] u = 1 := by
    apply (PadicInt.residueField (p := 3)).injective
    have hcomp : PadicInt.toZMod (p := 3) u =
        PadicInt.residueField (p := 3) (residue ℤ_[3] u) := by
      rw [PadicInt.toZMod_eq_residueField_comp_residue]
      rfl
    rw [← hcomp, hto]
    exact (map_one _).symm
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[3], 1 - u = 3 * w := by
    have hδmem : 1 - u ∈ maximalIdeal ℤ_[3] := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      rw [map_sub, map_one, hres, sub_self]
    rw [PadicInt.maximalIdeal_eq_span_p] at hδmem
    exact Ideal.mem_span_singleton.mp hδmem
  have hδeq : (1 - u) ^ 2 - 3 * (1 - u) + 3 = 0 := by linear_combination hquad
  have h1 : (1 : ℤ_[3]) = 3 * (w * (1 - w)) := by
    have h3ne : (3 : ℤ_[3]) ≠ 0 := by
      exact_mod_cast (show (3 : ℕ) ≠ 0 by norm_num)
    apply mul_left_cancel₀ h3ne
    calc 3 * 1 = 3 := mul_one _
      _ = (1 - u) * (3 - (1 - u)) := by linear_combination hδeq
      _ = 3 * w * (3 - 3 * w) := by rw [hw]
      _ = 3 * (3 * (w * (1 - w))) := by ring
  have hunit : IsUnit (3 : ℤ_[3]) :=
    isUnit_iff_exists.mpr
      ⟨w * (1 - w), h1.symm, by rw [mul_comm]; exact h1.symm⟩
  have hmem : (3 : ℤ_[3]) ∈ maximalIdeal ℤ_[3] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (maximalIdeal.isMaximal ℤ_[3]).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

/-- A rational cube root of unity is `1`, via the no-primitive-root lemma. -/
example (ζ : ℚ) (hζ : ζ ^ 3 = 1) : ζ = 1 := by
  have hno : ∀ ω : ℚ, ¬IsPrimitiveRoot ω 3 := by
    intro ω hω
    have hne : ω ≠ 1 := hω.ne_one (by norm_num)
    have hquad : ω ^ 2 + ω + 1 = 0 := by
      have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
        have h3' : ω ^ 3 - 1 = 0 := by rw [hω.pow_eq_one, sub_self]
        calc (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
          _ = 0 := h3'
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
    have hsq : (2 * ω + 1) ^ 2 = -3 := by linear_combination 4 * hquad
    have hnonneg : (0 : ℚ) ≤ (2 * ω + 1) ^ 2 := sq_nonneg _
    linarith
  exact pth_root_unity_eq_one_of_no_prim_root ℚ 3 hno ζ hζ

/-- The supporting lemmas at the trivial extension `ℚ_[3] / ℚ_[3]`:
a cube root of unity in `ℚ_[3]` is `1` and already lies in the base field. -/
example (η : ℚ_[3]) (hη : η ^ 3 = 1) :
    η = 1 ∧ ∃ ζ : ℚ_[3], algebraMap ℚ_[3] ℚ_[3] ζ = η := by
  have : Fintype (ResidueField ℤ_[3]) :=
    Fintype.ofEquiv (ZMod 3) (PadicInt.residueField (p := 3)).symm
  have : CharP (ResidueField ℤ_[3]) 3 := by
    rw [CharP.charP_iff_prime_eq_zero Nat.prime_three]
    apply (PadicInt.residueField (p := 3)).injective
    rw [map_natCast, ZMod.natCast_self, map_zero]
  have habsunram : Ideal.span {(3 : ℤ_[3])} = maximalIdeal ℤ_[3] :=
    (PadicInt.maximalIdeal_eq_span_p (p := 3)).symm
  have he : Ideal.ramificationIdx' (maximalIdeal ℤ_[3])
      (maximalIdeal ℤ_[3]) = 1 := by
    have hne_top : Ideal.map (algebraMap ℤ_[3] ℤ_[3])
        (maximalIdeal ℤ_[3]) ≠ ⊤ := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
      exact (maximalIdeal.isMaximal ℤ_[3]).ne_top
    have hne_bot : Ideal.map (algebraMap ℤ_[3] ℤ_[3])
        (maximalIdeal ℤ_[3]) ≠ ⊥ := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
      intro h
      exact IsDiscreteValuationRing.not_isField ℤ_[3]
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    have h := Ideal.ramificationIdx'_map_self_eq_one (p := maximalIdeal ℤ_[3])
      (R := ℤ_[3]) (S := ℤ_[3]) hne_top hne_bot
    simpa using h
  constructor
  · exact no_prim_pth_root_in_unramified_ext ℤ_[3] ℚ_[3] 3 ℚ_[3] ℤ_[3]
      habsunram he no_isPrimitiveRoot_three_of_padic_three η hη
  · exact unramified_pth_root_in_base ℤ_[3] ℚ_[3] 3 ℚ_[3] ℤ_[3] habsunram he
      η hη

/-- The integral closure of `ℤ_[3]` in `CyclotomicField 3 ℚ_[3]` is a DVR:
the instance is needed already to state `maximalIdeal B`. -/
private instance : IsDiscreteValuationRing
    ↥(integralClosure ℤ_[3] (CyclotomicField 3 ℚ_[3])) := by
  have : FiniteDimensional ℚ_[3] (CyclotomicField 3 ℚ_[3]) :=
    IsCyclotomicExtension.finiteDimensional {3} ℚ_[3] (CyclotomicField 3 ℚ_[3])
  have : Algebra.IsSeparable ℚ_[3] (CyclotomicField 3 ℚ_[3]) :=
    IsCyclotomicExtension.isSeparable {3} ℚ_[3] (CyclotomicField 3 ℚ_[3])
  exact IsIntegralClosure.isDiscreteValuationRing_of_isAdicComplete ℤ_[3] ℚ_[3]
    (CyclotomicField 3 ℚ_[3]) ↥(integralClosure ℤ_[3] (CyclotomicField 3 ℚ_[3]))

/-- The main theorem at `CyclotomicField 3 ℚ_[3] / ℚ_[3]`: adjoining a
primitive cube root of unity to `ℚ_[3]` is ramified. -/
example : Ideal.ramificationIdx' (maximalIdeal ℤ_[3])
    (maximalIdeal ↥(integralClosure ℤ_[3] (CyclotomicField 3 ℚ_[3]))) ≠ 1 := by
  have : FiniteDimensional ℚ_[3] (CyclotomicField 3 ℚ_[3]) :=
    IsCyclotomicExtension.finiteDimensional {3} ℚ_[3] (CyclotomicField 3 ℚ_[3])
  have : Algebra.IsSeparable ℚ_[3] (CyclotomicField 3 ℚ_[3]) :=
    IsCyclotomicExtension.isSeparable {3} ℚ_[3] (CyclotomicField 3 ℚ_[3])
  have : IsFractionRing ↥(integralClosure ℤ_[3] (CyclotomicField 3 ℚ_[3]))
      (CyclotomicField 3 ℚ_[3]) :=
    integralClosure.isFractionRing_of_finite_extension (A := ℤ_[3]) ℚ_[3]
      (CyclotomicField 3 ℚ_[3])
  have : Fintype (ResidueField ℤ_[3]) :=
    Fintype.ofEquiv (ZMod 3) (PadicInt.residueField (p := 3)).symm
  have : CharP (ResidueField ℤ_[3]) 3 := by
    rw [CharP.charP_iff_prime_eq_zero Nat.prime_three]
    apply (PadicInt.residueField (p := 3)).injective
    rw [map_natCast, ZMod.natCast_self, map_zero]
  have hno_prim : ∀ ζ : ℚ_[3], ζ ^ 3 = 1 → ζ = 1 := fun ζ hζ =>
    pth_root_unity_eq_one_of_no_prim_root ℚ_[3] 3
      no_isPrimitiveRoot_three_of_padic_three ζ hζ
  exact dvr_pth_root_ramified ℤ_[3] ℚ_[3] 3 hno_prim 3 (by norm_num)
    (by norm_num) (CyclotomicField 3 ℚ_[3])
    ↥(integralClosure ℤ_[3] (CyclotomicField 3 ℚ_[3]))
    (PadicInt.maximalIdeal_eq_span_p (p := 3)).symm

#print axioms dvr_pth_root_ramified
#print axioms no_prim_root_in_unramified_ext_of_base
#print axioms unramified_pth_root_in_base
