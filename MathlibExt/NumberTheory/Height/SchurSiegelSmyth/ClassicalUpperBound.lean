/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.SchurSiegelSmyth
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Trace.Basic

/-!
# Classical upper bound for the Schur–Siegel–Smyth trace constant

For odd primes `p`, the cyclotomic integers `2 + ζ + ζ⁻¹` have distinct absolute traces
`2 - 2 / (p - 1)` below two. They give the classical upper bound for the trace constant.
-/

namespace MathlibExt.NumberTheory.SchurSiegelSmyth

open Polynomial IntermediateField Module

private theorem absoluteTrace_embedding {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (σ : K →ₐ[ℚ] ℂ) (x : K) :
    absoluteTrace (σ x) = (Algebra.trace ℚ K x : ℝ) / finrank ℚ K := by
  have hx := IsIntegral.of_finite ℚ x
  have ht := trace_eq_sum_roots (x := x)
    (IsAlgClosed.splits ((minpoly ℚ x).map (algebraMap ℚ ℂ)))
  have hd := finrank_mul_finrank ℚ ℚ⟮x⟯ K
  rw [adjoin.finrank hx] at hd
  rw [absoluteTrace, trace, conjugates, degree, minpoly.algHom_eq σ σ.injective]
  rw [← hd, Nat.cast_mul]
  have htr : (Algebra.trace ℚ K x : ℝ) =
      finrank ℚ⟮x⟯ K * ((minpoly ℚ x).aroots ℂ).sum.re := by
    simpa [nsmul_eq_mul, Complex.mul_re] using congrArg Complex.re ht
  rw [htr]
  have : (finrank ℚ⟮x⟯ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  field_simp

private theorem trace_primitiveRoot {p : ℕ} (hp : p.Prime) {K : Type*} [Field K]
    [Algebra ℚ K] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Algebra.trace ℚ K ζ = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : (cyclotomic p ℚ).natDegree = p - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
  have hp2 := hp.two_le
  rw [← hζ.powerBasis_gen ℚ, PowerBasis.trace_gen_eq_nextCoeff_minpoly, hζ.powerBasis_gen ℚ,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hp.pos),
    nextCoeff_of_natDegree_pos (by omega), hd, cyclotomic_prime, finsetSum_coeff]
  simp [coeff_X_pow, show p - 1 - 1 < p by omega]

private theorem exists_prime_witness {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    ∃ α : ℂ, IsTotallyPositive α ∧ absoluteTrace α = 2 - 2 / (p - 1 : ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let K := CyclotomicField p ℚ
  let : IsCyclotomicExtension {p} ℚ K :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let ζ : K := IsCyclotomicExtension.zeta p ℚ K
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ K
  let x : K := 2 + ζ + ζ⁻¹
  let σ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨σ x, ⟨?_, ?_⟩, ?_⟩
  · exact (((isIntegral_natCast (R := ℤ) 2).add (hζ.isIntegral hp.pos)).add
      (hζ.inv.isIntegral hp.pos)).map σ
  · intro β hβ
    rw [conjugates, minpoly.algHom_eq σ σ.injective] at hβ
    have hroot : β ∈ (minpoly ℚ x).rootSet ℂ := by simpa [rootSet] using hβ
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hroot
    obtain ⟨τ, rfl⟩ := hroot
    have hu : IsPrimitiveRoot (τ ζ) p := hζ.map_of_injective τ.injective
    have hnorm := hu.norm'_eq_one hp.ne_zero
    have hpos : 0 < ‖1 + τ ζ‖ ^ 2 := by
      apply sq_pos_of_ne_zero
      apply norm_ne_zero_iff.mpr
      intro heq
      apply hu.pow_ne_one_of_pos_of_lt two_ne_zero hp2
      rw [show τ ζ = -1 by linear_combination heq]
      norm_num
    rw [Complex.sq_norm, Complex.normSq_add] at hpos
    have hunit : Complex.normSq (τ ζ) = 1 := by rw [← Complex.sq_norm, hnorm, one_pow]
    simp [hunit] at hpos
    change (τ x).im = 0 ∧ 0 < (τ x).re
    simp [x, map_ofNat, Complex.inv_eq_conj hnorm]
    linarith
  · have htrace : Algebra.trace ℚ K x = finrank ℚ K * 2 - 2 := by
      change Algebra.trace ℚ K (algebraMap ℚ K 2 + ζ + ζ⁻¹) = _
      rw [map_add, map_add, Algebra.trace_algebraMap, trace_primitiveRoot hp hζ,
        trace_primitiveRoot hp hζ.inv, nsmul_eq_mul]
      ring
    rw [absoluteTrace_embedding, htrace, IsCyclotomicExtension.finrank K
      (cyclotomic.irreducible_rat hp.pos), Nat.totient_prime hp]
    push_cast [Nat.cast_sub hp.one_le]
    have : (p : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (p : ℤ) - 1 ≠ 0 by omega)
    field_simp

/-- **Classical upper bound for the Schur–Siegel–Smyth constant.** The Schur–Siegel–Smyth trace
constant $C_{86}$, an extended real number, satisfies $C_{86} \le 2$.

Source: classical upper bound `C₈₆ ≤ 2`, from the totally positive
algebraic integers `4 cos^2 (π / n)` whose absolute traces tend to
`2`. -/
public theorem classicalUpperBound_wanted :
    schurSiegelSmythConstant ≤ (2 : EReal) := by
  apply schurSiegelSmythConstant_le_iff.mpr
  intro c hc
  suffices c ≤ 2 by exact EReal.coe_le_coe this
  by_contra! h
  let f (p : ℕ) : ℝ := 2 - 2 / (p - 1 : ℝ)
  have hprimes := Nat.infinite_setOfPred_prime.sdiff (Set.finite_singleton 2)
  have hinj : Function.Injective f := by
    intro p q heq
    simpa [f, div_eq_mul_inv] using heq
  apply (hprimes.image hinj.injOn).not_finite
  apply (hc.2.image absoluteTrace).subset
  rintro _ ⟨p, ⟨hp, hp2⟩, rfl⟩
  have hodd : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  obtain ⟨α, hα, ht⟩ := exists_prime_witness hp hodd
  refine ⟨α, ⟨hα, ht ▸ ?_⟩, ht⟩
  have : 0 < (p : ℝ) - 1 := by exact_mod_cast (show 0 < (p : ℤ) - 1 by omega)
  linarith [div_pos two_pos this]

end MathlibExt.NumberTheory.SchurSiegelSmyth
