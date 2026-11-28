/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/NumberTheory/SmallHouse.lean` (leanprover/lean-eval),
problem `cyclotomic_integer_house_le_two` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The attribution applies to the theorem statement. The proof is new.
-/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.House
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Tactic.ComputeDegree

/-!
# Real cyclotomic integers with house at most two

The house of a totally real cyclotomic integer of house at most two is either two or
`2 * Real.cos (Real.pi / m)` for some positive integer `m`.
-/

namespace MathlibExt.NumberTheory.SmallHouseWanted.NumberTheory

open NumberField Polynomial
open scoped Real

-- A root of the reciprocal quadratic with real trace in [-2, 2] lies on the unit circle.
private theorem norm_re_of_quadratic {z : ℂ} {t : ℝ} (ht : |t| ≤ 2)
    (hz : z ^ 2 - (t : ℂ) * z + 1 = 0) : ‖z‖ = 1 ∧ 2 * z.re = t := by
  have hr : z.re * z.re - z.im * z.im - t * z.re + 1 = 0 := by
    simpa [sq, Complex.mul_re] using congrArg Complex.re hz
  have hi : z.re * z.im + z.im * z.re - t * z.im = 0 := by
    simpa [sq, Complex.mul_im] using congrArg Complex.im hz
  have htrace : 2 * z.re = t := by
    have hp : (2 * z.re - t) * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hp with h | h
    · linarith
    · rw [h] at hr
      have ht' := (sq_le_sq.mpr (show |t| ≤ |(2 : ℝ)| by simpa using ht))
      nlinarith [sq_nonneg (2 * z.re - t)]
  refine ⟨?_, htrace⟩
  rw [← htrace] at hr
  have hs := Complex.sq_norm z
  rw [Complex.normSq_apply] at hs
  nlinarith [norm_nonneg z]

-- Among the primitive m-th roots, the one with angle 2π/m maximizes the real part.
private theorem re_le_cos_of_primitive {m : ℕ} (hm : 1 < m) {z : ℂ}
    (hz : IsPrimitiveRoot z m) : z.re ≤ Real.cos (2 * π / m) := by
  obtain ⟨i, hi, hc, rfl⟩ := (Complex.isPrimitiveRoot_iff z m (by omega)).mp hz
  have hip : 1 ≤ i := by
    by_contra! h
    have : i = 0 := by omega
    simp [this] at hc
    omega
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let θ := 2 * π * i / m
  have hangle : (2 * (π : ℂ) * Complex.I * (i / m)) = (θ : ℂ) * Complex.I := by
    push_cast [θ]
    ring
  rw [hangle, Complex.exp_ofReal_mul_I_re]
  have hlow : 2 * π / m ≤ θ := by
    apply div_le_div_of_nonneg_right _ hm'.le
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ i by exact_mod_cast hip)
        (show 0 ≤ 2 * π by positivity))
  have hhigh : 2 * π / m ≤ 2 * π - θ := by
    unfold θ
    rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hm']
    have hib : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
    nlinarith [mul_le_mul_of_nonneg_left hib (show 0 ≤ 2 * π by positivity)]
  by_cases hθ : θ ≤ π
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hθ hlow
  · rw [← Real.cos_two_pi_sub θ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) hhigh

private theorem exists_embedding_exp {L : Type*} [Field L] [NumberField L]
    {z : L} {m : ℕ} (hm : 0 < m) (hz : IsPrimitiveRoot z m) :
    ∃ φ : L →+* ℂ, φ z = Complex.exp (2 * π * Complex.I / m) := by
  change Complex.exp _ ∈ Set.range (fun φ : L →+* ℂ ↦ φ z)
  rw [Embeddings.range_eval_eq_rootSet_minpoly, ← cyclotomic_eq_minpoly_rat hz hm,
    Polynomial.mem_rootSet, cyclotomic_eq_minpoly_rat (Complex.isPrimitiveRoot_exp m hm.ne') hm]
  exact ⟨minpoly.ne_zero ((Complex.isPrimitiveRoot_exp m hm.ne').isIntegral hm).tower_top,
    minpoly.aeval _ _⟩

private theorem exists_embedding_house {K L : Type*} [Field K] [Field L] [NumberField K]
    [Algebra K L] [FiniteDimensional K L] (β : K) :
    ∃ φ : L →+* ℂ, house β = ‖φ (algebraMap K L β)‖ := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun σ : K →+* ℂ ↦ ‖σ β‖₊)
  let _ := σ.toAlgebra
  let φ : L →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_⟩
  rw [house_eq_sup', hσ]
  change ‖σ β‖ = ‖φ (algebraMap K L β)‖
  rw [φ.commutes]
  rfl

-- Compute the extremal conjugate using the order of the root with trace β² - 2.
private theorem house_of_primitive_trace {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {β : K} {z : L} {m : ℕ}
    (hm : 0 < m) (hz : IsPrimitiveRoot z m)
    (htrace : ∀ φ : L →+* ℂ, ‖φ (algebraMap K L β)‖ ^ 2 = 2 + 2 * (φ z).re) :
    house β = 2 ∨ ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (π / m) := by
  obtain ⟨ψ, hψ⟩ := exists_embedding_house (L := L) β
  have hmax := htrace ψ
  rw [← hψ] at hmax
  rcases (show 1 ≤ m from hm).eq_or_lt with rfl | hlarge
  · have hz1 : z = 1 := by simpa using hz.pow_eq_one
    simp [hz1] at hmax
    left
    nlinarith [house_nonneg β]
  · obtain ⟨φ, hφ⟩ := exists_embedding_exp hm hz
    have hattain := htrace φ
    rw [hφ, show 2 * (π : ℂ) * Complex.I / m = (↑(2 * π / m : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_ofReal_mul_I_re] at hattain
    have hle := norm_embedding_le_house β (φ.comp (algebraMap K L))
    change ‖φ (algebraMap K L β)‖ ≤ house β at hle
    have hupper := re_le_cos_of_primitive hlarge (hz.map_of_injective ψ.injective)
    have hsq : house β ^ 2 = 2 + 2 * Real.cos (2 * π / m) := by
      apply le_antisymm
      · linarith
      · rw [← hattain]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [show 2 * π / m = 2 * (π / m) by ring, Real.cos_two_mul] at hsq
    have hc : 0 ≤ Real.cos (π / m) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · exact le_trans (by linarith [Real.pi_pos]) (by positivity : 0 ≤ π / m)
      · exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by exact_mod_cast hlarge)
    exact Or.inr ⟨m, hm, by nlinarith [house_nonneg β]⟩

private theorem classify_house {K : Type*} [Field K] [NumberField K] {β : K}
    (hβ_int : IsIntegral ℤ β) (hβ_real : β ∈ maximalRealSubfield K) (hb : house β ≤ 2) :
    house β = 2 ∨ ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (π / m) := by
  let b : 𝓞 K := ⟨β, hβ_int⟩
  let p : (𝓞 K)[X] := X ^ 2 - C (b ^ 2 - 2) * X + 1
  let q := p.map (algebraMap (𝓞 K) K)
  let L := q.SplittingField
  let _ : NumberField L := NumberField.of_module_finite K L
  have hp : p.Monic := by dsimp [p]; monicity!
  have hd : p.natDegree = 2 := by dsimp [p]; compute_degree!
  obtain ⟨z, hz⟩ := (IsSplittingField.splits L q).exists_eval_eq_zero (by
    apply degree_ne_of_natDegree_ne
    rw [Polynomial.natDegree_map, hp.natDegree_map, hd]
    decide)
  have hroot : aeval z p = 0 := by
    simpa only [q, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, eval_map, aeval_def] using hz
  have hint : IsIntegral ℤ z := isIntegral_trans z ⟨p, hp, hroot⟩
  have heq : z ^ 2 - ((algebraMap K L β) ^ 2 - 2) * z + 1 = 0 := by
    simpa only [p, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one, map_ofNat,
      IsScalarTower.algebraMap_apply (𝓞 K) K L b, show algebraMap (𝓞 K) K b = β from rfl]
      using hroot
  have hconj (φ : L →+* ℂ) :
      ‖φ z‖ = 1 ∧ ‖φ (algebraMap K L β)‖ ^ 2 = 2 + 2 * (φ z).re := by
    let σ := φ.comp (algebraMap K L)
    have hreal := Complex.conj_eq_iff_re.mp ((mem_maximalRealSubfield_iff β).mp hβ_real σ)
    have hbound := (norm_embedding_le_house β σ).trans hb
    have hnorm : ‖σ β‖ = |(σ β).re| := by
      conv_lhs => rw [← hreal, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hbound
    have he := congrArg φ heq
    simp only [map_add, map_sub, map_pow, map_mul, map_one, map_ofNat, map_zero] at he
    change (φ z) ^ 2 - ((σ β) ^ 2 - 2) * φ z + 1 = 0 at he
    have ht : |(σ β).re ^ 2 - 2| ≤ 2 := by
      have hs : (σ β).re ^ 2 ≤ (2 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using hbound)
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg (σ β).re], by linarith⟩
    have hquad := norm_re_of_quadratic (z := φ z) ht (by push_cast; rwa [hreal])
    change ‖φ z‖ = 1 ∧ ‖σ β‖ ^ 2 = _
    rw [hnorm, sq_abs]
    exact ⟨hquad.1, by linarith [hquad.2]⟩
  obtain ⟨k, hk, hzk⟩ := Embeddings.pow_eq_one_of_norm_eq_one L ℂ hint fun φ ↦ (hconj φ).1
  exact house_of_primitive_trace
    (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk, hzk⟩))
    (.orderOf z) fun φ ↦ (hconj φ).2

set_option linter.dupNamespace false in
/-- **Real cyclotomic integers with house at most 2.** Let $n \ge 1$, let $K$ be a number field
that is a cyclotomic extension of $\mathbb{Q}$ generated by the $n$-th roots of unity, and let
$\beta \in K$ be an algebraic integer lying in the maximal real subfield of $K$. Write
$\operatorname{house}(\beta)$ for the largest absolute value of the images of $\beta$ under the
complex embeddings of $K$. If $\operatorname{house}(\beta) \le 2$, then
$\operatorname{house}(\beta) = 2$ or $\operatorname{house}(\beta) = 2\cos(\pi/m)$ for some
integer $m \ge 1$.

Source: https://arxiv.org/pdf/1004.0665 Via leanprover/lean-eval@38361be, problem
`cyclotomic_integer_house_le_two`. -/
public theorem cyclotomic_integer_house_le_two
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K) :
    house β ≤ 2 →
      house β = 2 ∨ ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m) :=
  classify_house hβ_int hβ_real

end MathlibExt.NumberTheory.SmallHouseWanted.NumberTheory
