/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_WeierstrassCurve_Affine_Point_eq_zero_of_prime_smul_eq_zero_of_isNode.lean`
and
`P2M/Sol/S_WeierstrassCurve_Affine_Point_eq_zero_of_prime_smul_eq_zero_of_isNode.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace NodalTorsion


section defs

variable {K : Type*} {W : WeierstrassCurve K}

lemma e₁ : W.toAffine.a₁ = W.a₁ := rfl
lemma e₂ : W.toAffine.a₂ = W.a₂ := rfl
lemma e₃ : W.toAffine.a₃ = W.a₃ := rfl
lemma e₄ : W.toAffine.a₄ = W.a₄ := rfl
lemma e₆ : W.toAffine.a₆ = W.a₆ := rfl

end defs

variable {K : Type*} [Field K] {W : WeierstrassCurve K} {x₀ y₀ α : K}

structure NodalFrame (W : WeierstrassCurve K) (x₀ y₀ α : K) : Prop where
  he : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) = 0
  hFX : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0
  hFY : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0
  hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0

noncomputable def tc (W : WeierstrassCurve K) (x₀ y₀ α : K) : W.toAffine.Point → K
  | .zero => 1
  | .some x y _ => (y - y₀ - α * (x - x₀)) / (y - y₀ - (-W.a₁ - α) * (x - x₀))

lemma tc_zero : tc W x₀ y₀ α 0 = 1 := rfl

lemma tc_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    tc W x₀ y₀ α (.some x y h) = (y - y₀ - α * (x - x₀)) / (y - y₀ - (-W.a₁ - α) * (x - x₀)) := rfl

variable (hd : NodalFrame W x₀ y₀ α)
include hd

lemma factor_eq {x y : K} (h : W.toAffine.Equation x y) :
    (y - y₀ - α * (x - x₀)) * (y - y₀ - (-W.a₁ - α) * (x - x₀)) = (x - x₀) ^ 3 := by
  rw [equation_iff, e₁, e₂, e₃, e₄, e₆] at h
  linear_combination h - hd.he - (x - x₀) * hd.hFX - (y - y₀) * hd.hFY - (x - x₀) ^ 2 * hd.hα

lemma not_nonsingular_centre : ¬ W.toAffine.Nonsingular x₀ y₀ := by
  rw [nonsingular_iff', e₁, e₂, e₃, e₄]
  rintro ⟨-, h | h⟩
  · exact h hd.hFX
  · exact h hd.hFY

lemma factors_ne_zero {x y : K} (h : W.toAffine.Nonsingular x y) :
    y - y₀ - α * (x - x₀) ≠ 0 ∧ y - y₀ - (-W.a₁ - α) * (x - x₀) ≠ 0 := by
  have hfac := factor_eq hd h.left
  have hx0 : ∀ {u v : K}, u * v = (x - x₀) ^ 3 → u = 0 → x = x₀ := by
    intro u v huv hu
    rw [hu, zero_mul] at huv
    exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 3) (by norm_num)).mp huv.symm)
  constructor
  · intro hu
    have hx := hx0 hfac hu
    have hy : y = y₀ := by rw [hx, sub_self, mul_zero, sub_zero, sub_eq_zero] at hu; exact hu
    subst hx; subst hy
    exact not_nonsingular_centre hd h
  · intro hu
    rw [mul_comm] at hfac
    have hx := hx0 hfac hu
    have hy : y = y₀ := by rw [hx, sub_self, mul_zero, sub_zero, sub_eq_zero] at hu; exact hu
    subst hx; subst hy
    exact not_nonsingular_centre hd h

lemma eq_zero_of_tc_eq_one (hαβ : α ≠ -W.a₁ - α) (P : W.toAffine.Point)
    (hP : tc W x₀ y₀ α P = 1) : P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · exfalso
    obtain ⟨h1, h2⟩ := factors_ne_zero hd h
    rw [tc_some, div_eq_one_iff_eq h2] at hP
    have hx : x = x₀ := by
      have : (α - (-W.a₁ - α)) * (x - x₀) = 0 := by linear_combination -hP
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hαβ
      · exact sub_eq_zero.mp h0
    have hfac := factor_eq hd h.left
    rw [hx, sub_self] at hfac h1
    simp only [mul_zero, sub_zero, ne_eq] at hfac h1
    have : (y - y₀) * (y - y₀) = 0 := by simpa using hfac
    exact h1 (mul_self_eq_zero.mp this)

section Group

variable [DecidableEq K]

lemma tc_add (P Q : W.toAffine.Point) :
    tc W x₀ y₀ α (P + Q) = tc W x₀ y₀ α P * tc W x₀ y₀ α Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← zero_def, zero_add, tc_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← zero_def, add_zero, tc_zero, mul_one]
  obtain ⟨hA₁, hB₁⟩ := factors_ne_zero hd h₁
  obtain ⟨hA₂, hB₂⟩ := factors_ne_zero hd h₂
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    rw [add_of_Y_eq hx hy, tc_zero, tc_some, tc_some]
    rw [negY, e₁, e₃] at hy
    subst hx
    have eA : y₁ - y₀ - α * (x₁ - x₀) = -(y₂ - y₀ - (-W.a₁ - α) * (x₁ - x₀)) := by
      rw [hy]; linear_combination -hd.hFY
    have eB : y₁ - y₀ - (-W.a₁ - α) * (x₁ - x₀) = -(y₂ - y₀ - α * (x₁ - x₀)) := by
      rw [hy]; linear_combination -hd.hFY
    rw [eA, eB, eq_comm, div_mul_div_comm, div_eq_one_iff_eq]
    · ring
    · exact mul_ne_zero (neg_ne_zero.mpr hA₂) hB₂
  · rw [add_some hxy, tc_some, tc_some, tc_some]
    set L := W.toAffine.slope x₁ x₂ y₁ y₂ with hL
    set x₃ := W.toAffine.addX x₁ x₂ L with hx₃
    set μ := y₁ - L * x₁ with hμ
    have hcubic : (Cubic.mk (1 : K) (-L ^ 2 - W.a₁ * L + W.a₂)
        (2 * x₁ * L ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * L + (-W.a₁ * y₁ + W.a₄))
        (-x₁ ^ 2 * L ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * L - (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)))
        = Cubic.mk 1 (-(x₁ + x₂ + x₃)) (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) (-(x₁ * x₂ * x₃)) := by
      have key := addPolynomial_slope h₁.left h₂.left hxy
      rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, e₁, e₂, e₃, e₄, e₆] at key
      exact (Cubic.toPoly_injective _ _).mp key
    simp only [Cubic.mk.injEq, true_and] at hcubic
    obtain ⟨hv₁, hv₂, hv₃⟩ := hcubic
    set ν := L * x₀ + μ - y₀ with hν
    have hs₁ : -L ^ 2 - W.a₁ * L + (3 * x₀ + W.a₂) = -((x₁ - x₀) + (x₂ - x₀) + (x₃ - x₀)) := by
      linear_combination hv₁
    have hs₂ : -(2 * L + W.a₁) * ν
        = (x₁ - x₀) * (x₂ - x₀) + (x₁ - x₀) * (x₃ - x₀) + (x₂ - x₀) * (x₃ - x₀) := by
      linear_combination hv₂ + 2 * x₀ * hv₁ + L * hd.hFY + hd.hFX
    have hs₃ : -ν ^ 2 = -((x₁ - x₀) * (x₂ - x₀) * (x₃ - x₀)) := by
      linear_combination hv₃ + x₀ * hv₂ + x₀ ^ 2 * hv₁ + ν * hd.hFY + hd.he
    have hy₂ : y₂ = L * x₂ + μ := by
      by_cases hx : x₁ = x₂
      · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
        have := Y_eq_of_Y_ne h₁.left h₂.left hx hy
        rw [hμ, ← hx, this]; ring
      · have hL' : L * (x₁ - x₂) = y₁ - y₂ := by
          rw [hL, slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
        rw [hμ]
        linear_combination hL'
    have h₃' : W.toAffine.Nonsingular x₃ (W.toAffine.negAddY x₁ x₂ y₁ L) :=
      nonsingular_negAdd h₁ h₂ hxy
    obtain ⟨hA₃, hB₃⟩ := factors_ne_zero hd h₃'
    have hnegAddY : W.toAffine.negAddY x₁ x₂ y₁ L = L * x₃ + μ := by
      simp only [negAddY, hμ]; ring
    rw [hnegAddY] at hA₃ hB₃
    have hprodA : (L * x₁ + μ - y₀ - α * (x₁ - x₀)) * (L * x₂ + μ - y₀ - α * (x₂ - x₀))
        * (L * x₃ + μ - y₀ - α * (x₃ - x₀)) = ν ^ 3 := by
      linear_combination (L - α) ^ 3 * hs₃ - ((L - α) ^ 2 * ν) * hs₂ + ((L - α) * ν ^ 2) * hs₁
        + (ν ^ 2 * (L - α)) * hd.hα
    have hprodB : (L * x₁ + μ - y₀ - (-W.a₁ - α) * (x₁ - x₀))
        * (L * x₂ + μ - y₀ - (-W.a₁ - α) * (x₂ - x₀))
        * (L * x₃ + μ - y₀ - (-W.a₁ - α) * (x₃ - x₀)) = ν ^ 3 := by
      have hβ : (-W.a₁ - α) ^ 2 + W.a₁ * (-W.a₁ - α) - (3 * x₀ + W.a₂) = 0 := by
        linear_combination hd.hα
      linear_combination (L - (-W.a₁ - α)) ^ 3 * hs₃ - ((L - (-W.a₁ - α)) ^ 2 * ν) * hs₂
        + ((L - (-W.a₁ - α)) * ν ^ 2) * hs₁ + (ν ^ 2 * (L - (-W.a₁ - α))) * hβ
    have hy₁ : y₁ = L * x₁ + μ := by rw [hμ]; ring
    simp only [addY, negY, negAddY, e₁, e₃]
    rw [← hx₃, hy₂, hy₁]
    rw [hy₁] at hA₁ hB₁
    rw [hy₂] at hA₂ hB₂
    have eNum : -(L * (x₃ - x₁) + (L * x₁ + μ)) - W.a₁ * x₃ - W.a₃ - y₀ - α * (x₃ - x₀)
        = -(L * x₃ + μ - y₀ - (-W.a₁ - α) * (x₃ - x₀)) := by
      linear_combination -hd.hFY
    have eDen : -(L * (x₃ - x₁) + (L * x₁ + μ)) - W.a₁ * x₃ - W.a₃ - y₀ - (-W.a₁ - α) * (x₃ - x₀)
        = -(L * x₃ + μ - y₀ - α * (x₃ - x₀)) := by
      linear_combination -hd.hFY
    rw [eNum, eDen, neg_div_neg_eq, div_mul_div_comm, div_eq_div_iff hA₃ (mul_ne_zero hB₁ hB₂)]
    linear_combination hprodB - hprodA

lemma tc_nsmul (P : W.toAffine.Point) (n : ℕ) :
    tc W x₀ y₀ α (n • P) = tc W x₀ y₀ α P ^ n := by
  induction n with
  | zero => rw [zero_smul, tc_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, tc_add hd, ih, pow_succ]

theorem eq_zero_of_prime_smul_eq_zero (hαβ : α ≠ -W.a₁ - α) {p : ℕ}
    [Fact p.Prime] [CharP K p] (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 := by
  apply eq_zero_of_tc_eq_one hd hαβ
  have h : tc W x₀ y₀ α P ^ p = 1 := by rw [← tc_nsmul hd, hP, tc_zero]
  have : (tc W x₀ y₀ α P - 1) ^ p = 0 := by rw [sub_pow_char, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp this)


end Group

omit hd in
lemma exists_frame {k : Type*} [Field k] (W : WeierstrassCurve k) (x₀ y₀ : k)
    (he : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀)
    (hnode : W.b₂ + 12 * x₀ ≠ 0) {K : Type*} [Field K] [IsAlgClosed K] (f : k →+* K)
    (hf : Function.Injective f) :
    ∃ α : K, NodalFrame (W.map f) (f x₀) (f y₀) α ∧ α ≠ -(W.map f).a₁ - α := by
  rw [nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hFX, hFY⟩ := hs he
  rw [equation_iff] at he
  obtain ⟨α, hα⟩ : ∃ α : K, α ^ 2 + f W.a₁ * α - (3 * f x₀ + f W.a₂) = 0 := by
    let q : Polynomial K := Polynomial.X ^ 2 + Polynomial.C (f W.a₁) * Polynomial.X
      - Polynomial.C (3 * f x₀ + f W.a₂)
    have hq : q.degree = 2 := by
      simp only [q]
      compute_degree!
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root q (by rw [hq]; norm_num)
    refine ⟨α, ?_⟩
    simpa [q] using hα
  refine ⟨α, ⟨?_, ?_, ?_, hα⟩, ?_⟩
  · change f y₀ ^ 2 + f W.a₁ * f x₀ * f y₀ + f W.a₃ * f y₀
      - (f x₀ ^ 3 + f W.a₂ * f x₀ ^ 2 + f W.a₄ * f x₀ + f W.a₆) = 0
    have := congrArg f he
    simp only [_root_.map_add, _root_.map_mul, _root_.map_pow] at this
    exact sub_eq_zero.mpr this
  · change f W.a₁ * f y₀ - (3 * f x₀ ^ 2 + 2 * f W.a₂ * f x₀ + f W.a₄) = 0
    have := congrArg f hFX
    simpa only [_root_.map_sub, _root_.map_mul, _root_.map_add, _root_.map_pow, map_ofNat,
      _root_.map_zero] using this
  · change 2 * f y₀ + f W.a₁ * f x₀ + f W.a₃ = 0
    have := congrArg f hFY
    simpa only [_root_.map_add, _root_.map_mul, map_ofNat, _root_.map_zero] using this
  · intro hαβ
    change α = -f W.a₁ - α at hαβ
    apply hnode
    apply hf
    rw [_root_.map_add, _root_.map_mul, map_ofNat, _root_.map_zero]
    have h2 : 2 * α + f W.a₁ = 0 := by linear_combination hαβ
    have hb : f W.b₂ = (f W.a₁) ^ 2 + 4 * f W.a₂ := by
      simp only [WeierstrassCurve.b₂, _root_.map_add, _root_.map_mul, _root_.map_pow, map_ofNat]
    rw [hb]
    linear_combination (2 * α + f W.a₁) * h2 - 4 * hα

end NodalTorsion

/-- **Trivial $p$-torsion on a nodal cubic in characteristic $p$.** Let $p$ be a prime, let $k$ be
a field of characteristic $p$, let $W$ be a Weierstrass curve over $k$, and let
$(x_0, y_0) \in k^2$ be a singular point of the affine curve $W$. Suppose $(x_0, y_0)$ is a node:
$b_2 + 12 x_0 \ne 0$, that is, the two tangent lines to $W$ at $(x_0, y_0)$, defined over an
algebraic closure of $k$, are distinct. Then the group $W(k)$ of nonsingular points of $W$,
including the point at infinity, has trivial $p$-torsion: every $P \in W(k)$ with $p P = 0$ is
$P = 0$. -/
public theorem WeierstrassCurve.Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode
    {k : Type*} [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0)
    (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 := by
  classical
  obtain ⟨α, hd, hαβ⟩ := NodalTorsion.exists_frame (K := AlgebraicClosure k) W x₀ y₀ he hs
    hnode (algebraMap k (AlgebraicClosure k)) (algebraMap k _).injective
  let φ := Point.map (W' := W.toAffine) (Algebra.ofId k (AlgebraicClosure k))
  have h0 : φ P = 0 := by
    refine NodalTorsion.eq_zero_of_prime_smul_eq_zero (p := p) hd hαβ _ ?_
    calc p • φ P = φ (p • P) := (_root_.map_nsmul φ p P).symm
      _ = φ 0 := congrArg φ hP
      _ = 0 := _root_.map_zero φ
  exact Point.map_injective (W' := W.toAffine) (Algebra.ofId k (AlgebraicClosure k))
    (h0.trans (_root_.map_zero φ).symm)
