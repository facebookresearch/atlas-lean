/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Isotropy of unit diagonal forms over `ℚ_[p]` for odd `p`

ArithmeticGeometry:75: for an odd prime `p` and `n > 2`, a diagonal quadratic form
over `ℚ_[p]` whose coefficients are units of `ℤ_[p]` is isotropic.

Clean-room proof: reduce the first three coefficients modulo `p` via the public
`PadicInt.toZMod` homomorphism, find a mod-`p` solution with first coordinate `1`
via the public finite-field lemma `FiniteField.exists_root_sum_quadratic`,
lift the other two coordinates to `ℤ_[p]`, and apply the public Hensel lemma
`hensels_lemma` in the first variable.
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbol

/-- **Unit diagonal forms in at least three variables over $\mathbb{Q}_p$ are isotropic for odd
$p$.** Let $p$ be an odd prime, let $n > 2$, and let $a_1, \dots, a_n$ be units of $\mathbb{Z}_p$.
Then there is a nonzero vector $(x_1, \dots, x_n) \in \mathbb{Q}_p^n$ with
$a_1 x_1^2 + \dots + a_n x_n^2 = 0$.

Source: ArithmeticGeometry:75. -/
theorem diagonal_unit_isotropic (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    {n : ℕ} (hn : 2 < n) (a : Fin n → ℤ_[p]ˣ) :
    ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, ((a i : ℤ_[p]) : ℚ_[p]) * (x i) ^ 2 = 0 := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  set i0 : Fin n := ⟨0, h0⟩ with hi0
  set i1 : Fin n := ⟨1, h1⟩ with hi1
  set i2 : Fin n := ⟨2, hn⟩ with hi2
  have h01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    rw [hi0, hi1] at hval
    exact (by decide : (1 : ℕ) ≠ 0) hval.symm
  have h10 : i1 ≠ i0 := Ne.symm h01
  have h02 : i0 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    rw [hi0, hi2] at hval
    exact (by decide : (2 : ℕ) ≠ 0) hval.symm
  have h20 : i2 ≠ i0 := Ne.symm h02
  have h12 : i1 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    rw [hi1, hi2] at hval
    exact (by decide : (1 : ℕ) ≠ 2) hval
  have h21 : i2 ≠ i1 := Ne.symm h12
  -- Work with the first three unit coefficients as elements of `ℤ_[p]`.
  set A0 : ℤ_[p] := ((a i0 : ℤ_[p]ˣ) : ℤ_[p]) with hA0
  set A1 : ℤ_[p] := ((a i1 : ℤ_[p]ˣ) : ℤ_[p]) with hA1
  set A2 : ℤ_[p] := ((a i2 : ℤ_[p]ˣ) : ℤ_[p]) with hA2
  have hU0 : IsUnit A0 := (a i0).isUnit
  have hU1 : IsUnit A1 := (a i1).isUnit
  have hU2 : IsUnit A2 := (a i2).isUnit
  have : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  -- Reduce modulo `p`. Units map to nonzero residues.
  set b0 : ZMod p := PadicInt.toZMod A0 with hb0
  set b1 : ZMod p := PadicInt.toZMod A1 with hb1
  set b2 : ZMod p := PadicInt.toZMod A2 with hb2
  have hb0_ne : b0 ≠ 0 := by
    intro h
    have hmem : A0 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
      rw [RingHom.mem_ker, ←hb0]
      exact h
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at hmem
    exact hmem hU0
  have hb1_ne : b1 ≠ 0 := by
    intro h
    have hmem : A1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
      rw [RingHom.mem_ker, ←hb1]
      exact h
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at hmem
    exact hmem hU1
  have hb2_ne : b2 ≠ 0 := by
    intro h
    have hmem : A2 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
      rw [RingHom.mem_ker, ←hb2]
      exact h
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at hmem
    exact hmem hU2
  -- `p` is odd, so `ZMod p` has odd cardinality.
  have hmod2 : p % 2 = 1 := ((Fact.out : Nat.Prime p).eq_two_or_odd).resolve_left hp_odd
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card p, hmod2]
  -- Mod-`p` solution with first coordinate `1`, via public finite-field lemma.
  set f : Polynomial (ZMod p) :=
    Polynomial.C b1 * Polynomial.X ^ 2 + Polynomial.C b0 with hf
  set g : Polynomial (ZMod p) := Polynomial.C b2 * Polynomial.X ^ 2 with hg
  have e1 : (Polynomial.C b1 * Polynomial.X ^ 2 : Polynomial (ZMod p)).degree = 2 :=
    Polynomial.degree_C_mul_X_pow 2 hb1_ne
  have e2 : (Polynomial.C b2 * Polynomial.X ^ 2 : Polynomial (ZMod p)).degree = 2 :=
    Polynomial.degree_C_mul_X_pow 2 hb2_ne
  have hC0_lt : (Polynomial.C b0 : Polynomial (ZMod p)).degree < 2 :=
    lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  have hC0_lt' : (Polynomial.C b0 : Polynomial (ZMod p)).degree <
      (Polynomial.C b1 * Polynomial.X ^ 2 : Polynomial (ZMod p)).degree := by
    rw [e1]
    exact hC0_lt
  have hf2 : f.degree = 2 := by
    rw [hf, Polynomial.degree_add_eq_left_of_degree_lt hC0_lt', e1]
  have hg2 : g.degree = 2 := by
    rw [hg]
    exact e2
  obtain ⟨y, z, hyz⟩ := FiniteField.exists_root_sum_quadratic hf2 hg2 hcard
  have hmod : b1 * y ^ 2 + b0 + b2 * z ^ 2 = 0 := by
    have h := hyz
    simp only [hf, hg, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] at h
    linear_combination h
  -- Lift the last two coordinates to `ℤ_[p]`.
  set y0 : ℤ_[p] := ((y.val : ℕ) : ℤ_[p]) with hy0
  set z0 : ℤ_[p] := ((z.val : ℕ) : ℤ_[p]) with hz0
  have hy0_red : PadicInt.toZMod y0 = y := by
    rw [hy0, map_natCast, ZMod.natCast_zmod_val]
  have hz0_red : PadicInt.toZMod z0 = z := by
    rw [hz0, map_natCast, ZMod.natCast_zmod_val]
  -- Univariate polynomial in the first variable over `ℤ_[p]`.
  set C0 : ℤ_[p] := A1 * y0 ^ 2 + A2 * z0 ^ 2 with hC0
  set F : Polynomial ℤ_[p] := Polynomial.C A0 * Polynomial.X ^ 2 + Polynomial.C C0 with hF
  have hF1 : F.aeval (1 : ℤ_[p]) = A0 + C0 := by
    simp [hF, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  have hFred : PadicInt.toZMod (F.aeval (1 : ℤ_[p])) = 0 := by
    rw [hF1, map_add, hC0, map_add, map_mul, map_mul, map_pow, map_pow,
      ←hb0, ←hb1, ←hb2, hy0_red, hz0_red]
    linear_combination hmod
  have hFnorm : ‖F.aeval (1 : ℤ_[p])‖ < 1 := by
    have hmem : F.aeval (1 : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) :=
      RingHom.mem_ker.mpr hFred
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hmem
    exact hmem
  -- The derivative at `1` is `2 * A0`, a unit since `p` is odd.
  have h2unit : IsUnit (2 : ℤ_[p]) := by
    have hcast : (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) := by simp
    rw [hcast, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    have hp : Nat.Prime p := Fact.out
    have h2p : Nat.Prime 2 := by decide
    exact (Nat.coprime_primes hp h2p).mpr hp_odd
  have hderiv : F.derivative.aeval (1 : ℤ_[p]) = 2 * A0 := by
    rw [hF, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_sq,
      Polynomial.derivative_C, add_zero]
    simp [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, mul_comm]
  have hdnorm : ‖F.derivative.aeval (1 : ℤ_[p])‖ = 1 := by
    rw [hderiv]
    exact PadicInt.isUnit_iff.mp (h2unit.mul hU0)
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hdnorm, one_pow]
    exact hFnorm
  obtain ⟨t, ht0, htclose, _, _⟩ := hensels_lemma (F := F) (a := (1 : ℤ_[p])) hnorm
  have hFt : A0 * t ^ 2 + C0 = 0 := by
    have h := ht0
    simp [hF, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] at h
    linear_combination h
  have ht_ne : t ≠ 0 := by
    intro htz
    rw [htz] at htclose
    simp only [zero_sub, norm_neg, norm_one] at htclose
    rw [hdnorm] at htclose
    exact lt_irrefl (1 : ℝ) htclose
  -- Assemble the ternary relation and extend by zero.
  have htern : ((a i0 : ℤ_[p]) : ℚ_[p]) * ((t : ℤ_[p]) : ℚ_[p]) ^ 2
      + ((a i1 : ℤ_[p]) : ℚ_[p]) * ((y0 : ℤ_[p]) : ℚ_[p]) ^ 2
      + ((a i2 : ℤ_[p]) : ℚ_[p]) * ((z0 : ℤ_[p]) : ℚ_[p]) ^ 2 = 0 := by
    have hZ : A0 * t ^ 2 + (A1 * y0 ^ 2 + A2 * z0 ^ 2) = 0 := by
      rw [← hC0]; linear_combination hFt
    have hQ := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hZ
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_zero] at hQ
    simpa [hA0, hA1, hA2, add_assoc] using hQ
  set x : Fin n → ℚ_[p] := fun i =>
    if i = i0 then ((t : ℤ_[p]) : ℚ_[p])
    else if i = i1 then ((y0 : ℤ_[p]) : ℚ_[p])
    else if i = i2 then ((z0 : ℤ_[p]) : ℚ_[p]) else 0 with hx_def
  have hx0 : x i0 = ((t : ℤ_[p]) : ℚ_[p]) := by simp [hx_def]
  have hx1 : x i1 = ((y0 : ℤ_[p]) : ℚ_[p]) := by simp [hx_def, h10]
  have hx2 : x i2 = ((z0 : ℤ_[p]) : ℚ_[p]) := by simp [hx_def, h20, h21]
  have hx_ne : x ≠ 0 := by
    intro h
    have hcon : ((t : ℤ_[p]) : ℚ_[p]) = 0 := by
      have hcon0 := congrFun h i0
      rwa [hx0] at hcon0
    exact ht_ne (PadicInt.ext (by simpa using hcon))
  have hsup : ∀ i : Fin n, i ≠ i0 → i ≠ i1 → i ≠ i2 →
      ((a i : ℤ_[p]) : ℚ_[p]) * (x i) ^ 2 = 0 := by
    intro i hi0' hi1' hi2'
    have hxi : x i = 0 := by simp [hx_def, hi0', hi1', hi2']
    rw [hxi]
    ring
  have hmem01 : i0 ∉ ({i1, i2} : Finset (Fin n)) := by simp [h01, h02]
  have hmem12 : i1 ∉ ({i2} : Finset (Fin n)) := by simp [h12]
  have hsum3 : ∑ i ∈ ({i0, i1, i2} : Finset (Fin n)), ((a i : ℤ_[p]) : ℚ_[p]) * (x i) ^ 2
      = ((a i0 : ℤ_[p]) : ℚ_[p]) * (((t : ℤ_[p]) : ℚ_[p])) ^ 2
        + ((a i1 : ℤ_[p]) : ℚ_[p]) * (((y0 : ℤ_[p]) : ℚ_[p])) ^ 2
        + ((a i2 : ℤ_[p]) : ℚ_[p]) * (((z0 : ℤ_[p]) : ℚ_[p])) ^ 2 := by
    rw [Finset.sum_insert hmem01, Finset.sum_insert hmem12, Finset.sum_singleton,
      hx0, hx1, hx2, add_assoc]
  have hsub : ({i0, i1, i2} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hEq : ∑ i, ((a i : ℤ_[p]) : ℚ_[p]) * (x i) ^ 2
      = ∑ i ∈ ({i0, i1, i2} : Finset (Fin n)), ((a i : ℤ_[p]) : ℚ_[p]) * (x i) ^ 2 := by
    apply Eq.symm
    apply Finset.sum_subset hsub
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hsup i hi.1 hi.2.1 hi.2.2
  refine ⟨x, hx_ne, ?_⟩
  rw [hEq, hsum3]
  linear_combination htern

end HilbertSymbol
