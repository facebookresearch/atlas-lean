/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Primitive
public import MathlibExt.NumberTheory.SelbergClass.Factorization
public import MathlibExt.NumberTheory.SelbergClass.Degree
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for primitive functions and Selberg's conjectures

Non-vacuity of `IsSelbergPrimitive`: `1` is not primitive, and `ζ` is primitive (by additivity
of the degree and the degree bound `deg ≥ 1` for non-trivial members). Consequently
`ConjectureA` is not vacuous: at `ζ` it is Mertens' second theorem.
-/

open Complex ArithmeticFunction SelbergClass Filter Asymptotics

@[expose] public section

namespace SelbergClassTest

example {p : ℕ} (hp : p.Prime) : (zetaC * zetaC) p = 2 := by
  rw [mul_apply_prime _ _ hp]
  simp [hp.ne_zero]
  norm_num

/-- `1` is not primitive. -/
example : ¬ IsSelbergPrimitive (1 : ArithmeticFunction ℂ) := fun h => h.2.1 rfl

/-- Non-members are not primitive. -/
example : ¬ IsSelbergPrimitive ((2 : ℂ) • zetaC) := fun h => by
  have := h.1.1
  simp at this

/-- **`ζ` is primitive.** A factorisation `ζ = b c` with `b, c ≠ 1` would give
`1 = deg ζ = deg b + deg c ≥ 2`. -/
theorem isSelbergPrimitive_zeta : IsSelbergPrimitive zetaC := by
  refine ⟨zeta_mem_selbergClass, zetaC_ne_one, fun b hb c hc h => ?_⟩
  by_contra hbc
  push Not at hbc
  obtain ⟨_, ⟨Fb, hFb, _, ⟨Db⟩⟩, _⟩ := id hb
  obtain ⟨_, ⟨Fc, hFc, _, ⟨Dc⟩⟩, _⟩ := id hc
  have hF : IsLSeriesContinuation (b * c) riemannZeta := h ▸ isLSeriesContinuation_zeta
  have hdeg := FunctionalEquation.degree_eq_add_of_mul b c hb hc Fb Fc riemannZeta hFb hFc hF
    Db Dc zetaFE
  have h1 := one_le_degree_of_ne_one hb hbc.1 hFb Db
  have h2 := one_le_degree_of_ne_one hc hbc.2 hFc Dc
  rw [zetaFE_degree] at hdeg
  linarith

/-- `ζ ⋆ ζ` (the coefficients of `ζ²`) is not primitive. -/
example : ¬ IsSelbergPrimitive (zetaC * zetaC) :=
  fun hp => (hp.2.2 zetaC zeta_mem_selbergClass zetaC zeta_mem_selbergClass rfl).elim
    zetaC_ne_one zetaC_ne_one

/-- `ConjectureA` at `ζ` is Mertens' second theorem `∑_{p ≤ x} 1/p = log log x + O(1)`. -/
example (hA : ConjectureA) :
    (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (1 : ℝ) / (p : ℝ))
        - Real.log (Real.log x)) =O[atTop] (fun _ => (1 : ℝ)) := by
  refine (hA zetaC isSelbergPrimitive_zeta).congr_left fun x => ?_
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  simp [(Finset.mem_filter.1 hp).2.ne_zero]

/-- `re_sum_prime_mul_conj_div_sub_isBigO` instantiated at `g = h = ζ`. -/
example (hA : ConjectureA) (hB : ConjectureB) :
    (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊),
        zetaC p * starRingEnd ℂ (zetaC p) / (p : ℂ)).re - Real.log (Real.log x))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  simpa using re_sum_prime_mul_conj_div_sub_isBigO hA hB isSelbergPrimitive_zeta
    isSelbergPrimitive_zeta

/-- `sum_prime_norm_sq_div_sub_isBigO_of_eq_prod_pow` at `a = ζ³`: the coefficient is `3² = 9`. -/
example (hA : ConjectureA) (hB : ConjectureB) :
    (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊),
        ‖(zetaC ^ 3) p‖ ^ 2 / (p : ℝ)) - 9 * Real.log (Real.log x))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  have := sum_prime_norm_sq_div_sub_isBigO_of_eq_prod_pow hA hB (s := {zetaC})
    (e := fun _ => 3) (a := zetaC ^ 3) (by simpa using isSelbergPrimitive_zeta) (by simp)
  refine this.congr_left fun x => ?_
  norm_num

/-- `exists_multiset_prod_eq` at `ζ`. -/
example : ∃ l : Multiset (ArithmeticFunction ℂ), (∀ g ∈ l, IsSelbergPrimitive g) ∧
    l.prod = zetaC :=
  exists_multiset_prod_eq zeta_mem_selbergClass zetaC_ne_one

end SelbergClassTest
