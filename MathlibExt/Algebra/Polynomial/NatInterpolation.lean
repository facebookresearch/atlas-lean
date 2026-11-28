/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Polynomial.NatPowerCoefficients

/-!
# Rational weighted power sums determined by natural values

For a finite index set `I`, exponents `e : I → ℕ`, and vectors `v_i` in a `ℚ`-vector space,
define `F(a)=∑ i, a^(e i) • v_i`.

Two such families, possibly using different finite index sets and repeated exponents, agree
for every rational parameter if they agree at every natural-number parameter.

Reference: Bourbaki, *Algebra*, Chapters II and IV.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u v w

namespace Polynomial

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
  {V : Type w} [AddCommGroup V] [Module ℚ V]

/-- Let `I,J` be finite types, `V` a `ℚ`-vector space, and `e : I → ℕ`, `f : J → ℕ`, `v : I → V`,
`w : J → V`. If the two weighted power sums agree at `(m : ℚ)` for every `m : ℕ`, then `∑ i,
a^(e i) • v i = ∑ j, a^(f j) • w j` for every `a : ℚ`. -/
theorem finiteWeightedPowerCombination_eq_of_nat (e : I → ℕ) (v : I → V)
    (f : J → ℕ) (w : J → V)
    (h : ∀ m : ℕ, finiteWeightedPowerCombination e v (m : ℚ) =
      finiteWeightedPowerCombination f w (m : ℚ)) (a : ℚ) :
    finiteWeightedPowerCombination e v a = finiteWeightedPowerCombination f w a := by
  classical
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ
    (finiteWeightedPowerCombination e v a - finiteWeightedPowerCombination f w a)).mp
  intro φ
  let p : Polynomial ℚ := ∑ i : I, monomial (e i) (φ (v i))
  let q : Polynomial ℚ := ∑ j : J, monomial (f j) (φ (w j))
  have hpq : p = q := by
    apply eq_of_infinite_eval_eq
    have hi : Set.Infinite (Set.range (fun m : ℕ => (m : ℚ))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    apply hi.mono
    rintro x ⟨m, rfl⟩
    have hm := congrArg φ (h m)
    change p.eval (m : ℚ) = q.eval (m : ℚ)
    simpa only [p, q, eval_finsetSum, eval_monomial, finiteWeightedPowerCombination,
      map_sum, map_smul, smul_eq_mul, mul_comm] using hm
  have ha := congrArg (fun r : Polynomial ℚ => r.eval a) hpq
  have heq : φ (finiteWeightedPowerCombination e v a) =
      φ (finiteWeightedPowerCombination f w a) := by
    simpa only [p, q, eval_finsetSum, eval_monomial, finiteWeightedPowerCombination,
      map_sum, map_smul, smul_eq_mul, mul_comm] using ha
  rw [map_sub, heq, sub_self]

end Polynomial
