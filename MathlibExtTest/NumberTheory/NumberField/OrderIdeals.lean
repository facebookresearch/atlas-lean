/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderIdeals

@[expose] public section

open Module

/-! Tests for `MathlibExt.NumberTheory.NumberField.OrderIdeals`. -/

-- The full-rank index lemma for `6ℤ ⊆ ℤ`: the transition matrix is `(6)`, the index is `6`.
example :
    let b := Basis.singleton (Fin 1) ℤ
    let bN := Basis.span (R := ℤ) (v := ![(6 : ℤ)]) (by
      rw [linearIndependent_unique_iff]; simp)
    (b.toMatrix fun i => (bN i : ℤ)).det ≠ 0 ∧
      Nat.card (ℤ ⧸ Submodule.span ℤ (Set.range ![(6 : ℤ)])) = 6 := by
  intro b bN
  obtain ⟨h0, -, hcard⟩ := Submodule.det_toMatrix_ne_zero_and_natCard_quotient b _ bN
  refine ⟨h0, ?_⟩
  rw [hcard, Matrix.det_unique, Basis.toMatrix_apply, Basis.span_apply]
  simp [b]

-- For the order `ℤ` of `ℚ`: rank one, and the principal ideal `6ℤ` has index `|N(6)| = 6`.
example : finrank ℤ (integralClosure ℤ ℚ) = 1 := by
  rw [(NumberField.isOrder_integralClosure ℚ).finrank_eq, finrank_self]

example : Nat.card (integralClosure ℤ ℚ ⧸ Ideal.span {(6 : integralClosure ℤ ℚ)}) = 6 := by
  have h := (NumberField.isOrder_integralClosure ℚ).natCard_quotient_span_singleton_eq_abs_norm
    (β := (6 : integralClosure ℤ ℚ)) (by
      intro h; have := congrArg Subtype.val h; norm_num at this)
  have h6 : ((6 : integralClosure ℤ ℚ) : ℚ) = 6 := rfl
  rw [h6, Algebra.norm_self, MonoidHom.id_apply] at h
  have h' : (Nat.card (integralClosure ℤ ℚ ⧸ Ideal.span {(6 : integralClosure ℤ ℚ)}) : ℚ) =
      (6 : ℕ) := by
    rw [h]; norm_num
  exact_mod_cast h'

-- Finite index: in the ring of integers of a number field of degree `n`, `#(𝒪/2𝒪)` divides
-- `2 ^ n`, and nonzero primes are maximal.
example (K : Type*) [Field K] [NumberField K] :
    Nat.card (integralClosure ℤ K ⧸ Ideal.span {(2 : integralClosure ℤ K)}) ∣
      2 ^ finrank ℚ K :=
  (NumberField.isOrder_integralClosure K).natCard_quotient_dvd_pow (m := 2) two_pos
    (by simp)

example (K : Type*) [Field K] [NumberField K] (P : Ideal (integralClosure ℤ K)) [P.IsPrime]
    (hP : P ≠ ⊥) : P.IsMaximal :=
  ((NumberField.isOrder_integralClosure K).ideal_finite_index hP).2.2.2 inferInstance

-- For the maximal order the conductor is the unit ideal, so every nonzero ideal of `𝒪_K` has
-- multiplier ring `𝒪_K`.
example (K : Type*) [Field K] [NumberField K] (b : Ideal (integralClosure ℤ K)) (hb : b ≠ ⊥) :
    {x : K | ∀ y ∈ b, ∃ z ∈ b, (z : K) = x * y} = (integralClosure ℤ K : Set K) := by
  have hO := NumberField.isOrder_integralClosure K
  refine hO.setOf_mul_mem_eq hb ?_
  have htop : (integralClosure ℤ K).comap (integralClosure ℤ K).val = ⊤ :=
    eq_top_iff.mpr fun t _ => t.2
  rw [htop, Subalgebra.conductorIdeal_top, Ideal.comap_top, sup_top_eq]

end
