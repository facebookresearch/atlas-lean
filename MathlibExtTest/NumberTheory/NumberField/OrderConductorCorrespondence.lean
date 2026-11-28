/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderConductorCorrespondence

@[expose] public section

/-! Tests for `MathlibExt.NumberTheory.NumberField.OrderConductorCorrespondence`. -/

/-- The conductor of the maximal order is the unit ideal. -/
theorem conductor_integralClosure_eq_top (K : Type*) [Field K] [NumberField K] :
    ((integralClosure ℤ K).comap (integralClosure ℤ K).val).conductorIdeal = ⊤ := by
  have htop : (integralClosure ℤ K).comap (integralClosure ℤ K).val = ⊤ :=
    eq_top_iff.mpr fun t _ => t.2
  rw [htop, Subalgebra.conductorIdeal_top]

-- For the maximal order every ideal is coprime to the conductor, so contraction and extension
-- along `𝒪_K → 𝒪_K` are mutually inverse and multiplicative.
example (K : Type*) [Field K] [NumberField K] (a a' : Ideal (integralClosure ℤ K)) :
    let hO := NumberField.isOrder_integralClosure K
    (a.comap (Subalgebra.inclusion hO.le_integralClosure)).map
        (Subalgebra.inclusion hO.le_integralClosure) = a ∧
      a.comap (Subalgebra.inclusion hO.le_integralClosure) *
          a'.comap (Subalgebra.inclusion hO.le_integralClosure) =
        (a * a').comap (Subalgebra.inclusion hO.le_integralClosure) := by
  intro hO
  have h := hO.ideals_coprime_conductor
  have hc : ∀ x : Ideal (integralClosure ℤ K),
      x ⊔ ((integralClosure ℤ K).comap (integralClosure ℤ K).val).conductorIdeal = ⊤ :=
    fun x => by rw [conductor_integralClosure_eq_top, sup_top_eq]
  exact ⟨(h.1 a (hc a)).2.1, h.2.2.2.2.1 a a' (hc a) (hc a')⟩

-- Principal ideals of the maximal order: `β𝒪_K ∩ 𝒪_K = β𝒪_K`.
example (K : Type*) [Field K] [NumberField K] (β : integralClosure ℤ K) :
    let hO := NumberField.isOrder_integralClosure K
    (Ideal.span {Subalgebra.inclusion hO.le_integralClosure β}).comap
        (Subalgebra.inclusion hO.le_integralClosure) = Ideal.span {β} := by
  intro hO
  refine hO.comap_span_singleton_eq_of_sup_eq_top ?_
  rw [conductor_integralClosure_eq_top, sup_top_eq]

-- The index is preserved: for `6ℤ` in the order `ℤ` of `ℚ`, `#(ℤ / (6ℤ ∩ ℤ)) = #(ℤ/6ℤ) = 6`.
example :
    let hO := NumberField.isOrder_integralClosure ℚ
    Nat.card (integralClosure ℤ ℚ ⧸ (Ideal.span {(6 : integralClosure ℤ ℚ)}).comap
      (Subalgebra.inclusion hO.le_integralClosure)) = 6 := by
  intro hO
  rw [hO.natCard_quotient_comap_of_sup_eq_top (by
    rw [conductor_integralClosure_eq_top, sup_top_eq])]
  have h := hO.natCard_quotient_span_singleton_eq_abs_norm
    (β := (6 : integralClosure ℤ ℚ)) (by
      intro h; have := congrArg Subtype.val h; norm_num at this)
  have h6 : ((6 : integralClosure ℤ ℚ) : ℚ) = 6 := rfl
  rw [h6, Algebra.norm_self, MonoidHom.id_apply] at h
  have h' : (Nat.card (integralClosure ℤ ℚ ⧸ Ideal.span {(6 : integralClosure ℤ ℚ)}) : ℚ) =
      (6 : ℕ) := by
    rw [h]; norm_num
  exact_mod_cast h'

end
