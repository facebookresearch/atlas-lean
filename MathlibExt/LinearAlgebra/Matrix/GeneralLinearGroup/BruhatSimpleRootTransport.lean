/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangularGeneration
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization

@[expose] public section

open Matrix
open Matrix.GeneralLinearGroup

namespace Matrix.GeneralLinearGroup

section SwapOrder

variable {ι : Type*} [DecidableEq ι]

theorem swap_eq_ite (i j : ι) (x : ι) :
    Equiv.swap i j x =
      if x = i then j else if x = j then i else x := by
  by_cases hx_i : x = i
  · simp [hx_i, Equiv.swap_apply_left]
  · by_cases hx_j : x = j
    · have hj_ne_i : j ≠ i := by
        intro heq
        exact hx_i (heq ▸ hx_j)
      rw [hx_j]
      simp [hj_ne_i, Equiv.swap_apply_right]
    · simp [hx_i, hx_j, Equiv.swap_apply_of_ne_of_ne]

end SwapOrder

section AdjacentSwapOrder

variable {ι : Type*} [DecidableEq ι] [LinearOrder ι]

theorem adjacentSwap_preserves_lt {i j : ι} (hij : i ⋖ j)
    {p q : ι} (hqp : q < p) (hne : ¬(q = i ∧ p = j)) :
    Equiv.swap i j q < Equiv.swap i j p := by
  classical
  by_cases hqi : q = i
  · by_cases hpj : p = j
    · exfalso
      exact hne ⟨hqi, hpj⟩
    · have hp_ne_j : p ≠ j := hpj
      by_cases hp_i : p = i
      · have h_eq : q = p := hqi.trans hp_i.symm
        exact absurd h_eq (ne_of_lt hqp)
      · have hq_swap : Equiv.swap i j q = j := by
          rw [swap_eq_ite i j q, ite_eq_left hqi]
        have hp_swap_eq : Equiv.swap i j p = p := by
          rw [swap_eq_ite i j p, ite_eq_right hp_i, ite_eq_right hp_ne_j]
        rw [hq_swap, hp_swap_eq]
        have hj_lt_p : j < p := by
          have h_le : j ≤ p := by
            by_contra h_not_le
            have hp_lt_j : p < j := lt_of_not_ge h_not_le
            have hi_lt_p : i < p := hqi ▸ hqp
            exfalso
            exact hij.2 (c := p) hi_lt_p hp_lt_j
          rcases eq_or_lt_of_le h_le with heq | hlt
          · exact absurd heq.symm hp_ne_j
          · exact hlt
        exact hj_lt_p
  · by_cases hqj : q = j
    · have hq_swap : Equiv.swap i j q = i := by
        rw [swap_eq_ite i j q, ite_eq_right hqi, ite_eq_left hqj]
      have hj_lt_p : j < p := hqj ▸ hqp
      rw [hq_swap]
      by_cases hp_i : p = i
      · subst hp_i
        exact absurd hj_lt_p (not_lt_of_gt hij.1)
      · by_cases hp_j : p = j
        · have h_eq : q = p := hqj.trans hp_j.symm
          exact absurd h_eq (ne_of_lt hqp)
        · have hp_swap_eq : Equiv.swap i j p = p := by
            rw [swap_eq_ite i j p, ite_eq_right hp_i, ite_eq_right hp_j]
          rw [hp_swap_eq]
          exact lt_trans hij.1 hj_lt_p
    · by_cases hp_i : p = i
      · have hp_swap : Equiv.swap i j p = j := by
          rw [swap_eq_ite i j p, ite_eq_left hp_i]
        have hq_swap_eq : Equiv.swap i j q = q := by
          rw [swap_eq_ite i j q, ite_eq_right hqi, ite_eq_right hqj]
        rw [hp_swap, hq_swap_eq]
        have hq_lt_i : q < i := hp_i ▸ hqp
        exact lt_trans hq_lt_i hij.1
      · by_cases hp_j : p = j
        · have hp_swap : Equiv.swap i j p = i := by
            rw [swap_eq_ite i j p, ite_eq_right hp_i, ite_eq_left hp_j]
          have hq_swap_eq : Equiv.swap i j q = q := by
            rw [swap_eq_ite i j q, ite_eq_right hqi, ite_eq_right hqj]
          rw [hp_swap, hq_swap_eq]
          have hq_lt_j : q < j := hp_j ▸ hqp
          have hq_lt_i : q < i := by
            by_contra h_not_lt
            have hi_le_q : i ≤ q := not_lt.mp h_not_lt
            rcases eq_or_lt_of_le hi_le_q with heq | hlt
            · exact absurd heq.symm hqi
            · exfalso
              exact hij.2 (c := q) hlt hq_lt_j
          exact hq_lt_i
        · have hp_swap_eq : Equiv.swap i j p = p := by
            rw [swap_eq_ite i j p, ite_eq_right hp_i, ite_eq_right hp_j]
          have hq_swap_eq : Equiv.swap i j q = q := by
            rw [swap_eq_ite i j q, ite_eq_right hqi, ite_eq_right hqj]
          rw [hp_swap_eq, hq_swap_eq]
          exact hqp

end AdjacentSwapOrder

section EntryFormula

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

open PermutationBilinearCocycle

private theorem weylGLUnit_entry_aux (i j : ι) (hij : i ≠ j) (u : Rˣ)
    (p q : ι) :
    (weylGLUnit (R := R) i j hij u : Matrix ι ι R) p q =
      if Equiv.swap i j q = p then
        (weylWeightUnit i j hij u p : R) else 0 := by
  have h_eq := weylGLUnit_eq_monomialMatrixHom (R := R) i j hij u
  have h_entry := monomialMatrixHom_val_entry
    (R := R) (x := weylMonomialBaseUnit i j hij u) p q
  have h_val :
      (weylGLUnit (R := R) i j hij u : Matrix ι ι R) =
      (monomialMatrixHom R ι (weylMonomialBaseUnit i j hij u) :
        Matrix ι ι R) := by
    rw [h_eq]
  rw [← h_val] at h_entry
  simpa [weylMonomialBaseUnit, weylWeightUnit, weylPerm] using h_entry

private theorem weylGLUnit_inv_entry_aux (i j : ι) (hij : i ≠ j)
    (u : Rˣ) (p q : ι) :
    (((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) p q =
      if Equiv.swap i j q = p then
        (weylWeightUnit (R := R) i j hij (-u) p : R) else 0 := by
  have h_inv : (weylGLUnit (R := R) i j hij u)⁻¹ =
      weylGLUnit (R := R) i j hij (-u) :=
    weylGLUnit_inv i j hij u
  have h :
      ((weylGLUnit (R := R) i j hij (-u) : GL ι R).val) p q =
      if Equiv.swap i j q = p then
        (weylWeightUnit (R := R) i j hij (-u) p : R) else 0 :=
    weylGLUnit_entry_aux i j hij (-u) p q
  have h2 :
      (((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) =
      ((weylGLUnit (R := R) i j hij (-u) : GL ι R).val) := by
    rw [h_inv]
  rw [h2]
  exact h

/-- Exact entry formula for conjugation by `weylGLUnit`.
For `W = weylGLUnit i j u` and `σ = swap i j`,
`(W * M * W⁻¹) p q = w p * M (σ p) (σ q) * (w q)⁻¹`
where `w = weylWeightUnit i j u`. Verified sign convention:
`W⁻¹ = weylGLUnit (-u)` with weight `-u` at `i` and `u⁻¹` at `j`. -/
theorem weylGLUnit_conj_entry (i j : ι) (hij : i ≠ j) (u : Rˣ)
    (M : Matrix ι ι R) (p q : ι) :
    (((weylGLUnit (R := R) i j hij u : GL ι R).val * M *
        ((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) p q) =
      (weylWeightUnit (R := R) i j hij u p : R) *
        M (Equiv.swap i j p) (Equiv.swap i j q) *
        ((weylWeightUnit (R := R) i j hij u q)⁻¹ : Rˣ).val := by
  classical
  have hW : ∀ a b,
      (weylGLUnit (R := R) i j hij u : Matrix ι ι R) a b =
      if b = Equiv.swap i j a then
        (weylWeightUnit (R := R) i j hij u a : R) else 0 := by
    intro a b
    have h := weylGLUnit_entry_aux (R := R) i j hij u a b
    have h_iff : Equiv.swap i j b = a ↔ b = Equiv.swap i j a := by
      constructor
      · intro h
        calc b = Equiv.swap i j (Equiv.swap i j b) :=
              (Equiv.swap_apply_self i j b).symm
          _ = Equiv.swap i j a := by rw [h]
      · intro h
        rw [h, Equiv.swap_apply_self]
    by_cases hb : Equiv.swap i j b = a
    · have hb2 : b = Equiv.swap i j a := h_iff.mp hb
      rw [h]
      rw [ite_eq_left hb, ite_eq_left hb2]
    · have hb2 : ¬ b = Equiv.swap i j a := fun h2 => hb (h_iff.mpr h2)
      rw [h]
      rw [ite_eq_right hb, ite_eq_right hb2]
  have hWinv : ∀ a b,
      (((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) a b =
      if b = Equiv.swap i j a then
        (weylWeightUnit (R := R) i j hij (-u) a : R) else 0 := by
    intro a b
    have h := weylGLUnit_inv_entry_aux (R := R) i j hij u a b
    have h_iff : Equiv.swap i j b = a ↔ b = Equiv.swap i j a := by
      constructor
      · intro h
        calc b = Equiv.swap i j (Equiv.swap i j b) :=
              (Equiv.swap_apply_self i j b).symm
          _ = Equiv.swap i j a := by rw [h]
      · intro h
        rw [h, Equiv.swap_apply_self]
    by_cases hb : Equiv.swap i j b = a
    · have hb2 : b = Equiv.swap i j a := h_iff.mp hb
      rw [h]
      rw [ite_eq_left hb, ite_eq_left hb2]
    · have hb2 : ¬ b = Equiv.swap i j a := fun h2 => hb (h_iff.mpr h2)
      rw [h]
      rw [ite_eq_right hb, ite_eq_right hb2]
  have hWeightInv : ∀ q,
      (weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) : R) =
        ((weylWeightUnit (R := R) i j hij u q)⁻¹ : Rˣ).val := by
    intro q
    have hUnit : weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) =
        ((weylWeightUnit (R := R) i j hij u q)⁻¹ : Rˣ) := by
      by_cases hqi : q = i
      · have h1 : Equiv.swap i j q = j := by
          rw [swap_eq_ite i j q, ite_eq_left hqi]
        have h2 : weylWeightUnit (R := R) i j hij u q = u := by
          simp [weylWeightUnit, hqi]
        have h3 : weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) =
            -(-u)⁻¹ := by
          rw [h1]
          simp [weylWeightUnit, hij.symm]
        rw [h2, h3]
        have h_inv : ((-u)⁻¹ : Rˣ) = -u⁻¹ := by
          apply Units.ext; simp
        rw [h_inv]
        simp
      · by_cases hqj : q = j
        · have h1 : Equiv.swap i j q = i := by
            rw [swap_eq_ite i j q, ite_eq_right hqi, ite_eq_left hqj]
          have h2 : weylWeightUnit (R := R) i j hij u q = -u⁻¹ := by
            simp only [weylWeightUnit, ite_eq_right hqi, ite_eq_left hqj]
          have h3 : weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) =
              -u := by
            rw [h1]
            simp [weylWeightUnit]
          rw [h2, h3]
          have h_inv : ((-u⁻¹)⁻¹ : Rˣ) = -u := by
            calc (-u⁻¹ : Rˣ)⁻¹ = (-(u⁻¹) : Rˣ)⁻¹ := by
                  have : (-u⁻¹ : Rˣ) = -(u⁻¹) := by
                    apply Units.ext; simp
                  rw [this]
              _ = -(u⁻¹)⁻¹ := by
                  have : ((-(u⁻¹) : Rˣ)⁻¹ : Rˣ) = -((u⁻¹)⁻¹ : Rˣ) := by
                    apply Units.ext; simp
                  exact this
              _ = -u := by simp [inv_inv]
          have : (-u⁻¹ : Rˣ)⁻¹ = -u := h_inv
          simp [this]
        · have h1 : Equiv.swap i j q = q := by
            rw [swap_eq_ite i j q, ite_eq_right hqi, ite_eq_right hqj]
          have h2 : weylWeightUnit (R := R) i j hij u q = 1 := by
            simp [weylWeightUnit, hqi, hqj]
          have h3 : weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) = 1 := by
            rw [h1]
            simp [weylWeightUnit, hqi, hqj]
          rw [h2, h3]
          simp
    calc (weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) : R)
        = ((weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) : Rˣ) : R) := rfl
      _ = ((((weylWeightUnit (R := R) i j hij u q)⁻¹ : Rˣ) : R)) := by
        rw [hUnit]
      _ = (((weylWeightUnit (R := R) i j hij u q)⁻¹ : Rˣ).val) := rfl
  have hWM : ∀ p b,
      ((weylGLUnit (R := R) i j hij u : Matrix ι ι R) * M) p b =
      (weylWeightUnit (R := R) i j hij u p : R) *
        M (Equiv.swap i j p) b := by
    intro p b
    calc ((weylGLUnit (R := R) i j hij u : Matrix ι ι R) * M) p b =
        ∑ k : ι, (weylGLUnit (R := R) i j hij u : Matrix ι ι R) p k * M k b := by
          simp [Matrix.mul_apply]
      _ = ∑ k : ι, (if k = Equiv.swap i j p then
            (weylWeightUnit (R := R) i j hij u p : R) else 0) * M k b := by
        apply Finset.sum_congr rfl; intro k _
        rw [hW p k]
      _ = ∑ k : ι, if k = Equiv.swap i j p then
            (weylWeightUnit (R := R) i j hij u p : R) * M k b else 0 := by
        apply Finset.sum_congr rfl; intro k _
        by_cases hk : k = Equiv.swap i j p <;> simp [hk]
      _ = (weylWeightUnit (R := R) i j hij u p : R) *
            M (Equiv.swap i j p) b := by
        rw [Finset.sum_ite_eq' Finset.univ (Equiv.swap i j p)
          (fun k => (weylWeightUnit (R := R) i j hij u p : R) * M k b)]
        simp
  have hFinal : ∀ p q,
      (((weylGLUnit (R := R) i j hij u : GL ι R).val * M *
        ((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) p q) =
      (weylWeightUnit (R := R) i j hij u p : R) *
        M (Equiv.swap i j p) (Equiv.swap i j q) *
        (weylWeightUnit (R := R) i j hij (-u) (Equiv.swap i j q) : R) := by
    intro p q
    have hMul :
        (((weylGLUnit (R := R) i j hij u : GL ι R).val * M *
          ((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) p q) =
        ∑ b, ((((weylGLUnit (R := R) i j hij u : GL ι R).val * M) p b) *
            ((((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) b q)) :=
      Matrix.mul_apply
    calc (((weylGLUnit (R := R) i j hij u : GL ι R).val * M *
        ((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) p q)
        = ∑ b, ((((weylGLUnit (R := R) i j hij u : GL ι R).val * M) p b) *
            ((((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) b q)) :=
        hMul
      _ = ∑ b, (((weylWeightUnit (R := R) i j hij u p : R) *
            M (Equiv.swap i j p) b) *
            ((((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) b q)) := by
        apply Finset.sum_congr rfl; intro b _
        rw [hWM p b]
      _ = ∑ b, ((weylWeightUnit (R := R) i j hij u p : R) *
            M (Equiv.swap i j p) b *
            ((((weylGLUnit (R := R) i j hij u)⁻¹ : GL ι R).val) b q)) := by
        apply Finset.sum_congr rfl; intro b _
        rw [mul_assoc]
      _ = ∑ b, ((weylWeightUnit (R := R) i j hij u p : R) *
            M (Equiv.swap i j p) b *
            (if q = Equiv.swap i j b then
              (weylWeightUnit (R := R) i j hij (-u) b : R) else 0)) := by
        apply Finset.sum_congr rfl; intro b _
        rw [hWinv b q]
      _ = ∑ b, (if q = Equiv.swap i j b then
            (weylWeightUnit (R := R) i j hij u p : R) *
              M (Equiv.swap i j p) b *
              (weylWeightUnit (R := R) i j hij (-u) b : R) else 0) := by
        apply Finset.sum_congr rfl; intro b _
        by_cases hb : q = Equiv.swap i j b
        · simp only [hb, ite_true, mul_assoc]
        · simp only [hb, ite_false, mul_zero]
      _ = ∑ b, (if b = Equiv.swap i j q then
            (weylWeightUnit (R := R) i j hij u p : R) *
              M (Equiv.swap i j p) b *
              (weylWeightUnit (R := R) i j hij (-u) b : R) else 0) := by
        apply Finset.sum_congr rfl; intro b _
        have h_iff : (q = Equiv.swap i j b) ↔ (b = Equiv.swap i j q) := by
          constructor
          · intro h
            calc b = Equiv.swap i j (Equiv.swap i j b) :=
                  (Equiv.swap_apply_self i j b).symm
              _ = Equiv.swap i j q := by rw [← h]
          · intro h
            calc q = Equiv.swap i j (Equiv.swap i j q) :=
                  (Equiv.swap_apply_self i j q).symm
              _ = Equiv.swap i j b := by rw [h]
        by_cases hb : q = Equiv.swap i j b
        · have hb2 : b = Equiv.swap i j q := h_iff.mp hb
          rw [ite_eq_left hb, ite_eq_left hb2]
        · have hb2 : ¬ b = Equiv.swap i j q :=
            fun h2 => hb (h_iff.mpr h2)
          rw [ite_eq_right hb, ite_eq_right hb2]
      _ = (weylWeightUnit (R := R) i j hij u p : R) *
            M (Equiv.swap i j p) (Equiv.swap i j q) *
            (weylWeightUnit (R := R) i j hij (-u)
              (Equiv.swap i j q) : R) := by
        have h :
            (∑ b : ι, if b = Equiv.swap i j q then
              (weylWeightUnit (R := R) i j hij u p : R) *
                M (Equiv.swap i j p) b *
                (weylWeightUnit (R := R) i j hij (-u) b : R)
              else 0) =
            if Equiv.swap i j q ∈ (Finset.univ : Finset ι) then
              (weylWeightUnit (R := R) i j hij u p : R) *
                M (Equiv.swap i j p) (Equiv.swap i j q) *
                (weylWeightUnit (R := R) i j hij (-u)
                  (Equiv.swap i j q) : R)
              else 0 :=
          Finset.sum_ite_eq' (Finset.univ : Finset ι) (Equiv.swap i j q)
            (fun b =>
              (weylWeightUnit (R := R) i j hij u p : R) *
                M (Equiv.swap i j p) b *
                (weylWeightUnit (R := R) i j hij (-u) b : R))
        simp only [Finset.mem_univ, ite_true] at h
        exact h
  simpa [hWeightInv q] using hFinal p q

end EntryFormula

section WeylTransportGL

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

private theorem weyl_conj_IsUpperTriangular
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    (M : Matrix ι ι R)
    (hM_tri : IsUpperTriangular M)
    (hM_ij : M i j = 0) :
    IsUpperTriangular
      (weylGLUnit (R := R) i j hij u * M *
        (weylGLUnit (R := R) i j hij u)⁻¹ : Matrix ι ι R) := by
  intro p q hqp
  rw [weylGLUnit_conj_entry i j hij u M p q]
  by_cases hne : q = i ∧ p = j
  · have hM0 : M (Equiv.swap i j p) (Equiv.swap i j q) = 0 := by
      have hpj : p = j := hne.2
      have hqi : q = i := hne.1
      have h1 : Equiv.swap i j p = i := by
        rw [hpj, Equiv.swap_apply_right]
      have h2 : Equiv.swap i j q = j := by
        rw [hqi, Equiv.swap_apply_left]
      calc M (Equiv.swap i j p) (Equiv.swap i j q) = M i j := by
            rw [h1, h2]
        _ = 0 := hM_ij
    rw [hM0, mul_zero, zero_mul]
  · have hlt : Equiv.swap i j q < Equiv.swap i j p :=
      adjacentSwap_preserves_lt hij_cov hqp hne
    have h0 : M (Equiv.swap i j p) (Equiv.swap i j q) = 0 := by
      have : Equiv.swap i j q < Equiv.swap i j p := hlt
      exact hM_tri this
    simp [h0]

omit [LinearOrder ι] in
private theorem weyl_conj_diag_one
    {i j : ι} (hij : i ≠ j) (u : Rˣ)
    (M : Matrix ι ι R) (hM_diag : ∀ k, M k k = 1) (p : ι) :
    (weylGLUnit (R := R) i j hij u * M *
      (weylGLUnit (R := R) i j hij u)⁻¹ : Matrix ι ι R) p p = 1 := by
  rw [weylGLUnit_conj_entry i j hij u M p p, hM_diag (Equiv.swap i j p)]
  have hUnit : (weylWeightUnit (R := R) i j hij u p : R) *
      ((weylWeightUnit (R := R) i j hij u p)⁻¹ : Rˣ).val = 1 := by
    have h : ((weylWeightUnit (R := R) i j hij u p : Rˣ) *
        (weylWeightUnit (R := R) i j hij u p)⁻¹ : Rˣ) = 1 := by
      simp
    have h2 : (((weylWeightUnit (R := R) i j hij u p : Rˣ) *
        (weylWeightUnit (R := R) i j hij u p)⁻¹ : Rˣ) : R) = 1 := by
      rw [h]; rfl
    calc (weylWeightUnit (R := R) i j hij u p : R) *
        ((weylWeightUnit (R := R) i j hij u p)⁻¹ : Rˣ).val
        = (((weylWeightUnit (R := R) i j hij u p : Rˣ) *
          (weylWeightUnit (R := R) i j hij u p)⁻¹ : Rˣ) : R) := by rfl
      _ = 1 := h2
  calc (weylWeightUnit (R := R) i j hij u p : R) *
      1 * ((weylWeightUnit (R := R) i j hij u p)⁻¹ : Rˣ).val
      = (weylWeightUnit (R := R) i j hij u p : R) *
        ((weylWeightUnit (R := R) i j hij u p)⁻¹ : Rˣ).val := by
          simp [mul_one]
    _ = 1 := hUnit

theorem weylGLUnit_conj_mem_upperUnitriangular_of_covBy_zero
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    {t : GL ι R} (ht : t ∈ upperUnitriangularSubgroup ι R)
    (ht_ij : (t : Matrix ι ι R) i j = 0) :
    weylGLUnit (R := R) i j hij u * t *
      (weylGLUnit (R := R) i j hij u)⁻¹ ∈
      upperUnitriangularSubgroup ι R := by
  have hM_tri : IsUpperTriangular (t : Matrix ι ι R) := ht.1
  have hM_diag : ∀ k, (t : Matrix ι ι R) k k = 1 := ht.2
  constructor
  · exact weyl_conj_IsUpperTriangular hij_cov u hij
      (t : Matrix ι ι R) hM_tri ht_ij
  · intro k
    exact weyl_conj_diag_one hij u (t : Matrix ι ι R) hM_diag k

theorem weylGLUnit_conj_mem_upperElementary_of_covBy_zero
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    {t : GL ι R} (ht : t ∈ upperUnitriangularSubgroup ι R)
    (ht_ij : (t : Matrix ι ι R) i j = 0) :
    weylGLUnit (R := R) i j hij u * t *
      (weylGLUnit (R := R) i j hij u)⁻¹ ∈
      upperElementarySubgroup ι R := by
  have hU := weylGLUnit_conj_mem_upperUnitriangular_of_covBy_zero
    hij_cov u hij ht ht_ij
  exact upperUnitriangularSubgroup_le_upperElementarySubgroup hU

theorem weylGL_conj_mem_upperElementary_of_covBy_zero
    {i j : ι} (hij_cov : i ⋖ j) (hij : i ≠ j)
    {t : GL ι R} (ht : t ∈ upperUnitriangularSubgroup ι R)
    (ht_ij : (t : Matrix ι ι R) i j = 0) :
    weylGL (R := R) i j hij * t * (weylGL (R := R) i j hij)⁻¹ ∈
      upperElementarySubgroup ι R := by
  have h : weylGL (R := R) i j hij = weylGLUnit i j hij 1 := rfl
  rw [h]
  exact weylGLUnit_conj_mem_upperElementary_of_covBy_zero
    hij_cov 1 hij ht ht_ij

theorem weylGLUnit_conj_mem_upperElementary_of_elementary_zero
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    weylGLUnit (R := R) i j hij u * (t : GL ι R) *
      (weylGLUnit (R := R) i j hij u)⁻¹ ∈
      upperElementarySubgroup ι R := by
  have htU : (t : GL ι R) ∈ upperUnitriangularSubgroup ι R :=
    upperElementarySubgroup_le_upperUnitriangularSubgroup_commRing t.2
  exact weylGLUnit_conj_mem_upperElementary_of_covBy_zero
    hij_cov u hij htU ht_ij

theorem weylGLUnit_mul_upperElementary_exists_left
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      (weylGLUnit (R := R) i j hij u : GL ι R) * (t : GL ι R) =
        (t' : GL ι R) * weylGLUnit (R := R) i j hij u := by
  let W : GL ι R := weylGLUnit (R := R) i j hij u
  have hMem : W * (t : GL ι R) * W⁻¹ ∈ upperElementarySubgroup ι R :=
    weylGLUnit_conj_mem_upperElementary_of_elementary_zero
      hij_cov u hij t ht_ij
  refine ⟨⟨W * (t : GL ι R) * W⁻¹, hMem⟩, ?_⟩
  simp [W, mul_assoc]

theorem weylGLUnit_mul_upperElementary_exists_right
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      (t : GL ι R) * weylGLUnit (R := R) i j hij u =
        (weylGLUnit (R := R) i j hij u : GL ι R) * (t' : GL ι R) := by
  let W : GL ι R := weylGLUnit (R := R) i j hij u
  have hInv : W⁻¹ = weylGLUnit (R := R) i j hij (-u) :=
    weylGLUnit_inv i j hij u
  have hInv2 : (weylGLUnit (R := R) i j hij (-u))⁻¹ = W := by
    have h := weylGLUnit_inv i j hij (-u)
    simpa [W, neg_neg] using h
  have hMem : W⁻¹ * (t : GL ι R) * W ∈ upperElementarySubgroup ι R := by
    have hEq2 : W⁻¹ * (t : GL ι R) * W =
        weylGLUnit (R := R) i j hij (-u) * (t : GL ι R) *
          (weylGLUnit (R := R) i j hij (-u))⁻¹ := by
      rw [hInv, hInv2]
    rw [hEq2]
    exact weylGLUnit_conj_mem_upperElementary_of_elementary_zero
      hij_cov (-u) hij t ht_ij
  refine ⟨⟨W⁻¹ * (t : GL ι R) * W, hMem⟩, ?_⟩
  have hEq : (t : GL ι R) * W = W * (W⁻¹ * (t : GL ι R) * W) := by
    calc (t : GL ι R) * W = 1 * ((t : GL ι R) * W) := by simp
      _ = (W * W⁻¹) * ((t : GL ι R) * W) := by rw [mul_inv_cancel]
      _ = W * (W⁻¹ * ((t : GL ι R) * W)) := by rw [mul_assoc]
      _ = W * (W⁻¹ * (t : GL ι R) * W) := by rw [mul_assoc]
  exact hEq

theorem weylGL_mul_upperElementary_exists_left
    {i j : ι} (hij_cov : i ⋖ j) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      (weylGL (R := R) i j hij : GL ι R) * (t : GL ι R) =
        (t' : GL ι R) * weylGL (R := R) i j hij := by
  have h : weylGL (R := R) i j hij = weylGLUnit i j hij 1 := rfl
  rw [h]
  exact weylGLUnit_mul_upperElementary_exists_left
    hij_cov 1 hij t ht_ij

theorem weylGL_mul_upperElementary_exists_right
    {i j : ι} (hij_cov : i ⋖ j) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      (t : GL ι R) * weylGL (R := R) i j hij =
        (weylGL (R := R) i j hij : GL ι R) * (t' : GL ι R) := by
  have h : weylGL (R := R) i j hij = weylGLUnit i j hij 1 := rfl
  rw [h]
  exact weylGLUnit_mul_upperElementary_exists_right
    hij_cov 1 hij t ht_ij

end WeylTransportGL

section WeylTransportSL

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

omit [LinearOrder ι] in
private theorem toGL_weylSLUnit_eq_weylGLUnit'
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (Matrix.SpecialLinearGroup.toGL
        (weylSLUnit (R := R) i j hij u) : GL ι R) =
      weylGLUnit (R := R) i j hij u := by
  apply Units.ext
  simp only [weylSLUnit, weylGLUnit,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, coe_elementary]

theorem weylSLUnit_conj_mem_upperElementary_toSLHom
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      weylSLUnit (R := R) i j hij u * UpperElementary.toSLHom t *
        (weylSLUnit (R := R) i j hij u)⁻¹ =
        UpperElementary.toSLHom t' := by
  have hGLMem : weylGLUnit (R := R) i j hij u * (t : GL ι R) *
      (weylGLUnit (R := R) i j hij u)⁻¹ ∈
      upperElementarySubgroup ι R :=
    weylGLUnit_conj_mem_upperElementary_of_elementary_zero
      hij_cov u hij t ht_ij
  let t' : upperElementarySubgroup ι R :=
    ⟨weylGLUnit (R := R) i j hij u * (t : GL ι R) *
      (weylGLUnit (R := R) i j hij u)⁻¹, hGLMem⟩
  refine ⟨t', ?_⟩
  apply Matrix.SpecialLinearGroup.toGL_injective
  calc Matrix.SpecialLinearGroup.toGL
        (weylSLUnit i j hij u * UpperElementary.toSLHom t *
          (weylSLUnit i j hij u)⁻¹)
      = Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij u) *
        Matrix.SpecialLinearGroup.toGL (UpperElementary.toSLHom t) *
        Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij u)⁻¹ := by
          simp [map_mul, map_inv]
    _ = weylGLUnit (R := R) i j hij u * (t : GL ι R) *
          (weylGLUnit (R := R) i j hij u)⁻¹ := by
        simp [toGL_weylSLUnit_eq_weylGLUnit',
          UpperElementary.toGL_toSLHom, map_inv]
    _ = Matrix.SpecialLinearGroup.toGL (UpperElementary.toSLHom t') := by
        simp [UpperElementary.toGL_toSLHom, t']

theorem weylSLUnit_mul_toSLHom_exists_left
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      weylSLUnit (R := R) i j hij u * UpperElementary.toSLHom t =
        UpperElementary.toSLHom t' * weylSLUnit (R := R) i j hij u := by
  obtain ⟨t', ht'⟩ :=
    weylSLUnit_conj_mem_upperElementary_toSLHom hij_cov u hij t ht_ij
  refine ⟨t', ?_⟩
  have hInv : (weylSLUnit (R := R) i j hij u)⁻¹ *
      weylSLUnit (R := R) i j hij u = 1 := inv_mul_cancel _
  calc weylSLUnit i j hij u * UpperElementary.toSLHom t
      = UpperElementary.toSLHom t' * weylSLUnit i j hij u := by
        have hConj : weylSLUnit i j hij u * UpperElementary.toSLHom t *
            (weylSLUnit i j hij u)⁻¹ = UpperElementary.toSLHom t' := ht'
        calc weylSLUnit i j hij u * UpperElementary.toSLHom t
            = weylSLUnit i j hij u * (UpperElementary.toSLHom t *
                ((weylSLUnit i j hij u)⁻¹ * weylSLUnit i j hij u)) := by
              rw [hInv, mul_one]
          _ = weylSLUnit i j hij u * UpperElementary.toSLHom t *
                (weylSLUnit i j hij u)⁻¹ * weylSLUnit i j hij u := by
              rw [(mul_assoc _ _ _).symm, (mul_assoc _ _ _).symm]
          _ = UpperElementary.toSLHom t' * weylSLUnit i j hij u := by
              rw [hConj]

theorem weylSLUnit_mul_toSLHom_exists_right
    {i j : ι} (hij_cov : i ⋖ j) (u : Rˣ) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      UpperElementary.toSLHom t * weylSLUnit (R := R) i j hij u =
        weylSLUnit (R := R) i j hij u * UpperElementary.toSLHom t' := by
  let W : Matrix.SpecialLinearGroup ι R :=
    weylSLUnit (R := R) i j hij u
  have hWinv : W⁻¹ = weylSLUnit (R := R) i j hij (-u) :=
    weylSLUnit_inv i j hij u
  obtain ⟨t', ht'⟩ :=
    weylSLUnit_conj_mem_upperElementary_toSLHom hij_cov (-u) hij t ht_ij
  have hConj : W⁻¹ * UpperElementary.toSLHom t * W =
      UpperElementary.toSLHom t' := by
    simpa [W, weylSLUnit_inv] using ht'
  refine ⟨t', ?_⟩
  have hW_inv : W * W⁻¹ = 1 := mul_inv_cancel _
  calc UpperElementary.toSLHom t * W
      = (W * W⁻¹) * (UpperElementary.toSLHom t * W) := by
        rw [hW_inv, one_mul]
    _ = W * (W⁻¹ * UpperElementary.toSLHom t * W) := by
        simp only [mul_assoc]
    _ = W * UpperElementary.toSLHom t' := by rw [hConj]

theorem weylSL_mul_toSLHom_exists_left
    {i j : ι} (hij_cov : i ⋖ j) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      weylSL (R := R) i j hij * UpperElementary.toSLHom t =
        UpperElementary.toSLHom t' * weylSL (R := R) i j hij := by
  have h : weylSL (R := R) i j hij = weylSLUnit i j hij 1 := rfl
  rw [h]
  exact weylSLUnit_mul_toSLHom_exists_left hij_cov 1 hij t ht_ij

theorem weylSL_mul_toSLHom_exists_right
    {i j : ι} (hij_cov : i ⋖ j) (hij : i ≠ j)
    (t : upperElementarySubgroup ι R)
    (ht_ij : ((t : GL ι R) : Matrix ι ι R) i j = 0) :
    ∃ t' : upperElementarySubgroup ι R,
      UpperElementary.toSLHom t * weylSL (R := R) i j hij =
        weylSL (R := R) i j hij * UpperElementary.toSLHom t' := by
  have h : weylSL (R := R) i j hij = weylSLUnit i j hij 1 := rfl
  rw [h]
  exact weylSLUnit_mul_toSLHom_exists_right hij_cov 1 hij t ht_ij

end WeylTransportSL

end Matrix.GeneralLinearGroup
