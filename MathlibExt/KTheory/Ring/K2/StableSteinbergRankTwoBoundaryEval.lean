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
public import MathlibExt.KTheory.Ring.K2.StableSteinbergRootInjectivity
public import MathlibExt.KTheory.Ring.StableElementary.Inclusions

/-! # Rank-two boundary evaluation
Rank-two singleton `inl`/`inr` boundary blocks evaluate under `toStableE`
as stable elementary factors; product `=1` over a field forces `c=1`, `r=1`.
No arbitrary `finiteStage 2` normalization nor rank-two kernel base.
Reuses block-eval, `fromFinite` injectivity, `2×2` entries.
-/

namespace AlgebraicKTheory
namespace StableSteinberg

universe u
variable {R : Type u} [Ring R]
private theorem fin1_eq_mulSingle (c : Fin 1 → Multiplicative R) :
    c = Pi.mulSingle (0 : Fin 1) (c 0) := by ext j; have hj : j = 0 := Fin.eq_zero j; subst hj; simp

/-- Rank-two column evaluation: `toStableE` of the `inl` singleton boundary block. -/
public theorem toStableE_lastBoundaryBlock_inl_one
    (c : (i : Fin 1) → Multiplicative R) :
    toStableE (R := R) (lastBoundaryBlock 1 (Sum.inl c)) =
      StableE.natElementary 0 1 (by decide) (c 0).toAdd := by
  have hc := fin1_eq_mulSingle c
  have h_prod : lastColumnProduct 1 (Pi.mulSingle (0 : Fin 1) (c 0) :
        Fin 1 → Multiplicative R) = x (R := R) 0 1 (by decide) (c 0).toAdd := by
    exact (lastColumnProduct_mulSingle (R := R) 1 (0 : Fin 1) (c 0)).trans
      (congrArg (fun hij : 0 ≠ 1 => x (R := R) 0 1 hij (c 0).toAdd)
        (Subsingleton.elim _ _))
  calc toStableE (R := R) (lastBoundaryBlock 1 (Sum.inl c))
      = toStableE (R := R) (lastColumnProduct 1 (Pi.mulSingle (0 : Fin 1) (c 0))) := by
        conv => lhs; rw [lastBoundaryBlock_inl, hc]
    _ = toStableE (R := R) (x (R := R) 0 1 (by decide) (c 0).toAdd) := by
        exact congrArg toStableE h_prod
    _ = StableE.natElementary 0 1 (by decide) (c 0).toAdd := by rw [toStableE_x]
/-- Rank-two row evaluation: `toStableE` of the `inr` singleton boundary block. -/
public theorem toStableE_lastBoundaryBlock_inr_one
    (r : (i : Fin 1) → Multiplicative R) :
    toStableE (R := R) (lastBoundaryBlock 1 (Sum.inr r)) =
      StableE.natElementary 1 0 (by decide) (r 0).toAdd := by
  have hr := fin1_eq_mulSingle r
  have h_prod : lastRowProduct 1 (Pi.mulSingle (0 : Fin 1) (r 0) :
        Fin 1 → Multiplicative R) = x (R := R) 1 0 (by decide) (r 0).toAdd := by
    exact (lastRowProduct_mulSingle (R := R) 1 (0 : Fin 1) (r 0)).trans
      (congrArg (fun hij : 1 ≠ 0 => x (R := R) 1 0 hij (r 0).toAdd)
        (Subsingleton.elim _ _))
  calc toStableE (R := R) (lastBoundaryBlock 1 (Sum.inr r))
      = toStableE (R := R) (lastRowProduct 1 (Pi.mulSingle (0 : Fin 1) (r 0))) := by
        conv => lhs; rw [lastBoundaryBlock_inr, hr]
    _ = toStableE (R := R) (x (R := R) 1 0 (by decide) (r 0).toAdd) := by
        exact congrArg toStableE h_prod
    _ = StableE.natElementary 1 0 (by decide) (r 0).toAdd := by rw [toStableE_x]

/-- Fin-2 consumer: `toStableE (lastBoundaryBlock 1 (inl c) *
lastBoundaryBlock 1 (inr r)) = 1` forces `c = 1` and `r = 1` over a field.

**Prominent nonclaims:**
* does **not** normalize arbitrary `finiteStage 2` words;
* does **not** prove the rank-two kernel base.
Reuses `toStableE_lastBoundaryBlock_inl_one`,
`toStableE_lastBoundaryBlock_inr_one`, `fromFinite_injective`,
and explicit `2 × 2` entries `E01(a)*E10(b)=[[1+a*b,a],[b,1]]`. -/
public theorem toStableE_lastBoundaryBlock_one_mul_one_eq_one_imp
    {F : Type u} [Field F]
    (c : (i : Fin 1) → Multiplicative F)
    (r : (i : Fin 1) → Multiplicative F)
    (h : toStableE (R := F)
      (lastBoundaryBlock 1 (Sum.inl c) * lastBoundaryBlock 1 (Sum.inr r)) = 1) :
    c = 1 ∧ r = 1 := by
  have h_inl := toStableE_lastBoundaryBlock_inl_one (R := F) c
  have h_inr := toStableE_lastBoundaryBlock_inr_one (R := F) r
  have h_map : toStableE (R := F) (lastBoundaryBlock 1 (Sum.inl c)) *
      toStableE (R := F) (lastBoundaryBlock 1 (Sum.inr r)) = 1 := by
    calc toStableE (R := F) (lastBoundaryBlock 1 (Sum.inl c)) *
        toStableE (R := F) (lastBoundaryBlock 1 (Sum.inr r))
        = toStableE (R := F) (lastBoundaryBlock 1 (Sum.inl c) *
          lastBoundaryBlock 1 (Sum.inr r)) := by rw [← map_mul]
      _ = 1 := h
  rw [h_inl, h_inr] at h_map
  set a := (c 0).toAdd; set b := (r 0).toAdd
  have h_prod : StableE.natElementary (R := F) 0 1 (by decide) a *
      StableE.natElementary (R := F) 1 0 (by decide) b = 1 := h_map
  have h01 : StableE.natElementary (R := F) 0 1 (by decide) a =
      StableE.elementary (R := F) 2 (0 : Fin 2) 1 (by decide) a := by
    have h := StableE.natElementary_fin (R := F) (n := 2) (i := (0 : Fin 2))
      (j := (1 : Fin 2)) (by decide) a
    have h' : StableE.natElementary (R := F) 0 1
        (fun h : (0 : ℕ) = 1 => (show (0 : Fin 2) ≠ 1 by decide)
          (Fin.eq_of_val_eq h)) a =
        StableE.elementary (R := F) 2 (0 : Fin 2) 1 (by decide) a := h
    have h_eq : (by decide : (0 : ℕ) ≠ 1) =
        fun h : (0 : ℕ) = 1 => (show (0 : Fin 2) ≠ 1 by decide)
          (Fin.eq_of_val_eq h) := Subsingleton.elim _ _
    rw [← h_eq] at h'
    exact h'
  have h10 : StableE.natElementary (R := F) 1 0 (by decide) b =
      StableE.elementary (R := F) 2 (1 : Fin 2) 0 (by decide) b := by
    have h := StableE.natElementary_fin (R := F) (n := 2) (i := (1 : Fin 2))
      (j := (0 : Fin 2)) (by decide) b
    have h' : StableE.natElementary (R := F) 1 0
        (fun h : (1 : ℕ) = 0 => (show (1 : Fin 2) ≠ 0 by decide)
          (Fin.eq_of_val_eq h)) b =
        StableE.elementary (R := F) 2 (1 : Fin 2) 0 (by decide) b := h
    have h_eq : (by decide : (1 : ℕ) ≠ 0) =
        fun h : (1 : ℕ) = 0 => (show (1 : Fin 2) ≠ 0 by decide)
          (Fin.eq_of_val_eq h) := Subsingleton.elim _ _
    rw [← h_eq] at h'
    exact h'
  rw [h01, h10] at h_prod
  have h_from : StableE.fromFinite (R := F) 2
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (0 : Fin 2) 1 (by decide) a *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (1 : Fin 2) 0 (by decide) b) = 1 := by
    rw [map_mul, StableE.fromFinite_elementary, StableE.fromFinite_elementary]
    exact h_prod
  have h_from_eq : StableE.fromFinite (R := F) 2
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (0 : Fin 2) 1 (by decide) a *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
        (1 : Fin 2) 0 (by decide) b) =
      StableE.fromFinite (R := F) 2 1 := by
    simpa using h_from.trans (map_one (StableE.fromFinite (R := F) 2)).symm
  have h_one_sub := StableE.fromFinite_injective (R := F) (n := 2) h_from_eq
  have h_gl : Matrix.GeneralLinearGroup.elementary (0 : Fin 2) 1 (by decide) a *
      Matrix.GeneralLinearGroup.elementary (1 : Fin 2) 0 (by decide) b =
      (1 : Matrix.GeneralLinearGroup (Fin 2) F) := by
    have := congrArg Subtype.val h_one_sub; simpa using this
  have h_a_zero : a = 0 := by
    have : (Matrix.GeneralLinearGroup.elementary (0 : Fin 2) 1 (by decide) a *
        Matrix.GeneralLinearGroup.elementary (1 : Fin 2) 0 (by decide) b :
        Matrix.GeneralLinearGroup (Fin 2) F).val 0 1 = 0 := by rw [h_gl]; simp
    simpa [Matrix.GeneralLinearGroup.coe_elementary, Matrix.single,
      Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h_b_zero : b = 0 := by
    have : (Matrix.GeneralLinearGroup.elementary (0 : Fin 2) 1 (by decide) a *
        Matrix.GeneralLinearGroup.elementary (1 : Fin 2) 0 (by decide) b :
        Matrix.GeneralLinearGroup (Fin 2) F).val 1 0 = 0 := by rw [h_gl]; simp
    simpa [Matrix.GeneralLinearGroup.coe_elementary, Matrix.single,
      Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two,
      h_a_zero] using this
  have hc0 : c 0 = 1 := by
    have h := congrArg Multiplicative.ofAdd h_a_zero
    simpa [a] using h
  have hr0 : r 0 = 1 := by
    have h := congrArg Multiplicative.ofAdd h_b_zero
    simpa [b] using h
  constructor
  · have hc := fin1_eq_mulSingle (R := F) c; rw [hc, hc0]; ext j; simp
  · have hr := fin1_eq_mulSingle (R := F) r; rw [hr, hr0]; ext j; simp

/-- Rank-two row-times-column forcing: `toStableE (lastBoundaryBlock 1 (inr r) *
lastBoundaryBlock 1 (inl c)) = 1` forces `r = 1` and `c = 1` over a field.
Symmetric to `toStableE_lastBoundaryBlock_one_mul_one_eq_one_imp`; proved by
taking inverses and applying the column-then-row version to `c⁻¹`, `r⁻¹`.
Uses `MonoidHom.map_inv`, `lastBoundaryBlock_inl`/`inr`, and `map_inv` for
`lastColumnProduct`/`lastRowProduct`; does not use private `lastBoundaryBlock_inv`.
Nonclaims: no arbitrary `finiteStage 2` normalization, no rank-two kernel base,
not arbitrary-rank; only `Fin 1`.
-/
public theorem toStableE_lastBoundaryBlock_inr_mul_inl_eq_one_imp
    {F : Type u} [Field F]
    (r : (i : Fin 1) → Multiplicative F)
    (c : (i : Fin 1) → Multiplicative F)
    (h : toStableE (R := F)
      (lastBoundaryBlock 1 (Sum.inr r) * lastBoundaryBlock 1 (Sum.inl c)) = 1) :
    r = 1 ∧ c = 1 := by
  have hInv : toStableE (R := F)
      ((lastBoundaryBlock 1 (Sum.inr r) * lastBoundaryBlock 1 (Sum.inl c))⁻¹) = 1 := by
    calc toStableE (R := F) ((lastBoundaryBlock 1 (Sum.inr r) *
        lastBoundaryBlock 1 (Sum.inl c))⁻¹)
        = (toStableE (R := F) (lastBoundaryBlock 1 (Sum.inr r) *
          lastBoundaryBlock 1 (Sum.inl c)))⁻¹ := by rw [MonoidHom.map_inv]
      _ = 1 := by rw [h, inv_one]
  have hRev : (lastBoundaryBlock (R := F) 1 (Sum.inr r) *
      lastBoundaryBlock 1 (Sum.inl c))⁻¹ =
      (lastBoundaryBlock 1 (Sum.inl c))⁻¹ *
      (lastBoundaryBlock 1 (Sum.inr r))⁻¹ := mul_inv_rev _ _
  have hCol : (lastBoundaryBlock (R := F) 1 (Sum.inl c))⁻¹ =
      lastBoundaryBlock 1 (Sum.inl c⁻¹) := by
    calc (lastBoundaryBlock 1 (Sum.inl c))⁻¹
        = (lastColumnProduct (R := F) 1 c)⁻¹ := by rw [lastBoundaryBlock_inl]
      _ = lastColumnProduct 1 c⁻¹ := by rw [← MonoidHom.map_inv]
      _ = lastBoundaryBlock 1 (Sum.inl c⁻¹) := by rw [← lastBoundaryBlock_inl]
  have hRow : (lastBoundaryBlock (R := F) 1 (Sum.inr r))⁻¹ =
      lastBoundaryBlock 1 (Sum.inr r⁻¹) := by
    calc (lastBoundaryBlock 1 (Sum.inr r))⁻¹
        = (lastRowProduct (R := F) 1 r)⁻¹ := by rw [lastBoundaryBlock_inr]
      _ = lastRowProduct 1 r⁻¹ := by rw [← MonoidHom.map_inv]
      _ = lastBoundaryBlock 1 (Sum.inr r⁻¹) := by rw [← lastBoundaryBlock_inr]
  have hColRow : toStableE (R := F)
      (lastBoundaryBlock 1 (Sum.inl c⁻¹) * lastBoundaryBlock 1 (Sum.inr r⁻¹)) = 1 := by
    calc toStableE (R := F) (lastBoundaryBlock 1 (Sum.inl c⁻¹) *
        lastBoundaryBlock 1 (Sum.inr r⁻¹))
        = toStableE (R := F) ((lastBoundaryBlock 1 (Sum.inl c))⁻¹ *
          (lastBoundaryBlock 1 (Sum.inr r))⁻¹) := by rw [hCol, hRow]
      _ = toStableE (R := F) ((lastBoundaryBlock 1 (Sum.inr r) *
          lastBoundaryBlock 1 (Sum.inl c))⁻¹) := by rw [← hRev]
      _ = 1 := hInv
  have hf := toStableE_lastBoundaryBlock_one_mul_one_eq_one_imp
    (F := F) c⁻¹ r⁻¹ hColRow
  have hc : c = 1 := by
    calc c = (c⁻¹)⁻¹ := (inv_inv c).symm
      _ = (1 : (i : Fin 1) → Multiplicative F)⁻¹ := by rw [hf.1]
      _ = 1 := inv_one
  have hr : r = 1 := by
    calc r = (r⁻¹)⁻¹ := (inv_inv r).symm
      _ = (1 : (i : Fin 1) → Multiplicative F)⁻¹ := by rw [hf.2]
      _ = 1 := inv_one
  exact ⟨hr, hc⟩

/-- Arbitrary-rank general-ring: `toStableE (lastBoundaryBlock n (inl c) *
lastBoundaryBlock n (inr r))` in `E_n` forces `c=1`, `r=1`. Reuses core forcing
`toStableE_lastColumnRow_product_mem_range_imp_eq_one` and `lastBoundaryBlock_inl`/`inr`;
no alternating-word, no torus mult, no cocycle, no kernel; ordered product preserved. -/
public theorem toStableE_lastBoundaryBlock_inl_mul_inr_mem_range_imp_eq_one
    (n : ℕ) (c r : Fin n → Multiplicative R)
    (h : toStableE (lastBoundaryBlock n (Sum.inl c) * lastBoundaryBlock n (Sum.inr r)) ∈
      (StableE.fromFinite (R := R) n).range) :
    c = 1 ∧ r = 1 := by
  have h_prod : lastBoundaryBlock (R := R) n (Sum.inl c) * lastBoundaryBlock n (Sum.inr r) =
      lastColumnProduct n c * lastRowProduct n r := by
    simp [lastBoundaryBlock_inl, lastBoundaryBlock_inr]
  have h_mem : toStableE (R := R) (lastColumnProduct n c * lastRowProduct n r) ∈
      (StableE.fromFinite (R := R) n).range := by
    have : toStableE (R := R) (lastColumnProduct n c * lastRowProduct n r) =
        toStableE (R := R) (lastBoundaryBlock n (Sum.inl c) *
          lastBoundaryBlock n (Sum.inr r)) := by rw [← h_prod]
    rw [this]; exact h
  exact toStableE_lastColumnRow_product_mem_range_imp_eq_one n c r h_mem

/-- Arbitrary-rank reverse-order via inverse symmetry: `toStableE (lastBoundaryBlock n
(inr r) * lastBoundaryBlock n (inl c))` in `E_n` forces `r=1`, `c=1`. Uses subgroup
inverse closure, `map_inv`, `mul_inv_rev`, `MonoidHom.map_inv` for column/row, then inverts
equalities. Ordered products preserved; no alternating-word, no torus mult, no cocycle,
no kernel. -/
public theorem toStableE_lastBoundaryBlock_inr_mul_inl_mem_range_imp_eq_one
    (n : ℕ) (r c : Fin n → Multiplicative R)
    (h : toStableE (lastBoundaryBlock n (Sum.inr r) * lastBoundaryBlock n (Sum.inl c)) ∈
      (StableE.fromFinite (R := R) n).range) :
    r = 1 ∧ c = 1 := by
  have h_inv : toStableE (R := R)
      ((lastBoundaryBlock n (Sum.inr r) * lastBoundaryBlock n (Sum.inl c))⁻¹) ∈
      (StableE.fromFinite (R := R) n).range := by
    have h1 : (toStableE (R := R)
        (lastBoundaryBlock n (Sum.inr r) * lastBoundaryBlock n (Sum.inl c)))⁻¹ ∈
        (StableE.fromFinite (R := R) n).range :=
      (StableE.fromFinite (R := R) n).range.inv_mem h
    rwa [← MonoidHom.map_inv] at h1
  have h_col_inv : (lastBoundaryBlock (R := R) n (Sum.inl c))⁻¹ =
      lastBoundaryBlock n (Sum.inl c⁻¹) := by
    rw [lastBoundaryBlock_inl, ← MonoidHom.map_inv, ← lastBoundaryBlock_inl]
  have h_row_inv : (lastBoundaryBlock (R := R) n (Sum.inr r))⁻¹ =
      lastBoundaryBlock n (Sum.inr r⁻¹) := by
    rw [lastBoundaryBlock_inr, ← MonoidHom.map_inv, ← lastBoundaryBlock_inr]
  have h_mem : toStableE (R := R)
      (lastBoundaryBlock n (Sum.inl c⁻¹) * lastBoundaryBlock n (Sum.inr r⁻¹)) ∈
      (StableE.fromFinite (R := R) n).range := by
    have h_eq : toStableE (R := R)
        ((lastBoundaryBlock n (Sum.inl c))⁻¹ * (lastBoundaryBlock n (Sum.inr r))⁻¹) =
        toStableE (R := R) ((lastBoundaryBlock n (Sum.inr r) *
          lastBoundaryBlock n (Sum.inl c))⁻¹) := by rw [← mul_inv_rev]
    have h_mid : toStableE (R := R)
        ((lastBoundaryBlock n (Sum.inl c))⁻¹ * (lastBoundaryBlock n (Sum.inr r))⁻¹) ∈
        (StableE.fromFinite (R := R) n).range := by rw [h_eq]; exact h_inv
    rw [h_col_inv, h_row_inv] at h_mid; exact h_mid
  have heq := toStableE_lastBoundaryBlock_inl_mul_inr_mem_range_imp_eq_one n c⁻¹ r⁻¹ h_mem
  exact ⟨by calc r = (r⁻¹)⁻¹ := (inv_inv r).symm
      _ = (1 : Fin n → Multiplicative R)⁻¹ := by rw [heq.2]
      _ = 1 := inv_one,
    by calc c = (c⁻¹)⁻¹ := (inv_inv c).symm
      _ = (1 : Fin n → Multiplicative R)⁻¹ := by rw [heq.1]
      _ = 1 := inv_one⟩

end StableSteinberg
end AlgebraicKTheory
