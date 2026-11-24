/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.ProductFiltration

/-!
# Multiplication and the mixed-weight filtration

Left exterior multiplication by `i` factors from the first summand raises
the first-weight filtration by `i`. The mixed product decomposition and
direct-sum projections prove this for arbitrary filtered elements, without
freeness or flatness assumptions.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct DirectSum

universe u v w z

namespace exteriorPower.ProductFiltration

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

/-- Actual homogeneous multiplication in the existing exterior algebra. -/
def multiply {V : Type z} [AddCommGroup V] [Module R V] (i j : ℕ)
    (x : ⋀[R]^i V) (y : ⋀[R]^j V) : ⋀[R]^(i + j) V :=
  ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩

/-- An original mixed tensor has the actual ordered exterior-product representative. -/
theorem injection_tmul_val (m : ℕ) (p : Index m)
    (x : ⋀[R]^p.val.1 M) (y : ⋀[R]^p.val.2 N) :
    (injection R M N m p (x ⊗ₜ[R] y) : ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) x *
        ExteriorAlgebra.map (LinearMap.inr R M N) y := by
  change ((exteriorPower.productEquiv R M N m).symm
    (DirectSum.lof R (Index m) (Piece R M N m) p (x ⊗ₜ[R] y)) :
      ExteriorAlgebra R (M × N)) = _
  rw [DirectSum.lof_eq_of]
  exact exteriorPower.productEquiv_symm_mixed R M N m p x y

/-- The original injection lands exactly when its first weight is allowed. -/
theorem injection_mem_filtration (m q : ℕ) (p : Index m) (hp : q ≤ p.val.1)
    (z : Piece R M N m p) : injection R M N m p z ∈ filtration R M N m q := by
  intro p' hp'
  apply coordinate_injection_ne
  intro h
  have hfirst := congrArg (fun p : Index m => p.val.1) h
  omega

/-- The native direct-sum projection onto the original allowed mixed weights. -/
def clip (m q : ℕ) :
    exteriorPower.productPieces R M N m →ₗ[R] exteriorPower.productPieces R M N m :=
  DirectSum.toModule R (Index m) (exteriorPower.productPieces R M N m)
    (fun p => if q ≤ p.val.1 then DirectSum.lof R (Index m) (Piece R M N m) p else 0)

theorem clip_of (m q : ℕ) (p : Index m) (z : Piece R M N m p) :
    clip R M N m q (DirectSum.lof R (Index m) (Piece R M N m) p z) =
      if q ≤ p.val.1 then DirectSum.lof R (Index m) (Piece R M N m) p z else 0 := by
  rw [clip, DirectSum.toModule_lof]
  split_ifs <;> rfl

theorem component_clip (m q : ℕ) (p : Index m) :
    (DirectSum.component R (Index m) (Piece R M N m) p).comp (clip R M N m q) =
      if q ≤ p.val.1 then DirectSum.component R (Index m) (Piece R M N m) p else 0 := by
  apply DirectSum.linearMap_ext
  intro p'
  apply LinearMap.ext
  intro z
  by_cases h : p' = p
  · subst p'
    by_cases hq : q ≤ p.val.1
    · simp only [LinearMap.comp_apply, clip_of, if_pos hq, DirectSum.component.lof_self]
    · simp only [LinearMap.comp_apply, clip_of, if_neg hq, map_zero, LinearMap.zero_apply]
  · by_cases hq' : q ≤ p'.val.1
    · by_cases hq : q ≤ p.val.1
      · simp only [LinearMap.comp_apply, clip_of, if_pos hq', if_pos hq,
          DirectSum.component.of, dif_neg h]
      · simp only [LinearMap.comp_apply, clip_of, if_pos hq', if_neg hq,
          DirectSum.component.of, dif_neg h, LinearMap.zero_apply]
    · by_cases hq : q ≤ p.val.1
      · simp only [LinearMap.comp_apply, clip_of, if_neg hq', if_pos hq,
          map_zero, DirectSum.component.of, dif_neg h]
      · simp only [LinearMap.comp_apply, clip_of, if_neg hq', if_neg hq,
          map_zero, LinearMap.zero_apply]

/-- The actual mixed coordinates of a filtered vector are fixed by that native projection. -/
theorem clip_equiv_of_mem (m q : ℕ) (z : ⋀[R]^m (M × N))
    (hz : z ∈ filtration R M N m q) :
    clip R M N m q (exteriorPower.productEquiv R M N m z) =
      exteriorPower.productEquiv R M N m z := by
  apply DirectSum.ext_component R
  intro p
  change DirectSum.component R (Index m) (Piece R M N m) p
      (clip R M N m q (exteriorPower.productEquiv R M N m z)) =
    DirectSum.component R (Index m) (Piece R M N m) p (exteriorPower.productEquiv R M N m z)
  rw [← LinearMap.comp_apply, component_clip]
  by_cases hp : q ≤ p.val.1
  · rw [if_pos hp]
  · rw [if_neg hp, LinearMap.zero_apply]
    exact (hz p (by omega)).symm

/-- The actual coordinate clipping lands in the original form stage. -/
def projectionToFiltration (m q : ℕ) : (⋀[R]^m (M × N)) →ₗ[R] filtration R M N m q :=
  ((exteriorPower.productEquiv R M N m).symm.toLinearMap.comp
    ((clip R M N m q).comp (exteriorPower.productEquiv R M N m).toLinearMap)).codRestrict
      (filtration R M N m q) (by
        intro z p hp
        change coordinate R M N m p
          ((exteriorPower.productEquiv R M N m).symm
            (clip R M N m q (exteriorPower.productEquiv R M N m z))) = 0
        let E := exteriorPower.productEquiv R M N m
        let C := DirectSum.component R (Index m) (Piece R M N m) p
        have hE : E.toLinearMap (E.symm (clip R M N m q (E z))) =
            clip R M N m q (E z) := E.apply_symm_apply _
        have hC := LinearMap.congr_fun (component_clip R M N m q p) (E z)
        have hbad : ¬ q ≤ p.val.1 := by omega
        rw [if_neg hbad, LinearMap.zero_apply] at hC
        exact (congrArg C hE).trans hC)

theorem projectionToFiltration_subtype (m q : ℕ) (z : filtration R M N m q) :
    projectionToFiltration R M N m q z.val = z := by
  apply Subtype.ext
  change (exteriorPower.productEquiv R M N m).symm
    (clip R M N m q (exteriorPower.productEquiv R M N m z.val)) = z.val
  let E := exteriorPower.productEquiv R M N m
  exact (congrArg E.symm (clip_equiv_of_mem R M N m q z.val z.property)).trans
    (E.symm_apply_apply _)

/-- Native multiplication by a pure first-summand exterior element. -/
def leftBaseMultiply (i j : ℕ) (x : ⋀[R]^i M) :
    (⋀[R]^j (M × N)) →ₗ[R] (⋀[R]^(i + j) (M × N)) where
  toFun y := multiply R i j (exteriorPower.map i (LinearMap.inl R M N) x) y
  map_add' y z := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' r y := by
    apply Subtype.ext
    exact mul_smul_comm _ _ _

def shiftedIndex (i j : ℕ) (p : Index j) : Index (i + j) :=
  ⟨(i + p.val.1, p.val.2), by have h := p.property; omega⟩

/-- Pure first factors combine with the original first part of each mixed tensor;
no permutation or unearned sign is introduced. -/
theorem leftBaseMultiply_injection (i j : ℕ) (x : ⋀[R]^i M) (p : Index j)
    (y : ⋀[R]^p.val.1 M) (z : ⋀[R]^p.val.2 N) :
    leftBaseMultiply R M N i j x (injection R M N j p (y ⊗ₜ[R] z)) =
      injection R M N (i + j) (shiftedIndex i j p)
        (multiply R i p.val.1 x y ⊗ₜ[R] z) := by
  apply Subtype.ext
  have hLeft := injection_tmul_val R M N j p y z
  have hRight := injection_tmul_val R M N (i + j) (shiftedIndex i j p)
    (multiply R i p.val.1 x y) z
  change (exteriorPower.map i (LinearMap.inl R M N) x : ExteriorAlgebra R (M × N)) *
      (injection R M N j p (y ⊗ₜ[R] z) : ExteriorAlgebra R (M × N)) = _
  have hProduct :
      ExteriorAlgebra.map (LinearMap.inl R M N) x *
        (ExteriorAlgebra.map (LinearMap.inl R M N) y * ExteriorAlgebra.map (LinearMap.inr R M N) z) =
      ExteriorAlgebra.map (LinearMap.inl R M N) (x.val * y.val) *
        ExteriorAlgebra.map (LinearMap.inr R M N) z :=
    (mul_assoc _ _ _).symm.trans
      (congrArg (fun w => w * ExteriorAlgebra.map (LinearMap.inr R M N) z)
        (map_mul (ExteriorAlgebra.map (LinearMap.inl R M N)) x.val y.val).symm)
  have hMap : (exteriorPower.map i (LinearMap.inl R M N) x : ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) x := by rw [exteriorPower.coe_map]
  exact (congrArg (fun w => w *
      (injection R M N j p (y ⊗ₜ[R] z) : ExteriorAlgebra R (M × N))) hMap).trans
    ((congrArg (fun w => ExteriorAlgebra.map (LinearMap.inl R M N) x * w) hLeft).trans
      (hProduct.trans hRight.symm))

theorem leftBaseMultiply_map_inr (i j : ℕ) (x : ⋀[R]^i M) (y : ⋀[R]^j N) :
    leftBaseMultiply R M N i j x (exteriorPower.map j (LinearMap.inr R M N) y) =
      injection R M N (i + j) ⟨(i, j), rfl⟩ (x ⊗ₜ[R] y) := by
  apply Subtype.ext
  change (exteriorPower.map i (LinearMap.inl R M N) x : ExteriorAlgebra R (M × N)) *
      (exteriorPower.map j (LinearMap.inr R M N) y : ExteriorAlgebra R (M × N)) = _
  rw [exteriorPower.coe_map, exteriorPower.coe_map, injection_tmul_val]

/-- An actual pure first factor raises the original filtration by its degree. -/
theorem leftBaseMultiply_mem (i j q : ℕ) (x : ⋀[R]^i M)
    (z : ⋀[R]^j (M × N)) (hz : z ∈ filtration R M N j q) :
    leftBaseMultiply R M N i j x z ∈ filtration R M N (i + j) (i + q) := by
  have h : ∀ y : exteriorPower.productPieces R M N j,
      leftBaseMultiply R M N i j x
        ((exteriorPower.productEquiv R M N j).symm (clip R M N j q y)) ∈
          filtration R M N (i + j) (i + q) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add y y' hy hy' =>
      simpa only [map_add] using Submodule.add_mem _ hy hy'
    | of p t =>
      rw [← DirectSum.lof_eq_of R, clip_of]
      split_ifs with hp
      · change leftBaseMultiply R M N i j x (injection R M N j p t) ∈ _
        induction t using TensorProduct.inductionOn with
        | add t t' ht ht' =>
          simpa only [map_add] using Submodule.add_mem _ ht ht'
        | tmul y z =>
          rw [leftBaseMultiply_injection]
          exact injection_mem_filtration R M N (i + j) (i + q) (shiftedIndex i j p)
            (by dsimp [shiftedIndex]; omega) _
      · simp only [map_zero]; exact Submodule.zero_mem _
  have h' := h (exteriorPower.productEquiv R M N j z)
  rw [clip_equiv_of_mem R M N j q z hz, LinearEquiv.symm_apply_apply] at h'
  exact h'

end exteriorPower.ProductFiltration

end
