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

public import MathlibExt.KTheory.Ring.StableElementary.Basic
public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockStabilization

/-! # Natural-index stable elementary generators

Minimal-rank `ℕ`-indexed generators for `E∞(R)` and identification
with finite-level `StableE.elementary`.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableE

universe u

variable {R : Type u} [Ring R]

/-- Natural-index elementary at minimal rank `max i j + 1`. -/
def natElementary (i j : ℕ) (hij : i ≠ j) (a : R) : StableE R :=
  StableE.elementary (max i j + 1)
    ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
    ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩
    (fun h => hij (congrArg Fin.val h)) a

private theorem elementary_castAdd (n m : ℕ) (i j : Fin n)
    (hij : i ≠ j) (a : R) :
    StableE.elementary (n + m) (Fin.castAdd m i) (Fin.castAdd m j)
      (fun h =>
        hij (Fin.eq_of_val_eq
          (by simpa [Fin.val_castAdd] using congrArg Fin.val h))) a =
      StableE.elementary n i j hij a := by
  have hijCast : Fin.castAdd m i ≠ Fin.castAdd m j :=
    fun h =>
      hij (Fin.eq_of_val_eq
        (by simpa [Fin.val_castAdd] using congrArg Fin.val h))
  have h_block :
      Matrix.GeneralLinearGroup.blockStabilization n m R
          (Matrix.GeneralLinearGroup.elementary i j hij a) =
        Matrix.GeneralLinearGroup.elementary (Fin.castAdd m i)
          (Fin.castAdd m j) hijCast a := by
    calc
      Matrix.GeneralLinearGroup.blockStabilization n m R
            (Matrix.GeneralLinearGroup.elementary i j hij a)
          = Matrix.GeneralLinearGroup.reindexMulEquiv
              (finSumFinEquiv (m := n) (n := m))
              (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin m) R
                (Matrix.GeneralLinearGroup.elementary i j hij a)) := rfl
      _ = Matrix.GeneralLinearGroup.reindexMulEquiv
              (finSumFinEquiv (m := n) (n := m))
              (Matrix.GeneralLinearGroup.elementary (Sum.inl i) (Sum.inl j)
                (fun h => hij (by cases h; rfl)) a) := by
            rw [Matrix.GeneralLinearGroup.blockDiagonalOne_elementary]
      _ = Matrix.GeneralLinearGroup.elementary
              (finSumFinEquiv (Sum.inl i))
              (finSumFinEquiv (Sum.inl j))
              (fun h => hij
                (by
                  have h_inj :=
                    (finSumFinEquiv (m := n) (n := m)).injective h
                  cases h_inj; rfl)) a := by
            rw [Matrix.GeneralLinearGroup.reindexMulEquiv_elementary]
      _ = Matrix.GeneralLinearGroup.elementary (Fin.castAdd m i)
              (Fin.castAdd m j) hijCast a := by
            have h1 :
                (finSumFinEquiv (m := n) (n := m)) (Sum.inl i) =
                  Fin.castAdd m i :=
              finSumFinEquiv_apply_left (m := n) (n := m) (i := i)
            have h2 :
                (finSumFinEquiv (m := n) (n := m)) (Sum.inl j) =
                  Fin.castAdd m j :=
              finSumFinEquiv_apply_left (m := n) (n := m) (i := j)
            have h_eq :
                Matrix.GeneralLinearGroup.elementary
                  ((finSumFinEquiv (m := n) (n := m)) (Sum.inl i))
                  ((finSumFinEquiv (m := n) (n := m)) (Sum.inl j))
                  (fun h => hij
                    (by
                      have h_inj :=
                        (finSumFinEquiv (m := n) (n := m)).injective h
                      cases h_inj; rfl)) a
                = Matrix.GeneralLinearGroup.elementary (Fin.castAdd m i)
                    (Fin.castAdd m j) hijCast a := by
              apply Units.ext
              simp only [Matrix.GeneralLinearGroup.coe_elementary]
              rw [h1, h2]
            exact h_eq
  have h_of :
      StableGL.of
        (Matrix.GeneralLinearGroup.elementary (Fin.castAdd m i)
          (Fin.castAdd m j) hijCast a) =
        StableGL.of (Matrix.GeneralLinearGroup.elementary i j hij a) := by
    calc
      StableGL.of
            (Matrix.GeneralLinearGroup.elementary (Fin.castAdd m i)
              (Fin.castAdd m j) hijCast a)
          = StableGL.of
              (Matrix.GeneralLinearGroup.blockStabilization n m R
                (Matrix.GeneralLinearGroup.elementary i j hij a)) := by
            rw [← h_block]
      _ = StableGL.of (Matrix.GeneralLinearGroup.elementary i j hij a) :=
            StableGL.of_blockStabilization (n := n) (m := m)
              (Matrix.GeneralLinearGroup.elementary i j hij a)
  apply Subtype.ext
  simp only [StableE.coe_elementary]
  exact h_of

private theorem natElementary_of_lt (n i j : ℕ) (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (a : R) :
    natElementary (R := R) i j hij a =
      StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩
        (fun h => hij (congrArg Fin.val h)) a := by
  let k := max i j + 1
  have hk_le : k ≤ n := by
    have h_max_lt : max i j < n := (Nat.max_lt.mpr ⟨hi, hj⟩)
    exact Nat.succ_le_of_lt h_max_lt
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk_le
  have hi_k : i < k := Nat.lt_succ_of_le (Nat.le_max_left i j)
  have hj_k : j < k := Nat.lt_succ_of_le (Nat.le_max_right i j)
  have hij_k : (⟨i, hi_k⟩ : Fin k) ≠ ⟨j, hj_k⟩ :=
    fun h => hij (congrArg Fin.val h)
  have hij_n : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ :=
    fun h => hij (congrArg Fin.val h)
  have h_nat : natElementary (R := R) i j hij a =
      StableE.elementary k ⟨i, hi_k⟩ ⟨j, hj_k⟩ hij_k a := rfl
  have h_cast :
      StableE.elementary (k + m) (Fin.castAdd m ⟨i, hi_k⟩)
        (Fin.castAdd m ⟨j, hj_k⟩)
        (fun h =>
          hij_k (Fin.eq_of_val_eq
            (by simpa [Fin.val_castAdd] using congrArg Fin.val h))) a =
      StableE.elementary k ⟨i, hi_k⟩ ⟨j, hj_k⟩ hij_k a :=
    elementary_castAdd (n := k) (m := m) (i := ⟨i, hi_k⟩)
      (j := ⟨j, hj_k⟩) hij_k a
  have hm_symm : k + m = n := hm.symm
  have h_hm_subst :
      StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩ hij_n a =
      StableE.elementary (k + m) ⟨i, hm_symm ▸ hi⟩
          ⟨j, hm_symm ▸ hj⟩ (fun h => hij (congrArg Fin.val h)) a := by
    cases hm_symm
    rfl
  have h_i_eq :
      (Fin.castAdd m ⟨i, hi_k⟩ : Fin (k + m)) = ⟨i, hm_symm ▸ hi⟩ := by
    apply Fin.ext
    simp
  have h_j_eq :
      (Fin.castAdd m ⟨j, hj_k⟩ : Fin (k + m)) = ⟨j, hm_symm ▸ hj⟩ := by
    apply Fin.ext
    simp
  have h_rewrite :
      StableE.elementary (k + m) (Fin.castAdd m ⟨i, hi_k⟩)
        (Fin.castAdd m ⟨j, hj_k⟩)
        (fun h =>
          hij_k (Fin.eq_of_val_eq
            (by simpa [Fin.val_castAdd] using congrArg Fin.val h))) a =
      StableE.elementary (k + m) ⟨i, hm_symm ▸ hi⟩
          ⟨j, hm_symm ▸ hj⟩ (fun h => hij (congrArg Fin.val h)) a := by
    apply Subtype.ext
    simp only [StableE.coe_elementary]
    have h_eq_gl :
        (Matrix.GeneralLinearGroup.elementary (Fin.castAdd m ⟨i, hi_k⟩)
          (Fin.castAdd m ⟨j, hj_k⟩)
          (fun h =>
            hij_k (Fin.eq_of_val_eq
              (by simpa [Fin.val_castAdd] using congrArg Fin.val h))) a :
          Matrix.GeneralLinearGroup (Fin (k + m)) R).val
        = (Matrix.GeneralLinearGroup.elementary ⟨i, hm_symm ▸ hi⟩
            ⟨j, hm_symm ▸ hj⟩ (fun h => hij (congrArg Fin.val h)) a :
          Matrix.GeneralLinearGroup (Fin (k + m)) R).val := by
      simp only [Matrix.GeneralLinearGroup.coe_elementary]
      rw [h_i_eq, h_j_eq]
    have h_units :
        (Matrix.GeneralLinearGroup.elementary (Fin.castAdd m ⟨i, hi_k⟩)
          (Fin.castAdd m ⟨j, hj_k⟩)
          (fun h =>
            hij_k (Fin.eq_of_val_eq
              (by simpa [Fin.val_castAdd] using congrArg Fin.val h))) a :
          Matrix.GeneralLinearGroup (Fin (k + m)) R)
        = Matrix.GeneralLinearGroup.elementary ⟨i, hm_symm ▸ hi⟩
            ⟨j, hm_symm ▸ hj⟩ (fun h => hij (congrArg Fin.val h)) a := by
      apply Units.ext
      exact h_eq_gl
    rw [h_units]
  calc
    natElementary (R := R) i j hij a
      = StableE.elementary k ⟨i, hi_k⟩ ⟨j, hj_k⟩ hij_k a := h_nat
    _ = StableE.elementary (k + m) (Fin.castAdd m ⟨i, hi_k⟩)
            (Fin.castAdd m ⟨j, hj_k⟩) _ a := h_cast.symm
    _ = StableE.elementary (k + m) ⟨i, hm_symm ▸ hi⟩
            ⟨j, hm_symm ▸ hj⟩ _ a := h_rewrite
    _ = StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩ hij_n a :=
          h_hm_subst.symm

/-- Identification of `natElementary` with finite-level `elementary` via `Fin.val`. -/
@[simp]
theorem natElementary_fin (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R) :
    natElementary (R := R) i.val j.val
        (fun h => hij (Fin.eq_of_val_eq h)) a =
      StableE.elementary n i j hij a := by
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  have hij_nat : i.val ≠ j.val := fun h => hij (Fin.eq_of_val_eq h)
  have h :=
    natElementary_of_lt (R := R) (n := n) (i := i.val) (j := j.val)
      hi hj hij_nat a
  have h2 :
      StableE.elementary n ⟨i.val, hi⟩ ⟨j.val, hj⟩
        (fun h => hij_nat (congrArg Fin.val h)) a
      = StableE.elementary n i j hij a := by
    simp only [show (⟨i.val, hi⟩ : Fin n) = i from rfl,
      show (⟨j.val, hj⟩ : Fin n) = j from rfl]
  calc
    natElementary (R := R) i.val j.val hij_nat a
      = StableE.elementary n ⟨i.val, hi⟩ ⟨j.val, hj⟩ _ a := h
    _ = StableE.elementary n i j hij a := h2

/-- Functoriality of `natElementary` under ring homomorphisms. -/
@[simp]
theorem mapRingHom_natElementary {S : Type u} [Ring S] (f : R →+* S)
    (i j : ℕ) (hij : i ≠ j) (a : R) :
    mapRingHom (R := R) (S := S) f (natElementary (R := R) i j hij a) =
      natElementary (R := S) i j hij (f a) := by
  simp only [natElementary, mapRingHom_elementary]

end StableE

end AlgebraicKTheory

end
