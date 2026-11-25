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

public import MathlibExt.KTheory.Ring.K2.StableFiniteStageImage
public import MathlibExt.KTheory.Ring.K2.StableProductOneRange
public import MathlibExt.KTheory.Ring.K2.StableSteinbergRootSubgroups

/-! # Torus image of the canonical `(0,1)`-torus in `E∞`

Identification of `toStableE (h_{01}(u))` with the finite `diag₂` representative and
multiplicativity in the unit argument. The six-factor decomposition of `diag₂` is
provided by `Matrix.SpecialLinearGroup.toGL_diag2_eq_six_elementary`.
Also covers the boundary torus `h_{i,n}`
specialization and that the finite product of
its images is the stabilized reindexed
product-one diagonal.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {F : Type u} [Field F]

/-- Image of the canonical `(0,1)` torus in the stable elementary group.

This identifies `toStableE (h_{01}(u))` with the `Fin 2` finite representative
`diag₂(u)` viewed in `E∞` via `StableE.fromFinite`. -/
theorem toStableE_torus_zero_one (u : Fˣ) :
    toStableE (torus (R := F) 0 1 (by omega) u) =
      StableE.fromFinite F 2
        ⟨Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero),
          Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
            (show (0 : Fin 2) ≠ 1 by decide) (u : F) u.ne_zero⟩ := by
  have h01 : ∀ a : F, StableE.natElementary (R := F) 0 1 (by omega) a =
      StableE.elementary (R := F) 2 0 1 (by decide) a := by
    intro a
    have h := StableE.natElementary_fin (R := F) (n := 2)
      (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) a
    have h' : StableE.natElementary (R := F) 0 1
        (fun h : (0 : ℕ) = 1 => (show (0 : Fin 2) ≠ 1 by decide)
          (Fin.eq_of_val_eq h)) a =
        StableE.elementary (R := F) 2 (0 : Fin 2) (1 : Fin 2) (by decide) a := h
    have h_eq : (by omega : (0 : ℕ) ≠ 1) =
        fun h : (0 : ℕ) = 1 => (show (0 : Fin 2) ≠ 1 by decide)
          (Fin.eq_of_val_eq h) := Subsingleton.elim _ _
    rw [← h_eq] at h'
    exact h'
  have h10 : ∀ a : F, StableE.natElementary (R := F) 1 0 (by omega) a =
      StableE.elementary (R := F) 2 1 0 (by decide) a := by
    intro a
    have h := StableE.natElementary_fin (R := F) (n := 2)
      (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide) a
    have h' : StableE.natElementary (R := F) 1 0
        (fun h : (1 : ℕ) = 0 => (show (1 : Fin 2) ≠ 0 by decide)
          (Fin.eq_of_val_eq h)) a =
        StableE.elementary (R := F) 2 (1 : Fin 2) (0 : Fin 2) (by decide) a := h
    have h_eq : (by omega : (1 : ℕ) ≠ 0) =
        fun h : (1 : ℕ) = 0 => (show (1 : Fin 2) ≠ 0 by decide)
          (Fin.eq_of_val_eq h) := Subsingleton.elim _ _
    rw [← h_eq] at h'
    exact h'
  have h_sub :
      (⟨Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero),
        Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
          (show (0 : Fin 2) ≠ 1 by decide) (u : F) u.ne_zero⟩ :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin 2) F) =
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (0 : Fin 2) (1 : Fin 2) (by decide) (u : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (1 : Fin 2) (0 : Fin 2) (by decide) (-((u : F)⁻¹)) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (0 : Fin 2) (1 : Fin 2) (by decide) (u : F)) *
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (0 : Fin 2) (1 : Fin 2) (by decide) (-1 : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (1 : Fin 2) (0 : Fin 2) (by decide) (1 : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
          (0 : Fin 2) (1 : Fin 2) (by decide) (-1 : F)) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,
      Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
      Matrix.SpecialLinearGroup.toGL_diag2_eq_six_elementary, mul_assoc]
  have h_congr := congrArg (StableE.fromFinite F 2) h_sub
  have h_neg_one : (↑(-1 : Fˣ) : F) = (-1 : F) := by simp
  simp only [toStableE_torus, map_mul, StableE.fromFinite_elementary,
    Units.val_inv_eq_inv_val] at h_congr ⊢
  simp only [h01, h10, h_neg_one] at h_congr ⊢
  simp only [inv_neg, inv_one, neg_neg] at h_congr ⊢
  exact h_congr.symm

/-- Multiplicativity of the projected `(0,1)` torus in the stable elementary group. -/
@[simp, nolint simpNF]
theorem toStableE_torus_zero_one_mul (u v : Fˣ) :
    toStableE (torus (R := F) 0 1 (by omega) (u * v)) =
      toStableE (torus (R := F) 0 1 (by omega) u) *
        toStableE (torus (R := F) 0 1 (by omega) v) := by
  simp only [toStableE_torus_zero_one]
  rw [← map_mul]
  apply congrArg
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.diag2_coe, Units.val_mul, mul_comm]

/-- Rank-two torus image is trivial iff the unit is trivial.

Uses `toStableE_torus_zero_one`, `fromFinite` injectivity at `2`,
and `diag2` entrywise equality. `mpr` simplifies from `u=1`.
-/
theorem toStableE_torus_zero_one_eq_one_iff (u : Fˣ) :
    toStableE (torus (R := F) 0 1 (by omega) u) = 1 ↔ u = 1 := by
  constructor
  · intro h
    have h_eq := toStableE_torus_zero_one (F := F) u
    have h_fin_one := h_eq.symm.trans h
    have h_fin :=
      h_fin_one.trans (map_one (StableE.fromFinite F 2)).symm
    have h_sub :=
      StableE.fromFinite_injective (R := F) 2 h_fin
    have h_gl : (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) F) = 1 := by
      have h_val := congrArg Subtype.val h_sub
      simpa using h_val
    have h_mat : (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) F).val =
        (1 : Matrix (Fin 2) (Fin 2) F) := by
      have h1 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F =>
        (g : Matrix (Fin 2) (Fin 2) F)) h_gl
      exact h1
    have h_diag :
        Matrix.diagonal (fun i : Fin 2 => match i with
          | 0 => (u : F) | 1 => (u : F)⁻¹) =
          (1 : Matrix (Fin 2) (Fin 2) F) := by
      have h1 : (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero).1 =
          (1 : Matrix (Fin 2) (Fin 2) F) := by
        simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h_mat
      calc Matrix.diagonal (fun i : Fin 2 => match i with
            | 0 => (u : F) | 1 => (u : F)⁻¹)
          = (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero).1 :=
            (Matrix.SpecialLinearGroup.diag2_coe (u : F) u.ne_zero).symm
        _ = _ := h1
    have h_entry : (u : F) = 1 := by
      have he := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h_diag
      simpa using he
    exact Units.ext h_entry
  · rintro rfl
    have h_eq_one := toStableE_torus_zero_one (F := F) (1 : Fˣ)
    have h_sub_one : (⟨Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2 (1 : F) one_ne_zero),
      Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
        (show (0 : Fin 2) ≠ 1 by decide) (1 : F) one_ne_zero⟩ :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin 2) F) = 1 := by
      apply Subtype.ext
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
          Matrix.SpecialLinearGroup.diag2_coe]
    have h_to : toStableE (torus (R := F) 0 1 (by omega) (1 : Fˣ)) =
        StableE.fromFinite F 2 1 := by
      have h1 := h_eq_one
      have h2 : StableE.fromFinite F 2
          ⟨Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.diag2 (1 : F) one_ne_zero),
            Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
              (show (0 : Fin 2) ≠ 1 by decide) (1 : F) one_ne_zero⟩ =
          StableE.fromFinite F 2 1 := by
        have h := congrArg (StableE.fromFinite F 2) h_sub_one
        exact h
      exact h1.trans h2
    have h_final : toStableE (torus (R := F) 0 1 (by omega) (1 : Fˣ)) = 1 := by
      have h1 := h_to
      have h2 := map_one (StableE.fromFinite F 2)
      exact h1.trans h2
    exact h_final

/-- Image of arbitrary `(i,j)`-torus in `E∞`.

Identifies `toStableE (h_{ij}(u))` with finite-rank representative
`diag₂ₙ` at rank `max i j + 1` via `fromFinite`, using
`toGL_diag2n_eq_reindex_blockDiagonalOne_diag2` and six-elementary
`toGL_diag2_eq_six_elementary`. Valid in characteristic two; no
injectivity of `toStableE` is claimed. Supports later
boundary-torus/product-one arguments.
-/
theorem toStableE_torus_general (i j : ℕ) (hij : i ≠ j) (u : Fˣ) :
    toStableE (torus (R := F) i j hij u) =
      StableE.fromFinite F (max i j + 1)
        ⟨Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.diag2n
              (show (⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩ :
                Fin (max i j + 1)) ≠
                ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩ from
                fun h => hij (congrArg Fin.val h)) (u : F) u.ne_zero),
          Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
            (show (⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩ :
              Fin (max i j + 1)) ≠
              ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩ from
              fun h => hij (congrArg Fin.val h)) (u : F) u.ne_zero⟩ := by
  let N := max i j + 1
  have hi : i < N := Nat.lt_succ_of_le (Nat.le_max_left i j)
  have hj : j < N := Nat.lt_succ_of_le (Nat.le_max_right i j)
  let iF : Fin N := ⟨i, hi⟩
  let jF : Fin N := ⟨j, hj⟩
  have hijF : iF ≠ jF := fun h => hij (congrArg Fin.val h)
  have h_ij : ∀ a : F, StableE.natElementary (R := F) i j hij a =
      StableE.elementary N iF jF hijF a := by
    intro a
    have hb := StableE.natElementary_fin (n := N) iF jF hijF a
    have heq : (fun h : i = j => hijF (Fin.eq_of_val_eq h)) = hij :=
      Subsingleton.elim _ _
    calc StableE.natElementary (R := F) i j hij a
        = StableE.natElementary (R := F) i j
          (fun h : i = j => hijF (Fin.eq_of_val_eq h)) a := by rw [heq]
      _ = StableE.elementary (R := F) N iF jF hijF a := hb
  have h_ji : ∀ a : F, StableE.natElementary (R := F) j i hij.symm a =
      StableE.elementary N jF iF hijF.symm a := by
    intro a
    have hb := StableE.natElementary_fin (n := N) jF iF hijF.symm a
    have heq : (fun h : j = i => hijF.symm (Fin.eq_of_val_eq h)) =
        hij.symm := Subsingleton.elim _ _
    calc StableE.natElementary (R := F) j i hij.symm a
        = StableE.natElementary (R := F) j i
          (fun h : j = i => hijF.symm (Fin.eq_of_val_eq h)) a := by rw [heq]
      _ = StableE.elementary (R := F) N jF iF hijF.symm a := hb
  have h_reidx :
      (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2n hijF (u : F) u.ne_zero) :
        Matrix.GeneralLinearGroup (Fin N) F) =
      Matrix.GeneralLinearGroup.reindexMulEquiv
        (Matrix.SpecialLinearGroup.pairComplEquiv hijF)
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
          {k // ¬(k = iF ∨ k = jF)} F
          (Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero))) :=
    Matrix.SpecialLinearGroup.toGL_diag2n_eq_reindex_blockDiagonalOne_diag2
      hijF u
  have h_six :
      (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) F) =
      Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
        Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero (-((u : F)⁻¹)) *
          Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
            Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1 : F) *
              Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero (1 : F) *
                Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1 : F) :=
    Matrix.SpecialLinearGroup.toGL_diag2_eq_six_elementary u
  have h_sub :
      (⟨Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2n hijF (u : F) u.ne_zero),
        Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup hijF
          (u : F) u.ne_zero⟩ :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin N) F) =
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF
        (u : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary jF iF
        hijF.symm (-((u : F)⁻¹)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF
        (u : F) *
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF
        (-1 : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary jF iF
          hijF.symm (1 : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF
          (-1 : F)) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,
      Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
      h_reidx, h_six, map_mul,
      Matrix.GeneralLinearGroup.blockDiagonalOne_elementary,
      Matrix.GeneralLinearGroup.reindexMulEquiv_elementary]
    have hi_eq : (Matrix.SpecialLinearGroup.pairComplEquiv hijF)
        (Sum.inl (0 : Fin 2)) = iF :=
      (congrArg (Matrix.SpecialLinearGroup.pairComplEquiv hijF)
        (Matrix.SpecialLinearGroup.pairComplEquiv_symm_apply_i hijF).symm).trans
        (Equiv.apply_symm_apply (Matrix.SpecialLinearGroup.pairComplEquiv hijF) iF)
    have hj_eq : (Matrix.SpecialLinearGroup.pairComplEquiv hijF)
        (Sum.inl (1 : Fin 2)) = jF :=
      (congrArg (Matrix.SpecialLinearGroup.pairComplEquiv hijF)
        (Matrix.SpecialLinearGroup.pairComplEquiv_symm_apply_j hijF).symm).trans
        (Equiv.apply_symm_apply (Matrix.SpecialLinearGroup.pairComplEquiv hijF) jF)
    simp only [hi_eq, hj_eq, mul_assoc]
  have h_congr := congrArg (StableE.fromFinite F N) h_sub
  have h_n1 : (↑(-1 : Fˣ) : F) = (-1 : F) := by simp
  simp only [toStableE_torus, map_mul, StableE.fromFinite_elementary,
    Units.val_inv_eq_inv_val] at h_congr ⊢
  simp only [h_ij, h_ji, h_n1] at h_congr ⊢
  simp only [inv_neg, inv_one, neg_neg] at h_congr ⊢
  exact h_congr.symm

/-- Multiplicativity of the torus image in the stable elementary group.

For field `F`, indices `i ≠ j`, and units `u v`, `toStableE (torus (u*v))`
equals `toStableE (torus u) * toStableE (torus v)` with exact orientation.
This holds only in the stable elementary image `E∞`; it does not assert
exact torus multiplicativity in StableSteinberg, whose defect is central.
Valid in characteristic two at rank `max i j + 1`.
-/
theorem toStableE_torus_general_mul (i j : ℕ) (hij : i ≠ j) (u v : Fˣ) :
    toStableE (torus (R := F) i j hij (u * v)) =
      toStableE (torus (R := F) i j hij u) *
        toStableE (torus (R := F) i j hij v) := by
  let N := max i j + 1
  have hi : i < N := Nat.lt_succ_of_le (Nat.le_max_left i j)
  have hj : j < N := Nat.lt_succ_of_le (Nat.le_max_right i j)
  let iF : Fin N := ⟨i, hi⟩
  let jF : Fin N := ⟨j, hj⟩
  have hijF : iF ≠ jF := fun h => hij (congrArg Fin.val h)
  simp only [toStableE_torus_general (i := i) (j := j) (hij := hij) u,
    toStableE_torus_general (i := i) (j := j) (hij := hij) v,
    toStableE_torus_general (i := i) (j := j) (hij := hij) (u * v)]
  rw [← map_mul]
  apply congrArg
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have h_sl :
      Matrix.SpecialLinearGroup.diag2n hijF (↑(u * v) : F)
        (u * v).ne_zero =
        Matrix.SpecialLinearGroup.diag2n hijF (↑u : F) u.ne_zero *
          Matrix.SpecialLinearGroup.diag2n hijF (↑v : F) v.ne_zero := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.diag2n_coe,
      Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext k
    by_cases hk_i : k = iF
    · subst hk_i
      simp [Units.val_mul]
    · by_cases hk_j : k = jF
      · subst hk_j
        simp [hk_i, Units.val_mul, mul_comm]
      · simp [hk_i, hk_j]
  have h_gl := congrArg Matrix.SpecialLinearGroup.toGL h_sl
  simp only [map_mul] at h_gl
  exact h_gl

/-- Boundary at last index: `i<n` gives `h_{i,n}(u)` in `n+1` as `diag2n`
via `toStableE_torus_general`/`max_eq_right`; n=0 vac, n=1 ok, char2. -/
theorem toStableE_torus_nat_last (n i : ℕ) (hi : i < n) (u : Fˣ) :
    toStableE (torus i n (Nat.ne_of_lt hi) u) =
      StableE.fromFinite F (n + 1)
        ⟨Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.diag2n
              (show (⟨i, Nat.lt_succ_of_le
                (Nat.le_of_lt hi)⟩ : Fin (n + 1)) ≠
                ⟨n, Nat.lt_succ_self n⟩ from
                fun h => Nat.ne_of_lt hi (congrArg Fin.val h))
              (u : F) u.ne_zero),
          Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
            _ (u : F) u.ne_zero⟩ := by
  let N := n + 1
  have hiN : i < N := Nat.lt_succ_of_le (Nat.le_of_lt hi)
  have hnN : n < N := Nat.lt_succ_self n
  let iF : Fin N := ⟨i, hiN⟩
  let jF : Fin N := ⟨n, hnN⟩
  have hijF : iF ≠ jF := fun h => Nat.ne_of_lt hi (congrArg Fin.val h)
  have h_ij : ∀ a : F, StableE.natElementary (R := F) i n (Nat.ne_of_lt hi) a =
      StableE.elementary N iF jF hijF a := by
    intro a
    have hb := StableE.natElementary_fin (n := N) iF jF hijF a
    have heq : (fun h : i = n => hijF (Fin.eq_of_val_eq h)) = Nat.ne_of_lt hi :=
      Subsingleton.elim _ _
    calc StableE.natElementary (R := F) i n (Nat.ne_of_lt hi) a
        = StableE.natElementary (R := F) i n (fun h => hijF (Fin.eq_of_val_eq h)) a := by rw [heq]
      _ = _ := hb
  have h_ji : ∀ a : F, StableE.natElementary (R := F) n i (Ne.symm (Nat.ne_of_lt hi)) a =
      StableE.elementary N jF iF hijF.symm a := by
    intro a
    have hb := StableE.natElementary_fin (n := N) jF iF hijF.symm a
    have heq : (fun h : n = i => hijF.symm (Fin.eq_of_val_eq h)) =
        Ne.symm (Nat.ne_of_lt hi) := Subsingleton.elim _ _
    calc StableE.natElementary (R := F) n i (Ne.symm (Nat.ne_of_lt hi)) a
        = StableE.natElementary (R := F) n i
          (fun h => hijF.symm (Fin.eq_of_val_eq h)) a := by rw [heq]
      _ = _ := hb
  have h_reidx :
      (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2n hijF (u : F) u.ne_zero) :
        Matrix.GeneralLinearGroup (Fin N) F) =
      Matrix.GeneralLinearGroup.reindexMulEquiv (Matrix.SpecialLinearGroup.pairComplEquiv hijF)
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2) {k // ¬(k = iF ∨ k = jF)} F
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero))) :=
    Matrix.SpecialLinearGroup.toGL_diag2n_eq_reindex_blockDiagonalOne_diag2 hijF u
  have h_six : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2 (u : F) u.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) F) =
      Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
        Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero (-((u : F)⁻¹)) *
          Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
            Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1 : F) *
              Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero (1 : F) *
                Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1 : F) :=
    Matrix.SpecialLinearGroup.toGL_diag2_eq_six_elementary u
  have h_sub :
      (⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2n hijF (u : F) u.ne_zero),
        Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup hijF (u : F) u.ne_zero⟩ :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin N) F) =
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF (u : F) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary jF iF hijF.symm (-((u : F)⁻¹)) *
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF (u : F) *
      (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF (-1 : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary jF iF hijF.symm (1 : F) *
        Matrix.GeneralLinearGroup.ElementarySubgroup.elementary iF jF hijF (-1 : F)) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.ElementarySubgroup.coe_elementary,
      h_reidx, h_six, map_mul, Matrix.GeneralLinearGroup.blockDiagonalOne_elementary,
      Matrix.GeneralLinearGroup.reindexMulEquiv_elementary]
    have hi_eq : (Matrix.SpecialLinearGroup.pairComplEquiv hijF) (Sum.inl (0 : Fin 2)) = iF :=
      (congrArg _ (Matrix.SpecialLinearGroup.pairComplEquiv_symm_apply_i hijF).symm).trans
        (Equiv.apply_symm_apply _ iF)
    have hj_eq : (Matrix.SpecialLinearGroup.pairComplEquiv hijF) (Sum.inl (1 : Fin 2)) = jF :=
      (congrArg _ (Matrix.SpecialLinearGroup.pairComplEquiv_symm_apply_j hijF).symm).trans
        (Equiv.apply_symm_apply _ jF)
    simp only [hi_eq, hj_eq, mul_assoc]
  have h_congr := congrArg (StableE.fromFinite F N) h_sub
  have h_n1 : (↑(-1 : Fˣ) : F) = (-1 : F) := by simp
  simp only [toStableE_torus, map_mul, StableE.fromFinite_elementary,
    Units.val_inv_eq_inv_val] at h_congr ⊢
  simp only [h_ij, h_ji, h_n1] at h_congr ⊢
  simp only [inv_neg, inv_one, neg_neg] at h_congr ⊢
  exact h_congr.symm

/-- Fin wrapper: `castSucc`/`last` boundary specialization, char2, n=0 vacuous. -/
theorem toStableE_torus_fin_last (n : ℕ) (i : Fin n) (u : Fˣ) :
    toStableE (torus i.val n (Nat.ne_of_lt i.isLt) u) =
      StableE.fromFinite F (n + 1)
        ⟨Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.diag2n
              (show i.castSucc ≠ Fin.last n from
                fun h => Nat.ne_of_lt i.isLt (congrArg Fin.val h))
              (u : F) u.ne_zero),
          Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
            _ (u : F) u.ne_zero⟩ := by
  have hi : i.val < n := i.isLt
  have h := toStableE_torus_nat_last (F := F) n i.val hi u
  calc toStableE (torus i.val n (Nat.ne_of_lt hi) u) = _ := h
    _ = _ := by
        apply congrArg
        apply Subtype.ext
        apply Units.ext
        rfl

/-- Pairwise commutativity of boundary torus
images after `toStableE` for `i : Fin n`.
Uniform for `n = 0`, characteristic-two
safe, supplies the commutativity witness
for `Finset.noncommProd`.
Holds only after `toStableE`; does not assert
commutativity in `StableSteinberg`.
-/
theorem toStableE_torus_fin_last_pairwise_commute (n : ℕ)
    (u : Fin n → Fˣ) :
    Set.Pairwise (↑(Finset.univ (α := Fin n)) : Set (Fin n))
      (Function.onFun Commute fun i =>
        toStableE (torus i.val n (Nat.ne_of_lt i.isLt) (u i))) := by
  intro i _ j _ _
  change Commute (toStableE (torus i.val n (Nat.ne_of_lt i.isLt) (u i)))
      (toStableE (torus j.val n (Nat.ne_of_lt j.isLt) (u j)))
  have hi := toStableE_torus_fin_last (F := F) n i (u i)
  have hj := toStableE_torus_fin_last (F := F) n j (u j)
  rw [hi, hj]
  let A : Fin n → Matrix.GeneralLinearGroup (Fin (n + 1)) F := fun k =>
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2n
      (show k.castSucc ≠ Fin.last n from
        fun h => Nat.ne_of_lt k.isLt (congrArg Fin.val h))
      (u k : F) (u k).ne_zero)
  have hA : Commute (A i) (A j) := by
    simp only [A]
    apply Units.ext
    simp only [Units.val_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact @mul_comm F _ _ _
  let g : Fin n →
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F :=
    fun k => ⟨A k, Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
      (show k.castSucc ≠ Fin.last n from
        fun h => Nat.ne_of_lt k.isLt (congrArg Fin.val h))
      (u k : F) (u k).ne_zero⟩
  have hg : g i * g j = g j * g i := by
    apply Subtype.ext; simp only [Subgroup.coe_mul]; exact hA.eq
  change StableE.fromFinite F (n + 1) (g i) *
      StableE.fromFinite F (n + 1) (g j) =
      StableE.fromFinite F (n + 1) (g j) *
        StableE.fromFinite F (n + 1) (g i)
  rw [← map_mul, ← map_mul, hg]

/-- Finite product of boundary torus images equals the
`fromFinite (n+1)` image of the product-one diagonal reindexed by
`finSumFinEquiv (m := n) (n := 1)`.

Orientation: `∏ i, toStableE (torus i.val n _ (u i)) =
fromFinite F (n+1) (reindex finSumFinEquiv (diagonalUnitsHom
(productOneDiagonal u)))`.

Uniform for `n = 0` (empty product is `1`) and valid in
characteristic two. This holds only after `toStableE`; it does not
claim exact torus multiplication in `StableSteinberg`, whose defect is
central. -/
theorem toStableE_torus_fin_last_prod_eq_reindex_productOneDiagonal
    (n : ℕ) (u : Fin n → Fˣ) :
    (Finset.univ.noncommProd
      (fun i : Fin n => toStableE (torus i.val n
        (Nat.ne_of_lt i.isLt) (u i)))
      (toStableE_torus_fin_last_pairwise_commute (F := F) n u)) =
    StableE.fromFinite F (n + 1)
      ⟨Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := 1))
          (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n ⊕ Fin 1)
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u)),
        Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup
          (finSumFinEquiv (m := n) (n := 1))
          (Matrix.GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
            (F := F) u)⟩ := by
  let e := finSumFinEquiv (m := n) (n := 1)
  let fU := Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u
  let dGL := Matrix.GeneralLinearGroup.diagonalUnitsHom F _ fU
  have h_diag : dGL ∈
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin n ⊕ Fin 1) F :=
    Matrix.GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
      (F := F) u
  have h_reidx : Matrix.GeneralLinearGroup.reindexMulEquiv e dGL ∈
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F :=
    Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup e h_diag
  let A : Fin n → Matrix.GeneralLinearGroup (Fin (n + 1)) F := fun k =>
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2n
      (Fin.castSucc_ne_last k) (u k : F) (u k).ne_zero)
  let g : Fin n →
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F :=
    fun k => ⟨A k, Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
      (Fin.castSucc_ne_last k) (u k : F) (u k).ne_zero⟩
  have hA : Set.Pairwise (↑(Finset.univ (α := Fin n)) : Set (Fin n))
      (Function.onFun Commute A) := by
    intro i _ j _ _
    simp only [A]
    apply Units.ext
    simp only [Units.val_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact @mul_comm F _ _ _
  have hG : Set.Pairwise (↑(Finset.univ (α := Fin n)) : Set (Fin n))
      (Function.onFun Commute g) := by
    intro i hi j hj hij; have h := hA hi hj hij
    apply Subtype.ext; simp only [Subgroup.coe_mul]; exact h.eq
  have h_torus : ∀ i : Fin n, toStableE (torus i.val n
      (Nat.ne_of_lt i.isLt) (u i)) = StableE.fromFinite F (n + 1) (g i) := by
    intro i; have h0 := toStableE_torus_fin_last (F := F) n i (u i)
    have h_eq : (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2n
          (show i.castSucc ≠ Fin.last n from
            fun h => Nat.ne_of_lt i.isLt (congrArg Fin.val h))
          (u i : F) (u i).ne_zero) : Matrix.GeneralLinearGroup
        (Fin (n + 1)) F) = A i := by apply Units.ext; rfl
    calc toStableE (torus i.val n (Nat.ne_of_lt i.isLt) (u i))
        = StableE.fromFinite F (n + 1) ⟨Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.diag2n
              (show i.castSucc ≠ Fin.last n from
                fun h => Nat.ne_of_lt i.isLt (congrArg Fin.val h))
              (u i : F) (u i).ne_zero),
            Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
              _ (u i : F) (u i).ne_zero⟩ := h0
      _ = StableE.fromFinite F (n + 1) (g i) := by
            apply congrArg (StableE.fromFinite F (n + 1))
            apply Subtype.ext
            exact h_eq
  have h_bnd :=
    Matrix.GeneralLinearGroup.boundary_diag2n_prod_eq_reindex_diagonalUnitsHom_productOneDiagonal
      (F := F) (n := n) u
  have h_sub : ((Finset.univ.noncommProd g hG :
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F) =
      Finset.univ.noncommProd A hA := by
    have hp : Set.Pairwise (↑(Finset.univ (α := Fin n)) : Set (Fin n))
        (Function.onFun Commute fun i =>
          (Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F).subtype
            (g i)) := by
      intro i hi j hj hij
      exact (hG hi hj hij).map _
    have hm := Finset.map_noncommProd Finset.univ g hG
      (Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F).subtype
    have h_pair : (fun _ hx _ hy _ => (hG.forall₂ hx hy).map
        (Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F).subtype) =
        hp := Subsingleton.elim _ _
    rw [h_pair] at hm
    have h_congr : Finset.univ.noncommProd
        (fun i => (Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F).subtype
          (g i)) hp = Finset.univ.noncommProd A hA := by
      apply Finset.noncommProd_congr rfl
      intro i _
      rfl
    rw [h_congr] at hm
    exact hm
  have h_g : Finset.univ.noncommProd g hG =
      ⟨Matrix.GeneralLinearGroup.reindexMulEquiv e dGL, h_reidx⟩ := by
    apply Subtype.ext; calc ((Finset.univ.noncommProd g hG :
        Matrix.GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) F) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) F)
        = Finset.univ.noncommProd A hA := h_sub
      _ = Matrix.GeneralLinearGroup.reindexMulEquiv e dGL := h_bnd
  calc (Finset.univ.noncommProd
      (fun i : Fin n => toStableE (torus i.val n
        (Nat.ne_of_lt i.isLt) (u i)))
      (toStableE_torus_fin_last_pairwise_commute (F := F) n u))
      = Finset.univ.noncommProd (fun i => StableE.fromFinite F (n + 1)
          (g i)) _ := by
        apply Finset.noncommProd_congr rfl; intro k _; exact h_torus k
    _ = StableE.fromFinite F (n + 1) (Finset.univ.noncommProd g hG) := by
        rw [← Finset.map_noncommProd]
    _ = StableE.fromFinite F (n + 1)
          ⟨Matrix.GeneralLinearGroup.reindexMulEquiv e dGL, h_reidx⟩ := by
        rw [h_g]

/-- Fixed-coordinate boundary torus hom into `StableE`. -/
public noncomputable def toStableETorusFinLastHom (n : ℕ)
    (i : Fin n) : Fˣ →* StableE F where
  toFun u := toStableE (torus i.val n (Nat.ne_of_lt i.isLt) u)
  map_one' := by
    have h_eq := toStableE_torus_fin_last (F := F) n i (1 : Fˣ)
    have h_fun : (fun k : Fin (n + 1) =>
        if k = i.castSucc then (1 : F)
        else if k = Fin.last n then (1 : F)⁻¹ else (1 : F)) =
        fun _ => (1 : F) := by
      funext k
      by_cases hk : k = i.castSucc
      · simp [hk]
      · simp [hk]
    have h_val : (Matrix.SpecialLinearGroup.diag2n
        (Fin.castSucc_ne_last i) (1 : F) one_ne_zero).1 =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := by
      simp only [Matrix.SpecialLinearGroup.diag2n_coe, h_fun,
        Matrix.diagonal_one]
    have h_one : Matrix.SpecialLinearGroup.diag2n
        (Fin.castSucc_ne_last i) (1 : F) one_ne_zero = 1 :=
      Subtype.ext h_val
    have h_gl : Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2n
          (Fin.castSucc_ne_last i) (1 : F) one_ne_zero) =
        (1 : Matrix.GeneralLinearGroup (Fin (n + 1)) F) := by
      apply Units.ext
      exact h_val
    have h_sub : (⟨Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2n
          (Fin.castSucc_ne_last i) (1 : F) one_ne_zero),
        Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
          (Fin.castSucc_ne_last i) (1 : F) one_ne_zero⟩ :
        Matrix.GeneralLinearGroup.elementarySubgroup
          (Fin (n + 1)) F) = 1 := by
      exact Subtype.ext h_gl
    calc toStableE (torus i.val n (Nat.ne_of_lt i.isLt) (1 : Fˣ))
        = StableE.fromFinite F (n + 1)
          ⟨Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.diag2n
              (Fin.castSucc_ne_last i) (1 : F) one_ne_zero),
            Matrix.SpecialLinearGroup.toGL_diag2n_mem_elementarySubgroup
              (Fin.castSucc_ne_last i) (1 : F) one_ne_zero⟩ := h_eq
      _ = StableE.fromFinite F (n + 1) 1 := by rw [h_sub]
      _ = 1 := map_one _
  map_mul' u v :=
    toStableE_torus_general_mul i.val n (Nat.ne_of_lt i.isLt) u v

/-- Deprecated alias for `toStableETorusFinLastHom`. -/
@[deprecated toStableETorusFinLastHom (since := "2026-10-23"),
  nolint defsWithUnderscore]
alias toStableE_torus_fin_last_hom := toStableETorusFinLastHom

theorem toStableE_torus_fin_last_hom_pairwise_commute (n : ℕ) :
    Pairwise fun i j : Fin n =>
      ∀ x y : Fˣ, Commute
        (toStableETorusFinLastHom (F := F) n i x)
        (toStableETorusFinLastHom (F := F) n j y) := by
  intro i j hij x y
  let u : Fin n → Fˣ := fun k =>
    if k = i then x else if k = j then y else 1
  have h_ui : u i = x := by
    dsimp only [u]
    rw [ite_eq_left rfl]
  have h_uj : u j = y := by
    dsimp only [u]
    have hji : j ≠ i := Ne.symm hij
    rw [ite_eq_right hji, ite_eq_left rfl]
  have h_pair := toStableE_torus_fin_last_pairwise_commute (F := F) n u
  have h_mem_i : i ∈ (Finset.univ (α := Fin n) : Set (Fin n)) := by
    simp
  have h_mem_j : j ∈ (Finset.univ (α := Fin n) : Set (Fin n)) := by
    simp
  have h_c : Commute
      (toStableE (torus i.val n (Nat.ne_of_lt i.isLt) (u i)))
      (toStableE (torus j.val n (Nat.ne_of_lt j.isLt) (u j))) :=
    h_pair h_mem_i h_mem_j hij
  rw [h_ui, h_uj] at h_c
  exact h_c

/-- Assembled boundary torus product hom `(Fin n → Fˣ) →* StableE F`. -/
@[nolint defsWithUnderscore]
public noncomputable def toStableE_torus_fin_last_piHom (n : ℕ) :
    (Fin n → Fˣ) →* StableE F :=
  MonoidHom.noncommPiCoprod
    (fun i => toStableETorusFinLastHom (F := F) n i)
    (toStableE_torus_fin_last_hom_pairwise_commute (F := F) n)

@[simp]
public theorem toStableE_torus_fin_last_piHom_mulSingle (n : ℕ)
    (i : Fin n) (u : Fˣ) :
    toStableE_torus_fin_last_piHom (F := F) n (Pi.mulSingle i u) =
      toStableE (torus i.val n (Nat.ne_of_lt i.isLt) u) := by
  have h : toStableE_torus_fin_last_piHom (F := F) n
      (Pi.mulSingle i u) =
      toStableETorusFinLastHom (F := F) n i u := by
    exact MonoidHom.noncommPiCoprod_mulSingle
      (ϕ := fun j => toStableETorusFinLastHom (F := F) n j)
      (hcomm := toStableE_torus_fin_last_hom_pairwise_commute
        (F := F) n) i u
  calc toStableE_torus_fin_last_piHom (F := F) n (Pi.mulSingle i u)
      = toStableETorusFinLastHom (F := F) n i u := h
    _ = toStableE (torus i.val n (Nat.ne_of_lt i.isLt) u) := rfl

/-- Range of `toStableE_torus_fin_last_piHom` equals the image of
`boundaryTorusSubgroup` under `toStableE`. Uniform for `n = 0` and
valid in characteristic two. Holds only after `toStableE`; does not
assert commutativity or product equality in `StableSteinberg`. -/
public theorem toStableE_torus_fin_last_piHom_range (n : ℕ) :
    (toStableE_torus_fin_last_piHom (F := F) n).range =
      (boundaryTorusSubgroup (R := F) n).map
        (toStableE (R := F)) := by
  apply le_antisymm
  · rw [toStableE_torus_fin_last_piHom,
        MonoidHom.noncommPiCoprod_range]
    apply iSup_le
    intro i y hy
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hy
    rw [← hu]
    have h_mem : torus (R := F) i.val n
        (Nat.ne_of_lt i.isLt) u ∈
        boundaryTorusSubgroup (R := F) n := by
      apply Subgroup.subset_closure
      exact ⟨i.val, i.isLt, Nat.ne_of_lt i.isLt, u, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨torus (R := F) i.val n (Nat.ne_of_lt i.isLt) u, h_mem, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    unfold boundaryTorusSubgroup
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨i, hi, hij, u, rfl⟩ := hg
    change toStableE (torus (R:=F) i n hij u) ∈
        (toStableE_torus_fin_last_piHom (F:=F) n).range
    have h_hij : hij = Nat.ne_of_lt hi :=
      Subsingleton.elim _ _
    have h_eq : torus (R := F) i n hij u =
        torus (R := F) i n (Nat.ne_of_lt hi) u := by
      rw [h_hij]
    rw [h_eq]
    let iFin : Fin n := ⟨i, hi⟩
    have h_range :
        toStableE (R := F)
          (torus (R := F) iFin.val n
            (Nat.ne_of_lt iFin.isLt) u) ∈
          (toStableE_torus_fin_last_piHom (F := F) n).range := by
      have h_mul := toStableE_torus_fin_last_piHom_mulSingle
        (F := F) n iFin u
      exact MonoidHom.mem_range.mpr
        ⟨Pi.mulSingle iFin u, h_mul⟩
    exact h_range

/-- Evaluation of the boundary torus product hom as the stabilized
reindexed product-one diagonal. Uses `noncommPiCoprod_apply` and
`toStableE_torus_fin_last_prod_eq_reindex_productOneDiagonal`.
Holds only after `toStableE` / in `StableE`; does not assert exact
torus multiplication or commutativity in `StableSteinberg`.
Uniform for `n = 0, 1`, char 2, multiplication in `StableE`. -/
public theorem toStableE_torus_fin_last_piHom_eq_reindex_productOneDiagonal
    (n : ℕ) (u : Fin n → Fˣ) :
    toStableE_torus_fin_last_piHom (F := F) n u =
      StableE.fromFinite F (n + 1)
        ⟨Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F
              (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal
                (R := F) u)),
          Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
              (F := F) u)⟩ := by
  rw [toStableE_torus_fin_last_piHom, MonoidHom.noncommPiCoprod_apply]
  exact toStableE_torus_fin_last_prod_eq_reindex_productOneDiagonal
    (F := F) n u

/-- Injectivity of the boundary torus product hom, recovering every unit
coefficient from its stable elementary image.

Descends the accepted reindexed product-one diagonal formula through
`StableE.fromFinite_injective`, strips the reindex equivalence, and reads the
`Sum.inl` diagonal entries to force each coordinate to `1`. Uniform for
`n = 0`, `n = 1` and in characteristic two. This is coefficient recovery only;
it makes no Steinberg-kernel generation and no Matsumoto-completion claim. -/
public theorem toStableE_torus_fin_last_piHom_injective
    (n : ℕ) : Function.Injective (toStableE_torus_fin_last_piHom (F := F) n) := by
  have hker : ∀ w : Fin n → Fˣ,
      toStableE_torus_fin_last_piHom (F := F) n w = 1 → w = 1 := by
    intro w hw
    rw [toStableE_torus_fin_last_piHom_eq_reindex_productOneDiagonal
      (F := F) n w] at hw
    have h_from : StableE.fromFinite F (n + 1)
        ⟨Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F
              (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal
                (R := F) w)),
          Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
              (F := F) w)⟩
        = StableE.fromFinite F (n + 1) 1 :=
      hw.trans (map_one _).symm
    have h_sub :=
      StableE.fromFinite_injective (R := F) (n + 1) h_from
    have h_gl : Matrix.GeneralLinearGroup.reindexMulEquiv
        (finSumFinEquiv (m := n) (n := 1))
        (Matrix.GeneralLinearGroup.diagonalUnitsHom F
          (Fin n ⊕ Fin 1)
          (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) w)) = 1 := by
      have h_val := congrArg Subtype.val h_sub
      simpa using h_val
    have h_reidx_one :
        Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := 1))
          (Matrix.GeneralLinearGroup.diagonalUnitsHom F
            (Fin n ⊕ Fin 1)
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) w))
          = Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1)) 1 :=
      h_gl.trans (map_one _).symm
    have h_diag :=
      (Matrix.GeneralLinearGroup.reindexMulEquiv
        (finSumFinEquiv (m := n) (n := 1)) (A := F)).injective h_reidx_one
    have hM := congrArg Units.val h_diag
    have hM' :
        (Matrix.diagonal fun s : Fin n ⊕ Fin 1 =>
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) w s
              : F))
          = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) F) := by
      simpa [Matrix.GeneralLinearGroup.coe_diagonalUnitsHom] using hM
    funext i
    have he := congrArg
        (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) F =>
          M (Sum.inl i) (Sum.inl i)) hM'
    simp only [Matrix.diagonal_apply_eq,
      Matrix.GeneralLinearGroup.productOneDiagonal, Sum.elim_inl,
      Matrix.one_apply_eq] at he
    exact Units.ext he
  intro u v h
  have h_mem : toStableE_torus_fin_last_piHom (F := F) n (u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h_one := hker _ h_mem
  have hcongr := congrArg (· * v) h_one
  simpa using hcongr

/-- Membership of the boundary torus product hom in the range of
`StableE.fromFinite F n` iff the coordinate product is `1`.
Uses `stableE_fromFinite_reindex_productOneDiagonal_mem_range_iff`.
Holds only after `toStableE` / in `StableE`; does not assert exact
torus multiplication or commutativity in `StableSteinberg`.
Uniform for `n = 0, 1`, char 2, multiplication in `StableE`. -/
public theorem toStableE_torus_fin_last_piHom_mem_range_iff
    (n : ℕ) (u : Fin n → Fˣ) :
    toStableE_torus_fin_last_piHom (F := F) n u ∈
        Set.range (StableE.fromFinite F n) ↔
      Finset.univ.prod u = 1 := by
  rw [toStableE_torus_fin_last_piHom_eq_reindex_productOneDiagonal
    (F := F) n u]
  exact stableE_fromFinite_reindex_productOneDiagonal_mem_range_iff
    (F := F) u

/-- Membership of a torus preimage in the kernel-joined finite stage
`finiteStage n ⊔ ker toStableE` iff the coordinate product is `1`.

This corrects the boundary torus/stage membership by joining with
`ker toStableE` via `comap_fromFinite_range_eq_finiteStage_sup_ker`;
it does not need or claim injectivity of `toStableE`. Uniform for
`n = 0` (empty product is `1`) and `n = 1`, valid in characteristic
two. This does not claim
`g ∈ finiteStage n ↔ Finset.univ.prod u = 1`, equivalently it
does not drop the required `⊔ ker toStableE` correction, exact torus
multiplication in `StableSteinberg` (defect is central),
commutativity in `StableSteinberg`, or triviality of the kernel; it
holds only after `toStableE` / in `StableE` via `hg`. -/
public theorem toStableE_torus_fin_last_piHom_mem_finiteStage_sup_ker_iff
    (n : ℕ) (u : Fin n → Fˣ) (g : StableSteinberg F)
    (hg : toStableE (R := F) g =
      toStableE_torus_fin_last_piHom (F := F) n u) :
    g ∈ finiteStage (R := F) n ⊔ (toStableE (R := F)).ker ↔
      Finset.univ.prod u = 1 := by
  have h_eq : finiteStage (R := F) n ⊔ (toStableE (R := F)).ker =
      Subgroup.comap (toStableE (R := F))
        (StableE.fromFinite F n).range := by
    rw [comap_fromFinite_range_eq_finiteStage_sup_ker]
  rw [h_eq, Subgroup.mem_comap, hg]
  exact toStableE_torus_fin_last_piHom_mem_range_iff (F := F) n u

/-- Boundary torus membership modulo `ker toStableE` via product-one
coordinates.

For `g` in `boundaryTorusSubgroup n`, membership in
`finiteStage n ⊔ ker toStableE` is equivalent to existence of
`u : Fin n → Fˣ` with `∏ u = 1` and `toStableE g = piHom n u`.
Retains the required `⊔ ker toStableE`; does not claim injectivity of
`toStableE`, exact torus multiplication in `StableSteinberg`,
commutativity in `StableSteinberg`, or triviality of the kernel.
Uniform for `n = 0, 1` and characteristic two, holding only after
`toStableE`. -/
public theorem boundaryTorusSubgroup_mem_finiteStage_sup_ker_iff_exists
    (n : ℕ) (g : StableSteinberg F)
    (hg : g ∈ boundaryTorusSubgroup (R := F) n) :
    g ∈ finiteStage (R := F) n ⊔ (toStableE (R := F)).ker ↔
      ∃ (u : Fin n → Fˣ),
        Finset.univ.prod u = 1 ∧
          toStableE (R := F) g =
            toStableE_torus_fin_last_piHom (F := F) n u := by
  have h_map : toStableE (R := F) g ∈
      (boundaryTorusSubgroup (R := F) n).map (toStableE (R := F)) :=
    Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  have h_range : toStableE (R := F) g ∈
      (toStableE_torus_fin_last_piHom (F := F) n).range := by
    rw [toStableE_torus_fin_last_piHom_range (F := F) n]
    exact h_map
  obtain ⟨u₀, hu₀⟩ := MonoidHom.mem_range.mp h_range
  constructor
  · intro h_mem
    have h_prod : Finset.univ.prod u₀ = 1 := by
      have h_iff :=
        toStableE_torus_fin_last_piHom_mem_finiteStage_sup_ker_iff
          (F := F) n u₀ g hu₀.symm
      exact h_iff.mp h_mem
    exact ⟨u₀, h_prod, hu₀.symm⟩
  · rintro ⟨u, h_prod, h_eq⟩
    have h_iff :=
      toStableE_torus_fin_last_piHom_mem_finiteStage_sup_ker_iff
        (F := F) n u g h_eq
    exact h_iff.mpr h_prod

/-- Factorization of a boundary torus element whose stable elementary
image lies in the range of `StableE.fromFinite F n`.

If `g ∈ boundaryTorusSubgroup n` and `toStableE g` is in the range of
`fromFinite n`, then `g` factors as `k * f` with `k ∈ ker toStableE`
and `f ∈ finiteStage n`. Uses `boundaryTorusSubgroup_le_finiteStage_succ`
to place `g` in `finiteStage (n+1)`, then
`finiteStage_succ_mem_finiteStage_sup_ker_of_toStableE_mem_range` to get
`g ∈ finiteStage n ⊔ ker`, `sup_comm` to flip to `ker ⊔ finiteStage n`,
and `Subgroup.mem_sup_of_normal_left` with the monoid-hom kernel
normality instance. Uniform for `n = 0, 1`; no extra hypothesis, no
commutative-only `mem_sup`, no direct intersection equality, and no
reproved range criterion. -/
public theorem boundaryTorusSubgroup_factorization_of_mem_range
    {n : ℕ} {g : StableSteinberg F}
    (hg : g ∈ boundaryTorusSubgroup (R := F) n)
    (h_range : toStableE (R := F) g ∈ (StableE.fromFinite F n).range) :
    ∃ (k : StableSteinberg F) (_ : k ∈ (toStableE (R := F)).ker)
      (f : StableSteinberg F) (_ : f ∈ finiteStage (R := F) n),
      g = k * f := by
  have h_le : boundaryTorusSubgroup (R := F) n ≤
      finiteStage (R := F) (n + 1) :=
    boundaryTorusSubgroup_le_finiteStage_succ (R := F) n
  have h_succ : g ∈ finiteStage (R := F) (n + 1) := h_le hg
  have h_sup : g ∈
      finiteStage (R := F) n ⊔ (toStableE (R := F)).ker :=
    finiteStage_succ_mem_finiteStage_sup_ker_of_toStableE_mem_range
      h_succ h_range
  have h_comm : finiteStage (R := F) n ⊔ (toStableE (R := F)).ker =
      (toStableE (R := F)).ker ⊔ finiteStage (R := F) n :=
    sup_comm _ _
  have h_sup' : g ∈
      (toStableE (R := F)).ker ⊔ finiteStage (R := F) n := by
    rw [← h_comm]
    exact h_sup
  obtain ⟨k, hk, f, hf, h_eq⟩ :=
    (Subgroup.mem_sup_of_normal_left.mp h_sup')
  exact ⟨k, hk, f, hf, h_eq.symm⟩

/-- Image-level identity: intersecting the `boundaryTorus` map with
`fromFinite n` range equals intersecting the product-hom range.
Rewrites `toStableE_torus_fin_last_piHom_range`. -/
public theorem boundaryTorus_map_inf_fromFinite_range_eq
    (n : ℕ) :
    (boundaryTorusSubgroup (R := F) n).map (toStableE (R := F)) ⊓
        (StableE.fromFinite F n).range =
      (toStableE_torus_fin_last_piHom (F := F) n).range ⊓
        (StableE.fromFinite F n).range := by
  rw [← toStableE_torus_fin_last_piHom_range (F := F) n]

/-- Corrected intersection after adjoining `ker toStableE`: the join-
intersection equals the comap of the image-level intersection. Uses
`comap_inf`, `comap_map_eq`, and `comap_fromFinite_range`. -/
public theorem boundaryTorus_sup_ker_inf_finiteStage_sup_ker_eq_comap
    (n : ℕ) :
    (boundaryTorusSubgroup (R := F) n ⊔ MonoidHom.ker (toStableE (R := F))) ⊓
        (finiteStage (R := F) n ⊔ MonoidHom.ker (toStableE (R := F))) =
      Subgroup.comap (toStableE (R := F))
        ((boundaryTorusSubgroup (R := F) n).map (toStableE (R := F)) ⊓
          (StableE.fromFinite F n).range) := by
  calc (boundaryTorusSubgroup (R := F) n ⊔
          MonoidHom.ker (toStableE (R := F))) ⊓
          (finiteStage (R := F) n ⊔ MonoidHom.ker (toStableE (R := F)))
      = (Subgroup.comap (toStableE (R := F))
            ((boundaryTorusSubgroup (R := F) n).map (toStableE (R := F)))) ⊓
          (Subgroup.comap (toStableE (R := F))
            ((StableE.fromFinite F n).range)) := by
        rw [Subgroup.comap_map_eq (toStableE (R := F))
            (boundaryTorusSubgroup (R := F) n),
          comap_fromFinite_range_eq_finiteStage_sup_ker (R := F) n]
    _ = Subgroup.comap (toStableE (R := F))
          ((boundaryTorusSubgroup (R := F) n).map (toStableE (R := F)) ⊓
            (StableE.fromFinite F n).range) := by
        rw [← Subgroup.comap_inf]

/-- Image-level, kernel-corrected: boundary `sup ker` join-intersection comaps from
piHom-range/`fromFinite`-range intersection. -/
public theorem boundaryTorus_sup_ker_inf_finiteStage_sup_ker_eq_comap_piHom_range
    (n : ℕ) :
    (boundaryTorusSubgroup (R := F) n ⊔ MonoidHom.ker (toStableE (R := F))) ⊓
        (finiteStage (R := F) n ⊔ MonoidHom.ker (toStableE (R := F))) =
      Subgroup.comap (toStableE (R := F))
        ((toStableE_torus_fin_last_piHom (F := F) n).range ⊓
          (StableE.fromFinite F n).range) := by
  rw [boundaryTorus_sup_ker_inf_finiteStage_sup_ker_eq_comap (F := F) n,
    boundaryTorus_map_inf_fromFinite_range_eq (F := F) n]

/-- Image-level, kernel-corrected membership iff `toStableE` image lies in
piHom-range/`fromFinite`-range intersection. -/
public theorem boundaryTorus_sup_ker_inf_finiteStage_sup_ker_mem_iff
    (n : ℕ) (g : StableSteinberg F) :
    g ∈ (boundaryTorusSubgroup (R := F) n ⊔ MonoidHom.ker (toStableE (R := F))) ⊓
        (finiteStage (R := F) n ⊔ MonoidHom.ker (toStableE (R := F))) ↔
      toStableE (R := F) g ∈ (toStableE_torus_fin_last_piHom (F := F) n).range ⊓
        (StableE.fromFinite F n).range := by
  rw [boundaryTorus_sup_ker_inf_finiteStage_sup_ker_eq_comap (F := F) n,
    boundaryTorus_map_inf_fromFinite_range_eq (F := F) n, Subgroup.mem_comap]

/-- `y ∈ piHom n range ⊓ fromFinite n range` iff `∃ u, ∏ u = 1 ∧ piHom u = y`.
Image-level in `StableE`; does not claim Steinberg-level exact intersection,
does not introduce new subgroup abstraction; uses only `MonoidHom.mem_range`,
`Subgroup.mem_inf`, `toStableE_torus_fin_last_piHom_mem_range_iff`. -/
public theorem toStableE_torus_fin_last_piHom_range_inf_fromFinite_range_mem_iff
    (n : ℕ) (y : StableE F) :
    y ∈ (toStableE_torus_fin_last_piHom (F := F) n).range ⊓
        (StableE.fromFinite F n).range ↔
      ∃ (u : Fin n → Fˣ), Finset.univ.prod u = 1 ∧
        toStableE_torus_fin_last_piHom (F := F) n u = y := by
  constructor
  · intro hy
    have hb := Subgroup.mem_inf.mp hy
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hb.1
    have hm : toStableE_torus_fin_last_piHom (F := F) n u ∈
        (StableE.fromFinite F n).range := by
      rw [hu]
      exact hb.2
    exact ⟨u, (toStableE_torus_fin_last_piHom_mem_range_iff (F := F) n u).mp hm, hu⟩
  · rintro ⟨u, hp, he⟩
    rw [Subgroup.mem_inf]
    constructor
    · exact MonoidHom.mem_range.mpr ⟨u, he⟩
    · have hm : toStableE_torus_fin_last_piHom (F := F) n u ∈
          (StableE.fromFinite F n).range :=
        (toStableE_torus_fin_last_piHom_mem_range_iff (F := F) n u).mpr hp
      exact he ▸ hm

end StableSteinberg

end AlgebraicKTheory

end
