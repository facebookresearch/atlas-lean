/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- AI-assisted original formalization: Avocado; responsible human author: @toskua.
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Group

/-!
# Pure Schreier transversal representatives, factors and tuple scans

The actual right transversal determines its representatives, subgroup factors,
right-multiplication action and every finite tuple scan. These constructions
use only a group and subgroup; no representation or cohomology dependency is
required. The original API names, universes and right-transversal conventions
are preserved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Subgroup.RightTransversal

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- The representative in a right transversal obtained after multiplying a
representative by a group element. -/
noncomputable def schreierRep (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) : (T : Set G) :=
  (T.2.equiv ((t : G) * g)).2

/-- The subgroup factor in the right-transversal decomposition of `t * g`. -/
noncomputable def schreierFactor (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) : H :=
  (T.2.equiv ((t : G) * g)).1

/-- The Schreier factor and new representative multiply back to `t * g`. -/
theorem schreierFactor_mul_schreierRep (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) :
    (schreierFactor T t g : G) * (schreierRep T t g : G) =
      (t : G) * g :=
  T.2.equiv_fst_mul_equiv_snd ((t : G) * g)

/-- Rewriting the Schreier factor after multiplying by the inverse of the
starting representative.  This is the coefficient-action identity used by
degree-one corestriction. -/
theorem inv_mul_schreierFactor (T : H.RightTransversal)
    (t : (T : Set G)) (g : G) :
    (t : G)⁻¹ * (schreierFactor T t g : G) =
      g * (schreierRep T t g : G)⁻¹ := by
  rw [schreierFactor, schreierRep,
    T.2.equiv_fst_eq_mul_inv ((t : G) * g)]
  group

/-- Multiplication on the right gives a genuine right action on transversal
representatives. -/
theorem schreierRep_mul (T : H.RightTransversal)
    (t : (T : Set G)) (g₁ g₂ : G) :
    schreierRep T t (g₁ * g₂) =
      schreierRep T (schreierRep T t g₁) g₂ := by
  change (T.2.equiv ((t : G) * (g₁ * g₂))).2 =
    (T.2.equiv (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).2
  calc
    (T.2.equiv ((t : G) * (g₁ * g₂))).2 =
        (T.2.equiv
          ((schreierFactor T t g₁ : G) *
            ((schreierRep T t g₁ : G) * g₂))).2 := by
      congr 2
      calc
        (t : G) * (g₁ * g₂) = ((t : G) * g₁) * g₂ :=
          (mul_assoc _ _ _).symm
        _ = ((schreierFactor T t g₁ : G) *
              (schreierRep T t g₁ : G)) * g₂ := by
          rw [schreierFactor_mul_schreierRep]
        _ = (schreierFactor T t g₁ : G) *
              ((schreierRep T t g₁ : G) * g₂) :=
          mul_assoc _ _ _
    _ = (T.2.equiv
          (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).2 := by
      simpa only [schreierFactor, schreierRep] using congrArg Prod.snd
          (T.2.equiv_mul_left
            (schreierFactor T t g₁)
            ((schreierRep T t g₁ : G) * g₂))

/-- The subgroup factors satisfy the Schreier cocycle identity. -/
theorem schreierFactor_mul (T : H.RightTransversal)
    (t : (T : Set G)) (g₁ g₂ : G) :
    schreierFactor T t (g₁ * g₂) =
      schreierFactor T t g₁ *
        schreierFactor T (schreierRep T t g₁) g₂ := by
  change (T.2.equiv ((t : G) * (g₁ * g₂))).1 =
    (T.2.equiv ((t : G) * g₁)).1 *
      (T.2.equiv (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).1
  calc
    (T.2.equiv ((t : G) * (g₁ * g₂))).1 =
        (T.2.equiv
          ((schreierFactor T t g₁ : G) *
            ((schreierRep T t g₁ : G) * g₂))).1 := by
      congr 2
      calc
        (t : G) * (g₁ * g₂) = ((t : G) * g₁) * g₂ :=
          (mul_assoc _ _ _).symm
        _ = ((schreierFactor T t g₁ : G) *
              (schreierRep T t g₁ : G)) * g₂ := by
          rw [schreierFactor_mul_schreierRep]
        _ = (schreierFactor T t g₁ : G) *
              ((schreierRep T t g₁ : G) * g₂) :=
          mul_assoc _ _ _
    _ = (T.2.equiv ((t : G) * g₁)).1 *
          (T.2.equiv
            (((T.2.equiv ((t : G) * g₁)).2 : G) * g₂)).1 := by
      simpa only [schreierFactor, schreierRep] using congrArg Prod.fst
          (T.2.equiv_mul_left
            (schreierFactor T t g₁)
            ((schreierRep T t g₁ : G) * g₂))

@[simp]
theorem schreierRep_one (T : H.RightTransversal)
    (t : (T : Set G)) : schreierRep T t 1 = t := by
  simpa only [schreierRep, mul_one] using
    T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.property

@[simp]
theorem schreierFactor_one (T : H.RightTransversal)
    (t : (T : Set G)) : schreierFactor T t 1 = 1 := by
  apply Subtype.ext
  change ((T.2.equiv ((t : G) * 1)).1 : G) = (1 : G)
  simpa only [mul_one] using congrArg Subtype.val
    (T.2.equiv_fst_eq_one_of_mem_of_one_mem H.one_mem t.property)

/-- Right multiplication by a group element permutes a right transversal. -/
noncomputable def schreierRepEquiv (T : H.RightTransversal) (g : G) :
    (T : Set G) ≃ (T : Set G) where
  toFun t := schreierRep T t g
  invFun t := schreierRep T t g⁻¹
  left_inv t := by
    change schreierRep T (schreierRep T t g) g⁻¹ = t
    rw [← schreierRep_mul, mul_inv_cancel, schreierRep_one]
  right_inv t := by
    change schreierRep T (schreierRep T t g⁻¹) g = t
    rw [← schreierRep_mul, inv_mul_cancel, schreierRep_one]

@[simp]
theorem schreierRepEquiv_apply (T : H.RightTransversal)
    (g : G) (t : (T : Set G)) :
    schreierRepEquiv T g t = schreierRep T t g :=
  rfl

end Subgroup.RightTransversal

namespace Subgroup.RightTransversal

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- Successive right-transversal representatives obtained by scanning a
finite tuple of group elements, including the initial representative. -/
noncomputable def schreierRepScan {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) : Fin (n + 1) → (T : Set G) :=
  fun i ↦ T.schreierRep t (Fin.partialProd g i)

/-- The Schreier scan starts at the supplied transversal representative. -/
@[simp]
theorem schreierRepScan_get_zero {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) :
    schreierRepScan T t g 0 = t := by
  unfold schreierRepScan
  rw [Fin.partialProd_zero, schreierRep_one]

/-- Successor computation for the Schreier representative scan. -/
@[simp]
theorem schreierRepScan_get_succ {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) (i : Fin n) :
    schreierRepScan T t g i.succ =
      T.schreierRep (schreierRepScan T t g i.castSucc) (g i) := by
  unfold schreierRepScan
  rw [Fin.partialProd_succ, schreierRep_mul]

/-- The representative scan of a contracted tuple is the corresponding
subsequence of the original representative scan. -/
theorem schreierRepScan_contractNth {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) (j : Fin (n + 1))
    (i : Fin (n + 1)) :
    schreierRepScan T t (Fin.contractNth j (fun x y ↦ x * y) g) i =
      schreierRepScan T t g (j.succ.succAbove i) := by
  unfold schreierRepScan
  have h := Fin.partialProd_contractNth g j
  exact congrArg (fun q ↦ T.schreierRep t (q i)) h

/-- Scanning the tail after the first representative update is the tail of
the original scan. -/
theorem schreierRepScan_tail {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) (i : Fin (n + 1)) :
    schreierRepScan T (T.schreierRep t (g 0)) (Fin.tail g) i =
      schreierRepScan T t g i.succ := by
  unfold schreierRepScan
  rw [← T.schreierRep_mul, ← Fin.partialProd_succ']

/-- Tuple of subgroup factors in the successive Schreier decompositions. -/
noncomputable def schreierFactorTuple {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) : Fin n → H :=
  fun i ↦ T.schreierFactor
    (schreierRepScan T t g i.castSucc) (g i)

/-- Closed formula for each tuple factor in the ambient group. -/
theorem schreierFactorTuple_coe {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) (i : Fin n) :
    (schreierFactorTuple T t g i : G) =
      (schreierRepScan T t g i.castSucc : G) * g i *
        (schreierRepScan T t g i.succ : G)⁻¹ := by
  unfold schreierFactorTuple
  rw [schreierFactor, T.2.equiv_fst_eq_mul_inv]
  congr 2
  exact congrArg Subtype.val (schreierRepScan_get_succ T t g i).symm

/-- Contracting adjacent group entries contracts the corresponding
Schreier-factor tuple by subgroup multiplication. -/
theorem schreierFactorTuple_contractNth {n : ℕ}
    (T : H.RightTransversal) (t : (T : Set G))
    (g : Fin (n + 1) → G) (j : Fin (n + 1)) :
    schreierFactorTuple T t
        (Fin.contractNth j (fun x y ↦ x * y) g) =
      Fin.contractNth j (fun x y ↦ x * y)
        (schreierFactorTuple T t g) := by
  funext i
  apply Subtype.ext
  rw [schreierFactorTuple_coe,
    schreierRepScan_contractNth, schreierRepScan_contractNth]
  simp only [Fin.succ_succAbove_succ]
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h,
      Fin.contractNth_apply_of_lt _ _ _ _ h]
    rw [Fin.succAbove_of_castSucc_lt j.succ i.castSucc (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega),
      Fin.succAbove_of_castSucc_lt j i (by
        simpa only [Fin.lt_def, Fin.val_castSucc] using h)]
    rw [schreierFactorTuple_coe]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h,
      Fin.contractNth_apply_of_eq _ _ _ _ h]
    rw [Fin.succAbove_of_castSucc_lt j.succ i.castSucc (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega),
      Fin.succAbove_of_le_castSucc j i (by
        simpa only [Fin.le_def, Fin.val_castSucc] using le_of_eq h.symm)]
    change _ =
      (schreierFactorTuple T t g i.castSucc : G) *
        (schreierFactorTuple T t g i.succ : G)
    rw [schreierFactorTuple_coe, schreierFactorTuple_coe]
    simp only [Fin.castSucc_succ]
    group
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h,
      Fin.contractNth_apply_of_gt _ _ _ _ h]
    rw [Fin.succAbove_of_le_castSucc j.succ i.castSucc (by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega),
      Fin.succAbove_of_le_castSucc j i (by
        simpa only [Fin.le_def, Fin.val_castSucc] using le_of_lt h)]
    rw [schreierFactorTuple_coe]
    simp only [Fin.castSucc_succ]

/-- The factor tuple of the tail after the first representative update is
the tail of the original factor tuple. -/
theorem schreierFactorTuple_tail {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) :
    schreierFactorTuple T (T.schreierRep t (g 0)) (Fin.tail g) =
      Fin.tail (schreierFactorTuple T t g) := by
  funext i
  apply Subtype.ext
  change (schreierFactorTuple T (T.schreierRep t (g 0))
      (Fin.tail g) i : G) = (schreierFactorTuple T t g i.succ : G)
  rw [schreierFactorTuple_coe, schreierFactorTuple_coe,
    schreierRepScan_tail, schreierRepScan_tail]
  rfl

/-- Zeroth tuple factor is the ordinary first Schreier factor. -/
@[simp]
theorem schreierFactorTuple_zero {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 1) → G) :
    schreierFactorTuple T t g 0 = T.schreierFactor t (g 0) := by
  unfold schreierFactorTuple
  rw [show (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) from rfl,
    schreierRepScan_get_zero]

/-- The second tuple factor specializes to the factor at the representative
obtained after the first coordinate. -/
@[simp]
theorem schreierFactorTuple_one {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 2) → G) :
    schreierFactorTuple T t g 1 =
      T.schreierFactor (T.schreierRep t (g 0)) (g 1) := by
  unfold schreierFactorTuple
  rw [show (1 : Fin (n + 2)).castSucc = (0 : Fin (n + 2)).succ from rfl,
    schreierRepScan_get_succ,
    show (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) from rfl,
    schreierRepScan_get_zero]

/-- The third tuple factor specializes to the factor after two successive
representative updates. -/
@[simp]
theorem schreierFactorTuple_two {n : ℕ} (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin (n + 3) → G) :
    schreierFactorTuple T t g 2 =
      T.schreierFactor
        (T.schreierRep (T.schreierRep t (g 0)) (g 1)) (g 2) := by
  unfold schreierFactorTuple
  rw [show (2 : Fin (n + 3)).castSucc = (1 : Fin (n + 3)).succ from rfl,
    schreierRepScan_get_succ,
    show (1 : Fin (n + 3)).castSucc = (0 : Fin (n + 3)).succ from rfl,
    schreierRepScan_get_succ,
    show (0 : Fin (n + 3)).castSucc = (0 : Fin (n + 4)) from rfl,
    schreierRepScan_get_zero]

/-- Partial products of the actual Schreier factors are the original complement projection. -/
theorem factorTuple_partialProd (T : H.RightTransversal) {n : ℕ} (t : (T : Set G)) (x : Fin n → G)
    (i : Fin (n + 1)) :
    Fin.partialProd (T.schreierFactorTuple t x) i =
      (T.2.equiv ((t : G) * Fin.partialProd x i)).1 := by
  induction i using Fin.induction with
  | zero =>
      rw [Fin.partialProd_zero, Fin.partialProd_zero, mul_one]
      exact (T.2.equiv_fst_eq_one_of_mem_of_one_mem H.one_mem t.property).symm
  | succ i ih =>
      rw [Fin.partialProd_succ, Fin.partialProd_succ, ih]
      unfold schreierFactorTuple schreierRepScan schreierFactor
      let y := (t : G) * Fin.partialProd x i.castSucc
      have hy := T.2.equiv_fst_mul_equiv_snd y
      have hm := congrArg Prod.fst
        (T.2.equiv_mul_left (T.2.equiv y).1 (((T.2.equiv y).2 : G) * x i))
      have he : (t : G) * (Fin.partialProd x i.castSucc * x i) =
          ((T.2.equiv y).1 : G) * (((T.2.equiv y).2 : G) * x i) := by
        exact (mul_assoc _ _ _).symm.trans
          ((congrArg (fun z : G => z * x i) hy).symm.trans (mul_assoc _ _ _))
      exact hm.symm.trans (congrArg (fun z : G => (T.2.equiv z).1) he.symm)


end Subgroup.RightTransversal
