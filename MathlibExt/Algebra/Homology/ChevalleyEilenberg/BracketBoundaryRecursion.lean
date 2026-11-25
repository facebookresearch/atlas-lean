/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Recursion for the Chevalley–Eilenberg bracket boundary

The ordered pair sum separates into the terms involving the first vector and
the boundary on the remaining vectors. Moving the front bracket past the
first vector accounts for the sign of the latter summand.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The bracket boundary, viewed in the ambient exterior algebra, has the
same ordered pair formula as its exterior-power presentation. -/
theorem bracketBoundary_succ_coe (n : ℕ) (v : Fin (n + 2) → L) :
    (bracketBoundary R L (n + 1) v : ExteriorAlgebra R L) =
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
        ((-1 : R) ^ (i.val + j.val + 1)) •
          ExteriorAlgebra.ιMulti R (n + 1)
            (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
              (j.removeNth (i.castSucc.removeNth v))) := by
  change (Submodule.subtype (⋀[R]^(n + 1) L))
    (bracketBoundary R L (n + 1) v) = _
  simp only [bracketBoundary, map_sum, map_smul, Submodule.coe_subtype,
    exteriorPower.ιMulti_apply_coe]

/-- Splitting the boundary at the first vector preserves the order of the
remaining factors and the sign of each original ordered pair. -/
theorem bracketBoundary_vecCons_coe (n : ℕ) (x : L) (v : Fin (n + 1) → L) :
    (bracketBoundary R L (n + 1) (Matrix.vecCons x v) : ExteriorAlgebra R L) =
      (∑ j : Fin (n + 1), ((-1 : R) ^ (j.val + 1)) •
        ExteriorAlgebra.ιMulti R (n + 1)
          (Matrix.vecCons ⁅x, v j⁆ (j.removeNth v))) -
        ExteriorAlgebra.ι R x *
          (bracketBoundary R L n v : ExteriorAlgebra R L) := by
  classical
  cases n with
  | zero => simp [bracketBoundary]
  | succ n =>
    rw [bracketBoundary_succ_coe R L (n + 1),
      bracketBoundary_succ_coe R L n, Fin.sum_univ_succ]
    have hhead :
        (∑ j ∈ Finset.Ici (0 : Fin (n + 2)),
          ((-1 : R) ^ ((0 : Fin (n + 2)).val + j.val + 1)) •
            ExteriorAlgebra.ιMulti R (n + 2)
              (Matrix.vecCons
                ⁅(Matrix.vecCons x v) (0 : Fin (n + 2)).castSucc,
                  (Matrix.vecCons x v) j.succ⁆
                (j.removeNth ((0 : Fin (n + 2)).castSucc.removeNth
                  (Matrix.vecCons x v))))) =
          ∑ j : Fin (n + 2), ((-1 : R) ^ (j.val + 1)) •
            ExteriorAlgebra.ιMulti R (n + 2)
              (Matrix.vecCons ⁅x, v j⁆ (j.removeNth v)) := by
      simp [Matrix.vecCons]
    rw [hhead, sub_eq_add_neg]
    congr 1
    calc
      (∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i.succ,
        ((-1 : R) ^ (i.succ.val + j.val + 1)) •
          ExteriorAlgebra.ιMulti R (n + 2)
            (Matrix.vecCons
              ⁅(Matrix.vecCons x v) i.succ.castSucc,
                (Matrix.vecCons x v) j.succ⁆
              (j.removeNth (i.succ.castSucc.removeNth
                (Matrix.vecCons x v))))) =
          ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
            -(ExteriorAlgebra.ι R x *
              (((-1 : R) ^ (i.val + j.val + 1)) •
                ExteriorAlgebra.ιMulti R (n + 1)
                  (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
                    (j.removeNth (i.castSucc.removeNth v))))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Fin.map_succEmb_Ici i, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro j _
        have hremove :
            j.succ.removeNth (i.succ.castSucc.removeNth
                (Matrix.vecCons x v)) =
              Matrix.vecCons x (j.removeNth (i.castSucc.removeNth v)) := by
          have hfirst : i.succ.castSucc.removeNth (Matrix.vecCons x v) =
              Matrix.vecCons x (i.castSucc.removeNth v) :=
            Fin.cons_comp_succ_succAbove x v i.castSucc
          rw [hfirst]
          exact Fin.cons_comp_succ_succAbove x (i.castSucc.removeNth v) j
        have hpow : ((-1 : R) ^ (i.succ.val + j.succ.val + 1)) =
            (-1 : R) ^ (i.val + j.val + 1) := by
          change ((-1 : R) ^ ((i.val + 1) + (j.val + 1) + 1)) = _
          rw [show (i.val + 1) + (j.val + 1) + 1 =
            (i.val + j.val + 1) + 2 by omega, pow_add]
          simp
        have hswap :
            ExteriorAlgebra.ιMulti R (n + 2)
                (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
                  (Matrix.vecCons x (j.removeNth (i.castSucc.removeNth v)))) =
              -(ExteriorAlgebra.ι R x *
                ExteriorAlgebra.ιMulti R (n + 1)
                  (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
                    (j.removeNth (i.castSucc.removeNth v)))) := by
          have hhead :
              ((Fin.cons ⁅v i.castSucc, v j.succ⁆
                  (Fin.cons x (j.removeNth (i.castSucc.removeNth v))) ∘
                    Fin.succ) 0) = x := by
            simp only [Function.comp_apply, Fin.cons_succ, Fin.cons_zero]
          have htail :
              (Fin.cons ⁅v i.castSucc, v j.succ⁆
                  (Fin.cons x (j.removeNth (i.castSucc.removeNth v))) ∘
                    Fin.succ) ∘ Fin.succ =
                j.removeNth (i.castSucc.removeNth v) := by
            funext k
            simp only [Function.comp_apply, Fin.cons_succ]
          have hbracketTail :
              (Fin.cons ⁅v i.castSucc, v j.succ⁆
                  (j.removeNth (i.castSucc.removeNth v))) ∘ Fin.succ =
                j.removeNth (i.castSucc.removeNth v) := by
            funext k
            simp only [Function.comp_apply, Fin.cons_succ]
          simp only [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail,
            Matrix.vecCons, Fin.cons_zero]
          rw [hhead, htail, hbracketTail]
          rw [← mul_assoc,
            eq_neg_of_add_eq_zero_left
              (ExteriorAlgebra.ι_add_mul_swap (R := R)
                ⁅v i.castSucc, v j.succ⁆ x), neg_mul, mul_assoc]
        change ((-1 : R) ^ (i.succ.val + j.succ.val + 1)) •
            ExteriorAlgebra.ιMulti R (n + 2)
              (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
                (j.succ.removeNth (i.succ.castSucc.removeNth
                  (Matrix.vecCons x v)))) = _
        rw [hremove, hpow, hswap]
        simp only [smul_neg, mul_smul_comm]
      _ = -(ExteriorAlgebra.ι R x *
          ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
            ((-1 : R) ^ (i.val + j.val + 1)) •
              ExteriorAlgebra.ιMulti R (n + 1)
                (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
                  (j.removeNth (i.castSucc.removeNth v)))) := by
        simp only [Finset.mul_sum, Finset.sum_neg_distrib]

/-- The first-vector part of the CE boundary is the negative sum of the
words with one vector replaced by its bracket with the first vector. -/
theorem bracketBoundary_vecCons_update_coe
    (n : ℕ) (x : L) (v : Fin (n + 1) → L) :
    (bracketBoundary R L (n + 1) (Matrix.vecCons x v) : ExteriorAlgebra R L) =
      -(∑ j : Fin (n + 1), ExteriorAlgebra.ιMulti R (n + 1)
        (Function.update v j ⁅x, v j⁆)) -
        ExteriorAlgebra.ι R x *
          (bracketBoundary R L n v : ExteriorAlgebra R L) := by
  classical
  rw [bracketBoundary_vecCons_coe R L n x v]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := (ExteriorAlgebra.ιMulti R (n + 1)).map_insertNth
    j ⁅x, v j⁆ (j.removeNth v)
  rw [Fin.insertNth_removeNth] at h
  have hR :
      ExteriorAlgebra.ιMulti R (n + 1) (Function.update v j ⁅x, v j⁆) =
        ((-1 : R) ^ j.val) • ExteriorAlgebra.ιMulti R (n + 1)
          (Matrix.vecCons ⁅x, v j⁆ (j.removeNth v)) := by
    simpa only [← Int.cast_smul_eq_zsmul R, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using h
  rw [hR, pow_succ, mul_smul, neg_one_smul, smul_neg]

end ChevalleyEilenberg
