/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.BracketBoundaryRecursion
public import MathlibExt.Data.List.EraseIdxOfFn

/-!
# The Chevalley–Eilenberg bracket boundary in list notation

The finite-triangle reindexing identifies the compressed pair formula with
the sum over strict ordered pairs. Deleting the higher index before the lower
index preserves the order of the remaining exterior factors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The compressed pair formula equals the full strict-pair sum, with the
higher index deleted before the lower index in the remaining list. -/
theorem bracketBoundary_succ_coe_eq_sum_pairs (n : ℕ) (v : Fin (n + 2) → L) :
    (bracketBoundary R L (n + 1) v : ExteriorAlgebra R L) =
      ∑ i : Fin (n + 2), ∑ j : Fin (n + 2),
        if i.val < j.val then
          ((-1 : R) ^ (i.val + j.val)) •
            (ExteriorAlgebra.ι R ⁅v i, v j⁆ *
              ((((List.ofFn v).eraseIdx j.val).eraseIdx i.val).map
                (ExteriorAlgebra.ι R)).prod)
        else 0 := by
  classical
  let t (i j : Fin (n + 2)) : ExteriorAlgebra R L :=
    if i.val < j.val then
      ((-1 : R) ^ (i.val + j.val)) •
        (ExteriorAlgebra.ι R ⁅v i, v j⁆ *
          ((((List.ofFn v).eraseIdx j.val).eraseIdx i.val).map
            (ExteriorAlgebra.ι R)).prod)
    else 0
  have hsum (i : Fin (n + 2)) :
      (∑ j : Fin (n + 2), t i j) =
        ∑ j : Fin (n + 1), t i (i.succAbove j) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [t, lt_self_iff_false, ite_false, zero_add]
  have hsumAll : (∑ i, ∑ j, t i j) =
      ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), t i (i.succAbove j) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hsum i
  change (bracketBoundary R L (n + 1) v : ExteriorAlgebra R L) = ∑ i, ∑ j, t i j
  rw [bracketBoundary_succ_coe R L n, hsumAll, Fin.sum_sum_eq_sum_triangle_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ici] at hj
  have hforward : i.castSucc.succAbove j = j.succ :=
    Fin.succAbove_castSucc_of_le i j hj
  have hbackward : j.succ.succAbove i = i.castSucc :=
    Fin.succAbove_succ_of_le j i hj
  have hlt : i.val < j.val + 1 := Nat.lt_succ_of_le hj
  have hnlt : ¬ j.val + 1 < i.val := not_lt.mpr (Nat.le_succ_of_le hj)
  simp only [hforward, hbackward, t, Fin.val_castSucc, Fin.val_succ,
    ite_eq_left hlt, ite_eq_right hnlt, add_zero]
  have herase :
      ((List.ofFn v).eraseIdx (j.val + 1)).eraseIdx i.val =
        List.ofFn (j.removeNth (i.castSucc.removeNth v)) := by
    simpa only [Fin.val_succ] using List.eraseIdx_eraseIdx_ofFn v i j hj
  have hprod :
      (List.ofFn ((ExteriorAlgebra.ι R) ∘
        j.removeNth (i.castSucc.removeNth v))).prod =
          ExteriorAlgebra.ιMulti R n (j.removeNth (i.castSucc.removeNth v)) := by
    rw [ExteriorAlgebra.ιMulti_apply]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext k
    rfl
  rw [herase, List.map_ofFn, hprod]
  rw [ExteriorAlgebra.ιMulti_succ_apply, Matrix.cons_val_zero, Matrix.tail_cons,
    Nat.add_assoc]

/-- The full strict-pair list formula also includes the zero boundary on
one-vector input. -/
theorem bracketBoundary_coe_eq_sum_pairs (n : ℕ) (v : Fin (n + 1) → L) :
    (bracketBoundary R L n v : ExteriorAlgebra R L) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        if i.val < j.val then
          ((-1 : R) ^ (i.val + j.val)) •
            (ExteriorAlgebra.ι R ⁅v i, v j⁆ *
              ((((List.ofFn v).eraseIdx j.val).eraseIdx i.val).map
                (ExteriorAlgebra.ι R)).prod)
        else 0 := by
  cases n with
  | zero => simp [bracketBoundary]
  | succ n => exact bracketBoundary_succ_coe_eq_sum_pairs R L n v

end ChevalleyEilenberg
