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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementary
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementaryRelations
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Data.Fintype.Basic

/-!
# Simultaneous upper-elementary sweeps

For `r : ι`, `rowSweep r` is the commuting product `∏_{i < r} E_{i,r}(v i)`.
For `c : ι`, `columnSweep c` is `∏_{c < j} E_{c,j}(v j)`.

Ring-generic, uses `MonoidHom.noncommPiCoprod` and `commute_elementary_elementary`.
Matrix is `1 + ∑ single` and action formulas are load-bearing for Bruhat.
Division only enters later when choosing clearing coefficients.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix Finset Function

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [Ring R]

section DecPred

noncomputable instance decPred_lt_r (r : ι) :
    DecidablePred (fun i : ι => i < r) :=
  fun _ => Classical.propDecidable _

noncomputable instance decPred_gt_c (c : ι) :
    DecidablePred (fun j : ι => c < j) :=
  fun _ => Classical.propDecidable _

end DecPred

/-- The subtype of coordinates strictly below the distinguished row index. -/
abbrev RowIdx (ι : Type*) [LinearOrder ι] (r : ι) := {i : ι // i < r}
/-- The subtype of coordinates strictly above the distinguished column index. -/
abbrev ColIdx (ι : Type*) [LinearOrder ι] (c : ι) := {j : ι // c < j}

noncomputable instance rowFintype (r : ι) : Fintype (RowIdx ι r) :=
  Subtype.fintype (fun i : ι => i < r)

noncomputable instance colFintype (c : ι) : Fintype (ColIdx ι c) :=
  Subtype.fintype (fun j : ι => c < j)

section ElementaryMulHom

/-- The elementary transvection homomorphism from the multiplicatively tagged additive ring. -/
noncomputable def elementaryMulHom (i j : ι) (hij : i ≠ j) :
    Multiplicative R →* GL ι R where
  toFun v := elementary i j hij v.toAdd
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    rw [← elementary_mul_same]

end ElementaryMulHom

section RowFamily

/-- The elementary transvection family supported in the distinguished column. -/
noncomputable def rowFamily (r : ι) (i : RowIdx ι r) :
    Multiplicative R →* GL ι R :=
  elementaryMulHom (R := R) i.val r (ne_of_lt i.prop)

theorem rowFamily_commute (r : ι) :
    Pairwise fun (i j : RowIdx ι r) =>
      ∀ (x y : Multiplicative R),
        Commute (rowFamily (R := R) r i x) (rowFamily r j y) := by
  intro i j _hij x y
  have hi : i.val ≠ r := ne_of_lt i.prop
  have hj : j.val ≠ r := ne_of_lt j.prop
  have hrj : r ≠ j.val := Ne.symm hj
  have hri : r ≠ i.val := Ne.symm hi
  exact commute_elementary_elementary i.val r j.val r
    hi hj hrj hri x.toAdd y.toAdd

/-- The simultaneous elementary word over the coordinates below the distinguished row index. -/
noncomputable def rowSweep (r : ι) :
    (RowIdx ι r → Multiplicative R) →* GL ι R :=
  MonoidHom.noncommPiCoprod
    (fun i => rowFamily (R := R) r i) (rowFamily_commute (R := R) r)

theorem rowSweep_mulSingle (r : ι) (i : RowIdx ι r) (v : Multiplicative R) :
    rowSweep (R := R) r (Pi.mulSingle i v) = rowFamily r i v := by
  classical
  simp [rowSweep, MonoidHom.noncommPiCoprod_mulSingle]

end RowFamily

section ColFamily

/-- The elementary transvection family supported in the distinguished row. -/
noncomputable def colFamily (c : ι) (j : ColIdx ι c) :
    Multiplicative R →* GL ι R :=
  elementaryMulHom (R := R) c j.val (ne_of_lt j.prop)

theorem colFamily_commute (c : ι) :
    Pairwise fun (i j : ColIdx ι c) =>
      ∀ (x y : Multiplicative R),
        Commute (colFamily (R := R) c i x) (colFamily c j y) := by
  intro i j _hij x y
  have hi : c ≠ i.val := ne_of_lt i.prop
  have hj : c ≠ j.val := ne_of_lt j.prop
  have h1 : i.val ≠ c := Ne.symm hi
  have h2 : j.val ≠ c := Ne.symm hj
  exact commute_elementary_elementary c i.val c j.val
    hi hj h1 h2 x.toAdd y.toAdd

/-- The simultaneous elementary word over the coordinates above the distinguished column index. -/
noncomputable def columnSweep (c : ι) :
    (ColIdx ι c → Multiplicative R) →* GL ι R :=
  MonoidHom.noncommPiCoprod
    (fun j => colFamily (R := R) c j) (colFamily_commute (R := R) c)

theorem columnSweep_mulSingle (c : ι) (j : ColIdx ι c) (v : Multiplicative R) :
    columnSweep (R := R) c (Pi.mulSingle j v) = colFamily c j v := by
  classical
  simp [columnSweep, MonoidHom.noncommPiCoprod_mulSingle]

end ColFamily

section RowMatrix

/-- The single-entry matrix supported at the given row and distinguished column. -/
noncomputable def rowSingle (r : ι) (v : RowIdx ι r → Multiplicative R)
    (i : RowIdx ι r) : Matrix ι ι R :=
  Matrix.single i.val r (v i).toAdd

/-- The identity plus the corresponding single-entry row matrix. -/
noncomputable def rowMatElem (r : ι) (v : RowIdx ι r → Multiplicative R)
    (i : RowIdx ι r) : Matrix ι ι R :=
  1 + rowSingle r v i

theorem rowSingle_mul_rowSingle_zero (r : ι)
    (v w : RowIdx ι r → Multiplicative R) (i j : RowIdx ι r) :
    rowSingle r v i * rowSingle r w j = 0 := by
  ext p q
  simp only [mul_apply, rowSingle]
  apply Finset.sum_eq_zero
  intro x _
  have hrj : r ≠ j.val := Ne.symm (ne_of_lt j.prop)
  by_cases hp : i.val = p
  · by_cases hx : r = x
    · have hxj : j.val ≠ x := by
        rw [← hx]
        exact hrj.symm
      have h2 : Matrix.single j.val r (w j).toAdd x q = 0 := by
        simp [hxj]
      simp [h2]
    · have h1 : Matrix.single i.val r (v i).toAdd p x = 0 := by
        simp [hx]
      simp [h1]
  · have h1 : Matrix.single i.val r (v i).toAdd p x = 0 := by
      simp [hp]
    simp [h1]

theorem rowSingle_mul_sum_zero (r : ι) (v : RowIdx ι r → Multiplicative R)
    (a : RowIdx ι r) (s : Finset (RowIdx ι r)) :
    rowSingle r v a * (∑ i ∈ s, rowSingle r v i) = 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact rowSingle_mul_rowSingle_zero r v v a i

theorem rowMatElem_eq_val_rowFamily (r : ι)
    (v : RowIdx ι r → Multiplicative R) (i : RowIdx ι r) :
    rowMatElem r v i = (rowFamily (R := R) r i (v i) : Matrix ι ι R) := rfl

theorem coe_rowSweep_aux (r : ι) (v : RowIdx ι r → Multiplicative R)
    (s : Finset (RowIdx ι r)) :
    (↑(s.noncommProd (fun i => rowFamily r i (v i))
      (fun (i : RowIdx ι r) _ (j : RowIdx ι r) _ hij =>
        rowFamily_commute (R := R) r hij (v i) (v j))
      : GL ι R) : Matrix ι ι R) =
      1 + ∑ i ∈ s, rowSingle r v i := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h_empty : (∅ : Finset (RowIdx ι r)).noncommProd
        (fun i => rowFamily r i (v i))
        (fun (i : RowIdx ι r) _ (j : RowIdx ι r) _ hij =>
          rowFamily_commute (R := R) r hij (v i) (v j)) = 1 := rfl
    simp only [h_empty, Finset.sum_empty, add_zero, Units.val_one]
  | @insert a s ha ih =>
    have h_comm_insert : (↑(insert a s) : Set (RowIdx ι r)).Pairwise
        (onFun Commute (fun i => rowFamily r i (v i))) := by
      intro i _ j _ hij
      exact rowFamily_commute (R := R) r hij (v i) (v j)
    have h_comm_s : (↑s : Set (RowIdx ι r)).Pairwise
        (onFun Commute (fun i => rowFamily r i (v i))) := by
      intro i _ j _ hij
      exact rowFamily_commute (R := R) r hij (v i) (v j)
    have h_prod : (insert a s).noncommProd (fun i => rowFamily r i (v i))
        h_comm_insert =
        rowFamily r a (v a) *
          s.noncommProd (fun i => rowFamily r i (v i)) h_comm_s := by
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    calc (↑((insert a s).noncommProd
          (fun i => rowFamily r i (v i)) h_comm_insert : GL ι R)
          : Matrix ι ι R)
        = (↑(rowFamily r a (v a) *
            s.noncommProd (fun i => rowFamily r i (v i)) h_comm_s
            : GL ι R) : Matrix ι ι R) := by rw [h_prod]
      _ = (↑(rowFamily r a (v a)) : Matrix ι ι R) *
          ↑(s.noncommProd (fun i => rowFamily r i (v i)) h_comm_s
            : GL ι R) := rfl
      _ = rowMatElem r v a * (1 + ∑ i ∈ s, rowSingle r v i) := by
          rw [rowMatElem_eq_val_rowFamily, ih]
      _ = (1 + rowSingle r v a) * (1 + ∑ i ∈ s, rowSingle r v i) := rfl
      _ = 1 + (∑ i ∈ s, rowSingle r v i) + rowSingle r v a +
            rowSingle r v a * (∑ i ∈ s, rowSingle r v i) := by
          simp only [mul_add, add_mul, one_mul, mul_one]
          abel
      _ = 1 + rowSingle r v a + (∑ i ∈ s, rowSingle r v i) +
            rowSingle r v a * (∑ i ∈ s, rowSingle r v i) := by
          abel
      _ = 1 + rowSingle r v a + (∑ i ∈ s, rowSingle r v i) := by
          rw [rowSingle_mul_sum_zero, add_zero]
      _ = 1 + (∑ i ∈ insert a s, rowSingle r v i) := by
          rw [Finset.sum_insert ha]
          abel

/-- The sum of the single-entry matrices in the row-sweep family. -/
noncomputable def rowSum (r : ι) (v : RowIdx ι r → Multiplicative R) :
    Matrix ι ι R :=
  ∑ i : RowIdx ι r, rowSingle r v i

theorem coe_rowSweep (r : ι) (v : RowIdx ι r → Multiplicative R) :
    (↑(rowSweep r v) : Matrix ι ι R) = 1 + rowSum r v := by
  classical
  unfold rowSweep rowSum
  have h_eq : MonoidHom.noncommPiCoprod
      (fun i => rowFamily (R := R) r i) (rowFamily_commute r) v =
      Finset.univ.noncommProd (fun i => rowFamily r i (v i))
        (fun (i : RowIdx ι r) _ (j : RowIdx ι r) _ hij =>
          rowFamily_commute (R := R) r hij (v i) (v j)) := rfl
  rw [h_eq]
  exact coe_rowSweep_aux r v Finset.univ

end RowMatrix

section ColMatrix

/-- The single-entry matrix supported at the distinguished row and given column. -/
noncomputable def colSingle (c : ι) (v : ColIdx ι c → Multiplicative R)
    (j : ColIdx ι c) : Matrix ι ι R :=
  Matrix.single c j.val (v j).toAdd

/-- The identity plus the corresponding single-entry column matrix. -/
noncomputable def colMatElem (c : ι) (v : ColIdx ι c → Multiplicative R)
    (j : ColIdx ι c) : Matrix ι ι R :=
  1 + colSingle c v j

theorem colSingle_mul_colSingle_zero (c : ι)
    (v w : ColIdx ι c → Multiplicative R) (i j : ColIdx ι c) :
    colSingle c v i * colSingle c w j = 0 := by
  ext p q
  simp only [mul_apply, colSingle]
  apply Finset.sum_eq_zero
  intro x _
  have hci : c ≠ i.val := ne_of_lt i.prop
  by_cases hp : c = p
  · by_cases hx : i.val = x
    · have hcx : c ≠ x := by
        rw [← hx]
        exact hci
      have h2 : Matrix.single c j.val (w j).toAdd x q = 0 := by
        simp [hcx]
      simp [h2]
    · have h1 : Matrix.single c i.val (v i).toAdd p x = 0 := by
        simp [hx]
      simp [h1]
  · have h1 : Matrix.single c i.val (v i).toAdd p x = 0 := by
      simp [hp]
    simp [h1]

theorem colSingle_mul_sum_zero (c : ι) (v : ColIdx ι c → Multiplicative R)
    (a : ColIdx ι c) (s : Finset (ColIdx ι c)) :
    colSingle c v a * (∑ i ∈ s, colSingle c v i) = 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact colSingle_mul_colSingle_zero c v v a i

theorem colMatElem_eq_val_colFamily (c : ι)
    (v : ColIdx ι c → Multiplicative R) (j : ColIdx ι c) :
    colMatElem c v j = (colFamily (R := R) c j (v j) : Matrix ι ι R) := rfl

theorem coe_columnSweep_aux (c : ι) (v : ColIdx ι c → Multiplicative R)
    (s : Finset (ColIdx ι c)) :
    (↑(s.noncommProd (fun j => colFamily c j (v j))
      (fun (i : ColIdx ι c) _ (j : ColIdx ι c) _ hij =>
        colFamily_commute (R := R) c hij (v i) (v j))
      : GL ι R) : Matrix ι ι R) =
      1 + ∑ j ∈ s, colSingle c v j := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h_empty : (∅ : Finset (ColIdx ι c)).noncommProd
        (fun j => colFamily c j (v j))
        (fun (i : ColIdx ι c) _ (j : ColIdx ι c) _ hij =>
          colFamily_commute (R := R) c hij (v i) (v j)) = 1 := rfl
    simp only [h_empty, Finset.sum_empty, add_zero, Units.val_one]
  | @insert a s ha ih =>
    have h_comm_insert : (↑(insert a s) : Set (ColIdx ι c)).Pairwise
        (onFun Commute (fun j => colFamily c j (v j))) := by
      intro i _ j _ hij
      exact colFamily_commute (R := R) c hij (v i) (v j)
    have h_comm_s : (↑s : Set (ColIdx ι c)).Pairwise
        (onFun Commute (fun j => colFamily c j (v j))) := by
      intro i _ j _ hij
      exact colFamily_commute (R := R) c hij (v i) (v j)
    have h_prod : (insert a s).noncommProd (fun j => colFamily c j (v j))
        h_comm_insert =
        colFamily c a (v a) *
          s.noncommProd (fun j => colFamily c j (v j)) h_comm_s := by
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    calc (↑((insert a s).noncommProd
          (fun j => colFamily c j (v j)) h_comm_insert : GL ι R)
          : Matrix ι ι R)
        = (↑(colFamily c a (v a) *
            s.noncommProd (fun j => colFamily c j (v j)) h_comm_s
            : GL ι R) : Matrix ι ι R) := by rw [h_prod]
      _ = (↑(colFamily c a (v a)) : Matrix ι ι R) *
          ↑(s.noncommProd (fun j => colFamily c j (v j)) h_comm_s
            : GL ι R) := rfl
      _ = colMatElem c v a * (1 + ∑ j ∈ s, colSingle c v j) := by
          rw [colMatElem_eq_val_colFamily, ih]
      _ = (1 + colSingle c v a) * (1 + ∑ j ∈ s, colSingle c v j) := rfl
      _ = 1 + (∑ j ∈ s, colSingle c v j) + colSingle c v a +
            colSingle c v a * (∑ j ∈ s, colSingle c v j) := by
          simp only [mul_add, add_mul, one_mul, mul_one]
          abel
      _ = 1 + colSingle c v a + (∑ j ∈ s, colSingle c v j) +
            colSingle c v a * (∑ j ∈ s, colSingle c v j) := by
          abel
      _ = 1 + colSingle c v a + (∑ j ∈ s, colSingle c v j) := by
          rw [colSingle_mul_sum_zero, add_zero]
      _ = 1 + (∑ j ∈ insert a s, colSingle c v j) := by
          rw [Finset.sum_insert ha]
          abel

/-- The sum of the single-entry matrices in the column-sweep family. -/
noncomputable def colSum (c : ι) (v : ColIdx ι c → Multiplicative R) :
    Matrix ι ι R :=
  ∑ j : ColIdx ι c, colSingle c v j

theorem coe_columnSweep (c : ι) (v : ColIdx ι c → Multiplicative R) :
    (↑(columnSweep c v) : Matrix ι ι R) = 1 + colSum c v := by
  classical
  unfold columnSweep colSum
  have h_eq : MonoidHom.noncommPiCoprod
      (fun j => colFamily (R := R) c j) (colFamily_commute c) v =
      Finset.univ.noncommProd (fun j => colFamily c j (v j))
        (fun (i : ColIdx ι c) _ (j : ColIdx ι c) _ hij =>
          colFamily_commute (R := R) c hij (v i) (v j)) := rfl
  rw [h_eq]
  exact coe_columnSweep_aux c v Finset.univ

end ColMatrix

section RowEntry

omit [Fintype ι] in
theorem rowSum_apply_finset (r : ι) (v : RowIdx ι r → Multiplicative R)
    (s : Finset (RowIdx ι r)) (p q : ι) :
    (∑ i ∈ s, rowSingle r v i) p q =
      ∑ i ∈ s, (rowSingle r v i p q) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    calc (∑ i ∈ insert a s, rowSingle r v i) p q
        = (rowSingle r v a + ∑ i ∈ s, rowSingle r v i) p q := by
          rw [Finset.sum_insert ha]
      _ = rowSingle r v a p q + (∑ i ∈ s, rowSingle r v i) p q := by
          rw [Matrix.add_apply]
      _ = rowSingle r v a p q + ∑ i ∈ s, (rowSingle r v i p q) := by
          rw [ih]
      _ = ∑ i ∈ insert a s, (rowSingle r v i p q) := by
          rw [Finset.sum_insert ha]

omit [Fintype ι] in
theorem rowSingle_entry (r : ι) (v : RowIdx ι r → Multiplicative R)
    (i : RowIdx ι r) (p q : ι) :
    rowSingle r v i p q =
      if p = i.val ∧ q = r then (v i).toAdd else 0 := by
  unfold rowSingle
  rw [Matrix.single_apply]
  have h_equiv : (p = i.val ∧ q = r) ↔ (i.val = p ∧ r = q) := by
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨hp.symm, hq.symm⟩
    · rintro ⟨hp, hq⟩
      exact ⟨hp.symm, hq.symm⟩
  by_cases h : p = i.val ∧ q = r
  · rw [ite_eq_left h, ite_eq_left (h_equiv.mp h)]
  · rw [ite_eq_right h, ite_eq_right (by intro h2; exact h (h_equiv.mpr h2))]

theorem rowSum_entry (r : ι) (v : RowIdx ι r → Multiplicative R) (p q : ι) :
    rowSum r v p q =
      if h : p < r then (if q = r then (v ⟨p, h⟩).toAdd else 0) else 0 := by
  classical
  have h_sum : rowSum r v p q =
      ∑ i : RowIdx ι r, rowSingle r v i p q := by
    unfold rowSum
    have := rowSum_apply_finset r v Finset.univ p q
    rw [this]
  rw [h_sum]
  have h_rw : ∀ (i : RowIdx ι r),
      rowSingle r v i p q =
        if p = i.val ∧ q = r then (v i).toAdd else 0 := by
    intro i
    exact rowSingle_entry r v i p q
  simp only [h_rw]
  by_cases hp : p < r
  · by_cases hq : q = r
    · have h_simp : ∀ (i : RowIdx ι r),
          (if p = i.val ∧ q = r then (v i).toAdd else 0) =
            (if p = i.val then (v i).toAdd else 0) := by
        intro i
        simp [hq]
      have h_eq : ∀ (i : RowIdx ι r),
          (if p = i.val then (v i).toAdd else 0) =
            if i = ⟨p, hp⟩ then (v ⟨p, hp⟩).toAdd else 0 := by
        intro i
        by_cases hi : i = ⟨p, hp⟩
        · subst hi
          simp
        · have hval : ¬(p = i.val) := by
            intro heq
            apply hi
            exact Subtype.ext heq.symm
          simp [hval, hi]
      calc (∑ i : RowIdx ι r, if p = i.val ∧ q = r then (v i).toAdd else 0)
          = (∑ i : RowIdx ι r, if p = i.val then (v i).toAdd else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            exact h_simp i
        _ = ∑ i : RowIdx ι r,
              if i = ⟨p, hp⟩ then (v ⟨p, hp⟩).toAdd else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            exact h_eq i
        _ = (v ⟨p, hp⟩).toAdd := by
            rw [Finset.sum_eq_single (⟨p, hp⟩ : RowIdx ι r)]
            · simp
            · intro b _ hb
              simp [hb]
            · intro hb
              exact absurd (Finset.mem_univ _) hb
      simp [hp, hq]
    · simp [hp, hq]
  · have h_zero : ∀ (i : RowIdx ι r),
        (if p = i.val ∧ q = r then (v i).toAdd else 0) = 0 := by
      intro i
      have : ¬(p = i.val ∧ q = r) := by
        intro ⟨hp_eq, _⟩
        have : p < r := hp_eq ▸ i.prop
        exact hp this
      simp [this]
    simp [h_zero, hp]

theorem rowSum_mul_apply_finset (r : ι) (v : RowIdx ι r → Multiplicative R)
    (s : Finset (RowIdx ι r)) (M : Matrix ι ι R) (i j : ι) :
    ((∑ k ∈ s, rowSingle r v k) * M) i j =
      ∑ k ∈ s, (rowSingle r v k * M) i j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    calc ((∑ k ∈ insert a s, rowSingle r v k) * M) i j
        = ((rowSingle r v a + ∑ k ∈ s, rowSingle r v k) * M) i j := by
          rw [Finset.sum_insert ha]
      _ = (rowSingle r v a * M + (∑ k ∈ s, rowSingle r v k) * M) i j := by
          rw [add_mul]
      _ = (rowSingle r v a * M) i j + ((∑ k ∈ s, rowSingle r v k) * M) i j := by
          rw [Matrix.add_apply]
      _ = (rowSingle r v a * M) i j + ∑ k ∈ s, (rowSingle r v k * M) i j := by
          rw [ih]
      _ = ∑ k ∈ insert a s, (rowSingle r v k * M) i j := by
          rw [Finset.sum_insert ha]

theorem rowSingle_mul_entry (r : ι) (v : RowIdx ι r → Multiplicative R)
    (i : RowIdx ι r) (M : Matrix ι ι R) (p q : ι) :
    (rowSingle r v i * M) p q =
      if p = i.val then (v i).toAdd * M r q else 0 := by
  unfold rowSingle
  by_cases hp : p = i.val
  · subst hp
    have h1 : (Matrix.single i.val r (v i).toAdd * M) i.val q =
        (v i).toAdd * M r q := by
      calc (Matrix.single i.val r (v i).toAdd * M) i.val q
          = ∑ x, (Matrix.single i.val r (v i).toAdd) i.val x * M x q := by
            rw [Matrix.mul_apply]
        _ = ∑ x, (if r = x then (v i).toAdd else 0) * M x q := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : r = x
            · simp [hx]
            · simp [hx]
        _ = (v i).toAdd * M r q := by
            rw [Finset.sum_eq_single r]
            · simp
            · intro b _ hb
              have : r ≠ b := fun h => hb h.symm
              simp [this]
            · simp
    simp [h1]
  · have h_zero : (Matrix.single i.val r (v i).toAdd * M) p q = 0 := by
      calc (Matrix.single i.val r (v i).toAdd * M) p q
          = ∑ x, (Matrix.single i.val r (v i).toAdd) p x * M x q := by
            rw [Matrix.mul_apply]
        _ = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            have : Matrix.single i.val r (v i).toAdd p x = 0 := by
              have : ¬(i.val = p ∧ r = x) := by
                intro ⟨hp', _⟩
                exact hp hp'.symm
              rw [Matrix.single_apply]
              rw [ite_eq_right this]
            simp [this]
    simp [hp, h_zero]

theorem rowSum_mul_entry (r : ι) (v : RowIdx ι r → Multiplicative R)
    (s : Finset (RowIdx ι r)) (M : Matrix ι ι R) (i j : ι) :
    ((∑ k ∈ s, rowSingle r v k) * M) i j =
      ∑ k ∈ s, if i = k.val then (v k).toAdd * M r j else 0 := by
  classical
  calc ((∑ k ∈ s, rowSingle r v k) * M) i j
      = ∑ k ∈ s, (rowSingle r v k * M) i j := by
        exact rowSum_mul_apply_finset r v s M i j
    _ = ∑ k ∈ s, if i = k.val then (v k).toAdd * M r j else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        exact rowSingle_mul_entry r v k M i j

theorem rowSum_mul_apply (r : ι) (v : RowIdx ι r → Multiplicative R)
    (M : Matrix ι ι R) (i j : ι) :
    (rowSum r v * M) i j =
      if h : i < r then (v ⟨i, h⟩).toAdd * M r j else 0 := by
  classical
  have h_general := rowSum_mul_entry r v Finset.univ M i j
  unfold rowSum at h_general ⊢
  rw [h_general]
  by_cases hi : i < r
  · have h_eq : (∑ k : RowIdx ι r,
          if i = k.val then (v k).toAdd * M r j else 0) =
        (v ⟨i, hi⟩).toAdd * M r j := by
      have h_eq2 : ∀ (k : RowIdx ι r),
          (if i = k.val then (v k).toAdd * M r j else 0) =
            if k = ⟨i, hi⟩ then (v ⟨i, hi⟩).toAdd * M r j else 0 := by
        intro k
        by_cases hk : k = ⟨i, hi⟩
        · subst hk
          simp
        · have hval : ¬(i = k.val) := by
            intro heq
            apply hk
            exact Subtype.ext heq.symm
          simp [hval, hk]
      calc (∑ k : RowIdx ι r, if i = k.val then (v k).toAdd * M r j else 0)
          = ∑ k : RowIdx ι r,
              if k = ⟨i, hi⟩ then (v ⟨i, hi⟩).toAdd * M r j else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            exact h_eq2 k
        _ = (v ⟨i, hi⟩).toAdd * M r j := by
            rw [Finset.sum_eq_single (⟨i, hi⟩ : RowIdx ι r)]
            · simp
            · intro b _ hb
              simp [hb]
            · intro hb
              exact absurd (Finset.mem_univ _) hb
    rw [h_eq]
    simp [hi]
  · have h_all_zero : ∀ (k : RowIdx ι r),
        (if i = k.val then (v k).toAdd * M r j else 0) = 0 := by
      intro k
      have hval : ¬(i = k.val) := by
        intro heq
        have : i < r := heq ▸ k.prop
        exact hi this
      simp [hval]
    have : (∑ k : RowIdx ι r,
        if i = k.val then (v k).toAdd * M r j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact h_all_zero k
    rw [this]
    simp [hi]

theorem rowSweep_mul_apply (r : ι) (v : RowIdx ι r → Multiplicative R)
    (M : Matrix ι ι R) (i j : ι) :
    (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) i j =
      if h : i < r then M i j + (v ⟨i, h⟩).toAdd * M r j else M i j := by
  classical
  have h_eq : (↑(rowSweep r v) : Matrix ι ι R) = 1 + rowSum r v :=
    coe_rowSweep r v
  calc (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) i j
      = ((1 + rowSum r v) * M) i j := by rw [h_eq]
    _ = (M + rowSum r v * M) i j := by rw [add_mul, one_mul]
    _ = M i j + (rowSum r v * M) i j := by rw [Matrix.add_apply]
    _ = if h : i < r then M i j + (v ⟨i, h⟩).toAdd * M r j else M i j := by
        rw [rowSum_mul_apply]
        by_cases hi : i < r <;> simp [hi]

end RowEntry

section ColEntry

omit [Fintype ι] in
theorem colSum_apply_finset (c : ι) (v : ColIdx ι c → Multiplicative R)
    (s : Finset (ColIdx ι c)) (p q : ι) :
    (∑ j ∈ s, colSingle c v j) p q =
      ∑ j ∈ s, (colSingle c v j p q) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    calc (∑ j ∈ insert a s, colSingle c v j) p q
        = (colSingle c v a + ∑ j ∈ s, colSingle c v j) p q := by
          rw [Finset.sum_insert ha]
      _ = colSingle c v a p q + (∑ j ∈ s, colSingle c v j) p q := by
          rw [Matrix.add_apply]
      _ = colSingle c v a p q + ∑ j ∈ s, (colSingle c v j p q) := by
          rw [ih]
      _ = ∑ j ∈ insert a s, (colSingle c v j p q) := by
          rw [Finset.sum_insert ha]

omit [Fintype ι] in
theorem colSingle_entry (c : ι) (v : ColIdx ι c → Multiplicative R)
    (j : ColIdx ι c) (p q : ι) :
    colSingle c v j p q =
      if p = c ∧ q = j.val then (v j).toAdd else 0 := by
  unfold colSingle
  rw [Matrix.single_apply]
  have h_equiv : (p = c ∧ q = j.val) ↔ (c = p ∧ j.val = q) := by
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨hp.symm, hq.symm⟩
    · rintro ⟨hp, hq⟩
      exact ⟨hp.symm, hq.symm⟩
  by_cases h : p = c ∧ q = j.val
  · rw [ite_eq_left h, ite_eq_left (h_equiv.mp h)]
  · rw [ite_eq_right h, ite_eq_right (by intro h2; exact h (h_equiv.mpr h2))]

theorem colSum_entry (c : ι) (v : ColIdx ι c → Multiplicative R) (p q : ι) :
    colSum c v p q =
      if h : c < q then (if p = c then (v ⟨q, h⟩).toAdd else 0) else 0 := by
  classical
  have h_sum : colSum c v p q =
      ∑ j : ColIdx ι c, colSingle c v j p q := by
    unfold colSum
    have := colSum_apply_finset c v Finset.univ p q
    rw [this]
  rw [h_sum]
  have h_rw : ∀ (j : ColIdx ι c),
      colSingle c v j p q =
        if p = c ∧ q = j.val then (v j).toAdd else 0 := by
    intro j
    exact colSingle_entry c v j p q
  simp only [h_rw]
  by_cases hq : c < q
  · by_cases hp : p = c
    · have h_simp : ∀ (j : ColIdx ι c),
          (if p = c ∧ q = j.val then (v j).toAdd else 0) =
            (if q = j.val then (v j).toAdd else 0) := by
        intro j
        simp [hp]
      have h_eq : ∀ (j : ColIdx ι c),
          (if q = j.val then (v j).toAdd else 0) =
            if j = ⟨q, hq⟩ then (v ⟨q, hq⟩).toAdd else 0 := by
        intro j
        by_cases hj : j = ⟨q, hq⟩
        · subst hj
          simp
        · have hval : ¬(q = j.val) := by
            intro heq
            apply hj
            exact Subtype.ext heq.symm
          simp [hval, hj]
      calc (∑ j : ColIdx ι c, if p = c ∧ q = j.val then (v j).toAdd else 0)
          = (∑ j : ColIdx ι c, if q = j.val then (v j).toAdd else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            exact h_simp j
        _ = ∑ j : ColIdx ι c,
              if j = ⟨q, hq⟩ then (v ⟨q, hq⟩).toAdd else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            exact h_eq j
        _ = (v ⟨q, hq⟩).toAdd := by
            rw [Finset.sum_eq_single (⟨q, hq⟩ : ColIdx ι c)]
            · simp
            · intro b _ hb
              simp [hb]
            · intro hb
              exact absurd (Finset.mem_univ _) hb
      simp [hp, hq]
    · simp [hp, hq]
  · have h_zero : ∀ (j : ColIdx ι c),
        (if p = c ∧ q = j.val then (v j).toAdd else 0) = 0 := by
      intro j
      have hq_contra : ¬(q = j.val) := by
        intro hq_eq
        have : c < q := hq_eq ▸ j.prop
        exact hq this
      have : ¬(p = c ∧ q = j.val) := by
        intro ⟨_, hq_eq⟩
        exact hq_contra hq_eq
      simp [this]
    simp [h_zero, hq]

theorem colSum_mul_aux_finset (c : ι) (v : ColIdx ι c → Multiplicative R)
    (s : Finset (ColIdx ι c)) (M : Matrix ι ι R) (i j : ι) :
    (M * (∑ k ∈ s, colSingle c v k)) i j =
      ∑ k ∈ s, (M * colSingle c v k) i j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    calc (M * (∑ k ∈ insert a s, colSingle c v k)) i j
        = (M * (colSingle c v a + ∑ k ∈ s, colSingle c v k)) i j := by
          rw [Finset.sum_insert ha]
      _ = (M * colSingle c v a + M * (∑ k ∈ s, colSingle c v k)) i j := by
          rw [mul_add]
      _ = (M * colSingle c v a) i j + (M * (∑ k ∈ s, colSingle c v k)) i j := by
          rw [Matrix.add_apply]
      _ = (M * colSingle c v a) i j + ∑ k ∈ s, (M * colSingle c v k) i j := by
          rw [ih]
      _ = ∑ k ∈ insert a s, (M * colSingle c v k) i j := by
          rw [Finset.sum_insert ha]

theorem colSingle_mul_entry_col (c : ι) (v : ColIdx ι c → Multiplicative R)
    (j : ColIdx ι c) (M : Matrix ι ι R) (p q : ι) :
    (M * colSingle c v j) p q =
      if q = j.val then M p c * (v j).toAdd else 0 := by
  unfold colSingle
  by_cases hq : q = j.val
  · subst hq
    have h1 : (M * Matrix.single c j.val (v j).toAdd) p j.val =
        M p c * (v j).toAdd := by
      calc (M * Matrix.single c j.val (v j).toAdd) p j.val
          = ∑ x, M p x * (Matrix.single c j.val (v j).toAdd) x j.val := by
            rw [Matrix.mul_apply]
        _ = ∑ x, M p x * (if c = x then (v j).toAdd else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : c = x
            · simp [hx]
            · simp [hx]
        _ = M p c * (v j).toAdd := by
            rw [Finset.sum_eq_single c]
            · simp
            · intro b _ hb
              have : c ≠ b := fun h => hb h.symm
              simp [this]
            · simp
    simp [h1]
  · have h_zero : (M * Matrix.single c j.val (v j).toAdd) p q = 0 := by
      calc (M * Matrix.single c j.val (v j).toAdd) p q
          = ∑ x, M p x * (Matrix.single c j.val (v j).toAdd) x q := by
            rw [Matrix.mul_apply]
        _ = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            have : Matrix.single c j.val (v j).toAdd x q = 0 := by
              have : ¬(c = x ∧ j.val = q) := by
                intro ⟨_, hq_eq⟩
                exact hq hq_eq.symm
              rw [Matrix.single_apply]
              rw [ite_eq_right this]
            simp [this]
    simp [hq, h_zero]

theorem colSum_mul_entry (c : ι) (v : ColIdx ι c → Multiplicative R)
    (s : Finset (ColIdx ι c)) (M : Matrix ι ι R) (i j : ι) :
    (M * (∑ k ∈ s, colSingle c v k)) i j =
      ∑ k ∈ s, if j = k.val then M i c * (v k).toAdd else 0 := by
  classical
  calc (M * (∑ k ∈ s, colSingle c v k)) i j
      = ∑ k ∈ s, (M * colSingle c v k) i j := by
        exact colSum_mul_aux_finset c v s M i j
    _ = ∑ k ∈ s, if j = k.val then M i c * (v k).toAdd else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        exact colSingle_mul_entry_col c v k M i j

theorem colSum_mul_apply (c : ι) (v : ColIdx ι c → Multiplicative R)
    (M : Matrix ι ι R) (i j : ι) :
    (M * colSum c v) i j =
      if h : c < j then M i c * (v ⟨j, h⟩).toAdd else 0 := by
  classical
  have h_general := colSum_mul_entry c v Finset.univ M i j
  unfold colSum at h_general ⊢
  rw [h_general]
  by_cases hj : c < j
  · have h_eq : (∑ k : ColIdx ι c,
          if j = k.val then M i c * (v k).toAdd else 0) =
        M i c * (v ⟨j, hj⟩).toAdd := by
      have h_eq2 : ∀ (k : ColIdx ι c),
          (if j = k.val then M i c * (v k).toAdd else 0) =
            if k = ⟨j, hj⟩ then M i c * (v ⟨j, hj⟩).toAdd else 0 := by
        intro k
        by_cases hk : k = ⟨j, hj⟩
        · subst hk
          simp
        · have hval : ¬(j = k.val) := by
            intro heq
            apply hk
            exact Subtype.ext heq.symm
          simp [hval, hk]
      calc (∑ k : ColIdx ι c, if j = k.val then M i c * (v k).toAdd else 0)
          = ∑ k : ColIdx ι c,
              if k = ⟨j, hj⟩ then M i c * (v ⟨j, hj⟩).toAdd else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            exact h_eq2 k
        _ = M i c * (v ⟨j, hj⟩).toAdd := by
            rw [Finset.sum_eq_single (⟨j, hj⟩ : ColIdx ι c)]
            · simp
            · intro b _ hb
              simp [hb]
            · intro hb
              exact absurd (Finset.mem_univ _) hb
    rw [h_eq]
    simp [hj]
  · have h_all_zero : ∀ (k : ColIdx ι c),
        (if j = k.val then M i c * (v k).toAdd else 0) = 0 := by
      intro k
      have hval : ¬(j = k.val) := by
        intro heq
        have : c < j := heq ▸ k.prop
        exact hj this
      simp [hval]
    have : (∑ k : ColIdx ι c,
        if j = k.val then M i c * (v k).toAdd else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact h_all_zero k
    rw [this]
    simp [hj]

theorem columnSweep_mul_apply (c : ι) (v : ColIdx ι c → Multiplicative R)
    (M : Matrix ι ι R) (i j : ι) :
    (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i j =
      if h : c < j then M i j + M i c * (v ⟨j, h⟩).toAdd else M i j := by
  classical
  have h_eq : (↑(columnSweep c v) : Matrix ι ι R) = 1 + colSum c v :=
    coe_columnSweep c v
  calc (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i j
      = (M * (1 + colSum c v)) i j := by rw [h_eq]
    _ = (M + M * colSum c v) i j := by rw [mul_add, mul_one]
    _ = M i j + (M * colSum c v) i j := by rw [Matrix.add_apply]
    _ = if h : c < j then M i j + M i c * (v ⟨j, h⟩).toAdd else M i j := by
        rw [colSum_mul_apply]
        by_cases hj : c < j <;> simp [hj]

end ColEntry


section Membership

theorem rowSweep_mem_aux (r : ι) (v : RowIdx ι r → Multiplicative R)
    (s : Finset (RowIdx ι r)) :
    s.noncommProd (fun i => rowFamily r i (v i))
      (fun (i : RowIdx ι r) _ (j : RowIdx ι r) _ hij =>
        rowFamily_commute (R := R) r hij (v i) (v j)) ∈
      upperElementarySubgroup ι R := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h_empty : (∅ : Finset (RowIdx ι r)).noncommProd
        (fun i => rowFamily r i (v i))
        (fun (i : RowIdx ι r) _ (j : RowIdx ι r) _ hij =>
          rowFamily_commute (R := R) r hij (v i) (v j)) = 1 := rfl
    rw [h_empty]
    exact (upperElementarySubgroup ι R).one_mem
  | @insert a s ha ih =>
    have h_comm_insert : (↑(insert a s) : Set (RowIdx ι r)).Pairwise
        (onFun Commute (fun i => rowFamily r i (v i))) := by
      intro i _ j _ hij
      exact rowFamily_commute (R := R) r hij (v i) (v j)
    have h_comm_s : (↑s : Set (RowIdx ι r)).Pairwise
        (onFun Commute (fun i => rowFamily r i (v i))) := by
      intro i _ j _ hij
      exact rowFamily_commute (R := R) r hij (v i) (v j)
    have h_prod : (insert a s).noncommProd (fun i => rowFamily r i (v i))
        h_comm_insert =
        rowFamily r a (v a) *
          s.noncommProd (fun i => rowFamily r i (v i)) h_comm_s := by
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    rw [h_prod]
    apply (upperElementarySubgroup ι R).mul_mem
    · exact elementary_mem_upperElementarySubgroup _ _ a.prop _
    · exact ih

theorem rowSweep_mem_upperElementary (r : ι)
    (v : RowIdx ι r → Multiplicative R) :
    rowSweep r v ∈ upperElementarySubgroup ι R := by
  classical
  have h_eq : rowSweep (R := R) r v =
      Finset.univ.noncommProd (fun i => rowFamily r i (v i))
        (fun (i : RowIdx ι r) _ (j : RowIdx ι r) _ hij =>
          rowFamily_commute (R := R) r hij (v i) (v j)) := rfl
  rw [h_eq]
  exact rowSweep_mem_aux r v Finset.univ

theorem columnSweep_mem_aux (c : ι) (v : ColIdx ι c → Multiplicative R)
    (s : Finset (ColIdx ι c)) :
    s.noncommProd (fun j => colFamily c j (v j))
      (fun (i : ColIdx ι c) _ (j : ColIdx ι c) _ hij =>
        colFamily_commute (R := R) c hij (v i) (v j)) ∈
      upperElementarySubgroup ι R := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h_empty : (∅ : Finset (ColIdx ι c)).noncommProd
        (fun j => colFamily c j (v j))
        (fun (i : ColIdx ι c) _ (j : ColIdx ι c) _ hij =>
          colFamily_commute (R := R) c hij (v i) (v j)) = 1 := rfl
    rw [h_empty]
    exact (upperElementarySubgroup ι R).one_mem
  | @insert a s ha ih =>
    have h_comm_insert : (↑(insert a s) : Set (ColIdx ι c)).Pairwise
        (onFun Commute (fun j => colFamily c j (v j))) := by
      intro i _ j _ hij
      exact colFamily_commute (R := R) c hij (v i) (v j)
    have h_comm_s : (↑s : Set (ColIdx ι c)).Pairwise
        (onFun Commute (fun j => colFamily c j (v j))) := by
      intro i _ j _ hij
      exact colFamily_commute (R := R) c hij (v i) (v j)
    have h_prod : (insert a s).noncommProd (fun j => colFamily c j (v j))
        h_comm_insert =
        colFamily c a (v a) *
          s.noncommProd (fun j => colFamily c j (v j)) h_comm_s := by
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    rw [h_prod]
    apply (upperElementarySubgroup ι R).mul_mem
    · exact elementary_mem_upperElementarySubgroup _ _ a.prop _
    · exact ih

theorem columnSweep_mem_upperElementary (c : ι)
    (v : ColIdx ι c → Multiplicative R) :
    columnSweep c v ∈ upperElementarySubgroup ι R := by
  classical
  have h_eq : columnSweep (R := R) c v =
      Finset.univ.noncommProd (fun j => colFamily c j (v j))
        (fun (i : ColIdx ι c) _ (j : ColIdx ι c) _ hij =>
          colFamily_commute (R := R) c hij (v i) (v j)) := rfl
  rw [h_eq]
  exact columnSweep_mem_aux c v Finset.univ

end Membership

section UpperRestricted

namespace UpperElementary

/-- The simultaneous row word in the actual upper elementary subgroup. -/
noncomputable def rowSweep (r : ι) :
    (RowIdx ι r → Multiplicative R) →* upperElementarySubgroup ι R :=
  (Matrix.GeneralLinearGroup.rowSweep r).codRestrict
    (upperElementarySubgroup ι R) (fun v => rowSweep_mem_upperElementary r v)

/-- The simultaneous column word in the actual upper elementary subgroup. -/
noncomputable def columnSweep (c : ι) :
    (ColIdx ι c → Multiplicative R) →* upperElementarySubgroup ι R :=
  (Matrix.GeneralLinearGroup.columnSweep c).codRestrict
    (upperElementarySubgroup ι R) (fun v => columnSweep_mem_upperElementary c v)

@[simp]
theorem coe_rowSweep (r : ι) (v : RowIdx ι r → Multiplicative R) :
    (↑(rowSweep (R := R) r v) : GL ι R) =
      Matrix.GeneralLinearGroup.rowSweep r v := rfl

@[simp]
theorem coe_columnSweep (c : ι) (v : ColIdx ι c → Multiplicative R) :
    (↑(columnSweep (R := R) c v) : GL ι R) =
      Matrix.GeneralLinearGroup.columnSweep c v := rfl

theorem rowSweep_mulSingle (r : ι) (i : RowIdx ι r) (a : R) :
    rowSweep (R := R) r (Pi.mulSingle i (Multiplicative.ofAdd a)) =
      elementary i.val r i.prop a := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.rowSweep_mulSingle,
    rowFamily, elementaryMulHom]

theorem columnSweep_mulSingle (c : ι) (j : ColIdx ι c) (a : R) :
    columnSweep (R := R) c (Pi.mulSingle j (Multiplicative.ofAdd a)) =
      elementary c j.val j.prop a := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.columnSweep_mulSingle,
    colFamily, elementaryMulHom]

end UpperElementary

end UpperRestricted

section Naturality

variable {S : Type*} [Ring S]

/-- The coefficient homomorphism on additive rings under the multiplicative tag. -/
noncomputable def multiplicativeMap (f : R →+* S) :
    Multiplicative R →* Multiplicative S where
  toFun x := Multiplicative.ofAdd (f x.toAdd)
  map_one' := by simp
  map_mul' a b := by simp

@[simp]
theorem multiplicativeMap_toAdd (f : R →+* S) (x : Multiplicative R) :
    (multiplicativeMap f x).toAdd = f x.toAdd := rfl

theorem rowSweep_mapRingHom (f : R →+* S) (r : ι)
    (v : RowIdx ι r → Multiplicative R) :
    mapRingHom (n := ι) f (rowSweep (R := R) r v) =
      rowSweep (R := S) r (fun i => multiplicativeMap f (v i)) := by
  classical
  apply Units.ext
  rw [coe_mapRingHom, coe_rowSweep, coe_rowSweep]
  apply Matrix.ext
  intro p q
  calc ((1 + rowSum r v : Matrix ι ι R).map f) p q
      = f ((1 + rowSum r v) p q) := rfl
    _ = f ((1 : Matrix ι ι R) p q + rowSum r v p q) := by rw [Matrix.add_apply]
    _ = f ((1 : Matrix ι ι R) p q) + f (rowSum r v p q) := by rw [f.map_add]
    _ = (1 : Matrix ι ι S) p q + f (rowSum r v p q) := by
        have : f ((1 : Matrix ι ι R) p q) = (1 : Matrix ι ι S) p q := by
          by_cases hpq : p = q
          · subst hpq
            simp [Matrix.one_apply_eq]
          · simp [Matrix.one_apply_ne, hpq]
        rw [this]
    _ = (1 : Matrix ι ι S) p q + rowSum (R := S) r (fun i => multiplicativeMap f (v i)) p q := by
        congr 1
        rw [rowSum_entry (r := r) (v := v) (p := p) (q := q),
          rowSum_entry (r := r) (v := fun i => multiplicativeMap f (v i)) (p := p) (q := q)]
        by_cases hp : p < r
        · by_cases hq : q = r
          · simp [hp, hq, multiplicativeMap_toAdd]
          · simp [hp, hq, f.map_zero]
        · simp [hp, f.map_zero]
    _ = (1 + rowSum (R := S) r (fun i => multiplicativeMap f (v i))) p q := by
        rw [Matrix.add_apply]

theorem columnSweep_mapRingHom (f : R →+* S) (c : ι)
    (v : ColIdx ι c → Multiplicative R) :
    mapRingHom (n := ι) f (columnSweep (R := R) c v) =
      columnSweep (R := S) c (fun j => multiplicativeMap f (v j)) := by
  classical
  apply Units.ext
  rw [coe_mapRingHom, coe_columnSweep, coe_columnSweep]
  apply Matrix.ext
  intro p q
  calc ((1 + colSum c v : Matrix ι ι R).map f) p q
      = f ((1 + colSum c v) p q) := rfl
    _ = f ((1 : Matrix ι ι R) p q + colSum c v p q) := by rw [Matrix.add_apply]
    _ = f ((1 : Matrix ι ι R) p q) + f (colSum c v p q) := by rw [f.map_add]
    _ = (1 : Matrix ι ι S) p q + f (colSum c v p q) := by
        have : f ((1 : Matrix ι ι R) p q) = (1 : Matrix ι ι S) p q := by
          by_cases hpq : p = q
          · subst hpq
            simp [Matrix.one_apply_eq]
          · simp [Matrix.one_apply_ne, hpq]
        rw [this]
    _ = (1 : Matrix ι ι S) p q + colSum (R := S) c (fun j => multiplicativeMap f (v j)) p q := by
        congr 1
        rw [colSum_entry (c := c) (v := v) (p := p) (q := q),
          colSum_entry (c := c) (v := fun j => multiplicativeMap f (v j)) (p := p) (q := q)]
        by_cases hq : c < q
        · by_cases hp : p = c
          · simp [hq, hp, multiplicativeMap_toAdd]
          · simp [hq, hp]
        · simp [hq, f.map_zero]
    _ = (1 + colSum (R := S) c (fun j => multiplicativeMap f (v j))) p q := by
        rw [Matrix.add_apply]

end Naturality

section UpperNaturality

variable {S : Type*} [Ring S]

namespace UpperElementary

theorem rowSweep_mapRingHom' {R : Type*} [Ring R] {S : Type*} [Ring S]
    (f : R →+* S) (r : ι) (v : RowIdx ι r → Multiplicative R) :
    mapRingHom (ι := ι) f (rowSweep (R := R) r v) =
      rowSweep (R := S) r (fun i => Matrix.GeneralLinearGroup.multiplicativeMap f (v i)) := by
  apply Subtype.ext
  simp only [coe_rowSweep]
  exact Matrix.GeneralLinearGroup.rowSweep_mapRingHom f r v

theorem columnSweep_mapRingHom' {R : Type*} [Ring R] {S : Type*} [Ring S]
    (f : R →+* S) (c : ι) (v : ColIdx ι c → Multiplicative R) :
    mapRingHom (ι := ι) f (columnSweep (R := R) c v) =
      columnSweep (R := S) c (fun j => Matrix.GeneralLinearGroup.multiplicativeMap f (v j)) := by
  apply Subtype.ext
  simp only [coe_columnSweep]
  exact Matrix.GeneralLinearGroup.columnSweep_mapRingHom f c v

end UpperElementary

end UpperNaturality

section PivotConsequences

theorem rowSweep_mul_apply_same_row (r : ι)
    (v : RowIdx ι r → Multiplicative R) (M : Matrix ι ι R) (j : ι) :
    (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) r j = M r j := by
  have h := rowSweep_mul_apply r v M r j
  have hr : ¬(r < r) := lt_irrefl r
  simp only [hr, dite_false] at h
  exact h

theorem rowSweep_mul_apply_of_not_lt (r : ι)
    (v : RowIdx ι r → Multiplicative R) (M : Matrix ι ι R)
    (i j : ι) (h : ¬(i < r)) :
    (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) i j = M i j := by
  have h_eq := rowSweep_mul_apply r v M i j
  simp only [h, dite_false] at h_eq
  exact h_eq

theorem columnSweep_mul_apply_same_col (c : ι)
    (v : ColIdx ι c → Multiplicative R) (M : Matrix ι ι R) (i : ι) :
    (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i c = M i c := by
  have h := columnSweep_mul_apply c v M i c
  have hc : ¬(c < c) := lt_irrefl c
  simp only [hc, dite_false] at h
  exact h

theorem columnSweep_mul_apply_of_not_gt (c : ι)
    (v : ColIdx ι c → Multiplicative R) (M : Matrix ι ι R)
    (i j : ι) (h : ¬(c < j)) :
    (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i j = M i j := by
  have h_eq := columnSweep_mul_apply c v M i j
  simp only [h, dite_false] at h_eq
  exact h_eq

end PivotConsequences

section FullRowSweepUniqueness

/-- Coefficient uniqueness for ordered full row-sweep products.

If the ascending ordered product of all row sweeps `rowSweep r (v r)` over
`r : Fin n` equals one, then every sweep coefficient `v r i` equals one.
The proof reads matrix entries in descending row order: every ordered prefix
product is upper-triangular with diagonal one, and the column of the next
index is untouched by earlier factors, so the vanishing of the full product
forces each coefficient to vanish in turn, starting from the last row. The
argument is uniform in `n`, including the degenerate ranks `0` and `1`.

This proves only the product-equal-one implication. It makes no claim about
injectivity of equality between two ordered products, ordered normal forms,
`toStableE` injectivity, TWT closure, kernel generation, or Matsumoto's
theorem. -/
theorem fullRowSweepProd_eq_one_imp {n : ℕ} {R : Type*} [Ring R]
    (v : (r : Fin n) →
      Matrix.GeneralLinearGroup.RowIdx (Fin n) r → Multiplicative R)
    (h : (List.ofFn (fun r : Fin n =>
      Matrix.GeneralLinearGroup.rowSweep (R := R) r (v r))).prod = 1) :
    ∀ (r : Fin n) (i : Matrix.GeneralLinearGroup.RowIdx (Fin n) r), v r i = 1 := by
  have hM : (((List.ofFn (fun r : Fin n =>
      rowSweep (R := R) r (v r))).prod) :
      Matrix (Fin n) (Fin n) R) = 1 := by
    rw [h]
    rfl
  have hS : ∀ (r p q : Fin n),
      ((rowSweep (R := R) r (v r)) : Matrix (Fin n) (Fin n) R) p q =
        (1 : Matrix (Fin n) (Fin n) R) p q +
          rowSum (R := R) r (v r) p q := by
    intro r p q
    have hcoe := coe_rowSweep (R := R) (r := r) (v := v r)
    calc ((rowSweep (R := R) r (v r)) : Matrix (Fin n) (Fin n) R) p q
        = ((1 + rowSum (R := R) r (v r) : Matrix (Fin n) (Fin n) R)) p q := by
          rw [hcoe]
      _ = _ := Matrix.add_apply _ _ _ _
  have hUT0 : ∀ (r p q : Fin n), q.val < p.val →
      ((rowSweep (R := R) r (v r)) : Matrix (Fin n) (Fin n) R) p q = 0 := by
    intro r p q hqp
    have hne : p ≠ q := by
      intro he
      rw [he] at hqp
      exact absurd hqp (lt_irrefl _)
    rw [hS, Matrix.one_apply, rowSum_entry, ite_eq_right hne]
    by_cases hpr : p < r
    · have hqr : q ≠ r := by
        intro he
        rw [he] at hqp
        have hlt : p.val < r.val := hpr
        omega
      rw [dite_eq_left hpr, ite_eq_right hqr, add_zero]
    · rw [dite_eq_right hpr, add_zero]
  have hdiag : ∀ (r p : Fin n),
      ((rowSweep (R := R) r (v r)) : Matrix (Fin n) (Fin n) R) p p = 1 := by
    intro r p
    rw [hS, Matrix.one_apply, rowSum_entry, ite_eq_left rfl]
    by_cases hpr : p < r
    · have hne : p ≠ r := ne_of_lt hpr
      rw [dite_eq_left hpr, ite_eq_right hne, add_zero]
    · rw [dite_eq_right hpr, add_zero]
  have hlen : (List.ofFn (fun r : Fin n =>
      rowSweep (R := R) r (v r))).length = n := by
    simp [List.length_ofFn]
  have htake : ∀ (m : ℕ) (hm : m < n),
      (((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take (m + 1)).prod :
        GL (Fin n) R) =
        ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take m).prod *
          rowSweep (R := R) (⟨m, hm⟩ : Fin n) (v (⟨m, hm⟩ : Fin n)) := by
    intro m hm
    have hmem : m <
        (List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).length := by
      rw [hlen]
      exact hm
    rw [List.prod_take_succ _ m hmem]
    congr 1
    simp only [List.getElem_ofFn]
  have hcol : ∀ (m : ℕ) (_hm : m ≤ n) (c : Fin n), m ≤ c.val → ∀ (i : Fin n),
      ((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take m).prod) :
        Matrix (Fin n) (Fin n) R) i c = (1 : Matrix (Fin n) (Fin n) R) i c := by
    intro m
    induction m with
    | zero =>
      intro _ c _ i
      rw [List.take_zero, List.prod_nil, Units.val_one]
    | succ m ih =>
      intro hm c hc i
      have hm' : m < n := by omega
      have hmle : m ≤ n := by omega
      have hcc : m ≤ c.val := by omega
      have hB : ∀ k : Fin n,
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (v (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) k c =
            (1 : Matrix (Fin n) (Fin n) R) k c := by
        intro k
        have hne : c ≠ (⟨m, hm'⟩ : Fin n) := by
          intro he
          have hve : c.val = m := congrArg Fin.val he
          omega
        rw [hS, Matrix.one_apply, rowSum_entry]
        by_cases hkr : k < (⟨m, hm'⟩ : Fin n)
        · rw [dite_eq_left hkr, ite_eq_right hne, add_zero]
        · rw [dite_eq_right hkr, add_zero]
      rw [htake m hm', Units.val_mul, Matrix.mul_apply]
      have hsum : (∑ k : Fin n,
          ((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take m).prod) :
            Matrix (Fin n) (Fin n) R) i k *
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (v (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) k c) =
          ∑ k : Fin n, ((((List.ofFn (fun r : Fin n =>
            rowSweep (R := R) r (v r))).take m).prod) :
            Matrix (Fin n) (Fin n) R) i k *
            (1 : Matrix (Fin n) (Fin n) R) k c :=
        Finset.sum_congr rfl (fun k _ => by rw [hB k])
      rw [hsum, ← Matrix.mul_apply, Matrix.mul_one]
      exact ih hmle c hcc i
  have hut : ∀ (m : ℕ) (_hm : m ≤ n) (p q : Fin n), q.val < p.val →
      ((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take m).prod) :
        Matrix (Fin n) (Fin n) R) p q = 0 := by
    intro m
    induction m with
    | zero =>
      intro _ p q hqp
      have hne : p ≠ q := by
        intro he
        rw [he] at hqp
        exact absurd hqp (lt_irrefl _)
      rw [List.take_zero, List.prod_nil, Units.val_one]
      exact Matrix.one_apply_ne hne
    | succ m ih =>
      intro hm p q hqp
      have hm' : m < n := by omega
      have hmle : m ≤ n := by omega
      rw [htake m hm', Units.val_mul, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hkp : k.val < p.val
      · have hA : ((((List.ofFn (fun r : Fin n =>
              rowSweep (R := R) r (v r))).take m).prod) :
              Matrix (Fin n) (Fin n) R) p k = 0 := ih hmle p k hkp
        rw [hA, zero_mul]
      · have hB : ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
            (v (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) k q = 0 :=
          hUT0 _ _ _ (by omega)
        rw [hB, mul_zero]
  have hdd : ∀ (m : ℕ) (_hm : m ≤ n) (p : Fin n),
      ((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take m).prod) :
        Matrix (Fin n) (Fin n) R) p p = 1 := by
    intro m
    induction m with
    | zero =>
      intro _ p
      rw [List.take_zero, List.prod_nil, Units.val_one]
      exact Matrix.one_apply_eq p
    | succ m ih =>
      intro hm p
      have hm' : m < n := by omega
      have hmle : m ≤ n := by omega
      rw [htake m hm', Units.val_mul, Matrix.mul_apply]
      have h1 : ((((List.ofFn (fun r : Fin n =>
              rowSweep (R := R) r (v r))).take m).prod) :
              Matrix (Fin n) (Fin n) R) p p *
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (v (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) p p = 1 := by
        rw [ih hmle p, hdiag _ p, mul_one]
      have h0 : ∀ k : Fin n, k ≠ p →
          ((((List.ofFn (fun r : Fin n =>
              rowSweep (R := R) r (v r))).take m).prod) :
            Matrix (Fin n) (Fin n) R) p k *
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (v (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) k p = 0 := by
        intro k hkp
        by_cases hkp2 : k.val < p.val
        · rw [hut m hmle p k hkp2, zero_mul]
        · by_cases heq : k.val = p.val
          · exfalso
            exact hkp (Fin.ext_iff.mpr heq)
          · have hB : ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
                (v (⟨m, hm'⟩ : Fin n))) :
                Matrix (Fin n) (Fin n) R) k p = 0 :=
              hUT0 _ _ _ (by omega)
            rw [hB, mul_zero]
      calc (∑ k : Fin n, ((((List.ofFn (fun r : Fin n =>
              rowSweep (R := R) r (v r))).take m).prod) :
            Matrix (Fin n) (Fin n) R) p k *
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (v (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) k p)
          = _ := Finset.sum_eq_single_of_mem p (Finset.mem_univ p)
            (fun k _ hkp => h0 k hkp)
        _ = 1 := h1
  have hmain : ∀ (m : ℕ) (_hm : m ≤ n),
      ((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take m).prod) :
        Matrix (Fin n) (Fin n) R) = 1 →
      ∀ (r : Fin n), r.val < m → ∀ (i : RowIdx (Fin n) r), v r i = 1 := by
    intro m
    induction m with
    | zero =>
      intro _ _ r hr _
      omega
    | succ m ih =>
      intro hm h1 r hr i
      have hm' : m < n := by omega
      have hmle : m ≤ n := by omega
      rw [htake m hm'] at h1
      have h1M : ((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (v r))).take m).prod) :
          Matrix (Fin n) (Fin n) R) *
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (v (⟨m, hm'⟩ : Fin n))) :
          Matrix (Fin n) (Fin n) R) = 1 := by
        rw [← Units.val_mul]
        exact h1
      have hcoeff : ∀ (d d' : ℕ), d' ≤ d → ∀ (p : Fin n), p.val + d' = m →
          ∀ (j : RowIdx (Fin n) (⟨m, hm'⟩ : Fin n)), j.val = p.val →
          ((v (⟨m, hm'⟩ : Fin n) j).toAdd : R) = 0 := by
        intro d
        induction d with
        | zero =>
          intro d' hd' p hp j hj
          have hd0 : d' = 0 := by omega
          subst hd0
          have hjlt : j.val < m := j.prop
          omega
        | succ d ihd =>
          intro d' hd' p hp j hj
          by_cases hd0 : d' = 0
          · subst hd0
            have hjlt : j.val < m := j.prop
            omega
          · have hAc : ((((List.ofFn (fun r : Fin n =>
                  rowSweep (R := R) r (v r))).take m).prod) :
                Matrix (Fin n) (Fin n) R) p (⟨m, hm'⟩ : Fin n) =
                (1 : Matrix (Fin n) (Fin n) R) p (⟨m, hm'⟩ : Fin n) :=
              hcol m hmle (⟨m, hm'⟩ : Fin n) le_rfl p
            have hPc : (((((List.ofFn (fun r : Fin n =>
                    rowSweep (R := R) r (v r))).take m).prod) :
                  Matrix (Fin n) (Fin n) R) *
                  ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
                    (v (⟨m, hm'⟩ : Fin n))) : Matrix (Fin n) (Fin n) R))
                    p (⟨m, hm'⟩ : Fin n) =
                (1 : Matrix (Fin n) (Fin n) R) p (⟨m, hm'⟩ : Fin n) := by
              rw [h1M]
            have hBdecomp : ∀ k : Fin n,
                ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
                  (v (⟨m, hm'⟩ : Fin n))) : Matrix (Fin n) (Fin n) R) k
                  (⟨m, hm'⟩ : Fin n) =
                (1 : Matrix (Fin n) (Fin n) R) k (⟨m, hm'⟩ : Fin n) +
                  (if h : k < (⟨m, hm'⟩ : Fin n) then
                    ((v (⟨m, hm'⟩ : Fin n) ⟨k, h⟩).toAdd : R) else 0) := by
              intro k
              rw [hS, Matrix.one_apply]
              congr 1
              rw [rowSum_entry]
              by_cases hkr : k < (⟨m, hm'⟩ : Fin n)
              · rw [dite_eq_left hkr, dite_eq_left hkr, ite_eq_left rfl]
              · rw [dite_eq_right hkr, dite_eq_right hkr]
            have hAB : (((((List.ofFn (fun r : Fin n =>
                    rowSweep (R := R) r (v r))).take m).prod) :
                  Matrix (Fin n) (Fin n) R) *
                  ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
                    (v (⟨m, hm'⟩ : Fin n))) : Matrix (Fin n) (Fin n) R))
                    p (⟨m, hm'⟩ : Fin n) =
                ((((List.ofFn (fun r : Fin n =>
                    rowSweep (R := R) r (v r))).take m).prod) :
                  Matrix (Fin n) (Fin n) R) p (⟨m, hm'⟩ : Fin n) +
                ∑ k : Fin n, ((((List.ofFn (fun r : Fin n =>
                    rowSweep (R := R) r (v r))).take m).prod) :
                  Matrix (Fin n) (Fin n) R) p k *
                  (if h : k < (⟨m, hm'⟩ : Fin n) then
                    ((v (⟨m, hm'⟩ : Fin n) ⟨k, h⟩).toAdd : R) else 0) := by
              have e : ∀ k : Fin n, ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p k *
                    ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
                      (v (⟨m, hm'⟩ : Fin n))) : Matrix (Fin n) (Fin n) R) k
                      (⟨m, hm'⟩ : Fin n) =
                    ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p k *
                      (1 : Matrix (Fin n) (Fin n) R) k (⟨m, hm'⟩ : Fin n) +
                    ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p k *
                    (if h : k < (⟨m, hm'⟩ : Fin n) then
                      ((v (⟨m, hm'⟩ : Fin n) ⟨k, h⟩).toAdd : R) else 0) := by
                intro k
                rw [hBdecomp k, mul_add]
              rw [Matrix.mul_apply]
              rw [show (∑ k : Fin n, ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p k *
                    ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
                      (v (⟨m, hm'⟩ : Fin n))) : Matrix (Fin n) (Fin n) R) k
                      (⟨m, hm'⟩ : Fin n)) =
                  ∑ k : Fin n, (((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p k *
                      (1 : Matrix (Fin n) (Fin n) R) k (⟨m, hm'⟩ : Fin n) +
                    ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p k *
                    (if h : k < (⟨m, hm'⟩ : Fin n) then
                      ((v (⟨m, hm'⟩ : Fin n) ⟨k, h⟩).toAdd : R) else 0)) from
                Finset.sum_congr rfl (fun k _ => e k)]
              rw [Finset.sum_add_distrib, ← Matrix.mul_apply, Matrix.mul_one]
            have hS0 : (∑ k : Fin n, ((((List.ofFn (fun r : Fin n =>
                    rowSweep (R := R) r (v r))).take m).prod) :
                  Matrix (Fin n) (Fin n) R) p k *
                  (if h : k < (⟨m, hm'⟩ : Fin n) then
                    ((v (⟨m, hm'⟩ : Fin n) ⟨k, h⟩).toAdd : R) else 0)) = 0 := by
              have h2 : ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p (⟨m, hm'⟩ : Fin n) +
                  (∑ k : Fin n, ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p k *
                    (if h : k < (⟨m, hm'⟩ : Fin n) then
                      ((v (⟨m, hm'⟩ : Fin n) ⟨k, h⟩).toAdd : R) else 0)) =
                  ((((List.ofFn (fun r : Fin n =>
                      rowSweep (R := R) r (v r))).take m).prod) :
                    Matrix (Fin n) (Fin n) R) p (⟨m, hm'⟩ : Fin n) + 0 := by
                rw [add_zero, ← hAB, hPc, hAc]
              exact add_left_cancel_iff.mp h2
            have hterm : ∀ k : Fin n, k ≠ p →
                ((((List.ofFn (fun r : Fin n =>
                    rowSweep (R := R) r (v r))).take m).prod) :
                  Matrix (Fin n) (Fin n) R) p k *
                (if h : k < (⟨m, hm'⟩ : Fin n) then
                  ((v (⟨m, hm'⟩ : Fin n) ⟨k, h⟩).toAdd : R) else 0) = 0 := by
              intro k hkp
              by_cases hkr : k < (⟨m, hm'⟩ : Fin n)
              · by_cases hlt : k.val < p.val
                · rw [dite_eq_left hkr, hut m hmle p k hlt, zero_mul]
                · by_cases heq : k.val = p.val
                  · exfalso
                    exact hkp (Fin.ext_iff.mpr heq)
                  · have hkm : k.val < m := hkr
                    have hd'' : m - k.val ≤ d := by omega
                    have hkeq : k.val + (m - k.val) = m := by omega
                    have h0 := ihd (m - k.val) hd'' k hkeq ⟨k, hkr⟩ rfl
                    rw [dite_eq_left hkr, h0, mul_zero]
              · rw [dite_eq_right hkr, mul_zero]
            have hsingle := Finset.sum_eq_single_of_mem p (Finset.mem_univ p)
              (fun k _ hkp => hterm k hkp)
            have hfp : ((((List.ofFn (fun r : Fin n =>
                    rowSweep (R := R) r (v r))).take m).prod) :
                  Matrix (Fin n) (Fin n) R) p p *
                (if h : p < (⟨m, hm'⟩ : Fin n) then
                  ((v (⟨m, hm'⟩ : Fin n) ⟨p, h⟩).toAdd : R) else 0) = 0 :=
              hsingle.symm.trans hS0
            have hplt : p < (⟨m, hm'⟩ : Fin n) := by
              have hlt : p.val < m := by omega
              exact hlt
            rw [dite_eq_left hplt] at hfp
            rw [hdd m hmle p, one_mul] at hfp
            have hjeq : ((⟨p, hplt⟩ :
                RowIdx (Fin n) (⟨m, hm'⟩ : Fin n))) = j :=
              Subtype.ext (Fin.ext_iff.mpr hj.symm)
            rw [hjeq] at hfp
            exact hfp
      have htop : ∀ j : RowIdx (Fin n) (⟨m, hm'⟩ : Fin n),
          v (⟨m, hm'⟩ : Fin n) j = 1 := by
        intro j
        have hilt : j.val < m := j.prop
        have hbound : j.val < n := by omega
        have hsum : j.val + (m - j.val) = m := by omega
        have hi0 := hcoeff (m - j.val) (m - j.val) le_rfl
          (⟨j.val, hbound⟩ : Fin n) hsum j rfl
        have h1eq : Multiplicative.ofAdd ((v (⟨m, hm'⟩ : Fin n) j).toAdd : R) = 1 := by
          rw [hi0]
          exact ofAdd_zero
        calc v (⟨m, hm'⟩ : Fin n) j
            = Multiplicative.ofAdd ((v (⟨m, hm'⟩ : Fin n) j).toAdd : R) :=
              (ofAdd_toAdd _).symm
          _ = 1 := h1eq
      have hB1 : ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
          (v (⟨m, hm'⟩ : Fin n))) : Matrix (Fin n) (Fin n) R) = 1 := by
        apply Matrix.ext
        intro k c'
        rw [hS]
        have h0 : rowSum (R := R) (⟨m, hm'⟩ : Fin n)
            (v (⟨m, hm'⟩ : Fin n)) k c' = 0 := by
          rw [rowSum_entry]
          by_cases hkr : k < (⟨m, hm'⟩ : Fin n)
          · rw [dite_eq_left hkr]
            by_cases hcc : c' = (⟨m, hm'⟩ : Fin n)
            · subst hcc
              have hv : v (⟨m, hm'⟩ : Fin n) ⟨k, hkr⟩ = 1 := htop ⟨k, hkr⟩
              rw [ite_eq_left rfl, hv, toAdd_one]
            · rw [ite_eq_right hcc]
          · rw [dite_eq_right hkr]
        rw [h0, add_zero]
      have hpre : ((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (v r))).take m).prod) :
          Matrix (Fin n) (Fin n) R) = 1 := by
        rw [hB1, Matrix.mul_one] at h1M
        exact h1M
      by_cases hrm : r.val = m
      · have hr0 : r = (⟨m, hm'⟩ : Fin n) := Fin.ext_iff.mpr hrm
        subst hr0
        exact htop i
      · have hrlt : r.val < m := by omega
        exact ih hmle hpre r hrlt i
  have htakeN : ((((List.ofFn (fun r : Fin n =>
      rowSweep (R := R) r (v r))).take n).prod) :
      Matrix (Fin n) (Fin n) R) = 1 := by
    have htn : (List.ofFn (fun r : Fin n =>
        rowSweep (R := R) r (v r))).take n =
        List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r)) := by
      have h2 := List.take_length (l := (List.ofFn (fun r : Fin n =>
        rowSweep (R := R) r (v r))))
      rwa [hlen] at h2
    rw [htn]
    exact hM
  intro r i
  exact hmain n le_rfl htakeN r r.isLt i

/-- Coefficient uniqueness for equal ordered full row-sweep products.

If the ascending ordered products of all row sweeps `rowSweep r (v r)` and
`rowSweep r (w r)` over `r : Fin n` agree, then every sweep coefficient agrees:
`v r i = w r i`. The proof peels the two products from the last row downward:
each peeled middle difference collapses to a single sweep by the homomorphism
equations, and the column of the next index is untouched by earlier factors, so
reading its entries forces each coefficient difference to vanish in turn. The
argument is uniform in `n`, including the degenerate ranks `0` and `1`.

This proves only coefficient uniqueness for equal full ordered products. It makes
no claim about ordered normal forms, `toStableE` injectivity, TWT closure,
kernel generation, Steinberg relations, or Matsumoto's theorem. -/
theorem fullRowSweepProd_eq_imp {n : ℕ} {R : Type*} [Ring R]
    (v w : (r : Fin n) →
      Matrix.GeneralLinearGroup.RowIdx (Fin n) r → Multiplicative R)
    (h :
      (List.ofFn (fun r : Fin n =>
        Matrix.GeneralLinearGroup.rowSweep (R := R) r (v r))).prod =
      (List.ofFn (fun r : Fin n =>
        Matrix.GeneralLinearGroup.rowSweep (R := R) r (w r))).prod) :
    ∀ (r : Fin n) (i : Matrix.GeneralLinearGroup.RowIdx (Fin n) r),
      v r i = w r i := by
  have hS : ∀ (r : Fin n) (g : RowIdx (Fin n) r → Multiplicative R)
      (p q : Fin n),
      ((rowSweep (R := R) r g) : Matrix (Fin n) (Fin n) R) p q =
        (1 : Matrix (Fin n) (Fin n) R) p q + rowSum (R := R) r g p q := by
    intro r g p q
    have hcoe := coe_rowSweep (R := R) (r := r) (v := g)
    calc ((rowSweep (R := R) r g) : Matrix (Fin n) (Fin n) R) p q
        = ((1 + rowSum (R := R) r g : Matrix (Fin n) (Fin n) R)) p q := by
          rw [hcoe]
      _ = _ := Matrix.add_apply _ _ _ _
  have htake : ∀ (f : (r : Fin n) → RowIdx (Fin n) r → Multiplicative R)
      (m : ℕ) (hm : m < n),
      ((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (f r))).take
        (m + 1)).prod : GL (Fin n) R) =
        ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (f r))).take m).prod *
          rowSweep (R := R) (⟨m, hm⟩ : Fin n) (f (⟨m, hm⟩ : Fin n))) := by
    intro f m hm
    have hmem : m <
        (List.ofFn (fun r : Fin n => rowSweep (R := R) r (f r))).length := by
      rw [List.length_ofFn]
      exact hm
    rw [List.prod_take_succ _ m hmem]
    congr 1
    simp only [List.getElem_ofFn]
  have hcol : ∀ (f : (r : Fin n) → RowIdx (Fin n) r → Multiplicative R)
      (m : ℕ) (_hm : m ≤ n) (c : Fin n), m ≤ c.val → ∀ (i : Fin n),
      ((((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (f r))).take
        m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) i c =
        (1 : Matrix (Fin n) (Fin n) R) i c := by
    intro f m
    induction m with
    | zero =>
      intro _ c _ i
      rw [List.take_zero, List.prod_nil, Units.val_one]
    | succ m ih =>
      intro hm c hc i
      have hm' : m < n := by omega
      have hmle : m ≤ n := by omega
      have hcc : m ≤ c.val := by omega
      have hB : ∀ k : Fin n,
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (f (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) k c =
            (1 : Matrix (Fin n) (Fin n) R) k c := by
        intro k
        have hne : c ≠ (⟨m, hm'⟩ : Fin n) := by
          intro he
          have hve : c.val = m := congrArg Fin.val he
          omega
        rw [hS _ _ _ _, rowSum_entry]
        by_cases hkr : k < (⟨m, hm'⟩ : Fin n)
        · rw [dite_eq_left hkr, ite_eq_right hne, add_zero]
        · rw [dite_eq_right hkr, add_zero]
      rw [htake f m hm', Units.val_mul, Matrix.mul_apply]
      have hsum : (∑ k : Fin n,
          ((((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (f r))).take
            m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) i k *
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (f (⟨m, hm'⟩ : Fin n))) :
            Matrix (Fin n) (Fin n) R) k c) =
          ∑ k : Fin n, ((((((List.ofFn (fun r : Fin n =>
            rowSweep (R := R) r (f r))).take m).prod : GL (Fin n) R))) :
            Matrix (Fin n) (Fin n) R) i k *
            (1 : Matrix (Fin n) (Fin n) R) k c :=
        Finset.sum_congr rfl (fun k _ => by rw [hB k])
      rw [hsum, ← Matrix.mul_apply, Matrix.mul_one]
      exact ih hmle c hcc i
  have hpeel : ∀ (Xw Yv Bw Bv : GL (Fin n) R),
      (Xw * Bw)⁻¹ * (Yv * Bv) = 1 → Xw⁻¹ * Yv = Bw * Bv⁻¹ := by
    intro Xw Yv Bw Bv h1
    have key : Yv * Bv = Xw * Bw := by
      have e : (Xw * Bw) * ((Xw * Bw)⁻¹ * (Yv * Bv)) = Yv * Bv := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [h1, mul_one] at e
      exact e.symm
    calc Xw⁻¹ * Yv = Xw⁻¹ * ((Yv * Bv) * Bv⁻¹) := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = Xw⁻¹ * ((Xw * Bw) * Bv⁻¹) := by rw [key]
      _ = (Xw⁻¹ * (Xw * Bw)) * Bv⁻¹ := by rw [← mul_assoc]
      _ = ((Xw⁻¹ * Xw) * Bw) * Bv⁻¹ := by rw [← mul_assoc]
      _ = Bw * Bv⁻¹ := by rw [inv_mul_cancel, one_mul]
  have hmidcol : ∀ (m : ℕ) (hm : m ≤ n) (c : Fin n), m ≤ c.val →
      ∀ (i : Fin n),
      (((((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r))).take
        m).prod)⁻¹ *
        ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take
          m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) i c =
        (1 : Matrix (Fin n) (Fin n) R) i c := by
    intro m hm c hc i
    have eY : ∀ k : Fin n,
        ((((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take
          m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) k c =
          (1 : Matrix (Fin n) (Fin n) R) k c :=
      fun k => hcol v m hm c hc k
    have eX : ∀ k : Fin n,
        ((((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r))).take
          m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) k c =
          (1 : Matrix (Fin n) (Fin n) R) k c :=
      fun k => hcol w m hm c hc k
    have eXinv : (((((((List.ofFn (fun r : Fin n =>
        rowSweep (R := R) r (w r))).take m).prod)⁻¹ : GL (Fin n) R))) :
        Matrix (Fin n) (Fin n) R) i c =
        (1 : Matrix (Fin n) (Fin n) R) i c := by
      have e1 : (((((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (w r))).take m).prod)⁻¹ *
          ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r))).take
            m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) i c =
          (1 : Matrix (Fin n) (Fin n) R) i c := by
        rw [inv_mul_cancel, Units.val_one]
      have e2 : (((((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (w r))).take m).prod)⁻¹ *
          ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r))).take
            m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) i c =
          (((((((List.ofFn (fun r : Fin n =>
            rowSweep (R := R) r (w r))).take m).prod)⁻¹ : GL (Fin n) R))) :
            Matrix (Fin n) (Fin n) R) i c := by
        rw [Units.val_mul, Matrix.mul_apply]
        have hsum : (∑ k : Fin n,
            (((((((List.ofFn (fun r : Fin n =>
              rowSweep (R := R) r (w r))).take m).prod)⁻¹ : GL (Fin n) R))) :
              Matrix (Fin n) (Fin n) R) i k *
            ((((((List.ofFn (fun r : Fin n =>
              rowSweep (R := R) r (w r))).take m).prod : GL (Fin n) R))) :
              Matrix (Fin n) (Fin n) R) k c) =
            ∑ k : Fin n, (((((((List.ofFn (fun r : Fin n =>
              rowSweep (R := R) r (w r))).take m).prod)⁻¹ : GL (Fin n) R))) :
              Matrix (Fin n) (Fin n) R) i k *
              (1 : Matrix (Fin n) (Fin n) R) k c :=
          Finset.sum_congr rfl (fun k _ => by rw [eX k])
        rw [hsum, ← Matrix.mul_apply, Matrix.mul_one]
      rw [← e2]
      exact e1
    rw [Units.val_mul, Matrix.mul_apply]
    have hsum : (∑ k : Fin n,
        (((((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (w r))).take m).prod)⁻¹ : GL (Fin n) R))) :
          Matrix (Fin n) (Fin n) R) i k *
        ((((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (v r))).take m).prod : GL (Fin n) R))) :
          Matrix (Fin n) (Fin n) R) k c) =
        ∑ k : Fin n, (((((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (w r))).take m).prod)⁻¹ : GL (Fin n) R))) :
          Matrix (Fin n) (Fin n) R) i k *
          (1 : Matrix (Fin n) (Fin n) R) k c :=
      Finset.sum_congr rfl (fun k _ => by rw [eY k])
    rw [hsum, ← Matrix.mul_apply, Matrix.mul_one]
    exact eXinv
  have hmain : ∀ (m : ℕ) (hm : m ≤ n),
      (((((((List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r))).take
        m).prod)⁻¹ *
        ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take
          m).prod : GL (Fin n) R)))) = 1 →
      ∀ (r : Fin n), r.val < m → ∀ (i : RowIdx (Fin n) r), v r i = w r i := by
    intro m
    induction m with
    | zero =>
      intro _ _ r hr _
      omega
    | succ m ih =>
      intro hm h1 r hr i
      have hm' : m < n := by omega
      have hmle : m ≤ n := by omega
      rw [htake w m hm', htake v m hm'] at h1
      have hM := hpeel _ _ _ _ h1
      have hfun : (w (⟨m, hm'⟩ : Fin n) * (v (⟨m, hm'⟩ : Fin n))⁻¹) =
          (fun i => w (⟨m, hm'⟩ : Fin n) i *
            (v (⟨m, hm'⟩ : Fin n) i)⁻¹) := by
        funext i
        rw [Pi.mul_apply, Pi.inv_apply]
      have hhom : rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
          (fun i => w (⟨m, hm'⟩ : Fin n) i *
            (v (⟨m, hm'⟩ : Fin n) i)⁻¹) =
          rowSweep (R := R) (⟨m, hm'⟩ : Fin n) (w (⟨m, hm'⟩ : Fin n)) *
            (rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
              (v (⟨m, hm'⟩ : Fin n)))⁻¹ := by
        rw [← hfun, map_mul, map_inv]
      rw [← hhom] at hM
      have hMeq : (((((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (w r))).take m).prod)⁻¹ *
          ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take
            m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) =
          ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
            (fun i => w (⟨m, hm'⟩ : Fin n) i *
              (v (⟨m, hm'⟩ : Fin n) i)⁻¹)) :
            Matrix (Fin n) (Fin n) R) := by
        rw [hM]
      have hread : ∀ (j : Fin n) (hj : j < (⟨m, hm'⟩ : Fin n)),
          (((fun i => w (⟨m, hm'⟩ : Fin n) i *
            (v (⟨m, hm'⟩ : Fin n) i)⁻¹) ⟨j, hj⟩).toAdd : R) = 0 := by
        intro j hj
        have eM : (((((((List.ofFn (fun r : Fin n =>
            rowSweep (R := R) r (w r))).take m).prod)⁻¹ *
            ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take
              m).prod : GL (Fin n) R))) : Matrix (Fin n) (Fin n) R) j
            (⟨m, hm'⟩ : Fin n) =
            (1 : Matrix (Fin n) (Fin n) R) j (⟨m, hm'⟩ : Fin n) :=
          hmidcol m hmle (⟨m, hm'⟩ : Fin n) le_rfl j
        have eF : ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
            (fun i => w (⟨m, hm'⟩ : Fin n) i *
              (v (⟨m, hm'⟩ : Fin n) i)⁻¹)) :
            Matrix (Fin n) (Fin n) R) j (⟨m, hm'⟩ : Fin n) =
            (1 : Matrix (Fin n) (Fin n) R) j (⟨m, hm'⟩ : Fin n) +
              rowSum (R := R) (⟨m, hm'⟩ : Fin n)
                (fun i => w (⟨m, hm'⟩ : Fin n) i *
                  (v (⟨m, hm'⟩ : Fin n) i)⁻¹) j (⟨m, hm'⟩ : Fin n) :=
          hS _ _ _ _
        rw [hMeq] at eM
        rw [eF] at eM
        have eM' : (1 : Matrix (Fin n) (Fin n) R) j (⟨m, hm'⟩ : Fin n) +
            rowSum (R := R) (⟨m, hm'⟩ : Fin n)
              (fun i => w (⟨m, hm'⟩ : Fin n) i *
                (v (⟨m, hm'⟩ : Fin n) i)⁻¹) j (⟨m, hm'⟩ : Fin n) =
            (1 : Matrix (Fin n) (Fin n) R) j (⟨m, hm'⟩ : Fin n) + 0 := by
          rw [add_zero]
          exact eM
        have e0 : rowSum (R := R) (⟨m, hm'⟩ : Fin n)
            (fun i => w (⟨m, hm'⟩ : Fin n) i *
              (v (⟨m, hm'⟩ : Fin n) i)⁻¹) j (⟨m, hm'⟩ : Fin n) = 0 :=
          add_left_cancel_iff.mp eM'
        rw [rowSum_entry] at e0
        rw [dite_eq_left hj, ite_eq_left rfl] at e0
        exact e0
      have htop : ∀ j : RowIdx (Fin n) (⟨m, hm'⟩ : Fin n),
          (fun i => w (⟨m, hm'⟩ : Fin n) i *
            (v (⟨m, hm'⟩ : Fin n) i)⁻¹) j = 1 := by
        intro j
        have h0 := hread j.val j.prop
        have hjeq : (⟨j.val, j.prop⟩ :
            RowIdx (Fin n) (⟨m, hm'⟩ : Fin n)) = j := Subtype.ext rfl
        rw [hjeq] at h0
        have h1eq : Multiplicative.ofAdd ((((fun i =>
            w (⟨m, hm'⟩ : Fin n) i *
              (v (⟨m, hm'⟩ : Fin n) i)⁻¹) j).toAdd) : R) = 1 := by
          rw [h0]
          exact ofAdd_zero
        calc (fun i => w (⟨m, hm'⟩ : Fin n) i *
              (v (⟨m, hm'⟩ : Fin n) i)⁻¹) j =
            Multiplicative.ofAdd ((((fun i => w (⟨m, hm'⟩ : Fin n) i *
              (v (⟨m, hm'⟩ : Fin n) i)⁻¹) j).toAdd) : R) :=
              (ofAdd_toAdd _).symm
          _ = 1 := h1eq
      have hB1 : ((rowSweep (R := R) (⟨m, hm'⟩ : Fin n)
          (fun i => w (⟨m, hm'⟩ : Fin n) i *
            (v (⟨m, hm'⟩ : Fin n) i)⁻¹)) :
          Matrix (Fin n) (Fin n) R) = 1 := by
        apply Matrix.ext
        intro k c'
        rw [hS _ _ _ _]
        have h0 : rowSum (R := R) (⟨m, hm'⟩ : Fin n)
            (fun i => w (⟨m, hm'⟩ : Fin n) i *
              (v (⟨m, hm'⟩ : Fin n) i)⁻¹) k c' = 0 := by
          rw [rowSum_entry]
          by_cases hkr : k < (⟨m, hm'⟩ : Fin n)
          · rw [dite_eq_left hkr]
            by_cases hcc : c' = (⟨m, hm'⟩ : Fin n)
            · subst hcc
              have hv : w (⟨m, hm'⟩ : Fin n) ⟨k, hkr⟩ *
                  (v (⟨m, hm'⟩ : Fin n) ⟨k, hkr⟩)⁻¹ = 1 := htop ⟨k, hkr⟩
              rw [ite_eq_left rfl, hv, toAdd_one]
            · rw [ite_eq_right hcc]
          · rw [dite_eq_right hkr]
        rw [h0, add_zero]
      have hM1 : (((((((List.ofFn (fun r : Fin n =>
          rowSweep (R := R) r (w r))).take m).prod)⁻¹ *
          ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take
            m).prod : GL (Fin n) R)))) = 1 := by
        apply Units.ext
        rw [hM]
        exact hB1.trans Units.val_one.symm
      by_cases hrm : r.val = m
      · have hr0 : r = (⟨m, hm'⟩ : Fin n) := Fin.ext_iff.mpr hrm
        subst hr0
        have hij : (fun i => w (⟨m, hm'⟩ : Fin n) i *
            (v (⟨m, hm'⟩ : Fin n) i)⁻¹) i = 1 := htop i
        have hdiff : w (⟨m, hm'⟩ : Fin n) i *
            (v (⟨m, hm'⟩ : Fin n) i)⁻¹ = 1 := hij
        have hwv : w (⟨m, hm'⟩ : Fin n) i = v (⟨m, hm'⟩ : Fin n) i := by
          calc w (⟨m, hm'⟩ : Fin n) i
              = w (⟨m, hm'⟩ : Fin n) i *
                ((v (⟨m, hm'⟩ : Fin n) i)⁻¹ *
                  v (⟨m, hm'⟩ : Fin n) i) := by
                  rw [inv_mul_cancel, mul_one]
            _ = (w (⟨m, hm'⟩ : Fin n) i *
                (v (⟨m, hm'⟩ : Fin n) i)⁻¹) *
                v (⟨m, hm'⟩ : Fin n) i := by rw [mul_assoc]
            _ = v (⟨m, hm'⟩ : Fin n) i := by rw [hdiff, one_mul]
        exact hwv.symm
      · have hrlt : r.val < m := by omega
        exact ih hmle hM1 r hrlt i
  have hbase : (((((((List.ofFn (fun r : Fin n =>
      rowSweep (R := R) r (w r))).take n).prod)⁻¹ *
      ((List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take n).prod :
      GL (Fin n) R)))) = 1 := by
    have e1w : (List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r))).take n =
        List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r)) := by
      have h2 := List.take_length
        (l := (List.ofFn (fun r : Fin n => rowSweep (R := R) r (w r))))
      rwa [List.length_ofFn] at h2
    have e1v : (List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))).take n =
        List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r)) := by
      have h2 := List.take_length
        (l := (List.ofFn (fun r : Fin n => rowSweep (R := R) r (v r))))
      rwa [List.length_ofFn] at h2
    rw [e1w, e1v, h]
    exact inv_mul_cancel _
  intro r i
  exact hmain n le_rfl hbase r r.isLt i

end FullRowSweepUniqueness

end Matrix.GeneralLinearGroup
