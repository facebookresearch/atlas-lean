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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementaryPivot
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Canonical pivots on finite ordered matrix indices

For an invertible matrix over a ring and a finite index set, `columnSupport`
records the nonzero rows of a chosen column. Over a nontrivial ring, this
support is nonempty; a linear order then supplies its greatest element,
`pivotRow`. A nonempty finite linear order also has a least column,
`leastIndex`, which is preserved by order isomorphisms.

Over a division ring, clearing about `pivotRow` isolates the chosen column.
When that column is least, it also isolates the pivot row. Clearing commutes
with division-ring homomorphisms. Column support commutes with injective
ring homomorphisms, as does pivot selection between nontrivial rings.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix Finset Function

universe u v w

section ColumnSupport

variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable {R : Type v} [Ring R]

/-- For an invertible matrix over a ring indexed by a finite set, the
finite set of rows with a nonzero entry in column `c`. Coefficient equality
is decided classically. -/
noncomputable def columnSupport (g : GL ι R) (c : ι) : Finset ι :=
  haveI : DecidablePred (fun i : ι => (g : Matrix ι ι R) i c ≠ 0) :=
    Classical.decPred _
  Finset.univ.filter fun i => (g : Matrix ι ι R) i c ≠ 0

@[simp]
theorem mem_columnSupport (g : GL ι R) (c i : ι) :
    i ∈ columnSupport (g : GL ι R) (c : ι) ↔ (g : Matrix ι ι R) i c ≠ 0 := by
  classical
  simp [columnSupport]

theorem columnSupport_nonempty [Nontrivial R] (g : GL ι R) (c : ι) :
    (columnSupport g c).Nonempty := by
  classical
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  have h_all_zero : ∀ i : ι, (g : Matrix ι ι R) i c = 0 := by
    intro i
    by_contra h_ne
    have : i ∈ columnSupport g c := by rwa [mem_columnSupport]
    rw [h_empty] at this
    exact Finset.notMem_empty i this
  let N := ((g⁻¹ : GL ι R) : Matrix ι ι R)
  have h_mul : N * (g : Matrix ι ι R) = 1 := by
    calc N * (g : Matrix ι ι R) = ((g⁻¹ * g : GL ι R) : Matrix ι ι R) := rfl
      _ = ((1 : GL ι R) : Matrix ι ι R) := by rw [inv_mul_cancel]
      _ = 1 := rfl
  have h_cc : (N * (g : Matrix ι ι R)) c c = (1 : Matrix ι ι R) c c := by
    rw [h_mul]
  have h_one : (1 : Matrix ι ι R) c c = (1 : R) := by simp [Matrix.one_apply_eq]
  have h_zero : (N * (g : Matrix ι ι R)) c c = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    simp [h_all_zero k]
  rw [h_zero, h_one] at h_cc
  exact one_ne_zero h_cc.symm

end ColumnSupport

section PivotRow

variable {ι : Type u} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type v} [Ring R] [Nontrivial R]

/-- For an invertible matrix over a nontrivial ring indexed by a finite
linear order, the greatest row with a nonzero entry in the chosen column `c`. -/
noncomputable def pivotRow (g : GL ι R) (c : ι) : ι :=
  (columnSupport g c).max' (columnSupport_nonempty g c)

theorem pivotRow_mem_columnSupport (g : GL ι R) (c : ι) :
    pivotRow (R := R) g c ∈ columnSupport g c :=
  Finset.max'_mem _ _

theorem pivotRow_ne_zero (g : GL ι R) (c : ι) :
    (g : Matrix ι ι R) (pivotRow g c) c ≠ 0 := by
  rw [← mem_columnSupport]
  exact pivotRow_mem_columnSupport g c

theorem pivotRow_le (g : GL ι R) (c : ι) (i : ι)
    (hi : i ∈ columnSupport g c) : i ≤ pivotRow (R := R) g c :=
  Finset.le_max' _ _ hi

theorem pivotRow_isGreatest (g : GL ι R) (c : ι) :
    IsGreatest {i | (g : Matrix ι ι R) i c ≠ 0} (pivotRow g c) := by
  constructor
  · exact pivotRow_ne_zero g c
  · intro j hj
    exact pivotRow_le g c j (by rwa [mem_columnSupport])

theorem pivotRow_gt_eq_zero (g : GL ι R) (c : ι) (i : ι)
    (hi : pivotRow (R := R) g c < i) : (g : Matrix ι ι R) i c = 0 := by
  by_contra h_ne
  exact not_le_of_gt hi (pivotRow_le g c i (by rwa [mem_columnSupport]))

end PivotRow

section Natural

variable {ι : Type u} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type v} [Ring R] {S : Type w} [Ring S]

private theorem map_ne_zero_iff_of_injective
    (f : R →+* S) (hf : Injective f) (x : R) : f x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hfx hx
    rw [hx, f.map_zero] at hfx
    exact hfx rfl
  · intro hx h0
    exact hx (hf (by rw [h0, f.map_zero]))

omit [LinearOrder ι] in
theorem columnSupport_mapRingHom
    (f : R →+* S) (hf : Injective f) (g : GL ι R) (c : ι) :
    columnSupport (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c =
      columnSupport g c := by
  classical
  ext i
  simp only [mem_columnSupport, Matrix.GeneralLinearGroup.coe_mapRingHom,
    Matrix.map_apply]
  exact map_ne_zero_iff_of_injective f hf _

private theorem isGreatest_unique
    {α : Type*} [PartialOrder α] {s : Set α} {a b : α}
    (ha : IsGreatest s a) (hb : IsGreatest s b) : a = b :=
  le_antisymm (hb.2 ha.1) (ha.2 hb.1)

theorem pivotRow_mapRingHom [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hf : Injective f) (g : GL ι R) (c : ι) :
    pivotRow (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c =
      pivotRow g c := by
  classical
  have h_eq_set :
      {i | (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g : Matrix ι ι S) i c ≠ 0} =
        {i | (g : Matrix ι ι R) i c ≠ 0} := by
    ext i
    simp only [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply]
    exact map_ne_zero_iff_of_injective f hf _
  have hg : IsGreatest {i | (g : Matrix ι ι R) i c ≠ 0} (pivotRow g c) :=
    pivotRow_isGreatest g c
  have hf_greatest : IsGreatest
      {i | (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g : Matrix ι ι S) i c ≠ 0}
      (pivotRow (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c) :=
    pivotRow_isGreatest _ c
  have hf' : IsGreatest {i | (g : Matrix ι ι R) i c ≠ 0}
      (pivotRow (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c) := by
    rwa [← h_eq_set]
  exact isGreatest_unique hf' hg

end Natural

section LeastIndex

variable {ι : Type u} [DecidableEq ι] [Fintype ι] [LinearOrder ι] [Nonempty ι]

/-- The least element of a nonempty finite linearly ordered index set. -/
noncomputable def leastIndex : ι :=
  Finset.univ.min' Finset.univ_nonempty

omit [DecidableEq ι] in
theorem leastIndex_le (j : ι) : (leastIndex (ι := ι)) ≤ j :=
  Finset.min'_le _ _ (Finset.mem_univ j)

omit [DecidableEq ι] in
theorem leastIndex_isLeast :
    IsLeast (Set.univ : Set ι) (leastIndex (ι := ι)) := by
  constructor
  · exact Set.mem_univ _
  · intro y _
    exact leastIndex_le (ι := ι) y

end LeastIndex

section LeastIndexIso

variable {ι : Type u} [DecidableEq ι] [Fintype ι] [LinearOrder ι] [Nonempty ι]
variable {κ : Type w} [DecidableEq κ] [Fintype κ] [LinearOrder κ] [Nonempty κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem leastIndex_map_orderIso (e : ι ≃o κ) :
    e (leastIndex (ι := ι)) = leastIndex (ι := κ) := by
  have h_img : IsLeast (Set.univ : Set κ) (e (leastIndex (ι := ι))) := by
    constructor
    · exact Set.mem_univ _
    · intro k _
      obtain ⟨j, rfl⟩ := e.surjective k
      exact e.monotone (leastIndex_le (ι := ι) j)
  have h_tgt : IsLeast (Set.univ : Set κ) (leastIndex (ι := κ)) :=
    leastIndex_isLeast (ι := κ)
  exact le_antisymm (h_img.2 (Set.mem_univ _)) (h_tgt.2 (Set.mem_univ _))

end LeastIndexIso

section DivisionRingConn

variable {ι : Type u} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {K : Type v} [DivisionRing K]

private theorem divRingHom_map_ne_zero
    {L : Type w} [DivisionRing L] (f : K →+* L) {a : K} (ha : a ≠ 0) :
    f a ≠ 0 := by
  intro h0
  have h1 : f (a * a⁻¹) = f 1 := by rw [mul_inv_cancel₀ ha]
  have hmul : f a * f a⁻¹ = 1 := by
    calc f a * f a⁻¹ = f (a * a⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [h1]
      _ = 1 := f.map_one
  rw [h0, zero_mul] at hmul
  exact one_ne_zero hmul.symm

private theorem divRingHom_injective
    {L : Type w} [DivisionRing L] (f : K →+* L) : Injective f := by
  intro a b hab
  by_contra hne
  have h_sub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h_map : f (a - b) = 0 := by rw [f.map_sub, hab, sub_self]
  exact divRingHom_map_ne_zero f h_sub h_map

private theorem rowClear_congr_same (M : Matrix ι ι K) {r c : ι}
    (hp1 hp2 : M r c ≠ 0) :
    rowClear (K := K) M r c hp1 = rowClear (K := K) M r c hp2 := by
  unfold rowClear
  exact congrArg (rowSweep r) (by funext i; rfl)

private theorem columnClear_congr_same (M : Matrix ι ι K) {r c : ι}
    (hp1 hp2 : M r c ≠ 0) :
    columnClear (K := K) M r c hp1 = columnClear (K := K) M r c hp2 := by
  unfold columnClear
  exact congrArg (columnSweep c) (by funext j; rfl)

private theorem pivotCleared_congr_same (M : Matrix ι ι K) {r c : ι}
    (hp1 hp2 : M r c ≠ 0) : pivotCleared M r c hp1 = pivotCleared M r c hp2 := by
  unfold pivotCleared
  rw [rowClear_congr_same M hp1 hp2, columnClear_congr_same M hp1 hp2]

private theorem pivotCleared_congr' (M : Matrix ι ι K) {r1 r2 c : ι}
    (h : r1 = r2) (hp1 : M r1 c ≠ 0) (hp2 : M r2 c ≠ 0) :
    pivotCleared M r1 c hp1 = pivotCleared M r2 c hp2 := by
  cases h
  exact pivotCleared_congr_same M hp1 hp2

/-- For an invertible matrix over a division ring indexed by a finite
linear order, clear column `c` about its greatest nonzero row. The column
is isolated; the pivot row is also isolated when `c` is least. -/
noncomputable def canonicalPivotClearedAt (g : GL ι K) (c : ι) :
    Matrix ι ι K :=
  pivotCleared (↑g : Matrix ι ι K) (pivotRow g c) c (pivotRow_ne_zero g c)

theorem canonicalPivotClearedAt_col_isolated
    (g : GL ι K) (c : ι) (i : ι) :
    canonicalPivotClearedAt (K := K) g c i c =
      if i = pivotRow g c then (↑g : Matrix ι ι K) (pivotRow g c) c else 0 := by
  unfold canonicalPivotClearedAt
  exact pivotCleared_col_isolated (pivotRow_ne_zero g c) (pivotRow_isGreatest g c) i

theorem canonicalPivotClearedAt_row_isolated_of_isLeast
    (g : GL ι K) (c : ι) (hc : IsLeast (Set.univ : Set ι) c) (j : ι) :
    canonicalPivotClearedAt g c (pivotRow g c) j =
      if j = c then (↑g : Matrix ι ι K) (pivotRow g c) c else 0 := by
  unfold canonicalPivotClearedAt
  exact pivotCleared_row_isolated (pivotRow_ne_zero g c) hc j

theorem canonicalPivotClearedAt_pivot (g : GL ι K) (c : ι) :
    canonicalPivotClearedAt g c (pivotRow g c) c =
      (↑g : Matrix ι ι K) (pivotRow g c) c := by
  unfold canonicalPivotClearedAt
  exact pivotCleared_pivot _ _ _ _

variable [Nonempty ι] in
/-- For an invertible matrix over a division ring indexed by a nonempty
finite linear order, clear at the least column, isolating that column and
its greatest nonzero row. -/
noncomputable def canonicalPivotCleared (g : GL ι K) : Matrix ι ι K :=
  canonicalPivotClearedAt (K := K) g (leastIndex (ι := ι))

variable [Nonempty ι] in
theorem canonicalPivotCleared_col_isolated (g : GL ι K) (i : ι) :
    canonicalPivotCleared (K := K) g i (leastIndex (ι := ι)) =
      if i = pivotRow g (leastIndex (ι := ι)) then
        (↑g : Matrix ι ι K) (pivotRow g (leastIndex (ι := ι)))
          (leastIndex (ι := ι))
      else 0 := by
  unfold canonicalPivotCleared
  exact canonicalPivotClearedAt_col_isolated g (leastIndex (ι := ι)) i

variable [Nonempty ι] in
theorem canonicalPivotCleared_row_isolated (g : GL ι K) (j : ι) :
    canonicalPivotCleared (K := K) g (pivotRow g (leastIndex (ι := ι))) j =
      if j = leastIndex (ι := ι) then
        (↑g : Matrix ι ι K) (pivotRow g (leastIndex (ι := ι)))
          (leastIndex (ι := ι))
      else 0 := by
  unfold canonicalPivotCleared
  exact canonicalPivotClearedAt_row_isolated_of_isLeast g _
    (leastIndex_isLeast (ι := ι)) j

variable [Nonempty ι] in
theorem canonicalPivotCleared_pivot (g : GL ι K) :
    canonicalPivotCleared (K := K) g (pivotRow g (leastIndex (ι := ι)))
        (leastIndex (ι := ι)) =
      (↑g : Matrix ι ι K) (pivotRow g (leastIndex (ι := ι)))
        (leastIndex (ι := ι)) := by
  unfold canonicalPivotCleared
  exact canonicalPivotClearedAt_pivot g (leastIndex (ι := ι))

section NatDiv

variable {L : Type w} [DivisionRing L]

theorem canonicalPivotClearedAt_map
    (f : K →+* L) (g : GL ι K) (c : ι) :
    (canonicalPivotClearedAt g c).map (⇑f) =
      canonicalPivotClearedAt (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c := by
  have hf : Injective f := divRingHom_injective f
  have h_r_eq :
      pivotRow (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c =
        pivotRow g c := by
    have : Nontrivial K := inferInstance
    have : Nontrivial L := inferInstance
    exact pivotRow_mapRingHom f hf g c
  have hp : (g : Matrix ι ι K) (pivotRow g c) c ≠ 0 := pivotRow_ne_zero g c
  have hMp : ((g : Matrix ι ι K).map ⇑f) (pivotRow g c) c ≠ 0 := by
    rw [Matrix.map_apply]
    exact divRingHom_map_ne_zero f hp
  calc (canonicalPivotClearedAt g c).map ⇑f
      = (pivotCleared (↑g : Matrix ι ι K) (pivotRow g c) c hp).map ⇑f := rfl
    _ = pivotCleared ((↑g : Matrix ι ι K).map ⇑f) (pivotRow g c) c hMp :=
        pivotCleared_map f (↑g : Matrix ι ι K) (pivotRow g c) c hp hMp
    _ = canonicalPivotClearedAt (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c := by
        calc _ = pivotCleared ((↑g : Matrix ι ι K).map ⇑f)
              (pivotRow (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c) c _ :=
            pivotCleared_congr' _ h_r_eq.symm hMp _
          _ = _ := rfl

variable [Nonempty ι] in
theorem canonicalPivotCleared_map (f : K →+* L) (g : GL ι K) :
    (canonicalPivotCleared (K := K) g).map (⇑f) =
      canonicalPivotCleared (K := L)
        (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) := by
  unfold canonicalPivotCleared
  rw [canonicalPivotClearedAt_map f g (leastIndex (ι := ι))]

end NatDiv

end DivisionRingConn

end Matrix.GeneralLinearGroup
