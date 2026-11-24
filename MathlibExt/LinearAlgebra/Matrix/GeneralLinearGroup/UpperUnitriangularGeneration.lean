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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementarySweep
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootExtraction
public import Mathlib.Data.Finset.Sort

@[expose] public section

open Matrix Finset

namespace Matrix.GeneralLinearGroup

section Generation

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

private def RowTrivial (g : GL ι R) (i : ι) : Prop :=
  ∀ j, (g : Matrix ι ι R) i j = if i = j then 1 else 0

omit [LinearOrder ι] in
private theorem rowTrivial_iff_eq_one (g : GL ι R) :
    (∀ i, RowTrivial g i) ↔ (g : Matrix ι ι R) = 1 := by
  constructor
  · intro h
    ext i j
    simp [h i j, Matrix.one_apply]
  · intro h i j
    rw [h]
    simp [Matrix.one_apply]

private noncomputable def sweepNeg (g : GL ι R) (c : ι) : GL ι R :=
  columnSweep (R := R) c
    (fun j : ColIdx ι c => Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))

private theorem sweepNeg_mem_upperElementary (g : GL ι R) (c : ι) :
    sweepNeg (R := R) g c ∈ upperElementarySubgroup ι R :=
  columnSweep_mem_upperElementary c _

private theorem upperUnitriangular_isUpperTriangular_of_mem
    (g : GL ι R) (hg : g ∈ upperUnitriangularSubgroup ι R) :
    IsUpperTriangular (g : Matrix ι ι R) :=
  hg.1

private theorem upperUnitriangular_diag_one_of_mem
    (g : GL ι R) (hg : g ∈ upperUnitriangularSubgroup ι R) (i : ι) :
    (g : Matrix ι ι R) i i = 1 :=
  hg.2 i

private theorem columnSweep_mul_apply_GL (c : ι)
    (v : ColIdx ι c → Multiplicative R) (M : Matrix ι ι R) (i j : ι) :
    (M * ((columnSweep (R := R) c v : GL ι R) : Matrix ι ι R)) i j =
      if h : c < j then M i j + M i c * (v ⟨j, h⟩).toAdd else M i j := by
  classical
  exact columnSweep_mul_apply (R := R) c v M i j

private theorem cleanStep_rowTrivial (g : GL ι R)
    (hg : g ∈ upperUnitriangularSubgroup ι R) (c : ι) :
    RowTrivial (g * sweepNeg (R := R) g c) c := by
  classical
  intro j
  have hg_diag : (g : Matrix ι ι R) c c = 1 :=
    upperUnitriangular_diag_one_of_mem g hg c
  have hg_tri : IsUpperTriangular (g : Matrix ι ι R) :=
    upperUnitriangular_isUpperTriangular_of_mem g hg
  by_cases hcj : c < j
  · have hc_ne_j : c ≠ j := ne_of_lt hcj
    have h0 :=
      columnSweep_mul_apply_GL (R := R) (c := c)
        (v := fun j : ColIdx ι c =>
          Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
        (M := (g : Matrix ι ι R)) (i := c) (j := j)
    simp only [hcj, dite_true] at h0
    have hv :
        ( (fun j : ColIdx ι c =>
              Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
            ⟨j, hcj⟩).toAdd = -( (g : Matrix ι ι R) c j) := rfl
    rw [hv] at h0
    have h_eq :
        ((g * sweepNeg (R := R) g c : GL ι R) : Matrix ι ι R) c j =
        (g : Matrix ι ι R) c j +
          (g : Matrix ι ι R) c c * (-( (g : Matrix ι ι R) c j)) :=
      h0
    rw [h_eq, hg_diag, one_mul, add_neg_cancel]
    simp [hc_ne_j]
  · by_cases heq : c = j
    · subst heq
      have h0 :=
        columnSweep_mul_apply_GL (R := R) (c := c)
          (v := fun j : ColIdx ι c =>
            Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
          (M := (g : Matrix ι ι R)) (i := c) (j := c)
      simp only [show ¬ c < c from lt_irrefl c, dite_false] at h0
      have h_eq :
          ((g * sweepNeg (R := R) g c : GL ι R) : Matrix ι ι R) c c =
          (g : Matrix ι ι R) c c := h0
      rw [h_eq, hg_diag]
      simp
    · have hjc : j < c := by
        have h_le : j ≤ c := not_lt.mp hcj
        rcases eq_or_lt_of_le h_le with heq2 | hlt
        · exact absurd heq2.symm heq
        · exact hlt
      have h_zero : (g : Matrix ι ι R) c j = 0 := hg_tri hjc
      have h0 :=
        columnSweep_mul_apply_GL (R := R) (c := c)
          (v := fun j : ColIdx ι c =>
            Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
          (M := (g : Matrix ι ι R)) (i := c) (j := j)
      simp only [hcj, dite_false] at h0
      have h_eq :
          ((g * sweepNeg (R := R) g c : GL ι R) : Matrix ι ι R) c j =
          (g : Matrix ι ι R) c j := h0
      rw [h_eq, h_zero]
      simp [heq]

private theorem cleanStep_preserves_rowTrivial (g : GL ι R)
    (c i : ι) (hi : RowTrivial g i) (hne : i ≠ c) :
    RowTrivial (g * sweepNeg (R := R) g c) i := by
  classical
  intro j
  have hi_c : (g : Matrix ι ι R) i c = 0 := by
    have h := hi c
    simp only [hne] at h
    exact h
  by_cases hcj : c < j
  · have h0 :=
      columnSweep_mul_apply_GL (R := R) (c := c)
        (v := fun j : ColIdx ι c =>
          Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
        (M := (g : Matrix ι ι R)) (i := i) (j := j)
    simp only [hcj, dite_true] at h0
    have hv :
        ( (fun j : ColIdx ι c =>
              Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
            ⟨j, hcj⟩).toAdd = -( (g : Matrix ι ι R) c j) := rfl
    rw [hv] at h0
    have h_eq :
        ((g * sweepNeg (R := R) g c : GL ι R) : Matrix ι ι R) i j =
        (g : Matrix ι ι R) i j +
          (g : Matrix ι ι R) i c * (-( (g : Matrix ι ι R) c j)) :=
      h0
    rw [h_eq, hi_c, zero_mul, add_zero]
    exact hi j
  · have h0 :=
      columnSweep_mul_apply_GL (R := R) (c := c)
        (v := fun j : ColIdx ι c =>
          Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
        (M := (g : Matrix ι ι R)) (i := i) (j := j)
    simp only [hcj, dite_false] at h0
    have h_eq :
        ((g * sweepNeg (R := R) g c : GL ι R) : Matrix ι ι R) i j =
        (g : Matrix ι ι R) i j := h0
    rw [h_eq]
    exact hi j

private theorem cleanStep_mem_upperUnitriangular (g : GL ι R)
    (hg : g ∈ upperUnitriangularSubgroup ι R) (c : ι) :
    g * sweepNeg (R := R) g c ∈ upperUnitriangularSubgroup ι R := by
  have hs : sweepNeg (R := R) g c ∈ upperElementarySubgroup ι R :=
    sweepNeg_mem_upperElementary g c
  have hs_unit :
      sweepNeg (R := R) g c ∈ upperUnitriangularSubgroup ι R :=
    upperElementarySubgroup_le_upperUnitriangularSubgroup_commRing hs
  exact (upperUnitriangularSubgroup ι R).mul_mem hg hs_unit

private theorem aux_mem_upperElementary_of_complement_trivial
    (S : Finset ι) :
    ∀ (g : GL ι R),
      g ∈ upperUnitriangularSubgroup ι R →
      (∀ i, i ∉ S → RowTrivial g i) →
      g ∈ upperElementarySubgroup ι R := by
  classical
  induction S using Finset.induction with
  | empty =>
    intro g hg h_triv
    have h_all : ∀ i, RowTrivial g i := by
      intro i
      exact h_triv i (by simp)
    have h_eq : (g : Matrix ι ι R) = 1 := (rowTrivial_iff_eq_one g).mp h_all
    have h_one : g = 1 := by
      apply Units.ext
      exact h_eq
    rw [h_one]
    exact (upperElementarySubgroup ι R).one_mem
  | @insert a S ha ih =>
    intro g hg h_triv
    let g' : GL ι R := g * sweepNeg (R := R) g a
    have hg' : g' ∈ upperUnitriangularSubgroup ι R :=
      cleanStep_mem_upperUnitriangular g hg a
    have h_triv_a : RowTrivial g' a :=
      cleanStep_rowTrivial g hg a
    have h_triv_rest : ∀ i, i ∉ S → RowTrivial g' i := by
      intro i hi
      by_cases hia : i = a
      · rw [hia]
        exact h_triv_a
      · have hi_mem : i ∉ insert a S := by
          simp [Finset.mem_insert, hia, hi]
        have h_row : RowTrivial g i := h_triv i hi_mem
        exact cleanStep_preserves_rowTrivial g a i h_row hia
    have hg'_mem : g' ∈ upperElementarySubgroup ι R :=
      ih g' hg' h_triv_rest
    have hs_mem : sweepNeg (R := R) g a ∈ upperElementarySubgroup ι R :=
      sweepNeg_mem_upperElementary g a
    have h_sweep_inv :
        (sweepNeg (R := R) g a)⁻¹ ∈ upperElementarySubgroup ι R :=
      (upperElementarySubgroup ι R).inv_mem hs_mem
    have h_eq : g = g' * (sweepNeg (R := R) g a)⁻¹ := by
      calc g = g * 1 := by simp
        _ = g * (sweepNeg (R := R) g a * (sweepNeg (R := R) g a)⁻¹) := by
            rw [mul_inv_cancel]
        _ = g * sweepNeg (R := R) g a * (sweepNeg (R := R) g a)⁻¹ := by
            rw [mul_assoc]
        _ = g' * (sweepNeg (R := R) g a)⁻¹ := rfl
    rw [h_eq]
    exact (upperElementarySubgroup ι R).mul_mem hg'_mem h_sweep_inv

theorem upperUnitriangularSubgroup_le_upperElementarySubgroup :
    upperUnitriangularSubgroup (ι := ι) (R := R) ≤
      upperElementarySubgroup ι R := by
  intro g hg
  have h_triv : ∀ i, i ∉ (Finset.univ : Finset ι) → RowTrivial g i := by
    intro i hi
    simp at hi
  exact aux_mem_upperElementary_of_complement_trivial (R := R) Finset.univ g hg h_triv

theorem upperElementarySubgroup_eq_upperUnitriangularSubgroup :
    upperElementarySubgroup (ι := ι) (R := R) =
      upperUnitriangularSubgroup ι R := by
  apply le_antisymm
  · exact upperElementarySubgroup_le_upperUnitriangularSubgroup_commRing
  · exact upperUnitriangularSubgroup_le_upperElementarySubgroup

theorem upperUnitriangular_induction
    (P : GL ι R → Prop) (h_one : P 1)
    (h_elem : ∀ i j (hij : i < j) (a : R), P (elementary i j (ne_of_lt hij) a))
    (h_mul : ∀ a b, P a → P b → P (a * b))
    (h_inv : ∀ a, P a → P a⁻¹)
    (g : GL ι R) (hg : g ∈ upperUnitriangularSubgroup ι R) : P g := by
  have hg_elem : g ∈ upperElementarySubgroup ι R :=
    upperUnitriangularSubgroup_le_upperElementarySubgroup hg
  exact Subgroup.closure_induction (p := fun g _ => P g)
    (fun x hx => by obtain ⟨i, j, hij, a, rfl⟩ := hx; exact h_elem i j hij a)
    h_one
    (fun x y _ _ hx hy => h_mul x y hx hy)
    (fun x _ hx => h_inv x hx)
    hg_elem

private noncomputable def sweepParam (g : GL ι R) (c : ι) :
    ColIdx ι c → Multiplicative R :=
  fun j => Multiplicative.ofAdd ((g : Matrix ι ι R) c j.val)

private noncomputable def sweepPos (g : GL ι R) (c : ι) :
    upperElementarySubgroup ι R :=
  UpperElementary.columnSweep (R := R) c (sweepParam g c)

private theorem sweepNeg_eq_inv_sweepPos (g : GL ι R) (c : ι) :
    sweepNeg (R := R) g c = (sweepPos (R := R) g c : GL ι R)⁻¹ := by
  unfold sweepNeg sweepPos sweepParam
  simp only [UpperElementary.coe_columnSweep]
  have h1 :
      (fun j : ColIdx ι c =>
        Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val))) =
      (fun j : ColIdx ι c => (Multiplicative.ofAdd ((g : Matrix ι ι R) c j.val))⁻¹) := by
    ext j
    rfl
  calc columnSweep (R := R) c
        (fun j : ColIdx ι c => Multiplicative.ofAdd (-( (g : Matrix ι ι R) c j.val)))
      = columnSweep (R := R) c
          (fun j : ColIdx ι c => (Multiplicative.ofAdd ((g : Matrix ι ι R) c j.val))⁻¹) := by
        rw [h1]
    _ = (columnSweep (R := R) c
          (fun j : ColIdx ι c => Multiplicative.ofAdd ((g : Matrix ι ι R) c j.val)))⁻¹ :=
      MonoidHom.map_inv _ _

theorem upperUnitriangular_mem_closure_columnSweep
    (g : GL ι R) (hg : g ∈ upperUnitriangularSubgroup ι R) :
    g ∈ Subgroup.closure
      {x : GL ι R | ∃ c : ι, ∃ v : ColIdx ι c → Multiplicative R,
        x = (UpperElementary.columnSweep (R := R) c v : GL ι R)} := by
  classical
  let S : Set (GL ι R) :=
    {x : GL ι R | ∃ c : ι, ∃ v : ColIdx ι c → Multiplicative R,
      x = (UpperElementary.columnSweep (R := R) c v : GL ι R)}
  let P : GL ι R → Prop := fun g => g ∈ Subgroup.closure S
  have h_one : P 1 := Subgroup.one_mem _
  have h_elem : ∀ i j (hij : i < j) (a : R), P (elementary i j (ne_of_lt hij) a) := by
    intro i j hij a
    have h_mem : (elementary i j (ne_of_lt hij) a : GL ι R) ∈ S := by
      refine ⟨i, Pi.mulSingle ⟨j, hij⟩ (Multiplicative.ofAdd a), ?_⟩
      have h :
          UpperElementary.columnSweep (R := R) i
          (Pi.mulSingle ⟨j, hij⟩ (Multiplicative.ofAdd a)) =
          UpperElementary.elementary i j hij a := by
        rw [UpperElementary.columnSweep_mulSingle]
      rw [h]
      rfl
    exact Subgroup.subset_closure h_mem
  have h_mul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb =>
    Subgroup.mul_mem _ ha hb
  have h_inv : ∀ a, P a → P a⁻¹ := fun a ha =>
    Subgroup.inv_mem _ ha
  exact upperUnitriangular_induction P h_one h_elem h_mul h_inv g hg

end Generation

end Matrix.GeneralLinearGroup
