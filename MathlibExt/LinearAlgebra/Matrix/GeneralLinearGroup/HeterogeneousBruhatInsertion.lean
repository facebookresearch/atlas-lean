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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.GeneralLinearEquiv
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.HeterogeneousIsolatedEntry
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementaryEmbedding
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.IsolatedCoordinate
public import Mathlib.Data.Fintype.BigOperators

/-!
# Insertion of an isolated monomial coordinate

Extends an equivalence and its monomial weights across a deleted coordinate. The
resulting matrix insertion is compatible with composition, scalar maps and
extension by the identity on upper-elementary matrices.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {ι : Type*} [LinearOrder ι]

/-- Canonical order embedding `DeletedIndex ι c ↪o ι` via `Subtype.val`. -/
def deletedOrderEmbedding (c : ι) : DeletedIndex ι c ↪o ι where
  toEmbedding :=
    { toFun := Subtype.val
      inj' := Subtype.val_injective }
  map_rel_iff' := by
    intro a b
    rfl

@[simp]
theorem deletedOrderEmbedding_coe (c : ι) (x : DeletedIndex ι c) :
    (deletedOrderEmbedding c x : ι) = x.val :=
  rfl

section MemRange

variable {ι : Type*} [LinearOrder ι]

/-- Characterisation of the range of `deletedOrderEmbedding`. -/
theorem mem_range_deletedOrderEmbedding {c : ι} {k : ι} :
    k ∈ Set.range (deletedOrderEmbedding (ι := ι) c) ↔ k ≠ c := by
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    exact hv
  · intro hk
    exact ⟨⟨k, hk⟩, rfl⟩

/-- The deleted point is not in the range of the embedding. -/
theorem not_mem_range_deletedOrderEmbedding_self (c : ι) :
    c ∉ Set.range (deletedOrderEmbedding (ι := ι) c) := by
  rw [mem_range_deletedOrderEmbedding]
  exact fun h => h rfl

/-- Membership in the range implies inequality with the deleted point. -/
theorem ne_of_mem_range_deletedOrderEmbedding {c : ι} {k : ι}
    (hk : k ∈ Set.range (deletedOrderEmbedding (ι := ι) c)) : k ≠ c :=
  mem_range_deletedOrderEmbedding.mp hk

end MemRange

section InvRange

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The inverse of the range embedding recovers the underlying value. -/
theorem invOfRange_deletedOrderEmbedding_val {c : ι} {k : ι}
    (hk : k ∈ Set.range (deletedOrderEmbedding (ι := ι) c)) :
    (invOfRange (deletedOrderEmbedding c) k hk).val = k :=
  invOfRange_spec (deletedOrderEmbedding c) k hk

/-- Explicit description of the range inverse as a subtype. -/
theorem invOfRange_deletedOrderEmbedding_eq {c : ι} {k : ι}
    (hk : k ∈ Set.range (deletedOrderEmbedding (ι := ι) c)) :
    invOfRange (deletedOrderEmbedding c) k hk =
      ⟨k, ne_of_mem_range_deletedOrderEmbedding hk⟩ := by
  apply Subtype.ext
  exact invOfRange_deletedOrderEmbedding_val hk

end InvRange

end Matrix.GeneralLinearGroup

namespace Matrix.GeneralLinearEquiv

open Matrix.GeneralLinearGroup

/-- Singleton subtype `{x // x = c}` equivalent to `Unit`. -/
def singletonEquivUnit {α : Type*} {c : α} :
    { x : α // x = c } ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨c, rfl⟩
  left_inv := by
    intro x
    obtain ⟨v, hv⟩ := x
    apply Subtype.ext
    exact hv.symm
  right_inv := by
    intro u
    cases u
    rfl

/-- Equivalence `α ≃ Unit ⊕ DeletedIndex α c` decomposing `α` at `c`. -/
noncomputable def nEquivUnitSumDel {α : Type*} (c : α) :
    α ≃ Unit ⊕ DeletedIndex α c := by
  classical
  haveI : DecidablePred (fun x : α => x = c) :=
    fun x => Classical.dec (x = c)
  exact Equiv.trans (Equiv.sumCompl (fun x => x = c)).symm
    (Equiv.sumCongr (singletonEquivUnit (c := c))
      (Equiv.refl (DeletedIndex α c)))

/-- `nEquivUnitSumDel` sends `c` to `inl ()`. -/
theorem nEquivUnitSumDel_apply_of_eq {α : Type*} {c : α} :
    nEquivUnitSumDel (α := α) c c = Sum.inl () := by
  classical
  have h1 : (Equiv.sumCompl (fun x => x = c)).symm c =
      Sum.inl ⟨c, rfl⟩ :=
    Equiv.sumCompl_symm_apply_of_pos (p := fun x => x = c) rfl
  have h_eq : nEquivUnitSumDel c c =
      (Equiv.sumCongr (singletonEquivUnit (c := c))
        (Equiv.refl (DeletedIndex α c)))
        ((Equiv.sumCompl (fun x => x = c)).symm c) := rfl
  rw [h_eq, h1]
  rfl

/-- `nEquivUnitSumDel` sends `j ≠ c` to `inr ⟨j, _⟩`. -/
theorem nEquivUnitSumDel_apply_of_ne {α : Type*} {c : α}
    {j : α} (hj : j ≠ c) :
    nEquivUnitSumDel c j = Sum.inr ⟨j, hj⟩ := by
  classical
  have h1 : (Equiv.sumCompl (fun x => x = c)).symm j =
      Sum.inr ⟨j, hj⟩ :=
    Equiv.sumCompl_symm_apply_of_neg (p := fun x => x = c) hj
  have h_eq : nEquivUnitSumDel c j =
      (Equiv.sumCongr (singletonEquivUnit (c := c))
        (Equiv.refl (DeletedIndex α c)))
        ((Equiv.sumCompl (fun x => x = c)).symm j) := rfl
  rw [h_eq, h1]
  rfl

/-- Symmetric of `nEquivUnitSumDel` on `inl`. -/
theorem nEquivUnitSumDel_symm_apply_inl {α : Type*} {c : α} :
    (nEquivUnitSumDel (α := α) c).symm (Sum.inl ()) = c := by
  classical
  have h1 : (Equiv.sumCongr (singletonEquivUnit (c := c))
      (Equiv.refl (DeletedIndex α c))).symm (Sum.inl ()) =
      Sum.inl ⟨c, rfl⟩ := rfl
  have h_eq : (nEquivUnitSumDel c).symm (Sum.inl ()) =
      (Equiv.sumCompl (fun x => x = c))
        ((Equiv.sumCongr (singletonEquivUnit (c := c))
          (Equiv.refl (DeletedIndex α c))).symm (Sum.inl ())) := rfl
  rw [h_eq, h1]
  rfl

/-- Symmetric of `nEquivUnitSumDel` on `inr`. -/
theorem nEquivUnitSumDel_symm_apply_inr {α : Type*} {c : α}
    (d : DeletedIndex α c) :
    (nEquivUnitSumDel c).symm (Sum.inr d) = d.val := by
  classical
  have h1 : (Equiv.sumCongr (singletonEquivUnit (c := c))
      (Equiv.refl (DeletedIndex α c))).symm (Sum.inr d) =
      Sum.inr d := rfl
  have h_eq : (nEquivUnitSumDel c).symm (Sum.inr d) =
      (Equiv.sumCompl (fun x => x = c))
        ((Equiv.sumCongr (singletonEquivUnit (c := c))
          (Equiv.refl (DeletedIndex α c))).symm (Sum.inr d)) := rfl
  rw [h_eq, h1]
  rfl

section InsertEquiv

variable {m n : Type*}

/-- Heterogeneous equivalence insertion: map `c` to `r` and otherwise use `σ`. -/
noncomputable def insertEquiv (r : m) (c : n)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) : n ≃ m :=
  Equiv.trans (nEquivUnitSumDel c)
    (Equiv.trans (Equiv.sumCongr (Equiv.refl Unit) σ)
      (nEquivUnitSumDel r).symm)

@[simp]
theorem insertEquiv_apply_c (r : m) (c : n)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) :
    insertEquiv r c σ c = r := by
  classical
  have h_n : nEquivUnitSumDel c c = Sum.inl () :=
    nEquivUnitSumDel_apply_of_eq
  have h_sum : (Equiv.sumCongr (Equiv.refl Unit) σ) (Sum.inl ()) =
      Sum.inl () := rfl
  have h_m : (nEquivUnitSumDel r).symm (Sum.inl ()) = r :=
    nEquivUnitSumDel_symm_apply_inl
  calc insertEquiv r c σ c
      = (Equiv.trans (Equiv.sumCongr (Equiv.refl Unit) σ)
            (nEquivUnitSumDel r).symm) (nEquivUnitSumDel c c) := rfl
    _ = (nEquivUnitSumDel r).symm
          ((Equiv.sumCongr (Equiv.refl Unit) σ) (nEquivUnitSumDel c c)) := rfl
    _ = (nEquivUnitSumDel r).symm
          ((Equiv.sumCongr (Equiv.refl Unit) σ) (Sum.inl ())) := by rw [h_n]
    _ = (nEquivUnitSumDel r).symm (Sum.inl ()) := by rw [h_sum]
    _ = r := h_m

/-- Insertion acts via `σ` away from `c`. -/
theorem insertEquiv_apply_of_ne {r : m} {c : n}
    {σ : DeletedIndex n c ≃ DeletedIndex m r} {j : n} (hj : j ≠ c) :
    insertEquiv r c σ j = (σ ⟨j, hj⟩).val := by
  classical
  have h_n : nEquivUnitSumDel c j = Sum.inr ⟨j, hj⟩ :=
    nEquivUnitSumDel_apply_of_ne hj
  have h_sum : (Equiv.sumCongr (Equiv.refl Unit) σ) (Sum.inr ⟨j, hj⟩) =
      Sum.inr (σ ⟨j, hj⟩) := rfl
  have h_m : (nEquivUnitSumDel r).symm (Sum.inr (σ ⟨j, hj⟩)) =
      (σ ⟨j, hj⟩).val := nEquivUnitSumDel_symm_apply_inr _
  calc insertEquiv r c σ j
      = (Equiv.trans (Equiv.sumCongr (Equiv.refl Unit) σ)
            (nEquivUnitSumDel r).symm) (nEquivUnitSumDel c j) := rfl
    _ = (nEquivUnitSumDel r).symm
          ((Equiv.sumCongr (Equiv.refl Unit) σ) (nEquivUnitSumDel c j)) := rfl
    _ = (nEquivUnitSumDel r).symm
          ((Equiv.sumCongr (Equiv.refl Unit) σ) (Sum.inr ⟨j, hj⟩)) := by rw [h_n]
    _ = (nEquivUnitSumDel r).symm (Sum.inr (σ ⟨j, hj⟩)) := by rw [h_sum]
    _ = (σ ⟨j, hj⟩).val := h_m

/-- Symmetry of heterogeneous insertion. -/
theorem insertEquiv_symm_eq (r : m) (c : n)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) :
    (insertEquiv r c σ).symm = insertEquiv c r σ.symm :=
  rfl

@[simp]
theorem insertEquiv_symm_apply_r (r : m) (c : n)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) :
    (insertEquiv r c σ).symm r = c := by
  rw [insertEquiv_symm_eq]
  exact insertEquiv_apply_c c r σ.symm

/-- Symmetric insertion away from `r`. -/
theorem insertEquiv_symm_apply_of_ne {r : m} {c : n}
    {σ : DeletedIndex n c ≃ DeletedIndex m r} {i : m} (hi : i ≠ r) :
    (insertEquiv r c σ).symm i = (σ.symm ⟨i, hi⟩).val := by
  rw [insertEquiv_symm_eq]
  exact insertEquiv_apply_of_ne hi

end InsertEquiv

section InsertWeights

variable {m : Type*} {R : Type*} [Semiring R]

/-- Heterogeneous weight insertion: assign `a` at `r` and `u` elsewhere. -/
noncomputable def insertWeights (r : m) (a : Rˣ)
    (u : DeletedIndex m r → Rˣ) : m → Rˣ :=
  fun i => by
    classical
    haveI : Decidable (i = r) := Classical.dec _
    exact if hi : i = r then a else u ⟨i, hi⟩

@[simp]
theorem insertWeights_apply_self (r : m) (a : Rˣ)
    (u : DeletedIndex m r → Rˣ) :
    insertWeights r a u r = a := by
  classical
  simp [insertWeights]

/-- Insertion acts via `u` away from `r`. -/
theorem insertWeights_apply_of_ne {r : m} {a : Rˣ}
    {u : DeletedIndex m r → Rˣ} {i : m} (hi : i ≠ r) :
    insertWeights r a u i = u ⟨i, hi⟩ := by
  classical
  simp [insertWeights, hi]

/-- Functoriality of `insertWeights` under `Units.map`. -/
theorem insertWeights_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {m : Type*} (r : m) (a : Rˣ)
    (u : DeletedIndex m r → Rˣ) (i : m) :
    Units.map f.toMonoidHom (insertWeights r a u i) =
      insertWeights r (Units.map f.toMonoidHom a)
        (fun d => Units.map f.toMonoidHom (u d)) i := by
  classical
  by_cases hi : i = r
  · rw [hi, insertWeights_apply_self, insertWeights_apply_self]
  · rw [insertWeights_apply_of_ne hi, insertWeights_apply_of_ne hi]

/-- Functoriality of `insertWeights` as a function. -/
theorem insertWeights_map_eq {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {m : Type*} (r : m) (a : Rˣ)
    (u : DeletedIndex m r → Rˣ) :
    (fun i => Units.map f.toMonoidHom (insertWeights r a u i)) =
      insertWeights r (Units.map f.toMonoidHom a)
        (fun d => Units.map f.toMonoidHom (u d)) := by
  funext i
  exact insertWeights_map f r a u i

end InsertWeights

section MonomialInsertion

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n] {R : Type*} [Semiring R]

/-- Inserting a pivot into a heterogeneous monomial equivalence yields a
monomial equivalence with inserted weights and permutation. -/
theorem insertEntryEquiv_monomialEquiv (r : m) (c : n) (a : Rˣ)
    (u : DeletedIndex m r → Rˣ)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) :
    insertEntryEquiv r c a (monomialEquiv (R := R) u σ) =
      monomialEquiv (R := R) (insertWeights r a u) (insertEquiv r c σ) := by
  apply ext
  ext i j
  by_cases hi : i = r
  · have hi_eq : i = r := hi
    by_cases hj : j = c
    · have hj_eq : j = c := hj
      have h_left : (insertEntryEquiv r c a (monomialEquiv u σ)).val i j =
          (a : R) := by
        rw [hi_eq, hj_eq]
        exact insertEntryEquiv_val_self r c a _
      have h_right : (monomialEquiv (R := R) (insertWeights r a u)
          (insertEquiv r c σ)).val i j = (a : R) := by
        rw [hi_eq, hj_eq, val_monomialEquiv_apply, insertEquiv_apply_c,
          insertWeights_apply_self, ite_eq_left rfl]
      rw [h_left, h_right]
    · have hj_ne : j ≠ c := hj
      have h_row : (insertEntryEquiv r c a (monomialEquiv u σ)).val i j = 0 := by
        rw [hi_eq]
        exact insertEntryEquiv_val_row_ne r c a (monomialEquiv u σ) hj_ne
      have h_val_ne : (σ ⟨j, hj_ne⟩).val ≠ r :=
        (σ ⟨j, hj_ne⟩).property
      have h_val_ne_i : (σ ⟨j, hj_ne⟩).val ≠ i := by
        rw [hi_eq]
        exact h_val_ne
      have h_right : (monomialEquiv (R := R) (insertWeights r a u)
          (insertEquiv r c σ)).val i j = 0 := by
        calc (monomialEquiv (R := R) (insertWeights r a u)
            (insertEquiv r c σ)).val i j
            = (monomialEquiv (R := R) (insertWeights r a u)
                (insertEquiv r c σ)).val r j := by rw [hi_eq]
          _ = if insertEquiv r c σ j = r then
                (insertWeights r a u r : R) else 0 := by
              simp only [val_monomialEquiv_apply]
          _ = if (σ ⟨j, hj_ne⟩).val = r then
                (insertWeights r a u r : R) else 0 := by
              rw [insertEquiv_apply_of_ne hj_ne]
          _ = 0 := by rw [ite_eq_right h_val_ne]
      rw [h_row, h_right]
  · have hi_ne : i ≠ r := hi
    by_cases hj : j = c
    · have hj_eq : j = c := hj
      have h_eq : insertEquiv r c σ c = r := insertEquiv_apply_c _ _ _
      have h_ne : r ≠ i := Ne.symm hi_ne
      have h_col : (insertEntryEquiv r c a (monomialEquiv u σ)).val i j = 0 := by
        rw [hj_eq]
        exact insertEntryEquiv_val_col_ne r c a (monomialEquiv u σ) hi_ne
      have h_right : (monomialEquiv (R := R) (insertWeights r a u)
          (insertEquiv r c σ)).val i j = 0 := by
        rw [hj_eq, val_monomialEquiv_apply, h_eq, ite_eq_right h_ne]
      rw [h_col, h_right]
    · have hj_ne : j ≠ c := hj
      have h_left : (insertEntryEquiv r c a (monomialEquiv u σ)).val i j =
          (monomialEquiv (R := R) u σ).val ⟨i, hi_ne⟩ ⟨j, hj_ne⟩ :=
        insertEntryEquiv_val_ne_ne r c a _ hi_ne hj_ne
      rw [h_left]
      simp only [val_monomialEquiv_apply, insertWeights_apply_of_ne hi_ne,
        insertEquiv_apply_of_ne hj_ne]
      by_cases hσ : σ ⟨j, hj_ne⟩ = ⟨i, hi_ne⟩
      · have h_val : (σ ⟨j, hj_ne⟩).val = i := congrArg Subtype.val hσ
        rw [ite_eq_left h_val, ite_eq_left hσ]
      · have h_val : (σ ⟨j, hj_ne⟩).val ≠ i := by
          intro heq
          apply hσ
          exact Subtype.ext heq
        rw [ite_eq_right h_val, ite_eq_right hσ]

end MonomialInsertion

section Composition

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {R : Type*} [Semiring R]

/-- Heterogeneous block composition law for insertion. -/
theorem insertEntryEquiv_trans (r : m) (s : p) (c : n) (a b : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex p s) R)
    (E : GeneralLinearEquiv (DeletedIndex p s) (DeletedIndex n c) R) :
    (insertEntryEquiv r s a D).trans (insertEntryEquiv s c b E) =
      insertEntryEquiv r c (a * b) (D.trans E) := by
  apply ext
  ext i j
  simp only [val_trans, Matrix.mul_apply, val_insertEntryEquiv]
  by_cases hi : i = r
  · have hi_eq : i = r := hi
    have hA_zero : ∀ k : p, k ≠ s →
        insertEntryVal r s a D i k = 0 := by
      intro k hk
      rw [hi_eq]
      simp [insertEntryVal, hk]
    have h_sum : ∀ j : n,
        (∑ k : p, insertEntryVal r s a D i k *
          insertEntryVal s c b E k j) =
        insertEntryVal r s a D i s *
          insertEntryVal s c b E s j := by
      intro j
      apply Fintype.sum_eq_single s
      intro k hk
      rw [hA_zero k hk, zero_mul]
    by_cases hj : j = c
    · have hj_eq : j = c := hj
      have h_sum_j := h_sum c
      rw [hj_eq, h_sum_j]
      simp [insertEntryVal, Units.val_mul, hi_eq]
    · have hj_ne : j ≠ c := hj
      have h_sum_j := h_sum j
      rw [h_sum_j]
      simp [insertEntryVal, hj_ne, hi_eq]
  · have hi_ne : i ≠ r := hi
    by_cases hj : j = c
    · have hj_eq : j = c := hj
      let f : p → R := fun k =>
        insertEntryVal r s a D i k * insertEntryVal s c b E k c
      have hf_s : f s = 0 := by
        simp [f, insertEntryVal, hi_ne]
      have h_sum_eq : (∑ k : p, f k) = ∑ d : DeletedIndex p s, f d.val := by
        have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := s)
        rw [hf_s, zero_add] at h
        exact h
      have h_f_eq : ∀ d : DeletedIndex p s, f d.val =
          D.val ⟨i, hi_ne⟩ d * insertEntryVal s c b E d.val c := by
        intro d
        simp [f, insertEntryVal, hi_ne, d.property]
      have hB_zero : ∀ d : DeletedIndex p s,
          insertEntryVal s c b E d.val c = 0 := by
        intro d
        simp [insertEntryVal, d.property]
      have h_sum_zero : (∑ d : DeletedIndex p s, f d.val) = 0 := by
        apply Finset.sum_eq_zero
        intro d _
        rw [h_f_eq d, hB_zero d, mul_zero]
      have h_left : (∑ k : p, insertEntryVal r s a D i k *
          insertEntryVal s c b E k c) = ∑ k : p, f k := rfl
      calc (∑ k : p, insertEntryVal r s a D i k *
            insertEntryVal s c b E k j)
          = (∑ k : p, insertEntryVal r s a D i k *
            insertEntryVal s c b E k c) := by rw [hj_eq]
        _ = ∑ k : p, f k := h_left
        _ = ∑ d : DeletedIndex p s, f d.val := h_sum_eq
        _ = 0 := h_sum_zero
        _ = insertEntryVal r c (a * b) (D.trans E) i j := by
            rw [hj_eq]
            simp [insertEntryVal, hi_ne]
    · have hj_ne : j ≠ c := hj
      let f : p → R := fun k =>
        insertEntryVal r s a D i k * insertEntryVal s c b E k j
      have hf_s : f s = 0 := by
        simp [f, insertEntryVal, hi_ne]
      have h_sum_eq : (∑ k : p, f k) = ∑ d : DeletedIndex p s, f d.val := by
        have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := s)
        rw [hf_s, zero_add] at h
        exact h
      have h_f_eq : ∀ d : DeletedIndex p s, f d.val =
          D.val ⟨i, hi_ne⟩ d * insertEntryVal s c b E d.val j := by
        intro d
        simp [f, insertEntryVal, hi_ne, d.property]
      have hB_eq : ∀ d : DeletedIndex p s,
          insertEntryVal s c b E d.val j = E.val d ⟨j, hj_ne⟩ := by
        intro d
        simp [insertEntryVal, d.property, hj_ne]
      have h_sum_sub : (∑ d : DeletedIndex p s, f d.val) =
          (D.val * E.val) ⟨i, hi_ne⟩ ⟨j, hj_ne⟩ := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro d _
        rw [h_f_eq d, hB_eq d]
      calc (∑ k : p, insertEntryVal r s a D i k *
            insertEntryVal s c b E k j)
          = ∑ k : p, f k := rfl
        _ = ∑ d : DeletedIndex p s, f d.val := h_sum_eq
        _ = (D.val * E.val) ⟨i, hi_ne⟩ ⟨j, hj_ne⟩ := h_sum_sub
        _ = (D.trans E).val ⟨i, hi_ne⟩ ⟨j, hj_ne⟩ := rfl
        _ = insertEntryVal r c (a * b) (D.trans E) i j := by
            simp [insertEntryVal, hi_ne, hj_ne]

/-- Left unit: inserting `refl` with `1` on the right is neutral. -/
@[simp]
theorem insertEntryEquiv_trans_refl_right (r : m) (s : p) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex p s) R) :
    (insertEntryEquiv r s a D).trans (insertEntryEquiv s s 1 refl) =
      insertEntryEquiv r s a D := by
  have h := insertEntryEquiv_trans r s s a 1 D refl
  simp only [trans_refl, mul_one] at h
  exact h

/-- Right unit: inserting `refl` with `1` on the left is neutral. -/
@[simp]
theorem insertEntryEquiv_trans_refl_left (s : p) (c : n) (b : Rˣ)
    (E : GeneralLinearEquiv (DeletedIndex p s) (DeletedIndex n c) R) :
    (insertEntryEquiv s s 1 refl).trans (insertEntryEquiv s c b E) =
      insertEntryEquiv s c b E := by
  have h := insertEntryEquiv_trans s s c 1 b refl E
  simp only [refl_trans, one_mul] at h
  exact h

end Composition

section SquareBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable {R : Type*} [Ring R]

private lemma extendMatrix_deletedOrderEmbedding_apply
    (c : ι) (M : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R)
    (i j : ι) :
    extendMatrix (deletedOrderEmbedding c) M i j =
      if hi : i = c then if j = c then 1 else 0
      else if hj : j = c then 0
      else M ⟨i, hi⟩ ⟨j, hj⟩ := by
  have h_range_iff : ∀ k : ι,
      k ∈ Set.range (deletedOrderEmbedding (ι := ι) c) ↔ k ≠ c :=
    fun k => mem_range_deletedOrderEmbedding
  by_cases h_i : i = c
  · have hi_mem : i ∉ Set.range (deletedOrderEmbedding c) := by
      intro h_mem
      have h_ne : i ≠ c := (h_range_iff i).mp h_mem
      exact h_ne h_i
    rw [extendMatrix_apply, dite_eq_right hi_mem]
    by_cases h_j : j = c
    · have hij : i = j := by rw [h_i, h_j]
      rw [ite_eq_left hij]
      rw [dite_eq_left h_i]
      rw [ite_eq_left h_j]
    · have hij : i ≠ j := by
        intro h_eq
        apply h_j
        rw [← h_i, h_eq]
      rw [ite_eq_right hij]
      rw [dite_eq_left h_i]
      rw [ite_eq_right h_j]
  · have hi_mem : i ∈ Set.range (deletedOrderEmbedding c) := by
      rw [h_range_iff]
      exact h_i
    rw [extendMatrix_apply, dite_eq_left hi_mem]
    by_cases h_j : j = c
    · have hj_mem : j ∉ Set.range (deletedOrderEmbedding c) := by
        intro h_mem
        have h_ne : j ≠ c := (h_range_iff j).mp h_mem
        exact h_ne h_j
      rw [dite_eq_right hj_mem]
      rw [dite_eq_right h_i]
      rw [dite_eq_left h_j]
    · have hj_mem : j ∈ Set.range (deletedOrderEmbedding c) := by
        rw [h_range_iff]
        exact h_j
      rw [dite_eq_left hj_mem]
      rw [dite_eq_right h_i]
      rw [dite_eq_right h_j]
      have h_eq_i := invOfRange_deletedOrderEmbedding_eq hi_mem
      have h_eq_j := invOfRange_deletedOrderEmbedding_eq hj_mem
      rw [h_eq_i, h_eq_j]

/-- Square bridge: insertion of `1` and `g` equals `extendByIdentity` via
`deletedOrderEmbedding`. -/
theorem toGL_insertEntryEquiv_one_ofGL_eq_extendByIdentity (c : ι)
    (g : GL (DeletedIndex ι c) R) :
    toGL (insertEntryEquiv (m := ι) (n := ι) c c 1 (ofGL g)) =
      Matrix.GeneralLinearGroup.extendByIdentity (deletedOrderEmbedding c) g := by
  have h_toGL : toGL (insertEntryEquiv (m := ι) (n := ι) c c 1 (ofGL g)) =
      Matrix.GeneralLinearGroup.insertCoordinateUnit c 1 g := by
    calc toGL (insertEntryEquiv c c 1 (ofGL g))
        = Matrix.GeneralLinearGroup.insertCoordinateUnit c 1 (toGL (ofGL g)) :=
          toGL_insertEntryEquiv c 1 (ofGL g)
      _ = Matrix.GeneralLinearGroup.insertCoordinateUnit c 1 g := by
          rw [toGL_ofGL]
  rw [h_toGL]
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_extendByIdentity,
    Matrix.GeneralLinearGroup.coe_insertCoordinateUnit]
  rw [extendMatrix_deletedOrderEmbedding_apply]
  rfl

/-- Insertion preserves upper-elementary membership. -/
theorem toGL_insertEntryEquiv_one_ofGL_mem_upperElementary (c : ι)
    (g : GL (DeletedIndex ι c) R)
    (hg : g ∈ Matrix.GeneralLinearGroup.upperElementarySubgroup
      (DeletedIndex ι c) R) :
    toGL (insertEntryEquiv (m := ι) (n := ι) c c 1 (ofGL g)) ∈
      Matrix.GeneralLinearGroup.upperElementarySubgroup ι R := by
  rw [toGL_insertEntryEquiv_one_ofGL_eq_extendByIdentity]
  exact Matrix.GeneralLinearGroup.extendByIdentity_mem_upperElementarySubgroup
    (deletedOrderEmbedding c) hg

/-- Bundled upper-elementary version of the square bridge. -/
theorem upperElementary_extendByIdentity_eq (c : ι)
    (g : Matrix.GeneralLinearGroup.upperElementarySubgroup
      (DeletedIndex ι c) R) :
    (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
      (deletedOrderEmbedding c) g).val =
      toGL (insertEntryEquiv (m := ι) (n := ι) c c 1 (ofGL g.val)) := by
  simp [Matrix.GeneralLinearGroup.UpperElementary.coe_extendByIdentity,
    toGL_insertEntryEquiv_one_ofGL_eq_extendByIdentity]

end SquareBridge

section CoeffNaturality

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]
variable {R S : Type*} [Semiring R] [Semiring S]

/-- Coefficient naturality for `insertEntryEquiv` composed with monomial. -/
theorem map_insertEntryEquiv_monomialEquiv (f : R →+* S)
    (r : m) (c : n) (a : Rˣ) (u : DeletedIndex m r → Rˣ)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) :
    (insertEntryEquiv r c a (monomialEquiv (R := R) u σ)).map f =
      insertEntryEquiv r c (Units.map f.toMonoidHom a)
        (monomialEquiv (R := S) (fun d => Units.map f.toMonoidHom (u d)) σ) := by
  have h1 : (insertEntryEquiv r c a (monomialEquiv (R := R) u σ)).map f =
      insertEntryEquiv r c (Units.map f.toMonoidHom a)
        ((monomialEquiv (R := R) u σ).map f) := by
    rw [map_insertEntryEquiv]
    rfl
  have h2 : (monomialEquiv (R := R) u σ).map f =
      monomialEquiv (R := S) (fun d => Units.map f.toMonoidHom (u d)) σ := by
    rw [map_monomialEquiv]
    rfl
  calc (insertEntryEquiv r c a (monomialEquiv u σ)).map f
      = insertEntryEquiv r c (Units.map f.toMonoidHom a)
          ((monomialEquiv u σ).map f) := h1
    _ = insertEntryEquiv r c (Units.map f.toMonoidHom a)
          (monomialEquiv (fun d => Units.map f.toMonoidHom (u d)) σ) := by
        rw [h2]

/-- Coefficient naturality for monomial with inserted weights. -/
theorem map_monomialEquiv_insertWeights (f : R →+* S)
    (r : m) (c : n) (a : Rˣ) (u : DeletedIndex m r → Rˣ)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) :
    (monomialEquiv (R := R) (insertWeights r a u) (insertEquiv r c σ)).map f =
      monomialEquiv (R := S)
        (insertWeights r (Units.map f.toMonoidHom a)
          (fun d => Units.map f.toMonoidHom (u d)))
        (insertEquiv r c σ) := by
  have h_map : (monomialEquiv (R := R) (insertWeights r a u)
      (insertEquiv r c σ)).map f =
      monomialEquiv (R := S)
        (fun i => Units.map f.toMonoidHom (insertWeights r a u i))
        (insertEquiv r c σ) := by
    rw [map_monomialEquiv]
    rfl
  have h_eq : (fun i => Units.map f.toMonoidHom (insertWeights r a u i)) =
      insertWeights r (Units.map f.toMonoidHom a)
        (fun d => Units.map f.toMonoidHom (u d)) := by
    funext i
    exact insertWeights_map f r a u i
  calc (monomialEquiv (R := R) (insertWeights r a u)
          (insertEquiv r c σ)).map f
      = monomialEquiv (R := S)
          (fun i => Units.map f.toMonoidHom (insertWeights r a u i))
          (insertEquiv r c σ) := h_map
    _ = monomialEquiv (R := S)
          (insertWeights r (Units.map f.toMonoidHom a)
            (fun d => Units.map f.toMonoidHom (u d)))
          (insertEquiv r c σ) := by
        rw [h_eq]

/-- Naturality bridge between insertion and monomial forms. -/
theorem insertEntryEquiv_monomialEquiv_map (f : R →+* S)
    (r : m) (c : n) (a : Rˣ) (u : DeletedIndex m r → Rˣ)
    (σ : DeletedIndex n c ≃ DeletedIndex m r) :
    (monomialEquiv (R := R) (insertWeights r a u) (insertEquiv r c σ)).map f =
      insertEntryEquiv r c (Units.map f.toMonoidHom a)
        (monomialEquiv (R := S) (fun d => Units.map f.toMonoidHom (u d)) σ) := by
  calc (monomialEquiv (R := R) (insertWeights r a u)
          (insertEquiv r c σ)).map f
      = monomialEquiv (R := S)
          (insertWeights r (Units.map f.toMonoidHom a)
            (fun d => Units.map f.toMonoidHom (u d)))
          (insertEquiv r c σ) := by
        rw [map_monomialEquiv_insertWeights]
    _ = insertEntryEquiv r c (Units.map f.toMonoidHom a)
          (monomialEquiv (R := S) (fun d => Units.map f.toMonoidHom (u d)) σ) := by
        rw [← insertEntryEquiv_monomialEquiv]

end CoeffNaturality

end Matrix.GeneralLinearEquiv
