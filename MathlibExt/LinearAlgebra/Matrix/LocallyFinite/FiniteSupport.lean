/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.Reindex
public import Mathlib.RingTheory.Ideal.Defs

/-!
# The finite-matrix ideal and its original local units

Finite matrices have finite total coefficient support. This is stronger than
row-and-column finiteness and is the actual condition defining the finite-matrix
ideal. Both multiplication directions are proved separately over arbitrary
noncommutative semirings.

For countable matrices, finite support is equivalent to lying inside an
original finite square. The literal finite diagonal projections are common
two-sided local units for every finite family of finite matrices.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe um un up um' un' uR uS uι

namespace Matrix.LocallyFinite

variable {m : Type um} {n : Type un} {p : Type up}
  {m' : Type um'} {n' : Type un'} {R : Type uR} {S : Type uS}

/-- The total support of the original coefficient matrix. -/
def support [Zero R] (A : Matrix.LocallyFinite m n R) : Set (m × n) :=
  Function.support (fun z => A z.1 z.2)

/-- Membership in total support records the actual nonzero coefficient. -/
@[simp]
theorem mem_support [Zero R] (A : Matrix.LocallyFinite m n R) (i : m) (j : n) :
    (i, j) ∈ support A ↔ A i j ≠ 0 := Iff.rfl

/-- A finite matrix has finite total support, rather than only finite individual rows. -/
abbrev HasFiniteSupport [Zero R] (A : Matrix.LocallyFinite m n R) : Prop :=
  (support A).Finite

/-- The original zero matrix has empty total support. -/
@[simp]
theorem support_zero [Zero R] : support (0 : Matrix.LocallyFinite m n R) = ∅ := by
  ext z
  change (0 : Matrix.LocallyFinite m n R) z.1 z.2 ≠ 0 ↔ False
  simp

/-- Zero is a finite matrix. -/
theorem hasFiniteSupport_zero [Zero R] : HasFiniteSupport (0 : Matrix.LocallyFinite m n R) := by
  change (support (0 : Matrix.LocallyFinite m n R)).Finite
  rw [support_zero]
  exact Set.finite_empty

/-- Pointwise addition preserves finite total coefficient support. -/
theorem HasFiniteSupport.add [AddZeroClass R] {A B : Matrix.LocallyFinite m n R}
    (hA : HasFiniteSupport A) (hB : HasFiniteSupport B) : HasFiniteSupport (A + B) := by
  refine (hA.union hB).subset ?_
  intro z hz
  by_contra h
  change ¬(A z.1 z.2 ≠ 0 ∨ B z.1 z.2 ≠ 0) at h
  simp only [not_or, not_not] at h
  change (A + B) z.1 z.2 ≠ 0 at hz
  exact hz (by simp [h.1, h.2])

/-- A zero-preserving coefficient map preserves finite total support. -/
theorem HasFiniteSupport.map [Zero R] [Zero S] {A : Matrix.LocallyFinite m n R}
    (hA : HasFiniteSupport A) (f : ZeroHom R S) : HasFiniteSupport (map f A) := by
  refine hA.subset ?_
  intro z hz
  change f (A z.1 z.2) ≠ 0 at hz
  change A z.1 z.2 ≠ 0
  intro h
  exact hz (h ▸ f.map_zero)

/-- Pointwise negation preserves finite total support. -/
theorem HasFiniteSupport.neg [AddGroup R] {A : Matrix.LocallyFinite m n R}
    (hA : HasFiniteSupport A) : HasFiniteSupport (-A) :=
  hA.map ⟨fun r => -r, neg_zero⟩

/-- Pointwise subtraction preserves finite total support. -/
theorem HasFiniteSupport.sub [AddGroup R] {A B : Matrix.LocallyFinite m n R}
    (hA : HasFiniteSupport A) (hB : HasFiniteSupport B) : HasFiniteSupport (A - B) :=
  hA.add hB.neg

/-- Finite-index coefficient matrices have finite total support. -/
theorem hasFiniteSupport_of_finite [Zero R] [Finite m] [Finite n]
    (A : Matrix.LocallyFinite m n R) : HasFiniteSupport A := Set.toFinite _

/-- Multiplication on the right uses only finitely many original rows of the second matrix. -/
theorem HasFiniteSupport.comp_right [Semiring R] {A : Matrix.LocallyFinite m n R}
    (hA : HasFiniteSupport A) (B : Matrix.LocallyFinite n p R) :
    HasFiniteSupport (A.comp B) := by
  refine (hA.biUnion fun z _ => (B.row_finite z.2).image (fun j => (z.1, j))).subset ?_
  intro z hz
  obtain ⟨k, hAik, hBkj⟩ := exists_comp_term A B z.1 z.2 hz
  exact Set.mem_iUnion.mpr ⟨(z.1, k), Set.mem_iUnion.mpr ⟨hAik, ⟨z.2, hBkj, rfl⟩⟩⟩

/-- Multiplication on the left uses only finitely many original columns of the first matrix. -/
theorem HasFiniteSupport.comp_left [Semiring R] {B : Matrix.LocallyFinite n p R}
    (hB : HasFiniteSupport B) (A : Matrix.LocallyFinite m n R) :
    HasFiniteSupport (A.comp B) := by
  refine (hB.biUnion fun z _ => (A.column_finite z.1).image (fun i => (i, z.2))).subset ?_
  intro z hz
  obtain ⟨k, hAik, hBkj⟩ := exists_comp_term A B z.1 z.2 hz
  exact Set.mem_iUnion.mpr ⟨(k, z.2), Set.mem_iUnion.mpr ⟨hBkj, ⟨z.1, hAik, rfl⟩⟩⟩

/-- Actual reindexing preserves finite total support. -/
theorem HasFiniteSupport.reindex [Zero R] {A : Matrix.LocallyFinite m n R}
    (hA : HasFiniteSupport A) (e : m ≃ m') (f : n ≃ n') :
    HasFiniteSupport (reindex e f A) :=
  hA.preimage (e.symm.prodCongr f.symm).injective.injOn

/-- Actual zero extension preserves finite total support. -/
theorem HasFiniteSupport.extend [Zero R] {A : Matrix.LocallyFinite m n R}
    (hA : HasFiniteSupport A) (e : m ↪ m') (f : n ↪ n') :
    HasFiniteSupport (extend e f A) := by
  refine (hA.image (Prod.map e f)).subset ?_
  intro z hz
  change Matrix.LocallyFinite.extend e f A z.1 z.2 ≠ 0 at hz
  have he : z.1 ∈ Set.range e := by
    by_contra he
    exact hz (extend_apply_of_notMem_row_range e f A z.1 z.2 he)
  have hf : z.2 ∈ Set.range f := by
    by_contra hf
    exact hz (extend_apply_of_notMem_column_range e f A z.1 z.2 hf)
  obtain ⟨i, hi⟩ := he
  obtain ⟨j, hj⟩ := hf
  refine ⟨(i, j), ?_, Prod.ext hi hj⟩
  change A i j ≠ 0
  simpa only [← hi, ← hj, extend_apply_image] using hz

/-- The actual finite-matrix left ideal inside the original square matrix ring. -/
def finiteSupportIdeal [Semiring R] : Ideal (Matrix.LocallyFinite n n R) where
  carrier := {A | HasFiniteSupport A}
  zero_mem' := hasFiniteSupport_zero
  add_mem' := HasFiniteSupport.add
  smul_mem' A _ hB := hB.comp_left A

/-- Ideal membership is exactly finite total support of the original coefficients. -/
@[simp]
theorem mem_finiteSupportIdeal [Semiring R] (A : Matrix.LocallyFinite n n R) :
    A ∈ finiteSupportIdeal ↔ HasFiniteSupport A := Iff.rfl

instance [Semiring R] : (finiteSupportIdeal (n := n) (R := R)).IsTwoSided where
  mul_mem_of_left B hA := hA.comp_right B

/-- Entrywise ring maps preserve the actual finite-matrix ideal. -/
theorem mapRingHom_mem_finiteSupportIdeal [Semiring R] [Semiring S] (f : R →+* S)
    {A : Matrix.LocallyFinite n n R} (hA : A ∈ finiteSupportIdeal) :
    mapRingHom f A ∈ finiteSupportIdeal := hA.map ⟨f, f.map_zero⟩

/-- Total finite support is equivalent to containment in an original finite rectangle. -/
theorem hasFiniteSupport_iff_exists_rectangle [Zero R] (A : Matrix.LocallyFinite m n R) :
    HasFiniteSupport A ↔ ∃ s : Finset m, ∃ t : Finset n,
      ∀ i j, i ∉ s ∨ j ∉ t → A i j = 0 := by
  classical
  constructor
  · intro hA
    have hs := hA.image Prod.fst
    have ht := hA.image Prod.snd
    refine ⟨hs.toFinset, ht.toFinset, ?_⟩
    intro i j h
    by_contra hij
    rcases h with hi | hj
    · exact hi (hs.mem_toFinset.mpr ⟨(i, j), hij, rfl⟩)
    · exact hj (ht.mem_toFinset.mpr ⟨(i, j), hij, rfl⟩)
  · rintro ⟨s, t, h⟩
    refine (s.finite_toSet.prod t.finite_toSet).subset ?_
    intro z hz
    constructor
    · by_contra hi
      exact hz (h z.1 z.2 (Or.inl hi))
    · by_contra hj
      exact hz (h z.1 z.2 (Or.inr hj))

/-- A countable finite matrix has an actual common row and column cutoff. -/
theorem exists_bound_of_hasFiniteSupport [Zero R] {A : Matrix.LocallyFinite ℕ ℕ R}
    (hA : HasFiniteSupport A) : ∃ N : ℕ,
      ∀ i j, N ≤ i ∨ N ≤ j → A i j = 0 := by
  obtain ⟨b, hb⟩ := (hA.image (fun z => max z.1 z.2)).bddAbove
  refine ⟨b + 1, ?_⟩
  intro i j h
  by_contra hij
  have hmax : max i j ≤ b := hb ⟨(i, j), hij, rfl⟩
  rcases h with hi | hj
  · exact Nat.not_succ_le_self b (hi.trans ((le_max_left i j).trans hmax))
  · exact Nat.not_succ_le_self b (hj.trans ((le_max_right i j).trans hmax))

/-- A genuine finite row and column cutoff implies finite total support. -/
theorem hasFiniteSupport_of_bound [Zero R] (A : Matrix.LocallyFinite ℕ ℕ R) (N : ℕ)
    (h : ∀ i j, N ≤ i ∨ N ≤ j → A i j = 0) : HasFiniteSupport A := by
  apply (hasFiniteSupport_iff_exists_rectangle A).mpr
  refine ⟨Finset.range N, Finset.range N, ?_⟩
  intro i j hij
  apply h i j
  simpa only [Finset.mem_range, not_lt] using hij

/-- The countable finite-matrix condition is exactly an original finite square cutoff. -/
theorem hasFiniteSupport_iff_exists_bound [Zero R] (A : Matrix.LocallyFinite ℕ ℕ R) :
    HasFiniteSupport A ↔ ∃ N : ℕ, ∀ i j, N ≤ i ∨ N ≤ j → A i j = 0 :=
  ⟨exists_bound_of_hasFiniteSupport, fun ⟨N, h⟩ => hasFiniteSupport_of_bound A N h⟩

/-- Products of original diagonal matrices multiply the actual ordered diagonal coefficients. -/
theorem diagonal_comp_diagonal [Semiring R] (d e : n → R) :
    (diagonal d).comp (diagonal e) = diagonal (fun i => d i * e i) := by
  ext i j
  rw [diagonal_comp_apply]
  by_cases h : i = j <;> simp [diagonal_apply, h]

/-- The original finite diagonal projection onto the first `N` countable coordinates. -/
def finiteProjection [Zero R] [One R] (N : ℕ) : Matrix.LocallyFinite ℕ ℕ R :=
  diagonal fun i => if i < N then 1 else 0

/-- Finite projection coefficients retain both the diagonal and original cutoff. -/
theorem finiteProjection_apply [Zero R] [One R] (N i j : ℕ) :
    finiteProjection (R := R) N i j = if i = j then (if i < N then 1 else 0) else 0 := by
  by_cases h : i = j <;> simp [finiteProjection, diagonal_apply, h]

/-- The original finite diagonal projection belongs to the actual finite-matrix ideal. -/
theorem hasFiniteSupport_finiteProjection [Zero R] [One R] (N : ℕ) :
    HasFiniteSupport (finiteProjection (R := R) N) := by
  apply hasFiniteSupport_of_bound _ N
  intro i j h
  by_cases hij : i = j
  · subst j
    have hi : N ≤ i := h.elim id id
    simp [finiteProjection_apply, Nat.not_lt.mpr hi]
  · simp [finiteProjection_apply, hij]

/-- The actual finite projection is a left unit for an original matrix with the given cutoff. -/
theorem finiteProjection_comp_eq [Semiring R] (A : Matrix.LocallyFinite ℕ ℕ R) (N : ℕ)
    (h : ∀ i j, N ≤ i ∨ N ≤ j → A i j = 0) :
    (finiteProjection N).comp A = A := by
  ext i j
  change (diagonal (fun i => if i < N then (1 : R) else 0)).comp A i j = A i j
  rw [diagonal_comp_apply]
  by_cases hi : i < N
  · simp [hi]
  · rw [h i j (Or.inl (Nat.le_of_not_lt hi))]
    simp

/-- The actual finite projection is a right unit for an original matrix with the given cutoff. -/
theorem comp_finiteProjection_eq [Semiring R] (A : Matrix.LocallyFinite ℕ ℕ R) (N : ℕ)
    (h : ∀ i j, N ≤ i ∨ N ≤ j → A i j = 0) :
    A.comp (finiteProjection N) = A := by
  ext i j
  change A.comp (diagonal (fun j => if j < N then (1 : R) else 0)) i j = A i j
  rw [comp_diagonal_apply]
  by_cases hj : j < N
  · simp [hj]
  · rw [h i j (Or.inr (Nat.le_of_not_lt hj))]
    simp

/-- Every finite countable matrix has the literal finite projection as a two-sided local unit. -/
theorem exists_finiteProjection_local_unit [Semiring R]
    {A : Matrix.LocallyFinite ℕ ℕ R} (hA : HasFiniteSupport A) :
    ∃ N : ℕ, finiteProjection N * A = A ∧ A * finiteProjection N = A := by
  obtain ⟨N, hN⟩ := exists_bound_of_hasFiniteSupport hA
  exact ⟨N, finiteProjection_comp_eq A N hN, comp_finiteProjection_eq A N hN⟩

/-- Every finite family of original finite matrices has one common literal two-sided local unit. -/
theorem exists_common_finiteProjection_local_unit [Semiring R] {ι : Type uι} [Finite ι]
    (A : ι → Matrix.LocallyFinite ℕ ℕ R) (hA : ∀ k, HasFiniteSupport (A k)) :
    ∃ N : ℕ, ∀ k, finiteProjection N * A k = A k ∧ A k * finiteProjection N = A k := by
  choose N hN using fun k => exists_bound_of_hasFiniteSupport (hA k)
  obtain ⟨b, hb⟩ := (Set.finite_range N).bddAbove
  refine ⟨b, fun k => ?_⟩
  have hcut : ∀ i j, b ≤ i ∨ b ≤ j → A k i j = 0 := by
    intro i j hij
    have hkb : N k ≤ b := hb (Set.mem_range_self k)
    exact hN k i j (hij.elim (fun hi => Or.inl (hkb.trans hi))
      (fun hj => Or.inr (hkb.trans hj)))
  exact ⟨finiteProjection_comp_eq (A k) b hcut, comp_finiteProjection_eq (A k) b hcut⟩

/-- Multiplying actual finite projections takes the minimum of their original cutoffs. -/
theorem finiteProjection_mul [Semiring R] (M N : ℕ) :
    finiteProjection (R := R) M * finiteProjection N = finiteProjection (min M N) := by
  change (diagonal _).comp (diagonal _) = diagonal _
  rw [diagonal_comp_diagonal]
  congr 1
  funext i
  by_cases hM : i < M <;> by_cases hN : i < N <;> simp [lt_min_iff, hM, hN]

/-- Each original finite diagonal projection is idempotent. -/
theorem finiteProjection_idempotent [Semiring R] (N : ℕ) :
    finiteProjection (R := R) N * finiteProjection N = finiteProjection N := by
  rw [finiteProjection_mul, min_self]

end Matrix.LocallyFinite

end
