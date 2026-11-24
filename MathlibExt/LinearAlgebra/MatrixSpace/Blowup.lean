/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Square Kronecker blow-ups and matrix-unit descent

A matrix space is a native submodule of `Matrix i j K`. Its square blow-up is the
bilinear submodule image under the native Kronecker product with all `d × d` matrices.
An amplified vector subspace consists of the vectors on `j × d` whose projected
columns lie in the original subspace. These constructions keep the product indices
used by `Matrix.kroneckerBilinear`.

The full block-factor matrix algebra saturates a vector subspace to the amplification
of its projected-column span. This saturation preserves the entire square-blow-up image.
Amplification multiplies dimension by the block degree, so a shrunk subspace descends to
its actual projected-column space with at least the scaled deficiency. Empty block-index
types are supported; recovering a subspace or cancelling the block degree requires a
nonempty block-index type.

## References

Gábor Ivanyos, Youming Qiao and K. V. Subrahmanyam, *Non-commutative Edmonds' problem
and matrix semi-invariants*, §5.1, Propositions 5.1 and 5.2; and *Constructive
noncommutative rank computation in deterministic polynomial time over fields of
arbitrary characteristics*, §2.
-/

@[expose] public section

universe u v w z

namespace LinearMap

variable {R : Type u} [CommSemiring R] {j : Type v} {d : Type w}

/-- Insert a vector in one column of the product-indexed vector space. -/
def columnInsert [DecidableEq d] (a : d) : (j → R) →ₗ[R] (j × d → R) :=
  LinearMap.pi fun p : j × d => if p.2 = a then LinearMap.proj p.1 else 0

@[simp]
theorem columnInsert_apply [DecidableEq d] (a : d) (x : j → R) (p : j × d) :
    columnInsert a x p = if p.2 = a then x p.1 else 0 := by
  by_cases h : p.2 = a <;> simp [columnInsert, h]

@[simp]
theorem funLeft_columnInsert [DecidableEq d] (a b : d) (x : j → R) :
    LinearMap.funLeft R R (fun k : j => (k, a)) (columnInsert b x) =
      if a = b then x else 0 := by
  by_cases h : a = b <;> ext k <;> simp [columnInsert_apply, h]

/-- A vector is the sum of the insertions of its actual projected columns. -/
theorem sum_columnInsert [Fintype d] [DecidableEq d] (x : j × d → R) :
    ∑ a : d, columnInsert a (fun k : j => x (k, a)) = x := by
  ext p
  simp [columnInsert_apply, Finset.sum_apply]

end LinearMap

namespace Submodule

section CommSemiring

variable {R : Type u} [CommSemiring R] {j : Type v} {d : Type w}

/-- The amplification of `U`, expressed as the native Pi submodule of its columns. -/
def columnAmplification (U : Submodule R (j → R)) (d : Type w) :
    Submodule R (j × d → R) :=
  (Submodule.pi Set.univ (fun _ : d => U)).comap
    ((LinearEquiv.curry R R d j).toLinearMap.comp
      (LinearMap.funLeft R R (Prod.swap : d × j → j × d)))

@[simp]
theorem mem_columnAmplification {U : Submodule R (j → R)} {x : j × d → R} :
    x ∈ U.columnAmplification d ↔ ∀ a : d, (fun k : j => x (k, a)) ∈ U := by
  simp [columnAmplification]
  rfl

@[simp]
theorem columnAmplification_bot : (⊥ : Submodule R (j → R)).columnAmplification d = ⊥ := by
  ext x
  simp only [mem_columnAmplification, Submodule.mem_bot]
  constructor
  · intro h
    funext p
    exact congrFun (h p.2) p.1
  · intro h
    subst x
    intro a
    rfl

@[simp]
theorem columnAmplification_top : (⊤ : Submodule R (j → R)).columnAmplification d = ⊤ := by
  ext x
  simp

theorem columnInsert_mem_columnAmplification [DecidableEq d]
    {U : Submodule R (j → R)} {x : j → R} (hx : x ∈ U) (a : d) :
    LinearMap.columnInsert a x ∈ U.columnAmplification d := by
  apply mem_columnAmplification.mpr
  intro b
  change LinearMap.funLeft R R (fun k : j => (k, b)) (LinearMap.columnInsert a x) ∈ U
  rw [LinearMap.funLeft_columnInsert]
  split_ifs
  · exact hx
  · exact U.zero_mem

/-- Column insertions generate an amplified subspace. -/
theorem columnAmplification_eq_iSup [Finite d] [DecidableEq d]
    (U : Submodule R (j → R)) :
    U.columnAmplification d = ⨆ a : d, U.map (LinearMap.columnInsert a) := by
  let := Fintype.ofFinite d
  apply le_antisymm
  · intro x hx
    rw [← LinearMap.sum_columnInsert x]
    exact Submodule.sum_mem_iSup fun a =>
      Submodule.mem_map_of_mem ((mem_columnAmplification.mp hx) a)
  · refine iSup_le fun a => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact columnInsert_mem_columnAmplification hx a

/-- The span of the actual projected columns of vectors in `S`. -/
def projectedColumnSpace (S : Submodule R (j × d → R)) : Submodule R (j → R) :=
  ⨆ a : d, S.map (LinearMap.funLeft R R (fun k : j => (k, a)))

theorem column_mem_projectedColumnSpace {S : Submodule R (j × d → R)}
    {x : j × d → R} (hx : x ∈ S) (a : d) :
    (fun k : j => x (k, a)) ∈ S.projectedColumnSpace :=
  Submodule.mem_iSup_of_mem a (Submodule.mem_map_of_mem hx)

theorem le_columnAmplification_projectedColumnSpace (S : Submodule R (j × d → R)) :
    S ≤ S.projectedColumnSpace.columnAmplification d :=
  fun _ hx => mem_columnAmplification.mpr (column_mem_projectedColumnSpace hx)

/-- A nonempty collection of columns recovers the original subspace from its amplification. -/
@[simp]
theorem projectedColumnSpace_columnAmplification [Nonempty d]
    (U : Submodule R (j → R)) : (U.columnAmplification d).projectedColumnSpace = U := by
  classical
  apply le_antisymm
  · refine iSup_le fun a => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_columnAmplification.mp hx a
  · let a : d := Classical.choice ‹Nonempty d›
    intro x hx
    have h := column_mem_projectedColumnSpace (columnInsert_mem_columnAmplification hx a) a
    simpa [LinearMap.columnInsert_apply] using h

/-- An amplified subspace is linearly equivalent to a tuple of its original vectors. -/
def columnAmplificationEquiv (U : Submodule R (j → R)) (d : Type w) :
    U.columnAmplification d ≃ₗ[R] (d → U) where
  toFun x a := ⟨fun k : j => x.1 (k, a), (mem_columnAmplification.mp x.2) a⟩
  invFun x := ⟨fun p : j × d => (x p.2).1 p.1,
    mem_columnAmplification.mpr fun a => (x a).2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext fun _ => Subtype.ext rfl
  map_add' _ _ := by ext a k; rfl
  map_smul' _ _ := by ext a k; rfl

end CommSemiring

section Field

variable {K : Type u} [Field K] {j : Type v} {d : Type w}

/-- Amplification multiplies dimension by the number of block columns. -/
theorem finrank_columnAmplification [Fintype d] (U : Submodule K (j → K))
    [FiniteDimensional K U] :
    Module.finrank K (U.columnAmplification d) = Module.finrank K U * Fintype.card d := by
  rw [(columnAmplificationEquiv U d).finrank_eq, Module.finrank_pi_fintype]
  simp [mul_comm]

end Field

end Submodule

namespace Matrix

section CommSemiring

variable {R : Type u} [CommSemiring R] {i : Type v} {j : Type w} {d : Type z}

/-- The square Kronecker blow-up of a native matrix subspace. -/
def kroneckerBlowup (B : Submodule R (Matrix i j R)) (d : Type z) :
    Submodule R (Matrix (i × d) (j × d) R) :=
  Submodule.map₂ (Matrix.kroneckerBilinear (R := R)) B (⊤ : Submodule R (Matrix d d R))

open scoped Kronecker

theorem kronecker_mem_kroneckerBlowup {B : Submodule R (Matrix i j R)}
    {A : Matrix i j R} (hA : A ∈ B) (T : Matrix d d R) :
    A ⊗ₖ T ∈ kroneckerBlowup B d :=
  Submodule.apply_mem_map₂ (Matrix.kroneckerBilinear (R := R)) hA Submodule.mem_top

@[simp]
theorem kroneckerBlowup_bot : kroneckerBlowup (⊥ : Submodule R (Matrix i j R)) d = ⊥ := by
  simp only [kroneckerBlowup, Submodule.map₂_bot_left]

/-- A product-indexed matrix is the sum of its blocks placed by the native matrix units. -/
theorem eq_sum_kronecker_single_blocks [Fintype d] [DecidableEq d]
    (X : Matrix (i × d) (j × d) R) :
    X = ∑ a : d, ∑ b : d,
      X.submatrix (fun k : i => (k, a)) (fun k : j => (k, b)) ⊗ₖ Matrix.single a b 1 := by
  ext ⟨k, a⟩ ⟨l, b⟩
  simp [Matrix.sum_apply, Matrix.single, ite_and, mul_ite]

/-- Membership in a square blow-up is exactly membership of all its blocks in the base space. -/
theorem mem_kroneckerBlowup_iff [Finite d] {B : Submodule R (Matrix i j R)}
    {X : Matrix (i × d) (j × d) R} :
    X ∈ kroneckerBlowup B d ↔
      ∀ a b : d, X.submatrix (fun k : i => (k, a)) (fun k : j => (k, b)) ∈ B := by
  classical
  let := Fintype.ofFinite d
  constructor
  · intro hX a b
    let P : Matrix (i × d) (j × d) R →ₗ[R] Matrix i j R :=
      (LinearMap.funLeft R R (fun k : j => (k, b))).compLeft i ∘ₗ
        LinearMap.funLeft R (j × d → R) (fun k : i => (k, a))
    have hP : kroneckerBlowup B d ≤ B.comap P := by
      apply Submodule.map₂_le.mpr
      intro A hA T _
      change P (A ⊗ₖ T) ∈ B
      have heq : P (A ⊗ₖ T) = T a b • A := by
        ext k l
        exact mul_comm _ _
      rw [heq]
      exact B.smul_mem _ hA
    exact hP hX
  · intro hX
    rw [eq_sum_kronecker_single_blocks X]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro b _
    exact kronecker_mem_kroneckerBlowup (hX a b) (Matrix.single a b 1)

/-- Matrix-unit Kronecker products generate the entire square blow-up. -/
theorem kroneckerBlowup_eq_iSup [Finite d] [DecidableEq d]
    (B : Submodule R (Matrix i j R)) :
    kroneckerBlowup B d = ⨆ a : d, ⨆ b : d,
      B.map ((Matrix.kroneckerBilinear (R := R)).flip (Matrix.single a b 1)) := by
  let := Fintype.ofFinite d
  apply le_antisymm
  · intro X hX
    rw [eq_sum_kronecker_single_blocks X]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro b _
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
      (Submodule.mem_map_of_mem (mem_kroneckerBlowup_iff.mp hX a b)))
  · refine iSup_le fun a => iSup_le fun b => ?_
    rintro _ ⟨A, hA, rfl⟩
    exact kronecker_mem_kroneckerBlowup hA (Matrix.single a b 1)

/-- A matrix unit selects one actual input column and inserts its image in one output column. -/
theorem kronecker_single_mulVec [Fintype j] [Fintype d] [DecidableEq d]
    (A : Matrix i j R) (a b : d) (x : j × d → R) :
    (A ⊗ₖ Matrix.single a b 1) *ᵥ x =
      LinearMap.columnInsert a (A *ᵥ (fun k : j => x (k, b))) := by
  ext ⟨k, c⟩
  by_cases h : c = a
  · subst c
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.single,
      LinearMap.columnInsert_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single,
      LinearMap.columnInsert_apply, h, Ne.symm h]

/-- Each output column of a block matrix action is the sum of its block actions. -/
theorem mulVec_block_column [Fintype j] [Fintype d]
    (X : Matrix (i × d) (j × d) R) (x : j × d → R) (a : d) :
    (fun k : i => (X *ᵥ x) (k, a)) = ∑ b : d,
      X.submatrix (fun k : i => (k, a)) (fun k : j => (k, b)) *ᵥ
        (fun k : j => x (k, b)) := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.submatrix_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The blow-up image of any vector subspace is the amplification of the base-space image
of its projected-column span. -/
theorem kroneckerBlowup_image [Fintype j] [Fintype d]
    (B : Submodule R (Matrix i j R)) (S : Submodule R (j × d → R)) :
    Submodule.map₂ (Matrix.mulVecBilin R R) (kroneckerBlowup B d) S =
      (Submodule.map₂ (Matrix.mulVecBilin R R) B S.projectedColumnSpace).columnAmplification d := by
  classical
  apply le_antisymm
  · apply Submodule.map₂_le.mpr
    intro X hX x hx
    apply Submodule.mem_columnAmplification.mpr
    intro a
    change (fun k : i => (X *ᵥ x) (k, a)) ∈
      Submodule.map₂ (Matrix.mulVecBilin R R) B S.projectedColumnSpace
    rw [mulVec_block_column]
    apply Submodule.sum_mem
    intro b _
    exact Submodule.apply_mem_map₂ (Matrix.mulVecBilin R R)
      (mem_kroneckerBlowup_iff.mp hX a b) (Submodule.column_mem_projectedColumnSpace hx b)
  · rw [Submodule.columnAmplification_eq_iSup]
    refine iSup_le fun a => ?_
    rw [Submodule.projectedColumnSpace, Submodule.map₂_iSup_right, Submodule.map_iSup]
    refine iSup_le fun b => ?_
    rw [Submodule.map_map₂, Submodule.map₂_map_right]
    apply Submodule.map₂_le.mpr
    intro A hA x hx
    change LinearMap.columnInsert a (A *ᵥ (fun k : j => x (k, b))) ∈
      Submodule.map₂ (Matrix.mulVecBilin R R) (kroneckerBlowup B d) S
    rw [← kronecker_single_mulVec]
    exact Submodule.apply_mem_map₂ (Matrix.mulVecBilin R R)
      (kronecker_mem_kroneckerBlowup hA (Matrix.single a b 1)) hx

/-- Evaluation on an amplified input commutes with the square blow-up, including empty indices. -/
theorem kroneckerBlowup_image_columnAmplification [Fintype j] [Fintype d]
    (B : Submodule R (Matrix i j R)) (U : Submodule R (j → R)) :
    Submodule.map₂ (Matrix.mulVecBilin R R) (kroneckerBlowup B d) (U.columnAmplification d) =
      (Submodule.map₂ (Matrix.mulVecBilin R R) B U).columnAmplification d := by
  cases isEmpty_or_nonempty d with
  | inl h =>
    let := h
    apply Submodule.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  | inr h =>
    let := h
    rw [kroneckerBlowup_image, Submodule.projectedColumnSpace_columnAmplification]

end CommSemiring

end Matrix

namespace Submodule

section CommSemiring

variable {R : Type u} [CommSemiring R] {j : Type v} {d : Type w}
variable [Fintype j] [Fintype d] [DecidableEq j]

/-- Saturation by the full matrix algebra acting through the literal identity Kronecker factor. -/
noncomputable def kroneckerSaturation (S : Submodule R (j × d → R)) :
    Submodule R (j × d → R) :=
  Submodule.map₂ (Matrix.mulVecBilin R R)
    (Matrix.kroneckerBlowup (Submodule.span R {(1 : Matrix j j R)}) d) S

/-- Saturation is exactly amplification of the span of the projected columns. -/
theorem kroneckerSaturation_eq_columnAmplification (S : Submodule R (j × d → R)) :
    S.kroneckerSaturation = S.projectedColumnSpace.columnAmplification d := by
  rw [kroneckerSaturation, Matrix.kroneckerBlowup_image,
    Submodule.map₂_span_singleton_eq_map]
  have hid : Matrix.mulVecBilin R R (1 : Matrix j j R) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact Matrix.one_mulVec x
  rw [hid, Submodule.map_id]

theorem le_kroneckerSaturation (S : Submodule R (j × d → R)) : S ≤ S.kroneckerSaturation := by
  rw [kroneckerSaturation_eq_columnAmplification]
  exact le_columnAmplification_projectedColumnSpace S

/-- An already amplified space is invariant under the full matrix algebra on the block factor. -/
theorem kroneckerSaturation_columnAmplification (U : Submodule R (j → R)) :
    (U.columnAmplification d).kroneckerSaturation = U.columnAmplification d := by
  rw [kroneckerSaturation_eq_columnAmplification]
  cases isEmpty_or_nonempty d with
  | inl h =>
    let := h
    apply Submodule.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  | inr h =>
    let := h
    rw [projectedColumnSpace_columnAmplification]

/-- The invariant subspaces of the full block-factor matrix algebra are precisely amplifications. -/
theorem kroneckerSaturation_eq_self_iff (S : Submodule R (j × d → R)) :
    S.kroneckerSaturation = S ↔ ∃ U : Submodule R (j → R), S = U.columnAmplification d := by
  constructor
  · intro h
    exact ⟨S.projectedColumnSpace, h.symm.trans (kroneckerSaturation_eq_columnAmplification S)⟩
  · rintro ⟨U, rfl⟩
    exact kroneckerSaturation_columnAmplification U

/-- Saturating the domain preserves its entire square-blow-up image. -/
theorem kroneckerBlowup_image_kroneckerSaturation {i : Type z}
    (B : Submodule R (Matrix i j R)) (S : Submodule R (j × d → R)) :
    Submodule.map₂ (Matrix.mulVecBilin R R) (Matrix.kroneckerBlowup B d) S.kroneckerSaturation =
      Submodule.map₂ (Matrix.mulVecBilin R R) (Matrix.kroneckerBlowup B d) S := by
  rw [kroneckerSaturation_eq_columnAmplification,
    Matrix.kroneckerBlowup_image_columnAmplification, Matrix.kroneckerBlowup_image]

end CommSemiring

end Submodule

namespace Matrix

section Field

variable {K : Type u} [Field K] {i : Type v} {j : Type w} {d : Type z}
variable [Finite i] [Fintype j] [Fintype d] [Nonempty d]

/-- A shrunk subspace in a square blow-up descends to its actual projected-column space.
The descended deficiency, multiplied by the block degree, is at least the original deficiency. -/
theorem kroneckerBlowup_shrunkSpace_descent (B : Submodule K (Matrix i j K))
    (S : Submodule K (j × d → K)) {s : ℕ}
    (hS : Module.finrank K (Submodule.map₂ (Matrix.mulVecBilin K K) (kroneckerBlowup B d) S) + s ≤
      Module.finrank K S) :
    let U := S.projectedColumnSpace
    let W := Submodule.map₂ (Matrix.mulVecBilin K K) B U
    Module.finrank K W + (Module.finrank K U - Module.finrank K W) = Module.finrank K U ∧
      s ≤ (Module.finrank K U - Module.finrank K W) * Fintype.card d := by
  let := Fintype.ofFinite i
  let U := S.projectedColumnSpace
  let W := Submodule.map₂ (Matrix.mulVecBilin K K) B U
  change Module.finrank K W + (Module.finrank K U - Module.finrank K W) = Module.finrank K U ∧
    s ≤ (Module.finrank K U - Module.finrank K W) * Fintype.card d
  have himage : Module.finrank K
      (Submodule.map₂ (Matrix.mulVecBilin K K) (kroneckerBlowup B d) S) =
      Module.finrank K W * Fintype.card d := by
    rw [kroneckerBlowup_image, Submodule.finrank_columnAmplification]
  have hdim : Module.finrank K S ≤ Module.finrank K U * Fintype.card d := by
    exact (Submodule.finrank_mono (Submodule.le_columnAmplification_projectedColumnSpace S)).trans_eq
      (Submodule.finrank_columnAmplification U)
  have hmul := hS.trans hdim
  rw [himage] at hmul
  have hle : Module.finrank K W ≤ Module.finrank K U :=
    le_of_mul_le_mul_right
      (show Module.finrank K W * Fintype.card d ≤ Module.finrank K U * Fintype.card d by omega)
      (Fintype.card_pos : 0 < Fintype.card d)
  have heq : Module.finrank K W + (Module.finrank K U - Module.finrank K W) =
      Module.finrank K U := by omega
  have hscale := congrArg (fun n : ℕ => n * Fintype.card d) heq
  rw [add_mul] at hscale
  exact ⟨heq, by omega⟩

end Field

end Matrix
