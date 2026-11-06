/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSpatialWordFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMatrixProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor

/-! # Matrix blocks of local words

The matrix block of a vector is stored as `α I + Σ c v vᵀ` with rational coefficients and
materialized rational vectors.  A local fiber element acts on the matrix block by conjugation
with the matrix of its spatial part (`conwayMatrixAction`); the identity part is fixed and each
rank-one term is carried by the spatial isometry.  Letters are given with a spatial isometry of
the same Conway projection (signs cancel in the matrix action) and an exact rational evaluator
on materialized vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped Matrix BigOperators

/-- The coordinates of a materialized rational vector (zero beyond its length). -/
def vecQ (v : List ℚ) : Fin 24 → ℚ := fun i => v.getD i.val 0

/-- Materialize a rational vector. -/
def matVec (v : Fin 24 → ℚ) : List ℚ := List.ofFn v

/-- Materialization keeps every coordinate. -/
theorem vecQ_matVec (v : Fin 24 → ℚ) : vecQ (matVec v) = v := by
  funext i
  rw [vecQ, matVec, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-- Entries of a list sum of matrices. -/
theorem list_sum_matrix_apply {R : Type} [AddCommMonoid R] (l : List (Matrix (Fin 24) (Fin 24) R))
    (i j : Fin 24) : l.sum i j = (l.map (fun M => M i j)).sum := by
  induction l with
  | nil => rfl
  | cons M l ih => simp only [List.sum_cons, Matrix.add_apply, ih, List.map_cons]

/-- A symmetric rational matrix `scal • 1 + Σ c • v vᵀ`. -/
structure MatRep where
  /-- The multiple of the identity. -/
  scal : ℚ
  /-- Rank-one terms: coefficient and materialized vector. -/
  terms : List (ℚ × List ℚ)

/-- The rational matrix of a matrix block. -/
def MatRep.toMat (A : MatRep) : Matrix (Fin 24) (Fin 24) ℚ :=
  A.scal • (1 : Matrix (Fin 24) (Fin 24) ℚ) +
    (A.terms.map (fun t => t.1 • Matrix.vecMulVec (vecQ t.2) (vecQ t.2))).sum

/-- One entry of a matrix block, by direct evaluation. -/
def MatRep.entry (A : MatRep) (i j : Fin 24) : ℚ :=
  (if i = j then A.scal else 0) +
    (A.terms.map (fun t => t.1 * (vecQ t.2 i * vecQ t.2 j))).sum

/-- The entries of a matrix block. -/
theorem MatRep.toMat_apply (A : MatRep) (i j : Fin 24) : A.toMat i j = A.entry i j := by
  unfold MatRep.toMat MatRep.entry
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  congr 1
  · split_ifs <;> simp
  · rw [list_sum_matrix_apply, List.map_map]
    rfl

/-- Spatial data of local fiber letters: an isometry of the same Conway projection and an exact
rational evaluator on materialized vectors. -/
structure SpatialAlphabet (α : Type) where
  /-- The local fiber element of a letter. -/
  fib : α → localFiberSubgroup
  /-- A spatial isometry of the letter. -/
  sp : α → leechIsomSubgroup
  /-- The isometry has the Conway projection of the letter. -/
  proj : ∀ x, (QuotientGroup.mk (fib x).val.2 : Co1) = QuotientGroup.mk (sp x)
  /-- The rational evaluator of the isometry. -/
  vec : α → List ℚ → List ℚ
  /-- The evaluator computes the isometry exactly. -/
  vec_actual : ∀ x v, (sp x).val (fun i => (vecQ v i : ℝ)) = fun i => (vecQ (vec x v) i : ℝ)

/-- Evaluate the spatial isometry of a word on a materialized vector (the last letter first). -/
def spWordVec {α : Type} (S : SpatialAlphabet α) : List α → List ℚ → List ℚ
  | [], v => v
  | x :: w, v => S.vec x (spWordVec S w v)

/-- The word evaluator computes the product isometry. -/
theorem spWordVec_actual {α : Type} (S : SpatialAlphabet α) (w : List α) (v : List ℚ) :
    ((w.map S.sp).prod).val (fun i => (vecQ v i : ℝ)) =
      fun i => (vecQ (spWordVec S w v) i : ℝ) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change (S.sp x).val (((w.map S.sp).prod).val (fun i => (vecQ v i : ℝ))) = _
    rw [ih, S.vec_actual]
    rfl

/-- The spatial part of a product of fiber letters is the product of their spatial parts. -/
theorem fiber_prod_snd {α : Type} (f : α → localFiberSubgroup) (w : List α) :
    ((w.map f).prod).val.2 = (w.map (fun x => (f x).val.2)).prod := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [List.map_cons, List.prod_cons]
    change (f x).val.2 * ((w.map f).prod).val.2 = _
    rw [ih]

/-- A word acts on matrix blocks through the product of the letters' isometries. -/
theorem SpatialAlphabet.matrixAction_word {α : Type} (S : SpatialAlphabet α) (w : List α) :
    conwayMatrixAction ((w.map S.fib).prod).val.2 = conwayMatrixAction ((w.map S.sp).prod) := by
  apply generatedAxisGlobalMatrixAction_eq_of_projection
  rw [fiber_prod_snd]
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [List.map_cons, List.prod_cons, QuotientGroup.mk_mul, ih, S.proj x]

/-- The conjugate of a rank-one matrix by an isometry. -/
theorem conwayMatrixAction_vecMulVec (e : leechIsomSubgroup) (v : Fin 24 → ℝ) :
    conwayMatrixAction e (Matrix.vecMulVec v v) = Matrix.vecMulVec (e.val v) (e.val v) := by
  rw [conwayMatrixAction_eq_conjugate, ← leechIsomMatrix_mulVec]
  generalize leechIsomMatrix e = M
  ext i j
  rw [Matrix.mul_apply, Matrix.vecMulVec_apply]
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Isometries fix the identity matrix. -/
theorem conwayMatrixAction_one (e : leechIsomSubgroup) :
    conwayMatrixAction e (1 : Matrix (Fin 24) (Fin 24) ℝ) = 1 := by
  rw [conwayMatrixAction_eq_conjugate, Matrix.mul_one]
  exact mul_eq_one_comm.mp (leechIsomMatrix_transpose_mul e)

/-- The action of a word on a matrix block: identity part fixed, rank-one vectors transported. -/
def MatRep.act {α : Type} (S : SpatialAlphabet α) (w : List α) (A : MatRep) : MatRep :=
  ⟨A.scal, A.terms.map (fun t => (t.1, spWordVec S w t.2))⟩

/-- The real cast of a rational matrix. -/
def matR (A : Matrix (Fin 24) (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℝ := A.map (Rat.castHom ℝ)

/-- The real matrix of a block. -/
theorem MatRep.matR_toMat (A : MatRep) :
    matR A.toMat = (A.scal : ℝ) • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
      (A.terms.map (fun t => (t.1 : ℝ) •
        Matrix.vecMulVec (fun i => (vecQ t.2 i : ℝ)) (fun i => (vecQ t.2 i : ℝ)))).sum := by
  ext i j
  rw [matR, Matrix.map_apply, MatRep.toMat_apply, MatRep.entry, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, list_sum_matrix_apply, map_add, Rat.coe_castHom,
    Rat.cast_list_sum, List.map_map, List.map_map]
  congr 1
  · split_ifs <;> simp
  · congr 1
    apply List.map_congr_left
    intro t _
    simp [Matrix.vecMulVec_apply]

/-- The matrix block of a word image is the transported block. -/
theorem MatRep.act_actual {α : Type} (S : SpatialAlphabet α) (w : List α) (A : MatRep) :
    conwayMatrixAction ((w.map S.fib).prod).val.2 (matR A.toMat) = matR (A.act S w).toMat := by
  rw [S.matrixAction_word, MatRep.matR_toMat, MatRep.matR_toMat, map_add, map_smul,
    conwayMatrixAction_one, map_list_sum, List.map_map]
  simp only [MatRep.act, List.map_map]
  congr 2
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, map_smul, conwayMatrixAction_vecMulVec, spWordVec_actual]

/-! ## Letter kinds -/

/-- The rational evaluator of an odd source letter on materialized vectors. -/
def sourceSpatialVec (l : Fin 10) (v : List ℚ) : List ℚ :=
  matVec (generatedAxisGlobalRationalSpatialLetterFast l (vecQ v))

/-- The source evaluator is exact. -/
theorem sourceSpatialVec_actual (l : Fin 10) (v : List ℚ) :
    (generatedAxisGlobalOddSourceSpatialLetter l).val (fun i => (vecQ v i : ℝ)) =
      fun i => (vecQ (sourceSpatialVec l v) i : ℝ) := by
  rw [generatedAxisGlobalRationalSpatialLetterFast_actual, sourceSpatialVec, vecQ_matVec]

/-- Odd source letters have the projection of their spatial letters. -/
theorem sourceSpatial_proj (l : Fin 10) :
    (QuotientGroup.mk (generatedAxisGlobalOddSourceFiberLetter l).val.2 : Co1) =
      QuotientGroup.mk (generatedAxisGlobalOddSourceSpatialLetter l) := by
  have h := generatedAxisGlobalOddSourceSpatialLetter_projection l
  rw [← generatedAxisGlobalOddSourceFiberLetter_local] at h
  exact h

/-- The rational evaluator of a source sign. -/
def signSpatialVec (a : Fin 4096) (v : List ℚ) : List ℚ :=
  matVec (fun i => if (golayEncodedMask a.val).testBit i.val then -vecQ v i else vecQ v i)

/-- The source sign evaluator is exact. -/
theorem signSpatialVec_actual (a : Fin 4096) (v : List ℚ) :
    (golaySignIsometry (sourceGeneratedSignCode a)).val (fun i => (vecQ v i : ℝ)) =
      fun i => (vecQ (signSpatialVec a v) i : ℝ) := by
  funext i
  rw [signSpatialVec, vecQ_matVec]
  change qSign (golayEncoder (golayLabelCoefficients a) i) * (vecQ v i : ℝ) = _
  have h := golayLabelEncoder_match a i
  by_cases hb : (golayEncodedMask a.val).testBit i.val = true
  · have : golayEncoder (golayLabelCoefficients a) i = 1 := by
      apply ZMod.val_injective
      rw [h]
      simp only [hb, ite_true]
      rfl
    simp [this, hb]
  · have : golayEncoder (golayLabelCoefficients a) i = 0 := by
      apply ZMod.val_injective
      rw [h]
      simp [hb]
    simp [this, hb]

/-- The extraspecial letters have trivial spatial part. -/
theorem qSpatial_snd (q : Q) : (localFiberIncl q).val.2 = 1 := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
