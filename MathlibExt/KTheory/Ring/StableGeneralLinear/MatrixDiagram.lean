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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Finite
public import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatMul
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MatrixComp
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockStabilization

/-!
# Stable matrix diagram for `K₁` matrix invariance

For a finite nonempty index type `ι` with `DecidableEq` and `Fintype`,
and a semiring `R`, this file assembles the finite-level equivalences and
`ℕ`-diagrams that underlie `K1 R ≃+ K1 (Matrix ι ι R)`.

* Noncanonical enumerations `equivFinMatrix` (`ι ≃ Fin (card ι)`) and
  `finProdMatrixEquiv` (`Fin n × ι ≃ Fin (n * card ι)`) orient the
  flattening `GLₙ (Matrix ι ι R) ≃* GL_{n*card ι} R`.

* One-step successor layer `finSuccSumEquiv` (`Fin (n+1) ≃ Fin n ⊕ Fin 1`),
  `finSuccProdDecomp` distributing it over `ι`, `oneMulFinCongr`, and
  `castSuccMul` (`n*card+card ≃ (n+1)*card`) orient stabilization as
  `castAdd`/`natAdd` on the outer index and as adding a trailing `card ι`
  block on the flattened side.

* `matrixGLMulEquiv` and `matrixGLIso` give the finite-level multiplicative
  and `GrpCat` flattening via `Matrix.comp` and product reindexing.

* `matrixBlockStabilization` is block stabilization on the flattened side:
  `blockStabilization (n*card) (card)` reindexed along `castSuccMul`.

* `matrixFiniteGLDiagram` (`n ↦ GLₙ (Matrix ι ι R)`) and
  `scaledBaseFiniteGLDiagram` (`n ↦ GL_{n*card} R` via
  `natMulFunctor (card ι)`) are the two `ℕ ⥤ GrpCat` diagrams; the lemma
  `scaledBaseFiniteGLDiagram_map_succ` identifies the successor map of the
  scaled diagram with `matrixBlockStabilization`.

Both the index type and the ring live in the same universe `u`
(`ι : Type u`, `R : Type u`); diagrams live in `GrpCat.{u}` and
`SemiRingCat.{u}`.

Public API kept for downstream matrix files: `equivFinMatrix`,
`prodEquivFin`, `finProdMatrixEquiv`, `finSuccSumEquiv`, `finSuccProdDecomp`,
`oneMulFinCongr`, `castSuccMul`, `finProdMatrixEquiv_val`,
`finSuccProdDecomp_symm_*`, `matrixGLMulEquiv`, `matrixGLIso`,
`matrixBlockStabilization`, `matrixFiniteGLDiagram`,
`scaledBaseFiniteGLDiagram`, and `scaledBaseFiniteGLDiagram_map_succ`.
Same-file-only helpers `finSuccSumEquiv_symm_apply_castAdd`,
`finSuccSumEquiv_symm_apply_natAdd`, `finiteGLDiagram_obj_map_le_add`,
and `eqToHom_GrpCat_finCongr` are private.
-/

@[expose] public section

open CategoryTheory Matrix

universe u

namespace AlgebraicKTheory
namespace MatrixDiagram

variable {ι : Type u} [DecidableEq ι] [Fintype ι]

/-- Noncanonical equivalence `ι ≃ Fin (Fintype.card ι)` via `Fintype.equivFin`.
Used to orient the flattening `Fin n × ι ≃ Fin (n * card ι)`. -/
noncomputable def equivFinMatrix : ι ≃ Fin (Fintype.card ι) :=
  Fintype.equivFin ι

/-- Product reindexing `Fin n × ι ≃ Fin n × Fin (card ι)` via `equivFinMatrix` on the
second factor; `finProdMatrixEquiv` and `matrixGLMulEquiv` unfold through this. -/
noncomputable def prodEquivFin (n : ℕ) :
    Fin n × ι ≃ Fin n × Fin (Fintype.card ι) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) equivFinMatrix

/-- Product flattening `Fin n × ι ≃ Fin (n * Fintype.card ι)` via
`prodEquivFin` followed by `finProdFinEquiv`. Outer `Fin n` varies slowest;
`ι` enumeration is noncanonical. -/
noncomputable def finProdMatrixEquiv (n : ℕ) :
    Fin n × ι ≃ Fin (n * Fintype.card ι) :=
  (prodEquivFin (ι := ι) n).trans finProdFinEquiv

-- Finite-index helper layer for one successor stabilization step.

omit [DecidableEq ι] [Fintype ι] in
/-- Successor decomposition `Fin (n+1) ≃ Fin n ⊕ Fin 1`, noncanonical choice
orienting stabilization as `castAdd` on the left summand and `natAdd` on the right. -/
noncomputable def finSuccSumEquiv (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Fin 1 :=
  (finSumFinEquiv (m := n) (n := 1)).symm

omit [DecidableEq ι] [Fintype ι] in
/-- Successor product decomposition
`Fin (n+1) × ι ≃ (Fin n × ι) ⊕ (Fin 1 × ι)` via `finSuccSumEquiv` distributed
over `ι`. -/
noncomputable def finSuccProdDecomp (n : ℕ) :
    Fin (n + 1) × ι ≃ (Fin n × ι) ⊕ (Fin 1 × ι) :=
  (Equiv.prodCongr (finSuccSumEquiv n) (Equiv.refl ι)).trans
    (Equiv.sumProdDistrib (Fin n) (Fin 1) ι)

omit [DecidableEq ι] [Fintype ι] in
/-- `Fin (1 * m) ≃ Fin m` via `Nat.one_mul`. -/
noncomputable def oneMulFinCongr (m : ℕ) : Fin (1 * m) ≃ Fin m :=
  finCongr (Nat.one_mul m)

omit [DecidableEq ι] in
/-- `Fin (n * card ι + card ι) ≃ Fin ((n+1) * card ι)` via `Nat.succ_mul`,
oriented to move the trailing block into the successor size. -/
noncomputable def castSuccMul (n : ℕ) :
    Fin (n * Fintype.card ι + Fintype.card ι) ≃ Fin ((n + 1) * Fintype.card ι) :=
  finCongr (Nat.succ_mul n (Fintype.card ι)).symm

omit [DecidableEq ι] [Fintype ι] in
@[simp]
private lemma finSuccSumEquiv_symm_apply_castAdd (n : ℕ) (i : Fin n) :
    (finSuccSumEquiv n).symm (Sum.inl i) = Fin.castAdd 1 i := by
  simp only [finSuccSumEquiv, Equiv.symm_symm, finSumFinEquiv_apply_left]

omit [DecidableEq ι] [Fintype ι] in
@[simp]
private lemma finSuccSumEquiv_symm_apply_natAdd (n : ℕ) (j : Fin 1) :
    (finSuccSumEquiv n).symm (Sum.inr j) = Fin.natAdd n j := by
  simp only [finSuccSumEquiv, Equiv.symm_symm, finSumFinEquiv_apply_right]

omit [DecidableEq ι] in
/-- Value formula for `finProdMatrixEquiv`: `val` equals
`equivFinMatrix x` offset by `card ι * a.val`; outer index is most significant. -/
lemma finProdMatrixEquiv_val (n : ℕ) (a : Fin n) (x : ι) :
    (finProdMatrixEquiv (ι := ι) n (a, x)).val =
      (equivFinMatrix x).val + Fintype.card ι * a.val := rfl

omit [DecidableEq ι] [Fintype ι] in
/-- Inverse of `finSuccProdDecomp` on `inl` is `castAdd` on the outer `Fin`.
Preserved for downstream successor equivalences. -/
lemma finSuccProdDecomp_symm_apply_inl (n : ℕ) (p : Fin n × ι) :
    (finSuccProdDecomp (ι := ι) n).symm (Sum.inl p) =
      (Fin.castAdd 1 p.1, p.2) := by
  cases p with
  | mk i x =>
    calc (finSuccProdDecomp (ι := ι) n).symm (Sum.inl (i, x))
        = (Equiv.prodCongr (finSuccSumEquiv n) (Equiv.refl ι)).symm
            ((Equiv.sumProdDistrib (Fin n) (Fin 1) ι).symm (Sum.inl (i, x))) := by
          simp only [finSuccProdDecomp, Equiv.symm_trans, Equiv.trans_apply]
      _ = (Equiv.prodCongr (finSuccSumEquiv n) (Equiv.refl ι)).symm (Sum.inl i, x) := by
          rw [Equiv.sumProdDistrib_symm_apply_left]
      _ = (Fin.castAdd 1 i, x) := by
          have h : (finSuccSumEquiv n).symm (Sum.inl i) = Fin.castAdd 1 i :=
            finSuccSumEquiv_symm_apply_castAdd n i
          calc (Equiv.prodCongr (finSuccSumEquiv n) (Equiv.refl ι)).symm (Sum.inl i, x)
              = ((finSuccSumEquiv n).symm (Sum.inl i), (Equiv.refl ι).symm x) := rfl
            _ = (Fin.castAdd 1 i, x) := by
              simp only [h, Equiv.refl_symm, Equiv.refl_apply]

omit [DecidableEq ι] [Fintype ι] in
/-- Inverse of `finSuccProdDecomp` on `inr` is `natAdd` on the outer `Fin`.
Preserved for downstream successor equivalences. -/
lemma finSuccProdDecomp_symm_apply_inr (n : ℕ) (p : Fin 1 × ι) :
    (finSuccProdDecomp (ι := ι) n).symm (Sum.inr p) =
      (Fin.natAdd n p.1, p.2) := by
  cases p with
  | mk j x =>
    calc (finSuccProdDecomp (ι := ι) n).symm (Sum.inr (j, x))
        = (Equiv.prodCongr (finSuccSumEquiv n) (Equiv.refl ι)).symm
            ((Equiv.sumProdDistrib (Fin n) (Fin 1) ι).symm (Sum.inr (j, x))) := by
          simp only [finSuccProdDecomp, Equiv.symm_trans, Equiv.trans_apply]
      _ = (Equiv.prodCongr (finSuccSumEquiv n) (Equiv.refl ι)).symm (Sum.inr j, x) := by
          rw [Equiv.sumProdDistrib_symm_apply_right]
      _ = (Fin.natAdd n j, x) := by
          have h : (finSuccSumEquiv n).symm (Sum.inr j) = Fin.natAdd n j :=
            finSuccSumEquiv_symm_apply_natAdd n j
          calc (Equiv.prodCongr (finSuccSumEquiv n) (Equiv.refl ι)).symm (Sum.inr j, x)
              = ((finSuccSumEquiv n).symm (Sum.inr j), (Equiv.refl ι).symm x) := rfl
            _ = (Fin.natAdd n j, x) := by
              simp only [h, Equiv.refl_symm, Equiv.refl_apply]

variable (R : Type u) [Semiring R]

/-- Finite-level flattening `GLₙ (Matrix ι ι R) ≃* GL_{n * card ι} R`
via `Matrix.comp` and product reindexing. -/
noncomputable def matrixGLMulEquiv (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (Matrix ι ι R) ≃*
      Matrix.GeneralLinearGroup (Fin (n * Fintype.card ι)) R :=
  (Matrix.GeneralLinearGroup.compMulEquiv (Fin n) ι R).trans
    ((Matrix.GeneralLinearGroup.reindexMulEquiv (prodEquivFin (ι := ι) n)).trans
      (Matrix.GeneralLinearGroup.reindexMulEquiv finProdFinEquiv))

/-- `GrpCat` isomorphism flattening `GLₙ (Matrix ι ι R)` to `GL_{n*card ι} R`.
Both sides are in `GrpCat.{u}`; `toGrpIso` of `matrixGLMulEquiv`. -/
noncomputable def matrixGLIso (n : ℕ) :
    GrpCat.of (Matrix.GeneralLinearGroup (Fin n) (Matrix ι ι R)) ≅
      GrpCat.of (Matrix.GeneralLinearGroup (Fin (n * Fintype.card ι)) R) :=
  (matrixGLMulEquiv (R := R) (ι := ι) n).toGrpIso

variable [Nonempty ι]

/-- Block stabilization on the flattened side: `GL_{n*card} R →* GL_{(n+1)*card} R`
via `blockStabilization (n*card) (card)` reindexed along `castSuccMul`. -/
noncomputable def matrixBlockStabilization (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin (n * Fintype.card ι)) R →*
      Matrix.GeneralLinearGroup (Fin ((n + 1) * Fintype.card ι)) R :=
  (Matrix.GeneralLinearGroup.reindexMulEquiv (castSuccMul (ι := ι) n)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.blockStabilization (n * Fintype.card ι) (Fintype.card ι) R)

private lemma finiteGLDiagram_obj_map_le_add (n m : ℕ) :
    (finiteGLDiagram.obj (SemiRingCat.of R)).map
        (homOfLE (Nat.le_add_right n m)) =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.blockStabilization n m R) := by
  induction m with
  | zero =>
    have h0 : n + 0 = n := rfl
    have hle : n ≤ n + 0 := by rw [h0]
    have hhom : homOfLE (Nat.le_add_right n 0) = homOfLE hle := by
      apply Subsingleton.elim
    rw [hhom]
    have h_eq : homOfLE hle = 𝟙 n := by
      apply Subsingleton.elim
    rw [h_eq]
    simp only [CategoryTheory.Functor.map_id]
    have hblock : Matrix.GeneralLinearGroup.blockStabilization n 0 R = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro g
      exact Matrix.GeneralLinearGroup.blockStabilization_zero n R g
    rw [hblock]
    rfl
  | succ m ih =>
    have h_add : n + (m + 1) = (n + m) + 1 := rfl
    have hle1 : n ≤ n + m := Nat.le_add_right n m
    have hle2 : n + m ≤ (n + m) + 1 := Nat.le_add_right (n + m) 1
    have hle3 : n ≤ n + (m + 1) := Nat.le_add_right n (m + 1)
    have hcomp : homOfLE hle3 = homOfLE hle1 ≫ homOfLE hle2 := by
      apply Subsingleton.elim
    rw [hcomp]
    rw [CategoryTheory.Functor.map_comp]
    rw [ih]
    have hsucc : (finiteGLDiagram.obj (SemiRingCat.of R)).map
        (homOfLE (Nat.le_add_right (n + m) 1)) =
        GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization R) :=
      finiteGLDiagram_obj_map_succ (R := SemiRingCat.of R) (n + m)
    rw [hsucc]
    have hstab_eq : Matrix.GeneralLinearGroup.stabilization (R := R) (n := n + m) =
        Matrix.GeneralLinearGroup.blockStabilization (n + m) 1 R := rfl
    rw [hstab_eq]
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact (Matrix.GeneralLinearGroup.blockStabilization_succ n m R g).symm

private lemma eqToHom_GrpCat_finCongr {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (fun m => GrpCat.of (Matrix.GeneralLinearGroup (Fin m) R)) h) =
      GrpCat.ofHom
        (Matrix.GeneralLinearGroup.reindexMulEquiv (finCongr h)).toMonoidHom := by
  cases h
  rfl

/-- `ℕ`-diagram `n ↦ GLₙ (Matrix ι ι R)` in `GrpCat.{u}`; objectwise
`Finite` diagram at `Matrix ι ι R`. -/
noncomputable def matrixFiniteGLDiagram : ℕ ⥤ GrpCat.{u} :=
  finiteGLDiagram.obj (SemiRingCat.of (Matrix ι ι R))

/-- Scaled diagram `n ↦ GL_{n * card ι} R` obtained by `natMulFunctor (card ι)`
composed with the base `R` diagram. Lives in `GrpCat.{u}`. -/
noncomputable def scaledBaseFiniteGLDiagram : ℕ ⥤ GrpCat.{u} :=
  (GrpCat.FilteredColimits.natMulFunctor (Fintype.card ι)).comp
    (finiteGLDiagram.obj (SemiRingCat.of R))

omit [DecidableEq ι] [Nonempty ι] in
/-- Successor map of `scaledBaseFiniteGLDiagram` equals `matrixBlockStabilization`:
the scaled colimit's `n → n+1` step adds a trailing `card ι` block. -/
lemma scaledBaseFiniteGLDiagram_map_succ (n : ℕ) :
    (scaledBaseFiniteGLDiagram (R := R) (ι := ι)).map (homOfLE (Nat.le_add_right n 1)) =
      GrpCat.ofHom (matrixBlockStabilization (R := R) (ι := ι) n) := by
  have hk_eq : n * Fintype.card ι + Fintype.card ι = (n + 1) * Fintype.card ι :=
    (Nat.succ_mul n (Fintype.card ι)).symm
  have h_le : n * Fintype.card ι ≤ (n + 1) * Fintype.card ι :=
    Nat.mul_le_mul_right _ (Nat.le_add_right n 1)
  have h_le' : n * Fintype.card ι ≤ n * Fintype.card ι + Fintype.card ι :=
    Nat.le_add_right _ _
  have h_scaled : (scaledBaseFiniteGLDiagram (R := R) (ι := ι)).map
      (homOfLE (Nat.le_add_right n 1)) =
      (finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE h_le) := rfl
  rw [h_scaled]
  have h_hom_eq : homOfLE h_le = homOfLE h_le' ≫ eqToHom hk_eq := by
    apply Subsingleton.elim
  have h_base_comp : (finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE h_le) =
      (finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE h_le') ≫
        (finiteGLDiagram.obj (SemiRingCat.of R)).map (eqToHom hk_eq) := by
    rw [h_hom_eq, Functor.map_comp]
  rw [h_base_comp]
  have h_block : (finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE h_le') =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.blockStabilization
        (n * Fintype.card ι) (Fintype.card ι) R) := by
    have h_eq : homOfLE h_le' =
        homOfLE (Nat.le_add_right (n * Fintype.card ι) (Fintype.card ι)) := by
      apply Subsingleton.elim
    rw [h_eq]
    exact finiteGLDiagram_obj_map_le_add (R := R) (n := n * Fintype.card ι)
      (m := Fintype.card ι)
  have h_eqToHom : (finiteGLDiagram.obj (SemiRingCat.of R)).map (eqToHom hk_eq) =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.reindexMulEquiv
        (finCongr hk_eq)).toMonoidHom := by
    have h1 : (finiteGLDiagram.obj (SemiRingCat.of R)).map (eqToHom hk_eq) =
        eqToHom (congrArg (finiteGLDiagram.obj (SemiRingCat.of R)).obj hk_eq) :=
      eqToHom_map _ _
    have h2 : congrArg (finiteGLDiagram.obj (SemiRingCat.of R)).obj hk_eq =
        congrArg (fun m => GrpCat.of (Matrix.GeneralLinearGroup (Fin m) R)) hk_eq := rfl
    rw [h1, h2]
    exact eqToHom_GrpCat_finCongr (R := R) hk_eq
  rw [h_block, h_eqToHom]
  have h_cast : finCongr hk_eq = castSuccMul (ι := ι) n := by
    simp only [castSuccMul]
  calc GrpCat.ofHom (Matrix.GeneralLinearGroup.blockStabilization
          (n * Fintype.card ι) (Fintype.card ι) R) ≫
        GrpCat.ofHom (Matrix.GeneralLinearGroup.reindexMulEquiv
          (finCongr hk_eq)).toMonoidHom
      = GrpCat.ofHom (Matrix.GeneralLinearGroup.blockStabilization
            (n * Fintype.card ι) (Fintype.card ι) R) ≫
          GrpCat.ofHom (Matrix.GeneralLinearGroup.reindexMulEquiv
            (castSuccMul (ι := ι) n)).toMonoidHom := by
        rw [h_cast]
    _ = GrpCat.ofHom (matrixBlockStabilization (R := R) (ι := ι) n) := by
        simp only [matrixBlockStabilization]
        rw [← GrpCat.ofHom_comp]

end MatrixDiagram
end AlgebraicKTheory

end
