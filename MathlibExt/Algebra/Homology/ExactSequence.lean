/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import MathlibExt.CategoryTheory.ComposableArrows.Opposite

/-!
# Opposites of complex composable arrows

This file shows that the canonical opposite of a complex remains a complex.
-/

@[expose] public section

namespace CategoryTheory.ComposableArrows

universe v u

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
private lemma rev_obj_eq {n : ℕ} (i : ℕ) (hi : i ≤ n) :
    (Fin.rev (⟨i, by omega⟩ : Fin (n + 1)) : Fin (n + 1)) = ⟨n - i, by omega⟩ := by
  ext
  simp [Fin.val_rev]

set_option backward.isDefEq.respectTransparency false in
private lemma op_obj_eq {n : ℕ} (S : ComposableArrows C n) (i : ℕ) (hi : i ≤ n) :
    S.op.obj ⟨i, by omega⟩ = Opposite.op (S.obj ⟨n - i, by omega⟩) := by
  rw [op_obj, rev_obj_eq i hi]

set_option backward.isDefEq.respectTransparency false in
private lemma op_map'_eq {n : ℕ} (S : ComposableArrows C n) (i : ℕ) (hi : i + 1 ≤ n) :
    S.op.map' i (i + 1) =
      eqToHom (op_obj_eq S i (by omega)) ≫ (S.map' (n - i - 1) (n - i)).op ≫
        eqToHom (op_obj_eq S (i + 1) (by omega)).symm := by
  have h_le : (⟨i, by omega⟩ : Fin (n + 1)) ≤ ⟨i + 1, by omega⟩ := by simp
  have h_rev_le : (Fin.rev (⟨i + 1, by omega⟩ : Fin (n + 1)) : Fin (n + 1)) ≤
      Fin.rev (⟨i, by omega⟩ : Fin (n + 1)) :=
    Fin.rev_le_rev.mpr h_le
  have h_op : S.op.map (homOfLE h_le) = (S.map (homOfLE h_rev_le)).op := by
    have := S.op_map (homOfLE h_le)
    exact this
  have h1 : (Fin.rev (⟨i + 1, by omega⟩ : Fin (n + 1)) : Fin (n + 1)) = ⟨n - i - 1, by omega⟩ :=
    rev_obj_eq (i + 1) (by omega)
  have h2 : (Fin.rev (⟨i, by omega⟩ : Fin (n + 1)) : Fin (n + 1)) = ⟨n - i, by omega⟩ :=
    rev_obj_eq i (by omega)
  have h_map : S.map (homOfLE h_rev_le) =
      eqToHom (congrArg S.obj h1) ≫ S.map' (n - i - 1) (n - i) ≫
        eqToHom (congrArg S.obj h2).symm := by
    have h_eq : homOfLE h_rev_le =
        (eqToHom h1 ≫ homOfLE (by omega : (⟨n - i - 1,
              Nat.lt_succ_of_le (Nat.sub_le n (i + 1))⟩ : Fin (n + 1)) ≤
          ⟨n - i, Nat.lt_succ_of_le (Nat.sub_le n i)⟩) ≫ eqToHom h2.symm) := by
      apply Subsingleton.elim
    rw [h_eq]
    simp only [Functor.map_comp, eqToHom_map]
  rw [show S.op.map' i (i + 1) = S.op.map (homOfLE h_le) from rfl]
  rw [h_op, h_map]
  simp [eqToHom_op]

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
lemma IsComplex.op {n : ℕ} {S : ComposableArrows C n} (h : S.IsComplex) :
    S.op.IsComplex where
  zero i hi := by
    have ha : (n - i - 2) + 1 = n - i - 1 := by omega
    have hb : (n - i - 1) + 1 = n - i := by omega
    have hc : n - i ≤ n := by omega
    let T := S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)
    have h1 : S.op.map' i (i + 1) =
        eqToHom (op_obj_eq S i (by omega)) ≫ (S.map' (n - i - 1) (n - i)).op ≫
          eqToHom (op_obj_eq S (i + 1) (by omega)).symm :=
      op_map'_eq S i (by omega)
    have h2 : S.op.map' (i + 1) (i + 2) =
        eqToHom (op_obj_eq S (i + 1) (by omega)) ≫ (S.map' (n - i - 2) (n - i - 1)).op ≫
          eqToHom (op_obj_eq S (i + 2) (by omega)).symm := by
      have h := op_map'_eq S (i + 1) (by omega)
      simpa [show n - (i + 1) - 1 = n - i - 2 from by omega,
             show n - (i + 1) = n - i - 1 from by omega,
             show i + 1 + 1 = i + 2 from by omega] using h
    have hT : T.op.f ≫ T.op.g = 0 := T.op.zero
    have hf : T.op.f = (S.map' (n - i - 1) (n - i)).op := rfl
    have hg : T.op.g = (S.map' (n - i - 2) (n - i - 1)).op := rfl
    have hT' : (S.map' (n - i - 1) (n - i)).op ≫ (S.map' (n - i - 2) (n - i - 1)).op = 0 := by
      rw [← hf, ← hg]
      exact hT
    calc S.op.map' i (i + 1) ≫ S.op.map' (i + 1) (i + 2)
        = (eqToHom (op_obj_eq S i (by omega)) ≫ (S.map' (n - i - 1) (n - i)).op ≫
            eqToHom (op_obj_eq S (i + 1) (by omega)).symm) ≫
          (eqToHom (op_obj_eq S (i + 1) (by omega)) ≫ (S.map' (n - i - 2) (n - i - 1)).op ≫
            eqToHom (op_obj_eq S (i + 2) (by omega)).symm) := by
          rw [h1, h2]
      _ = eqToHom (op_obj_eq S i (by omega)) ≫
            ((S.map' (n - i - 1) (n - i)).op ≫ (S.map' (n - i - 2) (n - i - 1)).op) ≫
            eqToHom (op_obj_eq S (i + 2) (by omega)).symm := by
          simp only [Category.assoc]
          simp
      _ = eqToHom (op_obj_eq S i (by omega)) ≫ (0 : _ ⟶ _) ≫
            eqToHom (op_obj_eq S (i + 2) (by omega)).symm := by
          rw [hT']
      _ = 0 := by
          simp

set_option backward.isDefEq.respectTransparency false in
private lemma unop_obj_eq {n : ℕ} (S : ComposableArrows Cᵒᵖ n) (i : ℕ) (hi : i ≤ n) :
    S.unop.obj ⟨i, by omega⟩ = Opposite.unop (S.obj ⟨n - i, by omega⟩) := by
  rw [unop_obj, rev_obj_eq i hi]

set_option backward.isDefEq.respectTransparency false in
private lemma unop_map'_eq {n : ℕ} (S : ComposableArrows Cᵒᵖ n) (i : ℕ) (hi : i + 1 ≤ n) :
    S.unop.map' i (i + 1) =
      eqToHom (unop_obj_eq S i (by omega)) ≫ (S.map' (n - i - 1) (n - i)).unop ≫
        eqToHom (unop_obj_eq S (i + 1) (by omega)).symm := by
  have h_le : (⟨i, by omega⟩ : Fin (n + 1)) ≤ ⟨i + 1, by omega⟩ := by simp
  have h_rev_le : (Fin.rev (⟨i + 1, by omega⟩ : Fin (n + 1)) : Fin (n + 1)) ≤
      Fin.rev (⟨i, by omega⟩ : Fin (n + 1)) :=
    Fin.rev_le_rev.mpr h_le
  have h_unop : S.unop.map (homOfLE h_le) = (S.map (homOfLE h_rev_le)).unop := by
    have := S.unop_map (homOfLE h_le)
    exact this
  have h1 : (Fin.rev (⟨i + 1, by omega⟩ : Fin (n + 1)) : Fin (n + 1)) = ⟨n - i - 1, by omega⟩ :=
    rev_obj_eq (i + 1) (by omega)
  have h2 : (Fin.rev (⟨i, by omega⟩ : Fin (n + 1)) : Fin (n + 1)) = ⟨n - i, by omega⟩ :=
    rev_obj_eq i (by omega)
  have h_map : S.map (homOfLE h_rev_le) =
      eqToHom (congrArg S.obj h1) ≫ S.map' (n - i - 1) (n - i) ≫
        eqToHom (congrArg S.obj h2).symm := by
    have h_eq : homOfLE h_rev_le =
        (eqToHom h1 ≫ homOfLE (by omega : (⟨n - i - 1,
              Nat.lt_succ_of_le (Nat.sub_le n (i + 1))⟩ : Fin (n + 1)) ≤
          ⟨n - i, Nat.lt_succ_of_le (Nat.sub_le n i)⟩) ≫ eqToHom h2.symm) := by
      apply Subsingleton.elim
    rw [h_eq]
    simp only [Functor.map_comp, eqToHom_map]
  rw [show S.unop.map' i (i + 1) = S.unop.map (homOfLE h_le) from rfl]
  rw [h_unop, h_map]
  simp [eqToHom_unop]

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
/-- The unopposite of a complex in `Cᵒᵖ` is a complex in `C`. -/
lemma IsComplex.unop {n : ℕ} {S : ComposableArrows Cᵒᵖ n}
    (h : S.IsComplex) : S.unop.IsComplex where
  zero i hi := by
    have h1 : S.unop.map' i (i + 1) =
        eqToHom (unop_obj_eq S i (by omega)) ≫ (S.map' (n - i - 1) (n - i)).unop ≫
          eqToHom (unop_obj_eq S (i + 1) (by omega)).symm :=
      unop_map'_eq S i (by omega)
    have h2 : S.unop.map' (i + 1) (i + 2) =
        eqToHom (unop_obj_eq S (i + 1) (by omega)) ≫ (S.map' (n - i - 2) (n - i - 1)).unop ≫
          eqToHom (unop_obj_eq S (i + 2) (by omega)).symm := by
      have h := unop_map'_eq S (i + 1) (by omega)
      simpa [show n - (i + 1) - 1 = n - i - 2 from by omega,
             show n - (i + 1) = n - i - 1 from by omega,
             show i + 1 + 1 = i + 2 from by omega] using h
    have h0 : S.map' (n - i - 2) (n - i - 1) ≫ S.map' (n - i - 1) (n - i) = 0 :=
      h.zero' (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)
    have h0' : (S.map' (n - i - 1) (n - i)).unop ≫ (S.map' (n - i - 2) (n - i - 1)).unop = 0 := by
      have h0_unop := congrArg Quiver.Hom.unop h0
      simpa using h0_unop
    calc S.unop.map' i (i + 1) ≫ S.unop.map' (i + 1) (i + 2)
        = (eqToHom (unop_obj_eq S i (by omega)) ≫ (S.map' (n - i - 1) (n - i)).unop ≫
            eqToHom (unop_obj_eq S (i + 1) (by omega)).symm) ≫
          (eqToHom (unop_obj_eq S (i + 1) (by omega)) ≫ (S.map' (n - i - 2) (n - i - 1)).unop ≫
            eqToHom (unop_obj_eq S (i + 2) (by omega)).symm) := by
          rw [h1, h2]
      _ = eqToHom (unop_obj_eq S i (by omega)) ≫
            ((S.map' (n - i - 1) (n - i)).unop ≫ (S.map' (n - i - 2) (n - i - 1)).unop) ≫
            eqToHom (unop_obj_eq S (i + 2) (by omega)).symm := by
          simp only [Category.assoc]
          simp
      _ = eqToHom (unop_obj_eq S i (by omega)) ≫ (0 : _ ⟶ _) ≫
            eqToHom (unop_obj_eq S (i + 2) (by omega)).symm := by
          rw [h0']
      _ = 0 := by
          simp

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
/-- A composable arrow is a complex iff its opposite is. -/
@[simp]
lemma isComplex_op_iff {n : ℕ} (S : ComposableArrows C n) :
    S.op.IsComplex ↔ S.IsComplex where
  mp h := isComplex_of_iso (opUnop S) h.unop
  mpr h := h.op

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
/-- A composable arrow in `Cᵒᵖ` is a complex iff its unopposite is. -/
@[simp]
lemma isComplex_unop_iff {n : ℕ} (S : ComposableArrows Cᵒᵖ n) :
    S.unop.IsComplex ↔ S.IsComplex where
  mp h := isComplex_of_iso (unopOp S) h.op
  mpr h := h.unop

set_option backward.isDefEq.respectTransparency false in
private noncomputable def opScIso {n : ℕ} [CategoryTheory.Limits.HasZeroMorphisms C]
    (S : ComposableArrows C n) (h : S.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n) :
    (S.op.sc (h.op) i hi) ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).op :=
  let e₁ : (S.op.sc (h.op) i hi).X₁ ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).op.X₁ :=
    eqToIso (by
      have h₁ : (S.op.sc (h.op) i hi).X₁ = S.op.obj ⟨i, by omega⟩ := rfl
      have h₂ : (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).op.X₁ =
          Opposite.op (S.obj ⟨n - i, by omega⟩) := by dsimp [ShortComplex.op]
      rw [h₁, h₂]
      exact op_obj_eq S i (by omega))
  let e₂ : (S.op.sc (h.op) i hi).X₂ ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).op.X₂ :=
    eqToIso (by
      have h₁ : (S.op.sc (h.op) i hi).X₂ = S.op.obj ⟨i + 1, by omega⟩ := rfl
      have h₂ : (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).op.X₂ =
          Opposite.op (S.obj ⟨n - i - 1, by omega⟩) := by dsimp [ShortComplex.op]
      have h : (⟨n - (i + 1), by omega⟩ : Fin (n + 1)) = ⟨n - i - 1, by omega⟩ := by
        apply Fin.ext; simp; omega
      rw [h₁, h₂, op_obj_eq S (i + 1) (by omega), congrArg (fun f => Opposite.op (S.obj f)) h])
  let e₃ : (S.op.sc (h.op) i hi).X₃ ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).op.X₃ :=
    eqToIso (by
      have h₁ : (S.op.sc (h.op) i hi).X₃ = S.op.obj ⟨i + 2, by omega⟩ := rfl
      have h₂ : (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).op.X₃ =
          Opposite.op (S.obj ⟨n - i - 2, by omega⟩) := by dsimp [ShortComplex.op]
      have h : (⟨n - (i + 2), by omega⟩ : Fin (n + 1)) = ⟨n - i - 2, by omega⟩ := by
        apply Fin.ext; simp; omega
      rw [h₁, h₂, op_obj_eq S (i + 2) (by omega), congrArg (fun f => Opposite.op (S.obj f)) h])
  ShortComplex.isoMk e₁ e₂ e₃
    (by
      have h1 := op_map'_eq S i (by omega)
      simp only [e₁, e₂, h1, Category.assoc]
      simp)
    (by
      have h2 := op_map'_eq S (i + 1) (by omega)
      have h2' : S.op.map' (i + 1) (i + 2) =
          eqToHom (op_obj_eq S (i + 1) (by omega)) ≫
            (S.map' (n - i - 2) (n - i - 1)).op ≫
              eqToHom (op_obj_eq S (i + 2) (by omega)).symm := by
        simpa [show n - (i + 1) - 1 = n - i - 2 from by omega,
               show n - (i + 1) = n - i - 1 from by omega,
               show i + 1 + 1 = i + 2 from by omega] using h2
      simp only [e₂, e₃, h2', Category.assoc]
      simp)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def unopScIso {n : ℕ} [CategoryTheory.Limits.HasZeroMorphisms C]
    (S : ComposableArrows Cᵒᵖ n) (h : S.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n) :
    (S.unop.sc (h.unop) i hi) ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop :=
  let e₁ : (S.unop.sc (h.unop) i hi).X₁ ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₁ :=
    eqToIso (show (S.unop.sc (h.unop) i hi).X₁ =
        (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₁ from by
      have h1 : (S.unop.sc (h.unop) i hi).X₁ = S.unop.obj ⟨i, by omega⟩ := rfl
      have h2 : S.unop.obj ⟨i, by omega⟩ = Opposite.unop (S.obj ⟨n - i, by omega⟩) :=
        unop_obj_eq S i (by omega)
      have h3 : S.obj ⟨n - i, by omega⟩ =
          (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).X₃ := rfl
      have h4 : Opposite.unop
          ((S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).X₃) =
          (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₁ := by
        dsimp [ShortComplex.unop]
      rw [h1, h2, congrArg Opposite.unop h3, h4])
  let e₂ : (S.unop.sc (h.unop) i hi).X₂ ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₂ :=
    eqToIso (show (S.unop.sc (h.unop) i hi).X₂ =
        (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₂ from by
      have h1 : (S.unop.sc (h.unop) i hi).X₂ = S.unop.obj ⟨i + 1, by omega⟩ := rfl
      have h2 : S.unop.obj ⟨i + 1, by omega⟩ = Opposite.unop (S.obj ⟨n - (i + 1), by omega⟩) :=
        unop_obj_eq S (i + 1) (by omega)
      have h3 : (⟨n - (i + 1), by omega⟩ : Fin (n + 1)) = ⟨n - i - 1, by omega⟩ := by
        apply Fin.ext; simp; omega
      have h4 : S.obj ⟨n - (i + 1), by omega⟩ = S.obj ⟨n - i - 1, by omega⟩ :=
        congrArg S.obj h3
      have h5 : S.obj ⟨n - i - 1, by omega⟩ =
          (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).X₂ := rfl
      have h6 : Opposite.unop
          ((S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).X₂) =
          (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₂ := by
        dsimp [ShortComplex.unop]
      rw [h1, h2, congrArg Opposite.unop h4, congrArg Opposite.unop h5, h6])
  let e₃ : (S.unop.sc (h.unop) i hi).X₃ ≅
      (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₃ :=
    eqToIso (show (S.unop.sc (h.unop) i hi).X₃ =
        (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₃ from by
      have h1 : (S.unop.sc (h.unop) i hi).X₃ = S.unop.obj ⟨i + 2, by omega⟩ := rfl
      have h2 : S.unop.obj ⟨i + 2, by omega⟩ = Opposite.unop (S.obj ⟨n - (i + 2), by omega⟩) :=
        unop_obj_eq S (i + 2) (by omega)
      have h3 : (⟨n - (i + 2), by omega⟩ : Fin (n + 1)) = ⟨n - i - 2, by omega⟩ := by
        apply Fin.ext; simp; omega
      have h4 : S.obj ⟨n - (i + 2), by omega⟩ = S.obj ⟨n - i - 2, by omega⟩ :=
        congrArg S.obj h3
      have h5 : S.obj ⟨n - i - 2, by omega⟩ =
          (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).X₁ := rfl
      have h6 : Opposite.unop
          ((S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).X₁) =
          (S.sc' h (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)).unop.X₃ := by
        dsimp [ShortComplex.unop]
      rw [h1, h2, congrArg Opposite.unop h4, congrArg Opposite.unop h5, h6])
  ShortComplex.isoMk e₁ e₂ e₃
    (by
      have h1 := unop_map'_eq S i (by omega)
      simp only [e₁, e₂, h1, Category.assoc]
      simp)
    (by
      have h2 := unop_map'_eq S (i + 1) (by omega)
      have h2' : S.unop.map' (i + 1) (i + 2) =
          eqToHom (unop_obj_eq S (i + 1) (by omega)) ≫
            (S.map' (n - i - 2) (n - i - 1)).unop ≫
              eqToHom (unop_obj_eq S (i + 2) (by omega)).symm := by
        simpa [show n - (i + 1) - 1 = n - i - 2 from by omega,
               show n - (i + 1) = n - i - 1 from by omega,
               show i + 1 + 1 = i + 2 from by omega] using h2
      simp only [e₂, e₃, h2', Category.assoc]
      simp)

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
/-- Exactness is preserved by taking opposites. -/
lemma Exact.op {n : ℕ} {S : ComposableArrows C n}
    (h : S.Exact) : S.op.Exact where
  toIsComplex := h.toIsComplex.op
  exact i hi := by
    let T := S.sc' h.toIsComplex (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)
    have hT : T.Exact := h.exact' (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)
    have hOp : T.op.Exact := hT.op
    exact ShortComplex.exact_of_iso (opScIso S h.toIsComplex i hi).symm hOp

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
/-- Exactness is preserved by taking unopposites. -/
lemma Exact.unop {n : ℕ} {S : ComposableArrows Cᵒᵖ n}
    (h : S.Exact) : S.unop.Exact where
  toIsComplex := h.toIsComplex.unop
  exact i hi := by
    let T := S.sc' h.toIsComplex (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)
    have hT : T.Exact := h.exact' (n - i - 2) (n - i - 1) (n - i) (by omega) (by omega) (by omega)
    have hUnop : T.unop.Exact := hT.unop
    exact ShortComplex.exact_of_iso (unopScIso S h.toIsComplex i hi).symm hUnop

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
/-- A composable arrow is exact iff its opposite is. -/
@[simp]
lemma exact_op_iff {n : ℕ} (S : ComposableArrows C n) :
    S.op.Exact ↔ S.Exact where
  mp h := exact_of_iso (opUnop S) h.unop
  mpr h := h.op

variable [CategoryTheory.Limits.HasZeroMorphisms C] in
/-- A composable arrow in `Cᵒᵖ` is exact iff its unopposite is. -/
@[simp]
lemma exact_unop_iff {n : ℕ} (S : ComposableArrows Cᵒᵖ n) :
    S.unop.Exact ↔ S.Exact where
  mp h := exact_of_iso (unopOp S) h.op
  mpr h := h.unop

def exactSequences (C : Type u) [Category.{v} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) :
    ObjectProperty (ComposableArrows C n) :=
  fun S => S.Exact

abbrev ExactSequences (C : Type u) [Category.{v} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) :=
  (exactSequences C n).FullSubcategory

instance (n : ℕ) [CategoryTheory.Limits.HasZeroMorphisms C] :
    (exactSequences (C := C) n).IsClosedUnderIsomorphisms where
  of_iso e h := exact_of_iso e h

/-- The exact-sequence property pulled back along the opposite equivalence is
the opposite exact-sequence property. -/
lemma exactSequences_op_eq [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) :
    (exactSequences Cᵒᵖ n).inverseImage (opEquivalence C n).functor =
      (exactSequences C n).op := by
  ext S
  change S.unop.op.Exact ↔ S.unop.Exact
  exact exact_op_iff S.unop

noncomputable def exactOpEquivalence (C : Type u) [Category.{v} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) :
    (ExactSequences C n)ᵒᵖ ≌ ExactSequences Cᵒᵖ n :=
  (ObjectProperty.opEquivalence (exactSequences C n)).symm.trans
    ((opEquivalence C n).congrFullSubcategory (exactSequences_op_eq (C := C) n))

@[simp]
lemma exactOpEquivalence_functor_obj_obj (C : Type u) [Category.{v} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) (S : ExactSequences C n) :
    ((exactOpEquivalence C n).functor.obj (Opposite.op S)).obj = S.obj.op :=
  rfl

@[simp]
lemma exactOpEquivalence_inverse_obj_unop_obj (C : Type u) [Category.{v} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) (S : ExactSequences Cᵒᵖ n) :
    ((exactOpEquivalence C n).inverse.obj S).unop.obj = S.obj.unop :=
  rfl

@[simp]
lemma exactOpEquivalence_functor_map_hom (C : Type u) [Category.{v} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) {X Y : ExactSequences C n}
    (f : X ⟶ Y) :
    ((exactOpEquivalence C n).functor.map f.op).hom = (opEquivalence C n).functor.map f.hom.op :=
  rfl

@[simp]
lemma exactOpEquivalence_inverse_map_unop_hom (C : Type u) [Category.{v} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] (n : ℕ) {X Y : ExactSequences Cᵒᵖ n} (f : X ⟶ Y) :
    ((exactOpEquivalence C n).inverse.map f).unop.hom =
      Quiver.Hom.unop ((opEquivalence C n).inverse.map f.hom) :=
  rfl

end CategoryTheory.ComposableArrows
