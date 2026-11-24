/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Fold and signed diagonal for binary biproducts

This file provides the comparison between the `Bool`-indexed coproduct and the
binary biproduct, the fold and signed diagonal maps and their identities, the
resulting kernel isomorphism for the fold map, and compatibility with the
biproduct braiding in a preadditive category.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

def boolCoproductIsoBiprod (R : C) [HasCoproduct (fun _ : Bool => R)]
    [HasBinaryBiproduct R R] :
    (∐ fun _ : Bool => R) ≅ R ⊞ R where
  hom := Sigma.desc (fun b => match b with
    | false => biprod.inl
    | true => biprod.inr)
  inv := biprod.desc (Sigma.ι (fun _ : Bool => R) false)
    (Sigma.ι (fun _ : Bool => R) true)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro b
    cases b with
    | false =>
      calc
        Sigma.ι (fun _ : Bool => R) false ≫
            (Sigma.desc (fun b => match b with
              | false => biprod.inl
              | true => biprod.inr) ≫
              biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                (Sigma.ι (fun _ : Bool => R) true))
            = (Sigma.ι (fun _ : Bool => R) false ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr)) ≫
              biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                (Sigma.ι (fun _ : Bool => R) true) := by
              rw [← Category.assoc]
        _ = (biprod.inl : R ⟶ R ⊞ R) ≫
              biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                (Sigma.ι (fun _ : Bool => R) true) := by
              rw [Sigma.ι_comp_desc]
        _ = Sigma.ι (fun _ : Bool => R) false := by
              rw [biprod.inl_desc]
        _ = Sigma.ι (fun _ : Bool => R) false ≫ 𝟙 _ := by
              rw [Category.comp_id]
    | true =>
      calc
        Sigma.ι (fun _ : Bool => R) true ≫
            (Sigma.desc (fun b => match b with
              | false => biprod.inl
              | true => biprod.inr) ≫
              biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                (Sigma.ι (fun _ : Bool => R) true))
            = (Sigma.ι (fun _ : Bool => R) true ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr)) ≫
              biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                (Sigma.ι (fun _ : Bool => R) true) := by
              rw [← Category.assoc]
        _ = (biprod.inr : R ⟶ R ⊞ R) ≫
              biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                (Sigma.ι (fun _ : Bool => R) true) := by
              rw [Sigma.ι_comp_desc]
        _ = Sigma.ι (fun _ : Bool => R) true := by
              rw [biprod.inr_desc]
        _ = Sigma.ι (fun _ : Bool => R) true ≫ 𝟙 _ := by
              rw [Category.comp_id]
  inv_hom_id := by
    apply biprod.hom_ext'
    · calc
        biprod.inl ≫
              (biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                  (Sigma.ι (fun _ : Bool => R) true) ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr))
            = (biprod.inl ≫
                biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                  (Sigma.ι (fun _ : Bool => R) true)) ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr) := by
              rw [← Category.assoc]
        _ = Sigma.ι (fun _ : Bool => R) false ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr) := by
              rw [biprod.inl_desc]
        _ = (biprod.inl : R ⟶ R ⊞ R) := by
              rw [Sigma.ι_comp_desc]
        _ = biprod.inl ≫ 𝟙 (R ⊞ R) := by
              rw [Category.comp_id]
    · calc
        biprod.inr ≫
              (biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                  (Sigma.ι (fun _ : Bool => R) true) ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr))
            = (biprod.inr ≫
                biprod.desc (Sigma.ι (fun _ : Bool => R) false)
                  (Sigma.ι (fun _ : Bool => R) true)) ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr) := by
              rw [← Category.assoc]
        _ = Sigma.ι (fun _ : Bool => R) true ≫
                Sigma.desc (fun b => match b with
                  | false => biprod.inl
                  | true => biprod.inr) := by
              rw [biprod.inr_desc]
        _ = (biprod.inr : R ⟶ R ⊞ R) := by
              rw [Sigma.ι_comp_desc]
        _ = biprod.inr ≫ 𝟙 (R ⊞ R) := by
              rw [Category.comp_id]

def biprodFold (R : C) [HasBinaryBiproduct R R] : R ⊞ R ⟶ R :=
  biprod.desc (𝟙 R) (𝟙 R)

def biprodSignedDiagonal (R : C) [HasBinaryBiproduct R R] : R ⟶ R ⊞ R :=
  biprod.lift (𝟙 R) (-𝟙 R)

@[reassoc (attr := simp)]
lemma biprod_inl_comp_fold (R : C) [HasBinaryBiproduct R R] :
    biprod.inl ≫ biprodFold (C := C) R = 𝟙 R := by
  simp [biprodFold]

@[reassoc (attr := simp)]
lemma biprod_inr_comp_fold (R : C) [HasBinaryBiproduct R R] :
    biprod.inr ≫ biprodFold (C := C) R = 𝟙 R := by
  simp [biprodFold]

@[reassoc (attr := simp)]
lemma biprodSignedDiagonal_comp_fst (R : C) [HasBinaryBiproduct R R] :
    biprodSignedDiagonal (C := C) R ≫ biprod.fst = 𝟙 R := by
  simp [biprodSignedDiagonal]

@[reassoc (attr := simp)]
lemma biprodSignedDiagonal_comp_snd (R : C) [HasBinaryBiproduct R R] :
    biprodSignedDiagonal (C := C) R ≫ biprod.snd = -𝟙 R := by
  simp [biprodSignedDiagonal]

@[reassoc (attr := simp)]
lemma biprodSignedDiagonal_comp_fold (R : C) [HasBinaryBiproduct R R] :
    biprodSignedDiagonal (C := C) R ≫ biprodFold (C := C) R = 0 := by
  unfold biprodSignedDiagonal biprodFold
  simp [biprod.lift_desc]

def biprodSignedDiagonalKernelIso (R : C) [HasBinaryBiproduct R R]
    [HasKernel (biprodFold (C := C) R)] :
    R ≅ kernel (biprodFold (C := C) R) where
  hom := kernel.lift (biprodFold (C := C) R)
    (biprodSignedDiagonal (C := C) R) (biprodSignedDiagonal_comp_fold R)
  inv := kernel.ι (biprodFold (C := C) R) ≫ biprod.fst
  hom_inv_id := by
    calc
      kernel.lift (biprodFold (C := C) R)
            (biprodSignedDiagonal (C := C) R)
            (biprodSignedDiagonal_comp_fold R) ≫
          (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst)
          = (kernel.lift (biprodFold (C := C) R)
              (biprodSignedDiagonal (C := C) R)
              (biprodSignedDiagonal_comp_fold R) ≫
            kernel.ι (biprodFold (C := C) R)) ≫ biprod.fst := by
              rw [← Category.assoc]
      _ = biprodSignedDiagonal (C := C) R ≫ biprod.fst := by
            rw [kernel.lift_ι]
      _ = 𝟙 R := by
            rw [biprodSignedDiagonal_comp_fst]
  inv_hom_id := by
    have hcond :
        kernel.ι (biprodFold (C := C) R) ≫ biprodFold (C := C) R = 0 :=
      kernel.condition _
    have h_sum :
        kernel.ι (biprodFold (C := C) R) ≫ biprod.fst +
          kernel.ι (biprodFold (C := C) R) ≫ biprod.snd = 0 := by
      -- Derive directly from hcond without rewriting the kernel index
      calc
        kernel.ι (biprodFold (C := C) R) ≫ biprod.fst +
            kernel.ι (biprodFold (C := C) R) ≫ biprod.snd
            = kernel.ι (biprodFold (C := C) R) ≫
                (biprod.fst + biprod.snd) := by
              rw [Preadditive.comp_add]
        _ = kernel.ι (biprodFold (C := C) R) ≫
                (biprod.fst ≫ 𝟙 R + biprod.snd ≫ 𝟙 R) := by
              simp only [Category.comp_id]
        _ = kernel.ι (biprodFold (C := C) R) ≫
                biprod.desc (𝟙 R) (𝟙 R) := by
              rw [← biprod.desc_eq]
        _ = kernel.ι (biprodFold (C := C) R) ≫
                biprodFold (C := C) R := rfl
        _ = 0 := hcond
    have h_snd :
        kernel.ι (biprodFold (C := C) R) ≫ biprod.snd =
          -(kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) := by
      calc
        kernel.ι (biprodFold (C := C) R) ≫ biprod.snd
            = 0 + kernel.ι (biprodFold (C := C) R) ≫ biprod.snd := by
              rw [zero_add]
        _ = (-(kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) +
              kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) +
              kernel.ι (biprodFold (C := C) R) ≫ biprod.snd := by
              rw [neg_add_cancel]
        _ = -(kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) +
              (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst +
                kernel.ι (biprodFold (C := C) R) ≫ biprod.snd) := by
              rw [add_assoc]
        _ = -(kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) + 0 := by
              rw [h_sum]
        _ = -(kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) := by
              rw [add_zero]
    apply (cancel_mono (kernel.ι (biprodFold (C := C) R))).mp
    have h_lift :
        ((kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
        kernel.lift (biprodFold (C := C) R)
          (biprodSignedDiagonal (C := C) R)
          (biprodSignedDiagonal_comp_fold R)) ≫
        kernel.ι (biprodFold (C := C) R)
        = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
            biprodSignedDiagonal (C := C) R := by
      calc
        ((kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
          kernel.lift (biprodFold (C := C) R)
            (biprodSignedDiagonal (C := C) R)
            (biprodSignedDiagonal_comp_fold R)) ≫
          kernel.ι (biprodFold (C := C) R)
          = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
            (kernel.lift (biprodFold (C := C) R)
                (biprodSignedDiagonal (C := C) R)
                (biprodSignedDiagonal_comp_fold R) ≫
              kernel.ι (biprodFold (C := C) R)) := by
                simp only [Category.assoc]
        _ = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
              biprodSignedDiagonal (C := C) R := by
              rw [kernel.lift_ι]
    calc
      ((kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
        kernel.lift (biprodFold (C := C) R)
          (biprodSignedDiagonal (C := C) R)
          (biprodSignedDiagonal_comp_fold R)) ≫
        kernel.ι (biprodFold (C := C) R)
          = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
              biprodSignedDiagonal (C := C) R := h_lift
      _ = kernel.ι (biprodFold (C := C) R) := by
            apply biprod.hom_ext
            · calc
                ((kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
                    biprodSignedDiagonal (C := C) R) ≫ biprod.fst
                    = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
                      (biprodSignedDiagonal (C := C) R ≫ biprod.fst) := by
                      simp only [Category.assoc]
                _ = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
                      𝟙 R := by
                      rw [biprodSignedDiagonal_comp_fst]
                _ = kernel.ι (biprodFold (C := C) R) ≫ biprod.fst := by
                      rw [Category.comp_id]
            · calc
                ((kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
                    biprodSignedDiagonal (C := C) R) ≫ biprod.snd
                    = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
                      (biprodSignedDiagonal (C := C) R ≫ biprod.snd) := by
                      simp only [Category.assoc]
                _ = (kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) ≫
                      (-𝟙 R) := by
                      rw [biprodSignedDiagonal_comp_snd]
                _ = -(kernel.ι (biprodFold (C := C) R) ≫ biprod.fst) := by
                      simp
                _ = kernel.ι (biprodFold (C := C) R) ≫ biprod.snd := by
                      rw [← h_snd]
      _ = 𝟙 (kernel (biprodFold (C := C) R)) ≫
            kernel.ι (biprodFold (C := C) R) := by
            rw [Category.id_comp]

@[reassoc (attr := simp)]
lemma biprodSignedDiagonalKernelIso_hom_ι (R : C) [HasBinaryBiproduct R R]
    [HasKernel (biprodFold (C := C) R)] :
    (biprodSignedDiagonalKernelIso (C := C) R).hom ≫
      kernel.ι (biprodFold (C := C) R) =
        biprodSignedDiagonal (C := C) R := by
  simp [biprodSignedDiagonalKernelIso]

@[simp]
lemma biprodSignedDiagonalKernelIso_inv (R : C) [HasBinaryBiproduct R R]
    [HasKernel (biprodFold (C := C) R)] :
    (biprodSignedDiagonalKernelIso (C := C) R).inv =
      kernel.ι (biprodFold (C := C) R) ≫ biprod.fst := rfl

section Braiding
variable [HasBinaryBiproducts C]

@[reassoc (attr := simp)]
lemma braiding_comp_biprodFold (R : C) :
    (biprod.braiding R R).hom ≫ biprodFold (C := C) R =
      biprodFold (C := C) R := by
  apply biprod.hom_ext'
  · calc
      biprod.inl ≫ ((biprod.braiding R R).hom ≫ biprodFold (C := C) R)
          = (biprod.inl ≫ (biprod.braiding R R).hom) ≫
              biprodFold (C := C) R := by
            rw [Category.assoc]
      _ = biprod.inr ≫ biprodFold (C := C) R := by
            have h : biprod.inl ≫ (biprod.braiding R R).hom = biprod.inr := by
              apply biprod.hom_ext
              · simp [biprod.braiding]
              · simp [biprod.braiding]
            rw [h]
      _ = 𝟙 R := by
            simp [biprodFold]
      _ = biprod.inl ≫ biprodFold (C := C) R := by
            simp [biprodFold]
  · calc
      biprod.inr ≫ ((biprod.braiding R R).hom ≫ biprodFold (C := C) R)
          = (biprod.inr ≫ (biprod.braiding R R).hom) ≫
              biprodFold (C := C) R := by
            rw [Category.assoc]
      _ = biprod.inl ≫ biprodFold (C := C) R := by
            have h : biprod.inr ≫ (biprod.braiding R R).hom = biprod.inl := by
              apply biprod.hom_ext
              · simp [biprod.braiding]
              · simp [biprod.braiding]
            rw [h]
      _ = 𝟙 R := by
            simp [biprodFold]
      _ = biprod.inr ≫ biprodFold (C := C) R := by
            simp [biprodFold]

@[reassoc (attr := simp)]
lemma biprodSignedDiagonal_comp_braiding (R : C) :
    biprodSignedDiagonal (C := C) R ≫ (biprod.braiding R R).hom =
      -biprodSignedDiagonal (C := C) R := by
  apply biprod.hom_ext
  · calc
      (biprodSignedDiagonal (C := C) R ≫ (biprod.braiding R R).hom) ≫
            biprod.fst
          = biprodSignedDiagonal (C := C) R ≫
              ((biprod.braiding R R).hom ≫ biprod.fst) := by
            rw [Category.assoc]
      _ = biprodSignedDiagonal (C := C) R ≫ biprod.snd := by
            simp [biprod.braiding]
      _ = -𝟙 R := by
            simp [biprodSignedDiagonal]
      _ = (-biprodSignedDiagonal (C := C) R) ≫ biprod.fst := by
            simp [biprodSignedDiagonal]
  · calc
      (biprodSignedDiagonal (C := C) R ≫ (biprod.braiding R R).hom) ≫
            biprod.snd
          = biprodSignedDiagonal (C := C) R ≫
              ((biprod.braiding R R).hom ≫ biprod.snd) := by
            rw [Category.assoc]
      _ = biprodSignedDiagonal (C := C) R ≫ biprod.fst := by
            simp [biprod.braiding]
      _ = 𝟙 R := by
            simp [biprodSignedDiagonal]
      _ = (-biprodSignedDiagonal (C := C) R) ≫ biprod.snd := by
            simp [biprodSignedDiagonal]

end Braiding

end CategoryTheory
