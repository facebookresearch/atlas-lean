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

public import MathlibExt.Algebra.Homology.PartialTotalConnectingDifferential
public import Mathlib.Algebra.Homology.Embedding.Splitting

/-!
# Degreewise splitting of an extended successor partial-total step

The raw successor filtration is degreewise split.  This file transports that
splitting through the standard chain-to-cochain embedding and exposes its
supported section and retraction coordinates.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The canonical degreewise splitting of the extended successor filtration
step. -/
noncomputable def partialTotalSuccessorCochainSplitting
    (m : ℕ) (i : ℤ) :
    ((B.partialTotalStepCochainShortComplex (m + 1)).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting := by
  rw [B.partialTotalStepCochainShortComplex_succ]
  exact ComplexShape.embeddingDownNat.splittingExtend
    (fun k => B.partialTotalSuccDegreeSplitting m k) i

set_option backward.isDefEq.respectTransparency false in
/-- Supported section component of the successor cochain splitting. -/
theorem partialTotalSuccessorCochainSplitting_s (m k : ℕ) :
    HEq
      (B.partialTotalSuccessorCochainSplitting m
        (ComplexShape.embeddingDownNat.f k)).s
      (((B.totalRow (m + 1)).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := ComplexShape.embeddingDownNat.f k) rfl).hom ≫
        B.partialTotalRowQuotientSectionF (m + 1) k ≫
        ((B.partialTotal (m + 1)).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := ComplexShape.embeddingDownNat.f k) rfl).inv) := by
  let e := ComplexShape.embeddingDownNat
  let S := B.partialTotalSuccShortComplex m
  let α := e.extendFunctorCompEvalIso C (i := k) (i' := e.f k) rfl
  let ι := S.mapNatIso α.symm
  let R := B.totalRow (m + 1)
  let D := (B.firstStupidTrunc (m + 1)).total (ComplexShape.down ℕ)
  let P := B.partialTotal (m + 1)
  have hDP : D = P := by
    rfl
  have hDPX : D.X k = P.X k :=
    congrArg (fun K : ChainComplex C ℕ => K.X k) hDP
  have hDPExt : (D.extend e).X (e.f k) = (P.extend e).X (e.f k) :=
    congrArg (fun K : ChainComplex C ℕ => (K.extend e).X (e.f k)) hDP
  have hLeftRaw : ι.inv.τ₃ =
      (R.extendXIso e (i := k) (i' := e.f k) rfl).hom := by
    dsimp only [ι, α, S, R, ShortComplex.mapNatIso,
      ShortComplex.mapNatTrans,
      ComplexShape.Embedding.extendFunctorCompEvalIso]
    rfl
  have hRaw : HEq (B.partialTotalSuccDegreeSplitting m k).s
      (B.partialTotalRowQuotientSectionF (m + 1) k) :=
    HEq.rfl
  have hRightRaw : ι.hom.τ₂ =
      (D.extendXIso e (i := k) (i' := e.f k) rfl).inv := by
    dsimp only [ι, α, S, D, ShortComplex.mapNatIso,
      ShortComplex.mapNatTrans,
      ComplexShape.Embedding.extendFunctorCompEvalIso]
    rfl
  have hRight : HEq ι.hom.τ₂
      (P.extendXIso e (i := k) (i' := e.f k) rfl).inv :=
    (heq_of_eq hRightRaw).trans
      (congr_arg_heq
        (fun K : ChainComplex C ℕ =>
          (K.extendXIso e (i := k) (i' := e.f k) rfl).inv) hDP)
  have hLeftMiddle := CategoryTheory.heq_comp rfl rfl rfl
    (heq_of_eq hLeftRaw) hRaw
  have hWhole := CategoryTheory.heq_comp rfl hDPX hDPExt
    hLeftMiddle hRight
  have hWhole' : HEq
      (ι.inv.τ₃ ≫ (B.partialTotalSuccDegreeSplitting m k).s ≫ ι.hom.τ₂)
      ((R.extendXIso e (i := k) (i' := e.f k) rfl).hom ≫
        B.partialTotalRowQuotientSectionF (m + 1) k ≫
        (P.extendXIso e (i := k) (i' := e.f k) rfl).inv) := by
    simpa only [Category.assoc] using hWhole
  have hWrapper : HEq
      (B.partialTotalSuccessorCochainSplitting m (e.f k)).s
      (ι.inv.τ₃ ≫ (B.partialTotalSuccDegreeSplitting m k).s ≫
        ι.hom.τ₂) := by
    dsimp only [partialTotalSuccessorCochainSplitting]
    rw [ComplexShape.Embedding.splittingExtend_apply
      ComplexShape.embeddingDownNat
      (fun n => B.partialTotalSuccDegreeSplitting m n) rfl]
    rfl
  exact hWrapper.trans hWhole'

set_option backward.isDefEq.respectTransparency false in
/-- Supported retraction component of the successor cochain splitting. -/
theorem partialTotalSuccessorCochainSplitting_r
    (m k : ℕ) {i : ℤ}
    (h : ComplexShape.embeddingDownNat.f k = i) :
    HEq (B.partialTotalSuccessorCochainSplitting m i).r
      (((B.partialTotal (m + 1)).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := i) h).hom ≫
        B.partialTotalSuccRetractionF m k ≫
        ((B.partialTotal m).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := i) h).inv) := by
  let e := ComplexShape.embeddingDownNat
  let S := B.partialTotalSuccShortComplex m
  let α := e.extendFunctorCompEvalIso C (i := k) (i' := i) h
  let ι := S.mapNatIso α.symm
  let D₁ := (B.firstStupidTrunc (m + 1)).total (ComplexShape.down ℕ)
  let P₁ := B.partialTotal (m + 1)
  let D₀ := (B.firstStupidTrunc m).total (ComplexShape.down ℕ)
  let P₀ := B.partialTotal m
  have hD₁P₁ : D₁ = P₁ := by
    rfl
  have hD₀P₀ : D₀ = P₀ := by
    rfl
  have hD₁P₁X : D₁.X k = P₁.X k :=
    congrArg (fun K : ChainComplex C ℕ => K.X k) hD₁P₁
  have hD₀P₀X : D₀.X k = P₀.X k :=
    congrArg (fun K : ChainComplex C ℕ => K.X k) hD₀P₀
  have hD₁P₁Ext : (D₁.extend e).X i = (P₁.extend e).X i :=
    congrArg (fun K : ChainComplex C ℕ => (K.extend e).X i) hD₁P₁
  have hD₀P₀Ext : (D₀.extend e).X i = (P₀.extend e).X i :=
    congrArg (fun K : ChainComplex C ℕ => (K.extend e).X i) hD₀P₀
  have hLeftRaw : ι.inv.τ₂ =
      (D₁.extendXIso e (i := k) (i' := i) h).hom := by
    dsimp only [ι, α, S, D₁, ShortComplex.mapNatIso,
      ShortComplex.mapNatTrans,
      ComplexShape.Embedding.extendFunctorCompEvalIso]
    rfl
  have hLeft : HEq ι.inv.τ₂
      (P₁.extendXIso e (i := k) (i' := i) h).hom :=
    (heq_of_eq hLeftRaw).trans
      (congr_arg_heq
        (fun K : ChainComplex C ℕ =>
          (K.extendXIso e (i := k) (i' := i) h).hom) hD₁P₁)
  have hRaw : HEq (B.partialTotalSuccDegreeSplitting m k).r
      (B.partialTotalSuccRetractionF m k) :=
    HEq.rfl
  have hRightRaw : ι.hom.τ₁ =
      (D₀.extendXIso e (i := k) (i' := i) h).inv := by
    dsimp only [ι, α, S, D₀, ShortComplex.mapNatIso,
      ShortComplex.mapNatTrans,
      ComplexShape.Embedding.extendFunctorCompEvalIso]
    rfl
  have hRight : HEq ι.hom.τ₁
      (P₀.extendXIso e (i := k) (i' := i) h).inv :=
    (heq_of_eq hRightRaw).trans
      (congr_arg_heq
        (fun K : ChainComplex C ℕ =>
          (K.extendXIso e (i := k) (i' := i) h).inv) hD₀P₀)
  have hLeftMiddle := CategoryTheory.heq_comp
    hD₁P₁Ext hD₁P₁X hD₀P₀X hLeft hRaw
  have hWhole := CategoryTheory.heq_comp
    hD₁P₁Ext hD₀P₀X hD₀P₀Ext hLeftMiddle hRight
  have hWhole' : HEq
      (ι.inv.τ₂ ≫ (B.partialTotalSuccDegreeSplitting m k).r ≫ ι.hom.τ₁)
      ((P₁.extendXIso e (i := k) (i' := i) h).hom ≫
        B.partialTotalSuccRetractionF m k ≫
        (P₀.extendXIso e (i := k) (i' := i) h).inv) := by
    simpa only [Category.assoc] using hWhole
  have hWrapper : HEq
      (B.partialTotalSuccessorCochainSplitting m i).r
      (ι.inv.τ₂ ≫ (B.partialTotalSuccDegreeSplitting m k).r ≫
        ι.hom.τ₁) := by
    dsimp only [partialTotalSuccessorCochainSplitting]
    rw [ComplexShape.Embedding.splittingExtend_apply
      ComplexShape.embeddingDownNat
      (fun n => B.partialTotalSuccDegreeSplitting m n) h]
    rfl
  exact hWrapper.trans hWhole'

end HomologicalComplex₂

end
