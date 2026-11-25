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

public import MathlibExt.Algebra.Homology.SpectralSequence.TwoColumnHomological
public import MathlibExt.Algebra.Homology.PartialTotalEdgeMaps

/-!
# An explicit two-column partial-total survivor coordinate

This file constructs a spectral-object-backed finite coordinate for the
partial-total spectral sequence. No equality with the generic two-column
spectral-sequence `IsTwoColumnAtTwo.pageTwoToPageIso` is asserted.
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

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

local notation "E" =>
  B.partialTotalSpectralObject.spectralSequence core

private noncomputable def partialTotalTwoColumnPageSuccIso
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) :
    ((E).page (((2 + k : ℕ) : ℤ))).X (p, q) ≅
      ((E).page (((2 + k.succ : ℕ) : ℤ))).X (p, q) := by
  let Y := B.partialTotalSpectralObject
  let r : ℤ := ((2 + k : ℕ) : ℤ)
  let r' : ℤ := ((2 + k.succ : ℕ) : ℤ)
  have hrr' : r + 1 = r' := by
    dsimp only [r, r']
    omega
  have hr : (1 : ℤ) ≤ r := by
    dsimp only [r]
    omega
  have hr' : (1 : ℤ) ≤ r' := by omega
  let pq : ℕ × ℕ := (p, q)
  let pqPrev :=
    (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).prev pq
  let pqNext :=
    (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).next pq
  let i₀' : EInt := (((p : ℤ) - r' : ℤ) : EInt)
  let i₀ : EInt := (((p : ℤ) - r : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := (((p : ℤ) + r - 1 : ℤ) : EInt)
  let i₃' : EInt := (((p : ℤ) + r' - 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  have hn : n₁ = (core).deg pq := by
    exact
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
        pq).symm
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hnPlus : n₂ = (core).deg pq + 1 := by
    rw [← hn]
  have hi₀' : i₀' = (core).i₀ r' pq hr' := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
      r' pq hr').symm
  have hi₀ : i₀ = (core).i₀ r pq hr := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
      r pq hr).symm
  have hi₁ : i₁ = (core).i₁ pq := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁
      pq).symm
  have hi₂ : i₂ = (core).i₂ pq := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂
      pq).symm
  have hi₃ : i₃ = (core).i₃ r pq hr := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
      r pq hr).symm
  have hi₃' : i₃' = (core).i₃ r' pq hr' := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
      r' pq hr').symm
  have hi₀'₀ : i₀' ≤ i₀ := by
    dsimp only [i₀', i₀]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := by
    dsimp only [i₁, i₂]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₀'₁ : i₀' ≤ i₁ := by
    dsimp only [i₀', i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₃₃' : i₃ ≤ i₃' := by
    dsimp only [i₃, i₃']
    simp only [WithBotTop.coe_le_coe]
    omega
  have hNoOut : ∀ z,
      ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq z := by
    rintro ⟨a, b⟩ hz
    dsimp only [pq] at hz
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hz
    dsimp only [r] at hz
    omega
  let hLeft : IsZero ((Y.H n₂).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show i₀' ≤ i₀ by
          exact hi₀'₀)))) :=
    Y.isZero_H_obj_mk₁_i₀_le' core r r' hrr' hr pq hNoOut
      n₂ hnPlus i₀' i₀ hi₀' hi₀
  let ePage := Y.spectralSequencePageXIso core r hr pq
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  let eLeft := Y.isoMapFourδ₁Toδ₀'
    i₀' i₀ i₁ i₂ i₃
      hi₀'₀ hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
  let rightMap := Y.mapFourδ₄Toδ₃'
    i₀' i₁ i₂ i₃ i₃'
      hi₀'₁ hi₁₂ hi₂₃ hi₃₃'
      n₀ n₁ n₂ hn₁ hn₂
  let ePage' := Y.spectralSequencePageXIso core r' hr' pq
    i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃'
      n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  let hData := Y.spectralSequenceHomologyData core r r' hrr' hr
    pqPrev pq pqNext rfl rfl i₀' i₀ i₁ i₂ i₃ i₃'
    hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
    n₀ n₁ n₂ hn hn₁ hn₂
  have hIn : ((E).page r hr).d pqPrev pq = 0 := by
    exact h₂.page_d_to_survivor_eq_zero k p q hp pqPrev
  let _ : IsIso rightMap := by
    change IsIso hData.left.π
    exact hData.left.isIso_π (by
      change ((E).page r hr).d pqPrev pq = 0
      exact hIn)
  exact ePage ≪≫ eLeft.symm ≪≫ asIso rightMap ≪≫ ePage'.symm

private theorem partialTotalTwoColumnPageSuccIso_hom
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) :
    (partialTotalTwoColumnPageSuccIso B h₂ k p q hp).hom = by
      let Y := B.partialTotalSpectralObject
      let r : ℤ := ((2 + k : ℕ) : ℤ)
      let r' : ℤ := ((2 + k.succ : ℕ) : ℤ)
      have hrr' : r + 1 = r' := by
        dsimp only [r, r']
        omega
      have hr : (1 : ℤ) ≤ r := by
        dsimp only [r]
        omega
      have hr' : (1 : ℤ) ≤ r' := by omega
      let pq : ℕ × ℕ := (p, q)
      let i₀' : EInt := (((p : ℤ) - r' : ℤ) : EInt)
      let i₀ : EInt := (((p : ℤ) - r : ℤ) : EInt)
      let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
      let i₂ : EInt := ((p : ℤ) : EInt)
      let i₃ : EInt := (((p : ℤ) + r - 1 : ℤ) : EInt)
      let i₃' : EInt := (((p : ℤ) + r' - 1 : ℤ) : EInt)
      let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
      let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
      let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
      have hn : n₁ = (core).deg pq := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
            pq).symm
      have hn₁ : n₀ + 1 = n₁ := by
        dsimp only [n₀, n₁]
        omega
      have hn₂ : n₁ + 1 = n₂ := by
        dsimp only [n₁, n₂]
      have hnPlus : n₂ = (core).deg pq + 1 := by
        rw [← hn]
      have hi₀' : i₀' = (core).i₀ r' pq hr' := by
        exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
          r' pq hr').symm
      have hi₀ : i₀ = (core).i₀ r pq hr := by
        exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
          r pq hr).symm
      have hi₁ : i₁ = (core).i₁ pq := by
        exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁
          pq).symm
      have hi₂ : i₂ = (core).i₂ pq := by
        exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂
          pq).symm
      have hi₃ : i₃ = (core).i₃ r pq hr := by
        exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
          r pq hr).symm
      have hi₃' : i₃' = (core).i₃ r' pq hr' := by
        exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
          r' pq hr').symm
      have hi₀'₀ : i₀' ≤ i₀ := by
        dsimp only [i₀', i₀]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₀₁ : i₀ ≤ i₁ := by
        dsimp only [i₀, i₁]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₁₂ : i₁ ≤ i₂ := by
        dsimp only [i₁, i₂]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₂₃ : i₂ ≤ i₃ := by
        dsimp only [i₂, i₃]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₀'₁ : i₀' ≤ i₁ := by
        dsimp only [i₀', i₁]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₃₃' : i₃ ≤ i₃' := by
        dsimp only [i₃, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega
      have hNoOut : ∀ z,
          ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq z := by
        rintro ⟨a, b⟩ hz
        dsimp only [pq] at hz
        simp only [ComplexShape.spectralSequenceNat_rel_iff] at hz
        dsimp only [r] at hz
        omega
      let hLeft : IsZero ((Y.H n₂).obj
          (CategoryTheory.ComposableArrows.mk₁
            (homOfLE (show i₀' ≤ i₀ by
              exact hi₀'₀)))) :=
        Y.isZero_H_obj_mk₁_i₀_le' core r r' hrr' hr pq hNoOut
          n₂ hnPlus i₀' i₀ hi₀' hi₀
      let ePage := Y.spectralSequencePageXIso core r hr pq
        i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
          (hn₁ := hn₁) (hn₂ := hn₂)
      let eLeft := Y.isoMapFourδ₁Toδ₀'
        i₀' i₀ i₁ i₂ i₃
          hi₀'₀ hi₀₁ hi₁₂ hi₂₃
          n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
      let rightMap := Y.mapFourδ₄Toδ₃'
        i₀' i₁ i₂ i₃ i₃'
          hi₀'₁ hi₁₂ hi₂₃ hi₃₃'
          n₀ n₁ n₂ hn₁ hn₂
      let ePage' := Y.spectralSequencePageXIso core r' hr' pq
        i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃'
          n₀ n₁ n₂ hn
          (hn₁ := hn₁) (hn₂ := hn₂)
      exact ePage.hom ≫ eLeft.inv ≫ rightMap ≫ ePage'.inv := by
  unfold partialTotalTwoColumnPageSuccIso
  dsimp only
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]

private noncomputable def partialTotalTwoColumnDirectPageToStable
    (q k : ℕ) :
    ((E).page (((2 + k : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 := by
  let Y := B.partialTotalSpectralObject
  let r : ℤ := ((2 + k : ℕ) : ℤ)
  have hr : (1 : ℤ) ≤ r := by
    dsimp only [r]
    omega
  let i₀ : EInt := (((((0 : ℕ) : ℤ)) - r : ℤ) : EInt)
  let i₁ : EInt := (((((0 : ℕ) : ℤ)) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((((0 : ℕ) : ℤ)) : EInt)
  let i₃ : EInt := (((((0 : ℕ) : ℤ)) + r - 1 : ℤ) : EInt)
  let n₀ : ℤ := -(0 : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(0 : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(0 : ℤ) - (q : ℤ) + 1
  have hn : n₁ = (core).deg (0, q) := by
    exact
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
        (0, q)).symm
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hi₀ : i₀ = (core).i₀ r (0, q) hr := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
      r (0, q) hr).symm
  have hi₁ : i₁ = (core).i₁ (0, q) := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁
      (0, q)).symm
  have hi₂ : i₂ = (core).i₂ (0, q) := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂
      (0, q)).symm
  have hi₃ : i₃ = (core).i₃ r (0, q) hr := by
    exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
      r (0, q) hr).symm
  have hi₀neg : i₀ = ((-r : ℤ) : EInt) := by
    dsimp only [i₀]
    congr 1
    omega
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := by
    dsimp only [i₁, i₂]
    simp
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
  have hLeft : IsZero ((Y.H n₂).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
    rw [hi₀neg]
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg n₂ (-r) (by
      dsimp only [r]
      omega)
  let ePage := Y.spectralSequencePageXIso core r hr (0, q)
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  let eLeft := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
  let rightOuterMap := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
      n₀ n₁ n₂ hn₁ hn₂
  let eTarget :
      Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
          (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ ≅
        B.partialTotalStableObj q 0 :=
    B.partialTotalZeroColumnStableTargetIso q
  exact ePage.hom ≫ eLeft.inv ≫ rightOuterMap ≫ eTarget.hom

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
private theorem partialTotalTwoColumnDirectPageToStable_zero (q : ℕ) :
    partialTotalTwoColumnDirectPageToStable B q 0 =
      B.partialTotalZeroColumnPageToStable q := by
  let χ := B.partialTotalFirstPageChoice
  let η := χ.pageTransitionIndex 0 q
  let Y := B.partialTotalSpectralObject
  have hi₀' : η.i₀' = ((-2 : ℤ) : EInt) := by
    dsimp only [η, PartialTotalFirstPageChoice.pageTransitionIndex]
    congr 1
  have hLeftAt (x : EInt) (hx : x = ((-2 : ℤ) : EInt))
      (hbx : (⊥ : EInt) ≤ x) :
      IsZero ((Y.H η.n₂).obj
        (CategoryTheory.ComposableArrows.mk₁ (homOfLE hbx))) := by
    subst x
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      η.n₂ (-2) (by omega)
  have hLeft : IsZero ((Y.H η.n₂).obj
      (CategoryTheory.ComposableArrows.mk₁ (homOfLE η.hiBot₀'))) :=
    hLeftAt η.i₀' hi₀' η.hiBot₀'
  let eLeftRaw := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) η.i₀' η.i₁ η.i₂ η.i₃'
    η.hiBot₀' η.hi₀'₁ η.hi₁₂ η.hi₂₃'
    η.n₀ η.n₁ η.n₂ hLeft η.hn₁ η.hn₂
  let ePage :=
    Y.spectralSequencePageXIso core 2 χ.pageTwoBound (0, q)
      η.i₀' η.i₁ η.i₂ η.i₃'
      η.hi₀' η.hi₁ η.hi₂ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂
  let eCoordinate := χ.pageTwoCoordinateIso 0 q
  let eRawCoordinate := χ.pageTwoRawCoordinateIso 0 q
  let rightOuter := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) η.i₁ η.i₂ η.i₃' (⊤ : EInt)
    η.hiBot₁ η.hi₁₂ η.hi₂₃' η.hi₃'Top
    η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let targetIso := B.partialTotalZeroColumnStableTargetIso q
  rw [B.partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate q]
  unfold partialTotalTwoColumnDirectPageToStable
  have hPageRaw : HEq
      (eCoordinate.hom ≫ eRawCoordinate.inv) ePage.hom :=
    heq_of_eq (eCoordinate.hom_inv_id_assoc ePage.hom)
  have hPublicTail :
      eCoordinate.hom ≫ (eLeftRaw ≪≫ eRawCoordinate).inv ≫
          rightOuter ≫ targetIso.hom =
        ePage.hom ≫ eLeftRaw.inv ≫ rightOuter ≫ targetIso.hom := by
    rw [Iso.trans_inv]
    apply eq_of_heq
    let tail := eLeftRaw.inv ≫ rightOuter ≫ targetIso.hom
    have hWhole := CategoryTheory.heq_comp
      (by rfl) (by rfl) (by rfl) hPageRaw
        (HEq.rfl : HEq tail tail)
    simpa only [tail, Category.assoc] using hWhole
  exact hPublicTail.symm

attribute [irreducible] partialTotalTwoColumnPageSuccIso
attribute [irreducible] partialTotalTwoColumnDirectPageToStable

/- The recurrence proof is localized in the finite induction below, so Lean
does not weak-head-normalize both large private definitions in a standalone
theorem statement.

private theorem partialTotalTwoColumnDirectPageToStable_succ
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q k : ℕ) :
    (partialTotalTwoColumnPageSuccIso B h₂ k 0 q (Nat.zero_le 1)).hom ≫
        partialTotalTwoColumnDirectPageToStable B q (k + 1) =
      partialTotalTwoColumnDirectPageToStable B q k := by
  change (partialTotalTwoColumnPageSuccIso B h₂ k 0 q
      (Nat.zero_le 1)).hom ≫
      partialTotalTwoColumnDirectPageToStable B q k.succ =
    partialTotalTwoColumnDirectPageToStable B q k
  let Y := B.partialTotalSpectralObject
  let r : ℤ := ((2 + k : ℕ) : ℤ)
  let r' : ℤ := ((2 + k.succ : ℕ) : ℤ)
  have hrr' : r + 1 = r' := by
    dsimp only [r, r']
    omega
  have hr : (1 : ℤ) ≤ r := by
    dsimp only [r]
    omega
  have hr' : (1 : ℤ) ≤ r' := by omega
  let pq : ℕ × ℕ := (0, q)
  let i₀' : EInt := ((-r' : ℤ) : EInt)
  let i₀ : EInt := ((-r : ℤ) : EInt)
  let i₁ : EInt := ((-1 : ℤ) : EInt)
  let i₂ : EInt := ((0 : ℤ) : EInt)
  let i₃ : EInt := (((r - 1 : ℤ)) : EInt)
  let i₃' : EInt := (((r' - 1 : ℤ)) : EInt)
  let n₀ : ℤ := -((q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -(q : ℤ)
  let n₂ : ℤ := -(q : ℤ) + 1
  have hn : n₁ = (core).deg pq := by
    change n₁ = -(0 : ℤ) - (q : ℤ)
    dsimp only [n₁, pq]
    omega
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hi₀' : i₀' = (core).i₀ r' pq hr' := by
    change i₀' = (((0 : ℤ) - r' : ℤ) : EInt)
    dsimp only [i₀']
    congr 1 <;> omega
  have hi₀ : i₀ = (core).i₀ r pq hr := by
    change i₀ = (((0 : ℤ) - r : ℤ) : EInt)
    dsimp only [i₀]
    congr 1 <;> omega
  have hi₁ : i₁ = (core).i₁ pq := by rfl
  have hi₂ : i₂ = (core).i₂ pq := by rfl
  have hi₃ : i₃ = (core).i₃ r pq hr := by
    change i₃ = (((0 : ℤ) + r - 1 : ℤ) : EInt)
    dsimp only [i₃]
    congr 1 <;> omega
  have hi₃' : i₃' = (core).i₃ r' pq hr' := by
    change i₃' = (((0 : ℤ) + r' - 1 : ℤ) : EInt)
    dsimp only [i₃']
    congr 1 <;> omega
  have hiBot₀' : (⊥ : EInt) ≤ i₀' := by simp
  have hi₀'₀ : i₀' ≤ i₀ := by
    dsimp only [i₀', i₀]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₀'₁ : i₀' ≤ i₁ := by
    dsimp only [i₀', i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := by
    dsimp only [i₁, i₂]
    simp
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₃₃' : i₃ ≤ i₃' := by
    dsimp only [i₃, i₃']
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₂₃' : i₂ ≤ i₃' := by
    dsimp only [i₂, i₃']
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
  have hi₃'Top : i₃' ≤ (⊤ : EInt) := by simp
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  have hCurrentLeft : IsZero ((Y.H n₂).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg n₂ (-r) (by
      dsimp only [r]
      omega)
  have hNextLeft : IsZero ((Y.H n₂).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ i₀' by simp)))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg n₂ (-r') (by
      dsimp only [r']
      omega)
  have hNoOut : ∀ z,
      ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq z := by
    rintro ⟨a, b⟩ hz
    dsimp only [pq] at hz
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hz
    dsimp only [r] at hz
    omega
  let hStepLeft : IsZero ((Y.H n₂).obj
      (CategoryTheory.ComposableArrows.mk₁ (homOfLE hi₀'₀))) :=
    Y.isZero_H_obj_mk₁_i₀_le' core r r' hrr' hr pq hNoOut
      n₂ (by
        change -(q : ℤ) + 1 = -(0 : ℤ) - (q : ℤ) + 1
        omega) i₀' i₀ hi₀' hi₀
  let Lstep := Y.isoMapFourδ₁Toδ₀'
    i₀' i₀ i₁ i₂ i₃ hi₀'₀ hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hStepLeft hn₁ hn₂
  let Laux := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀' i₁ i₂ i₃ hiBot₀' hi₀'₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hNextLeft hn₁ hn₂
  let Lnext := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀' i₁ i₂ i₃' hiBot₀' hi₀'₁ hi₁₂ hi₂₃'
      n₀ n₁ n₂ hNextLeft hn₁ hn₂
  let Lcurrent := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hCurrentLeft hn₁ hn₂
  let Rstep := Y.mapFourδ₄Toδ₃'
    i₀' i₁ i₂ i₃ i₃' hi₀'₁ hi₁₂ hi₂₃ hi₃₃'
      n₀ n₁ n₂ hn₁ hn₂
  let Rbot := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ i₃' hiBot₁ hi₁₂ hi₂₃ hi₃₃'
      n₀ n₁ n₂ hn₁ hn₂
  let RtopNext := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃' ⊤ hiBot₁ hi₁₂ hi₂₃' hi₃'Top
      n₀ n₁ n₂ hn₁ hn₂
  let RtopCurrent := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
      n₀ n₁ n₂ hn₁ hn₂
  let ePageCurrent := Y.spectralSequencePageXIso core r hr pq
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  let ePageNext := Y.spectralSequencePageXIso core r' hr' pq
    i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃'
      n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  have hTarget :
      Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
          (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ =
        B.partialTotalStableObj q 0 := by
    dsimp only [partialTotalStableObj,
      CategoryTheory.Abelian.SpectralObject.stableIntervalObj,
      CategoryTheory.Abelian.SpectralObject.stableIntervalLeft,
      CategoryTheory.Abelian.SpectralObject.stableIntervalMiddle,
      CategoryTheory.Abelian.SpectralObject.stableIntervalRight,
      partialTotalHomologyPreviousIndex, n₀, n₁, n₂, pq]
    congr 1
    all_goals first | rfl | subsingleton | omega
  let eTarget :
      Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
          (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ ≅
        B.partialTotalStableObj q 0 :=
    eqToIso hTarget
  have hInter : Laux.hom ≫ Rstep = Rbot ≫ Lnext.hom := by
    exact Y.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'
      (⊥ : EInt) i₀' i₁ i₂ i₃ i₃'
      hiBot₀' hi₀'₁ hi₁₂ hi₂₃ hi₃₃'
      n₀ n₁ n₂ hn₁ hn₂
  have hCross : Rstep ≫ Lnext.inv = Laux.inv ≫ Rbot := by
    rw [← cancel_epi Laux.hom]
    rw [reassoc_of% hInter]
    rw [Lnext.hom_inv_id, Category.comp_id,
      Laux.hom_inv_id_assoc]
  have hLeftComp : Laux.hom ≫ Lstep.hom = Lcurrent.hom := by
    exact Y.mapFourδ₁Toδ₀'_comp
      (⊥ : EInt) i₀' i₀ i₁ i₂ i₃
      hiBot₀' hi₀'₀ hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hn₁ hn₂
  have hLeftInv : Lstep.inv ≫ Laux.inv = Lcurrent.inv := by
    apply (cancel_mono Lcurrent.hom).1
    rw [Lcurrent.inv_hom_id]
    rw [← hLeftComp]
    rw [Category.assoc, Laux.inv_hom_id_assoc]
    exact Lstep.inv_hom_id
  have hRightComp : Rbot ≫ RtopNext = RtopCurrent := by
    exact Y.mapFourδ₄Toδ₃'_comp
      (⊥ : EInt) i₁ i₂ i₃ i₃' ⊤
      hiBot₁ hi₁₂ hi₂₃ hi₃₃' hi₃'Top
      n₀ n₁ n₂ hn₁ hn₂
  have hOuter :
      Lstep.inv ≫ Rstep ≫ Lnext.inv ≫ RtopNext =
        Lcurrent.inv ≫ RtopCurrent := by
    rw [reassoc_of% hCross, reassoc_of% hLeftInv, hRightComp]
  rw [partialTotalTwoColumnPageSuccIso_hom B h₂ k 0 q (Nat.zero_le 1)]
  unfold partialTotalTwoColumnDirectPageToStable
  dsimp only
  simp only [Category.assoc]
  change ePageCurrent.hom ≫ Lstep.inv ≫ Rstep ≫ ePageNext.inv ≫
      ePageNext.hom ≫ Lnext.inv ≫ RtopNext ≫ eTarget.hom =
    ePageCurrent.hom ≫ Lcurrent.inv ≫ RtopCurrent ≫ eTarget.hom
  simp only [ePageNext.inv_hom_id_assoc]
  rw [reassoc_of% hOuter]
-/

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The spectral-object-backed explicit coordinate from the chosen page two
to a later surviving partial-total page. No equality with the generic
two-column spectral-sequence `IsTwoColumnAtTwo.pageTwoToPageIso` is asserted. -/
noncomputable def partialTotalTwoColumnPageTwoToPageIso
    (h₂ :
      CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) :
    B.partialTotalFirstPageChoice.pageTwo.X (p, q) ≅
      ((E).page (((2 + k : ℕ) : ℤ))).X (p, q) := by
  let χ := B.partialTotalFirstPageChoice
  let Y := B.partialTotalSpectralObject
  let r (t : ℕ) : ℤ := ((2 + t : ℕ) : ℤ)
  let hr : ∀ t : ℕ, (1 : ℤ) ≤ r t := fun t =>
    Nat.rec
      (motive := fun t => (1 : ℤ) ≤ r t)
      χ.pageTwoBound
      (fun t ht => by
        dsimp only [r] at ht ⊢
        omega)
      t
  let P (t : ℕ) : C := ((E).page (r t) (hr t)).X (p, q)
  let step : ∀ t : ℕ, P t ≅ P (t + 1) := fun t => by
    let r₀ : ℤ := r t
    let r₁ : ℤ := r (t + 1)
    have hrr : r₀ + 1 = r₁ := by
      dsimp only [r₀, r₁, r]
      omega
    let pq : ℕ × ℕ := (p, q)
    let pqPrev :=
      (ComplexShape.spectralSequenceNat ⟨-r₀, r₀ - 1⟩).prev pq
    let pqNext :=
      (ComplexShape.spectralSequenceNat ⟨-r₀, r₀ - 1⟩).next pq
    let i₀' : EInt := (((p : ℤ) - r₁ : ℤ) : EInt)
    let i₀ : EInt := (((p : ℤ) - r₀ : ℤ) : EInt)
    let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
    let i₂ : EInt := ((p : ℤ) : EInt)
    let i₃ : EInt := (((p : ℤ) + r₀ - 1 : ℤ) : EInt)
    let i₃' : EInt := (((p : ℤ) + r₁ - 1 : ℤ) : EInt)
    let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
    let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
    let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
    have hn : n₁ = (core).deg pq := by
      exact
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
          pq).symm
    have hn₁ : n₀ + 1 = n₁ := by
      dsimp only [n₀, n₁]
      omega
    have hn₂ : n₁ + 1 = n₂ := by
      dsimp only [n₁, n₂]
    have hnPlus : n₂ = (core).deg pq + 1 := by
      rw [← hn]
    have hi₀' : i₀' = (core).i₀ r₁ pq (hr (t + 1)) := by
      exact
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
          r₁ pq (hr (t + 1))).symm
    have hi₀ : i₀ = (core).i₀ r₀ pq (hr t) := by
      exact
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
          r₀ pq (hr t)).symm
    have hi₁ : i₁ = (core).i₁ pq := by
      exact
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁
          pq).symm
    have hi₂ : i₂ = (core).i₂ pq := by
      exact
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂
          pq).symm
    have hi₃ : i₃ = (core).i₃ r₀ pq (hr t) := by
      exact
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
          r₀ pq (hr t)).symm
    have hi₃' : i₃' = (core).i₃ r₁ pq (hr (t + 1)) := by
      exact
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
          r₁ pq (hr (t + 1))).symm
    have hi₀'₀ : i₀' ≤ i₀ := by
      dsimp only [i₀', i₀, r₀, r₁, r]
      simp only [WithBotTop.coe_le_coe]
      omega
    have hi₀₁ : i₀ ≤ i₁ := by
      dsimp only [i₀, i₁, r₀, r]
      simp only [WithBotTop.coe_le_coe]
      omega
    have hi₁₂ : i₁ ≤ i₂ := by
      dsimp only [i₁, i₂]
      simp only [WithBotTop.coe_le_coe]
      omega
    have hi₂₃ : i₂ ≤ i₃ := by
      dsimp only [i₂, i₃, r₀, r]
      simp only [WithBotTop.coe_le_coe]
      omega
    have hi₀'₁ : i₀' ≤ i₁ := by
      dsimp only [i₀', i₁, r₁, r]
      simp only [WithBotTop.coe_le_coe]
      omega
    have hi₃₃' : i₃ ≤ i₃' := by
      dsimp only [i₃, i₃', r₀, r₁, r]
      simp only [WithBotTop.coe_le_coe]
      omega
    have hi₂₃' : i₂ ≤ i₃' := hi₂₃.trans hi₃₃'
    have hNoOut : ∀ z,
        ¬ (ComplexShape.spectralSequenceNat ⟨-r₀, r₀ - 1⟩).Rel pq z := by
      rintro ⟨a, b⟩ hz
      dsimp only [pq] at hz
      simp only [ComplexShape.spectralSequenceNat_rel_iff] at hz
      dsimp only [r₀, r] at hz
      omega
    let hLeft : IsZero ((Y.H n₂).obj
        (CategoryTheory.ComposableArrows.mk₁
          (homOfLE (show i₀' ≤ i₀ by exact hi₀'₀)))) :=
      Y.isZero_H_obj_mk₁_i₀_le' core r₀ r₁ hrr (hr t) pq hNoOut
        n₂ hnPlus i₀' i₀ hi₀' hi₀
    let ePage : P t ≅ Y.E
        (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃)
        n₀ n₁ n₂ hn₁ hn₂ :=
      Y.spectralSequencePageXIso core r₀ (hr t) pq
        i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃
        n₀ n₁ n₂ hn (hn₁ := hn₁) (hn₂ := hn₂)
    let eLeft := Y.isoMapFourδ₁Toδ₀'
      i₀' i₀ i₁ i₂ i₃ hi₀'₀ hi₀₁ hi₁₂ hi₂₃
        n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
    let rightMap := Y.mapFourδ₄Toδ₃'
      i₀' i₁ i₂ i₃ i₃' hi₀'₁ hi₁₂ hi₂₃ hi₃₃'
        n₀ n₁ n₂ hn₁ hn₂
    let ePageNext : P (t + 1) ≅ Y.E
        (homOfLE hi₀'₁) (homOfLE hi₁₂) (homOfLE hi₂₃')
        n₀ n₁ n₂ hn₁ hn₂ :=
      Y.spectralSequencePageXIso core r₁ (hr (t + 1)) pq
        i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃'
        n₀ n₁ n₂ hn (hn₁ := hn₁) (hn₂ := hn₂)
    let hData := Y.spectralSequenceHomologyData core
      r₀ r₁ hrr (hr t) pqPrev pq pqNext rfl rfl
      i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
      n₀ n₁ n₂ hn hn₁ hn₂
    have hIn0 := h₂.page_d_to_survivor_eq_zero t p q hp pqPrev
    have hIn : ((E).page r₀ (hr t)).d pqPrev pq = 0 := by
      change ((E).page (((2 + t : ℕ) : ℤ))).d pqPrev pq = 0
      exact hIn0
    let _ : IsIso rightMap := by
      change IsIso hData.left.π
      exact hData.left.isIso_π hIn
    exact ePage ≪≫ eLeft.symm ≪≫ asIso rightMap ≪≫ ePageNext.symm
  let iter : ∀ t : ℕ, P 0 ≅ P t := fun t =>
    Nat.rec
      (motive := fun t => P 0 ≅ P t)
      (Iso.refl _)
      (fun t e => e ≪≫ step t)
      t
  have hBase : (iter 0).hom = 𝟙 _ := by
    rfl
  change P 0 ≅ P k
  exact iter k

private theorem partialTotalTwoColumnPageTwoToPageIso_zero_hom
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (p q : ℕ) (hp : p ≤ 1) :
    (B.partialTotalTwoColumnPageTwoToPageIso h₂ 0 p q hp).hom = 𝟙 _ := by
  unfold partialTotalTwoColumnPageTwoToPageIso
  dsimp only
  rfl

/- The successor equation is proved only inside the finite induction, after
the public recursion has exposed its local successor term.
private theorem partialTotalTwoColumnPageTwoToPageIso_succ_hom
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) :
    (B.partialTotalTwoColumnPageTwoToPageIso h₂ (k + 1) p q hp).hom =
      (B.partialTotalTwoColumnPageTwoToPageIso h₂ k p q hp).hom ≫
        (partialTotalTwoColumnPageSuccIso B h₂ k p q hp).hom := by
  unfold partialTotalTwoColumnPageTwoToPageIso
  dsimp only
  simp only [Iso.trans_hom]
  congr 1 <;> first | rfl | subsingleton
-/

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
private theorem partialTotalTwoColumnDirectPageToStable_finite
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q k : ℕ) :
    partialTotalTwoColumnDirectPageToStable B q 0 =
      (B.partialTotalTwoColumnPageTwoToPageIso h₂ k 0 q (by omega)).hom ≫
        partialTotalTwoColumnDirectPageToStable B q k := by
  induction k with
  | zero =>
      rw [partialTotalTwoColumnPageTwoToPageIso_zero_hom B h₂ 0 q (by omega),
        Category.id_comp]
  | succ k ih =>
      let Y := B.partialTotalSpectralObject
      let r : ℤ := ((2 + k : ℕ) : ℤ)
      let r' : ℤ := ((2 + k.succ : ℕ) : ℤ)
      have hrr' : r + 1 = r' := by
        dsimp only [r, r']
        omega
      have hr : (1 : ℤ) ≤ r := by
        dsimp only [r]
        omega
      have hr' : (1 : ℤ) ≤ r' := by omega
      let pq : ℕ × ℕ := (0, q)
      let i₀' : EInt := (((((0 : ℕ) : ℤ)) - r' : ℤ) : EInt)
      let i₀ : EInt := (((((0 : ℕ) : ℤ)) - r : ℤ) : EInt)
      let i₁ : EInt := (((((0 : ℕ) : ℤ)) - 1 : ℤ) : EInt)
      let i₂ : EInt := ((((0 : ℕ) : ℤ)) : EInt)
      let i₃ : EInt := (((((0 : ℕ) : ℤ)) + r - 1 : ℤ) : EInt)
      let i₃' : EInt := (((((0 : ℕ) : ℤ)) + r' - 1 : ℤ) : EInt)
      let n₀ : ℤ := -(0 : ℤ) - (q : ℤ) - 1
      let n₁ : ℤ := -(0 : ℤ) - (q : ℤ)
      let n₂ : ℤ := -(0 : ℤ) - (q : ℤ) + 1
      have hn : n₁ = (core).deg pq := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
            pq).symm
      have hn₁ : n₀ + 1 = n₁ := by
        dsimp only [n₀, n₁]
        omega
      have hn₂ : n₁ + 1 = n₂ := by
        dsimp only [n₁, n₂]
      have hnPlus : n₂ = (core).deg pq + 1 := by
        rw [← hn]
      have hi₀' : i₀' = (core).i₀ r' pq hr' := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
            r' pq hr').symm
      have hi₀ : i₀ = (core).i₀ r pq hr := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀
            r pq hr).symm
      have hi₁ : i₁ = (core).i₁ pq := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁
            pq).symm
      have hi₂ : i₂ = (core).i₂ pq := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂
            pq).symm
      have hi₃ : i₃ = (core).i₃ r pq hr := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
            r pq hr).symm
      have hi₃' : i₃' = (core).i₃ r' pq hr' := by
        exact
          (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃
            r' pq hr').symm
      have hi₀neg : i₀ = ((-r : ℤ) : EInt) := by
        dsimp only [i₀]
        congr 1
        omega
      have hi₀'neg : i₀' = ((-r' : ℤ) : EInt) := by
        dsimp only [i₀']
        congr 1
      have hiBot₀' : (⊥ : EInt) ≤ i₀' := by simp
      have hi₀'₀ : i₀' ≤ i₀ := by
        dsimp only [i₀', i₀]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₀'₁ : i₀' ≤ i₁ := by
        dsimp only [i₀', i₁]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₀₁ : i₀ ≤ i₁ := by
        dsimp only [i₀, i₁]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₁₂ : i₁ ≤ i₂ := by
        dsimp only [i₁, i₂]
        simp
      have hi₂₃ : i₂ ≤ i₃ := by
        dsimp only [i₂, i₃]
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₃₃' : i₃ ≤ i₃' := by
        dsimp only [i₃, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₂₃' : i₂ ≤ i₃' := by
        dsimp only [i₂, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega
      have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
      have hi₃'Top : i₃' ≤ (⊤ : EInt) := by simp
      have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
      have hCurrentLeft : IsZero ((Y.H n₂).obj
          (CategoryTheory.ComposableArrows.mk₁
            (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
        rw [hi₀neg]
        exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg n₂ (-r) (by
          dsimp only [r]
          omega)
      have hNextLeft : IsZero ((Y.H n₂).obj
          (CategoryTheory.ComposableArrows.mk₁
            (homOfLE (show (⊥ : EInt) ≤ i₀' by simp)))) := by
        rw [hi₀'neg]
        exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg n₂ (-r') (by
          dsimp only [r']
          omega)
      have hNoOut : ∀ z,
          ¬ (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel pq z := by
        rintro ⟨a, b⟩ hz
        dsimp only [pq] at hz
        simp only [ComplexShape.spectralSequenceNat_rel_iff] at hz
        dsimp only [r] at hz
        omega
      let hStepLeft : IsZero ((Y.H n₂).obj
          (CategoryTheory.ComposableArrows.mk₁ (homOfLE hi₀'₀))) :=
        Y.isZero_H_obj_mk₁_i₀_le' core r r' hrr' hr pq hNoOut
          n₂ hnPlus i₀' i₀ hi₀' hi₀
      let Lstep := Y.isoMapFourδ₁Toδ₀'
        i₀' i₀ i₁ i₂ i₃ hi₀'₀ hi₀₁ hi₁₂ hi₂₃
          n₀ n₁ n₂ hStepLeft hn₁ hn₂
      let Laux := Y.isoMapFourδ₁Toδ₀'
        (⊥ : EInt) i₀' i₁ i₂ i₃ hiBot₀' hi₀'₁ hi₁₂ hi₂₃
          n₀ n₁ n₂ hNextLeft hn₁ hn₂
      let Lnext := Y.isoMapFourδ₁Toδ₀'
        (⊥ : EInt) i₀' i₁ i₂ i₃' hiBot₀' hi₀'₁ hi₁₂ hi₂₃'
          n₀ n₁ n₂ hNextLeft hn₁ hn₂
      let Lcurrent := Y.isoMapFourδ₁Toδ₀'
        (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
          n₀ n₁ n₂ hCurrentLeft hn₁ hn₂
      let Rstep := Y.mapFourδ₄Toδ₃'
        i₀' i₁ i₂ i₃ i₃' hi₀'₁ hi₁₂ hi₂₃ hi₃₃'
          n₀ n₁ n₂ hn₁ hn₂
      let Rbot := Y.mapFourδ₄Toδ₃'
        (⊥ : EInt) i₁ i₂ i₃ i₃' hiBot₁ hi₁₂ hi₂₃ hi₃₃'
          n₀ n₁ n₂ hn₁ hn₂
      let RtopNext := Y.mapFourδ₄Toδ₃'
        (⊥ : EInt) i₁ i₂ i₃' ⊤ hiBot₁ hi₁₂ hi₂₃' hi₃'Top
          n₀ n₁ n₂ hn₁ hn₂
      let RtopCurrent := Y.mapFourδ₄Toδ₃'
        (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
          n₀ n₁ n₂ hn₁ hn₂
      let ePageCurrent := Y.spectralSequencePageXIso core r hr pq
        i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
          (hn₁ := hn₁) (hn₂ := hn₂)
      let ePageNext := Y.spectralSequencePageXIso core r' hr' pq
        i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃'
          n₀ n₁ n₂ hn (hn₁ := hn₁) (hn₂ := hn₂)
      let eTarget :
          Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
              (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ ≅
            B.partialTotalStableObj q 0 :=
        B.partialTotalZeroColumnStableTargetIso q
      have hInter : Laux.hom ≫ Rstep = Rbot ≫ Lnext.hom := by
        exact Y.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'
          (⊥ : EInt) i₀' i₁ i₂ i₃ i₃'
          hiBot₀' hi₀'₁ hi₁₂ hi₂₃ hi₃₃'
          n₀ n₁ n₂ hn₁ hn₂
      have hCross : Rstep ≫ Lnext.inv = Laux.inv ≫ Rbot := by
        rw [← cancel_epi Laux.hom]
        rw [reassoc_of% hInter]
        rw [Lnext.hom_inv_id, Category.comp_id,
          Laux.hom_inv_id_assoc]
      have hLeftComp : Laux.hom ≫ Lstep.hom = Lcurrent.hom := by
        exact Y.mapFourδ₁Toδ₀'_comp
          (⊥ : EInt) i₀' i₀ i₁ i₂ i₃
          hiBot₀' hi₀'₀ hi₀₁ hi₁₂ hi₂₃
          n₀ n₁ n₂ hn₁ hn₂
      have hLeftInv : Lstep.inv ≫ Laux.inv = Lcurrent.inv := by
        apply (cancel_mono Lcurrent.hom).1
        rw [Lcurrent.inv_hom_id]
        rw [← hLeftComp]
        rw [Category.assoc, Laux.inv_hom_id_assoc]
        exact Lstep.inv_hom_id
      have hRightComp : Rbot ≫ RtopNext = RtopCurrent := by
        exact Y.mapFourδ₄Toδ₃'_comp
          (⊥ : EInt) i₁ i₂ i₃ i₃' ⊤
          hiBot₁ hi₁₂ hi₂₃ hi₃₃' hi₃'Top
          n₀ n₁ n₂ hn₁ hn₂
      have hOuter :
          Lstep.inv ≫ Rstep ≫ Lnext.inv ≫ RtopNext =
            Lcurrent.inv ≫ RtopCurrent := by
        rw [reassoc_of% hCross, reassoc_of% hLeftInv, hRightComp]
      have hRec :
          ePageCurrent.hom ≫ Lstep.inv ≫ Rstep ≫ ePageNext.inv ≫
              partialTotalTwoColumnDirectPageToStable B q k.succ =
            partialTotalTwoColumnDirectPageToStable B q k := by
        unfold partialTotalTwoColumnDirectPageToStable
        dsimp only
        change ePageCurrent.hom ≫ Lstep.inv ≫ Rstep ≫ ePageNext.inv ≫
            ePageNext.hom ≫ Lnext.inv ≫ RtopNext ≫ eTarget.hom =
          ePageCurrent.hom ≫ Lcurrent.inv ≫ RtopCurrent ≫ eTarget.hom
        simp only [ePageNext.inv_hom_id_assoc]
        rw [reassoc_of% hOuter]
      have hRecAdd :
          ePageCurrent.hom ≫ Lstep.inv ≫ Rstep ≫ ePageNext.inv ≫
              partialTotalTwoColumnDirectPageToStable B q (k + 1) =
            partialTotalTwoColumnDirectPageToStable B q k := by
        simpa only [Nat.add_one] using hRec
      have hIsoSucc :
          (B.partialTotalTwoColumnPageTwoToPageIso h₂ (k + 1)
              0 q (by omega)).hom =
            (B.partialTotalTwoColumnPageTwoToPageIso h₂ k
                0 q (by omega)).hom ≫
              (partialTotalTwoColumnPageSuccIso B h₂ k
                0 q (Nat.zero_le 1)).hom := by
        rw [partialTotalTwoColumnPageSuccIso_hom B h₂ k
          0 q (Nat.zero_le 1)]
        unfold partialTotalTwoColumnPageTwoToPageIso
        dsimp only [Nat.rec]
        rfl
      have hStepHom :
          (partialTotalTwoColumnPageSuccIso B h₂ k
              0 q (Nat.zero_le 1)).hom =
            ePageCurrent.hom ≫ Lstep.inv ≫ Rstep ≫ ePageNext.inv := by
        rw [partialTotalTwoColumnPageSuccIso_hom B h₂ k
          0 q (Nat.zero_le 1)]
        rfl
      rw [ih]
      rw [hIsoSucc]
      rw [hStepHom]
      have hWhisker := congrArg
        (fun z =>
          (B.partialTotalTwoColumnPageTwoToPageIso h₂ k
            0 q (by omega)).hom ≫ z) hRecAdd.symm
      simpa only [Category.assoc] using hWhisker

private theorem partialTotalTwoColumnDirectPageToStable_terminal
    (q : ℕ) :
    partialTotalTwoColumnDirectPageToStable B q q =
      ((E).pageXIsoOfEq (0, q) (((2 + q : ℕ) : ℤ))
          (((q + 2 : ℕ) : ℤ)) (by omega)).hom ≫
        (show ((E).page (((q + 2 : ℕ) : ℤ))).X (0, q) ≅
            B.partialTotalStableObj q 0 from
          (E).pageXIsoOfEq (0, q) (((q + 2 : ℕ) : ℤ))
              (((0 + q + 2 : ℕ) : ℤ)) (by omega) ≪≫
            B.partialTotalStablePageIso 0 q ≪≫
            eqToIso (by rw [Nat.zero_add])).hom := by
  let Y := B.partialTotalSpectralObject
  let rD : ℤ := ((2 + q : ℕ) : ℤ)
  have hrD : (1 : ℤ) ≤ rD := by
    dsimp only [rD]
    omega
  let i₀ : EInt := (((((0 : ℕ) : ℤ)) - rD : ℤ) : EInt)
  let i₁ : EInt := (((((0 : ℕ) : ℤ)) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((((0 : ℕ) : ℤ)) : EInt)
  let i₃ : EInt := (((((0 : ℕ) : ℤ)) + rD - 1 : ℤ) : EInt)
  let n₀ : ℤ := -(0 : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(0 : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(0 : ℤ) - (q : ℤ) + 1
  have hn : n₁ = (core).deg (0, q) := by
    exact
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
        (0, q)).symm
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := by
    dsimp only [i₁, i₂]
    simp
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
  have hi₀neg : i₀ = ((-rD : ℤ) : EInt) := by
    dsimp only [i₀, rD]
    congr 1
    omega
  have hLeft : IsZero ((Y.H n₂).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
    rw [hi₀neg]
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg n₂ (-rD) (by
      dsimp only [rD]
      omega)
  let eLeft := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
  let rightMap := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
      n₀ n₁ n₂ hn₁ hn₂
  let eTarget :
      Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
          (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ ≅
        B.partialTotalStableObj q 0 :=
    B.partialTotalZeroColumnStableTargetIso q
  let I := {r : ℤ // r = rD}
  let sD : I := ⟨rD, rfl⟩
  let rS : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  let sS : I := ⟨rS, by
    dsimp only [rS, rD]
    omega⟩
  have hs : sD = sS := by
    apply Subtype.ext
    dsimp only [sD, sS, rS, rD]
    omega
  let ePage (s : I) :
      ((E).page s.1 (by rw [s.2]; exact hrD)).X (0, q) ≅
        Y.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃)
          n₀ n₁ n₂ hn₁ hn₂ := by
    have hrs : (1 : ℤ) ≤ s.1 := by
      rw [s.2]
      exact hrD
    have h₀ : i₀ = (core).i₀ s.1 (0, q) hrs := by
      rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
      dsimp only [i₀]
      congr 1
      rw [s.2]
    have h₁ : i₁ = (core).i₁ (0, q) := by
      exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁
        (0, q)).symm
    have h₂ : i₂ = (core).i₂ (0, q) := by
      exact (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂
        (0, q)).symm
    have h₃ : i₃ = (core).i₃ s.1 (0, q) hrs := by
      rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
      dsimp only [i₃]
      congr 1
      rw [s.2]
    exact Y.spectralSequencePageXIso core s.1 hrs (0, q)
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn
        (hn₁ := hn₁) (hn₂ := hn₂)
  have hNat := CategoryTheory.eqToHom_iso_hom_naturality ePage hs
  let pageEq₁ := (E).pageXIsoOfEq (0, q) (((2 + q : ℕ) : ℤ))
    (((q + 2 : ℕ) : ℤ)) (by omega)
  let pageEq₂ := (E).pageXIsoOfEq (0, q) (((q + 2 : ℕ) : ℤ))
    (((0 + q + 2 : ℕ) : ℤ)) (by omega)
  have hPage : pageEq₁.hom ≫ pageEq₂.hom ≫ (ePage sS).hom =
      (ePage sD).hom := by
    dsimp only [pageEq₁, pageEq₂]
    unfold CategoryTheory.SpectralSequence.pageXIsoOfEq
    simpa only [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id] using hNat.symm
  let canonical := (ePage sD).hom ≫ eLeft.inv ≫ rightMap ≫ eTarget.hom
  let finalEq : B.partialTotalStableObj (0 + q) 0 ≅
      B.partialTotalStableObj q 0 :=
    eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
      (Nat.zero_add q))
  have hStable : pageEq₂.hom ≫ (B.partialTotalStablePageIso 0 q).hom ≫
      finalEq.hom =
        pageEq₂.hom ≫ B.partialTotalStablePageZeroColumnHom q := by
    dsimp only [finalEq]
    rw [B.partialTotalStablePageIso_zero_hom_comp_eqToIso_hom q]
  have hAligned : B.partialTotalStablePageZeroColumnHom q =
      (ePage sS).hom ≫ eLeft.inv ≫ rightMap ≫ eTarget.hom := by
    rfl
  have hDirect : partialTotalTwoColumnDirectPageToStable B q q = canonical := by
    unfold partialTotalTwoColumnDirectPageToStable
    dsimp only [canonical]
  rw [hDirect]
  rw [show ((E).pageXIsoOfEq (0, q) (((2 + q : ℕ) : ℤ))
      (((q + 2 : ℕ) : ℤ)) (by omega)).hom = pageEq₁.hom by rfl]
  change canonical = pageEq₁.hom ≫
    (pageEq₂.hom ≫ (B.partialTotalStablePageIso 0 q).hom ≫ finalEq.hom)
  rw [hStable]
  rw [hAligned]
  rw [reassoc_of% hPage]

/-- Under a two-column page-two hypothesis, the literal existing zero-column
page-to-stable map is the explicit finite survivor coordinate followed by
the stable-page coordinate. -/
theorem partialTotalZeroColumnPageToStable_eq_pageTwoToStable_of_twoColumn
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    B.partialTotalZeroColumnPageToStable q =
      (B.partialTotalTwoColumnPageTwoToPageIso h₂ q 0 q (Nat.zero_le 1) ≪≫
        (show ((E).page (((2 + q : ℕ) : ℤ))).X (0, q) ≅
            ((E).page (((q + 2 : ℕ) : ℤ))).X (0, q) from
          (E).pageXIsoOfEq (0, q) (((2 + q : ℕ) : ℤ))
            (((q + 2 : ℕ) : ℤ))
            (congrArg (fun n : ℕ => (n : ℤ)) (Nat.add_comm 2 q))) ≪≫
        (show ((E).page (((q + 2 : ℕ) : ℤ))).X (0, q) ≅
            B.partialTotalStableObj q 0 from
          (E).pageXIsoOfEq (0, q) (((q + 2 : ℕ) : ℤ))
              (((0 + q + 2 : ℕ) : ℤ))
              (congrArg (fun n : ℕ => (n : ℤ))
                (congrArg (fun m : ℕ => m + 2) (Nat.zero_add q).symm)) ≪≫
            B.partialTotalStablePageIso 0 q ≪≫
            eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
              (Nat.zero_add q)))).hom := by
  rw [← partialTotalTwoColumnDirectPageToStable_zero B q]
  rw [partialTotalTwoColumnDirectPageToStable_finite B h₂ q q]
  rw [partialTotalTwoColumnDirectPageToStable_terminal B q]
  simp only [Iso.trans_hom]

end HomologicalComplex₂

end
