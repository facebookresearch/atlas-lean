/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua, Codex -/
module

import MathlibExt.Algebra.Homology.PartialTotalConnectingDifferential
import MathlibExtTest.Algebra.Homology.TwoRowFixture
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Field.Rat

/-!
# A nonzero connecting map between two zero-differential rows

The two rows are the degree-zero rational module. Their horizontal map is a specified
endomorphism f. Canonical partial-total, zero-extension and zero-differential homology
coordinates identify the adjacent-row connecting map with f in degree zero. In particular
the horizontal identity sends 1 to +1, whereas the horizontal-zero map sends it to zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open MathlibExtTest.Algebra.Homology.TwoRowFixture

namespace MathlibExtTest.PartialTotalConnectingDifferential

private abbrev C := ModuleCat.{0} ℚ
private abbrev Q : C := ModuleCat.of ℚ ℚ
private abbrev e := ComplexShape.embeddingDownNat
private abbrev B (f : verticalRow ⟶ verticalRow) := twoRows f
private abbrev K₀ (f : verticalRow ⟶ verticalRow) := (B f).partialTotal 0
private abbrev K₁ (f : verticalRow ⟶ verticalRow) := (B f).partialTotal 1
private abbrev R₀ (f : verticalRow ⟶ verticalRow) := (B f).totalRow 0
private abbrev R₁ (f : verticalRow ⟶ verticalRow) := (B f).totalRow 1
private abbrev S (f : verticalRow ⟶ verticalRow) :=
  (B f).partialTotalStepCochainShortComplex 1

private lemma horizontal_d (f : verticalRow ⟶ verticalRow) : (B f).d 1 0 = f :=
  ChainComplex.mk_d_1_0 _ _ _ _ _ _ _

private lemma row₀_d_zero (f : verticalRow ⟶ verticalRow) (i j : ℕ) :
    (R₀ f).d i j = 0 := by
  rw [(B f).totalRow_d_eq 0 i j i j (Nat.zero_add i) (Nat.zero_add j)]
  have hz : ((B f).X 0).d i j = 0 := rfl
  rw [hz, smul_zero, zero_comp, comp_zero]

private lemma row₁_d_zero (f : verticalRow ⟶ verticalRow) (i j : ℕ) :
    (R₁ f).d i j = 0 := by
  cases i with
  | zero => exact ((B f).totalRow_isZero_X 1 0 (by decide)).eq_of_src _ _
  | succ i =>
    cases j with
    | zero => exact ((B f).totalRow_isZero_X 1 0 (by decide)).eq_of_tgt _ _
    | succ j =>
      rw [(B f).totalRow_d_eq 1 i j (i + 1) (j + 1) (by omega) (by omega)]
      have hz : ((B f).X 1).d i j = 0 := rfl
      rw [hz, smul_zero, zero_comp, comp_zero]

private lemma extend_zero_d (K : ChainComplex C ℕ)
    (h : ∀ i j, K.d i j = 0) (i j : ℤ) : (K.extend e).d i j = 0 := by
  cases hi : e.r i with
  | none => exact (K.isZero_extend_X' e i hi).eq_of_src _ _
  | some a =>
    cases hj : e.r j with
    | none => exact (K.isZero_extend_X' e j hj).eq_of_tgt _ _
    | some b =>
      rw [K.extend_d_eq e (e.f_eq_of_r_eq_some hi) (e.f_eq_of_r_eq_some hj)]
      rw [h, zero_comp, comp_zero]

private abbrev zeroData (K : CochainComplex C ℤ) (i : ℤ)
    (h : ∀ a b, K.d a b = 0) :=
  ShortComplex.HomologyData.ofZeros (K.sc i) (h _ _) (h _ _)

private def zeroHomologyIso (K : CochainComplex C ℤ) (i : ℤ)
    (h : ∀ a b, K.d a b = 0) : K.homology i ≅ K.X i :=
  (zeroData K i h).left.homologyIso

private lemma cycle_coordinate (K : CochainComplex C ℤ) (i : ℤ)
    (h : ∀ a b, K.d a b = 0) {A : C} (x : A ⟶ K.X i) :
    K.liftCycles x (i + 1) (by
      exact (ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl))
      (by rw [h, comp_zero]) ≫ K.homologyπ i ≫ (zeroHomologyIso K i h).hom = x := by
  change (K.sc i).liftCycles x _ ≫ (K.sc i).homologyπ ≫
    (zeroData K i h).left.homologyIso.hom = x
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.liftCycles_comp_cyclesIso_hom]
  simpa only [ShortComplex.HomologyData.ofZeros, ShortComplex.LeftHomologyData.ofZeros] using
    (zeroData K i h).left.liftK_i x _

private def row₀ObjectIso (f : verticalRow ⟶ verticalRow) : (R₀ f).X 0 ≅ Q :=
  (B f).totalRowXIso 0 0 0 rfl

private def row₁ObjectIso (f : verticalRow ⟶ verticalRow) : (R₁ f).X 1 ≅ Q :=
  (B f).totalRowXIso 1 0 1 rfl

private def row₀ExtendedObjectIso (f : verticalRow ⟶ verticalRow) :
    ((R₀ f).extend e).X 0 ≅ Q :=
  (R₀ f).extendXIso e (i := 0) (i' := 0) rfl ≪≫ row₀ObjectIso f

private def row₁ExtendedObjectIso (f : verticalRow ⟶ verticalRow) :
    ((R₁ f).extend e).X (-1) ≅ Q :=
  (R₁ f).extendXIso e (i := 1) (i' := -1) rfl ≪≫ row₁ObjectIso f

private def row₀HomologyCoordinate (f : verticalRow ⟶ verticalRow) :
    (R₀ f).homology 0 ≅ Q :=
  ((R₀ f).extendHomologyIso e (j := 0) (j' := 0) rfl).symm ≪≫
    zeroHomologyIso ((R₀ f).extend e) 0 (extend_zero_d _ (row₀_d_zero f)) ≪≫
      row₀ExtendedObjectIso f

private def row₁HomologyCoordinate (f : verticalRow ⟶ verticalRow) :
    (R₁ f).homology 1 ≅ Q :=
  ((R₁ f).extendHomologyIso e (j := 1) (j' := -1) rfl).symm ≪≫
    zeroHomologyIso ((R₁ f).extend e) (-1) (extend_zero_d _ (row₁_d_zero f)) ≪≫
      row₁ExtendedObjectIso f

private def upperComponent (f : verticalRow ⟶ verticalRow) : Q ⟶ (K₁ f).X 1 :=
  (B f).partialTotalComponent 1 ⟨1, by decide⟩ 0 1 rfl

private def lowerComponent (f : verticalRow ⟶ verticalRow) : Q ⟶ (K₀ f).X 0 :=
  (B f).partialTotalComponent 0 ⟨0, by decide⟩ 0 0 rfl

private def oldComponent (f : verticalRow ⟶ verticalRow) : Q ⟶ (K₁ f).X 0 :=
  (B f).partialTotalComponent 1 ⟨0, by decide⟩ 0 0 rfl

private lemma component_inclusion (f : verticalRow ⟶ verticalRow) :
    lowerComponent f ≫ ((B f).partialTotalMap (Nat.zero_le 1)).f 0 = oldComponent f := by
  dsimp only [lowerComponent, oldComponent]
  exact (B f).partialTotalComponent_partialTotalMap (Nat.zero_le 1) ⟨0, by decide⟩ 0 0 rfl

private lemma component_d (f : verticalRow ⟶ verticalRow) :
    upperComponent f ≫ (K₁ f).d 1 0 = f.f 0 ≫ oldComponent f := by
  dsimp only [upperComponent, oldComponent]
  apply (cancel_mono (((B f).partialTotalι 1).f 0)).1
  rw [← ((B f).partialTotalι 1).comm 1 0]
  rw [← Category.assoc, (B f).partialTotalComponent_comp_partialTotalι]
  rw [HomologicalComplex₂.total_d, comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂]
  rw [(B f).d₁_eq (ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
    0 0 rfl]
  rw [(B f).d₂_eq_zero (ComplexShape.down ℕ) 1 0 0 (by
    intro h
    change (ComplexShape.down ℕ).next 0 + 1 = 0 at h
    omega)]
  have hs : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (1, 0) = (1 : ℤˣ) := rfl
  rw [hs, one_smul, add_zero, horizontal_d]
  rw [(B f).partialTotalComponent_comp_partialTotalι]

private def upperLift (f : verticalRow ⟶ verticalRow) : Q ⟶ (S f).X₂.X (-1) :=
  upperComponent f ≫ ((K₁ f).extendXIso e (i := 1) (i' := -1) rfl).inv

private def sourceRepresentative (f : verticalRow ⟶ verticalRow) :
    Q ⟶ (S f).X₃.X (-1) :=
  (row₁ExtendedObjectIso f).inv

private def boundaryRepresentative (f : verticalRow ⟶ verticalRow) : Q ⟶ (S f).X₁.X 0 :=
  f.f 0 ≫ lowerComponent f ≫ ((K₀ f).extendXIso e (i := 0) (i' := 0) rfl).inv

private lemma quotient_lift (f : verticalRow ⟶ verticalRow) :
    upperLift f ≫ (S f).g.f (-1) = sourceRepresentative f := by
  change upperComponent f ≫ ((K₁ f).extendXIso e (i := 1) (i' := -1) rfl).inv ≫
    (HomologicalComplex.extendMap ((B f).partialTotalRowQuotient 1) e).f (-1) =
      (row₁ObjectIso f).inv ≫ ((R₁ f).extendXIso e (i := 1) (i' := -1) rfl).inv
  rw [HomologicalComplex.extendMap_f _ e (i := 1) (i' := -1) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp only [upperComponent, row₁ObjectIso]
  rw [(B f).partialTotalComponent_comp_partialTotalRowQuotient_assoc]

private lemma boundary_lift (f : verticalRow ⟶ verticalRow) :
    boundaryRepresentative f ≫ (S f).f.f 0 = upperLift f ≫ (S f).X₂.d (-1) 0 := by
  change (f.f 0 ≫ lowerComponent f ≫ ((K₀ f).extendXIso e (i := 0) (i' := 0) rfl).inv) ≫
    (HomologicalComplex.extendMap ((B f).partialTotalMap (Nat.zero_le 1)) e).f 0 =
      (upperComponent f ≫ ((K₁ f).extendXIso e (i := 1) (i' := -1) rfl).inv) ≫
        ((K₁ f).extend e).d (-1) 0
  rw [HomologicalComplex.extendMap_f _ e (i := 0) (i' := 0) rfl,
    HomologicalComplex.extend_d_eq _ e (i := 1) (i' := -1) (j := 0) (j' := 0) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hi : (f.f 0 ≫ lowerComponent f) ≫
      ((B f).partialTotalMap (Nat.zero_le 1)).f 0 = f.f 0 ≫ oldComponent f := by
    simpa only [Category.assoc] using congrArg (fun z => f.f 0 ≫ z) (component_inclusion f)
  have hd : upperComponent f ≫ (K₁ f).d 1 0 = f.f 0 ≫ oldComponent f := component_d f
  have hraw : (f.f 0 ≫ lowerComponent f) ≫
      ((B f).partialTotalMap (Nat.zero_le 1)).f 0 = upperComponent f ≫ (K₁ f).d 1 0 :=
    hi.trans hd.symm
  simpa only [Category.assoc] using congrArg
    (fun z : Q ⟶ (K₁ f).X 0 =>
      z ≫ ((K₁ f).extendXIso e (i := 0) (i' := 0) rfl).inv) hraw

private def quotient₀ (f : verticalRow ⟶ verticalRow) :
    (S f).X₁ ⟶ (R₀ f).extend e :=
  HomologicalComplex.extendMap ((B f).partialTotalRowQuotient 0) e

private lemma step₀_quotient (f : verticalRow ⟶ verticalRow) :
    ((B f).partialTotalStepCochainShortComplex 0).g = quotient₀ f := rfl

private lemma boundary_coordinate (f : verticalRow ⟶ verticalRow) :
    boundaryRepresentative f ≫ (quotient₀ f).f 0 ≫
      (row₀ExtendedObjectIso f).hom = f.f 0 := by
  change (f.f 0 ≫ lowerComponent f ≫ ((K₀ f).extendXIso e (i := 0) (i' := 0) rfl).inv) ≫
    (HomologicalComplex.extendMap ((B f).partialTotalRowQuotient 0) e).f 0 ≫
      ((R₀ f).extendXIso e (i := 0) (i' := 0) rfl).hom ≫ (row₀ObjectIso f).hom = f.f 0
  rw [HomologicalComplex.extendMap_f _ e (i := 0) (i' := 0) rfl]
  dsimp only [K₀, R₀]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp only [lowerComponent, row₀ObjectIso]
  rw [(B f).partialTotalComponent_comp_partialTotalRowQuotient_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma step₁_row_iso_refl (f : verticalRow ⟶ verticalRow) :
    (B f).partialTotalStepCochainX₃Iso 1 = Iso.refl ((R₁ f).extend e) := by
  change (e.extendFunctor C).mapIso (Iso.refl (R₁ f)) = Iso.refl _
  simp

private lemma step₀_row_iso_refl (f : verticalRow ⟶ verticalRow) :
    (B f).partialTotalStepCochainX₃Iso 0 = Iso.refl ((R₀ f).extend e) := by
  change (e.extendFunctor C).mapIso (Iso.refl (R₀ f)) = Iso.refl _
  simp

private lemma adjacent_iso_refl (f : verticalRow ⟶ verticalRow) :
    (B f).partialTotalAdjacentStepCochainIso 0 = Iso.refl ((K₀ f).extend e) := by
  change (e.extendFunctor C).mapIso (Iso.refl (K₀ f)) = Iso.refl _
  simp

private lemma connecting_model (f : verticalRow ⟶ verticalRow) :
    (B f).partialTotalE₁ConnectingDifferential 0 0 =
      ((R₁ f).extendHomologyIso e (j := 1) (j' := -1) rfl).inv ≫
        ((B f).partialTotalStepCochainShortExact 1).δ (-1) 0 (by decide) ≫
        HomologicalComplex.homologyMap (quotient₀ f) 0 ≫
        ((R₀ f).extendHomologyIso e (j := 0) (j' := 0) rfl).hom := by
  unfold HomologicalComplex₂.partialTotalE₁ConnectingDifferential
  rw [step₁_row_iso_refl, adjacent_iso_refl, step₀_row_iso_refl, step₀_quotient]
  simp only [HomologicalComplex.homologyMapIso, Iso.refl_hom, Iso.refl_inv,
    HomologicalComplex.homologyMap_id,
    Category.id_comp, Category.comp_id]

/-- The actual adjacent-row connecting map in rational coordinates is the horizontal map. -/
theorem connecting_coordinate (f : verticalRow ⟶ verticalRow) :
    (row₁HomologyCoordinate f).inv ≫
      (B f).partialTotalE₁ConnectingDifferential 0 0 ≫
      (row₀HomologyCoordinate f).hom = f.f 0 := by
  let h₁ := extend_zero_d (R₁ f) (row₁_d_zero f)
  let h₀ := extend_zero_d (R₀ f) (row₀_d_zero f)
  let c₃ := ((R₁ f).extend e).liftCycles (sourceRepresentative f) 0
    ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl))
    (by
      change sourceRepresentative f ≫ ((R₁ f).extend e).d (-1) 0 = 0
      rw [h₁, comp_zero]) ≫ ((R₁ f).extend e).homologyπ (-1)
  have hclass : c₃ ≫ (zeroHomologyIso ((R₁ f).extend e) (-1) h₁).hom =
      sourceRepresentative f := by
    dsimp only [c₃]
    simpa only [Category.assoc] using
      cycle_coordinate ((R₁ f).extend e) (-1) h₁ (sourceRepresentative f)
  have hsource : c₃ ≫ (zeroHomologyIso ((R₁ f).extend e) (-1) h₁).hom ≫
      (row₁ExtendedObjectIso f).hom = 𝟙 Q := by
    have hc := congrArg (fun z : Q ⟶ ((R₁ f).extend e).X (-1) =>
      z ≫ (row₁ExtendedObjectIso f).hom) hclass
    simpa only [Category.assoc, sourceRepresentative, Iso.inv_hom_id] using hc
  have hc₃ : c₃ = (row₁ExtendedObjectIso f).inv ≫
      (zeroHomologyIso ((R₁ f).extend e) (-1) h₁).inv := by
    apply (cancel_mono ((zeroHomologyIso ((R₁ f).extend e) (-1) h₁).hom ≫
      (row₁ExtendedObjectIso f).hom)).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id] using hsource
  have hδ := ((B f).partialTotalStepCochainShortExact 1).δ_eq (-1) 0 (by decide)
    (sourceRepresentative f) (by
      change sourceRepresentative f ≫ ((R₁ f).extend e).d (-1) 0 = 0
      rw [h₁, comp_zero])
    (upperLift f) (quotient_lift f) (boundaryRepresentative f) (boundary_lift f)
    1 ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl))
  have htarget : c₃ ≫
      ((B f).partialTotalStepCochainShortExact 1).δ (-1) 0 (by decide) ≫
      HomologicalComplex.homologyMap (quotient₀ f) 0 ≫
      (zeroHomologyIso ((R₀ f).extend e) 0 h₀).hom ≫
      (row₀ExtendedObjectIso f).hom = f.f 0 := by
    rw [← Category.assoc, hδ]
    simp only [Category.assoc]
    rw [HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
    calc
      _ = boundaryRepresentative f ≫ (quotient₀ f).f 0 ≫
          (row₀ExtendedObjectIso f).hom := by
        simpa only [Category.assoc] using congrArg
          (fun z => z ≫ (row₀ExtendedObjectIso f).hom)
          (cycle_coordinate ((R₀ f).extend e) 0 h₀
            (boundaryRepresentative f ≫ (quotient₀ f).f 0))
      _ = f.f 0 := boundary_coordinate f
  rw [connecting_model]
  unfold row₁HomologyCoordinate row₀HomologyCoordinate
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Iso.inv_hom_id,
    Category.comp_id, Category.id_comp]
  rw [hc₃] at htarget
  simpa only [Category.assoc] using htarget

/-- The horizontal identity gives the positive identity connecting map. -/
theorem identity_connecting :
    (row₁HomologyCoordinate (𝟙 verticalRow)).inv ≫
      horizontalIdentity.partialTotalE₁ConnectingDifferential 0 0 ≫
      (row₀HomologyCoordinate (𝟙 verticalRow)).hom = 𝟙 Q := by
  simpa only [B, horizontalIdentity, verticalRow, Q, HomologicalComplex.id_f] using
    connecting_coordinate (𝟙 verticalRow)

/-- In particular the nonzero class with coordinate one is sent to positive one. -/
example : ((row₁HomologyCoordinate (𝟙 verticalRow)).inv ≫
    horizontalIdentity.partialTotalE₁ConnectingDifferential 0 0 ≫
    (row₀HomologyCoordinate (𝟙 verticalRow)).hom).hom (1 : ℚ) = 1 := by
  rw [identity_connecting]
  rfl

/-- The horizontal-zero fixture gives the zero connecting map in the same coordinates. -/
theorem zero_connecting :
    (row₁HomologyCoordinate (0 : verticalRow ⟶ verticalRow)).inv ≫
      horizontalZero.partialTotalE₁ConnectingDifferential 0 0 ≫
      (row₀HomologyCoordinate (0 : verticalRow ⟶ verticalRow)).hom = 0 := by
  simpa only [B, horizontalZero, HomologicalComplex.zero_f] using
    connecting_coordinate (0 : verticalRow ⟶ verticalRow)

example : ((row₁HomologyCoordinate (0 : verticalRow ⟶ verticalRow)).inv ≫
    horizontalZero.partialTotalE₁ConnectingDifferential 0 0 ≫
    (row₀HomologyCoordinate (0 : verticalRow ⟶ verticalRow)).hom).hom (1 : ℚ) = 0 := by
  rw [zero_connecting]
  rfl

end MathlibExtTest.PartialTotalConnectingDifferential
