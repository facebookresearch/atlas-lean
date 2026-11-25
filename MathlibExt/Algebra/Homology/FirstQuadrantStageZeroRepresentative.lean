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

public import MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeHomology
public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCoherentCokernelNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPage
public import MathlibExt.Algebra.Homology.SpectralObject.ZeroColumnEdge
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

-- `spectralSequence_iso` refers to private default proofs in its public signature.
-- This implementation import is needed until those proof arguments are exposed.
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The original complete stage-zero representative

The original complete-filtration representative is compared with the actual
column-zero projection followed by the full incoming-boundary quotient.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace HomologicalComplex₂

private abbrev zero_bottom_arrow : (⊥ : EInt) ⟶ ((0 : ℤ) : EInt) :=
  horizontalBottomToStageMap ((0 : ℤ) : EInt)

private abbrev zero_lower_arrow : (⊥ : EInt) ⟶ ((-1 : ℤ) : EInt) :=
  homOfLE bot_le

private abbrev zero_middle_arrow : ((-1 : ℤ) : EInt) ⟶ ((0 : ℤ) : EInt) :=
  homOfLE (WithBotTop.coe_monotone (by omega))

private abbrev zero_right_arrow : ((0 : ℤ) : EInt) ⟶ ((1 : ℤ) : EInt) :=
  homOfLE (WithBotTop.coe_monotone (by omega))

private def zero_window_map : mk₁ zero_bottom_arrow ⟶ mk₁ zero_middle_arrow :=
  homMk₁ zero_lower_arrow (𝟙 ((0 : ℤ) : EInt)) (Subsingleton.elim _ _)

private def split_window_map :
    mk₃ (𝟙 (⊥ : EInt)) zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt)) ⟶
      mk₃ zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt)) :=
  homMk₃ (𝟙 (⊥ : EInt)) zero_lower_arrow
    (𝟙 ((0 : ℤ) : EInt)) (𝟙 ((0 : ℤ) : EInt))
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

private def cut_window_map :
    mk₃ zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt)) ⟶
      mk₃ (𝟙 ((-1 : ℤ) : EInt)) zero_middle_arrow (𝟙 ((0 : ℤ) : EInt)) :=
  homMk₃ zero_lower_arrow (𝟙 ((-1 : ℤ) : EInt))
    (𝟙 ((0 : ℤ) : EInt)) (𝟙 ((0 : ℤ) : EInt))
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

private def direct_window_map :
    mk₃ (𝟙 (⊥ : EInt)) zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt)) ⟶
      mk₃ (𝟙 ((-1 : ℤ) : EInt)) zero_middle_arrow (𝟙 ((0 : ℤ) : EInt)) :=
  homMk₃ zero_lower_arrow zero_lower_arrow
    (𝟙 ((0 : ℤ) : EInt)) (𝟙 ((0 : ℤ) : EInt))
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

private def extend_window_map :
    mk₃ zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt)) ⟶
      mk₃ zero_lower_arrow zero_middle_arrow zero_right_arrow :=
  homMk₃ (𝟙 (⊥ : EInt)) (𝟙 ((-1 : ℤ) : EInt))
    (𝟙 ((0 : ℤ) : EInt)) zero_right_arrow
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

private theorem split_cut_direct : split_window_map ≫ cut_window_map = direct_window_map := by
  apply hom_ext₃ <;> exact Subsingleton.elim _ _

variable {D : Type uD} [Category.{vD} D] [Abelian D]

private theorem identity_window_packet
    (E : CategoryTheory.Abelian.SpectralObject D EInt)
    {a b : EInt} (f : a ⟶ b) (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    E.pOpcycles f (𝟙 b) n₁ ≫
      E.opcyclesToE (𝟙 a) f (𝟙 b) f (Category.id_comp f)
        n₀ n₁ n₂ hn₁ hn₂ =
      (E.EIsoH f n₀ n₁ n₂ hn₁ hn₂).inv := by
  rw [E.p_opcyclesToE (𝟙 a) f (𝟙 b) f (Category.id_comp f)
    n₀ n₁ n₂ hn₁ hn₂]
  rw [← E.cyclesIsoH_hom_EIsoH_inv
    (n₀ := n₀) (n₁ := n₁) (n₂ := n₂)
    (hn₁ := hn₁) (hn₂ := hn₂) (f := f)]
  rw [← Category.assoc, E.cyclesIsoH_inv_hom_id f n₁ n₂ hn₂,
    Category.id_comp]

private theorem identity_packet_split
    (E : CategoryTheory.Abelian.SpectralObject D EInt) (n : ℤ) :
    (E.EIsoH zero_bottom_arrow (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).inv ≫
        E.map (𝟙 (⊥ : EInt)) zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt))
          zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
          split_window_map (n - 1) n (n + 1) (sub_add_cancel n 1) rfl =
      E.toCycles zero_lower_arrow zero_middle_arrow zero_bottom_arrow
          (Subsingleton.elim _ _) n ≫
        E.πE zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
          (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
  have hNat := E.opcyclesToE_map
    (𝟙 (⊥ : EInt)) zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt))
    zero_bottom_arrow (Category.id_comp zero_bottom_arrow)
    zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
    zero_bottom_arrow (Subsingleton.elim _ _)
    split_window_map (𝟙 (mk₂ zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt))))
    (n - 1) n (n + 1) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (sub_add_cancel n 1) rfl
  calc
    _ = (E.pOpcycles zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt)) n ≫
        E.opcyclesToE (𝟙 (⊥ : EInt)) zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt))
          zero_bottom_arrow (Category.id_comp zero_bottom_arrow)
          (n - 1) n (n + 1) (sub_add_cancel n 1) rfl) ≫
        E.map (𝟙 (⊥ : EInt)) zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt))
          zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
          split_window_map (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
      rw [identity_window_packet]
    _ = E.pOpcycles zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt)) n ≫
        E.opcyclesToE zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
          zero_bottom_arrow (Subsingleton.elim _ _)
          (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
      rw [Category.assoc, hNat, E.opcyclesMap_id, Category.id_comp]
    _ = _ := E.p_opcyclesToE zero_lower_arrow zero_middle_arrow
      (𝟙 ((0 : ℤ) : EInt)) zero_bottom_arrow (Subsingleton.elim _ _)
      (n - 1) n (n + 1) (sub_add_cancel n 1) rfl

private theorem bottom_window_naturality
    (E : CategoryTheory.Abelian.SpectralObject D EInt) (n : ℤ) :
    (E.EIsoH zero_bottom_arrow (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).inv ≫
        E.map (𝟙 (⊥ : EInt)) zero_bottom_arrow (𝟙 ((0 : ℤ) : EInt))
          (𝟙 ((-1 : ℤ) : EInt)) zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
          direct_window_map (n - 1) n (n + 1) (sub_add_cancel n 1) rfl =
      (E.H n).map zero_window_map ≫
        (E.EIsoH zero_middle_arrow (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).inv := by
  have hNat := E.EIsoH_hom_naturality zero_bottom_arrow zero_middle_arrow
    zero_window_map direct_window_map (n - 1) n (n + 1)
    (by apply hom_ext₃ <;> exact Subsingleton.elim _ _)
    (sub_add_cancel n 1) rfl
  apply (cancel_mono
    (E.EIsoH zero_middle_arrow (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hNat, Iso.inv_hom_id_assoc]

private def stage_zero_row_x_iso
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    (horizontalFirstPageRowComplex K q).X 0 ≅
      ((horizontalFirstQuadrantSpectralSequence K).page 1).X (0, q) :=
  ((horizontalFirstQuadrantSpectralSequence K).page 1).restrictionXIso
    (horizontalFirstPageRowEmbedding q) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem row_quotient_naturality
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    (stage_zero_row_x_iso K q).inv ≫
      (horizontalFirstPageRowComplex K q).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (horizontalFirstPageRowComplex K q)).inv ≫
      HomologicalComplex.homologyMap
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom 0 =
    (horizontalFirstPageNormalizedVerticalHomologyIso K 0 q).hom ≫
      (K.verticalHomologyComplex q).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv := by
  have h : (horizontalFirstPageRowComplex K q).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (horizontalFirstPageRowComplex K q)).inv ≫
      HomologicalComplex.homologyMap
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom 0 =
      (horizontalFirstPageNormalizedVerticalHomologyIso K 0 q).hom ≫
        (K.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv := by
    rw [ChainComplex.isoHomologyι₀_inv_naturality]
    rw [← Category.assoc, HomologicalComplex.p_opcyclesMap]
    rw [horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_f]
    exact Category.assoc _ _ _
  calc
    _ = 𝟙 ((horizontalFirstPageRowComplex K q).X 0) ≫
        (horizontalFirstPageRowComplex K q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (horizontalFirstPageRowComplex K q)).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom 0 := by rfl
    _ = _ := by rw [Category.id_comp]; exact h

private theorem zero_quotient_cycles (J : ChainComplex D ℕ) :
    J.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ J).inv =
      (ChainComplex.cycles₀Iso J).inv ≫ J.homologyπ 0 := by
  apply (cancel_mono (J.homologyι 0)).1
  rw [Category.assoc, HomologicalComplex.isoHomologyι_inv_hom_id]
  rw [Category.assoc, HomologicalComplex.homology_π_ι]
  rw [Category.comp_id]
  change J.pOpcycles 0 =
    (ChainComplex.cycles₀Iso J).inv ≫ (ChainComplex.cycles₀Iso J).hom ≫
      J.pOpcycles 0
  rw [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homology_factor_degree_cast
    (M : CochainComplex D ℤ) (a b : ℤ) (h : a = b) :
    eqToHom (congrArg (fun d : ℤ =>
      (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) d).obj
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj M)) h) ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) b).hom.app M =
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) a).hom.app M ≫
      eqToHom (congrArg (fun d : ℤ => M.homology d) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private def stage_zero_first_page_map
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(q : ℤ))).obj
        (mk₁ zero_bottom_arrow) ⟶
      ((horizontalFirstQuadrantSpectralSequence K).page 1).X (0, q) :=
  let E := horizontalCompleteFiltrationSpectralObject K
  let n : ℤ := -(q : ℤ)
  let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
  let hDegree : n = m := by simp [n, m]
  (E.H n).map zero_window_map ≫
    eqToHom (congrArg (fun d : ℤ => (E.H d).obj (mk₁ zero_middle_arrow)) hDegree) ≫
    (horizontalFirstPageCoherentXIso K 0 q).inv

private def stage_zero_homology_data
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    (((horizontalFirstQuadrantSpectralSequence K).page 1).sc'
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
      (0, q)
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q))).HomologyData :=
  let E := horizontalCompleteFiltrationSpectralObject K
  let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n : ℤ := -(q : ℤ)
  E.spectralSequenceHomologyData data 1 2 rfl (le_refl 1)
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
    (0, q)
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (n - 1) n (n + 1)
    (by simp [n, data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (sub_add_cancel n 1) rfl

private def stage_zero_page_one_iso
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    let E := horizontalCompleteFiltrationSpectralObject K
    let n : ℤ := -(q : ℤ)
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (0, q) ≅
      E.E (𝟙 ((-1 : ℤ) : EInt)) zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl :=
  let E := horizontalCompleteFiltrationSpectralObject K
  let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n : ℤ := -(q : ℤ)
  E.spectralSequencePageXIso data 1 (le_refl 1) (0, q)
    ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((0 : ℤ) : EInt)
    (by simp [data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (by simp [data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (by simp [data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (by simp [data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (n - 1) n (n + 1)
    (by simp [n, data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (sub_add_cancel n 1) rfl

private theorem first_page_iso_degree_cast
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) (n m : ℤ)
    (hn : n = CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.deg (0, q))
    (hm : m = CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.deg (0, q))
    (h : n = m) :
    let E := horizontalCompleteFiltrationSpectralObject K
    let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    eqToHom (congrArg (fun d : ℤ => (E.H d).obj (mk₁ zero_middle_arrow)) h) ≫
        (E.spectralSequenceFirstPageXIso data (0, q)
          ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) rfl rfl m hm).inv =
      (E.spectralSequenceFirstPageXIso data (0, q)
        ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) rfl rfl n hn).inv := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem first_page_map_eq_raw
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    let E := horizontalCompleteFiltrationSpectralObject K
    let n : ℤ := -(q : ℤ)
    stage_zero_first_page_map K q =
      (E.H n).map zero_window_map ≫
        (E.EIsoH zero_middle_arrow (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).inv ≫
        (stage_zero_page_one_iso K q).inv := by
  dsimp only
  let E := horizontalCompleteFiltrationSpectralObject K
  let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n : ℤ := -(q : ℤ)
  let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
  have hn : n = data.deg (0, q) := by simp [n, data,
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological]
  have hm : m = data.deg (0, q) := rfl
  have h : n = m := by simp [n, m]
  have hc := first_page_iso_degree_cast K q n m hn hm h
  change (E.H n).map zero_window_map ≫
      (eqToHom (congrArg (fun d : ℤ => (E.H d).obj (mk₁ zero_middle_arrow)) h) ≫
        (E.spectralSequenceFirstPageXIso data (0, q)
          ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) rfl rfl m hm).inv) =
    (E.H n).map zero_window_map ≫
      (E.EIsoH zero_middle_arrow (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).inv ≫
      (stage_zero_page_one_iso K q).inv
  rw [hc]
  rw [E.spectralSequenceFirstPageXIso_inv data (0, q)
    ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) rfl rfl
    (n - 1) n (n + 1) hn (sub_add_cancel n 1) rfl]
  rfl

private def stage_zero_cycle_prefix
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(q : ℤ))).obj
        (mk₁ zero_bottom_arrow) ⟶
      (stage_zero_homology_data K q).left.K :=
  let E := horizontalCompleteFiltrationSpectralObject K
  let n : ℤ := -(q : ℤ)
  let hLower : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let Lold := E.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((0 : ℤ) : EInt)
    bot_le hLower hMiddle le_rfl (n - 1) n (n + 1)
    (hneg (n + 1) (-2) (by omega)) (sub_add_cancel n 1) rfl
  E.toCycles zero_lower_arrow zero_middle_arrow zero_bottom_arrow
      (Subsingleton.elim _ _) n ≫
    E.πE zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
      (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
    Lold.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cycle_prefix_inclusion
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    stage_zero_cycle_prefix K hneg q ≫ (stage_zero_homology_data K q).left.i =
      stage_zero_first_page_map K q := by
  let E := horizontalCompleteFiltrationSpectralObject K
  let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n : ℤ := -(q : ℤ)
  let hLower : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  have hi : (stage_zero_homology_data K q).left.i =
      E.mapFourδ₁Toδ₀' ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((0 : ℤ) : EInt)
        hLower le_rfl hMiddle le_rfl (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
        (stage_zero_page_one_iso K q).inv := by
    exact E.spectralSequenceHomologyData_left_i data 1 2 rfl (le_refl 1)
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
      (0, q)
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl
      ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
      ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
      rfl rfl rfl rfl rfl rfl (n - 1) n (n + 1)
      (by simp [n, data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
      (sub_add_cancel n 1) rfl
  have hComp := E.mapFourδ₁Toδ₀'_comp
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((0 : ℤ) : EInt)
    bot_le hLower le_rfl hMiddle le_rfl (n - 1) n (n + 1) (sub_add_cancel n 1) rfl
  have hβ : cut_window_map =
      fourδ₁Toδ₀' (⊥ : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) bot_le le_rfl hMiddle le_rfl := by
    apply hom_ext₃ <;> exact Subsingleton.elim _ _
  have hβMap :
      E.map zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
        (𝟙 ((-1 : ℤ) : EInt)) zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
        cut_window_map (n - 1) n (n + 1) (sub_add_cancel n 1) rfl =
      E.mapFourδ₁Toδ₀' (⊥ : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) bot_le le_rfl hMiddle le_rfl
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
    rw [hβ]
    rfl
  apply (cancel_mono (stage_zero_page_one_iso K q).hom).1
  rw [hi, first_page_map_eq_raw]
  dsimp only [stage_zero_cycle_prefix,
    CategoryTheory.Abelian.SpectralObject.isoMapFourδ₁Toδ₀']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change E.toCycles zero_lower_arrow zero_middle_arrow zero_bottom_arrow
      (Subsingleton.elim _ _) n ≫
      E.πE zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
      (E.mapFourδ₁Toδ₀' (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) bot_le hLower hMiddle le_rfl
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
        E.mapFourδ₁Toδ₀' ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
          ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) hLower le_rfl hMiddle le_rfl
          (n - 1) n (n + 1) (sub_add_cancel n 1) rfl) =
    (E.H n).map zero_window_map ≫
      (E.EIsoH zero_middle_arrow (n - 1) n (n + 1) (sub_add_cancel n 1) rfl).inv
  rw [hComp, ← hβMap, ← Category.assoc, ← identity_packet_split E n]
  rw [Category.assoc,
    ← E.map_comp (n₀ := n - 1) (n₁ := n) (n₂ := n + 1)
      (hn₁ := sub_add_cancel n 1) (hn₂ := rfl),
    split_cut_direct, bottom_window_naturality]

private def stage_zero_restriction_cycles_iso
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    (horizontalFirstPageRowComplex K q).cycles 0 ≅
      ((horizontalFirstQuadrantSpectralSequence K).page 1).cycles (0, q) :=
  let e := horizontalFirstPageRowEmbedding q
  ((horizontalFirstQuadrantSpectralSequence K).page 1).restrictionCyclesIso
    e 0 ((ComplexShape.down ℕ).next 0) rfl rfl rfl (e.next_f rfl)

private def stage_zero_cycles_sc_iso
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).cycles (0, q) ≅
      (((horizontalFirstQuadrantSpectralSequence K).page 1).sc'
        ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
        (0, q)
        ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q))).cycles :=
  ((horizontalFirstQuadrantSpectralSequence K).page 1).cyclesIsoSc'
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
    (0, q)
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl

private def stage_zero_row_cycle_prefix
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (0, q) ⟶
      (stage_zero_homology_data K q).left.K :=
  (stage_zero_row_x_iso K q).inv ≫
    (ChainComplex.cycles₀Iso (horizontalFirstPageRowComplex K q)).inv ≫
    (stage_zero_restriction_cycles_iso K q).hom ≫
    (stage_zero_cycles_sc_iso K q).hom ≫
    (stage_zero_homology_data K q).left.cyclesIso.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem row_cycle_prefix_inclusion
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    stage_zero_row_cycle_prefix K q ≫ (stage_zero_homology_data K q).left.i =
      𝟙 (((horizontalFirstQuadrantSpectralSequence K).page 1).X (0, q)) := by
  let Y := (horizontalFirstQuadrantSpectralSequence K).page 1
  let e := horizontalFirstPageRowEmbedding q
  have hData := (stage_zero_homology_data K q).left.cyclesIso_hom_comp_i
  have hSc := Y.cyclesIsoSc'_hom_iCycles
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
    (0, q)
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl
  have hRes : (stage_zero_restriction_cycles_iso K q).hom ≫ Y.iCycles (0, q) =
      (horizontalFirstPageRowComplex K q).iCycles 0 ≫ (stage_zero_row_x_iso K q).hom := by
    exact Y.restrictionCyclesIso_hom_iCycles
      e 0 ((ComplexShape.down ℕ).next 0) rfl rfl rfl (e.next_f rfl)
  dsimp only [stage_zero_row_cycle_prefix]
  simp only [Category.assoc]
  rw [hData]
  dsimp only [stage_zero_cycles_sc_iso]
  rw [hSc]
  rw [hRes]
  change (stage_zero_row_x_iso K q).inv ≫
      (ChainComplex.cycles₀Iso (horizontalFirstPageRowComplex K q)).inv ≫
      (ChainComplex.cycles₀Iso (horizontalFirstPageRowComplex K q)).hom ≫
      (stage_zero_row_x_iso K q).hom = 𝟙 _
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem native_cycle_prefix_eq
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    stage_zero_first_page_map K q ≫ stage_zero_row_cycle_prefix K q =
      stage_zero_cycle_prefix K hneg q := by
  apply (cancel_mono (stage_zero_homology_data K q).left.i).1
  rw [Category.assoc, row_cycle_prefix_inclusion, Category.comp_id,
    cycle_prefix_inclusion]

private def stage_zero_page_two_iso
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, q) ≅
      (stage_zero_homology_data K q).left.H :=
  let E := horizontalCompleteFiltrationSpectralObject K
  let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n : ℤ := -(q : ℤ)
  E.spectralSequencePageXIso data 2 (by decide) (0, q)
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    rfl rfl rfl rfl (n - 1) n (n + 1)
    (by simp [n, data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (sub_add_cancel n 1) rfl

private theorem generic_successor_iso
    (E : CategoryTheory.Abelian.SpectralObject D EInt)
    [E.HasSpectralSequence CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (hr' : 1 ≤ r') (q : ℕ) :
    let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    let ξ : ℕ × ℕ := (0, q)
    let η := (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).prev ξ
    let ν := (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).next ξ
    let n : ℤ := -(q : ℤ)
    let i₀' := data.i₀ r' ξ hr'
    let i₀ := data.i₀ r ξ hr
    let i₁ := data.i₁ ξ
    let i₂ := data.i₂ ξ
    let i₃ := data.i₃ r ξ hr
    let i₃' := data.i₃ r' ξ hr'
    let HD := E.spectralSequenceHomologyData data r r' hrr' hr η ξ ν rfl rfl
      i₀' i₀ i₁ i₂ i₃ i₃' rfl rfl rfl rfl rfl rfl (n - 1) n (n + 1)
      (by simp [n, ξ, data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
      (sub_add_cancel n 1) rfl
    let eP := E.spectralSequencePageXIso data r' hr' ξ i₀' i₁ i₂ i₃'
      rfl rfl rfl rfl (n - 1) n (n + 1)
      (by simp [n, ξ, data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
      (sub_add_cancel n 1) rfl
    (E.spectralSequence data).iso r r' ξ =
      ((E.spectralSequence data).page r).homologyIsoSc' η ξ ν rfl rfl ≪≫
        HD.left.homologyIso ≪≫ eP.symm := by
  dsimp only
  exact E.spectralSequence_iso
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    r r' hrr' hr
    ((ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).prev (0, q)) (0, q)
    ((ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).next (0, q)) rfl rfl
    (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₀ r' (0, q) hr')
    (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₀ r (0, q) hr)
    (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₁ (0, q))
    (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₂ (0, q))
    (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₃ r (0, q) hr)
    (CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₃ r' (0, q) hr')
    rfl rfl rfl rfl rfl rfl (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1)
    (by simp [CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
    (sub_add_cancel (-(q : ℤ)) 1) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stage_zero_successor_hom
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, q)).hom =
      (((horizontalFirstQuadrantSpectralSequence K).page 1).homologyIsoSc'
        ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
        (0, q)
        ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl).hom ≫
        (stage_zero_homology_data K q).left.homologyIso.hom ≫
        (stage_zero_page_two_iso K q).inv := by
  let E := horizontalCompleteFiltrationSpectralObject K
  have h : (horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, q) =
      (((horizontalFirstQuadrantSpectralSequence K).page 1).homologyIsoSc'
        ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
        (0, q)
        ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl) ≪≫
      (stage_zero_homology_data K q).left.homologyIso ≪≫
        (stage_zero_page_two_iso K q).symm := by
    exact generic_successor_iso E 1 2 rfl (le_refl 1) (by decide) q
  simpa only [Iso.trans_hom, Iso.symm_hom] using congrArg Iso.hom h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem row_native_quotient
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    (stage_zero_row_x_iso K q).inv ≫
        (horizontalFirstPageRowComplex K q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (horizontalFirstPageRowComplex K q)).inv ≫
        (horizontalFirstPageRowHomologyIso K 0 q).hom ≫
        ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, q)).hom =
      stage_zero_row_cycle_prefix K q ≫
        (stage_zero_homology_data K q).left.π ≫ (stage_zero_page_two_iso K q).inv := by
  let Y := (horizontalFirstQuadrantSpectralSequence K).page 1
  let e := horizontalFirstPageRowEmbedding q
  have hRes : (horizontalFirstPageRowComplex K q).homologyπ 0 ≫
      (horizontalFirstPageRowHomologyIso K 0 q).hom =
      (stage_zero_restriction_cycles_iso K q).hom ≫ Y.homologyπ (0, q) := by
    exact Y.homologyπ_restrictionHomologyIso_hom
      e ((ComplexShape.down ℕ).prev 0) 0 ((ComplexShape.down ℕ).next 0)
      rfl rfl rfl rfl rfl (e.prev_f rfl) (e.next_f rfl)
  have hSc := Y.π_homologyIsoSc'_hom
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
    (0, q)
    ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl
  have hData := ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom
    (Y.sc'
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
      (0, q)
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)))
    (stage_zero_homology_data K q).left
  rw [stage_zero_successor_hom]
  dsimp only [stage_zero_row_cycle_prefix]
  simp only [Category.assoc]
  rw [reassoc_of% (zero_quotient_cycles (horizontalFirstPageRowComplex K q))]
  rw [reassoc_of% hRes, reassoc_of% hSc, reassoc_of% hData]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem right_window_projection
    (E : CategoryTheory.Abelian.SpectralObject D EInt) (n : ℤ) :
    E.πE zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
      E.mapFourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
        bot_le (WithBotTop.coe_monotone (by omega)) le_rfl
        (WithBotTop.coe_monotone (by omega)) (n - 1) n (n + 1) (sub_add_cancel n 1) rfl =
      E.πE zero_lower_arrow zero_middle_arrow zero_right_arrow
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  have hβ : extend_window_map =
      fourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) bot_le hMiddle le_rfl hUpper := by
    apply hom_ext₃ <;> exact Subsingleton.elim _ _
  have hβMap : E.map zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
      zero_lower_arrow zero_middle_arrow zero_right_arrow extend_window_map
      (n - 1) n (n + 1) (sub_add_cancel n 1) rfl =
      E.mapFourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) bot_le hMiddle le_rfl hUpper
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
    rw [hβ]
    rfl
  have hNat := E.πE_map zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
    zero_lower_arrow zero_middle_arrow zero_right_arrow extend_window_map
    (𝟙 (mk₂ zero_lower_arrow zero_middle_arrow)) (n - 1) n (n + 1)
    (by apply hom_ext₂ <;> exact Subsingleton.elim _ _)
    (sub_add_cancel n 1) rfl
  rw [E.cyclesMap_id, Category.id_comp] at hNat
  rw [← hβMap]
  exact hNat

private def stage_zero_outer_left_new
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    let E := horizontalCompleteFiltrationSpectralObject K
    let n : ℤ := -(q : ℤ)
    E.E zero_lower_arrow zero_middle_arrow zero_right_arrow
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≅
      (stage_zero_homology_data K q).left.H :=
  let E := horizontalCompleteFiltrationSpectralObject K
  let n : ℤ := -(q : ℤ)
  E.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    bot_le (WithBotTop.coe_monotone (by omega))
    (WithBotTop.coe_monotone (by omega)) (WithBotTop.coe_monotone (by omega))
    (n - 1) n (n + 1) (hneg (n + 1) (-2) (by omega))
    (sub_add_cancel n 1) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem native_cycle_projection
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    stage_zero_cycle_prefix K hneg q ≫
        (stage_zero_homology_data K q).left.π ≫ (stage_zero_page_two_iso K q).inv =
      (horizontalCompleteFiltrationSpectralObject K).nativeZeroColumnStageZeroRepresentative
        hneg q := by
  let E := horizontalCompleteFiltrationSpectralObject K
  let data := CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let n : ℤ := -(q : ℤ)
  let hLower : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  have hπ : (stage_zero_homology_data K q).left.π =
      E.mapFourδ₄Toδ₃' ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) hLower hMiddle le_rfl hUpper
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl := by
    exact E.spectralSequenceHomologyData_left_π data 1 2 rfl (le_refl 1)
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).prev (0, q))
      (0, q)
      ((ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).next (0, q)) rfl rfl
      ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
      ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
      rfl rfl rfl rfl rfl rfl (n - 1) n (n + 1)
      (by simp [n, data, CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological])
      (sub_add_cancel n 1) rfl
  have hInter := E.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    bot_le hLower hMiddle le_rfl hUpper (n - 1) n (n + 1) (sub_add_cancel n 1) rfl
  have hRep := E.nativeZeroColumnStageZeroRepresentative_comp_pageXIso_hom hneg q
  dsimp only at hRep
  dsimp only [CategoryTheory.Abelian.SpectralObject.cokernelSequenceE] at hRep
  simp only [Category.assoc] at hRep
  change E.nativeZeroColumnStageZeroRepresentative hneg q ≫
      (stage_zero_page_two_iso K q).hom =
      E.toCycles zero_lower_arrow zero_middle_arrow zero_bottom_arrow
          (Subsingleton.elim _ _) n ≫
        E.πE zero_lower_arrow zero_middle_arrow zero_right_arrow
          (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
        (stage_zero_outer_left_new K hneg q).hom at hRep
  apply (cancel_mono (stage_zero_page_two_iso K q).hom).1
  rw [hπ]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hRep]
  dsimp only [stage_zero_cycle_prefix, stage_zero_outer_left_new]
  simp only [Category.assoc,
    CategoryTheory.Abelian.SpectralObject.isoMapFourδ₁Toδ₀'_hom]
  change E.toCycles zero_lower_arrow zero_middle_arrow zero_bottom_arrow
      (Subsingleton.elim _ _) n ≫
      E.πE zero_lower_arrow zero_middle_arrow (𝟙 ((0 : ℤ) : EInt))
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
      (E.mapFourδ₁Toδ₀' (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((0 : ℤ) : EInt) bot_le hLower hMiddle le_rfl
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
        E.mapFourδ₄Toδ₃' ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
          ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) hLower hMiddle le_rfl hUpper
          (n - 1) n (n + 1) (sub_add_cancel n 1) rfl) =
    E.toCycles zero_lower_arrow zero_middle_arrow zero_bottom_arrow
      (Subsingleton.elim _ _) n ≫
      E.πE zero_lower_arrow zero_middle_arrow zero_right_arrow
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl ≫
      E.mapFourδ₁Toδ₀' (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
        ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) bot_le hLower hMiddle hUpper
        (n - 1) n (n + 1) (sub_add_cancel n 1) rfl
  rw [hInter, reassoc_of% (right_window_projection E n)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem first_page_native_representative
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    stage_zero_first_page_map K q ≫
        (stage_zero_row_x_iso K q).inv ≫
        (horizontalFirstPageRowComplex K q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (horizontalFirstPageRowComplex K q)).inv ≫
        (horizontalFirstPageRowHomologyIso K 0 q).hom ≫
        ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, q)).hom =
      (horizontalCompleteFiltrationSpectralObject K).nativeZeroColumnStageZeroRepresentative
        hneg q := by
  rw [row_native_quotient]
  rw [reassoc_of% (native_cycle_prefix_eq K hneg q)]
  exact native_cycle_projection K hneg q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cone_zero_comparison
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    (horizontalCompleteFiltrationMappingConeFunctor K).map zero_window_map ≫
        horizontalFirstPageCoherentMappingConeToDirectColumn K 0 =
      horizontalBottomMappingConeToStage K ((0 : ℤ) : EInt) ≫
        horizontalCompleteDirectColumnProjectionMap K 0 := by
  let F := horizontalCompleteFiltrationCochainDiagram K
  let S₁ := horizontalBottomStageShortComplex K ((0 : ℤ) : EInt)
  let S₂ := ShortComplex.cokernelSequence (horizontalFirstPageCoherentMap K 0)
  let τ : S₁ ⟶ S₂ :=
    { τ₁ := F.map zero_lower_arrow
      τ₂ := F.map (𝟙 ((0 : ℤ) : EInt))
      τ₃ := cokernel.π (horizontalFirstPageCoherentMap K 0)
      comm₁₂ := by
        change F.map zero_lower_arrow ≫ F.map zero_middle_arrow =
          F.map zero_bottom_arrow ≫ F.map (𝟙 ((0 : ℤ) : EInt))
        rw [← F.map_comp, ← F.map_comp]
        apply F.congr_map
        exact Subsingleton.elim _ _
      comm₂₃ := by
        change F.map (𝟙 ((0 : ℤ) : EInt)) ≫
            cokernel.π (horizontalFirstPageCoherentMap K 0) =
          (𝟙 (F.obj ((0 : ℤ) : EInt))) ≫
            cokernel.π (horizontalFirstPageCoherentMap K 0)
        rw [F.map_id] }
  have h := CochainComplex.mappingCone.map_descShortComplex S₁ S₂ τ
  have h' := h =≫ (horizontalFirstPageCoherentCokernelIso K 0).hom
  calc
    _ = CochainComplex.mappingCone.map S₁.f S₂.f τ.τ₁ τ.τ₂ τ.comm₁₂.symm ≫
        CochainComplex.mappingCone.descShortComplex S₂ ≫
        (horizontalFirstPageCoherentCokernelIso K 0).hom := by rfl
    _ = CochainComplex.mappingCone.descShortComplex S₁ ≫
        cokernel.π (horizontalFirstPageCoherentMap K 0) ≫
        (horizontalFirstPageCoherentCokernelIso K 0).hom := by
      simpa only [Category.assoc] using h'
    _ = _ := by
      rw [horizontalFirstPageCoherentCokernelIso_π_hom]
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem first_page_map_projection
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (q : ℕ) :
    let F₀ := horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt)
    let n : ℤ := -(q : ℤ)
    let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
    let hDegree : n = m := by simp [n, m]
    let eExt := F₀.extendHomologyIso ComplexShape.embeddingDownNat
      (j := q) (j' := n) (by simp [n, ComplexShape.embeddingDownNat_f])
    let castCol := eqToHom (congrArg
      (fun d : ℤ => (horizontalDirectColumnCochain K 0).homology d) hDegree)
    stage_zero_first_page_map K q ≫
        (horizontalFirstPageNormalizedVerticalHomologyIso K 0 q).hom =
      (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).hom ≫
        eExt.inv ≫
        HomologicalComplex.homologyMap (horizontalCompleteDirectColumnProjectionMap K 0) n ≫
        castCol ≫ (horizontalDirectColumnHomologyIso K 0 q).hom := by
  dsimp only
  let n : ℤ := -(q : ℤ)
  let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
  have hDegree : n = m := by simp [n, m]
  let F := horizontalCompleteFiltrationCochainDiagram K
  let M := (horizontalCompleteFiltrationMappingConeFunctor K).map zero_window_map
  let A := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n).hom.app
    (CochainComplex.mappingCone (F.map zero_bottom_arrow))
  let cN : (horizontalDirectColumnCochain K 0).homology n ⟶ (K.X 0).homology q :=
    eqToHom (congrArg
      (fun d : ℤ => (horizontalDirectColumnCochain K 0).homology d) hDegree) ≫
      (horizontalDirectColumnHomologyIso K 0 q).hom
  have hfac := (HomotopyCategory.homologyFunctorFactors D
    (ComplexShape.up ℤ) n).hom.naturality M
  change ((horizontalCompleteFiltrationSpectralObject K).H n).map zero_window_map ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n).hom.app
        (CochainComplex.mappingCone (F.map zero_middle_arrow)) =
    A ≫ HomologicalComplex.homologyMap M n at hfac
  have hH := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (cone_zero_comparison K)
  simp only [HomologicalComplex.homologyMap_comp] at hH
  have hFacDegree := homology_factor_degree_cast
    (CochainComplex.mappingCone (F.map zero_middle_arrow)) n m hDegree
  change eqToHom (congrArg (fun d : ℤ =>
      ((horizontalCompleteFiltrationSpectralObject K).H d).obj
        (mk₁ zero_middle_arrow)) hDegree) ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) m).hom.app
        (CochainComplex.mappingCone (F.map zero_middle_arrow)) =
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n).hom.app
        (CochainComplex.mappingCone (F.map zero_middle_arrow)) ≫
      eqToHom (congrArg (fun d : ℤ =>
        (CochainComplex.mappingCone (F.map zero_middle_arrow)).homology d) hDegree)
    at hFacDegree
  have hMapDegree := HomologicalComplex.homologyIsoOfEq_hom_naturality
    (horizontalFirstPageCoherentMappingConeToDirectColumn K 0) hDegree
  simp only [HomologicalComplex.homologyIsoOfEq_hom] at hMapDegree
  rw [horizontalFirstPageNormalizedVerticalHomologyIso_hom]
  simp only [Nat.cast_zero, zero_mul, Int.negOnePow_zero, one_smul]
  dsimp only [stage_zero_first_page_map,
    horizontalFirstPageCoherentVerticalHomologyIso,
    horizontalFirstPageCoherentDirectColumnIso]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom,
    horizontalBottomRelativeHomologyStageIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hFacDegree, ← reassoc_of% hMapDegree]
  change ((horizontalCompleteFiltrationSpectralObject K).H n).map zero_window_map ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n).hom.app
        (CochainComplex.mappingCone (F.map zero_middle_arrow)) ≫
      HomologicalComplex.homologyMap
        (horizontalFirstPageCoherentMappingConeToDirectColumn K 0) n ≫ cN =
    A ≫ HomologicalComplex.homologyMap
        (horizontalBottomMappingConeToStage K ((0 : ℤ) : EInt)) n ≫
      HomologicalComplex.homologyMap (horizontalCompleteDirectColumnProjectionMap K 0) n ≫ cN
  calc
    _ = A ≫ HomologicalComplex.homologyMap M n ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentMappingConeToDirectColumn K 0) n ≫
        cN := by
      simpa only [Category.assoc] using hfac =≫
        (HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentMappingConeToDirectColumn K 0) n ≫
          cN)
    _ = _ := by
      simpa only [Category.assoc, A, M, n, F, zero_bottom_arrow] using
        (A ≫= hH) =≫ cN

/-- The original stage-zero representative is the actual column-zero projection
followed by the full degree-zero quotient of the vertical-homology complex. -/
theorem horizontalSecondPageZeroColumnStageRepresentative
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    let E := horizontalCompleteFiltrationSpectralObject K
    let F₀ := horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt)
    let V := K.verticalHomologyComplex q
    let n : ℤ := -(q : ℤ)
    let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
    let hDegree : n = m := by simp [n, m]
    let uCol :
      F₀.extend ComplexShape.embeddingDownNat ⟶ horizontalDirectColumnCochain K 0 :=
      horizontalCompleteDirectColumnProjectionMap K 0
    let eExt :
      (F₀.extend ComplexShape.embeddingDownNat).homology n ≅ F₀.homology q :=
      F₀.extendHomologyIso ComplexShape.embeddingDownNat
        (j := q) (j' := n) (by simp [n, ComplexShape.embeddingDownNat_f])
    let castCol :
      (horizontalDirectColumnCochain K 0).homology n ⟶
        (horizontalDirectColumnCochain K 0).homology m :=
      eqToHom (congrArg
        (fun d : ℤ => (horizontalDirectColumnCochain K 0).homology d) hDegree)
    let r₀ : F₀.homology q ⟶ (K.X 0).homology q :=
      eExt.inv ≫ HomologicalComplex.homologyMap uCol n ≫ castCol ≫
        (horizontalDirectColumnHomologyIso K 0 q).hom
    (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫
      E.nativeZeroColumnStageZeroRepresentative hneg q ≫
      (horizontalSecondPageVerticalHorizontalHomologyIso K 0 q).hom =
      r₀ ≫ V.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ V).inv := by
  dsimp only
  let F₀ := horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt)
  let n : ℤ := -(q : ℤ)
  let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
  let hDegree : n = m := by simp [n, m]
  let uCol :
      F₀.extend ComplexShape.embeddingDownNat ⟶ horizontalDirectColumnCochain K 0 :=
    horizontalCompleteDirectColumnProjectionMap K 0
  let eExt : (F₀.extend ComplexShape.embeddingDownNat).homology n ≅ F₀.homology q :=
    F₀.extendHomologyIso ComplexShape.embeddingDownNat
      (j := q) (j' := n) (by simp [n, ComplexShape.embeddingDownNat_f])
  let castCol : (horizontalDirectColumnCochain K 0).homology n ⟶
      (horizontalDirectColumnCochain K 0).homology m :=
    eqToHom (congrArg (fun d : ℤ => (horizontalDirectColumnCochain K 0).homology d) hDegree)
  let r₀ : F₀.homology q ⟶ (K.X 0).homology q :=
    eExt.inv ≫ HomologicalComplex.homologyMap uCol n ≫ castCol ≫
      (horizontalDirectColumnHomologyIso K 0 q).hom
  change (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫
      (horizontalCompleteFiltrationSpectralObject K).nativeZeroColumnStageZeroRepresentative
        hneg q ≫
      (horizontalSecondPageVerticalHorizontalHomologyIso K 0 q).hom =
    r₀ ≫ (K.verticalHomologyComplex q).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv
  have hProjection : stage_zero_first_page_map K q ≫
      (horizontalFirstPageNormalizedVerticalHomologyIso K 0 q).hom =
      (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).hom ≫ r₀ :=
    first_page_map_projection K q
  have hRep :
      (horizontalCompleteFiltrationSpectralObject K).nativeZeroColumnStageZeroRepresentative
        hneg q ≫
        (horizontalSecondPageVerticalHorizontalHomologyIso K 0 q).hom =
      stage_zero_first_page_map K q ≫
        (horizontalFirstPageNormalizedVerticalHomologyIso K 0 q).hom ≫
        (K.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv := by
    rw [← first_page_native_representative K hneg q]
    change (stage_zero_first_page_map K q ≫
          (stage_zero_row_x_iso K q).inv ≫
          (horizontalFirstPageRowComplex K q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (horizontalFirstPageRowComplex K q)).inv ≫
          (horizontalFirstPageRowHomologyIso K 0 q).hom ≫
          ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, q)).hom) ≫
        (((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (0, q)).inv ≫
          (horizontalFirstPageRowHomologyIso K 0 q).inv ≫
          HomologicalComplex.homologyMap
            (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom 0) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [row_quotient_naturality K q]
  calc
    _ = (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫
        (stage_zero_first_page_map K q ≫
          (horizontalFirstPageNormalizedVerticalHomologyIso K 0 q).hom ≫
          (K.verticalHomologyComplex q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv) :=
      (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫= hRep
    _ = _ := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        ((horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫=
          hProjection) =≫
          ((K.verticalHomologyComplex q).pOpcycles 0 ≫
            (ChainComplex.isoHomologyι₀ (K.verticalHomologyComplex q)).inv)

end HomologicalComplex₂
