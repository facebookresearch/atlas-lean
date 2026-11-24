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

public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralSequenceData
public import MathlibExt.Algebra.Homology.SpectralObject.StableIntervalGraded
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Native column-zero edges

The canonical stage-zero representative and edge of the original native
first-quadrant homological sequence of a spectral object over `EInt`.
The edge uses the original page presentation, literal outer maps and the
selected-image quotient, with lower support alone in its definition.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable (X : SpectralObject D EInt)
variable [X.HasSpectralSequence coreE₁FirstQuadrantHomological]
variable (hneg : ∀ (n a : ℤ), a < 0 →
  IsZero ((X.H n).obj
    (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))

/-- The original finite-window projection, followed by the bottom-to-page
outer-left isomorphism and inverse native page presentation. -/
noncomputable def nativeZeroColumnStageZeroRepresentative (q : ℕ) :
    X.stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) ⟶
      ((X.spectralSequence coreE₁FirstQuadrantHomological).page (2 : ℤ)).X (0, q) :=
  let n : ℤ := -(q : ℤ)
  let hLower : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let eP := X.spectralSequencePageXIso coreE₁FirstQuadrantHomological
    (2 : ℤ) (by omega) (0, q)
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (n - 1) n (n + 1)
    (by simp [n, coreE₁FirstQuadrantHomological]) (by omega) (by rfl)
  let eL := X.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    bot_le hLower hMiddle hUpper (n - 1) n (n + 1)
    (hneg (n + 1) (-2) (by omega)) (by omega) (by rfl)
  let g₀ := (X.cokernelSequenceE
    (homOfLE (bot_le : (⊥ : EInt) ≤ ((-1 : ℤ) : EInt)))
    (homOfLE hMiddle) (homOfLE hUpper)
    (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
    (Subsingleton.elim _ _) (n - 1) n (n + 1) (by omega) (by rfl)).g
  g₀ ≫ eL.hom ≫ eP.inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical stage-zero representative is epic. -/
instance nativeZeroColumnStageZeroRepresentative_epi (q : ℕ) :
    Epi (X.nativeZeroColumnStageZeroRepresentative hneg q) := by
  dsimp only [nativeZeroColumnStageZeroRepresentative]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The defining equation of the representative with the original native page
presentation and finite-window cokernel projection. -/
@[reassoc]
theorem nativeZeroColumnStageZeroRepresentative_comp_pageXIso_hom (q : ℕ) :
  let n : ℤ := -(q : ℤ)
  let hLower : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let eP := X.spectralSequencePageXIso coreE₁FirstQuadrantHomological
    (2 : ℤ) (by omega) (0, q)
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (n - 1) n (n + 1)
    (by simp [n, coreE₁FirstQuadrantHomological]) (by omega) (by rfl)
  let eL := X.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    bot_le hLower hMiddle hUpper (n - 1) n (n + 1)
    (hneg (n + 1) (-2) (by omega)) (by omega) (by rfl)
  let g₀ := (X.cokernelSequenceE
    (homOfLE (bot_le : (⊥ : EInt) ≤ ((-1 : ℤ) : EInt)))
    (homOfLE hMiddle) (homOfLE hUpper)
    (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
    (Subsingleton.elim _ _) (n - 1) n (n + 1) (by omega) (by rfl)).g
  X.nativeZeroColumnStageZeroRepresentative hneg q ≫ eP.hom = g₀ ≫ eL.hom := by
  dsimp only [nativeZeroColumnStageZeroRepresentative]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The canonical native column-zero edge into the full bottom-to-top interval,
using lower support and the actual selected-image quotient projection. -/
noncomputable def nativeZeroColumnEdge (q : ℕ) :
    ((X.spectralSequence coreE₁FirstQuadrantHomological).page (2 : ℤ)).X (0, q) ⟶
      X.stableIntervalAbutment (-(q : ℤ)) :=
  let n : ℤ := -(q : ℤ)
  let hLower : ((-2 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let eP := X.spectralSequencePageXIso coreE₁FirstQuadrantHomological
    (2 : ℤ) (by omega) (0, q)
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (by simp [coreE₁FirstQuadrantHomological])
    (n - 1) n (n + 1)
    (by simp [n, coreE₁FirstQuadrantHomological]) (by omega) (by rfl)
  let eL := X.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt)
    bot_le hLower hMiddle hUpper (n - 1) n (n + 1)
    (hneg (n + 1) (-2) (by omega)) (by omega) (by rfl)
  let R := X.mapFourδ₄Toδ₃'
    (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
    ((1 : ℤ) : EInt) (⊤ : EInt)
    bot_le hMiddle hUpper le_top (n - 1) n (n + 1) (by omega) (by rfl)
  let π₀ := cokernel.π (X.stableIntervalImageMap n hMiddle)
  letI : IsIso π₀ := by
    apply cokernel.π_of_zero
    have hImage : IsZero (X.stableIntervalStepImage n ((-1 : ℤ) : EInt)) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply (cancel_epi (X.stableIntervalStepToImage n ((-1 : ℤ) : EInt))).1
      exact (hneg n (-1) (by omega)).eq_of_src _ _
    exact hImage.eq_of_src _ _
  eP.hom ≫ eL.inv ≫ R ≫ (X.stableIntervalImageCokernelIso n hMiddle).hom ≫
    (asIso π₀).inv ≫ Limits.image.ι
      (X.stableIntervalStepToAbutment n ((0 : ℤ) : EInt))

omit [X.HasSpectralSequence coreE₁FirstQuadrantHomological] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnStepProjection_comp_right (n : ℤ) :
    let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
      WithBotTop.coe_monotone (by omega)
    let hUpper : ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) :=
      WithBotTop.coe_monotone (by omega)
    (X.cokernelSequenceE
      (homOfLE (bot_le : (⊥ : EInt) ≤ ((-1 : ℤ) : EInt)))
      (homOfLE hMiddle) (homOfLE hUpper)
      (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
      (Subsingleton.elim _ _) (n - 1) n (n + 1) (by omega) (by rfl)).g ≫
        X.mapFourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt)
          ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) (⊤ : EInt)
          bot_le hMiddle hUpper le_top (n - 1) n (n + 1) (by omega) (by rfl) =
      X.stableIntervalStepToStable n hMiddle := by
  dsimp only
  let fL := homOfLE (bot_le : (⊥ : EInt) ≤ ((-1 : ℤ) : EInt))
  let fM := homOfLE (show ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) from
    WithBotTop.coe_monotone (by omega))
  let fR := homOfLE (show ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) from
    WithBotTop.coe_monotone (by omega))
  let fT := homOfLE (le_top : ((0 : ℤ) : EInt) ≤ (⊤ : EInt))
  let fLM := homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt))
  let a := fourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) (⊤ : EInt)
    bot_le (WithBotTop.coe_monotone (by omega))
    (WithBotTop.coe_monotone (by omega)) le_top
  have hRestriction : (𝟙 (mk₂ fL fM)) = homMk₂ (a.app 0) (a.app 1)
      (a.app 2) (naturality' a 0 1 (by omega) (by omega))
      (naturality' a 1 2 (by omega) (by omega)) := by
    rfl
  change (X.toCycles fL fM fLM (Subsingleton.elim _ _) n ≫
      X.πE fL fM fR (n - 1) n (n + 1) (by omega) (by rfl)) ≫
      X.map fL fM fR fL fM fT a (n - 1) n (n + 1) (by omega) (by rfl) = _
  rw [Category.assoc, X.πE_map fL fM fR fL fM fT a (𝟙 _)
    (n - 1) n (n + 1) hRestriction (by omega) (by rfl),
    X.cyclesMap_id, Category.id_comp]
  rfl

omit [X.HasSpectralSequence coreE₁FirstQuadrantHomological] in
include hneg in
private theorem nativeZeroColumnProjection_isIso (n : ℤ) :
    IsIso (cokernel.π (X.stableIntervalImageMap n
      (show ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) from
        WithBotTop.coe_monotone (by omega)))) := by
  apply cokernel.π_of_zero
  have hImage : IsZero (X.stableIntervalStepImage n ((-1 : ℤ) : EInt)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi (X.stableIntervalStepToImage n ((-1 : ℤ) : EInt))).1
    exact (hneg n (-1) (by omega)).eq_of_src _ _
  exact hImage.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The defined edge sends the actual canonical stage-zero representative to
its original interval map into the full bottom-to-top object. -/
@[reassoc]
theorem nativeZeroColumnEdge_representation (q : ℕ) :
    X.nativeZeroColumnStageZeroRepresentative hneg q ≫ X.nativeZeroColumnEdge hneg q =
      X.stableIntervalStepToAbutment (-(q : ℤ)) ((0 : ℤ) : EInt) := by
  let := nativeZeroColumnProjection_isIso X hneg (-(q : ℤ))
  dsimp only [nativeZeroColumnStageZeroRepresentative, nativeZeroColumnEdge]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, nativeZeroColumnStepProjection_comp_right X (-(q : ℤ))]
  rw [← X.stableIntervalStepToImage_comp_imageToStable (-(q : ℤ))
    (show ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) from
      WithBotTop.coe_monotone (by omega))]
  rw [Category.assoc, X.stableIntervalImageToStable_comp_iso_hom_assoc]
  simp only [asIso_inv, IsIso.hom_inv_id_assoc, stableIntervalStepToImage, Limits.image.fac]

variable (hupper : ∀ (d : ℕ) (a : ℤ), (d : ℤ) ≤ a →
  IsZero ((X.H (-(d : ℤ))).obj
    (mk₁ (homOfLE (le_top : (a : EInt) ≤ (⊤ : EInt))))))

variable (hpos : ∀ (p t : ℕ), 1 ≤ p →
  IsZero (((X.spectralSequence coreE₁FirstQuadrantHomological).page (2 : ℤ)).X (p, t)))

include hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnPositiveLater (m p t : ℕ) (hp : 1 ≤ p) :
    IsZero (((X.spectralSequence coreE₁FirstQuadrantHomological).page
      (2 + (m : ℤ))).X (p, t)) := by
  induction m with
  | zero => exact hpos p t hp
  | succ m ih =>
    let P := X.spectralSequence coreE₁FirstQuadrantHomological
    have hz : IsZero ((P.page (2 + (m : ℤ))).homology (p, t)) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ ih
    exact IsZero.of_iso hz
      (P.iso (2 + (m : ℤ)) (2 + (m.succ : ℤ)) (p, t) (by omega) (by omega)).symm

include hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnRawRight_isIso (m q : ℕ) (u v : ℤ)
    (hu : u = (2 + (m : ℤ)) - 1) (hv : v = 2 + (m : ℤ)) :
    IsIso (X.mapFourδ₄Toδ₃'
      ((-(2 + (m : ℤ)) - 1 : ℤ) : EInt) ((-1 : ℤ) : EInt)
      ((0 : ℤ) : EInt) ((u : ℤ) : EInt) ((v : ℤ) : EInt)
      (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) (by rfl)) := by
  let r : ℤ := 2 + (m : ℤ)
  let P := X.spectralSequence coreE₁FirstQuadrantHomological
  let η := (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).prev (0, q)
  let ν := (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).next (0, q)
  let data := coreE₁FirstQuadrantHomological
  have hcut₀' : ((-r - 1 : ℤ) : EInt) = data.i₀ (r + 1) (0, q)
      (by dsimp [r]; omega) := by
    dsimp [data, coreE₁FirstQuadrantHomological]
    congr 1
    omega
  have hcut₀ : ((-r : ℤ) : EInt) = data.i₀ r (0, q)
      (by dsimp [r]; omega) := by
    dsimp [data, coreE₁FirstQuadrantHomological]
    congr 1
    omega
  have hcut₁ : ((-1 : ℤ) : EInt) = data.i₁ (0, q) := rfl
  have hcut₂ : ((0 : ℤ) : EInt) = data.i₂ (0, q) := rfl
  have hcut₃ : ((u : ℤ) : EInt) = data.i₃ r (0, q)
      (by dsimp [r]; omega) := by
    dsimp [data, coreE₁FirstQuadrantHomological]
    congr 1
    dsimp [r]
    omega
  have hcut₃' : ((v : ℤ) : EInt) = data.i₃ (r + 1) (0, q)
      (by dsimp [r]; omega) := by
    dsimp [data, coreE₁FirstQuadrantHomological]
    congr 1
    dsimp [r]
    omega
  have hdegree : -(q : ℤ) = data.deg (0, q) := by
    dsimp [data, coreE₁FirstQuadrantHomological]
    omega
  let HD := X.spectralSequenceHomologyData data
    r (r + 1) rfl (by dsimp [r]; omega) η (0, q) ν rfl rfl
    ((-r - 1 : ℤ) : EInt) ((-r : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((u : ℤ) : EInt) ((v : ℤ) : EInt)
    hcut₀' hcut₀ hcut₁ hcut₂ hcut₃ hcut₃'
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) hdegree (by omega) rfl
  have hin : (P.page r).d η (0, q) = 0 := by
    by_cases hrel : (ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).Rel η (0, q)
    · have hp : 1 ≤ η.1 := by
        simp only [ComplexShape.spectralSequenceNat_rel_iff] at hrel
        dsimp only [r] at hrel
        omega
      exact (nativeZeroColumnPositiveLater X hpos m η.1 η.2 hp).eq_of_src _ _
    · exact (P.page r).shape η (0, q) hrel
  have hπ := X.spectralSequenceHomologyData_left_π data
    r (r + 1) rfl (by dsimp [r]; omega) η (0, q) ν rfl rfl
    ((-r - 1 : ℤ) : EInt) ((-r : ℤ) : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((u : ℤ) : EInt) ((v : ℤ) : EInt)
    hcut₀' hcut₀ hcut₁ hcut₂ hcut₃ hcut₃'
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) hdegree (by omega) rfl
  have hIso : IsIso HD.left.π := HD.left.isIso_π hin
  rw [hπ] at hIso
  exact hIso

include hneg hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnBottomRight_isIso (m q : ℕ) (u v : ℤ)
    (hu : u = (2 + (m : ℤ)) - 1) (hv : v = 2 + (m : ℤ)) :
    IsIso (X.mapFourδ₄Toδ₃'
      (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
      ((u : ℤ) : EInt) ((v : ℤ) : EInt)
      bot_le (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl) := by
  let r : ℤ := 2 + (m : ℤ)
  let n : ℤ := -(q : ℤ)
  let hLower : ((-r - 1 : ℤ) : EInt) ≤ ((-1 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by dsimp [r]; omega)
  let hMiddle : ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : ((0 : ℤ) : EInt) ≤ ((u : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hNext : ((u : ℤ) : EInt) ≤ ((v : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let Lu := X.isoMapFourδ₁Toδ₀' (⊥ : EInt) ((-r - 1 : ℤ) : EInt)
    ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((u : ℤ) : EInt)
    bot_le hLower hMiddle hUpper (n - 1) n (n + 1)
    (hneg (n + 1) (-r - 1) (by dsimp [r]; omega)) (by omega) rfl
  let Lv := X.isoMapFourδ₁Toδ₀' (⊥ : EInt) ((-r - 1 : ℤ) : EInt)
    ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((v : ℤ) : EInt)
    bot_le hLower hMiddle (hUpper.trans hNext) (n - 1) n (n + 1)
    (hneg (n + 1) (-r - 1) (by dsimp [r]; omega)) (by omega) rfl
  let raw := X.mapFourδ₄Toδ₃' ((-r - 1 : ℤ) : EInt)
    ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((u : ℤ) : EInt) ((v : ℤ) : EInt)
    hLower hMiddle hUpper hNext (n - 1) n (n + 1) (by omega) rfl
  let ρ := X.mapFourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((u : ℤ) : EInt) ((v : ℤ) : EInt)
    bot_le hMiddle hUpper hNext (n - 1) n (n + 1) (by omega) rfl
  have : IsIso raw := nativeZeroColumnRawRight_isIso X hpos m q u v hu hv
  have hinter : Lu.hom ≫ raw = ρ ≫ Lv.hom :=
    X.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' (⊥ : EInt) ((-r - 1 : ℤ) : EInt)
      ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) ((u : ℤ) : EInt) ((v : ℤ) : EInt)
      bot_le hLower hMiddle hUpper hNext (n - 1) n (n + 1) (by omega) rfl
  have hconj : ρ = Lu.hom ≫ raw ≫ Lv.inv := by
    calc
      ρ = (ρ ≫ Lv.hom) ≫ Lv.inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (Lu.hom ≫ raw) ≫ Lv.inv := congrArg (fun f => f ≫ Lv.inv) hinter.symm
      _ = _ := Category.assoc _ _ _
  change IsIso ρ
  rw [hconj]
  infer_instance

include hneg hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnFiniteRight_isIso (k q : ℕ) :
    IsIso (X.mapFourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
      ((1 : ℤ) : EInt) ((1 + (k : ℤ) : ℤ) : EInt)
      bot_le (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl) := by
  induction k with
  | zero =>
    change IsIso (X.map _ _ _ _ _ _ (𝟙 _) _ _ _ _ _)
    rw [X.map_id _ _ _ (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl]
    infer_instance
  | succ k ih =>
    have hStep : IsIso (X.mapFourδ₄Toδ₃'
        (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
        ((1 + (k : ℤ) : ℤ) : EInt) ((1 + (k.succ : ℤ) : ℤ) : EInt)
        bot_le (WithBotTop.coe_monotone (by omega))
        (WithBotTop.coe_monotone (by omega))
        (WithBotTop.coe_monotone (by omega))
        (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl) := by
      exact nativeZeroColumnBottomRight_isIso X hneg hpos k q
        (1 + (k : ℤ)) (1 + (k.succ : ℤ)) (by omega) (by omega)
    have hcomp := X.mapFourδ₄Toδ₃'_comp (⊥ : EInt) ((-1 : ℤ) : EInt)
      ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) ((1 + (k : ℤ) : ℤ) : EInt)
      ((1 + (k.succ : ℤ) : ℤ) : EInt)
      bot_le (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega))
      (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl
    rw [← hcomp]
    infer_instance

include hneg hupper hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnFullRight_isIso (q : ℕ) :
    IsIso (X.mapFourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
      ((1 : ℤ) : EInt) (⊤ : EInt)
      bot_le (WithBotTop.coe_monotone (by omega))
      (WithBotTop.coe_monotone (by omega)) le_top
      (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl) := by
  have := nativeZeroColumnFiniteRight_isIso X hneg hpos q q
  have ht : IsZero ((X.H (-(q : ℤ) - 1)).obj
      (mk₁ (homOfLE (le_top : ((1 + (q : ℤ) : ℤ) : EInt) ≤ (⊤ : EInt))))) := by
    have hn : -(q : ℤ) - 1 = -((q + 1 : ℕ) : ℤ) := by omega
    rw [hn]
    exact hupper (q + 1) (1 + (q : ℤ)) (by omega)
  have := X.isIso_mapFourδ₄Toδ₃' (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
    ((1 + (q : ℤ) : ℤ) : EInt) (⊤ : EInt)
    bot_le (WithBotTop.coe_monotone (by omega))
    (WithBotTop.coe_monotone (by omega)) le_top
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) ht (by omega) rfl
  rw [← X.mapFourδ₄Toδ₃'_comp (⊥ : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt)
    ((1 : ℤ) : EInt) ((1 + (q : ℤ) : ℤ) : EInt) (⊤ : EInt)
    bot_le (WithBotTop.coe_monotone (by omega))
    (WithBotTop.coe_monotone (by omega))
    (WithBotTop.coe_monotone (by omega)) le_top
    (-(q : ℤ) - 1) (-(q : ℤ)) (-(q : ℤ) + 1) (by omega) rfl]
  infer_instance

omit [X.HasSpectralSequence coreE₁FirstQuadrantHomological] in
private theorem nativeZeroColumnImageMap_mono (n : ℤ) {i j : EInt} (h : i ≤ j) :
    Mono (X.stableIntervalImageMap n h) :=
  mono_of_mono_fac (X.stableIntervalImageMap_comp_ι n h)

omit [X.HasSpectralSequence coreE₁FirstQuadrantHomological] in
private theorem nativeZeroColumnImageMap_id (n : ℤ) (i : EInt) :
    X.stableIntervalImageMap n (le_refl i) = 𝟙 _ := by
  apply (cancel_mono (Limits.image.ι (X.stableIntervalStepToAbutment n i))).1
  rw [X.stableIntervalImageMap_comp_ι, Category.id_comp]

omit [X.HasSpectralSequence coreE₁FirstQuadrantHomological] in
private theorem nativeZeroColumnImageMap_comp (n : ℤ) {i j k : EInt}
    (hij : i ≤ j) (hjk : j ≤ k) :
    X.stableIntervalImageMap n hij ≫ X.stableIntervalImageMap n hjk =
      X.stableIntervalImageMap n (hij.trans hjk) := by
  apply (cancel_mono (Limits.image.ι (X.stableIntervalStepToAbutment n k))).1
  rw [Category.assoc, X.stableIntervalImageMap_comp_ι,
    X.stableIntervalImageMap_comp_ι, X.stableIntervalImageMap_comp_ι]

include hneg hupper hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnPositiveImage_isIso (q k t : ℕ)
    (hsum : k + 1 + t = q) :
    IsIso (X.stableIntervalImageMap (-(q : ℤ))
      (show ((k : ℤ) : EInt) ≤ (((k + 1 : ℕ) : ℤ) : EInt) from
        WithBotTop.coe_monotone (by omega))) := by
  let r : ℤ := 2 + (q : ℤ)
  let n : ℤ := -(q : ℤ)
  let a : ℤ := ((k + 1 : ℕ) : ℤ) - r
  let b : ℤ := ((k + 1 : ℕ) : ℤ) + r - 1
  let data := coreE₁FirstQuadrantHomological
  let hLower : ((a : ℤ) : EInt) ≤ ((k : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by dsimp [a, r]; omega)
  let hMiddle : ((k : ℤ) : EInt) ≤ (((k + 1 : ℕ) : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by omega)
  let hUpper : (((k + 1 : ℕ) : ℤ) : EInt) ≤ ((b : ℤ) : EInt) :=
    WithBotTop.coe_monotone (by dsimp [b, r]; omega)
  have hcut₀ : ((a : ℤ) : EInt) = data.i₀ r (k + 1, t)
      (by dsimp [r]; omega) := rfl
  have hcut₁ : ((k : ℤ) : EInt) = data.i₁ (k + 1, t) := by
    dsimp [data, coreE₁FirstQuadrantHomological]
    congr 1
    omega
  have hcut₂ : (((k + 1 : ℕ) : ℤ) : EInt) = data.i₂ (k + 1, t) := rfl
  have hcut₃ : ((b : ℤ) : EInt) = data.i₃ r (k + 1, t)
      (by dsimp [r]; omega) := rfl
  have hdegree : n = data.deg (k + 1, t) := by
    dsimp [n, data, coreE₁FirstQuadrantHomological]
    omega
  let eP := X.spectralSequencePageXIso data r (by dsimp [r]; omega) (k + 1, t)
    ((a : ℤ) : EInt) ((k : ℤ) : EInt) (((k + 1 : ℕ) : ℤ) : EInt) ((b : ℤ) : EInt)
    hcut₀ hcut₁ hcut₂ hcut₃ (n - 1) n (n + 1) hdegree (by omega) rfl
  let eL := X.isoMapFourδ₁Toδ₀' (⊥ : EInt) ((a : ℤ) : EInt)
    ((k : ℤ) : EInt) (((k + 1 : ℕ) : ℤ) : EInt) ((b : ℤ) : EInt)
    bot_le hLower hMiddle hUpper (n - 1) n (n + 1)
    (hneg (n + 1) a (by dsimp [a, r]; omega)) (by omega) rfl
  have ht : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((b : ℤ) : EInt) ≤ (⊤ : EInt))))) := by
    have hn : n - 1 = -((q + 1 : ℕ) : ℤ) := by dsimp [n]; omega
    rw [hn]
    exact hupper (q + 1) b (by dsimp [b, r]; omega)
  let eR := X.isoMapFourδ₄Toδ₃' (⊥ : EInt) ((k : ℤ) : EInt)
    (((k + 1 : ℕ) : ℤ) : EInt) ((b : ℤ) : EInt) (⊤ : EInt)
    bot_le hMiddle hUpper le_top (n - 1) n (n + 1) ht (by omega) rfl
  have hz := nativeZeroColumnPositiveLater X hpos q (k + 1) t (by omega)
  have hs : IsZero (X.stableIntervalObj n hMiddle) :=
    IsZero.of_iso hz (eP ≪≫ eL.symm ≪≫ eR).symm
  have hc : IsZero (cokernel (X.stableIntervalImageMap n hMiddle)) :=
    IsZero.of_iso hs (X.stableIntervalImageCokernelIso n hMiddle).symm
  have := Preadditive.epi_of_isZero_cokernel (X.stableIntervalImageMap n hMiddle) hc
  have := nativeZeroColumnImageMap_mono X n hMiddle
  exact isIso_of_mono_of_epi _

omit [X.HasSpectralSequence coreE₁FirstQuadrantHomological] in
include hupper in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnFinalImage_isIso (q : ℕ) :
    IsIso (Limits.image.ι
      (X.stableIntervalStepToAbutment (-(q : ℤ)) ((q : ℤ) : EInt))) := by
  let f := homOfLE (bot_le : (⊥ : EInt) ≤ ((q : ℤ) : EInt))
  let g := homOfLE (le_top : ((q : ℤ) : EInt) ≤ (⊤ : EInt))
  let fg := homOfLE (bot_le : (⊥ : EInt) ≤ (⊤ : EInt))
  have hz : IsZero ((X.H (-(q : ℤ))).obj (mk₁ g)) := hupper q (q : ℤ) (by omega)
  have hepi : Epi (X.stableIntervalStepToAbutment (-(q : ℤ)) ((q : ℤ) : EInt)) := by
    change Epi ((X.H (-(q : ℤ))).map (twoδ₂Toδ₁ f g fg (Subsingleton.elim _ _)))
    exact (X.exact₂ f g fg (Subsingleton.elim _ _) (-(q : ℤ))).epi_f
      (hz.eq_of_tgt _ _)
  have := Limits.epi_image_of_epi
    (X.stableIntervalStepToAbutment (-(q : ℤ)) ((q : ℤ) : EInt))
  exact isIso_of_mono_of_epi _

include hneg hupper hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnFiniteImage_isIso (q k : ℕ) (hk : k ≤ q) :
    IsIso (X.stableIntervalImageMap (-(q : ℤ))
      (show ((0 : ℤ) : EInt) ≤ ((k : ℤ) : EInt) from
        WithBotTop.coe_monotone (by omega))) := by
  induction k with
  | zero =>
    rw [nativeZeroColumnImageMap_id]
    infer_instance
  | succ k ih =>
    have := ih (by omega)
    have := nativeZeroColumnPositiveImage_isIso X hneg hupper hpos
      q k (q - (k + 1)) (by omega)
    rw [← nativeZeroColumnImageMap_comp X (-(q : ℤ))
      (show ((0 : ℤ) : EInt) ≤ ((k : ℤ) : EInt) from
        WithBotTop.coe_monotone (by omega))
      (show ((k : ℤ) : EInt) ≤ (((k + 1 : ℕ) : ℤ) : EInt) from
        WithBotTop.coe_monotone (by omega))]
    infer_instance

include hneg hupper hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nativeZeroColumnImageZero_isIso (q : ℕ) :
    IsIso (Limits.image.ι
      (X.stableIntervalStepToAbutment (-(q : ℤ)) ((0 : ℤ) : EInt))) := by
  have := nativeZeroColumnFiniteImage_isIso X hneg hupper hpos q q le_rfl
  have := nativeZeroColumnFinalImage_isIso X hupper q
  rw [← X.stableIntervalImageMap_comp_ι (-(q : ℤ))
    (show ((0 : ℤ) : EInt) ≤ ((q : ℤ) : EInt) from
      WithBotTop.coe_monotone (by omega))]
  infer_instance

include hupper hpos in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The defined native edge is an isomorphism under upper support and the
vanishing of every positive column on the original second page. -/
theorem isIso_nativeZeroColumnEdge (q : ℕ) : IsIso (X.nativeZeroColumnEdge hneg q) := by
  have := nativeZeroColumnFullRight_isIso X hneg hupper hpos q
  have := nativeZeroColumnImageZero_isIso X hneg hupper hpos q
  dsimp only [nativeZeroColumnEdge]
  infer_instance

end CategoryTheory.Abelian.SpectralObject

end
