/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteCurrentToExponent
import Code.Exact3D.Intervals


















namespace StatMech
namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in

noncomputable def logRatioValue (fkMass : ℝ → ℝ) (p : ℝ) : ℝ :=
  Real.log (fkMass p) / Real.log (Ising3DFKPC - p)

set_option linter.style.longLine false in






structure EpsilonTable
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (Case : Type*) [DecidableEq Case]
    (epsilon : ℝ) where
  table : RatInterval.CaseTable Case
  classify : ℝ → Case
  window : ℝ
  window_pos : 0 < window
  covers_on_Ioo :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
      classify p ∈ table.cases
  sound_on_Ioo :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
      (table.interval (classify p)).MemR (logRatioValue fkMass p)
  lower_inside_slack :
    ∀ k, k ∈ table.cases →
      C.predictedExponent - epsilon < ((table.interval k).lower : ℝ)
  upper_inside_slack :
    ∀ k, k ∈ table.cases →
      ((table.interval k).upper : ℝ) < C.predictedExponent + epsilon

set_option linter.style.longLine false in



structure Certificate
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (Case : Type*) [DecidableEq Case] where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  epsilonTable :
    ∀ epsilon, 0 < epsilon → EpsilonTable C fkMass Case epsilon

namespace EpsilonTable

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in



def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    {epsilon : ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : EpsilonTable C fkMass Case epsilon) :
    EpsilonTable D fkMass Case epsilon where
  table := T.table
  classify := T.classify
  window := T.window
  window_pos := T.window_pos
  covers_on_Ioo := T.covers_on_Ioo
  sound_on_Ioo := T.sound_on_Ioo
  lower_inside_slack := by
    intro k hk
    simpa [hpred] using T.lower_inside_slack k hk
  upper_inside_slack := by
    intro k hk
    simpa [hpred] using T.upper_inside_slack k hk

set_option linter.style.longLine false in



def restrict_window
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    {epsilon : ℝ}
    (T : EpsilonTable C fkMass Case epsilon)
    {w : ℝ} (hw : 0 < w) (hle : w ≤ T.window) :
    EpsilonTable C fkMass Case epsilon where
  table := T.table
  classify := T.classify
  window := w
  window_pos := hw
  covers_on_Ioo := by
    intro p hp
    exact T.covers_on_Ioo p
      ⟨by linarith [hp.1, hle], hp.2⟩
  sound_on_Ioo := by
    intro p hp
    exact T.sound_on_Ioo p
      ⟨by linarith [hp.1, hle], hp.2⟩
  lower_inside_slack := T.lower_inside_slack
  upper_inside_slack := T.upper_inside_slack

set_option linter.style.longLine false in





def of_globalCaseTable
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    {epsilon window : ℝ}
    (table : RatInterval.CaseTable Case)
    (classify : ℝ → Case)
    (hwindow : 0 < window)
    (hcovers : RatInterval.CaseTable.Covers table classify)
    (hsound :
      RatInterval.CaseTable.Sound table classify (logRatioValue fkMass))
    (hlower :
      ∀ k, k ∈ table.cases →
        C.predictedExponent - epsilon < ((table.interval k).lower : ℝ))
    (hupper :
      ∀ k, k ∈ table.cases →
        ((table.interval k).upper : ℝ) < C.predictedExponent + epsilon) :
    EpsilonTable C fkMass Case epsilon where
  table := table
  classify := classify
  window := window
  window_pos := hwindow
  covers_on_Ioo := fun p _hp => hcovers p
  sound_on_Ioo := fun p _hp => hsound p
  lower_inside_slack := hlower
  upper_inside_slack := hupper

end EpsilonTable

namespace Certificate

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in




def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (hpred : D.predictedExponent = C.predictedExponent)
    (H : Certificate C fkMass Case) :
    Certificate D fkMass Case where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  epsilonTable := fun epsilon hepsilon =>
    (H.epsilonTable epsilon hepsilon).congr_predictedExponent hpred

set_option linter.style.longLine false in


def restrict_pδ
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case)
    {pδ' : ℝ} (hpδ' : 0 < pδ') (hle : pδ' ≤ H.pδ) :
    Certificate C fkMass Case where
  pδ := pδ'
  pδ_pos := hpδ'
  fkMass_pos := by
    intro p hp
    exact H.fkMass_pos p
      ⟨by linarith [hp.1, hle], hp.2⟩
  epsilonTable := H.epsilonTable

set_option linter.style.longLine false in


def restrict_epsilonWindows
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case)
    (window : ∀ epsilon, 0 < epsilon → ℝ)
    (hwindow_pos : ∀ epsilon hε, 0 < window epsilon hε)
    (hwindow_le :
      ∀ epsilon hε,
        window epsilon hε ≤ (H.epsilonTable epsilon hε).window) :
    Certificate C fkMass Case where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  epsilonTable := fun epsilon hε =>
    (H.epsilonTable epsilon hε).restrict_window
      (hwindow_pos epsilon hε) (hwindow_le epsilon hε)

set_option linter.style.longLine false in


def restrict_windows
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case)
    {pδ' : ℝ} (hpδ' : 0 < pδ') (hpδ_le : pδ' ≤ H.pδ)
    (window : ∀ epsilon, 0 < epsilon → ℝ)
    (hwindow_pos : ∀ epsilon hε, 0 < window epsilon hε)
    (hwindow_le :
      ∀ epsilon hε,
        window epsilon hε ≤ (H.epsilonTable epsilon hε).window) :
    Certificate C fkMass Case :=
  (H.restrict_pδ hpδ' hpδ_le).restrict_epsilonWindows
    window hwindow_pos hwindow_le

set_option linter.style.longLine false in






def of_globalCaseTables
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hfkMass_pos :
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
        0 < fkMass p)
    (table : ∀ epsilon : ℝ, 0 < epsilon → RatInterval.CaseTable Case)
    (classify : ∀ epsilon : ℝ, 0 < epsilon → ℝ → Case)
    (windows : ∀ epsilon : ℝ, 0 < epsilon → ℝ)
    (hwindow : ∀ (epsilon : ℝ) hε, 0 < windows epsilon hε)
    (hcovers :
      ∀ (epsilon : ℝ) hε,
        RatInterval.CaseTable.Covers
          (table epsilon hε) (classify epsilon hε))
    (hsound :
      ∀ (epsilon : ℝ) hε,
        RatInterval.CaseTable.Sound
          (table epsilon hε) (classify epsilon hε)
          (logRatioValue fkMass))
    (hlower :
      ∀ (epsilon : ℝ) hε k, k ∈ (table epsilon hε).cases →
        C.predictedExponent - epsilon <
          (((table epsilon hε).interval k).lower : ℝ))
    (hupper :
      ∀ (epsilon : ℝ) hε k, k ∈ (table epsilon hε).cases →
        (((table epsilon hε).interval k).upper : ℝ) <
          C.predictedExponent + epsilon) :
    Certificate C fkMass Case where
  pδ := pδ
  pδ_pos := hpδ
  fkMass_pos := hfkMass_pos
  epsilonTable := fun epsilon hε =>
    EpsilonTable.of_globalCaseTable
      (C := C)
      (fkMass := fkMass)
      (epsilon := epsilon)
      (window := windows epsilon hε)
      (table epsilon hε)
      (classify epsilon hε)
      (hwindow epsilon hε)
      (hcovers epsilon hε)
      (hsound epsilon hε)
      (hlower epsilon hε)
      (hupper epsilon hε)

set_option linter.style.longLine false in




noncomputable def of_eventuallyEq
    {fkMass modelMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    Certificate C fkMass Case := by
  classical
  let eqSpec := FKReparameterization.exists_Ioo_subset_of_eventually_left hEq
  let eqWindow := Classical.choose eqSpec
  have heqWindow_pos : 0 < eqWindow := (Classical.choose_spec eqSpec).1
  have heqWindow :
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
        fkMass p = modelMass p :=
    (Classical.choose_spec eqSpec).2
  refine
    { pδ := min H.pδ eqWindow
      pδ_pos := lt_min H.pδ_pos heqWindow_pos
      fkMass_pos := ?_
      epsilonTable := ?_ }
  · intro p hp
    have hpH : p ∈ Set.Ioo (Ising3DFKPC - H.pδ) Ising3DFKPC :=
      ⟨by linarith [hp.1, min_le_left H.pδ eqWindow], hp.2⟩
    have hpeq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC :=
      ⟨by linarith [hp.1, min_le_right H.pδ eqWindow], hp.2⟩
    have hEqp : fkMass p = modelMass p := heqWindow p hpeq
    simpa [hEqp] using H.fkMass_pos p hpH
  · intro epsilon hepsilon
    let T := H.epsilonTable epsilon hepsilon
    let w := min T.window eqWindow
    have hw : 0 < w := lt_min T.window_pos heqWindow_pos
    refine
      { table := T.table
        classify := T.classify
        window := w
        window_pos := hw
        covers_on_Ioo := ?_
        sound_on_Ioo := ?_
        lower_inside_slack := T.lower_inside_slack
        upper_inside_slack := T.upper_inside_slack }
    · intro p hp
      exact T.covers_on_Ioo p
        ⟨by
          have hwle : w ≤ T.window := min_le_left T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
    · intro p hp
      have hpT : p ∈ Set.Ioo (Ising3DFKPC - T.window) Ising3DFKPC :=
        ⟨by
          have hwle : w ≤ T.window := min_le_left T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
      have hpeq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC :=
        ⟨by
          have hwle : w ≤ eqWindow := min_le_right T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
      have hEqp : fkMass p = modelMass p := heqWindow p hpeq
      simpa [logRatioValue, hEqp] using T.sound_on_Ioo p hpT

end Certificate

set_option linter.style.longLine false in




structure VaryingCertificate
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  Case : ℝ → Type*
  caseDecidableEq : ∀ epsilon, DecidableEq (Case epsilon)
  epsilonTable :
    ∀ epsilon, 0 < epsilon →
      @EpsilonTable C fkMass (Case epsilon)
        (caseDecidableEq epsilon) epsilon

namespace VaryingCertificate

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def ofCertificate
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    VaryingCertificate C fkMass where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  Case := fun _ => Case
  caseDecidableEq := fun _ => inferInstance
  epsilonTable := H.epsilonTable

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (H : VaryingCertificate C fkMass) :
    VaryingCertificate D fkMass where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  Case := H.Case
  caseDecidableEq := H.caseDecidableEq
  epsilonTable := by
    intro epsilon hepsilon
    letI := H.caseDecidableEq epsilon
    exact (H.epsilonTable epsilon hepsilon).congr_predictedExponent hpred

set_option linter.style.longLine false in



def restrict_pδ
    {fkMass : ℝ → ℝ}
    (H : VaryingCertificate C fkMass)
    {pδ' : ℝ} (hpδ' : 0 < pδ') (hle : pδ' ≤ H.pδ) :
    VaryingCertificate C fkMass where
  pδ := pδ'
  pδ_pos := hpδ'
  fkMass_pos := by
    intro p hp
    exact H.fkMass_pos p
      ⟨by linarith [hp.1, hle], hp.2⟩
  Case := H.Case
  caseDecidableEq := H.caseDecidableEq
  epsilonTable := H.epsilonTable

set_option linter.style.longLine false in



def restrict_epsilonWindows
    {fkMass : ℝ → ℝ}
    (H : VaryingCertificate C fkMass)
    (window : ∀ epsilon, 0 < epsilon → ℝ)
    (hwindow_pos : ∀ epsilon hε, 0 < window epsilon hε)
    (hwindow_le :
      ∀ epsilon hε,
        letI : DecidableEq (H.Case epsilon) := H.caseDecidableEq epsilon
        window epsilon hε ≤ (H.epsilonTable epsilon hε).window) :
    VaryingCertificate C fkMass where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  Case := H.Case
  caseDecidableEq := H.caseDecidableEq
  epsilonTable := by
    intro epsilon hε
    letI := H.caseDecidableEq epsilon
    exact
      (H.epsilonTable epsilon hε).restrict_window
        (hwindow_pos epsilon hε) (hwindow_le epsilon hε)

set_option linter.style.longLine false in


def restrict_windows
    {fkMass : ℝ → ℝ}
    (H : VaryingCertificate C fkMass)
    {pδ' : ℝ} (hpδ' : 0 < pδ') (hpδ_le : pδ' ≤ H.pδ)
    (window : ∀ epsilon, 0 < epsilon → ℝ)
    (hwindow_pos : ∀ epsilon hε, 0 < window epsilon hε)
    (hwindow_le :
      ∀ epsilon hε,
        letI : DecidableEq (H.Case epsilon) := H.caseDecidableEq epsilon
        window epsilon hε ≤ (H.epsilonTable epsilon hε).window) :
    VaryingCertificate C fkMass :=
  (H.restrict_pδ hpδ' hpδ_le).restrict_epsilonWindows
    window hwindow_pos hwindow_le

set_option linter.style.longLine false in




def of_globalCaseTables
    {fkMass : ℝ → ℝ}
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hfkMass_pos :
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
        0 < fkMass p)
    (Case : ℝ → Type*)
    (caseDecidableEq : ∀ epsilon, DecidableEq (Case epsilon))
    (table :
      ∀ epsilon : ℝ, 0 < epsilon → RatInterval.CaseTable (Case epsilon))
    (classify : ∀ epsilon : ℝ, 0 < epsilon → ℝ → Case epsilon)
    (windows : ∀ epsilon : ℝ, 0 < epsilon → ℝ)
    (hwindow : ∀ (epsilon : ℝ) hε, 0 < windows epsilon hε)
    (hcovers :
      ∀ (epsilon : ℝ) hε,
        @RatInterval.CaseTable.Covers (Case epsilon) ℝ
          (caseDecidableEq epsilon)
          (table epsilon hε) (classify epsilon hε))
    (hsound :
      ∀ (epsilon : ℝ) hε,
        @RatInterval.CaseTable.Sound (Case epsilon) ℝ
          (caseDecidableEq epsilon)
          (table epsilon hε) (classify epsilon hε)
          (logRatioValue fkMass))
    (hlower :
      ∀ (epsilon : ℝ) hε k, k ∈ (table epsilon hε).cases →
        C.predictedExponent - epsilon <
          (((table epsilon hε).interval k).lower : ℝ))
    (hupper :
      ∀ (epsilon : ℝ) hε k, k ∈ (table epsilon hε).cases →
        (((table epsilon hε).interval k).upper : ℝ) <
          C.predictedExponent + epsilon) :
    VaryingCertificate C fkMass where
  pδ := pδ
  pδ_pos := hpδ
  fkMass_pos := hfkMass_pos
  Case := Case
  caseDecidableEq := caseDecidableEq
  epsilonTable := by
    intro epsilon hε
    letI := caseDecidableEq epsilon
    exact
      EpsilonTable.of_globalCaseTable
        (C := C)
        (fkMass := fkMass)
        (epsilon := epsilon)
        (window := windows epsilon hε)
        (table epsilon hε)
        (classify epsilon hε)
        (hwindow epsilon hε)
        (hcovers epsilon hε)
        (hsound epsilon hε)
        (hlower epsilon hε)
        (hupper epsilon hε)

set_option linter.style.longLine false in




noncomputable def of_eventuallyEq
    {fkMass modelMass : ℝ → ℝ}
    (H : VaryingCertificate C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    VaryingCertificate C fkMass := by
  classical
  let eqSpec := FKReparameterization.exists_Ioo_subset_of_eventually_left hEq
  let eqWindow := Classical.choose eqSpec
  have heqWindow_pos : 0 < eqWindow := (Classical.choose_spec eqSpec).1
  have heqWindow :
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
        fkMass p = modelMass p :=
    (Classical.choose_spec eqSpec).2
  refine
    { pδ := min H.pδ eqWindow
      pδ_pos := lt_min H.pδ_pos heqWindow_pos
      fkMass_pos := ?_
      Case := H.Case
      caseDecidableEq := H.caseDecidableEq
      epsilonTable := ?_ }
  · intro p hp
    have hpH : p ∈ Set.Ioo (Ising3DFKPC - H.pδ) Ising3DFKPC :=
      ⟨by linarith [hp.1, min_le_left H.pδ eqWindow], hp.2⟩
    have hpeq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC :=
      ⟨by linarith [hp.1, min_le_right H.pδ eqWindow], hp.2⟩
    have hEqp : fkMass p = modelMass p := heqWindow p hpeq
    simpa [hEqp] using H.fkMass_pos p hpH
  · intro epsilon hepsilon
    letI := H.caseDecidableEq epsilon
    let T := H.epsilonTable epsilon hepsilon
    let w := min T.window eqWindow
    have hw : 0 < w := lt_min T.window_pos heqWindow_pos
    refine
      { table := T.table
        classify := T.classify
        window := w
        window_pos := hw
        covers_on_Ioo := ?_
        sound_on_Ioo := ?_
        lower_inside_slack := T.lower_inside_slack
        upper_inside_slack := T.upper_inside_slack }
    · intro p hp
      exact T.covers_on_Ioo p
        ⟨by
          have hwle : w ≤ T.window := min_le_left T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
    · intro p hp
      have hpT : p ∈ Set.Ioo (Ising3DFKPC - T.window) Ising3DFKPC :=
        ⟨by
          have hwle : w ≤ T.window := min_le_left T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
      have hpeq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC :=
        ⟨by
          have hwle : w ≤ eqWindow := min_le_right T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
      have hEqp : fkMass p = modelMass p := heqWindow p hpeq
      simpa [logRatioValue, hEqp] using T.sound_on_Ioo p hpT

end VaryingCertificate

set_option linter.style.longLine false in



noncomputable def exactMonomialFKMass
    (C : RGCertificate Ising3DModel) : ℝ → ℝ :=
  fun p => Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p))

set_option linter.style.longLine false in


theorem exactMonomialFKMass_congr_predictedExponent
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent) :
    exactMonomialFKMass C = exactMonomialFKMass D := by
  funext p
  simp [exactMonomialFKMass, hpred]

set_option linter.style.longLine false in


theorem logRatioValue_exactMonomialFKMass
    (C : RGCertificate Ising3DModel)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (Ising3DFKPC - (1 : ℝ) / 2) Ising3DFKPC) :
    logRatioValue (exactMonomialFKMass C) p =
      C.predictedExponent := by
  have hdpos : 0 < Ising3DFKPC - p := sub_pos.mpr hp.2
  have hdlt_half : Ising3DFKPC - p < (1 : ℝ) / 2 := by
    linarith [hp.1]
  have hdlt_one : Ising3DFKPC - p < 1 := by
    linarith
  have hlog_neg : Real.log (Ising3DFKPC - p) < 0 :=
    (Real.log_neg_iff hdpos).mpr hdlt_one
  have hlog_ne : Real.log (Ising3DFKPC - p) ≠ 0 := ne_of_lt hlog_neg
  calc
    logRatioValue (exactMonomialFKMass C) p
        = (C.predictedExponent * Real.log (Ising3DFKPC - p)) /
            Real.log (Ising3DFKPC - p) := by
          simp [logRatioValue, exactMonomialFKMass]
    _ = C.predictedExponent := by
          field_simp [hlog_ne]

set_option linter.style.longLine false in



noncomputable def exactMonomialEpsilonTable
    (C : RGCertificate Ising3DModel)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    EpsilonTable C (exactMonomialFKMass C) Unit epsilon := by
  classical
  let lowerRat : ℚ :=
    Classical.choose
      (exists_rat_btwn (sub_lt_self C.predictedExponent hepsilon))
  have hlowerRat_spec :
      C.predictedExponent - epsilon < (lowerRat : ℝ) ∧
        (lowerRat : ℝ) < C.predictedExponent := by
    simpa [lowerRat] using
      Classical.choose_spec
        (exists_rat_btwn (sub_lt_self C.predictedExponent hepsilon))
  let upperRat : ℚ :=
    Classical.choose
      (exists_rat_btwn (lt_add_of_pos_right C.predictedExponent hepsilon))
  have hupperRat_spec :
      C.predictedExponent < (upperRat : ℝ) ∧
        (upperRat : ℝ) < C.predictedExponent + epsilon := by
    simpa [upperRat] using
      Classical.choose_spec
        (exists_rat_btwn (lt_add_of_pos_right C.predictedExponent hepsilon))
  let interval : RatInterval :=
    { lower := lowerRat
      upper := upperRat
      lower_le_upper := by
        exact_mod_cast le_of_lt
          (lt_trans hlowerRat_spec.2 hupperRat_spec.1) }
  exact
    { table :=
        { cases := {()}
          interval := fun _ => interval }
      classify := fun _ => ()
      window := (1 : ℝ) / 2
      window_pos := by norm_num
      covers_on_Ioo := by
        intro _ _
        simp
      sound_on_Ioo := by
        intro p hp
        have hvalue := logRatioValue_exactMonomialFKMass C hp
        dsimp [interval]
        rw [hvalue]
        exact ⟨le_of_lt hlowerRat_spec.2, le_of_lt hupperRat_spec.1⟩
      lower_inside_slack := by
        intro _ _
        simpa [interval] using hlowerRat_spec.1
      upper_inside_slack := by
        intro _ _
        simpa [interval] using hupperRat_spec.2 }

set_option linter.style.longLine false in



noncomputable def exactMonomialCertificate
    (C : RGCertificate Ising3DModel) :
    Certificate C (exactMonomialFKMass C) Unit where
  pδ := (1 : ℝ) / 2
  pδ_pos := by norm_num
  fkMass_pos := by
    intro _ _
    exact Real.exp_pos _
  epsilonTable := exactMonomialEpsilonTable C

set_option linter.style.longLine false in



noncomputable def constantPrefactorMonomialFKMass
    (C : RGCertificate Ising3DModel) (A : ℝ) : ℝ → ℝ :=
  fun p => A * exactMonomialFKMass C p

set_option linter.style.longLine false in


theorem constantPrefactorMonomialFKMass_congr_predictedExponent
    (C D : RGCertificate Ising3DModel)
    (A : ℝ)
    (hpred : C.predictedExponent = D.predictedExponent) :
    constantPrefactorMonomialFKMass C A =
      constantPrefactorMonomialFKMass D A := by
  funext p
  simp [constantPrefactorMonomialFKMass,
    exactMonomialFKMass_congr_predictedExponent C D hpred]

set_option linter.style.longLine false in



theorem logRatioValue_constantPrefactorMonomialFKMass
    (C : RGCertificate Ising3DModel)
    {A p : ℝ}
    (hA : 0 < A)
    (hp : p ∈ Set.Ioo (Ising3DFKPC - (1 : ℝ) / 2) Ising3DFKPC) :
    logRatioValue (constantPrefactorMonomialFKMass C A) p =
      C.predictedExponent + Real.log A / Real.log (Ising3DFKPC - p) := by
  have hdpos : 0 < Ising3DFKPC - p := sub_pos.mpr hp.2
  have hdlt_half : Ising3DFKPC - p < (1 : ℝ) / 2 := by
    linarith [hp.1]
  have hdlt_one : Ising3DFKPC - p < 1 := by
    linarith
  have hlog_neg : Real.log (Ising3DFKPC - p) < 0 :=
    (Real.log_neg_iff hdpos).mpr hdlt_one
  have hlog_ne : Real.log (Ising3DFKPC - p) ≠ 0 := ne_of_lt hlog_neg
  have hA_ne : A ≠ 0 := hA.ne'
  have hexp_ne :
      Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) ≠ 0 :=
    (Real.exp_pos _).ne'
  calc
    logRatioValue (constantPrefactorMonomialFKMass C A) p
        = (Real.log A +
              C.predictedExponent * Real.log (Ising3DFKPC - p)) /
            Real.log (Ising3DFKPC - p) := by
          unfold logRatioValue constantPrefactorMonomialFKMass exactMonomialFKMass
          rw [Real.log_mul hA_ne hexp_ne, Real.log_exp]
    _ = C.predictedExponent + Real.log A / Real.log (Ising3DFKPC - p) := by
          field_simp [hlog_ne]
          ring

set_option linter.style.longLine false in


theorem eventually_logRatioValue_constantPrefactorMonomialFKMass_halfSlack
    (C : RGCertificate Ising3DModel)
    {A ε : ℝ}
    (hA : 0 < A)
    (hε : 0 < ε) :
    ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
      C.predictedExponent - ε / 2 <
          logRatioValue (constantPrefactorMonomialFKMass C A) p ∧
        logRatioValue (constantPrefactorMonomialFKMass C A) p <
          C.predictedExponent + ε / 2 := by
  let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
  have hhalf : 0 < ε / 2 := by positivity
  have hlogd :
      Filter.Tendsto (fun p : ℝ => Real.log (Ising3DFKPC - p)) L
        Filter.atBot := by
    simpa [L, ParameterModel] using
      tendsto_log_betaC_sub_atBot (ParameterModel Ising3DFKPC)
  have hconst :
      Filter.Tendsto
        (fun p : ℝ => Real.log A / Real.log (Ising3DFKPC - p))
        L (nhds 0) :=
    hlogd.const_div_atBot (Real.log A)
  have hdist := (Metric.tendsto_nhds.mp hconst) (ε / 2) hhalf
  filter_upwards
    [hdist,
      Ioo_mem_nhdsLT
        (show Ising3DFKPC - (1 : ℝ) / 2 < Ising3DFKPC by norm_num)]
    with p hpdist hpwindow
  rw [Real.dist_eq] at hpdist
  have hsmall : |Real.log A / Real.log (Ising3DFKPC - p)| < ε / 2 := by
    simpa using hpdist
  have hvalue := logRatioValue_constantPrefactorMonomialFKMass C hA hpwindow
  rw [hvalue]
  have hsmall_bounds := abs_lt.mp hsmall
  constructor <;> linarith

set_option linter.style.longLine false in




noncomputable def constantPrefactorMonomialEpsilonTable
    (C : RGCertificate Ising3DModel)
    {A : ℝ}
    (hA : 0 < A)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    EpsilonTable C (constantPrefactorMonomialFKMass C A) Unit epsilon := by
  classical
  have hlowerGap :
      C.predictedExponent - epsilon <
        C.predictedExponent - epsilon / 2 := by
    linarith
  let lowerRat : ℚ := Classical.choose (exists_rat_btwn hlowerGap)
  have hlowerRat_spec :
      C.predictedExponent - epsilon < (lowerRat : ℝ) ∧
        (lowerRat : ℝ) < C.predictedExponent - epsilon / 2 := by
    simpa [lowerRat] using Classical.choose_spec (exists_rat_btwn hlowerGap)
  have hupperGap :
      C.predictedExponent + epsilon / 2 <
        C.predictedExponent + epsilon := by
    linarith
  let upperRat : ℚ := Classical.choose (exists_rat_btwn hupperGap)
  have hupperRat_spec :
      C.predictedExponent + epsilon / 2 < (upperRat : ℝ) ∧
        (upperRat : ℝ) < C.predictedExponent + epsilon := by
    simpa [upperRat] using Classical.choose_spec (exists_rat_btwn hupperGap)
  have hband :=
    eventually_logRatioValue_constantPrefactorMonomialFKMass_halfSlack
      C hA hepsilon
  let window : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  have hwindow_spec :
      0 < window ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
          C.predictedExponent - epsilon / 2 <
              logRatioValue (constantPrefactorMonomialFKMass C A) p ∧
            logRatioValue (constantPrefactorMonomialFKMass C A) p <
              C.predictedExponent + epsilon / 2 := by
    simpa [window] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  let interval : RatInterval :=
    { lower := lowerRat
      upper := upperRat
      lower_le_upper := by
        have hreal : (lowerRat : ℝ) < (upperRat : ℝ) := by
          linarith [hlowerRat_spec.2, hupperRat_spec.1]
        exact_mod_cast le_of_lt hreal }
  exact
    { table :=
        { cases := {()}
          interval := fun _ => interval }
      classify := fun _ => ()
      window := window
      window_pos := hwindow_spec.1
      covers_on_Ioo := by
        intro _ _
        simp
      sound_on_Ioo := by
        intro p hp
        have hpband := hwindow_spec.2 p hp
        dsimp [interval]
        exact ⟨le_of_lt (lt_trans hlowerRat_spec.2 hpband.1),
          le_of_lt (lt_trans hpband.2 hupperRat_spec.1)⟩
      lower_inside_slack := by
        intro _ _
        simpa [interval] using hlowerRat_spec.1
      upper_inside_slack := by
        intro _ _
        simpa [interval] using hupperRat_spec.2 }

set_option linter.style.longLine false in


noncomputable def constantPrefactorMonomialCertificate
    (C : RGCertificate Ising3DModel)
    {A : ℝ}
    (hA : 0 < A) :
    Certificate C (constantPrefactorMonomialFKMass C A) Unit where
  pδ := (1 : ℝ) / 2
  pδ_pos := by norm_num
  fkMass_pos := by
    intro _ _
    exact mul_pos hA (Real.exp_pos _)
  epsilonTable := constantPrefactorMonomialEpsilonTable C hA

set_option linter.style.longLine false in



noncomputable def epsilonTableOfLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    EpsilonTable C fkMass Unit epsilon := by
  classical
  have hhalf : 0 < epsilon / 2 := by positivity
  have hlowerGap :
      C.predictedExponent - epsilon <
        C.predictedExponent - epsilon / 2 := by
    linarith
  let lowerRat : ℚ := Classical.choose (exists_rat_btwn hlowerGap)
  have hlowerRat_spec :
      C.predictedExponent - epsilon < (lowerRat : ℝ) ∧
        (lowerRat : ℝ) < C.predictedExponent - epsilon / 2 := by
    simpa [lowerRat] using Classical.choose_spec (exists_rat_btwn hlowerGap)
  have hupperGap :
      C.predictedExponent + epsilon / 2 <
        C.predictedExponent + epsilon := by
    linarith
  let upperRat : ℚ := Classical.choose (exists_rat_btwn hupperGap)
  have hupperRat_spec :
      C.predictedExponent + epsilon / 2 < (upperRat : ℝ) ∧
        (upperRat : ℝ) < C.predictedExponent + epsilon := by
    simpa [upperRat] using Classical.choose_spec (exists_rat_btwn hupperGap)
  have hband := hsand.log_fk_mass_ratio_sandwich (epsilon / 2) hhalf
  let window : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  have hwindow_spec :
      0 < window ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
          C.predictedExponent - epsilon / 2 <
              logRatioValue fkMass p ∧
            logRatioValue fkMass p <
              C.predictedExponent + epsilon / 2 := by
    simpa [window, logRatioValue] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  let interval : RatInterval :=
    { lower := lowerRat
      upper := upperRat
      lower_le_upper := by
        have hreal : (lowerRat : ℝ) < (upperRat : ℝ) := by
          linarith [hlowerRat_spec.2, hupperRat_spec.1]
        exact_mod_cast le_of_lt hreal }
  exact
    { table :=
        { cases := {()}
          interval := fun _ => interval }
      classify := fun _ => ()
      window := window
      window_pos := hwindow_spec.1
      covers_on_Ioo := by
        intro _ _
        simp
      sound_on_Ioo := by
        intro p hp
        have hpband := hwindow_spec.2 p hp
        dsimp [interval]
        exact ⟨le_of_lt (lt_trans hlowerRat_spec.2 hpband.1),
          le_of_lt (lt_trans hpband.2 hupperRat_spec.1)⟩
      lower_inside_slack := by
        intro _ _
        simpa [interval] using hlowerRat_spec.1
      upper_inside_slack := by
        intro _ _
        simpa [interval] using hupperRat_spec.2 }

set_option linter.style.longLine false in




noncomputable def certificateOfLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    Certificate C fkMass Unit where
  pδ := hsand.pδ
  pδ_pos := hsand.pδ_pos
  fkMass_pos := hsand.fkMass_pos
  epsilonTable := epsilonTableOfLogRatioSandwich C fkMass hsand

set_option linter.style.longLine false in



noncomputable def certificateOfLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    Certificate C fkMass Unit :=
  certificateOfLogRatioSandwich C fkMass
    (freePositiveSubcriticalMassFKPCLogRatioSandwich_of_logRatioLimit
      C fkMass hratio)

set_option linter.style.longLine false in



noncomputable def logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro epsilon hepsilon
    let T := H.epsilonTable epsilon hepsilon
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - T.window < Ising3DFKPC by
          linarith [T.window_pos])] with p hp
    have hcover : T.classify p ∈ T.table.cases :=
      T.covers_on_Ioo p hp
    have hmem :
        (T.table.interval (T.classify p)).MemR (logRatioValue fkMass p) :=
      T.sound_on_Ioo p hp
    constructor
    · exact lt_of_lt_of_le
        (T.lower_inside_slack (T.classify p) hcover) hmem.1
    · exact lt_of_le_of_lt hmem.2
        (T.upper_inside_slack (T.classify p) hcover)

set_option linter.style.longLine false in



noncomputable def logRatioSandwichVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro epsilon hepsilon
    letI := H.caseDecidableEq epsilon
    let T := H.epsilonTable epsilon hepsilon
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - T.window < Ising3DFKPC by
          linarith [T.window_pos])] with p hp
    have hcover : T.classify p ∈ T.table.cases :=
      T.covers_on_Ioo p hp
    have hmem :
        (T.table.interval (T.classify p)).MemR (logRatioValue fkMass p) :=
      T.sound_on_Ioo p hp
    constructor
    · exact lt_of_lt_of_le
        (T.lower_inside_slack (T.classify p) hcover) hmem.1
    · exact lt_of_le_of_lt hmem.2
        (T.upper_inside_slack (T.classify p) hcover)

set_option linter.style.longLine false in


noncomputable def logRatioSandwich_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioSandwich_of_eventuallyEq
    C (logRatioSandwich C modelMass H) hEq

set_option linter.style.longLine false in


noncomputable def logRatioSandwichVarying_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    (H : VaryingCertificate C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioSandwich_of_eventuallyEq
    C (logRatioSandwichVarying C modelMass H) hEq

set_option linter.style.longLine false in


noncomputable def logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
    C fkMass (logRatioSandwich C fkMass H)

set_option linter.style.longLine false in


noncomputable def logRatioLimitVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
    C fkMass (logRatioSandwichVarying C fkMass H)

set_option linter.style.longLine false in


noncomputable def logRatioLimit_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_eventuallyEq
    C (logRatioLimit C modelMass H) hEq

set_option linter.style.longLine false in



noncomputable def logRatioLimitVarying_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    (H : VaryingCertificate C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_eventuallyEq
    C (logRatioLimitVarying C modelMass H) hEq

set_option linter.style.longLine false in


noncomputable def logAffine
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
    C fkMass (logRatioLimit C fkMass H)

set_option linter.style.longLine false in


noncomputable def logAffineVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
    C fkMass (logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in


noncomputable def exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    C fkMass (logRatioLimit C fkMass H)

set_option linter.style.longLine false in


noncomputable def exactPowerLawVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    C fkMass (logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in


noncomputable def selectedIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C hselected.fkMass Case) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
    C hmass hselected
    (exactPowerLaw C hselected.fkMass H)

set_option linter.style.longLine false in


noncomputable def selectedIooSandwichVarying
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (H : VaryingCertificate C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
    C hmass hselected
    (exactPowerLawVarying C hselected.fkMass H)

set_option linter.style.longLine false in



noncomputable def selectedIooSandwich_of_eventualMassEqCaseCertificate
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    {modelMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        hselected.fkMass p = modelMass p)
    (H : Certificate C modelMass Case) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  selectedIooSandwich C hmass hselected (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in



noncomputable def selectedIooSandwichVarying_of_eventualMassEqCaseCertificate
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    {modelMass : ℝ → ℝ}
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        hselected.fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  selectedIooSandwichVarying C hmass hselected
    (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C hselected.fkMass Case) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected
    (logRatioLimit C hselected.fkMass H)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (H : VaryingCertificate C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected
    (logRatioLimitVarying C hselected.fkMass H)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C fkMass hsand)

set_option linter.style.longLine false in




noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementAsymptoticPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        D fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree hβeq hβc hselectedEq
    (hasymp.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate C fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in

noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementConstantPrefactorMonomial
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass C A (IsingFK.pOfBeta β)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementExactMonomial_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass D (IsingFK.pOfBeta β)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementExactMonomial
    I C hagree hβeq hβc
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass D A (IsingFK.pOfBeta β)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree hβeq hβc hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (by
      simpa [hselected] using logRatioLimit C fkMass H)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate C fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (by
      simpa [hselected] using logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D fkMass Case) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate D fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D modelMass Case) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate D modelMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected hratio

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C fkMass hsand)

set_option linter.style.longLine false in




noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        D fkMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree hβeq hβc hselectedEq
    (hasymp.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass C A (IsingFK.pOfBeta β)) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass D (IsingFK.pOfBeta β)) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    I C hagree hβeq hβc
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in



noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass D A (IsingFK.pOfBeta β)) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree hβeq hβc hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C hselected.fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (logRatioLimit C hselected.fkMass H)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (H : VaryingCertificate C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (logRatioLimitVarying C hselected.fkMass H)

set_option linter.style.longLine false in





theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected hratio

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselected hsand

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree hβeq hβc hselectedEq
    (hasymp.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D fkMass Case) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate D fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in

theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in




theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass C A (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass D (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial
    I C hagree hβeq hβc
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass D A (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree hβeq hβc hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in




theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (logRatioLimit_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementEventualMassEqCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected
    (logRatioLimit_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D modelMass Case) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementEventualMassEqCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D modelMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected
    (logRatioLimitVarying_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (logRatioLimitVarying_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate D modelMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate D modelMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in





theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimit C fkMass H)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected hratio

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected hsand

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree htransition hnonpos hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree htransition hnonpos hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    I C hagree htransition hnonpos hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree htransition hnonpos hselectedEq
    (hasymp.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in




theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass C A (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass D (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    I C hagree htransition hnonpos
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass D A (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree htransition hnonpos hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimit_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D modelMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    I C hagree htransition hnonpos hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimitVarying_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in



theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate D modelMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    I C hagree htransition hnonpos hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

end FKLogRatioCaseCertificate

end Exact3D
end StatMech
