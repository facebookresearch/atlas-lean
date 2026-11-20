/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.Z2GaugeGKS










open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FrontierA

noncomputable section

local instance subsystemPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


def embeddingSplitEquiv {A B : Type*} (f : A ↪ B) :
    A ⊕ {b : B // b ∉ Set.range f} ≃ B :=
  (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl fun b => b ∈ Set.range f)

@[simp] theorem embeddingSplitEquiv_inl {A B : Type*}
    (f : A ↪ B) (a : A) :
    embeddingSplitEquiv f (.inl a) = f a := by
  simp [embeddingSplitEquiv, Equiv.sumCompl]

@[simp] theorem embeddingSplitEquiv_symm_apply {A B : Type*}
    (f : A ↪ B) (a : A) :
    (embeddingSplitEquiv f).symm (f a) = .inl a := by
  apply (embeddingSplitEquiv f).injective
  simp



def gaugeConfigSplitEquiv {A B : Type*} (f : A ↪ B) :
    (A → Bool) × ({b : B // b ∉ Set.range f} → Bool) ≃ (B → Bool) :=
  (Equiv.sumArrowEquivProdArrow A {b : B // b ∉ Set.range f} Bool).symm |>.trans
    (Equiv.arrowCongr (embeddingSplitEquiv f) (Equiv.refl Bool))

@[simp] theorem gaugeConfigSplitEquiv_apply_emb {A B : Type*}
    (f : A ↪ B) (sigma : A → Bool)
    (tau : {b : B // b ∉ Set.range f} → Bool) (a : A) :
    gaugeConfigSplitEquiv f (sigma, tau) (f a) = sigma a := by
  simp [gaugeConfigSplitEquiv]


def extendGaugeCoupling {Psmall Pbig : Type*} (f : Psmall ↪ Pbig)
    (K : Psmall → Real) : Pbig → Real :=
  fun q => match (embeddingSplitEquiv f).symm q with
    | .inl p => K p
    | .inr _ => 0

@[simp] theorem extendGaugeCoupling_apply {Psmall Pbig : Type*}
    (f : Psmall ↪ Pbig) (K : Psmall → Real) (p : Psmall) :
    extendGaugeCoupling f K (f p) = K p := by
  simp [extendGaugeCoupling]

variable {Esmall Ebig Psmall Pbig : Type*}
  [Fintype Esmall] [DecidableEq Esmall] [Fintype Ebig] [DecidableEq Ebig]
  [Fintype Psmall] [DecidableEq Psmall] [Fintype Pbig] [DecidableEq Pbig]

theorem plaquetteSpin_gaugeConfigSplitEquiv
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) (p : Psmall) :
    plaquetteSpin incidenceBig (gaugeConfigSplitEquiv eEmb (sigma, tau)) (pEmb p) =
      plaquetteSpin incidenceSmall sigma p := by
  unfold plaquetteSpin
  rw [hinc, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e _
  simp [gaugeEdgeSpin]

theorem gaugeAction_extendGaugeCoupling_gaugeConfigSplitEquiv
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
    gaugeAction incidenceBig (extendGaugeCoupling pEmb K)
        (gaugeConfigSplitEquiv eEmb (sigma, tau)) =
      gaugeAction incidenceSmall K sigma := by
  unfold gaugeAction
  rw [← (embeddingSplitEquiv pEmb).sum_comp, Fintype.sum_sum_type]
  simp [extendGaugeCoupling,
    plaquetteSpin_gaugeConfigSplitEquiv incidenceSmall incidenceBig eEmb pEmb hinc]

theorem gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
    gaugeWeight incidenceBig (extendGaugeCoupling pEmb K)
        (gaugeConfigSplitEquiv eEmb (sigma, tau)) =
      gaugeWeight incidenceSmall K sigma := by
  unfold gaugeWeight
  rw [gaugeAction_extendGaugeCoupling_gaugeConfigSplitEquiv
    incidenceSmall incidenceBig eEmb pEmb hinc]

theorem wilsonSpin_gaugeConfigSplitEquiv_map
    (eEmb : Esmall ↪ Ebig) (L : Finset Esmall)
    (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
    wilsonSpin (L.map eEmb) (gaugeConfigSplitEquiv eEmb (sigma, tau)) =
      wilsonSpin L sigma := by
  unfold wilsonSpin
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e _
  simp [gaugeEdgeSpin]

theorem gaugePartition_extendGaugeCoupling
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) :
    gaugePartition incidenceBig (extendGaugeCoupling pEmb K) =
      Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) *
        gaugePartition incidenceSmall K := by
  unfold gaugePartition
  rw [← (gaugeConfigSplitEquiv eEmb).sum_comp, Fintype.sum_prod_type]
  simp_rw [gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv
    incidenceSmall incidenceBig eEmb pEmb hinc]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]

theorem gaugeWilsonNumerator_extendGaugeCoupling
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (L : Finset Esmall) :
    gaugeWilsonNumerator incidenceBig (extendGaugeCoupling pEmb K) (L.map eEmb) =
      Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) *
        gaugeWilsonNumerator incidenceSmall K L := by
  unfold gaugeWilsonNumerator
  rw [← (gaugeConfigSplitEquiv eEmb).sum_comp, Fintype.sum_prod_type]
  simp_rw [gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv
    incidenceSmall incidenceBig eEmb pEmb hinc,
    wilsonSpin_gaugeConfigSplitEquiv_map]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]



theorem gaugeWilsonExpectation_extendGaugeCoupling
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (L : Finset Esmall) :
    gaugeWilsonExpectation incidenceBig (extendGaugeCoupling pEmb K) (L.map eEmb) =
      gaugeWilsonExpectation incidenceSmall K L := by
  unfold gaugeWilsonExpectation
  rw [gaugeWilsonNumerator_extendGaugeCoupling incidenceSmall incidenceBig
      eEmb pEmb hinc,
    gaugePartition_extendGaugeCoupling incidenceSmall incidenceBig eEmb pEmb hinc]
  have hcard :
      (Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) : Real) ≠ 0 := by
    positivity
  exact mul_div_mul_left _ _ hcard

end

end StatMech.FrontierA
