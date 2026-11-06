/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Binding the finite 128-coordinate lookup to the actual source tensor input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactColumnData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQIntegerSparse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual low or high source dictionary code of an input Gaussian term. -/
def monsterNortonLine01CompactSourceCode (a : Fin 64) (h : Fin 2) : Fin 4096 :=
  ⟨(monsterNortonLine01ShortInputCode a).val + 2048 * h.val, by
    have hd := (monsterNortonLine01ShortInputCode a).isLt
    have hh := h.isLt
    omega⟩

/-- The exact integer spin label after the genuine Norton v translation. -/
def monsterNortonLine01CompactSourceSeed (a : Fin 64) (h : Fin 2) : Fin 4096 :=
  nortonUIntegerLabel (golayLabelCoefficients (monsterNortonLine01CompactSourceCode a h) +
    spinTranslation y555NortonVQ)

/-- Every source coefficient retains the source quarter-weight and the complete actual Q phase. -/
def monsterNortonLine01CompactSourceCoefficient (k : Fin 16) (a : Fin 64) (h : Fin 2) : ℤ :=
  monsterNortonLine01InitialSpinSigns a *
    nortonUIntegerSign (golayMaskWeight
      (golayEncodedMask (monsterNortonLine01ShortInputCode a).val) / 4 : ℕ) *
    (if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit
      (monsterNortonLine01ShortPhysicalColumn k).val then -1 else 1) *
    (if h = 0 then 1 else -1) *
    nortonUIntegerSign (spinPhase y555NortonVQ
      (golayLabelCoefficients (monsterNortonLine01CompactSourceCode a h) +
        spinTranslation y555NortonVQ))

set_option maxHeartbeats 16000000 in
-- These 128 index checks concern the actual source translation, without a scalar assumption.
/-- Every genuine source seed belongs to the displayed input catalogue. -/
theorem monsterNortonLine01CompactSourceSeed_support (a : Fin 64) (h : Fin 2) :
    monsterNortonLine01CompactInputSupport (monsterNortonLine01CompactSourceSeed a h) := by
  revert a h
  decide +kernel

set_option maxHeartbeats 16000000 in
-- All 2048 signed source coefficients are checked against the actual Q phase.
/-- The finite lookup coefficient is precisely the actual translated source coefficient. -/
theorem monsterNortonLine01CompactSourceCoefficient_actual
    (k : Fin 16) (a : Fin 64) (h : Fin 2) :
    monsterNortonLine01CompactInputCoefficient k
      (monsterNortonLine01CompactInputLookup (monsterNortonLine01CompactSourceSeed a h)) =
        monsterNortonLine01CompactSourceCoefficient k a h := by
  revert k a h
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Distinctness is checked on the full finite source-code table.
/-- The sixty-four source codes are genuinely distinct. -/
theorem monsterNortonLine01ShortInputCode_injective :
    Function.Injective monsterNortonLine01ShortInputCode := by
  decide +kernel

/-- Translation preserves the distinct low and high actual source labels. -/
theorem monsterNortonLine01CompactSourceSeed_injective :
    Function.Injective (fun p : Fin 64 × Fin 2 =>
      monsterNortonLine01CompactSourceSeed p.1 p.2) := by
  intro a b hab
  have ht := congrArg golayLabelCoefficients hab
  simp only [monsterNortonLine01CompactSourceSeed, nortonUIntegerLabel_inverse] at ht
  have hc := congrArg nortonUIntegerLabel (add_right_cancel ht)
  simp only [nortonUIntegerLabel_coeff] at hc
  have hn := congrArg Fin.val hc
  change (monsterNortonLine01ShortInputCode a.1).val + 2048 * a.2.val =
    (monsterNortonLine01ShortInputCode b.1).val + 2048 * b.2.val at hn
  have ha := (monsterNortonLine01ShortInputCode a.1).isLt
  have hb := (monsterNortonLine01ShortInputCode b.1).isLt
  have ha2 := a.2.isLt
  have hb2 := b.2.isLt
  have hd : (monsterNortonLine01ShortInputCode a.1).val =
      (monsterNortonLine01ShortInputCode b.1).val := by omega
  have hh : a.2.val = b.2.val := by omega
  exact Prod.ext (monsterNortonLine01ShortInputCode_injective (Fin.ext hd)) (Fin.ext hh)

private def sourceLookup (p : Fin 64 × Fin 2) : Fin 128 :=
  monsterNortonLine01CompactInputLookup (monsterNortonLine01CompactSourceSeed p.1 p.2)

private theorem sourceLookup_injective : Function.Injective sourceLookup := by
  intro a b hab
  apply monsterNortonLine01CompactSourceSeed_injective
  have ha := monsterNortonLine01CompactSourceSeed_support a.1 a.2
  have hb := monsterNortonLine01CompactSourceSeed_support b.1 b.2
  change monsterNortonLine01CompactInputLabel (sourceLookup a) =
    monsterNortonLine01CompactSourceSeed a.1 a.2 at ha
  change monsterNortonLine01CompactInputLabel (sourceLookup b) =
    monsterNortonLine01CompactSourceSeed b.1 b.2 at hb
  exact ha.symm.trans ((congrArg monsterNortonLine01CompactInputLabel hab).trans hb)

private def sourceLookupEnd (p : Fin 128) : Fin 128 :=
  sourceLookup (finProdFinEquiv.symm p : Fin 64 × Fin 2)

private theorem sourceLookupEnd_injective : Function.Injective sourceLookupEnd :=
  sourceLookup_injective.comp (@finProdFinEquiv 64 2).symm.injective

private noncomputable def sourceCatalogueEquiv : (Fin 64 × Fin 2) ≃ Fin 128 :=
  finProdFinEquiv.trans (Equiv.ofBijective sourceLookupEnd
    ⟨sourceLookupEnd_injective, Finite.surjective_of_injective sourceLookupEnd_injective⟩)

private theorem sourceCatalogueEquiv_apply (p : Fin 64 × Fin 2) :
    sourceCatalogueEquiv p = sourceLookup p := by
  change sourceLookup (finProdFinEquiv.symm (finProdFinEquiv p)) = sourceLookup p
  rw [Equiv.symm_apply_apply]

/-- The exact signed integer source vector before inverse Norton transport. -/
def monsterNortonLine01CompactSourceVector (k : Fin 16) : NortonUIntegerVector :=
  ∑ p : Fin 64 × Fin 2, monsterNortonLine01CompactSourceCoefficient k p.1 p.2 •
    (Pi.single (monsterNortonLine01CompactSourceSeed p.1 p.2) 1 : NortonUIntegerVector)

/-- The finite coefficient lookup is the complete actual translated source vector. -/
theorem monsterNortonLine01CompactInputVector_source (k : Fin 16) :
    monsterNortonLine01CompactInputVector k = monsterNortonLine01CompactSourceVector k := by
  rw [monsterNortonLine01CompactInputVector_sparse, monsterNortonLine01CompactSourceVector]
  have hr := Equiv.sum_comp sourceCatalogueEquiv (fun p : Fin 128 =>
    monsterNortonLine01CompactInputCoefficient k p •
      (Pi.single (monsterNortonLine01CompactInputLabel p) 1 : NortonUIntegerVector))
  rw [← hr]
  apply Finset.sum_congr rfl
  intro p _
  rw [sourceCatalogueEquiv_apply]
  change monsterNortonLine01CompactInputCoefficient k
    (monsterNortonLine01CompactInputLookup (monsterNortonLine01CompactSourceSeed p.1 p.2)) •
      Pi.single (monsterNortonLine01CompactInputLabel
        (monsterNortonLine01CompactInputLookup
          (monsterNortonLine01CompactSourceSeed p.1 p.2))) 1 = _
  rw [monsterNortonLine01CompactSourceCoefficient_actual,
    monsterNortonLine01CompactSourceSeed_support p.1 p.2]

set_option maxHeartbeats 2000000 in
-- The proof transports the source sums before normalizing their low and high labels.
/-- The catalogue is exactly the weighted actual Q image of the original source Y vectors. -/
theorem monsterNortonLine01CompactInputVector_actual (k : Fin 16) :
    monsterNortonLine01CompactInputVector k =
      ∑ a : Fin 64, (monsterNortonLine01InitialSpinSigns a *
        nortonUIntegerSign (golayMaskWeight
          (golayEncodedMask (monsterNortonLine01ShortInputCode a).val) / 4 : ℕ) *
        (if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit
          (monsterNortonLine01ShortPhysicalColumn k).val then -1 else 1)) •
        nortonUIntegerQ y555NortonVQ
          (monsterNortonSourceYInteger (monsterNortonLine01ShortInputCode a)) := by
  rw [monsterNortonLine01CompactInputVector_source,
    monsterNortonLine01CompactSourceVector, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fin.sum_univ_two, monsterNortonUIntegerQ_source_Y]
  have ho : (1 : Fin 2) ≠ 0 := by decide
  simp only [monsterNortonLine01CompactSourceCoefficient,
    monsterNortonLine01CompactSourceSeed, monsterNortonLine01CompactSourceCode,
    Fin.val_zero, Fin.val_one, mul_zero, mul_one, add_zero, ite_true, ho, ite_false,
    mul_neg, smul_sub, mul_smul, neg_smul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
