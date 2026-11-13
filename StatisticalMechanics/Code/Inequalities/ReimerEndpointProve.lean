/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Code.Inequalities.ReimerCompression
import Code.Inequalities.ReimerDoubled
import Code.Inequalities.ReimerCompressLib

open Finset MeasureTheory
open scoped NNReal

namespace StatMech

open ConfigSpace

variable {α : Type*}










def leftBlock : Set (α ⊕ α) := {x | x.isLeft}


def rightBlock : Set (α ⊕ α) := {x | x.isRight}


theorem disjoint_leftBlock_rightBlock : Disjoint (leftBlock (α := α)) (rightBlock (α := α)) := by
  rw [Set.disjoint_left]
  rintro (a | a) hl hr <;>
    simp only [leftBlock, rightBlock, Set.mem_setOf_eq, Sum.isLeft, Sum.isRight,
      Bool.false_eq_true] at hl hr



def leftCfg (ω : ConfigSpace (α ⊕ α)) : ConfigSpace α := fun a => ω (Sum.inl a)



def rightCfg (ω : ConfigSpace (α ⊕ α)) : ConfigSpace α := fun a => ω (Sum.inr a)



def leftEvent (A : Set (ConfigSpace α)) : Set (ConfigSpace (α ⊕ α)) := {ω | leftCfg ω ∈ A}


def rightEvent (B : Set (ConfigSpace α)) : Set (ConfigSpace (α ⊕ α)) := {ω | rightCfg ω ∈ B}

@[simp] lemma mem_leftEvent {A : Set (ConfigSpace α)} {ω : ConfigSpace (α ⊕ α)} :
    ω ∈ leftEvent A ↔ leftCfg ω ∈ A := Iff.rfl

@[simp] lemma mem_rightEvent {B : Set (ConfigSpace α)} {ω : ConfigSpace (α ⊕ α)} :
    ω ∈ rightEvent B ↔ rightCfg ω ∈ B := Iff.rfl








lemma leftCfg_eq_of_agreeOn_leftBlock {ω ω' : ConfigSpace (α ⊕ α)}
    (h : agreeOn (leftBlock (α := α)) ω ω') : leftCfg ω' = leftCfg ω := by
  funext a
  exact h (Sum.inl a) (by simp [leftBlock, Sum.isLeft])


lemma rightCfg_eq_of_agreeOn_rightBlock {ω ω' : ConfigSpace (α ⊕ α)}
    (h : agreeOn (rightBlock (α := α)) ω ω') : rightCfg ω' = rightCfg ω := by
  funext a
  exact h (Sum.inr a) (by simp [rightBlock, Sum.isRight])


theorem dependsOn_leftEvent (A : Set (ConfigSpace α)) :
    DependsOn (leftEvent A) (leftBlock (α := α)) := by
  intro ω ω' hag
  simp only [mem_leftEvent]
  rw [leftCfg_eq_of_agreeOn_leftBlock hag]


theorem dependsOn_rightEvent (B : Set (ConfigSpace α)) :
    DependsOn (rightEvent B) (rightBlock (α := α)) := by
  intro ω ω' hag
  simp only [mem_rightEvent]
  rw [rightCfg_eq_of_agreeOn_rightBlock hag]










section Support

variable [DecidableEq α]




theorem leftCfg_supportCfg_dbl (S T : Finset α) :
    leftCfg (supportCfg (dbl S T)) = supportCfg S := by
  funext a
  simp only [leftCfg, supportCfg_apply, mem_dbl_inl]




theorem rightCfg_supportCfg_dbl (S T : Finset α) :
    rightCfg (supportCfg (dbl S T)) = supportCfg T := by
  funext a
  simp only [rightCfg, supportCfg_apply, mem_dbl_inr]

end Support

section Weighted

variable [Fintype α] [DecidableEq α]












def doubleWeight (w : α → Bool → ℝ) : (α ⊕ α) → Bool → ℝ := Sum.elim w w

omit [Fintype α] [DecidableEq α] in
@[simp] lemma doubleWeight_apply_inl (w : α → Bool → ℝ) (a : α) :
    doubleWeight w (Sum.inl a) = w a := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] lemma doubleWeight_apply_inr (w : α → Bool → ℝ) (a : α) :
    doubleWeight w (Sum.inr a) = w a := rfl

omit [Fintype α] [DecidableEq α] in

lemma doubleWeight_prob {w : α → Bool → ℝ} (hw1 : ∀ x, w x false + w x true = 1) :
    ∀ x, doubleWeight w x false + doubleWeight w x true = 1 := by
  rintro (a | a) <;> simp only [doubleWeight_apply_inl, doubleWeight_apply_inr] <;> exact hw1 a

omit [Fintype α] [DecidableEq α] in

lemma doubleWeight_nonneg {w : α → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b) :
    ∀ x b, 0 ≤ doubleWeight w x b := by
  rintro (a | a) b <;> simp only [doubleWeight_apply_inl, doubleWeight_apply_inr] <;> exact hw0 a b

omit [DecidableEq α] in


lemma pweight_doubleWeight (w : α → Bool → ℝ) (ω : ConfigSpace (α ⊕ α)) :
    pweight (doubleWeight w) ω = pweight w (leftCfg ω) * pweight w (rightCfg ω) := by
  simp only [pweight, doubleWeight, leftCfg, rightCfg]
  rw [Fintype.prod_sum_type]; rfl


lemma sum_pweight_eq_one {w : α → Bool → ℝ} (hw1 : ∀ x, w x false + w x true = 1) :
    (∑ b : ConfigSpace α, pweight w b) = 1 := by
  simp only [pweight]
  rw [← Fintype.prod_sum (fun s => w s)]
  simp only [Fintype.sum_bool]
  exact Finset.prod_eq_one (fun s _ => by rw [add_comm]; exact hw1 s)






theorem wprob_leftEvent (w : α → Bool → ℝ) (hw1 : ∀ x, w x false + w x true = 1)
    (A : Set (ConfigSpace α)) :
    wprob (doubleWeight w) (leftEvent A) = wprob w A := by
  classical
  set e := Equiv.sumArrowEquivProdArrow α α Bool with he
  simp only [wprob]
  rw [← e.symm.sum_comp
    (fun ω => (leftEvent A).indicator (fun _ => (1 : ℝ)) ω * pweight (doubleWeight w) ω)]
  rw [Fintype.sum_prod_type]
  have hcalc : ∀ (a b : ConfigSpace α),
      (leftEvent A).indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) *
          pweight (doubleWeight w) (e.symm (a, b))
        = A.indicator (fun _ => (1 : ℝ)) a * pweight w a * pweight w b := by
    intro a b
    have hl : leftCfg (e.symm (a, b)) = a := rfl
    have hr : rightCfg (e.symm (a, b)) = b := rfl
    rw [pweight_doubleWeight, hl, hr]
    have hmemiff : e.symm (a, b) ∈ leftEvent A ↔ a ∈ A := by rw [mem_leftEvent, hl]
    have hind : (leftEvent A).indicator (fun _ => (1 : ℝ)) (e.symm (a, b))
        = A.indicator (fun _ => (1 : ℝ)) a := by
      by_cases hA : a ∈ A
      · rw [Set.indicator_of_mem (hmemiff.mpr hA), Set.indicator_of_mem hA]
      · rw [Set.indicator_of_notMem (fun hc => hA (hmemiff.mp hc)), Set.indicator_of_notMem hA]
    rw [hind]; ring
  calc (∑ a : ConfigSpace α, ∑ b : ConfigSpace α,
          (leftEvent A).indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) *
            pweight (doubleWeight w) (e.symm (a, b)))
      = ∑ a : ConfigSpace α, ∑ b : ConfigSpace α,
          A.indicator (fun _ => (1 : ℝ)) a * pweight w a * pweight w b := by
        apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
        exact hcalc a b
    _ = ∑ a : ConfigSpace α, A.indicator (fun _ => (1 : ℝ)) a * pweight w a := by
        apply Finset.sum_congr rfl; intro a _
        rw [← Finset.mul_sum]
        rw [show (∑ b : ConfigSpace α, pweight w b) = 1 from sum_pweight_eq_one hw1, mul_one]
    _ = wprob w A := rfl



theorem wprob_rightEvent (w : α → Bool → ℝ) (hw1 : ∀ x, w x false + w x true = 1)
    (B : Set (ConfigSpace α)) :
    wprob (doubleWeight w) (rightEvent B) = wprob w B := by
  classical
  set e := Equiv.sumArrowEquivProdArrow α α Bool with he
  simp only [wprob]
  rw [← e.symm.sum_comp
    (fun ω => (rightEvent B).indicator (fun _ => (1 : ℝ)) ω * pweight (doubleWeight w) ω)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hcalc : ∀ (a b : ConfigSpace α),
      (rightEvent B).indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) *
          pweight (doubleWeight w) (e.symm (a, b))
        = B.indicator (fun _ => (1 : ℝ)) b * pweight w b * pweight w a := by
    intro a b
    have hl : leftCfg (e.symm (a, b)) = a := rfl
    have hr : rightCfg (e.symm (a, b)) = b := rfl
    rw [pweight_doubleWeight, hl, hr]
    have hmemiff : e.symm (a, b) ∈ rightEvent B ↔ b ∈ B := by rw [mem_rightEvent, hr]
    have hind : (rightEvent B).indicator (fun _ => (1 : ℝ)) (e.symm (a, b))
        = B.indicator (fun _ => (1 : ℝ)) b := by
      by_cases hB : b ∈ B
      · rw [Set.indicator_of_mem (hmemiff.mpr hB), Set.indicator_of_mem hB]
      · rw [Set.indicator_of_notMem (fun hc => hB (hmemiff.mp hc)), Set.indicator_of_notMem hB]
    rw [hind]; ring
  calc (∑ b : ConfigSpace α, ∑ a : ConfigSpace α,
          (rightEvent B).indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) *
            pweight (doubleWeight w) (e.symm (a, b)))
      = ∑ b : ConfigSpace α, ∑ a : ConfigSpace α,
          B.indicator (fun _ => (1 : ℝ)) b * pweight w b * pweight w a := by
        apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro a _
        exact hcalc a b
    _ = ∑ b : ConfigSpace α, B.indicator (fun _ => (1 : ℝ)) b * pweight w b := by
        apply Finset.sum_congr rfl; intro b _
        rw [← Finset.mul_sum]
        rw [show (∑ a : ConfigSpace α, pweight w a) = 1 from sum_pweight_eq_one hw1, mul_one]
    _ = wprob w B := rfl




theorem supportCfg_dbl_mem_leftEvent (𝒜 : Finset (Finset α)) (S T : Finset α) :
    supportCfg (dbl S T) ∈ leftEvent (familyEvent 𝒜) ↔ S ∈ 𝒜 := by
  simp only [mem_leftEvent, mem_familyEvent, leftCfg_supportCfg_dbl, cfgSupport_supportCfg]


theorem supportCfg_dbl_mem_rightEvent (ℬ : Finset (Finset α)) (S T : Finset α) :
    supportCfg (dbl S T) ∈ rightEvent (familyEvent ℬ) ↔ T ∈ ℬ := by
  simp only [mem_rightEvent, mem_familyEvent, rightCfg_supportCfg_dbl, cfgSupport_supportCfg]















theorem reimer_wprob_doubled_split (φ : (α ⊕ α) → Bool → ℝ)
    (hφ1 : ∀ x, φ x false + φ x true = 1) (A B : Set (ConfigSpace α)) :
    wprob φ (disjointOccurrence (leftEvent A) (rightEvent B))
      = wprob φ (leftEvent A) * wprob φ (rightEvent B) :=
  reimer_wprob_of_disjoint_support φ hφ1
    (dependsOn_leftEvent A) (dependsOn_rightEvent B) disjoint_leftBlock_rightBlock








theorem reimer_wprob_doubled_familyEvent (φ : (α ⊕ α) → Bool → ℝ)
    (hφ1 : ∀ x, φ x false + φ x true = 1) (𝒜 ℬ : Finset (Finset α)) :
    wprob φ (disjointOccurrence (leftEvent (familyEvent 𝒜)) (rightEvent (familyEvent ℬ)))
      = wprob φ (leftEvent (familyEvent 𝒜)) * wprob φ (rightEvent (familyEvent ℬ)) :=
  reimer_wprob_doubled_split φ hφ1 (familyEvent 𝒜) (familyEvent ℬ)
















theorem familyEvent_boxDoubled_subset_inter (𝒜 ℬ : Finset (Finset α)) :
    familyEvent (boxDoubled 𝒜 ℬ)
      ⊆ leftEvent (familyEvent 𝒜) ∩ rightEvent (familyEvent ℬ) := by
  intro ω hω
  rw [mem_familyEvent, mem_boxDoubled] at hω
  obtain ⟨S, hS, T, hT, _hd, hdbl⟩ := hω
  have hωeq : ω = supportCfg (dbl S T) := by
    rw [hdbl, supportCfg_cfgSupport]
  refine ⟨?_, ?_⟩
  · rw [mem_leftEvent, hωeq, leftCfg_supportCfg_dbl, mem_familyEvent, cfgSupport_supportCfg]
    exact hS
  · rw [mem_rightEvent, hωeq, rightCfg_supportCfg_dbl, mem_familyEvent, cfgSupport_supportCfg]
    exact hT















theorem wprob_familyEvent_boxDoubled_le (φ : (α ⊕ α) → Bool → ℝ)
    (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1) (𝒜 ℬ : Finset (Finset α)) :
    wprob φ (familyEvent (boxDoubled 𝒜 ℬ))
      ≤ wprob φ (leftEvent (familyEvent 𝒜)) * wprob φ (rightEvent (familyEvent ℬ)) := by
  have hAdep : DependsOn (leftEvent (familyEvent 𝒜)) {x : α ⊕ α | x.isLeft} :=
    dependsOn_leftEvent (familyEvent 𝒜)
  have hBdep : DependsOn (rightEvent (familyEvent ℬ)) {x : α ⊕ α | ¬ x.isLeft} :=
    (dependsOn_rightEvent (familyEvent ℬ)).mono (fun x hx => by
      simp only [rightBlock, Set.mem_setOf_eq] at hx
      simp only [Set.mem_setOf_eq]
      cases x with
      | inl a => simp only [Sum.isRight, Bool.false_eq_true] at hx
      | inr a => simp [Sum.isLeft])
  calc wprob φ (familyEvent (boxDoubled 𝒜 ℬ))
      ≤ wprob φ (leftEvent (familyEvent 𝒜) ∩ rightEvent (familyEvent ℬ)) :=
        wprob_mono hφ0 (familyEvent_boxDoubled_subset_inter 𝒜 ℬ)
    _ = wprob φ (leftEvent (familyEvent 𝒜)) * wprob φ (rightEvent (familyEvent ℬ)) :=
        wprob_inter_mul_of_split (fun x => x.isLeft) φ hφ1 hAdep hBdep












theorem fwt_doubleWeight_dbl (w : α → Bool → ℝ) (S T : Finset α) :
    fwt (doubleWeight w) (dbl S T) = fwt w S * fwt w T := by
  unfold fwt doubleWeight
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl; intro a _
    simp only [Sum.elim_inl]; congr 1; simp only [mem_dbl_inl]
  · apply Finset.prod_congr rfl; intro a _
    simp only [Sum.elim_inr]; congr 1; simp only [mem_dbl_inr]





theorem fmarg_boxDoubled (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) :
    fmarg (doubleWeight w) (boxDoubled 𝒜 ℬ) = wdpairs w 𝒜 ℬ := by
  unfold fmarg boxDoubled wdpairs
  rw [Finset.sum_image (fun p hp q hq h => dbl_injOn _ hp hq h)]
  apply Finset.sum_congr rfl
  intro p _
  rw [fwt_doubleWeight_dbl]




theorem wprob_familyEvent_boxDoubled_eq_wdpairs (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) :
    wprob (doubleWeight w) (familyEvent (boxDoubled 𝒜 ℬ)) = wdpairs w 𝒜 ℬ := by
  rw [← fmarg_eq_wprob_familyEvent, fmarg_boxDoubled]





























theorem wdpairs_le_mul_of_doubled_independence {w : α → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b)
    (hw1 : ∀ x, w x false + w x true = 1) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
  have hbound := wprob_familyEvent_boxDoubled_le (doubleWeight w)
    (doubleWeight_nonneg hw0) (doubleWeight_prob hw1) 𝒜 ℬ
  rw [wprob_familyEvent_boxDoubled_eq_wdpairs,
    wprob_leftEvent w hw1 (familyEvent 𝒜), wprob_rightEvent w hw1 (familyEvent ℬ),
    ← fmarg_eq_wprob_familyEvent, ← fmarg_eq_wprob_familyEvent] at hbound
  exact hbound

end Weighted













































end StatMech
