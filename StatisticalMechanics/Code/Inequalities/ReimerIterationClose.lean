/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Code.Inequalities.ReimerButterflyProve3
import Code.Inequalities.ReimerCompressLib
import Code.Inequalities.ReimerButterflyProve2
import Code.Inequalities.ReimerCompression
import Code.Inequalities.ReimerEndpointProve
import Code.Inequalities.Reimer

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]












theorem rit_familyEvent_powerset_univ :
    familyEvent (Finset.univ.powerset : Finset (Finset (Fin 1)))
      = (Set.univ : Set (ConfigSpace (Fin 1))) := by
  ext ω
  simp only [mem_familyEvent, Set.mem_univ, iff_true, Finset.mem_powerset]
  exact Finset.subset_univ _



theorem rit_disjointOccurrence_univ_univ :
    disjointOccurrence (Set.univ : Set (ConfigSpace (Fin 1))) Set.univ = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true]
  exact ⟨∅, ∅, by simp, fun _ _ => trivial, fun _ _ => trivial⟩


noncomputable def rit_wHalf : Fin 1 → Bool → ℝ := fun _ _ => 1 / 2

theorem rit_wHalf_prob : ∀ x, rit_wHalf x false + rit_wHalf x true = 1 := by
  intro x; norm_num [rit_wHalf]

theorem rit_wHalf_nonneg : ∀ x b, 0 ≤ rit_wHalf x b := by
  intro x b; norm_num [rit_wHalf]


theorem rit_collapseLHS :
    wprob rit_wHalf (disjointOccurrence
        (familyEvent (Finset.univ.powerset : Finset (Finset (Fin 1))))
        (familyEvent (Finset.univ.powerset))) = 1 := by
  rw [rit_familyEvent_powerset_univ, rit_disjointOccurrence_univ_univ]
  simp only [wprob, Set.indicator_univ, one_mul]
  exact sum_pweight_eq_one rit_wHalf_prob


theorem rit_collapseRHS :
    wdpairs rit_wHalf (Finset.univ.powerset : Finset (Finset (Fin 1)))
        (Finset.univ.powerset) = 3 / 4 := by
  unfold wdpairs
  have hfwt : ∀ S : Finset (Fin 1), fwt rit_wHalf S = 1 / 2 := by
    intro S; simp only [fwt, rit_wHalf]; rw [Finset.prod_const]; simp
  rw [Finset.sum_congr rfl (fun p _ => by rw [hfwt p.1, hfwt p.2])]
  rw [Finset.sum_const]
  have hcard : ((Finset.univ.powerset ×ˢ Finset.univ.powerset :
        Finset (Finset (Fin 1) × Finset (Fin 1))).filter
        (fun p => Disjoint p.1 p.2)).card = 3 := by decide
  rw [hcard]; norm_num










theorem rit_collapseDomination_false :
    ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β) (w : β → Bool → ℝ),
      (∀ x b, 0 ≤ w x b) ∧ (∀ x, w x false + w x true = 1) ∧ (∀ x, w x false = w x true) ∧
      ∃ 𝒜 ℬ : Finset (Finset β),
        wdpairs w 𝒜 ℬ
          < wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) := by
  refine ⟨Fin 1, inferInstance, inferInstance, rit_wHalf, rit_wHalf_nonneg, rit_wHalf_prob,
    fun x => by norm_num [rit_wHalf], Finset.univ.powerset, Finset.univ.powerset, ?_⟩
  rw [rit_collapseLHS, rit_collapseRHS]; norm_num











omit [Fintype α] in

theorem rit_iterDownComp_append_singleton (cs : List α) (i : α) (𝒜 : Finset (Finset α)) :
    iterDownComp (cs ++ [i]) 𝒜 = iterDownComp cs (Down.compression i 𝒜) := by
  unfold iterDownComp; rw [List.foldr_append]; rfl

omit [Fintype α] in







theorem rit_exists_common_iterDownComp_isLowerSet (𝒜 ℬ : Finset (Finset α)) :
    ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
      ∧ IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α)) := by
  generalize hM : totalSize 𝒜 + totalSize ℬ = M
  induction M using Nat.strong_induction_on generalizing 𝒜 ℬ with
  | _ M ih =>
    by_cases hA : IsLowerSet (𝒜 : Set (Finset α))
    · by_cases hB : IsLowerSet (ℬ : Set (Finset α))
      · exact ⟨[], hA, hB⟩
      · rw [isLowerSet_iff_forall_downComp_eq_self, not_forall] at hB
        obtain ⟨i, hi⟩ := hB
        have hltB : totalSize (Down.compression i ℬ) < totalSize ℬ :=
          totalSize_downComp_lt i ℬ hi
        have hleA : totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜 := totalSize_downComp_le i 𝒜
        have hlt : totalSize (Down.compression i 𝒜) + totalSize (Down.compression i ℬ) < M := by
          omega
        obtain ⟨cs, hcsA, hcsB⟩ := ih _ hlt (Down.compression i 𝒜) (Down.compression i ℬ) rfl
        exact ⟨cs ++ [i],
          by rw [rit_iterDownComp_append_singleton]; exact hcsA,
          by rw [rit_iterDownComp_append_singleton]; exact hcsB⟩
    · rw [isLowerSet_iff_forall_downComp_eq_self, not_forall] at hA
      obtain ⟨i, hi⟩ := hA
      have hltA : totalSize (Down.compression i 𝒜) < totalSize 𝒜 := totalSize_downComp_lt i 𝒜 hi
      have hleB : totalSize (Down.compression i ℬ) ≤ totalSize ℬ := totalSize_downComp_le i ℬ
      have hlt : totalSize (Down.compression i 𝒜) + totalSize (Down.compression i ℬ) < M := by
        omega
      obtain ⟨cs, hcsA, hcsB⟩ := ih _ hlt (Down.compression i 𝒜) (Down.compression i ℬ) rfl
      exact ⟨cs ++ [i],
        by rw [rit_iterDownComp_append_singleton]; exact hcsA,
        by rw [rit_iterDownComp_append_singleton]; exact hcsB⟩









noncomputable def eventFamily (A : Set (ConfigSpace α)) : Finset (Finset α) := by
  classical
  exact (Finset.univ.filter (fun ω => ω ∈ A)).image cfgSupport



theorem rit_familyEvent_eventFamily (A : Set (ConfigSpace α)) :
    familyEvent (eventFamily A) = A := by
  classical
  ext ω
  simp only [mem_familyEvent, eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨ω', hω', heq⟩
    have hωeq : ω' = ω := by
      have := congrArg supportCfg heq
      rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
    rwa [hωeq] at hω'
  · intro hω; exact ⟨ω, hω, rfl⟩










theorem rit_fmarg_symm_iterDownComp {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (cs : List α) (𝒜 : Finset (Finset α)) :
    fmarg w (iterDownComp cs 𝒜) = fmarg w 𝒜 := by
  induction cs with
  | nil => rfl
  | cons i cs ih => rw [iterDownComp_cons, fmarg_symm_downComp hsym, ih]
















def rit_BoxDownCompMono (α : Type*) [Fintype α] [DecidableEq α] : Prop :=
  ∀ (w : α → Bool → ℝ), (∀ x b, 0 ≤ w x b) → (∀ x, w x false = w x true) →
    ∀ (i : α) (𝒜 ℬ : Finset (Finset α)),
      wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
        ≤ wprob w (disjointOccurrence (familyEvent (Down.compression i 𝒜))
            (familyEvent (Down.compression i ℬ)))




theorem rit_boxDownCompMono_eq_of_isLowerSet (w : α → Bool → ℝ) (i : α) {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      = wprob w (disjointOccurrence (familyEvent (Down.compression i 𝒜))
          (familyEvent (Down.compression i ℬ))) := by
  rw [downComp_eq_self_of_isLowerSet h𝒜, downComp_eq_self_of_isLowerSet hℬ]



theorem rit_boxDownCompMono_fin0 : rit_BoxDownCompMono (Fin 0) := by
  intro w _ _ i _ _; exact Fin.elim0 i



theorem rit_box_iterDownComp_mono (hmono : rit_BoxDownCompMono α) {w : α → Bool → ℝ}
    (hw0 : ∀ x b, 0 ≤ w x b) (hsym : ∀ x, w x false = w x true) (cs : List α)
    (𝒜 ℬ : Finset (Finset α)) :
    wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      ≤ wprob w (disjointOccurrence (familyEvent (iterDownComp cs 𝒜))
          (familyEvent (iterDownComp cs ℬ))) := by
  induction cs with
  | nil => simp
  | cons i cs ih =>
      rw [iterDownComp_cons, iterDownComp_cons]
      exact le_trans ih (hmono w hw0 hsym i (iterDownComp cs 𝒜) (iterDownComp cs ℬ))





















theorem rit_reimer_wprob_symm_of_boxMono (hmono : rit_BoxDownCompMono α) (w : α → Bool → ℝ)
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1)
    (hsym : ∀ x, w x false = w x true) (A B : Set (ConfigSpace α)) :
    wprob w (disjointOccurrence A B) ≤ wprob w A * wprob w B := by
  set 𝒜 := eventFamily A with h𝒜def
  set ℬ := eventFamily B with hℬdef
  have hA : A = familyEvent 𝒜 := (rit_familyEvent_eventFamily A).symm
  have hB : B = familyEvent ℬ := (rit_familyEvent_eventFamily B).symm
  obtain ⟨cs, hlA, hlB⟩ := rit_exists_common_iterDownComp_isLowerSet 𝒜 ℬ
  rw [hA, hB]
  calc wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      ≤ wprob w (disjointOccurrence (familyEvent (iterDownComp cs 𝒜))
          (familyEvent (iterDownComp cs ℬ))) := rit_box_iterDownComp_mono hmono hw0 hsym cs 𝒜 ℬ
    _ ≤ fmarg w (iterDownComp cs 𝒜) * fmarg w (iterDownComp cs ℬ) :=
        reimer_fmarg_of_isLowerSet w hw0 hw1 hlA hlB
    _ = fmarg w 𝒜 * fmarg w ℬ := by
        rw [rit_fmarg_symm_iterDownComp hsym, rit_fmarg_symm_iterDownComp hsym]
    _ = wprob w (familyEvent 𝒜) * wprob w (familyEvent ℬ) := by
        rw [fmarg_eq_wprob_familyEvent, fmarg_eq_wprob_familyEvent]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in






theorem rit_reimer_inequality_half_of_boxMono (hmono : rit_BoxDownCompMono α)
    (A B : Set (ConfigSpace α)) :
    (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real A
        * (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real B := by
  set φ : α → Bool → ℝ :=
    fun (_ : α) (b : Bool) => (bernoulliMeasure (1/2) (by norm_num)).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  have hf : (bernoulliMeasure (1/2 : ℝ≥0) (by norm_num)).real {false} = (1/2 : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal,
      NNReal.coe_sub (by norm_num), NNReal.coe_one]; norm_num
  have ht : (bernoulliMeasure (1/2 : ℝ≥0) (by norm_num)).real {true} = (1/2 : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]; norm_num
  have hφ1 : ∀ x, φ x false + φ x true = 1 := by
    intro x; simp only [hφ]; rw [hf, ht]; norm_num
  have hsym : ∀ x, φ x false = φ x true := by
    intro x; simp only [hφ]; rw [hf, ht]
  rw [bernoulli_real_eq_wprob (by norm_num) (disjointOccurrence A B),
    bernoulli_real_eq_wprob (by norm_num) A, bernoulli_real_eq_wprob (by norm_num) B]
  exact rit_reimer_wprob_symm_of_boxMono hmono φ hφ0 hφ1 hsym A B
































end StatMech
