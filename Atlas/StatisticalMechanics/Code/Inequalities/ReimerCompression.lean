/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Code.Inequalities.BK
import Code.Inequalities.DisjointOccurrence
import Mathlib.Combinatorics.SetFamily.Compression.Down

open MeasureTheory Finset
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {E : Type*}









def cfgSupport [Fintype E] [DecidableEq E] (ω : ConfigSpace E) : Finset E :=
  Finset.univ.filter (fun i => ω i = true)


def supportCfg [DecidableEq E] (s : Finset E) : ConfigSpace E := fun i => decide (i ∈ s)

@[simp] lemma mem_cfgSupport [Fintype E] [DecidableEq E] (ω : ConfigSpace E) (i : E) :
    i ∈ cfgSupport ω ↔ ω i = true := by
  simp only [cfgSupport, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] lemma supportCfg_apply [DecidableEq E] (s : Finset E) (i : E) :
    supportCfg s i = decide (i ∈ s) := rfl

lemma supportCfg_cfgSupport [Fintype E] [DecidableEq E] (ω : ConfigSpace E) :
    supportCfg (cfgSupport ω) = ω := by
  funext i
  simp only [supportCfg_apply, mem_cfgSupport]
  cases ω i <;> simp

lemma cfgSupport_supportCfg [Fintype E] [DecidableEq E] (s : Finset E) :
    cfgSupport (supportCfg s) = s := by
  ext i
  simp only [mem_cfgSupport, supportCfg_apply, decide_eq_true_eq]


def cfgEquivFinset [Fintype E] [DecidableEq E] : ConfigSpace E ≃ Finset E where
  toFun := cfgSupport
  invFun := supportCfg
  left_inv := supportCfg_cfgSupport
  right_inv := cfgSupport_supportCfg

@[simp] lemma cfgEquivFinset_apply [Fintype E] [DecidableEq E] (ω : ConfigSpace E) :
    cfgEquivFinset ω = cfgSupport ω := rfl

@[simp] lemma cfgEquivFinset_symm_apply [Fintype E] [DecidableEq E] (s : Finset E) :
    cfgEquivFinset.symm s = supportCfg s := rfl





















noncomputable def downCompress [Fintype E] [DecidableEq E] (i : E)
    (𝒜 : Finset (ConfigSpace E)) : Finset (ConfigSpace E) :=
  (Down.compression i (𝒜.image cfgSupport)).image supportCfg




theorem downCompress_card [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E)) :
    (downCompress i 𝒜).card = 𝒜.card := by
  unfold downCompress
  rw [Finset.card_image_of_injOn, Down.card_compression, Finset.card_image_of_injOn]
  · intro x _ y _ h
    have := congrArg supportCfg h
    rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
  · intro x _ y _ h
    have := congrArg cfgSupport h
    rwa [cfgSupport_supportCfg, cfgSupport_supportCfg] at this



lemma mem_downCompress [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E))
    (ω : ConfigSpace E) :
    ω ∈ downCompress i 𝒜 ↔ cfgSupport ω ∈ Down.compression i (𝒜.image cfgSupport) := by
  unfold downCompress
  rw [Finset.mem_image]
  refine ⟨?_, fun h => ⟨cfgSupport ω, h, supportCfg_cfgSupport ω⟩⟩
  rintro ⟨s, hs, rfl⟩
  rwa [cfgSupport_supportCfg]


def lowerCoord [DecidableEq E] (i : E) (ω : ConfigSpace E) : ConfigSpace E :=
  Function.update ω i false

@[simp] lemma lowerCoord_self [DecidableEq E] (i : E) (ω : ConfigSpace E) :
    lowerCoord i ω i = false := by simp [lowerCoord]

lemma lowerCoord_of_ne [DecidableEq E] {i j : E} (h : j ≠ i) (ω : ConfigSpace E) :
    lowerCoord i ω j = ω j := by simp [lowerCoord, Function.update_of_ne h]

lemma cfgSupport_lowerCoord [Fintype E] [DecidableEq E] (i : E) (ω : ConfigSpace E) :
    cfgSupport (lowerCoord i ω) = (cfgSupport ω).erase i := by
  ext j
  simp only [mem_cfgSupport, lowerCoord, Function.update, Finset.mem_erase]
  by_cases h : j = i
  · subst h; simp
  · simp [h]



theorem downCompress_isDownAt [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E))
    {ω : ConfigSpace E} (hω : ω ∈ downCompress i 𝒜) :
    lowerCoord i ω ∈ downCompress i 𝒜 := by
  rw [mem_downCompress] at hω ⊢
  rw [cfgSupport_lowerCoord]
  exact Down.erase_mem_compression_of_mem_compression hω


theorem downCompress_idem [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E)) :
    downCompress i (downCompress i 𝒜) = downCompress i 𝒜 := by
  unfold downCompress
  have h1 : ((Down.compression i (𝒜.image cfgSupport)).image supportCfg).image cfgSupport
      = Down.compression i (𝒜.image cfgSupport) := by
    rw [Finset.image_image]
    have : (cfgSupport ∘ supportCfg) = (id : Finset E → Finset E) := by
      funext s; simp [cfgSupport_supportCfg]
    rw [this, Finset.image_id]
  rw [h1, Down.compression_idem]










lemma occursOn_univ_iff (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    OccursOn A Set.univ ω ↔ ω ∈ A := by
  refine ⟨OccursOn.mem_self, fun hω ω' hω' => ?_⟩
  have : ω' = ω := by funext i; exact hω' i (Set.mem_univ i)
  rwa [this]


lemma occursOn_empty_iff (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    OccursOn A (∅ : Set E) ω ↔ ∀ ω', ω' ∈ A :=
  ⟨fun h ω' => h ω' (by intro e he; simp at he), fun h ω' _ => h ω'⟩


lemma fin1_coord_cases (K : Set (Fin 1)) : K = ∅ ∨ K = Set.univ := by
  by_cases h : (0 : Fin 1) ∈ K
  · right; ext i; fin_cases i; simp [h]
  · left; ext i; fin_cases i; simp [h]




lemma mem_disjointOccurrence_fin1 (A B : Set (ConfigSpace (Fin 1))) (ω : ConfigSpace (Fin 1)) :
    ω ∈ disjointOccurrence A B ↔
      ((∀ ω', ω' ∈ A) ∧ ω ∈ B) ∨ (ω ∈ A ∧ (∀ ω', ω' ∈ B)) := by
  rw [mem_disjointOccurrence]
  refine ⟨?_, ?_⟩
  · rintro ⟨K, L, hKL, hA, hB⟩
    rcases fin1_coord_cases K with hK | hK <;> rcases fin1_coord_cases L with hL | hL <;>
      subst hK <;> subst hL
    · exact Or.inl ⟨(occursOn_empty_iff A ω).mp hA, (occursOn_empty_iff B ω).mp hB ω⟩
    · exact Or.inl ⟨(occursOn_empty_iff A ω).mp hA, (occursOn_univ_iff B ω).mp hB⟩
    · exact Or.inr ⟨(occursOn_univ_iff A ω).mp hA, (occursOn_empty_iff B ω).mp hB⟩
    · exact absurd hKL (by simp)
  · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
    · exact ⟨∅, Set.univ, by simp, (occursOn_empty_iff A ω).mpr hA, (occursOn_univ_iff B ω).mpr hB⟩
    · exact ⟨Set.univ, ∅, by simp, (occursOn_univ_iff A ω).mpr hA, (occursOn_empty_iff B ω).mpr hB⟩



lemma forall_mem_fin1 (A : Set (ConfigSpace (Fin 1))) :
    (∀ ω', ω' ∈ A) ↔ ((fun _ => false) ∈ A ∧ (fun _ => true) ∈ A) := by
  refine ⟨fun h => ⟨h _, h _⟩, ?_⟩
  rintro ⟨h0, h1⟩ ω'
  rcases (show ω' = (fun _ => false) ∨ ω' = (fun _ => true) from by
    by_cases h : ω' 0 = true
    · right; funext i; fin_cases i; exact h
    · left; funext i; fin_cases i; simpa using h) with h | h
  · rwa [h]
  · rwa [h]


lemma pweight_fin1 (φ : Fin 1 → Bool → ℝ) (ω : ConfigSpace (Fin 1)) :
    pweight φ ω = φ 0 (ω 0) := by simp only [pweight, Fin.prod_univ_one]


lemma wprob_fin1 (φ : Fin 1 → Bool → ℝ) (S : Set (ConfigSpace (Fin 1))) :
    wprob φ S = S.indicator (fun _ => (1 : ℝ)) (fun _ => false) * φ 0 false
              + S.indicator (fun _ => (1 : ℝ)) (fun _ => true) * φ 0 true := by
  simp only [wprob]
  rw [show (Finset.univ : Finset (ConfigSpace (Fin 1)))
        = {(fun _ => false), (fun _ => true)} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, pweight_fin1, pweight_fin1]




theorem reimer_wprob_one (φ : Fin 1 → Bool → ℝ)
    (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin 1))) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  have hq0 : 0 ≤ φ 0 false := hφ0 0 false
  have hp0 : 0 ≤ φ 0 true := hφ0 0 true
  have hqp : φ 0 false + φ 0 true = 1 := hφ1 0
  rw [wprob_fin1, wprob_fin1, wprob_fin1]
  simp only [Set.indicator_apply, mem_disjointOccurrence_fin1, forall_mem_fin1]
  by_cases hAF : (fun _ => false) ∈ A <;> by_cases hAT : (fun _ => true) ∈ A <;>
    by_cases hBF : (fun _ => false) ∈ B <;> by_cases hBT : (fun _ => true) ∈ B <;>
    simp only [hAF, hAT, hBF, hBT, and_true, and_false, or_false, or_true,
      if_true, if_false, and_self] <;>
    nlinarith [hq0, hp0, hqp]












def DependsOn (A : Set (ConfigSpace E)) (S : Set E) : Prop :=
  ∀ ω ω', agreeOn S ω ω' → (ω ∈ A ↔ ω' ∈ A)


lemma DependsOn.mono {A : Set (ConfigSpace E)} {S S' : Set E} (h : DependsOn A S)
    (hSS' : S ⊆ S') : DependsOn A S' :=
  fun ω ω' hag => h ω ω' (agreeOn_mono hSS' hag)


lemma DependsOn.occursOn_iff {A : Set (ConfigSpace E)} {S : Set E} (h : DependsOn A S)
    (ω : ConfigSpace E) : OccursOn A S ω ↔ ω ∈ A :=
  ⟨OccursOn.mem_self, fun hω ω' hω' => (h ω ω' hω').mp hω⟩



theorem disjointOccurrence_eq_inter_of_dependsOn {A B : Set (ConfigSpace E)} {S T : Set E}
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    disjointOccurrence A B = A ∩ B := by
  apply Set.Subset.antisymm (disjointOccurrence_subset_inter A B)
  rintro ω ⟨hAω, hBω⟩
  exact ⟨S, T, hST, (hA.occursOn_iff ω).mpr hAω, (hB.occursOn_iff ω).mpr hBω⟩







lemma pweight_split [Fintype E] (P : E → Prop) [DecidablePred P] (φ : E → Bool → ℝ)
    (a : {x // P x} → Bool) (b : {x // ¬ P x} → Bool) :
    pweight φ ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      = (∏ i : {x // P x}, φ i (a i)) * (∏ i : {x // ¬ P x}, φ i (b i)) := by
  simp only [pweight]
  rw [← Fintype.prod_subtype_mul_prod_subtype P
        (fun i => φ i ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b) i))]
  congr 1
  · exact Finset.prod_congr rfl
      (fun i _ => by rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2])
  · exact Finset.prod_congr rfl
      (fun i _ => by rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2])


lemma wprob_reindex [Fintype E] [DecidableEq E] (P : E → Prop) [DecidablePred P]
    (φ : E → Bool → ℝ) (S : Set (ConfigSpace E)) :
    wprob φ S = ∑ a : {x // P x} → Bool, ∑ b : {x // ¬ P x} → Bool,
      S.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
        * pweight φ ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) := by
  simp only [wprob]
  rw [← (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm.sum_comp
    (fun ω => S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω)]
  rw [Fintype.sum_prod_type]



lemma indicator_indep_compl {A : Set (ConfigSpace E)} (P : E → Prop) [DecidablePred P]
    (hA : DependsOn A {x | P x}) (a : {x // P x} → Bool) (b b' : {x // ¬ P x} → Bool) :
    A.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      = A.indicator (fun _ => (1 : ℝ))
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b')) := by
  have hag : agreeOn {x | P x}
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b')) := by
    intro e he; simp only [Set.mem_setOf_eq] at he
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
      dif_pos he, dif_pos he]
  have := hA _ _ hag
  by_cases h : ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (this.mpr hc))]



lemma indicator_indep_pred {B : Set (ConfigSpace E)} (P : E → Prop) [DecidablePred P]
    (hB : DependsOn B {x | ¬ P x}) (a a' : {x // P x} → Bool) (b : {x // ¬ P x} → Bool) :
    B.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      = B.indicator (fun _ => (1 : ℝ))
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a', b)) := by
  have hag : agreeOn {x | ¬ P x}
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a', b)) := by
    intro e he; simp only [Set.mem_setOf_eq] at he
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
      dif_neg he, dif_neg he]
  have := hB _ _ hag
  by_cases h : ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) ∈ B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (this.mpr hc))]


lemma sum_prod_eq_one {S : Type*} [Fintype S] [DecidableEq S] (ψ : S → Bool → ℝ)
    (h : ∀ s, ψ s false + ψ s true = 1) :
    (∑ a : S → Bool, ∏ s, ψ s (a s)) = 1 := by
  rw [← Fintype.prod_sum (fun s => ψ s)]; simp only [Fintype.sum_bool]
  exact Finset.prod_eq_one (fun s _ => by rw [add_comm]; exact h s)

set_option maxHeartbeats 1000000 in



theorem wprob_inter_mul_of_split [Fintype E] [DecidableEq E] (P : E → Prop) [DecidablePred P]
    (φ : E → Bool → ℝ) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : DependsOn A {x | P x}) (hB : DependsOn B {x | ¬ P x}) :
    wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
  classical
  set e := Equiv.piEquivPiSubtypeProd P (fun _ : E => Bool) with he
  set IA : ({x // P x} → Bool) → ({x // ¬ P x} → Bool) → ℝ :=
    fun a b => A.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) with hIA
  set IB : ({x // P x} → Bool) → ({x // ¬ P x} → Bool) → ℝ :=
    fun a b => B.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) with hIB
  set WP : ({x // P x} → Bool) → ℝ := fun a => ∏ i : {x // P x}, φ i (a i) with hWP
  set WQ : ({x // ¬ P x} → Bool) → ℝ := fun b => ∏ i : {x // ¬ P x}, φ i (b i) with hWQ
  let b0 : {x // ¬ P x} → Bool := fun _ => false
  let a0 : {x // P x} → Bool := fun _ => false
  have hIAb : ∀ a b, IA a b = IA a b0 := fun a b => indicator_indep_compl P hA a b b0
  have hIBa : ∀ a b, IB a b = IB a0 b := fun a b => indicator_indep_pred P hB a a0 b
  have hsumWQ : (∑ b : {x // ¬ P x} → Bool, WQ b) = 1 :=
    sum_prod_eq_one (S := {x // ¬ P x}) (fun i b => φ (i : E) b) (fun i => hφ1 (i : E))
  have hsumWP : (∑ a : {x // P x} → Bool, WP a) = 1 :=
    sum_prod_eq_one (S := {x // P x}) (fun i b => φ (i : E) b) (fun i => hφ1 (i : E))
  have hABind : ∀ a b, (A ∩ B).indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) = IA a b * IB a b := by
    intro a b
    by_cases hAm : e.symm (a, b) ∈ A <;> by_cases hBm : e.symm (a, b) ∈ B <;>
      simp [hIA, hIB, Set.indicator, Set.mem_inter_iff, hAm, hBm]
  have hwAB : wprob φ (A ∩ B) = (∑ a, IA a b0 * WP a) * (∑ b, IB a0 b * WQ b) := by
    rw [wprob_reindex P φ (A ∩ B), Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hABind a b, pweight_split, hIAb a b, hIBa a b]; ring
  have hwA : wprob φ A = ∑ a, IA a b0 * WP a := by
    rw [wprob_reindex P φ A]
    apply Finset.sum_congr rfl; intro a _
    calc (∑ b : {x // ¬ P x} → Bool,
            A.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) * pweight φ (e.symm (a, b)))
        = ∑ b : {x // ¬ P x} → Bool, IA a b0 * WP a * WQ b := by
          apply Finset.sum_congr rfl; intro b _
          rw [pweight_split,
            show A.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) = IA a b from rfl, hIAb a b]; ring
      _ = IA a b0 * WP a := by rw [← Finset.mul_sum, hsumWQ, mul_one]
  have hwB : wprob φ B = ∑ b, IB a0 b * WQ b := by
    rw [wprob_reindex P φ B, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    calc (∑ a : {x // P x} → Bool,
            B.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) * pweight φ (e.symm (a, b)))
        = ∑ a : {x // P x} → Bool, IB a0 b * WQ b * WP a := by
          apply Finset.sum_congr rfl; intro a _
          rw [pweight_split,
            show B.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) = IB a b from rfl, hIBa a b]; ring
      _ = IB a0 b * WQ b := by rw [← Finset.mul_sum, hsumWP, mul_one]
  rw [hwAB, hwA, hwB]






theorem reimer_wprob_of_disjoint_support [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} {S T : Set E}
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    wprob φ (disjointOccurrence A B) = wprob φ A * wprob φ B := by
  classical
  have hAP : DependsOn A {x | x ∈ S} := hA
  have hTcompl : T ⊆ {x | x ∉ S} := by
    intro x hx; simp only [Set.mem_setOf_eq]
    exact fun hxS => (Set.disjoint_left.mp hST) hxS hx
  have hBP : DependsOn B {x | ¬ (x ∈ S)} := hB.mono hTcompl
  rw [disjointOccurrence_eq_inter_of_dependsOn hA hB hST]
  exact wprob_inter_mul_of_split (fun x => x ∈ S) φ hφ1 hAP hBP



































end StatMech
