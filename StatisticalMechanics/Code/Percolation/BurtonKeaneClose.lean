/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Foundations.ProductMeasure
import Code.FK.Ergodicity
import Code.Percolation.BurtonKeaneMergeGeom
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.BurtonKeaneUniqueness
import Code.Lattice.BoxSurfaceVolume

open MeasureTheory Measure Set MeasurableSpace ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation







variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]




theorem bkc_infinitePi_disjoint_cylinder
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {s t : Finset ι} {S : Set (Π i : s, X i)} {T : Set (Π i : t, X i)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint s t) :
    Measure.infinitePi μ (cylinder s S ∩ cylinder t T)
      = Measure.infinitePi μ (cylinder s S) * Measure.infinitePi μ (cylinder t T) := by
  have hind : iIndepFun (fun i (ω : Π i, X i) => ω i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (𝓧 := X) (X := fun _ x => x) (fun i => measurable_id)
  simpa only [cylinder] using
    (hind.indepFun_finset s t hd (fun e => measurable_pi_apply e)).measure_inter_preimage_eq_mul
      S T hS hT

omit [∀ i, MeasurableSpace (X i)] in


theorem bkc_projP_preimage_cylinder (p : ι → Prop) (s : Finset (Subtype p))
    (S : Set (Π j : s, X ((j : Subtype p) : ι))) :
    (fun (ω : Π i, X i) (j' : Subtype p) => ω (j' : ι)) ⁻¹' (cylinder s S)
      = cylinder (s.map (Function.Embedding.subtype p))
          ((fun (y : Π i : s.map (Function.Embedding.subtype p), X (i : ι)) (j : s) =>
              y ⟨((j : Subtype p) : ι),
                by rw [Finset.mem_map]; exact ⟨(j : Subtype p), j.2, rfl⟩⟩) ⁻¹' S) := by
  ext ω; simp only [Set.mem_preimage, mem_cylinder]; rfl





theorem bkc_infinitePi_map_piEquivPiSubtypeProd
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    (Measure.infinitePi μ).map (MeasurableEquiv.piEquivPiSubtypeProd X p)
      = (Measure.infinitePi (fun j : Subtype p => μ (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => μ (j : ι))) := by
  classical
  symm
  refine Measure.prod_eq_generateFrom generateFrom_measurableCylinders
    generateFrom_measurableCylinders isPiSystem_measurableCylinders isPiSystem_measurableCylinders
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, fun _ => by simp,
      by rw [iUnion_const]⟩
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, fun _ => by simp,
      by rw [iUnion_const]⟩
    ?_
  intro A hA B hB
  rw [mem_measurableCylinders] at hA hB
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hA
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := hB
  rw [Measure.map_apply (MeasurableEquiv.piEquivPiSubtypeProd X p).measurable
    ((MeasurableSet.cylinder _ hS₁).prod (MeasurableSet.cylinder _ hS₂))]
  have hpre : (MeasurableEquiv.piEquivPiSubtypeProd X p) ⁻¹' (cylinder s₁ S₁ ×ˢ cylinder s₂ S₂)
      = ((fun (ω : Π i, X i) (j : Subtype p) => ω (j : ι)) ⁻¹' (cylinder s₁ S₁)) ∩
        ((fun (ω : Π i, X i) (j : {i // ¬ p i}) => ω (j : ι)) ⁻¹' (cylinder s₂ S₂)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    rfl
  rw [hpre, bkc_projP_preimage_cylinder p s₁ S₁,
    bkc_projP_preimage_cylinder (fun i => ¬ p i) s₂ S₂]
  rw [bkc_infinitePi_disjoint_cylinder μ (?_) (?_) (?_)]
  · congr 1
    · rw [← bkc_projP_preimage_cylinder p s₁ S₁,
        ← Measure.map_apply (by fun_prop) (MeasurableSet.cylinder _ hS₁),
        Measure.map_infinitePi_infinitePi_of_inj (f := (Subtype.val : Subtype p → ι))
          Subtype.val_injective]
    · rw [← bkc_projP_preimage_cylinder (fun i => ¬ p i) s₂ S₂,
        ← Measure.map_apply (by fun_prop) (MeasurableSet.cylinder _ hS₂),
        Measure.map_infinitePi_infinitePi_of_inj (f := (Subtype.val : {i // ¬ p i} → ι))
          Subtype.val_injective]
  · exact (by fun_prop : Measurable _) hS₁
  · exact (by fun_prop : Measurable _) hS₂
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_map] at ha1 ha2
    obtain ⟨j1, _, rfl⟩ := ha1
    obtain ⟨j2, _, hj2⟩ := ha2
    simp only [Function.Embedding.subtype, Function.Embedding.coeFn_mk] at hj2
    exact j2.2 (hj2 ▸ j1.2)




theorem bkc_pi_absolutelyContinuous_fin :
    ∀ (n : ℕ) {Y : Fin n → Type*} [∀ k, MeasurableSpace (Y k)]
      (ν μ : (k : Fin n) → Measure (Y k))
      [∀ k, IsProbabilityMeasure (μ k)] [∀ k, IsProbabilityMeasure (ν k)],
      (∀ k, ν k ≪ μ k) → Measure.pi ν ≪ Measure.pi μ := by
  intro n
  induction n with
  | zero =>
    intro Y _ ν μ _ _ _
    have heq : Measure.pi ν = Measure.pi μ := by
      ext s _
      rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
      · simp
      · have hsu : s = Set.univ := by
          ext y; simp only [Set.mem_univ, iff_true]; rwa [Subsingleton.elim y x]
        rw [hsu, measure_univ, measure_univ]
    rw [heq]
  | succ n ih =>
    intro Y _ ν μ _ _ h
    set e := MeasurableEquiv.piFinSuccAbove Y 0 with he
    have hμ : Measure.pi μ
        = ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))).map e.symm := by
      rw [← (measurePreserving_piFinSuccAbove μ 0).map_eq, ← he,
        Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    have hν : Measure.pi ν
        = ((ν 0).prod (Measure.pi fun j => ν (Fin.succAbove 0 j))).map e.symm := by
      rw [← (measurePreserving_piFinSuccAbove ν 0).map_eq, ← he,
        Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    rw [hμ, hν]
    exact (Measure.AbsolutelyContinuous.prod (h 0)
      (ih (fun j => ν (Fin.succAbove 0 j)) (fun j => μ (Fin.succAbove 0 j))
        (fun j => h _))).map e.symm.measurable




theorem bkc_pi_absolutelyContinuous_fintype {κ : Type*} [Fintype κ] {Y : κ → Type*}
    [∀ k, MeasurableSpace (Y k)] (ν μ : (k : κ) → Measure (Y k))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, IsProbabilityMeasure (ν k)]
    (h : ∀ k, ν k ≪ μ k) : Measure.pi ν ≪ Measure.pi μ := by
  classical
  set ee := Fintype.equivFin κ with hee
  have hmpμ := measurePreserving_piCongrLeft (fun k => μ k) ee.symm
  have hmpν := measurePreserving_piCongrLeft (fun k => ν k) ee.symm
  have hfin := bkc_pi_absolutelyContinuous_fin (Fintype.card κ)
    (fun n => ν (ee.symm n)) (fun n => μ (ee.symm n)) (fun n => h _)
  rw [← hmpμ.map_eq, ← hmpν.map_eq]
  exact hfin.map (MeasurableEquiv.piCongrLeft Y ee.symm).measurable








theorem bkc_infinitePi_ac_of_finite_diff
    (ν μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)]
    (F : Finset ι) (hdiff : ∀ i ∉ F, ν i = μ i) (hac : ∀ i, ν i ≪ μ i) :
    Measure.infinitePi ν ≪ Measure.infinitePi μ := by
  classical
  set p : ι → Prop := fun i => i ∈ F with hp
  set e := MeasurableEquiv.piEquivPiSubtypeProd X p with he
  have hsμ := bkc_infinitePi_map_piEquivPiSubtypeProd μ p
  have hsν := bkc_infinitePi_map_piEquivPiSubtypeProd ν p
  have heqrest : (fun j : {i // ¬ p i} => ν (j : ι)) = (fun j : {i // ¬ p i} => μ (j : ι)) := by
    funext j; exact hdiff (j : ι) j.2
  have hprodac : ((Measure.infinitePi (fun j : Subtype p => ν (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => ν (j : ι))))
      ≪ ((Measure.infinitePi (fun j : Subtype p => μ (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => μ (j : ι)))) := by
    rw [heqrest]
    refine Measure.AbsolutelyContinuous.prod ?_ (Measure.absolutelyContinuous_refl _)
    have : Fintype (Subtype p) := Fintype.ofFinite _
    rw [Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi]
    exact bkc_pi_absolutelyContinuous_fintype _ _ (fun j => hac _)
  calc Measure.infinitePi ν
      = ((Measure.infinitePi ν).map e).map e.symm := by
        rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
          Measure.map_id]
    _ ≪ ((Measure.infinitePi μ).map e).map e.symm := by
        rw [hsμ, hsν]; exact hprodac.map e.symm.measurable
    _ = Measure.infinitePi μ := by
        rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
          Measure.map_id]








variable {d : ℕ}


instance bkc_isProbMeasure_factor (p : ℝ≥0) (hp : p ≤ 1) (e : Sym2 (Site d))
    (F : Finset (Sym2 (Site d))) :
    IsProbabilityMeasure ((bernoulliMeasure p hp).map (fun b => if e ∈ F then true else b)) :=
  isProbabilityMeasure_map (by
    by_cases h : e ∈ F <;> simp only [h, if_true, if_false]
    · exact measurable_const.aemeasurable
    · exact measurable_id.aemeasurable)





theorem bkc_factor_ac (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p) (e : Sym2 (Site d))
    (F : Finset (Sym2 (Site d))) :
    (bernoulliMeasure p hp).map (fun b => if e ∈ F then true else b) ≪ bernoulliMeasure p hp := by
  by_cases h : e ∈ F
  · simp only [h, if_true]
    refine Measure.AbsolutelyContinuous.mk ?_
    intro s hs hs0
    rw [Measure.map_apply (by fun_prop) hs]
    by_cases ht : (true : Bool) ∈ s
    · exfalso
      have hsub : ({true} : Set Bool) ⊆ s := by rintro x rfl; exact ht
      have h1 : bernoulliMeasure p hp {true} ≤ bernoulliMeasure p hp s := measure_mono hsub
      rw [bernoulliMeasure_apply_true, hs0] at h1
      have hpz : (p : ℝ≥0∞) = 0 := le_antisymm h1 (by positivity)
      simp only [ENNReal.coe_eq_zero] at hpz
      exact hp0.ne' hpz
    · have hpre : (fun _ : Bool => true) ⁻¹' s = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]; exact ht
      rw [hpre]; simp
  · simp only [h, if_false]
    have he : (fun b : Bool => b) = id := rfl
    rw [he, Measure.map_id]











theorem bkc_bernoulli_hasFiniteEnergyMerge (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p) :
    HasFiniteEnergyMerge (d := d) (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) := by
  intro F
  
  have hmap : (fun (ω : ConfigSpace (Sym2 (Site d))) => forceOpenFinset F ω)
      = (fun (ω : ConfigSpace (Sym2 (Site d))) e =>
          (fun b => if e ∈ F then true else b) (ω e)) := by
    funext ω e; unfold forceOpenFinset; by_cases h : e ∈ F <;> simp [h]
  have hpush : (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).map
        (fun ω => forceOpenFinset F ω)
      = Measure.infinitePi
          (fun e => (bernoulliMeasure p hp).map (fun b => if e ∈ F then true else b)) := by
    rw [hmap]
    unfold bernoulliProductMeasure
    refine Measure.infinitePi_map_pi (μ := fun _ : Sym2 (Site d) => bernoulliMeasure p hp)
      (f := fun e (b : Bool) => if e ∈ F then true else b) (fun e => ?_)
    by_cases h : e ∈ F <;> simp only [h, if_true, if_false]
    · exact measurable_const
    · exact measurable_id
  rw [hpush]
  
  have hμ : bernoulliProductMeasure (E := Sym2 (Site d)) p hp
      = Measure.infinitePi (fun _ : Sym2 (Site d) => bernoulliMeasure p hp) := rfl
  rw [hμ]
  refine bkc_infinitePi_ac_of_finite_diff _ _ F (fun e he => ?_)
    (fun e => bkc_factor_ac p hp hp0 e F)
  
  simp only [he, if_false]
  have he2 : (fun b : Bool => b) = id := rfl
  rw [he2, Measure.map_id]





theorem bkc_smul_site_injective (a : Site d) :
    Function.Injective (fun g : Multiplicative (Site d) => g • a) := by
  intro g g' h
  apply Multiplicative.toAdd.injective
  funext i
  have := congrFun h i
  simp only [smul_site_apply] at this
  linarith





theorem bkc_smul_sym2_injective (a : Sym2 (Site d)) :
    Function.Injective (fun g : Multiplicative (Site d) => g • a) := by
  intro g g' h
  simp only at h
  induction a with
  | h x y =>
    rw [smul_sym2_mk, smul_sym2_mk, Sym2.eq_iff] at h
    apply Multiplicative.toAdd.injective
    funext i
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · have := congrFun h1 i; simp only [smul_site_apply] at this; linarith
    · have e1 := congrFun h1 i
      have e2 := congrFun h2 i
      simp only [smul_site_apply] at e1 e2
      linarith





theorem bkc_bernoulli_isErgodic (hd : 1 ≤ d) (p : ℝ≥0) (hp : p ≤ 1) :
    IsErgodic (G := Multiplicative (Site d))
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Infinite (Multiplicative (Site d)) := by unfold Site; infer_instance
  exact FK.bernoulli_isErgodic (E := Sym2 (Site d)) (G := Multiplicative (Site d))
    bkc_smul_sym2_injective p hp







theorem bkc_boxFinsetBK_card_pos (d n : ℕ) : 0 < (boxFinsetBK d n).card := by
  unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; positivity




theorem bkc_boundary_vol_ratio_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ) ≤ (2 * d : ℝ) / n := by
  have hboxcard : ((boxFinsetBK d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
    unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  set P : ℝ := (2 * (n : ℝ) + 1) ^ (d - 1) with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  have hbound : (boxSV_boundaryCard d n : ℝ) ≤ 2 * (d * P) := by
    have hbR : (boxSV_boundaryCard d n : ℝ)
        = (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d := by
      rw [boxSV_boundary_card d n hn]
      have hle : (2 * n - 1) ^ d ≤ (2 * n + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      rw [Nat.cast_sub hle]
      congr 1
      · push_cast; ring
      · have h1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
          have : (1 : ℕ) ≤ 2 * n := by omega
          rw [Nat.cast_sub this]; push_cast; ring
        rw [← h1]; push_cast; ring_nf
    rw [hbR]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsub := boxSV_pow_sub_pow_le (2 * (n : ℝ) + 1) (2 * (n : ℝ) - 1)
      (by linarith) (by linarith) d
    calc (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d
        ≤ ((2 * (n : ℝ) + 1) - (2 * (n : ℝ) - 1)) * (d * (2 * (n : ℝ) + 1) ^ (d - 1)) := hsub
      _ = 2 * (d * P) := by rw [hP]; ring
  have hpow : (2 * (n : ℝ) + 1) ^ d = (2 * (n : ℝ) + 1) * P := by
    rw [hP, ← pow_succ']; congr 1; omega
  rw [hboxcard, hpow, div_le_div_iff₀ (by positivity) (by exact_mod_cast hn)]
  calc (boxSV_boundaryCard d n : ℝ) * n ≤ 2 * (d * P) * n :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
    _ ≤ 2 * d * ((2 * (n : ℝ) + 1) * P) := by
        have hle : (n : ℝ) ≤ 2 * (n : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ n by positivity]
        nlinarith [hP0, mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * d * P)]




theorem bkc_boundary_vol_tendsto (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      atTop (𝓝 0) := by
  have hd0 : Tendsto (fun n : ℕ => (2 * d : ℝ) / n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 * d : ℝ))).div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hd0
  filter_upwards [eventually_ge_atTop 1] with n hn using bkc_boundary_vol_ratio_le d n hd hn
























theorem bkc_burton_keane_bernoulli (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      Tcount d ω n ≤ boxSV_boundaryCard d n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    hbound
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation

end StatMech
