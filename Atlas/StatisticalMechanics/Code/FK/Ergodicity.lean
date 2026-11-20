/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Code.Foundations.ProductMeasure
import Code.Foundations.Ergodicity
import Code.Percolation.SubcriticalDecayFull

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal NNReal Pointwise symmDiff



set_option linter.unusedVariables false

namespace StatMech

namespace FK

open ConfigSpace

variable {E G : Type*} [Group G] [MulAction G E]






theorem bernoulli_iIndepFun (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepFun (fun (e : E) (ω : ConfigSpace E) => ω e)
      (bernoulliProductMeasure (E := E) p hp) := by
  unfold bernoulliProductMeasure
  exact iIndepFun_infinitePi (𝓧 := fun _ => Bool) (Ω := fun _ => Bool)
    (X := fun _ (b : Bool) => b) (fun _ => measurable_id)






theorem bernoulli_cylinder_factor (p : ℝ≥0) (hp : p ≤ 1) {s t : Finset E}
    {S : Set (Π i : s, Bool)} {T : Set (Π i : t, Bool)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint s t) :
    bernoulliProductMeasure (E := E) p hp (cylinder s S ∩ cylinder t T)
      = bernoulliProductMeasure (E := E) p hp (cylinder s S)
        * bernoulliProductMeasure (E := E) p hp (cylinder t T) := by
  have hfin : IndepFun (fun (ω : ConfigSpace E) (i : s) => ω i)
      (fun (ω : ConfigSpace E) (i : t) => ω i) (bernoulliProductMeasure (E := E) p hp) :=
    (bernoulli_iIndepFun p hp).indepFun_finset s t hd (fun e => measurable_pi_apply e)
  simpa only [cylinder] using hfin.measure_inter_preimage_eq_mul S T hS hT







theorem exists_disjoint_translate [Infinite G]
    (hfin : ∀ a b : E, {g : G | g • a = b}.Finite) (s t : Finset E) :
    ∃ g : G, Disjoint (s : Set E) (g⁻¹ • (t : Set E)) := by
  classical
  set bad : Set G := ⋃ a ∈ t, ⋃ b ∈ s, {h : G | h • a = b} with hbad
  have hbadfin : bad.Finite := by
    refine Set.Finite.biUnion t.finite_toSet (fun a _ => ?_)
    exact Set.Finite.biUnion s.finite_toSet (fun b _ => hfin a b)
  have hne : badᶜ.Nonempty := by
    have hbu : bad ≠ Set.univ := fun h => Set.infinite_univ (α := G) (h ▸ hbadfin)
    rwa [Set.nonempty_compl]
  obtain ⟨g0, hg0⟩ := hne
  refine ⟨g0⁻¹, ?_⟩
  rw [Set.disjoint_right]
  intro x hxt hxs
  rw [inv_inv, Set.mem_smul_set] at hxt
  obtain ⟨a, ha, rfl⟩ := hxt
  exact hg0 (Set.mem_biUnion ha (Set.mem_biUnion hxs rfl))



theorem finite_solution_of_injective
    (hinj : ∀ a : E, Function.Injective (fun g : G => g • a)) (a b : E) :
    {g : G | g • a = b}.Finite := by
  refine Set.Subsingleton.finite (fun g1 hg1 g2 hg2 => ?_)
  apply hinj a
  simp only [Set.mem_setOf_eq] at hg1 hg2
  simp only
  rw [hg1, hg2]





theorem shift_preimage_cylinder [DecidableEq E] (g : G) (t : Finset E)
    (T : Set (Π i : t, Bool)) :
    (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (cylinder t T)
      = cylinder (t.image (fun e => g⁻¹ • e))
          ((fun (x : Π i : (t.image (fun e => g⁻¹ • e)), Bool) (i : t) =>
              x ⟨g⁻¹ • (i : E), Finset.mem_image_of_mem _ i.2⟩) ⁻¹' T) := by
  ext ω
  simp only [cylinder, Set.mem_preimage]
  rfl







theorem bernoulli_mixing_cylinder [Countable E] [DecidableEq E] [Infinite G]
    (hfin : ∀ a b : E, {g : G | g • a = b}.Finite)
    (p : ℝ≥0) (hp : p ≤ 1) (s t : Finset E)
    (S : Set (Π i : s, Bool)) (T : Set (Π i : t, Bool))
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∃ g : G,
      bernoulliProductMeasure (E := E) p hp
          (cylinder s S ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' cylinder t T)
        = bernoulliProductMeasure (E := E) p hp (cylinder s S)
          * bernoulliProductMeasure (E := E) p hp (cylinder t T) := by
  obtain ⟨g, hg⟩ := exists_disjoint_translate hfin s t
  refine ⟨g, ?_⟩
  have hpre := shift_preimage_cylinder (E := E) (G := G) g t T
  rw [hpre]
  have hdisj : Disjoint s (t.image (fun e => g⁻¹ • e)) := by
    rw [← Finset.disjoint_coe]
    have hcoe : (↑(t.image (fun e => g⁻¹ • e)) : Set E) = g⁻¹ • (t : Set E) := by
      rw [Finset.coe_image]; rfl
    rw [hcoe]; exact hg
  rw [bernoulli_cylinder_factor p hp hS (hT.preimage (by fun_prop)) hdisj]
  have hti := Percolation.bernoulli_translationInvariant (E := E) (G := G) p hp
  have hmeaseq : bernoulliProductMeasure (E := E) p hp
        (cylinder (t.image (fun e => g⁻¹ • e))
          ((fun (x : Π i : (t.image (fun e => g⁻¹ • e)), Bool) (i : t) =>
              x ⟨g⁻¹ • (i : E), Finset.mem_image_of_mem _ i.2⟩) ⁻¹' T))
      = bernoulliProductMeasure (E := E) p hp (cylinder t T) := by
    rw [← hpre]
    exact hti.measure_preimage g (MeasurableSet.cylinder t hT)
  rw [hmeaseq]




private theorem measurableSet_of_mem_measurableCylinders
    {A : Set (ConfigSpace E)} (hA : A ∈ measurableCylinders (fun _ : E => Bool)) :
    MeasurableSet A :=
  MeasurableSet.of_mem_measurableCylinders hA



theorem isSetRing_measurableCylinders :
    IsSetRing (measurableCylinders (fun _ : E => Bool)) :=
  { empty_mem := empty_mem_measurableCylinders _
    union_mem := fun _ _ hs ht => union_mem_measurableCylinders hs ht
    diff_mem := fun _ _ hs ht => diff_mem_measurableCylinders hs ht }


theorem generateFrom_cylinders_eq :
    (inferInstance : MeasurableSpace (ConfigSpace E))
      = generateFrom (measurableCylinders (fun _ : E => Bool)) :=
  generateFrom_measurableCylinders.symm



theorem exists_cylinder_symmDiff_lt [Countable E] (p : ℝ≥0) (hp : p ≤ 1)
    {A : Set (ConfigSpace E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C ∈ measurableCylinders (fun _ : E => Bool),
      bernoulliProductMeasure (E := E) p hp (C ∆ A) < ε := by
  refine exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_measurableCylinders ?_ generateFrom_cylinders_eq hA hε
  refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
  · simpa using univ_mem_measurableCylinders (fun _ : E => Bool)
  · simp



private theorem cylinder_eq_of_mem
    {C : Set (ConfigSpace E)} (hC : C ∈ measurableCylinders (fun _ : E => Bool)) :
    ∃ (s : Finset E) (S : Set (Π i : s, Bool)), MeasurableSet S ∧ C = cylinder s S :=
  (mem_measurableCylinders C).mp hC






theorem bernoulli_ergodic [Countable E] [Infinite G]
    (hfin : ∀ a b : E, {g : G | g • a = b}.Finite)
    (p : ℝ≥0) (hp : p ≤ 1) {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    bernoulliProductMeasure (E := E) p hp s = 0 ∨
      bernoulliProductMeasure (E := E) p hp s
        = bernoulliProductMeasure (E := E) p hp Set.univ := by
  classical
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  
  
  have hμs_sq : μ.real s = (μ.real s) ^ 2 := by
    have key : ∀ ε : ℝ, 0 < ε → |μ.real s - (μ.real s) ^ 2| ≤ 4 * ε := by
      intro ε hε
      
      obtain ⟨C, hCmem, hCsd⟩ := exists_cylinder_symmDiff_lt (E := E) p hp hs
        (ε := ENNReal.ofReal ε) (by simpa using hε)
      obtain ⟨q, Q, hQ, rfl⟩ := cylinder_eq_of_mem hCmem
      
      obtain ⟨g, hmix⟩ := bernoulli_mixing_cylinder (E := E) (G := G) hfin p hp q q Q Q hQ hQ
      set C := cylinder (α := fun _ : E => Bool) q Q with hC
      set C' := (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C with hC'
      have hCmeas : MeasurableSet C := MeasurableSet.cylinder q hQ
      have hC'meas : MeasurableSet C' := hCmeas.preimage (measurable_shift g)
      
      have hCsd' : μ.real (C ∆ s) < ε := by
        have := (ENNReal.toReal_lt_toReal (measure_ne_top μ _)
          (by simp)).2 hCsd
        rwa [ENNReal.toReal_ofReal hε.le] at this
      
      have hC'sd : μ.real (C' ∆ s) < ε := by
        have hpre_eq : C' ∆ s
            = (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (C ∆ s) := by
          rw [hC', Set.preimage_symmDiff, hinv g]
        have hmp := Percolation.bernoulli_translationInvariant (E := E) (G := G) p hp g
        have : μ (C' ∆ s) = μ (C ∆ s) := by
          rw [hpre_eq]
          exact hmp.measure_preimage ((hCmeas.symmDiff hs).nullMeasurableSet)
        rw [Measure.real, this]
        rw [show (μ (C ∆ s)).toReal = μ.real (C ∆ s) from rfl]
        exact hCsd'
      
      have hCC' : μ.real (C ∩ C') = (μ.real C) ^ 2 := by
        have h1 : μ (C ∩ C') = μ C * μ C := by
          rw [hC', hC] at hmix ⊢
          exact hmix
        simp only [Measure.real, h1, ENNReal.toReal_mul]
        ring
      
      have hCs : |μ.real C - μ.real s| ≤ μ.real (C ∆ s) :=
        abs_measureReal_sub_le_measureReal_symmDiff hCmeas.nullMeasurableSet hs.nullMeasurableSet
      
      have hint : |μ.real s - μ.real (C ∩ C')| ≤ μ.real (C ∆ s) + μ.real (C' ∆ s) := by
        have hsub : s ∆ (C ∩ C') ⊆ (s ∆ C) ∪ (s ∆ C') := by
          intro x hx
          rcases hx with ⟨hxs, hxCC'⟩ | ⟨hxCC', hxs⟩
          · rw [Set.mem_inter_iff, not_and_or] at hxCC'
            rcases hxCC' with hxC | hxC'
            · exact Or.inl (Or.inl ⟨hxs, hxC⟩)
            · exact Or.inr (Or.inl ⟨hxs, hxC'⟩)
          · obtain ⟨hxC, hxC'⟩ := hxCC'
            exact Or.inl (Or.inr ⟨hxC, hxs⟩)
        calc |μ.real s - μ.real (C ∩ C')|
            ≤ μ.real (s ∆ (C ∩ C')) :=
              abs_measureReal_sub_le_measureReal_symmDiff hs.nullMeasurableSet
                (hCmeas.inter hC'meas).nullMeasurableSet
          _ ≤ μ.real ((s ∆ C) ∪ (s ∆ C')) :=
              measureReal_mono hsub (by finiteness)
          _ ≤ μ.real (s ∆ C) + μ.real (s ∆ C') := measureReal_union_le _ _
          _ = μ.real (C ∆ s) + μ.real (C' ∆ s) := by rw [symmDiff_comm, symmDiff_comm s C']
      
      have habs1 : |μ.real (C ∩ C') - (μ.real s) ^ 2| ≤ 2 * μ.real (C ∆ s) := by
        rw [hCC']
        have hCnn : 0 ≤ μ.real C := measureReal_nonneg
        have hsnn : 0 ≤ μ.real s := measureReal_nonneg
        have hle1 : μ.real C ≤ 1 := measureReal_le_one
        have hle1s : μ.real s ≤ 1 := measureReal_le_one
        calc |μ.real C ^ 2 - μ.real s ^ 2|
            = |μ.real C - μ.real s| * |μ.real C + μ.real s| := by
              rw [← abs_mul]; ring_nf
          _ ≤ |μ.real C - μ.real s| * 2 := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              rw [abs_of_nonneg (by positivity)]; linarith
          _ ≤ μ.real (C ∆ s) * 2 := by
              apply mul_le_mul_of_nonneg_right hCs (by norm_num)
          _ = 2 * μ.real (C ∆ s) := by ring
      
      have htri : |μ.real s - (μ.real s) ^ 2|
          ≤ |μ.real s - μ.real (C ∩ C')| + |μ.real (C ∩ C') - (μ.real s) ^ 2| := by
        have := abs_sub_le (μ.real s) (μ.real (C ∩ C')) ((μ.real s) ^ 2)
        linarith
      have hCsd'' : μ.real (C' ∆ s) ≥ 0 := measureReal_nonneg
      have hCsd0 : μ.real (C ∆ s) ≥ 0 := measureReal_nonneg
      calc |μ.real s - (μ.real s) ^ 2|
          ≤ |μ.real s - μ.real (C ∩ C')| + |μ.real (C ∩ C') - (μ.real s) ^ 2| := htri
        _ ≤ (μ.real (C ∆ s) + μ.real (C' ∆ s)) + 2 * μ.real (C ∆ s) := by
            apply add_le_add hint habs1
        _ ≤ (ε + ε) + 2 * ε := by
            apply add_le_add (add_le_add hCsd'.le hC'sd.le) (by linarith [hCsd'.le])
        _ ≤ 4 * ε := by linarith
    
    have hzero : |μ.real s - (μ.real s) ^ 2| = 0 := by
      by_contra hne
      have hpos : 0 < |μ.real s - (μ.real s) ^ 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      have := key (|μ.real s - (μ.real s) ^ 2| / 8) (by positivity)
      linarith
    have := abs_eq_zero.mp hzero
    linarith
  
  have hreal01 : μ.real s = 0 ∨ μ.real s = 1 := by
    have : μ.real s * (μ.real s - 1) = 0 := by nlinarith [hμs_sq]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hreal01 with h0 | h1
  · left
    have : μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
    rw [this, h0, ENNReal.ofReal_zero]
  · right
    rw [measure_univ]
    have : μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
    rw [this, h1, ENNReal.ofReal_one]





theorem bernoulli_isErgodic [Countable E] [Infinite G]
    (hinj : ∀ a : E, Function.Injective (fun g : G => g • a))
    (p : ℝ≥0) (hp : p ≤ 1) :
    ConfigSpace.IsErgodic (G := G) (bernoulliProductMeasure (E := E) p hp) := by
  refine ⟨Percolation.bernoulli_translationInvariant (E := E) (G := G) p hp, ?_⟩
  intro s hs hinv
  exact bernoulli_ergodic (E := E) (G := G)
    (fun a b => finite_solution_of_injective hinj a b) p hp hs hinv

end FK

end StatMech
