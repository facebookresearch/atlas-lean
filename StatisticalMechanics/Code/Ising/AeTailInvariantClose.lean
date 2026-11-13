/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Ising.TIChoquetClose
import Code.Lattice.HypercubicLattice
import Code.Foundations.Ergodicity
import Code.Foundations.CondDistribution

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}





@[reducible] noncomputable def aetc_finSig (F : Finset (Site d)) :
    MeasurableSpace (ConfigSpace (Site d)) :=
  ⨆ e ∈ F, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance



def aetc_Cring (d : ℕ) : Set (Set (ConfigSpace (Site d))) :=
  {A | ∃ F : Finset (Site d), MeasurableSet[aetc_finSig F] A}


theorem aetc_finSig_mono {F G : Finset (Site d)} (h : F ⊆ G) :
    aetc_finSig F ≤ aetc_finSig G :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩



theorem aetc_isSetRing_Cring : IsSetRing (aetc_Cring d) := by
  refine ⟨⟨∅, @MeasurableSet.empty _ (aetc_finSig ∅)⟩, ?_, ?_⟩
  · rintro A B ⟨F, hA⟩ ⟨G, hB⟩
    exact ⟨F ∪ G, (aetc_finSig_mono Finset.subset_union_left _ hA).union
      (aetc_finSig_mono Finset.subset_union_right _ hB)⟩
  · rintro A B ⟨F, hA⟩ ⟨G, hB⟩
    exact ⟨F ∪ G, (aetc_finSig_mono Finset.subset_union_left _ hA).diff
      (aetc_finSig_mono Finset.subset_union_right _ hB)⟩




theorem aetc_univ_mem_Cring : (Set.univ : Set (ConfigSpace (Site d))) ∈ aetc_Cring d :=
  ⟨∅, @MeasurableSet.univ _ (aetc_finSig ∅)⟩



theorem aetc_generateFrom_Cring :
    (inferInstance : MeasurableSpace (ConfigSpace (Site d))) = generateFrom (aetc_Cring d) := by
  apply le_antisymm
  · rw [measurableSpace_eq_iSup_comap]
    refine iSup_le fun e => fun A hA => measurableSet_generateFrom ⟨{e}, ?_⟩
    have : aetc_finSig ({e} : Finset (Site d))
        = MeasurableSpace.comap (ConfigSpace.eval e) inferInstance := by simp [aetc_finSig]
    rw [this]; exact hA
  · refine generateFrom_le ?_
    rintro A ⟨F, hF⟩
    exact (iSup₂_le fun e _ => (ConfigSpace.measurable_eval e).comap_le) A hF










theorem aetc_shift_measurable (g : Multiplicative (Site d)) (F : Finset (Site d)) :
    @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d))
      (aetc_finSig (F.image (fun e => g⁻¹ • e))) (aetc_finSig F) (shift g) := by
  refine Measurable.of_comap_le ?_
  rw [show aetc_finSig F
      = ⨆ e ∈ F, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance from rfl,
      MeasurableSpace.comap_iSup]
  refine iSup_le fun e => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun he => ?_
  rw [comap_comp]
  have heq : (ConfigSpace.eval e ∘ shift g) = ConfigSpace.eval (g⁻¹ • e) := by
    funext ω; simp [ConfigSpace.eval, shift]
  rw [heq]
  exact le_iSup₂_of_le (g⁻¹ • e) (Finset.mem_image_of_mem _ he) le_rfl



theorem aetc_finSig_le_outsideSigma (F : Finset (Site d)) (Λ : Set (Site d))
    (h : (↑F : Set (Site d)) ⊆ Λᶜ) : aetc_finSig F ≤ outsideSigma Λ :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩



theorem aetc_exists_shift_outside (hd : 1 ≤ d) (F : Finset (Site d)) (k : ℕ) :
    ∃ g : Multiplicative (Site d), (↑(F.image (fun e => g⁻¹ • e)) : Set (Site d)) ⊆ (box d k)ᶜ := by
  
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ e ∈ F, (e ⟨0, hd⟩).natAbs ≤ M :=
    ⟨(F.sup fun e => (e ⟨0, hd⟩).natAbs),
      fun e he => Finset.le_sup (f := fun e => (e ⟨0, hd⟩).natAbs) he⟩
  set g : Multiplicative (Site d) :=
    Multiplicative.ofAdd (fun i => if i = ⟨0, hd⟩ then (M + k + 1 : ℤ) else 0) with hg
  refine ⟨g, ?_⟩
  intro y hy
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
  obtain ⟨e, he, rfl⟩ := hy
  rw [Set.mem_compl_iff, box, Set.mem_setOf_eq, not_forall]
  refine ⟨⟨0, hd⟩, ?_⟩
  
  have hval : (g⁻¹ • e) ⟨0, hd⟩ = e ⟨0, hd⟩ - (M + k + 1 : ℤ) := by
    show (-(Multiplicative.toAdd g) + e) ⟨0, hd⟩ = _
    rw [hg]
    show -(if (⟨0, hd⟩ : Fin d) = ⟨0, hd⟩ then (M + k + 1 : ℤ) else 0) + e ⟨0, hd⟩ = _
    rw [if_pos rfl]; ring
  rw [not_le, hval]
  
  have h2 : e ⟨0, hd⟩ ≤ (M : ℤ) := by have := Int.le_natAbs (a := e ⟨0, hd⟩); have := hM e he; omega
  have h3 : e ⟨0, hd⟩ - (M + k + 1 : ℤ) ≤ -(k + 1 : ℤ) := by omega
  zify; rw [Int.abs_eq_natAbs] at *; omega






theorem aetc_symmDiff_preimage_invariant {μ : Measure (ConfigSpace (Site d))}
    (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    {s A : Set (ConfigSpace (Site d))} (hs : MeasurableSet s) (hA : MeasurableSet A)
    (g : Multiplicative (Site d)) (hinv : shift g ⁻¹' s = s) :
    μ (s ∆ (shift g ⁻¹' A)) = μ (s ∆ A) := by
  have hpre : shift g ⁻¹' (s ∆ A) = s ∆ (shift g ⁻¹' A) := by
    rw [Set.preimage_symmDiff, hinv]
  calc μ (s ∆ (shift g ⁻¹' A)) = μ (shift g ⁻¹' (s ∆ A)) := by rw [hpre]
    _ = μ (s ∆ A) := (hμ g).measure_preimage (hs.symmDiff hA).nullMeasurableSet


















theorem aetc_invariant_approx (hd : 1 ≤ d) {μ : Measure (ConfigSpace (Site d))} [IsFiniteMeasure μ]
    (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s)
    (k : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set (ConfigSpace (Site d)), @MeasurableSet _ (outsideSigma (box d k)) A
      ∧ μ (s ∆ A) < ε := by
  
  have hcover : ∃ D : Set (Set (ConfigSpace (Site d))), D.Countable ∧ D ⊆ aetc_Cring d
      ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact aetc_univ_mem_Cring
    · simp
  obtain ⟨A₀, hA₀mem, hA₀⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing aetc_isSetRing_Cring hcover
      aetc_generateFrom_Cring hs hε
  obtain ⟨F₀, hF₀⟩ := hA₀mem
  have hA₀meas : MeasurableSet A₀ :=
    (aetc_finSig_le_outsideSigma F₀ (∅ : Set (Site d)) (by simp)).trans
      (outsideSigma_le _) A₀ hF₀
  
  obtain ⟨g, hgout⟩ := aetc_exists_shift_outside hd F₀ k
  refine ⟨shift g ⁻¹' A₀, ?_, ?_⟩
  · 
    have hsm : @MeasurableSet _ (aetc_finSig (F₀.image (fun e => g⁻¹ • e))) (shift g ⁻¹' A₀) :=
      aetc_shift_measurable g F₀ hF₀
    exact aetc_finSig_le_outsideSigma _ _ hgout _ hsm
  · 
    have hdist : μ (s ∆ (shift g ⁻¹' A₀)) = μ (s ∆ A₀) :=
      aetc_symmDiff_preimage_invariant hμ hs hA₀meas g (hinv g)
    rw [hdist, symmDiff_comm s A₀]
    exact hA₀










def AeApproxFarOut (μ : Measure (ConfigSpace (Site d))) (s : Set (ConfigSpace (Site d))) : Prop :=
  ∀ (k : ℕ) (ε : ℝ≥0∞), 0 < ε →
    ∃ A : Set (ConfigSpace (Site d)), @MeasurableSet _ (outsideSigma (box d k)) A ∧ μ (s ∆ A) < ε




















theorem aetc_outsideSigma_box_antitone {j n : ℕ} (h : j ≤ n) :
    outsideSigma (box d n) ≤ outsideSigma (box d j) :=
  iSup₂_mono' fun e he => ⟨e, fun hc => he (box_mono d h hc), le_rfl⟩





theorem aetc_isTailEvent_liminf (A : ℕ → Set (ConfigSpace (Site d)))
    (hA : ∀ n, @MeasurableSet _ (outsideSigma (box d n)) (A n)) :
    IsTailEvent (d := d) (⋃ N, ⋂ i, A (i + N)) := by
  intro j
  have hmono : Monotone (fun N => ⋂ i, A (i + N)) := by
    intro N M hNM
    refine Set.iInter_mono' fun i => ⟨i + (M - N), ?_⟩
    have hi : i + (M - N) + N = i + M := by omega
    rw [hi]
  have hrw : (⋃ N, ⋂ i, A (i + N)) = ⋃ N, ⋂ i, A (i + (N + j)) := by
    apply le_antisymm
    · exact Set.iUnion_mono' fun N => ⟨N, hmono (by omega)⟩
    · exact Set.iUnion_mono' fun N => ⟨N + j, le_rfl⟩
  rw [hrw]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun i => ?_
  exact aetc_outsideSigma_box_antitone (by omega) _ (hA (i + (N + j)))





theorem aetc_aeTail_of_approxFarOut {μ : Measure (ConfigSpace (Site d))} [IsFiniteMeasure μ]
    {s : Set (ConfigSpace (Site d))} (happ : AeApproxFarOut μ s) :
    ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[μ] s' := by
  
  have hpos : ∀ n : ℕ, (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ n := fun n =>
    ENNReal.pow_pos (by simp) n
  have hchoice : ∀ n : ℕ, ∃ A : Set (ConfigSpace (Site d)),
      @MeasurableSet _ (outsideSigma (box d n)) A ∧ μ (s ∆ A) < ((2 : ℝ≥0∞)⁻¹) ^ n :=
    fun n => happ n (((2 : ℝ≥0∞)⁻¹) ^ n) (hpos n)
  choose A hAmeas hAlt using hchoice
  
  refine ⟨⋃ N, ⋂ i, A (i + N), aetc_isTailEvent_liminf A hAmeas, ?_⟩
  
  have hsumm : ∑' n, μ (s ∆ A n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => (hAlt n).le)
    rw [ENNReal.tsum_geometric]; simp
  have hfin : ∀ᵐ x ∂μ, {n | x ∈ s ∆ A n}.Finite := ae_finite_setOf_mem hsumm
  
  rw [Filter.eventuallyEq_set]
  filter_upwards [hfin] with x hx
  have hev : ∀ᶠ n in atTop, (x ∈ s ↔ x ∈ A n) := by
    rw [eventually_atTop]
    obtain ⟨N, hN⟩ := hx.bddAbove
    refine ⟨N + 1, fun n hn => ?_⟩
    by_contra hne
    have hmem : n ∈ {n | x ∈ s ∆ A n} := by
      simp only [mem_setOf_eq, Set.mem_symmDiff]
      by_cases hxs : x ∈ s
      · exact Or.inl ⟨hxs, fun hA => hne (iff_of_true hxs hA)⟩
      · exact Or.inr ⟨by by_contra hA; exact hne (iff_of_false hxs hA), hxs⟩
    have := hN hmem; omega
  have hmemset : (x ∈ ⋃ N, ⋂ i, A (i + N)) ↔ ∀ᶠ n in atTop, x ∈ A n := by
    simp only [mem_iUnion, mem_iInter]
    rw [Filter.eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n hn => by have := hN (n - N); rwa [Nat.sub_add_cancel hn] at this⟩
    · rintro ⟨N, hN⟩; exact ⟨N, fun i => hN (i + N) (Nat.le_add_left N i)⟩
  rw [hmemset]
  constructor
  · intro hxs; exact hev.mono fun n hn => hn.mp hxs
  · intro hxA; obtain ⟨n, hn1, hn2⟩ := (hev.and hxA).exists; exact hn1.mpr hn2











theorem aetc_haeTail (hd : 1 ≤ d) {μ : Measure (ConfigSpace (Site d))} [IsFiniteMeasure μ]
    (hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    ∀ s : Set (ConfigSpace (Site d)), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) →
        ∃ s' : Set (ConfigSpace (Site d)), IsTailEvent (d := d) s' ∧ s =ᵐ[μ] s' := by
  intro s hs hinv
  exact aetc_aeTail_of_approxFarOut (fun k ε hε => aetc_invariant_approx hd hμ hs hinv k hε)











theorem aetc_plusState_isErgodic (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  tic_plusState_isErgodic_of_aeTailInvariant β h hβ hh hti hdlr (aetc_haeTail hd hti)



theorem aetc_minusState_isErgodic (β h : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))) :=
  tic_minusState_isErgodic_of_aeTailInvariant β h hβ hh hti hdlr (aetc_haeTail hd hti)








theorem aetc_dirac_const_isTranslationInvariant :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site d))) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  rw [Measure.map_dirac' (measurable_shift g)]
  have hfix : (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) (fun _ => true)
      = (fun _ => true) := by funext e; simp [shift]
  rw [hfix]




theorem aetc_haeTail_nonvacuous :
    ∃ s' : Set (ConfigSpace (Site 1)), IsTailEvent (d := 1) s'
      ∧ (Set.univ : Set (ConfigSpace (Site 1)))
          =ᵐ[(Measure.dirac (fun _ => true) : Measure (ConfigSpace (Site 1)))] s' :=
  aetc_haeTail (d := 1) le_rfl aetc_dirac_const_isTranslationInvariant Set.univ
    MeasurableSet.univ (fun _ => Set.preimage_univ)

end Ising

end StatMech
