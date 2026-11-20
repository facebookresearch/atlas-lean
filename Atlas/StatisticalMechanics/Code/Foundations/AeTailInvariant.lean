/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Foundations.CondDistribution
import Code.Foundations.Ergodicity

open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace StatMech

open ConfigSpace

variable {E H : Type*} [Countable E] [DecidableEq E]
  [Group H] [MulAction H E]





@[reducible] noncomputable def atiFinSig (F : Finset E) :
    MeasurableSpace (ConfigSpace E) :=
  ⨆ e ∈ F, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance

def atiCylinderRing (E : Type*) [Countable E] :
    Set (Set (ConfigSpace E)) :=
  {A | ∃ F : Finset E, MeasurableSet[atiFinSig F] A}

theorem atiFinSig_mono {F K : Finset E} (h : F ⊆ K) :
    atiFinSig F ≤ atiFinSig K :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩

theorem atiCylinderRing_isSetRing : IsSetRing (atiCylinderRing E) := by
  refine ⟨⟨∅, @MeasurableSet.empty _ (atiFinSig ∅)⟩, ?_, ?_⟩
  · rintro A B ⟨F, hA⟩ ⟨K, hB⟩
    exact ⟨F ∪ K,
      (atiFinSig_mono Finset.subset_union_left _ hA).union
        (atiFinSig_mono Finset.subset_union_right _ hB)⟩
  · rintro A B ⟨F, hA⟩ ⟨K, hB⟩
    exact ⟨F ∪ K,
      (atiFinSig_mono Finset.subset_union_left _ hA).diff
        (atiFinSig_mono Finset.subset_union_right _ hB)⟩

theorem atiCylinderRing_univ_mem :
    (Set.univ : Set (ConfigSpace E)) ∈ atiCylinderRing E :=
  ⟨∅, @MeasurableSet.univ _ (atiFinSig ∅)⟩

theorem atiCylinderRing_generateFrom :
    (inferInstance : MeasurableSpace (ConfigSpace E)) =
      generateFrom (atiCylinderRing E) := by
  apply le_antisymm
  · rw [measurableSpace_eq_iSup_comap]
    refine iSup_le fun e => fun A hA =>
      measurableSet_generateFrom ⟨{e}, ?_⟩
    have hsingle : atiFinSig ({e} : Finset E) =
        MeasurableSpace.comap (ConfigSpace.eval e) inferInstance := by
      simp [atiFinSig]
    rw [hsingle]
    exact hA
  · refine generateFrom_le ?_
    rintro A ⟨F, hF⟩
    exact (iSup₂_le fun e _ => (ConfigSpace.measurable_eval e).comap_le) A hF


def atiExteriorCylinderRing (window : Set E) :
    Set (Set (ConfigSpace E)) :=
  {A | ∃ (F : Finset E) (S : Set (ConfigSpace F)),
    (↑F : Set E) ⊆ windowᶜ ∧ A = MeasureTheory.cylinder F S}

theorem atiExteriorCylinderRing_isSetRing (window : Set E) :
    IsSetRing (atiExteriorCylinderRing (E := E) window) := by
  classical
  refine ⟨⟨∅, ∅, by simp, by simp⟩, ?_, ?_⟩
  · rintro A B ⟨F, S, hF, rfl⟩ ⟨K, T, hK, rfl⟩
    refine ⟨F ∪ K,
      (Finset.restrict₂ (π := fun _ : E => Bool)
          (s := F) (t := F ∪ K) Finset.subset_union_left :
          ConfigSpace ↥(F ∪ K) → ConfigSpace F) ⁻¹' S ∪
        (Finset.restrict₂ (π := fun _ : E => Bool)
          (s := K) (t := F ∪ K) Finset.subset_union_right :
          ConfigSpace ↥(F ∪ K) → ConfigSpace K) ⁻¹' T,
      ?_, MeasureTheory.union_cylinder (α := fun _ : E => Bool) F K S T⟩
    simpa using Set.union_subset hF hK
  · rintro A B ⟨F, S, hF, rfl⟩ ⟨K, T, hK, rfl⟩
    refine ⟨F ∪ K,
      (Finset.restrict₂ (π := fun _ : E => Bool)
          (s := F) (t := F ∪ K) Finset.subset_union_left :
          ConfigSpace ↥(F ∪ K) → ConfigSpace F) ⁻¹' S ∩
        ((Finset.restrict₂ (π := fun _ : E => Bool)
          (s := K) (t := F ∪ K) Finset.subset_union_right :
          ConfigSpace ↥(F ∪ K) → ConfigSpace K) ⁻¹' T)ᶜ,
      ?_, ?_⟩
    · simpa using Set.union_subset hF hK
    · rw [diff_eq,
        MeasureTheory.compl_cylinder (α := fun _ : E => Bool),
        MeasureTheory.inter_cylinder (α := fun _ : E => Bool)]
      rfl

theorem atiExteriorCylinderRing_univ_mem (window : Set E) :
    (Set.univ : Set (ConfigSpace E)) ∈
      atiExteriorCylinderRing (E := E) window :=
  ⟨∅, Set.univ, by simp, by simp⟩

theorem ati_restrict_measurable_finSig (F : Finset E) :
    @Measurable (ConfigSpace E) (ConfigSpace F)
      (atiFinSig F) inferInstance F.restrict := by
  refine (@measurable_pi_iff (ConfigSpace E) F (fun _ => Bool)
    (atiFinSig F) _ F.restrict).mpr ?_
  intro e
  have hle : MeasurableSpace.comap (ConfigSpace.eval e.1) inferInstance ≤
      atiFinSig F := le_iSup₂_of_le e.1 e.2 le_rfl
  exact measurable_iff_comap_le.mpr hle


theorem atiExteriorCylinderRing_generateFrom (window : Set E) :
    outsideSigma window =
      generateFrom (atiExteriorCylinderRing (E := E) window) := by
  apply le_antisymm
  · change (⨆ e ∈ windowᶜ,
      MeasurableSpace.comap (ConfigSpace.eval e) inferInstance) ≤ _
    refine iSup_le fun e => iSup_le fun he => fun A hA => ?_
    obtain ⟨B, hB, rfl⟩ := hA
    apply measurableSet_generateFrom
    let S : Set (ConfigSpace ({e} : Finset E)) :=
      {eta | eta ⟨e, Finset.mem_singleton_self e⟩ ∈ B}
    refine ⟨{e}, S, ?_, ?_⟩
    · simpa using he
    · ext omega
      simp [S, MeasureTheory.cylinder, ConfigSpace.eval]
  · refine generateFrom_le ?_
    rintro A ⟨F, S, hF, rfl⟩
    have hle : atiFinSig F ≤ outsideSigma window :=
      iSup₂_mono' fun e he => ⟨e, hF he, le_rfl⟩
    exact ((ati_restrict_measurable_finSig F).mono
      hle le_rfl)
      MeasurableSet.of_discrete



theorem ati_exterior_approx_cylinder
    (window : Set E) {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    {s : Set (ConfigSpace E)}
    (hs : @MeasurableSet _ (outsideSigma window) s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (F : Finset E) (S : Set (ConfigSpace F)),
      (↑F : Set E) ⊆ windowᶜ ∧
      mu (s ∆ MeasureTheory.cylinder F S) < ε := by
  let nu : @Measure (ConfigSpace E) (outsideSigma window) :=
    mu.trim (outsideSigma_le window)
  haveI : IsFiniteMeasure nu := by
    dsimp [nu]
    infer_instance
  have hcover : ∃ D : Set (Set (ConfigSpace E)), D.Countable ∧
      D ⊆ atiExteriorCylinderRing (E := E) window ∧ nu (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, by simp⟩
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst A
    exact atiExteriorCylinderRing_univ_mem window
  obtain ⟨A, hAmem, hclose⟩ :=
    @exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (ConfigSpace E) (outsideSigma window) nu inferInstance
      (atiExteriorCylinderRing (E := E) window)
      (atiExteriorCylinderRing_isSetRing window) hcover
      (atiExteriorCylinderRing_generateFrom window) s hs ε hε
  obtain ⟨F, S, hF, rfl⟩ := hAmem
  refine ⟨F, S, hF, ?_⟩
  have hcyl : @MeasurableSet _ (outsideSigma window)
      (MeasureTheory.cylinder F S) := by
    have hle : atiFinSig F ≤ outsideSigma window :=
      iSup₂_mono' fun e he => ⟨e, hF he, le_rfl⟩
    exact ((ati_restrict_measurable_finSig F).mono hle le_rfl)
      MeasurableSet.of_discrete
  rw [show nu (MeasureTheory.cylinder F S ∆ s) =
      mu (MeasureTheory.cylinder F S ∆ s) from
        trim_measurableSet_eq (outsideSigma_le window) (hcyl.symmDiff hs)] at hclose
  rwa [symmDiff_comm] at hclose

theorem atiShift_measurable (g : H) (F : Finset E) :
    @Measurable (ConfigSpace E) (ConfigSpace E)
      (atiFinSig (F.image (fun e => g⁻¹ • e))) (atiFinSig F) (shift g) := by
  refine Measurable.of_comap_le ?_
  rw [show atiFinSig F =
      ⨆ e ∈ F, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance from rfl,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun e => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun he => ?_
  rw [comap_comp]
  have heq : (ConfigSpace.eval e ∘ shift g) =
      ConfigSpace.eval (g⁻¹ • e) := by
    funext omega
    simp [ConfigSpace.eval, shift]
  rw [heq]
  exact le_iSup₂_of_le (g⁻¹ • e)
    (Finset.mem_image_of_mem _ he) le_rfl

theorem atiFinSig_le_outsideSigma (F : Finset E) (window : Set E)
    (h : (↑F : Set E) ⊆ windowᶜ) : atiFinSig F ≤ outsideSigma window :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩

theorem ati_symmDiff_preimage_invariant
    {mu : Measure (ConfigSpace E)}
    (hmu : IsTranslationInvariant (G := H) mu)
    {s A : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hA : MeasurableSet A) (g : H)
    (hinv : shift g ⁻¹' s = s) :
    mu (s ∆ (shift g ⁻¹' A)) = mu (s ∆ A) := by
  have hpre : shift g ⁻¹' (s ∆ A) = s ∆ (shift g ⁻¹' A) := by
    rw [Set.preimage_symmDiff, hinv]
  calc
    mu (s ∆ (shift g ⁻¹' A)) = mu (shift g ⁻¹' (s ∆ A)) := by rw [hpre]
    _ = mu (s ∆ A) :=
      (hmu g).measure_preimage (hs.symmDiff hA).nullMeasurableSet



theorem ati_invariant_approx
    (window : ℕ → Set E)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H,
      (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : H, shift g ⁻¹' s = s)
    (k : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set (ConfigSpace E),
      @MeasurableSet _ (outsideSigma (window k)) A ∧ mu (s ∆ A) < ε := by
  have hcover : ∃ D : Set (Set (ConfigSpace E)), D.Countable ∧
      D ⊆ atiCylinderRing E ∧ mu (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro A hA
      rw [Set.mem_singleton_iff] at hA
      subst A
      exact atiCylinderRing_univ_mem
    · simp
  obtain ⟨A₀, hA₀mem, hA₀close⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      atiCylinderRing_isSetRing hcover atiCylinderRing_generateFrom hs hε
  obtain ⟨F₀, hF₀⟩ := hA₀mem
  have hA₀meas : MeasurableSet A₀ :=
    (atiFinSig_le_outsideSigma F₀ (∅ : Set E) (by simp)).trans
      (outsideSigma_le _) A₀ hF₀
  obtain ⟨g, hg⟩ := hescape F₀ k
  refine ⟨shift g ⁻¹' A₀, ?_, ?_⟩
  · have hshift : @MeasurableSet _
        (atiFinSig (F₀.image (fun e => g⁻¹ • e))) (shift g ⁻¹' A₀) :=
      atiShift_measurable g F₀ hF₀
    exact atiFinSig_le_outsideSigma _ _ hg _ hshift
  · rw [ati_symmDiff_preimage_invariant hmu hs hA₀meas g (hinv g),
      symmDiff_comm s A₀]
    exact hA₀close




theorem ati_sequenceInvariant_approx
    (window : ℕ → Set E) (g : ℕ → H)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ n : ℕ,
      (↑(F.image (fun e => (g n)⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ n : ℕ, shift (g n) ⁻¹' s = s)
    (k : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set (ConfigSpace E),
      @MeasurableSet _ (outsideSigma (window k)) A ∧ mu (s ∆ A) < ε := by
  have hcover : ∃ D : Set (Set (ConfigSpace E)), D.Countable ∧
      D ⊆ atiCylinderRing E ∧ mu (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, by simp⟩
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst A
    exact atiCylinderRing_univ_mem
  obtain ⟨A₀, hA₀mem, hA₀close⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      atiCylinderRing_isSetRing hcover atiCylinderRing_generateFrom hs hε
  obtain ⟨F₀, hF₀⟩ := hA₀mem
  have hA₀meas : MeasurableSet A₀ :=
    (atiFinSig_le_outsideSigma F₀ (∅ : Set E) (by simp)).trans
      (outsideSigma_le _) A₀ hF₀
  obtain ⟨n, hn⟩ := hescape F₀ k
  refine ⟨shift (g n) ⁻¹' A₀, ?_, ?_⟩
  · have hshift : @MeasurableSet _
        (atiFinSig (F₀.image (fun e => (g n)⁻¹ • e)))
        (shift (g n) ⁻¹' A₀) :=
      atiShift_measurable (g n) F₀ hF₀
    exact atiFinSig_le_outsideSigma _ _ hn _ hshift
  · rw [ati_symmDiff_preimage_invariant hmu hs hA₀meas (g n) (hinv n),
      symmDiff_comm s A₀]
    exact hA₀close

def AtiTailEvent (window : ℕ → Set E)
    (s : Set (ConfigSpace E)) : Prop :=
  ∀ n, @MeasurableSet _ (outsideSigma (window n)) s

theorem AtiTailEvent.measurableSet {window : ℕ → Set E}
    {s : Set (ConfigSpace E)} (hs : AtiTailEvent window s) :
    MeasurableSet s :=
  outsideSigma_le (window 0) s (hs 0)

theorem AtiTailEvent.compl {window : ℕ → Set E}
    {s : Set (ConfigSpace E)} (hs : AtiTailEvent window s) :
    AtiTailEvent window sᶜ :=
  fun n => (hs n).compl

def AtiApproxFarOut (window : ℕ → Set E)
    (mu : Measure (ConfigSpace E)) (s : Set (ConfigSpace E)) : Prop :=
  ∀ (k : ℕ) (ε : ℝ≥0∞), 0 < ε →
    ∃ A : Set (ConfigSpace E),
      @MeasurableSet _ (outsideSigma (window k)) A ∧ mu (s ∆ A) < ε

theorem atiOutsideSigma_antitone {window : ℕ → Set E}
    (hwindow : Monotone window) {j n : ℕ} (h : j ≤ n) :
    outsideSigma (window n) ≤ outsideSigma (window j) :=
  iSup₂_mono' fun e he => ⟨e, fun hc => he (hwindow h hc), le_rfl⟩

theorem atiTailEvent_liminf {window : ℕ → Set E}
    (hwindow : Monotone window)
    (A : ℕ → Set (ConfigSpace E))
    (hA : ∀ n, @MeasurableSet _ (outsideSigma (window n)) (A n)) :
    AtiTailEvent window (⋃ N, ⋂ i, A (i + N)) := by
  intro j
  have hmono : Monotone (fun N => ⋂ i, A (i + N)) := by
    intro N M hNM
    refine Set.iInter_mono' fun i => ⟨i + (M - N), ?_⟩
    have hi : i + (M - N) + N = i + M := by omega
    rw [hi]
  have hrw : (⋃ N, ⋂ i, A (i + N)) =
      ⋃ N, ⋂ i, A (i + (N + j)) := by
    apply le_antisymm
    · exact Set.iUnion_mono' fun N => ⟨N, hmono (by omega)⟩
    · exact Set.iUnion_mono' fun N => ⟨N + j, le_rfl⟩
  rw [hrw]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun i => ?_
  exact atiOutsideSigma_antitone hwindow (by omega) _ (hA (i + (N + j)))

theorem ati_aeTail_of_approxFarOut {window : ℕ → Set E}
    (hwindow : Monotone window)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    {s : Set (ConfigSpace E)} (happ : AtiApproxFarOut window mu s) :
    ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
  have hpos : ∀ n : ℕ, (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ n :=
    fun n => ENNReal.pow_pos (by simp) n
  have hchoice : ∀ n : ℕ, ∃ A : Set (ConfigSpace E),
      @MeasurableSet _ (outsideSigma (window n)) A ∧
        mu (s ∆ A) < ((2 : ℝ≥0∞)⁻¹) ^ n :=
    fun n => happ n (((2 : ℝ≥0∞)⁻¹) ^ n) (hpos n)
  choose A hAmeas hAlt using hchoice
  refine ⟨⋃ N, ⋂ i, A (i + N), atiTailEvent_liminf hwindow A hAmeas, ?_⟩
  have hsumm : ∑' n, mu (s ∆ A n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      (ENNReal.tsum_le_tsum fun n => (hAlt n).le)
    rw [ENNReal.tsum_geometric]
    simp
  have hfin : ∀ᵐ x ∂mu, {n | x ∈ s ∆ A n}.Finite :=
    ae_finite_setOf_mem hsumm
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
    have := hN hmem
    omega
  have hmemset : (x ∈ ⋃ N, ⋂ i, A (i + N)) ↔
      ∀ᶠ n in atTop, x ∈ A n := by
    simp only [mem_iUnion, mem_iInter]
    rw [Filter.eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n hn => by
        have := hN (n - N)
        rwa [Nat.sub_add_cancel hn] at this⟩
    · rintro ⟨N, hN⟩
      exact ⟨N, fun i => hN (i + N) (Nat.le_add_left N i)⟩
  rw [hmemset]
  constructor
  · intro hxs
    exact hev.mono fun n hn => hn.mp hxs
  · intro hxA
    obtain ⟨n, hn1, hn2⟩ := (hev.and hxA).exists
    exact hn1.mpr hn2



theorem ati_invariant_aeTail
    (window : ℕ → Set E) (hwindow : Monotone window)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H,
      (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu) :
    ∀ s : Set (ConfigSpace E), MeasurableSet s →
      (∀ g : H, shift g ⁻¹' s = s) →
      ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
  intro s hs hinv
  exact ati_aeTail_of_approxFarOut hwindow
    (fun k ε hε => ati_invariant_approx window hescape hmu hs hinv k hε)



theorem ati_sequenceInvariant_aeTail
    (window : ℕ → Set E) (hwindow : Monotone window)
    (g : ℕ → H)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ n : ℕ,
      (↑(F.image (fun e => (g n)⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu) :
    ∀ s : Set (ConfigSpace E), MeasurableSet s →
      (∀ n : ℕ, shift (g n) ⁻¹' s = s) →
      ∃ s' : Set (ConfigSpace E), AtiTailEvent window s' ∧ s =ᵐ[mu] s' := by
  intro s hs hinv
  exact ati_aeTail_of_approxFarOut hwindow
    (fun k ε hε =>
      ati_sequenceInvariant_approx window g hescape hmu hs hinv k hε)

end StatMech
