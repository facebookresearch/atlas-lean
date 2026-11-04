/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

section
open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-!
# Atomless measures

Basic API for atomless measures: restriction to measurable sets and the
Sierpinski theorem that every intermediate measure value is attained.
-/

/-- **Atomless measure.** A measure $\mu$ on a measurable space is atomless when every
measurable set $s$ with $\mu(s) > 0$ contains a measurable subset $t \subseteq s$ with
$0 < \mu(t) < \mu(s)$. -/
def IsAtomless {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop :=
  ∀ s, MeasurableSet s → 0 < μ s → ∃ t, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s


/-- **Restriction of an atomless measure.** The restriction of an atomless measure to a
measurable set is atomless. -/
theorem isAtomless_restrict {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Z : Set α} (hZ : MeasurableSet Z) (hA : IsAtomless μ) :
    IsAtomless (μ.restrict Z) := by
  intro s hs hspos
  have hrestr : (μ.restrict Z) s = μ (s ∩ Z) := Measure.restrict_apply hs
  rw [hrestr] at hspos
  have hmeas : MeasurableSet (s ∩ Z) := hs.inter hZ
  obtain ⟨t, hts, htmeas, htpos, htlt⟩ := hA (s ∩ Z) hmeas hspos
  have htrestr : (μ.restrict Z) t = μ t := by
    rw [Measure.restrict_apply htmeas]
    have hsub : t ∩ Z = t :=
      Set.inter_eq_self_of_subset_left (fun x hx => (hts hx).2)
    rw [hsub]
  refine ⟨t, fun x hx => (hts hx).1, htmeas, htrestr.symm ▸ htpos, ?_⟩
  rw [htrestr, hrestr]
  exact htlt

/-- N2 (real form): atomless finite measure admits arbitrarily small positive-measure
subsets with a geometric bound. Consumed by Sierpinski (N3) and the bang-bang step. -/
private theorem isAtomless_exists_small_subset_real {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {s : Set α} (hs : MeasurableSet s) (hpos : 0 < μ s) (n : ℕ) :
    ∃ u, u ⊆ s ∧ MeasurableSet u ∧ 0 < μ u ∧ μ.real u ≤ μ.real s / 2 ^ n := by
  induction n with
  | zero =>
    refine ⟨s, le_rfl, hs, hpos, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨u, hus, humeas, hupos, hule⟩ := ih
    obtain ⟨t, htu, htmeas, htpos, htlt⟩ := hA u humeas hupos
    have ht_ne_top : μ t ≠ ⊤ := (measure_lt_top μ t).ne
    have hu_ne_top : μ u ≠ ⊤ := (measure_lt_top μ u).ne
    have hdiff_meas : MeasurableSet (u \ t) := humeas.diff htmeas
    have hunion : t ∪ (u \ t) = u := Set.union_sdiff_cancel htu
    have hdisj : Disjoint t (u \ t) := disjoint_sdiff_self_right
    have hdiff_eq : μ.real (u \ t) = μ.real u - μ.real t :=
      measureReal_sdiff htu htmeas
    have hdiff_pos : 0 < μ.real (u \ t) := by
      rw [hdiff_eq]
      have hlt : μ.real t < μ.real u :=
        (ENNReal.toReal_lt_toReal ht_ne_top hu_ne_top).mpr htlt
      linarith
    have hdiff_ne : μ (u \ t) ≠ 0 := by
      intro h0
      have hrz : μ.real (u \ t) = 0 := by
        rw [measureReal_def, h0, ENNReal.toReal_zero]
      linarith
    have hdiff_pos_enn : 0 < μ (u \ t) := bot_lt_iff_ne_bot.mpr hdiff_ne
    have hsum : μ.real t + μ.real (u \ t) = μ.real u := by
      have hun := measureReal_union hdisj hdiff_meas (μ := μ)
      rw [hunion] at hun
      linarith
    by_cases hcase : μ.real t ≤ μ.real u / 2
    · refine ⟨t, htu.trans hus, htmeas, htpos, ?_⟩
      calc μ.real t ≤ μ.real u / 2 := hcase
        _ ≤ (μ.real s / 2 ^ n) / 2 := by linarith [hule]
        _ = μ.real s / 2 ^ (n + 1) := by ring
    · have hlt : μ.real u / 2 < μ.real t := lt_of_not_ge hcase
      have hsmall : μ.real (u \ t) ≤ μ.real u / 2 := by linarith [hsum, hlt]
      refine ⟨u \ t, (Set.sdiff_subset.trans hus), hdiff_meas, hdiff_pos_enn, ?_⟩
      calc μ.real (u \ t) ≤ μ.real u / 2 := hsmall
        _ ≤ (μ.real s / 2 ^ n) / 2 := by linarith [hule]
        _ = μ.real s / 2 ^ (n + 1) := by ring

/-- N2 corollary: atomless finite measure admits positive-measure subsets below any
positive real bound. -/
private theorem isAtomless_exists_small_subset_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {s : Set α} (hs : MeasurableSet s) (hpos : 0 < μ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u, u ⊆ s ∧ MeasurableSet u ∧ 0 < μ u ∧ μ.real u ≤ ε := by
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt ((μ.real s + 1) / ε) (show (1:ℝ) < 2 by norm_num)
  have h2n : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hle : μ.real s / 2 ^ n ≤ ε := by
    have h1 := (div_lt_iff₀ hε).mp hn
    have h2 : μ.real s ≤ ε * 2 ^ n := by linarith
    exact (div_le_iff₀ h2n).mpr h2
  obtain ⟨u, hus, humeas, hupos, hu2n⟩ :=
    isAtomless_exists_small_subset_real hA hs hpos n
  exact ⟨u, hus, humeas, hupos, le_trans hu2n hle⟩

/-- Admissible measures for the Sierpinski greedy step: measures of measurable pieces of
`s \ u` that fit in the remaining budget. -/
private def sierpinskiAdm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (t : ENNReal) (u : Set α) : Set ENNReal :=
  { m | ∃ v, MeasurableSet v ∧ v ⊆ s \ u ∧ μ u + μ v ≤ t ∧ μ v = m }

/-- Capacity: supremum of admissible measures for the Sierpinski greedy step. -/
private noncomputable def sierpinskiCap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (t : ENNReal) (u : Set α) : ENNReal :=
  sSup (sierpinskiAdm μ s t u)

/-- The Sierpinski capacity is bounded by the target. -/
private theorem sierpinskiCap_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {t : ENNReal} {u : Set α} :
    sierpinskiCap μ s t u ≤ t := by
  change sSup _ ≤ t
  apply sSup_le
  rintro m ⟨v, _, _, hle, rfl⟩
  exact le_add_self.trans hle

/-- Choice of a greedy piece attaining at least half the Sierpinski capacity. -/
private theorem sierpinskiChoice {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) {u : Set α} (hle : μ u ≤ t) :
    ∃ v, MeasurableSet v ∧ v ⊆ s \ u ∧ μ u + μ v ≤ t ∧
      sierpinskiCap μ s t u / 2 ≤ μ v := by
  by_cases hcap : sierpinskiCap μ s t u = 0
  · refine ⟨∅, MeasurableSet.empty, Set.empty_subset _, ?_, ?_⟩
    · simpa using hle
    · simp [hcap]
  · have hpos : 0 < sierpinskiCap μ s t u := bot_lt_iff_ne_bot.mpr hcap
    have ht_ne : t ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top μ s).ne ht
    have hcap_ne : sierpinskiCap μ s t u ≠ ⊤ :=
      ne_top_of_le_ne_top ht_ne sierpinskiCap_le
    have hhalf : sierpinskiCap μ s t u / 2 < sierpinskiCap μ s t u :=
      ENNReal.half_lt_self (ne_of_gt hpos) hcap_ne
    by_contra hcon
    have hall : ∀ v, MeasurableSet v → v ⊆ s \ u → μ u + μ v ≤ t →
        μ v ≤ sierpinskiCap μ s t u / 2 := by
      intro v hvmeas hvsub hle'
      by_contra hlt
      push Not at hlt
      exact hcon ⟨v, hvmeas, hvsub, hle', le_of_lt hlt⟩
    have hle2 : sierpinskiCap μ s t u ≤ sierpinskiCap μ s t u / 2 := by
      change sSup _ ≤ _
      apply sSup_le
      rintro m ⟨v, hvmeas, hvsub, hle', rfl⟩
      exact hall v hvmeas hvsub hle'
    exact (lt_irrefl _ (lt_of_le_of_lt hle2 hhalf)).elim

/-- State for the Sierpinski greedy recursion: a measurable subset of `s` within budget. -/
private structure SierpinskiState {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (t : ENNReal) where
  u : Set α
  hsub : u ⊆ s
  hmeas : MeasurableSet u
  hle : μ u ≤ t

/-- The greedy piece chosen at a Sierpinski state. -/
private noncomputable def sierpinskiPiece {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (U : SierpinskiState μ s t) : Set α :=
  Classical.choose (sierpinskiChoice ht U.hle)

/-- Specification of the greedy piece. -/
private theorem sierpinskiPiece_spec {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (U : SierpinskiState μ s t) :
    MeasurableSet (sierpinskiPiece ht U) ∧
      sierpinskiPiece ht U ⊆ s \ U.u ∧
      μ U.u + μ (sierpinskiPiece ht U) ≤ t ∧
      sierpinskiCap μ s t U.u / 2 ≤ μ (sierpinskiPiece ht U) :=
  Classical.choose_spec (sierpinskiChoice ht U.hle)

/-- One greedy Sierpinski step. -/
private noncomputable def sierpinskiNext {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (U : SierpinskiState μ s t) :
    SierpinskiState μ s t where
  u := U.u ∪ sierpinskiPiece ht U
  hsub := Set.union_subset U.hsub
    ((sierpinskiPiece_spec ht U).2.1.trans Set.sdiff_subset)
  hmeas := U.hmeas.union (sierpinskiPiece_spec ht U).1
  hle := by
    have hspec := sierpinskiPiece_spec ht U
    have hdisj : Disjoint U.u (sierpinskiPiece ht U) :=
      (Set.disjoint_left.mpr (fun x hx => (hspec.2.1 hx).2)).symm
    rw [measure_union hdisj hspec.1]
    exact hspec.2.2.1

/-- The greedy Sierpinski iteration. -/
private noncomputable def sierpinskiSeq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) : ℕ → SierpinskiState μ s t
  | 0 => ⟨∅, Set.empty_subset s, MeasurableSet.empty, by simp⟩
  | n + 1 => sierpinskiNext ht (sierpinskiSeq ht n)

/-- Successor states extend by the chosen piece. -/
private theorem sierpinskiSeq_succ {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (n : ℕ) :
    (sierpinskiSeq ht (n + 1)).u =
      (sierpinskiSeq ht n).u ∪ sierpinskiPiece ht (sierpinskiSeq ht n) :=
  rfl

/-- The Sierpinski iteration is monotone. -/
private theorem sierpinskiSeq_mono {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) :
    Monotone (fun n => ((sierpinskiSeq ht n).u)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sierpinskiSeq_succ ht n]
  exact Set.subset_union_left

/-- Measures add along the Sierpinski iteration. -/
private theorem sierpinskiSeq_measure_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (n : ℕ) :
    μ ((sierpinskiSeq ht (n + 1)).u) = μ ((sierpinskiSeq ht n).u) +
      μ (sierpinskiPiece ht (sierpinskiSeq ht n)) := by
  have hspec := sierpinskiPiece_spec ht (sierpinskiSeq ht n)
  have hdisj : Disjoint ((sierpinskiSeq ht n).u)
      (sierpinskiPiece ht (sierpinskiSeq ht n)) :=
    (Set.disjoint_left.mpr (fun x hx => (hspec.2.1 hx).2)).symm
  rw [sierpinskiSeq_succ ht n, measure_union hdisj hspec.1]

/-- **Sierpiński's theorem on atomless measures.** Let $\mu$ be a finite atomless measure. For
every measurable set $s$ and every $t \in [0, \infty]$ with $t \le \mu(s)$, there is a measurable
set $u \subseteq s$ with $\mu(u) = t$. -/
theorem isAtomless_exists_subset_measure_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {s : Set α} (hs : MeasurableSet s) {t : ENNReal} (ht : t ≤ μ s) :
    ∃ u, u ⊆ s ∧ MeasurableSet u ∧ μ u = t := by
  have hmono : Monotone (fun n => ((sierpinskiSeq ht n).u)) :=
    sierpinskiSeq_mono ht
  have hmono_a : Monotone (fun n => μ.real ((sierpinskiSeq ht n).u)) := by
    intro m n hmn
    exact ENNReal.toReal_mono ((measure_lt_top μ _).ne)
      (measure_mono (hmono hmn))
  have ht_ne : t ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top μ s).ne ht
  have hbdd : BddAbove
      (Set.range (fun n => μ.real ((sierpinskiSeq ht n).u))) := by
    refine ⟨t.toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact ENNReal.toReal_mono ht_ne (sierpinskiSeq ht n).hle
  obtain ⟨A, hA_lim⟩ :
      ∃ A, Tendsto (fun n => μ.real ((sierpinskiSeq ht n).u)) atTop (𝓝 A) :=
    ⟨_, tendsto_atTop_ciSup hmono_a hbdd⟩
  have hshift : Tendsto (fun n => μ.real ((sierpinskiSeq ht (n + 1)).u)) atTop
      (𝓝 A) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hA_lim
  have hdiff_lim : Tendsto
      (fun n => μ.real ((sierpinskiSeq ht (n + 1)).u) -
        μ.real ((sierpinskiSeq ht n).u)) atTop (𝓝 0) := by
    have h := hshift.sub hA_lim
    rwa [sub_self] at h
  have hpiece_eq : ∀ n, μ.real (sierpinskiPiece ht (sierpinskiSeq ht n))
      = μ.real ((sierpinskiSeq ht (n + 1)).u) -
        μ.real ((sierpinskiSeq ht n).u) := by
    intro n
    have hfin2 : μ ((sierpinskiSeq ht n).u) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    have hfin3 : μ (sierpinskiPiece ht (sierpinskiSeq ht n)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    simp only [measureReal_def, sierpinskiSeq_measure_add ht n,
      ENNReal.toReal_add hfin2 hfin3]
    ring
  have hpiece_lim : Tendsto
      (fun n => μ.real (sierpinskiPiece ht (sierpinskiSeq ht n))) atTop
      (𝓝 0) :=
    hdiff_lim.congr (fun n => (hpiece_eq n).symm)
  have hcap_le2 : ∀ n, (sierpinskiCap μ s t ((sierpinskiSeq ht n).u)).toReal
      ≤ 2 * μ.real (sierpinskiPiece ht (sierpinskiSeq ht n)) := by
    intro n
    have hspec := sierpinskiPiece_spec ht (sierpinskiSeq ht n)
    have hfin : μ (sierpinskiPiece ht (sierpinskiSeq ht n)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    have hcap_le : sierpinskiCap μ s t ((sierpinskiSeq ht n).u)
        ≤ μ (sierpinskiPiece ht (sierpinskiSeq ht n)) +
          μ (sierpinskiPiece ht (sierpinskiSeq ht n)) := by
      have hadd := ENNReal.add_halves
        (sierpinskiCap μ s t ((sierpinskiSeq ht n).u))
      rw [← hadd]
      exact add_le_add hspec.2.2.2 hspec.2.2.2
    have hsum_ne : μ (sierpinskiPiece ht (sierpinskiSeq ht n)) +
        μ (sierpinskiPiece ht (sierpinskiSeq ht n)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hfin, hfin⟩
    have hto := ENNReal.toReal_mono hsum_ne hcap_le
    rw [ENNReal.toReal_add hfin hfin] at hto
    rw [measureReal_def]
    linarith
  have hcap_lim : Tendsto
      (fun n => (sierpinskiCap μ s t ((sierpinskiSeq ht n).u)).toReal)
      atTop (𝓝 0) := by
    have h2lim : Tendsto
        (fun n => 2 * μ.real (sierpinskiPiece ht (sierpinskiSeq ht n)))
        atTop (𝓝 0) := by
      have h := Filter.Tendsto.const_mul 2 hpiece_lim
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      h2lim ?_ ?_
    · exact Eventually.of_forall (fun n => ENNReal.toReal_nonneg)
    · exact Eventually.of_forall hcap_le2
  have hwmeas : MeasurableSet (⋃ n, ((sierpinskiSeq ht n).u)) :=
    MeasurableSet.iUnion (fun n => (sierpinskiSeq ht n).hmeas)
  have hwsub : (⋃ n, ((sierpinskiSeq ht n).u)) ⊆ s :=
    Set.iUnion_subset (fun n => (sierpinskiSeq ht n).hsub)
  have hμw : μ (⋃ n, ((sierpinskiSeq ht n).u)) ≤ t := by
    rw [hmono.measure_iUnion]
    exact iSup_le (fun n => (sierpinskiSeq ht n).hle)
  by_cases hlt : μ (⋃ n, ((sierpinskiSeq ht n).u)) < t
  · have hgap_ne : t - μ (⋃ n, ((sierpinskiSeq ht n).u)) ≠ 0 := by
      intro h0
      have h1 := tsub_add_cancel_of_le hμw
      rw [h0, zero_add] at h1
      exact (ne_of_lt hlt) h1
    have hgap_pos : 0 < t - μ (⋃ n, ((sierpinskiSeq ht n).u)) :=
      bot_lt_iff_ne_bot.mpr hgap_ne
    have hgap_ne_top : t - μ (⋃ n, ((sierpinskiSeq ht n).u)) ≠ ⊤ :=
      ne_top_of_le_ne_top ht_ne tsub_le_self
    have hgap_real : 0
        < (t - μ (⋃ n, ((sierpinskiSeq ht n).u))).toReal :=
      ENNReal.toReal_pos_iff.mpr
        ⟨hgap_pos, lt_top_iff_ne_top.mpr hgap_ne_top⟩
    have hinter : μ (s ∩ (⋃ n, ((sierpinskiSeq ht n).u))) +
        μ (s \ (⋃ n, ((sierpinskiSeq ht n).u))) = μ s :=
      measure_inter_add_sdiff s hwmeas
    have hsdiff : s ∩ (⋃ n, ((sierpinskiSeq ht n).u)) =
        ⋃ n, ((sierpinskiSeq ht n).u) :=
      Set.inter_eq_self_of_subset_right hwsub
    rw [hsdiff] at hinter
    have hrem_ne : μ (s \ (⋃ n, ((sierpinskiSeq ht n).u))) ≠ 0 := by
      intro h0
      rw [h0, add_zero] at hinter
      have hltμ : μ (⋃ n, ((sierpinskiSeq ht n).u)) < μ s :=
        lt_of_lt_of_le hlt ht
      exact (ne_of_lt hltμ) hinter
    have hrem_pos : 0 < μ (s \ (⋃ n, ((sierpinskiSeq ht n).u))) :=
      bot_lt_iff_ne_bot.mpr hrem_ne
    have hrem_meas : MeasurableSet (s \ (⋃ n, ((sierpinskiSeq ht n).u))) :=
      hs.diff hwmeas
    obtain ⟨w, hwsub', hwmeas, hwpos, hwle⟩ :=
      isAtomless_exists_small_subset_le hA hrem_meas hrem_pos hgap_real
    rw [measureReal_def] at hwle
    have hwfin : μ w ≠ ⊤ := (measure_lt_top μ w).ne
    have hw_le_gap : μ w ≤ t - μ (⋃ n, ((sierpinskiSeq ht n).u)) :=
      (ENNReal.toReal_le_toReal hwfin hgap_ne_top).mp hwle
    have hadm : ∀ n, μ w ≤
        sierpinskiCap μ s t ((sierpinskiSeq ht n).u) := by
      intro n
      apply le_sSup
      refine ⟨w, hwmeas, ?_, ?_, rfl⟩
      · intro x hx
        have hx2 := hwsub' hx
        refine ⟨hx2.1, ?_⟩
        intro hxmem
        exact hx2.2 (Set.mem_iUnion_of_mem n hxmem)
      · have h1 : μ ((sierpinskiSeq ht n).u) ≤
            μ (⋃ n, ((sierpinskiSeq ht n).u)) :=
          measure_mono
            (Set.subset_iUnion (fun k => ((sierpinskiSeq ht k).u)) n)
        have h2 : μ (⋃ n, ((sierpinskiSeq ht n).u)) + μ w ≤ t :=
          add_le_of_le_tsub_left_of_le hμw hw_le_gap
        calc μ ((sierpinskiSeq ht n).u) + μ w
            ≤ μ (⋃ n, ((sierpinskiSeq ht n).u)) + μ w :=
              add_le_add_left h1 _
          _ ≤ t := h2
    have hw_real_pos : 0 < μ.real w := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos_iff.mpr
        ⟨hwpos, lt_top_iff_ne_top.mpr hwfin⟩
    have hle_all : ∀ n, μ.real w ≤
        (sierpinskiCap μ s t ((sierpinskiSeq ht n).u)).toReal := by
      intro n
      rw [measureReal_def]
      exact ENNReal.toReal_mono
        (ne_top_of_le_ne_top ht_ne sierpinskiCap_le) (hadm n)
    obtain ⟨n, hn⟩ := (hcap_lim.eventually_lt_const hw_real_pos).exists
    exact (lt_irrefl _ (lt_of_le_of_lt (hle_all n) hn)).elim
  · have heq : μ (⋃ n, ((sierpinskiSeq ht n).u)) = t :=
      le_antisymm hμw (not_lt.mp hlt)
    exact ⟨⋃ n, ((sierpinskiSeq ht n).u), hwsub, hwmeas, heq⟩

end MeasureTheory
end
