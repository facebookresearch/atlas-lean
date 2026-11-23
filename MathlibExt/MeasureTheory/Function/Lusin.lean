/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

open MeasureTheory Measure Topology
open scoped ENNReal

namespace MathlibExt.MeasureTheory.Function.Lusin

/-!
# Lusin's theorem
-/

/--
**Lusin's theorem.** Let $X$ be a locally compact Hausdorff topological space with its Borel
$\sigma$-algebra, and let $\mu$ be a finite measure on $X$ that is regular: finite on compact
sets, outer regular, and inner regular on open sets by compact sets. Let $Y$ be a
second-countable topological space with its Borel $\sigma$-algebra, and let $f : X \to Y$ be
measurable. Then for every real $\varepsilon > 0$ there is a compact set $K \subseteq X$ with
$\mu(X \setminus K) < \varepsilon$ such that $f$ is continuous on $K$.

Source: G. B. Folland, Real Analysis, 2nd ed., Lusin's theorem.
Proves `Wanted` entry `lusin`.
-/
theorem lusin {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [T2Space α] [LocallyCompactSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β] {μ : Measure α}
    [IsFiniteMeasure μ] [Regular μ] {f : α → β} (hf : Measurable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  -- A countable basis of `β`.
  set T : Set (Set β) := TopologicalSpace.countableBasis β with hT
  have hTcount : T.Countable := TopologicalSpace.countable_countableBasis β
  have hTbasis : TopologicalSpace.IsTopologicalBasis T :=
    TopologicalSpace.isBasis_countableBasis β
  have : Countable ↥T := hTcount.to_subtype
  -- Error budgets: `H` for the large compact, `Q` for each inner/outer approximation.
  have hH0 : (0 : ℝ) < ε / 2 := by linarith
  have hQ0 : (0 : ℝ) < ε / 4 := by linarith
  set H : ℝ≥0∞ := ENNReal.ofReal (ε / 2) with hH
  set Q : ℝ≥0∞ := ENNReal.ofReal (ε / 4) with hQ
  have hHne : H ≠ 0 := (ENNReal.ofReal_pos.mpr hH0).ne'
  have hQne : Q ≠ 0 := (ENNReal.ofReal_pos.mpr hQ0).ne'
  obtain ⟨e, hpos, hsum⟩ := ENNReal.exists_pos_sum_of_countable hQne ↥T
  set S : ℝ≥0∞ := ∑' b : ↥T, (e b : ℝ≥0∞) with hS
  have hsum' : S < Q := hsum
  -- Basic opens of `β` are open and have measurable, finite-measure preimages.
  have hopen : ∀ b : ↥T, IsOpen (b.val : Set β) := fun b =>
    TopologicalSpace.isOpen_of_mem_countableBasis b.property
  have hAmeas : ∀ b : ↥T, MeasurableSet (f ⁻¹' (b.val : Set β)) := fun b =>
    hf (hopen b).measurableSet
  have hAfin : ∀ b : ↥T, μ (f ⁻¹' (b.val : Set β)) ≠ ∞ := fun _ =>
    measure_ne_top μ _
  have hene : ∀ b : ↥T, ((e b : ℝ≥0∞) ≠ 0) := fun b => by
    exact_mod_cast (hpos b).ne'
  -- Outer approximations of the preimages.
  have outer : ∀ b : ↥T, ∃ U ⊇ f ⁻¹' (b.val : Set β), IsOpen U ∧
      μ (U \ f ⁻¹' (b.val : Set β)) < (e b : ℝ≥0∞) := by
    intro b
    obtain ⟨U, hAU, hUo, -, hU⟩ :=
      (hAmeas b).exists_isOpen_sdiff_lt (hAfin b) (hene b)
    exact ⟨U, hAU, hUo, hU⟩
  choose V hAV hVopen hVμ using outer
  -- Inner compact approximations of the preimages.
  have inner : ∀ b : ↥T, ∃ K ⊆ f ⁻¹' (b.val : Set β), IsCompact K ∧
      μ (f ⁻¹' (b.val : Set β) \ K) < (e b : ℝ≥0∞) :=
    fun b => (hAmeas b).exists_isCompact_sdiff_lt (hAfin b) (hene b)
  choose K hKA hKcomp hKμ using inner
  -- A large compact set.
  obtain ⟨K0, _, hK0comp, hK0μ⟩ :=
    MeasurableSet.exists_isCompact_sdiff_lt MeasurableSet.univ (measure_ne_top μ _) hHne
  have hK0c : μ K0ᶜ < H := by
    rw [Set.compl_eq_univ_sdiff]
    exact hK0μ
  -- The exceptional open set and its two halves.
  set W : Set α := ⋃ b : ↥T, (V b \ K b) with hW
  set W1 : Set α := ⋃ b : ↥T, (V b \ f ⁻¹' (b.val : Set β)) with hW1
  set W2 : Set α := ⋃ b : ↥T, (f ⁻¹' (b.val : Set β) \ K b) with hW2
  have hWopen : IsOpen W :=
    isOpen_iUnion fun b => (hVopen b).sdiff (hKcomp b).isClosed
  -- On `Wᶜ`, preimages of basic opens agree with the open approximations.
  have hkey : ∀ b : ↥T, f ⁻¹' (b.val : Set β) ∩ Wᶜ = V b ∩ Wᶜ := by
    intro b
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨hxf, hxW⟩
      exact ⟨hAV b hxf, hxW⟩
    · rintro ⟨hxV, hxW⟩
      by_cases hxa : x ∈ f ⁻¹' (b.val : Set β)
      · exact ⟨hxa, hxW⟩
      · exfalso
        apply hxW
        have hxK : x ∉ K b := fun hxK => hxa (hKA b hxK)
        exact Set.mem_iUnion.mpr ⟨b, hxV, hxK⟩
  have hcont : ContinuousOn f Wᶜ := by
    rw [hTbasis.continuousOn_iff]
    intro t ht
    exact ⟨V ⟨t, ht⟩, hVopen _, hkey ⟨t, ht⟩⟩
  -- Measure estimates.
  have hW1 : μ W1 ≤ S :=
    le_trans (measure_iUnion_le _)
      (ENNReal.tsum_le_tsum fun b => le_of_lt (hVμ b))
  have hW2 : μ W2 ≤ S :=
    le_trans (measure_iUnion_le _)
      (ENNReal.tsum_le_tsum fun b => le_of_lt (hKμ b))
  have hWsub : W ⊆ W1 ∪ W2 := by
    intro x hx
    obtain ⟨b, hxV, hxK⟩ := Set.mem_iUnion.mp hx
    by_cases hxa : x ∈ f ⁻¹' (b.val : Set β)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨b, hxa, hxK⟩)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨b, hxV, hxa⟩)
  have hW1lt : μ W1 < Q := lt_of_le_of_lt hW1 hsum'
  have hW2le : μ W2 ≤ Q := le_trans hW2 hsum'.le
  have hW2ne : μ W2 ≠ ∞ := ne_top_of_le_ne_top hsum'.ne_top hW2
  have hW12 : μ W1 + μ W2 < Q + Q :=
    ENNReal.add_lt_add_of_lt_of_le hW2ne hW1lt hW2le
  have hKclosed : IsClosed (K0 \ W) := by
    rw [Set.sdiff_eq]
    exact hK0comp.isClosed.inter hWopen.isClosed_compl
  have hKcomp : IsCompact (K0 \ W) :=
    hK0comp.of_isClosed_subset hKclosed Set.sdiff_subset
  refine ⟨K0 \ W, hKcomp, ?_, hcont.mono (fun x hx => hx.2)⟩
  have hKc : (K0 \ W)ᶜ = W ∪ K0ᶜ := Set.compl_sdiff
  rw [hKc]
  have hle : μ (W ∪ K0ᶜ) ≤ μ K0ᶜ + (μ W1 + μ W2) := by
    calc μ (W ∪ K0ᶜ) ≤ μ W + μ K0ᶜ := measure_union_le _ _
      _ ≤ (μ W1 + μ W2) + μ K0ᶜ :=
        add_le_add (le_trans (measure_mono hWsub) (measure_union_le _ _)) le_rfl
      _ = μ K0ᶜ + (μ W1 + μ W2) := add_comm _ _
  have hlt : μ K0ᶜ + (μ W1 + μ W2) < H + (Q + Q) :=
    ENNReal.add_lt_add_of_le_of_lt hK0c.ne_top hK0c.le hW12
  have hQQ : Q + Q = H := by
    rw [hQ, hH, ← ENNReal.ofReal_add (le_of_lt hQ0) (le_of_lt hQ0)]
    congr 1
    ring
  have hHH : H + H = ENNReal.ofReal ε := by
    rw [hH, ← ENNReal.ofReal_add (le_of_lt hH0) (le_of_lt hH0)]
    congr 1
    ring
  rw [hQQ, hHH] at hlt
  exact lt_of_le_of_lt hle hlt

end MathlibExt.MeasureTheory.Function.Lusin
