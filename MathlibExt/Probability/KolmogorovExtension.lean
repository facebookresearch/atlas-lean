/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section
open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.KolmogorovExtensionWanted

/-!
# Daniell–Kolmogorov extension theorem

Extending a projective family of Borel probability measures on
Polish factors to a measure on the arbitrary product.
-/

/-- Each factor is nonempty, since it carries a marginal probability measure. -/
private lemma factor_nonempty {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsProbabilityMeasure (P J)] (i : ι) : Nonempty (α i) := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  have hE : IsEmpty (∀ j : ({i} : Finset ι), α j) := by
    rw [isEmpty_pi]
    exact ⟨⟨i, Finset.mem_singleton_self i⟩, hcon⟩
  have h1 : P {i} Set.univ = 1 := measure_univ
  have h0 : P {i} Set.univ = 0 := by
    have huniv : (Set.univ : Set (∀ j : ({i} : Finset ι), α j)) = ∅ :=
      Set.eq_empty_of_isEmpty _
    rw [huniv]
    exact measure_empty
  rw [h1] at h0
  exact one_ne_zero h0

/-- Closed compact cylinders form a compact system. -/
private lemma isCompactSystem_closedCompactCylinders {ι : Type*} {α : ι → Type*}
    [∀ i, TopologicalSpace (α i)] [∀ i, PolishSpace (α i)]
    (hNe : ∀ i, Nonempty (α i)) :
    IsCompactSystem (closedCompactCylinders α) := by
  classical
  refine IsCompactSystem.of_nonempty_iInter fun C hC hne ↦ ?_
  have hCS : ∀ n, C n = cylinder (closedCompactCylinders.finset (hC n))
      (closedCompactCylinders.set (hC n)) :=
    fun n ↦ closedCompactCylinders.eq_cylinder (hC n)
  have hSclosed : ∀ n, IsClosed (closedCompactCylinders.set (hC n)) :=
    fun n ↦ closedCompactCylinders.isClosed (hC n)
  have hScompact : ∀ n, IsCompact (closedCompactCylinders.set (hC n)) :=
    fun n ↦ closedCompactCylinders.isCompact (hC n)
  have hCclosed : ∀ n, IsClosed (C n) := by
    intro n
    rw [hCS n]
    exact (hSclosed n).cylinder _
  have hSne : ∀ n, (closedCompactCylinders.set (hC n)).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := hne n
    have hxC : x ∈ C n := Set.dissipate_subset le_rfl hx
    rw [hCS n, mem_cylinder] at hxC
    exact ⟨_, hxC⟩
  set K : ∀ i, Set (α i) := fun i ↦
    if h : ∃ n, i ∈ closedCompactCylinders.finset (hC n) then
      (fun f : (∀ j : closedCompactCylinders.finset (hC (Nat.find h)), α j) ↦
        f ⟨i, Nat.find_spec h⟩) '' closedCompactCylinders.set (hC (Nat.find h))
    else {(hNe i).some} with hKdef
  have hKeq : ∀ i (h : ∃ n, i ∈ closedCompactCylinders.finset (hC n)),
      K i = (fun f : (∀ j : closedCompactCylinders.finset (hC (Nat.find h)), α j) ↦
        f ⟨i, Nat.find_spec h⟩) '' closedCompactCylinders.set (hC (Nat.find h)) := by
    intro i h
    simp only [hKdef]
    rw [dite_eq_left h]
  have hKcompact : ∀ i, IsCompact (K i) := by
    intro i
    by_cases h : ∃ n, i ∈ closedCompactCylinders.finset (hC n)
    · rw [hKeq i h]
      exact (hScompact _).image (continuous_apply _)
    · simp only [hKdef]
      rw [dite_eq_right h]
      exact isCompact_singleton
  have hKne : ∀ i, (K i).Nonempty := by
    intro i
    by_cases h : ∃ n, i ∈ closedCompactCylinders.finset (hC n)
    · rw [hKeq i h]
      obtain ⟨x, hx⟩ := hSne (Nat.find h)
      exact ⟨_, x, hx, rfl⟩
    · simp only [hKdef]
      rw [dite_eq_right h]
      exact ⟨_, rfl⟩
  have hKclosed : ∀ i, IsClosed (K i) := by
    intro i
    by_cases h : ∃ n, i ∈ closedCompactCylinders.finset (hC n)
    · rw [hKeq i h]
      exact ((hScompact _).image (continuous_apply _)).isClosed
    · simp only [hKdef]
      rw [dite_eq_right h]
      exact isClosed_singleton
  have hmemK : ∀ (n : ℕ) (x : ∀ i, α i), x ∈ Set.dissipate C n →
      ∀ i, (∃ k, k ≤ n ∧ i ∈ closedCompactCylinders.finset (hC k)) → x i ∈ K i := by
    intro n x hx i hik
    obtain ⟨k, hkn, hik⟩ := hik
    have hex : ∃ m, i ∈ closedCompactCylinders.finset (hC m) := ⟨k, hik⟩
    have hfind : Nat.find hex ≤ n := le_trans (Nat.find_min' hex hik) hkn
    have hxCk : x ∈ C (Nat.find hex) := Set.dissipate_subset hfind hx
    rw [hCS _, mem_cylinder] at hxCk
    rw [hKeq i hex]
    exact ⟨_, hxCk, rfl⟩
  have hTcompact : IsCompact (Set.univ.pi K) := isCompact_univ_pi hKcompact
  have hTclosed : IsClosed (Set.univ.pi K) := by
    have hpi : Set.univ.pi K = ⋂ i, (fun x : ∀ i, α i ↦ x i) ⁻¹' K i := by
      ext x
      simp [Set.mem_pi]
    rw [hpi]
    exact isClosed_iInter fun i ↦ (hKclosed i).preimage (continuous_apply i)
  have hEne : ∀ n, (Set.univ.pi K ∩ Set.dissipate C n).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := hne n
    refine ⟨fun i ↦ if _ : ∃ k, k ≤ n ∧ i ∈ closedCompactCylinders.finset (hC k) then
      x i else (hKne i).some, ?_, ?_⟩
    · intro i _
      simp only []
      by_cases hi : ∃ k, k ≤ n ∧ i ∈ closedCompactCylinders.finset (hC k)
      · rw [dite_eq_left hi]
        exact hmemK n x hx i hi
      · rw [dite_eq_right hi]
        exact (hKne i).choose_spec
    · rw [Set.mem_dissipate]
      intro k hkn
      have hagree : (closedCompactCylinders.finset (hC k)).restrict
            (fun i ↦ if _ : ∃ k, k ≤ n ∧ i ∈ closedCompactCylinders.finset (hC k) then
              x i else (hKne i).some)
          = (closedCompactCylinders.finset (hC k)).restrict x := by
        ext j
        simp only [Finset.restrict_def]
        rw [dite_eq_left ⟨k, hkn, j.2⟩]
      have hxCk : x ∈ C k := Set.dissipate_subset hkn hx
      rw [hCS k, mem_cylinder] at hxCk ⊢
      rw [hagree]
      exact hxCk
  have hEanti : ∀ i, (Set.univ.pi K ∩ Set.dissipate C (i + 1))
      ⊆ Set.univ.pi K ∩ Set.dissipate C i :=
    fun i ↦ Set.inter_subset_inter le_rfl (Set.antitone_dissipate (Nat.le_succ i))
  have hEclosed : ∀ i, IsClosed (Set.univ.pi K ∩ Set.dissipate C i) := by
    intro i
    refine hTclosed.inter ?_
    rw [Set.dissipate_def]
    exact isClosed_biInter fun j _ ↦ hCclosed j
  have hEcompact0 : IsCompact (Set.univ.pi K ∩ Set.dissipate C 0) :=
    hTcompact.of_isClosed_subset (hEclosed 0) Set.inter_subset_left
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    _ hEanti hEne hEcompact0 hEclosed
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro n
  exact Set.dissipate_subset le_rfl (hx n).2

/-- A finite additive content on a set ring which admits inner approximation by a compact
system contained in the ring is sigma-subadditive. -/
private lemma IsSigmaSubadditive_of_compactSystem {α : Type*} {C : Set (Set α)}
    {m : AddContent ℝ≥0∞ C} (hC : IsSetRing C)
    (hm_top : ∀ s ∈ C, m s ≠ ∞)
    {K : Set (Set α)} (hK : IsCompactSystem K) (hKC : K ⊆ C)
    (hApprox : ∀ s ∈ C, ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ k ∈ K, k ⊆ s ∧ m (s \ k) < ε) :
    m.IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum hC ?_
  refine addContent_iUnion_eq_sum_of_tendsto_zero hC m hm_top ?_
  intro s hs hAnti h_empty
  rw [tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · simp at ha
  · have hane : a ≠ 0 := ne_of_gt ha
    by_cases hatop : a = ∞
    · subst hatop
      refine Filter.Eventually.of_forall fun n ↦ ?_
      calc m (s n) ≤ m (s 0) :=
            addContent_mono hC.isSetSemiring (hs n) (hs 0) (hAnti (Nat.zero_le n))
        _ < ∞ := lt_top_iff_ne_top.mpr (hm_top _ (hs 0))
    · have hmul_ne : ∀ i : ℕ, (a * (2⁻¹ : ℝ≥0∞) ^ (i + 2)) ≠ 0 := by
        intro i hcon
        apply hane
        have hw0 : ((2⁻¹ : ℝ≥0∞) ^ (i + 2)) ≠ 0 := by simp
        have hwtop : ((2⁻¹ : ℝ≥0∞) ^ (i + 2)) ≠ ∞ := by simp
        have hwinv := ENNReal.mul_inv_cancel hw0 hwtop
        calc a = a * (((2⁻¹ : ℝ≥0∞) ^ (i + 2)) * (((2⁻¹ : ℝ≥0∞) ^ (i + 2)))⁻¹) := by
              rw [hwinv, mul_one]
          _ = (a * ((2⁻¹ : ℝ≥0∞) ^ (i + 2))) * (((2⁻¹ : ℝ≥0∞) ^ (i + 2)))⁻¹ :=
              (mul_assoc _ _ _).symm
          _ = 0 := by rw [hcon, zero_mul]
      have hδ : ∀ i : ℕ, ∃ k ∈ K, k ⊆ s i ∧ m (s i \ k) < a * (2⁻¹ : ℝ≥0∞) ^ (i + 2) := by
        intro i
        exact hApprox _ (hs i) _ (hmul_ne i)
      choose k hkK hksub hkbnd using hδ
      have hKinter : ⋂ i, k i = ∅ := by
        apply Set.eq_empty_of_subset_empty
        rw [← h_empty]
        intro x hx
        simp only [Set.mem_iInter] at hx ⊢
        intro i
        exact hksub i (hx i)
      obtain ⟨N, hN⟩ := hK _ (fun i ↦ hkK i) hKinter
      have hmem : ∀ i, s i \ k i ∈ C :=
        fun i ↦ hC.sdiff_mem (hs i) (hKC (hkK i))
      have hsub : ∀ n, N ≤ n → s n ⊆ ⋃ i ∈ Finset.range (N + 1), (s i \ k i) := by
        intro n hn x hx
        simp only [Set.mem_iUnion, Finset.mem_range]
        by_contra hcon
        push Not at hcon
        have hxN : x ∈ Set.dissipate (fun i ↦ k i) N :=
          Set.mem_dissipate.mpr fun j hjN ↦ by
            show x ∈ k j
            have hxsj : x ∈ s j := hAnti (le_trans hjN hn) hx
            by_contra hxkj
            exact hcon j (Nat.lt_succ_of_le hjN) ⟨hxsj, hxkj⟩
        rw [hN] at hxN
        exact hxN
      have h2inv : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by simp) (by simp)
      have hcalc : (2 : ℝ≥0∞) * (2⁻¹) ^ 2 = 2⁻¹ := by
        rw [sq, ← mul_assoc, h2inv, one_mul]
      have hle : (∑ i ∈ Finset.range (N + 1), (2⁻¹ : ℝ≥0∞) ^ i) ≤ 2 :=
        (ENNReal.sum_le_tsum _).trans_eq ENNReal.tsum_geometric_two
      have hle2 : (∑ i ∈ Finset.range (N + 1), (2⁻¹ : ℝ≥0∞) ^ i) * (2⁻¹ : ℝ≥0∞) ^ 2
          ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ 2 :=
        mul_le_mul_left hle _
      have hgeom : ∑ i ∈ Finset.range (N + 1), a * (2⁻¹ : ℝ≥0∞) ^ (i + 2) ≤ a / 2 := by
        calc ∑ i ∈ Finset.range (N + 1), a * (2⁻¹ : ℝ≥0∞) ^ (i + 2)
            = ∑ i ∈ Finset.range (N + 1), a * ((2⁻¹ : ℝ≥0∞) ^ i * (2⁻¹) ^ 2) :=
              Finset.sum_congr rfl fun i _ ↦ by rw [pow_add]
          _ = a * ∑ i ∈ Finset.range (N + 1), ((2⁻¹ : ℝ≥0∞) ^ i * (2⁻¹) ^ 2) :=
              (Finset.mul_sum _ _ _).symm
          _ = a * ((∑ i ∈ Finset.range (N + 1), (2⁻¹ : ℝ≥0∞) ^ i) * (2⁻¹) ^ 2) := by
              rw [Finset.sum_mul]
          _ ≤ a * (2 * (2⁻¹ : ℝ≥0∞) ^ 2) := mul_le_mul_right hle2 _
          _ = a / 2 := by
              rw [hcalc, ENNReal.div_eq_inv_mul, mul_comm]
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
      calc m (s n) ≤ m (⋃ i ∈ Finset.range (N + 1), (s i \ k i)) :=
            addContent_mono hC.isSetSemiring (hs n)
              (hC.biUnion_mem _ (fun i _ ↦ hmem i)) (hsub n hn)
        _ ≤ ∑ i ∈ Finset.range (N + 1), m (s i \ k i) :=
            addContent_biUnion_le hC (fun i _ ↦ hmem i)
        _ ≤ ∑ i ∈ Finset.range (N + 1), a * (2⁻¹ : ℝ≥0∞) ^ (i + 2) :=
            Finset.sum_le_sum fun i _ ↦ le_of_lt (hkbnd i)
        _ ≤ a / 2 := hgeom
        _ < a := ENNReal.half_lt_self hane hatop

/--
**Kolmogorov extension theorem.** Let $(\alpha_i)_{i \in \iota}$ be a family of Polish spaces, each
with its Borel σ-algebra, indexed by an arbitrary type $\iota$. For each finite set
$J \subseteq \iota$ let $P_J$ be a probability measure on $\prod_{j \in J} \alpha_j$, and suppose
the family is projective: whenever $J \subseteq I$ are finite, the image of $P_I$ under the
restriction map $\prod_{i \in I} \alpha_i \to \prod_{j \in J} \alpha_j$ is $P_J$. Then there is a
measure $\mu$ on $\prod_{i \in \iota} \alpha_i$ whose image under the restriction map to
$\prod_{j \in J} \alpha_j$ is $P_J$ for every finite $J \subseteq \iota$.

Proves `Wanted` entry `kolmogorov_extension`.

Source: A. N. Kolmogorov, Grundbegriffe der
Wahrscheinlichkeitsrechnung, 1933; P. J. Daniell 1918 precursor; textbook in Kallenberg,
Foundations of Modern Probability, 3rd ed. (Kolmogorov extension) and Tao, Introduction to Measure
Theory Lean Polish Borel projective-limit version; full general version handles standard Borel
factors.
-/
theorem kolmogorov_extension
    {ι : Type*} {α : ι → Type*}
    [∀ i, TopologicalSpace (α i)] [∀ i, PolishSpace (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, BorelSpace (α i)]
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ P := by
  have hNe : ∀ i, Nonempty (α i) := fun i ↦ factor_nonempty P i
  have hApprox : ∀ s ∈ measurableCylinders α, ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ k ∈ closedCompactCylinders α, k ⊆ s ∧
        projectiveFamilyContent hP (s \ k) < ε := by
    intro s hs ε hε
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
    obtain ⟨K, hKs, hKco, hKcl, hlt⟩ :=
      hS.exists_isCompact_isClosed_sdiff_lt (measure_lt_top (P I) S).ne hε
    refine ⟨cylinder I K, cylinder_mem_closedCompactCylinders I K hKcl hKco, ?_, ?_⟩
    · exact Set.preimage_mono hKs
    · rw [sdiff_cylinder_same,
        projectiveFamilyContent_cylinder hP (MeasurableSet.diff hS hKcl.measurableSet)]
      exact hlt
  have hsub : (projectiveFamilyContent hP).IsSigmaSubadditive :=
    IsSigmaSubadditive_of_compactSystem isSetRing_measurableCylinders
      (fun s _ ↦ projectiveFamilyContent_ne_top hP)
      (isCompactSystem_closedCompactCylinders hNe)
      (fun _ ht ↦ mem_measurableCylinders_of_mem_closedCompactCylinders ht)
      hApprox
  have hmu_eq : ∀ (J : Finset ι) {T : Set (∀ j : J, α j)} (hT : MeasurableSet T),
      (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
        generateFrom_measurableCylinders.ge hsub (cylinder J T) = P J T := by
    intro J T hT
    calc (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
            generateFrom_measurableCylinders.ge hsub (cylinder J T)
        = projectiveFamilyContent hP (cylinder J T) :=
          AddContent.measure_eq _ isSetSemiring_measurableCylinders
            generateFrom_measurableCylinders.symm hsub
            (cylinder_mem_measurableCylinders J T hT)
      _ = P J T := projectiveFamilyContent_cylinder hP hT
  refine ⟨(projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge hsub, fun I ↦ Measure.ext fun S hS ↦ ?_⟩
  rw [Measure.map_apply (Finset.measurable_restrict I) hS]
  exact hmu_eq I hS

end MathlibExt.Probability.KolmogorovExtensionWanted
end
