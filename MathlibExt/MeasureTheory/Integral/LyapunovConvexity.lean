/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import MathlibExt.MeasureTheory.Measure.Atomless
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences

@[expose] public section

section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted

/-!
# Lyapunov convexity theorem

Records Lyapunov's convexity theorem for the range of a finite-dimensional vector measure.
-/

/-- **Lyapunov range.** For a measure $\mu$ on a measurable space $\alpha$ and a function
$f : \alpha \to E$ into a real normed space $E$, the Lyapunov range of $f$ with respect to $\mu$ is
the set $\lbrace \int_s f \, d\mu : s \subseteq \alpha \text{ measurable} \rbrace$ of integrals of
$f$ over measurable subsets of $\alpha$.

Here $\int_s f \, d\mu$ is the Bochner integral, which is $0$ when $f$ is not integrable on $s$
or when $E$ is not complete. -/
noncomputable def lyapunovRange {α : Type*} [MeasurableSpace α] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (f : α → E) :
    Set E :=
  { y | ∃ (s : Set α), MeasurableSet s ∧ y = ∫ x in s, f x ∂μ }

private theorem isAtomless_exists_pieces_aux {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {V : Set α} (hV : MeasurableSet V) {n : ℕ} (hn : 0 < n) :
    ∀ m, m ≤ n →
      ∃ A : Fin m → Set α, (∀ i, MeasurableSet (A i)) ∧
        (∀ i, A i ⊆ V) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧
        (∀ i, μ (A i) = μ V / (n : ENNReal)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ?_, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | succ m ih =>
    intro hm
    have hm' : m ≤ n := Nat.le_of_succ_le hm
    obtain ⟨A, hmeas, hsub, hpair, hmeas_eq⟩ := ih hm'
    have hUmeas : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hmeas
    have hUsub : (⋃ i, A i) ⊆ V := Set.iUnion_subset hsub
    have hUsum : μ (⋃ i, A i)
        = (m : ENNReal) * (μ V / (n : ENNReal)) := by
      have hd : PairwiseDisjoint
          ((Finset.univ : Finset (Fin m)) : Set (Fin m)) A := by
        intro i _ j _ hij
        exact hpair hij
      have hbi := measure_biUnion_finset (μ := μ) hd (fun b _ => hmeas b)
      have hunion : (⋃ b ∈ (Finset.univ : Finset (Fin m)), A b)
          = ⋃ b, A b := by
        simp
      rw [hunion] at hbi
      rw [hbi]
      simp only [hmeas_eq]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hRmeas : MeasurableSet (V \ ⋃ i, A i) := hV.diff hUmeas
    have hinter : μ (V ∩ (⋃ i, A i)) + μ (V \ ⋃ i, A i) = μ V :=
      measure_inter_add_sdiff V hUmeas
    have hcap : V ∩ (⋃ i, A i) = ⋃ i, A i :=
      Set.inter_eq_self_of_subset_right hUsub
    rw [hcap] at hinter
    have hfinU : μ (⋃ i, A i) ≠ ⊤ := (measure_lt_top μ _).ne
    have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hn
    have hntop : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hcancel : (n : ENNReal) * (μ V / (n : ENNReal)) = μ V := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel hn0 hntop
    have hmul_le : ((m + 1 : ℕ) : ENNReal) * (μ V / (n : ENNReal))
        ≤ μ V := by
      have hcast : ((m + 1 : ℕ) : ENNReal) ≤ (n : ENNReal) := by
        exact_mod_cast hm
      calc ((m + 1 : ℕ) : ENNReal) * (μ V / (n : ENNReal))
          ≤ (n : ENNReal) * (μ V / (n : ENNReal)) :=
            mul_le_mul_of_nonneg_right hcast zero_le
        _ = μ V := hcancel
    have hadd : μ (⋃ i, A i) + μ V / (n : ENNReal) ≤ μ V := by
      rw [hUsum]
      have hexpand : ((m + 1 : ℕ) : ENNReal) * (μ V / (n : ENNReal))
          = (m : ENNReal) * (μ V / (n : ENNReal))
            + μ V / (n : ENNReal) := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [← hexpand]
      exact hmul_le
    have hq_le : μ V / (n : ENNReal) ≤ μ (V \ ⋃ i, A i) := by
      have hadd2 : μ (⋃ i, A i) + μ V / (n : ENNReal)
          ≤ μ (⋃ i, A i) + μ (V \ ⋃ i, A i) := by
        rw [hinter]
        exact hadd
      exact (ENNReal.add_le_add_iff_left hfinU).mp hadd2
    obtain ⟨B, hBsub, hBmeas, hBeq⟩ :=
      isAtomless_exists_subset_measure_eq hA hRmeas hq_le
    have hBsubV : B ⊆ V := hBsub.trans Set.sdiff_subset
    have hdisjR : Disjoint (V \ ⋃ i, A i) (⋃ i, A i) :=
      Set.disjoint_left.mpr (fun x hx => hx.2)
    have hBdisj : ∀ k : Fin m, Disjoint B (A k) := by
      intro k
      exact hdisjR.mono hBsub (Set.subset_iUnion (fun k => A k) k)
    refine ⟨Fin.cons B A, ?_, ?_, ?_, ?_⟩
    · intro i
      obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · rw [Fin.cons_zero]
        exact hBmeas
      · rw [Fin.cons_succ]
        exact hmeas k
    · intro i
      obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · rw [Fin.cons_zero]
        exact hBsubV
      · rw [Fin.cons_succ]
        exact hsub k
    · intro i j hij
      obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
      · obtain rfl | ⟨j', rfl⟩ := Fin.eq_zero_or_eq_succ j
        · exact absurd rfl hij
        · rw [Fin.cons_zero, Fin.cons_succ]
          exact hBdisj j'
      · obtain rfl | ⟨j', rfl⟩ := Fin.eq_zero_or_eq_succ j
        · rw [Fin.cons_succ, Fin.cons_zero]
          exact (hBdisj i').symm
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact hpair (fun h => hij (congrArg Fin.succ h))
    · intro i
      obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · rw [Fin.cons_zero]
        exact hBeq
      · rw [Fin.cons_succ]
        exact hmeas_eq k

/-- N4 (equipartition): a measurable set splits into `n` disjoint pieces of equal
real measure. -/
private theorem isAtomless_exists_equipartition {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {V : Set α} (hV : MeasurableSet V) {n : ℕ} (hn : 0 < n) :
    ∃ A : Fin n → Set α, (∀ i, MeasurableSet (A i)) ∧
      (∀ i, A i ⊆ V) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ i, μ.real (A i) = μ.real V / (n : ℝ)) := by
  obtain ⟨A, hmeas, hsub, hpair, hmeas_eq⟩ :=
    isAtomless_exists_pieces_aux hA hV hn n le_rfl
  refine ⟨A, hmeas, hsub, hpair, ?_⟩
  intro i
  simp only [measureReal_def, hmeas_eq i, ENNReal.toReal_div,
    ENNReal.toReal_natCast]


/-- N5: normalized linear dependence for d+1 vectors in a d-dimensional space. -/
private theorem exists_dependence_coeffs_normalized {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : ℕ) (hd : Module.finrank ℝ E = d) (v : Fin (d + 1) → E) :
    ∃ b : Fin (d + 1) → ℝ, (∃ i, b i = -1) ∧ (∀ j, |b j| ≤ 1) ∧
      ∑ j, b j • v j = 0 := by
  have hnot : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank (R := ℝ)
    simp [Fintype.card_fin] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hnot
  obtain ⟨a, ha0, i0, hi0⟩ := hnot
  obtain ⟨imax, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun j => |a j|) Finset.univ_nonempty
  have haimax : a imax ≠ 0 := by
    intro hcon
    apply hi0
    have hle0 : ∀ j : Fin (d + 1), |a j| ≤ 0 := by
      intro j
      have h := hmax j (Finset.mem_univ j)
      rw [hcon, abs_zero] at h
      exact h
    have h0 : |a i0| ≤ 0 := hle0 i0
    have := le_antisymm h0 (abs_nonneg _)
    exact abs_eq_zero.mp this
  refine ⟨fun j => -(a imax)⁻¹ * a j, ⟨imax, ?_⟩, ?_, ?_⟩
  · simp [haimax]
  · intro j
    have hle := hmax j (Finset.mem_univ j)
    have hpos : 0 < |a imax| := abs_pos.mpr haimax
    calc |-(a imax)⁻¹ * a j| = |a j| / |a imax| := by
            rw [abs_mul, abs_neg, abs_inv, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := by rw [div_le_one hpos]; exact hle
  · have hscale : (∑ j, (-(a imax)⁻¹ * a j) • v j) = (-(a imax)⁻¹) • (∑ j, a j • v j) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul]
    rw [hscale, ha0, smul_zero]

/-- The undecided set of a relaxed control: points where `g` is strictly
between 0 and 1. -/
private def bangBangUndecided {α : Type*} (g : α → ℝ) : Set α :=
  { x | 0 < g x ∧ g x < 1 }

/-- The undecided set of a measurable control is measurable. -/
private theorem bangBangUndecided_measurable {α : Type*} [MeasurableSpace α]
    {g : α → ℝ} (hg : Measurable g) :
    MeasurableSet (bangBangUndecided g) :=
  (measurableSet_lt measurable_const hg).inter
    (measurableSet_lt hg measurable_const)

/-- N6 auxiliary: one bang-bang perturbation step on a large piece `V`. -/
private theorem bangBang_step_aux {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : α → E) (hf : Integrable f μ)
    (d : ℕ) (hd : Module.finrank ℝ E = d)
    (g : α → ℝ) (hgmeas : Measurable g) (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1)
    (V : Set α) (hVmeas : MeasurableSet V)
    (hVU : V ⊆ bangBangUndecided g)
    (hVbig : μ.real (bangBangUndecided g) / 2 ≤ μ.real V)
    (ψ : α → ℝ) (hψmeas : Measurable ψ) (hψbound : ∀ x, |ψ x| ≤ 1)
    (c : ℝ) (hc : c = 0 ∨ c = 1)
    (hψstay : ∀ x ∈ V, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      g x + b * ψ x ∈ Set.Icc (0 : ℝ) 1)
    (hψc : ∀ x ∈ V, g x - ψ x = c) :
    ∃ g' : α → ℝ, Measurable g' ∧ (∀ x, g' x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, x ∉ bangBangUndecided g → g' x = g x) ∧
      bangBangUndecided g' ⊆ bangBangUndecided g ∧
      (∫ x, g' x • f x ∂μ) = ∫ x, g x • f x ∂μ ∧
      μ.real (bangBangUndecided g')
        ≤ (1 - 1 / (2 * ((d : ℝ) + 1)))
          * μ.real (bangBangUndecided g) := by
  obtain ⟨A, hAmeas, hAsub, hApair, hAeq⟩ :=
    isAtomless_exists_equipartition hA hVmeas (show 0 < d + 1 by omega)
  obtain ⟨b, ⟨i, hbi⟩, hb01, hbsum⟩ :=
    exists_dependence_coeffs_normalized d hd
      (fun j => ∫ x in A j, ψ x • f x ∂μ)
  set g' : α → ℝ :=
    fun x => g x + ∑ j, b j * (A j).indicator ψ x with hg'def
  have hg'apply : ∀ x, g' x
      = g x + ∑ j, b j * (A j).indicator ψ x := fun x => rfl
  have hsum_single : ∀ (x : α) (j : Fin (d + 1)), x ∈ A j →
      (∑ k, b k * (A k).indicator ψ x) = b j * ψ x := by
    intro x j hx
    have hmem : (A j).indicator ψ x = ψ x :=
      Set.indicator_of_mem hx _
    calc (∑ k, b k * (A k).indicator ψ x)
        = b j * (A j).indicator ψ x :=
          Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
            (fun k _ hkj => by
              have hdisj := hApair (Ne.symm hkj)
              have hnot : x ∉ A k :=
                Set.disjoint_left.mp hdisj hx
              rw [Set.indicator_of_notMem hnot _, mul_zero])
      _ = b j * ψ x := by rw [hmem]
  have hsum_zero : ∀ x : α, (∀ j, x ∉ A j) →
      (∑ k, b k * (A k).indicator ψ x) = 0 := by
    intro x hx
    apply Finset.sum_eq_zero
    intro k _
    rw [Set.indicator_of_notMem (hx k) _, mul_zero]
  have hg'meas : Measurable g' := by
    rw [hg'def]
    apply Measurable.add hgmeas
    apply Finset.measurable_sum
    intro j _
    exact (hψmeas.indicator (hAmeas j)).const_mul (b j)
  have hg'01 : ∀ x, g' x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    rw [hg'apply x]
    by_cases hex : ∃ j, x ∈ A j
    · obtain ⟨j, hxj⟩ := hex
      rw [hsum_single x j hxj]
      have hxV : x ∈ V := hAsub j hxj
      have hbmem : b j ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp (hb01 j)
      exact hψstay x hxV (b j) hbmem
    · have hall : ∀ j, x ∉ A j := fun j hj => hex ⟨j, hj⟩
      rw [hsum_zero x hall, add_zero]
      exact hg01 x
  have hfreeze : ∀ x, x ∉ bangBangUndecided g → g' x = g x := by
    intro x hxU
    rw [hg'apply x]
    have hall : ∀ j, x ∉ A j := by
      intro j haj
      exact hxU (hVU (hAsub j haj))
    rw [hsum_zero x hall, add_zero]
  have hUU : bangBangUndecided g' ⊆ bangBangUndecided g := by
    intro x hx'
    have hx'' : 0 < g' x ∧ g' x < 1 := hx'
    by_contra hcon
    have hfr := hfreeze x hcon
    rw [hfr] at hx''
    exact hcon hx''
  have hg'c : ∀ x ∈ A i, g' x = c := by
    intro x hxi
    rw [hg'apply x, hsum_single x i hxi, hbi]
    have hxV : x ∈ V := hAsub i hxi
    have heq : g x + -1 * ψ x = g x - ψ x := by ring
    rw [heq]
    exact hψc x hxV
  have hsub2 : bangBangUndecided g' ⊆ bangBangUndecided g \ A i := by
    intro x hx'
    have hxU : x ∈ bangBangUndecided g := hUU hx'
    refine ⟨hxU, ?_⟩
    intro hxi
    have hgc := hg'c x hxi
    have hx'' : 0 < g' x ∧ g' x < 1 := hx'
    rw [hgc] at hx''
    rcases hc with rfl | rfl
    · exact absurd hx''.1 (lt_irrefl 0)
    · exact absurd hx''.2 (lt_irrefl 1)
  have hAisub : A i ⊆ bangBangUndecided g := (hAsub i).trans hVU
  have hdiff : μ.real (bangBangUndecided g \ A i)
      = μ.real (bangBangUndecided g) - μ.real (A i) :=
    measureReal_sdiff hAisub (hAmeas i)
  have hmono2 : μ.real (bangBangUndecided g')
      ≤ μ.real (bangBangUndecided g \ A i) :=
    measureReal_mono hsub2
  have hAeqi : μ.real (A i) = μ.real V / ((d : ℝ) + 1) := by
    have h := hAeq i
    have hDn : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [hDn] at h
    exact h
  have hnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hDpos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  have hD2pos : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by linarith
  have hWdiv : μ.real (bangBangUndecided g) / (2 * ((d : ℝ) + 1))
      ≤ μ.real V / ((d : ℝ) + 1) := by
    rw [div_le_div_iff₀ hD2pos hDpos]
    have h2 : μ.real (bangBangUndecided g) ≤ 2 * μ.real V := by
      linarith [hVbig]
    have hmul := mul_le_mul_of_nonneg_right h2 (le_of_lt hDpos)
    have heq : (2 * μ.real V) * ((d : ℝ) + 1)
        = μ.real V * (2 * ((d : ℝ) + 1)) := by ring
    rwa [heq] at hmul
  have hexpand : (1 - 1 / (2 * ((d : ℝ) + 1)))
        * μ.real (bangBangUndecided g)
      = μ.real (bangBangUndecided g)
        - μ.real (bangBangUndecided g) / (2 * ((d : ℝ) + 1)) := by
    rw [sub_mul, one_mul]
    congr 1
    rw [div_mul_eq_mul_div, one_mul]
  have hshrink : μ.real (bangBangUndecided g')
      ≤ (1 - 1 / (2 * ((d : ℝ) + 1)))
        * μ.real (bangBangUndecided g) := by
    calc μ.real (bangBangUndecided g')
        ≤ μ.real (bangBangUndecided g \ A i) := hmono2
      _ = μ.real (bangBangUndecided g) - μ.real (A i) := hdiff
      _ = μ.real (bangBangUndecided g) - μ.real V / ((d : ℝ) + 1) := by
          rw [hAeqi]
      _ ≤ μ.real (bangBangUndecided g)
            - μ.real (bangBangUndecided g) / (2 * ((d : ℝ) + 1)) := by
          linarith [hWdiv]
      _ = (1 - 1 / (2 * ((d : ℝ) + 1)))
            * μ.real (bangBangUndecided g) := hexpand.symm
  have hscal_meas : ∀ j, Measurable
      (fun x => b j * (A j).indicator ψ x) := by
    intro j
    exact (hψmeas.indicator (hAmeas j)).const_mul (b j)
  have hscal_bound : ∀ j, ∀ x, |b j * (A j).indicator ψ x| ≤ 1 := by
    intro j x
    by_cases hx : x ∈ A j
    · rw [Set.indicator_of_mem hx _]
      have h1 : |b j| ≤ 1 := hb01 j
      have h2 : |ψ x| ≤ 1 := hψbound x
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans h2
    · rw [Set.indicator_of_notMem hx _, mul_zero, abs_zero]
      exact zero_le_one
  have hpiece_int : ∀ j, Integrable
      (fun x => (b j * (A j).indicator ψ x) • f x) μ := by
    intro j
    have h1 : AEStronglyMeasurable
        (fun x => b j * (A j).indicator ψ x) μ :=
      (hscal_meas j).aestronglyMeasurable
    have h2 : ∀ᵐ x ∂μ, ‖b j * (A j).indicator ψ x‖ ≤ 1 :=
      Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact hscal_bound j x)
    exact hf.bdd_smul 1 h1 h2
  have hg_int : Integrable (fun x => g x • f x) μ := by
    have h1 : AEStronglyMeasurable g μ := hgmeas.aestronglyMeasurable
    have h2 : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      have hx := hg01 x
      exact abs_le.mpr ⟨by have h0 := hx.1; linarith, hx.2⟩)
    exact hf.bdd_smul 1 h1 h2
  have hfun : (fun x => g' x • f x)
      = fun x => g x • f x
        + ∑ j, ((b j * (A j).indicator ψ x) • f x) := by
    funext x
    rw [hg'apply x, add_smul, Finset.sum_smul]
  have hpiece_fun : ∀ j, (fun x => ((b j * (A j).indicator ψ x)) • f x)
      = fun x => b j • ((A j).indicator (fun x => ψ x • f x) x) := by
    intro j
    funext x
    by_cases hx : x ∈ A j
    · rw [Set.indicator_of_mem hx _, Set.indicator_of_mem hx _, mul_smul]
    · rw [Set.indicator_of_notMem hx _, Set.indicator_of_notMem hx _,
        mul_zero, zero_smul, smul_zero]
  have hpiece_int_eq : ∀ j, (∫ x, ((b j * (A j).indicator ψ x)) • f x ∂μ)
      = b j • (∫ x in A j, ψ x • f x ∂μ) := by
    intro j
    rw [hpiece_fun j, integral_smul, integral_indicator (hAmeas j)]
  have hsum_int : Integrable
      (fun x => ∑ j, ((b j * (A j).indicator ψ x) • f x)) μ :=
    integrable_finsetSum Finset.univ (fun j _ => hpiece_int j)
  have hint : (∫ x, g' x • f x ∂μ) = ∫ x, g x • f x ∂μ := by
    rw [hfun, integral_add hg_int hsum_int,
      integral_finsetSum _ (fun j _ => hpiece_int j)]
    simp only [hpiece_int_eq]
    rw [hbsum, add_zero]
  exact ⟨g', hg'meas, hg'01, hfreeze, hUU, hint, hshrink⟩

/-- N6 (bang-bang step): one perturbation shrinking the undecided set while
preserving the integral. -/
private theorem bangBang_step {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : α → E) (hf : Integrable f μ)
    (d : ℕ) (hd : Module.finrank ℝ E = d)
    (g : α → ℝ) (hgmeas : Measurable g) (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ g' : α → ℝ, Measurable g' ∧ (∀ x, g' x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, x ∉ bangBangUndecided g → g' x = g x) ∧
      bangBangUndecided g' ⊆ bangBangUndecided g ∧
      (∫ x, g' x • f x ∂μ) = ∫ x, g x • f x ∂μ ∧
      μ.real (bangBangUndecided g')
        ≤ (1 - 1 / (2 * ((d : ℝ) + 1)))
          * μ.real (bangBangUndecided g) := by
  by_cases hU0 : μ.real (bangBangUndecided g) = 0
  · refine ⟨g, hgmeas, hg01, fun x _ => rfl, le_rfl, rfl, ?_⟩
    rw [hU0, mul_zero]
  · have hUmeas := bangBangUndecided_measurable hgmeas
    set V1 : Set α := bangBangUndecided g ∩ { x | g x ≤ 1 / 2 } with hV1def
    set V2 : Set α := bangBangUndecided g ∩ { x | 1 / 2 < g x } with hV2def
    have hV1meas : MeasurableSet V1 := by
      rw [hV1def]
      exact hUmeas.inter (measurableSet_le hgmeas measurable_const)
    have hV2meas : MeasurableSet V2 := by
      rw [hV2def]
      exact hUmeas.inter (measurableSet_lt measurable_const hgmeas)
    have hV1sub : V1 ⊆ bangBangUndecided g := by
      rw [hV1def]
      exact Set.inter_subset_left
    have hV2sub : V2 ⊆ bangBangUndecided g := by
      rw [hV2def]
      exact Set.inter_subset_left
    have hcover : bangBangUndecided g ⊆ V1 ∪ V2 := by
      intro x hx
      by_cases hle : g x ≤ 1 / 2
      · left
        rw [hV1def]
        exact ⟨hx, hle⟩
      · right
        rw [hV2def]
        exact ⟨hx, lt_of_not_ge hle⟩
    have hunle : μ.real (bangBangUndecided g) ≤ μ.real V1 + μ.real V2 := by
      calc μ.real (bangBangUndecided g) ≤ μ.real (V1 ∪ V2) :=
            measureReal_mono hcover
        _ ≤ μ.real V1 + μ.real V2 := measureReal_union_le _ _
    have hsplit : μ.real (bangBangUndecided g) / 2 ≤ μ.real V1 ∨
        μ.real (bangBangUndecided g) / 2 ≤ μ.real V2 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      linarith [hunle]
    rcases hsplit with hbig | hbig
    · refine bangBang_step_aux hA f hf d hd g hgmeas hg01 V1 hV1meas hV1sub
        hbig g hgmeas ?_ 0 (Or.inl rfl) ?_ ?_
      · intro x
        have hx := hg01 x
        exact abs_le.mpr ⟨by have h0 := hx.1; linarith, hx.2⟩
      · intro x hxV b hb
        rw [hV1def] at hxV
        have hxU : x ∈ bangBangUndecided g := hxV.1
        have hxhalf : g x ≤ 1 / 2 := hxV.2
        have hx' : 0 < g x ∧ g x < 1 := hxU
        have hb' : (-1 : ℝ) ≤ b ∧ b ≤ 1 := hb
        have heq : g x + b * g x = g x * (1 + b) := by ring
        rw [heq]
        refine ⟨?_, ?_⟩
        · apply mul_nonneg (le_of_lt hx'.1)
          linarith [hb'.1]
        · have h1b : (0 : ℝ) ≤ 1 + b := by linarith [hb'.1]
          have h2b : 1 + b ≤ 2 := by linarith [hb'.2]
          calc g x * (1 + b) ≤ (1 / 2) * (1 + b) :=
                mul_le_mul_of_nonneg_right hxhalf h1b
            _ ≤ (1 / 2) * 2 :=
                mul_le_mul_of_nonneg_left h2b (by norm_num)
            _ = 1 := by norm_num
      · intro x _
        exact sub_self (g x)
    · refine bangBang_step_aux hA f hf d hd g hgmeas hg01 V2 hV2meas hV2sub
        hbig (fun x => g x - 1) (hgmeas.sub measurable_const) ?_ 1
        (Or.inr rfl) ?_ ?_
      · intro x
        have hx := hg01 x
        exact abs_le.mpr
          ⟨by have h0 := hx.1; linarith, by have h1 := hx.2; linarith⟩
      · intro x hxV b hb
        rw [hV2def] at hxV
        have hxU : x ∈ bangBangUndecided g := hxV.1
        have hxhalf : 1 / 2 < g x := hxV.2
        have hx' : 0 < g x ∧ g x < 1 := hxU
        have hb' : (-1 : ℝ) ≤ b ∧ b ≤ 1 := hb
        have hnn : (0 : ℝ) ≤ 1 - g x := by linarith [hx'.2]
        have h1 : b * (g x - 1) ≤ 1 - g x := by
          have heq : b * (g x - 1) = (-b) * (1 - g x) := by ring
          have hnb : -b ≤ 1 := by linarith [hb'.1]
          calc b * (g x - 1) = (-b) * (1 - g x) := heq
            _ ≤ 1 * (1 - g x) := mul_le_mul_of_nonneg_right hnb hnn
            _ = 1 - g x := one_mul _
        have h2 : -(1 - g x) ≤ b * (g x - 1) := by
          have heq : b * (g x - 1) = (-b) * (1 - g x) := by ring
          have hnb : (-1 : ℝ) ≤ -b := by linarith [hb'.2]
          have hle : (-1) * (1 - g x) ≤ (-b) * (1 - g x) :=
            mul_le_mul_of_nonneg_right hnb hnn
          rw [heq]
          linarith [hle]
        refine ⟨?_, ?_⟩
        · linarith [h2, hxhalf]
        · linarith [h1]
      · intro x _
        ring

/-- N7 (bang-bang principle): every relaxed control is realized by a set. -/
private theorem exists_set_integral_eq_integral_smul {α : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hA : IsAtomless μ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : α → E) (hf : Integrable f μ)
    (g : α → ℝ) (hgmeas : Measurable g) (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ s, MeasurableSet s ∧ (∫ x in s, f x ∂μ) = ∫ x, g x • f x ∂μ := by
  set d : ℕ := Module.finrank ℝ E with hddef
  set ρ : ℝ := 1 - 1 / (2 * ((d : ℝ) + 1)) with hρdef
  have hd : Module.finrank ℝ E = d := hddef.symm
  have hnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have h2D : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by linarith
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    have hle : 1 / (2 * ((d : ℝ) + 1)) ≤ 1 :=
      (div_le_one h2D).mpr (by linarith)
    linarith
  have hρ1 : ρ < 1 := by
    rw [hρdef]
    have hpos : (0 : ℝ) < 1 / (2 * ((d : ℝ) + 1)) :=
      div_pos zero_lt_one h2D
    linarith
  have hstep : ∀ G0 : { g : α → ℝ //
        Measurable g ∧ ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 },
      ∃ G1 : { g : α → ℝ //
        Measurable g ∧ ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 },
        (∀ x, x ∉ bangBangUndecided G0.1 → G1.1 x = G0.1 x) ∧
        bangBangUndecided G1.1 ⊆ bangBangUndecided G0.1 ∧
        (∫ x, G1.1 x • f x ∂μ) = ∫ x, G0.1 x • f x ∂μ ∧
        μ.real (bangBangUndecided G1.1)
          ≤ ρ * μ.real (bangBangUndecided G0.1) := by
    intro G0
    obtain ⟨g', hg'meas, hg'01, hfr, hUU, hint, hshrink⟩ :=
      bangBang_step hA f hf d hd G0.1 G0.2.1 G0.2.2
    exact ⟨⟨g', hg'meas, hg'01⟩, hfr, hUU, hint, hshrink⟩
  choose step hstep_spec using hstep
  set G0 : { g : α → ℝ //
      Measurable g ∧ ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 } :=
    ⟨g, hgmeas, hg01⟩ with hG0def
  set seq : ℕ → { g : α → ℝ //
      Measurable g ∧ ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 } :=
    fun n => step^[n] G0 with hseqdef
  have hseq_succ : ∀ n, seq (n + 1) = step (seq n) := by
    intro n
    have hiter : step^[n + 1] G0 = step (step^[n] G0) := by
      rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply']
    exact hiter
  have hfr : ∀ n x, x ∉ bangBangUndecided (seq n).1 →
      (seq (n + 1)).1 x = (seq n).1 x := by
    intro n x hx
    have h := (hstep_spec (seq n)).1 x hx
    rwa [← hseq_succ n] at h
  have hUU : ∀ n, bangBangUndecided (seq (n + 1)).1
      ⊆ bangBangUndecided (seq n).1 := by
    intro n
    have h := (hstep_spec (seq n)).2.1
    rwa [← hseq_succ n] at h
  have hint : ∀ n, (∫ x, (seq (n + 1)).1 x • f x ∂μ)
      = ∫ x, (seq n).1 x • f x ∂μ := by
    intro n
    have h := (hstep_spec (seq n)).2.2.1
    rwa [← hseq_succ n] at h
  have hshrink : ∀ n, μ.real (bangBangUndecided (seq (n + 1)).1)
      ≤ ρ * μ.real (bangBangUndecided (seq n).1) := by
    intro n
    have h := (hstep_spec (seq n)).2.2.2
    rwa [← hseq_succ n] at h
  have hseq0 : (seq 0).1 = g := rfl
  have hint_all : ∀ n, (∫ x, (seq n).1 x • f x ∂μ)
      = ∫ x, g x • f x ∂μ := by
    intro n
    induction n with
    | zero => rw [hseq0]
    | succ n ih => rw [hint n]; exact ih
  have hUbound : ∀ n, μ.real (bangBangUndecided (seq n).1)
      ≤ ρ ^ n * μ.real (bangBangUndecided g) := by
    intro n
    induction n with
    | zero => rw [hseq0, pow_zero, one_mul]
    | succ n ih =>
      calc μ.real (bangBangUndecided (seq (n + 1)).1)
          ≤ ρ * μ.real (bangBangUndecided (seq n).1) := hshrink n
        _ ≤ ρ * (ρ ^ n * μ.real (bangBangUndecided g)) :=
            mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (n + 1) * μ.real (bangBangUndecided g) := by
            rw [pow_succ]; ring
  have hUanti : Antitone (fun n => bangBangUndecided (seq n).1) := by
    apply antitone_nat_of_succ_le
    intro n
    exact hUU n
  have hpow0 : Tendsto (fun n => ρ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hpow : Tendsto (fun n => ρ ^ n * μ.real (bangBangUndecided g)) atTop
      (𝓝 0) := by
    have h := Filter.Tendsto.mul_const (μ.real (bangBangUndecided g)) hpow0
    simpa using h
  have hNle : ∀ n, μ.real (⋂ n, bangBangUndecided (seq n).1)
      ≤ ρ ^ n * μ.real (bangBangUndecided g) := by
    intro n
    calc μ.real (⋂ n, bangBangUndecided (seq n).1)
        ≤ μ.real (bangBangUndecided (seq n).1) :=
          measureReal_mono
            (Set.iInter_subset (fun k => bangBangUndecided (seq k).1) n)
      _ ≤ ρ ^ n * μ.real (bangBangUndecided g) := hUbound n
  have hN0 : μ.real (⋂ n, bangBangUndecided (seq n).1) = 0 := by
    have hle : μ.real (⋂ n, bangBangUndecided (seq n).1) ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hNle
    exact le_antisymm hle measureReal_nonneg
  have hN0' : μ (⋂ n, bangBangUndecided (seq n).1) = 0 := by
    rw [measureReal_def] at hN0
    have hfin : μ (⋂ n, bangBangUndecided (seq n).1) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    rcases (ENNReal.toReal_eq_zero_iff _).mp hN0 with h | h
    · exact h
    · exact absurd h hfin
  have hae : ∀ᵐ x ∂μ, x ∉ ⋂ n, bangBangUndecided (seq n).1 :=
    compl_mem_ae_iff.mpr hN0'
  have hfrwd : ∀ m k, k ≤ m → ∀ x,
      x ∉ bangBangUndecided (seq k).1 → (seq m).1 x = (seq k).1 x := by
    intro m
    induction m with
    | zero =>
      intro k hkm x hxk
      have hkk : k = 0 := by omega
      subst hkk
      rfl
    | succ m ih =>
      intro k hkm x hxk
      by_cases h : k ≤ m
      · have hxm : x ∉ bangBangUndecided (seq m).1 :=
          fun hx => hxk (hUanti h hx)
        rw [hfr m x hxm]
        exact ih k h x hxk
      · have hkk : k = m + 1 := by omega
        subst hkk
        rfl
  have h01or : ∀ k x, x ∉ bangBangUndecided (seq k).1 →
      (seq k).1 x = 0 ∨ (seq k).1 x = 1 := by
    intro k x hxk
    have h01x := (seq k).2.2 x
    by_cases h0 : (seq k).1 x = 0
    · exact Or.inl h0
    · have hpos : 0 < (seq k).1 x := lt_of_le_of_ne h01x.1 (Ne.symm h0)
      have hnge : ¬ (seq k).1 x < 1 := fun hlt => hxk ⟨hpos, hlt⟩
      have hge : 1 ≤ (seq k).1 x := not_lt.mp hnge
      exact Or.inr (le_antisymm h01x.2 hge)
  set s : Set α := ⋃ n, { x | (seq n).1 x = 1 } with hsdef
  have hsmeas : MeasurableSet s := by
    rw [hsdef]
    exact MeasurableSet.iUnion
      (fun n => measurableSet_eq_fun (seq n).2.1 measurable_const)
  have hmem : ∀ x, ∀ n, x ∉ bangBangUndecided (seq n).1 →
      (x ∈ s ↔ (seq n).1 x = 1) := by
    intro x n hnx
    constructor
    · intro hxs
      rw [hsdef] at hxs
      have hexk : ∃ k, (seq k).1 x = 1 := by
        have hmemU := Set.mem_iUnion.mp hxs
        obtain ⟨k, hk⟩ := hmemU
        exact ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hexk
      by_cases hkn : k ≤ n
      · have hxk : x ∉ bangBangUndecided (seq k).1 := by
          intro hmemU
          have h' : 0 < (seq k).1 x ∧ (seq k).1 x < 1 := hmemU
          rw [hk] at h'
          exact absurd h'.2 (lt_irrefl 1)
        have hfrz := hfrwd n k hkn x hxk
        rw [hfrz]
        exact hk
      · have hnk : n ≤ k := le_of_not_ge hkn
        have hfrz := hfrwd k n hnk x hnx
        rw [← hfrz]
        exact hk
    · intro hnx1
      rw [hsdef]
      exact Set.mem_iUnion_of_mem n hnx1
  have hlimpt : ∀ x, x ∉ ⋂ n, bangBangUndecided (seq n).1 →
      ∃ c : ℝ, Tendsto (fun m => (seq m).1 x) atTop (𝓝 c) ∧
        c • f x = s.indicator f x := by
    intro x hxN
    have hex : ∃ n, x ∉ bangBangUndecided (seq n).1 := by
      by_contra hcon
      exact hxN (Set.mem_iInter.mpr
        (fun n => by_contra (fun h => hcon ⟨n, h⟩)))
    obtain ⟨n, hnx⟩ := hex
    have hev : ∀ᶠ m in atTop, (seq m).1 x = (seq n).1 x := by
      filter_upwards [eventually_ge_atTop n] with m hm
      exact hfrwd m n hm x hnx
    refine ⟨(seq n).1 x,
      tendsto_const_nhds.congr' (hev.mono fun m hm => hm.symm), ?_⟩
    by_cases h1 : (seq n).1 x = 1
    · have hxs : x ∈ s := (hmem x n hnx).mpr h1
      have e2 : s.indicator f x = f x := Set.indicator_of_mem hxs _
      rw [h1, e2, one_smul]
    · rcases h01or n x hnx with h0 | h1'
      · have hxns : x ∉ s := by
          intro hxs
          exact h1 ((hmem x n hnx).mp hxs)
        have e2 : s.indicator f x = 0 := Set.indicator_of_notMem hxns _
        rw [h0, e2, zero_smul]
      · exact absurd h1' h1
  have hFint : ∀ n, Integrable (fun x => (seq n).1 x • f x) μ := by
    intro n
    have h1 : AEStronglyMeasurable (seq n).1 μ :=
      (seq n).2.1.aestronglyMeasurable
    have h2 : ∀ᵐ x ∂μ, ‖(seq n).1 x‖ ≤ 1 :=
      Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        have hx := (seq n).2.2 x
        exact abs_le.mpr ⟨by have h0 := hx.1; linarith, hx.2⟩)
    exact hf.bdd_smul 1 h1 h2
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun x => (seq n).1 x • f x) μ :=
    fun n => (hFint n).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖(seq n).1 x • f x‖ ≤ ‖f x‖ := by
    intro n
    apply Eventually.of_forall
    intro x
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |(seq n).1 x| ≤ 1 := by
      have hx := (seq n).2.2 x
      exact abs_le.mpr ⟨by have h0 := hx.1; linarith, hx.2⟩
    calc |(seq n).1 x| * ‖f x‖ ≤ 1 * ‖f x‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖f x‖ := one_mul _
  have hlim_ae : ∀ᵐ x ∂μ, Tendsto (fun m => (seq m).1 x • f x) atTop
      (𝓝 (s.indicator f x)) := by
    filter_upwards [hae] with x hxN
    obtain ⟨c, hseq, hbridge⟩ := hlimpt x hxN
    have hG : Continuous (fun c : ℝ => c • f x) :=
      continuous_id.smul continuous_const
    have hcomp : Tendsto (fun m => (seq m).1 x • f x) atTop (𝓝 (c • f x)) :=
      (hG.tendsto _).comp hseq
    rwa [hbridge] at hcomp
  have hdct := tendsto_integral_of_dominated_convergence
    (fun x => ‖f x‖) hFmeas hf.norm hbound hlim_ae
  have hconst : Tendsto (fun n => ∫ x, (seq n).1 x • f x ∂μ) atTop
      (𝓝 (∫ x, g x • f x ∂μ)) := by
    have hfun : (fun n => ∫ x, (seq n).1 x • f x ∂μ)
        = fun _ => ∫ x, g x • f x ∂μ :=
      funext hint_all
    rw [hfun]
    exact tendsto_const_nhds
  have heq : (∫ x, g x • f x ∂μ) = ∫ x, s.indicator f x ∂μ :=
    tendsto_nhds_unique hconst hdct
  have hfin : ∫ x, s.indicator f x ∂μ = ∫ x in s, f x ∂μ :=
    integral_indicator hsmeas
  refine ⟨s, hsmeas, ?_⟩
  rw [← hfin]
  exact heq.symm

/-- N9: the Lyapunov range is bounded. -/
private theorem lyapunovRange_isBounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) (hf : Integrable f μ) :
    Bornology.IsBounded (lyapunovRange (μ := μ) (f := f)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨∫ x, ‖f x‖ ∂μ, fun y hy => ?_⟩
  obtain ⟨s, hs, rfl⟩ := hy
  calc ‖∫ x in s, f x ∂μ‖ ≤ ∫ x in s, ‖f x‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ ∂μ :=
        setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)

/-- N10: the Lyapunov range depends only on the a.e. class of `f`. -/
private theorem lyapunovRange_congr_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : α → E} (h : f =ᵐ[μ] f') :
    lyapunovRange (μ := μ) (f := f) = lyapunovRange (μ := μ) (f := f') := by
  ext y
  simp only [lyapunovRange, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, setIntegral_congr_ae hs (h.mono fun x hx _ => hx)⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, setIntegral_congr_ae hs (h.symm.mono fun x hx _ => hx)⟩

/-- N11a: transport of the Lyapunov range into a finite-dimensional subspace. -/
private theorem lyapunovRange_eq_image_subtype {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) (f : α → E) (hf : Integrable f μ)
    (hae : ∀ᵐ x ∂μ, f x ∈ W) :
    ∃ fW : α → W, Integrable fW μ ∧
      lyapunovRange (μ := μ) (f := f) = W.subtypeL '' lyapunovRange (μ := μ) (f := fW) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  let π : E →L[ℝ] ↥W := LinearMap.toContinuousLinearMap g
  have hfW : Integrable (fun x => π (f x)) μ := π.integrable_comp hf
  have hae2 : (fun x => W.subtypeL (π (f x))) =ᵐ[μ] f := by
    filter_upwards [hae] with x hx
    show W.subtypeL (π (f x)) = f x
    let w : ↥W := ⟨f x, hx⟩
    have hw : (W.subtype w : E) = f x := rfl
    have hgw : g (W.subtype w) = w := by
      have := LinearMap.congr_fun hg w
      simpa using this
    have hpi : π (W.subtype w) = w := hgw
    have hpix : π (f x) = w := by rw [← hw]; exact hpi
    rw [hpix]
    have hcoe : ⇑W.subtypeL = ⇑W.subtype := Submodule.coe_subtypeL W
    rw [hcoe]
    exact hw
  refine ⟨fun x => π (f x), hfW, ?_⟩
  ext y
  simp only [lyapunovRange, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨∫ x in s, (fun x => π (f x)) x ∂μ, ⟨s, hs, rfl⟩, ?_⟩
    have hWr : Integrable (fun x => π (f x)) (μ.restrict s) := hfW.restrict
    have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) W.subtypeL hWr
    rw [← hcomm]
    exact setIntegral_congr_ae hs (hae2.mono fun x hx _ => hx)
  · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    have hWr : Integrable (fun x => π (f x)) (μ.restrict s) := hfW.restrict
    have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) W.subtypeL hWr
    rw [← hcomm]
    exact setIntegral_congr_ae hs (hae2.mono fun x hx _ => hx)

/-- N11b: closedness transfers from the subspace range to the ambient range. -/
private theorem lyapunovRange_isClosed_of_subtype_isClosed {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℝ E) [FiniteDimensional ℝ ↥W]
    {fW : α → W} (hclosed : IsClosed (lyapunovRange (μ := μ) (f := fW))) :
    IsClosed (W.subtypeL '' lyapunovRange (μ := μ) (f := fW)) := by
  have hWclosed : IsClosed (W : Set E) := W.closed_of_finiteDimensional
  have hmap : IsClosedMap (⇑W.subtypeL) := by
    rw [Submodule.coe_subtypeL, Submodule.coe_subtype]
    exact hWclosed.isClosedMap_subtype_val
  exact hmap _ hclosed

/-- N14: if the range has empty interior, a nonzero dual functional vanishes a.e. on `f`. -/
private theorem exists_dual_ae_zero_of_interior_eq_empty {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (hf : Integrable f μ)
    (hconv : Convex ℝ (lyapunovRange (μ := μ) (f := f)))
    (hempty : interior (lyapunovRange (μ := μ) (f := f)) = ∅) :
    ∃ p : E →L[ℝ] ℝ, p ≠ 0 ∧ (fun x => p (f x)) =ᵐ[μ] 0 := by
  have h0mem : (0 : E) ∈ lyapunovRange (μ := μ) (f := f) :=
    ⟨∅, MeasurableSet.empty, (setIntegral_empty).symm⟩
  have hne : (lyapunovRange (μ := μ) (f := f)).Nonempty := ⟨0, h0mem⟩
  have haff_ne : affineSpan ℝ (lyapunovRange (μ := μ) (f := f)) ≠ ⊤ := by
    intro htop
    have := (hconv.interior_nonempty_iff_affineSpan_eq_top).mpr htop
    rw [hempty] at this
    exact Set.not_nonempty_empty this
  have hvec_ne : vectorSpan ℝ (lyapunovRange (μ := μ) (f := f)) ≠ ⊤ := by
    intro htop
    apply haff_ne
    have := (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E hne).mpr htop
    exact this
  have hlt : vectorSpan ℝ (lyapunovRange (μ := μ) (f := f)) < ⊤ := lt_top_iff_ne_top.mpr hvec_ne
  obtain ⟨q, hqne, hqle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  let p : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap q
  have hpq : ∀ x, p x = q x := fun x => rfl
  have hpne : p ≠ 0 := by
    intro h0
    apply hqne
    have hqe : LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ) q = 0 := h0
    have := (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).injective hqe
    simpa using this
  refine ⟨p, hpne, ?_⟩
  have hzero : ∀ s : Set α, MeasurableSet s → μ s < ⊤ → ∫ x in s, p (f x) ∂μ = 0 := by
    intro s hs hfin
    have hmem : (∫ x in s, f x ∂μ) ∈ lyapunovRange (μ := μ) (f := f) := ⟨s, hs, rfl⟩
    have hvsub : (∫ x in s, f x ∂μ) -ᵥ (0 : E) ∈ vectorSpan ℝ (lyapunovRange (μ := μ) (f := f)) :=
      vsub_mem_vectorSpan ℝ hmem h0mem
    have hvsub' : (∫ x in s, f x ∂μ) ∈
        vectorSpan ℝ (lyapunovRange (μ := μ) (f := f)) := by
      simpa using hvsub
    have hker : q (∫ x in s, f x ∂μ) = 0 := hqle hvsub'
    have hfr : Integrable f (μ.restrict s) := hf.restrict
    have hcomm0 := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) p hfr
    have hcommeq : p (∫ x in s, f x ∂μ) = ∫ x in s, p (f x) ∂μ := hcomm0.symm
    rw [← hcommeq, hpq]
    exact hker
  have hpf : Integrable (fun x => p (f x)) μ := p.integrable_comp hf
  exact hpf.ae_eq_zero_of_forall_setIntegral_eq_zero hzero

/-- N8 (convexity): the Lyapunov range is convex, via the bang-bang principle (N7). -/
private theorem lyapunovRange_convex {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : α → E) (hf : Integrable f μ) :
    Convex ℝ (lyapunovRange (μ := μ) (f := f)) := by
  intro y1 hy1 y2 hy2 a b ha hb hab
  obtain ⟨s1, hs1, rfl⟩ := hy1
  obtain ⟨s2, hs2, rfl⟩ := hy2
  set g : α → ℝ :=
    fun x => a * (s1.indicator (1 : α → ℝ) x) + b * (s2.indicator (1 : α → ℝ) x)
    with hgdef
  have h1meas : Measurable (s1.indicator (1 : α → ℝ)) :=
    measurable_one.indicator hs1
  have h2meas : Measurable (s2.indicator (1 : α → ℝ)) :=
    measurable_one.indicator hs2
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact (measurable_const.mul h1meas).add (measurable_const.mul h2meas)
  have h1le : ∀ x, s1.indicator (1 : α → ℝ) x ≤ 1 := by
    intro x
    by_cases hx : x ∈ s1
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le_one
  have h2le : ∀ x, s2.indicator (1 : α → ℝ) x ≤ 1 := by
    intro x
    by_cases hx : x ∈ s2
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le_one
  have h1nn : ∀ x, 0 ≤ s1.indicator (1 : α → ℝ) x := by
    intro x
    by_cases hx : x ∈ s1
    · rw [Set.indicator_of_mem hx]
      exact zero_le_one
    · rw [Set.indicator_of_notMem hx]
  have h2nn : ∀ x, 0 ≤ s2.indicator (1 : α → ℝ) x := by
    intro x
    by_cases hx : x ∈ s2
    · rw [Set.indicator_of_mem hx]
      exact zero_le_one
    · rw [Set.indicator_of_notMem hx]
  have hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    simp only [hgdef]
    constructor
    · have h1 : 0 ≤ a * (s1.indicator (1 : α → ℝ) x) :=
        mul_nonneg ha (h1nn x)
      have h2 : 0 ≤ b * (s2.indicator (1 : α → ℝ) x) :=
        mul_nonneg hb (h2nn x)
      linarith
    · have h1 : a * (s1.indicator (1 : α → ℝ) x) ≤ a * 1 :=
        mul_le_mul_of_nonneg_left (h1le x) ha
      have h2 : b * (s2.indicator (1 : α → ℝ) x) ≤ b * 1 :=
        mul_le_mul_of_nonneg_left (h2le x) hb
      linarith [hab]
  obtain ⟨s, hs, hseq⟩ :=
    exists_set_integral_eq_integral_smul hA f hf g hgmeas hg01
  refine ⟨s, hs, ?_⟩
  rw [hseq]
  have hF1 : (fun x => s1.indicator (1 : α → ℝ) x • f x) = s1.indicator f := by
    funext x
    by_cases hx : x ∈ s1
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_smul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
  have hF2 : (fun x => s2.indicator (1 : α → ℝ) x • f x) = s2.indicator f := by
    funext x
    by_cases hx : x ∈ s2
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_smul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
  have hint1 : Integrable (fun x => s1.indicator (1 : α → ℝ) x • f x) μ := by
    rw [hF1]
    exact hf.indicator hs1
  have hint2 : Integrable (fun x => s2.indicator (1 : α → ℝ) x • f x) μ := by
    rw [hF2]
    exact hf.indicator hs2
  have hfun : (fun x => g x • f x) = fun x =>
      a • (s1.indicator (1 : α → ℝ) x • f x) +
      b • (s2.indicator (1 : α → ℝ) x • f x) := by
    funext x
    simp only [hgdef]
    rw [add_smul, mul_smul, mul_smul]
  have hint1' : Integrable (fun x => a • (s1.indicator (1 : α → ℝ) x • f x)) μ :=
    hint1.smul a
  have hint2' : Integrable (fun x => b • (s2.indicator (1 : α → ℝ) x • f x)) μ :=
    hint2.smul b
  rw [hfun, integral_add hint1' hint2', integral_smul a _, integral_smul b _]
  have he1 : (∫ x, s1.indicator (1 : α → ℝ) x • f x ∂μ) = ∫ x in s1, f x ∂μ := by
    rw [hF1]
    exact integral_indicator hs1
  have he2 : (∫ x, s2.indicator (1 : α → ℝ) x • f x ∂μ) = ∫ x in s2, f x ∂μ := by
    rw [hF2]
    exact integral_indicator hs2
  rw [he1, he2]

/-- N12: integrals over sets where an integrable weight is small are small. -/
private theorem lyapunov_tendsto_setIntegral_zero_of_weight {α : Type*}
    [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) (hf : Integrable f μ)
    (w : α → ℝ) (hwmeas : Measurable w) (hwint : Integrable w μ)
    (A : ℕ → Set α) (hAmeas : ∀ n, MeasurableSet (A n))
    (hApos : ∀ n, ∀ x ∈ A n, 0 < w x)
    (hlim : Tendsto (fun n => ∫ x in A n, w x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in A n, f x ∂μ) atTop (𝓝 0) := by
  set S : Set α := { x | 0 < w x } with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const hwmeas
  have hAsub : ∀ n, A n ⊆ S := by
    intro n x hx
    exact hApos n x hx
  set H : ℕ → α → ℝ :=
    fun k => S.indicator (fun x => max (‖f x‖ - (k : ℝ) * w x) 0) with hHdef
  have hHnonneg : ∀ k x, 0 ≤ H k x := by
    intro k x
    rw [hHdef]
    simp only
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact le_max_right _ _
    · rw [Set.indicator_of_notMem hx]
  have hHsub : ∀ k : ℕ, Integrable (fun x => ‖f x‖ - (k : ℝ) * w x) μ :=
    fun k => hf.norm.sub (hwint.const_mul (k : ℝ))
  have hHint : ∀ k : ℕ, Integrable (H k) μ := by
    intro k
    rw [hHdef]
    simp only
    exact (hHsub k).pos_part.indicator hSmeas
  have hHle : ∀ (k : ℕ) (x : α), H k x ≤ ‖f x‖ := by
    intro k x
    rw [hHdef]
    simp only
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      have hxw : 0 ≤ (k : ℝ) * w x := by
        apply mul_nonneg (Nat.cast_nonneg k)
        exact le_of_lt hx
      calc max (‖f x‖ - (k : ℝ) * w x) 0
          ≤ max (‖f x‖) 0 := max_le_max (by linarith) le_rfl
          _ = ‖f x‖ := max_eq_left (norm_nonneg _)
    · rw [Set.indicator_of_notMem hx]
      exact norm_nonneg _
  have hHmeas : ∀ k, AEStronglyMeasurable (H k) μ :=
    fun k => (hHint k).aestronglyMeasurable
  have hHbound : ∀ k, ∀ᵐ x ∂μ, ‖H k x‖ ≤ ‖f x‖ := by
    intro k
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hHnonneg k x)]
    exact hHle k x
  have hHeq : ∀ (x : α), x ∈ S → ∀ᶠ k in atTop, H k x = 0 := by
    intro x hx
    have hxw : 0 < w x := hx
    obtain ⟨k0, hk0⟩ := exists_nat_gt (‖f x‖ / w x)
    filter_upwards [eventually_ge_atTop k0] with k hk
    rw [hHdef]
    simp only
    rw [Set.indicator_of_mem hx]
    have hkle : (k0 : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    have hlt : ‖f x‖ < (k0 : ℝ) * w x := by
      have h1 : ‖f x‖ / w x * w x < (k0 : ℝ) * w x :=
        mul_lt_mul_of_pos_right hk0 hxw
      rwa [div_mul_cancel₀ _ (ne_of_gt hxw)] at h1
    have hle : ‖f x‖ - (k : ℝ) * w x ≤ 0 := by
      have h2 : (k0 : ℝ) * w x ≤ (k : ℝ) * w x :=
        mul_le_mul_of_nonneg_right hkle (le_of_lt hxw)
      linarith
    exact max_eq_right hle
  have hHlim : ∀ᵐ x ∂μ, Tendsto (fun k => H k x) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ S
    · exact tendsto_const_nhds.congr' ((hHeq x hx).mono fun k hk => hk.symm)
    · have heq : (fun k => H k x) = fun _ => (0 : ℝ) := by
        funext k
        rw [hHdef]
        simp only
        exact Set.indicator_of_notMem hx _
      rw [heq]
      exact tendsto_const_nhds
  have hHtends : Tendsto (fun k => ∫ x, H k x ∂μ) atTop (𝓝 0) := by
    have h :=
      tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
        hHmeas hf.norm hHbound hHlim
    simpa using h
  have hNorm : Tendsto (fun n => ∫ x in A n, ‖f x‖ ∂μ) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hHtends (ε / 2) hε2)
    have hKmem : dist (∫ x, H K x ∂μ) 0 < ε / 2 := hK K le_rfl
    have hHintK_nonneg : 0 ≤ ∫ x, H K x ∂μ :=
      integral_nonneg_of_ae (Eventually.of_forall fun x => hHnonneg K x)
    have hHKlt : ∫ x, H K x ∂μ < ε / 2 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hHintK_nonneg] at hKmem
      exact hKmem
    have hKlim : Tendsto (fun n => (K : ℝ) * ∫ x in A n, w x ∂μ) atTop (𝓝 0) := by
      have h := Filter.Tendsto.const_mul (K : ℝ) hlim
      simpa using h
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hKlim (ε / 2) hε2)
    refine ⟨N, fun n hn => ?_⟩
    have hWnn : 0 ≤ ∫ x in A n, w x ∂μ :=
      setIntegral_nonneg (hAmeas n) (fun x hx => le_of_lt (hApos n x hx))
    have hFnn : 0 ≤ ∫ x in A n, ‖f x‖ ∂μ :=
      setIntegral_nonneg (hAmeas n) (fun x _ => norm_nonneg _)
    have hKnn : 0 ≤ (K : ℝ) * ∫ x in A n, w x ∂μ :=
      mul_nonneg (Nat.cast_nonneg K) hWnn
    have hdistK : dist ((K : ℝ) * ∫ x in A n, w x ∂μ) 0 < ε / 2 := hN n hn
    have hKlt : (K : ℝ) * ∫ x in A n, w x ∂μ < ε / 2 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hKnn] at hdistK
      exact hdistK
    have hle : ∫ x in A n, ‖f x‖ ∂μ
        ≤ (K : ℝ) * ∫ x in A n, w x ∂μ + ∫ x, H K x ∂μ := by
      have hsub1 : ∀ x ∈ A n, ‖f x‖ ≤ (K : ℝ) * w x + H K x := by
        intro x hx
        have hxS : x ∈ S := hAsub n hx
        have hHval : H K x = max (‖f x‖ - (K : ℝ) * w x) 0 := by
          rw [hHdef]
          simp only
          exact Set.indicator_of_mem hxS _
        linarith [le_max_left (‖f x‖ - (K : ℝ) * w x) (0 : ℝ), hHval]
      have hF_on : IntegrableOn (fun x => ‖f x‖) (A n) μ := hf.norm.integrableOn
      have hW_on : IntegrableOn (fun x => (K : ℝ) * w x) (A n) μ :=
        (hwint.const_mul (K : ℝ)).integrableOn
      have hH_on : IntegrableOn (H K) (A n) μ := (hHint K).integrableOn
      have hG_on : IntegrableOn (fun x => (K : ℝ) * w x + H K x) (A n) μ :=
        hW_on.add hH_on
      have hmono : ∫ x in A n, ‖f x‖ ∂μ
          ≤ ∫ x in A n, ((K : ℝ) * w x + H K x) ∂μ :=
        setIntegral_mono_on hF_on hG_on (hAmeas n) hsub1
      have hsplit : ∫ x in A n, ((K : ℝ) * w x + H K x) ∂μ
          = (K : ℝ) * ∫ x in A n, w x ∂μ + ∫ x in A n, H K x ∂μ := by
        have hadd := integral_add hW_on hH_on
        have hmul : ∫ x in A n, (K : ℝ) * w x ∂μ
            = (K : ℝ) * ∫ x in A n, w x ∂μ :=
          integral_const_mul (K : ℝ) (fun x => w x)
        rw [hadd, hmul]
      have hleH : ∫ x in A n, H K x ∂μ ≤ ∫ x, H K x ∂μ :=
        setIntegral_le_integral (hHint K)
          (Eventually.of_forall fun x => hHnonneg K x)
      linarith
    have hlt : ∫ x in A n, ‖f x‖ ∂μ < ε := by linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hFnn]
    exact hlt
  exact squeeze_zero_norm (fun n => norm_integral_le_integral_norm _) hNorm

/-- N13: a supporting face reduces to the zero set of the functional. -/
private theorem lyapunovRange_face {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (hf : Integrable f μ) (hfs : StronglyMeasurable f)
    (p : E →L[ℝ] ℝ) (y : E)
    (hy : y ∈ closure (lyapunovRange (μ := μ) (f := f)))
    (hle : ∀ z ∈ lyapunovRange (μ := μ) (f := f), p z ≤ p y) :
    y - ∫ x in { x | 0 < p (f x) }, f x ∂μ ∈
      closure (lyapunovRange (μ.restrict { x | p (f x) = 0 }) (f := f)) := by
  set P : Set α := { x | 0 < p (f x) } with hPdef
  set N : Set α := { x | p (f x) < 0 } with hNdef
  set Z : Set α := { x | p (f x) = 0 } with hZdef
  set w : α → ℝ := fun x => |p (f x)| with hwdef
  have hg_strong : StronglyMeasurable (fun x => p (f x)) :=
    p.continuous.comp_stronglyMeasurable hfs
  have hg_meas : Measurable (fun x => p (f x)) := hg_strong.measurable
  have hPmeas : MeasurableSet P := by
    rw [hPdef]
    exact measurableSet_lt measurable_const hg_meas
  have hNmeas : MeasurableSet N := by
    rw [hNdef]
    exact measurableSet_lt hg_meas measurable_const
  have hZmeas : MeasurableSet Z := by
    rw [hZdef]
    exact measurableSet_eq_fun hg_meas measurable_const
  have hg_int : Integrable (fun x => p (f x)) μ := p.integrable_comp hf
  have hwmeas : Measurable w := by
    rw [hwdef]
    exact continuous_abs.measurable.comp hg_meas
  have hwint : Integrable w μ := by
    rw [hwdef]
    exact hg_int.abs
  have _hfinR : IsFiniteMeasure (μ.restrict Z) :=
    isFiniteMeasure_restrict.mpr (measure_lt_top μ Z).ne
  have hPN : Disjoint P N := by
    apply Set.disjoint_left.mpr
    intro x hxP hxN
    rw [hPdef] at hxP
    rw [hNdef] at hxN
    simp only [Set.mem_ofPred_eq] at hxP hxN
    linarith
  have hPZ : Disjoint P Z := by
    apply Set.disjoint_left.mpr
    intro x hxP hxZ
    rw [hPdef] at hxP
    rw [hZdef] at hxZ
    simp only [Set.mem_ofPred_eq] at hxP hxZ
    linarith
  have hNZ : Disjoint N Z := by
    apply Set.disjoint_left.mpr
    intro x hxN hxZ
    rw [hNdef] at hxN
    rw [hZdef] at hxZ
    simp only [Set.mem_ofPred_eq] at hxN hxZ
    linarith
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hy
  have hmem : ∀ n, ∃ s, MeasurableSet s ∧ u n = ∫ x in s, f x ∂μ := by
    intro n
    have h := hu_mem n
    simp only [lyapunovRange, Set.mem_ofPred_eq] at h
    exact h
  choose s hsmeas heq using hmem
  have hlim : Tendsto (fun n => ∫ x in s n, f x ∂μ) atTop (𝓝 y) := by
    have hfun : (fun n => ∫ x in s n, f x ∂μ) = u :=
      funext fun n => (heq n).symm
    rw [hfun]
    exact hu_lim
  have hcomm : ∀ t : Set α, p (∫ x in t, f x ∂μ) = ∫ x in t, p (f x) ∂μ := by
    intro t
    have hfr : Integrable f (μ.restrict t) := hf.restrict
    exact (p.integral_comp_comm hfr).symm
  have hleP : ∀ t : Set α, MeasurableSet t →
      p (∫ x in t, f x ∂μ) ≤ p (∫ x in P, f x ∂μ) := by
    intro t ht
    rw [hcomm t, hcomm P]
    have htP : MeasurableSet (t ∩ P) := ht.inter hPmeas
    have htD : MeasurableSet (t \ P) := ht.diff hPmeas
    have hPD : MeasurableSet (P \ t) := hPmeas.diff ht
    have hPt : MeasurableSet (P ∩ t) := hPmeas.inter ht
    have hdisj1 : Disjoint (t ∩ P) (t \ P) := by
      apply Set.disjoint_left.mpr
      intro x hx1 hx2
      exact hx2.2 hx1.2
    have hun1 : (t ∩ P) ∪ (t \ P) = t := Set.inter_union_sdiff t P
    have hdisj2 : Disjoint (P ∩ t) (P \ t) := by
      apply Set.disjoint_left.mpr
      intro x hx1 hx2
      exact hx2.2 hx1.2
    have hun2 : (P ∩ t) ∪ (P \ t) = P := Set.inter_union_sdiff P t
    have hg_on_tP : IntegrableOn (fun x => p (f x)) (t ∩ P) μ :=
      hg_int.integrableOn
    have hg_on_tD : IntegrableOn (fun x => p (f x)) (t \ P) μ :=
      hg_int.integrableOn
    have hg_on_Pt : IntegrableOn (fun x => p (f x)) (P ∩ t) μ :=
      hg_int.integrableOn
    have hg_on_PD : IntegrableOn (fun x => p (f x)) (P \ t) μ :=
      hg_int.integrableOn
    have ht_eq : ∫ x in t, p (f x) ∂μ
        = ∫ x in t ∩ P, p (f x) ∂μ + ∫ x in t \ P, p (f x) ∂μ := by
      have h := setIntegral_union hdisj1 htD hg_on_tP hg_on_tD
      rwa [hun1] at h
    have hP_eq : ∫ x in P, p (f x) ∂μ
        = ∫ x in P ∩ t, p (f x) ∂μ + ∫ x in P \ t, p (f x) ∂μ := by
      have h := setIntegral_union hdisj2 hPD hg_on_Pt hg_on_PD
      rwa [hun2] at h
    have htP_eq : ∫ x in t ∩ P, p (f x) ∂μ = ∫ x in P ∩ t, p (f x) ∂μ := by
      rw [Set.inter_comm t P]
    have hnonpos : ∫ x in t \ P, p (f x) ∂μ ≤ 0 := by
      apply setIntegral_nonpos htD
      intro x hx
      have hnp : ¬ (0 < p (f x)) := by
        intro hlt
        exact hx.2 (by rw [hPdef]; simp only [Set.mem_ofPred_eq]; exact hlt)
      exact not_lt.mp hnp
    have hnonneg : 0 ≤ ∫ x in P \ t, p (f x) ∂μ := by
      apply setIntegral_nonneg hPD
      intro x hx
      have hxP : x ∈ P := hx.1
      rw [hPdef] at hxP
      simp only [Set.mem_ofPred_eq] at hxP
      exact le_of_lt hxP
    linarith
  have hmemP : (∫ x in P, f x ∂μ) ∈ lyapunovRange (μ := μ) (f := f) :=
    ⟨P, hPmeas, rfl⟩
  have hlePy : p (∫ x in P, f x ∂μ) ≤ p y := hle _ hmemP
  have hcont : Tendsto (fun n => p (∫ x in s n, f x ∂μ)) atTop (𝓝 (p y)) :=
    (p.continuous.tendsto _).comp hlim
  have hleY : p y ≤ p (∫ x in P, f x ∂μ) := by
    have hle_n : ∀ n, p (∫ x in s n, f x ∂μ) ≤ p (∫ x in P, f x ∂μ) :=
      fun n => hleP (s n) (hsmeas n)
    exact le_of_tendsto hcont (Eventually.of_forall hle_n)
  have heqPy : p y = p (∫ x in P, f x ∂μ) := le_antisymm hleY hlePy
  have hcontP : Tendsto (fun n => p (∫ x in s n, f x ∂μ)) atTop
      (𝓝 (p (∫ x in P, f x ∂μ))) := by
    rw [← heqPy]
    exact hcont
  have hdiff : Tendsto
      (fun n => p (∫ x in P, f x ∂μ) - p (∫ x in s n, f x ∂μ)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := p (∫ x in P, f x ∂μ))).sub hcontP
    simpa using h
  have hwval : ∀ x, w x = |p (f x)| := fun x => by rw [hwdef]
  have hPw_eq : ∀ n, ∫ x in P \ s n, p (f x) ∂μ = ∫ x in P \ s n, w x ∂μ := by
    intro n
    apply setIntegral_congr_fun (hPmeas.diff (hsmeas n))
    intro x hx
    have hxP : 0 < p (f x) := by
      have h : x ∈ P := hx.1
      rw [hPdef] at h
      simp only [Set.mem_ofPred_eq] at h
      exact h
    rw [hwval x, abs_of_pos hxP]
  have hNw_eq : ∀ n, ∫ x in s n ∩ N, p (f x) ∂μ
      = -(∫ x in s n ∩ N, w x ∂μ) := by
    intro n
    have hcongr : ∫ x in s n ∩ N, p (f x) ∂μ
        = ∫ x in s n ∩ N, (-(w x)) ∂μ := by
      apply setIntegral_congr_fun ((hsmeas n).inter hNmeas)
      intro x hx
      have hxN : p (f x) < 0 := by
        have h : x ∈ N := hx.2
        rw [hNdef] at h
        simp only [Set.mem_ofPred_eq] at h
        exact h
      have hw : w x = |p (f x)| := hwval x
      change p (f x) = -w x
      rw [hw, abs_of_neg hxN, neg_neg]
    rw [hcongr, integral_neg]
  have hZzero : ∀ n, ∫ x in s n ∩ Z, p (f x) ∂μ = 0 := by
    intro n
    have hcongr : ∫ x in s n ∩ Z, p (f x) ∂μ = ∫ x in s n ∩ Z, (0 : ℝ) ∂μ := by
      apply setIntegral_congr_fun ((hsmeas n).inter hZmeas)
      intro x hx
      have hzx : x ∈ Z := hx.2
      rw [hZdef] at hzx
      simp only [Set.mem_ofPred_eq] at hzx
      exact hzx
    rw [hcongr]
    exact integral_zero _ _
  have hsum_eq : ∀ n, p (∫ x in P, f x ∂μ) - p (∫ x in s n, f x ∂μ)
      = ∫ x in P \ s n, w x ∂μ + ∫ x in s n ∩ N, w x ∂μ := by
    intro n
    rw [hcomm P, hcomm (s n)]
    have htP : MeasurableSet (s n ∩ P) := (hsmeas n).inter hPmeas
    have htD : MeasurableSet (s n \ P) := (hsmeas n).diff hPmeas
    have hPD : MeasurableSet (P \ s n) := hPmeas.diff (hsmeas n)
    have hPt : MeasurableSet (P ∩ s n) := hPmeas.inter (hsmeas n)
    have hNN : MeasurableSet (s n ∩ N) := (hsmeas n).inter hNmeas
    have hZZ : MeasurableSet (s n ∩ Z) := (hsmeas n).inter hZmeas
    have hg_on_sP : IntegrableOn (fun x => p (f x)) (s n ∩ P) μ :=
      hg_int.integrableOn
    have hg_on_sD : IntegrableOn (fun x => p (f x)) (s n \ P) μ :=
      hg_int.integrableOn
    have hg_on_Pt : IntegrableOn (fun x => p (f x)) (P ∩ s n) μ :=
      hg_int.integrableOn
    have hg_on_PD : IntegrableOn (fun x => p (f x)) (P \ s n) μ :=
      hg_int.integrableOn
    have hg_on_NN : IntegrableOn (fun x => p (f x)) (s n ∩ N) μ :=
      hg_int.integrableOn
    have hg_on_ZZ : IntegrableOn (fun x => p (f x)) (s n ∩ Z) μ :=
      hg_int.integrableOn
    have hdisj_sP : Disjoint (s n ∩ P) (s n \ P) := by
      apply Set.disjoint_left.mpr
      intro x hx1 hx2
      exact hx2.2 hx1.2
    have hun_s : (s n ∩ P) ∪ (s n \ P) = s n :=
      Set.inter_union_sdiff (s n) P
    have hdisj_P : Disjoint (P ∩ s n) (P \ s n) := by
      apply Set.disjoint_left.mpr
      intro x hx1 hx2
      exact hx2.2 hx1.2
    have hun_P : (P ∩ s n) ∪ (P \ s n) = P :=
      Set.inter_union_sdiff P (s n)
    have hs_eq : ∫ x in s n, p (f x) ∂μ
        = ∫ x in s n ∩ P, p (f x) ∂μ + ∫ x in s n \ P, p (f x) ∂μ := by
      have h := setIntegral_union hdisj_sP htD hg_on_sP hg_on_sD
      rwa [hun_s] at h
    have hP_eq : ∫ x in P, p (f x) ∂μ
        = ∫ x in P ∩ s n, p (f x) ∂μ + ∫ x in P \ s n, p (f x) ∂μ := by
      have h := setIntegral_union hdisj_P hPD hg_on_Pt hg_on_PD
      rwa [hun_P] at h
    have hsplitD : (s n \ P) = (s n ∩ N) ∪ (s n ∩ Z) := by
      apply Set.ext
      intro x
      constructor
      · intro hx
        have hle : p (f x) ≤ 0 := by
          have hnp : ¬ (0 < p (f x)) := fun hlt =>
            hx.2 (by rw [hPdef]; simp only [Set.mem_ofPred_eq]; exact hlt)
          exact not_lt.mp hnp
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Or.inl (by exact ⟨hx.1, by
            rw [hNdef]; simp only [Set.mem_ofPred_eq]; exact hlt⟩)
        · exact Or.inr (by exact ⟨hx.1, by
            rw [hZdef]; simp only [Set.mem_ofPred_eq]; exact heq⟩)
      · intro hx
        rcases hx with hxN | hxZ
        · refine ⟨hxN.1, ?_⟩
          intro hP
          have hxP : 0 < p (f x) := by
            rw [hPdef] at hP
            simp only [Set.mem_ofPred_eq] at hP
            exact hP
          have hxNN : p (f x) < 0 := by
            have h : x ∈ N := hxN.2
            rw [hNdef] at h
            simp only [Set.mem_ofPred_eq] at h
            exact h
          linarith
        · refine ⟨hxZ.1, ?_⟩
          intro hP
          have hxP : 0 < p (f x) := by
            rw [hPdef] at hP
            simp only [Set.mem_ofPred_eq] at hP
            exact hP
          have hxZZ : p (f x) = 0 := by
            have h : x ∈ Z := hxZ.2
            rw [hZdef] at h
            simp only [Set.mem_ofPred_eq] at h
            exact h
          linarith
    have hdisj_NZ : Disjoint (s n ∩ N) (s n ∩ Z) :=
      Disjoint.mono Set.inter_subset_right Set.inter_subset_right hNZ
    have hg_on_sDD : IntegrableOn (fun x => p (f x)) (s n \ P) μ :=
      hg_int.integrableOn
    have hD_eq : ∫ x in s n \ P, p (f x) ∂μ
        = ∫ x in s n ∩ N, p (f x) ∂μ + ∫ x in s n ∩ Z, p (f x) ∂μ := by
      have h := setIntegral_union hdisj_NZ hZZ hg_on_NN hg_on_ZZ
      rwa [← hsplitD] at h
    have hinter_eq : ∫ x in s n ∩ P, p (f x) ∂μ
        = ∫ x in P ∩ s n, p (f x) ∂μ := by
      rw [Set.inter_comm (s n) P]
    rw [hP_eq, hs_eq, hD_eq, hZzero n, hPw_eq n, hNw_eq n] at ⊢
    rw [hinter_eq]
    ring
  have hsum_lim : Tendsto
      (fun n => ∫ x in P \ s n, w x ∂μ + ∫ x in s n ∩ N, w x ∂μ) atTop
      (𝓝 0) := by
    have h := hdiff
    simpa [hsum_eq] using h
  have hPnonneg : ∀ n, 0 ≤ ∫ x in P \ s n, w x ∂μ := by
    intro n
    apply setIntegral_nonneg (hPmeas.diff (hsmeas n))
    intro x _
    rw [hwval x]
    exact abs_nonneg _
  have hNnonneg : ∀ n, 0 ≤ ∫ x in s n ∩ N, w x ∂μ := by
    intro n
    apply setIntegral_nonneg ((hsmeas n).inter hNmeas)
    intro x _
    rw [hwval x]
    exact abs_nonneg _
  have hPlim : Tendsto (fun n => ∫ x in P \ s n, w x ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => hPnonneg n)
      (fun n => le_add_of_nonneg_right (hNnonneg n)) hsum_lim
  have hNlim : Tendsto (fun n => ∫ x in s n ∩ N, w x ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => hNnonneg n)
      (fun n => le_add_of_nonneg_left (hPnonneg n)) hsum_lim
  have hPf_lim : Tendsto (fun n => ∫ x in P \ s n, f x ∂μ) atTop (𝓝 0) := by
    apply lyapunov_tendsto_setIntegral_zero_of_weight f hf w hwmeas hwint
      (fun n => P \ s n) (fun n => hPmeas.diff (hsmeas n)) _ hPlim
    intro n x hx
    have hxP : 0 < p (f x) := by
      have h : x ∈ P := hx.1
      rw [hPdef] at h
      simp only [Set.mem_ofPred_eq] at h
      exact h
    rw [hwval x]
    exact abs_pos.mpr (ne_of_gt hxP)
  have hNf_lim : Tendsto (fun n => ∫ x in s n ∩ N, f x ∂μ) atTop (𝓝 0) := by
    apply lyapunov_tendsto_setIntegral_zero_of_weight f hf w hwmeas hwint
      (fun n => s n ∩ N) (fun n => (hsmeas n).inter hNmeas) _ hNlim
    intro n x hx
    have hxN : p (f x) < 0 := by
      have h : x ∈ N := hx.2
      rw [hNdef] at h
      simp only [Set.mem_ofPred_eq] at h
      exact h
    rw [hwval x]
    exact abs_pos.mpr (ne_of_lt hxN)
  have hZlim : Tendsto (fun n => ∫ x in s n ∩ Z, f x ∂μ) atTop
      (𝓝 (y - ∫ x in P, f x ∂μ)) := by
    have hIP : IntegrableOn f P μ := hf.integrableOn
    have hIs : ∀ n, IntegrableOn f (s n) μ := fun n => hf.integrableOn
    have hIPin : ∀ n, IntegrableOn f (s n ∩ P) μ := fun n => hf.integrableOn
    have hINN : ∀ n, IntegrableOn f (s n ∩ N) μ := fun n => hf.integrableOn
    have hIZZ : ∀ n, IntegrableOn f (s n ∩ Z) μ := fun n => hf.integrableOn
    have hIPout : ∀ n, IntegrableOn f (P \ s n) μ := fun n => hf.integrableOn
    have hIPt : ∀ n, IntegrableOn f (P ∩ s n) μ := fun n => hf.integrableOn
    have hIsD : ∀ n, IntegrableOn f (s n \ P) μ := fun n => hf.integrableOn
    have hmD : ∀ n, MeasurableSet (s n \ P) := fun n => (hsmeas n).diff hPmeas
    have hmPD : ∀ n, MeasurableSet (P \ s n) := fun n => hPmeas.diff (hsmeas n)
    have hmZZ : ∀ n, MeasurableSet (s n ∩ Z) := fun n => (hsmeas n).inter hZmeas
    have heq_all : ∀ n, ∫ x in s n ∩ Z, f x ∂μ
        = (∫ x in s n, f x ∂μ - ∫ x in P, f x ∂μ)
          + ∫ x in P \ s n, f x ∂μ - ∫ x in s n ∩ N, f x ∂μ := by
      intro n
      have hdisj_sP : Disjoint (s n ∩ P) (s n \ P) := by
        apply Set.disjoint_left.mpr
        intro x hx1 hx2
        exact hx2.2 hx1.2
      have hun_s : (s n ∩ P) ∪ (s n \ P) = s n :=
        Set.inter_union_sdiff (s n) P
      have hdisj_P : Disjoint (P ∩ s n) (P \ s n) := by
        apply Set.disjoint_left.mpr
        intro x hx1 hx2
        exact hx2.2 hx1.2
      have hun_P : (P ∩ s n) ∪ (P \ s n) = P :=
        Set.inter_union_sdiff P (s n)
      have hsplitD : (s n \ P) = (s n ∩ N) ∪ (s n ∩ Z) := by
        apply Set.ext
        intro x
        constructor
        · intro hx
          have hle : p (f x) ≤ 0 := by
            have hnp : ¬ (0 < p (f x)) := fun hlt =>
              hx.2 (by rw [hPdef]; simp only [Set.mem_ofPred_eq]; exact hlt)
            exact not_lt.mp hnp
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact Or.inl (by exact ⟨hx.1, by
              rw [hNdef]; simp only [Set.mem_ofPred_eq]; exact hlt⟩)
          · exact Or.inr (by exact ⟨hx.1, by
              rw [hZdef]; simp only [Set.mem_ofPred_eq]; exact heq⟩)
        · intro hx
          rcases hx with hxN | hxZ
          · refine ⟨hxN.1, ?_⟩
            intro hP
            have hxP : 0 < p (f x) := by
              rw [hPdef] at hP
              simp only [Set.mem_ofPred_eq] at hP
              exact hP
            have hxNN : p (f x) < 0 := by
              have h : x ∈ N := hxN.2
              rw [hNdef] at h
              simp only [Set.mem_ofPred_eq] at h
              exact h
            linarith
          · refine ⟨hxZ.1, ?_⟩
            intro hP
            have hxP : 0 < p (f x) := by
              rw [hPdef] at hP
              simp only [Set.mem_ofPred_eq] at hP
              exact hP
            have hxZZ : p (f x) = 0 := by
              have h : x ∈ Z := hxZ.2
              rw [hZdef] at h
              simp only [Set.mem_ofPred_eq] at h
              exact h
            linarith
      have hdisj_NZ : Disjoint (s n ∩ N) (s n ∩ Z) :=
        Disjoint.mono Set.inter_subset_right Set.inter_subset_right hNZ
      have hs_eq : ∫ x in s n, f x ∂μ
          = ∫ x in s n ∩ P, f x ∂μ + ∫ x in s n \ P, f x ∂μ := by
        have h := setIntegral_union hdisj_sP (hmD n) (hIPin n) (hIsD n)
        rwa [hun_s] at h
      have hP_eq : ∫ x in P, f x ∂μ
          = ∫ x in P ∩ s n, f x ∂μ + ∫ x in P \ s n, f x ∂μ := by
        have h := setIntegral_union hdisj_P (hmPD n) (hIPt n) (hIPout n)
        rwa [hun_P] at h
      have hD_eq : ∫ x in s n \ P, f x ∂μ
          = ∫ x in s n ∩ N, f x ∂μ + ∫ x in s n ∩ Z, f x ∂μ := by
        have h := setIntegral_union hdisj_NZ (hmZZ n) (hINN n) (hIZZ n)
        rwa [← hsplitD] at h
      have hinter_eq : ∫ x in s n ∩ P, f x ∂μ
          = ∫ x in P ∩ s n, f x ∂μ := by
        rw [Set.inter_comm (s n) P]
      rw [hs_eq, hD_eq, hP_eq, hinter_eq] at ⊢
      abel
    have hRHS : Tendsto
        (fun n => (∫ x in s n, f x ∂μ - ∫ x in P, f x ∂μ)
          + ∫ x in P \ s n, f x ∂μ - ∫ x in s n ∩ N, f x ∂μ) atTop
        (𝓝 (y - ∫ x in P, f x ∂μ)) := by
      have h1 : Tendsto (fun n => ∫ x in s n, f x ∂μ - ∫ x in P, f x ∂μ) atTop
          (𝓝 (y - ∫ x in P, f x ∂μ)) :=
        hlim.sub tendsto_const_nhds
      have h2 := h1.add hPf_lim
      have h3 := h2.sub hNf_lim
      simpa using h3
    exact hRHS.congr fun n => (heq_all n).symm
  have hmem_each : ∀ n, (∫ x in s n, f x ∂(μ.restrict Z)) ∈
      lyapunovRange (μ.restrict Z) (f := f) := fun n => ⟨s n, hsmeas n, rfl⟩
  have htrans : ∀ n, ∫ x in s n, f x ∂(μ.restrict Z)
      = ∫ x in s n ∩ Z, f x ∂μ := by
    intro n
    have hrr : (μ.restrict Z).restrict (s n) = μ.restrict (s n ∩ Z) :=
      Measure.restrict_restrict (hsmeas n)
    change ∫ x, f x ∂((μ.restrict Z).restrict (s n))
      = ∫ x, f x ∂(μ.restrict (s n ∩ Z))
    rw [hrr]
  have hlimZ : Tendsto (fun n => ∫ x in s n, f x ∂(μ.restrict Z)) atTop
      (𝓝 (y - ∫ x in P, f x ∂μ)) := by
    simpa [htrans] using hZlim
  exact mem_closure_of_tendsto hlimZ (Eventually.of_forall hmem_each)

/-- N15: the Lyapunov range is closed, by induction on the dimension. -/
private theorem lyapunovRange_isClosed {α : Type*} [MeasurableSpace α] :
    ∀ (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E],
      Module.finrank ℝ E = n →
      ∀ (μ : Measure α) [IsFiniteMeasure μ], IsAtomless μ →
      ∀ (f : α → E), Integrable f μ →
      IsClosed (lyapunovRange (μ := μ) (f := f)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ hrank μ _ hA f hf
    set g : α → E := hf.aestronglyMeasurable.mk f with hgdef
    have hg_strong : StronglyMeasurable g :=
      hf.aestronglyMeasurable.stronglyMeasurable_mk
    have hae : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
    have hg_int : Integrable g μ := hf.congr hae
    have heqR : lyapunovRange (μ := μ) (f := f)
        = lyapunovRange (μ := μ) (f := g) :=
      lyapunovRange_congr_ae hae
    rw [heqR]
    have hconv : Convex ℝ (lyapunovRange (μ := μ) (f := g)) :=
      lyapunovRange_convex hA g hg_int
    by_cases hempty : interior (lyapunovRange (μ := μ) (f := g)) = ∅
    · obtain ⟨p, hpne, hzero⟩ :=
        exists_dual_ae_zero_of_interior_eq_empty g hg_int hconv hempty
      set W : Submodule ℝ E := LinearMap.ker p.toLinearMap with hWdef
      have hWne : W ≠ ⊤ := by
        intro htop
        apply hpne
        have h0 : p.toLinearMap = 0 := LinearMap.ker_eq_top.mp htop
        apply ContinuousLinearMap.ext
        intro x
        have hx : p.toLinearMap x = (0 : E →ₗ[ℝ] ℝ) x := by rw [h0]
        simpa using hx
      have hlt : Module.finrank ℝ W < n := by
        have hlt' : Module.finrank ℝ W < Module.finrank ℝ E :=
          Submodule.finrank_lt hWne
        rw [hrank] at hlt'
        exact hlt'
      have haeW : ∀ᵐ x ∂μ, g x ∈ W := by
        filter_upwards [hzero] with x hx
        change g x ∈ LinearMap.ker p.toLinearMap
        rw [LinearMap.mem_ker]
        exact hx
      obtain ⟨fW, hfWint, heqW⟩ :=
        lyapunovRange_eq_image_subtype W g hg_int haeW
      have hclosedW : IsClosed (lyapunovRange (μ := μ) (f := fW)) :=
        ih _ hlt _ rfl _ hA _ hfWint
      have hclosedImg : IsClosed (W.subtypeL '' lyapunovRange (μ := μ) (f := fW)) :=
        lyapunovRange_isClosed_of_subtype_isClosed W hclosedW
      rw [← heqW] at hclosedImg
      exact hclosedImg
    · have hinter_ne : (interior (lyapunovRange (μ := μ) (f := g))).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hempty
      apply closure_subset_iff_isClosed.mp
      intro y hy
      by_cases hyInt : y ∈ interior (lyapunovRange (μ := μ) (f := g))
      · exact interior_subset hyInt
      · obtain ⟨p, hp⟩ := geometric_hahn_banach_open_point hconv.interior
          isOpen_interior hyInt
        have hpne : p ≠ 0 := by
          intro h0
          obtain ⟨a0, ha0⟩ := hinter_ne
          have hlt := hp a0 ha0
          rw [h0] at hlt
          simp only [zero_apply] at hlt
          exact lt_irrefl _ hlt
        have hle_int : ∀ a ∈ interior (lyapunovRange (μ := μ) (f := g)),
            p a ≤ p y := fun a ha => le_of_lt (hp a ha)
        have hclosed_set : IsClosed { z | p z ≤ p y } :=
          isClosed_le p.continuous continuous_const
        have hsub_int : closure (interior (lyapunovRange (μ := μ) (f := g)))
            ⊆ { z | p z ≤ p y } :=
          closure_minimal (fun x hx => hle_int x hx) hclosed_set
        have hclosure_eq : closure (interior (lyapunovRange (μ := μ) (f := g)))
            = closure (lyapunovRange (μ := μ) (f := g)) :=
          hconv.closure_interior_eq_closure_of_nonempty_interior hinter_ne
        have hle_closure : ∀ z ∈ closure (lyapunovRange (μ := μ) (f := g)),
            p z ≤ p y := by
          intro z hz
          have hz' : z ∈ closure (interior (lyapunovRange (μ := μ) (f := g))) := by
            rw [hclosure_eq]
            exact hz
          have hmem := hsub_int hz'
          simpa using hmem
        have hleR : ∀ z ∈ lyapunovRange (μ := μ) (f := g), p z ≤ p y :=
          fun z hz => hle_closure z (subset_closure hz)
        set P : Set α := { x | 0 < p (g x) } with hPdef
        set Z : Set α := { x | p (g x) = 0 } with hZdef
        have hPmeas : MeasurableSet P := by
          rw [hPdef]
          exact measurableSet_lt measurable_const
            (p.continuous.comp_stronglyMeasurable hg_strong).measurable
        have hZmeas : MeasurableSet Z := by
          rw [hZdef]
          exact measurableSet_eq_fun
            (p.continuous.comp_stronglyMeasurable hg_strong).measurable
            measurable_const
        have hface := lyapunovRange_face g hg_int hg_strong p y hy hleR
        set hW : Submodule ℝ E := LinearMap.ker p.toLinearMap with hWdef
        have hWne : hW ≠ ⊤ := by
          intro htop
          apply hpne
          have h0 : p.toLinearMap = 0 := LinearMap.ker_eq_top.mp htop
          apply ContinuousLinearMap.ext
          intro x
          have hx : p.toLinearMap x = (0 : E →ₗ[ℝ] ℝ) x := by rw [h0]
          simpa using hx
        have hlt : Module.finrank ℝ hW < n := by
          have hlt' : Module.finrank ℝ hW < Module.finrank ℝ E :=
            Submodule.finrank_lt hWne
          rw [hrank] at hlt'
          exact hlt'
        have : IsFiniteMeasure (μ.restrict Z) :=
          isFiniteMeasure_restrict.mpr (measure_lt_top μ Z).ne
        have hAZ : IsAtomless (μ.restrict Z) :=
          isAtomless_restrict hZmeas hA
        have hgR : Integrable g (μ.restrict Z) := hg_int.restrict
        have haeW_Z : ∀ᵐ x ∂(μ.restrict Z), g x ∈ hW := by
          apply ae_restrict_of_forall_mem hZmeas
          intro x hx
          change g x ∈ LinearMap.ker p.toLinearMap
          rw [LinearMap.mem_ker]
          have hzx : x ∈ Z := hx
          rw [hZdef] at hzx
          simp only [Set.mem_ofPred_eq] at hzx
          exact hzx
        obtain ⟨fW, hfWint, heqW⟩ :=
          lyapunovRange_eq_image_subtype hW g hgR haeW_Z
        have hclosedW : IsClosed (lyapunovRange (μ.restrict Z) (f := fW)) :=
          ih _ hlt _ rfl _ hAZ _ hfWint
        have hclosedR : IsClosed (lyapunovRange (μ.restrict Z) (f := g)) := by
          have himg := lyapunovRange_isClosed_of_subtype_isClosed hW hclosedW
          rw [← heqW] at himg
          exact himg
        have hmem : y - ∫ x in P, g x ∂μ ∈
            lyapunovRange (μ.restrict Z) (f := g) :=
          closure_subset_iff_isClosed.mpr hclosedR hface
        obtain ⟨t, htmeas, ht_eq⟩ := hmem
        have htrans : (∫ x in t, g x ∂(μ.restrict Z))
            = ∫ x in t ∩ Z, g x ∂μ := by
          have hrr : (μ.restrict Z).restrict t = μ.restrict (t ∩ Z) :=
            Measure.restrict_restrict htmeas
          change ∫ x, g x ∂((μ.restrict Z).restrict t)
            = ∫ x, g x ∂(μ.restrict (t ∩ Z))
          rw [hrr]
        have hdisj : Disjoint P (t ∩ Z) := by
          apply Set.disjoint_left.mpr
          intro x hxP hxTZ
          have hxZ : x ∈ Z := hxTZ.2
          have hxPZ : x ∈ P ∩ Z := ⟨hxP, hxZ⟩
          have hemptyPZ : P ∩ Z = ∅ :=
            Set.disjoint_iff_inter_eq_empty.mp
              (by
                apply Set.disjoint_left.mpr
                intro a haP haZ
                rw [hPdef] at haP
                rw [hZdef] at haZ
                simp only [Set.mem_ofPred_eq] at haP haZ
                linarith)
          rw [hemptyPZ] at hxPZ
          exact Set.notMem_empty x hxPZ
        have hPUmeas : MeasurableSet (P ∪ (t ∩ Z)) :=
          hPmeas.union (htmeas.inter hZmeas)
        have hP_on : IntegrableOn g P μ := hg_int.integrableOn
        have hTZ_on : IntegrableOn g (t ∩ Z) μ := hg_int.integrableOn
        have hunion_eq : ∫ x in P ∪ (t ∩ Z), g x ∂μ
            = ∫ x in P, g x ∂μ + ∫ x in t ∩ Z, g x ∂μ :=
          setIntegral_union hdisj (htmeas.inter hZmeas) hP_on hTZ_on
        have hy_eq : y = ∫ x in P ∪ (t ∩ Z), g x ∂μ := by
          have h1 : y - ∫ x in P, g x ∂μ = ∫ x in t ∩ Z, g x ∂μ := by
            rw [ht_eq, htrans]
          have h2 : y = ∫ x in P, g x ∂μ + ∫ x in t ∩ Z, g x ∂μ := by
            have hsub : y - ∫ x in P, g x ∂μ + ∫ x in P, g x ∂μ = y :=
              sub_add_cancel y _
            rw [h1] at hsub
            rw [add_comm] at hsub
            exact hsub.symm
          rw [h2, ← hunion_eq]
        exact ⟨P ∪ (t ∩ Z), hPUmeas, hy_eq⟩

/--
**Lyapunov convexity theorem.** Let $\mu$ be a finite atomless measure on a measurable space
$\alpha$, let $E$ be a finite-dimensional real normed space, and let $f : \alpha \to E$ be Bochner
integrable with respect to $\mu$. Then the Lyapunov range of $f$ with respect to $\mu$, the set of
integrals $\int_s f \, d\mu$ over measurable sets $s \subseteq \alpha$, is compact and convex.

Proves `Wanted` entry `lyapunov_convexity`.

Source: A. Lyapunov, Izv. Akad. Nauk SSSR 4
(1940) 465–478; Diestel-Uhl, Vector Measures; Lean states atomless finite measure case with
Bochner integrable finite-dim integrand, infinite-dim fails.
-/
theorem lyapunov_convexity
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (hf : Integrable f μ) (hAtomless : IsAtomless μ) :
    IsCompact (lyapunovRange (μ := μ) (f := f)) ∧
      Convex ℝ (lyapunovRange (μ := μ) (f := f)) := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have hclosed : IsClosed (lyapunovRange (μ := μ) (f := f)) :=
    lyapunovRange_isClosed (Module.finrank ℝ E) E rfl μ hAtomless f hf
  exact ⟨Metric.isCompact_of_isClosed_isBounded hclosed
    (lyapunovRange_isBounded f hf), lyapunovRange_convex hAtomless f hf⟩

end MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted
end
