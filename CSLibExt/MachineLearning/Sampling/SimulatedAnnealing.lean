/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.Sampling.MetropolisHastings
public import MathlibExt.Analysis.SpecialFunctions.LogSumExp

/-!
# Simulated annealing: Gibbs stationarity and Hajek's depth apparatus

For a finite state space with energy `V` and symmetric proposal `R`, the
annealing step at temperature `T` is the Metropolis-Hastings step for the
Gibbs law (`annealStep_eq_mhStep`), so the Gibbs law is stationary at fixed
`T` (`bind_annealStep`) and concentrates on the global minima as `T` tends to
zero (`tendsto_gibbs_globalMinSet`). The depth apparatus follows Bruce
Hajek, "Optimization by simulated annealing: a necessary and sufficient
condition for convergence", in *Adaptive Statistical Procedures and Related
Topics*, IMS Lecture Notes--Monograph Series, vol. 8 (1986), pp. 417--427,
DOI `10.1214/lnms/1215540316`. It is developed from height-bounded
reachability (`ReachableAt`): strong
irreducibility, weak reversibility, local minima, escape depth (`depth`),
and the critical depth `dStar`. The logarithmic schedules used in
Hajek's convergence characterization are specified by
`logSchedule_specs`; that deferred characterization is recorded as a
`theorem_wanted` in
`WantedExt/ComputerScience/MachineLearning/SimulatedAnnealingHajekWanted.lean`.
-/

@[expose] public section

namespace Cslib.MachineLearning.Sampling.SimulatedAnnealing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {S : Type*} [Fintype S] [DecidableEq S] (R : S → PMF S) (V : S → ℝ)

/-- Proposal arc: `t` can be proposed from `s`. -/
def Arc (s t : S) : Prop := R s t ≠ 0

/-- `i` is reachable from `j` along a path staying at height `≤ E`
(endpoints included). -/
def ReachableAt (E : ℝ) (j i : S) : Prop :=
  V j ≤ E ∧ Relation.ReflTransGen (fun a b => Arc R a b ∧ V b ≤ E) j i

/-- Strong irreducibility: every state reaches every other at some height. -/
def StronglyIrreducible : Prop := ∀ i j, ∃ E, ReachableAt R V E j i

/-- Weak reversibility: height reachability is symmetric. -/
def WeaklyReversible : Prop :=
  ∀ (E : ℝ) (i j : S), ReachableAt R V E j i ↔ ReachableAt R V E i j

/-- The global minima `S*`. -/
def globalMinSet : Set S := {s | ∀ t, V s ≤ V t}

/-- A Hajek local minimum: no strictly lower state is reachable at its
own height. -/
def IsHajekLocalMin (s : S) : Prop := ∀ t, V t < V s → ¬ ReachableAt R V (V s) s t

/-- Escape depth (`⊤` when no lower state exists). -/
noncomputable def depth (s : S) : ℝ≥0∞ :=
  ⨅ (E : ℝ) (_ : 0 < E ∧ ∃ t, V t < V s ∧ ReachableAt R V (V s + E) s t), ENNReal.ofReal E

/-- `d*`: the largest depth of a non-global local minimum, `0` if none. -/
noncomputable def dStar : ℝ≥0∞ :=
  ⨆ (s : S) (_ : IsHajekLocalMin R V s ∧ s ∉ globalMinSet V), depth R V s

/-- The Gibbs law at temperature `T`. -/
noncomputable def gibbs [Nonempty S] (T : ℝ) : PMF S :=
  PMF.ofFintype (fun x => ENNReal.ofReal (Real.softmax (fun y => -V y / T) x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · simp [Real.sum_softmax]
    · intro i _
      exact le_of_lt (Real.softmax_pos _ _))

/-- Acceptance probability of a move `x → y` at temperature `T`. -/
noncomputable def accept (T : ℝ) (x y : S) : ℝ≥0∞ :=
  min 1 (ENNReal.ofReal (Real.exp (-(max (V y - V x) 0) / T)))

/-- One annealing step at temperature `T`. -/
noncomputable def annealStep (T : ℝ) (x : S) : PMF S :=
  (R x).bind fun y ↦ (coin (accept V T x y) (min_le_left _ _)).map fun b ↦ cond b y x

/-- Law of `X_k` under schedule `T` from `x₀` (step `k → k+1` at `T (k+1)`). -/
noncomputable def annealLaw (T : ℕ → ℝ) (x₀ : S) : ℕ → PMF S
  | 0 => PMF.pure x₀
  | k + 1 => (annealLaw T x₀ k).bind (annealStep R V (T (k + 1)))

/-- For positive `T` the acceptance probability is Hajek's `exp` form. -/
theorem accept_eq_of_pos {T : ℝ} (hT : 0 < T) (x y : S) :
    accept V T x y = ENNReal.ofReal (Real.exp (-(max (V y - V x) 0) / T)) := by
  rw [accept]
  apply min_eq_right
  rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _)) hT.le

/-- The annealing step is the Metropolis–Hastings step for the Gibbs law
when the proposal is symmetric. -/
theorem annealStep_eq_mhStep [Nonempty S] (hR : ∀ x y, R x y = R y x) {T : ℝ}
    (hT : 0 < T) :
    annealStep R V T = mhStep (gibbs V T) R := by
  have hT' : T ≠ 0 := hT.ne'
  have hZ : 0 < ∑ j, Real.exp (-V j / T) := Real.sum_exp_pos _
  have hg : ∀ a : S, gibbs V T a
      = ENNReal.ofReal (Real.exp (-V a / T) / ∑ j, Real.exp (-V j / T)) := by
    intro a
    rw [gibbs, PMF.ofFintype_apply, Real.softmax]
  have key : ∀ (x y : S), R x y ≠ 0 → accept V T x y = mhAccept (gibbs V T) R x y := by
    intro x y hy
    rw [accept, mhAccept, hR y x,
      ENNReal.mul_div_mul_right _ _ hy (PMF.apply_ne_top _ _), hg y, hg x,
      ← ENNReal.ofReal_div_of_pos (div_pos (Real.exp_pos _) hZ)]
    have hZ' : (∑ j, Real.exp (-V j / T)) ≠ 0 := hZ.ne'
    have hcancel : ∀ a b : ℝ, (a / ∑ j, Real.exp (-V j / T))
        / (b / ∑ j, Real.exp (-V j / T)) = a / b := by
      intro a b
      by_cases hb : b = 0
      · simp [hb]
      · field_simp
    have hdiv : (Real.exp (-V y / T) / ∑ j, Real.exp (-V j / T))
        / (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T))
        = Real.exp (-(V y - V x) / T) := by
      rw [hcancel, ← Real.exp_sub]
      congr 1
      field_simp
      ring
    rw [hdiv]
    rcases le_total (V y - V x) 0 with hle | hle
    · rw [max_eq_right hle, neg_zero, zero_div, Real.exp_zero, ENNReal.ofReal_one,
        min_self]
      symm
      apply min_eq_left
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      apply Real.one_le_exp
      exact div_nonneg (neg_nonneg.mpr hle) hT.le
    · rw [max_eq_left hle]
  funext x
  apply PMF.ext
  intro z
  simp only [annealStep, mhStep, PMF.bind_apply]
  apply tsum_congr
  intro y
  by_cases hy : R x y = 0
  · rw [hy, zero_mul, zero_mul]
  · simp only [key x y hy]

/-- Detailed balance of the annealing step for the Gibbs law. -/
theorem gibbs_detailedBalance [Nonempty S] (hR : ∀ x y, R x y = R y x) {T : ℝ}
    (hT : 0 < T) (x y : S) :
    gibbs V T x * annealStep R V T x y = gibbs V T y * annealStep R V T y x := by
  have h := annealStep_eq_mhStep R V hR hT
  rw [h]
  exact mh_detailedBalance _ _ x y

/-- The Gibbs law is stationary for the annealing step. -/
theorem bind_annealStep [Nonempty S] (hR : ∀ x y, R x y = R y x) {T : ℝ}
    (hT : 0 < T) :
    (gibbs V T).bind (annealStep R V T) = gibbs V T := by
  have h := annealStep_eq_mhStep R V hR hT
  rw [h]
  exact bind_mhStep _ _

/-- As `T → 0+`, the Gibbs law concentrates on the global minima. -/
theorem tendsto_gibbs_globalMinSet [Nonempty S] :
    Tendsto (fun T => (gibbs V T).toOuterMeasure (globalMinSet V)) (𝓝[>] 0) (𝓝 1) := by
  classical
  obtain ⟨sstar, -, hstar⟩ := Finset.exists_min_image Finset.univ V Finset.univ_nonempty
  have hstar' : ∀ x : S, V sstar ≤ V x := fun x => hstar x (Finset.mem_univ x)
  set B : Finset S := Finset.univ.filter (fun x => x ∉ globalMinSet V) with hBdef
  have hmeas : ∀ T : ℝ, (gibbs V T).toOuterMeasure (globalMinSet V)
      = ∑ x ∈ Finset.univ.filter (fun x => x ∈ globalMinSet V), (gibbs V T) x := by
    intro T
    rw [PMF.toOuterMeasure_apply_fintype, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ globalMinSet V
    · simp only [Set.indicator_of_mem hx, if_pos hx]
    · simp only [Set.indicator_of_notMem hx, if_neg hx]
  have hsum1 : ∀ T : ℝ, ∑ x : S, (gibbs V T) x = 1 := by
    intro T
    calc ∑ x : S, (gibbs V T) x = ∑' x : S, (gibbs V T) x := (tsum_fintype _).symm
      _ = 1 := (gibbs V T).tsum_coe
  have hle1 : ∀ T : ℝ, (gibbs V T).toOuterMeasure (globalMinSet V) ≤ 1 := by
    intro T
    rw [PMF.toOuterMeasure_apply_fintype]
    calc ∑ x : S, (globalMinSet V).indicator (⇑(gibbs V T)) x
        ≤ ∑ x : S, (gibbs V T) x := by
          refine Finset.sum_le_sum fun x _ => ?_
          by_cases hx : x ∈ globalMinSet V
          · rw [Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx]
            exact zero_le
      _ = 1 := hsum1 T
  have hgibbs : ∀ (T : ℝ) (x : S), (gibbs V T) x
      = ENNReal.ofReal (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T)) := by
    intro T x
    simp only [gibbs, PMF.ofFintype_apply, Real.softmax]
  by_cases hB : B.Nonempty
  · set Img : Finset ℝ := B.image (fun x => V x - V sstar) with hImgdef
    have hImgne : Img.Nonempty := hB.image _
    set gap : ℝ := Img.min' hImgne with hgapdef
    have hgap_mem : gap ∈ Img := Finset.min'_mem _ _
    obtain ⟨u0, hu0B, hu0eq⟩ := Finset.mem_image.mp hgap_mem
    have hu0bad : u0 ∉ globalMinSet V := (Finset.mem_filter.mp hu0B).2
    have hu0lt : V sstar < V u0 := by
      by_contra hcon
      have hcon' : V u0 ≤ V sstar := le_of_not_gt hcon
      exact hu0bad (fun t => le_trans hcon' (hstar' t))
    have hgap_pos : 0 < gap := by
      rw [← hu0eq]
      linarith
    have hgap_le : ∀ x : S, x ∉ globalMinSet V → gap ≤ V x - V sstar := by
      intro x hx
      have hxB : x ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
      have hmem : V x - V sstar ∈ Img := Finset.mem_image.mpr ⟨x, hxB, rfl⟩
      exact Finset.min'_le _ _ hmem
    have hterm : ∀ (T : ℝ) (hT : 0 < T) (x : S), x ∉ globalMinSet V →
        Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T)
          ≤ Real.exp (-(gap * T⁻¹)) := by
      intro T hT x hx
      have hZ : 0 < ∑ j, Real.exp (-V j / T) := Real.sum_exp_pos _
      have hnonneg : ∀ j ∈ (Finset.univ : Finset S), 0 ≤ Real.exp (-V j / T) :=
        fun j _ => (Real.exp_pos _).le
      have hsingle : Real.exp (-V sstar / T) ≤ ∑ j, Real.exp (-V j / T) :=
        Finset.single_le_sum hnonneg (Finset.mem_univ sstar)
      have hV : gap + V sstar ≤ V x := by
        have h := hgap_le x hx
        linarith
      have hTinv : 0 < T⁻¹ := inv_pos.mpr hT
      have hmul : (gap + V sstar) * T⁻¹ ≤ V x * T⁻¹ :=
        mul_le_mul_of_nonneg_right hV hTinv.le
      have hexp2 : Real.exp (-V x / T)
          ≤ Real.exp (-(gap * T⁻¹)) * Real.exp (-V sstar / T) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have e : -(gap * T⁻¹) + -V sstar / T = -((gap + V sstar) * T⁻¹) := by
          rw [div_eq_mul_inv]; ring
        have e' : -V x / T = -(V x * T⁻¹) := by rw [div_eq_mul_inv, neg_mul]
        rw [e, e']
        exact neg_le_neg hmul
      rw [div_le_iff₀ hZ]
      calc Real.exp (-V x / T)
          ≤ Real.exp (-(gap * T⁻¹)) * Real.exp (-V sstar / T) := hexp2
        _ ≤ Real.exp (-(gap * T⁻¹)) * ∑ j, Real.exp (-V j / T) :=
            mul_le_mul_of_nonneg_left hsingle (Real.exp_pos _).le
    have hsumB : ∀ T : ℝ, 0 < T →
        ∑ x ∈ B, (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T))
          ≤ B.card * Real.exp (-(gap * T⁻¹)) := by
      intro T hT
      calc ∑ x ∈ B, (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T))
          ≤ ∑ x ∈ B, Real.exp (-(gap * T⁻¹)) :=
            Finset.sum_le_sum fun x hx => hterm T hT x (Finset.mem_filter.mp hx).2
        _ = B.card * Real.exp (-(gap * T⁻¹)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hgood : ∀ T : ℝ, 0 < T →
        1 - B.card * Real.exp (-(gap * T⁻¹))
          ≤ ∑ x ∈ Finset.univ.filter (fun x => x ∈ globalMinSet V),
            (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T)) := by
      intro T hT
      have hsplit : (∑ x ∈ Finset.univ.filter (fun x => x ∈ globalMinSet V),
            (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T)))
          + (∑ x ∈ B, (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T)))
          = ∑ x ∈ (Finset.univ : Finset S),
            (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T)) :=
        Finset.sum_filter_add_sum_filter_not _ _ _
      have htot : ∑ x ∈ (Finset.univ : Finset S),
          (Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T)) = 1 := by
        have h := Real.sum_softmax (fun y => -V y / T)
        simpa [Real.softmax] using h
      rw [htot] at hsplit
      have hle := hsumB T hT
      linarith
    have hlow : ∀ T : ℝ, 0 < T →
        ENNReal.ofReal (1 - B.card * Real.exp (-(gap * T⁻¹)))
          ≤ (gibbs V T).toOuterMeasure (globalMinSet V) := by
      intro T hT
      rw [hmeas]
      have hnn : ∀ x ∈ Finset.univ.filter (fun x => x ∈ globalMinSet V),
          0 ≤ Real.exp (-V x / T) / ∑ j, Real.exp (-V j / T) := by
        intro x _
        exact div_nonneg (Real.exp_pos _).le (Real.sum_exp_pos _).le
      simp only [hgibbs T]
      rw [← ENNReal.ofReal_sum_of_nonneg hnn]
      exact ENNReal.ofReal_le_ofReal (hgood T hT)
    have hlim : Tendsto (fun T : ℝ => ENNReal.ofReal (1 - B.card * Real.exp (-(gap * T⁻¹))))
        (𝓝[>] 0) (𝓝 1) := by
      have htop : Tendsto (fun T : ℝ => gap * T⁻¹) (𝓝[>] 0) atTop :=
        Filter.Tendsto.const_mul_atTop hgap_pos tendsto_inv_nhdsGT_zero
      have hbot : Tendsto (fun T : ℝ => -(gap * T⁻¹)) (𝓝[>] 0) atBot :=
        Filter.tendsto_neg_atTop_atBot.comp htop
      have hexp : Tendsto (fun T : ℝ => Real.exp (-(gap * T⁻¹))) (𝓝[>] 0) (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hbot
      have hmul : Tendsto (fun T : ℝ => (B.card : ℝ) * Real.exp (-(gap * T⁻¹)))
          (𝓝[>] 0) (𝓝 0) := by
        have h := hexp.const_mul (B.card : ℝ)
        simpa using h
      have hsub : Tendsto (fun T : ℝ => 1 - (B.card : ℝ) * Real.exp (-(gap * T⁻¹)))
          (𝓝[>] 0) (𝓝 1) := by
        have h := Filter.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ))) hmul
        simpa using h
      have hof : Tendsto
          (fun T : ℝ => ENNReal.ofReal (1 - (B.card : ℝ) * Real.exp (-(gap * T⁻¹))))
          (𝓝[>] 0) (𝓝 (ENNReal.ofReal 1)) :=
        (ENNReal.continuous_ofReal.tendsto 1).comp hsub
      simpa using hof
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with T hT
      exact hlow T hT
    · filter_upwards with T
      exact hle1 T
  · have hall : ∀ x : S, x ∈ globalMinSet V := by
      intro x
      by_contra hx
      exact hB ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    have heq : (fun T => (gibbs V T).toOuterMeasure (globalMinSet V)) = fun _ => 1 := by
      funext T
      rw [PMF.toOuterMeasure_apply_fintype]
      calc ∑ x : S, (globalMinSet V).indicator (⇑(gibbs V T)) x
          = ∑ x : S, (gibbs V T) x := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Set.indicator_of_mem (hall x)]
        _ = 1 := hsum1 T
    rw [heq]
    exact tendsto_const_nhds

/-- Global minima have infinite depth. -/
theorem depth_eq_top_of_globalMin {s : S} (hs : s ∈ globalMinSet V) :
    depth R V s = ⊤ := by
  simp only [globalMinSet, Set.mem_ofPred_eq] at hs
  have hempty : ∀ E : ℝ, ¬ (0 < E ∧ ∃ t, V t < V s ∧ ReachableAt R V (V s + E) s t) := by
    intro E hE
    obtain ⟨-, t, hlt, -⟩ := hE
    exact (not_le_of_gt hlt) (hs t)
  rw [depth]
  have htop : ∀ E : ℝ, (⨅ _ : (0 < E ∧ ∃ t, V t < V s ∧
      ReachableAt R V (V s + E) s t), ENNReal.ofReal E) = ⊤ :=
    fun E => iInf_neg (hempty E)
  simp_rw [htop]
  exact iInf_const

/-- Non-global local minima have positive depth. -/
theorem depth_pos_of_localMin {s : S} (hs : IsHajekLocalMin R V s)
    (hg : s ∉ globalMinSet V) :
    0 < depth R V s := by
  have _ : s ∉ globalMinSet V := hg
  classical
  set T : Finset S := Finset.univ.filter (fun u => V s < V u) with hTdef
  by_cases hne : T.Nonempty
  · set Img : Finset ℝ := T.image (fun u => V u - V s) with hImgdef
    have hImgne : Img.Nonempty := hne.image _
    set gap : ℝ := Img.min' hImgne with hgapdef
    have hgap_mem : gap ∈ Img := Finset.min'_mem _ _
    obtain ⟨u0, hu0T, hu0eq⟩ := Finset.mem_image.mp hgap_mem
    have hu0lt : V s < V u0 := (Finset.mem_filter.mp hu0T).2
    have hgap_pos : 0 < gap := by
      rw [← hu0eq]
      linarith
    have hgap_le : ∀ u : S, V s < V u → gap ≤ V u - V s := by
      intro u hu
      have huT : u ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
      have hmem : V u - V s ∈ Img := Finset.mem_image.mpr ⟨u, huT, rfl⟩
      exact Finset.min'_le _ _ hmem
    have hle : ENNReal.ofReal gap ≤ depth R V s := by
      rw [depth]
      apply le_iInf
      intro E
      apply le_iInf
      intro hP
      obtain ⟨-, t, hlt, hreach⟩ := hP
      have hgapE : gap ≤ E := by
        by_contra hcon
        have hltE : E < gap := lt_of_not_ge hcon
        simp only [ReachableAt] at hreach
        obtain ⟨-, hrtc⟩ := hreach
        have hfall : ∀ b : S, V b ≤ V s + E → V b ≤ V s := by
          intro b hb
          by_contra hnb
          have hltb : V s < V b := lt_of_not_ge hnb
          have hle_gap : gap ≤ V b - V s := hgap_le b hltb
          linarith
        have hmono : ∀ a b : S, (Arc R a b ∧ V b ≤ V s + E) →
            (Arc R a b ∧ V b ≤ V s) := by
          intro a b hab
          exact ⟨hab.1, hfall b hab.2⟩
        have hrtc' : Relation.ReflTransGen
            (fun a b => Arc R a b ∧ V b ≤ V s) s t :=
          Relation.ReflTransGen.mono (fun a b => hmono a b) s t hrtc
        have hreach' : ReachableAt R V (V s) s t := ⟨le_rfl, hrtc'⟩
        exact hs t hlt hreach'
      exact ENNReal.ofReal_le_ofReal hgapE
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal gap :=
      ENNReal.ofReal_pos.mpr hgap_pos
    exact lt_of_lt_of_le hpos hle
  · have hall : ∀ u, V u ≤ V s := by
      intro u
      by_contra hcon
      have hlt : V s < V u := lt_of_not_ge hcon
      have huT : u ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hlt⟩
      exact hne ⟨u, huT⟩
    have hempty : ∀ E : ℝ, ¬ (0 < E ∧ ∃ t, V t < V s ∧
        ReachableAt R V (V s + E) s t) := by
      intro E hE
      obtain ⟨-, t, hlt, hreach⟩ := hE
      simp only [ReachableAt] at hreach
      obtain ⟨-, hrtc⟩ := hreach
      have hmono : ∀ a b : S, (Arc R a b ∧ V b ≤ V s + E) →
          (Arc R a b ∧ V b ≤ V s) := by
        intro a b hab
        exact ⟨hab.1, hall b⟩
      have hrtc' : Relation.ReflTransGen
          (fun a b => Arc R a b ∧ V b ≤ V s) s t :=
        Relation.ReflTransGen.mono (fun a b => hmono a b) s t hrtc
      have hreach' : ReachableAt R V (V s) s t := ⟨le_rfl, hrtc'⟩
      exact hs t hlt hreach'
    have htop : depth R V s = ⊤ := by
      rw [depth]
      have htop' : ∀ E : ℝ, (⨅ _ : (0 < E ∧ ∃ t, V t < V s ∧
        ReachableAt R V (V s + E) s t), ENNReal.ofReal E) = ⊤ :=
        fun E => iInf_neg (hempty E)
      simp_rw [htop']
      exact iInf_const
    rw [htop]
    exact ENNReal.zero_lt_top

/-- Under SI, local minima have finite depth. -/
theorem depth_lt_top_of_localMin (hSI : StronglyIrreducible R V) {s : S}
    (hs : IsHajekLocalMin R V s) (hg : s ∉ globalMinSet V) :
    depth R V s < ⊤ := by
  have _ : IsHajekLocalMin R V s := hs
  have hex : ∃ t, V t < V s := by
    by_contra hcon
    apply hg
    simp only [globalMinSet, Set.mem_ofPred_eq]
    intro t
    exact le_of_not_gt (fun hlt => hcon ⟨t, hlt⟩)
  obtain ⟨t, hlt⟩ := hex
  obtain ⟨E0, hreach0⟩ := hSI t s
  simp only [ReachableAt] at hreach0
  obtain ⟨-, hrtc0⟩ := hreach0
  set E' : ℝ := |E0 - V s| + 1 with hE'def
  have hEpos : 0 < E' := by positivity
  have hEge : E0 ≤ V s + E' := by
    have h : E0 - V s ≤ |E0 - V s| := le_abs_self _
    linarith
  have hle' : V s ≤ V s + E' := by linarith
  have hmono : ∀ a b : S, (Arc R a b ∧ V b ≤ E0) → (Arc R a b ∧ V b ≤ V s + E') := by
    intro a b hab
    exact ⟨hab.1, le_trans hab.2 hEge⟩
  have hrtc' : Relation.ReflTransGen (fun a b => Arc R a b ∧ V b ≤ V s + E') s t :=
    Relation.ReflTransGen.mono (fun a b => hmono a b) s t hrtc0
  have hP : 0 < E' ∧ ∃ u, V u < V s ∧ (V s ≤ V s + E' ∧
      Relation.ReflTransGen (fun a b => Arc R a b ∧ V b ≤ V s + E') s u) :=
    ⟨hEpos, t, hlt, hle', hrtc'⟩
  have hle : depth R V s ≤ ENNReal.ofReal E' := by
    calc depth R V s
        = ⨅ (E : ℝ) (_ : 0 < E ∧ ∃ t, V t < V s ∧ ReachableAt R V (V s + E) s t),
          ENNReal.ofReal E := rfl
      _ ≤ (⨅ _ : 0 < E' ∧ ∃ t, V t < V s ∧ ReachableAt R V (V s + E') s t,
          ENNReal.ofReal E') := iInf_le _ E'
      _ ≤ ENNReal.ofReal E' := iInf_le _ hP
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- Under SI, `d*` is finite. -/
theorem dStar_lt_top (hSI : StronglyIrreducible R V) : dStar R V < ⊤ := by
  have hall : ∀ s : S, (⨆ _ : IsHajekLocalMin R V s ∧ s ∉ globalMinSet V,
      depth R V s) < ⊤ := by
    intro s
    by_cases h : IsHajekLocalMin R V s ∧ s ∉ globalMinSet V
    · rw [iSup_pos h]
      exact depth_lt_top_of_localMin R V hSI h.1 h.2
    · rw [iSup_neg h]
      exact bot_lt_top
  have hEq : (⨆ s : S, ⨆ _ : IsHajekLocalMin R V s ∧ s ∉ globalMinSet V,
      depth R V s) =
      Finset.sup Finset.univ (fun s => ⨆ _ : IsHajekLocalMin R V s ∧
        s ∉ globalMinSet V, depth R V s) :=
    (Finset.sup_univ_eq_iSup _).symm
  have hsup : Finset.sup Finset.univ (fun s => ⨆ _ : IsHajekLocalMin R V s ∧
      s ∉ globalMinSet V, depth R V s) < ⊤ := by
    by_cases huniv : (Finset.univ : Finset S).Nonempty
    · obtain ⟨b, -, heq⟩ := Finset.exists_mem_eq_sup Finset.univ huniv
        (fun s => ⨆ _ : IsHajekLocalMin R V s ∧ s ∉ globalMinSet V, depth R V s)
      rw [heq]
      exact hall b
    · have huniv_empty : (Finset.univ : Finset S) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        exact huniv ⟨x, hx⟩
      rw [huniv_empty, Finset.sup_empty]
      exact bot_lt_top
  have hdStar : dStar R V = (⨆ s : S, ⨆ _ : IsHajekLocalMin R V s ∧
      s ∉ globalMinSet V, depth R V s) := rfl
  rw [hdStar, hEq]
  exact hsup

/-- The logarithmic schedule is positive, nonincreasing, and cools to 0. -/
theorem logSchedule_specs {c : ℝ} (hc : 0 < c) :
    (∀ k : ℕ, 0 < c / Real.log ((k : ℝ) + 2)) ∧
      Antitone (fun k : ℕ => c / Real.log ((k : ℝ) + 2)) ∧
      Tendsto (fun k : ℕ => c / Real.log ((k : ℝ) + 2)) atTop (𝓝 0) := by
  have hlog_pos : ∀ k : ℕ, 0 < Real.log ((k : ℝ) + 2) := by
    intro k
    apply Real.log_pos
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  refine ⟨fun k => div_pos hc (hlog_pos k), ?_, ?_⟩
  · intro a b hab
    show c / Real.log ((b : ℝ) + 2) ≤ c / Real.log ((a : ℝ) + 2)
    have hle : (a:ℝ) + 2 ≤ (b:ℝ) + 2 := by
      have h : (a:ℝ) ≤ (b:ℝ) := Nat.cast_le.mpr hab
      linarith
    have hlog_le : Real.log ((a:ℝ)+2) ≤ Real.log ((b:ℝ)+2) :=
      Real.log_le_log (by positivity) hle
    have h1div : (1 : ℝ) / Real.log ((b:ℝ)+2) ≤ 1 / Real.log ((a:ℝ)+2) :=
      (one_div_le_one_div (hlog_pos b) (hlog_pos a)).mpr hlog_le
    calc c / Real.log ((b:ℝ)+2) = c * (1 / Real.log ((b:ℝ)+2)) := by
            rw [div_eq_mul_one_div c _]
      _ ≤ c * (1 / Real.log ((a:ℝ)+2)) :=
            mul_le_mul_of_nonneg_left h1div hc.le
      _ = c / Real.log ((a:ℝ)+2) := by rw [div_eq_mul_one_div c _]
  · have hcast : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ => (k:ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 hcast
    have h2 : Tendsto (fun k : ℕ => Real.log ((k:ℝ)+2)) atTop atTop :=
      Real.tendsto_log_atTop.comp h1
    exact Tendsto.const_div_atTop h2 c

end Cslib.MachineLearning.Sampling.SimulatedAnnealing
