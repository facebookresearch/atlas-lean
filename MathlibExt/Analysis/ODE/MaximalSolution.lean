/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Piecewise
import Mathlib.Topology.Sequences

/-!
# Maximal solutions of ordinary differential equations

This file proves global existence for continuous vector fields that are globally Lipschitz in the
state variable, and constructs maximal solutions for locally Lipschitz vector fields on open
subsets of spacetime.  The latter solutions eventually leave every compact subset at each finite
or infinite end of their interval of definition.
-/

@[expose] public section

open Filter Function Metric Set
open scoped NNReal Topology

/-- **Gluing solutions of an ODE.** Let $E$ be a real normed space, let
$v : \mathbb{R} \times E \to E$, let $I, J \subseteq \mathbb{R}$ be open, and let
$x, y : \mathbb{R} \to E$ satisfy $x'(t) = v(t, x(t))$ for every $t \in I$ and
$y'(t) = v(t, y(t))$ for every $t \in J$, with $x = y$ on $I \cap J$. Then there is
$z : \mathbb{R} \to E$ with $z = x$ on $I$, $z = y$ on $J$ and $z'(t) = v(t, z(t))$ for every
$t \in I \cup J$. -/
theorem hasDerivAt_piecewise_union_of_eqOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {x y : ℝ → E} {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J)
    (hx : ∀ t ∈ I, HasDerivAt x (v t (x t)) t)
    (hy : ∀ t ∈ J, HasDerivAt y (v t (y t)) t)
    (hxy : EqOn x y (I ∩ J)) :
    ∃ z : ℝ → E, EqOn z x I ∧ EqOn z y J ∧
      ∀ t ∈ I ∪ J, HasDerivAt z (v t (z t)) t := by
  classical
  refine ⟨I.piecewise x y, Set.piecewise_eqOn I x y, ?_, ?_⟩
  · intro t ht
    by_cases htI : t ∈ I
    · simp [Set.piecewise, htI, hxy ⟨htI, ht⟩]
    · simp [Set.piecewise, htI]
  intro t ht
  by_cases htI : t ∈ I
  · have heq : I.piecewise x y =ᶠ[𝓝 t] x := by
      filter_upwards [hI.mem_nhds htI] with u hu
      simp [Set.piecewise, hu]
    simpa [Set.piecewise, htI] using (hx t htI).congr_of_eventuallyEq heq
  · have htJ : t ∈ J := ht.resolve_left htI
    have heq : I.piecewise x y =ᶠ[𝓝 t] y := by
      filter_upwards [hJ.mem_nhds htJ] with u hu
      by_cases huI : u ∈ I
      · simp [Set.piecewise, huI, hxy ⟨huI, hu⟩]
      · simp [Set.piecewise, huI]
    simpa [Set.piecewise, htI] using (hy t htJ).congr_of_eventuallyEq heq

namespace MathlibExt.Analysis.ODE.MaximalSolutionWanted

private lemma odeMaximalLocalFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    {p : ℝ × E} (hp : p ∈ U) :
    ∃ W ∈ nhds p, ∃ ε > 0, ∀ q ∈ W, ∃ x : ℝ → E, x q.1 = q.2 ∧
      ∀ t ∈ Ioo (q.1 - ε) (q.1 + ε),
        (t, x t) ∈ U ∧ HasDerivAt x (f (t, x t)) t := by
  classical
  obtain ⟨C, s, hs, hC⟩ := hlip p hp
  have hfp : ContinuousAt f p := hf.continuousAt (hU.mem_nhds hp)
  have hnorm : {q | ‖f q‖ < ‖f p‖ + 1} ∈ nhds p :=
    hfp.norm (Iio_mem_nhds (lt_add_one ‖f p‖))
  have hw : (s ∩ U) ∩ {q | ‖f q‖ < ‖f p‖ + 1} ∈ nhds p :=
    inter_mem (inter_mem hs (hU.mem_nhds hp)) hnorm
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hw
  let B : ℝ := ‖f p‖ + 1
  have hB : 0 < B := by
    dsimp [B]
    exact add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  let ε : ℝ := min (δ / 8) (δ / (8 * B))
  have hε : 0 < ε := by simp [ε, hδ, hB]
  refine ⟨ball p (δ / 8), ball_mem_nhds p (by positivity), ε, hε, ?_⟩
  intro q hq
  have hqt : dist q.1 p.1 < δ / 8 := by
    calc
      dist q.1 p.1 ≤ dist q p := by simp [Prod.dist_eq]
      _ < δ / 8 := hq
  have hqx : dist q.2 p.2 < δ / 8 := by
    calc
      dist q.2 p.2 ≤ dist q p := by simp [Prod.dist_eq]
      _ < δ / 8 := hq
  let a : NNReal := ⟨δ / 2, by positivity⟩
  let r : NNReal := ⟨δ / 4, by positivity⟩
  let L : NNReal := ⟨B, hB.le⟩
  have hbox (t : ℝ) (ht : t ∈ Icc (q.1 - ε) (q.1 + ε))
      (y : E) (hy : y ∈ closedBall p.2 a) : (t, y) ∈ (s ∩ U) ∩ {z | ‖f z‖ < B} := by
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · calc
        dist t p.1 ≤ dist t q.1 + dist q.1 p.1 := dist_triangle _ _ _
        _ < ε + δ / 8 := by
          apply add_lt_add_of_le_of_lt _ hqt
          rw [Real.dist_eq]
          refine (abs_le (G := ℝ) (a := t - q.1) (b := ε)).2 ⟨?_, ?_⟩
          · linarith [ht.1]
          · linarith [ht.2]
        _ ≤ δ / 4 := by dsimp [ε]; linarith [min_le_left (δ / 8) (δ / (8 * B))]
        _ < δ := by linarith
    · calc
        dist y p.2 ≤ δ / 2 := by
          change dist y p.2 ≤ δ / 2 at hy
          exact hy
        _ < δ := by linarith
  have hqball : q.2 ∈ closedBall p.2 r := by
    change dist q.2 p.2 ≤ δ / 4
    exact hqx.le.trans (by linarith)
  have hqtime : q.1 ∈ Icc (q.1 - ε) (q.1 + ε) := by simp [hε.le]
  let q₀ : Icc (q.1 - ε) (q.1 + ε) := ⟨q.1, hqtime⟩
  have hPL : IsPicardLindelof (fun t y ↦ f (t, y)) q₀ p.2 a r L C := by
    refine IsPicardLindelof.mk ?_ ?_ ?_ ?_
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      exact hC t x y (hbox t ht x hx).1 (hbox t ht y hy).1
    · intro y hy
      exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht ↦ (hbox t ht y hy).1.2)
    · intro t ht y hy
      exact le_of_lt (hbox t ht y hy).2
    · change B * max ((q.1 + ε) - q.1) (q.1 - (q.1 - ε)) ≤ δ / 2 - δ / 4
      rw [add_sub_cancel_left, sub_sub_cancel, max_self]
      have he : ε ≤ δ / (8 * B) := min_le_right _ _
      have : B * ε ≤ δ / 8 := by
        calc
          B * ε ≤ B * (δ / (8 * B)) := by gcongr
          _ = δ / 8 := by field_simp
      linarith
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hPL hqball
  refine ⟨α.compProj, ?_, fun t ht ↦ ⟨?_, ?_⟩⟩
  · change α.compProj (q₀ : ℝ) = q.2
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · exact (hbox t (Ioo_subset_Icc_self ht) _
      (α.compProj_mem_closedBall hPL.mul_max_le)).1.2
  · apply HasDerivWithinAt.hasDerivAt ?_ (Icc_mem_nhds ht.1 ht.2)
    apply (ODE.hasDerivWithinAt_picard_Icc q₀.2 hPL.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ ↦ α.compProj_mem_closedBall hPL.mul_max_le) q.2
      (Ioo_subset_Icc_self ht)).congr_of_mem _ (Ioo_subset_Icc_self ht)
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

private structure OdeMaximalSolutionOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set (ℝ × E)) (f : ℝ × E → E) (I : Set ℝ) (x : ℝ → E) : Prop where
  isOpen : IsOpen I
  ordConnected : I.OrdConnected
  graph_mem : ∀ t ∈ I, (t, x t) ∈ U
  hasDerivAt : ∀ t ∈ I, HasDerivAt x (f (t, x t)) t

private structure OdeMaximalCandidate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set (ℝ × E)) (f : ℝ × E → E) (t₀ : ℝ) (x₀ : E) where
  I : Set ℝ
  x : ℝ → E
  solution : OdeMaximalSolutionOn U f I x
  mem_domain : t₀ ∈ I
  initial : x t₀ = x₀

private lemma odeMaximalLocalUnique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (ℝ × E)} {f : ℝ × E → E}
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    {I J : Set ℝ} {x y : ℝ → E}
    (hx : OdeMaximalSolutionOn U f I x) (hy : OdeMaximalSolutionOn U f J y)
    {t : ℝ} (htI : t ∈ I) (htJ : t ∈ J) (heq : x t = y t) :
    x =ᶠ[nhds t] y := by
  obtain ⟨C, s, hs, hC⟩ := hlip (t, x t) (hx.graph_mem t htI)
  let S : ℝ → Set E := fun u ↦ {z | (u, z) ∈ s ∩ U}
  have hxs : ∀ᶠ u in nhds t, (u, x u) ∈ s :=
    (continuousAt_id.prodMk (hx.hasDerivAt t htI).continuousAt) hs
  have hys : ∀ᶠ u in nhds t, (u, y u) ∈ s := by
    have hs' : s ∈ nhds (t, y t) := by rwa [← heq]
    exact (continuousAt_id.prodMk (hy.hasDerivAt t htJ).continuousAt) hs'
  apply ODE_solution_unique_of_eventually (K := C) (v := fun u z ↦ f (u, z)) (s := S)
  · exact Filter.Eventually.of_forall fun u ↦ LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦
      hC u a b ha hb
  · filter_upwards [hx.isOpen.mem_nhds htI, hxs] with u hu hus
    exact ⟨hx.hasDerivAt u hu, hus, hx.graph_mem u hu⟩
  · filter_upwards [hy.isOpen.mem_nhds htJ, hys] with u hu hus
    exact ⟨hy.hasDerivAt u hu, hus, hy.graph_mem u hu⟩
  · exact heq

private lemma odeMaximalUniqueOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (ℝ × E)} {f : ℝ × E → E}
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    {I J : Set ℝ} {x y : ℝ → E}
    (hx : OdeMaximalSolutionOn U f I x) (hy : OdeMaximalSolutionOn U f J y)
    {t : ℝ} (htI : t ∈ I) (htJ : t ∈ J) (heq : x t = y t) :
    EqOn x y (I ∩ J) := by
  let D := I ∩ J
  have hDord : D.OrdConnected := hx.ordConnected.inter hy.ordConnected
  have hxc : ContinuousOn x D := fun u hu ↦
    (hx.hasDerivAt u hu.1).continuousAt.continuousWithinAt
  have hyc : ContinuousOn y D := fun u hu ↦
    (hy.hasDerivAt u hu.2).continuousAt.continuousWithinAt
  let A : Set D := {u | x u = y u}
  have hAclosed : IsClosed A := by
    apply isClosed_eq
    · exact continuousOn_iff_continuous_domRestrict.mp hxc
    · exact continuousOn_iff_continuous_domRestrict.mp hyc
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    have hlocal := odeMaximalLocalUnique hlip hx hy u.property.1 u.property.2 hu
    exact continuousAt_subtype_val hlocal
  let _ : PreconnectedSpace D := Subtype.preconnectedSpace hDord.isPreconnected
  have hAuniv : A = Set.univ := by
    rcases isClopen_iff.mp ⟨hAclosed, hAopen⟩ with h | h
    · exfalso
      have htA : (⟨t, ⟨htI, htJ⟩⟩ : D) ∈ A := heq
      rw [h] at htA
      exact htA
    · exact h
  intro u hu
  have huA : (⟨u, hu⟩ : D) ∈ A := by rw [hAuniv]; trivial
  exact huA

private lemma odeMaximalSolutionOnGlue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (ℝ × E)} {f : ℝ × E → E}
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    {I J : Set ℝ} {x y : ℝ → E}
    (hx : OdeMaximalSolutionOn U f I x) (hy : OdeMaximalSolutionOn U f J y)
    {t : ℝ} (htI : t ∈ I) (htJ : t ∈ J) (heq : x t = y t) :
    ∃ z : ℝ → E, OdeMaximalSolutionOn U f (I ∪ J) z ∧
      EqOn z x I ∧ EqOn z y J := by
  have hxy := odeMaximalUniqueOn hlip hx hy htI htJ heq
  obtain ⟨z, hzx, hzy, hzderiv⟩ := hasDerivAt_piecewise_union_of_eqOn
    (v := fun u w ↦ f (u, w)) (x := x) (y := y) (I := I) (J := J)
    hx.isOpen hy.isOpen hx.hasDerivAt hy.hasDerivAt hxy
  refine ⟨z, ⟨hx.isOpen.union hy.isOpen, ?_, ?_, hzderiv⟩, hzx, hzy⟩
  · exact (IsPreconnected.union t htI htJ hx.ordConnected.isPreconnected
      hy.ordConnected.isPreconnected).ordConnected
  · intro u hu
    rcases hu with hu | hu
    · simpa only [hzx hu] using hx.graph_mem u hu
    · simpa only [hzy hu] using hy.graph_mem u hu

private lemma odeMaximalCandidateNonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hU : IsOpen U) (hmem : (t₀, x₀) ∈ U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y) :
    Nonempty (OdeMaximalCandidate U f t₀ x₀) := by
  obtain ⟨W, hW, ε, hε, hflow⟩ := odeMaximalLocalFlow hU hf hlip hmem
  obtain ⟨x, hx₀, hx⟩ := hflow (t₀, x₀) (mem_of_mem_nhds hW)
  exact ⟨{
    I := Ioo (t₀ - ε) (t₀ + ε)
    x := x
    solution := {
      isOpen := isOpen_Ioo
      ordConnected := ordConnected_Ioo
      graph_mem := fun t ht ↦ (hx t ht).1
      hasDerivAt := fun t ht ↦ (hx t ht).2 }
    mem_domain := by simp [hε]
    initial := hx₀ }⟩

private lemma odeMaximalGreatestCandidate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hU : IsOpen U) (hmem : (t₀, x₀) ∈ U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y) :
    ∃ m : OdeMaximalCandidate U f t₀ x₀, ∀ c : OdeMaximalCandidate U f t₀ x₀,
      c.I ⊆ m.I := by
  classical
  let C := OdeMaximalCandidate U f t₀ x₀
  have hC : Nonempty C := odeMaximalCandidateNonempty hU hmem hf hlip
  let I : Set ℝ := ⋃ c : C, c.I
  let pick (t : ℝ) (ht : t ∈ I) : C := Classical.choose (Set.mem_iUnion.mp ht)
  have pick_mem (t : ℝ) (ht : t ∈ I) : t ∈ (pick t ht).I :=
    Classical.choose_spec (Set.mem_iUnion.mp ht)
  let x : ℝ → E := fun t ↦ if ht : t ∈ I then (pick t ht).x t else x₀
  have hsubset (c : C) : c.I ⊆ I := Set.subset_iUnion (fun c : C ↦ c.I) c
  have hxeq (c : C) : EqOn x c.x c.I := by
    intro t ht
    have htI := hsubset c ht
    change (if ht' : t ∈ I then (pick t ht').x t else x₀) = c.x t
    rw [dite_eq_left htI]
    have huniq := odeMaximalUniqueOn hlip c.solution (pick t htI).solution
      c.mem_domain (pick t htI).mem_domain (c.initial.trans (pick t htI).initial.symm)
    exact (huniq ⟨ht, pick_mem t htI⟩).symm
  have hIopen : IsOpen I := isOpen_iUnion fun c : C ↦ c.solution.isOpen
  have hIord : I.OrdConnected := by
    apply IsPreconnected.ordConnected
    apply isPreconnected_iUnion
    · exact ⟨t₀, Set.mem_iInter.2 fun c : C ↦ c.mem_domain⟩
    · exact fun c : C ↦ c.solution.ordConnected.isPreconnected
  have hIsolution : OdeMaximalSolutionOn U f I x := {
    isOpen := hIopen
    ordConnected := hIord
    graph_mem t ht := by
      obtain ⟨c, htc⟩ := Set.mem_iUnion.mp ht
      rw [hxeq c htc]
      exact c.solution.graph_mem t htc
    hasDerivAt t ht := by
      obtain ⟨c, htc⟩ := Set.mem_iUnion.mp ht
      have heq : x =ᶠ[nhds t] c.x := by
        filter_upwards [c.solution.isOpen.mem_nhds htc] with u hu
        exact hxeq c hu
      simpa only [hxeq c htc] using
        (c.solution.hasDerivAt t htc).congr_of_eventuallyEq heq }
  let c₀ : C := Classical.choice hC
  refine ⟨{
    I := I
    x := x
    solution := hIsolution
    mem_domain := hsubset c₀ c₀.mem_domain
    initial := (hxeq c₀ c₀.mem_domain).trans c₀.initial }, hsubset⟩

private lemma odeMaximalNoRightCluster
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    (m : OdeMaximalCandidate U f t₀ x₀)
    (hmax : ∀ c : OdeMaximalCandidate U f t₀ x₀, c.I ⊆ m.I)
    {b : ℝ} (hb : ∀ t ∈ m.I, t ≤ b) {u : ℕ → ℝ} {p : ℝ × E}
    (hu : ∀ n, u n ∈ m.I) (hut : Tendsto u atTop (nhds b))
    (hgraph : Tendsto (fun n ↦ (u n, m.x (u n))) atTop (nhds p)) (hp : p ∈ U) :
    False := by
  obtain ⟨W, hW, ε, hε, hflow⟩ := odeMaximalLocalFlow hU hf hlip hp
  have hnear : ∀ᶠ n in atTop, b - ε / 2 < u n :=
    hut (Ioi_mem_nhds (by linarith))
  have hW' : ∀ᶠ n in atTop, (u n, m.x (u n)) ∈ W := hgraph hW
  have hboth : ∀ᶠ n in atTop, (u n, m.x (u n)) ∈ W ∧ b - ε / 2 < u n :=
    Filter.Eventually.and hW' hnear
  obtain ⟨n, hnW, hn⟩ := Filter.Eventually.exists hboth
  obtain ⟨z, hz₀, hz⟩ := hflow (u n, m.x (u n)) hnW
  let J := Ioo (u n - ε) (u n + ε)
  have hunJ : u n ∈ J := by simp [J, hε]
  have hzsol : OdeMaximalSolutionOn U f J z := {
    isOpen := isOpen_Ioo
    ordConnected := ordConnected_Ioo
    graph_mem := fun t ht ↦ (hz t ht).1
    hasDerivAt := fun t ht ↦ (hz t ht).2 }
  obtain ⟨w, hw, hwm, -⟩ := odeMaximalSolutionOnGlue hlip m.solution hzsol
    (hu n) hunJ hz₀.symm
  let c : OdeMaximalCandidate U f t₀ x₀ := {
    I := m.I ∪ J
    x := w
    solution := hw
    mem_domain := Or.inl m.mem_domain
    initial := (hwm m.mem_domain).trans m.initial }
  have hc : c.I ⊆ m.I := hmax c
  have hvJ : u n + ε / 2 ∈ J := by
    change u n - ε < u n + ε / 2 ∧ u n + ε / 2 < u n + ε
    constructor <;> linarith
  have hvM : u n + ε / 2 ∈ m.I := hc (Or.inr hvJ)
  linarith [hb _ hvM]

private lemma odeMaximalNoLeftCluster
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    (m : OdeMaximalCandidate U f t₀ x₀)
    (hmax : ∀ c : OdeMaximalCandidate U f t₀ x₀, c.I ⊆ m.I)
    {b : ℝ} (hb : ∀ t ∈ m.I, b ≤ t) {u : ℕ → ℝ} {p : ℝ × E}
    (hu : ∀ n, u n ∈ m.I) (hut : Tendsto u atTop (nhds b))
    (hgraph : Tendsto (fun n ↦ (u n, m.x (u n))) atTop (nhds p)) (hp : p ∈ U) :
    False := by
  obtain ⟨W, hW, ε, hε, hflow⟩ := odeMaximalLocalFlow hU hf hlip hp
  have hnear : ∀ᶠ n in atTop, u n < b + ε / 2 :=
    hut (Iio_mem_nhds (by linarith))
  have hW' : ∀ᶠ n in atTop, (u n, m.x (u n)) ∈ W := hgraph hW
  have hboth : ∀ᶠ n in atTop, (u n, m.x (u n)) ∈ W ∧ u n < b + ε / 2 :=
    Filter.Eventually.and hW' hnear
  obtain ⟨n, hnW, hn⟩ := Filter.Eventually.exists hboth
  obtain ⟨z, hz₀, hz⟩ := hflow (u n, m.x (u n)) hnW
  let J := Ioo (u n - ε) (u n + ε)
  have hunJ : u n ∈ J := by simp [J, hε]
  have hzsol : OdeMaximalSolutionOn U f J z := {
    isOpen := isOpen_Ioo
    ordConnected := ordConnected_Ioo
    graph_mem := fun t ht ↦ (hz t ht).1
    hasDerivAt := fun t ht ↦ (hz t ht).2 }
  obtain ⟨w, hw, hwm, -⟩ := odeMaximalSolutionOnGlue hlip m.solution hzsol
    (hu n) hunJ hz₀.symm
  let c : OdeMaximalCandidate U f t₀ x₀ := {
    I := m.I ∪ J
    x := w
    solution := hw
    mem_domain := Or.inl m.mem_domain
    initial := (hwm m.mem_domain).trans m.initial }
  have hc : c.I ⊆ m.I := hmax c
  have hvJ : u n - ε / 2 ∈ J := by
    change u n - ε < u n - ε / 2 ∧ u n - ε / 2 < u n + ε
    constructor <;> linarith
  have hvM : u n - ε / 2 ∈ m.I := hc (Or.inr hvJ)
  linarith [hb _ hvM]

private lemma odeMaximalExitRight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    (m : OdeMaximalCandidate U f t₀ x₀)
    (hmax : ∀ c : OdeMaximalCandidate U f t₀ x₀, c.I ⊆ m.I)
    (K : Set (ℝ × E)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c ∈ m.I, ∀ t ∈ m.I, c ≤ t → (t, m.x t) ∉ K := by
  classical
  by_cases hbd : BddAbove m.I
  · let b := sSup m.I
    have hb : ∀ t ∈ m.I, t ≤ b := fun t ht ↦ le_csSup hbd ht
    by_contra hno
    push Not at hno
    have hseq : ∀ n : ℕ, ∃ t ∈ m.I,
        b - 1 / ((n : ℝ) + 1) < t ∧ (t, m.x t) ∈ K := by
      intro n
      have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      obtain ⟨c, hc, hbc⟩ := exists_lt_of_lt_csSup (Set.nonempty_of_mem m.mem_domain)
        (sub_lt_self b hpos)
      obtain ⟨t, ht, hct, htK⟩ := hno c hc
      exact ⟨t, ht, hbc.trans_le hct, htK⟩
    choose u hu hut huK using hseq
    have hlow : Tendsto (fun n : ℕ ↦ b - 1 / ((n : ℝ) + 1)) atTop (nhds b) := by
      simpa using tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hu_tendsto : Tendsto u atTop (nhds b) :=
      hlow.squeeze tendsto_const_nhds (fun n ↦ (hut n).le) (fun n ↦ hb _ (hu n))
    obtain ⟨p, hpK, φ, hφ, hp⟩ := hK.tendsto_subseq huK
    apply odeMaximalNoRightCluster hU hf hlip m hmax hb
      (u := u ∘ φ) (p := p) (fun n ↦ hu (φ n))
      (hu_tendsto.comp hφ.tendsto_atTop)
    · simpa only [Function.comp_def] using hp
    · exact hKU hpK
  · have hproj : IsCompact (Prod.fst '' K) := hK.image continuous_fst
    obtain ⟨B, hB⟩ := hproj.bddAbove
    rw [not_bddAbove_iff] at hbd
    obtain ⟨c, hc, hBc⟩ := hbd B
    refine ⟨c, hc, fun t ht hct htK ↦ ?_⟩
    have htB : t ≤ B := hB ⟨(t, m.x t), htK, rfl⟩
    linarith

private lemma odeMaximalExitLeft
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    (m : OdeMaximalCandidate U f t₀ x₀)
    (hmax : ∀ c : OdeMaximalCandidate U f t₀ x₀, c.I ⊆ m.I)
    (K : Set (ℝ × E)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c ∈ m.I, ∀ t ∈ m.I, t ≤ c → (t, m.x t) ∉ K := by
  classical
  by_cases hbd : BddBelow m.I
  · let b := sInf m.I
    have hb : ∀ t ∈ m.I, b ≤ t := fun t ht ↦ csInf_le hbd ht
    by_contra hno
    push Not at hno
    have hseq : ∀ n : ℕ, ∃ t ∈ m.I,
        t < b + 1 / ((n : ℝ) + 1) ∧ (t, m.x t) ∈ K := by
      intro n
      have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      obtain ⟨c, hc, hcb⟩ := exists_lt_of_csInf_lt (Set.nonempty_of_mem m.mem_domain)
        (lt_add_of_pos_right b hpos)
      obtain ⟨t, ht, htc, htK⟩ := hno c hc
      exact ⟨t, ht, htc.trans_lt hcb, htK⟩
    choose u hu hut huK using hseq
    have hhigh : Tendsto (fun n : ℕ ↦ b + 1 / ((n : ℝ) + 1)) atTop (nhds b) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hu_tendsto : Tendsto u atTop (nhds b) :=
      tendsto_const_nhds.squeeze hhigh (fun n ↦ hb _ (hu n)) (fun n ↦ (hut n).le)
    obtain ⟨p, hpK, φ, hφ, hp⟩ := hK.tendsto_subseq huK
    apply odeMaximalNoLeftCluster hU hf hlip m hmax hb
      (u := u ∘ φ) (p := p) (fun n ↦ hu (φ n))
      (hu_tendsto.comp hφ.tendsto_atTop)
    · simpa only [Function.comp_def] using hp
    · exact hKU hpK
  · have hproj : IsCompact (Prod.fst '' K) := hK.image continuous_fst
    obtain ⟨B, hB⟩ := hproj.bddBelow
    rw [not_bddBelow_iff] at hbd
    obtain ⟨c, hc, hcB⟩ := hbd B
    refine ⟨c, hc, fun t ht htc htK ↦ ?_⟩
    have hBt : B ≤ t := hB ⟨(t, m.x t), htK, rfl⟩
    linarith

private lemma odeMaximalGlobalNotBddAbove
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {L : NNReal}
    (hfcont : Continuous (Function.uncurry f)) (hlip : ∀ t, LipschitzWith L (f t))
    (m : OdeMaximalCandidate Set.univ (Function.uncurry f) t₀ x₀)
    (hmax : ∀ c : OdeMaximalCandidate Set.univ (Function.uncurry f) t₀ x₀,
      c.I ⊆ m.I) :
    ¬BddAbove m.I := by
  intro hbounded
  let b := sSup m.I
  have hb : ∀ t ∈ m.I, t ≤ b := fun t ht ↦ le_csSup hbounded ht
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (m.solution.isOpen.mem_nhds m.mem_domain)
  have ht₀ε : t₀ + ε / 2 ∈ m.I := by
    apply hball
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith
  have ht₀b : t₀ < b := by linarith [hb _ ht₀ε]
  have hIco : Ico t₀ b ⊆ m.I := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup (Set.nonempty_of_mem m.mem_domain) ht.2
    exact m.solution.ordConnected.out m.mem_domain hu ⟨ht.1, htu.le⟩
  have hfzero : Continuous (fun t : ℝ ↦ ‖f t (0 : E)‖) :=
    (hfcont.comp (continuous_id.prodMk continuous_const)).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hfzero).bddAbove
  have hMbound : ∀ t ∈ Icc t₀ b, ‖f t (0 : E)‖ ≤ M := by
    intro t ht
    exact hM ⟨t, ht, rfl⟩
  have hMnonneg : 0 ≤ M :=
    (norm_nonneg (f t₀ (0 : E))).trans (hMbound t₀ ⟨le_rfl, ht₀b.le⟩)
  let B := gronwallBound ‖x₀‖ (L : ℝ) M (b - t₀)
  have hBnonneg : 0 ≤ B := by
    calc
      0 ≤ ‖x₀‖ := norm_nonneg _
      _ = gronwallBound ‖x₀‖ (L : ℝ) M 0 := (gronwallBound_x0 _ _ _).symm
      _ ≤ B := gronwallBound_mono (norm_nonneg _) hMnonneg L.2 (sub_nonneg.mpr ht₀b.le)
  have hstate : ∀ t ∈ Ico t₀ b, ‖m.x t‖ ≤ B := by
    intro t ht
    have hseg : Icc t₀ t ⊆ m.I := by
      intro u hu
      exact hIco ⟨hu.1, hu.2.trans_lt ht.2⟩
    have hcont : ContinuousOn m.x (Icc t₀ t) := by
      intro u hu
      exact (m.solution.hasDerivAt u (hseg hu)).continuousAt.continuousWithinAt
    have hderiv : ∀ u ∈ Ico t₀ t,
        HasDerivWithinAt m.x (f u (m.x u)) (Ici u) u := by
      intro u hu
      exact (m.solution.hasDerivAt u (hseg ⟨hu.1, hu.2.le⟩)).hasDerivWithinAt
    have hderivBound : ∀ u ∈ Ico t₀ t,
        ‖f u (m.x u)‖ ≤ (L : ℝ) * ‖m.x u‖ + M := by
      intro u hu
      calc
        ‖f u (m.x u)‖ = ‖(f u (m.x u) - f u 0) + f u 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖f u (m.x u) - f u 0‖ + ‖f u 0‖ := norm_add_le _ _
        _ ≤ (L : ℝ) * ‖m.x u‖ + M := by
          apply add_le_add
          · simpa only [dist_eq_norm, sub_zero] using (hlip u).dist_le_mul (m.x u) 0
          · exact hMbound u ⟨hu.1, hu.2.le.trans ht.2.le⟩
    have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
      (δ := ‖x₀‖) (K := (L : ℝ)) (ε := M) hcont hderiv
      (by simp [m.initial]) hderivBound t ⟨ht.1, le_rfl⟩
    exact hgronwall.trans
      (gronwallBound_mono (norm_nonneg _) hMnonneg L.2 (sub_le_sub_right ht.2.le t₀))
  let C : NNReal :=
    ⟨(L : ℝ) * B + M, add_nonneg (mul_nonneg L.2 hBnonneg) hMnonneg⟩
  have hxlip : LipschitzOnWith C m.x (Ico t₀ b) := by
    apply (convex_Ico t₀ b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    · intro t ht
      exact (m.solution.hasDerivAt t (hIco ht)).hasDerivWithinAt
    · intro t ht
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      change ‖f t (m.x t)‖ ≤ (L : ℝ) * B + M
      calc
        ‖f t (m.x t)‖ = ‖(f t (m.x t) - f t 0) + f t 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖f t (m.x t) - f t 0‖ + ‖f t 0‖ := norm_add_le _ _
        _ ≤ (L : ℝ) * ‖m.x t‖ + M := by
          apply add_le_add
          · simpa only [dist_eq_norm, sub_zero] using (hlip t).dist_le_mul (m.x t) 0
          · exact hMbound t ⟨ht.1, ht.2.le⟩
        _ ≤ (L : ℝ) * B + M := by gcongr; exact hstate t ht
  let u : ℕ → ℝ := fun n ↦ b - (b - t₀) / ((n : ℝ) + 1)
  have hu : ∀ n, u n ∈ Ico t₀ b := by
    intro n
    have hden : 1 ≤ (n : ℝ) + 1 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hdenpos : 0 < (n : ℝ) + 1 := lt_of_lt_of_le zero_lt_one hden
    have hquotpos : 0 < (b - t₀) / ((n : ℝ) + 1) := div_pos (sub_pos.mpr ht₀b) hdenpos
    have hquotle : (b - t₀) / ((n : ℝ) + 1) ≤ b - t₀ :=
      div_le_self (sub_nonneg.mpr ht₀b.le) hden
    constructor <;> dsimp [u] <;> linarith
  have hut : Tendsto u atTop (nhds b) := by
    have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hmul : Tendsto (fun n : ℕ ↦ (b - t₀) * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hzero
    simpa only [u, div_eq_mul_inv, one_mul, sub_zero] using tendsto_const_nhds.sub hmul
  have hxcauchy : CauchySeq (m.x ∘ u) :=
    hxlip.cauchySeq_comp hut.cauchySeq (fun _ ⟨n, hn⟩ ↦ hn ▸ hu n)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hxcauchy
  have hlocal : ∀ p ∈ (Set.univ : Set (ℝ × E)), ∃ D : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ Set.univ → (t, y) ∈ s ∩ Set.univ →
        dist (Function.uncurry f (t, x)) (Function.uncurry f (t, y)) ≤ D * dist x y := by
    intro p _
    refine ⟨L, Set.univ, univ_mem, ?_⟩
    intro t x y _ _
    exact (hlip t).dist_le_mul x y
  apply odeMaximalNoRightCluster isOpen_univ hfcont.continuousOn hlocal m hmax hb
    (fun n ↦ hIco (hu n)) hut (p := (b, y))
  · simpa only [Function.comp_apply] using hut.prodMk_nhds hy
  · trivial

/-- **Global existence and uniqueness for globally Lipschitz ODEs.** Let $E$ be a real Banach
space, let $f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be such that
$f(t, \cdot)$ is $L$-Lipschitz for every $t \in \mathbb{R}$. Then for every $t_0 \in \mathbb{R}$
and $x_0 \in E$ there is exactly one function $x : \mathbb{R} \to E$ with $x(t_0) = x_0$ and
$x'(t) = f(t, x(t))$ for every $t \in \mathbb{R}$.

Proof: local Picard--Lindelöf solutions are continued using the Gronwall bound of Teschl's
Theorem 2.17 and the extension criterion of Lemma 2.14.  Time reversal supplies the
negative-time solution, and global Gronwall uniqueness identifies every solution with the glued
one.

Proves `Wanted` entry `ode_global_exists_of_global_lipschitz`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential equations`, entry `maximal solutions` (unmapped);
G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.2;
stable ref https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem.
-/
theorem ode_global_exists_of_global_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (L : NNReal)
    (hfcont : Continuous (Function.uncurry f))
    (hlip : ∀ t, LipschitzWith L (f t)) :
    ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t, HasDerivAt x (f t (x t)) t := by
  have hlocal : ∀ p ∈ (Set.univ : Set (ℝ × E)), ∃ D : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ Set.univ → (t, y) ∈ s ∩ Set.univ →
        dist (Function.uncurry f (t, x)) (Function.uncurry f (t, y)) ≤ D * dist x y := by
    intro p _
    refine ⟨L, Set.univ, univ_mem, ?_⟩
    intro t x y _ _
    exact (hlip t).dist_le_mul x y
  obtain ⟨m, hmax⟩ := odeMaximalGreatestCandidate (t₀ := t₀) (x₀ := x₀)
    isOpen_univ trivial hfcont.continuousOn hlocal
  have hmUnbounded := odeMaximalGlobalNotBddAbove hfcont hlip m hmax
  let g : ℝ → E → E := fun t x ↦ -f (-t) x
  have hgcont : Continuous (Function.uncurry g) := by
    change Continuous (fun p : ℝ × E ↦ -f (-p.1) p.2)
    fun_prop
  have hglip : ∀ t, LipschitzWith L (g t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [g, dist_neg_neg] using (hlip (-t)).dist_le_mul x y
  have hglocal : ∀ p ∈ (Set.univ : Set (ℝ × E)), ∃ D : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ Set.univ → (t, y) ∈ s ∩ Set.univ →
        dist (Function.uncurry g (t, x)) (Function.uncurry g (t, y)) ≤ D * dist x y := by
    intro p _
    refine ⟨L, Set.univ, univ_mem, ?_⟩
    intro t x y _ _
    exact (hglip t).dist_le_mul x y
  obtain ⟨mr, hmaxr⟩ := odeMaximalGreatestCandidate (t₀ := -t₀) (x₀ := x₀)
    isOpen_univ trivial hgcont.continuousOn hglocal
  have hmrUnbounded := odeMaximalGlobalNotBddAbove hgcont hglip mr hmaxr
  let J : Set ℝ := {t | -t ∈ mr.I}
  let y : ℝ → E := fun t ↦ mr.x (-t)
  have hJopen : IsOpen J := mr.solution.isOpen.preimage continuous_id.neg
  have hJord : J.OrdConnected := by
    rw [ordConnected_iff]
    intro a ha b hb _ t ht
    change -a ∈ mr.I at ha
    change -b ∈ mr.I at hb
    change -t ∈ mr.I
    exact mr.solution.ordConnected.out hb ha ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  have hJmem : t₀ ∈ J := by
    change -t₀ ∈ mr.I
    exact mr.mem_domain
  have hyinitial : y t₀ = x₀ := by
    change mr.x (-t₀) = x₀
    exact mr.initial
  have hyderiv : ∀ t ∈ J, HasDerivAt y (f t (y t)) t := by
    intro t ht
    change -t ∈ mr.I at ht
    have h := (mr.solution.hasDerivAt (-t) ht).scomp t (hasDerivAt_neg t)
    simpa only [y, g, Function.comp_def, Function.uncurry_apply_pair, neg_neg, neg_smul,
      one_smul] using h
  have hysol : OdeMaximalSolutionOn Set.univ (Function.uncurry f) J y := {
    isOpen := hJopen
    ordConnected := hJord
    graph_mem := fun _ _ ↦ trivial
    hasDerivAt := hyderiv }
  obtain ⟨z, hzsol, hzm, hzy⟩ := odeMaximalSolutionOnGlue hlocal m.solution hysol
    m.mem_domain hJmem (m.initial.trans hyinitial.symm)
  have hall : ∀ t : ℝ, t ∈ m.I ∪ J := by
    intro t
    by_cases ht : t₀ ≤ t
    · rw [not_bddAbove_iff] at hmUnbounded
      obtain ⟨u, hu, htu⟩ := hmUnbounded t
      exact Or.inl (m.solution.ordConnected.out m.mem_domain hu ⟨ht, htu.le⟩)
    · rw [not_bddAbove_iff] at hmrUnbounded
      obtain ⟨u, hu, htu⟩ := hmrUnbounded (-t)
      have hnegu : -u ∈ J := by
        change -(-u) ∈ mr.I
        simpa only [neg_neg] using hu
      exact Or.inr (hJord.out hnegu hJmem ⟨by linarith, le_of_not_ge ht⟩)
  have hzinitial : z t₀ = x₀ := (hzm m.mem_domain).trans m.initial
  have hzderiv : ∀ t, HasDerivAt z (f t (z t)) t := fun t ↦ hzsol.hasDerivAt t (hall t)
  refine ⟨z, ⟨hzinitial, hzderiv⟩, ?_⟩
  intro w hw
  apply ODE_solution_unique_univ (K := L) (v := f) (s := fun _ ↦ Set.univ)
  · exact fun t ↦ (hlip t).lipschitzOnWith
  · exact fun t ↦ ⟨hw.2 t, trivial⟩
  · exact fun t ↦ ⟨hzderiv t, trivial⟩
  · exact hw.1.trans hzinitial.symm

/-- **Solutions of locally Lipschitz ODEs that leave every compact set.** Let $E$ be a real
Banach space, let $U \subseteq \mathbb{R} \times E$ be open, let $(t_0, x_0) \in U$, and let
$f : \mathbb{R} \times E \to E$ be continuous on $U$ and locally Lipschitz in the state variable,
uniformly in time: every $p \in U$ has a neighbourhood $N$ and a constant $C \ge 0$ such that
$\|f(t, u) - f(t, w)\| \le C \|u - w\|$ whenever $(t, u)$ and $(t, w)$ lie in $N \cap U$. Then
there are an open interval $I$ (possibly unbounded) containing $t_0$ and a function
$x : \mathbb{R} \to E$ with $x(t_0) = x_0$ such that $(t, x(t)) \in U$ and
$x'(t) = f(t, x(t))$ for every $t \in I$, and such that for every compact $K \subseteq U$ there
are $c_1, c_2 \in I$ with $(t, x(t)) \notin K$ for every $t \in I$ with $t \ge c_1$ and for
every $t \in I$ with $t \le c_2$.

Proof: local Picard--Lindelöf solutions are glued by uniqueness into Teschl's maximal solution
(Theorem 2.13).  A compactly recurrent finite endpoint extends by Lemma 2.14, giving the two exit
statements of Corollaries 2.15--2.16.

Proves `Wanted` entry `ode_maximal_solution_exit_compact`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential equations`, entries `maximal solutions` and
`exit theorem of a compact subspace` (unmapped);
G. Teschl, Ordinary Differential Equations and Dynamical Systems,
Section 2.4.
-/
theorem ode_maximal_solution_exit_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : Set (ℝ × E)) (f : ℝ × E → E) (t₀ : ℝ) (x₀ : E)
    (hU : IsOpen U) (hmem : (t₀, x₀) ∈ U)
    (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y) :
    ∃ I : Set ℝ, ∃ x : ℝ → E, x t₀ = x₀ ∧ IsOpen I ∧ t₀ ∈ I ∧
      (∀ t₁ ∈ I, ∀ t₂ ∈ I, Set.Icc t₁ t₂ ⊆ I) ∧
      (∀ t ∈ I, (t, x t) ∈ U ∧ HasDerivAt x (f (t, x t)) t) ∧
      ∀ K : Set (ℝ × E), IsCompact K → K ⊆ U →
        (∃ c ∈ I, ∀ t ∈ I, c ≤ t → (t, x t) ∉ K) ∧
        ∃ c ∈ I, ∀ t ∈ I, t ≤ c → (t, x t) ∉ K := by
  obtain ⟨m, hmax⟩ := odeMaximalGreatestCandidate hU hmem hf hlip
  refine ⟨m.I, m.x, m.initial, m.solution.isOpen, m.mem_domain, ?_, ?_, ?_⟩
  · intro t₁ ht₁ t₂ ht₂
    exact m.solution.ordConnected.out ht₁ ht₂
  · intro t ht
    exact ⟨m.solution.graph_mem t ht, m.solution.hasDerivAt t ht⟩
  · intro K hK hKU
    exact ⟨odeMaximalExitRight hU hf hlip m hmax K hK hKU,
      odeMaximalExitLeft hU hf hlip m hmax K hK hKU⟩

end MathlibExt.Analysis.ODE.MaximalSolutionWanted
