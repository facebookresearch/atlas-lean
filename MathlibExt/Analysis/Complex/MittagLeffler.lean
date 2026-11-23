/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

@[expose] public section

open scoped BigOperators Topology ENNReal NNReal
open Metric



section
/-!
# Mittag-Leffler theorem (prescribed principal parts on `ℂ`)
-/

namespace MathlibExt.Analysis.Complex.MittagLefflerWanted

/--
**Principal part with finitely many coefficients.** For a point $s \in \mathbb{C}$ and a finitely
supported sequence $c = (c_k)_{k \in \mathbb{N}}$ of complex coefficients, the principal part at
$s$ with coefficients $c$ is the function $\mathbb{C} \to \mathbb{C}$ given by
$z \mapsto \sum_k c_k (z - s)^{-(k+1)}$, the sum running over the finitely many $k$ with
$c_k \neq 0$.

At $z = s$ every term is taken to be $0$ (the convention $0^{-n} = 0$), so the function has value
$0$ there.
-/
noncomputable def principalPart (s : ℂ) (coeff : ℕ →₀ ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ coeff.support, coeff k * (z - s) ^ (-(↑k + 1) : ℤ)

/-- **The principal part is analytic away from its pole.** For every $s \in \mathbb{C}$ and every
finitely supported sequence $c$ of complex coefficients, the principal part at $s$ with
coefficients $c$ is analytic at every point $z \neq s$. -/
theorem principalPart_analyticAt (s : ℂ) (coeff : ℕ →₀ ℂ) (z : ℂ) (hz : z ≠ s) :
    AnalyticAt ℂ (principalPart s coeff) z := by
  unfold principalPart
  apply Finset.analyticAt_fun_sum
  intro k _
  apply AnalyticAt.mul analyticAt_const
  have h1 : AnalyticAt ℂ (fun w : ℂ => w - s) z := analyticAt_id.sub analyticAt_const
  have h2 : (fun w : ℂ => w - s) z ≠ 0 := by simpa [sub_eq_zero] using hz
  exact h1.zpow h2

/-- The principal part is differentiable on any closed ball around `0` not reaching its pole. -/
private theorem principalPart_differentiableOn_closedBall (s : ℂ) (coeff : ℕ →₀ ℂ) (R : ℝ)
    (hR : R < ‖s‖) : DifferentiableOn ℂ (principalPart s coeff) (closedBall 0 R) := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm, sub_zero] at hz
  have hzne : z ≠ s := by
    intro h; rw [h] at hz; linarith
  exact (principalPart_analyticAt s coeff z hzne).differentiableAt.differentiableWithinAt

/-- A partial sum of a formal multilinear power series is analytic everywhere. -/
private theorem partialSum_analyticAt (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (w : ℂ) :
    AnalyticAt ℂ (p.partialSum n) w := by
  unfold FormalMultilinearSeries.partialSum
  apply Finset.analyticAt_fun_sum
  intro i _
  have hdiag : AnalyticAt ℂ (fun x : ℂ => (fun _ : Fin i => x)) w :=
    (ContinuousLinearMap.pi (fun _ : Fin i => ContinuousLinearMap.id ℂ ℂ)).analyticAt w
  exact ((p i).analyticAt (x := fun _ : Fin i => w)).comp hdiag

/-- Any holomorphic function on a closed ball is uniformly approximable, on a smaller disk, by an
entire function (a partial sum of its Taylor series). -/
private theorem trunc (F : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (closedBall 0 R))
    (r' : ℝ) (hr'0 : 0 ≤ r') (hr' : r' < R) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℂ → ℂ, (∀ w, AnalyticAt ℂ Q w) ∧ ∀ z ∈ ball (0 : ℂ) r', ‖F z - Q z‖ ≤ ε := by
  lift R to ℝ≥0 using hR.le with R'
  lift r' to ℝ≥0 using hr'0 with r''
  have hp := hF.hasFPowerSeriesOnBall (by exact_mod_cast hR)
  have hlt : (r'' : ℝ≥0∞) < (R' : ℝ≥0∞) := by exact_mod_cast hr'
  have hunif := hp.tendstoUniformlyOn hlt
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := (hunif ε hε).exists
  refine ⟨fun z => (cauchyPowerSeries F 0 R').partialSum N z,
    fun w => partialSum_analyticAt _ _ _, ?_⟩
  intro z hz
  have hd := hN z hz
  simp only [zero_add, dist_eq_norm] at hd
  exact hd.le

/-- The Mittag-Leffler correction term at pole `s`: an entire `Q` with `principalPart s coeff - Q`
uniformly small on the disk `ball 0 (‖s‖/2)`. -/
private theorem exists_correction (s : ℂ) (coeff : ℕ →₀ ℂ) (weight : ℝ) (hw : 0 < weight) :
    ∃ Q : ℂ → ℂ, (∀ w, AnalyticAt ℂ Q w) ∧
      ∀ z ∈ ball (0 : ℂ) (‖s‖ / 2), ‖principalPart s coeff z - Q z‖ ≤ weight := by
  rcases eq_or_lt_of_le (norm_nonneg s) with h0 | h0
  · refine ⟨fun _ => 0, fun _ => analyticAt_const, ?_⟩
    intro z hz
    rw [mem_ball, dist_eq_norm, sub_zero, ← h0] at hz
    simp only [zero_div] at hz
    exact absurd hz (not_lt.mpr (norm_nonneg z))
  · exact trunc (principalPart s coeff) (3 * ‖s‖ / 4) (by linarith)
      (principalPart_differentiableOn_closedBall s coeff (3 * ‖s‖ / 4) (by linarith))
      (‖s‖ / 2) (by positivity) (by linarith) weight hw

/-- **The principal part is meromorphic.** For every $s \in \mathbb{C}$ and every finitely
supported sequence $c$ of complex coefficients, the principal part at $s$ with coefficients $c$ is
meromorphic at every point of $\mathbb{C}$. -/
theorem principalPart_meromorphicAt (s : ℂ) (coeff : ℕ →₀ ℂ) (x : ℂ) :
    MeromorphicAt (principalPart s coeff) x := by
  unfold principalPart
  apply MeromorphicAt.fun_sum
  intro k _
  exact (MeromorphicAt.const (coeff k) x).mul
    (((MeromorphicAt.id x).sub (MeromorphicAt.const s x)).zpow _)

/--
**Mittag-Leffler theorem, discrete-subspace form.** Let $S \subseteq \mathbb{C}$ be a closed set
that is discrete in the subspace topology, and for each $s \in S$ let $c_s$ be a finitely supported
sequence of complex coefficients. Then there is a function $f : \mathbb{C} \to \mathbb{C}$ that is
holomorphic on $\mathbb{C} \setminus S$, meromorphic on all of $\mathbb{C}$, and such that for every
$s \in S$ the difference between $f$ and the principal part at $s$ with coefficients $c_s$ is
analytic at $s$.
-/
theorem mittag_leffler_of_isDiscrete
    (S : Set ℂ) (hS_closed : IsClosed S)
    (hSdisc : IsDiscrete S)
    (coeff : ↥S → ℕ →₀ ℂ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Sᶜ ∧
      (∀ s : ↥S, AnalyticAt ℂ (fun z => f z - principalPart s.val (coeff s) z) s.val) ∧
      MeromorphicOn f Set.univ := by
  have hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅ := by
    intro z hz
    obtain ⟨U, hU, hUS⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hSdisc z hz
    have hzU : z ∈ U ∩ S := by rw [hUS]; rfl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hzU.1
    refine ⟨ε, hε, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
    rintro w ⟨⟨hw, hne⟩, hwS⟩
    have hwUS : w ∈ U ∩ S := ⟨hball hw, hwS⟩
    rw [hUS] at hwUS
    exact hne hwUS
  have hdt : DiscreteTopology ↥S := isDiscrete_iff_discreteTopology.mp hSdisc
  have hcount : Countable ↥S := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ↥S
  set w : ↥S → ℝ := fun s => (1 / 2 : ℝ) ^ (e s) with hw_def
  have hw_pos : ∀ s, 0 < w s := fun s => by positivity
  have hw_sum : Summable w := by
    simpa [hw_def, Function.comp_def] using summable_geometric_two.comp_injective he
  choose Qfun hQ_an hQ_bd using fun s : ↥S => exists_correction s.val (coeff s) (w s) (hw_pos s)
  set g : ↥S → ℂ → ℂ := fun s z => principalPart s.val (coeff s) z - Qfun s z with hg_def
  have hLF : ∀ C : ℝ, {s : ↥S | ‖(s : ℂ)‖ ≤ C}.Finite := by
    intro C
    have hcpt : IsCompact (closedBall (0 : ℂ) C ∩ S) :=
      (isCompact_closedBall 0 C).inter_right hS_closed
    have hfin : (closedBall (0 : ℂ) C ∩ S).Finite :=
      hcpt.finite (hSdisc.mono Set.inter_subset_right)
    have hset : {s : ↥S | ‖(s : ℂ)‖ ≤ C} = Subtype.val ⁻¹' (closedBall (0 : ℂ) C ∩ S) := by
      ext s
      simp [mem_closedBall, dist_eq_norm, sub_zero]
    rw [hset]
    exact hfin.preimage (Subtype.val_injective.injOn)
  have hopen : IsOpen Sᶜ := hS_closed.isOpen_compl
  have hdiffOn : DifferentiableOn ℂ (fun z => ∑' s, g s z) Sᶜ := by
    have hSLU : SummableLocallyUniformlyOn g Sᶜ := by
      apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hopen
      intro K hKsub hKcpt
      obtain ⟨M, hM⟩ := hKcpt.isBounded.subset_closedBall 0
      refine ⟨w, hw_sum, ?_⟩
      rw [Filter.eventually_cofinite]
      refine (hLF (2 * M)).subset ?_
      intro s hs
      simp only [Set.mem_ofPred_eq] at hs ⊢
      by_contra hcon
      rw [not_le] at hcon
      apply hs
      intro k hk
      have hkM : ‖k‖ ≤ M := by
        have hkc := hM hk
        rwa [mem_closedBall, dist_eq_norm, sub_zero] at hkc
      have hkball : k ∈ ball (0 : ℂ) (‖(s : ℂ)‖ / 2) := by
        rw [mem_ball, dist_eq_norm, sub_zero]
        linarith
      simpa [hg_def] using hQ_bd s k hkball
    have hdiff : ∀ (s : ↥S) (r : ℂ), r ∈ Sᶜ → DifferentiableAt ℂ (g s) r := by
      intro s r hr
      have hrs : r ≠ s.val := fun h => hr (h ▸ s.2)
      have h1 : DifferentiableAt ℂ (fun z => principalPart s.val (coeff s) z) r :=
        (principalPart_analyticAt s.val (coeff s) r hrs).differentiableAt
      have h2 : DifferentiableAt ℂ (Qfun s) r := (hQ_an s r).differentiableAt
      exact h1.sub h2
    exact SummableLocallyUniformlyOn.differentiableOn hopen hSLU hdiff
  have hP2 : ∀ s₀ : ↥S, AnalyticAt ℂ
      (fun z => (∑' s, g s z) - principalPart s₀.val (coeff s₀) z) s₀.val := by
    intro s₀
    classical
    obtain ⟨ρ, hρ, hballρ⟩ := hS_discrete s₀.val s₀.2
    have hnotin : ∀ t : ↥S, t ≠ s₀ → (t : ℂ) ∉ ball s₀.val ρ := by
      intro t htne hmem
      have h1 : (t : ℂ) ≠ s₀.val := fun h => htne (Subtype.ext h)
      have hmem2 : (t : ℂ) ∈ (ball s₀.val ρ \ {s₀.val}) ∩ S := ⟨⟨hmem, h1⟩, t.2⟩
      rw [hballρ] at hmem2
      exact hmem2
    have hballopen : IsOpen (ball s₀.val ρ) := isOpen_ball
    have hSLU : SummableLocallyUniformlyOn
        (fun t z => if t = s₀ then (0 : ℂ) else g t z) (ball s₀.val ρ) := by
      apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hballopen
      intro K hKsub hKcpt
      obtain ⟨M, hM⟩ := hKcpt.isBounded.subset_closedBall 0
      refine ⟨w, hw_sum, ?_⟩
      rw [Filter.eventually_cofinite]
      refine (hLF (2 * M)).subset ?_
      intro t ht
      simp only [Set.mem_ofPred_eq] at ht ⊢
      by_contra hcon
      rw [not_le] at hcon
      apply ht
      intro k hk
      by_cases htt : t = s₀
      · rw [ite_eq_left htt, norm_zero]; exact (hw_pos t).le
      · have hkM : ‖k‖ ≤ M := by
          have hkc := hM hk
          rwa [mem_closedBall, dist_eq_norm, sub_zero] at hkc
        have hkball : k ∈ ball (0 : ℂ) (‖(t : ℂ)‖ / 2) := by
          rw [mem_ball, dist_eq_norm, sub_zero]; linarith
        simp only [ite_eq_right htt]
        simpa [hg_def] using hQ_bd t k hkball
    have hdiff : ∀ (t : ↥S) (r : ℂ), r ∈ ball s₀.val ρ →
        DifferentiableAt ℂ (fun z => if t = s₀ then (0 : ℂ) else g t z) r := by
      intro t r hr
      by_cases htt : t = s₀
      · simp only [ite_eq_left htt]; exact differentiableAt_const 0
      · have hrne : r ≠ (t : ℂ) := fun h => hnotin t htt (h ▸ hr)
        have hd1 := (principalPart_analyticAt t.val (coeff t) r hrne).differentiableAt
        have hd2 := (hQ_an t r).differentiableAt
        simp only [ite_eq_right htt, hg_def]
        exact hd1.sub hd2
    have hTan : AnalyticAt ℂ (fun z => ∑' t, if t = s₀ then (0 : ℂ) else g t z) s₀.val :=
      (SummableLocallyUniformlyOn.differentiableOn hballopen hSLU hdiff).analyticAt
        (hballopen.mem_nhds (mem_ball_self hρ))
    have hfsum : ∀ z ∈ ball s₀.val ρ, Summable (fun t => g t z) := by
      obtain ⟨G, hG⟩ := hSLU
      rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hG
      intro z hz
      have hhs : HasSum (fun t => if t = s₀ then (0 : ℂ) else g t z) (G z) :=
        hG.tendsto_at hz
      have hgi : Summable (fun t => if t = s₀ then (0 : ℂ) else g t z) := hhs.summable
      have hfin : Summable (fun t => if t = s₀ then g t z else (0 : ℂ)) :=
        summable_of_ne_finset_zero (s := {s₀}) (fun b hb => by rw [ite_eq_right]; simpa using hb)
      refine (hgi.add hfin).congr (fun t => ?_)
      by_cases htt : t = s₀ <;> simp [htt]
    refine (hTan.sub (hQ_an s₀ s₀.val)).congr ?_
    filter_upwards [hballopen.mem_nhds (mem_ball_self hρ)] with z hz
    have hsplit := (hfsum z hz).tsum_eq_add_tsum_ite s₀
    change (∑' t, if t = s₀ then (0 : ℂ) else g t z) - Qfun s₀ z
        = (∑' t, g t z) - principalPart s₀.val (coeff s₀) z
    rw [hsplit]
    change (∑' t, if t = s₀ then (0 : ℂ) else g t z) - Qfun s₀ z
        = (g s₀ z + ∑' t, if t = s₀ then (0 : ℂ) else g t z)
          - principalPart s₀.val (coeff s₀) z
    simp only [hg_def]
    ring
  refine ⟨fun z => ∑' s, g s z, hdiffOn, hP2, ?_⟩
  intro x _
  by_cases hx : x ∈ S
  · have hmero : MeromorphicAt
        (fun z => (∑' s, g s z) - principalPart (⟨x, hx⟩ : ↥S).val (coeff ⟨x, hx⟩) z) x :=
      (hP2 ⟨x, hx⟩).meromorphicAt
    have hpp : MeromorphicAt (principalPart (⟨x, hx⟩ : ↥S).val (coeff ⟨x, hx⟩)) x :=
      principalPart_meromorphicAt _ _ x
    refine (hmero.add hpp).congr ?_
    filter_upwards with z
    simp only [Pi.add_apply, sub_add_cancel]
  · exact (hdiffOn.analyticAt (hopen.mem_nhds hx)).meromorphicAt

/--
**Mittag-Leffler theorem.** Let $S \subseteq \mathbb{C}$ be a closed set such that every $z \in S$
has a radius $\varepsilon > 0$ for which the punctured disk $\{w : 0 < |w - z| < \varepsilon\}$
contains no point of $S$, and for each $s \in S$ let $c_s$ be a finitely supported sequence of
complex coefficients. Then there is a function $f : \mathbb{C} \to \mathbb{C}$ that is holomorphic
on $\mathbb{C} \setminus S$, meromorphic on all of $\mathbb{C}$, and such that for every $s \in S$
the difference between $f$ and the principal part at $s$ with coefficients $c_s$ is analytic at
$s$.

Proves `Wanted` entry `mittag_leffler`.

Source: Mittag-Leffler theorem, G. Mittag-Leffler, Acta Math. 4 (1884); see Rudin;
Lean is closed discrete S with punctured-ball isolation, prescribed finite principal parts via
Finsupp, global meromorphic existence holomorphic on Sᶜ.
-/
theorem mittag_leffler
    (S : Set ℂ) (hS_closed : IsClosed S)
    (hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅)
    (coeff : ↥S → ℕ →₀ ℂ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Sᶜ ∧
      (∀ s : ↥S, AnalyticAt ℂ (fun z => f z - principalPart s.val (coeff s) z) s.val) ∧
      MeromorphicOn f Set.univ := by
  have hSdisc : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro y hy
    obtain ⟨ε, hε, hball⟩ := hS_discrete y hy
    refine ⟨ball y ε, isOpen_ball, ?_⟩
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨mem_ball_self hε, hy⟩, ?_⟩
    intro w hw
    by_contra hne
    have hmem : w ∈ (ball y ε \ {y}) ∩ S := ⟨⟨hw.1, hne⟩, hw.2⟩
    rw [hball] at hmem
    exact hmem
  exact mittag_leffler_of_isDiscrete S hS_closed hSdisc coeff

end MathlibExt.Analysis.Complex.MittagLefflerWanted
