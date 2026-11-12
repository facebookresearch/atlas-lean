/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Path conditional expectation for independent increments

For an adapted real process whose future increments are independent of the filtration,
a bounded measurable functional of `t ↦ B (s + t)` has conditional expectation given
`ℱ s` obtained from the centered future law at the absolute time `s` and state `B s`.
The expectation is time dependent: it integrates against the law of
`t ↦ B (s + t) - B s`, which can vary with `s`.

## Relation to the archive

This is a generic independent-increments identity related to
`v1/Atlas/TheoryOfProbability/code/MarkovPropertyBM.lean`. The Lecture 37 target
in `v1/Atlas/TheoryOfProbability/targets.yaml`, namely the stationary Brownian/Wiener
expectation under `P_x` conditioned on `ℱ_s⁺`, remains deferred. Stationary Wiener law,
right-continuous-filtration conditioning, arbitrary starting laws, and the general
`ℝᵈ` target are not established here.

The archived structure called `IsBrownianMotion` records zero start, adaptedness,
independence, continuous paths, and measurable increments. It has no Gaussian or
stationarity field. Its name and the accompanying law description are not a faithful
Brownian specification.

## API

The canonical results are `independent_increments_lintegral_shift`,
`independent_increments_setIntegral`, and `independent_increments_condExp`.
The legacy `bm` helper names describe arbitrary real processes and remain available
for source compatibility. `MathlibExt.Probability.BrownianMarkovProperty` re-exports
the historical names; those aliases carry this generic conclusion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology MeasureTheory Classical

namespace MathlibExt.Probability.IndependentIncrementsMarkovProperty

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 m0}

/-- **Predecessor of a time in a finite set.** For a finite set $S \subseteq \mathbb{R}_{\ge 0}$ and
$t \in \mathbb{R}_{\ge 0}$, the predecessor of $t$ in $S$ is the largest element of $S$ strictly
below $t$, or $0$ if there is no such element. -/
noncomputable def bmPrev (S : Finset ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  (S.filter (· < t)).sup id

/-- **Increment over the predecessor interval.** Let $(B_t)_{t \ge 0}$ be a real-valued process
on $\Omega$, let $s \ge 0$, and let $S \subset \mathbb{R}_{\ge 0}$ be a finite set. For $t \ge 0$
let $t^-$ be the largest element of $S$ strictly below $t$, or $0$ if there is none. The
increment at $t$ is the random variable $\omega \mapsto B_{s+t}(\omega) - B_{s+t^-}(\omega)$. -/
noncomputable def bmInc (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (S : Finset ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  B (s + t) ω - B (s + bmPrev S t) ω

/-- **Shifted path of a process.** For a real-valued process $(B_t)_{t \ge 0}$ on $\Omega$
indexed by $t \in \mathbb{R}_{\ge 0}$ and a time $s \ge 0$, the shifted path is the map sending
$\omega \in \Omega$ to the path $t \mapsto B_{s+t}(\omega)$ in $\mathbb{R}^{\mathbb{R}_{\ge 0}}$. -/
noncomputable def bmShifted (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : Ω → (ℝ≥0 → ℝ) :=
  fun ω t => B (s + t) ω

/-- **Centered shifted path.** Let $(B_t)_{t \ge 0}$ be a real-valued process on $\Omega$ and
let $s \ge 0$. The centered shifted path at time $s$ sends $\omega \in \Omega$ to the function
$t \mapsto B_{s+t}(\omega) - B_s(\omega)$ on $\mathbb{R}_{\ge 0}$. -/
noncomputable def bmCenteredShift (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
    Ω → (ℝ≥0 → ℝ) :=
  fun ω t => B (s + t) ω - B s ω

/-- **Law of the centered shifted path.** Let $(B_t)_{t \ge 0}$ be a real-valued process on a
measure space $(\Omega, \mu)$ and let $s \ge 0$. This is the pushforward of $\mu$ under the map
sending $\omega \in \Omega$ to the path $t \mapsto B_{s+t}(\omega) - B_s(\omega)$, a measure on
the space of functions $\mathbb{R}_{\ge 0} \to \mathbb{R}$ with its product σ-algebra. -/
noncomputable def bmCenteredLaw (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) (s : ℝ≥0) :
    Measure (ℝ≥0 → ℝ) :=
  Measure.map (bmCenteredShift B s) μ

/-- **Time-dependent path expectation.** Let $\mu$ be a measure on $\Omega$, let
$(B_t)_{t \ge 0}$ be a real process on $\Omega$ indexed by $t \in \mathbb{R}_{\ge 0}$, let
$s \ge 0$, and let $\nu_s$ be the law under $\mu$ (the pushforward of $\mu$) of the centered
shifted path $\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$. For a real function $Y$
on paths $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and $x \in \mathbb{R}$, the path expectation is the
Bochner integral $\int Y(t \mapsto x + f(t))\, d\nu_s(f)$, which is $0$ when the integrand is
not integrable.

This value can depend on $s$; it is the generic time-dependent expectation. -/
noncomputable def bmPathExpectation (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) (s : ℝ≥0)
    (Y : (ℝ≥0 → ℝ) → ℝ) (x : ℝ) : ℝ :=
  ∫ f, Y (fun t => x + f t) ∂(bmCenteredLaw B μ s)

/-- **Adapted real process.** A real-valued process $(B_t)_{t \ge 0}$ on $\Omega$, indexed by
$t \in \mathbb{R}_{\ge 0}$, is adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ when $B_t$ is
$\mathcal{F}_t$-measurable for every $t \ge 0$. -/
abbrev BmAdapted (B : ℝ≥0 → Ω → ℝ) (ℱ : Filtration ℝ≥0 m0) : Prop :=
  ∀ t, Measurable[ℱ t] (B t)

/-- **Independent increments with respect to a filtration.** A real-valued process
$(B_t)_{t \ge 0}$ on $\Omega$ has independent increments with respect to a filtration
$(\mathcal{F}_t)_{t \ge 0}$ and a measure $\mu$ when, for all $0 \le s \le t$, the σ-algebra
generated by $B_t - B_s$ is independent of $\mathcal{F}_s$ under $\mu$. -/
abbrev BmIndepIncrements (B : ℝ≥0 → Ω → ℝ) (ℱ : Filtration ℝ≥0 m0)
    (μ : Measure Ω) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ

/-- **Measurability of the shifted path.** Let $B = (B_t)_{t \ge 0}$ be a real process on a
measurable space $\Omega$, adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ of its σ-algebra,
and give the space $\mathbb{R}^{[0, \infty)}$ of real paths indexed by $t \ge 0$ the product
σ-algebra. For every $s \ge 0$, the map from $\Omega$ to $\mathbb{R}^{[0, \infty)}$ sending
$\omega$ to the path $t \mapsto B_{s+t}(\omega)$ is measurable.

Each coordinate $B_{s+t}$ is $\mathcal{F}_{s+t}$-measurable, hence measurable. -/
lemma measurable_bmShifted (hAd : BmAdapted B ℱ) (s : ℝ≥0) :
    Measurable (bmShifted B s) := by
  apply Measurable.of_eval
  intro t
  show Measurable fun ω => B (s + t) ω
  exact (hAd (s + t)).mono (Filtration.le ℱ (s + t)) le_rfl

/-- **Measurability of the centered shifted path.** Let $(\mathcal{F}_t)_{t \ge 0}$ be a
filtration on a measurable space $\Omega$ indexed by $\mathbb{R}_{\ge 0}$, and let
$(B_t)_{t \ge 0}$ be a real-valued process adapted to it (each $B_t$ is
$\mathcal{F}_t$-measurable). Then for every $s \ge 0$ the map
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$ from $\Omega$ to
$\mathbb{R}^{\mathbb{R}_{\ge 0}}$, with the product σ-algebra, is measurable. -/
lemma measurable_bmCenteredShift (hAd : BmAdapted B ℱ) (s : ℝ≥0) :
    Measurable (bmCenteredShift B s) := by
  apply Measurable.of_eval
  intro t
  show Measurable fun ω => B (s + t) ω - B s ω
  exact Measurable.sub ((hAd (s + t)).mono (Filtration.le ℱ (s + t)) le_rfl)
    ((hAd s).mono (Filtration.le ℱ s) le_rfl)

/-- The law of the centered shifted path is a probability measure. -/
instance bmCenteredLaw_isProbabilityMeasure [IsProbabilityMeasure μ] (s : ℝ≥0) :
    IsProbabilityMeasure (bmCenteredLaw B μ s) := by
  unfold bmCenteredLaw
  infer_instance

/-- **Measurability of an increment before a given time.** Let $B = (B_t)_{t \ge 0}$ be a real
process on a measurable space $\Omega$, adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ of its
σ-algebra, let $S$ be a finite set of nonnegative reals and let $s, t, u \ge 0$. Write $p_S(t)$
for the largest element of $S$ strictly below $t$, or $0$ if there is none. If $s + t \le s + u$
and $s + p_S(t) \le s + u$, then the increment $B_{s+t} - B_{s+p_S(t)}$ is
$\mathcal{F}_{s+u}$-measurable. -/
lemma measurable_bmInc_of_le (hAd : BmAdapted B ℱ) {s u t : ℝ≥0}
    (S : Finset ℝ≥0) (ht : s + t ≤ s + u) (hprev : s + bmPrev S t ≤ s + u) :
    Measurable[ℱ (s + u)] (fun ω => bmInc B s S t ω) := by
  show Measurable[ℱ (s + u)] (fun ω => B (s + t) ω - B (s + bmPrev S t) ω)
  exact Measurable.sub ((hAd (s + t)).mono (Filtration.mono ℱ ht) le_rfl)
    ((hAd (s + bmPrev S t)).mono (Filtration.mono ℱ hprev) le_rfl)

/-- **Inserting a larger element does not change the predecessor.** For a finite set
$T \subseteq \mathbb{R}_{\ge 0}$ and $t \in \mathbb{R}_{\ge 0}$, call the largest element of $T$
strictly below $t$ (or $0$ if there is none) the predecessor of $t$ in $T$. Let
$S \subseteq \mathbb{R}_{\ge 0}$ be finite and let $t, a \in \mathbb{R}_{\ge 0}$ with $t < a$.
Then the predecessor of $t$ in $S \cup \{a\}$ equals the predecessor of $t$ in $S$. -/
lemma bmPrev_insert_of_lt {a : ℝ≥0} {S' : Finset ℝ≥0} {t : ℝ≥0} (ht : t < a) :
    bmPrev (insert a S') t = bmPrev S' t := by
  unfold bmPrev
  rw [Finset.filter_insert]
  simp only [ite_eq_right (not_lt_of_ge ht.le)]

/-- **Predecessor of a new maximum.** For a finite set $T \subseteq \mathbb{R}_{\ge 0}$ and
$t \in \mathbb{R}_{\ge 0}$, call the largest element of $T$ strictly below $t$ (or $0$ if there
is none) the predecessor of $t$ in $T$. Let $S \subseteq \mathbb{R}_{\ge 0}$ be finite and let
$a \in \mathbb{R}_{\ge 0}$ with $x < a$ for every $x \in S$. Then the predecessor of $a$ in
$S \cup \{a\}$ is the supremum of $S$ in $\mathbb{R}_{\ge 0}$, that is, its largest element, or $0$
if $S$ is empty. -/
lemma bmPrev_insert_self {a : ℝ≥0} {S' : Finset ℝ≥0}
    (h : ∀ x ∈ S', x < a) :
    bmPrev (insert a S') a = S'.sup id := by
  unfold bmPrev
  rw [Finset.filter_insert]
  simp only [ite_eq_right (lt_irrefl a), Finset.filter_true_of_mem h]

/-- **Past events factor against grid increments.** Let $\mu$ be a probability measure and let
$(B_t)_{t \ge 0}$ be a real process adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ such that
$B_t - B_s$ is independent of $\mathcal{F}_s$ under $\mu$ whenever $s \le t$. Let
$s \in \mathbb{R}_{\ge 0}$ and let $S \subseteq \mathbb{R}_{\ge 0}$ be finite. For $t \in S$ let
$\Delta_t = B_{s+t} - B_{s+t^-}$, where $t^-$ is the largest element of $S$ strictly below $t$, or
$0$ if there is none. Then for every family $(C_t)_{t \ge 0}$ of Borel subsets of $\mathbb{R}$ and
every $A \in \mathcal{F}_s$,
$$\mu\Big(A \cap \bigcap_{t \in S} \{\Delta_t \in C_t\}\Big)
= \mu(A)\,\mu\Big(\bigcap_{t \in S} \{\Delta_t \in C_t\}\Big).$$

The proof is induction on $S$ by its maximum element $a$: the increment $\Delta_a$ is independent
of $\mathcal{F}_{s + a^-}$, which contains both $A$ and the earlier increments. -/
lemma measure_inter_biInter_bmInc (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) [IsProbabilityMeasure μ] (s : ℝ≥0)
    (S : Finset ℝ≥0) (C : ℝ≥0 → Set ℝ) (hC : ∀ t, MeasurableSet (C t))
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    μ (A ∩ ⋂ t ∈ S, {ω | bmInc B s S t ω ∈ C t})
      = μ A * μ (⋂ t ∈ S, {ω | bmInc B s S t ω ∈ C t}) := by
  induction S using Finset.induction_on_max with
  | empty =>
    simp
  | insert a S' hlt ih =>
    -- `a` is the maximum; write `a' = sup S'` for the predecessor of `a`.
    set a' : ℝ≥0 := S'.sup id with ha'_def
    have ha'_le : a' ≤ a := by
      rw [ha'_def]
      exact Finset.sup_le fun b hb => (hlt b hb).le
    have htle : ∀ t ∈ S', t ≤ a' := fun t ht => by
      rw [ha'_def]
      exact Finset.le_sup (f := id) ht
    -- the increments for the old set agree with those for the inserted set
    have hinc_eq : ∀ t ∈ S', ∀ ω, bmInc B s (insert a S') t ω
        = bmInc B s S' t ω := by
      intro t ht ω
      simp only [bmInc, bmPrev_insert_of_lt (hlt t ht)]
    -- the rectangles for the inserted set split as the old rectangle times
    -- the last increment's event
    have hrect_eq : (⋂ t ∈ insert a S', {ω | bmInc B s (insert a S') t ω ∈ C t})
        = (⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) ∩
          {ω | bmInc B s (insert a S') a ω ∈ C a} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h
        refine ⟨fun t ht => ?_, h a (Finset.mem_insert_self a S')⟩
        rw [← hinc_eq t ht ω]
        exact h t (Finset.mem_insert_of_mem ht)
      · rintro ⟨h1, h2⟩ t ht
        rcases Finset.mem_insert.mp ht with rfl | ht'
        · exact h2
        · rw [hinc_eq t ht' ω]
          exact h1 t ht'
    -- the last increment is the increment from `s + a'` to `s + a`
    have hinc_a : (fun ω => bmInc B s (insert a S') a ω)
        = fun ω => B (s + a) ω - B (s + a') ω := by
      funext ω
      simp only [bmInc, bmPrev_insert_self hlt, ← ha'_def]
    -- the old rectangle is `ℱ (s + a')`-measurable
    have hR'_meas : MeasurableSet[ℱ (s + a')]
        (⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) := by
      refine Finset.measurableSet_biInter S' fun t ht => ?_
      exact measurable_bmInc_of_le hAd S' (by
        have : s + t ≤ s + a' := add_le_add_right (htle t ht) s
        exact this) (by
        have h1 : bmPrev S' t ≤ a' := by
          unfold bmPrev
          apply Finset.sup_le
          intro b hb
          have hb' : b ∈ S' := (Finset.mem_filter.mp hb).1
          exact htle b hb'
        have : s + bmPrev S' t ≤ s + a' := add_le_add_right h1 s
        exact this) (hC t)
    have hA' : MeasurableSet[ℱ (s + a')] A :=
      Filtration.mono ℱ (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ a' from zero_le)) A hA
    have hFa_meas : MeasurableSet[MeasurableSpace.comap
        (fun ω => B (s + a) ω - B (s + a') ω) inferInstance]
        {ω | bmInc B s (insert a S') a ω ∈ C a} := by
      rw [show {ω | bmInc B s (insert a S') a ω ∈ C a}
          = (fun ω => B (s + a) ω - B (s + a') ω) ⁻¹' C a from by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, hinc_a]]
      exact ⟨C a, hC a, rfl⟩
    have hInd_a := hInd (s + a') (s + a) (add_le_add_right ha'_le s)
    have key1 : μ ((A ∩ ⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) ∩
        {ω | bmInc B s (insert a S') a ω ∈ C a})
        = μ (A ∩ ⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) *
          μ {ω | bmInc B s (insert a S') a ω ∈ C a} :=
      IndepSet.measure_inter_eq_mul
        (hInd_a.indepSet_of_measurableSet (MeasurableSet.inter hA' hR'_meas) hFa_meas)
    have key2 : μ ((⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) ∩
        {ω | bmInc B s (insert a S') a ω ∈ C a})
        = μ (⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) *
          μ {ω | bmInc B s (insert a S') a ω ∈ C a} :=
      IndepSet.measure_inter_eq_mul
        (hInd_a.indepSet_of_measurableSet hR'_meas hFa_meas)
    rw [hrect_eq]
    have hset : A ∩ ((⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) ∩
        {ω | bmInc B s (insert a S') a ω ∈ C a})
        = (A ∩ ⋂ t ∈ S', {ω | bmInc B s S' t ω ∈ C t}) ∩
          {ω | bmInc B s (insert a S') a ω ∈ C a} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hset, key1, ih, mul_assoc, ← key2]

/-- **Telescoping sum of grid increments.** Let $(B_t)_{t \ge 0}$ be a family of real functions
on $\Omega$, let $s \in \mathbb{R}_{\ge 0}$ and let $S \subseteq \mathbb{R}_{\ge 0}$ be a nonempty
finite set. For $u \in S$ let $\Delta_u = B_{s+u} - B_{s+u^-}$, where $u^-$ is the largest element
of $S$ strictly below $u$, or $0$ if there is none. Then for every $\omega \in \Omega$,
$\sum_{u \in S} \Delta_u(\omega) = B_{s + \max S}(\omega) - B_s(\omega)$. -/
lemma sum_bmInc_eq {s : ℝ≥0} (S : Finset ℝ≥0) (hS : S.Nonempty) (ω : Ω) :
    ∑ u ∈ S, bmInc B s S u ω = B (s + S.sup id) ω - B s ω := by
  induction S using Finset.induction_on_max with
  | empty =>
    exact absurd hS (Finset.not_nonempty_empty)
  | insert a S' hlt ih =>
    by_cases hS' : S'.Nonempty
    · have hsum : ∑ u ∈ insert a S', bmInc B s (insert a S') u ω
          = bmInc B s (insert a S') a ω + ∑ u ∈ S', bmInc B s S' u ω := by
        rw [Finset.sum_insert (fun hmem => absurd (hlt a hmem) (lt_irrefl a))]
        apply congrArg (bmInc B s (insert a S') a ω + ·)
        apply Finset.sum_congr rfl
        intro u hu
        simp only [bmInc, bmPrev_insert_of_lt (hlt u hu)]
      rw [hsum, ih hS', bmInc, bmPrev_insert_self hlt]
      have hsup : (insert a S').sup id = a := by
        rw [Finset.sup_insert]
        simp only [id_eq]
        exact max_eq_left (Finset.sup_le fun b hb => (hlt b hb).le)
      rw [hsup]
      ring
    · have hS'eq : S' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hS'eq
      have hsup : (insert a (∅ : Finset ℝ≥0)).sup id = a := by
        simp
      have hprev : bmPrev (insert a (∅ : Finset ℝ≥0)) a = 0 := by
        simp [bmPrev]
      rw [Finset.sum_insert (by simp : a ∉ (∅ : Finset ℝ≥0)), Finset.sum_empty,
        add_zero, hsup]
      simp only [bmInc, hprev, add_zero]

/-- **Telescoping the centered shifted path over a finite set.** Let $(B_t)_{t \ge 0}$ be a
real-valued process on $\Omega$, let $s \ge 0$, and let $S \subset \mathbb{R}_{\ge 0}$ be a
finite set. For $u \ge 0$ let $u^-$ be the largest element of $S$ strictly below $u$, or $0$
if there is none. Then for every $t \in S$ and every $\omega \in \Omega$,
$B_{s+t}(\omega) - B_s(\omega) =
\sum_{u \in S : u \le t} (B_{s+u}(\omega) - B_{s+u^-}(\omega))$. -/
lemma bmCentered_eq_sum_bmInc {s : ℝ≥0} (S : Finset ℝ≥0) {t : ℝ≥0} (ht : t ∈ S) (ω : Ω) :
    bmCenteredShift B s ω t
      = ∑ u ∈ S.filter (· ≤ t), bmInc B s S u ω := by
  have hne : (S.filter (· ≤ t)).Nonempty :=
    ⟨t, Finset.mem_filter.mpr ⟨ht, le_rfl⟩⟩
  have hsum := sum_bmInc_eq (S := S.filter (· ≤ t)) (s := s) (B := B) hne ω
  rw [show (S.filter (· ≤ t)).sup id = t from
    le_antisymm (Finset.sup_le fun u hu => (Finset.mem_filter.mp hu).2)
      (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨ht, le_rfl⟩))] at hsum
  show B (s + t) ω - B s ω = ∑ u ∈ S.filter (· ≤ t), bmInc B s S u ω
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro u hu
  have huS : u ∈ S := (Finset.mem_filter.mp hu).1
  have hut : u ≤ t := (Finset.mem_filter.mp hu).2
  have hfilter : (S.filter (· ≤ t)).filter (· < u) = S.filter (· < u) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hvS, -⟩, hvu⟩
      exact ⟨hvS, hvu⟩
    · rintro ⟨hvS, hvu⟩
      exact ⟨⟨hvS, le_trans (le_of_lt hvu) hut⟩, hvu⟩
  simp only [bmInc]
  unfold bmPrev
  rw [hfilter]

/-- **Measurability of the increments.** Let $B = (B_t)_{t \ge 0}$ be a real process on a
measurable space $\Omega$, adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ of its σ-algebra.
For every finite set $S$ of nonnegative reals and all $s, t \ge 0$, the increment
$B_{s+t} - B_{s+p_S(t)}$ is measurable, where $p_S(t)$ is the largest element of $S$ strictly
below $t$, or $0$ if there is none. -/
lemma measurable_bmInc (hAd : BmAdapted B ℱ) {s : ℝ≥0} (S : Finset ℝ≥0) (t : ℝ≥0) :
    Measurable fun ω => bmInc B s S t ω := by
  show Measurable fun ω => B (s + t) ω - B (s + bmPrev S t) ω
  exact Measurable.sub ((hAd (s + t)).mono (Filtration.le ℱ (s + t)) le_rfl)
    ((hAd (s + bmPrev S t)).mono (Filtration.le ℱ (s + bmPrev S t)) le_rfl)

/-- **Increment rectangles.** Let $(B_t)_{t \ge 0}$ be a real-valued process on $\Omega$, let
$s \ge 0$, and let $S \subset \mathbb{R}_{\ge 0}$ be a finite set. For $t \ge 0$ let $t^-$ be the
largest element of $S$ strictly below $t$, or $0$ if there is none. The increment rectangles
are the events
$\bigcap_{t \in S} \{\omega \in \Omega : B_{s+t}(\omega) - B_{s+t^-}(\omega) \in C_t\}$, where each
$C_t \subseteq \mathbb{R}$ is a Borel set. -/
def bmIncRectangles (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (S : Finset ℝ≥0) :
    Set (Set Ω) :=
  {T | ∃ C : ℝ≥0 → Set ℝ, (∀ t, MeasurableSet (C t)) ∧
    T = ⋂ t ∈ S, {ω | bmInc B s S t ω ∈ C t}}

/-- **σ-algebra of the increments over a finite set.** Let $(B_t)_{t \ge 0}$ be a real-valued
process on $\Omega$, let $s \ge 0$, and let $S \subset \mathbb{R}_{\ge 0}$ be a finite set. For
$t \ge 0$ let $t^-$ be the largest element of $S$ strictly below $t$, or $0$ if there is none.
This is the σ-algebra on $\Omega$ generated by the increment rectangles, the events
$\bigcap_{t \in S} \{\omega \in \Omega : B_{s+t}(\omega) - B_{s+t^-}(\omega) \in C_t\}$ with each
$C_t \subseteq \mathbb{R}$ a Borel set. -/
@[instance_reducible]
def bmIncSigma (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (S : Finset ℝ≥0) :
    MeasurableSpace Ω :=
  MeasurableSpace.generateFrom (bmIncRectangles B s S)

/-- **Events of a single increment lie in the increment σ-algebra.** Let $B = (B_t)_{t \ge 0}$
be a real process on a measurable space $\Omega$, let $s \ge 0$ and let $S$ be a finite set of
nonnegative reals. For $u \ge 0$ let $p_S(u)$ be the largest element of $S$ strictly below $u$,
or $0$ if there is none, and let $\Delta_u = B_{s+u} - B_{s+p_S(u)}$. Let $\mathcal{G}_S$ be the
σ-algebra on $\Omega$ generated by the sets
$\bigcap_{u \in S} \{\omega : \Delta_u(\omega) \in E_u\}$ for families $(E_u)_{u \ge 0}$ of
measurable subsets of $\mathbb{R}$. Then for every $t \in S$ and every measurable
$D \subseteq \mathbb{R}$, the event $\{\omega : \Delta_t(\omega) \in D\}$ belongs to
$\mathcal{G}_S$. -/
lemma measurableSet_bmInc_preimage {s : ℝ≥0} (S : Finset ℝ≥0) {t : ℝ≥0} (ht : t ∈ S)
    {D : Set ℝ} (hD : MeasurableSet D) :
    MeasurableSet[bmIncSigma B s S] {ω | bmInc B s S t ω ∈ D} := by
  have hmem : {ω | bmInc B s S t ω ∈ D} ∈ bmIncRectangles B s S := by
    refine ⟨fun u => if u = t then D else Set.univ, fun u => ?_, ?_⟩
    · by_cases hu : u = t <;> simp [hu, hD, MeasurableSet.univ]
    · ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h u hu
        by_cases hut : u = t
        · subst hut
          simpa using h
        · simp [hut]
      · intro h
        simpa using h t ht
  exact MeasurableSpace.measurableSet_generateFrom hmem

/-- **Measurability of an increment in the increment σ-algebra.** Let $(B_t)_{t \ge 0}$ be a
real-valued process on $\Omega$, let $s \ge 0$, and let $S \subseteq \mathbb{R}_{\ge 0}$ be
finite; for $t \in S$ let $t^-$ be the largest element of $S$ strictly below $t$, or $0$ if there
is none. Then for every $t \in S$, the increment $\omega \mapsto B_{s+t}(\omega) -
B_{s+t^-}(\omega)$ is measurable with respect to the σ-algebra generated by the events
$\bigcap_{u \in S} \{B_{s+u} - B_{s+u^-} \in C_u\}$, where every $C_u \subseteq \mathbb{R}$ is
Borel. -/
lemma measurable_bmInc_incSigma {s : ℝ≥0} (S : Finset ℝ≥0) {t : ℝ≥0} (ht : t ∈ S) :
    Measurable[bmIncSigma B s S] (fun ω => bmInc B s S t ω) := by
  intro D hD
  exact measurableSet_bmInc_preimage S ht hD

/-- **Independence of future increments from the present.** Let $\mu$ be a probability measure
on $\Omega$, let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration indexed by $\mathbb{R}_{\ge 0}$, and
let $(B_t)_{t \ge 0}$ be a real-valued process that is adapted (each $B_t$ is
$\mathcal{F}_t$-measurable) and has independent increments (for $u \le t$, the increment
$B_t - B_u$ is independent of $\mathcal{F}_u$ under $\mu$). For a finite set
$S \subseteq \mathbb{R}_{\ge 0}$ and $t \in S$, let $t^-$ be the largest element of $S$ strictly
below $t$, or $0$ if there is none. Then for every $s \ge 0$ and every finite
$S \subseteq \mathbb{R}_{\ge 0}$, $\mathcal{F}_s$ is independent under $\mu$ of the σ-algebra
generated by the events $\bigcap_{t \in S} \{B_{s+t} - B_{s+t^-} \in C_t\}$, where every
$C_t \subseteq \mathbb{R}$ is Borel. -/
lemma indep_bmIncSigma (hAd : BmAdapted B ℱ) (hInd : BmIndepIncrements B ℱ μ)
    [IsProbabilityMeasure μ] (s : ℝ≥0) (S : Finset ℝ≥0) :
    Indep (ℱ s) (bmIncSigma B s S) μ := by
  have h := IndepSets.indep' (μ := μ)
    (p1 := {A : Set Ω | MeasurableSet[ℱ s] A}) (p2 := bmIncRectangles B s S)
    (by intro T hT
        exact (Filtration.le ℱ s) T hT)
    (by intro T hT
        obtain ⟨C, hC, rfl⟩ := hT
        exact Finset.measurableSet_biInter S (fun t _ => (measurable_bmInc hAd S t) (hC t)))
    (by intro a ha b hb _
        exact MeasurableSet.inter ha hb)
    (by intro T1 hT1 T2 hT2 _
        obtain ⟨C1, hC1, e1⟩ := hT1
        obtain ⟨C2, hC2, e2⟩ := hT2
        subst e1
        subst e2
        refine ⟨fun t => C1 t ∩ C2 t, fun t => MeasurableSet.inter (hC1 t) (hC2 t), ?_⟩
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
        constructor
        · rintro ⟨h1, h2⟩ t ht
          exact ⟨h1 t ht, h2 t ht⟩
        · intro h
          exact ⟨fun t ht => (h t ht).1, fun t ht => (h t ht).2⟩)
    (by simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure,
          Kernel.const_apply]
        intro T1 T2 hT1 hT2
        obtain ⟨C, hC, rfl⟩ := hT2
        exact measure_inter_biInter_bmInc hAd hInd s S C hC T1 hT1)
  have hgen : MeasurableSpace.generateFrom {A : Set Ω | MeasurableSet[ℱ s] A} = ℱ s :=
    @MeasurableSpace.generateFrom_measurableSet Ω (ℱ s)
  rw [hgen] at h
  exact h

/-- **Cylinder events of the centered shifted path.** Let $(B_t)_{t \ge 0}$ be a real-valued
process on $\Omega$ and let $s \ge 0$. The centered cylinders at time $s$ are the events
$\bigcap_{t \in S} \{\omega \in \Omega : B_{s+t}(\omega) - B_s(\omega) \in C_t\}$, where
$S \subset \mathbb{R}_{\ge 0}$ is a finite set and each $C_t \subseteq \mathbb{R}$ is a
Borel set. -/
def bmCenteredCylinders (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : Set (Set Ω) :=
  {T | ∃ (S : Finset ℝ≥0) (C : ℝ≥0 → Set ℝ), (∀ t, MeasurableSet (C t)) ∧
    T = ⋂ t ∈ S, {ω | bmCenteredShift B s ω t ∈ C t}}

/-- **Centered cylinders lie in the increment σ-algebra.** Let $B = (B_t)_{t \ge 0}$ be a real
process on a measurable space $\Omega$, let $s \ge 0$ and let $S$ be a finite set of nonnegative
reals. For $u \ge 0$ let $p_S(u)$ be the largest element of $S$ strictly below $u$, or $0$ if
there is none, and let $\Delta_u = B_{s+u} - B_{s+p_S(u)}$. Let $\mathcal{G}_S$ be the σ-algebra
on $\Omega$ generated by the sets $\bigcap_{u \in S} \{\omega : \Delta_u(\omega) \in E_u\}$ for
families $(E_u)_{u \ge 0}$ of measurable subsets of $\mathbb{R}$. Then for every family
$(C_t)_{t \ge 0}$ of measurable subsets of $\mathbb{R}$, the set
$\bigcap_{t \in S} \{\omega : B_{s+t}(\omega) - B_s(\omega) \in C_t\}$ belongs to
$\mathcal{G}_S$. -/
lemma measurableSet_bmCentered_cylinder {s : ℝ≥0} (S : Finset ℝ≥0) (C : ℝ≥0 → Set ℝ)
    (hC : ∀ t, MeasurableSet (C t)) :
    MeasurableSet[bmIncSigma B s S]
      (⋂ t ∈ S, {ω | bmCenteredShift B s ω t ∈ C t}) := by
  refine Finset.measurableSet_biInter S fun t ht => ?_
  have hset : {ω | bmCenteredShift B s ω t ∈ C t}
      = (fun ω => ∑ u ∈ S.filter (· ≤ t), bmInc B s S u ω) ⁻¹' C t := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage,
      bmCentered_eq_sum_bmInc S ht ω]
  rw [hset]
  exact (Finset.measurable_sum _ (fun u hu =>
    measurable_bmInc_incSigma S (Finset.mem_filter.mp hu).1)) (hC t)

/-- **Evaluation events are measurable.** For every $t \in \mathbb{R}_{\ge 0}$ and every Borel set
$D \subseteq \mathbb{R}$, the set of paths $f : \mathbb{R}_{\ge 0} \to \mathbb{R}$ with $f(t) \in D$
is measurable for the product σ-algebra on the space of all such paths. -/
lemma measurableSet_pi_eval_preimage {t : ℝ≥0} {D : Set ℝ} (hD : MeasurableSet D) :
    MeasurableSet {f : ℝ≥0 → ℝ | f t ∈ D} := by
  have h1 : MeasurableSet[MeasurableSpace.comap
      (Function.eval t : (ℝ≥0 → ℝ) → ℝ) inferInstance]
      {f : ℝ≥0 → ℝ | f t ∈ D} := ⟨D, hD, rfl⟩
  exact (le_iSup (fun i : ℝ≥0 => MeasurableSpace.comap
    (Function.eval i : (ℝ≥0 → ℝ) → ℝ) inferInstance) t) _ h1

/-- **Independence of the centered future path from the present.** Let $\mu$ be a probability
measure on $\Omega$, let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration indexed by
$\mathbb{R}_{\ge 0}$, and let $(B_t)_{t \ge 0}$ be a real-valued process that is adapted (each
$B_t$ is $\mathcal{F}_t$-measurable) and has independent increments (for $u \le t$, the
increment $B_t - B_u$ is independent of $\mathcal{F}_u$ under $\mu$). Then for every $s \ge 0$,
$\mathcal{F}_s$ is independent under $\mu$ of the σ-algebra generated by the centered shifted
path $\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$, where the path space
$\mathbb{R}^{\mathbb{R}_{\ge 0}}$ carries the product σ-algebra. -/
lemma indep_bmCenteredShift (hAd : BmAdapted B ℱ) (hInd : BmIndepIncrements B ℱ μ)
    [IsProbabilityMeasure μ] (s : ℝ≥0) :
    Indep (ℱ s) (MeasurableSpace.comap (bmCenteredShift B s) inferInstance) μ := by
  refine IndepSets.indep (p1 := {A : Set Ω | MeasurableSet[ℱ s] A})
    (p2 := bmCenteredCylinders B s) (Filtration.le ℱ s)
    (Measurable.comap_le (measurable_bmCenteredShift hAd s)) ?_ ?_ ?_ ?_ ?_
  · intro a ha b hb _
    exact MeasurableSet.inter ha hb
  · intro T1 hT1 T2 hT2 _
    obtain ⟨S1, C1, hC1, e1⟩ := hT1
    obtain ⟨S2, C2, hC2, e2⟩ := hT2
    subst e1
    subst e2
    refine ⟨S1 ∪ S2, fun t => {x | (t ∈ S1 → x ∈ C1 t) ∧ (t ∈ S2 → x ∈ C2 t)},
      fun t => ?_, ?_⟩
    · have hDeq : {x | (t ∈ S1 → x ∈ C1 t) ∧ (t ∈ S2 → x ∈ C2 t)}
          = (if t ∈ S1 then C1 t else Set.univ) ∩ (if t ∈ S2 then C2 t else Set.univ) := by
        ext x
        by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;> simp [h1, h2]
      show MeasurableSet {x | (t ∈ S1 → x ∈ C1 t) ∧ (t ∈ S2 → x ∈ C2 t)}
      rw [hDeq]
      by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;>
        simp [h1, h2, hC1 t, hC2 t, MeasurableSet.univ]
    · ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩ t ht
        rcases ht with ht | ht
        · exact ⟨fun _ => h1 t ht, fun h => h2 t h⟩
        · exact ⟨fun h => h1 t h, fun _ => h2 t ht⟩
      · intro h
        exact ⟨fun t ht => (h t (Or.inl ht)).1 ht, fun t ht => (h t (Or.inr ht)).2 ht⟩
  · exact (@MeasurableSpace.generateFrom_measurableSet Ω (ℱ s)).symm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections,
      MeasurableSpace.comap_generateFrom]
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro T hT
      obtain ⟨T', hT', hTeq⟩ := hT
      obtain ⟨t, A, hA, hT'eq⟩ := hT'
      subst hTeq
      subst hT'eq
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨{t}, fun u => if u = t then A else Set.univ,
        fun u => by by_cases h : u = t <;> simp [h, hA, MeasurableSet.univ], ?_⟩
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iInter,
        Finset.mem_singleton]
      constructor
      · intro h u hu
        rw [hu]
        simpa using h
      · intro h
        have := h t rfl
        simpa using this
    · apply MeasurableSpace.generateFrom_le
      intro T hT
      obtain ⟨S, C, hC, hTeq⟩ := hT
      subst hTeq
      refine Finset.measurableSet_biInter S fun t _ => ?_
      have hmem : MeasurableSet[MeasurableSpace.comap (bmCenteredShift B s)
          inferInstance] {ω | bmCenteredShift B s ω t ∈ C t} :=
        ⟨Function.eval t ⁻¹' C t, measurableSet_pi_eval_preimage (hC t), by
          ext ω
          simp only [Set.mem_preimage, Function.eval, Set.mem_ofPred_eq]⟩
      rw [← MeasurableSpace.comap_generateFrom,
        ← MeasurableSpace.pi_eq_generateFrom_projections]
      exact hmem
  · simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure,
        Kernel.const_apply]
    intro T1 T2 hT1 hT2
    obtain ⟨S, C, hC, rfl⟩ := hT2
    exact IndepSet.measure_inter_eq_mul
      ((indep_bmIncSigma hAd hInd s S).indepSet_of_measurableSet hT1
        (measurableSet_bmCentered_cylinder S C hC))

/-- **Cylinder sets of path space.** The collection of sets of paths
$f : \mathbb{R}_{\ge 0} \to \mathbb{R}$ of the form $\bigcap_{t \in S} \{f : f(t) \in C_t\}$,
where $S \subseteq \mathbb{R}_{\ge 0}$ is a finite set and each $C_t$ is a measurable subset of
$\mathbb{R}$. -/
def bmPathCylinders : Set (Set (ℝ≥0 → ℝ)) :=
  {T | ∃ (S : Finset ℝ≥0) (C : ℝ≥0 → Set ℝ), (∀ t, MeasurableSet (C t)) ∧
    T = ⋂ t ∈ S, {f | f t ∈ C t}}

/-- **Path cylinders form a π-system.** Consider the subsets of $\mathbb{R}^{\mathbb{R}_{\ge 0}}$
of the form $\bigcap_{t \in S} \{f : f(t) \in C_t\}$, where $S \subseteq \mathbb{R}_{\ge 0}$ is
finite and every $C_t \subseteq \mathbb{R}$ is Borel. They form a π-system: whenever two of them
have nonempty intersection, the intersection is again of this form. -/
lemma isPiSystem_bmPathCylinders : IsPiSystem bmPathCylinders := by
  intro T1 hT1 T2 hT2 _
  obtain ⟨S1, C1, hC1, e1⟩ := hT1
  obtain ⟨S2, C2, hC2, e2⟩ := hT2
  subst e1
  subst e2
  refine ⟨S1 ∪ S2, fun t => {x | (t ∈ S1 → x ∈ C1 t) ∧ (t ∈ S2 → x ∈ C2 t)},
    fun t => ?_, ?_⟩
  · have hDeq : {x | (t ∈ S1 → x ∈ C1 t) ∧ (t ∈ S2 → x ∈ C2 t)}
        = (if t ∈ S1 then C1 t else Set.univ) ∩ (if t ∈ S2 then C2 t else Set.univ) := by
      ext x
      by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;> simp [h1, h2]
    show MeasurableSet {x | (t ∈ S1 → x ∈ C1 t) ∧ (t ∈ S2 → x ∈ C2 t)}
    rw [hDeq]
    by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;>
      simp [h1, h2, hC1 t, hC2 t, MeasurableSet.univ]
  · ext f
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      rcases ht with ht | ht
      · exact ⟨fun _ => h1 t ht, fun h => h2 t h⟩
      · exact ⟨fun h => h1 t h, fun _ => h2 t ht⟩
    · intro h
      exact ⟨fun t ht => (h t (Or.inl ht)).1 ht, fun t ht => (h t (Or.inr ht)).2 ht⟩

/-- **Cylinders generate the product σ-algebra on path space.** The product σ-algebra on the space
of paths $f : \mathbb{R}_{\ge 0} \to \mathbb{R}$ equals the σ-algebra generated by the cylinders,
the sets $\{f : f(t) \in C_t \text{ for all } t \in S\}$ with $S$ a finite subset of
$\mathbb{R}_{\ge 0}$ and $(C_t)_{t \ge 0}$ a family of Borel subsets of $\mathbb{R}$. -/
lemma pi_eq_generateFrom_bmPathCylinders :
    (inferInstance : MeasurableSpace (ℝ≥0 → ℝ))
      = MeasurableSpace.generateFrom bmPathCylinders := by
  rw [MeasurableSpace.pi_eq_generateFrom_projections]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro T hT
    obtain ⟨t, A, hA, hTeq⟩ := hT
    subst hTeq
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{t}, fun u => if u = t then A else Set.univ,
      fun u => by by_cases h : u = t <;> simp [h, hA, MeasurableSet.univ], ?_⟩
    ext f
    simp only [Set.mem_preimage, Function.eval, Set.mem_ofPred_eq, Set.mem_iInter,
      Finset.mem_singleton]
    constructor
    · intro h u hu
      rw [hu]
      simpa using h
    · intro h
      have := h t rfl
      simpa using this
  · apply MeasurableSpace.generateFrom_le
    intro T hT
    obtain ⟨S, C, hC, hTeq⟩ := hT
    subst hTeq
    refine Finset.measurableSet_biInter S fun t _ =>
      MeasurableSpace.measurableSet_generateFrom ⟨t, C t, hC t, rfl⟩

/-- **Rectangles of a Borel set and a path cylinder.** Write $\mathbb{R}^{\mathbb{R}_{\ge 0}}$
for the space of functions $\mathbb{R}_{\ge 0} \to \mathbb{R}$. These are the subsets of
$\mathbb{R} \times \mathbb{R}^{\mathbb{R}_{\ge 0}}$ of the form
$U \times \{f : f(t) \in V_t \text{ for all } t \in S\}$, where $U \subseteq \mathbb{R}$ is a
Borel set, $S \subset \mathbb{R}_{\ge 0}$ is a finite set, and each $V_t \subseteq \mathbb{R}$
is a Borel set. -/
def bmCylRectangles : Set (Set (ℝ × (ℝ≥0 → ℝ))) :=
  {T | ∃ (U : Set ℝ) (S : Finset ℝ≥0) (V : ℝ≥0 → Set ℝ), MeasurableSet U ∧
    (∀ t, MeasurableSet (V t)) ∧ T = U ×ˢ ⋂ t ∈ S, {f | f t ∈ V t}}

/-- **Rectangles of a Borel set and a path cylinder form a π-system.** Consider the subsets of
$\mathbb{R} \times \mathbb{R}^{\mathbb{R}_{\ge 0}}$ of the form
$U \times \bigcap_{t \in S} \{f \in \mathbb{R}^{\mathbb{R}_{\ge 0}} : f(t) \in V_t\}$, where
$U \subseteq \mathbb{R}$ is Borel, $S \subseteq \mathbb{R}_{\ge 0}$ is finite and every
$V_t \subseteq \mathbb{R}$ is Borel. They form a π-system: whenever two of them have nonempty
intersection, the intersection is again of this form. -/
lemma isPiSystem_bmCylRectangles : IsPiSystem bmCylRectangles := by
  intro T1 hT1 T2 hT2 _
  obtain ⟨U1, S1, V1, hU1, hV1, e1⟩ := hT1
  obtain ⟨U2, S2, V2, hU2, hV2, e2⟩ := hT2
  subst e1
  subst e2
  refine ⟨U1 ∩ U2, S1 ∪ S2, fun t => {x | (t ∈ S1 → x ∈ V1 t) ∧ (t ∈ S2 → x ∈ V2 t)},
    MeasurableSet.inter hU1 hU2, fun t => ?_, ?_⟩
  · have hDeq : {x | (t ∈ S1 → x ∈ V1 t) ∧ (t ∈ S2 → x ∈ V2 t)}
        = (if t ∈ S1 then V1 t else Set.univ) ∩ (if t ∈ S2 then V2 t else Set.univ) := by
      ext x
      by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;> simp [h1, h2]
    show MeasurableSet {x | (t ∈ S1 → x ∈ V1 t) ∧ (t ∈ S2 → x ∈ V2 t)}
    rw [hDeq]
    by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;>
      simp [h1, h2, hV1 t, hV2 t, MeasurableSet.univ]
  · ext ⟨x, f⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_iInter,
      Finset.mem_union]
    constructor
    · rintro ⟨⟨hx1, h1⟩, hx2, h2⟩
      refine ⟨⟨hx1, hx2⟩, fun t ht => ?_⟩
      rcases ht with ht | ht
      · exact ⟨fun _ => h1 t ht, fun h => h2 t h⟩
      · exact ⟨fun h => h1 t h, fun _ => h2 t ht⟩
    · rintro ⟨⟨hx1, hx2⟩, h⟩
      refine ⟨⟨hx1, fun t ht => (h t (Or.inl ht)).1 ht⟩,
        hx2, fun t ht => (h t (Or.inr ht)).2 ht⟩

/-- **Measurable rectangles lie in the σ-algebra of cylinder rectangles.** Let
$U \subseteq \mathbb{R}$ be a Borel set and let $V$ be a set of paths
$f : \mathbb{R}_{\ge 0} \to \mathbb{R}$ that is measurable for the product σ-algebra. Then
$U \times V$ belongs to the σ-algebra on $\mathbb{R} \times (\mathbb{R}_{\ge 0} \to \mathbb{R})$
generated by the cylinder rectangles, the sets $U' \times \{f : f(t) \in C_t \text{ for all }
t \in S\}$ with $U'$ Borel, $S$ a finite subset of $\mathbb{R}_{\ge 0}$ and $(C_t)_{t \ge 0}$ a
family of Borel sets.

This is Dynkin's theorem applied to the cylinder π-system on path space. -/
lemma mem_generateFrom_bmCylRectangles {V : Set (ℝ≥0 → ℝ)} (hV : MeasurableSet V)
    (U : Set ℝ) (hU : MeasurableSet U) :
    MeasurableSet[MeasurableSpace.generateFrom bmCylRectangles] (U ×ˢ V) := by
  refine MeasurableSpace.induction_on_inter pi_eq_generateFrom_bmPathCylinders
    isPiSystem_bmPathCylinders ?_ ?_ ?_ ?_ V hV
  · rw [Set.prod_empty]
    exact @MeasurableSet.empty _ (MeasurableSpace.generateFrom bmCylRectangles)
  · intro T hT
    obtain ⟨S, C, hC, hTeq⟩ := hT
    subst hTeq
    exact MeasurableSpace.measurableSet_generateFrom ⟨U, S, C, hU, hC, rfl⟩
  · intro T _ hCT
    rw [show U ×ˢ Tᶜ = (U ×ˢ Set.univ) ∩ (U ×ˢ T)ᶜ from by
      ext ⟨x, f⟩
      simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto]
    exact MeasurableSet.inter
      (MeasurableSpace.measurableSet_generateFrom
        ⟨U, ∅, fun _ => Set.univ, hU, fun _ => MeasurableSet.univ, by simp⟩)
      (MeasurableSet.compl hCT)
  · intro f _ _ hf
    rw [Set.prod_iUnion]
    exact MeasurableSet.iUnion (fun i => hf i)

/-- **Cylinder rectangles generate the product σ-algebra.** The product σ-algebra on
$\mathbb{R} \times (\mathbb{R}_{\ge 0} \to \mathbb{R})$, where the path space carries its product
σ-algebra, equals the σ-algebra generated by the cylinder rectangles, the sets
$U \times \{f : f(t) \in V_t \text{ for all } t \in S\}$ with $U$ Borel, $S$ a finite subset of
$\mathbb{R}_{\ge 0}$ and $(V_t)_{t \ge 0}$ a family of Borel subsets of $\mathbb{R}$. -/
lemma prod_eq_generateFrom_bmCylRectangles :
    (inferInstance : MeasurableSpace (ℝ × (ℝ≥0 → ℝ)))
      = MeasurableSpace.generateFrom bmCylRectangles := by
  rw [← generateFrom_prod]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro T hT
    obtain ⟨U, hU, V, hV, hTeq⟩ := hT
    subst hTeq
    exact mem_generateFrom_bmCylRectangles hV U hU
  · apply MeasurableSpace.generateFrom_le
    intro T hT
    obtain ⟨U, S, V, hU, hV, hTeq⟩ := hT
    subst hTeq
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨U, hU, ⋂ t ∈ S, {f | f t ∈ V t},
        Finset.measurableSet_biInter S fun t _ => measurableSet_pi_eval_preimage (hV t),
        rfl⟩

/-- **The process value paired with its centered future path.** For a real process
$(B_t)_{t \ge 0}$ on $\Omega$ indexed by $t \in \mathbb{R}_{\ge 0}$ and a time $s \ge 0$, this is
the map $\Omega \to \mathbb{R} \times \mathbb{R}^{\mathbb{R}_{\ge 0}}$ sending $\omega$ to the pair
consisting of $B_s(\omega)$ and the path $t \mapsto B_{s+t}(\omega) - B_s(\omega)$. -/
noncomputable def bmPair (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : Ω → ℝ × (ℝ≥0 → ℝ) :=
  fun ω => (B s ω, bmCenteredShift B s ω)

/-- **Translating a path by a constant.** The map sending a pair $(x, f)$, with
$x \in \mathbb{R}$ and $f : \mathbb{R}_{\ge 0} \to \mathbb{R}$, to the path $t \mapsto x + f(t)$. -/
noncomputable def bmPhi : ℝ × (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) :=
  fun p t => p.1 + p.2 t

/-- **Measurability of the pair map.** Let $B = (B_t)_{t \ge 0}$ be a real process on a
measurable space $\Omega$, adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ of its σ-algebra,
and give the space $\mathbb{R}^{[0, \infty)}$ of real paths indexed by $t \ge 0$ the product
σ-algebra. For every $s \ge 0$, the map from $\Omega$ to
$\mathbb{R} \times \mathbb{R}^{[0, \infty)}$ sending $\omega$ to the pair of $B_s(\omega)$ and the
centered shifted path $t \mapsto B_{s+t}(\omega) - B_s(\omega)$ is measurable. -/
lemma measurable_bmPair (hAd : BmAdapted B ℱ) (s : ℝ≥0) :
    Measurable (bmPair B s) :=
  Measurable.prodMk ((hAd s).mono (Filtration.le ℱ s) le_rfl)
    (measurable_bmCenteredShift hAd s)

/-- **Translation of paths is measurable.** Give the space $\mathbb{R}^{[0, \infty)}$ of real paths
indexed by $t \ge 0$ the product σ-algebra. The map from
$\mathbb{R} \times \mathbb{R}^{[0, \infty)}$ to $\mathbb{R}^{[0, \infty)}$ sending $(x, f)$ to the
path $t \mapsto x + f(t)$ is measurable. -/
lemma measurable_bmPhi : Measurable bmPhi := by
  apply Measurable.of_eval
  intro t
  show Measurable fun p : ℝ × (ℝ≥0 → ℝ) => p.1 + p.2 t
  exact measurable_fst.add ((measurable_pi_apply t).comp measurable_snd)

/-- **Translating the centered future path recovers the shifted path.** For a real process
$(B_t)_{t \ge 0}$ on $\Omega$ indexed by $t \in \mathbb{R}_{\ge 0}$, a time $s \ge 0$ and
$\omega \in \Omega$, translating the centered shifted path
$t \mapsto B_{s+t}(\omega) - B_s(\omega)$ by the constant $B_s(\omega)$ gives the shifted path
$t \mapsto B_{s+t}(\omega)$. -/
lemma bmPhi_bmPair (s : ℝ≥0) (ω : Ω) :
    bmPhi (bmPair B s ω) = bmShifted B s ω := by
  funext t
  simp only [bmPhi, bmPair, bmShifted, bmCenteredShift]
  ring

/-- **Section measures of the centered law are measurable.** Let $B = (B_t)_{t \ge 0}$ be a real
process on a probability space $(\Omega, \mu)$, let $s \ge 0$, and let $\nu_s$ be the law of the
centered shifted path $t \mapsto B_{s+t} - B_s$ on the space $\mathbb{R}^{[0, \infty)}$ of real
paths indexed by $t \ge 0$, with its product σ-algebra. For every measurable set
$T \subseteq \mathbb{R} \times \mathbb{R}^{[0, \infty)}$, the function
$x \mapsto \nu_s(\{f : (x, f) \in T\})$ from $\mathbb{R}$ to $[0, \infty]$ is measurable. -/
lemma measurable_section_bmCenteredLaw [IsProbabilityMeasure μ] {s : ℝ≥0}
    {T : Set (ℝ × (ℝ≥0 → ℝ))} (hT : MeasurableSet T) :
    Measurable fun x : ℝ => bmCenteredLaw B μ s {f | (x, f) ∈ T} := by
  have hsec : ∀ x : ℝ, MeasurableSet {f : ℝ≥0 → ℝ | (x, f) ∈ T} :=
    fun x => hT.preimage measurable_prodMk_left
  have hEq : ∀ x : ℝ, bmCenteredLaw B μ s {f | (x, f) ∈ T}
      = ∫⁻ f, Set.indicator T (fun _ => 1) (x, f) ∂(bmCenteredLaw B μ s) := by
    intro x
    have hfun : (fun f => Set.indicator T (fun _ => (1 : ENNReal)) (x, f))
        = Set.indicator {f | (x, f) ∈ T} (fun _ => 1) := by
      funext f
      by_cases hf : (x, f) ∈ T <;> simp [Set.indicator, hf]
    rw [hfun, lintegral_indicator_const (hsec x), one_mul]
  simp_rw [hEq]
  have hmeas : Measurable (Function.uncurry fun (x : ℝ) (f : ℝ≥0 → ℝ) =>
      Set.indicator T (fun _ => (1 : ENNReal)) (x, f)) :=
    Measurable.indicator measurable_const hT
  exact hmeas.lintegral_prod_right

/-- **The pair identity on cylinder rectangles.** Let $\mu$ be a probability measure and let
$(B_t)_{t \ge 0}$ be a real process adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ such that
$B_t - B_s$ is independent of $\mathcal{F}_s$ under $\mu$ whenever $s \le t$. Fix
$s \in \mathbb{R}_{\ge 0}$, let $W^s$ be the centered shifted path $t \mapsto B_{s+t} - B_s$ and
let $\nu_s$ be its law under $\mu$. Let $U \subseteq \mathbb{R}$ be Borel, let
$S \subseteq \mathbb{R}_{\ge 0}$ be finite, let $(V_t)_{t \ge 0}$ be Borel subsets of $\mathbb{R}$,
and let $R = U \times \{f : f(t) \in V_t \text{ for all } t \in S\}$. Then for every
$A \in \mathcal{F}_s$,
$$\mu\big(A \cap \{(B_s, W^s) \in R\}\big)
= \int_A \nu_s\big(\{f : (B_s(\omega), f) \in R\}\big)\,d\mu(\omega).$$

The left side factors by the independence of $W^s$ from $\mathcal{F}_s$, and the section on the
right is empty unless $B_s(\omega) \in U$. -/
lemma pair_section_rectangle (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) [IsProbabilityMeasure μ] (s : ℝ≥0)
    (U : Set ℝ) (hU : MeasurableSet U) (S : Finset ℝ≥0) (V : ℝ≥0 → Set ℝ)
    (hV : ∀ t, MeasurableSet (V t)) (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    μ (A ∩ bmPair B s ⁻¹' (U ×ˢ ⋂ t ∈ S, {f | f t ∈ V t}))
      = ∫⁻ ω in A, bmCenteredLaw B μ s
          {f | (B s ω, f) ∈ U ×ˢ ⋂ t ∈ S, {f | f t ∈ V t}} ∂μ := by
  have hCyl : MeasurableSet (⋂ t ∈ S, {f : ℝ≥0 → ℝ | f t ∈ V t}) :=
    Finset.measurableSet_biInter S fun t _ =>
      measurableSet_pi_eval_preimage (hV t)
  have hA' : MeasurableSet[ℱ s] (A ∩ {ω | B s ω ∈ U}) :=
    MeasurableSet.inter hA ((hAd s) hU)
  have hBsU : MeasurableSet {ω | B s ω ∈ U} := (Filtration.le ℱ s) _ ((hAd s) hU)
  have hset : A ∩ bmPair B s ⁻¹' (U ×ˢ ⋂ t ∈ S, {f | f t ∈ V t})
      = (A ∩ {ω | B s ω ∈ U}) ∩
        {ω | bmCenteredShift B s ω ∈ ⋂ t ∈ S, {f | f t ∈ V t}} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod,
      bmPair]
    tauto
  have hIndep : μ ((A ∩ {ω | B s ω ∈ U}) ∩
        {ω | bmCenteredShift B s ω ∈ ⋂ t ∈ S, {f | f t ∈ V t}})
      = μ (A ∩ {ω | B s ω ∈ U}) *
        μ {ω | bmCenteredShift B s ω ∈ ⋂ t ∈ S, {f | f t ∈ V t}} :=
    IndepSet.measure_inter_eq_mul
      ((indep_bmCenteredShift hAd hInd s).indepSet_of_measurableSet hA'
        ⟨⋂ t ∈ S, {f | f t ∈ V t}, hCyl, rfl⟩)
  have hmap : μ {ω | bmCenteredShift B s ω ∈ ⋂ t ∈ S, {f | f t ∈ V t}}
      = bmCenteredLaw B μ s (⋂ t ∈ S, {f | f t ∈ V t}) := by
    show μ (bmCenteredShift B s ⁻¹' ⋂ t ∈ S, {f | f t ∈ V t})
        = bmCenteredLaw B μ s (⋂ t ∈ S, {f | f t ∈ V t})
    rw [bmCenteredLaw, Measure.map_apply (measurable_bmCenteredShift hAd s) hCyl]
  have hInt : ∫⁻ ω in A, bmCenteredLaw B μ s
        {f | (B s ω, f) ∈ U ×ˢ ⋂ t ∈ S, {f | f t ∈ V t}} ∂μ
      = bmCenteredLaw B μ s (⋂ t ∈ S, {f | f t ∈ V t}) *
        μ (A ∩ {ω | B s ω ∈ U}) := by
    have hfun : (fun ω => bmCenteredLaw B μ s
          {f | (B s ω, f) ∈ U ×ˢ ⋂ t ∈ S, {f | f t ∈ V t}})
        = Set.indicator {ω | B s ω ∈ U}
            (fun _ => bmCenteredLaw B μ s (⋂ t ∈ S, {f | f t ∈ V t})) := by
      funext ω
      by_cases h : B s ω ∈ U
      · rw [Set.indicator_of_mem (show ω ∈ {ω' | B s ω' ∈ U} from h)]
        congr 1
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_prod, h, true_and]
      · have hset' : {f : ℝ≥0 → ℝ | (B s ω, f) ∈ U ×ˢ ⋂ t ∈ S, {f | f t ∈ V t}} = ∅ := by
          ext f
          simp only [Set.mem_ofPred_eq, Set.mem_prod, h, false_and,
            Set.mem_empty_iff_false]
        rw [Set.indicator_of_notMem (show ω ∉ {ω' | B s ω' ∈ U} from h), hset',
          measure_empty]
    rw [hfun, setLIntegral_indicator hBsU, setLIntegral_const, Set.inter_comm]
  rw [hset, hIndep, hmap, hInt, mul_comm]

/-- **The pair-section identity for measurable sets.** Let $\mu$ be a probability measure and
let $(B_t)_{t \ge 0}$ be a real process adapted to a filtration $(\mathcal{F}_t)_{t \ge 0}$ such
that $B_t - B_s$ is independent of $\mathcal{F}_s$ under $\mu$ whenever $s \le t$. Fix
$s \in \mathbb{R}_{\ge 0}$, let $W^s$ be the centered shifted path $t \mapsto B_{s+t} - B_s$ and
let $\nu_s$ be its law under $\mu$. Then for every set
$T \subseteq \mathbb{R} \times (\mathbb{R}_{\ge 0} \to \mathbb{R})$ that is measurable for the
product σ-algebra and every $A \in \mathcal{F}_s$,
$$\mu\big(A \cap \{(B_s, W^s) \in T\}\big)
= \int_A \nu_s\big(\{f : (B_s(\omega), f) \in T\}\big)\,d\mu(\omega).$$

The proof is Dynkin's theorem over cylinder rectangles. -/
lemma pair_section_lintegral (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) [IsProbabilityMeasure μ] (s : ℝ≥0)
    {T : Set (ℝ × (ℝ≥0 → ℝ))} (hT : MeasurableSet T) (A : Set Ω)
    (hA : MeasurableSet[ℱ s] A) :
    μ (A ∩ bmPair B s ⁻¹' T)
      = ∫⁻ ω in A, bmCenteredLaw B μ s {f | (B s ω, f) ∈ T} ∂μ := by
  have hAm : MeasurableSet A := (Filtration.le ℱ s) A hA
  refine MeasurableSpace.induction_on_inter prod_eq_generateFrom_bmCylRectangles
    isPiSystem_bmCylRectangles ?_ ?_ ?_ ?_ T hT
  · simp
  · intro T' hT'
    obtain ⟨U, S, V, hU, hV, rfl⟩ := hT'
    exact pair_section_rectangle hAd hInd s U hU S V hV A hA
  · intro T' hT' hCT
    have hsec : ∀ x : ℝ, MeasurableSet {f : ℝ≥0 → ℝ | (x, f) ∈ T'} :=
      fun x => hT'.preimage measurable_prodMk_left
    have hsecMeas : Measurable fun ω => bmCenteredLaw B μ s
        {f | (B s ω, f) ∈ T'} :=
      (measurable_section_bmCenteredLaw hT').comp
        ((hAd s).mono (Filtration.le ℱ s) le_rfl)
    have hLHS : A ∩ bmPair B s ⁻¹' T'ᶜ = A \ (A ∩ bmPair B s ⁻¹' T') := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_sdiff]
      tauto
    have hRHS : (∫⁻ ω in A, bmCenteredLaw B μ s {f | (B s ω, f) ∈ T'ᶜ} ∂μ)
        = μ A - ∫⁻ ω in A, bmCenteredLaw B μ s {f | (B s ω, f) ∈ T'} ∂μ := by
      have hcompl : ∀ ω : Ω, bmCenteredLaw B μ s {f | (B s ω, f) ∈ T'ᶜ}
          = 1 - bmCenteredLaw B μ s {f | (B s ω, f) ∈ T'} := by
        intro ω
        have hsec' : {f : ℝ≥0 → ℝ | (B s ω, f) ∈ T'ᶜ}
            = {f : ℝ≥0 → ℝ | (B s ω, f) ∈ T'}ᶜ := by
          ext f
          simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
        rw [hsec', measure_compl (hsec (B s ω)) (measure_ne_top _ _),
          measure_univ]
      have hmeas_g : Measurable (A.indicator (fun ω => bmCenteredLaw B μ s
          {f | (B s ω, f) ∈ T'})) :=
        Measurable.indicator hsecMeas hAm
      have hfin : ∫⁻ a, A.indicator (fun ω => bmCenteredLaw B μ s
          {f | (B s ω, f) ∈ T'}) a ∂μ ≠ ⊤ := by
        have hle : ∫⁻ a, A.indicator (fun ω => bmCenteredLaw B μ s
            {f | (B s ω, f) ∈ T'}) a ∂μ ≤ ∫⁻ a, (1 : ENNReal) ∂μ := by
          apply lintegral_mono
          intro ω
          by_cases hω : ω ∈ A
          · simp only [Set.indicator_of_mem hω]
            rw [← measure_univ (μ := bmCenteredLaw B μ s)]
            exact measure_mono (Set.subset_univ _)
          · simp only [Set.indicator_of_notMem hω]
            exact zero_le
        rw [lintegral_one, measure_univ] at hle
        exact ne_of_lt (lt_of_le_of_lt hle (by simp : (1 : ENNReal) < ⊤))
      have hle_ae : A.indicator (fun ω => bmCenteredLaw B μ s
          {f | (B s ω, f) ∈ T'}) ≤ᵐ[μ] A.indicator (fun _ : Ω => (1 : ENNReal)) := by
        refine Filter.Eventually.of_forall (fun ω => ?_)
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
          rw [← measure_univ (μ := bmCenteredLaw B μ s)]
          exact measure_mono (Set.subset_univ _)
        · simp only [Set.indicator_of_notMem hω]
          exact zero_le
      have hsubeq := lintegral_sub hmeas_g hfin hle_ae
      simp only [← Pi.sub_apply] at hsubeq
      have hconv : A.indicator (fun ω => bmCenteredLaw B μ s {f | (B s ω, f) ∈ T'ᶜ})
          = A.indicator (fun _ : Ω => (1 : ENNReal)) - A.indicator (fun ω =>
              bmCenteredLaw B μ s {f | (B s ω, f) ∈ T'}) := by
        funext ω
        by_cases hω : ω ∈ A
        · simp only [Pi.sub_apply, Set.indicator_of_mem hω, hcompl]
        · rw [Set.indicator_of_notMem hω, Pi.sub_apply, Set.indicator_of_notMem hω,
            Set.indicator_of_notMem hω, tsub_zero]
      rw [← lintegral_indicator hAm, ← lintegral_indicator hAm, hconv, hsubeq,
        lintegral_indicator hAm, setLIntegral_const, one_mul]
    rw [hLHS, measure_sdiff (Set.inter_subset_left)
      (MeasurableSet.inter hAm ((measurable_bmPair hAd s) hT')).nullMeasurableSet
      (measure_ne_top _ _), hCT, hRHS]
  · intro f hdisj hfm hf
    have hLHS : A ∩ bmPair B s ⁻¹' (⋃ i, f i)
        = ⋃ i, (A ∩ bmPair B s ⁻¹' f i) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
      tauto
    have hdisj' : Pairwise (Function.onFun Disjoint (fun i => A ∩ bmPair B s ⁻¹' f i)) := by
      intro i j hij
      have h := hdisj hij
      rw [Function.onFun] at h ⊢
      exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
        (by
          have : Disjoint (bmPair B s ⁻¹' f i) (bmPair B s ⁻¹' f j) :=
            Disjoint.preimage (bmPair B s) h
          exact this)
    have hmeas' : ∀ i, MeasurableSet (A ∩ bmPair B s ⁻¹' f i) :=
      fun i => MeasurableSet.inter hAm ((measurable_bmPair hAd s) (hfm i))
    rw [hLHS, measure_iUnion hdisj' hmeas']
    have hsecUnion : ∀ ω : Ω, bmCenteredLaw B μ s {g | (B s ω, g) ∈ ⋃ i, f i}
        = ∑' i, bmCenteredLaw B μ s {g | (B s ω, g) ∈ f i} := by
      intro ω
      have hset : {g : ℝ≥0 → ℝ | (B s ω, g) ∈ ⋃ i, f i}
          = ⋃ i, {g : ℝ≥0 → ℝ | (B s ω, g) ∈ f i} := by
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      have hdisj'' : Pairwise (Function.onFun Disjoint
          (fun i => {g : ℝ≥0 → ℝ | (B s ω, g) ∈ f i})) := by
        intro i j hij
        have h := hdisj hij
        rw [Function.onFun] at h ⊢
        exact Disjoint.preimage (Prod.mk (B s ω)) h
      rw [hset, measure_iUnion hdisj'' (fun i => (hfm i).preimage measurable_prodMk_left)]
    have hRHS : (∫⁻ ω in A, bmCenteredLaw B μ s {g | (B s ω, g) ∈ ⋃ i, f i} ∂μ)
        = ∑' i, ∫⁻ ω in A, bmCenteredLaw B μ s {g | (B s ω, g) ∈ f i} ∂μ := by
      have hInnerMeas : ∀ i, Measurable fun ω => bmCenteredLaw B μ s
          {g | (B s ω, g) ∈ f i} :=
        fun i => (measurable_section_bmCenteredLaw (hfm i)).comp
          ((hAd s).mono (Filtration.le ℱ s) le_rfl)
      have htsum : (∫⁻ ω in A, bmCenteredLaw B μ s {g | (B s ω, g) ∈ ⋃ i, f i} ∂μ)
          = ∫⁻ ω, A.indicator (fun ω => ∑' i, bmCenteredLaw B μ s
              {g | (B s ω, g) ∈ f i}) ω ∂μ := by
        rw [← lintegral_indicator hAm]
        congr 1
        funext ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω, hsecUnion]
        · simp only [Set.indicator_of_notMem hω]
      have hfun : A.indicator (fun ω => ∑' i, bmCenteredLaw B μ s
          {g | (B s ω, g) ∈ f i})
          = fun ω => ∑' i, A.indicator (fun ω => bmCenteredLaw B μ s
              {g | (B s ω, g) ∈ f i}) ω := by
        funext ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
        · simp only [Set.indicator_of_notMem hω, tsum_zero]
      rw [htsum, hfun,
        lintegral_tsum (fun i => (Measurable.indicator (hInnerMeas i) hAm).aemeasurable)]
      exact tsum_congr fun i => lintegral_indicator hAm _
    rw [hRHS]
    exact tsum_congr fun i => hf i

/-- **Nonnegative translated integrals against the centered law are measurable.** Let
$B = (B_t)_{t \ge 0}$ be a real process on a probability space $(\Omega, \mu)$, let $s \ge 0$,
and let $\nu_s$ be the law of the centered shifted path $t \mapsto B_{s+t} - B_s$ on the space
$\mathbb{R}^{[0, \infty)}$ of real paths indexed by $t \ge 0$, with its product σ-algebra. For
every measurable $Y : \mathbb{R}^{[0, \infty)} \to [0, \infty]$, the function
$x \mapsto \int Y(x + g) \, d\nu_s(g)$ on $\mathbb{R}$ is measurable, where $x + g$ is the path
$t \mapsto x + g(t)$. -/
lemma measurable_lintegral_bmPhi [IsProbabilityMeasure μ] {s : ℝ≥0}
    {Y : (ℝ≥0 → ℝ) → ENNReal} (hY : Measurable Y) :
    Measurable fun x : ℝ => ∫⁻ g, Y (fun t => x + g t) ∂(bmCenteredLaw B μ s) := by
  have hmeas : Measurable (Function.uncurry fun (x : ℝ) (g : ℝ≥0 → ℝ) =>
      Y (fun t => x + g t)) :=
    hY.comp measurable_bmPhi
  have h := Measurable.lintegral_kernel_prod_right
    (κ := Kernel.const ℝ (bmCenteredLaw B μ s)) hmeas
  simpa only [Kernel.const_apply] using h

/-- **Nonnegative integrals of future path functionals over present events.** Let $\mu$ be a
probability measure on $\Omega$, let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration indexed by
$\mathbb{R}_{\ge 0}$, and let $(B_t)_{t \ge 0}$ be a real-valued process that is adapted (each
$B_t$ is $\mathcal{F}_t$-measurable) and has independent increments (for $u \le t$, the
increment $B_t - B_u$ is independent of $\mathcal{F}_u$ under $\mu$). Fix $s \ge 0$ and let
$\nu_s$ be the law under $\mu$ of the centered shifted path
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$ on $\mathbb{R}^{\mathbb{R}_{\ge 0}}$
with the product σ-algebra. Then for every measurable
$Y : \mathbb{R}^{\mathbb{R}_{\ge 0}} \to [0, \infty]$ and every $A \in \mathcal{F}_s$,
$$\int_A Y\big((B_{s+t}(\omega))_{t \ge 0}\big) \, d\mu(\omega)
= \int_A \int Y\big(t \mapsto B_s(\omega) + g(t)\big) \, d\nu_s(g) \, d\mu(\omega),$$
where all integrals are Lebesgue integrals of $[0, \infty]$-valued functions. -/
lemma independent_increments_lintegral_shift (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) [IsProbabilityMeasure μ] (s : ℝ≥0)
    {Y : (ℝ≥0 → ℝ) → ENNReal} (hY : Measurable Y) (A : Set Ω)
    (hA : MeasurableSet[ℱ s] A) :
    ∫⁻ ω in A, Y (bmShifted B s ω) ∂μ
      = ∫⁻ ω in A, (∫⁻ g, Y (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) ∂μ := by
  have hAm : MeasurableSet A := (Filtration.le ℱ s) A hA
  have hBs : Measurable (B s) := (hAd s).mono (Filtration.le ℱ s) le_rfl
  refine Measurable.ennreal_induction (motive := fun Y => ∀ A : Set Ω,
    MeasurableSet[ℱ s] A → ∫⁻ ω in A, Y (bmShifted B s ω) ∂μ
      = ∫⁻ ω in A, (∫⁻ g, Y (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) ∂μ)
    ?_ ?_ ?_ hY A hA
  · intro c S hs A hA
    have hAm : MeasurableSet A := (Filtration.le ℱ s) A hA
    have hLHS : (∫⁻ ω in A, S.indicator (fun _ => c) (bmShifted B s ω) ∂μ)
        = c * μ (A ∩ bmShifted B s ⁻¹' S) := by
      rw [← lintegral_indicator hAm]
      have hfun : A.indicator (fun ω => S.indicator (fun _ => c) (bmShifted B s ω))
          = (A ∩ bmShifted B s ⁻¹' S).indicator (fun _ => c) := by
        funext ω
        by_cases hω : ω ∈ A <;> by_cases h : bmShifted B s ω ∈ S <;>
          simp [Set.indicator, hω, h]
      rw [hfun,
        lintegral_indicator_const (MeasurableSet.inter hAm ((measurable_bmShifted hAd s) hs))]
    have hRHS : (∫⁻ ω in A, (∫⁻ g, S.indicator (fun _ => c)
          (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) ∂μ)
        = c * μ (A ∩ bmShifted B s ⁻¹' S) := by
      have hPhi : MeasurableSet (bmPhi ⁻¹' S) := hs.preimage measurable_bmPhi
      have hsecMeas : Measurable fun ω => bmCenteredLaw B μ s
          {g | (B s ω, g) ∈ bmPhi ⁻¹' S} :=
        (measurable_section_bmCenteredLaw hPhi).comp hBs
      have hInner : ∀ ω : Ω, (∫⁻ g, S.indicator (fun _ => c)
            (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s))
          = c * bmCenteredLaw B μ s {g | (B s ω, g) ∈ bmPhi ⁻¹' S} := by
        intro ω
        have hfun : (fun g => S.indicator (fun _ => c) (fun t => B s ω + g t))
            = {g | (B s ω, g) ∈ bmPhi ⁻¹' S}.indicator (fun _ => c) := by
          funext g
          by_cases h' : bmPhi (B s ω, g) ∈ S
          · have h2 : (fun t => B s ω + g t) ∈ S := h'
            have hmem : g ∈ {g | (B s ω, g) ∈ bmPhi ⁻¹' S} := h'
            rw [Set.indicator_of_mem h2, Set.indicator_of_mem hmem]
          · have h2 : (fun t => B s ω + g t) ∉ S := h'
            have hmem : g ∉ {g | (B s ω, g) ∈ bmPhi ⁻¹' S} := h'
            rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem hmem]
        have hsec : MeasurableSet {g : ℝ≥0 → ℝ | (B s ω, g) ∈ bmPhi ⁻¹' S} :=
          hPhi.preimage measurable_prodMk_left
        rw [hfun, lintegral_indicator_const hsec]
      have hpairEq : A ∩ bmPair B s ⁻¹' (bmPhi ⁻¹' S) = A ∩ bmShifted B s ⁻¹' S := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, bmPhi_bmPair]
      have hconst : (∫⁻ ω in A, (c * bmCenteredLaw B μ s
            {g | (B s ω, g) ∈ bmPhi ⁻¹' S}) ∂μ)
          = c * ∫⁻ ω in A, bmCenteredLaw B μ s
              {g | (B s ω, g) ∈ bmPhi ⁻¹' S} ∂μ := by
        rw [← lintegral_indicator hAm, ← lintegral_indicator hAm]
        rw [show A.indicator (fun ω => c * bmCenteredLaw B μ s
              {g | (B s ω, g) ∈ bmPhi ⁻¹' S})
            = fun ω => c * A.indicator (fun ω => bmCenteredLaw B μ s
                {g | (B s ω, g) ∈ bmPhi ⁻¹' S}) ω from by
          funext ω
          by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]]
        rw [lintegral_const_mul c (Measurable.indicator hsecMeas hAm)]
      calc ∫⁻ ω in A, (∫⁻ g, S.indicator (fun _ => c)
              (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) ∂μ
          = ∫⁻ ω in A, (c * bmCenteredLaw B μ s
              {g | (B s ω, g) ∈ bmPhi ⁻¹' S}) ∂μ := by
            congr 1
            funext ω
            exact hInner ω
        _ = c * ∫⁻ ω in A, bmCenteredLaw B μ s
              {g | (B s ω, g) ∈ bmPhi ⁻¹' S} ∂μ := hconst
        _ = c * μ (A ∩ bmPair B s ⁻¹' (bmPhi ⁻¹' S)) := by
            rw [pair_section_lintegral hAd hInd s hPhi A hA]
        _ = c * μ (A ∩ bmShifted B s ⁻¹' S) := by rw [hpairEq]
    rw [hLHS, hRHS]
  · intro F G _hdisj hF hG ihF ihG A hA
    have hAm : MeasurableSet A := (Filtration.le ℱ s) A hA
    have hMeasF : Measurable fun ω => F (bmShifted B s ω) :=
      hF.comp (measurable_bmShifted hAd s)
    have hMeasG : Measurable fun ω => G (bmShifted B s ω) :=
      hG.comp (measurable_bmShifted hAd s)
    have hInnerMeas : ∀ Y : (ℝ≥0 → ℝ) → ENNReal, Measurable Y →
        Measurable fun ω => ∫⁻ g, Y (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s) :=
      fun Y hY => (measurable_lintegral_bmPhi hY).comp hBs
    have hInnerAdd : ∀ ω : Ω, (∫⁻ g, (F + G) (fun t => B s ω + g t)
          ∂(bmCenteredLaw B μ s))
        = (∫⁻ g, F (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s))
          + (∫⁻ g, G (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) := by
      intro ω
      have hFg : Measurable fun g : ℝ≥0 → ℝ => F (fun t => B s ω + g t) := by
        apply hF.comp
        apply Measurable.of_eval
        intro t
        exact measurable_const.add (measurable_pi_apply t)
      rw [show (fun (g : ℝ≥0 → ℝ) => (F + G) (fun t => B s ω + g t))
          = fun (g : ℝ≥0 → ℝ) => F (fun t => B s ω + g t) + G (fun t => B s ω + g t) from by
        funext g
        rfl]
      exact lintegral_add_left hFg _
    have hAddLHS : (∫⁻ ω in A, (F + G) (bmShifted B s ω) ∂μ)
        = (∫⁻ ω in A, F (bmShifted B s ω) ∂μ)
          + (∫⁻ ω in A, G (bmShifted B s ω) ∂μ) := by
      rw [← lintegral_indicator hAm, ← lintegral_indicator hAm, ← lintegral_indicator hAm]
      rw [show A.indicator (fun ω => (F + G) (bmShifted B s ω))
          = fun ω => A.indicator (fun ω => F (bmShifted B s ω)) ω
              + A.indicator (fun ω => G (bmShifted B s ω)) ω from by
        funext ω
        by_cases hω : ω ∈ A <;> simp [Set.indicator, hω, Pi.add_apply]]
      rw [lintegral_add_left (Measurable.indicator hMeasF hAm)]
    have hAddRHS : (∫⁻ ω in A, (∫⁻ g, (F + G) (fun t => B s ω + g t)
          ∂(bmCenteredLaw B μ s)) ∂μ)
        = (∫⁻ ω in A, (∫⁻ g, F (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) ∂μ)
          + (∫⁻ ω in A, (∫⁻ g, G (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) ∂μ) := by
      rw [← lintegral_indicator hAm, ← lintegral_indicator hAm, ← lintegral_indicator hAm]
      rw [show A.indicator (fun ω => ∫⁻ g, (F + G) (fun t => B s ω + g t)
              ∂(bmCenteredLaw B μ s))
          = fun ω => A.indicator (fun ω => ∫⁻ g, F (fun t => B s ω + g t)
                ∂(bmCenteredLaw B μ s)) ω
              + A.indicator (fun ω => ∫⁻ g, G (fun t => B s ω + g t)
                ∂(bmCenteredLaw B μ s)) ω from by
        funext ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
          exact hInnerAdd ω
        · simp only [Set.indicator_of_notMem hω, add_zero]]
      rw [lintegral_add_left (Measurable.indicator (hInnerMeas F hF) hAm)]
    rw [hAddLHS, hAddRHS, ihF A hA, ihG A hA]
  · intro Fn hFm hmono ih A hA
    have hAm : MeasurableSet A := (Filtration.le ℱ s) A hA
    have hInnerMeas : ∀ n : ℕ, Measurable fun ω =>
        ∫⁻ g, Fn n (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s) :=
      fun n => (measurable_lintegral_bmPhi (hFm n)).comp hBs
    have hInnerSup : ∀ ω : Ω, (∫⁻ g, (⨆ n, Fn n) (fun t => B s ω + g t)
          ∂(bmCenteredLaw B μ s))
        = ⨆ n, ∫⁻ g, Fn n (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s) := by
      intro ω
      rw [show (fun (g : ℝ≥0 → ℝ) => (⨆ n, Fn n) (fun t => B s ω + g t))
          = fun (g : ℝ≥0 → ℝ) => ⨆ n, Fn n (fun t => B s ω + g t) from by
        funext g
        rw [iSup_apply]]
      refine lintegral_iSup (fun n => ?_) (fun n m hnm g => ?_)
      · apply (hFm n).comp
        apply Measurable.of_eval
        intro t
        exact measurable_const.add (measurable_pi_apply t)
      · exact hmono hnm _
    have hLHS : (∫⁻ ω in A, (⨆ n, Fn n) (bmShifted B s ω) ∂μ)
        = ⨆ n, ∫⁻ ω in A, Fn n (bmShifted B s ω) ∂μ := by
      rw [← lintegral_indicator hAm]
      have hmonoInd : Monotone fun n => A.indicator
          (fun ω => Fn n (bmShifted B s ω)) := by
        intro n m hnm ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
          exact hmono hnm _
        · simp only [Set.indicator_of_notMem hω]
          exact zero_le
      rw [show A.indicator (fun ω => (⨆ n, Fn n) (bmShifted B s ω))
          = ⨆ n, A.indicator (fun ω => Fn n (bmShifted B s ω)) from by
        funext ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω, iSup_apply]
        · simp only [Set.indicator_of_notMem hω, iSup_apply, iSup_const]]
      simp only [iSup_apply]
      rw [lintegral_iSup (fun n => Measurable.indicator
        (show Measurable fun ω => Fn n (bmShifted B s ω) from
          (hFm n).comp (measurable_bmShifted hAd s)) hAm) hmonoInd]
      simp only [lintegral_indicator hAm]
    have hRHS : (∫⁻ ω in A, (∫⁻ g, (⨆ n, Fn n) (fun t => B s ω + g t)
          ∂(bmCenteredLaw B μ s)) ∂μ)
        = ⨆ n, ∫⁻ ω in A, (∫⁻ g, Fn n (fun t => B s ω + g t)
            ∂(bmCenteredLaw B μ s)) ∂μ := by
      rw [show (∫⁻ ω in A, (∫⁻ g, (⨆ n, Fn n) (fun t => B s ω + g t)
              ∂(bmCenteredLaw B μ s)) ∂μ)
          = ∫⁻ ω in A, (⨆ n, ∫⁻ g, Fn n (fun t => B s ω + g t)
              ∂(bmCenteredLaw B μ s)) ∂μ from by
        congr 1
        funext ω
        exact hInnerSup ω]
      rw [← lintegral_indicator hAm]
      have hmonoInd : Monotone fun n => A.indicator
          (fun ω => ∫⁻ g, Fn n (fun t => B s ω + g t) ∂(bmCenteredLaw B μ s)) := by
        intro n m hnm ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
          exact lintegral_mono (fun g => hmono hnm _)
        · simp only [Set.indicator_of_notMem hω]
          exact zero_le
      rw [show A.indicator (fun ω => ⨆ n, ∫⁻ g, Fn n (fun t => B s ω + g t)
              ∂(bmCenteredLaw B μ s))
          = ⨆ n, A.indicator (fun ω => ∫⁻ g, Fn n (fun t => B s ω + g t)
              ∂(bmCenteredLaw B μ s)) from by
        funext ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω, iSup_apply]
        · simp only [Set.indicator_of_notMem hω, iSup_apply, iSup_const]]
      simp only [iSup_apply]
      rw [lintegral_iSup (fun n => Measurable.indicator (hInnerMeas n) hAm) hmonoInd]
      simp only [lintegral_indicator hAm]
    have hEq : (fun x : ℝ≥0 → ℝ => ⨆ n, Fn n x) = (⨆ n, Fn n) := by
      funext x
      rw [iSup_apply]
    rw [hEq, hLHS, hRHS]
    exact iSup_congr fun n => ih n A hA

/-- Historical name for the generic independent-increments result. -/
alias brownian_lintegral_shift := independent_increments_lintegral_shift

/-- **The path expectation is measurable in the starting point.** Let $B = (B_t)_{t \ge 0}$ be a
real process on a probability space $(\Omega, \mu)$, let $s \ge 0$, and let $\nu_s$ be the law of
the centered shifted path $t \mapsto B_{s+t} - B_s$ on the space $\mathbb{R}^{[0, \infty)}$ of
real paths indexed by $t \ge 0$, with its product σ-algebra. For every measurable
$Y : \mathbb{R}^{[0, \infty)} \to \mathbb{R}$, the function $x \mapsto \int Y(x + f) \, d\nu_s(f)$
on $\mathbb{R}$ is measurable, where $x + f$ is the path $t \mapsto x + f(t)$. -/
lemma measurable_bmPathExpectation [IsProbabilityMeasure μ] {s : ℝ≥0}
    {Y : (ℝ≥0 → ℝ) → ℝ} (hY : Measurable Y) :
    Measurable fun x : ℝ => bmPathExpectation B μ s Y x := by
  have hSM : StronglyMeasurable fun x : ℝ =>
      ∫ f, Y (fun t => x + f t) ∂(bmCenteredLaw B μ s) := by
    have h := StronglyMeasurable.integral_kernel_prod_right
      (κ := Kernel.const ℝ (bmCenteredLaw B μ s))
      (f := fun (x : ℝ) (f : ℝ≥0 → ℝ) => Y (fun t => x + f t))
      (hY.stronglyMeasurable.comp_measurable measurable_bmPhi)
    simpa only [Kernel.const_apply] using h
  exact hSM.measurable

/-- **Bound on the path expectation.** Let $\mu$ be a probability measure on $\Omega$, let
$(B_t)_{t \ge 0}$ be a real process on $\Omega$ indexed by $t \in \mathbb{R}_{\ge 0}$, let
$s \ge 0$, and let $\nu_s$ be the law under $\mu$ of the path
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$. If $Y$ is a measurable real function
on paths $\mathbb{R}_{\ge 0} \to \mathbb{R}$ with $|Y(p)| \le C$ for every path $p$, then for
every $x \in \mathbb{R}$ the path expectation $E_s Y(x) = \int Y(t \mapsto x + f(t))\, d\nu_s(f)$
satisfies $|E_s Y(x)| \le C$. -/
lemma bmPathExpectation_bound [IsProbabilityMeasure μ] {s : ℝ≥0} {Y : (ℝ≥0 → ℝ) → ℝ}
    (hY : Measurable Y) {C : ℝ} (hYb : ∀ p, |Y p| ≤ C) (x : ℝ) :
    |bmPathExpectation B μ s Y x| ≤ C := by
  have hMeas : Measurable fun f : ℝ≥0 → ℝ => Y (fun t => x + f t) := by
    apply hY.comp
    apply Measurable.of_eval
    intro t
    exact measurable_const.add (measurable_pi_apply t)
  have hIntNorm : Integrable (fun f : ℝ≥0 → ℝ => ‖Y (fun t => x + f t)‖)
      (bmCenteredLaw B μ s) := by
    refine Integrable.of_bound ?_ C ?_
    · exact Measurable.aestronglyMeasurable (Measurable.norm hMeas)
    · exact Filter.Eventually.of_forall (fun f => by
        show ‖‖Y (fun t => x + f t)‖‖ ≤ C
        rw [norm_norm, Real.norm_eq_abs]
        exact hYb _)
  show |∫ f, Y (fun t => x + f t) ∂(bmCenteredLaw B μ s)| ≤ C
  rw [← Real.norm_eq_abs]
  calc ‖(∫ f, Y (fun t => x + f t) ∂(bmCenteredLaw B μ s))‖
      ≤ ∫ f, ‖Y (fun t => x + f t)‖ ∂(bmCenteredLaw B μ s) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _ : ℝ≥0 → ℝ, C ∂(bmCenteredLaw B μ s) :=
        integral_mono_ae hIntNorm (integrable_const C)
          (Filter.Eventually.of_forall (fun f => by
            show ‖Y (fun t => x + f t)‖ ≤ C
            rw [Real.norm_eq_abs]
            exact hYb _))
    _ = C := by simp [integral_const]

/-- **Set integrals of the path expectation.** Let $\mu$ be a probability measure on $\Omega$, let
$(\mathcal{F}_t)_{t \ge 0}$ be a filtration of the σ-algebra of $\Omega$ indexed by
$\mathbb{R}_{\ge 0}$, and let $(B_t)_{t \ge 0}$ be a real process such that each $B_t$ is
$\mathcal{F}_t$-measurable and, for all $u \le t$, the increment $B_t - B_u$ is independent of
$\mathcal{F}_u$ under $\mu$. Let $s \ge 0$, let $Y$ be a measurable real function on paths
$\mathbb{R}_{\ge 0} \to \mathbb{R}$ with $|Y(p)| \le C$ for every path $p$, and let
$A \in \mathcal{F}_s$. Write $\nu_s$ for the law under $\mu$ of
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$,
$E_s Y(x) = \int Y(t \mapsto x + f(t))\, d\nu_s(f)$ for $x \in \mathbb{R}$, and
$\theta_s \omega$ for the shifted path $t \mapsto B_{s+t}(\omega)$. Then

$$
\int_A E_s Y(B_s(\omega))\, d\mu(\omega)
  = \int_A Y^+(\theta_s \omega)\, d\mu(\omega) - \int_A Y^-(\theta_s \omega)\, d\mu(\omega),
$$

where $Y^+ = \max(Y, 0)$, $Y^- = \max(-Y, 0)$, and each integral on the right is the integral of
a nonnegative function, taken in $[0, \infty]$ and then converted to a real number. -/
lemma bmPathExpectation_setIntegral (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) [IsProbabilityMeasure μ] (s : ℝ≥0)
    {Y : (ℝ≥0 → ℝ) → ℝ} (hY : Measurable Y) {C : ℝ} (hYb : ∀ p, |Y p| ≤ C)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, bmPathExpectation B μ s Y (B s ω) ∂μ
      = (∫⁻ ω in A, ENNReal.ofReal (Y (bmShifted B s ω)) ∂μ).toReal
        - (∫⁻ ω in A, ENNReal.ofReal (-Y (bmShifted B s ω)) ∂μ).toReal := by
  have hBs : Measurable (B s) := (hAd s).mono (Filtration.le ℱ s) le_rfl
  have hAm : MeasurableSet A := (Filtration.le ℱ s) A hA
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hYb (fun _ => 0))
  have hfin : ∀ ω : Ω,
      (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)) ≠ ⊤ := by
    intro ω
    have hle : (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)) ≤ ENNReal.ofReal C := by
      calc (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s))
          ≤ ∫⁻ _ : ℝ≥0 → ℝ, ENNReal.ofReal C ∂(bmCenteredLaw B μ s) :=
            lintegral_mono (fun g => ENNReal.ofReal_le_ofReal
              (le_trans (le_abs_self _) (hYb _)))
        _ = ENNReal.ofReal C := by
            rw [lintegral_const, measure_univ, mul_one]
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hfinNeg : ∀ ω : Ω,
      (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)) ≠ ⊤ := by
    intro ω
    have hle : (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)) ≤ ENNReal.ofReal C := by
      calc (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s))
          ≤ ∫⁻ _ : ℝ≥0 → ℝ, ENNReal.ofReal C ∂(bmCenteredLaw B μ s) :=
            lintegral_mono (fun g => ENNReal.ofReal_le_ofReal (by
              exact le_trans (neg_le_abs _) (hYb _)))
        _ = ENNReal.ofReal C := by
            rw [lintegral_const, measure_univ, mul_one]
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hmeas1 : Measurable fun ω =>
      (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal :=
    (Measurable.ennreal_toReal
      (measurable_lintegral_bmPhi (Measurable.ennreal_ofReal hY))).comp hBs
  have hmeas2 : Measurable fun ω =>
      (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal :=
    (Measurable.ennreal_toReal
      (measurable_lintegral_bmPhi
        (Measurable.ennreal_ofReal (Measurable.neg hY)))).comp hBs
  have hnonneg1 : ∀ ω : Ω, 0 ≤
      (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal :=
    fun ω => ENNReal.toReal_nonneg
  have hnonneg2 : ∀ ω : Ω, 0 ≤
      (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal :=
    fun ω => ENNReal.toReal_nonneg
  have hbound1 : ∀ ω : Ω,
      (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal ≤ C := by
    intro ω
    have hle : (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)) ≤ ENNReal.ofReal C := by
      calc (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s))
          ≤ ∫⁻ _ : ℝ≥0 → ℝ, ENNReal.ofReal C ∂(bmCenteredLaw B μ s) :=
            lintegral_mono (fun g => ENNReal.ofReal_le_ofReal
              (le_trans (le_abs_self _) (hYb _)))
        _ = ENNReal.ofReal C := by
            rw [lintegral_const, measure_univ, mul_one]
    calc (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)).toReal
        ≤ (ENNReal.ofReal C).toReal :=
          (ENNReal.toReal_le_toReal (hfin ω) ENNReal.ofReal_ne_top).mpr hle
      _ = C := ENNReal.toReal_ofReal hCnonneg
  have hbound2 : ∀ ω : Ω,
      (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal ≤ C := by
    intro ω
    have hle : (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)) ≤ ENNReal.ofReal C := by
      calc (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s))
          ≤ ∫⁻ _ : ℝ≥0 → ℝ, ENNReal.ofReal C ∂(bmCenteredLaw B μ s) :=
            lintegral_mono (fun g => ENNReal.ofReal_le_ofReal (by
              exact le_trans (neg_le_abs _) (hYb _)))
        _ = ENNReal.ofReal C := by
            rw [lintegral_const, measure_univ, mul_one]
    calc (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)).toReal
        ≤ (ENNReal.ofReal C).toReal :=
          (ENNReal.toReal_le_toReal (hfinNeg ω) ENNReal.ofReal_ne_top).mpr hle
      _ = C := ENNReal.toReal_ofReal hCnonneg
  have hint1 : Integrable (fun ω =>
      (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal) μ := by
    refine Integrable.of_bound ?_ C ?_
    · exact hmeas1.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        show ‖(∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)).toReal‖ ≤ C
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg1 ω)]
        exact hbound1 ω)
  have hint2 : Integrable (fun ω =>
      (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal) μ := by
    refine Integrable.of_bound ?_ C ?_
    · exact hmeas2.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        show ‖(∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)).toReal‖ ≤ C
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg2 ω)]
        exact hbound2 ω)
  have hEq : ∀ ω : Ω, bmPathExpectation B μ s Y (B s ω)
      = (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal
        - (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t)) ∂(bmCenteredLaw B μ s)).toReal := by
    intro ω
    have hint : Integrable (fun g => Y (fun t => B s ω + g t))
        (bmCenteredLaw B μ s) := by
      refine Integrable.of_bound ?_ C ?_
      · have hmeas : Measurable fun g : ℝ≥0 → ℝ => Y (fun t => B s ω + g t) := by
          apply hY.comp
          apply Measurable.of_eval
          intro t
          exact measurable_const.add (measurable_pi_apply t)
        exact hmeas.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun g => by
          show ‖Y (fun t => B s ω + g t)‖ ≤ C
          rw [Real.norm_eq_abs]
          exact hYb _)
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  have hLHS : (∫ ω in A, bmPathExpectation B μ s Y (B s ω) ∂μ)
      = (∫ ω in A, (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)).toReal ∂μ)
        - (∫ ω in A, (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
          ∂(bmCenteredLaw B μ s)).toReal ∂μ) := by
    rw [show (fun ω => bmPathExpectation B μ s Y (B s ω))
        = fun ω => (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s)).toReal
          - (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s)).toReal from funext hEq]
    exact integral_sub hint1.integrableOn hint2.integrableOn
  have hInt1 : (∫ ω in A, (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
        ∂(bmCenteredLaw B μ s)).toReal ∂μ)
      = (∫⁻ ω in A, ENNReal.ofReal (Y (bmShifted B s ω)) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (μ := μ.restrict A)
      (Filter.Eventually.of_forall (fun ω => hnonneg1 ω))
      (hmeas1.aestronglyMeasurable.restrict)]
    congr 1
    rw [show (∫⁻ ω in A, ENNReal.ofReal
          ((∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s)).toReal) ∂μ)
        = ∫⁻ ω in A, (∫⁻ g, ENNReal.ofReal (Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s)) ∂μ from by
      congr 1
      funext ω
      exact ENNReal.ofReal_toReal (hfin ω)]
    exact (brownian_lintegral_shift hAd hInd s (Measurable.ennreal_ofReal hY) A hA).symm
  have hInt2 : (∫ ω in A, (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
        ∂(bmCenteredLaw B μ s)).toReal ∂μ)
      = (∫⁻ ω in A, ENNReal.ofReal (-Y (bmShifted B s ω)) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (μ := μ.restrict A)
      (Filter.Eventually.of_forall (fun ω => hnonneg2 ω))
      (hmeas2.aestronglyMeasurable.restrict)]
    congr 1
    rw [show (∫⁻ ω in A, ENNReal.ofReal
          ((∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s)).toReal) ∂μ)
        = ∫⁻ ω in A, (∫⁻ g, ENNReal.ofReal (-Y (fun t => B s ω + g t))
            ∂(bmCenteredLaw B μ s)) ∂μ from by
      congr 1
      funext ω
      exact ENNReal.ofReal_toReal (hfinNeg ω)]
    exact (brownian_lintegral_shift hAd hInd s
      (Measurable.ennreal_ofReal (Measurable.neg hY)) A hA).symm
  rw [hLHS, hInt1, hInt2]

/-- **Bounded integrals of future path functionals over present events.** Let $\mu$ be a
probability measure on $\Omega$, let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration indexed by
$\mathbb{R}_{\ge 0}$, and let $(B_t)_{t \ge 0}$ be a real-valued process that is adapted (each
$B_t$ is $\mathcal{F}_t$-measurable) and has independent increments (for $u \le t$, the
increment $B_t - B_u$ is independent of $\mathcal{F}_u$ under $\mu$). Fix $s \ge 0$ and let
$\nu_s$ be the law under $\mu$ of the centered shifted path
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$ on $\mathbb{R}^{\mathbb{R}_{\ge 0}}$
with the product σ-algebra. Let $Y : \mathbb{R}^{\mathbb{R}_{\ge 0}} \to \mathbb{R}$ be
measurable with $|Y(p)| \le C$ for every path $p$, for some real $C$, and for $x \in \mathbb{R}$
put $\Phi_s(x) = \int Y(t \mapsto x + f(t)) \, d\nu_s(f)$. Then for every $A \in \mathcal{F}_s$,
$$\int_A Y\big((B_{s+t}(\omega))_{t \ge 0}\big) \, d\mu(\omega)
= \int_A \Phi_s(B_s(\omega)) \, d\mu(\omega).$$ -/
lemma independent_increments_setIntegral (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) [IsProbabilityMeasure μ] (s : ℝ≥0)
    {Y : (ℝ≥0 → ℝ) → ℝ} (hY : Measurable Y) {C : ℝ} (hYb : ∀ p, |Y p| ≤ C)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, Y (bmShifted B s ω) ∂μ
      = ∫ ω in A, bmPathExpectation B μ s Y (B s ω) ∂μ := by
  have hYshift_int : Integrable (fun ω => Y (bmShifted B s ω)) μ := by
    refine Integrable.of_bound ?_ C ?_
    · exact ((hY.comp (measurable_bmShifted hAd s)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun ω => by
        show ‖Y (bmShifted B s ω)‖ ≤ C
        rw [Real.norm_eq_abs]
        exact hYb _)
  have hLHS : (∫ ω in A, Y (bmShifted B s ω) ∂μ)
      = (∫⁻ ω in A, ENNReal.ofReal (Y (bmShifted B s ω)) ∂μ).toReal
        - (∫⁻ ω in A, ENNReal.ofReal (-Y (bmShifted B s ω)) ∂μ).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (μ := μ.restrict A) hYshift_int.integrableOn
  rw [hLHS, bmPathExpectation_setIntegral hAd hInd s hY hYb A hA]

/-- Historical name for the generic independent-increments result. -/
alias brownian_markov_setIntegral := independent_increments_setIntegral

/-- **Conditional expectation of a future path functional.** Let $\mu$ be a probability measure
on $\Omega$, let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration indexed by $\mathbb{R}_{\ge 0}$, and
let $(B_t)_{t \ge 0}$ be a real-valued process that is adapted (each $B_t$ is
$\mathcal{F}_t$-measurable) and has independent increments (for $u \le t$, the increment
$B_t - B_u$ is independent of $\mathcal{F}_u$ under $\mu$). Fix $s \ge 0$ and let $\nu_s$ be the
law under $\mu$ of the centered shifted path $\omega \mapsto (t \mapsto B_{s+t}(\omega) -
B_s(\omega))$ on $\mathbb{R}^{\mathbb{R}_{\ge 0}}$ with the product σ-algebra. Let
$Y : \mathbb{R}^{\mathbb{R}_{\ge 0}} \to \mathbb{R}$ be measurable with $|Y(p)| \le C$ for every
path $p$, for some real $C$, and for $x \in \mathbb{R}$ put
$\Phi_s(x) = \int Y(t \mapsto x + f(t)) \, d\nu_s(f)$. Then, $\mu$-almost everywhere,
$$\mathbb{E}_\mu\big[\, Y\big((B_{s+t})_{t \ge 0}\big) \bigm| \mathcal{F}_s \big] = \Phi_s(B_s).$$

The function $\Phi_s$ is computed from the law of the increments after time $s$, so it may
depend on $s$. -/
lemma independent_increments_condExp (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) [IsProbabilityMeasure μ] (s : ℝ≥0)
    {Y : (ℝ≥0 → ℝ) → ℝ} (hY : Measurable Y) {C : ℝ} (hYb : ∀ p, |Y p| ≤ C) :
    μ[fun ω => Y (bmShifted B s ω) | ℱ s] =ᵐ[μ]
      fun ω => bmPathExpectation B μ s Y (B s ω) := by
  have hBs : Measurable (B s) := (hAd s).mono (Filtration.le ℱ s) le_rfl
  have hYshift_int : Integrable (fun ω => Y (bmShifted B s ω)) μ := by
    refine Integrable.of_bound ?_ C ?_
    · exact ((hY.comp (measurable_bmShifted hAd s)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun ω => by
        show ‖Y (bmShifted B s ω)‖ ≤ C
        rw [Real.norm_eq_abs]
        exact hYb _)
  have hExp_int : Integrable (fun ω => bmPathExpectation B μ s Y (B s ω)) μ := by
    refine Integrable.of_bound ?_ C ?_
    · exact (((measurable_bmPathExpectation hY).comp hBs).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun ω => by
        show ‖bmPathExpectation B μ s Y (B s ω)‖ ≤ C
        rw [Real.norm_eq_abs]
        exact bmPathExpectation_bound hY hYb _)
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (Filtration.le ℱ s) hYshift_int ?_ ?_ ?_
  · intro T hT _hTfin
    exact hExp_int.integrableOn
  · intro T hT _hTfin
    exact (brownian_markov_setIntegral hAd hInd s hY hYb T hT).symm
  · exact ((measurable_bmPathExpectation (μ := μ) hY).comp (hAd s)).stronglyMeasurable.aestronglyMeasurable

/-- Historical name for the generic independent-increments result. -/
alias brownian_markov_condExp :=
  independent_increments_condExp

end MathlibExt.Probability.IndependentIncrementsMarkovProperty
