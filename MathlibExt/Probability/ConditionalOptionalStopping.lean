/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptionalStoppingUniformIntegrable
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.PiSystem

/-!
# Conditional optional stopping with a uniformly integrable stopped process

For a real martingale `f` and stopping times `L ≤ M` (possibly infinite),
assume only that the stopped process `n ↦ f_{M ∧ n}` is uniformly integrable.
Then the stopped value at `L` is the conditional expectation of the stopped
value at `M` given `ℱ_L`:

`f_L =ᵐ μ[f_M | ℱ_L]`. The values use the existing
`stoppedValueAtTop` from `OptionalStoppingUniformIntegrable`.

## Source

The general optional stopping theorem (Lecture 29) of
`v1/Atlas/TheoryOfProbability/targets.yaml` states:
"If `L ≤ M` are stopping times and `Y_{M ∧ n}` is a uniformly integrable
submartingale, then `EY_L ≤ EY_M` and `Y_L ≤ E(Y_M | ℱ_L)`."
This file proves the conditional conclusion for martingales, with equality
and the source's stopped-process UI hypothesis. The submartingale conditional
inequality and the expectation conclusion are not proved here.

The limit-process lemma assumes UI of the whole process. Applying that
lemma to `stoppedProcess f M` gives the main result with UI only after
stopping at `M`. Its proof identifies stopped values with conditional
expectations of the `L¹` limit, via Lévy's upward theorem for the filtration
`n ↦ ℱ_{τ ∧ n}`.
-/

@[expose] public section

open MeasureTheory Filter Set

open scoped Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} [SigmaFiniteFiltration μ ℱ] {f : ℕ → Ω → ℝ}

/-- **Stopped filtration.** Let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration on a
measurable space $\Omega$ and let $\tau$ be a stopping time for it with values in
$\mathbb{N} \cup \{\infty\}$. The stopped filtration is the filtration
$n \mapsto \mathcal{F}_{\tau \wedge n}$, where $\mathcal{F}_{\tau \wedge n}$ is the σ-algebra of
the stopping time $\tau \wedge n$. -/
noncomputable def IsStoppingTime.stoppedFiltration (ℱ : Filtration ℕ m0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) : Filtration ℕ m0 where
  seq n := (hτ.min_const n).measurableSpace
  mono' := by
    intro i j hij
    exact IsStoppingTime.measurableSpace_mono (hτ.min_const i) (hτ.min_const j)
      (fun ω => min_le_min le_rfl (WithTop.coe_le_coe.mpr hij))
  le' n := (hτ.min_const n).measurableSpace_le

/-- **Levels of the stopped filtration.** Let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration
on a measurable space $\Omega$ and let $\tau$ be a stopping time for it with values in
$\mathbb{N} \cup \{\infty\}$. For every $n \in \mathbb{N}$, the $n$-th σ-algebra of the stopped
filtration is $\mathcal{F}_{\tau \wedge n}$, the σ-algebra of the stopping time $\tau \wedge n$. -/
theorem IsStoppingTime.stoppedFiltration_apply (ℱ : Filtration ℕ m0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    (hτ.stoppedFiltration ℱ) n = (hτ.min_const n).measurableSpace :=
  rfl

/-- **The event that the stopping time is infinite is measurable for the stopped filtration.** Let
$(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration on a measurable space $\Omega$ and let $\tau$
be a stopping time for it with values in $\mathbb{N} \cup \{\infty\}$. For each $n$, let
$\mathcal{F}_{\tau \wedge n}$ be the σ-algebra of the stopping time $\tau \wedge n$. Then the set
$\{\omega : \tau(\omega) = \infty\}$ is measurable with respect to
$\bigvee_n \mathcal{F}_{\tau \wedge n}$. -/
theorem IsStoppingTime.measurableSet_eq_top_iSup_stoppedFiltration
    (ℱ : Filtration ℕ m0) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[⨆ n, (hτ.stoppedFiltration ℱ) n] {ω | τ ω = ⊤} := by
  have hset : {ω : Ω | τ ω = ⊤} = ⋂ (n : ℕ), {ω | ((n : WithTop ℕ)) < τ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h n
      rw [h]
      exact WithTop.coe_lt_top n
    · intro h
      by_contra hne
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      have := h n
      rw [← hn] at this
      exact absurd this (by simp)
  rw [hset]
  apply MeasurableSet.iInter
  intro n
  have h1 : MeasurableSet[(hτ.min_const n).measurableSpace]
      {ω | ((n : WithTop ℕ)) < τ ω} := by
    have hinf : MeasurableSet[hτ.measurableSpace ⊓ ℱ n]
        {ω | ((n : WithTop ℕ)) < τ ω} :=
      MeasurableSpace.measurableSet_inf.mpr ⟨hτ.measurableSet_gt' n, hτ.measurableSet_gt n⟩
    exact (IsStoppingTime.measurableSpace_min_const hτ).symm ▸ hinf
  exact (le_iSup (fun k => (hτ.stoppedFiltration ℱ) k) n) _ h1

/-- **Infinite-time parts of limit-σ-algebra sets are measurable for the stopped filtration.** Let
$(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration on a measurable space $\Omega$ and let $\tau$
be a stopping time for it with values in $\mathbb{N} \cup \{\infty\}$. For each $n$, let
$\mathcal{F}_{\tau \wedge n}$ be the σ-algebra of the stopping time $\tau \wedge n$. If a set
$s \subseteq \Omega$ is measurable with respect to $\bigvee_n \mathcal{F}_n$, then
$s \cap \{\tau = \infty\}$ is measurable with respect to $\bigvee_n \mathcal{F}_{\tau \wedge n}$.

The proof is induction on the σ-algebra generated by the π-system of sets measurable at some
finite time. For $s \in \mathcal{F}_k$ and $m \ge k$, the sets
$(s \cap \{\tau > m\}) \cup \{\tau \le m\}$ lie in $\mathcal{F}_{\tau \wedge m}$, and their
intersection over $m \ge k$, intersected with $\{\tau = \infty\}$, is $s \cap \{\tau = \infty\}$. -/
theorem IsStoppingTime.measurableSet_inter_eq_top_iSup_stoppedFiltration
    (ℱ : Filtration ℕ m0) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    {s : Set Ω} (hs : MeasurableSet[⨆ n, ℱ n] s) :
    MeasurableSet[⨆ n, (hτ.stoppedFiltration ℱ) n] (s ∩ {ω | τ ω = ⊤}) := by
  have htop := hτ.measurableSet_eq_top_iSup_stoppedFiltration ℱ
  have hpi : IsPiSystem {t : Set Ω | ∃ n, MeasurableSet[ℱ n] t} := by
    rw [Set.ofPred_exists]
    exact isPiSystem_iUnion_of_monotone _ (fun n => (ℱ n).isPiSystem_measurableSet)
      (fun _ _ => ℱ.mono)
  induction s, hs using MeasurableSpace.induction_on_inter
    (MeasurableSpace.measurableSpace_iSup_eq ℱ) hpi with
  | empty =>
    simp
  | basic t ht =>
    obtain ⟨n, hn⟩ := ht
    -- Approximating sets `B m = (t ∩ {τ > m}) ∪ {τ ≤ m}` for `m ≥ n`.
    -- Each `B m` lies in `ℱ_{τ ∧ m}` (and hence in the `iSup`), and
    -- `(⋂ m ≥ n, B m) ∩ {τ = ⊤} = t ∩ {τ = ⊤}`.
    have hBℱ : ∀ m, n ≤ m →
        MeasurableSet[ℱ m]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
      intro m hmn
      exact ((ℱ.mono hmn _ hn).inter (hτ.measurableSet_gt m)).union (hτ.measurableSet_le m)
    have hBτ : ∀ m, n ≤ m →
        MeasurableSet[hτ.measurableSpace]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
      intro m hmn
      rw [hτ.measurableSet]
      refine ⟨(le_iSup (fun k => ℱ k) m) _ (hBℱ m hmn), fun k => ?_⟩
      by_cases hk : k ≤ m
      · have heq : ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) ∩
              {ω | τ ω ≤ (k : WithTop ℕ)} = {ω | τ ω ≤ (k : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
          constructor
          · intro h
            obtain ⟨hunion, hle⟩ := h
            rcases hunion with ⟨-, hlt⟩ | hle_m
            · exact absurd (hlt.trans_le hle) (not_lt.mpr (WithTop.coe_le_coe.mpr hk))
            · exact hle
          · intro hle
            exact ⟨Or.inr (hle.trans (WithTop.coe_le_coe.mpr hk)), hle⟩
        exact (congrArg (fun s => MeasurableSet[ℱ k] s) heq).mpr (hτ.measurableSet_le k)
      · have hk' : m < k := Nat.lt_of_not_le hk
        have heq : ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) ∩
                {ω | τ ω ≤ (k : WithTop ℕ)}
            = (t ∩ {ω | (m : WithTop ℕ) < τ ω ∧ τ ω ≤ (k : WithTop ℕ)}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
          constructor
          · intro h
            obtain ⟨hunion, hle⟩ := h
            rcases hunion with ⟨htω, hlt⟩ | hle_m
            · exact Or.inl ⟨htω, hlt, hle⟩
            · exact Or.inr hle_m
          · intro h
            rcases h with ⟨htω, hlt, hle⟩ | hle_m
            · exact ⟨Or.inl ⟨htω, hlt⟩, hle⟩
            · exact ⟨Or.inr hle_m, hle_m.trans (WithTop.coe_le_coe.mpr (Nat.le_of_lt hk'))⟩
        refine (congrArg (fun s => MeasurableSet[ℱ k] s) heq).mpr ?_
        apply MeasurableSet.union
        · apply MeasurableSet.inter
          · exact ℱ.mono (hmn.trans (Nat.le_of_lt hk')) _ hn
          · exact ((ℱ.mono (Nat.le_of_lt hk') _ (hτ.measurableSet_gt m)).inter
              (hτ.measurableSet_le k))
        · exact ℱ.mono (Nat.le_of_lt hk') _ (hτ.measurableSet_le m)
    have hBmem : ∀ m, n ≤ m →
        MeasurableSet[⨆ k, (hτ.stoppedFiltration ℱ) k]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
      intro m hmn
      have h1 : MeasurableSet[(hτ.min_const m).measurableSpace]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
        have hinf : MeasurableSet[hτ.measurableSpace ⊓ ℱ m]
            ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) :=
          MeasurableSpace.measurableSet_inf.mpr ⟨hBτ m hmn, hBℱ m hmn⟩
        exact (IsStoppingTime.measurableSpace_min_const hτ).symm ▸ hinf
      exact (le_iSup (fun k => (hτ.stoppedFiltration ℱ) k) m) _ h1
    have hInter : (⋂ m ∈ Set.Ici n,
            ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)})) ∩ {ω | τ ω = ⊤}
        = t ∩ {ω | τ ω = ⊤} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_Ici, Set.mem_union,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hω, htopω⟩
        have hmem := hω n le_rfl
        rcases hmem with ⟨htω, -⟩ | hle
        · exact ⟨htω, htopω⟩
        · rw [htopω] at hle
          exact absurd hle (by simp)
      · rintro ⟨htω, htopω⟩
        refine ⟨fun m _ => Or.inl ⟨htω, ?_⟩, htopω⟩
        rw [htopω]
        exact WithTop.coe_lt_top m
    rw [← hInter]
    exact MeasurableSet.inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun (_ : n ≤ m) => hBmem m ‹n ≤ m›)
      htop
  | compl t _ iht =>
    have : tᶜ ∩ {ω | τ ω = ⊤} = {ω | τ ω = ⊤} \ (t ∩ {ω | τ ω = ⊤}) := by
      ext ω
      simp [Set.mem_sdiff, and_comm]
    rw [this]
    exact htop.diff iht
  | iUnion f _ _ ih =>
    have : (⋃ i, f i) ∩ {ω | τ ω = ⊤} = ⋃ i, (f i ∩ {ω | τ ω = ⊤}) := by
      rw [Set.iUnion_inter]
    rw [this]
    exact MeasurableSet.iUnion ih

/-- **The stopped filtration generates the stopping-time σ-algebra.** Let
$(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration on a measurable space $\Omega$ and let $\tau$
be a stopping time for it with values in $\mathbb{N} \cup \{\infty\}$. For each $n$, let
$\mathcal{F}_{\tau \wedge n}$ be the σ-algebra of the stopping time $\tau \wedge n$, the $n$-th
σ-algebra of the stopped filtration, and let $\mathcal{F}_\tau$ be the σ-algebra of $\tau$. Then
$\bigvee_n \mathcal{F}_{\tau \wedge n} = \mathcal{F}_\tau$.

The inclusion $\le$ is monotonicity. For $\ge$, a set $s \in \mathcal{F}_\tau$ splits into its
finite-time part $s \cap \{\tau < \infty\} = \bigcup_n (s \cap \{\tau \le n\})$ and its
infinite-time part $s \cap \{\tau = \infty\}$, and both are measurable for the supremum. -/
theorem IsStoppingTime.iSup_stoppedFiltration (ℱ : Filtration ℕ m0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    ⨆ n, (hτ.stoppedFiltration ℱ) n = hτ.measurableSpace := by
  apply le_antisymm
  · apply iSup_le
    intro n
    show (hτ.min_const n).measurableSpace ≤ hτ.measurableSpace
    exact IsStoppingTime.measurableSpace_mono (hτ.min_const n) hτ
      (fun ω => min_le_left _ _)
  · intro s hs
    have hs_split := (hτ.measurableSet s).mp hs
    have htop_part := hτ.measurableSet_inter_eq_top_iSup_stoppedFiltration ℱ hs_split.1
    have hlt_part : MeasurableSet[⨆ n, (hτ.stoppedFiltration ℱ) n]
        (s ∩ {ω | τ ω < ⊤}) := by
      have hset : s ∩ {ω | τ ω < ⊤} = ⋃ (n : ℕ), (s ∩ {ω | τ ω ≤ ((n : WithTop ℕ))}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hsω, hlt⟩
          obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hlt)
          exact ⟨k, hsω, le_of_eq hk.symm⟩
        · rintro ⟨n, hsω, hle⟩
          exact ⟨hsω, lt_of_le_of_lt hle (WithTop.coe_lt_top n)⟩
      rw [hset]
      apply MeasurableSet.iUnion
      intro n
      have hinf : MeasurableSet[hτ.measurableSpace ⊓ ℱ n]
          (s ∩ {ω | τ ω ≤ ((n : WithTop ℕ))}) :=
        MeasurableSpace.measurableSet_inf.mpr
          ⟨hs.inter (hτ.measurableSet_le' n), hs_split.2 n⟩
      have hmin : MeasurableSet[(hτ.min_const n).measurableSpace]
          (s ∩ {ω | τ ω ≤ ((n : WithTop ℕ))}) :=
        (IsStoppingTime.measurableSpace_min_const hτ).symm ▸ hinf
      exact (le_iSup (fun k => (hτ.stoppedFiltration ℱ) k) n) _ hmin
    have hsplit : s = (s ∩ {ω | τ ω = ⊤}) ∪ (s ∩ {ω | τ ω < ⊤}) := by
      ext ω
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hsω
        rcases lt_or_eq_of_le (le_top : τ ω ≤ ⊤) with hlt | heqτ
        · exact Or.inr ⟨hsω, hlt⟩
        · exact Or.inl ⟨hsω, heqτ⟩
      · rintro (⟨hsω, -⟩ | ⟨hsω, -⟩)
        · exact hsω
        · exact hsω
    exact (congrArg
      (fun t => MeasurableSet[⨆ n, (hτ.stoppedFiltration ℱ) n] t) hsplit).mpr
      (MeasurableSet.union htop_part hlt_part)

set_option linter.style.haveILetI false in
/-- **Stopped value as conditional expectation of the limit.** Let $\mu$ be a probability measure
on $\Omega$, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration, and let
$(f_n)_{n \in \mathbb{N}}$ be a real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$
that is uniformly integrable in $L^1(\mu)$. Let $f_\infty$ be its limit process, a function
measurable with respect to $\bigvee_n \mathcal{F}_n$ to which $f_n$ converges $\mu$-almost
everywhere. Then for every stopping time $\tau$ with values in $\mathbb{N} \cup \{\infty\}$, the
value $f_\tau$ of $f$ at $\tau$ (with $f_\tau(\omega) = \lim_n f_n(\omega)$ where
$\tau(\omega) = \infty$) satisfies $f_\tau = \mu[f_\infty \mid \mathcal{F}_\tau]$ $\mu$-almost
everywhere, where $\mu[\,\cdot \mid \mathcal{F}_\tau]$ is conditional expectation given the
σ-algebra $\mathcal{F}_\tau$ of $\tau$.

For each $n$, bounded optional sampling gives
$f_{\tau \wedge n} = \mu[f_\infty \mid \mathcal{F}_{\tau \wedge n}]$ almost everywhere, and
Lévy's upward theorem for the filtration $n \mapsto \mathcal{F}_{\tau \wedge n}$ identifies the
almost-everywhere limit of these conditional expectations with
$\mu[f_\infty \mid \bigvee_n \mathcal{F}_{\tau \wedge n}] = \mu[f_\infty \mid \mathcal{F}_\tau]$. -/
theorem Martingale.stoppedValueAtTop_ae_eq_condExp_limitProcess
    (hf : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    stoppedValueAtTop f τ =ᵐ[μ] μ[ℱ.limitProcess f μ | hτ.measurableSpace] := by
  haveI : SigmaFiniteFiltration μ (hτ.stoppedFiltration ℱ) :=
    ⟨fun n => IsStoppingTime.sigmaFinite_stopping_time (hτ.min_const n)⟩
  -- Bounded optional sampling at `τ ∧ n`.
  have hstep : ∀ n, stoppedProcess f τ n
      =ᵐ[μ] μ[ℱ.limitProcess f μ | (hτ.stoppedFiltration ℱ) n] := by
    intro n
    have hpoint : stoppedProcess f τ n
        = stoppedValue f (fun ω => min (τ ω) ((n : WithTop ℕ))) := by
      funext ω
      exact (congrArg (fun a => f a ω)
        (congrArg WithTop.untopA (min_comm (τ ω) ((n : WithTop ℕ))))).symm
    calc stoppedProcess f τ n
        = stoppedValue f (fun ω => min (τ ω) ((n : WithTop ℕ))) := hpoint
      _ =ᵐ[μ] μ[f n | (hτ.stoppedFiltration ℱ) n] :=
          hf.stoppedValue_ae_eq_condExp_of_le_const (hτ.min_const n)
            (fun ω => min_le_right _ _)
      _ =ᵐ[μ] μ[μ[ℱ.limitProcess f μ | ℱ n] | (hτ.stoppedFiltration ℱ) n] :=
          condExp_congr_ae (hf.ae_eq_condExp_limitProcess hui n)
      _ =ᵐ[μ] μ[ℱ.limitProcess f μ | (hτ.stoppedFiltration ℱ) n] :=
          condExp_condExp_of_le (by
            show (hτ.min_const n).measurableSpace ≤ ℱ n
            exact (hτ.min_const n).measurableSpace_le_of_le_const
              (fun ω => min_le_right _ _))
            (ℱ.le n)
  -- The stopped process converges a.e. to the stopped value at `τ`.
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess f τ n ω) atTop
      (𝓝 (stoppedValueAtTop f τ ω)) := by
    filter_upwards [hf.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hui]
      with ω hω
    by_cases hτtop : τ ω = ⊤
    · have hlim : limUnder atTop (fun n => f n ω) = ℱ.limitProcess f μ ω :=
        hω.limUnder_eq
      have hfun : (fun n => stoppedProcess f τ n ω) = fun n => f n ω := by
        funext n
        show f (min ((n : WithTop ℕ)) (τ ω)).untopA ω = f n ω
        rw [hτtop, min_top_right]
        rfl
      rw [hfun]
      have hval : stoppedValueAtTop f τ ω = ℱ.limitProcess f μ ω := by
        show (if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
          else stoppedValue f τ ω) = ℱ.limitProcess f μ ω
        rw [ite_eq_left hτtop, hlim]
      rw [hval]
      exact hω
    · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hτtop
      have hval : stoppedValueAtTop f τ ω = f k ω := by
        show (if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
          else stoppedValue f τ ω) = f k ω
        rw [ite_eq_right hτtop]
        show f (τ ω).untopA ω = f k ω
        rw [← hk]
        rfl
      rw [hval]
      refine tendsto_atTop_of_eventually_const (i₀ := k) (fun n hn => ?_)
      have hle : τ ω ≤ ((n : WithTop ℕ)) := by
        rw [← hk]
        exact WithTop.coe_le_coe.mpr hn
      have hsp := stoppedProcess_eq_of_ge (u := f) (τ := τ) (i := n) hle
      rw [hsp, ← hk]
      rfl
  have hstep_all : ∀ᵐ ω ∂μ, ∀ n,
      stoppedProcess f τ n ω = (μ[ℱ.limitProcess f μ | (hτ.stoppedFiltration ℱ) n]) ω :=
    ae_all_iff.mpr hstep
  have hlevy : ∀ᵐ ω ∂μ, Tendsto
      (fun n => (μ[ℱ.limitProcess f μ | (hτ.stoppedFiltration ℱ) n]) ω) atTop
      (𝓝 ((μ[ℱ.limitProcess f μ | ⨆ n, (hτ.stoppedFiltration ℱ) n]) ω)) :=
    tendsto_ae_condExp (ℱ := hτ.stoppedFiltration ℱ) (ℱ.limitProcess f μ)
  filter_upwards [hconv, hlevy, hstep_all] with ω hω hlevyω hstepω
  have hlim1 : Tendsto
      (fun n => (μ[ℱ.limitProcess f μ | (hτ.stoppedFiltration ℱ) n]) ω) atTop
      (𝓝 (stoppedValueAtTop f τ ω)) :=
    hω.congr (fun n => hstepω n)
  have hfinal : stoppedValueAtTop f τ ω
      = (μ[ℱ.limitProcess f μ | ⨆ n, (hτ.stoppedFiltration ℱ) n]) ω :=
    tendsto_nhds_unique hlim1 hlevyω
  rwa [hτ.iSup_stoppedFiltration ℱ] at hfinal

/-- **Stopping at a later time does not change the stopped value.** Let $(f_n)_{n \in \mathbb{N}}$
be a sequence of real-valued functions on $\Omega$ and let
$L, M : \Omega \to \mathbb{N} \cup \{\infty\}$ satisfy $L(\omega) \le M(\omega)$ for every
$\omega$. Then the value at $L$ of the stopped process $n \mapsto f_{M \wedge n}$ equals the value
$f_L$ of $f$ at $L$ at every point of $\Omega$. Here the value of a sequence $(g_n)$ at a point
$\omega$ where the time is infinite is $\lim_n g_n(\omega)$ when this limit exists, and otherwise
a fixed default value that depends only on the sequence $(g_n(\omega))_{n \in \mathbb{N}}$.

On $\{L = \infty\}$ the inequality forces $M = \infty$, so there the stopped process is $f$
itself. -/
theorem stoppedValueAtTop_stoppedProcess_of_le
    {L M : Ω → WithTop ℕ} (hLM : L ≤ M) :
    stoppedValueAtTop (stoppedProcess f M) L = stoppedValueAtTop f L := by
  funext ω
  by_cases hLtop : L ω = ⊤
  · have hMtop : M ω = ⊤ := top_le_iff.mp (hLtop ▸ hLM ω)
    have hseq : (fun n => stoppedProcess f M n ω) = fun n => f n ω := by
      funext n
      exact stoppedProcess_eq_of_le (by rw [hMtop]; exact le_top)
    simp only [stoppedValueAtTop, hLtop, ite_true]
    rw [hseq]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hLtop
    simp only [stoppedValueAtTop, hLtop, ite_false]
    rw [← hk]
    change stoppedProcess f M k ω = f k ω
    exact stoppedProcess_eq_of_le (by rw [hk]; exact hLM ω)

/-- The whole-process UI case, using the unchanged limit-process engine. -/
private theorem stoppedValueAtTop_ae_eq_condExp_of_uniformIntegrable
    (hf : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtTop f L
      =ᵐ[μ] μ[stoppedValueAtTop f M | hL.measurableSpace] := by
  have hL_eq := hf.stoppedValueAtTop_ae_eq_condExp_limitProcess hui hL
  have hM_eq := hf.stoppedValueAtTop_ae_eq_condExp_limitProcess hui hM
  exact (hL_eq.trans
    (condExp_condExp_of_le (IsStoppingTime.measurableSpace_mono hL hM hLM)
      hM.measurableSpace_le).symm).trans (condExp_congr_ae hM_eq).symm

/-- **Conditional optional stopping with UI of the stopped process.** Let $\mu$ be a probability
measure on $\Omega$, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration, and let
$(f_n)_{n \in \mathbb{N}}$ be a real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$.
Let $L \le M$ be stopping times with values in $\mathbb{N} \cup \{\infty\}$, and suppose the
stopped process $(f_{M \wedge n})_{n \in \mathbb{N}}$ is uniformly integrable in $L^1(\mu)$. Then
$f_L = \mu[f_M \mid \mathcal{F}_L]$ $\mu$-almost everywhere. Here $f_L$ and $f_M$ are the values
of $f$ at the possibly infinite times $L$ and $M$, with $f_L(\omega) = \lim_n f_n(\omega)$ where
$L(\omega) = \infty$ and likewise for $M$, and $\mu[\,\cdot \mid \mathcal{F}_L]$ is conditional
expectation given the σ-algebra $\mathcal{F}_L$ of $L$.

If $f$ itself is uniformly integrable, then so is the stopped process $(f_{M \wedge n})$, so the
conclusion holds in that case as well. -/
theorem Martingale.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop
    (hf : Martingale f ℱ μ) {L M : Ω → WithTop ℕ}
    (hui : UniformIntegrable (stoppedProcess f M) 1 μ)
    (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M) (hLM : L ≤ M) :
    stoppedValueAtTop f L
      =ᵐ[μ] μ[stoppedValueAtTop f M | hL.measurableSpace] := by
  have hstop : Martingale (stoppedProcess f M) ℱ μ := by
    refine martingale_iff.mpr ⟨?_, hf.submartingale.stoppedProcess hM⟩
    simpa only [stoppedProcess_neg, neg_neg] using
      (hf.neg.submartingale.stoppedProcess hM).neg
  have h := stoppedValueAtTop_ae_eq_condExp_of_uniformIntegrable hstop hui hL hM hLM
  rwa [stoppedValueAtTop_stoppedProcess_of_le (f := f) hLM,
    stoppedValueAtTop_stoppedProcess_of_le (f := f) (L := M) (M := M) le_rfl] at h

end MeasureTheory
