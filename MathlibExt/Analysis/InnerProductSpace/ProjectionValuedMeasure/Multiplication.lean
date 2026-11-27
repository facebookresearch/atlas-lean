/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.MeasureTheory.Function.LpSpace.SupportedOn
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Indicator multiplication as a projection-valued measure

For any measure `μ` on a measurable space `X`, let `L²(μ)=Lp ℂ 2 μ`. A measurable set `s`
defines the orthogonal projection `P_s` by `(P_s f)(x)=1_s(x) f(x)` almost everywhere. Its range
is the closed subspace of functions vanishing almost everywhere off `s`.

These projections satisfy `P_∅=0`, `P_X=I`, `P_(s∩t)=P_s P_t`, and `Σ_n P_(s_n) f=P_(⋃n s_n) f`
in the Hilbert norm for pairwise disjoint measurable sets `s_n`. Assigning zero to nonmeasurable
sets gives the indicator-multiplication PVM. No finiteness, sigma-finiteness, nonzero measure or
nonempty-space condition is imposed.

## Indicator spectral measures

John B. Conway, A Course in Functional Analysis, second edition, Chapter IX, §1, Example 1.6,
gives the compact Borel-space example. Here the measure space is arbitrary and countable
additivity is strong operator additivity.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace MeasureTheory Topology

namespace MathlibExt.Analysis.InnerProductSpace

noncomputable section

universe u

namespace ProjectionValuedMeasure

variable {X : Type u} [MeasurableSpace X] (mu : Measure X)

private noncomputable def indicatorLinearMap (s : Set X) (hs : MeasurableSet s) :
    Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun f := ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator fun x ↦ f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (f + g)).indicator hs.nullMeasurableSet).coeFn_toLp,
      ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp,
      ((Lp.memLp g).indicator hs.nullMeasurableSet).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add (((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator fun x ↦ f x))
        (((Lp.memLp g).indicator hs.nullMeasurableSet).toLp (s.indicator fun x ↦ g x))] with x hfg
            hf hg hadd ht
    rw [hfg, ht, Pi.add_apply, hf, hg]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [hadd, Pi.add_apply]
    · simp [hx]
  map_smul' c f := by
    change ((Lp.memLp (c • f)).indicator hs.nullMeasurableSet).toLp
        (s.indicator fun x ↦ (c • f) x) =
      c • ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator fun x ↦ f x)
    apply Lp.ext
    filter_upwards [((Lp.memLp (c • f)).indicator hs.nullMeasurableSet).coeFn_toLp,
      ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c
          (((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator fun x ↦ f x))]
      with x hcf hf hsmul ht
    rw [hcf, ht, Pi.smul_apply, hf]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [hsmul, Pi.smul_apply]
    · simp [hx]

private theorem norm_indicatorLinearMap_le (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℂ 2 mu) :
    ‖indicatorLinearMap mu s hs f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator fun x ↦ f x)‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  exact eLpNorm_indicator_le (fun x ↦ f x) hs.nullMeasurableSet

/-- **Orthogonal projection by an indicator multiplier.** Let `X` be a measurable space, `μ`
any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for a measurable set `s`,
`indicatorProjection μ s : L²(μ) →L[ℂ] L²(μ)` acts by `f ↦ 1_s f` almost everywhere, with
norm at most one. -/
@[no_expose]
noncomputable def indicatorProjection (s : Set X) (hs : MeasurableSet s) :
    Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  (indicatorLinearMap mu s hs).mkContinuous 1 fun f ↦ by
    simpa only [one_mul] using norm_indicatorLinearMap_le mu s hs f

/-- **Almost-everywhere formula for an indicator projection.** Let `X` be a measurable space,
`μ` any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for a measurable `s ⊆
X` and `f ∈ L²(μ)`, `(indicatorProjection μ s f)(x)=1_s(x) f(x)` for `μ`-almost every `x`.
In Lean this is `indicatorProjection μ s hs f =ᵐ[μ] s.indicator f`. -/
theorem indicatorProjection_apply (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 mu) :
    indicatorProjection mu s hs f =ᵐ[mu] s.indicator fun x ↦ f x :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp

@[simp]
theorem indicatorProjection_empty :
    indicatorProjection mu ∅ MeasurableSet.empty = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [zero_apply]
  apply Lp.ext
  filter_upwards [indicatorProjection_apply mu ∅ MeasurableSet.empty f,
    Lp.coeFn_zero ℂ 2 mu] with x hf hzero
  have hf' : indicatorProjection mu ∅ MeasurableSet.empty f x = 0 := by
    simpa only [Set.indicator_empty, Pi.zero_apply] using hf
  exact hf'.trans (by simpa only [Pi.zero_apply] using hzero.symm)

@[simp]
theorem indicatorProjection_univ :
    indicatorProjection mu Set.univ MeasurableSet.univ = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [indicatorProjection_apply mu Set.univ MeasurableSet.univ f] with x hf
  simpa using hf

/-- **Intersection product of indicator projections.** Let `X` be a measurable space, `μ` any
measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for measurable sets `s,t`,
`indicatorProjection μ (s∩t)=indicatorProjection μ s * indicatorProjection μ t`, with
operator multiplication given by composition. -/
theorem indicatorProjection_inter (s t : Set X) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    indicatorProjection mu (s ∩ t) (hs.inter ht) =
      indicatorProjection mu s hs * indicatorProjection mu t ht := by
  apply ContinuousLinearMap.ext
  intro f
  change indicatorProjection mu (s ∩ t) (hs.inter ht) f =
    indicatorProjection mu s hs (indicatorProjection mu t ht f)
  apply Lp.ext
  filter_upwards [indicatorProjection_apply mu (s ∩ t) (hs.inter ht) f,
    indicatorProjection_apply mu t ht f,
    indicatorProjection_apply mu s hs (indicatorProjection mu t ht f)] with x hst ht' hs'
  rw [hst, hs']
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt, ht']

/-- **Additivity on disjoint measurable indicators.** Let `X` be a measurable space, `μ` any
measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. if measurable `s,t` are
disjoint, `indicatorProjection μ (s∪t)=indicatorProjection μ s+indicatorProjection μ t`. -/
theorem indicatorProjection_union {s t : Set X} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    indicatorProjection mu (s ∪ t) (hs.union ht) =
      indicatorProjection mu s hs + indicatorProjection mu t ht := by
  apply ContinuousLinearMap.ext
  intro f
  change indicatorProjection mu (s ∪ t) (hs.union ht) f =
    indicatorProjection mu s hs f + indicatorProjection mu t ht f
  apply Lp.ext
  filter_upwards [indicatorProjection_apply mu (s ∪ t) (hs.union ht) f,
    indicatorProjection_apply mu s hs f, indicatorProjection_apply mu t ht f,
    Lp.coeFn_add (indicatorProjection mu s hs f) (indicatorProjection mu t ht f)]
      with x hu hs' ht' hadd
  rw [hu, hadd, Pi.add_apply, hs', ht']
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t
  · exact (Set.disjoint_left.1 hdisj hxs hxt).elim
  all_goals simp [hxs, hxt]

/-- **Self-adjoint idempotence of an indicator multiplier.** Let `X` be a measurable space,
`μ` any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for a measurable set
`s`, `P=indicatorProjection μ s` satisfies `P²=P` and `P*=P`. -/
theorem indicatorProjection_isStarProjection (s : Set X) (hs : MeasurableSet s) :
    IsStarProjection (indicatorProjection mu s hs) := by
  constructor
  · change indicatorProjection mu s hs * indicatorProjection mu s hs =
      indicatorProjection mu s hs
    simpa only [Set.inter_self] using (indicatorProjection_inter mu s s hs hs).symm
  · rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro f g
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indicatorProjection_apply mu s hs f,
      indicatorProjection_apply mu s hs g] with x hf hg
    rw [hf, hg]
    by_cases hx : x ∈ s <;> simp [hx]

/-- **Subspace of square-integrable functions supported on a set.** Let `X` be a measurable
space, `μ` any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for any `s ⊆
X`, `indicatorRange μ s` is the complex submodule `{f ∈ L²(μ) : f(x)=0 for μ-almost every
x outside s}`. -/
abbrev indicatorRange (s : Set X) : Submodule ℂ (Lp ℂ 2 mu) :=
  MathlibExt.MeasureTheory.Function.Lp.supportedOn
    (𝕜 := ℂ) (E := ℂ) (p := 2) mu s

/-- **Range of an indicator projection.** Let `X` be a measurable space, `μ` any measure on
`X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for a measurable set `s`, the linear
range of `indicatorProjection μ s` is exactly `indicatorRange μ s`, the functions
vanishing almost everywhere off `s`. -/
theorem range_indicatorProjection (s : Set X) (hs : MeasurableSet s) :
    LinearMap.range (indicatorProjection mu s hs).toLinearMap = indicatorRange mu s := by
  apply le_antisymm
  · rintro f ⟨g, rfl⟩
    change ∀ᵐ x ∂mu, x ∉ s → indicatorProjection mu s hs g x = 0
    filter_upwards [indicatorProjection_apply mu s hs g] with x hx
    intro hxs
    rw [hx, Set.indicator_of_notMem hxs]
  · intro f hf
    refine ⟨f, ?_⟩
    change indicatorProjection mu s hs f = f
    change ∀ᵐ x ∂mu, x ∉ s → f x = 0 at hf
    apply Lp.ext
    filter_upwards [indicatorProjection_apply mu s hs f, hf] with x hproj hf
    rw [hproj]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem hxs, hf hxs]

private theorem indicatorProjection_biUnion_finset {I : Type*} (u : Finset I)
    (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : (u : Set I).PairwiseDisjoint s) :
    indicatorProjection mu (⋃ i ∈ u, s i) (Finset.measurableSet_biUnion u fun i _ ↦ hs i) =
      ∑ i ∈ u, indicatorProjection mu (s i) (hs i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | @insert a u hau ih =>
      have ha : MeasurableSet (s a) := hs a
      have hu : MeasurableSet (⋃ i ∈ u, s i) :=
        Finset.measurableSet_biUnion u fun i _ ↦ hs i
      have hdisj' : Disjoint (s a) (⋃ i ∈ u, s i) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        rw [Set.disjoint_iUnion_right]
        intro hi
        exact hdisj (Finset.mem_insert_self a u) (Finset.mem_insert_of_mem hi) fun hai ↦
            hau (hai ▸ hi)
      have hinsert : (⋃ i ∈ insert a u, s i) = s a ∪ ⋃ i ∈ u, s i := by
        ext x
        simp
      simp only [hinsert, Finset.sum_insert hau]
      rw [indicatorProjection_union mu ha hu hdisj']
      rw [ih (by
        intro i hi j hj hij
        exact hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij)]

private def partialUnion (s : ℕ → Set X) (n : ℕ) : Set X :=
  ⋃ i ∈ Finset.range n, s i

private def unionTail (s : ℕ → Set X) (n : ℕ) : Set X :=
  (⋃ i, s i) \ partialUnion s n

private theorem measurableSet_partialUnion (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (n : ℕ) : MeasurableSet (partialUnion s n) :=
  Finset.measurableSet_biUnion _ fun i _ ↦ hs i

private theorem measurableSet_unionTail (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (n : ℕ) : MeasurableSet (unionTail s n) :=
  (MeasurableSet.iUnion hs).diff (measurableSet_partialUnion s hs n)

omit [MeasurableSpace X] in
private theorem antitone_unionTail (s : ℕ → Set X) : Antitone (unionTail s) := by
  intro m n hmn
  apply Set.sdiff_subset_sdiff_right
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂_of_mem (Finset.mem_range.2 ((Finset.mem_range.1 hi).trans_le hmn)) hxi

omit [MeasurableSpace X] in
private theorem iInter_unionTail (s : ℕ → Set X) :
    ⋂ n, unionTail s n = ∅ := by
  ext x
  constructor
  · intro hx
    have hxall := Set.mem_iInter.mp hx
    have hxU : x ∈ ⋃ i, s i := (hxall 0).1
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
    have hxtail := hxall (i + 1)
    exact hxtail.2 (Set.mem_iUnion₂_of_mem (Finset.mem_range.2 (Nat.lt_succ_self i)) hxi)
  · simp

private theorem norm_sq_indicatorProjection (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℂ 2 mu) :
    ‖indicatorProjection mu s hs f‖ ^ 2 = ∫ x in s, ‖f x‖ ^ 2 ∂mu := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def (𝕜 := ℂ)]
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (indicatorProjection mu s hs f)
    (indicatorProjection mu s hs f))]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorProjection_apply mu s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;>
    simp [hxs, inner_self_eq_norm_sq_to_K]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

private theorem tendsto_indicatorProjection_partialUnion
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n)) (f : Lp ℂ 2 mu) :
    Tendsto (fun n ↦ indicatorProjection mu (partialUnion s n)
      (measurableSet_partialUnion s hs n) f) atTop
      (𝓝 (indicatorProjection mu (⋃ n, s n) (MeasurableSet.iUnion hs) f)) := by
  let U : Set X := ⋃ n, s n
  let t : ℕ → Set X := unionTail s
  have htmeas : ∀ n, MeasurableSet (t n) := measurableSet_unionTail s hs
  have hanti : Antitone t := antitone_unionTail s
  have hfint : Integrable (fun x ↦ ‖f x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable f).aestronglyMeasurable).1 (Lp.memLp f)
  have hint := hanti.tendsto_setIntegral htmeas hfint.integrableOn
  rw [iInter_unionTail, setIntegral_empty] at hint
  have hnormsq : Tendsto
      (fun n ↦ ‖indicatorProjection mu (t n) (htmeas n) f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_sq_indicatorProjection] using hint
  have hnorm : Tendsto (fun n ↦ ‖indicatorProjection mu (t n) (htmeas n) f‖)
      atTop (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hnormsq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  convert hnorm using 1
  funext n
  rw [norm_sub_rev]
  congr 1
  apply Lp.ext
  filter_upwards [indicatorProjection_apply mu U (MeasurableSet.iUnion hs) f,
    indicatorProjection_apply mu (partialUnion s n) (measurableSet_partialUnion s hs n) f,
    indicatorProjection_apply mu (t n) (htmeas n) f,
    Lp.coeFn_sub (indicatorProjection mu U (MeasurableSet.iUnion hs) f)
      (indicatorProjection mu (partialUnion s n) (measurableSet_partialUnion s hs n) f)]
      with x hU hpartial htail hsub
  rw [hsub, Pi.sub_apply, hU, hpartial, htail]
  by_cases hxp : x ∈ partialUnion s n
  · have hxU : x ∈ U := by
      obtain ⟨i, _hi, hxi⟩ := Set.mem_iUnion₂.mp hxp
      exact Set.mem_iUnion_of_mem i hxi
    simp [U, t, unionTail, hxU, hxp]
  · by_cases hxU : x ∈ U <;> simp [U, t, unionTail, hxU, hxp]

/-- **Projection-valued measure of indicator multipliers.** Let `X` be a measurable space, `μ`
any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. `indicatorPVM μ :
ProjectionValuedMeasure X L²(μ)` sends measurable `s` to `P_s f=1_s f` and nonmeasurable
sets to zero. It is countably additive in the strong operator topology and sends `X` to
the identity. -/
@[no_expose]
noncomputable def indicatorPVM : ProjectionValuedMeasure X (Lp ℂ 2 mu) := by
  classical
  exact
    { toFun := fun s ↦ if hs : MeasurableSet s then indicatorProjection mu s hs else 0
      not_measurable' := by
        intro s hs
        simp [hs]
      projection' := by
        intro s hs
        simpa [hs] using indicatorProjection_isStarProjection mu s hs
      empty' := by simp
      univ' := by simp
      inter' := by
        intro s hs t ht
        simp only [hs, ht, hs.inter ht, dite_true]
        exact indicatorProjection_inter mu s t hs ht
      m_iUnion' := by
        intro s hs hdisj f
        let P : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
          fun n ↦ indicatorProjection mu (s n) (hs n)
        have hP (n : ℕ) : IsStarProjection (P n) := indicatorProjection_isStarProjection mu _ _
        have horth : Pairwise fun i j ↦ P i * P j = 0 := by
          intro i j hij
          simpa only [Set.disjoint_iff_inter_eq_empty.mp (hdisj hij),
            indicatorProjection_empty] using
            (indicatorProjection_inter mu (s i) (s j) (hs i) (hs j)).symm
        obtain ⟨Q, _hQproj, hQsum, _hQrange⟩ :=
          exists_hasSum_of_pairwise_orthogonal P hP horth
        have hseqQ := (hQsum f).tendsto_sum_nat
        have hseqUnion := tendsto_indicatorProjection_partialUnion mu s hs f
        have hQeq : Q f = indicatorProjection mu (⋃ n, s n) (MeasurableSet.iUnion hs) f :=
          tendsto_nhds_unique hseqQ <| by
            convert hseqUnion using 1
            funext n
            have hfinite := congrArg (fun T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu ↦ T f)
              (indicatorProjection_biUnion_finset mu (Finset.range n) s hs (by
                intro i hi j hj hij
                exact hdisj hij)).symm
            simpa only [sum_apply, P, partialUnion] using hfinite
        rw [show (if _h : MeasurableSet (⋃ n, s n) then
            indicatorProjection mu (⋃ n, s n) _h else 0) =
            indicatorProjection mu (⋃ n, s n) (MeasurableSet.iUnion hs) by
          rw [dite_eq_left (MeasurableSet.iUnion hs)]]
        rw [← hQeq]
        simpa only [P, hs, dite_true] using hQsum f }

/-- **Measurable-set action of the multiplication PVM.** Let `X` be a measurable space, `μ`
any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for a measurable set `s`
and `f ∈ L²(μ)`, `(indicatorPVM μ s f)(x)=1_s(x) f(x)` for `μ`-almost every `x`. -/
theorem indicatorPVM_apply {s : Set X} (hs : MeasurableSet s) (f : Lp ℂ 2 mu) :
    indicatorPVM mu s f =ᵐ[mu] s.indicator fun x ↦ f x := by
  classical
  rw [indicatorPVM]
  change (if h : MeasurableSet s then indicatorProjection mu s h else 0) f =ᵐ[mu]
    s.indicator fun x ↦ f x
  rw [dite_eq_left hs]
  exact indicatorProjection_apply mu s hs f

/-- **Supported-function range of the multiplication PVM.** Let `X` be a measurable space, `μ`
any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for measurable `s`, the
linear range of `indicatorPVM μ s` is `{f ∈ L²(μ) : f=0 μ-almost everywhere off s}`,
namely `indicatorRange μ s`. -/
theorem range_indicatorPVM {s : Set X} (hs : MeasurableSet s) :
    LinearMap.range (indicatorPVM mu s).toLinearMap = indicatorRange mu s := by
  classical
  rw [indicatorPVM]
  change LinearMap.range
    (if h : MeasurableSet s then indicatorProjection mu s h else 0).toLinearMap =
      indicatorRange mu s
  rw [dite_eq_left hs]
  exact range_indicatorProjection mu s hs

end ProjectionValuedMeasure

end

end MathlibExt.Analysis.InnerProductSpace
