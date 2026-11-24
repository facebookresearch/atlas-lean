/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Data.Fintype.Pi

/-!
# Kolmogorov–Sinai entropy

Sinai's definition of the entropy of a measure-preserving transformation of a probability space
`(α, μ)`. A finite partition `ξ = {C₁, …, C_r}` of the phase space has Shannon entropy
`H(ξ) = -∑ μ(Cᵢ) log μ(Cᵢ)`; the entropy of `T` relative to `ξ` is the growth rate
`h(T, ξ) = lim (1/n) H(ξ ∨ T⁻¹ξ ∨ ⋯ ∨ T^{-(n-1)}ξ)`, and the Kolmogorov–Sinai entropy is
`h(T) = sup_ξ h(T, ξ)` over all finite measurable partitions.

The entropies take an instance `IsProbabilityMeasure μ`, as in the sources: `H(ξ)` is the
Shannon entropy of the probability vector `(μ(Cᵢ))ᵢ`. For an arbitrary measure the formula is no
entropy: the zero measure would give every map entropy `0`, and an atom of infinite measure
would contribute `negMulLog (∞.toReal) = 0`. Measurable partitions (`IsMeasurablePartition`) and
isomorphism modulo null sets (`IsIsomorphicMod0`) make sense for every measure and take no such
instance.

Partitions are indexed families `ξ : ι → Set α` over a finite type, and the refinement
`ξ ∨ T⁻¹ξ ∨ ⋯ ∨ T^{-(n-1)}ξ` is indexed by words `w : Fin n → ι`, so no atoms are merged and
empty atoms contribute `negMulLog 0 = 0`. The entropy takes values in `ℝ≥0∞`: `h(T, ξ)` is a
`limsup` (equal to the limit, which exists by subadditivity for measure-preserving `T`) and
`h(T)` may be infinite, with no junk value.

## Main results

* `ksEntropy`: the Kolmogorov–Sinai entropy (Ya. G. Sinai, *Kolmogorov–Sinai entropy*,
  Scholarpedia 4(3):2034, Definition 1).
* `ksEntropy_le_of_factor`: a factor has at most the entropy of the system.
* `ksEntropy_eq_of_isomorphic`: invariance under conjugacy by a measure-preserving measurable
  equivalence.
* `IsIsomorphicMod0`, `ksEntropy_eq_of_isIsomorphicMod0`: Kolmogorov–Sinai entropy is an
  invariant of measure-theoretic isomorphism modulo null sets.
* `ksEntropy_id`: the identity has zero entropy.

## References

* Ya. G. Sinai, *On the notion of entropy of a dynamical system*, Dokl. Akad. Nauk SSSR 124
  (1959), 768–771.
* Ya. G. Sinai, *Kolmogorov–Sinai entropy*, Scholarpedia 4(3):2034 (2009),
  http://www.scholarpedia.org/article/Kolmogorov-Sinai_entropy
* O. Sarig, *Lecture Notes on Ergodic Theory*, §4.3,
  https://www.weizmann.ac.il/math/sarigo/sites/math.sarigo/files/uploads/ergodicnotes.pdf
-/

@[expose] public section

namespace MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Finite measurable partition modulo null sets.** A family `ξ : ι → Set α` of measurable
sets is a measurable partition of `(α, μ)` if its members are pairwise disjoint up to
`μ`-null sets and cover `α` up to a `μ`-null set. -/
structure IsMeasurablePartition (μ : Measure α) {ι : Type*} (ξ : ι → Set α) : Prop where
  /-- Every atom is measurable. -/
  measurableSet : ∀ i, MeasurableSet (ξ i)
  /-- Distinct atoms are almost disjoint. -/
  aedisjoint : Pairwise fun i j => AEDisjoint μ (ξ i) (ξ j)
  /-- The atoms cover almost all of `α`. -/
  measure_compl_iUnion : μ (⋃ i, ξ i)ᶜ = 0

/-- **Entropy of a finite partition.** For a probability measure `μ`, the Shannon entropy
`H_μ(ξ) = -∑ᵢ μ(Cᵢ) log μ(Cᵢ)` of a partition `ξ = (Cᵢ)` indexed by a finite type, with the
convention `0 log 0 = 0` (`Real.negMulLog`) (Sinai, Scholarpedia *Kolmogorov–Sinai entropy*;
O. Sarig, *Lecture Notes on Ergodic Theory*, Definition 4.1). The logarithm is natural, as in
Sinai's article; Sarig uses `log₂`, which divides every entropy by `log 2`. -/
noncomputable def partitionEntropy (μ : Measure α) [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] (ξ : ι → Set α) : ℝ :=
  ∑ i, Real.negMulLog (μ (ξ i)).toReal

/-- **Dynamical refinement of a partition.** The partition
`ξ ∨ T⁻¹ξ ∨ ⋯ ∨ T^{-(n-1)}ξ`, indexed by words `w : Fin n → ι`: the atom of `w` is the set of
points `x` with `T^[k] x ∈ ξ (w k)` for every `k < n`, i.e. the points whose `ξ`-itinerary
begins with `w`. -/
def iterateJoin (T : α → α) {ι : Type*} (ξ : ι → Set α) (n : ℕ) : (Fin n → ι) → Set α :=
  fun w => ⋂ k : Fin n, T^[(k : ℕ)] ⁻¹' ξ (w k)

/-- **Entropy of a transformation relative to a partition.** For a probability measure `μ`,
`h_μ(T, ξ) = limsup_{n → ∞} (1/n) H_μ(ξ ∨ T⁻¹ξ ∨ ⋯ ∨ T^{-(n-1)}ξ)`, in `ℝ≥0∞`. For a
measure-preserving `T` the sequence converges by subadditivity, so this is the limit of Sinai,
Scholarpedia *Kolmogorov–Sinai entropy*, and of O. Sarig, *Lecture Notes on Ergodic Theory*,
Definition 4.3. -/
noncomputable def entropyRel (μ : Measure α) [IsProbabilityMeasure μ] (T : α → α) {ι : Type*}
    [Fintype ι] (ξ : ι → Set α) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal (partitionEntropy μ (iterateJoin T ξ n) / n)) atTop

/-- **Kolmogorov–Sinai entropy.** The entropy of a dynamical system `(α, μ, T)` on a
probability space is `h_μ(T) = sup_ξ h_μ(T, ξ)`, the supremum over all finite measurable
partitions `ξ` (Ya. G. Sinai, *Kolmogorov–Sinai entropy*, Scholarpedia 4(3):2034, Definition 1;
introduced in Sinai, Dokl. Akad. Nauk SSSR 124 (1959)). Partitions are indexed by `Fin r`,
`r ∈ ℕ`; the value lies in `ℝ≥0∞`. -/
noncomputable def ksEntropy (μ : Measure α) [IsProbabilityMeasure μ] (T : α → α) : ℝ≥0∞ :=
  ⨆ (r : ℕ) (ξ : Fin r → Set α) (_ : IsMeasurablePartition μ ξ), entropyRel μ T ξ

/-- **Relative entropy is bounded by the Kolmogorov–Sinai entropy.** For every finite
measurable partition `ξ` indexed by `Fin r`, `h_μ(T, ξ) ≤ h_μ(T)`. -/
theorem entropyRel_le_ksEntropy {μ : Measure α} [IsProbabilityMeasure μ] (T : α → α) {r : ℕ}
    {ξ : Fin r → Set α} (hξ : IsMeasurablePartition μ ξ) : entropyRel μ T ξ ≤ ksEntropy μ T :=
  le_iSup_of_le r <| le_iSup_of_le ξ <| le_iSup_of_le hξ le_rfl

/-- **Entropy of a partition is nonnegative** for a probability measure, since every atom has
measure in `[0, 1]` and `-t log t ≥ 0` there. -/
theorem partitionEntropy_nonneg (μ : Measure α) [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] (ξ : ι → Set α) : 0 ≤ partitionEntropy μ ξ :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg ENNReal.toReal_nonneg <| by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := ξ i))

/-- **Atoms of the dynamical refinement are measurable.** If `T` is measurable and every atom of
`ξ` is measurable, then every atom of `ξ ∨ T⁻¹ξ ∨ ⋯ ∨ T^{-(n-1)}ξ` is measurable. -/
theorem measurableSet_iterateJoin {T : α → α} (hT : Measurable T) {ι : Type*}
    {ξ : ι → Set α} (hξ : ∀ i, MeasurableSet (ξ i)) (n : ℕ) (w : Fin n → ι) :
    MeasurableSet (iterateJoin T ξ n w) :=
  MeasurableSet.iInter fun k => (hξ (w k)).preimage (hT.iterate k)

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- **Dynamical refinement commutes with pullback along a factor map.** If `π ∘ T = S ∘ π`, the
atom of the word `w` in the refinement of the pulled-back partition `π⁻¹η` under `T` is the
preimage under `π` of the atom of `w` in the refinement of `η` under `S`. -/
theorem iterateJoin_preimage {T : α → α} {S : β → β} {π : α → β}
    (hπ : Function.Semiconj π T S) {ι : Type*} (η : ι → Set β) (n : ℕ) (w : Fin n → ι) :
    iterateJoin T (fun i => π ⁻¹' η i) n w = π ⁻¹' iterateJoin S η n w := by
  simp only [iterateJoin, Set.preimage_iInter, ← Set.preimage_comp]
  refine Set.iInter_congr fun k => ?_
  rw [(hπ.iterate_right k).comp_eq]

/-- **Pullback of a measurable partition.** The preimages `π⁻¹ ηᵢ` of the atoms of a measurable
partition `η` of `(β, ν)` under a measure-preserving map `π : (α, μ) → (β, ν)` form a measurable
partition of `(α, μ)`. -/
theorem IsMeasurablePartition.preimage {μ : Measure α} {ν : Measure β} {π : α → β}
    (hπ : MeasurePreserving π μ ν) {ι : Type*} [Countable ι] {η : ι → Set β}
    (hη : IsMeasurablePartition ν η) : IsMeasurablePartition μ (fun i => π ⁻¹' η i) where
  measurableSet i := (hη.measurableSet i).preimage hπ.measurable
  aedisjoint i j hij := by
    change μ (π ⁻¹' η i ∩ π ⁻¹' η j) = 0
    rw [← Set.preimage_inter,
      hπ.measure_preimage ((hη.measurableSet i).inter (hη.measurableSet j)).nullMeasurableSet]
    exact hη.aedisjoint hij
  measure_compl_iUnion := by
    rw [← Set.preimage_iUnion, ← Set.preimage_compl,
      hπ.measure_preimage (MeasurableSet.iUnion hη.measurableSet).compl.nullMeasurableSet]
    exact hη.measure_compl_iUnion

/-- **Relative entropy of a pulled-back partition.** If `π : (α, μ, T) → (β, ν, S)` is a
measure-preserving map of probability spaces with `π ∘ T = S ∘ π`, then
`h_μ(T, π⁻¹η) = h_ν(S, η)` for every finite measurable partition `η` of `β`: the two refinements
have atoms of equal measure. -/
theorem entropyRel_preimage {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : α → α} {S : β → β}
    {π : α → β} (hπ : MeasurePreserving π μ ν) (hS : Measurable S)
    (hconj : Function.Semiconj π T S) {ι : Type*} [Fintype ι] {η : ι → Set β}
    (hη : ∀ i, MeasurableSet (η i)) :
    entropyRel μ T (fun i => π ⁻¹' η i) = entropyRel ν S η := by
  have h : ∀ (n : ℕ) (w : Fin n → ι),
      μ (iterateJoin T (fun i => π ⁻¹' η i) n w) = ν (iterateJoin S η n w) := fun n w => by
    rw [iterateJoin_preimage hconj,
      hπ.measure_preimage (measurableSet_iterateJoin hS hη n w).nullMeasurableSet]
  simp only [entropyRel, partitionEntropy, h]

/-- **Entropy does not increase under factors.** If `π` is a measure-preserving map from
`(α, μ, T)` onto `(β, ν, S)`, both on probability spaces, with `π ∘ T = S ∘ π`, then
`h_ν(S) ≤ h_μ(T)`: every finite partition of the factor pulls back to a partition of the system
with the same relative entropy (cf. O. Sarig, *Lecture Notes on Ergodic Theory*, §4.3). -/
theorem ksEntropy_le_of_factor {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : α → α} {S : β → β}
    {π : α → β} (hπ : MeasurePreserving π μ ν) (hS : Measurable S)
    (hconj : Function.Semiconj π T S) : ksEntropy ν S ≤ ksEntropy μ T := by
  refine iSup_le fun r => iSup_le fun η => iSup_le fun hη => ?_
  rw [← entropyRel_preimage hπ hS hconj hη.measurableSet]
  exact entropyRel_le_ksEntropy T (hη.preimage hπ)

/-- **Entropy is invariant under conjugacy by a measure-preserving measurable equivalence.** If
a measure-preserving measurable equivalence `e : α ≃ᵐ β` of probability spaces conjugates `T` to
`S` everywhere (`e ∘ T = S ∘ e`), then `h_μ(T) = h_ν(S)`. This everywhere version needs no
measure preservation of `T` or `S`; measure-theoretic isomorphism modulo null sets, the notion
in Sinai's remark that entropy is a metric invariant, is `ksEntropy_eq_of_isIsomorphicMod0`. -/
theorem ksEntropy_eq_of_isomorphic {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : α → α} {S : β → β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (hT : Measurable T) (hS : Measurable S) (hconj : Function.Semiconj e T S) :
    ksEntropy μ T = ksEntropy ν S := by
  refine le_antisymm ?_ (ksEntropy_le_of_factor he hS hconj)
  have hconj' : Function.Semiconj e.symm S T := fun y => by
    apply e.injective
    rw [hconj (e.symm y), e.apply_symm_apply, e.apply_symm_apply]
  exact ksEntropy_le_of_factor (he.symm e) hT hconj'

/-- **Isomorphism modulo null sets.** Two dynamical systems `(α, μ, T)` and `(β, ν, S)` are
isomorphic modulo null sets if there are measure-preserving maps `π : α → β` and `ρ : β → α`
that are inverse to each other almost everywhere (`ρ ∘ π = id` `μ`-a.e., `π ∘ ρ = id` `ν`-a.e.)
and intertwine the dynamics almost everywhere (`π ∘ T = S ∘ π` `μ`-a.e.,
`ρ ∘ S = T ∘ ρ` `ν`-a.e.). This encodes measure-theoretic isomorphism (O. Sarig, *Lecture Notes
on Ergodic Theory*, Definition 1.3: a measure-preserving bijection between invariant sets of
full measure that intertwines the maps) by maps defined almost everywhere: on nonempty spaces an
isomorphism in Sarig's sense, extended by a constant off its domain, gives such `π` and `ρ`.
Fixed points and other null sets play no role, unlike for an everywhere conjugacy. -/
def IsIsomorphicMod0 (μ : Measure α) (T : α → α) (ν : Measure β) (S : β → β) : Prop :=
  ∃ (π : α → β) (ρ : β → α), MeasurePreserving π μ ν ∧ MeasurePreserving ρ ν μ ∧
    ρ ∘ π =ᵐ[μ] id ∧ π ∘ ρ =ᵐ[ν] id ∧ π ∘ T =ᵐ[μ] S ∘ π ∧ ρ ∘ S =ᵐ[ν] T ∘ ρ

/-- **A conjugacy by a measure-preserving measurable equivalence is an isomorphism modulo null
sets.** -/
theorem isIsomorphicMod0_of_measurableEquiv {μ : Measure α} {ν : Measure β} {T : α → α}
    {S : β → β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (hconj : Function.Semiconj e T S) :
    IsIsomorphicMod0 μ T ν S := by
  have hconj' : Function.Semiconj e.symm S T := fun y => by
    apply e.injective
    rw [hconj (e.symm y), e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨e, e.symm, he, he.symm e, ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => e.symm_apply_apply x
  · exact Filter.Eventually.of_forall fun y => e.apply_symm_apply y
  · exact Filter.Eventually.of_forall fun x => hconj x
  · exact Filter.Eventually.of_forall fun y => hconj' y

omit [MeasurableSpace β] in
/-- **Almost-everywhere semiconjugacy passes to iterates.** If `T` is quasi-measure-preserving
and `π ∘ T = S ∘ π` almost everywhere, then `π ∘ T^[k] = S^[k] ∘ π` almost everywhere. -/
theorem iterate_comp_ae_eq {μ : Measure α} {T : α → α} {S : β → β} {π : α → β}
    (hT : QuasiMeasurePreserving T μ μ) (hπ : π ∘ T =ᵐ[μ] S ∘ π) (k : ℕ) :
    π ∘ T^[k] =ᵐ[μ] S^[k] ∘ π := by
  induction k with
  | zero => exact Filter.EventuallyEq.rfl
  | succ k ih =>
    have h1 : (π ∘ T^[k]) ∘ T =ᵐ[μ] (S^[k] ∘ π) ∘ T := hT.ae_eq_comp ih
    filter_upwards [h1, hπ] with x hx1 hx2
    simp only [Function.comp_apply] at hx1 hx2 ⊢
    rw [Function.iterate_succ_apply, hx1, hx2, ← Function.iterate_succ_apply]

omit [MeasurableSpace β] in
/-- **Dynamical refinement commutes with pullback, almost everywhere.** If `T` is
quasi-measure-preserving and `π ∘ T = S ∘ π` almost everywhere, then each atom of the
refinement of `π⁻¹η` under `T` agrees almost everywhere with the preimage under `π` of the
corresponding atom of the refinement of `η` under `S`. -/
theorem iterateJoin_preimage_ae_eq {μ : Measure α} {T : α → α} {S : β → β} {π : α → β}
    (hT : QuasiMeasurePreserving T μ μ) (hπ : π ∘ T =ᵐ[μ] S ∘ π) {ι : Type*}
    (η : ι → Set β) (n : ℕ) (w : Fin n → ι) :
    iterateJoin T (fun i => π ⁻¹' η i) n w =ᵐ[μ] π ⁻¹' iterateJoin S η n w := by
  have h : ∀ᵐ x ∂μ, ∀ k : Fin n, π (T^[(k : ℕ)] x) = S^[(k : ℕ)] (π x) :=
    ae_all_iff.2 fun k => (iterate_comp_ae_eq hT hπ k).mono fun x hx => hx
  filter_upwards [h] with x hx
  simp only [iterateJoin, Set.mem_iInter, Set.mem_preimage, hx]

/-- **Relative entropy of a pulled-back partition under an a.e. factor map.** If
`π : (α, μ) → (β, ν)` is a measure-preserving map of probability spaces, `T` is
quasi-measure-preserving, `S` is measurable and `π ∘ T = S ∘ π` almost everywhere, then
`h_μ(T, π⁻¹η) = h_ν(S, η)` for every finite measurable partition `η` of `β`. -/
theorem entropyRel_preimage_of_ae {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : α → α} {S : β → β} {π : α → β} (hπ : MeasurePreserving π μ ν)
    (hT : QuasiMeasurePreserving T μ μ) (hS : Measurable S) (hconj : π ∘ T =ᵐ[μ] S ∘ π)
    {ι : Type*} [Fintype ι] {η : ι → Set β} (hη : ∀ i, MeasurableSet (η i)) :
    entropyRel μ T (fun i => π ⁻¹' η i) = entropyRel ν S η := by
  have h : ∀ (n : ℕ) (w : Fin n → ι),
      μ (iterateJoin T (fun i => π ⁻¹' η i) n w) = ν (iterateJoin S η n w) := fun n w => by
    rw [measure_congr (iterateJoin_preimage_ae_eq hT hconj η n w),
      hπ.measure_preimage (measurableSet_iterateJoin hS hη n w).nullMeasurableSet]
  simp only [entropyRel, partitionEntropy, h]

/-- **Entropy does not increase under factors (almost-everywhere form).** If
`π : (α, μ) → (β, ν)` is a measure-preserving map of probability spaces, `T` is
quasi-measure-preserving, `S` is measurable and `π ∘ T = S ∘ π` almost everywhere, then
`h_ν(S) ≤ h_μ(T)`. -/
theorem ksEntropy_le_of_factor_ae {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {T : α → α} {S : β → β} {π : α → β} (hπ : MeasurePreserving π μ ν)
    (hT : QuasiMeasurePreserving T μ μ) (hS : Measurable S) (hconj : π ∘ T =ᵐ[μ] S ∘ π) :
    ksEntropy ν S ≤ ksEntropy μ T := by
  refine iSup_le fun r => iSup_le fun η => iSup_le fun hη => ?_
  rw [← entropyRel_preimage_of_ae hπ hT hS hconj hη.measurableSet]
  exact entropyRel_le_ksEntropy T (hη.preimage hπ)

/-- **Entropy is an invariant of isomorphism modulo null sets.** If two measure-preserving
systems `(α, μ, T)` and `(β, ν, S)` on probability spaces are isomorphic modulo null sets
(`IsIsomorphicMod0`), then `h_μ(T) = h_ν(S)`: "It is clear from the definition that this
entropy is a metric invariant of dynamical system" (Ya. G. Sinai, *Kolmogorov–Sinai entropy*,
Scholarpedia 4(3):2034, after Definition 1), with isomorphism as in O. Sarig, *Lecture Notes on
Ergodic Theory*, Definition 1.3. -/
theorem ksEntropy_eq_of_isIsomorphicMod0 {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {T : α → α} {S : β → β}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (h : IsIsomorphicMod0 μ T ν S) : ksEntropy μ T = ksEntropy ν S := by
  obtain ⟨π, ρ, hπ, hρ, -, -, hπT, hρS⟩ := h
  exact le_antisymm (ksEntropy_le_of_factor_ae hρ hS.quasiMeasurePreserving hT.measurable hρS)
    (ksEntropy_le_of_factor_ae hπ hT.quasiMeasurePreserving hS.measurable hπT)

/-- **Refinements under the identity.** For the identity map of a probability space and
`n ≥ 1`, the dynamical refinement `ξ ∨ ξ ∨ ⋯ ∨ ξ` of a measurable partition has the same
entropy as `ξ`: the atom of a constant word `(i, …, i)` is `ξ i`, and the atom of a non-constant
word is contained in the intersection of two distinct atoms, a null set. -/
theorem partitionEntropy_iterateJoin_id {μ : Measure α} [IsProbabilityMeasure μ] {r : ℕ}
    {ξ : Fin r → Set α} (hξ : IsMeasurablePartition μ ξ) {n : ℕ} (hn : n ≠ 0) :
    partitionEntropy μ (iterateJoin id ξ n) = partitionEntropy μ ξ := by
  classical
  have hconst : Function.Injective (fun (i : Fin r) (_ : Fin n) => i) := fun i j h => by
    simpa using congrFun h ⟨0, Nat.pos_of_ne_zero hn⟩
  have hzero : ∀ w : Fin n → Fin r, w ∉ Finset.univ.image (fun (i : Fin r) (_ : Fin n) => i) →
      Real.negMulLog (μ (iterateJoin id ξ n w)).toReal = 0 := by
    intro w hw
    have hnc : ∃ k₁ k₂, w k₁ ≠ w k₂ := by
      by_contra h
      push Not at h
      exact hw (Finset.mem_image.2 ⟨w ⟨0, Nat.pos_of_ne_zero hn⟩, Finset.mem_univ _,
        funext fun k => h _ _⟩)
    obtain ⟨k₁, k₂, hk⟩ := hnc
    have hsub : iterateJoin id ξ n w ⊆ ξ (w k₁) ∩ ξ (w k₂) := fun x hx => by
      simp only [iterateJoin, Function.iterate_id, Set.preimage_id, Set.mem_iInter] at hx
      exact ⟨hx k₁, hx k₂⟩
    have h0 : μ (iterateJoin id ξ n w) = 0 := measure_mono_null hsub (hξ.aedisjoint hk)
    simp [h0]
  unfold partitionEntropy
  rw [← Finset.sum_subset (Finset.subset_univ _) fun w _ hw => hzero w hw,
    Finset.sum_image fun i _ j _ h => hconst h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : iterateJoin id ξ n (fun _ => i) = ξ i := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simp only [iterateJoin, Function.iterate_id, Set.preimage_id]
    exact Set.iInter_const _
  rw [this]

/-- **The identity has zero entropy.** For every probability measure `μ`, `h_μ(id) = 0`: the
dynamical refinements of a finite partition under the identity have bounded entropy, so their
entropy per step tends to `0`. -/
theorem ksEntropy_id (μ : Measure α) [IsProbabilityMeasure μ] : ksEntropy μ id = 0 := by
  refine le_antisymm (iSup_le fun r => iSup_le fun ξ => iSup_le fun hξ => ?_) bot_le
  refine le_of_eq ?_
  unfold entropyRel
  refine Tendsto.limsup_eq ?_
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (partitionEntropy μ ξ / n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat _)
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [partitionEntropy_iterateJoin_id hξ hn]

end MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy
