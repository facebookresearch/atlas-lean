/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.MeasurableList
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-! # Raw prefix, stream law, and uniform box

This file lifts the sampling-based planners to i.i.d. random samples. The sample
space is streams `ω : ℕ → C` with the product law `ν^ℕ`. At step `N` a planner
reads the first `N` raw samples and applies its own collision filter, keeping a
list of random length at most `N`. The uniform box generalizes the sampling
domain of Karaman and Frazzoli ("Sampling-based algorithms for optimal motion
planning", International Journal of Robotics Research, 2011, Sections 2.1
and 3.1), the open unit cube with independent uniform samples.
-/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-- The first `N` raw samples `[ω 0, ..., ω (N - 1)]` of a sample stream, in order.
Nothing is discarded here: each planner applies its own collision test, so the
collision-free samples it keeps form a list of random length at most `N`. -/
def rawPrefix {α : Type*} (N : ℕ) (ω : ℕ → α) : List α :=
  List.ofFn fun i : Fin N => ω i

/-- The raw prefix has exactly `N` entries. -/
@[simp] theorem length_rawPrefix {α : Type*} (N : ℕ) (ω : ℕ → α) :
    (rawPrefix N ω).length = N := by
  simp [rawPrefix]

/-- The raw prefix map is measurable for the product σ-algebra on streams. -/
theorem measurable_rawPrefix {α : Type*} [MeasurableSpace α] (N : ℕ) :
    Measurable (rawPrefix (α := α) N) := by
  unfold rawPrefix
  exact (measurable_list_ofFn N).comp
    (Measurable.of_eval fun i => measurable_pi_apply _)

/-- The i.i.d. sample law on streams `ℕ → α`: the infinite product measure `ν^ℕ`. -/
noncomputable def streamLaw {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] : Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => ν

/-- The stream law is a probability measure. -/
instance isProbabilityMeasure_streamLaw {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (streamLaw ν) := by
  unfold streamLaw
  infer_instance

/-- Each coordinate sample `ω ↦ ω i` has law `ν`. -/
theorem streamLaw_map_eval {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (i : ℕ) : (streamLaw ν).map (fun ω => ω i) = ν := by
  unfold streamLaw
  exact Measure.infinitePi_map_eval _ i

/-- The coordinate samples are mutually independent under the stream law. -/
theorem iIndepFun_streamLaw {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] :
    ProbabilityTheory.iIndepFun (fun (i : ℕ) (ω : ℕ → α) => ω i) (streamLaw ν) := by
  unfold streamLaw
  have h := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => ν)
    (X := fun _ : ℕ => id (α := α)) (fun _ => measurable_id)
  simpa using h

/-- Equivalence between `Fin N` and the range-finset subtype, for reindexing. -/
private def finRangeEquiv (N : ℕ) : Fin N ≃ ↥(Finset.range N) where
  toFun i := ⟨i, Finset.mem_range.mpr i.isLt⟩
  invFun j := ⟨j, Finset.mem_range.mp j.2⟩
  left_inv i := by simp
  right_inv j := by simp

/-- The raw prefix of length `N` has the law of `N` independent `ν`-samples. -/
theorem streamLaw_map_rawPrefix {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (N : ℕ) :
    (streamLaw ν).map (rawPrefix N) =
      (Measure.pi fun _ : Fin N => ν).map (fun v : Fin N → α => List.ofFn v) := by
  have hRmeas : Measurable (fun ω : ℕ → α => fun i : Fin N => ω i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hOfFn : Measurable (fun v : Fin N → α => List.ofFn v) :=
    measurable_list_ofFn N
  have hraw : rawPrefix (α := α) N =
      (fun v : Fin N → α => List.ofFn v) ∘
        (fun ω : ℕ → α => fun i : Fin N => ω i) := rfl
  rw [hraw, ← Measure.map_map hOfFn hRmeas]
  have hRlaw : (streamLaw ν).map (fun ω : ℕ → α => fun i : Fin N => ω i) =
      Measure.pi fun _ : Fin N => ν := by
    unfold streamLaw
    have hR : (fun ω : ℕ → α => fun i : Fin N => ω i) =
        (MeasurableEquiv.piCongrLeft (fun _ : Fin N => α)
          (finRangeEquiv N).symm) ∘ (Finset.range N).restrict := rfl
    rw [hR, ← Measure.map_map]
    · have hrest := Measure.infinitePi_map_restrict (fun _ : ℕ => ν)
        (I := Finset.range N)
      rw [hrest]
      have hpi := Measure.pi_map_piCongrLeft (finRangeEquiv N).symm
        (fun _ : Fin N => ν)
      simpa using hpi
    · exact (MeasurableEquiv.piCongrLeft (fun _ : Fin N => α)
        (finRangeEquiv N).symm).measurable
    · exact Measurable.of_eval fun j => measurable_pi_apply _
  rw [hRlaw]

/-- Fixed-step output law: a measurable function of the raw prefix has, as its law,
the pushforward of the `N`-fold product law through the same function. -/
theorem streamLaw_map_comp_rawPrefix {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsProbabilityMeasure ν] {F : List α → β} (hF : Measurable F) (N : ℕ) :
    (streamLaw ν).map (fun ω => F (rawPrefix N ω)) =
      (Measure.pi fun _ : Fin N => ν).map (fun v : Fin N → α => F (List.ofFn v)) := by
  have hRaw : Measurable (rawPrefix (α := α) N) := measurable_rawPrefix N
  have hOfFn : Measurable (fun v : Fin N → α => List.ofFn v) :=
    measurable_list_ofFn N
  have h1 : (fun ω : ℕ → α => F (rawPrefix N ω)) = F ∘ rawPrefix (α := α) N :=
    rfl
  have h2 : (fun v : Fin N → α => F (List.ofFn v)) =
      F ∘ (fun v : Fin N → α => List.ofFn v) := rfl
  rw [h1, h2, ← Measure.map_map hF hRaw, ← Measure.map_map hF hOfFn]
  rw [streamLaw_map_rawPrefix]

/-- The number of collision-free samples among the first `N` raw samples: the random
length of the filtered list, which PRM* passes to its radius schedule. -/
def freeCount {C : Type} (O : Oracles C) (N : ℕ) (ω : ℕ → C) : ℕ :=
  ((rawPrefix N ω).filter O.free).length

/-- The filtered list is no longer than the raw prefix. -/
theorem freeCount_le {C : Type} (O : Oracles C) (N : ℕ) (ω : ℕ → C) :
    freeCount O N ω ≤ N := by
  unfold freeCount
  calc ((rawPrefix N ω).filter O.free).length
      ≤ (rawPrefix N ω).length := List.length_filter_le _ _
    _ = N := length_rawPrefix _ _

/-- The free-sample count is measurable when the collision test is. -/
theorem measurable_freeCount {C : Type} [MeasurableSpace C] (O : Oracles C)
    (hfree : Measurable O.free) (N : ℕ) : Measurable (freeCount O N) := by
  have hRaw : Measurable (rawPrefix (α := C) N) := measurable_rawPrefix N
  have hq : Measurable (fun p : Unit × C => O.free p.2) :=
    hfree.comp measurable_snd
  have hFilt : Measurable (fun p : Unit × List C => p.2.filter O.free) :=
    measurable_list_filter hq
  have hUnit : Measurable (fun l : List C => ((), l)) :=
    measurable_const.prodMk measurable_id
  have hSingle : Measurable (fun l : List C => l.filter O.free) :=
    hFilt.comp hUnit
  have hLen : Measurable (fun l : List C => (l.filter O.free).length) :=
    measurable_list_length.comp hSingle
  unfold freeCount
  exact hLen.comp hRaw

/-- The sampling domain of Karaman and Frazzoli (2011, Section 2.1),
generalized from the unit cube to a box: dimension `d ≥ 2` and the bounded
open box `∏ i, (lo i, hi i)` in `Fin d → ℝ` with `lo i < hi i`. -/
structure SourceBox (d : ℕ) where
  /-- The dimension is at least two. -/
  two_le : 2 ≤ d
  /-- Lower corner. -/
  lo : Fin d → ℝ
  /-- Upper corner. -/
  hi : Fin d → ℝ
  /-- Each side is nondegenerate. -/
  lo_lt_hi : ∀ i, lo i < hi i

namespace SourceBox

/-- The open box `∏ i, (lo i, hi i)`. -/
def carrier {d : ℕ} (B : SourceBox d) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Ioo (B.lo i) (B.hi i)

/-- The uniform law on the box: Lebesgue measure restricted to the box and
normalized, `A ↦ volume (A ∩ box) / volume box`. -/
noncomputable def law {d : ℕ} (B : SourceBox d) : Measure (Fin d → ℝ) :=
  ProbabilityTheory.cond volume B.carrier

/-- The box is measurable. -/
theorem measurableSet_carrier {d : ℕ} (B : SourceBox d) : MeasurableSet B.carrier := by
  unfold carrier
  exact MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_Ioo

/-- The box has positive volume. -/
theorem volume_carrier_pos {d : ℕ} (B : SourceBox d) : 0 < volume B.carrier := by
  unfold carrier
  rw [Real.volume_pi_Ioo, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  rw [ne_eq, ENNReal.ofReal_eq_zero]
  have h := B.lo_lt_hi i
  have hpos : 0 < B.hi i - B.lo i := by linarith
  linarith

/-- The box has finite volume. -/
theorem volume_carrier_lt_top {d : ℕ} (B : SourceBox d) : volume B.carrier < ⊤ := by
  unfold carrier
  rw [Real.volume_pi_Ioo]
  have h : ∀ s : Finset (Fin d),
      (∏ i ∈ s, ENNReal.ofReal (B.hi i - B.lo i)) < ⊤ := by
    intro s
    induction s using Finset.induction with
    | empty => simp [ENNReal.one_lt_top]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ih
  have htop := h Finset.univ
  simpa using htop

/-- The uniform law on the box is a probability measure. -/
instance isProbabilityMeasure_law {d : ℕ} (B : SourceBox d) : IsProbabilityMeasure B.law := by
  unfold law
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (ne_of_gt (volume_carrier_pos B)) (ne_of_lt (volume_carrier_lt_top B))

/-- The uniform law is normalized restricted Lebesgue measure. -/
theorem law_apply {d : ℕ} (B : SourceBox d) (A : Set (Fin d → ℝ)) :
    B.law A = volume (A ∩ B.carrier) / volume B.carrier := by
  unfold law
  rw [ProbabilityTheory.cond_apply (measurableSet_carrier B)]
  rw [Set.inter_comm B.carrier A, div_eq_mul_inv, mul_comm]

/-- The uniform law is supported on the box. -/
theorem law_compl_carrier {d : ℕ} (B : SourceBox d) : B.law B.carrierᶜ = 0 := by
  rw [law_apply, Set.compl_inter_self, measure_empty]
  exact ENNReal.zero_div

/-- The law is uniform on the box in Mathlib's sense. -/
theorem isUniform_law {d : ℕ} (B : SourceBox d) :
    MeasureTheory.pdf.IsUniform id B.carrier B.law volume := by
  unfold MeasureTheory.pdf.IsUniform
  refine ⟨?_, ?_⟩
  · exact measurable_id.aemeasurable
  · exact Measure.map_id

/-- Under the stream law of the box, every raw sample is uniform on the box. -/
theorem isUniform_sample {d : ℕ} (B : SourceBox d) (i : ℕ) :
    MeasureTheory.pdf.IsUniform (fun ω : ℕ → (Fin d → ℝ) => ω i) B.carrier
      (streamLaw B.law) volume := by
  unfold MeasureTheory.pdf.IsUniform
  refine ⟨?_, ?_⟩
  · exact (measurable_pi_apply i).aemeasurable
  · exact streamLaw_map_eval B.law i

/-- The unit cube `(0, 1)^d`, the configuration space of Karaman and Frazzoli
(2011, Section 2.1). -/
def unitCube (d : ℕ) (hd : 2 ≤ d) : SourceBox d :=
  ⟨hd, 0, 1, fun _ => zero_lt_one⟩

/-- The unit cube is the box `∏ i, (0, 1)`. -/
theorem carrier_unitCube (d : ℕ) (hd : 2 ≤ d) :
    (unitCube d hd).carrier = Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1 := by
  simp [unitCube, carrier]

end SourceBox

end Cslib.Planning.MotionPlanning.SamplingPlanners
