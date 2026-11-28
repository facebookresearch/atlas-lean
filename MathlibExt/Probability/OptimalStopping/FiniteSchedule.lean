/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Process.Stopping

/-! # Stopping rules sampled on a finite nonuniform schedule -/

open MeasureTheory

namespace MetaMathlibExt

@[expose] public section

private def scheduleIndex (n k : ℕ) : Fin (n + 1) :=
  ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Sample `F` at a monotone finite schedule `e`, freezing the sampled filtration
at the terminal date `e (Fin.last n)`. At natural index `k` its σ-algebra is
that of `F` at date `e (min k n)`. -/
def finiteScheduleFiltration {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (F : Filtration ι m) {n : ℕ} (e : Fin (n + 1) → ι) (he : Monotone e) : Filtration ℕ m where
  seq k := F (e ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  mono' _ _ h := F.mono (he (Fin.le_iff_val_le_val.mpr (min_le_min_right n h)))
  le' k := F.le (e ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩)

/-- At an index on the schedule, the sampled filtration has exactly the σ-algebra
of the original filtration at the corresponding date. -/
theorem finiteScheduleFiltration_apply {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (F : Filtration ι m) {n : ℕ} (e : Fin (n + 1) → ι) (he : Monotone e) (j : Fin (n + 1)) :
    finiteScheduleFiltration F e he j.val = F (e j) := by
  change F (e (scheduleIndex n j.val)) = F (e j)
  rw [show scheduleIndex n j.val = j from
    Fin.ext (min_eq_left (Nat.le_of_lt_succ j.isLt))]

/-- The equivalence of bounded stopping indices for the sampled filtration and
schedule-valued stopping times for the original filtration. The forward map applies
the schedule pointwise, and the inverse recovers the unique index of each date. -/
noncomputable def finiteScheduleStoppingEquiv {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : Filtration ι m) {n : ℕ} (e : Fin (n + 1) → ι) (he : StrictMono e) :
    {i : Ω → Fin (n + 1) //
        IsStoppingTime (finiteScheduleFiltration F e he.monotone) (fun ω => (i ω).val)} ≃
      {τ : Ω → ι // IsStoppingTime F (fun ω => τ ω) ∧ ∀ ω, τ ω ∈ Set.range e} := by
  let G := finiteScheduleFiltration F e he.monotone
  let I := {i : Ω → Fin (n + 1) // IsStoppingTime G (fun ω => (i ω).val)}
  let S := {τ : Ω → ι // IsStoppingTime F (fun ω => τ ω) ∧ ∀ ω, τ ω ∈ Set.range e}
  let toTime (i : I) : S := ⟨fun ω => e (i.val ω), by
    refine ⟨?_, fun ω => ⟨i.val ω, rfl⟩⟩
    intro t
    change MeasurableSet[F t] {ω | (↑(e (i.val ω)) : WithTop ι) ≤ ↑t}
    have hset : {ω | (↑(e (i.val ω)) : WithTop ι) ≤ ↑t} =
        ⋃ j : {j : Fin (n + 1) // e j ≤ t}, {ω | (↑(i.val ω).val : WithTop ℕ) ≤ ↑j.val.val} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Nat.cast_withTop, WithTop.coe_le_coe]
      constructor
      · intro hω
        exact ⟨⟨i.val ω, hω⟩, le_rfl⟩
      · rintro ⟨j, hω⟩
        exact (he.monotone (Fin.le_iff_val_le_val.mpr hω)).trans j.property
    rw [hset]
    apply MeasurableSet.iUnion
    intro j
    have hj := i.property.measurableSet_le j.val.val
    change MeasurableSet[G j.val.val] {ω | (↑(i.val ω).val : WithTop ℕ) ≤ ↑j.val.val} at hj
    rw [show G j.val.val = F (e j.val) from
      finiteScheduleFiltration_apply F e he.monotone j.val] at hj
    exact F.mono j.property _ hj⟩
  let index (τ : S) (ω : Ω) : Fin (n + 1) := Classical.choose (τ.property.2 ω)
  have hindex (τ : S) (ω : Ω) : e (index τ ω) = τ.val ω :=
    Classical.choose_spec (τ.property.2 ω)
  let toIndex (τ : S) : I := ⟨index τ, by
    intro k
    change MeasurableSet[F (e (scheduleIndex n k))] {ω | (↑(index τ ω).val : WithTop ℕ) ≤ ↑k}
    have hset : {ω | (↑(index τ ω).val : WithTop ℕ) ≤ ↑k} =
        {ω | (↑(τ.val ω) : WithTop ι) ≤ ↑(e (scheduleIndex n k))} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Nat.cast_withTop, WithTop.coe_le_coe, ← hindex τ ω,
        he.le_iff_le, Fin.le_iff_val_le_val]
      change (index τ ω).val ≤ k ↔ (index τ ω).val ≤ min k n
      exact ⟨fun h => le_min h (Nat.le_of_lt_succ (index τ ω).isLt),
        fun h => h.trans (min_le_left _ _)⟩
    rw [hset]
    exact τ.property.1.measurableSet_le (e (scheduleIndex n k))⟩
  refine ⟨toTime, toIndex, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    funext ω
    exact he.injective (hindex (toTime i) ω)
  · intro τ
    apply Subtype.ext
    funext ω
    exact hindex τ ω

/- This is the defining forward equation of `finiteScheduleStoppingEquiv`. -/
theorem finiteScheduleStoppingEquiv_apply {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : Filtration ι m) {n : ℕ} (e : Fin (n + 1) → ι) (he : StrictMono e)
    (i : {i : Ω → Fin (n + 1) //
      IsStoppingTime (finiteScheduleFiltration F e he.monotone) (fun ω => (i ω).val)}) (ω : Ω) :
    (finiteScheduleStoppingEquiv F e he i).val ω = e (i.val ω) := rfl

/-- **Stopping rules sampled on a finite nonuniform schedule.** Let `F` be a filtration on a
linearly ordered time domain, and `e` a strictly increasing schedule indexed by `Fin (n + 1)`.
Sample the filtration at `e (min k n)` for each natural index `k`, freezing it after the terminal
date. Composing a bounded stopping index with `e` gives a bijection with the stopping times for
`F` whose values all belong to the schedule. Its inverse recovers the unique index at each sample
point. The correspondence preserves the value of any process pointwise, with no measure or
integrability assumptions. For a singleton schedule it corresponds to the constant terminal rule.
Use `finiteScheduleStoppingEquiv` for the equivalence itself. -/
theorem finite_schedule_stopping_times {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : Filtration ι m) {n : ℕ} (e : Fin (n + 1) → ι) (he : StrictMono e) :
    let I := {i : Ω → Fin (n + 1) //
      IsStoppingTime (finiteScheduleFiltration F e he.monotone) (fun ω => (i ω).val)}
    let S := {τ : Ω → ι // IsStoppingTime F (fun ω => τ ω) ∧ ∀ ω, τ ω ∈ Set.range e}
    ∃ E : I ≃ S, ∀ i ω, (E i).val ω = e (i.val ω) :=
  ⟨finiteScheduleStoppingEquiv F e he, finiteScheduleStoppingEquiv_apply F e he⟩

end

end MetaMathlibExt
