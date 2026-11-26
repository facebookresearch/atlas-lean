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

/-- **Stopping rules sampled on a finite nonuniform schedule.** Let `F` be a filtration on a
linearly ordered time domain, and `e` a strictly increasing schedule indexed by `Fin (n + 1)`.
Sample the filtration at `e (min k n)` for each natural index `k`, freezing it after the terminal
date. Composing a bounded stopping index with `e` gives a bijection with the stopping times for
`F` whose values all belong to the schedule. Its inverse recovers the unique index at each sample
point. The correspondence preserves the value of any process pointwise, with no measure or
integrability assumptions. For a singleton schedule it corresponds to the constant terminal rule. -/
theorem finite_schedule_stopping_times {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : Filtration ι m) {n : ℕ} (e : Fin (n + 1) → ι) (he : StrictMono e) :
    let clamp : ℕ → Fin (n + 1) := fun k => ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩
    let G : Filtration ℕ m :=
      ⟨fun k => F (e (clamp k)),
        fun _ _ h => F.mono (he.monotone (Fin.le_iff_val_le_val.mpr (min_le_min_right n h))),
        fun k => F.le (e (clamp k))⟩
    let I := {i : Ω → Fin (n + 1) // IsStoppingTime G (fun ω => (i ω).val)}
    let S := {τ : Ω → ι // IsStoppingTime F (fun ω => τ ω) ∧ ∀ ω, τ ω ∈ Set.range e}
    ∃ E : I ≃ S, ∀ i ω, (E i).val ω = e (i.val ω) := by
  intro clamp G I S
  have hclamp (j : Fin (n + 1)) : clamp j.val = j :=
    Fin.ext (min_eq_left (Nat.le_of_lt_succ j.isLt))
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
    change MeasurableSet[F (e (clamp j.val.val))]
      {ω | (↑(i.val ω).val : WithTop ℕ) ≤ ↑j.val.val} at hj
    rw [hclamp j.val] at hj
    exact F.mono j.property _ hj⟩
  let index (τ : S) (ω : Ω) : Fin (n + 1) := Classical.choose (τ.property.2 ω)
  have hindex (τ : S) (ω : Ω) : e (index τ ω) = τ.val ω :=
    Classical.choose_spec (τ.property.2 ω)
  let toIndex (τ : S) : I := ⟨index τ, by
    intro k
    change MeasurableSet[F (e (clamp k))] {ω | (↑(index τ ω).val : WithTop ℕ) ≤ ↑k}
    have hset : {ω | (↑(index τ ω).val : WithTop ℕ) ≤ ↑k} =
        {ω | (↑(τ.val ω) : WithTop ι) ≤ ↑(e (clamp k))} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Nat.cast_withTop, WithTop.coe_le_coe, ← hindex τ ω,
        he.le_iff_le, Fin.le_iff_val_le_val]
      change (index τ ω).val ≤ k ↔ (index τ ω).val ≤ min k n
      exact ⟨fun h => le_min h (Nat.le_of_lt_succ (index τ ω).isLt),
        fun h => h.trans (min_le_left _ _)⟩
    rw [hset]
    exact τ.property.1.measurableSet_le (e (clamp k))⟩
  refine ⟨⟨toTime, toIndex, ?_, ?_⟩, fun _ _ => rfl⟩
  · intro i
    apply Subtype.ext
    funext ω
    exact he.injective (hindex (toTime i) ω)
  · intro τ
    apply Subtype.ext
    funext ω
    exact hindex τ ω

end

end MetaMathlibExt
