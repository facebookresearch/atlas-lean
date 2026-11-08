/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Countable Borel partition step: a measurable nearest-index map on a separable
pseudometric space. Used to replace arbitrary approximation maps by Borel ones.
-/

@[expose] public section

noncomputable section

theorem Metric.exists_measurable_index_dist_lt {B : Type*} [PseudoMetricSpace B]
    [TopologicalSpace.SeparableSpace B] [MeasurableSpace B] [BorelSpace B]
    (b₀ : B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (u : ℕ → B) (ι : B → ℕ), u 0 = b₀ ∧ Measurable ι ∧ ι b₀ = 0 ∧
      ∀ x, dist x (u (ι x)) < δ := by
  have : Nonempty B := ⟨b₀⟩
  classical
  let u : ℕ → B := fun n => match n with
    | 0 => b₀
    | Nat.succ k => TopologicalSpace.denseSeq B k
  have hu0 : u 0 = b₀ := rfl
  have huS : ∀ k, u (Nat.succ k) = TopologicalSpace.denseSeq B k := fun k => rfl
  have hdense := TopologicalSpace.denseRange_denseSeq B
  have hex : ∀ x, ∃ k, dist x (u k) < δ := by
    intro x
    obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hdense x δ hδ
    exact ⟨Nat.succ y, by rw [huS]; exact hy⟩
  have h0 : dist b₀ (u 0) < δ := by
    rw [hu0]
    exact Metric.mem_ball.mp (Metric.mem_ball_self hδ)
  refine ⟨u, fun x => Nat.find (hex x), hu0, ?_, ?_, ?_⟩
  · apply measurable_to_countable'
    intro k
    have hfib : (fun x => Nat.find (hex x)) ⁻¹' {k} =
        Metric.ball (u k) δ ∩ (⋃ j ∈ {i : ℕ | i < k}, Metric.ball (u j) δ)ᶜ := by
      apply funext
      intro x
      apply propext
      constructor
      · intro hx
        have hx' : Nat.find (hex x) = k := hx
        have hspec : dist x (u (Nat.find (hex x))) < δ := Nat.find_spec (hex x)
        rw [hx'] at hspec
        refine ⟨Metric.mem_ball.mpr hspec, ?_⟩
        change x ∉ (⋃ j ∈ {i : ℕ | i < k}, Metric.ball (u j) δ)
        intro hmem
        obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.mp hmem
        have hj' : j < k := hj
        have hjx : dist x (u j) < δ := Metric.mem_ball.mp hbj
        have hle := Nat.find_min' (hex x) hjx
        omega
      · intro hmem
        obtain ⟨hk_mem, hcompl⟩ := hmem
        have hk : dist x (u k) < δ := Metric.mem_ball.mp hk_mem
        have hle : Nat.find (hex x) ≤ k := Nat.find_min' (hex x) hk
        have hge : k ≤ Nat.find (hex x) := by
          by_contra hlt
          have hlt' : Nat.find (hex x) < k := by omega
          have hspec := Nat.find_spec (hex x)
          have hmem' : Nat.find (hex x) ∈ {i : ℕ | i < k} := hlt'
          have hwx : x ∈ ⋃ j ∈ {i : ℕ | i < k}, Metric.ball (u j) δ :=
            Set.mem_iUnion₂_of_mem hmem' (Metric.mem_ball.mpr hspec)
          exact hcompl hwx
        change Nat.find (hex x) = k
        omega
    rw [hfib]
    exact MeasurableSet.inter (IsOpen.measurableSet Metric.isOpen_ball)
      (MeasurableSet.compl (MeasurableSet.biUnion
        (Set.to_countable ({i : ℕ | i < k}))
        (fun j _ => IsOpen.measurableSet Metric.isOpen_ball)))
  · change Nat.find (hex b₀) = 0
    have hle : Nat.find (hex b₀) ≤ 0 := Nat.find_min' (hex b₀) h0
    omega
  · intro x
    exact Nat.find_spec (hex x)
