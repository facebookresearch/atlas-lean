/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFiniteCutoff
import Mathlib.Combinatorics.SimpleGraph.Metric



namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

noncomputable def isingFiniteGraphBoundaryVertices
    {V : Type*} [Fintype V] (boundary : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter boundary

theorem isingFiniteGraphBoundaryVertices_nonempty
    {V : Type*} [Fintype V] (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) :
    (isingFiniteGraphBoundaryVertices boundary).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := hboundary
  exact ⟨x, by simp [isingFiniteGraphBoundaryVertices, hx]⟩


noncomputable def isingFiniteGraphDistanceToBoundary
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x : V) : Nat := by
  classical
  let B := isingFiniteGraphBoundaryVertices boundary
  have hB : B.Nonempty :=
    isingFiniteGraphBoundaryVertices_nonempty boundary hboundary
  exact (B.image (G.dist x)).min' (hB.image _)

theorem isingFiniteGraphDistanceToBoundary_le_dist
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x b : V) (hb : boundary b) :
    isingFiniteGraphDistanceToBoundary G boundary hboundary x ≤ G.dist x b := by
  classical
  unfold isingFiniteGraphDistanceToBoundary
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  exact ⟨b, by simp [isingFiniteGraphBoundaryVertices, hb], rfl⟩

theorem isingFiniteGraphDistanceToBoundary_eq_zero
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x : V) (hx : boundary x) :
    isingFiniteGraphDistanceToBoundary G boundary hboundary x = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using isingFiniteGraphDistanceToBoundary_le_dist
    G boundary hboundary x x hx

theorem isingFiniteGraphDistanceToBoundary_exists_eq_dist
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (x : V) :
    ∃ b, boundary b ∧
      isingFiniteGraphDistanceToBoundary G boundary hboundary x = G.dist x b := by
  classical
  let B := isingFiniteGraphBoundaryVertices boundary
  have hB : B.Nonempty :=
    isingFiniteGraphBoundaryVertices_nonempty boundary hboundary
  have hmem := Finset.min'_mem (B.image (G.dist x)) (hB.image _)
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hmem
  refine ⟨b, ?_, ?_⟩
  · simpa [B, isingFiniteGraphBoundaryVertices] using hb
  · unfold isingFiniteGraphDistanceToBoundary
    exact heq.symm



theorem isingFiniteGraphDistanceToBoundary_adj
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) {x y : V} (hxy : G.Adj x y) :
    isingFiniteGraphDistanceToBoundary G boundary hboundary y ≤
        isingFiniteGraphDistanceToBoundary G boundary hboundary x + 1 ∧
      isingFiniteGraphDistanceToBoundary G boundary hboundary x ≤
        isingFiniteGraphDistanceToBoundary G boundary hboundary y + 1 := by
  constructor
  · obtain ⟨b, hb, hxb⟩ :=
      isingFiniteGraphDistanceToBoundary_exists_eq_dist
        G boundary hboundary x
    have hstep := hxy.diff_dist_adj (u := b)
    have hyb : G.dist y b ≤ G.dist x b + 1 := by
      rw [G.dist_comm (u := y) (v := b), G.dist_comm (u := x) (v := b)]
      rcases hstep with hstep | hstep | hstep <;> omega
    exact (isingFiniteGraphDistanceToBoundary_le_dist
      G boundary hboundary y b hb).trans (hxb.symm ▸ hyb)
  · obtain ⟨b, hb, hyb⟩ :=
      isingFiniteGraphDistanceToBoundary_exists_eq_dist
        G boundary hboundary y
    have hstep := hxy.symm.diff_dist_adj (u := b)
    have hxb : G.dist x b ≤ G.dist y b + 1 := by
      rw [G.dist_comm (u := x) (v := b), G.dist_comm (u := y) (v := b)]
      rcases hstep with hstep | hstep | hstep <;> omega
    exact (isingFiniteGraphDistanceToBoundary_le_dist
      G boundary hboundary x b hb).trans (hyb.symm ▸ hxb)



noncomputable def isingFiniteGraphBoundaryTentCutoff
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) (x : V) : Real :=
  min 1 ((isingFiniteGraphDistanceToBoundary G boundary hboundary x : Real) /
    (r : Real))

theorem isingFiniteGraphBoundaryTentCutoff_support
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) :
    ∀ x, isingFiniteGraphBoundaryTentCutoff G boundary hboundary r x ≠ 0 →
      ¬ boundary x := by
  intro x hx hxb
  have hzero := isingFiniteGraphDistanceToBoundary_eq_zero
    G boundary hboundary x hxb
  simp [isingFiniteGraphBoundaryTentCutoff, hzero] at hx

theorem isingFiniteGraphBoundaryTentCutoff_lipschitz
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) (hr : 0 < r)
    (d : G.Dart) :
    |isingFiniteGraphBoundaryTentCutoff G boundary hboundary r d.snd -
      isingFiniteGraphBoundaryTentCutoff G boundary hboundary r d.fst| ≤
        1 / (r : Real) := by
  let rho := isingFiniteGraphDistanceToBoundary G boundary hboundary
  have hdistNat := isingFiniteGraphDistanceToBoundary_adj
    G boundary hboundary d.2
  have hdist : |(rho d.snd : Real) - (rho d.fst : Real)| ≤ 1 := by
    have hforward : (rho d.snd : Real) ≤ (rho d.fst : Real) + 1 := by
      exact_mod_cast hdistNat.1
    have hbackward : (rho d.fst : Real) ≤ (rho d.snd : Real) + 1 := by
      exact_mod_cast hdistNat.2
    rw [abs_le]
    constructor <;> linarith
  have hmin := abs_min_sub_min_le_max (1 : Real)
    ((rho d.snd : Real) / (r : Real)) 1
    ((rho d.fst : Real) / (r : Real))
  calc
    _ ≤ |(rho d.snd : Real) / (r : Real) -
        (rho d.fst : Real) / (r : Real)| := by
      simpa [isingFiniteGraphBoundaryTentCutoff, rho] using hmin
    _ = |(rho d.snd : Real) - (rho d.fst : Real)| / (r : Real) := by
      rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : Real) < r)]
    _ ≤ 1 / (r : Real) := by
      exact div_le_div_of_nonneg_right hdist (by positivity)

theorem isingFiniteGraphBoundaryTentCutoff_eq_one
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) (hr : 0 < r) (x : V)
    (hx : r ≤ isingFiniteGraphDistanceToBoundary G boundary hboundary x) :
    isingFiniteGraphBoundaryTentCutoff G boundary hboundary r x = 1 := by
  unfold isingFiniteGraphBoundaryTentCutoff
  rw [min_eq_left]
  apply (le_div_iff₀' (by positivity : (0 : Real) < r)).2
  norm_num
  exact_mod_cast hx

end

end StatMech.Universality
