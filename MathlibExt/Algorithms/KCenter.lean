/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Metric k-center: separation counting

The Gonzalez farthest-first 2-approximation rests on a counting
fact: `k + 1` points, pairwise more than `2r` apart, cannot all
lie within `r` of `k` or fewer centers. This module proves that
fact for finite sets of points and centers. The greedy
algorithm itself is not formalized here.
-/

@[expose] public section

/-- Two points within `r` of one center are within `2 * r`. -/
private theorem dist_le_two_mul_of_le {X : Type*} [PseudoMetricSpace X]
    {x y c : X} {r : ℝ} (hx : dist x c ≤ r) (hy : dist y c ≤ r) :
    dist x y ≤ 2 * r := by
  have h := dist_triangle x c y
  rw [dist_comm c y] at h
  linarith

/-- K-center separation core (ALG-42a): `k + 1` points, pairwise
more than `2 * r` apart, cannot all lie within `r` of `k` or
fewer centers. This is the counting step behind the Gonzalez
farthest-first 2-approximation; the greedy algorithm itself is
not formalized here. The general form, for packing and covering
numbers of arbitrary sets, is Mathlib's
`Metric.packingNumber_two_mul_le_externalCoveringNumber`. -/
theorem kcenter_separation_impossible {X : Type*} [PseudoMetricSpace X]
    {k : ℕ} {r : ℝ} (centers pts : Finset X)
    (hc : centers.card ≤ k) (hpts : k < pts.card)
    (hcov : ∀ x ∈ pts, ∃ c ∈ centers, dist x c ≤ r)
    (hsep : ∀ x ∈ pts, ∀ y ∈ pts, x ≠ y → 2 * r < dist x y) :
    False := by
  have hne : pts.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨c0, -, -⟩ := hcov x0 hx0
  have hcov' : ∀ x : X, ∃ c : X, x ∈ pts → c ∈ centers ∧ dist x c ≤ r := by
    intro x
    by_cases hx : x ∈ pts
    · obtain ⟨c, hc_mem, hc_dist⟩ := hcov x hx
      exact ⟨c, fun _ => ⟨hc_mem, hc_dist⟩⟩
    · exact ⟨c0, fun h => absurd h hx⟩
  choose f hf using hcov'
  have hmaps : Set.MapsTo f (↑pts : Set X) (↑centers : Set X) := by
    intro x hx
    have hx' : x ∈ pts := Finset.mem_coe.mp hx
    have h := (hf x hx').1
    exact Finset.mem_coe.mpr h
  have hinj : Set.InjOn f (↑pts : Set X) := by
    intro x1 hx1 x2 hx2 heq
    have hx1' : x1 ∈ pts := Finset.mem_coe.mp hx1
    have hx2' : x2 ∈ pts := Finset.mem_coe.mp hx2
    by_contra hne
    have h1 : dist x1 (f x1) ≤ r := (hf x1 hx1').2
    have h2 : dist x2 (f x2) ≤ r := (hf x2 hx2').2
    rw [← heq] at h2
    have hle : dist x1 x2 ≤ 2 * r := dist_le_two_mul_of_le h1 h2
    have hlt : 2 * r < dist x1 x2 := hsep x1 hx1' x2 hx2' hne
    linarith
  have hcard : pts.card ≤ centers.card := Finset.card_le_card_of_injOn f hmaps hinj
  omega

end
