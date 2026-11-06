/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientDoubleCount
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationFeasibleSecondaryCount
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.GroupTheory.GroupAction.Blocks

/-! Conditional assembly of the actual feasible orbit count.

The feasible orbit lies in the orthogonal partners of the first axis. If the actual
global axis orbit is covered by finitely many actual local orbits, double counting
bounds the number of orthogonal partners by the local orbit sizes and the numbers of
orthogonal signed-short axes. A lower bound by actual feasible vectors then fixes the
feasible count. Coverage, the local orbit sizes, the orthogonal axis counts and the
feasible lower bound are explicit hypotheses here; this module proves no closure of
the final count by itself. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem localOrbitUnion_mem_iff {ι : Type*} (v : ι → GriessSpace) (x : GriessSpace) :
    x ∈ generatedLocalOrbitUnion v ↔ ∃ i, x ∈ MulAction.orbit H (v i) := by
  constructor
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, h, rfl⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, h, rfl⟩

/-- Under a finite actual local-orbit cover, the orthogonal partners of an actual
signed-short axis form a finite set. -/
theorem generatedFeasibleAmbientOrthogonalAxes_finite {ι : Type*} [Finite ι]
    (r : GriessShortIndex) (c : ZMod 2) (v : ι → GriessSpace)
    (hcover : generatedVectorOrbit (conwayShortAxis r c) ⊆ generatedLocalOrbitUnion v) :
    (generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r c)).Finite := by
  refine (Set.finite_iUnion fun i => generatedFeasibleAmbient_local_orbit_finite (v i)).subset ?_
  intro x hx
  obtain ⟨i, hi⟩ := (localOrbitUnion_mem_iff v x).mp (hcover hx.1)
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Double counting over an actual local-orbit cover bounds the orthogonal partners. -/
theorem generatedFeasibleAmbient_orthogonal_card_mul_le {ι : Type*} [Fintype ι]
    (r : GriessShortIndex) (c : ZMod 2) (v : ι → GriessSpace)
    (hcover : generatedVectorOrbit (conwayShortAxis r c) ⊆ generatedLocalOrbitUnion v) :
    196560 * Nat.card (generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r c)) ≤
      ∑ i, Nat.card (MulAction.orbit H (v i)) * generatedFeasibleAmbientAxisZeroCount (v i) := by
  let T : ι → Set GriessSpace := fun i =>
    {x | x ∈ MulAction.orbit H (v i) ∧ griessForm (conwayShortAxis r c) x = 0}
  have hsub : generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r c) ⊆ ⋃ i, T i := by
    intro x hx
    obtain ⟨i, hi⟩ := (localOrbitUnion_mem_iff v x).mp (hcover hx.1)
    exact Set.mem_iUnion.mpr ⟨i, hi, hx.2⟩
  have hfin : (⋃ i, T i).Finite := Set.finite_iUnion fun i =>
    (generatedFeasibleAmbient_local_orbit_finite (v i)).subset fun x hx => hx.1
  have hle : Nat.card (generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r c)) ≤
      ∑ i, Nat.card (T i) := by
    rw [Nat.card_coe_set_eq]
    simp_rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_iUnion_le_of_fintype T)
  calc 196560 * Nat.card (generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r c))
      ≤ 196560 * ∑ i, Nat.card (T i) := Nat.mul_le_mul_left _ hle
    _ = ∑ i, 196560 * Nat.card (T i) := Finset.mul_sum _ _ _
    _ = ∑ i, Nat.card (MulAction.orbit H (v i)) *
        generatedFeasibleAmbientAxisZeroCount (v i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact generatedFeasibleAmbient_local_double_count r c (v i)

/-- Local orbit sizes and upper bounds for the orthogonal axis counts give the
double-counting bound, with any numerical upper estimate. -/
theorem generatedFeasibleAmbient_upper_of_bounds {ι : Type*} [Fintype ι]
    (v : ι → GriessSpace) (n s : ι → ℕ) (N : ℕ)
    (hn : ∀ i, Nat.card (MulAction.orbit H (v i)) = n i)
    (hs : ∀ i, generatedFeasibleAmbientAxisZeroCount (v i) ≤ s i)
    (harith : ∑ i, n i * s i ≤ 196560 * N) :
    ∑ i, Nat.card (MulAction.orbit H (v i)) * generatedFeasibleAmbientAxisZeroCount (v i) ≤
      196560 * N := by
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) harith
  rw [hn i]
  exact Nat.mul_le_mul_left _ (hs i)

/-- The actual feasible count from an actual local-orbit cover of the global orbit,
the double-counting upper bound, and a finite set of actual feasible vectors. -/
theorem generatedFeasibleAmbient_feasible_card_of_cover {ι : Type*} [Fintype ι]
    (r : GriessShortIndex) (v : ι → GriessSpace) (N : ℕ)
    (hcover : generatedVectorOrbit (conwayShortAxis r 0) ⊆ generatedLocalOrbitUnion v)
    (hupper : ∑ i, Nat.card (MulAction.orbit H (v i)) *
      generatedFeasibleAmbientAxisZeroCount (v i) ≤ 196560 * N)
    (U : Set GriessSpace)
    (hU : U ⊆ generatedFeasibleVectorOrbit (conwayShortAxis r 0) (conwayShortAxis r 1))
    (hUcard : N ≤ Nat.card U) :
    Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis r 0) (conwayShortAxis r 1)) =
      N := by
  have hsubF := generatedFeasibleVectorOrbit_subset_opposite_orthogonalAxes r
  have hfinP := generatedFeasibleAmbientOrthogonalAxes_finite r 0 v hcover
  have hfinF := hfinP.subset hsubF
  have hP : Nat.card (generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r 0)) ≤ N := by
    have h := (generatedFeasibleAmbient_orthogonal_card_mul_le r 0 v hcover).trans hupper
    omega
  have hFP : Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis r 0)
      (conwayShortAxis r 1)) ≤
      Nat.card (generatedFeasibleAmbientOrthogonalAxes (conwayShortAxis r 0)) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsubF hfinP
  have hUF : Nat.card U ≤ Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis r 0)
      (conwayShortAxis r 1)) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hU hfinF
  omega

/-- Actual local first-axis stabilizer elements lie in the actual generated stabilizer. -/
theorem generatedFeasibleAmbient_local_orbit_subset (p : Fin 276) (x : GriessSpace)
    (hx : x ∈ generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1)) :
    MulAction.orbit (localAxisStabilizer p) x ⊆
      generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
        (conwayShortAxis (Sum.inl (0, p)) 1) := by
  rintro y ⟨h, rfl⟩
  obtain ⟨g, hg⟩ := hx
  have hfix : (localIntoGenerated h.val).val (conwayShortAxis (Sum.inl (0, p)) 0) =
      conwayShortAxis (Sum.inl (0, p)) 0 := by
    rw [conwayShortAxis_pair_zero]
    exact h.property
  have hgfix : g.val.val (conwayShortAxis (Sum.inl (0, p)) 0) =
      conwayShortAxis (Sum.inl (0, p)) 0 := g.property
  refine ⟨⟨localIntoGenerated h.val * g.val, ?_⟩, ?_⟩
  · change (localIntoGenerated h.val).val (g.val.val _) = _
    rw [hgfix, hfix]
  · change rhoLocal h.val (g.val.val _) = rhoLocal h.val x
    change g.val.val _ = x at hg
    rw [hg]

/-- Finitely many actual feasible vectors whose actual local stabilizer orbits have
pairwise distinct sizes give a feasible lower bound by the sum of those sizes. -/
theorem generatedFeasibleAmbient_class_union_card {κ : Type*} [Fintype κ] (p : Fin 276)
    (w : κ → GriessSpace) (f : κ → ℕ)
    (hw : ∀ j, w j ∈ generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1))
    (hf : ∀ j, Nat.card (MulAction.orbit (localAxisStabilizer p) (w j)) = f j)
    (hinj : Function.Injective f) :
    (⋃ j, MulAction.orbit (localAxisStabilizer p) (w j)) ⊆
        generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
          (conwayShortAxis (Sum.inl (0, p)) 1) ∧
      Nat.card (⋃ j, MulAction.orbit (localAxisStabilizer p) (w j)) = ∑ j, f j := by
  refine ⟨Set.iUnion_subset fun j => generatedFeasibleAmbient_local_orbit_subset p (w j) (hw j),
    ?_⟩
  have hdisj : Pairwise (Function.onFun Disjoint
      fun j => MulAction.orbit (localAxisStabilizer p) (w j)) := by
    intro j k hjk
    refine (MulAction.orbit.eq_or_disjoint (w j) (w k)).resolve_left fun he => hjk ?_
    apply hinj
    rw [← hf j, ← hf k]
    exact congrArg (fun s : Set GriessSpace => Nat.card s) he
  have hfin (j : κ) : (MulAction.orbit (localAxisStabilizer p) (w j)).Finite := by
    have : Finite H := h_finite
    exact Set.finite_range _
  rw [Nat.card_coe_set_eq, Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Nat.card_coe_set_eq, hf j]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
