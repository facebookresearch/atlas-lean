/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2NeighborTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PlaneFibers

/-! Genuine root-line isometries transport all actual rooted A2 planes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual unnormalized integer vectors transform by the same real isometry. -/
theorem leechRootedA2RealVector_action (e : leechIsomSubgroup) (u : leechIntegral) :
    e.val (leechRootedA2RealVector u.val) =
      leechRootedA2RealVector (leechIntegralAction e u).val := by
  have hs : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hv (v : Fin 24 → ℤ) : leechRootedA2RealVector v =
      Real.sqrt 8 • leechCoordinateEmbedding v := by
    funext i
    simp only [leechRootedA2RealVector, leechCoordinateEmbedding, Pi.smul_apply, smul_eq_mul]
    change (v i : ℝ) = Real.sqrt 8 * ((v i : ℝ) / Real.sqrt 8)
    field_simp
  rw [hv, map_smul, ← leechIntegralAction_embedding, ← hv]

/-- Orientation changes only the original preferred global sign. -/
theorem leechRootedA2Orient_integral_sign (r : leechRootedA2NeighborAddress) :
    (leechRootedA2Orient r).val = griessShortLatticeVector r.val ∨
      (leechRootedA2Orient r).val = -griessShortLatticeVector r.val := by
  unfold leechRootedA2Orient
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A genuine short-label transporter carries the oriented representatives with a possible sign. -/
theorem leechRootedA2Orient_action_signed (e : leechIsomSubgroup)
    (r s : leechRootedA2NeighborAddress) (hes : griessShortPermutation e r.val = s.val) :
    leechIntegralAction e (leechRootedA2Orient r).val = (leechRootedA2Orient s).val ∨
      leechIntegralAction e (leechRootedA2Orient r).val = -(leechRootedA2Orient s).val := by
  have hi := leechRootedA2_short_integral_image e r.val
  rw [hes] at hi
  rcases leechRootedA2Orient_integral_sign r with hr | hr <;>
    rcases leechRootedA2Orient_integral_sign s with hs | hs <;>
    rcases hi with hi | hi <;> simp [hr, hs, hi]

/-- Actual positively paired lattice neighbors are transported with their possible global sign. -/
theorem leechRootedA2OrientedNeighbor_signed_transitive
    (v w : leechRootedA2OrientedNeighbor) :
    ∃ e : leechIsomSubgroup, leechRootedA2PreservesRootLine e ∧
      (leechIntegralAction e v.val = w.val ∨ leechIntegralAction e v.val = -w.val) := by
  obtain ⟨r, rfl⟩ := leechRootedA2Orient_surjective v
  obtain ⟨s, rfl⟩ := leechRootedA2Orient_surjective w
  obtain ⟨e, he, hes⟩ := leechRootedA2Neighbor_transitive r s
  exact ⟨e, he, leechRootedA2Orient_action_signed e r s hes⟩

/-- Changing either generator by its global sign does not enlarge its real span. -/
theorem leechRootedA2_span_signed_le (u v x y : Fin 24 → ℝ)
    (hu : x = u ∨ x = -u) (hv : y = v ∨ y = -v) :
    Submodule.span ℝ ({x, y} : Set (Fin 24 → ℝ)) ≤
      Submodule.span ℝ ({u, v} : Set (Fin 24 → ℝ)) := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · rcases hu with rfl | rfl
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_insert _ _))
  · have he := Set.mem_singleton_iff.mp hz
    subst z
    rcases hv with rfl | rfl
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact Submodule.neg_mem _
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The real span is insensitive to either generator's global sign. -/
theorem leechRootedA2_span_signed (u v x y : Fin 24 → ℝ)
    (hu : x = u ∨ x = -u) (hv : y = v ∨ y = -v) :
    Submodule.span ℝ ({x, y} : Set (Fin 24 → ℝ)) =
      Submodule.span ℝ ({u, v} : Set (Fin 24 → ℝ)) := by
  have hiu : u = x ∨ u = -x := by
    rcases hu with hu | hu
    · exact Or.inl hu.symm
    · exact Or.inr (by rw [hu, neg_neg])
  have hiv : v = y ∨ v = -y := by
    rcases hv with hv | hv
    · exact Or.inl hv.symm
    · exact Or.inr (by rw [hv, neg_neg])
  exact le_antisymm (leechRootedA2_span_signed_le u v x y hu hv)
    (leechRootedA2_span_signed_le x y u v hiu hiv)

/-- A root-line isometry carrying a neighbor up to sign carries its actual real plane. -/
theorem leechRootedA2NeighborPlane_map (e : leechIsomSubgroup)
    (v w : leechRootedA2OrientedNeighbor) (he : leechRootedA2PreservesRootLine e)
    (hew : leechIntegralAction e v.val = w.val ∨ leechIntegralAction e v.val = -w.val) :
    (leechRootedA2NeighborPlane v).map e.val.toLinearMap = leechRootedA2NeighborPlane w := by
  rw [leechRootedA2NeighborPlane, leechRootedA2NeighborPlane,
    Submodule.map_span, Set.image_pair]
  change Submodule.span ℝ ({e.val (leechRootedA2RealVector leechRootedA2Root.val),
      e.val (leechRootedA2RealVector v.val.val)} : Set (Fin 24 → ℝ)) =
    Submodule.span ℝ ({leechRootedA2RealVector leechRootedA2Root.val,
      leechRootedA2RealVector w.val.val} : Set (Fin 24 → ℝ))
  rw [leechRootedA2RealVector_action, leechRootedA2RealVector_action]
  apply leechRootedA2_span_signed
  · rcases he with he | he <;> rw [he]
    · exact Or.inl rfl
    · right
      funext i
      simp [leechRootedA2RealVector]
  · rcases hew with hew | hew <;> rw [hew]
    · exact Or.inl rfl
    · right
      funext i
      simp [leechRootedA2RealVector]

/-- Every root-line isometry sends an actual rooted plane to another actual rooted plane. -/
theorem leechRootedA2Plane_map_mem (e : leechIsomSubgroup)
    (he : leechRootedA2PreservesRootLine e) (p : leechRootedA2Plane) :
    p.val.map e.val.toLinearMap ∈ Set.range leechRootedA2NeighborPlane := by
  obtain ⟨v, hv⟩ := p.property
  obtain ⟨r, hrv⟩ := leechRootedA2Orient_surjective v
  let s : leechRootedA2NeighborAddress := ⟨griessShortPermutation e r.val,
    leechRootedA2_root_action_neighbor e he r.val r.property⟩
  refine ⟨leechRootedA2Orient s, ?_⟩
  rw [← hv, ← hrv]
  exact (leechRootedA2NeighborPlane_map e _ _ he
    (leechRootedA2Orient_action_signed e r s rfl)).symm

/-- Every genuine rooted plane is the real image of any other by a root-line isometry. -/
theorem leechRootedA2Plane_transitive (p q : leechRootedA2Plane) :
    ∃ e : leechIsomSubgroup, leechRootedA2PreservesRootLine e ∧
      p.val.map e.val.toLinearMap = q.val := by
  obtain ⟨v, hv⟩ := p.property
  obtain ⟨w, hw⟩ := q.property
  obtain ⟨e, he, hew⟩ := leechRootedA2OrientedNeighbor_signed_transitive v w
  refine ⟨e, he, ?_⟩
  rw [← hv, ← hw]
  exact leechRootedA2NeighborPlane_map e v w he hew

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
