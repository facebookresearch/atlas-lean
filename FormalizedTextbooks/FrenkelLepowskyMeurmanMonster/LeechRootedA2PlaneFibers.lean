/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PlaneGeometry

/-! The actual two-neighbor fibers of a rooted A2 plane. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual Euclidean pairing distributes over a two-vector linear combination. -/
theorem leechRootedA2_pairing_combination (u v w : Fin 24 → ℝ) (a b : ℝ) :
    stdPairingFun u (a • v + b • w) =
      a * stdPairingFun u v + b * stdPairingFun u w := by
  simp only [stdPairingFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual Euclidean square of a two-vector linear combination. -/
theorem leechRootedA2_square_combination (u v : Fin 24 → ℝ) (a b : ℝ) :
    stdPairingFun (a • u + b • v) (a • u + b • v) =
      a ^ 2 * stdPairingFun u u + 2 * a * b * stdPairingFun u v +
        b ^ 2 * stdPairingFun v v := by
  simp only [stdPairingFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An A2 plane contains exactly the two positively paired vectors of root length. -/
theorem leechRootedA2_plane_two_neighbors (u v w : Fin 24 → ℝ)
    (hu : stdPairingFun u u = 32) (hv : stdPairingFun v v = 32)
    (huv : stdPairingFun u v = 16) (hw : stdPairingFun w w = 32)
    (huw : stdPairingFun u w = 16)
    (hm : w ∈ Submodule.span ℝ ({u, v} : Set (Fin 24 → ℝ))) :
    w = v ∨ w = u - v := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hm
  have hp : 32 * a + 16 * b = 16 := by
    rw [← hab, leechRootedA2_pairing_combination, hu, huv] at huw
    linarith
  have hn : 32 * a ^ 2 + 32 * a * b + 32 * b ^ 2 = 32 := by
    rw [← hab, leechRootedA2_square_combination, hu, hv, huv] at hw
    nlinarith
  rcases leechRootedA2Plane_neighbor_coefficients a b hp hn with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    rw [← hab, ha, hb]
    simp
  · right
    rw [← hab, ha, hb]
    simp [sub_eq_add_neg]

/-- Integer lattice vectors are embedded in the actual real coordinate space. -/
def leechRootedA2RealVector (v : Fin 24 → ℤ) : Fin 24 → ℝ := fun i => (v i : ℝ)

/-- The real pairing agrees with the actual integer lattice pairing. -/
theorem leechRootedA2RealVector_pairing (u v : Fin 24 → ℤ) :
    stdPairingFun (leechRootedA2RealVector u) (leechRootedA2RealVector v) =
      (leechIntegralPairing u v : ℝ) := by
  simp [stdPairingFun, leechRootedA2RealVector, leechIntegralPairing]

/-- The real square agrees with the actual integer square sum. -/
theorem leechRootedA2RealVector_square (u : Fin 24 → ℤ) :
    stdPairingFun (leechRootedA2RealVector u) (leechRootedA2RealVector u) =
      (leechSquareSum u : ℝ) := by
  simp [stdPairingFun, leechRootedA2RealVector, leechSquareSum, pow_two]

/-- The genuine root and neighbor span their real A2 plane. -/
def leechRootedA2NeighborPlane (v : leechRootedA2OrientedNeighbor) :
    Submodule ℝ (Fin 24 → ℝ) :=
  Submodule.span ℝ ({leechRootedA2RealVector leechRootedA2RootIntegral,
    leechRootedA2RealVector v.val.val} : Set (Fin 24 → ℝ))

/-- Every actual neighbor in one such plane is the first neighbor or its root-minus mate. -/
theorem leechRootedA2NeighborPlane_member_iff (v w : leechRootedA2OrientedNeighbor) :
    leechRootedA2RealVector w.val.val ∈ leechRootedA2NeighborPlane v ↔
      w = v ∨ w = leechRootedA2NeighborMate v := by
  constructor
  · intro hm
    have hu : stdPairingFun (leechRootedA2RealVector leechRootedA2RootIntegral)
        (leechRootedA2RealVector leechRootedA2RootIntegral) = 32 := by
      rw [leechRootedA2RealVector_square, leechRootedA2RootIntegral_squareSum]
      norm_num
    have hv : stdPairingFun (leechRootedA2RealVector v.val.val)
        (leechRootedA2RealVector v.val.val) = 32 := by
      rw [leechRootedA2RealVector_square, v.property.1]; norm_num
    have hw : stdPairingFun (leechRootedA2RealVector w.val.val)
        (leechRootedA2RealVector w.val.val) = 32 := by
      rw [leechRootedA2RealVector_square, w.property.1]; norm_num
    have hp (x : leechRootedA2OrientedNeighbor) :
        stdPairingFun (leechRootedA2RealVector leechRootedA2RootIntegral)
          (leechRootedA2RealVector x.val.val) = 16 := by
      rw [leechRootedA2RealVector_pairing, leechRootedA2RootIntegral_pairing, x.property.2]
      norm_num
    rcases leechRootedA2_plane_two_neighbors _ _ _ hu hv (hp v) hw (hp w) hm with he | he
    · left
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact Int.cast_injective (congrFun he i)
    · right
      apply Subtype.ext
      apply Subtype.ext
      funext i
      have hi := congrFun he i
      change (w.val.val i : ℝ) =
        (leechRootedA2RootIntegral i : ℝ) - (v.val.val i : ℝ) at hi
      exact_mod_cast hi
  · rintro (rfl | rfl)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have he : leechRootedA2RealVector (leechRootedA2NeighborMate v).val.val =
          leechRootedA2RealVector leechRootedA2RootIntegral -
            leechRootedA2RealVector v.val.val := by
        funext i
        simp [leechRootedA2RealVector, leechRootedA2NeighborMate]
      rw [he]
      apply (leechRootedA2NeighborPlane v).sub_mem
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Neighbor membership gives actual plane inclusion. -/
theorem leechRootedA2NeighborPlane_le (v w : leechRootedA2OrientedNeighbor)
    (hm : leechRootedA2RealVector w.val.val ∈ leechRootedA2NeighborPlane v) :
    leechRootedA2NeighborPlane w ≤ leechRootedA2NeighborPlane v := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · have he := Set.mem_singleton_iff.mp hx
    rw [he]
    exact hm

/-- Exactly the two root-minus partners span the same actual rooted A2 plane. -/
theorem leechRootedA2NeighborPlane_eq_iff (v w : leechRootedA2OrientedNeighbor) :
    leechRootedA2NeighborPlane w = leechRootedA2NeighborPlane v ↔
      w = v ∨ w = leechRootedA2NeighborMate v := by
  constructor
  · intro he
    apply (leechRootedA2NeighborPlane_member_iff v w).mp
    rw [← he]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro (rfl | rfl)
    · rfl
    · apply le_antisymm
      · apply leechRootedA2NeighborPlane_le
        exact (leechRootedA2NeighborPlane_member_iff _ _).mpr (Or.inr rfl)
      · apply leechRootedA2NeighborPlane_le
        apply (leechRootedA2NeighborPlane_member_iff _ _).mpr
        exact Or.inr (leechRootedA2NeighborMate_involutive v).symm

/-- Actual real planes spanned by the standard root and a genuine neighboring lattice vector. -/
abbrev leechRootedA2Plane := Set.range leechRootedA2NeighborPlane

/-- There are finitely many actual rooted planes, as an image of the genuine catalogue. -/
noncomputable instance : Fintype leechRootedA2Plane :=
  (Set.finite_range leechRootedA2NeighborPlane).fintype

/-- Map a genuine lattice neighbor to its actual rooted plane. -/
def leechRootedA2PlaneOfNeighbor (v : leechRootedA2OrientedNeighbor) : leechRootedA2Plane :=
  ⟨leechRootedA2NeighborPlane v, ⟨v, rfl⟩⟩

/-- Every actual rooted plane has exactly two genuine positively paired lattice neighbors. -/
theorem leechRootedA2Plane_fiber_card (p : leechRootedA2Plane) :
    Fintype.card {w : leechRootedA2OrientedNeighbor // leechRootedA2PlaneOfNeighbor w = p} = 2 := by
  classical
  obtain ⟨v, hv⟩ := p.property
  have hp : leechRootedA2PlaneOfNeighbor v = p := Subtype.ext hv
  rw [← hp]
  have hf : Finset.univ.filter (fun w => leechRootedA2PlaneOfNeighbor w =
      leechRootedA2PlaneOfNeighbor v) = {v, leechRootedA2NeighborMate v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [Subtype.ext_iff]
    change (leechRootedA2NeighborPlane w = leechRootedA2NeighborPlane v) ↔ _
    exact leechRootedA2NeighborPlane_eq_iff v w
  rw [Fintype.card_subtype, hf, Finset.card_pair
    (leechRootedA2NeighborMate_ne v).symm]

/-- The actual geometric rooted A2 planes are counted by their two-neighbor fibers. -/
theorem leechRootedA2Plane_card : Fintype.card leechRootedA2Plane = 2300 := by
  classical
  have hc := Fintype.card_congr (Equiv.sigmaFiberEquiv leechRootedA2PlaneOfNeighbor)
  rw [Fintype.card_sigma, leechRootedA2OrientedNeighbor_card] at hc
  simp only [leechRootedA2Plane_fiber_card, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hc
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
