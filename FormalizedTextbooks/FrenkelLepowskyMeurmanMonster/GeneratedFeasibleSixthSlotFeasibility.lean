/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryPhysicalCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthRepresentative

/-! The counted sixth prototype is a genuine feasible axis for its own rooted pair axis.
This is the feasibility half of source slot 7 (label 6A1) of Höhn–Seysen,
arXiv:2508.01037, §4 and Table 3. The proof follows the literal triality, local and
triality word of the prototype, starting from the actual secondary feasible orbit.
No orbit count or table value is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every generated element transports a feasible orbit together with both reference axes. -/
theorem generatedFeasibleSixthSlot_orbit_map (g : ↥G) {a b x : GriessSpace}
    (hx : x ∈ generatedFeasibleVectorOrbit a b) :
    g.val x ∈ generatedFeasibleVectorOrbit (g.val a) (g.val b) := by
  obtain ⟨s, rfl⟩ := hx
  have hs : s.val.val a = a := s.property
  have hinv : (g⁻¹ : ↥G).val (g.val a) = a := by
    change (g⁻¹ * g : ↥G).val a = a
    rw [inv_mul_cancel]
    rfl
  refine ⟨⟨g * s.val * g⁻¹, ?_⟩, ?_⟩
  · change g.val (s.val.val ((g⁻¹ : ↥G).val (g.val a))) = g.val a
    rw [hinv, hs]
  · change g.val (s.val.val ((g⁻¹ : ↥G).val (g.val b))) = g.val (s.val.val b)
    have hb : (g⁻¹ : ↥G).val (g.val b) = b := by
      change (g⁻¹ * g : ↥G).val b = b
      rw [inv_mul_cancel]
      rfl
    rw [hb]

/-- The local specialization of feasible-orbit transport. -/
theorem generatedFeasibleSixthSlot_orbit_local (h : H) {a b x : GriessSpace}
    (hx : x ∈ generatedFeasibleVectorOrbit a b) :
    rhoLocal h x ∈ generatedFeasibleVectorOrbit (rhoLocal h a) (rhoLocal h b) :=
  generatedFeasibleSixthSlot_orbit_map (localIntoGenerated h) hx

/-- A generated element fixing the first axis preserves the feasible orbit itself. -/
theorem generatedFeasibleSixthSlot_orbit_fixed (g : ↥G) {a b x : GriessSpace}
    (hg : g.val a = a) (hx : x ∈ generatedFeasibleVectorOrbit a b) :
    g.val x ∈ generatedFeasibleVectorOrbit a b := by
  obtain ⟨s, rfl⟩ := hx
  have hs : s.val.val a = a := s.property
  refine ⟨⟨g * s.val, ?_⟩, rfl⟩
  change g.val (s.val.val a) = a
  rw [hs, hg]

/-- Triality fixes every positive pair axis, hence preserves its feasible orbit. -/
theorem generatedFeasibleSixthSlot_orbit_triality (p : Fin 276) {x : GriessSpace}
    (hx : x ∈ generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1)) :
    sExtra x ∈ generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1) := by
  refine generatedFeasibleSixthSlot_orbit_fixed extraIntoGenerated ?_ hx
  change sExtra (conwayShortAxis (Sum.inl (0, p)) 0) = conwayShortAxis (Sum.inl (0, p)) 0
  rw [conwayShortAxis_pair_zero]
  exact conwayAxis_triality p

/-- A local element carrying one positive signed axis to another carries the opposite
signed axis to the opposite signed axis. -/
theorem generatedFeasibleSixthSlot_local_opposite (h : H) (r s : GriessShortIndex)
    (hh : rhoLocal h (conwayShortAxis r 0) = conwayShortAxis s 0) :
    rhoLocal h (conwayShortAxis r 1) = conwayShortAxis s 1 := by
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localGriessRepresentation f _ = _ at hh ⊢
  rw [generatedAxis_localFiber_image] at hh ⊢
  have he := @generatedAxis_signed_injective (_, _) (_, _) hh
  simp only [Prod.mk.injEq, add_zero] at he
  rw [he.1, he.2, zero_add]

/-- The inverse local element reverses a proved vector transport. -/
theorem generatedFeasibleSixthSlot_local_inverse (h : H) {x y : GriessSpace}
    (hh : rhoLocal h x = y) : rhoLocal h⁻¹ y = x := by
  rw [← hh, map_inv]
  exact (rhoLocal h).symm_apply_apply x

/-- Original Leech isometries preserve perpendicularity of short representatives. -/
theorem generatedFeasibleSixthSlot_image_orthogonal (e : leechIsomSubgroup)
    (r s : GriessShortIndex)
    (hrs : stdPairingFun (griessShortVector r) (griessShortVector s) = 0) :
    stdPairingFun (griessShortVector (griessShortPermutation e r))
      (griessShortVector (griessShortPermutation e s)) = 0 := by
  have hp := e.property.1 (griessShortVector r) (griessShortVector s)
  rw [hrs] at hp
  rcases griessShortPermutation_vector e r with h0 | h0 <;>
    rcases griessShortPermutation_vector e s with h1 | h1
  all_goals
    rw [h0, h1] at hp
    simpa only [stdPairingFun, Pi.neg_apply, neg_mul, mul_neg, neg_neg,
      Finset.sum_neg_distrib, neg_eq_zero] using hp

/-- The literal odd short prototype is perpendicular to the first preferred source root,
the minus pair on physical coordinates twelve and sixteen. -/
theorem generatedFeasibleSixthSlot_source_root_orthogonal :
    stdPairingFun (griessShortVector (Sum.inl (0, generatedSixthSourcePair 0)))
      (griessShortVector (Sum.inr (Sum.inr (0, 0)))) = 0 := by
  have hi : griessShortIntegral (Sum.inl (0, generatedSixthSourcePair 0)) =
      fun i => 4 * (if i = 12 then (1 : ℤ) else 0) +
        (-4) * (if i = 16 then (1 : ℤ) else 0) := by
    funext i
    simp only [griessShortIntegral, (generatedSixth_pair_coordinate_certificate 0).1,
      Matrix.cons_val_zero, ite_true]
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  rw [griessShortVector_pairing, leechIntegralPairing, hi]
  simp only [add_mul, mul_assoc, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [griessShortIntegral, Fin.val_zero, hm, Nat.zero_testBit, Bool.false_eq_true,
    ite_false, one_mul]
  norm_num

set_option maxRecDepth 10000 in
-- Elaborate the subtype of the complete 93,150-address finite physical catalogue.
/-- The literal odd short prototype is feasible for the positive source root axis.
Coverage of the actual secondary orbit is transported from the physical first root. -/
theorem generatedFeasibleSixthSlot_source_short_feasible :
    conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0 ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedSixthSourcePair 0)) 0)
      (conwayShortAxis (Sum.inl (0, generatedSixthSourcePair 0)) 1) := by
  obtain ⟨k, hk⟩ := generatedAxis_local_signed_transitive
    (Sum.inl (0, generatedSixthSourcePair 0))
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 0
  have hk1 := generatedFeasibleSixthSlot_local_opposite k _ _ hk
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup k
  change localFiberIntoH f = k at hf
  have hperm : griessShortPermutation f.val.2 (Sum.inl (0, generatedSixthSourcePair 0)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair) := by
    have h := hk
    rw [← hf] at h
    change localGriessRepresentation f _ = _ at h
    rw [generatedAxis_localFiber_image] at h
    exact congrArg Prod.fst (@generatedAxis_signed_injective (_, _) (_, _) h)
  have himage : rhoLocal k (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0) =
      conwayShortAxis (griessShortPermutation f.val.2 (Sum.inr (Sum.inr (0, 0))))
        (localShortPhase f (Sum.inr (Sum.inr (0, 0))) + 0) := by
    rw [← hf]
    exact generatedAxis_localFiber_image f _ _
  have horth := generatedFeasibleSixthSlot_image_orthogonal f.val.2 _ _
    generatedFeasibleSixthSlot_source_root_orthogonal
  rw [hperm] at horth
  have hmem : griessShortPermutation f.val.2 (Sum.inr (Sum.inr (0, 0))) ∈
      generatedFeasibleOrthogonalShortLabels := by
    rw [generatedFeasibleOrthogonalShortLabels_mem,
      ← generatedFeasiblePhysicalRoot_orthogonal_iff]
    exact horth
  have hsec : rhoLocal k (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0) ∈
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
    rw [generatedFeasibleSecondaryLocalOrbit_eq_physical, himage]
    exact ⟨⟨(_, _), Finset.mem_product.mpr ⟨hmem, Finset.mem_univ _⟩⟩, rfl⟩
  have hback := generatedFeasibleSixthSlot_orbit_local k⁻¹
    (generatedFeasibleSecondaryLocalOrbit_subset generatedFeasiblePhysicalRootPair hsec)
  rwa [generatedFeasibleSixthSlot_local_inverse k hk,
    generatedFeasibleSixthSlot_local_inverse k hk1,
    generatedFeasibleSixthSlot_local_inverse k
      (x := conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0) rfl] at hback

/-- The literal middle local word sends both signs of the source root axis to the
corresponding signs of the target root axis on coordinates sixteen and seventeen. -/
theorem generatedFeasibleSixthSlot_local_root (c : ZMod 2) :
    rhoLocal (localFiberIntoH generatedSixthLocalFiber)
      (conwayShortAxis (Sum.inl (0, generatedSixthSourcePair 0)) c) =
        conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) c := by
  change localGriessRepresentation generatedSixthLocalFiber _ = _
  rw [generatedAxis_localFiber_image, generatedSixth_pair_permutation,
    generatedSixth_pair_phase, zero_add]

/-- The counted sixth prototype is an actual feasible axis for the positive target root axis:
it lies in the orbit of the opposite axis under the full generated stabilizer. -/
theorem generatedFeasibleSixthSlot_prototype_feasible :
    generatedSixthAxis ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) 0)
      (conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) 1) := by
  have hodd := generatedFeasibleSixthSlot_orbit_triality (generatedSixthSourcePair 0)
    generatedFeasibleSixthSlot_source_short_feasible
  have hmid := generatedFeasibleSixthSlot_orbit_local
    (localFiberIntoH generatedSixthLocalFiber) hodd
  rw [generatedFeasibleSixthSlot_local_root, generatedFeasibleSixthSlot_local_root] at hmid
  rw [generatedSixthAxis_local_expression]
  exact generatedFeasibleSixthSlot_orbit_triality (generatedSixthTargetPair 0) hmid

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
