/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindTriangle

/-! Short Fifth coset words for the partner-facing Fifth roots 7, 10 and 4.

The explicit Fifth root words 7, 10 and 4 are long (three to five Xi factors and many monomial
letters). This module certifies short coset words in the same C₅ orbits, with their exact binary
roots and explicit products of genuine Fifth-axis fixers carrying the root words' binary roots to
them, and turns identifications at these short words into the triality images at the root words:

* root 7: the two-Xi word `Root7c` of worker goctad's Eighth root 25 transport (both images from
  that inverse identification and the coverage of the Eighth family), or the two-Xi
  representative `Root7t` (both images from two identifications);
* roots 10 and 4 (phase merged): either triality image at the two-Xi representative.

No identification is asserted: all identification statements are hypotheses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-! ## Binary operators of the letters -/

private theorem partners_xiBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction co1XiIsometry v = omegaOrbitBinaryMatrices 0 *ᵥ v :=
  omegaOrbitIsometry_binary 0 v

private theorem partners_p0Binary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 0) v = omegaOrbitBinaryMatrices 3 *ᵥ v :=
  omegaOrbitIsometry_binary 3 v

private theorem partners_p1Binary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 1) v = omegaOrbitBinaryMatrices 4 *ᵥ v :=
  omegaOrbitIsometry_binary 4 v

set_option maxHeartbeats 1000000 in
-- One complete 24 by 24 binary matrix product.
/-- The binary operator of the second source permutation is an involution. -/
theorem generatedAxisGlobalTwelveFifthBindPartners_p1_sq :
    omegaOrbitBinaryMatrices 4 * omegaOrbitBinaryMatrices 4 = 1 := by
  decide +kernel

private theorem partners_p1invBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 1)⁻¹ v = omegaOrbitBinaryMatrices 4 *ᵥ v := by
  have h1 : leechBinaryAction (omegaOrbitPermutationIsometry 1)
      (omegaOrbitBinaryMatrices 4 *ᵥ v) = v := by
    rw [partners_p1Binary, Matrix.mulVec_mulVec, generatedAxisGlobalTwelveFifthBindPartners_p1_sq,
      Matrix.one_mulVec]
  calc leechBinaryAction (omegaOrbitPermutationIsometry 1)⁻¹ v =
      leechBinaryAction (omegaOrbitPermutationIsometry 1)⁻¹
        (leechBinaryAction (omegaOrbitPermutationIsometry 1)
          (omegaOrbitBinaryMatrices 4 *ᵥ v)) := by rw [h1]
    _ = _ := by rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

private theorem partners_xi_inv : co1XiIsometry⁻¹ = co1XiIsometry * co1XiIsometry := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, ← pow_three']
  exact co1XiIsometry_cube

private theorem partners_binaryRoot_val (f : localFiberSubgroup) :
    (generatedAxisGlobalBinaryRoot (localFiberIntoH f)).val =
      leechBinaryAction f⁻¹.val.2 (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) := by
  change co1BinaryAction (projH (localFiberIntoH f)⁻¹)
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← map_inv]
  rfl

/-! ## The short coset words -/

/-- The two-Xi Fifth coset word of goctad's Eighth root 25 transport (root 7 orbit). -/
def generatedAxisGlobalTwelveFifthBindRoot7cLetters : List IdentLetter :=
  [.xi, .mono (0, false), .mono (1, false), .xi, .mono (0, false)]

/-- The two-Xi Fifth representative of root 7. -/
def generatedAxisGlobalTwelveFifthBindRoot7tLetters : List IdentLetter :=
  [.xi, .xi, .mono (0, true), .mono (1, true), .xi, .xi, .mono (0, false)]

/-- The two-Xi Fifth representative of root 10. -/
def generatedAxisGlobalTwelveFifthBindRoot10tLetters : List IdentLetter :=
  [.xi, .xi, .mono (1, true), .mono (0, false), .mono (0, false), .xi, .xi, .mono (1, true)]

/-- The two-Xi Fifth representative of root 4. -/
def generatedAxisGlobalTwelveFifthBindRoot4tLetters : List IdentLetter :=
  [.xi, .xi, .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true),
    .mono (0, false), .mono (1, true), .xi, .xi, .mono (1, true), .mono (0, true)]

set_option maxHeartbeats 20000000 in
-- Short products of original binary operators on one complete binary point.
/-- The exact binary root of `Root7c`. -/
theorem generatedAxisGlobalTwelveFifthBindRoot7cLetters_root :
    (generatedAxisGlobalBinaryRoot
      (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7cLetters)).val =
      monsterCo1GeometryBinaryMaskDecode 7000320 := by
  unfold identWordLocal
  rw [partners_binaryRoot_val]
  have hs : (identWordFiber generatedAxisGlobalTwelveFifthBindRoot7cLetters)⁻¹.val.2 =
      (co1XiIsometry * (omegaOrbitPermutationIsometry 0 * (omegaOrbitPermutationIsometry 1 *
        (co1XiIsometry * (omegaOrbitPermutationIsometry 0 * 1)))))⁻¹ := rfl
  rw [hs]
  simp only [mul_one, mul_inv_rev, partners_xi_inv, mul_assoc]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [partners_xiBinary, generatedAxisGlobalTwelveFifthBind_permutationZeroInverse_binary,
    partners_p1invBinary]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Short products of original binary operators on one complete binary point.
/-- The exact binary root of `Root7t`. -/
theorem generatedAxisGlobalTwelveFifthBindRoot7tLetters_root :
    (generatedAxisGlobalBinaryRoot
      (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7tLetters)).val =
      monsterCo1GeometryBinaryMaskDecode 4249856 := by
  unfold identWordLocal
  rw [partners_binaryRoot_val]
  have hs : (identWordFiber generatedAxisGlobalTwelveFifthBindRoot7tLetters)⁻¹.val.2 =
      (co1XiIsometry * (co1XiIsometry * ((omegaOrbitPermutationIsometry 0)⁻¹ *
        ((omegaOrbitPermutationIsometry 1)⁻¹ * (co1XiIsometry * (co1XiIsometry *
          (omegaOrbitPermutationIsometry 0 * 1)))))))⁻¹ := rfl
  rw [hs]
  simp only [mul_one, mul_inv_rev, inv_inv, partners_xi_inv, mul_assoc]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [partners_xiBinary, partners_p0Binary, partners_p1Binary,
    generatedAxisGlobalTwelveFifthBind_permutationZeroInverse_binary]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Short products of original binary operators on one complete binary point.
/-- The exact binary root of `Root10t`. -/
theorem generatedAxisGlobalTwelveFifthBindRoot10tLetters_root :
    (generatedAxisGlobalBinaryRoot
      (identWordLocal generatedAxisGlobalTwelveFifthBindRoot10tLetters)).val =
      monsterCo1GeometryBinaryMaskDecode 1782788 := by
  unfold identWordLocal
  rw [partners_binaryRoot_val]
  have hs : (identWordFiber generatedAxisGlobalTwelveFifthBindRoot10tLetters)⁻¹.val.2 =
      (co1XiIsometry * (co1XiIsometry * ((omegaOrbitPermutationIsometry 1)⁻¹ *
        (omegaOrbitPermutationIsometry 0 * (omegaOrbitPermutationIsometry 0 *
          (co1XiIsometry * (co1XiIsometry * ((omegaOrbitPermutationIsometry 1)⁻¹ * 1))))))))⁻¹ :=
    rfl
  rw [hs]
  simp only [mul_one, mul_inv_rev, inv_inv, partners_xi_inv, mul_assoc]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [partners_xiBinary, partners_p1Binary,
    generatedAxisGlobalTwelveFifthBind_permutationZeroInverse_binary]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Short products of original binary operators on one complete binary point.
/-- The exact binary root of `Root4t`. -/
theorem generatedAxisGlobalTwelveFifthBindRoot4tLetters_root :
    (generatedAxisGlobalBinaryRoot
      (identWordLocal generatedAxisGlobalTwelveFifthBindRoot4tLetters)).val =
      monsterCo1GeometryBinaryMaskDecode 397418 := by
  unfold identWordLocal
  rw [partners_binaryRoot_val]
  have hs : (identWordFiber generatedAxisGlobalTwelveFifthBindRoot4tLetters)⁻¹.val.2 =
      (co1XiIsometry * (co1XiIsometry * (omegaOrbitPermutationIsometry 0 *
        ((omegaOrbitPermutationIsometry 1)⁻¹ * ((omegaOrbitPermutationIsometry 0)⁻¹ *
          ((omegaOrbitPermutationIsometry 1)⁻¹ * (omegaOrbitPermutationIsometry 0 *
            ((omegaOrbitPermutationIsometry 1)⁻¹ * (co1XiIsometry * (co1XiIsometry *
              ((omegaOrbitPermutationIsometry 1)⁻¹ *
                ((omegaOrbitPermutationIsometry 0)⁻¹ * 1))))))))))))⁻¹ := rfl
  rw [hs]
  simp only [mul_one, mul_inv_rev, inv_inv, partners_xi_inv, mul_assoc]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [partners_xiBinary, partners_p0Binary, partners_p1Binary,
    generatedAxisGlobalTwelveFifthBind_permutationZeroInverse_binary]
  decide +kernel

/-! ## Explicit Fifth-axis fixers -/

/-- Fixers carrying the binary root of the root word 7 to that of `Root7c`. -/
def generatedAxisGlobalTwelveFifthBindRoot7cTransport : generatedFifthLocalAxisStabilizer :=
  generatedAxisGlobalFifthGenerator 16 * generatedAxisGlobalFifthGenerator 12 *
    generatedAxisGlobalFifthGenerator 16 * generatedAxisGlobalFifthGenerator 18 *
    generatedAxisGlobalFifthGenerator 17 * generatedAxisGlobalFifthGenerator 1

/-- Fixers carrying the binary root of the root word 7 to that of `Root7t`. -/
def generatedAxisGlobalTwelveFifthBindRoot7tTransport : generatedFifthLocalAxisStabilizer :=
  generatedAxisGlobalFifthGenerator 15 * generatedAxisGlobalFifthGenerator 16 *
    generatedAxisGlobalFifthGenerator 16 * generatedAxisGlobalFifthGenerator 12 *
    generatedAxisGlobalFifthGenerator 18 * generatedAxisGlobalFifthGenerator 17 *
    generatedAxisGlobalFifthGenerator 0

/-- Fixers carrying the binary root of the root word 10 to that of `Root10t`. -/
def generatedAxisGlobalTwelveFifthBindRoot10tTransport : generatedFifthLocalAxisStabilizer :=
  generatedAxisGlobalFifthGenerator 14 * generatedAxisGlobalFifthGenerator 15 *
    generatedAxisGlobalFifthGenerator 17 * generatedAxisGlobalFifthGenerator 18 *
    generatedAxisGlobalFifthGenerator 15 * generatedAxisGlobalFifthGenerator 14 *
    generatedAxisGlobalFifthGenerator 1

/-- Fixers carrying the binary root of the root word 4 to that of `Root4t`. -/
def generatedAxisGlobalTwelveFifthBindRoot4tTransport : generatedFifthLocalAxisStabilizer :=
  generatedAxisGlobalFifthGenerator 18 * generatedAxisGlobalFifthGenerator 16 *
    generatedAxisGlobalFifthGenerator 10 * generatedAxisGlobalFifthGenerator 13 *
    generatedAxisGlobalFifthGenerator 9

set_option maxHeartbeats 20000000 in
-- Six actual generator binary matrices on one complete binary point.
theorem generatedAxisGlobalTwelveFifthBindRoot7cTransport_actual :
    generatedAxisGlobalBinaryAct generatedAxisGlobalTwelveFifthBindRoot7cTransport.val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 7)) =
      generatedAxisGlobalBinaryRoot
        (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7cLetters) := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFifthBindRoot7cLetters_root]
  change (generatedAxisGlobalBinaryAct
    ((generatedAxisGlobalFifthGenerator 16).val * (generatedAxisGlobalFifthGenerator 12).val *
      (generatedAxisGlobalFifthGenerator 16).val * (generatedAxisGlobalFifthGenerator 18).val *
      (generatedAxisGlobalFifthGenerator 17).val * (generatedAxisGlobalFifthGenerator 1).val)
    (generatedAxisGlobalFifthRoot 7)).val = _
  simp only [generatedAxisGlobalBinaryAct_mul]
  simp_rw [generatedAxisGlobalFifthGenerator_binary]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Seven actual generator binary matrices on one complete binary point.
theorem generatedAxisGlobalTwelveFifthBindRoot7tTransport_actual :
    generatedAxisGlobalBinaryAct generatedAxisGlobalTwelveFifthBindRoot7tTransport.val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 7)) =
      generatedAxisGlobalBinaryRoot
        (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7tLetters) := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFifthBindRoot7tLetters_root]
  change (generatedAxisGlobalBinaryAct
    ((generatedAxisGlobalFifthGenerator 15).val * (generatedAxisGlobalFifthGenerator 16).val *
      (generatedAxisGlobalFifthGenerator 16).val * (generatedAxisGlobalFifthGenerator 12).val *
      (generatedAxisGlobalFifthGenerator 18).val * (generatedAxisGlobalFifthGenerator 17).val *
      (generatedAxisGlobalFifthGenerator 0).val)
    (generatedAxisGlobalFifthRoot 7)).val = _
  simp only [generatedAxisGlobalBinaryAct_mul]
  simp_rw [generatedAxisGlobalFifthGenerator_binary]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Seven actual generator binary matrices on one complete binary point.
theorem generatedAxisGlobalTwelveFifthBindRoot10tTransport_actual :
    generatedAxisGlobalBinaryAct generatedAxisGlobalTwelveFifthBindRoot10tTransport.val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 10)) =
      generatedAxisGlobalBinaryRoot
        (identWordLocal generatedAxisGlobalTwelveFifthBindRoot10tLetters) := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFifthBindRoot10tLetters_root]
  change (generatedAxisGlobalBinaryAct
    ((generatedAxisGlobalFifthGenerator 14).val * (generatedAxisGlobalFifthGenerator 15).val *
      (generatedAxisGlobalFifthGenerator 17).val * (generatedAxisGlobalFifthGenerator 18).val *
      (generatedAxisGlobalFifthGenerator 15).val * (generatedAxisGlobalFifthGenerator 14).val *
      (generatedAxisGlobalFifthGenerator 1).val)
    (generatedAxisGlobalFifthRoot 10)).val = _
  simp only [generatedAxisGlobalBinaryAct_mul]
  simp_rw [generatedAxisGlobalFifthGenerator_binary]
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Five actual generator binary matrices on one complete binary point.
theorem generatedAxisGlobalTwelveFifthBindRoot4tTransport_actual :
    generatedAxisGlobalBinaryAct generatedAxisGlobalTwelveFifthBindRoot4tTransport.val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 4)) =
      generatedAxisGlobalBinaryRoot
        (identWordLocal generatedAxisGlobalTwelveFifthBindRoot4tLetters) := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFifthBindRoot4tLetters_root]
  change (generatedAxisGlobalBinaryAct
    ((generatedAxisGlobalFifthGenerator 18).val * (generatedAxisGlobalFifthGenerator 16).val *
      (generatedAxisGlobalFifthGenerator 10).val * (generatedAxisGlobalFifthGenerator 13).val *
      (generatedAxisGlobalFifthGenerator 9).val)
    (generatedAxisGlobalFifthRoot 4)).val = _
  simp only [generatedAxisGlobalBinaryAct_mul]
  simp_rw [generatedAxisGlobalFifthGenerator_binary]
  decide +kernel

/-! ## Converters -/

private theorem partners_inv_eq (x : GriessSpace) : sExtra⁻¹ x = sExtra (sExtra x) := by
  rw [LinearEquiv.coe_inv]
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_triple]

/-- Root 7 from an inverse identification of the shape of goctad's Eighth root 25 transport
(`sExtra⁻¹ (w · v₈) = (M ++ Root7c) · v₅` with a phase-fixing prefix `M`) and the coverage of
the Eighth family: both triality images at the root word 7. -/
theorem generatedAxisGlobalTwelveFifthBind_root7_of_eighth (w : H) (pre : List IdentLetter)
    (hpre : GeneratedAxisGlobalTwelveFifthBindFixPrefix pre)
    (he : sExtra⁻¹ (rhoLocal w (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal (pre ++ generatedAxisGlobalTwelveFifthBindRoot7cLetters))
        (generatedAxisGlobalTwelveRepresentative 4))
    (h8 : GeneratedAxisGlobalTwelveFamilyCovered 7) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 7) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 7) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, _⟩ := generatedAxisGlobalTwelveFifthBindPrefix_letters hpre.1
  have hn := sixthPhase_mem pre hl hpre.2
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨_, hn⟩
    (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7cLetters) generatedFifthAxis)
  have hw : rhoLocal w (generatedAxisGlobalTwelveRepresentative 7) =
      sExtra (rhoLocal (identWordLocal pre)
        (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7cLetters)
          generatedFifthAxis)) := by
    have h2 := congrArg sExtra he
    rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h2
    rw [h2, identWordLocal_append, map_mul, LinearEquiv.mul_apply]
    rfl
  have hy : sExtra (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7cLetters)
      generatedFifthAxis) = rhoLocal (k⁻¹ * w) (generatedAxisGlobalTwelveRepresentative 7) := by
    rw [map_mul, LinearEquiv.mul_apply, hw, ← hk, map_inv, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
  have hpos := generatedAxisGlobalTwelve_mem_of_transport 7 _ hy
  have hneg : sExtra⁻¹ (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7cLetters)
      generatedFifthAxis) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    rw [partners_inv_eq, hy]
    exact h8 _
  exact generatedAxisGlobalTwelve_root_pair_mem _ generatedFifthAxis _ _
    generatedAxisGlobalTwelveFifthBindRoot7cTransport.val
    generatedAxisGlobalTwelveFifthBindRoot7cTransport.property
    generatedAxisGlobalTwelveFifthBindRoot7cTransport_actual hpos hneg

/-- Root 7 from two identifications at the two-Xi representative `Root7t`. -/
theorem generatedAxisGlobalTwelveFifthBind_root7_of_twoXi (i j : Fin 12) (gp gn : H)
    (hp : sExtra (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7tLetters)
      (generatedAxisGlobalTwelveRepresentative 4)) =
        rhoLocal gp (generatedAxisGlobalTwelveRepresentative i))
    (hn : sExtra⁻¹ (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot7tLetters)
      (generatedAxisGlobalTwelveRepresentative 4)) =
        rhoLocal gn (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 7) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 7) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_root_pair_mem _ generatedFifthAxis _ _
    generatedAxisGlobalTwelveFifthBindRoot7tTransport.val
    generatedAxisGlobalTwelveFifthBindRoot7tTransport.property
    generatedAxisGlobalTwelveFifthBindRoot7tTransport_actual
    (generatedAxisGlobalTwelve_mem_of_transport i gp hp)
    (generatedAxisGlobalTwelve_mem_of_transport j gn hn)

/-- Merged root 10 from either identification at the two-Xi representative `Root10t`. -/
theorem generatedAxisGlobalTwelveFifthBind_root10_of_twoXi (i : Fin 12) (g : H)
    (h : sExtra (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot10tLetters)
        (generatedAxisGlobalTwelveRepresentative 4)) =
          rhoLocal g (generatedAxisGlobalTwelveRepresentative i) ∨
      sExtra⁻¹ (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot10tLetters)
        (generatedAxisGlobalTwelveRepresentative 4)) =
          rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 10) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveFifthBind_merged_of_orbit 6 _
    generatedAxisGlobalTwelveFifthBindRoot10tTransport.val
    generatedAxisGlobalTwelveFifthBindRoot10tTransport.property
    generatedAxisGlobalTwelveFifthBindRoot10tTransport_actual
    (h.imp (generatedAxisGlobalTwelve_mem_of_transport i g)
      (generatedAxisGlobalTwelve_mem_of_transport i g))

/-- Merged root 4 from either identification at the two-Xi representative `Root4t`. -/
theorem generatedAxisGlobalTwelveFifthBind_root4_of_twoXi (i : Fin 12) (g : H)
    (h : sExtra (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot4tLetters)
        (generatedAxisGlobalTwelveRepresentative 4)) =
          rhoLocal g (generatedAxisGlobalTwelveRepresentative i) ∨
      sExtra⁻¹ (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBindRoot4tLetters)
        (generatedAxisGlobalTwelveRepresentative 4)) =
          rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 4) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveFifthBind_merged_of_orbit 2 _
    generatedAxisGlobalTwelveFifthBindRoot4tTransport.val
    generatedAxisGlobalTwelveFifthBindRoot4tTransport.property
    generatedAxisGlobalTwelveFifthBindRoot4tTransport_actual
    (h.imp (generatedAxisGlobalTwelve_mem_of_transport i g)
      (generatedAxisGlobalTwelve_mem_of_transport i g))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
