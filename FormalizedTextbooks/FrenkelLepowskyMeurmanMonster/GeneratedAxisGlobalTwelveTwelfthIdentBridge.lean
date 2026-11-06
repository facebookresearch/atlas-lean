/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthLink
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceFiber

/-! The Twelfth root words in the packed-identification alphabet.

Each original odd-family source letter is written as a word of `IdentLetter`s with the same
Conway projection: Xi, the code signs 16 and 32 and the four permutation letters translate
exactly, the inverse Xi as Xi twice, and the inverse code signs as the code signs (equal
projection). Hence every translated Twelfth root word has the actual binary root of the original
root word, and a binding of both triality images at the translated word binds the root word.
`generatedAxisGlobalTwelve_twelfth_covered_of_ident` states Twelfth-family coverage with
hypotheses phrased at the translated words, the form produced by identifications in this
alphabet. No identification is asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- The identification-alphabet word of an original odd-family source letter. -/
def generatedAxisGlobalTwelveTwelfthIdentOf : Fin 10 → List IdentLetter :=
  ![[.xi], [.xi, .xi], [.sign 16 0], [.sign 16 0], [.sign 32 0], [.sign 32 0],
    [.mono (0, false)], [.mono (0, true)], [.mono (1, false)], [.mono (1, true)]]

/-- The identification-alphabet word of a Twelfth root word. -/
def generatedAxisGlobalTwelveTwelfthRootIdentWord (k : Fin 38) : List IdentLetter :=
  (generatedAxisGlobalTwelveTwelfthRootLetters k).flatMap generatedAxisGlobalTwelveTwelfthIdentOf

/-- Every Golay sign isometry is an involution. -/
theorem generatedAxisGlobalTwelveTwelfth_golaySign_sq (d : golayCode) :
    golaySignIsometry d * golaySignIsometry d = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  change golayRealSign d.val (golayRealSign d.val x) i = x i
  rw [golayRealSign_apply, golayRealSign_apply, ← mul_assoc, qSign_sq]
  exact one_mul _

/-- The projection of a source code sign letter is an involution. -/
theorem generatedAxisGlobalTwelveTwelfth_sign_projection_inv (a : Fin 4096) :
    (projH (generatedFifthSignLocal a 0))⁻¹ = projH (generatedFifthSignLocal a 0) := by
  rw [generatedFifth_sign_local_projection, ← QuotientGroup.mk_inv,
    inv_eq_of_mul_eq_one_left (generatedAxisGlobalTwelveTwelfth_golaySign_sq _)]

/-- The local Xi has cube one. -/
theorem generatedAxisGlobalTwelveTwelfth_xi_sq :
    localFiberIntoH xiSpinLocalFiber * localFiberIntoH xiSpinLocalFiber =
      (localFiberIntoH xiSpinLocalFiber)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, show xiSpinLocalFiber * xiSpinLocalFiber * xiSpinLocalFiber =
    xiSpinLocalFiber ^ 3 by rw [pow_three, mul_assoc], xiSpinLocalFiber_cube, map_one]

set_option maxRecDepth 20000 in
/-- Each translated letter has the Conway projection of the original source letter. -/
theorem generatedAxisGlobalTwelveTwelfthIdentOf_projection (l : Fin 10) :
    projH (identWordLocal (generatedAxisGlobalTwelveTwelfthIdentOf l)) =
      projH (generatedAxisGlobalOddSourceLocalLetter l) := by
  rw [← generatedAxisGlobalOddSourceFiberLetter_local]
  fin_cases l
  · rfl
  · change projH (localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber)) =
      projH (localFiberIntoH xiSpinLocalFiber⁻¹)
    rw [map_mul, generatedAxisGlobalTwelveTwelfth_xi_sq]
    simp only [map_inv]
  · rfl
  · change projH (localFiberIntoH (generatedFifthSignFiber 16 0)) =
      projH (localFiberIntoH (generatedFifthSignFiber 16 0)⁻¹)
    rw [map_inv, map_inv, generatedFifth_sign_fiber_local,
      generatedAxisGlobalTwelveTwelfth_sign_projection_inv]
  · rfl
  · change projH (localFiberIntoH (generatedFifthSignFiber 32 0)) =
      projH (localFiberIntoH (generatedFifthSignFiber 32 0)⁻¹)
    rw [map_inv, map_inv, generatedFifth_sign_fiber_local,
      generatedAxisGlobalTwelveTwelfth_sign_projection_inv]
  · rfl
  · rfl
  · rfl
  · rfl

/-- A flattened word has the product of the words of its letters as local element. -/
theorem generatedAxisGlobalTwelveTwelfth_identWordLocal_flatMap (ls : List (Fin 10)) :
    identWordLocal (ls.flatMap generatedAxisGlobalTwelveTwelfthIdentOf) =
      (ls.map fun l => identWordLocal (generatedAxisGlobalTwelveTwelfthIdentOf l)).prod := by
  induction ls with
  | nil => simp [identWordLocal, identWordFiber]
  | cons l ls ih =>
    rw [List.flatMap_cons, identWordLocal_append, ih, List.map_cons, List.prod_cons]

/-- Every translated root word has the Conway projection of the original root word. -/
theorem generatedAxisGlobalTwelveTwelfthRootIdentWord_projection (k : Fin 38) :
    projH (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k)) =
      projH (generatedAxisGlobalTwelveTwelfthRootWord k) := by
  rw [generatedAxisGlobalTwelveTwelfthRootIdentWord,
    generatedAxisGlobalTwelveTwelfth_identWordLocal_flatMap,
    generatedAxisGlobalTwelveTwelfthRootWord,
    map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  exact generatedAxisGlobalTwelveTwelfthIdentOf_projection l

/-- Every translated root word has the actual binary root of the original root word. -/
theorem generatedAxisGlobalTwelveTwelfthRootIdentWord_binaryRoot (k : Fin 38) :
    generatedAxisGlobalBinaryRoot
        (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k)) =
      generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTwelfthRootWord k) := by
  apply Subtype.ext
  change co1BinaryAction
      (projH (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k))⁻¹)
      (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
    co1BinaryAction (projH (generatedAxisGlobalTwelveTwelfthRootWord k)⁻¹)
      (Multiplicative.toAdd (qQuotHom sourceOmegaQ))
  simp only [map_inv]
  rw [generatedAxisGlobalTwelveTwelfthRootIdentWord_projection]

/-- Both triality images at a translated root word bind both images at the root word. -/
theorem generatedAxisGlobalTwelveTwelfth_root_pair_of_ident {ι : Type*} (u : ι → GriessSpace)
    (k : Fin 38)
    (hpos : sExtra (rhoLocal (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k))
      generatedTwelfthAxis) ∈ generatedLocalOrbitUnion u)
    (hneg : sExtra⁻¹ (rhoLocal (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k))
      generatedTwelfthAxis) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion u ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion u := by
  apply generatedAxisGlobalTwelve_root_pair_mem u generatedTwelfthAxis
    (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k))
    (generatedAxisGlobalTwelveTwelfthRootWord k) 1
    (by rw [map_one, LinearEquiv.coe_one, id_eq]) _ hpos hneg
  rw [generatedAxisGlobalTwelveTwelfthRootIdentWord_binaryRoot]
  apply Subtype.ext
  change co1BinaryAction (projH 1) _ = _
  rw [map_one, map_one]
  rfl

/-- Twelfth-family coverage from both images at the thirty-seven translated root words. -/
theorem generatedAxisGlobalTwelve_twelfth_covered_of_ident
    (h : ∀ k ∈ generatedAxisGlobalTwelveTwelfthOpenRoots,
      sExtra (rhoLocal (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k))
        generatedTwelfthAxis) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k))
        generatedTwelfthAxis) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 10 :=
  generatedAxisGlobalTwelve_twelfth_covered_of
    (fun k hk => (generatedAxisGlobalTwelveTwelfth_root_pair_of_ident _ k (h k hk).1 (h k hk).2).1)
    (fun k hk => (generatedAxisGlobalTwelveTwelfth_root_pair_of_ident _ k (h k hk).1 (h k hk).2).2)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
