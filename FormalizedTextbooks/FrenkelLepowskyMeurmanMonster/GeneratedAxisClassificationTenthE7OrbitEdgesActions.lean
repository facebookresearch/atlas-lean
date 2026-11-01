/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7XiRootMove

/-! Full genuine integral action behind each certified original root-orbit edge. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual lattice root at each original traversal address. -/
def generatedTenthE7OrbitNodeRoot (n : Fin 63) : leechIntegral :=
  generatedTenthE7StandardE8Root
    (generatedTenthE7OrbitRootIndex (generatedTenthE7OrbitOrder n))

/-- Its entire integral coordinate vector is the original literal source vector. -/
theorem generatedTenth_e7_orbit_node_physical (n : Fin 63) :
    (generatedTenthE7OrbitNodeRoot n).val = generatedTenthE7OrbitNodeVector n :=
  generatedTenth_e7_standard_e8_root_physical _

/-- The actual two correcting lattice isometries, with their original orientation. -/
def generatedTenthE7OrbitSpatialLetter (k : Fin 2) : leechIsomSubgroup :=
  if k = 0 then generatedTenthE7XiCorrection else generatedTenthE7OrbitMonoSpatial

private theorem xi_embedding (u v : Fin 24 → ℤ)
    (h : generatedTenthE7XiCorrectedNumerator *ᵥ u = (2 : ℤ) • v) :
    generatedTenthE7XiCorrection.val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding v := by
  rw [generatedTenth_e7_xi_correction_apply, ← leechCoordinateEmbedding_mulVec, h]
  ext i
  change (1 / 2 : ℝ) * (((2 * v i : ℤ) : ℝ) / Real.sqrt 8) =
    (v i : ℝ) / Real.sqrt 8
  push_cast
  ring

private theorem letter_embedding (k : Fin 2) (u v : Fin 24 → ℤ)
    (h : generatedTenthE7OrbitLetterNumerator k *ᵥ u =
      generatedTenthE7OrbitLetterDenominator k • v) :
    (generatedTenthE7OrbitSpatialLetter k).val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding v := by
  by_cases hk : k = 0
  · simp only [generatedTenthE7OrbitLetterNumerator,
      generatedTenthE7OrbitLetterDenominator, ite_eq_left hk] at h
    simp only [generatedTenthE7OrbitSpatialLetter, ite_eq_left hk]
    exact xi_embedding u v h
  · simp only [generatedTenthE7OrbitLetterNumerator,
      generatedTenthE7OrbitLetterDenominator, ite_eq_right hk, one_smul] at h
    simp only [generatedTenthE7OrbitSpatialLetter, ite_eq_right hk]
    rw [generatedTenth_e7_orbit_mono_apply, ← leechCoordinateEmbedding_mulVec, h]

/-- The unchanged full integer edge certificate implies the genuine actual integral image. -/
theorem generatedTenth_e7_orbit_edge_integral (n : Fin 63)
    (h : generatedTenthE7OrbitEdgeCondition n) :
    leechIntegralAction (generatedTenthE7OrbitSpatialLetter (generatedTenthE7OrbitLetter n))
      (generatedTenthE7OrbitNodeRoot (generatedTenthE7OrbitParent n)) =
        generatedTenthE7OrbitSign n • generatedTenthE7OrbitNodeRoot n := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding, generatedTenth_e7_orbit_node_physical]
  change _ = leechCoordinateEmbedding
    (generatedTenthE7OrbitSign n • (generatedTenthE7OrbitNodeRoot n).val)
  rw [generatedTenth_e7_orbit_node_physical]
  apply letter_embedding
  exact (show generatedTenthE7OrbitLetterNumerator (generatedTenthE7OrbitLetter n) *ᵥ
    generatedTenthE7OrbitNodeVector (generatedTenthE7OrbitParent n) =
      (generatedTenthE7OrbitLetterDenominator (generatedTenthE7OrbitLetter n) *
        generatedTenthE7OrbitSign n) • generatedTenthE7OrbitNodeVector n from h).trans
    (mul_smul _ _ _)

/-- Every original orientation is one of the two genuine root signs. -/
theorem generatedTenth_e7_orbit_sign : ∀ n : Fin 63,
    generatedTenthE7OrbitSign n = 1 ∨ generatedTenthE7OrbitSign n = -1 := by
  decide +kernel

/-- The actual quotient class at each complete original traversal address. -/
def generatedTenthE7OrbitNodeClass (n : Fin 63) : LeechModTwo :=
  leechReduction (generatedTenthE7OrbitNodeRoot n)

/-- Every entire signed integer edge gives the genuine action on the original short class. -/
theorem generatedTenth_e7_orbit_edge_class (n : Fin 63)
    (h : generatedTenthE7OrbitEdgeCondition n) :
    leechModTwoAction (generatedTenthE7OrbitSpatialLetter (generatedTenthE7OrbitLetter n))
      (generatedTenthE7OrbitNodeClass (generatedTenthE7OrbitParent n)) =
        generatedTenthE7OrbitNodeClass n := by
  change leechReduction (leechIntegralAction _ _) = _
  rw [generatedTenth_e7_orbit_edge_integral n h]
  rcases generatedTenth_e7_orbit_sign n with hs | hs
  · rw [hs, one_smul]
    rfl
  · rw [hs, neg_one_smul, leechReduction_neg]
    rfl

/-- The complete original preferred short label of each traversal root. -/
def generatedTenthE7OrbitNodeLabel (n : Fin 63) : GriessShortIndex :=
  (generatedTenthE7StandardE8RootLabelEquiv
    (generatedTenthE7OrbitRootIndex (generatedTenthE7OrbitOrder n))).val

/-- Each original root class is exactly its actual preferred short class. -/
theorem generatedTenth_e7_orbit_node_class_actual (n : Fin 63) :
    generatedTenthE7OrbitNodeClass n = griessShortClass (generatedTenthE7OrbitNodeLabel n) := by
  rcases generatedTenth_e7_standard_e8_root_label_sign
      (generatedTenthE7OrbitRootIndex (generatedTenthE7OrbitOrder n)) with h | h
  · change leechReduction (generatedTenthE7StandardE8Root _) = _
    rw [h]
    rfl
  · change leechReduction (generatedTenthE7StandardE8Root _) = _
    rw [h, leechReduction_neg]
    rfl

/-- All sixty-three original traversal classes are distinct actual short classes. -/
theorem generatedTenth_e7_orbit_node_class_injective :
    Function.Injective generatedTenthE7OrbitNodeClass := by
  intro i j h
  apply generatedTenth_e7_orbit_order_injective
  apply generatedTenth_e7_orbit_root_index_injective
  apply generatedTenthE7StandardE8RootLabelEquiv.injective
  apply Subtype.ext
  apply griessShortClass_injective
  exact (generatedTenth_e7_orbit_node_class_actual i).symm.trans
    (h.trans (generatedTenth_e7_orbit_node_class_actual j))

/-- The genuine standard normal root, with its original positive orientation. -/
def generatedTenthE7OrbitNormalRoot : leechIntegral :=
  ⟨generatedTenthE7XiNormal, generatedTenth_e7_xi_integral_of_balanced_four _
    (by decide +kernel) (by decide +kernel)⟩

/-- Both actual correcting letters fix the normal root with its positive orientation. -/
theorem generatedTenth_e7_orbit_letter_normal (k : Fin 2) :
    leechIntegralAction (generatedTenthE7OrbitSpatialLetter k)
      generatedTenthE7OrbitNormalRoot = generatedTenthE7OrbitNormalRoot := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  by_cases hk : k = 0
  · simp only [generatedTenthE7OrbitSpatialLetter, ite_eq_left hk]
    exact generatedTenth_e7_xi_correction_normal
  · simp only [generatedTenthE7OrbitSpatialLetter, ite_eq_right hk]
    exact generatedTenth_e7_orbit_mono_normal

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
