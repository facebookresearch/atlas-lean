/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixBinaryCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactCompatibility

/-! Complete certified physical matrices yield genuine local compact lifts with the source classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact rational matrix is an actual complete lattice isometry. -/
def generatedTwelfthCertifiedSpatial (g : Fin 12) : leechIsomSubgroup :=
  generatedTwelfthCertifiedMatrixIsometry
    (generatedTwelfthCertifiedNumerator g) (generatedTwelfthCertifiedIntegral g)
    (generatedTwelfthCertifiedIntegralInverse g) (generatedTwelfthCertifiedDenominator g)
    (generatedTwelfth_certified_denominator_ne_zero g)
    (generatedTwelfth_certified_orthogonal_left g)
    (generatedTwelfth_certified_orthogonal_right g)
    (generatedTwelfth_certified_basis g) (generatedTwelfth_certified_integral_inverse g)

/-- The complete physical matrix of each constructed lift is exactly its rational numerator. -/
theorem generatedTwelfth_certified_spatial_matrix (g : Fin 12) :
    leechIsomMatrix (generatedTwelfthCertifiedSpatial g) =
      generatedTwelfthCertifiedRealMatrix (generatedTwelfthCertifiedNumerator g)
        (generatedTwelfthCertifiedDenominator g) :=
  generatedTwelfth_certified_isometry_matrix _ _ _ _ _ _ _ _ _

/-- Every constructed spatial lift has its genuine full binary source columns. -/
theorem generatedTwelfth_certified_spatial_binary_generator (g : Fin 12) (j : Fin 24) :
    leechBinaryAction (generatedTwelfthCertifiedSpatial g)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j) := by
  unfold generatedTwelfthCertifiedSpatial
  rw [generatedTwelfth_certified_isometry_binary]
  exact generatedTwelfth_certified_matrix_binary_columns g j

private theorem binary_equiv_eq_of_columns
    (e f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (h : ∀ j : Fin 24,
      e (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        f (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val))) : e = f := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  simpa only [Pi.basisFun_apply, generatedTwelfth_spin_compact_binary_basis] using h j

/-- The actual compact spin factor is compatible with the complete constructed spatial lift. -/
theorem generatedTwelfth_certified_spatial_compatibility (g : Fin 12) :
    spinBinaryAction (generatedTwelfthSpinCompact g) =
      leechBinaryAction (generatedTwelfthCertifiedSpatial g) := by
  exact binary_equiv_eq_of_columns _ _ (fun j =>
    (generatedTwelfth_spin_compact_binary_generator_actual g j).trans
      (generatedTwelfth_certified_spatial_binary_generator g j).symm)

/-- The exact physical candidate and actual compact spin factor define a genuine local fiber. -/
def generatedTwelfthCertifiedFiber (g : Fin 12) : localFiberSubgroup :=
  ⟨(generatedTwelfthSpinCompact g, generatedTwelfthCertifiedSpatial g),
    generatedTwelfth_certified_spatial_compatibility g⟩

/-- The complete certified compact candidate is an actual local group element. -/
def generatedTwelfthCertifiedLocal (g : Fin 12) : H :=
  localFiberIntoH (generatedTwelfthCertifiedFiber g)

/-- Binary faithfulness identifies the exact original source Conway class of the candidate. -/
theorem generatedTwelfth_certified_spatial_source_projection (g : Fin 12) :
    (QuotientGroup.mk (generatedTwelfthCertifiedSpatial g) : Co1) =
      QuotientGroup.mk (generatedTwelfthSpinCompactSpatial g) := by
  apply co1BinaryAction_injective
  change leechBinaryAction (generatedTwelfthCertifiedSpatial g) =
    leechBinaryAction (generatedTwelfthSpinCompactSpatial g)
  exact (generatedTwelfth_certified_spatial_compatibility g).symm.trans
    (generatedTwelfth_spin_compact_compatibility g)

/-- Every constructed compact local lift projects to the complete original source class. -/
theorem generatedTwelfth_certified_local_source_projection (g : Fin 12) :
    projH (generatedTwelfthCertifiedLocal g) =
      (QuotientGroup.mk (generatedTwelfthSpinCompactSpatial g) : Co1) :=
  generatedTwelfth_certified_spatial_source_projection g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
