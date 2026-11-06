/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixGeneric

/-! Certified whole numerator matrices give genuine physical and binary lattice actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The explicit rational numerator constructs an actual whole Co0 element. -/
def generatedTwelfthCertifiedMatrixIsometry (n c ci : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℕ) (hd : d ≠ 0)
    (hl : n.transpose * n = (d * d : ℤ) • 1)
    (hr : n * n.transpose = (d * d : ℤ) • 1)
    (hb : n * leechBasisMatrix = (d : ℤ) • (leechBasisMatrix * c))
    (hi : c * ci = 1) : leechIsomSubgroup :=
  generatedTwelfthMatrixIsometry (generatedTwelfthCertifiedRealMatrix n d) c ci
    (generatedTwelfth_certified_real_left n d hd hl)
    (generatedTwelfth_certified_real_right n d hd hr)
    (generatedTwelfth_certified_real_basis n c d hd hb) hi

/-- Every physical coordinate agrees with the supplied complete rational matrix. -/
theorem generatedTwelfth_certified_isometry_matrix (n c ci : Matrix (Fin 24) (Fin 24) ℤ)
    (d : ℕ) (hd hl hr hb hi) :
    leechIsomMatrix (generatedTwelfthCertifiedMatrixIsometry n c ci d hd hl hr hb hi) =
      generatedTwelfthCertifiedRealMatrix n d := by
  ext i j
  change (generatedTwelfthCertifiedRealMatrix n d *ᵥ (Pi.single j 1)) i = _
  simp

/-- The actual whole physical isometry retains the exact integer numerator and denominator. -/
theorem generatedTwelfth_certified_isometry_numerator
    (n c ci : Matrix (Fin 24) (Fin 24) ℤ) (d : ℕ) (hd hl hr hb hi) :
    (d : ℝ) • leechIsomMatrix
      (generatedTwelfthCertifiedMatrixIsometry n c ci d hd hl hr hb hi) =
        n.map (Int.castRingHom ℝ) := by
  rw [generatedTwelfth_certified_isometry_matrix, generatedTwelfthCertifiedRealMatrix,
    smul_smul]
  have hz : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [mul_inv_cancel₀ hz, one_smul]

/-- Every original binary coordinate is the exact lattice-basis action of the constructed lift. -/
theorem generatedTwelfth_certified_isometry_binary
    (n c ci : Matrix (Fin 24) (Fin 24) ℤ) (d : ℕ) (hd hl hr hb hi)
    (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedTwelfthCertifiedMatrixIsometry n c ci d hd hl hr hb hi) v =
      (leechHyperbolicInverse * c.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ v := by
  exact generatedTwelfth_spatial_binary_of_matrix _ n c d hd
    (generatedTwelfth_certified_isometry_numerator n c ci d hd hl hr hb hi) hb v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
