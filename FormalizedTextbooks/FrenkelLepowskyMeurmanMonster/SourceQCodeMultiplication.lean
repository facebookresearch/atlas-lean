/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The actual code-generator multiplication law from Seysen (5.3.3).
The integral XOR carry supplies the intersection cocode, and the proved
Parker polarization supplies the central phase. This checks the source-word
normalization beyond individual generators and their squares.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
-- The named Q is the concrete cocycle extension.
set_option backward.isDefEq.respectTransparency false

/-- The intersection cocode A(d,e) in the published source group law. -/
def sourceCodeIntersectionCocode (d e : Fin 4096) : Fin 12 → ZMod 2 :=
  golaySyndrome (integerParity (sourceCodeIntersection d e))

private theorem qBeta_code_code (d e : Fin 4096) :
    qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients d))
      (sourceExpectedCodeCoordinates (golayLabelCoefficients e)) =
      spinDot (sourceWordTheta e) (golayLabelCoefficients d) := by
  rw [sourceWordTheta_polynomial]
  simp only [qBeta, sourceExpectedCodeCoordinates, Fin.append_left, Fin.append_right,
    spinDot, mul_comm]

private theorem qBeta_code_cocode (d : Fin 4096) (δ : Fin 12 → ZMod 2) :
    qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients d))
      (binaryCocodeEmbedding δ) = spinDot δ (golayLabelCoefficients d) := by
  simp only [qBeta, sourceExpectedCodeCoordinates, Fin.append_left,
    binaryCocodeEmbedding_right, spinDot, mul_comm]

private theorem sourceCodeCoordinates_sum (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    sourceExpectedCodeCoordinates (golayLabelCoefficients d) +
      sourceExpectedCodeCoordinates (golayLabelCoefficients e) =
      sourceExpectedCodeCoordinates (golayLabelCoefficients f) +
        binaryCocodeEmbedding (sourceCodeIntersectionCocode d e) := by
  have h := sourceCodeCoordinates_add (golayLabelCoefficients d) (golayLabelCoefficients e)
  rw [← hf, sourceCodeCoordinates_eq, sourceCodeCoordinates_eq,
    sourceCodeCoordinates_eq, ← sourceCodeIntersection_parity d e] at h
  have hz (v : Fin 24 → ZMod 2) : v + v = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero _
  have h' := congrArg (fun v => v + binaryCocodeEmbedding (sourceCodeIntersectionCocode d e)) h
  simpa only [sourceCodeIntersectionCocode, add_assoc, hz, add_zero] using h'.symm

/-- The source multiplication x_d x_e = x_de x_A(d,e), including the Parker
sign in de. All terms are elements of the actual coordinate group Q. -/
theorem sourceQCode_mul (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e)
    (ε η : ZMod 2) :
    sourceQCode d ε * sourceQCode e η =
      sourceQCode f (ε + η + spinDot (sourceWordTheta d) (golayLabelCoefficients e)) *
        sourceQCocode (sourceCodeIntersectionCocode d e) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact sourceCodeCoordinates_sum d e f hf
  · apply toAdd.injective
    change (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) +
      (η + (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)) +
      qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients d))
        (sourceExpectedCodeCoordinates (golayLabelCoefficients e)) =
      (ε + η + spinDot (sourceWordTheta d) (golayLabelCoefficients e) +
        (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ)) + 0 +
      qBeta (sourceExpectedCodeCoordinates (golayLabelCoefficients f))
        (binaryCocodeEmbedding (sourceCodeIntersectionCocode d e))
    rw [qBeta_code_code, qBeta_code_cocode, hf, sourceCodeIntersectionCocode,
      sourceCodeIntersection_dot_sum, add_zero, add_zero]
    have hc := sourceWordTheta_cross_dot d e f hf
    linear_combination (norm := skip) -hc
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero]

/-- The same checked source relation in the actual generated group G. -/
theorem sourceGeneratedCode_mul (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e)
    (ε η : ZMod 2) :
    sourceGeneratedCode d ε * sourceGeneratedCode e η =
      sourceGeneratedCode f (ε + η + spinDot (sourceWordTheta d) (golayLabelCoefficients e)) *
        sourceGeneratedCocode (sourceCodeIntersectionCocode d e) := by
  simp only [sourceGeneratedCode, sourceGeneratedCocode, ← map_mul, sourceQCode_mul d e f hf]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
