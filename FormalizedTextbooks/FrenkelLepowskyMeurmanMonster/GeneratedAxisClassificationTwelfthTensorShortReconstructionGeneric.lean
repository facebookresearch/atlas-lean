/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSpatialTensor

/-! Signed short coefficients reconstructed from tensor Pauli traces
are fixed by every tensor fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The complete Pauli tensor trace uses the actual preferred extraspecial short lift. -/
def generatedTwelfthTensorPauliTrace (T : SpinIndex → Fin 24 → ℝ)
    (r : GriessShortIndex) : ℝ :=
  conwayTensorForm (localTensorRepresentation (localFiberIncl (griessShortQ r)) T) T

private theorem central_tensor_scalar (c : ZMod 2) (T : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation (localFiberIncl (qCentral c)) T = qSign c • T := by
  ext t i
  rw [generatedFourth_local_tensor_columns]
  change (∑ j : Fin 24, (Pi.single j (1 : ℝ) : Fin 24 → ℝ) i *
    (spinRepresentation (qCentral c) (fun u => T u j)) t) = qSign c * T t i
  simp [spinRepresentation_central, Pi.single_apply]

/-- Every genuine local action transports full Pauli traces
with its actual signed-short phase. -/
theorem generatedTwelfth_tensor_pauli_trace_covariant (f : localFiberSubgroup)
    (T : SpinIndex → Fin 24 → ℝ) (r : GriessShortIndex) :
    generatedTwelfthTensorPauliTrace (localTensorRepresentation f T)
      (griessShortPermutation f.val.2 r) =
        qSign (localShortPhase f r) * generatedTwelfthTensorPauliTrace T r := by
  have ha : localTensorRepresentation f
      (localTensorRepresentation (localFiberIncl (griessShortQ r)) T) =
        localTensorRepresentation (localFiberIncl (spinConjugation f.val.1 (griessShortQ r)))
          (localTensorRepresentation f T) := by
    rw [localFiberIncl_conjugate, map_mul, map_mul, map_inv]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [griessShortQ_image, map_mul, map_mul, LinearEquiv.mul_apply,
    central_tensor_scalar] at ha
  have hp := localTensorRepresentation_pairing f
    (localTensorRepresentation (localFiberIncl (griessShortQ r)) T) T
  rw [ha] at hp
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hp
  change qSign (localShortPhase f r) *
    generatedTwelfthTensorPauliTrace (localTensorRepresentation f T)
      (griessShortPermutation f.val.2 r) = generatedTwelfthTensorPauliTrace T r at hp
  calc
    generatedTwelfthTensorPauliTrace (localTensorRepresentation f T)
        (griessShortPermutation f.val.2 r) =
        qSign (localShortPhase f r) * (qSign (localShortPhase f r) *
          generatedTwelfthTensorPauliTrace (localTensorRepresentation f T)
            (griessShortPermutation f.val.2 r)) := by rw [← mul_assoc, qSign_sq, one_mul]
    _ = qSign (localShortPhase f r) * generatedTwelfthTensorPauliTrace T r := by rw [hp]

/-- An odd scalar reconstruction of all short coefficients turns every full tensor fixer
into a full signed-short fixer. -/
theorem generatedTwelfth_tensor_fixer_short_reconstruction (f : localFiberSubgroup)
    (T : SpinIndex → Fin 24 → ℝ) (C : GriessShortIndex → ℝ) (F : ℝ → ℝ)
    (hodd : ∀ x, F (-x) = -F x)
    (hsource : ∀ r, C r = F (generatedTwelfthTensorPauliTrace T r))
    (hfix : localTensorRepresentation f T = T) : localShortRepresentation f C = C := by
  have hF (c : ZMod 2) (x : ℝ) : F (qSign c * x) = qSign c * F x := by
    fin_cases c
    · change F (qSign (0 : ZMod 2) * x) = qSign (0 : ZMod 2) * F x
      simp only [qSign_zero, one_mul]
    · change F (qSign (1 : ZMod 2) * x) = qSign (1 : ZMod 2) * F x
      simp only [qSign_one, neg_one_mul, hodd]
  ext s
  obtain ⟨r, rfl⟩ := (griessShortPermutation f.val.2).surjective s
  change localShortOperator f C (griessShortPermutation f.val.2 r) = _
  rw [localShortOperator_image, hsource, hsource]
  have hc := generatedTwelfth_tensor_pauli_trace_covariant f T r
  rw [hfix] at hc
  rw [hc, hF]

/-- An explicit odd candidate reconstruction on the thirteen observed trace values.
The complete actual source identity is a separate finite certificate obligation. -/
def generatedTwelfthTensorTraceShortLookup (x : ℝ) : ℝ :=
  (if x * x = 1 / 4 then -(1 / 8 : ℝ)
    else if x * x = 9 / 4 then (1 / 24 : ℝ)
    else if x * x = 169 / 4 then (1 / 104 : ℝ)
    else if x * x = 49 / 16 then (1 / 56 : ℝ)
    else if x * x = 169 / 16 then (3 / 104 : ℝ)
    else if x * x = 361 / 16 then (1 / 152 : ℝ)
    else 0) * x

/-- The candidate reconstruction preserves every actual signed phase on all real inputs. -/
theorem generatedTwelfth_tensor_trace_short_lookup_odd (x : ℝ) :
    generatedTwelfthTensorTraceShortLookup (-x) =
      -generatedTwelfthTensorTraceShortLookup x := by
  have hxx : (-x) * (-x) = x * x := by ring
  unfold generatedTwelfthTensorTraceShortLookup
  simp only [hxx]
  rw [mul_neg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
