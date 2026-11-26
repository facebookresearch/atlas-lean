/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Exp
public import PhyslibExt.BiomedicalImaging.PhotonObservation.Law

/-!
# Photon observation on a finite CT design

## i. Overview

The monochromatic photon law instantiated with a finite CT
design matrix: coefficient vectors with the same design
measurement have the same transmitted intensity at every ray,
and the rank-deficient design `[1, 1]` has an explicit
admissible nonnegative nullspace pair.

## ii. Key results

* `ct_nullspace_pair`: the admissible pair `(1, 0)`, `(0, 1)`.
* `ct_equal_rates`: equal transmitted intensities for the pair.
* `PhotonObservation.transmittedRate_eq_of_mulVec_eq`: the general agreement law (in the photon-law API).

## iii. Table of contents

* A. The nullspace pair and rate agreement.
-/

@[expose] public section

open Matrix
open scoped NNReal

namespace PhyslibExt.BiomedicalImaging.PhotonCTInstance

/-! ## A. The nullspace pair and rate agreement. -/

/-- The rank-deficient two-cell single-ray CT design `[1, 1]`. -/
def ctRow : Matrix (Fin 1) (Fin 2) ℝ := ![![1, 1]]

/-- **Admissible nullspace pair.** For the single-ray design `ctRow = [1, 1]`, the
nonnegative coefficient vectors `(1, 0)` and `(0, 1)` are distinct but have the same
forward measurement `1`. -/
lemma ct_nullspace_pair :
    ctRow *ᵥ ![1, 0] = ctRow *ᵥ ![0, 1] ∧ (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] ∧
      (∀ i, 0 ≤ (![1, 0] : Fin 2 → ℝ) i) ∧ (∀ i, 0 ≤ (![0, 1] : Fin 2 → ℝ) i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i
    simp [ctRow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · intro i
    fin_cases i <;> simp
  · intro i
    fin_cases i <;> simp

/-- **Equal transmitted rates.** The pair has the same
transmitted Poisson rate at nonnegative incident intensities. -/
lemma ct_equal_rates (I0 : Fin 1 → ℝ≥0) :
    PhyslibExt.BiomedicalImaging.PhotonObservation.transmittedRate I0 ctRow ![1, 0] (0 : Fin 1) =
      PhyslibExt.BiomedicalImaging.PhotonObservation.transmittedRate I0 ctRow ![0, 1] (0 : Fin 1) := by
  unfold PhyslibExt.BiomedicalImaging.PhotonObservation.transmittedRate
  rw [ct_nullspace_pair.1]

/-- **Equal photon laws.** For arbitrary nonnegative source intensities,
the pair has the same independent-Poisson photon law. -/
lemma ct_photon_law_pair (I0 : Fin 1 → ℝ≥0) :
    PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw I0 ctRow ![1, 0] =
      PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw I0 ctRow ![0, 1] := by
  unfold PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw
    PhyslibExt.BiomedicalImaging.PhotonObservation.transmittedRate
  rw [ct_nullspace_pair.1]

/-- **Non-identification on the nonnegative orthant.** The
photon law for the design `[1, 1]` is not injective on
nonnegative coefficient vectors. -/
lemma ct_photon_not_identified (I0 : Fin 1 → ℝ≥0) :
    ¬ Set.InjOn (fun x => PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw I0 ctRow x)
      {x : Fin 2 → ℝ | ∀ i, 0 ≤ x i} := by
  apply PhyslibExt.BiomedicalImaging.PhotonObservation.photon_not_identify_of_kernel
    ctRow _ (x := ![1, 0]) (v := ![-1, 1])
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · ext i
    fin_cases i
    simp [ctRow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> simp
  · show ∀ i, 0 ≤ (![1, 0] + ![-1, 1] : Fin 2 → ℝ) i
    intro i
    fin_cases i <;> simp

end PhyslibExt.BiomedicalImaging.PhotonCTInstance
