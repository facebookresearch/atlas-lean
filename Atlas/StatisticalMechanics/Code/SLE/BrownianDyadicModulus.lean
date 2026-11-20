/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianModificationLaw









open Filter MeasureTheory Set
open scoped ENNReal

namespace StatMech.SLE




theorem brownianContinuousModification_ae_dyadicModulus :
    ∀ᵐ omega ∂brownianProductLaw, ∀ N : Nat, ∃ n0 : Nat,
      ∀ n, n0 <= n -> ∀ s ∈ Icc (-(N : Real)) N,
        ∀ t ∈ Icc (-(N : Real)) N,
          dist s t < ((brownianDyadicDenominator n : Nat) : Real)⁻¹ ->
            edist (brownianContinuousModification s omega)
                (brownianContinuousModification t omega) <=
              (513 : ENNReal) * brownianDyadicThreshold n := by
  filter_upwards [
    brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt]
      with omega hgood
  intro N
  obtain ⟨n0, hn0⟩ := (eventually_atTop.1 (hgood N))
  refine ⟨n0, ?_⟩
  intro n hn s hs t ht hclose
  rw [brownianContinuousModification_eq_dyadicLimit omega N hs.1 hs.2,
    brownianContinuousModification_eq_dyadicLimit omega N ht.1 ht.2]
  exact edist_brownianDyadicLimit_le omega N n
    hs.1 hs.2 ht.1 ht.2 hclose
      (fun m hm => hn0 m (hn.trans hm))

end StatMech.SLE
