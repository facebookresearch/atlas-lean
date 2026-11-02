/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Global-local valuation ring compatibility

This file gives the precise, typed form of the identity `R_{(p)} = R_p ∩ K`: the localization
valuation subring inside a fraction field is the preimage of the valuation ring in its adic
completion along the canonical embedding.

## References

* [S. Anscombe et al., *A survey of local-global methods for Hilbert's Tenth
  Problem*](https://arxiv.org/abs/2309.14987v1)
* [G. Hu, *Anisotropy of quadratic forms over global fields of characteristic ≠ 2 is
  diophantine*](https://arxiv.org/abs/2401.00537v3)
-/

@[expose] public section

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Localization at a prime as a preimage of the completed valuation ring.** Let $R$ be a
Dedekind domain with fraction field $K$, let $v$ be a height-one prime of $R$, and let
$\mathcal{O}_v$ be the valuation ring of the $v$-adic completion $K_v$ of $K$. Then the
localization $R_v$ of $R$ at $v$, viewed as a subring of $K$, is the preimage of $\mathcal{O}_v$
under the canonical embedding $K \to K_v$. -/
theorem valuationSubringAtPrime_eq_comap_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (valuationSubringAtPrime (K := K) v).toSubring =
      Subring.comap (algebraMap K (adicCompletion K v))
        (adicCompletionIntegers K v).toSubring := by
  ext x
  simp only [Subring.mem_comap, ValuationSubring.mem_toSubring]
  simp only [valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff]
  rw [mem_adicCompletionIntegers]
  change (valuation K v) x ≤ 1 ↔ Valued.v (x : adicCompletion K v) ≤ 1
  rw [valuedAdicCompletion_eq_valuation']

end IsDedekindDomain.HeightOneSpectrum
