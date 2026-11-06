/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootMaskAction
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskEncode

/-! Exact whole-mask certificates can use original preferred-Q coordinates directly. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Complete encoded binary and central identities certify the actual preferred-Q transport. -/
theorem generatedAxisGlobalOddRootMaskCheck_actual (k : Fin 9)
    (hk : ∀ i, generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k)
      (qCoordinateGenerator i) =
      generatedAxisGlobalOddRootQCache k i) (q r : Q) (c : ZMod 2)
    (hq : q.coeff = 1) (hr : r.coeff = 1)
    (hb : generatedAxisGlobalQMaskVector (generatedAxisGlobalOddRootQCacheBinary k)
      (generatedAxisGlobalMaskEncode (toAdd q.base)) =
        generatedAxisGlobalMaskEncode (toAdd r.base))
    (hc : (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddRootMaskRows k)
      (generatedAxisGlobalOddRootMaskCoefficients k)
      (generatedAxisGlobalMaskEncode (toAdd q.base))).testBit 0 then (1 : ZMod 2) else 0) = c) :
    generatedAxisGlobalOddRootQFast k q = qCentral c * r := by
  conv_lhs => rw [generatedAxisGlobalQMaskEncode_positive q hq]
  conv_rhs => rw [generatedAxisGlobalQMaskEncode_positive r hr]
  rw [generatedAxisGlobalOddRootQFast_mask k hk]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ hb hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
