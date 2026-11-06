/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadActualRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SupportSaturation

/-! Actual 56-root arithmetic forces signed product coherence in the coordinate section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A zero-tensor 64-idempotent with unit supported short coordinates satisfies
each actual supported signed product relation separately. -/
theorem generatedOctad_idempotent_short_coherent (x : ConwayRawSpace)
    (ht : x.2.2 = 0)
    (hx : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r → x.2.1 r ^ 2 = 1)
    (hz : ∀ r, ¬ generatedOctadShortSupport generatedOctadBasisOctad r → x.2.1 r = 0)
    (hp : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      conwayShortPairing x.1 r = 4)
    (hid : ∀ r, (conwayRawProduct x x).2.1 r = 64 * x.2.1 r)
    (r s u : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedOctadBasisOctad r)
    (hs : generatedOctadShortSupport generatedOctadBasisOctad s)
    (hu : generatedOctadShortSupport generatedOctadBasisOctad u)
    (hedge : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * x.2.1 r * x.2.1 s =
      x.2.1 u := by
  classical
  apply generatedAxisE8_supported_convolution_saturated
    (generatedOctadShortSupport generatedOctadBasisOctad)
    (fun a b => (griessShortQ a * griessShortQ b).base = (griessShortQ u).base)
    (fun a b => qSign (toAdd (griessShortQ a * griessShortQ b).coeff))
    x.2.1 (x.2.1 u) 56 _ hx hz (hx u hu)
    (generatedOctadActualRootPairs_filter_card u hu)
    (generatedAxisE8_short_convolution x u ht (hp u hu) (hid u)) r s hr hs hedge
  intro a b
  rw [pow_two, qSign_sq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
