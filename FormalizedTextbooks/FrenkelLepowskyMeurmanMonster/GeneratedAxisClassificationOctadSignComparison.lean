/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSignRealization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadConvolution

/-! Two coherent real sign systems on the actual roots differ by actual Q conjugation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem sign_injective : Function.Injective qSign := by
  intro a b h
  have he : qSign (a + b) = 1 := by rw [qSign_add, h, qSign_sq]
  have hab := (qSign_eq_one_iff _).mp he
  have haa : ∀ c : ZMod 2, c + c = 0 := by decide +kernel
  exact add_left_cancel ((haa a).trans hab.symm)

/-- Real unit coordinates with coherent preferred-Q product signs differ by
a genuine extraspecial conjugation character. -/
theorem generatedOctad_coherent_sign_comparison (x y : GriessShortIndex → ℝ)
    (hx : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r → x r ^ 2 = 1)
    (hy : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r → y r ^ 2 = 1)
    (hxc : ∀ r s u,
      generatedOctadShortSupport generatedOctadBasisOctad r →
      generatedOctadShortSupport generatedOctadBasisOctad s →
      generatedOctadShortSupport generatedOctadBasisOctad u →
      (griessShortQ r * griessShortQ s).base = (griessShortQ u).base →
      qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * x r * x s = x u)
    (hyc : ∀ r s u,
      generatedOctadShortSupport generatedOctadBasisOctad r →
      generatedOctadShortSupport generatedOctadBasisOctad s →
      generatedOctadShortSupport generatedOctadBasisOctad u →
      (griessShortQ r * griessShortQ s).base = (griessShortQ u).base →
      qSign (toAdd (griessShortQ r * griessShortQ s).coeff) * y r * y s = y u) :
    ∃ q : Q, ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      qSign (toAdd (localAxisQPhase r q)) * x r = y r := by
  classical
  let f : GriessShortIndex → ZMod 2 := fun r => if y r * x r = 1 then 0 else 1
  have hf (r) (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
      qSign (f r) = y r * x r := by
    have hs : (y r * x r) ^ 2 = 1 := by rw [mul_pow, hx r hr, hy r hr]; norm_num
    by_cases h : y r * x r = 1
    · simp [f, h]
    · have hm : y r * x r = -1 := (sq_eq_one_iff.mp hs).resolve_left h
      rw [show f r = 1 from ite_eq_right h, qSign_one, hm]
  have hadd : ∀ r s u,
      generatedOctadShortSupport generatedOctadBasisOctad r →
      generatedOctadShortSupport generatedOctadBasisOctad s →
      generatedOctadShortSupport generatedOctadBasisOctad u →
      (griessShortQ r * griessShortQ s).base = (griessShortQ u).base →
        f r + f s = f u := by
    intro r s u hr hs hu he
    apply sign_injective
    rw [qSign_add, hf r hr, hf s hs, hf u hu]
    apply generatedAxisE8_triple_ratio
      (qSign (toAdd (griessShortQ r * griessShortQ s).coeff))
    · rw [pow_two, qSign_sq]
    · exact hxc r s u hr hs hu he
    · exact hyc r s u hr hs hu he
  obtain ⟨q, hq⟩ := generatedOctad_supported_sign_realization f hadd
  refine ⟨q, ?_⟩
  intro r hr
  rw [hq r hr, hf r hr, mul_assoc, ← pow_two, hx r hr, mul_one]

/-- For actual raw 64-idempotents, the proved 56-pair count discharges coherence,
so their supported unit signs are related by an actual element of Q. -/
theorem generatedOctad_idempotent_sign_comparison (x y : ConwayRawSpace)
    (htx : x.2.2 = 0) (hty : y.2.2 = 0)
    (hx : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r → x.2.1 r ^ 2 = 1)
    (hy : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r → y.2.1 r ^ 2 = 1)
    (hzx : ∀ r, ¬ generatedOctadShortSupport generatedOctadBasisOctad r → x.2.1 r = 0)
    (hzy : ∀ r, ¬ generatedOctadShortSupport generatedOctadBasisOctad r → y.2.1 r = 0)
    (hpx : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      conwayShortPairing x.1 r = 4)
    (hpy : ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      conwayShortPairing y.1 r = 4)
    (hix : ∀ r, (conwayRawProduct x x).2.1 r = 64 * x.2.1 r)
    (hiy : ∀ r, (conwayRawProduct y y).2.1 r = 64 * y.2.1 r) :
    ∃ q : Q, ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      qSign (toAdd (localAxisQPhase r q)) * x.2.1 r = y.2.1 r :=
  generatedOctad_coherent_sign_comparison x.2.1 y.2.1 hx hy
    (generatedOctad_idempotent_short_coherent x htx hx hzx hpx hix)
    (generatedOctad_idempotent_short_coherent y hty hy hzy hpy hiy)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
