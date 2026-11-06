/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadActualRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPropagation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhaseExact

/-! Every coherent sign assignment on the actual supported roots is conjugation
by an actual element of Q. Coherence is an explicit input; it will follow from
the actual extremal short-product convolution. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Any supported binary-additive sign assignment is realized by actual Q conjugation. -/
theorem generatedOctad_supported_sign_realization (f : GriessShortIndex → ZMod 2)
    (hadd : ∀ r s t,
      generatedOctadShortSupport generatedOctadBasisOctad r →
      generatedOctadShortSupport generatedOctadBasisOctad s →
      generatedOctadShortSupport generatedOctadBasisOctad t →
      (griessShortQ r * griessShortQ s).base = (griessShortQ t).base →
        f r + f s = f t) :
    ∃ q : Q, ∀ r, generatedOctadShortSupport generatedOctadBasisOctad r →
      toAdd (localAxisQPhase r q) = f r := by
  let fp : Fin 120 → ZMod 2 := fun p => f (generatedOctadPatternLabel p)
  let v := generatedOctadPropagationValues fp
  have hf (p : Fin 120) : fp p = dotProduct v (generatedOctadPatternBits p) := by
    apply generatedOctadPropagation_linear
    intro r s t ht
    exact hadd _ _ _ (generatedOctadPatternLabel_supported r)
      (generatedOctadPatternLabel_supported s) (generatedOctadPatternLabel_supported t)
      ((generatedOctadPatternLabel_product_iff r s t).mpr ht)
  obtain ⟨q, hq⟩ := generatedOctadBasis_Q_phases_surjective (ofAdd v)
  have hb (j : Fin 8) : generatedOctadQCommuteLinear q
      (generatedOctadBasisBinaryMatrix.col j) = v j := by
    have hj := congrArg (fun a : Multiplicative (Fin 8 → ZMod 2) => toAdd a j) hq
    change toAdd (localAxisQPhase (generatedOctadBasisLabel j) q) = v j at hj
    change generatedOctadQCommuteLinear q
      (toAdd (griessShortQ (generatedOctadBasisLabel j)).base) = _ at hj
    rwa [generatedOctadBasis_actual_base] at hj
  refine ⟨q, ?_⟩
  intro r hr
  obtain ⟨p, hp⟩ := generatedOctadPatternEquiv.surjective ⟨r, hr⟩
  have hp' : generatedOctadPatternLabel p = r := congrArg Subtype.val hp
  rw [← hp']
  change generatedOctadQCommuteLinear q
    (toAdd (griessShortQ (generatedOctadPatternLabel p)).base) = fp p
  rw [generatedOctadPatternLabel_base, hf]
  have hm : generatedOctadBasisBinaryMatrix *ᵥ generatedOctadPatternBits p =
      ∑ j, generatedOctadPatternBits p j • generatedOctadBasisBinaryMatrix.col j := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.col_apply]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hm, map_sum]
  simp only [map_smul, hb, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
