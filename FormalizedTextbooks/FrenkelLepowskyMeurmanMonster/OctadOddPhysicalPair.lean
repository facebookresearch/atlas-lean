/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Two physical octad-coordinate flips produce the actual normalized pair translation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddPhysicalLabel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairFourier

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A local singleton embeds as its actual physical-coordinate singleton. -/
theorem octadPhysicalEmbedding_single (o : Fin 759) (a : Fin 8) :
    octadPhysicalEmbedding o (Pi.single a 1) = Pi.single (golayOctadCoordinate o a) 1 := by
  change (∑ k, (Pi.single (golayOctadCoordinate o k)
    ((Pi.single a 1 : Fin 8 → ZMod 2) k) : Fin 24 → ZMod 2)) = _
  simp only [Pi.single_apply, apply_ite, Pi.single_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Physical normalization is local normalization after the actual coordinate embedding. -/
theorem octadPhysicalNormalize_embedding (o : Fin 759) (v : Fin 8 → ZMod 2) :
    octadPhysicalNormalize o (octadPhysicalEmbedding o v) = octadSignNormalize v := by
  change octadSignNormalize (fun k => octadPhysicalEmbedding o v (golayOctadCoordinate o k)) = _
  simp only [octadPhysicalEmbedding_local]

private theorem octadPair_bit_local (e : Fin 64) (k : Fin 8) :
    trialityBinaryBit e k = trialityOctadLocalBit e k := by
  unfold trialityBinaryBit trialityOctadLocalBit
  cases (trialityEvenMask e).testBit k.val <;> rfl

private theorem octadPair_zero_bit : ∀ k : Fin 8, trialityOctadLocalBit 0 k = 0 := by
  decide +kernel

/-- Normalizing the local two-point pattern gives the actual pair-translation label. -/
theorem octadSignNormalize_pair (a b : Fin 8) (hab : a ≠ b) :
    octadSignNormalize (Pi.single a 1 + Pi.single b 1) =
      octadSignLabelEquiv (trialityOctadPairShift a b) := by
  have hrep : octadSignRepresentative (octadSignLabelEquiv (trialityOctadPairShift a b)) =
      fun k => (Pi.single a 1 + Pi.single b 1 : Fin 8 → ZMod 2) k +
        trialityOctadPairComplement a b := by
    rw [octadSignRepresentative_label]
    ext k
    rw [octadPair_bit_local, trialityOctadPairShift,
      trialityOctadPairFlip_bit a b 0 hab k, octadPair_zero_bit]
    simp only [zero_add, Pi.add_apply, Pi.single_apply]
  have hn := congrArg octadSignNormalize hrep
  rw [octadSignNormalize_representative, octadSignNormalize_complement] at hn
  exact hn.symm

/-- Two physical coordinate flips normalize to their actual octad pair translation. -/
theorem octadPhysicalNormalize_pair (o : Fin 759) (a b : Fin 8) (hab : a ≠ b) :
    octadPhysicalNormalize o (Pi.single (golayOctadCoordinate o a) 1 +
      Pi.single (golayOctadCoordinate o b) 1) =
        octadSignLabelEquiv (trialityOctadPairShift a b) := by
  have he : (Pi.single (golayOctadCoordinate o a) 1 +
      Pi.single (golayOctadCoordinate o b) 1 : Fin 24 → ZMod 2) =
        octadPhysicalEmbedding o (Pi.single a 1 + Pi.single b 1) := by
    rw [map_add, octadPhysicalEmbedding_single, octadPhysicalEmbedding_single]
  rw [he, octadPhysicalNormalize_embedding, octadSignNormalize_pair a b hab]

/-- Flipping two physical octad coordinates adds precisely the actual normalized
pair-shift label to any given normalized physical pattern. -/
theorem octadOddPhysical_normalized_pair_shift (o : Fin 759) (I : Fin 24 → ZMod 2)
    (c : Fin 64) (hNorm : octadPhysicalNormalize o I = octadSignLabelEquiv c)
    (a b : Fin 8) (hab : a ≠ b) :
    octadPhysicalNormalize o (I + Pi.single (golayOctadCoordinate o a) 1 +
      Pi.single (golayOctadCoordinate o b) 1) =
        octadSignLabelEquiv (trialityXor c (trialityOctadPairShift a b)) := by
  rw [map_add, map_add, hNorm, octadSignLabelEquiv_xor, add_assoc,
    ← map_add, octadPhysicalNormalize_pair o a b hab]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
