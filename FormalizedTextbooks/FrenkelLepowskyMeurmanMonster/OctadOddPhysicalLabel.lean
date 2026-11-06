/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual octad sign label determined by an even physical pattern and two points. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadSmallSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadKernelCardinality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem octadOddPhysical_code (o : Fin 759) (v : Fin 24 → ZMod 2)
    (hv : ∀ k, k ∉ golayOctadSupport o → v k = 0) (i j : Fin 24)
    (h : golaySyndrome (v + Pi.single i 1 + Pi.single j 1) = 0) :
    v + Pi.single i 1 + Pi.single j 1 = 0 ∨
      v + Pi.single i 1 + Pi.single j 1 = golayOctadWord o := by
  apply golayCode_supported_octad_extra o {i,j} (by by_cases h : i=j <;> simp [h])
    _ ((golaySyndrome_zero_iff_code _).mp h)
  intro k hk
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [hv k hk.1, hk.2.1, hk.2.2]

private theorem octadOddPhysical_add_zero (a b : OctadSignSpace) :
    a+b=0 ↔ a=b := by
  constructor
  · intro h
    have hz := congrArg (fun x => x+b) h
    simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hz
  · rintro rfl
    exact ZModModule.add_self a

private theorem octadOddPhysical_pair_supported (o : Fin 759) (I : Fin 24 → ZMod 2)
    (hIs : ∀ k, k ∉ golayOctadSupport o → I k = 0) (i j : Fin 24)
    (his : i ∈ golayOctadSupport o) (hjs : j ∈ golayOctadSupport o) :
    ∀ k, k ∉ golayOctadSupport o → (I+Pi.single i 1+Pi.single j 1 : Fin 24 → ZMod 2) k = 0 := by
  intro k hk
  have hki : k≠i := by intro h; exact hk (h ▸ his)
  have hkj : k≠j := by intro h; exact hk (h ▸ hjs)
  simp [hIs k hk, hki, hkj]

private theorem octadOddPhysical_pair_even (I : Fin 24 → ZMod 2)
    (hIe : ∑ k, I k = 0) (i j : Fin 24) :
    (∑ k : Fin 24, (I+Pi.single i 1+Pi.single j 1 : Fin 24 → ZMod 2) k) = 0 := by
  simp [Finset.sum_add_distrib, hIe, CharTwo.add_self_eq_zero]

/-- A supported even pattern determines its actual preferred sign label by its syndrome. -/
theorem octadOddPhysical_normalized_syndrome (o : Fin 759) (e : Fin 64)
    (J : Fin 24 → ZMod 2)
    (hJs : ∀ k, k ∉ golayOctadSupport o → J k = 0) (hJe : ∑ k, J k = 0) :
    golaySyndrome (integerParity (griessOctadNegativeInteger o e) + J) = 0 ↔
      octadSignLabelEquiv e = octadPhysicalNormalize o J := by
  rw [← octadPhysicalSignMap_label]
  constructor
  · intro hs
    have hc : octadPhysicalSignMap o (octadSignLabelEquiv e) + J = 0 ∨
        octadPhysicalSignMap o (octadSignLabelEquiv e) + J = golayOctadWord o := by
      apply golayCode_supported_octad_extra o ∅ (by simp)
        _ ((golaySyndrome_zero_iff_code _).mp hs)
      intro k hk
      simp only [Finset.union_empty] at hk
      simp [octadPhysicalSignMap_supported o _ k hk, hJs k hk]
    apply (octadOddPhysical_add_zero _ _).mp
    rcases hc with hc | hc
    · have hn := congrArg (octadPhysicalNormalize o) hc
      simpa only [map_add, map_zero, octadPhysicalNormalize_signMap] using hn
    · have hn := congrArg (octadPhysicalNormalize o) hc
      simpa only [map_add, octadPhysicalNormalize_word,
        octadPhysicalNormalize_signMap] using hn
  · intro hl
    rw [hl, octadPhysicalSignMap_normalize o J hJs hJe]
    have hx : (J + J (golayOctadCoordinate o 7) • golayOctadWord o) + J =
        J (golayOctadCoordinate o 7) • golayOctadWord o := by
      rw [add_comm J, add_assoc, ZModModule.add_self, add_zero]
    rw [hx, map_smul, golayOctadWord, golaySyndrome_encoder, smul_zero]

/-- A two-point syndrome condition either has equal indices and the unchanged
sign label, or two distinct octad coordinates and their actual flipped sign label. -/
theorem octadOddPhysical_syndrome_iff (o : Fin 759) (e : Fin 64)
    (I : Fin 24 → ZMod 2)
    (hIs : ∀ k, k ∉ golayOctadSupport o → I k = 0) (hIe : ∑ k, I k = 0)
    (i j : Fin 24) :
    golaySyndrome (integerParity (griessOctadNegativeInteger o e) + I +
      Pi.single i 1 + Pi.single j 1) = 0 ↔
      (i=j ∧ octadSignLabelEquiv e = octadPhysicalNormalize o I) ∨
      (i≠j ∧ i ∈ golayOctadSupport o ∧ j ∈ golayOctadSupport o ∧
        octadSignLabelEquiv e = octadPhysicalNormalize o (I+Pi.single i 1+Pi.single j 1)) := by
  by_cases hij : i=j
  · subst j
    have hcancel (x y : Fin 24 → ZMod 2) : x+y+y=x := by
      rw [add_assoc, ZModModule.add_self, add_zero]
    rw [hcancel]
    simp only [ne_eq, not_true_eq_false, false_and, or_false, true_and]
    exact octadOddPhysical_normalized_syndrome o e I hIs hIe
  · constructor
    · intro hs
      have hv : ∀ k, k ∉ golayOctadSupport o →
          (integerParity (griessOctadNegativeInteger o e) + I) k = 0 := by
        intro k hk
        simp [griessOctadNegative_supported o e k hk, hIs k hk]
      have hc := octadOddPhysical_code o _ hv i j hs
      have hout : ∀ k, k ∉ golayOctadSupport o →
          (Pi.single i 1 + Pi.single j 1 : Fin 24 → ZMod 2) k = 0 := by
        intro k hk
        have hzero :
            (integerParity (griessOctadNegativeInteger o e) + I +
              Pi.single i 1 + Pi.single j 1 : Fin 24 → ZMod 2) k = 0 := by
          rcases hc with hc | hc
          · exact congrFun hc k
          · rw [hc]
            exact golayOctadWord_supported o k hk
        simpa only [Pi.add_apply, griessOctadNegative_supported o e k hk,
          hIs k hk, zero_add] using hzero
      have his : i ∈ golayOctadSupport o := by
        by_contra hi
        have hz := hout i hi
        simp [hij] at hz
      have hjs : j ∈ golayOctadSupport o := by
        by_contra hj
        have hz := hout j hj
        simp [Ne.symm hij] at hz
      right
      refine ⟨hij,his,hjs,?_⟩
      apply (octadOddPhysical_normalized_syndrome o e _
        (octadOddPhysical_pair_supported o I hIs i j his hjs)
        (octadOddPhysical_pair_even I hIe i j)).mp
      simpa only [add_assoc] using hs
    · rintro (⟨h,_⟩ | ⟨_,his,hjs,hl⟩)
      · exact (hij h).elim
      have hs := (octadOddPhysical_normalized_syndrome o e _
        (octadOddPhysical_pair_supported o I hIs i j his hjs)
        (octadOddPhysical_pair_even I hIe i j)).mpr hl
      simpa only [add_assoc] using hs

/-- The equal-index alternative is equality to the actual normalized physical label. -/
theorem octadOddPhysical_syndrome_label_iff (o : Fin 759) (e : Fin 64)
    (I : Fin 24 → ZMod 2)
    (hIs : ∀ k, k ∉ golayOctadSupport o → I k = 0) (hIe : ∑ k, I k = 0)
    (i j : Fin 24) :
    golaySyndrome (integerParity (griessOctadNegativeInteger o e) + I +
      Pi.single i 1 + Pi.single j 1) = 0 ↔
      (i=j ∧ e = octadSignLabelEquiv.symm (octadPhysicalNormalize o I)) ∨
      (i≠j ∧ i ∈ golayOctadSupport o ∧ j ∈ golayOctadSupport o ∧
        octadSignLabelEquiv e = octadPhysicalNormalize o (I+Pi.single i 1+Pi.single j 1)) := by
  simpa only [Equiv.eq_symm_apply] using octadOddPhysical_syndrome_iff o e I hIs hIe i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
