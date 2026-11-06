/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact physical syndrome selection of actual signed-octad/odd preferred-Q products. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXYZSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadSmallSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Zero syndrome is precisely membership in the actual binary Golay code. -/
theorem golaySyndrome_eq_zero_iff_mem_code (v : Fin 24 → ZMod 2) :
    golaySyndrome v = 0 ↔ v ∈ golayCode := by
  constructor
  · intro h
    have hd := golayCodeCocode_decomposition v
    simp only [h, map_zero, sub_zero, add_zero] at hd
    exact ⟨golayDecoder v, hd⟩
  · rintro ⟨t,rfl⟩
    exact golaySyndrome_encoder t

/-- A physical cocode supported on one octad and two indicated points has
zero syndrome exactly when it is zero or the octad word. -/
theorem octad_pair_syndrome_zero_iff (o : Fin 759) (v : Fin 24 → ZMod 2)
    (hv : ∀ k, k ∉ golayOctadSupport o → v k = 0) (i j : Fin 24) :
    golaySyndrome (v + Pi.single i 1 + Pi.single j 1) = 0 ↔
      v + Pi.single i 1 + Pi.single j 1 = 0 ∨
      v + Pi.single i 1 + Pi.single j 1 = golayOctadWord o := by
  constructor
  · intro h
    apply golayCode_supported_octad_extra o {i,j} (by by_cases h : i = j <;> simp [h])
      _ ((golaySyndrome_eq_zero_iff_mem_code _).mp h)
    intro k hk
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [hv k hk.1, hk.2.1, hk.2.2]
  · rintro (h | h)
    · rw [h, map_zero]
    · rw [golaySyndrome_eq_zero_iff_mem_code, h]
      exact golayOctadWord_mem_code o

private theorem add_eq_iff_four_zero (a b c d : Fin 12 → ZMod 2) :
    a+b = c+d ↔ a+c+b+d = 0 := by
  constructor
  · intro h
    calc
      _ = (a+b)+(c+d) := by abel
      _ = _ := by rw [h, ZModModule.add_self]
  · intro h
    have he := congrArg (fun x : Fin 12 → ZMod 2 => x+(c+d)) h
    simpa only [show a+c+b+d+(c+d) = a+b by
      calc
        _ = a+b+((c+d)+(c+d)) := by abel
        _ = _ := by rw [ZModModule.add_self, add_zero], zero_add] using he

/-- Under the actual source theta addition identity, preferred-Q modulation
selection is exactly the physical negative/intersection/pair syndrome equation. -/
theorem griessOctadOdd_modulation_selector (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) (I : Fin 24 → ZMod 2)
    (hθ : sourceWordTheta ⟨f.val, by omega⟩ =
      sourceWordTheta (golayOctadLabel o) + sourceWordTheta ⟨d.val, by omega⟩ +
        golaySyndrome I) :
    spinModulation (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inr (d,i)))) =
        spinModulation (griessShortQ (Sum.inr (Sum.inr (f,j)))) ↔
      golaySyndrome (integerParity (griessOctadNegativeInteger o e) + I +
        Pi.single i 1 + Pi.single j 1) = 0 := by
  rw [spinModulation_mul, griessOctad_modulation, griessOdd_modulation,
    griessOdd_modulation, hθ]
  have hi : (fun k : Fin 12 => (golayGeneratorBit k i : ZMod 2)) =
      golaySyndrome (Pi.single i 1) := by
    ext k
    simp [golaySyndrome, Pi.single_apply]
  have hj : (fun k : Fin 12 => (golayGeneratorBit k j : ZMod 2)) =
      golaySyndrome (Pi.single j 1) := by
    ext k
    simp [golaySyndrome, Pi.single_apply]
  rw [hi,hj]
  have hl :
      (sourceWordTheta (golayOctadLabel o) +
        golaySyndrome (integerParity (griessOctadNegativeInteger o e))) +
        (sourceWordTheta ⟨d.val, by omega⟩ + golaySyndrome (Pi.single i 1)) =
      (sourceWordTheta (golayOctadLabel o) + sourceWordTheta ⟨d.val, by omega⟩) +
        (golaySyndrome (integerParity (griessOctadNegativeInteger o e)) +
          golaySyndrome (Pi.single i 1)) := by abel
  have hr : (sourceWordTheta (golayOctadLabel o) + sourceWordTheta ⟨d.val, by omega⟩ +
      golaySyndrome I) + golaySyndrome (Pi.single j 1) =
      (sourceWordTheta (golayOctadLabel o) + sourceWordTheta ⟨d.val, by omega⟩) +
        (golaySyndrome I + golaySyndrome (Pi.single j 1)) := by abel
  rw [hl,hr,add_left_cancel_iff,add_eq_iff_four_zero]
  simp only [map_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
