/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameClass

/-! The distinguished lattice-class fiber inside the coordinate E8 section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Section vectors in the genuine distinguished frame class modulo twice the lattice. -/
def GeneratedOctadNormEightFrameFiber (c : Fin 24 → ZMod 2) :=
  {x : GeneratedOctadNormEight c // leechReduction x.val =
    leechReduction (leechCoordinateFrameLattice 0)}

/-- The signed frame vector at a section coordinate lies in the distinguished fiber. -/
def generatedStandardOctadSignedFrame (t : Fin 8 × ZMod 2) :
    GeneratedOctadNormEightFrameFiber golayStandardOctad := by
  let s := leechSignedFrame (Fin.castAdd 16 t.1, t.2)
  refine ⟨⟨s.val, ?_, s.property⟩, leechSignedFrame_reduction _⟩
  intro i hi
  have hn : ¬ i.val < 8 := by
    by_contra hb
    simp [golayStandardOctad, hb] at hi
  have hne : i ≠ Fin.castAdd 16 t.1 := by
    intro he
    have hv : i.val = t.1.val := congrArg (fun j : Fin 24 => j.val) he
    omega
  change (leechSignedFrame (Fin.castAdd 16 t.1, t.2)).val.val i = 0
  simp [leechSignedFrame, leechCoordinateFrameVector, ite_apply, hne]

/-- The sixteen coordinate/sign labels remain distinct as actual section vectors. -/
theorem generatedStandardOctadSignedFrame_injective :
    Function.Injective generatedStandardOctadSignedFrame := by
  intro t s h
  have he : leechSignedFrame (Fin.castAdd 16 t.1, t.2) =
      leechSignedFrame (Fin.castAdd 16 s.1, s.2) := by
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) h
  have ht := leechSignedFrame_injective he
  apply Prod.ext
  · exact Fin.ext (congrArg (fun x : Fin 24 × ZMod 2 => x.1.val) ht)
  · exact congrArg (fun x : Fin 24 × ZMod 2 => x.2) ht

/-- Every actual distinguished-frame vector in the section is one of these sixteen. -/
theorem generatedStandardOctadSignedFrame_surjective :
    Function.Surjective generatedStandardOctadSignedFrame := by
  intro x
  let u : LeechNormEight := ⟨x.val.val, x.val.property.2⟩
  have hm : u ∈ Set.range leechSignedFrame := by
    rw [← leechNormEight_frameClass_eq_signedFrame]
    exact x.property
  obtain ⟨t, ht⟩ := hm
  have hu := (generatedOctadSupported_standard x.val.val.val).mp x.val.property.1
  have hin : t.1.val < 8 := by
    by_contra hn
    have hz := hu t.1 (by omega)
    have he := congrArg (fun y : LeechNormEight => y.val.val t.1) ht
    change (leechSignedFrame t).val.val t.1 = x.val.val.val t.1 at he
    rw [hz] at he
    have hne : (if t.2 = 0 then (8 : ℤ) else -8) ≠ 0 := by
      split_ifs <;> norm_num
    exact hne (by simpa [leechSignedFrame, leechCoordinateFrameVector, ite_apply] using he)
  refine ⟨(⟨t.1.val, hin⟩, t.2), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (leechSignedFrame (Fin.castAdd 16 ⟨t.1.val, hin⟩, t.2)).val = x.val.val
  have hi : Fin.castAdd 16 (⟨t.1.val, hin⟩ : Fin 8) = t.1 := Fin.ext rfl
  rw [hi]
  exact congrArg Subtype.val ht

/-- The actual distinguished frame-class fiber inside this E8 section has sixteen vectors. -/
theorem generatedStandardOctad_frameFiber_card :
    Nat.card (GeneratedOctadNormEightFrameFiber golayStandardOctad) = 16 := by
  rw [Nat.card_congr (Equiv.ofBijective generatedStandardOctadSignedFrame
    ⟨generatedStandardOctadSignedFrame_injective,
      generatedStandardOctadSignedFrame_surjective⟩).symm]
  norm_num [Nat.card_prod]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
