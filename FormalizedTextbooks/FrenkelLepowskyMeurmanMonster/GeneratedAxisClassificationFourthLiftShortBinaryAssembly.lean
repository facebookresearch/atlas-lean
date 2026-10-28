/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryCertificate8

/-! All packed binary coordinates equal the intrinsic preferred-Q coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Complete binary-coordinate certificates for every listed actual octad and preferred sign. -/
theorem generatedFourth_lift_short_binary_certificate (j : Fin 63) (e : Fin 64) :
    toAdd (generatedFourthLiftShortOctadQFast j e).base =
      toAdd (generatedFourthLiftShortOctadQPacked j e).base := by
  have hb : ∀ b : Fin 9, ∀ k : Fin 7, ∀ f : Fin 64,
      let i : Fin 63 := ⟨7 * b.val + k.val, by omega⟩
      toAdd (generatedFourthLiftShortOctadQFast i f).base =
        toAdd (generatedFourthLiftShortOctadQPacked i f).base := by
    intro b
    fin_cases b
    · exact generatedFourth_lift_short_binary_certificate_0
    · exact generatedFourth_lift_short_binary_certificate_1
    · exact generatedFourth_lift_short_binary_certificate_2
    · exact generatedFourth_lift_short_binary_certificate_3
    · exact generatedFourth_lift_short_binary_certificate_4
    · exact generatedFourth_lift_short_binary_certificate_5
    · exact generatedFourth_lift_short_binary_certificate_6
    · exact generatedFourth_lift_short_binary_certificate_7
    · exact generatedFourth_lift_short_binary_certificate_8
  have he : (⟨7 * (j.val / 7) + j.val % 7, by omega⟩ : Fin 63) = j := by
    apply Fin.ext
    dsimp
    omega
  simpa only [he] using hb (⟨j.val / 7, by omega⟩ : Fin 9)
    (⟨j.val % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) e

/-- The packed evaluator equals the full genuine preferred Q lift in every listed sign row. -/
theorem generatedFourth_lift_short_octad_q_packed (j : Fin 63) (e : Fin 64) :
    generatedFourthLiftShortSourceQ j e = generatedFourthLiftShortOctadQPacked j e := by
  rw [generatedFourth_lift_short_octad_q_fast]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact generatedFourth_lift_short_binary_certificate j e
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
