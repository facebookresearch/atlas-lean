/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal translation, modulation and central coordinates for the actual Pauli group Q. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineSpin
public import Mathlib.Data.Fin.Tuple.Basic
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Construct an actual Q element from its translation, modulation and central sign bit. -/
def generatedAxisFourthQFromSpin (u m : SpinIndex) (c : ZMod 2) : Q :=
  ⟨Multiplicative.ofAdd (Fin.append u m), Multiplicative.ofAdd c⟩

/-- The literal coordinate constructor has the prescribed translation. -/
theorem generatedAxisFourthQFromSpin_translation (u m : SpinIndex) (c : ZMod 2) :
    spinTranslation (generatedAxisFourthQFromSpin u m c) = u := by
  funext i
  exact Fin.append_left u m i

/-- The literal coordinate constructor has the prescribed modulation. -/
theorem generatedAxisFourthQFromSpin_modulation (u m : SpinIndex) (c : ZMod 2) :
    spinModulation (generatedAxisFourthQFromSpin u m c) = m := by
  funext i
  exact Fin.append_right u m i

/-- The literal coordinate constructor has the prescribed central sign. -/
theorem generatedAxisFourthQFromSpin_coeff (u m : SpinIndex) (c : ZMod 2) :
    Multiplicative.toAdd (generatedAxisFourthQFromSpin u m c).coeff = c := rfl

/-- Translation, modulation and the central sign determine the actual Q element uniquely. -/
theorem generatedAxisFourthQ_spin_coordinates_injective (q r : Q)
    (hu : spinTranslation q = spinTranslation r)
    (hm : spinModulation q = spinModulation r)
    (hc : Multiplicative.toAdd q.coeff = Multiplicative.toAdd r.coeff) : q = r := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    funext i
    refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i
    · exact congrFun hu j
    · exact congrFun hm j
  · exact Multiplicative.toAdd.injective hc

/-- Reconstructing an actual Q element from its literal spin coordinates returns that element. -/
theorem generatedAxisFourthQFromSpin_reconstruct (q : Q) :
    generatedAxisFourthQFromSpin (spinTranslation q) (spinModulation q)
      (Multiplicative.toAdd q.coeff) = q := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · exact generatedAxisFourthQFromSpin_translation _ _ _
  · exact generatedAxisFourthQFromSpin_modulation _ _ _
  · exact generatedAxisFourthQFromSpin_coeff _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
