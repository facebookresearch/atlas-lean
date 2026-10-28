/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSelectedShortData

/-! Every finite selected term is bound to its original canonical preferred target coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The finite selected row of each original preferred pair target. -/
def generatedAxisGlobalOddFourthSelectedPair (s : Fin 2) (p : Fin 276) : Fin 4584 :=
  ⟨276*s.val+p.val, by omega⟩

/-- Every selected pair row retains its actual original target. -/
theorem generatedAxisGlobalOddFourthSelectedPair_actual (s : Fin 2) (p : Fin 276) :
    generatedAxisGlobalOddFourthSelectedTarget (generatedAxisGlobalOddFourthSelectedPair s p) =
      Sum.inl (s,p) := by
  have h : 276*s.val+p.val < 552 := by omega
  simp only [generatedAxisGlobalOddFourthSelectedTarget, generatedAxisGlobalOddFourthSelectedPair,
    h, ↓reduceDIte, Sum.inl.injEq, Prod.mk.injEq]
  constructor
  · apply Fin.ext
    change (276*s.val+p.val)/276 = s.val
    omega
  · apply Fin.ext
    change (276*s.val+p.val)%276 = p.val
    omega

/-- The finite selected row of each original canonical even root Fourier input. -/
def generatedAxisGlobalOddFourthSelectedEven (j : Fin 63) (e : Fin 64) : Fin 4584 :=
  ⟨552+64*j.val+e.val, by omega⟩

/-- Each selected Fourier row retains the actual original canonical middle octad index. -/
theorem generatedAxisGlobalOddFourthSelectedEven_actual (j : Fin 63) (e : Fin 64) :
    generatedAxisGlobalOddFourthSelectedTarget (generatedAxisGlobalOddFourthSelectedEven j e) =
      Sum.inr (Sum.inl (generatedFourthEvenRootOctad j,e)) := by
  have h : ¬ 552+64*j.val+e.val < 552 := by omega
  simp only [generatedAxisGlobalOddFourthSelectedTarget, generatedAxisGlobalOddFourthSelectedEven,
    h, ↓reduceDIte]
  have hj : (⟨(552+64*j.val+e.val-552)/64, by omega⟩ : Fin 63) = j := by
    apply Fin.ext
    change (552+64*j.val+e.val-552)/64 = j.val
    omega
  have he : (⟨(552+64*j.val+e.val-552)%64, Nat.mod_lt _ (by decide)⟩ : Fin 64) = e := by
    apply Fin.ext
    change (552+64*j.val+e.val-552)%64 = e.val
    omega
  rw [hj, he, generatedAxisGlobalCanonicalFourthEvenOctadIndex_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
