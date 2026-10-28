/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthSelectedShortData

/-! Every finite selected term is bound to its original canonical preferred target coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The finite selected row of each original preferred pair target. -/
def generatedAxisGlobalOddFifthSelectedPair (s : Fin 2) (p : Fin 276) : Fin 4136 :=
  ⟨276*s.val+p.val, by omega⟩

/-- Every selected pair row retains its actual original target. -/
theorem generatedAxisGlobalOddFifthSelectedPair_actual (s : Fin 2) (p : Fin 276) :
    generatedAxisGlobalOddFifthSelectedTarget (generatedAxisGlobalOddFifthSelectedPair s p) =
      Sum.inl (s,p) := by
  have h : 276*s.val+p.val < 552 := by omega
  simp only [generatedAxisGlobalOddFifthSelectedTarget, generatedAxisGlobalOddFifthSelectedPair,
    h, ↓reduceDIte, Sum.inl.injEq, Prod.mk.injEq]
  constructor
  · apply Fin.ext
    change (276*s.val+p.val)/276 = s.val
    omega
  · apply Fin.ext
    change (276*s.val+p.val)%276 = p.val
    omega

/-- The finite selected row of each original canonical even root Fourier input. -/
def generatedAxisGlobalOddFifthSelectedEven (j : Fin 56) (e : Fin 64) : Fin 4136 :=
  ⟨552+64*j.val+e.val, by omega⟩

/-- Each selected Fourier row retains the actual original canonical middle octad index. -/
theorem generatedAxisGlobalOddFifthSelectedEven_actual (j : Fin 56) (e : Fin 64) :
    generatedAxisGlobalOddFifthSelectedTarget (generatedAxisGlobalOddFifthSelectedEven j e) =
      Sum.inr (Sum.inl (generatedFifthEvenRootOctad j,e)) := by
  have h : ¬ 552+64*j.val+e.val < 552 := by omega
  simp only [generatedAxisGlobalOddFifthSelectedTarget, generatedAxisGlobalOddFifthSelectedEven,
    h, ↓reduceDIte]
  have hj : (⟨(552+64*j.val+e.val-552)/64, by omega⟩ : Fin 56) = j := by
    apply Fin.ext
    change (552+64*j.val+e.val-552)/64 = j.val
    omega
  have he : (⟨(552+64*j.val+e.val-552)%64, Nat.mod_lt _ (by decide)⟩ : Fin 64) = e := by
    apply Fin.ext
    change (552+64*j.val+e.val-552)%64 = e.val
    omega
  rw [hj, he, generatedAxisGlobalCanonicalFifthEvenOctadIndex_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
