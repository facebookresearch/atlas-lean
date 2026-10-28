/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortProductCovariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators

/-! # Inverse letters as words of the identification alphabet

Inverses of letters are words of the alphabet `IdentLetter`, exactly as local elements:
`xi⁻¹ = xi * xi` (`xi` has order three), the inverse of a permutation letter is the letter with
the flipped flag, the inverse of an extraspecial letter is the extraspecial letter of the inverse,
and the inverse of the source sign `σ(a, ε)` is the sign `σ(a, ε + P(a))` with the quarter-weight
parity `P(a)` of the code word.  Words in the extended alphabet `IdentLetterX` (with `xiInv` and
`signInv`) are normalized letter by letter (`identNorm`, `identNorm_local`), and every word has an
inverse word (`identInv`, `identInv_local`).  Moreover `σ(a, ε + 1) = σ(a, ε) * σ(0, 1)`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-! ## Signs -/

/-- The quarter-weight parity `P(a)` of a code label. -/
def signQ (a : Fin 4096) : ZMod 2 := ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2)

/-- Multiplying a code lift by a central element shifts its phase. -/
theorem sourceQCode_mul_central (d : Fin 4096) (ε c : ZMod 2) :
    sourceQCode d ε * qCentral c = sourceQCode d (ε + c) := by
  rw [qCentral_commute]
  apply NormalizedCocycleExtension.Extension.ext
  · exact qCentral_mul_base c _
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change c + (ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)) =
      (ε + c) + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
    ring

/-- A central element squares to one. -/
theorem qCentral_mul_self (c : ZMod 2) : qCentral c * qCentral c = 1 := by
  rw [qCentral_mul, CharTwo.add_self_eq_zero]
  rfl

/-- The inverse of a code lift. -/
theorem sourceQCode_inv (d : Fin 4096) (ε : ZMod 2) :
    (sourceQCode d ε)⁻¹ = sourceQCode d (ε + signQ d) := by
  rw [← sourceQCode_mul_central]
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, ← pow_two, sourceQCode_square, signQ, qCentral_mul_self]

/-- The inverse of a source sign is a source sign. -/
theorem signLocal_inv (d : Fin 4096) (ε : ZMod 2) :
    (generatedFifthSignLocal d ε)⁻¹ = generatedFifthSignLocal d (ε + signQ d) := by
  apply localIntoGenerated_injective
  rw [map_inv, generatedFifth_sign_local_generated, generatedFifth_sign_local_generated,
    sourceGeneratedY, sourceGeneratedY, sourceGeneratedCode, sourceGeneratedCode,
    ← sourceQCode_inv, map_inv]
  group

/-- The code lift of the zero label with phase one is the central element. -/
theorem sourceQCode_zero_one : sourceQCode 0 1 = qCentral 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change sourceExpectedCodeCoordinates (golayLabelCoefficients 0) = (0 : Fin 24 → ZMod 2)
    decide
  · apply toAdd.injective
    change (1 : ZMod 2) + ((golayMaskWeight (golayEncodedMask (0 : Fin 4096).val) / 4 : ℕ) : ZMod 2) =
      1
    decide

/-- A source sign with shifted phase. -/
theorem signLocal_add_one (d : Fin 4096) (ε : ZMod 2) :
    generatedFifthSignLocal d (ε + 1) = generatedFifthSignLocal d ε * generatedFifthSignLocal 0 1 := by
  apply localIntoGenerated_injective
  rw [map_mul, generatedFifth_sign_local_generated, generatedFifth_sign_local_generated,
    generatedFifth_sign_local_generated, sourceGeneratedY, sourceGeneratedY, sourceGeneratedY,
    sourceGeneratedCode, sourceGeneratedCode, sourceGeneratedCode, ← sourceQCode_mul_central,
    sourceQCode_zero_one, map_mul]
  group

/-! ## Inverse letters -/

/-- The inverse of a letter, as a word. -/
def IdentLetter.invWord : IdentLetter → List IdentLetter
  | .xi => [.xi, .xi]
  | .sign a ε => [.sign a (ε + signQ a)]
  | .mono l => [.mono (l.1, !l.2)]
  | .qel g => [.qel g⁻¹]

/-- `xi` has order three. -/
theorem xiFiber_inv : xiSpinLocalFiber⁻¹ = xiSpinLocalFiber * xiSpinLocalFiber := by
  apply inv_eq_of_mul_eq_one_right
  rw [← xiSpinLocalFiber_cube, pow_succ, pow_two, mul_assoc]

/-- The local element of `xi` has order three. -/
theorem xiLocal_inv :
    (localFiberIntoH xiSpinLocalFiber)⁻¹ = identWordLocal [.xi, .xi] := by
  rw [← map_inv, xiFiber_inv, identWordLocal, identWordFiber]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

/-- The inverse of a permutation letter flips its flag. -/
theorem monoFiber_inv (l : Fin 2 × Bool) :
    (IdentLetter.mono (l.1, !l.2)).fiber = ((IdentLetter.mono l).fiber)⁻¹ := by
  change generatedFourthMonomialFiberLetter (l.1, !l.2) = (generatedFourthMonomialFiberLetter l)⁻¹
  rcases l with ⟨i, b⟩
  cases b <;> simp [generatedFourthMonomialFiberLetter]

/-- The inverse of an extraspecial letter. -/
theorem qelFiber_inv (g : Q) : (IdentLetter.qel g⁻¹).fiber = ((IdentLetter.qel g).fiber)⁻¹ :=
  map_inv localFiberIncl g

/-- The inverse word of a letter names the inverse local element. -/
theorem IdentLetter.invWord_local (x : IdentLetter) :
    identWordLocal x.invWord = (localFiberIntoH x.fiber)⁻¹ := by
  cases x with
  | xi => exact xiLocal_inv.symm
  | sign a ε =>
    rw [IdentLetter.invWord, identWordLocal_singleton]
    change localFiberIntoH (generatedFifthSignFiber a (ε + signQ a)) =
      (localFiberIntoH (generatedFifthSignFiber a ε))⁻¹
    rw [generatedFifth_sign_fiber_local, generatedFifth_sign_fiber_local, signLocal_inv]
  | mono l =>
    rw [IdentLetter.invWord, identWordLocal_singleton, ← map_inv, monoFiber_inv]
  | qel g =>
    rw [IdentLetter.invWord, identWordLocal_singleton, ← map_inv, qelFiber_inv]

/-- The inverse word of a word. -/
def identInv (ls : List IdentLetter) : List IdentLetter := ls.reverse.flatMap IdentLetter.invWord

/-- The inverse word names the inverse local element. -/
theorem identInv_local (ls : List IdentLetter) :
    identWordLocal (identInv ls) = (identWordLocal ls)⁻¹ := by
  induction ls with
  | nil => simp [identInv, identWordLocal, identWordFiber]
  | cons x ls ih =>
    rw [identInv, List.reverse_cons, List.flatMap_append, ← identInv, identWordLocal_append, ih,
      show x :: ls = [x] ++ ls by rfl, identWordLocal_append, mul_inv_rev, List.flatMap_singleton,
      IdentLetter.invWord_local, identWordLocal_singleton]

/-! ## The extended alphabet -/

/-- Letters together with formal inverses of `xi` and of source signs. -/
inductive IdentLetterX
  | xi
  | xiInv
  | sign (a : Fin 4096) (ε : ZMod 2)
  | signInv (a : Fin 4096) (ε : ZMod 2)
  | mono (l : Fin 2 × Bool)
  | qel (g : Q)

/-- The local element of an extended letter. -/
noncomputable def IdentLetterX.local : IdentLetterX → H
  | .xi => localFiberIntoH xiSpinLocalFiber
  | .xiInv => (localFiberIntoH xiSpinLocalFiber)⁻¹
  | .sign a ε => generatedFifthSignLocal a ε
  | .signInv a ε => (generatedFifthSignLocal a ε)⁻¹
  | .mono l => localFiberIntoH (generatedFourthMonomialFiberLetter l)
  | .qel g => localFiberIntoH (localFiberIncl g)

/-- The normal form of an extended letter. -/
def IdentLetterX.norm : IdentLetterX → List IdentLetter
  | .xi => [.xi]
  | .xiInv => [.xi, .xi]
  | .sign a ε => [.sign a ε]
  | .signInv a ε => [.sign a (ε + signQ a)]
  | .mono l => [.mono l]
  | .qel g => [.qel g]

/-- The normal form names the same local element. -/
theorem IdentLetterX.norm_local (x : IdentLetterX) : identWordLocal x.norm = x.local := by
  cases x with
  | xi => rw [IdentLetterX.norm, identWordLocal_singleton]; rfl
  | xiInv => exact xiLocal_inv.symm
  | sign a ε =>
    rw [IdentLetterX.norm, identWordLocal_singleton]
    exact generatedFifth_sign_fiber_local a ε
  | signInv a ε =>
    rw [IdentLetterX.norm, identWordLocal_singleton]
    change localFiberIntoH (generatedFifthSignFiber a (ε + signQ a)) =
      (generatedFifthSignLocal a ε)⁻¹
    rw [generatedFifth_sign_fiber_local, signLocal_inv]
  | mono l => rw [IdentLetterX.norm, identWordLocal_singleton]; rfl
  | qel g => rw [IdentLetterX.norm, identWordLocal_singleton]; rfl

/-- The normal form of an extended word. -/
def identNorm (ls : List IdentLetterX) : List IdentLetter := ls.flatMap IdentLetterX.norm

/-- The normal form of an extended word names the same local element. -/
theorem identNorm_local (ls : List IdentLetterX) :
    identWordLocal (identNorm ls) = (ls.map IdentLetterX.local).prod := by
  induction ls with
  | nil => simp [identNorm, identWordLocal, identWordFiber]
  | cons x ls ih =>
    rw [identNorm, List.flatMap_cons, ← identNorm, identWordLocal_append, ih,
      IdentLetterX.norm_local, List.map_cons, List.prod_cons]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
