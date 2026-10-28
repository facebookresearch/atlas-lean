/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLettersInv
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSourceSignLocal

/-! # Normal forms with phase-zero source signs

The source sign with phase one is the phase-zero sign followed by the extraspecial letter of
`sourceOmegaQ` (`signLocal_one`), because the triality conjugate of the central involution is
`sourceOmegaQ` (`generatedSeventh_inverse_central`).  Hence every word of the extended alphabet
`IdentLetterX` (with formal inverses of `xi` and of signs) has a normal form in `IdentLetter`
whose source signs all have phase zero (`identNormE`, `identNormE_local`, `identNormE_phase`). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-- The zero-label source sign of phase one is the extraspecial element `sourceOmegaQ`. -/
theorem signLocal_zero_one : generatedFifthSignLocal 0 1 = inclQ sourceOmegaQ := by
  apply localIntoGenerated_injective
  rw [generatedFifth_sign_local_generated, sourceGeneratedY, sourceGeneratedCode,
    sourceQCode_zero_one]
  exact generatedSeventh_inverse_central

/-- A source sign of phase one is the phase-zero sign times `sourceOmegaQ`. -/
theorem signLocal_one (a : Fin 4096) :
    generatedFifthSignLocal a 1 = generatedFifthSignLocal a 0 * inclQ sourceOmegaQ := by
  rw [show (1 : ZMod 2) = 0 + 1 from rfl, signLocal_add_one, signLocal_zero_one]

/-- The normal form of a source sign: phase-zero sign, then `sourceOmegaQ` for phase one. -/
def signWord (a : Fin 4096) (ε : ZMod 2) : List IdentLetter :=
  if ε = 0 then [.sign a 0] else [.sign a 0, .qel sourceOmegaQ]

/-- The normal form of a source sign names the source sign. -/
theorem signWord_local (a : Fin 4096) (ε : ZMod 2) :
    identWordLocal (signWord a ε) = generatedFifthSignLocal a ε := by
  have hε : ε = 0 ∨ ε = 1 := by
    have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact h ε
  rcases hε with rfl | rfl
  · rw [signWord, ite_eq_left rfl, identWordLocal_singleton]
    exact generatedFifth_sign_fiber_local a 0
  · rw [signWord, ite_eq_right (by decide : ¬ (1 : ZMod 2) = 0), show ([.sign a 0, .qel sourceOmegaQ] : List IdentLetter) =
      [.sign a 0] ++ [.qel sourceOmegaQ] from rfl, identWordLocal_append, identWordLocal_singleton,
      identWordLocal_singleton, signLocal_one]
    rw [show localFiberIntoH (IdentLetter.sign a 0).fiber = generatedFifthSignLocal a 0 from
      generatedFifth_sign_fiber_local a 0]
    rfl

/-- Every sign of a sign normal form has phase zero. -/
theorem signWord_phase (a : Fin 4096) (ε : ZMod 2) :
    ∀ x ∈ signWord a ε, ∀ b η, x = .sign b η → η = 0 := by
  intro x hx b η hxe
  unfold signWord at hx
  split_ifs at hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hx] at hxe
    cases hxe
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [hx] at hxe
      cases hxe
      rfl
    · rw [hx] at hxe
      cases hxe

/-- The phase-zero normal form of an extended letter. -/
def IdentLetterX.normE : IdentLetterX → List IdentLetter
  | .xi => [.xi]
  | .xiInv => [.xi, .xi]
  | .sign a ε => signWord a ε
  | .signInv a ε => signWord a (ε + signQ a)
  | .mono l => [.mono l]
  | .qel g => [.qel g]

/-- The phase-zero normal form names the same local element. -/
theorem IdentLetterX.normE_local (x : IdentLetterX) : identWordLocal x.normE = x.local := by
  cases x with
  | xi => rw [IdentLetterX.normE, identWordLocal_singleton]; rfl
  | xiInv => exact xiLocal_inv.symm
  | sign a ε => exact signWord_local a ε
  | signInv a ε =>
    rw [IdentLetterX.normE, signWord_local]
    exact (signLocal_inv a ε).symm
  | mono l => rw [IdentLetterX.normE, identWordLocal_singleton]; rfl
  | qel g => rw [IdentLetterX.normE, identWordLocal_singleton]; rfl

/-- Every sign of a phase-zero normal form of a letter has phase zero. -/
theorem IdentLetterX.normE_phase (x : IdentLetterX) :
    ∀ y ∈ x.normE, ∀ b η, y = .sign b η → η = 0 := by
  cases x with
  | sign a ε => exact signWord_phase a ε
  | signInv a ε => exact signWord_phase a (ε + signQ a)
  | xi => intro y hy b η h; simp [IdentLetterX.normE] at hy; subst hy; cases h
  | xiInv => intro y hy b η h; simp [IdentLetterX.normE] at hy; subst hy; cases h
  | mono l => intro y hy b η h; simp [IdentLetterX.normE] at hy; subst hy; cases h
  | qel g => intro y hy b η h; simp [IdentLetterX.normE] at hy; subst hy; cases h

/-- The phase-zero normal form of an extended word. -/
def identNormE (ls : List IdentLetterX) : List IdentLetter := ls.flatMap IdentLetterX.normE

/-- The phase-zero normal form of an extended word names the same local element. -/
theorem identNormE_local (ls : List IdentLetterX) :
    identWordLocal (identNormE ls) = (ls.map IdentLetterX.local).prod := by
  induction ls with
  | nil => simp [identNormE, identWordLocal, identWordFiber]
  | cons x ls ih =>
    rw [identNormE, List.flatMap_cons, ← identNormE, identWordLocal_append, ih,
      IdentLetterX.normE_local, List.map_cons, List.prod_cons]

/-- Every sign of a phase-zero normal form has phase zero. -/
theorem identNormE_phase (ls : List IdentLetterX) :
    ∀ y ∈ identNormE ls, ∀ b η, y = .sign b η → η = 0 := by
  intro y hy
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp hy
  exact x.normE_phase y hx

/-- An extended letter for every letter. -/
def IdentLetter.toX : IdentLetter → IdentLetterX
  | .xi => .xi
  | .sign a ε => .sign a ε
  | .mono l => .mono l
  | .qel g => .qel g

/-- The extended letter of a letter names the same local element. -/
theorem IdentLetter.toX_local (x : IdentLetter) : x.toX.local = localFiberIntoH x.fiber := by
  cases x with
  | xi => rfl
  | sign a ε => exact (generatedFifth_sign_fiber_local a ε).symm
  | mono l => rfl
  | qel g => rfl

/-- The formal inverse of an extended letter. -/
def IdentLetterX.inv : IdentLetterX → IdentLetterX
  | .xi => .xiInv
  | .xiInv => .xi
  | .sign a ε => .signInv a ε
  | .signInv a ε => .sign a ε
  | .mono l => .mono (l.1, !l.2)
  | .qel g => .qel g⁻¹

/-- The formal inverse names the inverse local element. -/
theorem IdentLetterX.inv_local (x : IdentLetterX) : x.inv.local = x.local⁻¹ := by
  cases x with
  | xi => rfl
  | xiInv => exact (inv_inv _).symm
  | sign a ε => rfl
  | signInv a ε => exact (inv_inv _).symm
  | mono l =>
    change localFiberIntoH (IdentLetter.mono (l.1, !l.2)).fiber =
      (localFiberIntoH (IdentLetter.mono l).fiber)⁻¹
    rw [monoFiber_inv, map_inv]
  | qel g =>
    change localFiberIntoH (IdentLetter.qel g⁻¹).fiber = (localFiberIntoH (IdentLetter.qel g).fiber)⁻¹
    rw [qelFiber_inv, map_inv]

/-- The formal inverse of an extended word. -/
def identInvX (ls : List IdentLetterX) : List IdentLetterX := (ls.map IdentLetterX.inv).reverse

/-- The formal inverse of an extended word names the inverse local element. -/
theorem identInvX_local (ls : List IdentLetterX) :
    ((identInvX ls).map IdentLetterX.local).prod = ((ls.map IdentLetterX.local).prod)⁻¹ := by
  induction ls with
  | nil => simp [identInvX]
  | cons x ls ih =>
    have h1 : identInvX (x :: ls) = identInvX ls ++ [x.inv] := by simp [identInvX]
    rw [h1, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_singleton,
      IdentLetterX.inv_local, List.map_cons, List.prod_cons, mul_inv_rev]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
