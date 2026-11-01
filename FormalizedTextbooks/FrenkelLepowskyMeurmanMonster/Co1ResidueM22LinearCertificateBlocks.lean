/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22LinearData

/-! Bounded kernel certificates, separated so their geometric assembly can reuse checked proofs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Bounded original-line reduction certificate block masksBlock0. -/
theorem co1ResidueM22LinearMasksBlock0 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨0 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨0 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨0 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨0 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock1. -/
theorem co1ResidueM22LinearMasksBlock1 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨1 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨1 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨1 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨1 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock2. -/
theorem co1ResidueM22LinearMasksBlock2 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨2 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨2 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨2 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨2 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock3. -/
theorem co1ResidueM22LinearMasksBlock3 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨3 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨3 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨3 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨3 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock4. -/
theorem co1ResidueM22LinearMasksBlock4 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨4 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨4 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨4 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨4 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock5. -/
theorem co1ResidueM22LinearMasksBlock5 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨5 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨5 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨5 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨5 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock6. -/
theorem co1ResidueM22LinearMasksBlock6 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨6 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨6 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨6 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨6 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock7. -/
theorem co1ResidueM22LinearMasksBlock7 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨7 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨7 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨7 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨7 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock8. -/
theorem co1ResidueM22LinearMasksBlock8 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨8 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨8 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨8 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨8 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock9. -/
theorem co1ResidueM22LinearMasksBlock9 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨9 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨9 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨9 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨9 * 15 + k.val, by omega⟩ : Fin
          1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock10. -/
theorem co1ResidueM22LinearMasksBlock10 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨10 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨10 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨10 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨10 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock11. -/
theorem co1ResidueM22LinearMasksBlock11 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨11 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨11 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨11 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨11 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock12. -/
theorem co1ResidueM22LinearMasksBlock12 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨12 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨12 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨12 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨12 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock13. -/
theorem co1ResidueM22LinearMasksBlock13 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨13 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨13 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨13 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨13 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock14. -/
theorem co1ResidueM22LinearMasksBlock14 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨14 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨14 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨14 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨14 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock15. -/
theorem co1ResidueM22LinearMasksBlock15 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨15 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨15 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨15 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨15 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock16. -/
theorem co1ResidueM22LinearMasksBlock16 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨16 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨16 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨16 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨16 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock17. -/
theorem co1ResidueM22LinearMasksBlock17 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨17 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨17 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨17 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨17 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock18. -/
theorem co1ResidueM22LinearMasksBlock18 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨18 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨18 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨18 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨18 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock19. -/
theorem co1ResidueM22LinearMasksBlock19 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨19 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨19 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨19 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨19 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock20. -/
theorem co1ResidueM22LinearMasksBlock20 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨20 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨20 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨20 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨20 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock21. -/
theorem co1ResidueM22LinearMasksBlock21 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨21 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨21 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨21 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨21 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock22. -/
theorem co1ResidueM22LinearMasksBlock22 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨22 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨22 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨22 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨22 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock23. -/
theorem co1ResidueM22LinearMasksBlock23 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨23 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨23 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨23 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨23 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock24. -/
theorem co1ResidueM22LinearMasksBlock24 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨24 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨24 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨24 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨24 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock25. -/
theorem co1ResidueM22LinearMasksBlock25 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨25 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨25 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨25 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨25 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock26. -/
theorem co1ResidueM22LinearMasksBlock26 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨26 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨26 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨26 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨26 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock27. -/
theorem co1ResidueM22LinearMasksBlock27 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨27 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨27 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨27 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨27 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock28. -/
theorem co1ResidueM22LinearMasksBlock28 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨28 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨28 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨28 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨28 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock29. -/
theorem co1ResidueM22LinearMasksBlock29 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨29 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨29 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨29 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨29 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock30. -/
theorem co1ResidueM22LinearMasksBlock30 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨30 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨30 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨30 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨30 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock31. -/
theorem co1ResidueM22LinearMasksBlock31 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨31 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨31 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨31 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨31 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock32. -/
theorem co1ResidueM22LinearMasksBlock32 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨32 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨32 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨32 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨32 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock33. -/
theorem co1ResidueM22LinearMasksBlock33 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨33 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨33 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨33 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨33 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock34. -/
theorem co1ResidueM22LinearMasksBlock34 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨34 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨34 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨34 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨34 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock35. -/
theorem co1ResidueM22LinearMasksBlock35 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨35 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨35 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨35 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨35 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock36. -/
theorem co1ResidueM22LinearMasksBlock36 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨36 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨36 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨36 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨36 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock37. -/
theorem co1ResidueM22LinearMasksBlock37 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨37 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨37 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨37 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨37 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock38. -/
theorem co1ResidueM22LinearMasksBlock38 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨38 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨38 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨38 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨38 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock39. -/
theorem co1ResidueM22LinearMasksBlock39 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨39 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨39 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨39 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨39 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock40. -/
theorem co1ResidueM22LinearMasksBlock40 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨40 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨40 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨40 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨40 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock41. -/
theorem co1ResidueM22LinearMasksBlock41 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨41 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨41 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨41 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨41 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock42. -/
theorem co1ResidueM22LinearMasksBlock42 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨42 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨42 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨42 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨42 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock43. -/
theorem co1ResidueM22LinearMasksBlock43 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨43 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨43 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨43 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨43 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock44. -/
theorem co1ResidueM22LinearMasksBlock44 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨44 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨44 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨44 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨44 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock45. -/
theorem co1ResidueM22LinearMasksBlock45 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨45 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨45 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨45 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨45 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock46. -/
theorem co1ResidueM22LinearMasksBlock46 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨46 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨46 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨46 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨46 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock47. -/
theorem co1ResidueM22LinearMasksBlock47 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨47 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨47 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨47 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨47 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock48. -/
theorem co1ResidueM22LinearMasksBlock48 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨48 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨48 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨48 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨48 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock49. -/
theorem co1ResidueM22LinearMasksBlock49 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨49 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨49 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨49 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨49 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock50. -/
theorem co1ResidueM22LinearMasksBlock50 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨50 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨50 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨50 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨50 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock51. -/
theorem co1ResidueM22LinearMasksBlock51 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨51 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨51 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨51 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨51 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock52. -/
theorem co1ResidueM22LinearMasksBlock52 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨52 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨52 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨52 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨52 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock53. -/
theorem co1ResidueM22LinearMasksBlock53 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨53 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨53 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨53 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨53 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock54. -/
theorem co1ResidueM22LinearMasksBlock54 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨54 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨54 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨54 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨54 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock55. -/
theorem co1ResidueM22LinearMasksBlock55 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨55 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨55 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨55 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨55 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock56. -/
theorem co1ResidueM22LinearMasksBlock56 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨56 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨56 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨56 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨56 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock57. -/
theorem co1ResidueM22LinearMasksBlock57 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨57 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨57 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨57 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨57 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock58. -/
theorem co1ResidueM22LinearMasksBlock58 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨58 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨58 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨58 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨58 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock59. -/
theorem co1ResidueM22LinearMasksBlock59 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨59 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨59 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨59 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨59 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock60. -/
theorem co1ResidueM22LinearMasksBlock60 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨60 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨60 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨60 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨60 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock61. -/
theorem co1ResidueM22LinearMasksBlock61 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨61 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨61 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨61 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨61 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock62. -/
theorem co1ResidueM22LinearMasksBlock62 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨62 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨62 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨62 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨62 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock63. -/
theorem co1ResidueM22LinearMasksBlock63 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨63 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨63 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨63 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨63 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock64. -/
theorem co1ResidueM22LinearMasksBlock64 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨64 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨64 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨64 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨64 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock65. -/
theorem co1ResidueM22LinearMasksBlock65 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨65 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨65 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨65 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨65 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock66. -/
theorem co1ResidueM22LinearMasksBlock66 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨66 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨66 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨66 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨66 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock67. -/
theorem co1ResidueM22LinearMasksBlock67 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨67 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨67 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨67 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨67 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock68. -/
theorem co1ResidueM22LinearMasksBlock68 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨68 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨68 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨68 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨68 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock69. -/
theorem co1ResidueM22LinearMasksBlock69 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨69 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨69 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨69 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨69 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock70. -/
theorem co1ResidueM22LinearMasksBlock70 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨70 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨70 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨70 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨70 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock71. -/
theorem co1ResidueM22LinearMasksBlock71 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨71 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨71 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨71 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨71 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock72. -/
theorem co1ResidueM22LinearMasksBlock72 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨72 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨72 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨72 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨72 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock73. -/
theorem co1ResidueM22LinearMasksBlock73 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨73 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨73 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨73 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨73 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock74. -/
theorem co1ResidueM22LinearMasksBlock74 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨74 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨74 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨74 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨74 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock75. -/
theorem co1ResidueM22LinearMasksBlock75 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨75 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨75 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨75 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨75 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block masksBlock76. -/
theorem co1ResidueM22LinearMasksBlock76 : ∀ k : Fin 15,
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨76 * 15 + k.val, by omega⟩ : Fin
      1155)).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨76 * 15 + k.val, by omega⟩ : Fin
        1155)).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines (⟨76 * 15 + k.val, by omega⟩ : Fin
        1155)).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads (⟨76 * 15 + k.val, by omega⟩ :
          Fin 1155)) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock0. -/
theorem co1ResidueM22LinearPointBlock0 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨0 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨0 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨0 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock1. -/
theorem co1ResidueM22LinearPointBlock1 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨1 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨1 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨1 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock2. -/
theorem co1ResidueM22LinearPointBlock2 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨2 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨2 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨2 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock3. -/
theorem co1ResidueM22LinearPointBlock3 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨3 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨3 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨3 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock4. -/
theorem co1ResidueM22LinearPointBlock4 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨4 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨4 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨4 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock5. -/
theorem co1ResidueM22LinearPointBlock5 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨5 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨5 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨5 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock6. -/
theorem co1ResidueM22LinearPointBlock6 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨6 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨6 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨6 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock7. -/
theorem co1ResidueM22LinearPointBlock7 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨7 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨7 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨7 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock8. -/
theorem co1ResidueM22LinearPointBlock8 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨8 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨8 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨8 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock9. -/
theorem co1ResidueM22LinearPointBlock9 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨9 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨9 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨9 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

/-- Bounded original-line reduction certificate block pointBlock10. -/
theorem co1ResidueM22LinearPointBlock10 : ∀ k : Fin 21,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates (⟨10 * 21 + k.val, by omega⟩ : Fin 231)).map
        co1ResidueM22LinearLineMask) =
        (2 ^ ((⟨10 * 21 + k.val, by omega⟩ : Fin 231)).val) ^^^
        co1ResidueM22LinearBasisMask (⟨10 * 21 + k.val, by omega⟩ : Fin 231) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
