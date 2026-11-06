/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22LinearCertificateBlocks

/-! Bounded ordinary kernel replay of original hexad relations and point reductions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private def masksPredicate (l : Fin 1155) : Prop :=
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines l).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines l).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines l).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads l)

private theorem masksBlock_all (h : Fin 77) (j : Fin 15) (l : Fin 1155)
    (hl : l.val = h.val * 15 + j.val) : masksPredicate l := by
  fin_cases h
  · have he : l = (⟨0 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock0 j) he.symm
  · have he : l = (⟨1 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock1 j) he.symm
  · have he : l = (⟨2 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock2 j) he.symm
  · have he : l = (⟨3 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock3 j) he.symm
  · have he : l = (⟨4 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock4 j) he.symm
  · have he : l = (⟨5 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock5 j) he.symm
  · have he : l = (⟨6 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock6 j) he.symm
  · have he : l = (⟨7 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock7 j) he.symm
  · have he : l = (⟨8 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock8 j) he.symm
  · have he : l = (⟨9 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock9 j) he.symm
  · have he : l = (⟨10 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock10 j) he.symm
  · have he : l = (⟨11 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock11 j) he.symm
  · have he : l = (⟨12 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock12 j) he.symm
  · have he : l = (⟨13 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock13 j) he.symm
  · have he : l = (⟨14 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock14 j) he.symm
  · have he : l = (⟨15 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock15 j) he.symm
  · have he : l = (⟨16 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock16 j) he.symm
  · have he : l = (⟨17 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock17 j) he.symm
  · have he : l = (⟨18 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock18 j) he.symm
  · have he : l = (⟨19 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock19 j) he.symm
  · have he : l = (⟨20 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock20 j) he.symm
  · have he : l = (⟨21 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock21 j) he.symm
  · have he : l = (⟨22 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock22 j) he.symm
  · have he : l = (⟨23 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock23 j) he.symm
  · have he : l = (⟨24 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock24 j) he.symm
  · have he : l = (⟨25 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock25 j) he.symm
  · have he : l = (⟨26 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock26 j) he.symm
  · have he : l = (⟨27 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock27 j) he.symm
  · have he : l = (⟨28 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock28 j) he.symm
  · have he : l = (⟨29 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock29 j) he.symm
  · have he : l = (⟨30 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock30 j) he.symm
  · have he : l = (⟨31 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock31 j) he.symm
  · have he : l = (⟨32 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock32 j) he.symm
  · have he : l = (⟨33 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock33 j) he.symm
  · have he : l = (⟨34 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock34 j) he.symm
  · have he : l = (⟨35 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock35 j) he.symm
  · have he : l = (⟨36 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock36 j) he.symm
  · have he : l = (⟨37 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock37 j) he.symm
  · have he : l = (⟨38 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock38 j) he.symm
  · have he : l = (⟨39 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock39 j) he.symm
  · have he : l = (⟨40 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock40 j) he.symm
  · have he : l = (⟨41 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock41 j) he.symm
  · have he : l = (⟨42 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock42 j) he.symm
  · have he : l = (⟨43 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock43 j) he.symm
  · have he : l = (⟨44 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock44 j) he.symm
  · have he : l = (⟨45 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock45 j) he.symm
  · have he : l = (⟨46 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock46 j) he.symm
  · have he : l = (⟨47 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock47 j) he.symm
  · have he : l = (⟨48 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock48 j) he.symm
  · have he : l = (⟨49 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock49 j) he.symm
  · have he : l = (⟨50 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock50 j) he.symm
  · have he : l = (⟨51 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock51 j) he.symm
  · have he : l = (⟨52 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock52 j) he.symm
  · have he : l = (⟨53 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock53 j) he.symm
  · have he : l = (⟨54 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock54 j) he.symm
  · have he : l = (⟨55 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock55 j) he.symm
  · have he : l = (⟨56 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock56 j) he.symm
  · have he : l = (⟨57 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock57 j) he.symm
  · have he : l = (⟨58 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock58 j) he.symm
  · have he : l = (⟨59 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock59 j) he.symm
  · have he : l = (⟨60 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock60 j) he.symm
  · have he : l = (⟨61 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock61 j) he.symm
  · have he : l = (⟨62 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock62 j) he.symm
  · have he : l = (⟨63 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock63 j) he.symm
  · have he : l = (⟨64 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock64 j) he.symm
  · have he : l = (⟨65 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock65 j) he.symm
  · have he : l = (⟨66 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock66 j) he.symm
  · have he : l = (⟨67 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock67 j) he.symm
  · have he : l = (⟨68 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock68 j) he.symm
  · have he : l = (⟨69 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock69 j) he.symm
  · have he : l = (⟨70 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock70 j) he.symm
  · have he : l = (⟨71 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock71 j) he.symm
  · have he : l = (⟨72 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock72 j) he.symm
  · have he : l = (⟨73 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock73 j) he.symm
  · have he : l = (⟨74 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock74 j) he.symm
  · have he : l = (⟨75 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock75 j) he.symm
  · have he : l = (⟨76 * 15 + j.val, by omega⟩ : Fin 1155) := Fin.ext (by simpa using hl)
    exact Eq.rec (motive := fun i _ => masksPredicate i)
      (co1ResidueM22LinearMasksBlock76 j) he.symm

/-- Every selected relation row is a genuine original cached hexad matching. -/
theorem co1ResidueM22LinearLines_masks (l : Fin 1155) :
    co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines l).1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines l).2.1 |||
      co1ResidueM22FinitePointMasks (co1ResidueM22LinearLines l).2.2 =
        co1ResidueM22FiniteHexadMasks (co1ResidueM22LinearHexads l) := by
  let h : Fin 77 := ⟨l.val / 15, by omega⟩
  let j : Fin 15 := ⟨l.val % 15, Nat.mod_lt _ (by decide)⟩
  exact masksBlock_all h j l (by dsimp [h, j]; omega)

private theorem pointBlock_all (h : Fin 11) (j : Fin 21) (i : Fin 231)
    (hl : i.val = h.val * 21 + j.val) :
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates i).map co1ResidueM22LinearLineMask) =
        (2 ^ (i).val) ^^^ co1ResidueM22LinearBasisMask i := by
  fin_cases h
  · have he : i = (⟨0 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock0 j
  · have he : i = (⟨1 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock1 j
  · have he : i = (⟨2 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock2 j
  · have he : i = (⟨3 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock3 j
  · have he : i = (⟨4 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock4 j
  · have he : i = (⟨5 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock5 j
  · have he : i = (⟨6 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock6 j
  · have he : i = (⟨7 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock7 j
  · have he : i = (⟨8 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock8 j
  · have he : i = (⟨9 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock9 j
  · have he : i = (⟨10 * 21 + j.val, by omega⟩ : Fin 231) := Fin.ext (by simpa using hl)
    exact he.symm ▸ co1ResidueM22LinearPointBlock10 j

/-- Original line rows sum to the claimed point reduction in the free binary module. -/
theorem co1ResidueM22LinearCertificates_correct (i : Fin 231) :
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22LinearCertificates i).map co1ResidueM22LinearLineMask) =
        (2 ^ (i).val) ^^^ co1ResidueM22LinearBasisMask i := by
  let h : Fin 11 := ⟨i.val / 21, by omega⟩
  let j : Fin 21 := ⟨i.val % 21, Nat.mod_lt _ (by decide)⟩
  exact pointBlock_all h j i (by dsimp [h, j]; omega)

/-- Every selected relation row satisfies the genuine hexad-line predicate. -/
theorem co1ResidueM22LinearLines_genuine (l : Fin 1155) :
    co1ResidueM22Line 0 1 (co1ResidueM22FinitePoint (co1ResidueM22LinearLines l).1)
      (co1ResidueM22FinitePoint (co1ResidueM22LinearLines l).2.1)
      (co1ResidueM22FinitePoint (co1ResidueM22LinearLines l).2.2) :=
  co1ResidueM22FiniteLine_of_masks _ _ _ _ (co1ResidueM22LinearLines_masks l)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
