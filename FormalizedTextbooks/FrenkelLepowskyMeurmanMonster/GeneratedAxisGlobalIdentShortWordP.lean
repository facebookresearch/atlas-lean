/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortFast

/-! # Packed mask data of words in the identification alphabet

Packed (`QMaskP`) letter data for the shared alphabet `IdentLetter`, so that the composite data of
a word are certified with the fast packed step (`QMaskP.stepP`) instead of the list-based step.
Odd source letters come with packed literals checked against their canonical data. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-- Packed columns of the ten odd source letters. -/
def sourceLetterColsP : Fin 10 → ℕ := ![
  0x40000080000000020000010000008000004000002000001000700000b00000d00000e000 |||
    (0x80040040080020000010000008000004000002000001000000800700400b00200d00100e <<< 288),
  0x40080080040000020000010000008000004000002000001000700800b00400d00200e001 |||
    (0x40000080020000010000008000004000002000001000000000700000b00000d00000e <<< 288),
  0x0008000004000ca20008c10030608020c04000f0200000103608081e08042a0802020801 |||
    (0x80f010400000200000100000080000040000020000010800008000004000002000001000 <<< 288),
  0x0008000004000ca20008c10030608020c04000f0200000103608081e08042a0802020801 |||
    (0x80f010400000200000100000080000040000020000010800008000004000002000001000 <<< 288),
  0x00080000040004c2000c610010c08030a04000002000f0102d0808390804150802010801 |||
    (0x80f020400000200000100000080000040000020800010000008000004000002000001000 <<< 288),
  0x00080000040004c2000c610010c08030a04000002000f0102d0808390804150802010801 |||
    (0x80f020400000200000100000080000040000020800010000008000004000002000001000 <<< 288),
  0x00080000c7fe40b80400c00c16f94f3f03c026ea213f03305fca0c6fc90c30130e40fffd |||
    (0xbfd0004f100000c00030b0000c00004800000300004100002930001630004330000f1000 <<< 288),
  0x00080020d4520769080da90405ccc90fcc850fcc2705cc3b7adb005ada002a110e283d0f |||
    (0xaad00040100047b0004d70004410004c100043100041100058f00078f0004820000a1000 <<< 288),
  0x0008000004000300cd0c003310208010302020204020301000740800b4040fc3fc05c2ac |||
    (0x80000040c00000300000200028300022200014300011200020b000207000100000300000 <<< 288),
  0x0008000004000300cd0c003310208010302020204020301000740800b4040fc3fc05c2ac |||
    (0x80000040c00000300000200028300022200014300011200020b000207000100000300000 <<< 288)
]

/-- Packed correction rows of the ten odd source letters. -/
def sourceLetterRowsP : Fin 10 → ℕ := ![
  0x800000400000000000000000000000000000000000000000008000004000002000001000 |||
    (0x80000000000000000000000000000000000000000000000000800000c00000e000 <<< 288),
  0x80000040080000000000000000000000000000000000000000800000400800200c00100e,
  0x0000000000000000000000000003000002000000000000000003600001e00002a0000020 |||
    (0x800000000000000000000000000000 <<< 288),
  0x0000000000000000000000000003000002000000000000000003600001e00002a0000020 |||
    (0x800000000000000000000000000000 <<< 288),
  0x0000000000000000000000000001000003000000000000000002d0000390000150000010 |||
    (0x800000000000000000000000000000000000 <<< 288),
  0x0000000000000000000000000001000003000000000000000002d0000390000150000010 |||
    (0x800000000000000000000000000000000000 <<< 288),
  0x4000002000002000000000002000000000002700002d800000c000222,
  0x40000060000030000038000038000036000040000040800000c00040e,
  0x1000002000001000002000000000000080000fc00033c,
  0x1000002000001000002000000000000080000fc00033c
]

/-- Packed coordinate units. -/
def unitsP : ℕ :=
    0x000800000400000200000100000080000040000020000010000008000004000002000001 |||
    (0x800000400000200000100000080000040000020000010000008000004000002000001000 <<< 288)

/-- Packed data of an odd source letter. -/
def sourceLetterP (l : Fin 10) : QMaskP :=
  ⟨sourceLetterColsP l, sourceLetterRowsP l, sourceLetterCoeff l⟩

set_option maxRecDepth 100000 in
/-- The packed source letter data unpack to the canonical data. -/
theorem sourceLetterP_eq : ∀ l : Fin 10,
    qmDataEq (sourceLetterP l).toData (sourceLetterData l) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed source letter data fit in 24 fields. -/
theorem sourceLetterP_ok : ∀ l : Fin 10, (sourceLetterP l).ok = true := by
  decide +kernel

/-- The packed check of one letter: fitting data whose unpacked data pass the letter check. -/
def identLetterCheckP (x : IdentLetter) (d : QMaskP) : Bool := d.ok && identLetterCheck x d.toData

/-- Checked packed letter data are valid. -/
theorem identLetterCheckP_sound (x : IdentLetter) (d : QMaskP) (h : identLetterCheckP x d = true) :
    d.toData.Valid (spinConjugation x.fiber.val.1) := by
  simp only [identLetterCheckP, Bool.and_eq_true] at h
  exact identLetterCheck_sound x d.toData h.2

/-- A packed checked word is computed by its packed word of data. -/
theorem identCheckedWordP_spec (w : List (IdentLetter × QMaskP))
    (hw : w.all (fun p => identLetterCheckP p.1 p.2) = true) (p : ℕ × Bool) :
    spinConjugation (identWordFiber (w.map Prod.fst)).val.1 (qmElt p) =
      qmElt (qmWordP (w.map Prod.snd) p) := by
  have hok : (w.map Prod.snd).all QMaskP.ok = true := by
    simp only [List.all_eq_true, List.mem_map] at hw ⊢
    rintro d ⟨x, hx, rfl⟩
    have := hw x hx
    simp only [identLetterCheckP, Bool.and_eq_true] at this
    exact this.1
  have hw' : (w.map (fun p => (p.1, p.2.toData))).all
      (fun p => identLetterCheck p.1 p.2) = true := by
    simp only [List.all_eq_true, List.mem_map] at hw ⊢
    rintro q ⟨x, hx, rfl⟩
    have := hw x hx
    simp only [identLetterCheckP, Bool.and_eq_true] at this
    exact this.2
  have h1 := identCheckedWord_spec _ hw' p
  simp only [List.map_map] at h1
  rw [qmWordP_eq _ hok, List.map_map]
  exact h1

/-- Composite packed data of a checked word: generator images by the packed step and computed
correction rows. -/
theorem identCheckedWordP_valid (w : List (IdentLetter × QMaskP))
    (hw : w.all (fun p => identLetterCheckP p.1 p.2) = true) (D : QMaskP)
    (hcols : ∀ i : Fin 24, qmWordP (w.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 D.colsP i.val, D.coeff.testBit i.val))
    (hrows : ∀ i : Fin 24, fld 24 D.rowsP i.val = rowsOf (fun j => fld 24 D.colsP j.val) i) :
    D.toData.Valid (spinConjugation (identWordFiber (w.map Prod.fst)).val.1) := by
  apply QMaskData.valid_of_generators _ D.toData _ hrows
  intro i
  rw [← qmElt_unit, identCheckedWordP_spec w hw, hcols]
  rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
