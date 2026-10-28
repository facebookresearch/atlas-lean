/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Direct finite lookup of every genuine tenth-state odd-short coefficient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SourceCoordinateLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSparseRealLookup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original odd-short label of one actual tenth-state term. -/
def monsterNortonLine01SeventhUShortLabel (jp : Fin 16 × Fin 32) : GriessShortIndex :=
  Sum.inr (Sum.inr
    (monsterNortonLine01ShortInputCode (monsterNortonLine01OctadSourceA jp.1 jp.2),
      monsterNortonLine01ShortPhysicalColumn (monsterNortonLine01OctadSourceK jp.1 jp.2)))

/-- The inverse index of a tenth-state label, using the genuine code and octad dictionaries. -/
def monsterNortonLine01SeventhUShortLookup : GriessShortIndex → Fin 16 × Fin 32
  | Sum.inr (Sum.inr (d, i)) =>
      let a := monsterNortonLine01SourceCodeLookup d
      let k := monsterNortonLine01SourcePhysicalLookup i
      (monsterNortonLine01ShortInverseOctadId a k,
        monsterNortonLine01OctadSignLookup (monsterNortonLine01ShortInverseOctadSigns a k))
  | _ => (0, 0)

/-- Membership in the exact finite tenth-state odd-short catalogue. -/
def monsterNortonLine01SeventhUShortSupport (r : GriessShortIndex) : Prop :=
  monsterNortonLine01SeventhUShortLabel (monsterNortonLine01SeventhUShortLookup r) = r

instance (r : GriessShortIndex) : Decidable (monsterNortonLine01SeventhUShortSupport r) :=
  inferInstanceAs (Decidable (_ = _))

private theorem sign_lookup_label (p : Fin 32) :
    monsterNortonLine01OctadSignLookup (monsterNortonLine01OctadSignLabel p) = p := by
  revert p
  decide +kernel

/-- Every actual tenth-state term is recovered with its precise octad and sign index. -/
theorem monsterNortonLine01SeventhUShortLookup_label (jp : Fin 16 × Fin 32) :
    monsterNortonLine01SeventhUShortLookup (monsterNortonLine01SeventhUShortLabel jp) = jp := by
  rcases jp with ⟨j, p⟩
  simp only [monsterNortonLine01SeventhUShortLookup, monsterNortonLine01SeventhUShortLabel,
    monsterNortonLine01SourceCodeLookup_label, monsterNortonLine01SourcePhysicalLookup_label]
  have h := monsterNortonLine01OctadSource_right j p
  rw [h.2.1, h.2.2, sign_lookup_label]

/-- The exact signed original coefficient of one genuine tenth-state odd-short term. -/
noncomputable def monsterNortonLine01SeventhUShortCoefficient (jp : Fin 16 × Fin 32) : ℝ :=
  (monsterNortonLine01OctadSeventhCoefficientLookup jp.1
    (monsterNortonLine01OctadSignLabel jp.2) : ℝ) *
    qSign (monsterNortonLine01ShortInversePhase (monsterNortonLine01OctadSourceA jp.1 jp.2)
      (monsterNortonLine01OctadSourceK jp.1 jp.2))

/-- The full short coordinate vector is a single lookup, retaining every actual central phase. -/
theorem monsterNortonLine01SeventhUShortLookup_actual (r : GriessShortIndex) :
    monsterNortonLine01SeventhUShortCoordinates r =
      (1 / 512 : ℝ) * (if monsterNortonLine01SeventhUShortSupport r then
        monsterNortonLine01SeventhUShortCoefficient (monsterNortonLine01SeventhUShortLookup r)
          else 0) := by
  have h := monsterNortonSparseRealLookup_eval monsterNortonLine01SeventhUShortLabel
    monsterNortonLine01SeventhUShortLookup monsterNortonLine01SeventhUShortSupport
    monsterNortonLine01SeventhUShortLookup_label
    (fun jp => by
      unfold monsterNortonLine01SeventhUShortSupport
      rw [monsterNortonLine01SeventhUShortLookup_label])
    (fun _ hr => hr) monsterNortonLine01SeventhUShortCoefficient r
  simpa only [monsterNortonLine01SeventhUShortCoordinates,
    monsterNortonLine01SeventhUShortCoefficient, monsterNortonLine01SeventhUShortLabel,
    Fintype.sum_prod_type, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mul_assoc] using
      congrArg (fun z : ℝ => (1 / 512 : ℝ) * z) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
