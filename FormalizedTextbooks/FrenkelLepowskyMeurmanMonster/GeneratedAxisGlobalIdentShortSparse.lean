/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortCoordinateCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortTables

/-! # Sparse short blocks and their local transport

A sparse short block is a list of flat short labels with integer numerators.  Flat labels
enumerate `GriessShortIndex` as pairs `0..551`, octad labels `552 + 64 o + e` and odd labels
`49128 + 24 d + i`.  A local fiber element with valid mask data
(`GeneratedAxisGlobalIdentShortMask`) transports such a block term by term: the preferred mask
of each source label is mapped by the data, compared with the preferred mask of the claimed
target label, and the central bit gives the sign.  One boolean check over the whole list
certifies the complete transported block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-- Flat short labels: pairs `0..551`, octads `552..49127`, odd labels `49128..98279`. -/
def shortDecode (j : ℕ) : GriessShortIndex :=
  if j < 552 then
    Sum.inl (⟨j / 276 % 2, Nat.mod_lt _ (by decide)⟩, ⟨j % 276, Nat.mod_lt _ (by decide)⟩)
  else if j < 49128 then
    Sum.inr (Sum.inl (⟨(j - 552) / 64 % 759, Nat.mod_lt _ (by decide)⟩,
      ⟨(j - 552) % 64, Nat.mod_lt _ (by decide)⟩))
  else
    Sum.inr (Sum.inr (⟨(j - 49128) / 24 % 2048, Nat.mod_lt _ (by decide)⟩,
      ⟨(j - 49128) % 24, Nat.mod_lt _ (by decide)⟩))

/-- The flat label of a short label. -/
def shortEncode : GriessShortIndex → ℕ
  | Sum.inl (s, p) => 276 * s.val + p.val
  | Sum.inr (Sum.inl (o, e)) => 552 + 64 * o.val + e.val
  | Sum.inr (Sum.inr (d, i)) => 49128 + 24 * d.val + i.val

/-- Decoding inverts encoding. -/
theorem shortDecode_encode (r : GriessShortIndex) : shortDecode (shortEncode r) = r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · have h1 : 276 * s.val + p.val < 552 := by omega
    simp only [shortDecode, shortEncode, h1, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq]
    constructor <;> apply Fin.ext <;> simp only <;> omega
  · have h1 : ¬ 552 + 64 * o.val + e.val < 552 := by omega
    have h2 : 552 + 64 * o.val + e.val < 49128 := by omega
    simp only [shortDecode, shortEncode, h1, h2, ↓reduceIte, Sum.inr.injEq, Sum.inl.injEq,
      Prod.mk.injEq]
    constructor <;> apply Fin.ext <;> simp only <;> omega
  · have h1 : ¬ 49128 + 24 * d.val + i.val < 552 := by omega
    have h2 : ¬ 49128 + 24 * d.val + i.val < 49128 := by omega
    simp only [shortDecode, shortEncode, h1, h2, ↓reduceIte, Sum.inr.injEq, Prod.mk.injEq]
    constructor <;> apply Fin.ext <;> simp only <;> omega

/-- The preferred mask of a flat short label, read from the packed catalogue tables. -/
def shortMaskFlat (j : ℕ) : ℕ := identShortMaskR (shortDecode j)

/-- The preferred lift of a flat short label is its unsigned mask. -/
theorem griessShortQ_flat (j : ℕ) :
    griessShortQ (shortDecode j) = qmElt (shortMaskFlat j, false) := by
  rw [qmElt_false, shortMaskFlat, identShortMaskR_eq, ← generatedAxisGlobalShortMask_Q_actual,
    generatedAxisGlobalShortQFinite_actual]

/-- The real short block of a sparse list of flat labels and integer numerators. -/
noncomputable def shortVec (L : List (ℕ × ℤ)) : GriessShortIndex → ℝ :=
  (L.map (fun p => (p.2 : ℝ) • Pi.single (shortDecode p.1) (1 : ℝ))).sum

/-- The empty list is the zero block. -/
theorem shortVec_nil : shortVec [] = 0 := rfl

/-- A cons adds one term. -/
theorem shortVec_cons (p : ℕ × ℤ) (L : List (ℕ × ℤ)) :
    shortVec (p :: L) = (p.2 : ℝ) • Pi.single (shortDecode p.1) (1 : ℝ) + shortVec L := by
  simp only [shortVec, List.map_cons, List.sum_cons]

/-- Coordinates of a sparse block. -/
theorem shortVec_apply (L : List (ℕ × ℤ)) (r : GriessShortIndex) :
    shortVec L r = ((L.filter (fun p => decide (shortDecode p.1 = r))).map
      (fun p => (p.2 : ℝ))).sum := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [shortVec_cons, Pi.add_apply, ih, List.filter_cons]
    by_cases h : shortDecode p.1 = r
    · simp [h]
    · simp [h, Ne.symm h]

/-- One checked transported term: target mask and central sign. -/
def shortTermCheck (d : QMaskData) (s t : ℕ × ℤ) : Bool :=
  let p := d.step (shortMaskFlat s.1, false)
  p.1 == shortMaskFlat t.1 && t.2 == (if p.2 then -s.2 else s.2)

/-- All terms of a sparse list are transported to the terms of the target list. -/
def shortCheck (d : QMaskData) : List (ℕ × ℤ) → List (ℕ × ℤ) → Bool
  | [], [] => true
  | s :: L, t :: L' => shortTermCheck d s t && shortCheck d L L'
  | _, _ => false

/-- A checked list is the exact image of a sparse short block under the local short operator. -/
theorem shortVec_transport (f : localFiberSubgroup) (d : QMaskData)
    (hd : d.Valid (spinConjugation f.val.1)) :
    ∀ (L L' : List (ℕ × ℤ)), shortCheck d L L' = true →
      localShortOperator f (shortVec L) = shortVec L'
  | [], [], _ => by simp [shortVec]
  | [], _ :: _, h => by simp [shortCheck] at h
  | _ :: _, [], h => by simp [shortCheck] at h
  | s :: L, t :: L', h => by
    simp only [shortCheck, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := shortVec_transport f d hd L L' h2
    simp only [shortTermCheck, Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨hm, hc⟩ := h1
    have hq : spinConjugation f.val.1 (monsterNortonShortQ (shortDecode s.1)) =
        qCentral (golayBooleanCast (d.step (shortMaskFlat s.1, false)).2) *
          monsterNortonShortQ (shortDecode t.1) := by
      rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, griessShortQ_flat, griessShortQ_flat,
        d.step_spec _ hd, qmElt_false]
      unfold qmElt
      rw [hm]
    have hb := monsterNortonShortBasis_of_Q_image f _ _ _ hq
    rw [shortVec_cons, shortVec_cons, map_add, map_smul, ih, hb, hc, smul_smul]
    congr 1
    cases (d.step (shortMaskFlat s.1, false)).2 <;> simp [golayBooleanCast]

/-- Checked transport of the short block of an actual Griess vector. -/
theorem shortVec_rhoLocal (f : localFiberSubgroup) (d : QMaskData)
    (hd : d.Valid (spinConjugation f.val.1)) (L L' : List (ℕ × ℤ))
    (h : shortCheck d L L' = true) (x : GriessSpace) (D : ℝ)
    (hx : (griessConwayEncode x).2.1 = D • shortVec L) :
    (griessConwayEncode (rhoLocal (localFiberIntoH f) x)).2.1 = D • shortVec L' := by
  change (griessConwayEncode (localGriessRepresentation f x)).2.1 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localShortOperator f (griessConwayEncode x).2.1 = _
  rw [hx, map_smul, shortVec_transport f d hd L L' h]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
