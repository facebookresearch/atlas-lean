/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

/-! The actual Golay-coordinate model of the auxiliary M22 residue geometry in Ivanov II
section 4.2. Its comparison with the Conway point residue is a separate task. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- M22 residue points are pairs outside the two distinguished Golay coordinates. -/
abbrev Co1ResidueM22Point (p q : Fin 24) :=
  {s : Finset (Fin 24) // s.card = 2 ∧ p ∉ s ∧ q ∉ s}

/-- Removing the distinguished coordinate pair from an actual containing Golay octad
produces its six-element hexad. -/
def co1ResidueM22Hexad (p q : Fin 24) (o : Fin 759) : Finset (Fin 24) :=
  ((golayOctadSupport o).erase p).erase q

/-- Every actual containing octad gives a hexad of exactly six coordinates. -/
theorem co1ResidueM22Hexad_card (p q : Fin 24) (hpq : p ≠ q) (o : Fin 759)
    (hp : p ∈ golayOctadSupport o) (hq : q ∈ golayOctadSupport o) :
    (co1ResidueM22Hexad p q o).card = 6 := by
  have hqe : q ∈ (golayOctadSupport o).erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  rw [co1ResidueM22Hexad, Finset.card_erase_of_mem hqe, Finset.card_erase_of_mem hp,
    golayOctadSupport_card]

/-- A hexad never contains either distinguished coordinate. -/
theorem co1ResidueM22Hexad_not_mem (p q : Fin 24) (o : Fin 759) :
    p ∉ co1ResidueM22Hexad p q o ∧ q ∉ co1ResidueM22Hexad p q o := by
  simp [co1ResidueM22Hexad]

/-- The original auxiliary M22 lines partition an actual Golay hexad into three pair points.
No binary collinearity predicate replaces this octad condition. -/
def co1ResidueM22Line (p q : Fin 24) (a b c : Co1ResidueM22Point p q) : Prop :=
  ∃ o : Fin 759, p ∈ golayOctadSupport o ∧ q ∈ golayOctadSupport o ∧
    a.val ∪ b.val ∪ c.val = co1ResidueM22Hexad p q o

/-- Six-coordinate labels for any actual Golay hexad. -/
def co1ResidueM22HexadCoordinates (p q : Fin 24) (hpq : p ≠ q) (o : Fin 759)
    (hp : p ∈ golayOctadSupport o) (hq : q ∈ golayOctadSupport o) :
    Fin 6 ≃ (co1ResidueM22Hexad p q o) :=
  (co1ResidueM22Hexad p q o).equivFinOfCardEq (co1ResidueM22Hexad_card p q hpq o hp hq) |>.symm

/-- An unordered pair of distinct hexad coordinates is an actual auxiliary M22 point. -/
def co1ResidueM22HexadPair (p q : Fin 24) (o : Fin 759)
    (e : Fin 6 ≃ (co1ResidueM22Hexad p q o)) (a b : Fin 6) (hab : a ≠ b) :
    Co1ResidueM22Point p q :=
  ⟨{(e a).val, (e b).val}, by
    have he : (e a).val ≠ (e b).val := Subtype.val_injective.ne (e.injective.ne hab)
    have hpa := (co1ResidueM22Hexad_not_mem p q o).1
    have hqa := (co1ResidueM22Hexad_not_mem p q o).2
    refine ⟨by simp [he], ?_, ?_⟩
    · intro hi
      apply hpa
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with h | h
      · exact Eq.mpr (congrArg (fun i : Fin 24 => i ∈ co1ResidueM22Hexad p q o) h)
          (e a).property
      · exact Eq.mpr (congrArg (fun i : Fin 24 => i ∈ co1ResidueM22Hexad p q o) h)
          (e b).property
    · intro hi
      apply hqa
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with h | h
      · exact Eq.mpr (congrArg (fun i : Fin 24 => i ∈ co1ResidueM22Hexad p q o) h)
          (e a).property
      · exact Eq.mpr (congrArg (fun i : Fin 24 => i ∈ co1ResidueM22Hexad p q o) h)
          (e b).property⟩

/-- Exchanging hexad coordinates leaves their actual unordered point unchanged. -/
theorem co1ResidueM22HexadPair_swap (p q : Fin 24) (o : Fin 759)
    (e : Fin 6 ≃ (co1ResidueM22Hexad p q o)) (a b : Fin 6) (hab : a ≠ b) :
    co1ResidueM22HexadPair p q o e a b hab =
      co1ResidueM22HexadPair p q o e b a hab.symm :=
  Subtype.ext (Finset.pair_comm _ _)

/-- Every perfect matching of an actual Golay hexad is an original auxiliary M22 line. -/
theorem co1ResidueM22HexadPair_line (p q : Fin 24) (o : Fin 759)
    (hp : p ∈ golayOctadSupport o) (hq : q ∈ golayOctadSupport o)
    (e : Fin 6 ≃ (co1ResidueM22Hexad p q o)) (v : Fin 6 → Fin 6)
    (hv : Function.Bijective v) :
    co1ResidueM22Line p q
      (co1ResidueM22HexadPair p q o e (v 0) (v 1) (hv.injective.ne (by decide +kernel)))
      (co1ResidueM22HexadPair p q o e (v 2) (v 3) (hv.injective.ne (by decide +kernel)))
      (co1ResidueM22HexadPair p q o e (v 4) (v 5) (hv.injective.ne (by decide +kernel))) := by
  refine ⟨o, hp, hq, ?_⟩
  ext i
  constructor
  · intro hi
    simp only [co1ResidueM22HexadPair, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl) <;> exact (e _).property
  · intro hi
    obtain ⟨a, ha⟩ := e.surjective ⟨i, hi⟩
    obtain ⟨k, hk⟩ := hv.surjective a
    have he : (e (v k)).val = i := congrArg Subtype.val (hk ▸ ha)
    rw [← he]
    fin_cases k <;> simp [co1ResidueM22HexadPair]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
