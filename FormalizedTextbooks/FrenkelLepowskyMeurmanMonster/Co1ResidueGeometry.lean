/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueLocalRepresentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineBinary

/-! Actual residue points are genuine lines through the distinguished point, represented by
one of their two other points. The group image is independent of this choice. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual neighbors of a point, with original genuine adjacency. -/
abbrev Co1ResidueNeighbor (p : MonsterCo1GeometryPoint) :=
  {q : MonsterCo1GeometryPoint // monsterCo1GeometryAdjacent p q}

/-- A pair of fixed original points has at most one third point on a genuine line.
Only the forward genuine-line binary identity is used. -/
theorem co1Residue_line_third_unique (p q r s : MonsterCo1GeometryPoint)
    (hr : monsterCo1GeometryLine p q r) (hs : monsterCo1GeometryLine p q s) : r = s := by
  apply Subtype.ext
  exact add_left_cancel ((monsterCo1GeometryLine_binary p q r hr).trans
    (monsterCo1GeometryLine_binary p q s hs).symm)

/-- Two neighbors represent the same residue point precisely when they coincide or lie
on one genuine original line with the base. -/
def co1ResidueNeighborSetoid (p : MonsterCo1GeometryPoint) : Setoid (Co1ResidueNeighbor p) where
  r q r := q = r ∨ monsterCo1GeometryLine p q.val r.val
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro q r h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (monsterCo1GeometryLine_swap_last p q.val r.val h)
    trans := by
      intro q r s hqr hrs
      rcases hqr with rfl | hqr
      · exact hrs
      rcases hrs with rfl | hrs
      · exact Or.inr hqr
      apply Or.inl
      apply Subtype.ext
      exact co1Residue_line_third_unique p r.val q.val s.val
        (monsterCo1GeometryLine_swap_last p q.val r.val hqr) hrs }

/-- The actual unordered lines through the distinguished point, viewed as residue points. -/
abbrev Co1ResiduePoint (p : MonsterCo1GeometryPoint) :=
  Quotient (co1ResidueNeighborSetoid p)

/-- The actual source group representation on residue points; the original base-line
product proves that its value does not depend on which other point is chosen. -/
def co1ResiduePointImage (p : MonsterCo1GeometryPoint) :
    Co1ResiduePoint p → Co1ResidueLocalQuotient p :=
  Quotient.lift (fun q => co1ResidueNeighborImage p q.val q.property) (by
    intro q r h
    rcases h with rfl | h
    · rfl
    · exact co1ResidueNeighborImage_eq_of_base_line p q.val r.val q.property r.property h)

/-- The residue point image is the original neighbor image on representatives. -/
theorem co1ResiduePointImage_mk (p : MonsterCo1GeometryPoint) (q : Co1ResidueNeighbor p) :
    co1ResiduePointImage p (Quotient.mk (co1ResidueNeighborSetoid p) q) =
      co1ResidueNeighborImage p q.val q.property := rfl

/-- Genuine original triples within the neighborhood induce residue triples. In particular,
any source plane with such representatives supplies this relation. -/
def co1ResidueLine (p : MonsterCo1GeometryPoint) (a b c : Co1ResiduePoint p) : Prop :=
  ∃ q r s : Co1ResidueNeighbor p, monsterCo1GeometryLine q.val r.val s.val ∧
    Quotient.mk (co1ResidueNeighborSetoid p) q = a ∧
    Quotient.mk (co1ResidueNeighborSetoid p) r = b ∧
    Quotient.mk (co1ResidueNeighborSetoid p) s = c

/-- Each actual residue point is represented by an involution in the central point quotient. -/
theorem co1ResiduePointImage_mul_self (p : MonsterCo1GeometryPoint) (a : Co1ResiduePoint p) :
    co1ResiduePointImage p a * co1ResiduePointImage p a = 1 := by
  induction a using Quotient.inductionOn with
  | h q => exact co1ResidueNeighborImage_mul_self p q.val q.property

/-- The group representation retains every genuinely induced residue triple product. -/
theorem co1ResiduePointImage_line (p : MonsterCo1GeometryPoint) (a b c : Co1ResiduePoint p)
    (h : co1ResidueLine p a b c) :
    co1ResiduePointImage p a * co1ResiduePointImage p b * co1ResiduePointImage p c = 1 := by
  obtain ⟨q, r, s, hline, rfl, rfl, rfl⟩ := h
  exact co1ResidueNeighborImage_line p q.val r.val s.val q.property r.property s.property hline

/-- The actual residue point images generate the whole first-neighborhood quotient. -/
theorem co1ResiduePointImage_generates (p : MonsterCo1GeometryPoint) :
    Subgroup.closure (Set.range (co1ResiduePointImage p)) = ⊤ := by
  apply top_unique
  rw [← co1ResidueNeighborImage_generates p]
  apply Subgroup.closure_mono
  rintro _ ⟨q, rfl⟩
  exact ⟨Quotient.mk (co1ResidueNeighborSetoid p) q, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
