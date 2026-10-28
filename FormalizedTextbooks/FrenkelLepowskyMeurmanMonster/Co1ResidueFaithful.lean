/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueGeometry
public import Mathlib.Algebra.Group.TypeTags.Hom

/-! Faithfulness of the actual residue point representation. Genuine adjacency is essential
in reconstructing a line; binary sum zero by itself is not treated as genuine collinearity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source group maps to the actual binary Leech module. -/
def co1ResidueIntoBinary : Co1UniversalPresentation →* Multiplicative (Fin 24 → ZMod 2) :=
  monsterCo1GeometryUniversalBinary.toAddMonoidHom.toMultiplicative.comp co1UniversalIntoModule

/-- Original source point images retain their exact actual binary values. -/
theorem co1ResidueIntoBinary_point (p : MonsterCo1GeometryPoint) :
    co1ResidueIntoBinary (PresentedGroup.of p) = Multiplicative.ofAdd p.val := by
  change Multiplicative.ofAdd
    (monsterCo1GeometryUniversalBinary (co1UniversalIntoModule (PresentedGroup.of p)).toAdd) = _
  rw [co1UniversalIntoModule_point]
  exact congrArg Multiplicative.ofAdd (monsterCo1GeometryUniversalBinary_point p)

/-- If one genuine adjacency is known, its third point is determined by binary sum zero.
This is not a converse for arbitrary binary triples. -/
theorem co1Residue_line_of_adjacent_binary (p q r : MonsterCo1GeometryPoint)
    (hq : monsterCo1GeometryAdjacent p q) (h : p.val + q.val + r.val = 0) :
    monsterCo1GeometryLine p q r := by
  obtain ⟨s, hs⟩ := hq
  have he : r = s := Subtype.ext (add_left_cancel
    (h.trans (monsterCo1GeometryLine_binary p q s hs).symm))
  exact he ▸ hs

/-- Equality of two neighbor images in the actual central quotient identifies their
original genuine line through the base, rather than creating additional residue points. -/
theorem co1ResidueNeighborImage_eq_iff (p : MonsterCo1GeometryPoint)
    (q r : Co1ResidueNeighbor p) :
    co1ResidueNeighborImage p q.val q.property = co1ResidueNeighborImage p r.val r.property ↔
      (co1ResidueNeighborSetoid p).r q r := by
  constructor
  · intro h
    let a : co1ResidueLocal p := ⟨PresentedGroup.of q.val,
      co1ResidueLocal_neighbor_mem p q.val q.property⟩
    let b : co1ResidueLocal p := ⟨PresentedGroup.of r.val,
      co1ResidueLocal_neighbor_mem p r.val r.property⟩
    have he : (a : Co1ResidueLocalQuotient p) = (b : Co1ResidueLocalQuotient p) := h
    have hk : a / b ∈ co1ResidueBaseKernel p := QuotientGroup.eq_iff_div_mem.mp he
    rcases (co1ResidueBaseKernel_mem_iff p (a / b)).mp hk with h1 | h2
    · have hab : a = b := div_eq_one.mp h1
      have hqr := co1UniversalPoint_injective
        (congrArg (fun x : co1ResidueLocal p => x.val) hab)
      exact Or.inl (Subtype.ext hqr)
    · have hb := congrArg (fun x : co1ResidueLocal p =>
        (co1ResidueIntoBinary x.val).toAdd) h2
      change (co1ResidueIntoBinary
        ((PresentedGroup.of q.val : Co1UniversalPresentation) / PresentedGroup.of r.val)).toAdd =
        (co1ResidueIntoBinary (PresentedGroup.of p)).toAdd at hb
      rw [map_div, co1ResidueIntoBinary_point, co1ResidueIntoBinary_point,
        co1ResidueIntoBinary_point] at hb
      change q.val.val - r.val.val = p.val at hb
      have hn : -r.val.val = r.val.val := CharTwo.neg_eq _
      rw [sub_eq_add_neg, hn] at hb
      apply Or.inr
      apply co1Residue_line_of_adjacent_binary p q.val r.val q.property
      rw [add_assoc, hb]
      exact CharTwo.add_self_eq_zero _
  · rintro (rfl | hline)
    · rfl
    · exact co1ResidueNeighborImage_eq_of_base_line p q.val r.val q.property r.property hline

/-- The actual residue representation is injective on the original genuine residue points. -/
theorem co1ResiduePointImage_injective (p : MonsterCo1GeometryPoint) :
    Function.Injective (co1ResiduePointImage p) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h q =>
    induction b using Quotient.inductionOn with
    | h r =>
      intro h
      exact Quotient.sound ((co1ResidueNeighborImage_eq_iff p q r).mp h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
