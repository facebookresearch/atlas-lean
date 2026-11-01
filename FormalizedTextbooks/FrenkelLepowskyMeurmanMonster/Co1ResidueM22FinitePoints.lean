/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FiniteData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22Geometry

/-! The literal 231-pair table is an exact enumeration of the actual auxiliary M22 points,
not a replacement carrier. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All literal pairs are increasing and outside the two distinguished coordinates. -/
theorem co1ResidueM22FinitePairs_bounds : ∀ i : Fin 231,
    2 ≤ (co1ResidueM22FinitePairs i).1.val ∧
      (co1ResidueM22FinitePairs i).1.val < (co1ResidueM22FinitePairs i).2.val := by
  decide +kernel

/-- Distinct literal indices give distinct actual increasing pairs. -/
theorem co1ResidueM22FinitePairs_injective : Function.Injective co1ResidueM22FinitePairs := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Kernel-check all increasing coordinate pairs against the 231 literal addresses.
/-- Every increasing pair outside the two distinguished coordinates occurs in the literal table. -/
theorem co1ResidueM22FinitePairs_covers : ∀ a b : Fin 24, 2 ≤ a.val → a.val < b.val →
    ∃ i : Fin 231, co1ResidueM22FinitePairs i = (a, b) := by
  decide +kernel

/-- The literal pair index denotes its actual auxiliary M22 point. -/
def co1ResidueM22FinitePoint (i : Fin 231) : Co1ResidueM22Point 0 1 :=
  ⟨{(co1ResidueM22FinitePairs i).1, (co1ResidueM22FinitePairs i).2}, by
    obtain ⟨ha, hb⟩ := co1ResidueM22FinitePairs_bounds i
    have hn : (co1ResidueM22FinitePairs i).1 ≠ (co1ResidueM22FinitePairs i).2 := by
      intro h
      have he := congrArg (fun a : Fin 24 => a.val) h
      omega
    have ha0 : (co1ResidueM22FinitePairs i).1 ≠ 0 := by
      intro h
      have he := congrArg (fun a : Fin 24 => a.val) h
      omega
    have hb0 : (co1ResidueM22FinitePairs i).2 ≠ 0 := by
      intro h
      have he := congrArg (fun a : Fin 24 => a.val) h
      omega
    have ha1 : (co1ResidueM22FinitePairs i).1 ≠ 1 := by
      intro h
      have he := congrArg (fun a : Fin 24 => a.val) h
      omega
    have hb1 : (co1ResidueM22FinitePairs i).2 ≠ 1 := by
      intro h
      have he := congrArg (fun a : Fin 24 => a.val) h
      omega
    refine ⟨Finset.card_pair hn, ?_, ?_⟩
    · simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        And.intro (fun h => ha0 h.symm) (fun h => hb0 h.symm)
    · simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        And.intro (fun h => ha1 h.symm) (fun h => hb1 h.symm)⟩

/-- The actual point map of the literal increasing-pair enumeration is injective. -/
theorem co1ResidueM22FinitePoint_injective : Function.Injective co1ResidueM22FinitePoint := by
  intro i j hij
  have hs := congrArg (fun s : Co1ResidueM22Point 0 1 => s.val) hij
  have he := congrArg (fun s : Finset (Fin 24) => (s : Set (Fin 24))) hs
  simp only [co1ResidueM22FinitePoint, Finset.coe_insert, Finset.coe_singleton] at he
  rcases Set.pair_eq_pair_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact co1ResidueM22FinitePairs_injective (Prod.ext ha hb)
  · have hi := (co1ResidueM22FinitePairs_bounds i).2
    have hj := (co1ResidueM22FinitePairs_bounds j).2
    have hav := congrArg (fun a : Fin 24 => a.val) ha
    have hbv := congrArg (fun a : Fin 24 => a.val) hb
    omega

/-- Every actual auxiliary M22 point occurs in the literal finite enumeration. -/
theorem co1ResidueM22FinitePoint_surjective : Function.Surjective co1ResidueM22FinitePoint := by
  intro s
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp s.property.1
  have hma : a ∈ s.val := by rw [he]; simp
  have hmb : b ∈ s.val := by rw [he]; simp
  have ha0 : a.val ≠ 0 := fun h => s.property.2.1 ((show a = (0 : Fin 24) from Fin.ext h) ▸ hma)
  have hb0 : b.val ≠ 0 := fun h => s.property.2.1 ((show b = (0 : Fin 24) from Fin.ext h) ▸ hmb)
  have ha1 : a.val ≠ 1 := fun h => s.property.2.2 ((show a = (1 : Fin 24) from Fin.ext h) ▸ hma)
  have hb1 : b.val ≠ 1 := fun h => s.property.2.2 ((show b = (1 : Fin 24) from Fin.ext h) ▸ hmb)
  have hav : 2 ≤ a.val := by omega
  have hbv : 2 ≤ b.val := by omega
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  by_cases hlt : a.val < b.val
  · obtain ⟨i, hi⟩ := co1ResidueM22FinitePairs_covers a b hav hlt
    refine ⟨i, Subtype.ext ?_⟩
    change {(co1ResidueM22FinitePairs i).1, (co1ResidueM22FinitePairs i).2} = s.val
    rw [hi, he]
  · obtain ⟨i, hi⟩ := co1ResidueM22FinitePairs_covers b a hbv (by omega)
    refine ⟨i, Subtype.ext ?_⟩
    change {(co1ResidueM22FinitePairs i).1, (co1ResidueM22FinitePairs i).2} = s.val
    rw [hi, he]
    exact Finset.pair_comm _ _

/-- Exact equivalence between the literal finite addresses and the actual auxiliary points. -/
def co1ResidueM22FinitePointEquiv : Fin 231 ≃ Co1ResidueM22Point 0 1 :=
  Equiv.ofBijective co1ResidueM22FinitePoint
    ⟨co1ResidueM22FinitePoint_injective, co1ResidueM22FinitePoint_surjective⟩

/-- The actual rooted auxiliary M22 geometry has exactly 231 points. -/
theorem co1ResidueM22Point_card : Nat.card (Co1ResidueM22Point 0 1) = 231 := by
  rw [← Nat.card_congr co1ResidueM22FinitePointEquiv, Nat.card_fin]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
