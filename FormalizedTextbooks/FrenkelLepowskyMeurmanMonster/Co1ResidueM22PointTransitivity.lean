/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22Automorphisms

/-! Five-transitivity of the actual Golay action gives actual auxiliary pair-point transitivity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual pair point is reached from the base
by a genuine Golay automorphism fixing0 and1. -/
theorem co1ResidueM22Point_transitive (s : Co1ResidueM22Point 0 1) :
    ∃ g : golayAutomorphismSubgroup, ∃ h0 : g.val 0 = 0, ∃ h1 : g.val 1 = 1,
      co1ResidueM22PointMap g h0 h1 (co1ResidueM22FinitePoint 0) = s := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp s.property.1
  have hma : a ∈ s.val := by rw [hs]; simp
  have hmb : b ∈ s.val := by rw [hs]; simp
  have ha0 : a ≠ 0 := fun h => s.property.2.1 (h ▸ hma)
  have hb0 : b ≠ 0 := fun h => s.property.2.1 (h ▸ hmb)
  have ha1 : a ≠ 1 := fun h => s.property.2.2 (h ▸ hma)
  have hb1 : b ≠ 1 := fun h => s.property.2.2 (h ▸ hmb)
  let S := ({0, 1} : Finset (Fin 24)) ∪ s.val
  have hS : S.card ≤ 4 := by
    have h := Finset.card_union_le ({0, 1} : Finset (Fin 24)) s.val
    have h01 : ({0, 1} : Finset (Fin 24)).card = 2 := by decide +kernel
    rw [h01, s.property.1] at h
    exact h
  have hcn : ∃ c : Fin 24, c ∉ S := by
    by_contra hn
    push Not at hn
    have h := Finset.card_le_card (show (Finset.univ : Finset (Fin 24)) ⊆ S from
      fun i _ => hn i)
    have hu : (Finset.univ : Finset (Fin 24)).card = 24 := by decide +kernel
    rw [hu] at h
    omega
  obtain ⟨c, hc⟩ := hcn
  have hc0 : c ≠ 0 := by intro h; exact hc (by simp [S, h])
  have hc1 : c ≠ 1 := by intro h; exact hc (by simp [S, h])
  have hca : c ≠ a := by intro h; exact hc (by simp [S, hs, h])
  have hcb : c ≠ b := by intro h; exact hc (by simp [S, hs, h])
  let t : Fin 5 → Fin 24 := ![0, 1, a, b, c]
  have ht : Function.Injective t := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [t]
  obtain ⟨g, hg⟩ := golayAutomorphism_maps_firstFive t ht
  have h0 : g.val 0 = 0 := hg 0
  have h1 : g.val 1 = 1 := hg 1
  refine ⟨g, h0, h1, Subtype.ext ?_⟩
  change ({2, 3} : Finset (Fin 24)).image g.val = s.val
  have h2 : g.val 2 = a := hg 2
  have h3 : g.val 3 = b := hg 3
  simp only [Finset.image_insert, Finset.image_singleton, h2, h3, hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
