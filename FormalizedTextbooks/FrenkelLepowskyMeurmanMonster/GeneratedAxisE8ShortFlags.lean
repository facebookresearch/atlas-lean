/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortLines
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortTransport

/-! Genuine E8 sections together with one of their actual short lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An actual E8 section in the orbit, together with an actual short line inside it. -/
def generatedAxisE8ShortFlags (o : Fin 759) :=
  Σ S : generatedAxisE8SectionOrbit (golayOctadWord o), generatedAxisE8ShortLines S.val

/-- The actual section-line incidence has exactly 5,594,589,000 flags. -/
theorem generatedAxisE8ShortFlags_card (o : Fin 759) :
    Nat.card (generatedAxisE8ShortFlags o) = 5594589000 := by
  let X := generatedAxisE8SectionOrbit (golayOctadWord o)
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let f : leechIsomSubgroup → X := fun g =>
    ⟨generatedAxisE8ImageSection g (golayOctadWord o), ⟨g, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨S, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite X := Finite.of_surjective f hf
  let : Fintype X := Fintype.ofFinite X
  have hs (S : X) : Nat.card (generatedAxisE8ShortLines S.val) = 120 := by
    obtain ⟨g, hg⟩ := S.property
    change generatedAxisE8ImageSection g (golayOctadWord o) = S.val at hg
    rw [← hg]
    exact generatedAxisE8ShortLines_image_card o g
  change Nat.card (Σ S : X, generatedAxisE8ShortLines S.val) = _
  rw [Nat.card_sigma]
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  change Nat.card (generatedAxisE8SectionOrbit (golayOctadWord o)) * 120 = _
  rw [generatedAxisE8_sectionOrbit_card]

/-- The actual section-preserving generators act transitively on its short labels. -/
theorem generatedAxisE8Short_coordinate_transitive (o : Fin 759)
    (r s : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o)))
    (hs : s ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves (golayOctadWord o) e ∧ griessShortPermutation e r = s := by
  obtain ⟨e, he, hpres, hvec⟩ := generatedOctad_short_transitive (golayOctadWord o)
    (golayOctadWord_mem_code o) (golayOctadWord_weight o)
    (griessShortLatticeVector r) (griessShortLatticeVector s) hr hs
    (griessShortIntegral_squareSum r) (griessShortIntegral_squareSum s)
  refine ⟨e, he, hpres, ?_⟩
  apply griessShortClass_injective
  rw [griessShortPermutation_class]
  change leechReduction (leechIntegralAction e (griessShortLatticeVector r)) =
    leechReduction (griessShortLatticeVector s)
  rw [hvec]

/-- Every actual section-line flag is reached from any incident coordinate flag. -/
theorem generatedAxisE8Short_flags_transitive (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o)))
    (S : Submodule ℤ leechIntegral) (s : GriessShortIndex)
    (hS : S ∈ generatedAxisE8SectionOrbit (golayOctadWord o))
    (hs : s ∈ generatedAxisE8ShortLines S) :
    ∃ g : leechIsomSubgroup, generatedAxisE8ImageSection g (golayOctadWord o) = S ∧
      griessShortPermutation g r = s := by
  obtain ⟨a, ha⟩ := hS
  change generatedAxisE8ImageSection a (golayOctadWord o) = S at ha
  let t := griessShortPermutation a⁻¹ s
  have hst : griessShortPermutation a t = s := by
    simp [t, map_inv]
  have ht : t ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o)) := by
    apply (generatedAxisE8ShortLines_image_mem a
      (generatedAxisE8CoordinateSection (golayOctadWord o)) t).mp
    rw [hst]
    change s ∈ generatedAxisE8ShortLines (generatedAxisE8ImageSection a (golayOctadWord o))
    rw [ha]
    exact hs
  obtain ⟨e, _, he, het⟩ := generatedAxisE8Short_coordinate_transitive o r t hr ht
  refine ⟨a * e, ?_, ?_⟩
  · rw [generatedAxisE8ImageSection_mul_preserving a e _ he, ha]
  · rw [map_mul, Equiv.Perm.mul_apply, het, hst]

/-- The actual orbit of a section and short line, using the constructed lattice action. -/
def generatedAxisE8ShortFlagOrbit (o : Fin 759) (r : GriessShortIndex) :
    Set (Submodule ℤ leechIntegral × GriessShortIndex) :=
  Set.range (fun g : leechIsomSubgroup =>
    (generatedAxisE8ImageSection g (golayOctadWord o), griessShortPermutation g r))

/-- The actual orbit is bijective with the full section-line incidence. -/
def generatedAxisE8ShortFlagOrbitEquiv (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    generatedAxisE8ShortFlagOrbit o r ≃ generatedAxisE8ShortFlags o where
  toFun x := ⟨⟨x.val.1, by
    obtain ⟨g, hg⟩ := x.property
    exact ⟨g, congrArg Prod.fst hg⟩⟩, ⟨x.val.2, by
    obtain ⟨g, hg⟩ := x.property
    have h := (generatedAxisE8ShortLines_image_mem g
      (generatedAxisE8CoordinateSection (golayOctadWord o)) r).mpr hr
    change griessShortPermutation g r ∈
      generatedAxisE8ShortLines (generatedAxisE8ImageSection g (golayOctadWord o)) at h
    change (generatedAxisE8ImageSection g (golayOctadWord o), griessShortPermutation g r) =
      x.val at hg
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hg
    change generatedAxisE8ImageSection g (golayOctadWord o) = x.val.1 at h1
    change griessShortPermutation g r = x.val.2 at h2
    rw [h1, h2] at h
    exact h⟩⟩
  invFun x := ⟨(x.1.val, x.2.val), by
    obtain ⟨g, hS, hs⟩ := generatedAxisE8Short_flags_transitive o r hr
      x.1.val x.2.val x.1.property x.2.property
    exact ⟨g, Prod.ext hS hs⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by cases x; rfl

/-- The actual orbit of any incident coordinate section-line pair has 5,594,589,000 elements. -/
theorem generatedAxisE8ShortFlagOrbit_card (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (generatedAxisE8ShortFlagOrbit o r) = 5594589000 := by
  rw [Nat.card_congr (generatedAxisE8ShortFlagOrbitEquiv o r hr),
    generatedAxisE8ShortFlags_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
