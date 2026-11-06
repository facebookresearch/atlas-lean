/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Assemble all actual octad products from the remaining four-point intersection case. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SameOctadPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProductCompletion

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Equal octads and intersections of size zero or two are already proved.
Only the actual four-point intersection family remains as an explicit input. -/
theorem sExtra_preserves_octad_product_of_four
    (hfour : ∀ (o p : Fin 759) (e f : Fin 64),
      (golayOctadIntersection o p).card = 4 →
      TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f))
    (o : Fin 759) (e : Fin 64) (p : Fin 759) (f : Fin 64) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f) := by
  by_cases hop : o = p
  · subst p
    exact sExtra_preserves_sameOctad_product o e f
  · rcases golayOctad_intersection_le_two_or_four o p hop with hs | hf
    · exact sExtra_octad_product_small_intersection o p e f hop hs
    · exact hfour o p e f hf

/-- The full product law requires only the four-point octad intersection
and octad×XYZ families; all other cases are instantiated with proved facts. -/
theorem sExtra_preserves_product_of_four_and_octadXYZ
    (hfour : ∀ (o p : Fin 759) (e f : Fin 64),
      (golayOctadIntersection o p).card = 4 →
      TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f))
    (hOT : ∀ (o : Fin 759) (e : Fin 64) (s : Fin 3) (k : Fin 49152),
      TrialityProductPreserved (trialityOctadBasis o e) (trialityXYZBasis s k)) :
    ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y) :=
  sExtra_preserves_product_of_octad_pairs
    (sExtra_preserves_octad_product_of_four hfour) hOT

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
