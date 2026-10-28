/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual three-octad syndrome kernel is isotropic. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadKernelCardinality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadLagrangian

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The three sign vectors in actual physical coordinates. -/
def octadTriplePhysicalVectors (o p u : Fin 759) (x : OctadTripleSignSpace) :
    Fin 3 → Fin 24 → ZMod 2 :=
  ![octadPhysicalSignMap o (x 0), octadPhysicalSignMap p (x 1),
    octadPhysicalSignMap u (x 2)]

/-- Physical vectors retain the exact canonical triple form. -/
theorem octadTripleForm_eq_physical (o p u : Fin 759) (x y : OctadTripleSignSpace) :
    octadTripleForm x y =
      ∑ s : Fin 3, ∑ i, octadTriplePhysicalVectors o p u x s i *
        octadTriplePhysicalVectors o p u y s i := by
  change (∑ s, octadSignForm (x s) (y s)) = _
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  change octadSignForm (x 0) (y 0) + octadSignForm (x 1) (y 1) +
    octadSignForm (x 2) (y 2) =
      (∑ i, octadPhysicalSignMap o (x 0) i * octadPhysicalSignMap o (y 0) i) +
      (∑ i, octadPhysicalSignMap p (x 1) i * octadPhysicalSignMap p (y 1) i) +
      (∑ i, octadPhysicalSignMap u (x 2) i * octadPhysicalSignMap u (y 2) i)
  rw [octadPhysicalSignMap_pairing, octadPhysicalSignMap_pairing,
    octadPhysicalSignMap_pairing]

/-- The actual physical vectors have the two-parent support pattern. -/
theorem octadTriplePhysicalVectors_supported (o p u : Fin 759) (x : OctadTripleSignSpace)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    ∀ s i, (if s = 0 then golayOctadWord o i else if s = 1 then golayOctadWord p i
      else golayOctadWord o i + golayOctadWord p i) = 0 →
      octadTriplePhysicalVectors o p u x s i = 0 := by
  intro s i hi
  fin_cases s
  · change golayOctadWord o i = 0 at hi
    apply octadPhysicalSignMap_supported
    intro him
    exact ((golayOctadWord_ne_zero_iff o i).mpr him) hi
  · change golayOctadWord p i = 0 at hi
    apply octadPhysicalSignMap_supported
    intro him
    exact ((golayOctadWord_ne_zero_iff p i).mpr him) hi
  · change golayOctadWord o i + golayOctadWord p i = 0 at hi
    have hz : golayOctadWord u i = 0 := by rw [hu]; exact hi
    apply octadPhysicalSignMap_supported
    intro him
    exact ((golayOctadWord_ne_zero_iff u i).mpr him) hz

/-- Each actual physical sign vector has even parity. -/
theorem octadTriplePhysicalVectors_even (o p u : Fin 759) (x : OctadTripleSignSpace) :
    ∀ s, (∑ i, octadTriplePhysicalVectors o p u x s i) = 0 := by
  intro s
  fin_cases s <;> apply octadPhysicalSignMap_even

/-- The actual homogeneous syndrome kernel is isotropic for the triple form. -/
theorem octadTripleSyndromeKernel_isotropic (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (x : OctadTripleSignSpace) (hx : x ∈ octadTripleSyndromeKernel o p u)
    (y : OctadTripleSignSpace) (hy : y ∈ octadTripleSyndromeKernel o p u) :
    octadTripleForm x y = 0 := by
  rw [octadTripleForm_eq_physical o p u]
  apply octadTriple_physical_isotropic_of_span
    (golayOctadWord o) (golayOctadWord p) _ _
    (octadTriplePhysicalVectors_supported o p u x hu)
    (octadTriplePhysicalVectors_supported o p u y hu)
    (octadTriplePhysicalVectors_even o p u x) (octadTriplePhysicalVectors_even o p u y)
  · obtain ⟨a,b,h⟩ := octadTripleSyndromeKernel_span o p u hfour hu x hx
    exact Submodule.mem_span_pair.mpr ⟨a,b,h.symm⟩
  · obtain ⟨a,b,h⟩ := octadTripleSyndromeKernel_span o p u hfour hu y hy
    exact Submodule.mem_span_pair.mpr ⟨a,b,h.symm⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
