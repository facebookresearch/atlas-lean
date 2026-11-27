/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneCage

/-!
# First and last contacts of a planar path with a line

For a continuous path in `ℝ²` and a coordinate line `{z i = a}` that it reaches, the first and
last contact times and the excursions of the path on one side of the line.

## i. Overview

If a path starts on one side of the line and ends on the other, there is a first contact time
`t` with the line, and the subpath before `t` stays on the starting side; symmetrically for the
last contact and the subpath after it. If a path starts and ends below the line and visits
`{z i ≥ a}` at time `t`, the last contact before `t` and the first contact after `t` cut out an
excursion from the line to the line staying in `{z i ≥ a}` (and symmetrically for lower
excursions). These are the topological inputs of the crosscut arguments; all results are
proved unconditionally.

## ii. Key results

- `exists_first_line_contact_prefix_in_halfPlane`, `exists_last_line_contact_suffix_in_halfPlane`.
- `exists_upper_line_excursion_path`, `exists_lower_line_excursion_path`.

## iii. Table of contents

- A. First and last contacts
- B. Excursions above and below a line

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open Set

namespace StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut

/-! ## A. First and last contacts -/

lemma exists_first_line_contact_prefix_in_halfPlane
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i <= a)
    (hfinish : a <= finish i) :
    exists t : unitInterval,
      gamma t i = a /\
      (forall u : unitInterval, gamma u i = a -> t <= u) /\
      Set.range (gamma.subpath 0 t) <= Set.range gamma /\
      forall z : Fin 2 -> Real,
        z ∈ Set.range (gamma.subpath 0 t) -> z i <= a := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq gamma i a hstart hfinish
  obtain ⟨t, ht, htfirst⟩ :=
    exists_first_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htfirst, ?_, ?_⟩
  · rw [Path.range_subpath]
    exact image_subset_range _ _
  · intro z hz
    rw [Path.range_subpath_of_le gamma 0 t t.2.1] at hz
    obtain ⟨u, huIcc, rfl⟩ := hz
    by_contra hnot
    have huAbove : a <= gamma u i := (lt_of_not_ge hnot).le
    obtain ⟨s, hs⟩ := exists_parameter_coord_eq
      (gamma.subpath 0 u) i a (by simpa using hstart) huAbove
    have hsMem : gamma.subpath 0 u s ∈
        Set.range (gamma.subpath 0 u) := ⟨s, rfl⟩
    rw [Path.range_subpath_of_le gamma 0 u u.2.1] at hsMem
    obtain ⟨v, hvIcc, hv⟩ := hsMem
    have hvLine : gamma v i = a := by
      rw [hv]
      exact hs
    have hvFirst : t <= v := htfirst v hvLine
    have huv : u = v := le_antisymm (huIcc.2.trans hvFirst) hvIcc.2
    have huLine : gamma u i = a := by simpa [huv] using hvLine
    exact (lt_of_not_ge hnot).ne' huLine

lemma exists_last_line_contact_suffix_in_halfPlane
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i <= a)
    (hfinish : a <= finish i) :
    exists t : unitInterval,
      gamma t i = a /\
      (forall u : unitInterval, gamma u i = a -> u <= t) /\
      Set.range (gamma.subpath t 1) <= Set.range gamma /\
      forall z : Fin 2 -> Real,
        z ∈ Set.range (gamma.subpath t 1) -> a <= z i := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq gamma i a hstart hfinish
  obtain ⟨t, ht, htlast⟩ :=
    exists_last_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htlast, ?_, ?_⟩
  · rw [Path.range_subpath]
    exact image_subset_range _ _
  · intro z hz
    rw [Path.range_subpath_of_le gamma t 1 t.2.2] at hz
    obtain ⟨u, huIcc, rfl⟩ := hz
    by_contra hnot
    have huBelow : gamma u i <= a := (lt_of_not_ge hnot).le
    obtain ⟨s, hs⟩ := exists_parameter_coord_eq
      (gamma.subpath u 1) i a huBelow (by simpa using hfinish)
    have hsMem : gamma.subpath u 1 s ∈
        Set.range (gamma.subpath u 1) := ⟨s, rfl⟩
    rw [Path.range_subpath_of_le gamma u 1 u.2.2] at hsMem
    obtain ⟨v, hvIcc, hv⟩ := hsMem
    have hvLine : gamma v i = a := by
      rw [hv]
      exact hs
    have hvLast : v <= t := htlast v hvLine
    have huv : u = v := le_antisymm hvIcc.1 (hvLast.trans huIcc.1)
    have huLine : gamma u i = a := by simpa [huv] using hvLine
    exact (lt_of_not_ge hnot).ne huLine

lemma exists_first_line_contact_prefix_in_upperHalfPlane
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : a <= start i)
    (hfinish : finish i <= a) :
    exists t : unitInterval,
      gamma t i = a /\
      (forall u : unitInterval, gamma u i = a -> t <= u) /\
      Set.range (gamma.subpath 0 t) <= Set.range gamma /\
      forall z : Fin 2 -> Real,
        z ∈ Set.range (gamma.subpath 0 t) -> a <= z i := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq_of_ge
    gamma i a hstart hfinish
  obtain ⟨t, ht, htfirst⟩ :=
    exists_first_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htfirst, ?_, ?_⟩
  · rw [Path.range_subpath]
    exact image_subset_range _ _
  · intro z hz
    rw [Path.range_subpath_of_le gamma 0 t t.2.1] at hz
    obtain ⟨u, huIcc, rfl⟩ := hz
    by_contra hnot
    have huBelow : gamma u i <= a := (lt_of_not_ge hnot).le
    obtain ⟨s, hs⟩ := exists_parameter_coord_eq_of_ge
      (gamma.subpath 0 u) i a (by simpa using hstart) huBelow
    have hsMem : gamma.subpath 0 u s ∈
        Set.range (gamma.subpath 0 u) := ⟨s, rfl⟩
    rw [Path.range_subpath_of_le gamma 0 u u.2.1] at hsMem
    obtain ⟨v, hvIcc, hv⟩ := hsMem
    have hvLine : gamma v i = a := by
      rw [hv]
      exact hs
    have hvFirst : t <= v := htfirst v hvLine
    have huv : u = v := le_antisymm (huIcc.2.trans hvFirst) hvIcc.2
    have huLine : gamma u i = a := by simpa [huv] using hvLine
    exact (lt_of_not_ge hnot).ne huLine

lemma exists_last_line_contact_suffix_in_lowerHalfPlane
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : a <= start i)
    (hfinish : finish i <= a) :
    exists t : unitInterval,
      gamma t i = a /\
      (forall u : unitInterval, gamma u i = a -> u <= t) /\
      Set.range (gamma.subpath t 1) <= Set.range gamma /\
      forall z : Fin 2 -> Real,
        z ∈ Set.range (gamma.subpath t 1) -> z i <= a := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq_of_ge
    gamma i a hstart hfinish
  obtain ⟨t, ht, htlast⟩ :=
    exists_last_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htlast, ?_, ?_⟩
  · rw [Path.range_subpath]
    exact image_subset_range _ _
  · intro z hz
    rw [Path.range_subpath_of_le gamma t 1 t.2.2] at hz
    obtain ⟨u, huIcc, rfl⟩ := hz
    by_contra hnot
    have huAbove : a <= gamma u i := (lt_of_not_ge hnot).le
    obtain ⟨s, hs⟩ := exists_parameter_coord_eq_of_ge
      (gamma.subpath u 1) i a huAbove (by simpa using hfinish)
    have hsMem : gamma.subpath u 1 s ∈
        Set.range (gamma.subpath u 1) := ⟨s, rfl⟩
    rw [Path.range_subpath_of_le gamma u 1 u.2.2] at hsMem
    obtain ⟨v, hvIcc, hv⟩ := hsMem
    have hvLine : gamma v i = a := by
      rw [hv]
      exact hs
    have hvLast : v <= t := htlast v hvLine
    have huv : u = v := le_antisymm hvIcc.1 (hvLast.trans huIcc.1)
    have huLine : gamma u i = a := by simpa [huv] using hvLine
    exact (lt_of_not_ge hnot).ne' huLine

/-! ## B. Excursions above and below a line -/

lemma exists_upper_line_excursion
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i <= a)
    (hfinish : finish i <= a) (t : unitInterval)
    (ht : a <= gamma t i) :
    (∃ (lo hi : Fin 2 -> Real)
      (lower : Path lo (gamma t)) (upper : Path (gamma t) hi),
      lo i = a /\ hi i = a /\
      Set.range lower <= Set.range gamma /\
      Set.range upper <= Set.range gamma /\
      (forall z : Fin 2 -> Real, z ∈ Set.range lower -> a <= z i) /\
      (forall z : Fin 2 -> Real, z ∈ Set.range upper -> a <= z i)) := by
  let pref := gamma.subpath 0 t
  let suff := gamma.subpath t 1
  obtain ⟨s, hs, _hsLast, hsRange, hsHalf⟩ :=
    exists_last_line_contact_suffix_in_halfPlane
      pref i a (by simpa [pref] using hstart) (by simpa [pref] using ht)
  obtain ⟨u, hu, _huFirst, huRange, huHalf⟩ :=
    exists_first_line_contact_prefix_in_upperHalfPlane
      suff i a (by simpa [suff] using ht) (by simpa [suff] using hfinish)
  let lower : Path (pref s) (gamma t) :=
    (pref.subpath s 1).cast rfl (by simp [pref])
  let upper : Path (gamma t) (suff u) :=
    (suff.subpath 0 u).cast (by simp [suff]) rfl
  have hlowerCoe : (lower : unitInterval -> Fin 2 -> Real) =
      pref.subpath s 1 := by
    rfl
  have hupperCoe : (upper : unitInterval -> Fin 2 -> Real) =
      suff.subpath 0 u := by
    rfl
  have hprefRange : Set.range pref <= Set.range gamma := by
    dsimp [pref]
    rw [Path.range_subpath]
    exact image_subset_range _ _
  have hsuffRange : Set.range suff <= Set.range gamma := by
    dsimp [suff]
    rw [Path.range_subpath]
    exact image_subset_range _ _
  refine ⟨pref s, suff u, lower, upper, hs, hu, ?_, ?_, ?_, ?_⟩
  · rw [hlowerCoe]
    exact hsRange.trans hprefRange
  · rw [hupperCoe]
    exact huRange.trans hsuffRange
  · rw [hlowerCoe]
    exact hsHalf
  · rw [hupperCoe]
    exact huHalf

lemma exists_lower_line_excursion
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : a <= start i)
    (hfinish : a <= finish i) (t : unitInterval)
    (ht : gamma t i <= a) :
    (∃ (lo hi : Fin 2 -> Real)
      (lower : Path lo (gamma t)) (upper : Path (gamma t) hi),
      lo i = a /\ hi i = a /\
      Set.range lower <= Set.range gamma /\
      Set.range upper <= Set.range gamma /\
      (forall z : Fin 2 -> Real, z ∈ Set.range lower -> z i <= a) /\
      (forall z : Fin 2 -> Real, z ∈ Set.range upper -> z i <= a)) := by
  let pref := gamma.subpath 0 t
  let suff := gamma.subpath t 1
  obtain ⟨s, hs, _hsLast, hsRange, hsHalf⟩ :=
    exists_last_line_contact_suffix_in_lowerHalfPlane
      pref i a (by simpa [pref] using hstart) (by simpa [pref] using ht)
  obtain ⟨u, hu, _huFirst, huRange, huHalf⟩ :=
    exists_first_line_contact_prefix_in_halfPlane
      suff i a (by simpa [suff] using ht) (by simpa [suff] using hfinish)
  let lower : Path (pref s) (gamma t) :=
    (pref.subpath s 1).cast rfl (by simp [pref])
  let upper : Path (gamma t) (suff u) :=
    (suff.subpath 0 u).cast (by simp [suff]) rfl
  have hlowerCoe : (lower : unitInterval -> Fin 2 -> Real) =
      pref.subpath s 1 := by
    rfl
  have hupperCoe : (upper : unitInterval -> Fin 2 -> Real) =
      suff.subpath 0 u := by
    rfl
  have hprefRange : Set.range pref <= Set.range gamma := by
    dsimp [pref]
    rw [Path.range_subpath]
    exact image_subset_range _ _
  have hsuffRange : Set.range suff <= Set.range gamma := by
    dsimp [suff]
    rw [Path.range_subpath]
    exact image_subset_range _ _
  refine ⟨pref s, suff u, lower, upper, hs, hu, ?_, ?_, ?_, ?_⟩
  · rw [hlowerCoe]
    exact hsRange.trans hprefRange
  · rw [hupperCoe]
    exact huRange.trans hsuffRange
  · rw [hlowerCoe]
    exact hsHalf
  · rw [hupperCoe]
    exact huHalf

/-- An excursion of the path from the line `{z i = a}` back to it, staying in `{z i ≥ a}`, as a
single path. Derived from `exists_upper_line_excursion` by concatenation. -/
lemma exists_upper_line_excursion_path
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i <= a)
    (hfinish : finish i <= a) (t : unitInterval)
    (ht : a <= gamma t i) :
    ∃ (lo hi : Fin 2 -> Real) (excursion : Path lo hi),
      lo i = a /\ hi i = a /\
      Set.range excursion <= Set.range gamma /\
      ∀ z : Fin 2 -> Real, z ∈ Set.range excursion -> a <= z i := by
  obtain ⟨lo, hi, lower, upper, hlo, hhi, hlowerRange, hupperRange,
    hlowerHalf, hupperHalf⟩ :=
      exists_upper_line_excursion gamma i a hstart hfinish t ht
  refine ⟨lo, hi, lower.trans upper, hlo, hhi, ?_, ?_⟩
  · rw [Path.trans_range]
    exact union_subset hlowerRange hupperRange
  · intro z hz
    rw [Path.trans_range] at hz
    exact hz.elim (hlowerHalf z) (hupperHalf z)

/-- An excursion of the path from the line `{z i = a}` back to it, staying in `{z i ≤ a}`, as a
single path. -/
lemma exists_lower_line_excursion_path
    {start finish : Fin 2 -> Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : a <= start i)
    (hfinish : a <= finish i) (t : unitInterval)
    (ht : gamma t i <= a) :
    ∃ (lo hi : Fin 2 -> Real) (excursion : Path lo hi),
      lo i = a /\ hi i = a /\
      Set.range excursion <= Set.range gamma /\
      ∀ z : Fin 2 -> Real, z ∈ Set.range excursion -> z i <= a := by
  obtain ⟨lo, hi, lower, upper, hlo, hhi, hlowerRange, hupperRange,
    hlowerHalf, hupperHalf⟩ :=
      exists_lower_line_excursion gamma i a hstart hfinish t ht
  refine ⟨lo, hi, lower.trans upper, hlo, hhi, ?_, ?_⟩
  · rw [Path.trans_range]
    exact union_subset hlowerRange hupperRange
  · intro z hz
    rw [Path.trans_range] at hz
    exact hz.elim (hlowerHalf z) (hupperHalf z)

end StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut
