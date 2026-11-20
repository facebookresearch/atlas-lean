/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Code.FK.PeriodicPlanarSheffieldCrosscut
import Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster
import Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability
import Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation
import Code.FK.PeriodicPlanarSheffieldRotated
import Mathlib.Topology.Subpath











open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

namespace ContinuousHalfPlaneCrosscut




theorem exists_parameter_coord_eq
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i ≤ a)
    (hfinish : a ≤ finish i) :
    ∃ t : unitInterval, gamma t i = a := by
  have hcontinuous : Continuous (fun t : unitInterval => gamma t i) :=
    continuous_apply i |>.comp gamma.continuous
  have ha : a ∈ Set.Icc ((fun t : unitInterval => gamma t i) 0)
      ((fun t : unitInterval => gamma t i) 1) := by
    simpa using ⟨hstart, hfinish⟩
  exact intermediate_value_univ (0 : unitInterval) 1 hcontinuous ha


theorem exists_parameter_coord_eq_of_ge
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : a ≤ start i)
    (hfinish : finish i ≤ a) :
    ∃ t : unitInterval, gamma t i = a := by
  have hcontinuous : Continuous (fun t : unitInterval => gamma t i) :=
    continuous_apply i |>.comp gamma.continuous
  have ha : a ∈ Set.Icc ((fun t : unitInterval => gamma t i) 1)
      ((fun t : unitInterval => gamma t i) 0) := by
    simpa using ⟨hfinish, hstart⟩
  exact intermediate_value_univ (1 : unitInterval) 0 hcontinuous ha


theorem exists_first_parameter_coord_eq
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real)
    (hne : ∃ u : unitInterval, gamma u i = a) :
    ∃ t : unitInterval, gamma t i = a ∧
      ∀ u : unitInterval, gamma u i = a → t ≤ u := by
  let K : Set unitInterval := {u | gamma u i = a}
  have hcontinuous : Continuous (fun u : unitInterval => gamma u i) :=
    continuous_apply i |>.comp gamma.continuous
  have hclosed : IsClosed K := by
    exact isClosed_eq hcontinuous continuous_const
  have hKne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu⟩
  obtain ⟨t, htK, htmin⟩ := hclosed.isCompact.exists_isMinOn
    hKne continuous_id.continuousOn
  exact ⟨t, htK, fun u hu => htmin hu⟩


theorem exists_last_parameter_coord_eq
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real)
    (hne : ∃ u : unitInterval, gamma u i = a) :
    ∃ t : unitInterval, gamma t i = a ∧
      ∀ u : unitInterval, gamma u i = a → u ≤ t := by
  let K : Set unitInterval := {u | gamma u i = a}
  have hcontinuous : Continuous (fun u : unitInterval => gamma u i) :=
    continuous_apply i |>.comp gamma.continuous
  have hclosed : IsClosed K := by
    exact isClosed_eq hcontinuous continuous_const
  have hKne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu⟩
  obtain ⟨t, htK, htmax⟩ := hclosed.isCompact.exists_isMaxOn
    hKne continuous_id.continuousOn
  exact ⟨t, htK, fun u hu => htmax hu⟩



theorem exists_first_line_contact_suffix
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i ≤ a)
    (hfinish : a ≤ finish i) :
    ∃ t : unitInterval,
      gamma t i = a ∧
      (∀ u : unitInterval, gamma u i = a → t ≤ u) ∧
      Set.range (gamma.subpath t 1) ⊆ Set.range gamma := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq gamma i a hstart hfinish
  obtain ⟨t, ht, htfirst⟩ :=
    exists_first_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htfirst, ?_⟩
  rw [Path.range_subpath]
  exact image_subset_range _ _



theorem exists_last_line_contact_prefix
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i ≤ a)
    (hfinish : a ≤ finish i) :
    ∃ t : unitInterval,
      gamma t i = a ∧
      (∀ u : unitInterval, gamma u i = a → u ≤ t) ∧
      Set.range (gamma.subpath 0 t) ⊆ Set.range gamma := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq gamma i a hstart hfinish
  obtain ⟨t, ht, htlast⟩ :=
    exists_last_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htlast, ?_⟩
  rw [Path.range_subpath]
  exact image_subset_range _ _


noncomputable def affinePath (x y : Fin 2 → Real) : Path x y where
  toFun t i := (1 - (t : Real)) * x i + (t : Real) * y i
  continuous_toFun := by fun_prop
  source' := by ext i; simp
  target' := by ext i; simp

@[simp] theorem affinePath_apply (x y : Fin 2 → Real) (t : unitInterval)
    (i : Fin 2) :
    affinePath x y t i = (1 - (t : Real)) * x i + (t : Real) * y i := rfl


noncomputable def horizontalPrefix (a : Real) (root : Fin 2 → Real) :
    Path ![a, root 1] root :=
  affinePath ![a, root 1] root

@[simp] theorem horizontalPrefix_apply_one (a : Real)
    (root : Fin 2 → Real) (t : unitInterval) :
    horizontalPrefix a root t 1 = root 1 := by
  simp [horizontalPrefix, affinePath_apply]
  ring



theorem horizontalPrefix_disjoint_of_range_below
    {x y root : Fin 2 → Real} (a : Real) (gamma : Path x y)
    (hbelow : ∀ z ∈ Set.range gamma, z 1 < root 1) :
    Disjoint (Set.range (horizontalPrefix a root)) (Set.range gamma) := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzGamma
  obtain ⟨t, rfl⟩ := hzPrefix
  have h := hbelow _ hzGamma
  rw [horizontalPrefix_apply_one] at h
  exact lt_irrefl _ h



theorem horizontalPrefix_disjoint_of_range_above
    {x y root : Fin 2 → Real} (a : Real) (gamma : Path x y)
    (habove : ∀ z ∈ Set.range gamma, root 1 < z 1) :
    Disjoint (Set.range (horizontalPrefix a root)) (Set.range gamma) := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzGamma
  obtain ⟨t, rfl⟩ := hzPrefix
  have h := habove _ hzGamma
  rw [horizontalPrefix_apply_one] at h
  exact lt_irrefl _ h



theorem disjoint_of_coord_lt {A C : Set (Fin 2 → Real)} (i : Fin 2)
    (hsep : ∀ x ∈ A, ∀ y ∈ C, x i < y i) :
    Disjoint A C := by
  rw [Set.disjoint_left]
  intro z hzA hzC
  exact lt_irrefl _ (hsep z hzA z hzC)



theorem horizontalPrefix_coord_lt
    {a R : Real} {root : Fin 2 → Real}
    (ha : a < R) (hroot : root 0 < R) :
    ∀ z ∈ Set.range (horizontalPrefix a root), z 0 < R := by
  rintro z ⟨t, rfl⟩
  have ht0 := t.2.1
  have ht1 := t.2.2
  change (1 - (t : Real)) * a + (t : Real) * root 0 < R
  by_cases ht : (t : Real) = 1
  · rw [ht]
    norm_num
    exact hroot
  · have htlt : (t : Real) < 1 := lt_of_le_of_ne ht1 ht
    have hleft : 0 < (1 - (t : Real)) * (R - a) :=
      mul_pos (sub_pos.mpr htlt) (sub_pos.mpr ha)
    have hright : 0 ≤ (t : Real) * (R - root 0) :=
      mul_nonneg ht0 (sub_nonneg.mpr hroot.le)
    nlinarith



noncomputable def rectangleMargin (a b c d : Real)
    (z : Fin 2 → Real) : Real :=
  min (z 0 - a) (min (b - z 0) (min (z 1 - c) (d - z 1)))

theorem rectangleMargin_nonneg_iff (a b c d : Real) (z : Fin 2 → Real) :
    0 ≤ rectangleMargin a b c d z ↔
      ContinuousRectangleCrossing.InRectangle a b c d z := by
  simp only [rectangleMargin, le_min_iff,
    ContinuousRectangleCrossing.InRectangle]
  constructor
  · rintro ⟨hxa, hbx, hyc, hdy⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hax, hxb, hcy, hyd⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩




theorem exists_first_rectangle_exit_prefix
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    {a b c d : Real}
    (hstart : a < start 0 ∧ start 0 < b ∧
      c < start 1 ∧ start 1 < d)
    (hfinish : ¬ ContinuousRectangleCrossing.InRectangle a b c d finish) :
    ∃ t : unitInterval,
      rectangleMargin a b c d (gamma t) = 0 ∧
      Set.range (gamma.subpath 0 t) ⊆
        {z | ContinuousRectangleCrossing.InRectangle a b c d z} ∧
      Set.range (gamma.subpath 0 t) ⊆ Set.range gamma ∧
      (gamma t 0 = a ∨ gamma t 0 = b ∨
        gamma t 1 = c ∨ gamma t 1 = d) := by
  let f : unitInterval → Real := fun u =>
    rectangleMargin a b c d (gamma u)
  have hf : Continuous f := by
    dsimp only [f, rectangleMargin]
    fun_prop
  have hf0 : 0 < f 0 := by
    dsimp only [f, rectangleMargin]
    simp only [Path.source]
    apply lt_min
    · linarith [hstart.1]
    apply lt_min
    · linarith [hstart.2.1]
    apply lt_min <;> linarith [hstart.2.2.1, hstart.2.2.2]
  have hf1 : f 1 < 0 := by
    apply lt_of_not_ge
    intro hnonneg
    apply hfinish
    apply (rectangleMargin_nonneg_iff a b c d finish).1
    simpa only [f, Path.target] using hnonneg
  have hzero : ∃ u : unitInterval, f u = 0 := by
    have hz : (0 : Real) ∈ Set.Icc (f 1) (f 0) := ⟨hf1.le, hf0.le⟩
    obtain ⟨u, _hu, hu0⟩ :=
      intermediate_value_Icc' (show (0 : unitInterval) ≤ 1 by simp)
        hf.continuousOn hz
    exact ⟨u, hu0⟩
  let K : Set unitInterval := {u | f u = 0}
  have hKclosed : IsClosed K := isClosed_eq hf continuous_const
  have hKne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hzero
    exact ⟨u, hu⟩
  obtain ⟨t, htK, htmin⟩ := hKclosed.isCompact.exists_isMinOn
    hKne continuous_id.continuousOn
  change f t = 0 at htK
  have hprefixNonneg : ∀ u : unitInterval, u ≤ t → 0 ≤ f u := by
    intro u hut
    by_contra hnot
    have hfu : f u < 0 := lt_of_not_ge hnot
    have huPos : (0 : unitInterval) < u := by
      by_contra hu0
      have : u = 0 := le_antisymm (le_of_not_gt hu0) u.2.1
      subst u
      exact (not_lt_of_ge hf0.le) hfu
    have hz : (0 : Real) ∈ Set.Icc (f u) (f 0) := ⟨hfu.le, hf0.le⟩
    obtain ⟨v, hvI, hv0⟩ :=
      intermediate_value_Icc' (show (0 : unitInterval) ≤ u by exact u.2.1)
        hf.continuousOn hz
    have hvlt : v < t := by
      have hvle : v ≤ u := hvI.2
      have hutNe : u ≠ t := by
        intro hutEq
        subst u
        rw [htK] at hfu
        exact lt_irrefl _ hfu
      exact lt_of_le_of_lt hvle (lt_of_le_of_ne hut hutNe)
    exact (not_lt_of_ge (htmin hv0)) hvlt
  have htRect : ContinuousRectangleCrossing.InRectangle a b c d (gamma t) :=
    (rectangleMargin_nonneg_iff a b c d (gamma t)).1
      (by change 0 ≤ f t; rw [htK])
  have htSide : gamma t 0 = a ∨ gamma t 0 = b ∨
      gamma t 1 = c ∨ gamma t 1 = d := by
    by_contra hnone
    push Not at hnone
    have hxa : 0 < gamma t 0 - a := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.1 hnone.1.symm)
    have hbx : 0 < b - gamma t 0 := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.2.1 hnone.2.1)
    have hyc : 0 < gamma t 1 - c := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.2.2.1 hnone.2.2.1.symm)
    have hdy : 0 < d - gamma t 1 := by
      exact sub_pos.mpr (lt_of_le_of_ne htRect.2.2.2 hnone.2.2.2)
    have : 0 < rectangleMargin a b c d (gamma t) := by
      dsimp only [rectangleMargin]
      exact lt_min hxa (lt_min hbx (lt_min hyc hdy))
    change 0 < f t at this
    rw [htK] at this
    exact lt_irrefl _ this
  refine ⟨t, htK, ?_, ?_, htSide⟩
  · intro z hz
    rw [Path.range_subpath] at hz
    obtain ⟨u, huI, rfl⟩ := hz
    have hut : u ≤ t := by
      rw [Set.uIcc_of_le (show (0 : unitInterval) ≤ t from t.2.1)] at huI
      exact huI.2
    exact (rectangleMargin_nonneg_iff a b c d (gamma u)).1
      (hprefixNonneg u hut)
  · rw [Path.range_subpath]
    exact Set.image_subset_range _ _




theorem leftCrosscut_intersects_leftRightPath_of_left_between
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishX : finish 0 = b)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottom : Fin 2 → Real := ![a, c]
  let top : Fin 2 → Real := ![a, d]
  let lower : Path bottom lo := affinePath bottom lo
  let upper : Path hi top := affinePath hi top
  let vertical : Path bottom top := lower.trans (crosscut.trans upper)
  have hlowerRect : Set.range lower ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ lower t 0 ∧ lower t 0 ≤ b ∧
      c ≤ lower t 1 ∧ lower t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hloRect : ContinuousRectangleCrossing.InRectangle a b c d lo := by
      simpa using hcrossRect (Set.mem_range_self (0 : unitInterval))
    dsimp only [lower, bottom]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hloX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hloRect.2.2.2]
  have hupperRect : Set.range upper ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ upper t 0 ∧ upper t 0 ≤ b ∧
      c ≤ upper t 1 ∧ upper t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hhiRect : ContinuousRectangleCrossing.InRectangle a b c d hi := by
      simpa using hcrossRect (Set.mem_range_self (1 : unitInterval))
    dsimp only [upper, top]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hhiX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hhiRect.2.2.1]
  have hverticalRect : Set.range vertical ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range vertical =
      Set.range lower ∪ (Set.range crosscut ∪ Set.range upper) by
        simp [vertical, Path.trans_range]]
    exact union_subset hlowerRect (union_subset hcrossRect hupperRect)
  obtain ⟨t, s, hts⟩ :=
    ContinuousRectangleCrossing.rectangle_paths_intersect
      hab hcd escape vertical hescapeRect hverticalRect
        hstartX hfinishX (by simp [bottom]) (by simp [top])
  have hsVertical : vertical s ∈ Set.range vertical := ⟨s, rfl⟩
  have hsCases : vertical s ∈ Set.range lower ∨
      vertical s ∈ Set.range crosscut ∨ vertical s ∈ Set.range upper := by
    simpa [vertical, Path.trans_range] using hsVertical
  rcases hsCases with hsLower | hsCrosscut | hsUpper
  · obtain ⟨u, hu⟩ := hsLower
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      simp [lower, bottom, hloX]
      ring
    have hbetween := hescapeLeftBetween (escape t) ⟨t, rfl⟩ hleft
    have hyEq : escape t 1 = lower u 1 := by rw [hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [lower, bottom] at hyEq
    change escape t 1 = (1 - (u : Real)) * c + (u : Real) * lo 1 at hyEq
    nlinarith
  · exact ⟨escape t, ⟨t, rfl⟩, by rwa [hts]⟩
  · obtain ⟨u, hu⟩ := hsUpper
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      simp [upper, top, hhiX]
      ring
    have hbetween := hescapeLeftBetween (escape t) ⟨t, rfl⟩ hleft
    have hyEq : escape t 1 = upper u 1 := by rw [hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [upper, top] at hyEq
    change escape t 1 = (1 - (u : Real)) * hi 1 + (u : Real) * d at hyEq
    nlinarith



theorem leftCrosscut_intersects_leftTopPath_of_left_between
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = d)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1)
    (hcrossBelowTop : ∀ t : unitInterval, crosscut t 1 < d) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let topRight : Fin 2 → Real := ![b, d]
  let tail : Path finish topRight := affinePath finish topRight
  let extended : Path start topRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, topRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact hcd.le
    · rw [hfinishY]
      ring_nf
      exact le_rfl
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeftBetween : ∀ p ∈ Set.range extended, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1 := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeftBetween p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, topRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath_of_left_between
    hab hcd crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [topRight]) hloY hhiY hextendedLeftBetween
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = d := by
      dsimp only [tail, topRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * d = d
      rw [hfinishY]
      ring
    have := hcrossBelowTop s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith



theorem leftCrosscut_intersects_leftBottomPath_of_left_between
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = c)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ p ∈ Set.range escape, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1)
    (hcrossAboveBottom : ∀ t : unitInterval, c < crosscut t 1) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottomRight : Fin 2 → Real := ![b, c]
  let tail : Path finish bottomRight := affinePath finish bottomRight
  let extended : Path start bottomRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, bottomRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact le_rfl
    · rw [hfinishY]
      ring_nf
      exact hcd.le
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeftBetween : ∀ p ∈ Set.range extended, p 0 = a →
      lo 1 < p 1 ∧ p 1 < hi 1 := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeftBetween p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, bottomRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath_of_left_between
    hab hcd crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [bottomRight]) hloY hhiY hextendedLeftBetween
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = c := by
      dsimp only [tail, bottomRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * c = c
      rw [hfinishY]
      ring
    have := hcrossAboveBottom s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith




theorem attachedCrosscut_intersection_reduces_to_core
    {lo hi x y start finish : Fin 2 → Real}
    (lower : Path lo x) (core : Path x y) (upper : Path y hi)
    (escape : Path start finish)
    (hinter : (Set.range escape ∩
      Set.range (lower.trans (core.trans upper))).Nonempty)
    (hlower : Disjoint (Set.range escape) (Set.range lower))
    (hupper : Disjoint (Set.range escape) (Set.range upper)) :
    (Set.range escape ∩ Set.range core).Nonempty := by
  obtain ⟨p, hpEscape, hpCrosscut⟩ := hinter
  have hpCases : p ∈ Set.range lower ∨
      p ∈ Set.range core ∨ p ∈ Set.range upper := by
    simpa only [Path.trans_range, Set.mem_union] using hpCrosscut
  rcases hpCases with hpLower | hpCore | hpUpper
  · exact (Set.disjoint_left.1 hlower hpEscape hpLower).elim
  · exact ⟨p, hpEscape, hpCore⟩
  · exact (Set.disjoint_left.1 hupper hpEscape hpUpper).elim




theorem doublyAttached_intersection_reduces_to_cores
    {plo px py phi estart eroot efinish : Fin 2 → Real}
    (plower : Path plo px) (pcore : Path px py) (pupper : Path py phi)
    (eprefix : Path estart eroot) (ecore : Path eroot efinish)
    (hinter : (Set.range (eprefix.trans ecore) ∩
      Set.range (plower.trans (pcore.trans pupper))).Nonempty)
    (hPrefixLower : Disjoint (Set.range eprefix) (Set.range plower))
    (hPrefixCore : Disjoint (Set.range eprefix) (Set.range pcore))
    (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range pupper))
    (hCoreLower : Disjoint (Set.range ecore) (Set.range plower))
    (hCoreUpper : Disjoint (Set.range ecore) (Set.range pupper)) :
    (Set.range ecore ∩ Set.range pcore).Nonempty := by
  obtain ⟨z, hzEscape, hzPrimal⟩ := hinter
  have hzEscapeCases : z ∈ Set.range eprefix ∨ z ∈ Set.range ecore := by
    simpa only [Path.trans_range, Set.mem_union] using hzEscape
  have hzPrimalCases : z ∈ Set.range plower ∨
      z ∈ Set.range pcore ∨ z ∈ Set.range pupper := by
    simpa only [Path.trans_range, Set.mem_union] using hzPrimal
  rcases hzEscapeCases with hzPrefix | hzCore
  · rcases hzPrimalCases with hzLower | hzPCore | hzUpper
    · exact (Set.disjoint_left.1 hPrefixLower hzPrefix hzLower).elim
    · exact (Set.disjoint_left.1 hPrefixCore hzPrefix hzPCore).elim
    · exact (Set.disjoint_left.1 hPrefixUpper hzPrefix hzUpper).elim
  · rcases hzPrimalCases with hzLower | hzPCore | hzUpper
    · exact (Set.disjoint_left.1 hCoreLower hzCore hzLower).elim
    · exact ⟨z, hzCore, hzPCore⟩
    · exact (Set.disjoint_left.1 hCoreUpper hzCore hzUpper).elim





theorem leftCrosscut_intersects_leftRightPath
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishX : finish 0 = b)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (horderLo : lo 1 < start 1) (horderHi : start 1 < hi 1)
    (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottom : Fin 2 → Real := ![a, c]
  let top : Fin 2 → Real := ![a, d]
  let lower : Path bottom lo := affinePath bottom lo
  let upper : Path hi top := affinePath hi top
  let vertical : Path bottom top := lower.trans (crosscut.trans upper)
  have hlowerRect : Set.range lower ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ lower t 0 ∧ lower t 0 ≤ b ∧
      c ≤ lower t 1 ∧ lower t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hloRect : ContinuousRectangleCrossing.InRectangle a b c d lo := by
      simpa using hcrossRect (Set.mem_range_self (0 : unitInterval))
    dsimp only [lower, bottom]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hloX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hloRect.2.2.2]
  have hupperRect : Set.range upper ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    change a ≤ upper t 0 ∧ upper t 0 ≤ b ∧
      c ≤ upper t 1 ∧ upper t 1 ≤ d
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hhiRect : ContinuousRectangleCrossing.InRectangle a b c d hi := by
      simpa using hcrossRect (Set.mem_range_self (1 : unitInterval))
    dsimp only [upper, top]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hhiX]
    constructor
    · ring_nf
      exact le_rfl
    constructor
    · linarith
    constructor <;> nlinarith [hhiRect.2.2.1]
  have hverticalRect : Set.range vertical ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range vertical =
      Set.range lower ∪ (Set.range crosscut ∪ Set.range upper) by
        simp [vertical, Path.trans_range]]
    exact union_subset hlowerRect (union_subset hcrossRect hupperRect)
  obtain ⟨t, s, hts⟩ :=
    ContinuousRectangleCrossing.rectangle_paths_intersect
      hab hcd escape vertical hescapeRect hverticalRect
        hstartX hfinishX (by simp [bottom]) (by simp [top])
  have hsVertical : vertical s ∈ Set.range vertical := ⟨s, rfl⟩
  have hsCases : vertical s ∈ Set.range lower ∨
      vertical s ∈ Set.range crosscut ∨ vertical s ∈ Set.range upper := by
    simpa [vertical, Path.trans_range] using hsVertical
  rcases hsCases with hsLower | hsCrosscut | hsUpper
  · obtain ⟨u, hu⟩ := hsLower
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      change lower u 0 = a
      simp [lower, bottom, hloX]
      ring
    have ht : escape t = start :=
      hescapeLeft (escape t) ⟨t, rfl⟩ hleft
    have hyEq : start 1 = lower u 1 := by
      rw [← ht, hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [lower, bottom] at hyEq
    change start 1 = (1 - (u : Real)) * c + (u : Real) * lo 1 at hyEq
    nlinarith
  · exact ⟨escape t, ⟨t, rfl⟩, by rwa [hts]⟩
  · obtain ⟨u, hu⟩ := hsUpper
    have hleft : escape t 0 = a := by
      rw [hts, ← hu]
      change upper u 0 = a
      simp [upper, top, hhiX]
      ring
    have ht : escape t = start :=
      hescapeLeft (escape t) ⟨t, rfl⟩ hleft
    have hyEq : start 1 = upper u 1 := by
      rw [← ht, hts, ← hu]
    have hu0 := u.2.1
    have hu1 := u.2.2
    dsimp only [upper, top] at hyEq
    change start 1 = (1 - (u : Real)) * hi 1 + (u : Real) * d at hyEq
    nlinarith


theorem leftCrosscut_intersects_leftTopPath
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = d)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (horderLo : lo 1 < start 1) (horderHi : start 1 < hi 1)
    (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start)
    (hcrossBelowTop : ∀ t : unitInterval, crosscut t 1 < d) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let topRight : Fin 2 → Real := ![b, d]
  let tail : Path finish topRight := affinePath finish topRight
  let extended : Path start topRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, topRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact hcd.le
    · rw [hfinishY]
      ring_nf
      exact le_rfl
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeft : ∀ p ∈ Set.range extended, p 0 = a → p = start := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeft p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, topRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath hab hcd
    crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [topRight]) hloY hhiY horderLo horderHi hextendedLeft
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = d := by
      dsimp only [tail, topRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * d = d
      rw [hfinishY]
      ring
    have := hcrossBelowTop s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith


theorem leftCrosscut_intersects_leftBottomPath
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi start finish : Fin 2 → Real}
    (crosscut : Path lo hi) (escape : Path start finish)
    (hcrossRect : Set.range crosscut ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hescapeRect : Set.range escape ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : start 0 = a) (hfinishY : finish 1 = c)
    (hfinishX : a < finish 0)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (horderLo : lo 1 < start 1) (horderHi : start 1 < hi 1)
    (hescapeLeft : ∀ p ∈ Set.range escape, p 0 = a → p = start)
    (hcrossAboveBottom : ∀ t : unitInterval, c < crosscut t 1) :
    (Set.range escape ∩ Set.range crosscut).Nonempty := by
  let bottomRight : Fin 2 → Real := ![b, c]
  let tail : Path finish bottomRight := affinePath finish bottomRight
  let extended : Path start bottomRight := escape.trans tail
  have htailRect : Set.range tail ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rintro p ⟨t, rfl⟩
    have ht0 := t.2.1
    have ht1 := t.2.2
    have hfinishRect : ContinuousRectangleCrossing.InRectangle a b c d finish := by
      simpa using hescapeRect (Set.mem_range_self (1 : unitInterval))
    change a ≤ tail t 0 ∧ tail t 0 ≤ b ∧
      c ≤ tail t 1 ∧ tail t 1 ≤ d
    dsimp only [tail, bottomRight]
    simp only [affinePath_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · nlinarith [hfinishRect.1]
    constructor
    · nlinarith [hfinishRect.2.1]
    constructor
    · rw [hfinishY]
      ring_nf
      exact le_rfl
    · rw [hfinishY]
      ring_nf
      exact hcd.le
  have hextendedRect : Set.range extended ⊆
      {p | ContinuousRectangleCrossing.InRectangle a b c d p} := by
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]]
    exact union_subset hescapeRect htailRect
  have hextendedLeft : ∀ p ∈ Set.range extended, p 0 = a → p = start := by
    intro p hp hpLeft
    rw [show Set.range extended = Set.range escape ∪ Set.range tail by
      simp [extended, Path.trans_range]] at hp
    rcases hp with hpEscape | hpTail
    · exact hescapeLeft p hpEscape hpLeft
    · obtain ⟨t, rfl⟩ := hpTail
      have ht0 := t.2.1
      have ht1 := t.2.2
      dsimp only [tail, bottomRight] at hpLeft
      simp only [affinePath_apply, Matrix.cons_val_zero] at hpLeft
      exfalso
      by_cases htOne : (t : Real) = 1
      · rw [htOne] at hpLeft
        norm_num at hpLeft
        linarith
      · have htLt : (t : Real) < 1 := lt_of_le_of_ne ht1 htOne
        have hfirst := mul_lt_mul_of_pos_left hfinishX (sub_pos.mpr htLt)
        have hsecond := mul_le_mul_of_nonneg_left hab.le ht0
        have ha : (1 - (t : Real)) * a + (t : Real) * a = a := by ring
        linarith
  have hinter := leftCrosscut_intersects_leftRightPath hab hcd
    crosscut extended hcrossRect hextendedRect hloX hhiX hstartX
      (by simp [bottomRight]) hloY hhiY horderLo horderHi hextendedLeft
  obtain ⟨p, hpExtended, hpCrosscut⟩ := hinter
  rw [show Set.range extended = Set.range escape ∪ Set.range tail by
    simp [extended, Path.trans_range]] at hpExtended
  rcases hpExtended with hpEscape | hpTail
  · exact ⟨p, hpEscape, hpCrosscut⟩
  · obtain ⟨t, rfl⟩ := hpTail
    obtain ⟨s, hs⟩ := hpCrosscut
    have htailY : tail t 1 = c := by
      dsimp only [tail, bottomRight]
      change (1 - (t : Real)) * finish 1 + (t : Real) * c = c
      rw [hfinishY]
      ring
    have := hcrossAboveBottom s
    have hsCoord := congrFun hs 1
    rw [htailY] at hsCoord
    linarith

end ContinuousHalfPlaneCrosscut



theorem PeriodicPlaneEmbedding.simpleWalkArc_coord_lower_of_support
    (E : PeriodicPlaneEmbedding P) {B r : Real}
    (hB0 : 0 ≤ B)
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (i : Fin 2) {x y : V} (p : P.graph.Walk x y)
    (hp : ∀ v ∈ p.support, r ≤ E.vertexCoord v i) :
    ∀ t : unitInterval,
      r - B ≤ E.coordinates (E.simpleWalkArc p t) i := by
  intro t
  have hq : E.simpleWalkArc p t ∈ Set.range (E.walkArc p) := by
    rw [← E.simpleWalkArc_range p]
    exact ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · change E.simpleWalkArc p t = E.vertex x at hstart
    rw [hstart]
    change r - B ≤ E.vertexCoord x i
    exact (sub_le_self r hB0).trans (hp x (by simp))
  · obtain ⟨u, v, huv, huvEdge, q, hqEdge⟩ := hedge
    have hu := hp u (p.fst_mem_support_of_mem_edges huvEdge)
    have hlo := E.vertex_sub_le_edgeArc_coord hB huv q i
    change E.edgeArc huv q = E.simpleWalkArc p t at hqEdge
    rw [← hqEdge]
    linarith



theorem PeriodicPlaneEmbedding.simpleWalkArc_coord_upper_of_support
    (E : PeriodicPlaneEmbedding P) {B r : Real}
    (hB0 : 0 ≤ B)
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (i : Fin 2) {x y : V} (p : P.graph.Walk x y)
    (hp : ∀ v ∈ p.support, E.vertexCoord v i ≤ r) :
    ∀ t : unitInterval,
      E.coordinates (E.simpleWalkArc p t) i ≤ r + B := by
  intro t
  have hq : E.simpleWalkArc p t ∈ Set.range (E.walkArc p) := by
    rw [← E.simpleWalkArc_range p]
    exact ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · change E.simpleWalkArc p t = E.vertex x at hstart
    rw [hstart]
    change E.vertexCoord x i ≤ r + B
    exact (hp x (by simp)).trans (le_add_of_nonneg_right hB0)
  · obtain ⟨u, v, huv, huvEdge, q, hqEdge⟩ := hedge
    have hu := hp u (p.fst_mem_support_of_mem_edges huvEdge)
    have hhi := E.edgeArc_coord_le_vertex_add hB huv q i
    change E.edgeArc huv q = E.simpleWalkArc p t at hqEdge
    rw [← hqEdge]
    linarith





theorem PeriodicPlaneEmbedding.exists_boundary_line_attachments
    (E : PeriodicPlaneEmbedding P) {B r c d : Real}
    (hB0 : 0 ≤ B)
    (hB : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hvw t - E.vertex v) i| ≤ B)
    {b u : V} (hb : b ∈ E.lowerBoundaryRayVertices r c)
    (hu : u ∈ E.upperBoundaryRayVertices r d) :
    ∃ lo hi : Fin 2 → Real,
      ∃ lower : Path lo (E.coordinates (E.vertex b)),
      ∃ upper : Path (E.coordinates (E.vertex u)) hi,
        lo 0 = r ∧ hi 0 = r ∧
        lo 1 ≤ c + B ∧ d - B ≤ hi 1 ∧
        (∀ z ∈ Set.range lower, z 1 ≤ c + B) ∧
        (∀ z ∈ Set.range upper, d - B ≤ z 1) ∧
        (∀ z ∈ Set.range lower, z 0 < r + 2 * B) ∧
        ∀ z ∈ Set.range upper, z 0 < r + 2 * B := by
  obtain ⟨_hbH, bOut, hbOut, hbOutX⟩ := hb.1
  obtain ⟨_huH, uOut, huOut, huOutX⟩ := hu.1
  let gammaB := (E.edgeArc hbOut).map E.coordinates.continuous
  let gammaU := (E.edgeArc huOut).map E.coordinates.continuous
  obtain ⟨tb, htb⟩ :=
    ContinuousHalfPlaneCrosscut.exists_parameter_coord_eq_of_ge
      gammaB 0 r hb.1.1 hbOutX.le
  obtain ⟨tu, htu⟩ :=
    ContinuousHalfPlaneCrosscut.exists_parameter_coord_eq_of_ge
      gammaU 0 r hu.1.1 huOutX.le
  let lo : Fin 2 → Real := gammaB tb
  let hi : Fin 2 → Real := gammaU tu
  let lower0 := (gammaB.subpath 0 tb).symm
  let upper0 := gammaU.subpath 0 tu
  let lower : Path lo (E.coordinates (E.vertex b)) :=
    lower0.cast rfl gammaB.source.symm
  let upper : Path (E.coordinates (E.vertex u)) hi :=
    upper0.cast gammaU.source.symm rfl
  have hloYDisp : |lo 1 - E.vertexCoord b 1| ≤ B := by
    have h := hB hbOut tb (1 : Fin 2)
    have heq : E.coordinates
        (E.edgeArc hbOut tb - E.vertex b) 1 =
        lo 1 - E.vertexCoord b 1 := by
      simp [lo, gammaB, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rwa [heq] at h
  have hhiYDisp : |hi 1 - E.vertexCoord u 1| ≤ B := by
    have h := hB huOut tu (1 : Fin 2)
    have heq : E.coordinates
        (E.edgeArc huOut tu - E.vertex u) 1 =
        hi 1 - E.vertexCoord u 1 := by
      simp [hi, gammaU, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rwa [heq] at h
  have hbX := E.rightHalfPlaneBoundary_coord_lt hB hb.1
  have huX := E.rightHalfPlaneBoundary_coord_lt hB hu.1
  have hlowerRange : Set.range lower ⊆ Set.range gammaB := by
    intro z hz
    have hz0 : z ∈ Set.range lower0 := by
      simpa [lower, Path.cast_coe] using hz
    dsimp only [lower0] at hz0
    rw [Path.symm_range, Path.range_subpath] at hz0
    obtain ⟨q, _hqI, hq⟩ := hz0
    exact ⟨q, hq⟩
  have hupperRange : Set.range upper ⊆ Set.range gammaU := by
    intro z hz
    have hz0 : z ∈ Set.range upper0 := by
      simpa [upper, Path.cast_coe] using hz
    dsimp only [upper0] at hz0
    rw [Path.range_subpath] at hz0
    obtain ⟨q, _hqI, hq⟩ := hz0
    exact ⟨q, hq⟩
  refine ⟨lo, hi, lower, upper, htb, htu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hbY := hb.2
    change E.vertexCoord b 1 ≤ c at hbY
    linarith [abs_le.mp hloYDisp |>.2]
  · have huY := hu.2
    change d ≤ E.vertexCoord u 1 at huY
    linarith [abs_le.mp hhiYDisp |>.1]
  · intro z hz
    obtain ⟨q, hq⟩ := hlowerRange hz
    have hdisp := hB hbOut q (1 : Fin 2)
    have heq : gammaB q 1 - E.vertexCoord b 1 =
        E.coordinates (E.edgeArc hbOut q - E.vertex b) 1 := by
      simp [gammaB, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 1
    have hbY := hb.2
    change E.vertexCoord b 1 ≤ c at hbY
    linarith [abs_le.mp hdisp |>.2]
  · intro z hz
    obtain ⟨q, hq⟩ := hupperRange hz
    have hdisp := hB huOut q (1 : Fin 2)
    have heq : gammaU q 1 - E.vertexCoord u 1 =
        E.coordinates (E.edgeArc huOut q - E.vertex u) 1 := by
      simp [gammaU, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 1
    have huY := hu.2
    change d ≤ E.vertexCoord u 1 at huY
    linarith [abs_le.mp hdisp |>.1]
  · intro z hz
    obtain ⟨q, hq⟩ := hlowerRange hz
    have hdisp := hB hbOut q (0 : Fin 2)
    have heq : gammaB q 0 - E.vertexCoord b 0 =
        E.coordinates (E.edgeArc hbOut q - E.vertex b) 0 := by
      simp [gammaB, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 0
    linarith [abs_le.mp hdisp |>.2]
  · intro z hz
    obtain ⟨q, hq⟩ := hupperRange hz
    have hdisp := hB huOut q (0 : Fin 2)
    have heq : gammaU q 0 - E.vertexCoord u 0 =
        E.coordinates (E.edgeArc huOut q - E.vertex u) 0 := by
      simp [gammaU, PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [← heq] at hdisp
    have hzEq := congrFun hq.symm 0
    linarith [abs_le.mp hdisp |>.2]

omit [Countable V] in


theorem PeriodicGraph.exists_open_boundary_walk_of_walk_to_compl
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (A : Set V)
    {x y : V} (p : (P.openSubgraph omega).Walk x y)
    (hx : x ∈ A) (hy : y ∉ A) :
    ∃ b ∈ A, ∃ z : V, (P.openSubgraph omega).Adj b z ∧ z ∉ A ∧
      ∃ q : (P.openSubgraph omega).Walk x b,
        (∀ v ∈ q.support, v ∈ A) ∧
        (∀ v ∈ q.support, v ∈ p.support) ∧ z ∈ p.support := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y hxz p ih =>
      by_cases hz : z ∈ A
      · obtain ⟨b, hb, w, hbw, hw, q, hqA, hqp, hwSupport⟩ := ih hz hy
        refine ⟨b, hb, w, hbw, hw, q.cons hxz, ?_, ?_, ?_⟩
        · intro v hv
          rw [SimpleGraph.Walk.support_cons] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hx
          · exact hqA v hv
        · intro v hv
          rw [SimpleGraph.Walk.support_cons] at hv ⊢
          rcases List.mem_cons.mp hv with rfl | hv
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem x (hqp v hv)
        · exact List.mem_cons_of_mem x hwSupport
      · refine ⟨x, hx, z, hxz, hz, .nil, ?_, ?_, ?_⟩
        · simpa using hx
        · intro v hv
          rw [SimpleGraph.Walk.support_nil] at hv
          rw [SimpleGraph.Walk.support_cons]
          have hvx : v = x := by simpa using hv
          exact List.mem_cons.2 (Or.inl hvx)
        · simp



def PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite ∧
    ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
      ∃ z : V, P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧
        omega s(b, z) = true ∧
        omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b}


def PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite ∧
    ∃ b ∈ T, b ∈ E.rightHalfPlaneBoundaryVertices r ∧
      ∃ z : V, P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧
        omega s(b, z) = true ∧
        omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b}

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    MeasurableSet (E.infiniteOpenBoundaryConnectionTo r S T) := by
  classical
  have heq : E.infiniteOpenBoundaryConnectionTo r S T =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          ⋃ b : V, ⋃ (_hbT : b ∈ T),
            ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
              ⋃ z : V, ⋃ (_hbz : P.graph.Adj b z),
                ⋃ (_hz : z ∉ E.rightHalfPlaneVertices r),
                  {omega : ConfigSpace (Sym2 V) | omega s(b, z) = true} ∩
                    P.connectedWithinSet (E.rightHalfPlaneVertices r) x b := by
    ext omega
    simp [PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo,
      and_left_comm, and_assoc]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    (P.measurableSet_cluster_infinite x).inter
      (MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hbT =>
        MeasurableSet.iUnion fun _hb => MeasurableSet.iUnion fun z =>
          MeasurableSet.iUnion fun _hbz => MeasurableSet.iUnion fun _hz =>
            (measurableSet_eq_fun (ConfigSpace.measurable_eval s(b, z))
              measurable_const).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneVertices r) x b))

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    IsIncreasing (E.infiniteOpenBoundaryConnectionTo r S T) := by
  intro omega eta homega
  rintro ⟨x, hxS, hxInfinite, b, hbT, hb, z, hbz, hz, hbzOpen, hxb⟩
  exact ⟨x, hxS, P.clusterInfinite_isIncreasing x homega hxInfinite,
    b, hbT, hb, z, hbz, hz, homega _ hbzOpen,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb⟩

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_subset
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    E.infiniteOpenBoundaryConnectionTo r S T ⊆
      E.infiniteOpenBoundaryConnection r S := by
  rintro omega ⟨x, hxS, hxInfinite, b, _hbT, hb, z, hbz, hz, hbzOpen, hxb⟩
  exact ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩




theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_configTranslate_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int)
    (omega : ConfigSpace (Sym2 V)) (r : Real) (S T : Set V) :
    P.configTranslate (verticalShift t) omega ∈
        E.infiniteOpenBoundaryConnectionTo r
          (P.shift (verticalShift t) '' S)
          (P.shift (verticalShift t) '' T) ↔
      omega ∈ E.infiniteOpenBoundaryConnectionTo r S T := by
  let q := verticalShift t
  constructor
  · rintro ⟨_, ⟨x, hxS, rfl⟩, hxInfinite,
      _, ⟨b, hbT, rfl⟩, hbBoundary, z, hbz, hzOutside, hbzOpen, hxb⟩
    let z₀ := P.shift (-q) z
    have hz : P.shift q z₀ = z := by
      simpa [z₀] using P.shift_shift_neg q z
    refine ⟨x, hxS, (P.cluster_infinite_configTranslate q omega x).mp hxInfinite,
      b, hbT, (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r b).mp
        hbBoundary, z₀, ?_, ?_, ?_, ?_⟩
    · rw [← hz] at hbz
      exact (P.shift_adj q b z₀).mp hbz
    · intro hz₀
      apply hzOutside
      rw [← hz]
      exact (E.shift_mem_rightHalfPlaneVertices_vertical t r z₀).mpr hz₀
    · simpa [q, z₀, PeriodicGraph.configTranslate] using hbzOpen
    · have h := P.connectedWithinSet_configTranslate q omega
          (E.rightHalfPlaneVertices r) x b
      rw [E.shift_image_rightHalfPlaneVertices_vertical] at h
      exact h.mp hxb
  · rintro ⟨x, hxS, hxInfinite, b, hbT, hbBoundary,
      z, hbz, hzOutside, hbzOpen, hxb⟩
    refine ⟨P.shift q x, ⟨x, hxS, rfl⟩,
      (P.cluster_infinite_configTranslate q omega x).mpr hxInfinite,
      P.shift q b, ⟨b, hbT, rfl⟩,
      (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r b).mpr hbBoundary,
      P.shift q z, (P.shift_adj q b z).mpr hbz, ?_, ?_, ?_⟩
    · intro hzShift
      exact hzOutside
        ((E.shift_mem_rightHalfPlaneVertices_vertical t r z).mp hzShift)
    · simpa [q, PeriodicGraph.configTranslate] using hbzOpen
    · have h := P.connectedWithinSet_configTranslate q omega
          (E.rightHalfPlaneVertices r) x b
      rw [E.shift_image_rightHalfPlaneVertices_vertical] at h
      exact h.mpr hxb



theorem PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int)
    (r s : Real) (S : Set V) :
    mu.real (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift t) '' S)
        (E.lowerBoundaryRayVertices r (s + t))) =
      mu.real (E.infiniteOpenBoundaryConnectionTo r S
        (E.lowerBoundaryRayVertices r s)) := by
  let A := E.infiniteOpenBoundaryConnectionTo r
    (P.shift (verticalShift t) '' S)
    (E.lowerBoundaryRayVertices r (s + t))
  have hpre : P.configTranslate (verticalShift t) ⁻¹' A =
      E.infiniteOpenBoundaryConnectionTo r S
        (E.lowerBoundaryRayVertices r s) := by
    ext omega
    dsimp only [A]
    rw [show E.lowerBoundaryRayVertices r (s + t) =
      P.shift (verticalShift t) '' E.lowerBoundaryRayVertices r s by
        symm
        exact E.shift_image_lowerBoundaryRayVertices_vertical t r s]
    exact E.infiniteOpenBoundaryConnectionTo_configTranslate_vertical
      t omega r S (E.lowerBoundaryRayVertices r s)
  have hm := (hTI (verticalShift t)).measure_preimage
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r
      (P.shift (verticalShift t) '' S)
      (E.lowerBoundaryRayVertices r (s + t))).nullMeasurableSet
  change mu.real A = _
  rw [← hpre]
  exact congrArg ENNReal.toReal hm.symm



theorem PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int)
    (r s : Real) (S : Set V) :
    mu.real (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift t) '' S)
        (E.upperBoundaryRayVertices r (s + t))) =
      mu.real (E.infiniteOpenBoundaryConnectionTo r S
        (E.upperBoundaryRayVertices r s)) := by
  let A := E.infiniteOpenBoundaryConnectionTo r
    (P.shift (verticalShift t) '' S)
    (E.upperBoundaryRayVertices r (s + t))
  have hpre : P.configTranslate (verticalShift t) ⁻¹' A =
      E.infiniteOpenBoundaryConnectionTo r S
        (E.upperBoundaryRayVertices r s) := by
    ext omega
    dsimp only [A]
    rw [show E.upperBoundaryRayVertices r (s + t) =
      P.shift (verticalShift t) '' E.upperBoundaryRayVertices r s by
        symm
        exact E.shift_image_upperBoundaryRayVertices_vertical t r s]
    exact E.infiniteOpenBoundaryConnectionTo_configTranslate_vertical
      t omega r S (E.upperBoundaryRayVertices r s)
  have hm := (hTI (verticalShift t)).measure_preimage
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r
      (P.shift (verticalShift t) '' S)
      (E.upperBoundaryRayVertices r (s + t))).nullMeasurableSet
  change mu.real A = _
  rw [← hpre]
  exact congrArg ENNReal.toReal hm.symm


theorem PeriodicPlaneEmbedding.iUnion_infiniteOpenLowerBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S
      (E.lowerBoundaryRayVertices r n)) =
        E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact E.infiniteOpenBoundaryConnectionTo_subset r S _ hn
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (E.vertexCoord b 1)
    apply Set.mem_iUnion.2
    refine ⟨n, x, hxS, hxInfinite, b, ?_, hb, z, hbz, hz, hbzOpen, hxb⟩
    exact ⟨hb, hn⟩



theorem PeriodicPlaneEmbedding.iUnion_infiniteOpenUpperBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S
      (E.upperBoundaryRayVertices r (-(n : Real)))) =
        E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact E.infiniteOpenBoundaryConnectionTo_subset r S _ hn
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (-E.vertexCoord b 1)
    apply Set.mem_iUnion.2
    refine ⟨n, x, hxS, hxInfinite, b, ?_, hb, z, hbz, hz, hbzOpen, hxb⟩
    have hn' : -(n : Real) ≤ E.vertexCoord b 1 := by linarith
    exact ⟨hb, hn'⟩


theorem exists_measureReal_pos_of_iUnion_measureReal_pos
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (A : Nat → Set X)
    (hpos : 0 < mu.real (⋃ n, A n)) :
    ∃ n, 0 < mu.real (A n) := by
  by_contra hnot
  push_neg at hnot
  have hrealZero (n : Nat) : mu.real (A n) = 0 := by
    exact le_antisymm (hnot n) measureReal_nonneg
  have hmeasureZero (n : Nat) : mu (A n) = 0 := by
    have h := (ENNReal.toReal_eq_zero_iff (mu (A n))).mp (hrealZero n)
    exact h.resolve_right (measure_ne_top mu _)
  have hunion : mu (⋃ n, A n) = 0 := measure_iUnion_null hmeasureZero
  unfold Measure.real at hpos
  rw [hunion] at hpos
  norm_num at hpos

theorem PeriodicPlaneEmbedding.exists_positive_infiniteOpenLowerBoundaryConnection
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V)
    (hpos : 0 < mu.real (E.infiniteOpenBoundaryConnection r S)) :
    ∃ n : Nat, 0 < mu.real (E.infiniteOpenBoundaryConnectionTo r S
      (E.lowerBoundaryRayVertices r n)) := by
  rw [← E.iUnion_infiniteOpenLowerBoundaryConnection r S] at hpos
  exact exists_measureReal_pos_of_iUnion_measureReal_pos mu _ hpos

theorem PeriodicPlaneEmbedding.exists_positive_infiniteOpenUpperBoundaryConnection
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V)
    (hpos : 0 < mu.real (E.infiniteOpenBoundaryConnection r S)) :
    ∃ n : Nat, 0 < mu.real (E.infiniteOpenBoundaryConnectionTo r S
      (E.upperBoundaryRayVertices r (-(n : Real)))) := by
  rw [← E.iUnion_infiniteOpenUpperBoundaryConnection r S] at hpos
  exact exists_measureReal_pos_of_iUnion_measureReal_pos mu _ hpos






def PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) (b u : V) : Set (ConfigSpace (Sym2 V)) :=
  {omega |
    b ∈ E.lowerBoundaryRayVertices r c ∧
    u ∈ E.upperBoundaryRayVertices r d ∧
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧
    ∃ y ∈ R, (P.cluster omega y).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧
      omega ∈ P.connectedWithinSet
        (E.rightHalfPlaneStripVertices r n) x y}

theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) (b u : V) :
    MeasurableSet (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
  classical
  by_cases hb : b ∈ E.lowerBoundaryRayVertices r c
  · by_cases hu : u ∈ E.upperBoundaryRayVertices r d
    · have heq : E.finiteJoinedBoundaryArmAt r c d n L R b u =
          ⋃ x : V, ⋃ (_hx : x ∈ L),
            {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
              P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∩
              ⋃ y : V, ⋃ (_hy : y ∈ R),
                {omega : ConfigSpace (Sym2 V) |
                  (P.cluster omega y).Infinite} ∩
                  P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∩
                  P.connectedWithinSet
                    (E.rightHalfPlaneStripVertices r n) x y := by
        ext omega
        simp only [PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt,
          Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, hb, hu,
          true_and]
        aesop
      rw [heq]
      exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
        ((P.measurableSet_cluster_infinite x).inter
          (P.connectedWithinSet_measurableSet
            (E.rightHalfPlaneVertices r) x b)).inter
          (MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
            ((P.measurableSet_cluster_infinite y).inter
              (P.connectedWithinSet_measurableSet
                (E.rightHalfPlaneVertices r) y u)).inter
              (P.connectedWithinSet_measurableSet
                (E.rightHalfPlaneStripVertices r n) x y))
    · have heq : E.finiteJoinedBoundaryArmAt r c d n L R b u = ∅ := by
        ext omega
        simp [PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt, hu]
      rw [heq]
      exact MeasurableSet.empty
  · have heq : E.finiteJoinedBoundaryArmAt r c d n L R b u = ∅ := by
      ext omega
      simp [PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt, hb]
    rw [heq]
    exact MeasurableSet.empty

theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) (b u : V) :
    IsIncreasing (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
  intro omega eta homega
  rintro ⟨hb, hu, x, hxL, hxInfinite, hxb,
    y, hyR, hyInfinite, hyu, hxy⟩
  exact ⟨hb, hu, x, hxL,
    P.clusterInfinite_isIncreasing x homega hxInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb,
    y, hyR, P.clusterInfinite_isIncreasing y homega hyInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hyu,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxy⟩


theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_subset_iUnion_at
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    E.finiteJoinedBoundaryArmEvent r c d n L R ⊆
      ⋃ b : V, ⋃ u : V, E.finiteJoinedBoundaryArmAt r c d n L R b u := by
  intro omega homega
  obtain ⟨x, hxL, hxInfinite, b, hb, hxb,
    y, hyR, hyInfinite, u, hu, hyu, hxy⟩ :=
      E.finiteJoinedBoundaryArmEvent_witnesses homega
  exact Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨u,
    hb, hu, x, hxL, hxInfinite, hxb, y, hyR, hyInfinite, hyu, hxy⟩⟩



theorem exists_measureReal_pos_of_countable_iUnion_measureReal_pos
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (mu : Measure X) [IsFiniteMeasure mu] (A : I → Set X)
    (hpos : 0 < mu.real (⋃ i, A i)) :
    ∃ i, 0 < mu.real (A i) := by
  by_contra hnot
  push Not at hnot
  have hmeasureZero (i : I) : mu (A i) = 0 := by
    have hrealZero : mu.real (A i) = 0 :=
      le_antisymm (hnot i) measureReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff (mu (A i))).mp hrealZero).resolve_right
      (measure_ne_top mu _)
  have hunion : mu (⋃ i, A i) = 0 := measure_iUnion_null hmeasureZero
  unfold Measure.real at hpos
  rw [hunion] at hpos
  norm_num at hpos


theorem PeriodicPlaneEmbedding.exists_positive_finiteJoinedBoundaryArmAt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r c d : Real) (n : Nat) (L R : Finset V)
    (hpos : 0 < mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R)) :
    ∃ b u : V,
      0 < mu.real (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
  let A := fun b : V => ⋃ u : V,
    E.finiteJoinedBoundaryArmAt r c d n L R b u
  have hunionPos : 0 < mu.real (⋃ b, A b) :=
    lt_of_lt_of_le hpos
      (measureReal_mono
        (E.finiteJoinedBoundaryArmEvent_subset_iUnion_at r c d n L R))
  obtain ⟨b, hb⟩ :=
    exists_measureReal_pos_of_countable_iUnion_measureReal_pos mu A hunionPos
  obtain ⟨u, hu⟩ :=
    exists_measureReal_pos_of_countable_iUnion_measureReal_pos mu
      (fun u => E.finiteJoinedBoundaryArmAt r c d n L R b u) hb
  exact ⟨b, u, hu⟩



def PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  {omega |
    ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V,
      P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧
      omega s(b, z) = true ∧
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧
    ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V,
      P.graph.Adj u w ∧ w ∉ E.rightHalfPlaneVertices r ∧
      omega s(u, w) = true ∧
    ∃ y ∈ R, (P.cluster omega y).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧
      omega ∈ P.connectedWithinSet
        (E.rightHalfPlaneStripVertices r n) x y}

theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    MeasurableSet (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
  classical
  have heq : E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R =
      ⋃ b : V, ⋃ (_hb : b ∈ E.lowerBoundaryRayVertices r c),
      ⋃ z : V, ⋃ (_hbz : P.graph.Adj b z),
      ⋃ (_hz : z ∉ E.rightHalfPlaneVertices r),
        {omega : ConfigSpace (Sym2 V) | omega s(b, z) = true} ∩
        ⋃ x : V, ⋃ (_hx : x ∈ L),
          {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∩
        ⋃ u : V, ⋃ (_hu : u ∈ E.upperBoundaryRayVertices r d),
        ⋃ w : V, ⋃ (_huw : P.graph.Adj u w),
        ⋃ (_hw : w ∉ E.rightHalfPlaneVertices r),
          {omega : ConfigSpace (Sym2 V) | omega s(u, w) = true} ∩
          ⋃ y : V, ⋃ (_hy : y ∈ R),
            {omega : ConfigSpace (Sym2 V) | (P.cluster omega y).Infinite} ∩
            P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∩
            P.connectedWithinSet
              (E.rightHalfPlaneStripVertices r n) x y := by
    ext omega
    constructor
    · rintro ⟨b, hb, z, hbz, hz, hbzOpen, x, hxL, hxInfinite, hxb,
        u, hu, w, huw, hw, huwOpen, y, hyR, hyInfinite, hyu, hxy⟩
      apply Set.mem_iUnion.2
      refine ⟨b, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hb, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨z, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hbz, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hz, hbzOpen, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨x, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hxL, ⟨hxInfinite, hxb⟩, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨u, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hu, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨w, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨huw, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hw, huwOpen, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨y, ?_⟩
      apply Set.mem_iUnion.2
      exact ⟨hyR, ⟨hyInfinite, hyu⟩, hxy⟩
    · intro h
      obtain ⟨b, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hb, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨z, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hbz, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hz, hbzOpen, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨x, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hxL, ⟨hxInfinite, hxb⟩, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨u, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hu, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨w, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨huw, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hw, huwOpen, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨y, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hyR, ⟨hyInfinite, hyu⟩, hxy⟩ := Set.mem_iUnion.1 h
      exact ⟨b, hb, z, hbz, hz, hbzOpen, x, hxL, hxInfinite, hxb,
        u, hu, w, huw, hw, huwOpen, y, hyR, hyInfinite, hyu, hxy⟩
  rw [heq]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
    MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _hbz =>
    MeasurableSet.iUnion fun _hz =>
      (measurableSet_eq_fun (ConfigSpace.measurable_eval s(b, z))
        measurable_const).inter
      (MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
        ((P.measurableSet_cluster_infinite x).inter
          (P.connectedWithinSet_measurableSet
            (E.rightHalfPlaneVertices r) x b)).inter
        (MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun _hu =>
          MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun _huw =>
          MeasurableSet.iUnion fun _hw =>
            (measurableSet_eq_fun (ConfigSpace.measurable_eval s(u, w))
              measurable_const).inter
            (MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
              ((P.measurableSet_cluster_infinite y).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneVertices r) y u)).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneStripVertices r n) x y))))

theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    IsIncreasing (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
  intro omega eta homega
  rintro ⟨b, hb, z, hbz, hz, hbzOpen, x, hxL, hxInfinite, hxb,
    u, hu, w, huw, hw, huwOpen, y, hyR, hyInfinite, hyu, hxy⟩
  exact ⟨b, hb, z, hbz, hz, homega _ hbzOpen,
    x, hxL, P.clusterInfinite_isIncreasing x homega hxInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb,
    u, hu, w, huw, hw, homega _ huwOpen,
    y, hyR, P.clusterInfinite_isIncreasing y homega hyInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hyu,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxy⟩



theorem measureReal_pos_of_forceOpenFinset_preimage
    {X : Type*} [DecidableEq X] [Countable X]
    (mu : Measure (ConfigSpace (Sym2 X))) [IsFiniteMeasure mu]
    (hfe : HasFiniteEnergy mu) (F : Finset (Sym2 X))
    {A B : Set (ConfigSpace (Sym2 X))}
    (hB : MeasurableSet B) (hApos : 0 < mu.real A)
    (hsub : A ⊆ forceOpenFinset F ⁻¹' B) :
    0 < mu.real B := by
  by_contra hnot
  have hBreal : mu.real B = 0 :=
    le_antisymm (not_lt.mp hnot) measureReal_nonneg
  have hBzero : mu B = 0 :=
    ((ENNReal.toReal_eq_zero_iff (mu B)).mp hBreal).resolve_right
      (measure_ne_top mu _)
  have hmapZero := hfe F hBzero
  rw [Measure.map_apply (measurable_forceOpenFinset F) hB] at hmapZero
  have hAzero : mu A = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hmapZero) bot_le
  unfold Measure.real at hApos
  rw [hAzero] at hApos
  norm_num at hApos



theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_forceOpen_subset_exited
    (E : PeriodicPlaneEmbedding P) {r c d : Real} {n : Nat}
    {L R : Finset V} {b u z w : V}
    (hbz : P.graph.Adj b z) (hz : z ∉ E.rightHalfPlaneVertices r)
    (huw : P.graph.Adj u w) (hw : w ∉ E.rightHalfPlaneVertices r) :
    E.finiteJoinedBoundaryArmAt r c d n L R b u ⊆
      forceOpenFinset {s(b, z), s(u, w)} ⁻¹'
        E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R := by
  intro omega homega
  rcases homega with ⟨hb, hu, x, hxL, hxInfinite, hxb,
    y, hyR, hyInfinite, hyu, hxy⟩
  let eta := forceOpenFinset {s(b, z), s(u, w)} omega
  have home : omega ≤ eta := by
    intro e
    by_cases he : e ∈ ({s(b, z), s(u, w)} : Finset (Sym2 V))
    · simp [eta, forceOpenFinset, he]
    · simp [eta, forceOpenFinset, he]
  change eta ∈ E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R
  refine ⟨b, hb, z, hbz, hz, ?_, x, hxL,
    P.clusterInfinite_isIncreasing x home hxInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ home hxb,
    u, hu, w, huw, hw, ?_, y, hyR,
    P.clusterInfinite_isIncreasing y home hyInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ home hyu,
    P.connectedWithinSet_isIncreasing _ _ _ home hxy⟩
  · simp [eta, forceOpenFinset]
  · simp [eta, forceOpenFinset]



theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measureReal_pos
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hfe : HasFiniteEnergy mu)
    (r c d : Real) (n : Nat) (L R : Finset V)
    (hpos : 0 < mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R)) :
    0 < mu.real
      (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
  obtain ⟨b, u, hAtPos⟩ :=
    E.exists_positive_finiteJoinedBoundaryArmAt mu r c d n L R hpos
  have hAtNonempty :
      (E.finiteJoinedBoundaryArmAt r c d n L R b u).Nonempty := by
    by_contra hnot
    rw [Set.not_nonempty_iff_eq_empty.mp hnot] at hAtPos
    simp at hAtPos
  obtain ⟨omega, hb, hu, _⟩ := hAtNonempty
  obtain ⟨z, hbz, hz⟩ := hb.1.2
  obtain ⟨w, huw, hw⟩ := hu.1.2
  apply measureReal_pos_of_forceOpenFinset_preimage mu hfe
    {s(b, z), s(u, w)}
    (E.finiteOpenExitedJoinedBoundaryArmEvent_measurableSet r c d n L R)
    hAtPos
  exact E.finiteJoinedBoundaryArmAt_forceOpen_subset_exited
    hbz (by change ¬ r ≤ E.vertexCoord z 0; exact not_le.mpr hz)
    huw (by change ¬ r ≤ E.vertexCoord w 0; exact not_le.mpr hw)



theorem PeriodicPlaneEmbedding.exists_positive_finiteOpenExitedJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hfe : HasFiniteEnergy mu) (r : Real) :
    ∃ L U : Finset V, ∃ n : Nat,
      0 < mu.real
        (E.finiteOpenExitedJoinedBoundaryArmEvent r 0 1 n L U) := by
  obtain ⟨L, U, n, _hL, hjoined⟩ :=
    E.exists_highProbability_finiteJoinedBoundaryArmEvent_with_margin
      mu hFKG hTI hunique (r := r) (R := r) le_rfl
        (by norm_num : (0 : Real) < 1 / 2)
  refine ⟨L, U, n,
    E.finiteOpenExitedJoinedBoundaryArmEvent_measureReal_pos
      mu hfe r 0 1 n L U ?_⟩
  linarith



theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_openWalk
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V,
      z ∉ E.rightHalfPlaneVertices r ∧
    ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V,
      w ∉ E.rightHalfPlaneVertices r ∧
    ∃ q : (P.openSubgraph omega).Walk z w,
      b ∈ q.support ∧ u ∈ q.support ∧
      ∀ v ∈ q.support, v = z ∨ v = w ∨
        v ∈ E.rightHalfPlaneVertices r := by
  rcases h with ⟨b, hb, z, hbz, hz, hbzOpen, x, _hxL, _hxInfinite, hxb,
    u, hu, w, huw, hw, huwOpen, y, _hyR, _hyInfinite, hyu, hxy⟩
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxb
  obtain ⟨qyu, hqyu⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyu
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  have hbzAdj : (P.openSubgraph omega).Adj b z := ⟨hbz, hbzOpen⟩
  have huwAdj : (P.openSubgraph omega).Adj u w := ⟨huw, huwOpen⟩
  let left : (P.openSubgraph omega).Walk z x := qxb.reverse.cons hbzAdj.symm
  let right : (P.openSubgraph omega).Walk y w :=
    qyu.append ((SimpleGraph.Walk.nil : (P.openSubgraph omega).Walk w w).cons huwAdj)
  let q : (P.openSubgraph omega).Walk z w := (left.append qxy).append right
  refine ⟨b, hb, z, hz, u, hu, w, hw, q, ?_, ?_, ?_⟩
  · have hbLeft : b ∈ left.support := by
      dsimp only [left]
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_reverse]
      apply List.mem_cons_of_mem
      simpa using qxb.end_mem_support
    simp only [q, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl hbLeft)
  · have huRight : u ∈ right.support := by
      simp only [right, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl qyu.end_mem_support
    simp only [q, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr huRight
  · intro v hv
    simp only [q, SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with (hv | hv) | hv
    · dsimp only [left] at hv
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_reverse]
        at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hqxb v (by simpa using hv)))
    · exact Or.inr (Or.inr
        (E.rightHalfPlaneStripVertices_subset r n (hqxy v hv)))
    · simp only [right, SimpleGraph.Walk.mem_support_append_iff] at hv
      rcases hv with hv | hv
      · exact Or.inr (Or.inr (hqyu v hv))
      · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hv
        simp only [List.mem_cons] at hv
        rcases hv with hv | hv
        · exact Or.inr (Or.inr (hv.symm ▸ hu.1.1))
        · have hvw : v = w := by simpa using hv
          exact Or.inr (Or.inl hvw)





def PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
    (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) b).Infinite}

theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    MeasurableSet (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
  have heq : E.rightHalfPlaneBoundaryHasInfiniteCluster r =
      ⋃ b : V, ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega
            (E.rightHalfPlaneVertices r) b).Infinite} := by
    ext omega
    simp [PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster]
  rw [heq]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
    P.measurableSet_clusterWithinSet_infinite
      (E.rightHalfPlaneVertices r) b


theorem PeriodicGraph.clusterWithinSet_infinite_of_connectedWithinSet
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {A : Set V} {x b : V}
    (hinfinite : (P.clusterWithinSet omega A x).Infinite)
    (hxb : omega ∈ P.connectedWithinSet A x b) :
    (P.clusterWithinSet omega A b).Infinite := by
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxb
  apply hinfinite.mono
  intro y hy
  obtain ⟨qxy, hqxy⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk (by simpa using hy)
  have hwalk : ∀ v ∈ (qxb.reverse.append qxy).support, v ∈ A := by
    intro v hv
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv
    · exact hqxb v (by simpa using hv)
    · exact hqxy v hv
  exact P.mem_connectedWithinSet_of_walk (qxb.reverse.append qxy) hwalk




theorem PeriodicPlaneEmbedding.unique_halfPlane_outside_subset_boundaryInfinite
    (E : PeriodicPlaneEmbedding P) (r : Real) (T : Set V)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩
      (E.rightHalfPlaneHasInfiniteCluster r ∩ P.setHitsInfinite T) ⊆
        E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
  rintro omega ⟨hunique, ⟨⟨x, hxH, hxRestricted⟩,
    y, hyT, hyInfinite⟩⟩
  have hxGlobal : (P.cluster omega x).Infinite := by
    apply hxRestricted.mono
    intro z hz
    obtain ⟨q, _hq⟩ :=
      P.connectedWithinSet_exists_openSubgraphWalk (by simpa using hz)
    exact ⟨q⟩
  have hxy : (P.openSubgraph omega).Reachable x y :=
    hunique.2 x y hxGlobal hyInfinite
  obtain ⟨b, hb, hxb⟩ :=
    E.connectedWithin_rightHalfPlane_boundary_of_reachable
      omega r hxH (hT hyT) hxy
  exact ⟨b, hb,
    P.clusterWithinSet_infinite_of_connectedWithinSet hxRestricted hxb⟩




theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (hhalf : mu (E.rightHalfPlaneHasInfiniteCluster r) = 1) :
    mu (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1 := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  choose z hz using fun N : Nat =>
    E.exists_shift_orbitBox_subset_leftComplement N r
  let T : Nat → Set V := fun N => P.shift (z N) '' (P.orbitBox N : Set V)
  have hToutside (N : Nat) : T N ⊆
      (E.rightHalfPlaneVertices r)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hz N v hv
  have hTmass (N : Nat) :
      mu.real (P.setHitsInfinite (T N)) =
        mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [T]
    rw [P.setHitsInfinite_translate_measureReal_eq mu hTI (z N)]
    rfl
  have hUae : ∀ᵐ omega ∂mu,
      omega ∈ {omega | P.HasUniqueInfiniteCluster omega} :=
    (mem_ae_iff_prob_eq_one P.measurableSet_hasUniqueInfiniteCluster).2 hunique
  have hHae : ∀ᵐ omega ∂mu,
      omega ∈ E.rightHalfPlaneHasInfiniteCluster r :=
    (mem_ae_iff_prob_eq_one
      (E.rightHalfPlaneHasInfiniteCluster_measurableSet r)).2 hhalf
  have hle (N : Nat) : mu.real (P.setHitsInfinite (T N)) ≤
      mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
    have hae : (P.setHitsInfinite (T N) : Set (ConfigSpace (Sym2 V))) ≤ᵐ[mu]
        E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
      filter_upwards [hUae, hHae] with omega hU hH hT
      exact E.unique_halfPlane_outside_subset_boundaryInfinite r (T N)
        (hToutside N) ⟨hU, hH, hT⟩
    exact ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono_ae hae)
  have ht := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hbound : (1 : Real) ≤
      mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
    apply le_of_tendsto ht
    filter_upwards with N
    rw [← hTmass N]
    exact hle N
  have hreal : mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1 :=
    le_antisymm measureReal_le_one hbound
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu _)
    (by norm_num : (1 : ENNReal) ≠ ⊤)).mp
  simpa [Measure.real] using hreal



def PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P) (r c d : Real) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
    c ≤ E.vertexCoord b 1 ∧ E.vertexCoord b 1 ≤ d ∧
    (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) b).Infinite}

theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) :
    MeasurableSet (E.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d) := by
  have heq : E.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d =
      ⋃ b : V, ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
      ⋃ (_hc : c ≤ E.vertexCoord b 1),
      ⋃ (_hd : E.vertexCoord b 1 ≤ d),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega
            (E.rightHalfPlaneVertices r) b).Infinite} := by
    ext omega
    simp only [PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster,
      Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  rw [heq]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
    MeasurableSet.iUnion fun _hc => MeasurableSet.iUnion fun _hd =>
      P.measurableSet_clusterWithinSet_infinite
        (E.rightHalfPlaneVertices r) b



theorem PeriodicPlaneEmbedding.iUnion_boundaryBandHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    (⋃ n : Nat, E.rightHalfPlaneBoundaryBandHasInfiniteCluster
      r (-(n : Real)) n) =
        E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, b, hb, _hc, _hd, hinfinite⟩ := by
      simpa only [Set.mem_iUnion,
        PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster,
        Set.mem_setOf_eq] using h
    exact ⟨b, hb, hinfinite⟩
  · rintro ⟨b, hb, hinfinite⟩
    obtain ⟨n, hn⟩ := exists_nat_ge |E.vertexCoord b 1|
    apply Set.mem_iUnion.2
    refine ⟨n, b, hb, ?_, ?_, hinfinite⟩
    · exact (neg_le_of_abs_le hn)
    · exact le_trans (le_abs_self _) hn


theorem PeriodicPlaneEmbedding.exists_positive_boundaryBandHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r : Real)
    (hone : mu (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1) :
    ∃ n : Nat, 0 < mu.real
      (E.rightHalfPlaneBoundaryBandHasInfiniteCluster r (-(n : Real)) n) := by
  have hpos : 0 < mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
    rw [Measure.real, hone]
    norm_num
  rw [← E.iUnion_boundaryBandHasInfiniteCluster r] at hpos
  exact exists_measureReal_pos_of_iUnion_measureReal_pos mu _ hpos

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair





theorem no_open_dual_escape_of_attached_simpleCrosscut
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {s t : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk s t)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi : Fin 2 → Real}
    (lower : Path lo
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex x)))
    (upper : Path
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex y)) hi)
    (hcrossRect : Set.range
      (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous).trans upper)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hescapeRect : Set.range
      ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : D.dualEmbedding.vertexCoord s 0 = a)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ z ∈ Set.range
      ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous), z 0 = a →
      lo 1 < z 1 ∧ z 1 < hi 1)
    (hlower : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range lower))
    (hupper : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range upper))
    (hexit : D.dualEmbedding.vertexCoord t 0 = b ∨
      (D.dualEmbedding.vertexCoord t 1 = d ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval,
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1 < d) ∨
      (D.dualEmbedding.vertexCoord t 1 = c ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval, c <
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1)) :
    False := by
  let core := (D.primalEmbedding.simpleWalkArc p).map
    D.primalEmbedding.coordinates.continuous
  let escape := (D.dualEmbedding.simpleWalkArc q).map
    D.dualEmbedding.coordinates.continuous
  let crosscut := lower.trans (core.trans upper)
  have hinter : (Set.range escape ∩ Set.range crosscut).Nonempty := by
    rcases hexit with hright | htop | hbottom
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hright hloY hhiY hescapeLeftBetween
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX htop.1 htop.2.1 hloY hhiY hescapeLeftBetween htop.2.2
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hbottom.1 hbottom.2.1 hloY hhiY hescapeLeftBetween
            hbottom.2.2
  have hinterCore : (Set.range escape ∩ Set.range core).Nonempty :=
    ContinuousHalfPlaneCrosscut.attachedCrosscut_intersection_reduces_to_core
      lower core upper escape hinter hlower hupper
  obtain ⟨z, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hinterCore
  have hcoord : D.dualEmbedding.coordinates
      (D.dualEmbedding.simpleWalkArc q u) =
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p v) := by
    simpa only [escape, core] using hu.trans hv.symm
  have hphysical : D.dualEmbedding.simpleWalkArc q u =
      D.primalEmbedding.simpleWalkArc p v := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨v, rfl⟩ ⟨u, hphysical⟩





theorem no_open_dual_escape_of_doublyAttached_simpleCrosscut
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {s t : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk s t)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi estart : Fin 2 → Real}
    (lower : Path lo
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex x)))
    (upper : Path
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex y)) hi)
    (eprefix : Path estart
      (D.dualEmbedding.coordinates (D.dualEmbedding.vertex s)))
    (hcrossRect : Set.range
      (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous).trans upper)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hescapeRect : Set.range
      (eprefix.trans ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : estart 0 = a)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ z ∈ Set.range
      (eprefix.trans ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous)), z 0 = a →
      lo 1 < z 1 ∧ z 1 < hi 1)
    (hPrefixLower : Disjoint (Set.range eprefix) (Set.range lower))
    (hPrefixCore : Disjoint (Set.range eprefix)
      (Set.range ((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous)))
    (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range upper))
    (hCoreLower : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range lower))
    (hCoreUpper : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range upper))
    (hexit : D.dualEmbedding.vertexCoord t 0 = b ∨
      (D.dualEmbedding.vertexCoord t 1 = d ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval,
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1 < d) ∨
      (D.dualEmbedding.vertexCoord t 1 = c ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval, c <
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1)) :
    False := by
  let pcore := (D.primalEmbedding.simpleWalkArc p).map
    D.primalEmbedding.coordinates.continuous
  let ecore := (D.dualEmbedding.simpleWalkArc q).map
    D.dualEmbedding.coordinates.continuous
  let crosscut := lower.trans (pcore.trans upper)
  let escape := eprefix.trans ecore
  have hinter : (Set.range escape ∩ Set.range crosscut).Nonempty := by
    rcases hexit with hright | htop | hbottom
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hright hloY hhiY hescapeLeftBetween
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX htop.1 htop.2.1 hloY hhiY hescapeLeftBetween htop.2.2
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hbottom.1 hbottom.2.1 hloY hhiY hescapeLeftBetween
            hbottom.2.2
  have hinterCore : (Set.range ecore ∩ Set.range pcore).Nonempty :=
    ContinuousHalfPlaneCrosscut.doublyAttached_intersection_reduces_to_cores
      lower pcore upper eprefix ecore hinter hPrefixLower hPrefixCore
        hPrefixUpper hCoreLower hCoreUpper
  obtain ⟨z, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hinterCore
  have hcoord : D.dualEmbedding.coordinates
      (D.dualEmbedding.simpleWalkArc q u) =
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p v) := by
    simpa only [ecore, pcore] using hu.trans hv.symm
  have hphysical : D.dualEmbedding.simpleWalkArc q u =
      D.primalEmbedding.simpleWalkArc p v := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨v, rfl⟩ ⟨u, hphysical⟩




theorem no_open_dual_escape_of_doublyAttached_subpaths
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {s t : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk s t)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo px py hi estart eroot efinish : Fin 2 → Real}
    (lower : Path lo px) (pcore : Path px py) (upper : Path py hi)
    (eprefix : Path estart eroot) (ecore : Path eroot efinish)
    (hpcoreRange : Set.range pcore ⊆ Set.range
      ((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous))
    (hecoreRange : Set.range ecore ⊆ Set.range
      ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
    (hcrossRect : Set.range (lower.trans (pcore.trans upper)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hescapeRect : Set.range (eprefix.trans ecore) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : estart 0 = a)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ z ∈ Set.range (eprefix.trans ecore),
      z 0 = a → lo 1 < z 1 ∧ z 1 < hi 1)
    (hPrefixLower : Disjoint (Set.range eprefix) (Set.range lower))
    (hPrefixCore : Disjoint (Set.range eprefix) (Set.range pcore))
    (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range upper))
    (hCoreLower : Disjoint (Set.range ecore) (Set.range lower))
    (hCoreUpper : Disjoint (Set.range ecore) (Set.range upper))
    (hexit : efinish 0 = b ∨
      (efinish 1 = d ∧ a < efinish 0 ∧
        ∀ u : unitInterval,
          (lower.trans (pcore.trans upper)) u 1 < d) ∨
      (efinish 1 = c ∧ a < efinish 0 ∧
        ∀ u : unitInterval, c <
          (lower.trans (pcore.trans upper)) u 1)) :
    False := by
  let crosscut := lower.trans (pcore.trans upper)
  let escape := eprefix.trans ecore
  have hinter : (Set.range escape ∩ Set.range crosscut).Nonempty := by
    rcases hexit with hright | htop | hbottom
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hright hloY hhiY hescapeLeftBetween
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX htop.1 htop.2.1 hloY hhiY hescapeLeftBetween htop.2.2
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hbottom.1 hbottom.2.1 hloY hhiY hescapeLeftBetween
            hbottom.2.2
  have hinterCore : (Set.range ecore ∩ Set.range pcore).Nonempty :=
    ContinuousHalfPlaneCrosscut.doublyAttached_intersection_reduces_to_cores
      lower pcore upper eprefix ecore hinter hPrefixLower hPrefixCore
        hPrefixUpper hCoreLower hCoreUpper
  obtain ⟨z, hzECore, hzPCore⟩ := hinterCore
  obtain ⟨u, hu⟩ := hecoreRange hzECore
  obtain ⟨v, hv⟩ := hpcoreRange hzPCore
  have hcoord : D.dualEmbedding.coordinates
      (D.dualEmbedding.simpleWalkArc q u) =
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p v) :=
    hu.trans hv.symm
  have hphysical : D.dualEmbedding.simpleWalkArc q u =
      D.primalEmbedding.simpleWalkArc p v := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨v, rfl⟩ ⟨u, hphysical⟩




theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_orderedJoinedBand_exclusion
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rPrimal rDual R : Real) (hrR : rPrimal ≤ R) (buffer : Nat)
    (hgeom : ∀ (n m : Nat) (L U : Finset V) (k : Nat),
      n + buffer < m →
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift (verticalShift (1 + 2 * (m : Int)))) →
      (∀ x ∈ L, ∀ y ∈ U,
        D.primalEmbedding.vertexCoord x 1 +
            2 * (n + buffer : Nat) + 2 <
          D.primalEmbedding.vertexCoord y 1) →
      Disjoint
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(m : Real)) m k L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(n : Real)) n)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  rcases D.dualEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one
      muDual hdualErgodic rDual with hzero | hone
  · exact hzero
  · have hboundaryOne :=
      D.dualEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one
        muDual hdualErgodic.1 hdualUnique rDual hone
    obtain ⟨n, hbandPos⟩ :=
      D.dualEmbedding.exists_positive_boundaryBandHasInfiniteCluster
        muDual rDual hboundaryOne
    let band := D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
      rDual (-(n : Real)) n
    let pulled := (dualConfigEquiv D.edgeDual) ⁻¹' band
    have hbandMeas : MeasurableSet band :=
      D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet
        rDual (-(n : Real)) n
    have hpulledMeas : MeasurableSet pulled :=
      (continuous_dualConfigEquiv D.edgeDual).measurable hbandMeas
    have hpulledPos : 0 < mu.real pulled := by
      rw [← D.dualMeasure_measureReal mu hbandMeas]
      exact hbandPos
    let epsilon : Real := mu.real pulled / 2
    have hepsilon : 0 < epsilon := half_pos hpulledPos
    obtain ⟨m, L, U, k, hm, hL, hU, horder, hjoined⟩ :=
      D.primalEmbedding.exists_highProbability_ordered_finiteJoinedBoundaryArmEvent
        mu hFKG hTI hunique hrR n buffer hepsilon
    let joined := D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
      (-(m : Real)) m k L U
    have hjdisjoint : Disjoint joined pulled := by
      dsimp only [joined, pulled, band]
      exact hgeom n m L U k hm hL hU horder
    have hjMeas : MeasurableSet joined :=
      D.primalEmbedding.finiteJoinedBoundaryArmEvent_measurableSet
        rPrimal (-(m : Real)) m k L U
    have hinter : joined ∩ pulled = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hjdisjoint
    have hadd := measureReal_union_add_inter (μ := mu) hpulledMeas (s := joined)
    rw [hinter] at hadd
    simp only [measureReal_empty, add_zero] at hadd
    have hunion : mu.real (joined ∪ pulled) ≤ 1 := measureReal_le_one
    have hsum : mu.real joined + mu.real pulled ≤ 1 := by linarith
    dsimp only [epsilon] at hjoined
    have hjShape : mu.real joined = mu.real
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(m : Real)) m k L U) := rfl
    rw [← hjShape] at hjoined
    linarith





theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_deepJoinedBand_exclusion
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rPrimal rDual R : Real) (hrR : rPrimal ≤ R)
    (margin : Nat) (hmargin : 0 < margin)
    (hgeom : ∀ (n : Nat) (L U : Finset V) (k : Nat),
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift
        (verticalShift (1 + 2 * (n + margin : Nat)))) →
      Disjoint
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(n + margin : Nat) : Real) (n + margin : Nat) k L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(n : Real)) n)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  rcases D.dualEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one
      muDual hdualErgodic rDual with hzero | hone
  · exact hzero
  · have hboundaryOne :=
      D.dualEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one
        muDual hdualErgodic.1 hdualUnique rDual hone
    obtain ⟨n, hbandPos⟩ :=
      D.dualEmbedding.exists_positive_boundaryBandHasInfiniteCluster
        muDual rDual hboundaryOne
    let band := D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
      rDual (-(n : Real)) n
    let pulled := (dualConfigEquiv D.edgeDual) ⁻¹' band
    have hbandMeas : MeasurableSet band :=
      D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet
        rDual (-(n : Real)) n
    have hpulledMeas : MeasurableSet pulled :=
      (continuous_dualConfigEquiv D.edgeDual).measurable hbandMeas
    have hpulledPos : 0 < mu.real pulled := by
      rw [← D.dualMeasure_measureReal mu hbandMeas]
      exact hbandPos
    let epsilon : Real := mu.real pulled / 2
    have hepsilon : 0 < epsilon := half_pos hpulledPos
    let gap : Int := 2 * (n + margin : Nat)
    have hgap : 0 < gap := by
      dsimp only [gap]
      positivity
    obtain ⟨L, U, k, hL, hU, hjoined⟩ :=
      D.primalEmbedding.exists_highProbability_separated_finiteJoinedBoundaryArmEvent_with_margin
        mu hFKG hTI hunique hrR
          (-(n + margin : Nat) : Real) gap hepsilon
    let joined := D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
      (-(n + margin : Nat) : Real)
      ((-(n + margin : Nat) : Real) + gap) k L U
    have hgapEnd : ((-(n + margin : Nat) : Real) + gap) =
        (n + margin : Nat) := by
      dsimp only [gap]
      norm_num
      push_cast
      ring
    have hjdisjoint : Disjoint joined pulled := by
      dsimp only [joined, pulled, band]
      rw [hgapEnd]
      exact hgeom n L U k hL hU
    have hjMeas : MeasurableSet joined :=
      D.primalEmbedding.finiteJoinedBoundaryArmEvent_measurableSet
        rPrimal (-(n + margin : Nat) : Real)
          ((-(n + margin : Nat) : Real) + gap) k L U
    have hinter : joined ∩ pulled = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hjdisjoint
    have hadd := measureReal_union_add_inter (μ := mu) hpulledMeas (s := joined)
    rw [hinter] at hadd
    simp only [measureReal_empty, add_zero] at hadd
    have hunion : mu.real (joined ∪ pulled) ≤ 1 := measureReal_le_one
    have hsum : mu.real joined + mu.real pulled ≤ 1 := by linarith
    dsimp only [epsilon] at hjoined
    have hjShape : mu.real joined = mu.real
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(n + margin : Nat) : Real)
          ((-(n + margin : Nat) : Real) + gap) k L U) := rfl
    rw [← hjShape] at hjoined
    linarith





theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_joinedBand_exclusion
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rPrimal rDual : Real)
    (hgeom : ∀ (n : Nat) (L U : Finset V) (k : Nat),
      Disjoint
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(n + 1 : Nat) : Real) (n + 1 : Nat) k L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(n : Real)) n)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  apply D.complementaryDual_rightHalfPlane_measure_eq_zero_of_deepJoinedBand_exclusion
    mu hFKG hTI hunique hdualErgodic hdualUnique
      rPrimal rDual rPrimal le_rfl 1 (by norm_num)
  intro n L U k _hL _hU
  simpa using hgeom n L U k

end PeriodicPlanarDualPair

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    MeasurableSet (E.infiniteOpenBoundaryConnection r S) := by
  classical
  have heq : E.infiniteOpenBoundaryConnection r S =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          ⋃ b : V, ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
            ⋃ z : V, ⋃ (_hbz : P.graph.Adj b z),
              ⋃ (_hz : z ∉ E.rightHalfPlaneVertices r),
                {omega : ConfigSpace (Sym2 V) | omega s(b, z) = true} ∩
                  P.connectedWithinSet (E.rightHalfPlaneVertices r) x b := by
    ext omega
    constructor
    · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
    · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
      exact ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    (P.measurableSet_cluster_infinite x).inter
      (MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
        MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _hbz =>
          MeasurableSet.iUnion fun _hz =>
            (measurableSet_eq_fun (ConfigSpace.measurable_eval s(b, z))
              measurable_const).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneVertices r) x b))

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    IsIncreasing (E.infiniteOpenBoundaryConnection r S) := by
  intro omega eta homega
  rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
  exact ⟨x, hxS, P.clusterInfinite_isIncreasing x homega hxInfinite,
    b, hb, z, hbz, hz, homega _ hbzOpen,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb⟩



theorem PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteOpenBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩
        (P.setHitsInfinite S ∩ P.setHitsInfinite T) ⊆
      E.infiniteOpenBoundaryConnection r S := by
  rintro omega ⟨hunique, ⟨x, hxS, hxInfinite⟩, ⟨y, hyT, hyInfinite⟩⟩
  have hxy : (P.openSubgraph omega).Reachable x y :=
    hunique.2 x y hxInfinite hyInfinite
  obtain ⟨p⟩ := hxy
  obtain ⟨b, hbHalfPlane, z, hbzOpen, hzOutside, q, hqHalfPlane,
    _hqSub, _hzSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      (E.rightHalfPlaneVertices r) p (hS hxS) (hT hyT)
  have hbBoundary : b ∈ E.rightHalfPlaneBoundaryVertices r :=
    ⟨hbHalfPlane, z, hbzOpen.1, by
      change ¬ r ≤ E.vertexCoord z 0 at hzOutside
      exact lt_of_not_ge hzOutside⟩
  have hxb : omega ∈ P.connectedWithinSet
      (E.rightHalfPlaneVertices r) x b :=
    P.mem_connectedWithinSet_of_walk q hqHalfPlane
  exact ⟨x, hxS, hxInfinite, b, hbBoundary, z, hbzOpen.1,
    hzOutside, hbzOpen.2, hxb⟩



theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_mul
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    mu.real (P.setHitsInfinite S) * mu.real (P.setHitsInfinite T) ≤
      mu.real (E.infiniteOpenBoundaryConnection r S) := by
  let U : Set (ConfigSpace (Sym2 V)) :=
    {omega | P.HasUniqueInfiniteCluster omega}
  let A := P.setHitsInfinite S
  let B := P.setHitsInfinite T
  let C := E.infiniteOpenBoundaryConnection r S
  have hAB : mu.real A * mu.real B ≤ mu.real (A ∩ B) :=
    hFKG A B (P.setHitsInfinite_measurableSet S)
      (P.setHitsInfinite_measurableSet T)
      (P.setHitsInfinite_isIncreasing S) (P.setHitsInfinite_isIncreasing T)
  have hUC : U ∩ (A ∩ B) ⊆ C := by
    exact E.unique_two_sides_subset_infiniteOpenBoundaryConnection r hS hT
  have hUae : ∀ᵐ omega ∂mu, omega ∈ U :=
    (mem_ae_iff_prob_eq_one P.measurableSet_hasUniqueInfiniteCluster).2 hunique
  have hABleC : (A ∩ B : Set (ConfigSpace (Sym2 V))) ≤ᵐ[mu] C := by
    filter_upwards [hUae] with omega hU hABmem
    exact hUC ⟨hU, hABmem⟩
  have hmeasure : mu (A ∩ B) ≤ mu C := measure_mono_ae hABleC
  have hreal : mu.real (A ∩ B) ≤ mu.real C :=
    ENNReal.toReal_mono (measure_ne_top mu C) hmeasure
  exact hAB.trans hreal





theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_of_openWalk
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    {B a b c d : Real}
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (hB0 : 0 ≤ B) (hab : a + B < b) {x y : V}
    (p : (P.openSubgraph omega).Walk x y)
    (hx : E.vertexCoord x 0 < a) (hy : b < E.vertexCoord y 0)
    (hpY : ∀ v ∈ p.support,
      c ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ d) :
    omega ∈ E.horizontalCrossingEvent a b c d := by
  have hxB : x ∈ {v : V | E.vertexCoord v 0 ≤ b} := by
    change E.vertexCoord x 0 ≤ b
    linarith
  have hyB : y ∉ {v : V | E.vertexCoord v 0 ≤ b} := by
    simpa only [Set.mem_setOf_eq, not_le] using hy
  obtain ⟨xr, hxrB, zr, hxrZr, hzrB, right, hrightB,
    hrightSub, _hzrSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | E.vertexCoord v 0 ≤ b} p hxB hyB
  have hxrNear : a < E.vertexCoord xr 0 := by
    have hdisp := hB hxrZr.1 (1 : unitInterval) (0 : Fin 2)
    have heq :
        E.coordinates (E.edgeArc hxrZr.1 (1 : unitInterval) - E.vertex xr) 0 =
          E.vertexCoord zr 0 - E.vertexCoord xr 0 := by
      rw [Path.target]
      simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [heq] at hdisp
    have hhigh := (abs_le.mp hdisp).2
    change ¬ E.vertexCoord zr 0 ≤ b at hzrB
    have hzrRight : b < E.vertexCoord zr 0 := lt_of_not_ge hzrB
    linarith
  have hxrA : xr ∈ {v : V | a ≤ E.vertexCoord v 0} := hxrNear.le
  have hxA : x ∉ {v : V | a ≤ E.vertexCoord v 0} := by
    simpa only [Set.mem_setOf_eq, not_le] using hx
  obtain ⟨xl, hxlA, zl, hxlZl, hzlA, middleRev, hmiddleA,
    hmiddleSub, _hzlSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | a ≤ E.vertexCoord v 0} right.reverse hxrA hxA
  let middle : (P.openSubgraph omega).Walk xl xr := middleRev.reverse
  have hmiddleRect : ∀ v ∈ middle.support,
      v ∈ E.rectVertices a b c d := by
    intro v hv
    have hvRev : v ∈ middleRev.support := by simpa [middle] using hv
    have hvRightRev : v ∈ right.reverse.support := hmiddleSub v hvRev
    have hvRight : v ∈ right.support := by simpa using hvRightRev
    have hvP : v ∈ p.support := hrightSub v hvRight
    exact ⟨hmiddleA v hvRev, hrightB v hvRight, hpY v hvP⟩
  have hxlRect := hmiddleRect xl middle.start_mem_support
  have hxrRect := hmiddleRect xr middle.end_mem_support
  have hleft : E.rectLeftBoundary a b c d ⟨xl, hxlRect⟩ := by
    refine ⟨zl, hxlZl.1, ?_⟩
    change ¬ a ≤ E.vertexCoord zl 0 at hzlA
    exact lt_of_not_ge hzlA
  have hright : E.rectRightBoundary a b c d ⟨xr, hxrRect⟩ := by
    refine ⟨zr, hxrZr.1, ?_⟩
    change ¬ E.vertexCoord zr 0 ≤ b at hzrB
    exact lt_of_not_ge hzrB
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xl, hxlRect⟩ ⟨xr, hxrRect⟩ :=
    ⟨middle.induce (E.rectVertices a b c d) hmiddleRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteHorizontalCrossing a b c d
  refine ⟨⟨xl, hxlRect⟩, ⟨xr, hxrRect⟩, hleft, hright, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach



theorem PeriodicPlaneEmbedding.verticalCrossingEvent_of_openWalk
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    {B a b c d : Real}
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (hB0 : 0 ≤ B) (hcd : c + B < d) {x y : V}
    (p : (P.openSubgraph omega).Walk x y)
    (hx : E.vertexCoord x 1 < c) (hy : d < E.vertexCoord y 1)
    (hpX : ∀ v ∈ p.support,
      a ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ b) :
    omega ∈ E.verticalCrossingEvent a b c d := by
  have hxD : x ∈ {v : V | E.vertexCoord v 1 ≤ d} := by
    change E.vertexCoord x 1 ≤ d
    linarith
  have hyD : y ∉ {v : V | E.vertexCoord v 1 ≤ d} := by
    simpa only [Set.mem_setOf_eq, not_le] using hy
  obtain ⟨xt, hxtD, zt, hxtZt, hztD, top, htopD,
    htopSub, _hztSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | E.vertexCoord v 1 ≤ d} p hxD hyD
  have hxtNear : c < E.vertexCoord xt 1 := by
    have hdisp := hB hxtZt.1 (1 : unitInterval) (1 : Fin 2)
    have heq :
        E.coordinates (E.edgeArc hxtZt.1 (1 : unitInterval) - E.vertex xt) 1 =
          E.vertexCoord zt 1 - E.vertexCoord xt 1 := by
      rw [Path.target]
      simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [heq] at hdisp
    have hhigh := (abs_le.mp hdisp).2
    change ¬ E.vertexCoord zt 1 ≤ d at hztD
    have hztTop : d < E.vertexCoord zt 1 := lt_of_not_ge hztD
    linarith
  have hxtC : xt ∈ {v : V | c ≤ E.vertexCoord v 1} := hxtNear.le
  have hxC : x ∉ {v : V | c ≤ E.vertexCoord v 1} := by
    simpa only [Set.mem_setOf_eq, not_le] using hx
  obtain ⟨xb, hxbC, zb, hxbZb, hzbC, middleRev, hmiddleC,
    hmiddleSub, _hzbSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | c ≤ E.vertexCoord v 1} top.reverse hxtC hxC
  let middle : (P.openSubgraph omega).Walk xb xt := middleRev.reverse
  have hmiddleRect : ∀ v ∈ middle.support,
      v ∈ E.rectVertices a b c d := by
    intro v hv
    have hvRev : v ∈ middleRev.support := by simpa [middle] using hv
    have hvTopRev : v ∈ top.reverse.support := hmiddleSub v hvRev
    have hvTop : v ∈ top.support := by simpa using hvTopRev
    have hvP : v ∈ p.support := htopSub v hvTop
    exact ⟨(hpX v hvP).1, (hpX v hvP).2,
      hmiddleC v hvRev, htopD v hvTop⟩
  have hxbRect := hmiddleRect xb middle.start_mem_support
  have hxtRect := hmiddleRect xt middle.end_mem_support
  have hbottom : E.rectBottomBoundary a b c d ⟨xb, hxbRect⟩ := by
    refine ⟨zb, hxbZb.1, ?_⟩
    change ¬ c ≤ E.vertexCoord zb 1 at hzbC
    exact lt_of_not_ge hzbC
  have htop : E.rectTopBoundary a b c d ⟨xt, hxtRect⟩ := by
    refine ⟨zt, hxtZt.1, ?_⟩
    change ¬ E.vertexCoord zt 1 ≤ d at hztD
    exact lt_of_not_ge hztD
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xb, hxbRect⟩ ⟨xt, hxtRect⟩ :=
    ⟨middle.induce (E.rectVertices a b c d) hmiddleRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteVerticalCrossing a b c d
  refine ⟨⟨xb, hxbRect⟩, ⟨xt, hxtRect⟩, hbottom, htop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach




theorem PeriodicPlaneEmbedding.exists_open_rectExit_of_clusterWithinSet_infinite
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    (A : Set V) {a b c d : Real} {x : V}
    (hxRect : x ∈ E.rectVertices a b c d)
    (hinfinite : (P.clusterWithinSet omega A x).Infinite) :
    ∃ v ∈ E.rectVertices a b c d, ∃ z : V,
      (P.openSubgraph omega).Adj v z ∧
      z ∉ E.rectVertices a b c d ∧ z ∈ A ∧
      ∃ q : (P.openSubgraph omega).Walk x v,
        ∀ u ∈ q.support, u ∈ A ∩ E.rectVertices a b c d := by
  obtain ⟨y, hyCluster, hyOutside⟩ :=
    hinfinite.exists_notMem_finite (E.rectVertices_finite a b c d)
  have hxy : omega ∈ P.connectedWithinSet A x y := by
    simpa [PeriodicGraph.clusterWithinSet] using hyCluster
  obtain ⟨p, hpA⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨v, hvRect, z, hvz, hzOutside, q, hqRect, hqSub, hzSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      (E.rectVertices a b c d) p hxRect hyOutside
  refine ⟨v, hvRect, z, hvz, hzOutside, hpA z hzSupport, q, ?_⟩
  intro u hu
  exact ⟨hpA u (hqSub u hu), hqRect u hu⟩





theorem PeriodicPlaneEmbedding.exists_open_exposedRectExit_of_rightHalfPlane_cluster
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    {r b c d : Real} {x : V}
    (hxRect : x ∈ E.rectVertices r b c d)
    (hinfinite : (P.clusterWithinSet omega
      (E.rightHalfPlaneVertices r) x).Infinite) :
    ∃ v ∈ E.rectVertices r b c d, ∃ z : V,
      (P.openSubgraph omega).Adj v z ∧
      z ∈ E.rightHalfPlaneVertices r ∧
      (b < E.vertexCoord z 0 ∨ E.vertexCoord z 1 < c ∨
        d < E.vertexCoord z 1) ∧
      ∃ q : (P.openSubgraph omega).Walk x v,
        ∀ u ∈ q.support,
          u ∈ E.rightHalfPlaneVertices r ∩ E.rectVertices r b c d := by
  obtain ⟨v, hvRect, z, hvz, hzOutside, hzHalfPlane, q, hq⟩ :=
    E.exists_open_rectExit_of_clusterWithinSet_infinite omega
      (E.rightHalfPlaneVertices r) hxRect hinfinite
  refine ⟨v, hvRect, z, hvz, hzHalfPlane, ?_, q, hq⟩
  by_cases hzRight : b < E.vertexCoord z 0
  · exact Or.inl hzRight
  by_cases hzBottom : E.vertexCoord z 1 < c
  · exact Or.inr (Or.inl hzBottom)
  by_cases hzTop : d < E.vertexCoord z 1
  · exact Or.inr (Or.inr hzTop)
  exfalso
  apply hzOutside
  exact ⟨hzHalfPlane, le_of_not_gt hzRight,
    le_of_not_gt hzBottom, le_of_not_gt hzTop⟩

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair






theorem not_infiniteComplementaryDualClusterWithin_rightHalfPlane_of_threeCrossings
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {B r R C D0 A Tbottom Ttop : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ B)
    (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ B)
    (hrR : r < R) (hRightWidth : A + 10 * B < R)
    (hBottom : C + 10 * B < Tbottom)
    (hTop : Ttop + 10 * B < D0)
    {x : W}
    (hxRect : x ∈ D.dualEmbedding.rectVertices r R C D0)
    (hxRight : D.dualEmbedding.vertexCoord x 0 < A)
    (hxBottom : Tbottom < D.dualEmbedding.vertexCoord x 1)
    (hxTop : D.dualEmbedding.vertexCoord x 1 < Ttop)
    (hRightCrossing : omega ∈
      D.primalEmbedding.verticalCrossingEvent
        (A + 4 * B) (R - 4 * B) (C - 4 * B) (D0 + 4 * B))
    (hBottomCrossing : omega ∈
      D.primalEmbedding.horizontalCrossingEvent
        (r - 5 * B) (R + 5 * B) (C + 4 * B) (Tbottom - 4 * B))
    (hTopCrossing : omega ∈
      D.primalEmbedding.horizontalCrossingEvent
        (r - 5 * B) (R + 5 * B) (Ttop + 4 * B) (D0 - 4 * B)) :
    ¬(Pdual.clusterWithinSet (dualConfigEquiv D.edgeDual omega)
      (D.dualEmbedding.rightHalfPlaneVertices r) x).Infinite := by
  intro hinfinite
  let eta := dualConfigEquiv D.edgeDual omega
  obtain ⟨v, hvRect, z, hvz, hzHalfPlane, hzSide, q, hq⟩ :=
    D.dualEmbedding.exists_open_exposedRectExit_of_rightHalfPlane_cluster
      eta hxRect hinfinite
  let edge : (Pdual.openSubgraph eta).Walk v z := .cons hvz .nil
  let exitWalk : (Pdual.openSubgraph eta).Walk x z := q.append edge
  have hzDisplacement :
      |D.dualEmbedding.vertexCoord z 0 -
        D.dualEmbedding.vertexCoord v 0| ≤ B := by
    have h := hBd hvz.1 (1 : unitInterval) (0 : Fin 2)
    have heq : D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hvz.1 (1 : unitInterval) -
          D.dualEmbedding.vertex v) 0 =
        D.dualEmbedding.vertexCoord z 0 -
          D.dualEmbedding.vertexCoord v 0 := by
      rw [Path.target]
      simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rwa [heq] at h
  have hzX : r - B ≤ D.dualEmbedding.vertexCoord z 0 ∧
      D.dualEmbedding.vertexCoord z 0 ≤ R + B := by
    have hvLeft := hvRect.1
    have hvRight := hvRect.2.1
    rw [abs_le] at hzDisplacement
    constructor <;> linarith
  have hexitX : ∀ u ∈ exitWalk.support,
      r - B ≤ D.dualEmbedding.vertexCoord u 0 ∧
        D.dualEmbedding.vertexCoord u 0 ≤ R + B := by
    intro u hu
    dsimp only [exitWalk] at hu
    rw [SimpleGraph.Walk.support_append] at hu
    rcases List.mem_append.mp hu with huQ | huEdge
    · have huRect := (hq u huQ).2
      exact ⟨huRect.1.trans' (sub_le_self r hBpos.le),
        huRect.2.1.trans (le_add_of_nonneg_right hBpos.le)⟩
    · have huz : u = z := by
        simpa [edge] using huEdge
      simpa [huz] using hzX
  by_cases hzBottom : D.dualEmbedding.vertexCoord z 1 < C
  · have hdualCrossing : eta ∈
        D.dualEmbedding.verticalCrossingEvent
          (r - B) (R + B) C Tbottom := by
      apply D.dualEmbedding.verticalCrossingEvent_of_openWalk eta hBd
        hBpos.le (by linarith) exitWalk.reverse hzBottom hxBottom
      intro u hu
      apply hexitX u
      rw [SimpleGraph.Walk.support_reverse] at hu
      simpa using hu
    have hdisjoint := D.matchedCrossingEvents_disjoint
      (a := r - 5 * B) (b := R + 5 * B) (c := C) (d := Tbottom)
      hBpos hBp hBd (by linarith) (by linarith)
    have hdualMem : omega ∈ (dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) C Tbottom := by
      change eta ∈ D.dualEmbedding.verticalCrossingEvent
        (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) C Tbottom
      convert hdualCrossing using 1 <;> ring_nf
    exact Set.disjoint_left.mp hdisjoint hBottomCrossing hdualMem
  by_cases hzTop : D0 < D.dualEmbedding.vertexCoord z 1
  · have hdualCrossing : eta ∈
        D.dualEmbedding.verticalCrossingEvent
          (r - B) (R + B) Ttop D0 := by
      apply D.dualEmbedding.verticalCrossingEvent_of_openWalk eta hBd
        hBpos.le (by linarith) exitWalk hxTop hzTop hexitX
    have hdisjoint := D.matchedCrossingEvents_disjoint
      (a := r - 5 * B) (b := R + 5 * B) (c := Ttop) (d := D0)
      hBpos hBp hBd (by linarith) (by linarith)
    have hdualMem : omega ∈ (dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) Ttop D0 := by
      change eta ∈ D.dualEmbedding.verticalCrossingEvent
        (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) Ttop D0
      convert hdualCrossing using 1 <;> ring_nf
    exact Set.disjoint_left.mp hdisjoint hTopCrossing hdualMem
  have hzRight : R < D.dualEmbedding.vertexCoord z 0 := by
    rcases hzSide with hzRight | hzBottom' | hzTop'
    · exact hzRight
    · exact (hzBottom hzBottom').elim
    · exact (hzTop hzTop').elim
  have hexitY : ∀ u ∈ exitWalk.support,
        C ≤ D.dualEmbedding.vertexCoord u 1 ∧
          D.dualEmbedding.vertexCoord u 1 ≤ D0 := by
      intro u hu
      dsimp only [exitWalk] at hu
      rw [SimpleGraph.Walk.support_append] at hu
      rcases List.mem_append.mp hu with huQ | huEdge
      · exact (hq u huQ).2.2.2
      · have huz : u = z := by simpa [edge] using huEdge
        subst u
        constructor
        · by_contra hnot
          have : D.dualEmbedding.vertexCoord z 1 < C := lt_of_not_ge hnot
          exact hzBottom this
        · by_contra hnot
          have : D0 < D.dualEmbedding.vertexCoord z 1 := lt_of_not_ge hnot
          exact hzTop this
  have hdualCrossing : eta ∈
      D.dualEmbedding.horizontalCrossingEvent A R C D0 :=
    D.dualEmbedding.horizontalCrossingEvent_of_openWalk eta hBd
      hBpos.le (by linarith) exitWalk hxRight hzRight hexitY
  have hdisjoint := D.matchedVerticalHorizontalCrossingEvents_disjoint
    (a := A) (b := R) (c := C - 4 * B) (d := D0 + 4 * B)
    hBpos hBp hBd (by linarith) (by linarith)
  have hdualMem : omega ∈ (dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent A R
        (C - 4 * B + 4 * B) (D0 + 4 * B - 4 * B) := by
    change eta ∈ D.dualEmbedding.horizontalCrossingEvent A R
      (C - 4 * B + 4 * B) (D0 + 4 * B - 4 * B)
    convert hdualCrossing using 1 <;> ring_nf
  exact Set.disjoint_left.mp hdisjoint hRightCrossing hdualMem

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
