/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.HurewiczCofibration
public import MathlibExt.Topology.Category.TopPair.NDR
import MathlibExt.Topology.Homotopy.CompactTimeFixed
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Standard NDR data and Hurewicz cylinder retractions

Only textbook NDR data is used here: control monotonicity plays no role.
The cylinder `X × I` is retracted onto `A × I ∪ X × {0}` by gluing three
closed-region formulas.  For control `u` and time `t`, the regions are

* `2t ≤ u`: move directly to the bottom;
* `u ≤ 2t` and `t ≤ u`: run the NDR deformation through the bounded ratio
  `(2t-u)/u`, then move to the bottom;
* `u ≤ t`: use the NDR endpoint and side time `t-u`.

The bounded ratio itself is not continuous at `u=0`.  Continuity of its
composite with the relative deformation follows from compact-time fixed-locus
continuity.  No separation, delta-generated, model-category, pushout, or
telescope assumption is used.

Conversely, closed cylinder-retraction data gives standard NDR data. Its control
is the norm of the path-height discrepancy on the compact interval. Closedness
identifies the zero locus, and positive endpoint height gives the neighborhood
endpoint law. This direction also supplies the actual global deformation.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Filter Topology
open scoped unitInterval

universe u v

namespace TopPair.StandardNDRData

variable {P : TopPair.{u}} (d : TopPair.StandardNDRData P)

private abbrev CylinderPoint := P.fst × TopCat.I.{u}

private def cylinderTime (p : CylinderPoint (P := P)) : unitInterval :=
  TopCat.I.homeomorph p.2

private def controlReal (p : CylinderPoint (P := P)) : ℝ :=
  d.control p.1

private def timeReal (p : CylinderPoint (P := P)) : ℝ :=
  cylinderTime p

private theorem continuous_controlReal : Continuous (controlReal d) := by
  exact continuous_subtype_val.comp (d.control.continuous.comp continuous_fst)

private theorem continuous_timeReal : Continuous (timeReal (P := P)) := by
  exact continuous_subtype_val.comp
    (TopCat.I.homeomorph.continuous.comp continuous_snd)

private def cylinderBottomRegion : Set (CylinderPoint (P := P)) :=
  {p | 2 * timeReal p ≤ controlReal d p}

private def cylinderMiddleRegion : Set (CylinderPoint (P := P)) :=
  {p | controlReal d p ≤ 2 * timeReal p ∧ timeReal p ≤ controlReal d p}

private def cylinderSideRegion : Set (CylinderPoint (P := P)) :=
  {p | controlReal d p ≤ timeReal p}

private theorem isClosed_cylinderBottomRegion :
    IsClosed (cylinderBottomRegion d) := by
  exact isClosed_le ((continuous_timeReal (P := P)).const_mul 2)
    (continuous_controlReal d)

private theorem isClosed_cylinderMiddleRegion :
    IsClosed (cylinderMiddleRegion d) := by
  exact (isClosed_le (continuous_controlReal d)
    ((continuous_timeReal (P := P)).const_mul 2)).inter
      (isClosed_le (continuous_timeReal (P := P)) (continuous_controlReal d))

private theorem isClosed_cylinderSideRegion :
    IsClosed (cylinderSideRegion d) := by
  exact isClosed_le (continuous_controlReal d) (continuous_timeReal (P := P))

private theorem cylinderRegions_cover :
    (cylinderBottomRegion d ∪ cylinderMiddleRegion d) ∪
      cylinderSideRegion d = Set.univ := by
  ext p
  constructor
  · intro
    trivial
  · intro
    by_cases hb : 2 * timeReal p ≤ controlReal d p
    · exact Or.inl (Or.inl hb)
    · by_cases hm : timeReal p ≤ controlReal d p
      · exact Or.inl (Or.inr ⟨le_of_not_ge hb, hm⟩)
      · exact Or.inr (le_of_not_ge hm)

private def middleNumerator (p : CylinderPoint (P := P)) : unitInterval :=
  Set.projIcc (0 : ℝ) 1 zero_le_one
    (2 * timeReal p - controlReal d p)

private theorem continuous_middleNumerator : Continuous (middleNumerator d) := by
  exact continuous_projIcc.comp
    (((continuous_timeReal (P := P)).const_mul 2).sub (continuous_controlReal d))

private def middleTime (p : CylinderPoint (P := P)) : unitInterval :=
  boundedRatio (middleNumerator d p) (d.control p.1)

private def sideTime (p : CylinderPoint (P := P)) : unitInterval :=
  Set.projIcc (0 : ℝ) 1 zero_le_one
    (timeReal p - controlReal d p)

private theorem continuous_sideTime : Continuous (sideTime d) := by
  exact continuous_projIcc.comp
    ((continuous_timeReal (P := P)).sub (continuous_controlReal d))

private theorem middleNumerator_eq_zero
    (p : CylinderPoint (P := P))
    (hb : p ∈ cylinderBottomRegion d)
    (hm : p ∈ cylinderMiddleRegion d) :
    middleNumerator d p = 0 := by
  change 2 * timeReal p ≤ controlReal d p at hb
  change controlReal d p ≤ 2 * timeReal p ∧ _ at hm
  have h : 2 * timeReal p - controlReal d p = 0 := by
    linarith [hb, hm.1]
  unfold middleNumerator
  rw [h]
  exact Set.projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩

private theorem middleNumerator_eq_control
    (p : CylinderPoint (P := P))
    (hm : p ∈ cylinderMiddleRegion d)
    (hs : p ∈ cylinderSideRegion d) :
    middleNumerator d p = d.control p.1 := by
  have hut : controlReal d p = timeReal p := le_antisymm hs hm.2
  have harg : 2 * timeReal p - controlReal d p = (d.control p.1 : ℝ) := by
    change 2 * timeReal p - controlReal d p = controlReal d p
    rw [hut]
    ring
  unfold middleNumerator
  rw [harg]
  exact Set.projIcc_of_mem zero_le_one (d.control p.1).property

private theorem sideTime_eq_zero
    (p : CylinderPoint (P := P))
    (h : controlReal d p = timeReal p) :
    sideTime d p = 0 := by
  have harg : timeReal p - controlReal d p = 0 := by rw [h, sub_self]
  unfold sideTime
  rw [harg]
  exact Set.projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩

private theorem sideTime_eq_cylinderTime_of_control_eq_zero
    (p : CylinderPoint (P := P)) (hu : d.control p.1 = 0) :
    sideTime d p = cylinderTime p := by
  apply Subtype.ext
  change Set.projIcc (0 : ℝ) 1 zero_le_one
      (timeReal p - controlReal d p) = (cylinderTime p : ℝ)
  have hu' : controlReal d p = 0 := congrArg Subtype.val hu
  rw [hu', sub_zero]
  exact congrArg Subtype.val
    (Set.projIcc_of_mem zero_le_one (cylinderTime p).property)

private def bottomPiece (p : CylinderPoint (P := P)) :
    (TopPair.hurewiczCylinderPair P).snd :=
  ⟨(p.1, 0), Set.mem_unionProd.mpr (Or.inr rfl)⟩

private def middlePiece (p : CylinderPoint (P := P)) :
    (TopPair.hurewiczCylinderPair P).snd :=
  ⟨(d.deformation (middleTime d p, p.1), 0),
    Set.mem_unionProd.mpr (Or.inr rfl)⟩

private def sidePiece (p : CylinderPoint (P := P))
    (hp : p ∈ cylinderSideRegion d) :
    (TopPair.hurewiczCylinderPair P).snd := by
  refine ⟨(d.deformation (1, p.1),
    TopCat.I.homeomorph.symm (sideTime d p)), ?_⟩
  by_cases hu : d.control p.1 < 1
  · apply Set.mem_unionProd.mpr
    apply Or.inl
    have h := d.endpoint_mem_range p.1 hu
    simpa only [d.deformation.apply_one] using h
  · apply Set.mem_unionProd.mpr
    apply Or.inr
    have hu' : controlReal d p = 1 := by
      exact le_antisymm (d.control p.1).property.2 (not_lt.mp hu)
    have ht' : timeReal p = 1 := by
      exact le_antisymm (cylinderTime p).property.2 (hu' ▸ hp)
    apply TopCat.I.ext
    simp only [TopCat.I.homeomorph.apply_symm_apply, TopCat.I.homeomorph_zero]
    have hside : sideTime d p = 0 := by
      apply sideTime_eq_zero d
      rw [hu', ht']
    rw [hside]

private def bottomPieceMap :
    C(CylinderPoint (P := P), (TopPair.hurewiczCylinderPair P).snd) where
  toFun := bottomPiece
  continuous_toFun := by
    exact (continuous_fst.prodMk
      (continuous_const : Continuous
        (fun _ : CylinderPoint (P := P) => (0 : TopCat.I.{u})))).subtype_mk _

private theorem continuous_middleFirst : Continuous
    (fun z : cylinderMiddleRegion d =>
      d.deformation (middleTime d z.1, z.1.1)) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hu : d.control z.1.1 = 0
  · apply d.deformation.continuousAt_comp_arbitrary_time_of_mem
    · exact (continuous_fst.comp continuous_subtype_val).continuousAt
    · exact (d.control_eq_zero_iff z.1.1).mp hu
  · have htime : ContinuousAt
        (fun w : cylinderMiddleRegion d => middleTime d w.1) z := by
      exact continuousAt_boundedRatio_of_ne_zero
        (fun w : cylinderMiddleRegion d => middleNumerator d w.1)
        (fun w : cylinderMiddleRegion d => d.control w.1.1) z
        ((continuous_middleNumerator d).comp continuous_subtype_val).continuousAt
        (d.control.continuous.comp
          (continuous_fst.comp continuous_subtype_val)).continuousAt hu
    exact d.deformation.continuous.continuousAt.comp
      (htime.prodMk (continuous_fst.comp continuous_subtype_val).continuousAt)

private def middlePieceMap :
    C(cylinderMiddleRegion d, (TopPair.hurewiczCylinderPair P).snd) where
  toFun z := middlePiece d z.1
  continuous_toFun := by
    exact ((continuous_middleFirst d).prodMk
      (continuous_const : Continuous
        (fun _ : cylinderMiddleRegion d => (0 : TopCat.I.{u})))).subtype_mk _

private def sidePieceMap :
    C(cylinderSideRegion d, (TopPair.hurewiczCylinderPair P).snd) where
  toFun z := sidePiece d z.1 z.2
  continuous_toFun := by
    have hfirst : Continuous (fun z : cylinderSideRegion d =>
        d.deformation (1, z.1.1)) := by
      fun_prop
    have hsecond : Continuous (fun z : cylinderSideRegion d =>
        TopCat.I.homeomorph.symm (sideTime d z.1)) := by
      exact TopCat.I.homeomorph.symm.continuous.comp
        ((continuous_sideTime d).comp continuous_subtype_val)
    exact (hfirst.prodMk hsecond).subtype_mk _

private theorem bottomPiece_eq_middlePiece
    (p : CylinderPoint (P := P))
    (hb : p ∈ cylinderBottomRegion d)
    (hm : p ∈ cylinderMiddleRegion d) :
    bottomPiece p = middlePiece d p := by
  have hnum := middleNumerator_eq_zero d p hb hm
  have htime : middleTime d p = 0 := by
    rw [middleTime, hnum, boundedRatio_zero_left]
  apply Subtype.ext
  apply Prod.ext
  · change p.1 = d.deformation (middleTime d p, p.1)
    rw [htime, d.deformation.apply_zero]
    rfl
  · rfl

private theorem middlePiece_eq_sidePiece
    (p : CylinderPoint (P := P))
    (hm : p ∈ cylinderMiddleRegion d)
    (hs : p ∈ cylinderSideRegion d) :
    middlePiece d p = sidePiece d p hs := by
  have hut : controlReal d p = timeReal p := le_antisymm hs hm.2
  have hside : sideTime d p = 0 := sideTime_eq_zero d p hut
  by_cases hu : d.control p.1 = 0
  · have hx : p.1 ∈ Set.range P.map := (d.control_eq_zero_iff p.1).mp hu
    have hnum : middleNumerator d p = 0 := by
      apply Subtype.ext
      have hut' : timeReal p = 0 := by
        rw [← hut]
        exact congrArg Subtype.val hu
      simp [middleNumerator, hut, hut']
    have hmiddle : middleTime d p = 0 := by
      rw [middleTime, hnum, boundedRatio_zero_left]
    apply Subtype.ext
    apply Prod.ext
    · change d.deformation (middleTime d p, p.1) = d.deformation (1, p.1)
      rw [hmiddle, d.deformation.apply_zero, d.deformation.eq_fst 1 hx]
    · apply TopCat.I.ext
      change TopCat.I.homeomorph (0 : TopCat.I.{u}) = sideTime d p
      rw [TopCat.I.homeomorph_zero, hside]
  · have hnum := middleNumerator_eq_control d p hm hs
    have hmiddle : middleTime d p = 1 := by
      rw [middleTime, hnum, boundedRatio_self_of_ne_zero _ hu]
    apply Subtype.ext
    apply Prod.ext
    · change d.deformation (middleTime d p, p.1) = d.deformation (1, p.1)
      rw [hmiddle]
    · apply TopCat.I.ext
      change TopCat.I.homeomorph (0 : TopCat.I.{u}) = sideTime d p
      rw [TopCat.I.homeomorph_zero, hside]

private theorem bottomPiece_eq_sidePiece
    (p : CylinderPoint (P := P))
    (hb : p ∈ cylinderBottomRegion d)
    (hs : p ∈ cylinderSideRegion d) :
    bottomPiece p = sidePiece d p hs := by
  change 2 * timeReal p ≤ controlReal d p at hb
  change controlReal d p ≤ timeReal p at hs
  have ht : timeReal p = 0 := by
    have ht0 : 0 ≤ timeReal p := (cylinderTime p).property.1
    linarith [hb, hs]
  have hu : d.control p.1 = 0 := by
    apply Subtype.ext
    have hu0 : controlReal d p = 0 := by
      have hu_nonneg : 0 ≤ controlReal d p := (d.control p.1).property.1
      linarith [hb, hs]
    exact hu0
  have hx : p.1 ∈ Set.range P.map := (d.control_eq_zero_iff p.1).mp hu
  have hside : sideTime d p = cylinderTime p :=
    sideTime_eq_cylinderTime_of_control_eq_zero d p hu
  apply Subtype.ext
  apply Prod.ext
  · change p.1 = d.deformation (1, p.1)
    exact (d.deformation.eq_fst 1 hx).symm
  · apply TopCat.I.ext
    change TopCat.I.homeomorph (0 : TopCat.I.{u}) = sideTime d p
    rw [TopCat.I.homeomorph_zero, hside]
    apply Subtype.ext
    exact ht.symm

private noncomputable def cylinderRetractionFn
    (p : CylinderPoint (P := P)) : (TopPair.hurewiczCylinderPair P).snd := by
  classical
  exact if hb : p ∈ cylinderBottomRegion d then bottomPiece p
    else if hm : p ∈ cylinderMiddleRegion d then middlePiece d p
    else sidePiece d p (by
      have hp : p ∈ (cylinderBottomRegion d ∪ cylinderMiddleRegion d) ∪
          cylinderSideRegion d := by
        rw [cylinderRegions_cover d]
        trivial
      rcases hp with (hb' | hm') | hs
      · exact (hb hb').elim
      · exact (hm hm').elim
      · exact hs)

private theorem cylinderRetractionFn_eq_bottom
    {p : CylinderPoint (P := P)} (hp : p ∈ cylinderBottomRegion d) :
    cylinderRetractionFn d p = bottomPiece p := by
  simp [cylinderRetractionFn, hp]

private theorem cylinderRetractionFn_eq_middle
    {p : CylinderPoint (P := P)} (hp : p ∈ cylinderMiddleRegion d) :
    cylinderRetractionFn d p = middlePiece d p := by
  by_cases hb : p ∈ cylinderBottomRegion d
  · rw [cylinderRetractionFn_eq_bottom d hb,
      bottomPiece_eq_middlePiece d p hb hp]
  · simp [cylinderRetractionFn, hb, hp]

private theorem cylinderRetractionFn_eq_side
    {p : CylinderPoint (P := P)} (hp : p ∈ cylinderSideRegion d) :
    cylinderRetractionFn d p = sidePiece d p hp := by
  by_cases hb : p ∈ cylinderBottomRegion d
  · rw [cylinderRetractionFn_eq_bottom d hb,
      bottomPiece_eq_sidePiece d p hb hp]
  · by_cases hm : p ∈ cylinderMiddleRegion d
    · rw [cylinderRetractionFn_eq_middle d hm,
        middlePiece_eq_sidePiece d p hm hp]
    · simp only [cylinderRetractionFn, hb, hm, dite_false]

private theorem continuousOn_cylinderRetractionFn_bottom :
    ContinuousOn (cylinderRetractionFn d) (cylinderBottomRegion d) := by
  apply (bottomPieceMap (P := P)).continuous.continuousOn.congr
  intro p hp
  exact cylinderRetractionFn_eq_bottom d hp

private theorem continuousOn_cylinderRetractionFn_middle :
    ContinuousOn (cylinderRetractionFn d) (cylinderMiddleRegion d) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply (middlePieceMap d).continuous.congr
  intro p
  exact (cylinderRetractionFn_eq_middle d p.2).symm

private theorem continuousOn_cylinderRetractionFn_side :
    ContinuousOn (cylinderRetractionFn d) (cylinderSideRegion d) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply (sidePieceMap d).continuous.congr
  intro p
  exact (cylinderRetractionFn_eq_side d p.2).symm

private theorem continuous_cylinderRetractionFn : Continuous (cylinderRetractionFn d) := by
  have hBM := (continuousOn_cylinderRetractionFn_bottom d).union_of_isClosed
    (continuousOn_cylinderRetractionFn_middle d)
    (isClosed_cylinderBottomRegion d) (isClosed_cylinderMiddleRegion d)
  have hAll := hBM.union_of_isClosed (continuousOn_cylinderRetractionFn_side d)
    ((isClosed_cylinderBottomRegion d).union (isClosed_cylinderMiddleRegion d))
    (isClosed_cylinderSideRegion d)
  rw [cylinderRegions_cover d] at hAll
  exact continuousOn_univ.mp hAll

/-- NDR data supplies closed Hurewicz cylinder-retraction data. -/
noncomputable opaque hurewiczCofibrationData (d : TopPair.StandardNDRData P) :
    TopPair.HurewiczCofibrationData P := by
  let r : (TopPair.hurewiczCylinderPair P).fst ⟶
      (TopPair.hurewiczCylinderPair P).snd :=
    TopCat.ofHom ⟨cylinderRetractionFn d, continuous_cylinderRetractionFn d⟩
  refine
    { isClosed_range := d.isClosed_range
      cylinderRetraction := r
      inclusion_comp_retraction := ?_ }
  apply TopCat.hom_ext
  ext z
  apply Subtype.ext
  rcases Set.mem_unionProd.mp z.2 with hz | hz
  · rcases hz with ⟨a, ha⟩
    have hu : d.control (P.map a) = 0 :=
      (d.control_eq_zero_iff (P.map a)).2 ⟨a, rfl⟩
    have hs : (P.map a, z.1.2) ∈ cylinderSideRegion d := by
      change (d.control (P.map a) : ℝ) ≤
        (TopCat.I.homeomorph z.1.2 : unitInterval)
      rw [hu]
      exact (TopCat.I.homeomorph z.1.2).property.1
    have h := cylinderRetractionFn_eq_side d hs
    have h' := congrArg Subtype.val h
    have hside : sideTime d (P.map a, z.1.2) =
        cylinderTime (P.map a, z.1.2) :=
      sideTime_eq_cylinderTime_of_control_eq_zero d (P.map a, z.1.2) hu
    change sideTime d (P.map a, z.1.2) = TopCat.I.homeomorph z.1.2 at hside
    have hfixed : d.deformation (1, P.map a) = P.map a :=
      d.deformation.eq_fst 1 ⟨a, rfl⟩
    have htop : TopCat.I.homeomorph.symm
        (sideTime d (P.map a, z.1.2)) = z.1.2 := by
      apply TopCat.I.ext
      simpa only [TopCat.I.homeomorph.apply_symm_apply] using hside
    change (cylinderRetractionFn d (P.map a, z.1.2)).1 =
      (d.deformation (1, P.map a),
        TopCat.I.homeomorph.symm (sideTime d (P.map a, z.1.2))) at h'
    rw [hfixed, htop] at h'
    change (cylinderRetractionFn d (z.1.1, z.1.2)).1 = z.1
    calc
      (cylinderRetractionFn d (z.1.1, z.1.2)).1 =
          (cylinderRetractionFn d (P.map a, z.1.2)).1 :=
        congrArg (fun x => (cylinderRetractionFn d (x, z.1.2)).1) ha.symm
      _ = z.1 := h'.trans (Prod.ext ha rfl)
  · have ht : z.1.2 = 0 := hz
    have hb : (z.1.1, (0 : TopCat.I.{u})) ∈ cylinderBottomRegion d := by
      change 2 * (0 : ℝ) ≤ (d.control z.1.1 : ℝ)
      simpa using (d.control z.1.1).property.1
    have h := cylinderRetractionFn_eq_bottom d hb
    have h' := congrArg Subtype.val h
    change (cylinderRetractionFn d (z.1.1, 0)).1 = (z.1.1, 0) at h'
    change (cylinderRetractionFn d (z.1.1, z.1.2)).1 = z.1
    exact (congrArg (fun t => (cylinderRetractionFn d (z.1.1, t)).1) ht).trans
      (h'.trans (Prod.ext rfl ht.symm))

/-- The explicit NDR cylinder retraction. -/
noncomputable def cylinderRetraction (d : TopPair.StandardNDRData P) :
    (TopPair.hurewiczCylinderPair P).fst ⟶
      (TopPair.hurewiczCylinderPair P).snd :=
  d.hurewiczCofibrationData.cylinderRetraction

/-- The NDR cylinder retraction fixes the bottom. -/
@[simp]
theorem cylinderRetraction_bottom (d : TopPair.StandardNDRData P) (x : P.fst) :
    d.cylinderRetraction (x, (0 : TopCat.I.{u})) =
      TopPair.hurewiczCylinderBottomPoint P x := by
  change d.hurewiczCofibrationData.cylinderRetraction
    ((TopPair.hurewiczCylinderPair P).map
      (TopPair.hurewiczCylinderBottomPoint P x)) = _
  exact d.hurewiczCofibrationData.cylinderRetraction_boundary _

/-- The NDR cylinder retraction fixes the side. -/
@[simp]
theorem cylinderRetraction_side (d : TopPair.StandardNDRData P)
    (a : P.snd) (t : TopCat.I.{u}) :
    d.cylinderRetraction (P.map a, t) =
      TopPair.hurewiczCylinderSidePoint P t a := by
  change d.hurewiczCofibrationData.cylinderRetraction
    ((TopPair.hurewiczCylinderPair P).map
      (TopPair.hurewiczCylinderSidePoint P t a)) = _
  exact d.hurewiczCofibrationData.cylinderRetraction_boundary _

/-- NDR data gives explicit cross-universe homotopy-extension data. -/
noncomputable def homotopyExtension
    (d : TopPair.StandardNDRData P)
    {Y : Type v} [TopologicalSpace Y]
    (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
    (h0 : ∀ a, H (0, a) = f (P.map a)) :
    Topology.HomotopyExtensionData P.map.hom f H h0 :=
  d.hurewiczCofibrationData.homotopyExtension f H h0

/-- Every standard NDR pair inclusion is a Hurewicz cofibration. -/
theorem isHurewiczCofibration (d : TopPair.StandardNDRData P) :
    TopCat.IsHurewiczCofibration P.map :=
  TopPair.HurewiczCofibrationData.isHurewiczCofibration
    d.hurewiczCofibrationData

end TopPair.StandardNDRData

namespace TopPair.HurewiczCofibrationData

variable {P : TopPair.{u}} (d : TopPair.HurewiczCofibrationData P)

private def cylinderImage : C(P.fst × unitInterval, (TopPair.hurewiczCylinderPair P).snd) where
  toFun z := d.cylinderRetraction (z.1, TopCat.I.homeomorph.{u}.symm z.2)
  continuous_toFun := d.cylinderRetraction.hom.continuous.comp
    (continuous_fst.prodMk (TopCat.I.homeomorph.{u}.symm.continuous.comp continuous_snd))

private theorem cylinderImage_zero (x : P.fst) :
    cylinderImage d (x, 0) = TopPair.hurewiczCylinderBottomPoint P x := by
  have hz : TopCat.I.homeomorph.{u}.symm 0 = (0 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.{u}.injective
    simp
  change d.cylinderRetraction (x, TopCat.I.homeomorph.{u}.symm 0) = _
  rw [hz]
  exact d.cylinderRetraction_boundary (TopPair.hurewiczCylinderBottomPoint P x)

private theorem cylinderImage_range (a : P.snd) (t : unitInterval) :
    cylinderImage d (P.map a, t) =
      TopPair.hurewiczCylinderSidePoint P (TopCat.I.homeomorph.{u}.symm t) a := by
  change d.cylinderRetraction (P.map a, TopCat.I.homeomorph.{u}.symm t) = _
  exact d.cylinderRetraction_boundary
    (TopPair.hurewiczCylinderSidePoint P (TopCat.I.homeomorph.{u}.symm t) a)

private def heightDifference : C(P.fst × unitInterval, ℝ) where
  toFun z := (z.2 : ℝ) -
    (TopCat.I.homeomorph.{u} (cylinderImage d z).1.2 : ℝ)
  continuous_toFun := by fun_prop

private theorem heightDifference_norm_le_one (x : P.fst) :
    ‖(heightDifference d).curry x‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro t
  change ‖(t : ℝ) -
    (TopCat.I.homeomorph.{u} (cylinderImage d (x, t)).1.2 : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  rcases t.2 with ⟨ht0, ht1⟩
  rcases (TopCat.I.homeomorph.{u} (cylinderImage d (x, t)).1.2).2 with ⟨hr0, hr1⟩
  constructor <;> linarith

private def heightControl : C(P.fst, unitInterval) where
  toFun x := ⟨‖(heightDifference d).curry x‖, norm_nonneg _, heightDifference_norm_le_one d x⟩
  continuous_toFun := (continuous_norm.comp (heightDifference d).curry.continuous).subtype_mk _

private def cylinderDeformation : C(unitInterval × P.fst, P.fst) where
  toFun z := (cylinderImage d (z.2, z.1)).1.1
  continuous_toFun := by fun_prop

private theorem heightControl_eq_zero_iff (x : P.fst) :
    heightControl d x = 0 ↔ x ∈ Set.range P.map := by
  constructor
  · intro hzero
    have hn : ‖(heightDifference d).curry x‖ = 0 := congrArg Subtype.val hzero
    have hf : (heightDifference d).curry x = 0 := norm_eq_zero.mp hn
    have hheight (t : unitInterval) :
        TopCat.I.homeomorph.{u} (cylinderImage d (x, t)).1.2 = t := by
      apply Subtype.ext
      have ht := DFunLike.congr_fun hf t
      change (t : ℝ) -
        (TopCat.I.homeomorph.{u} (cylinderImage d (x, t)).1.2 : ℝ) = 0 at ht
      linarith
    let g : C(unitInterval, P.fst) :=
      (cylinderDeformation d).comp
        { toFun := fun t => (t, x), continuous_toFun := by fun_prop }
    have hclosed : IsClosed (g ⁻¹' Set.range P.map) :=
      d.isClosed_range.preimage g.continuous
    have hpos : Set.Ioi (0 : unitInterval) ⊆ g ⁻¹' Set.range P.map := by
      intro t ht
      rcases Set.mem_unionProd.mp (cylinderImage d (x, t)).2 with hr | hr
      · exact hr
      · exfalso
        have heq := hheight t
        rw [hr, TopCat.I.homeomorph_zero.{u}] at heq
        change (0 : ℝ) < (t : ℝ) at ht
        exact (ne_of_gt ht) (congrArg Subtype.val heq.symm)
    have h0 : (0 : unitInterval) ∈ closure (Set.Ioi (0 : unitInterval)) := by
      rw [closure_Ioi' ⟨1, zero_lt_one⟩]
      exact Set.self_mem_Ici
    have hmem := closure_minimal hpos hclosed h0
    change (cylinderImage d (x, 0)).1.1 ∈ Set.range P.map at hmem
    rw [cylinderImage_zero] at hmem
    exact hmem
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    change ‖(heightDifference d).curry (P.map a)‖ = 0
    rw [norm_eq_zero]
    ext t
    change (t : ℝ) -
      (TopCat.I.homeomorph.{u} (cylinderImage d (P.map a, t)).1.2 : ℝ) = 0
    rw [cylinderImage_range]
    change (t : ℝ) - (TopCat.I.homeomorph.{u} (TopCat.I.homeomorph.{u}.symm t) : ℝ) = 0
    rw [Homeomorph.apply_symm_apply, sub_self]

private def endpoint : C(P.fst, P.fst) :=
  (cylinderDeformation d).comp
    { toFun := fun x => (1, x), continuous_toFun := by fun_prop }

private def deformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id P.fst) (endpoint d) (Set.range P.map) where
  toFun := cylinderDeformation d
  continuous_toFun := (cylinderDeformation d).continuous
  map_zero_left x := by
    change (cylinderImage d (x, 0)).1.1 = x
    rw [cylinderImage_zero]
    rfl
  map_one_left x := rfl
  prop' t x hx := by
    rcases hx with ⟨a, rfl⟩
    change (cylinderImage d (P.map a, t)).1.1 = P.map a
    rw [cylinderImage_range]
    rfl

private theorem endpoint_mem_range (x : P.fst) (hx : heightControl d x < 1) :
    endpoint d x ∈ Set.range P.map := by
  rcases Set.mem_unionProd.mp (cylinderImage d (x, 1)).2 with hr | hr
  · exact hr
  · have hb := ((heightDifference d).curry x).apply_le_norm 1
    change 1 -
      (TopCat.I.homeomorph.{u} (cylinderImage d (x, 1)).1.2 : ℝ) ≤
        ‖(heightDifference d).curry x‖ at hb
    rw [hr, TopCat.I.homeomorph_zero.{u}] at hb
    change ‖(heightDifference d).curry x‖ < 1 at hx
    norm_num at hb
    linarith

/-- Closed cylinder-retraction data gives standard NDR control and its actual deformation. -/
noncomputable opaque toStandardNDRData : TopPair.StandardNDRData P := by
  exact
    { control := heightControl d
      endpoint := endpoint d
      deformation := deformation d
      control_eq_zero_iff := heightControl_eq_zero_iff d
      endpoint_mem_range := endpoint_mem_range d }

end TopPair.HurewiczCofibrationData

end
