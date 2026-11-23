/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.NDR
public import MathlibExt.Topology.Category.TopPair.Product
import MathlibExt.Topology.Category.TopPair.ProductExcisive
import MathlibExt.Topology.Homotopy.CompactTimeFixed
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Algebra.Algebra

/-!
# Pushout products of controlled NDR pairs

Two controlled NDR pairs determine controlled NDR data on their product
pair, whose subspace is `A × Y ∪ X × B`.  The control is the product of
the two controls.  The deformation is glued across the closed regions
`u ≤ v` and `v ≤ u`, running the smaller-control factor at full speed and
the other at the corresponding bounded boundedRatio.

Continuity at the double-zero corner uses the compact-time fixed-locus
theorem.  This file makes no quotient, smash-product, or cup-product claim.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace TopPair.NDRData

variable {P Q : TopPair.{u}} (d : TopPair.NDRData P) (e : TopPair.NDRData Q)

local instance : ContinuousMul unitInterval :=
  Topology.IsInducing.subtypeVal.continuousMul Set.Icc.coeMonoidWithZeroHom

private def controlLeft (p : unitInterval × (P.fst × Q.fst)) : unitInterval :=
  d.control p.2.1

private def controlRight (p : unitInterval × (P.fst × Q.fst)) : unitInterval :=
  e.control p.2.2

private theorem continuous_controlLeft : Continuous (controlLeft (Q := Q) d) := by
  unfold controlLeft
  exact d.control.continuous.comp continuous_snd.fst

private theorem continuous_controlRight : Continuous (controlRight (P := P) e) := by
  unfold controlRight
  exact e.control.continuous.comp continuous_snd.snd

private def leftRegion : Set (unitInterval × (P.fst × Q.fst)) :=
  {p | controlLeft (Q := Q) d p ≤ controlRight (P := P) e p}

private def rightRegion : Set (unitInterval × (P.fst × Q.fst)) :=
  {p | controlRight (P := P) e p ≤ controlLeft (Q := Q) d p}

private theorem isClosed_leftRegion : IsClosed (leftRegion d e) :=
  isClosed_le (continuous_controlLeft (Q := Q) d)
    (continuous_controlRight (P := P) e)

private theorem isClosed_rightRegion : IsClosed (rightRegion d e) :=
  isClosed_le (continuous_controlRight (P := P) e)
    (continuous_controlLeft (Q := Q) d)

private def leftPiece
    (p : unitInterval × (P.fst × Q.fst)) : P.fst × Q.fst :=
  (d.deformation (p.1, p.2.1),
    e.deformation
      (p.1 * boundedRatio (d.control p.2.1) (e.control p.2.2), p.2.2))

private def rightPiece
    (p : unitInterval × (P.fst × Q.fst)) : P.fst × Q.fst :=
  (d.deformation
      (p.1 * boundedRatio (e.control p.2.2) (d.control p.2.1), p.2.1),
    e.deformation (p.1, p.2.2))

private theorem continuousOn_leftPiece :
    ContinuousOn (leftPiece d e) (leftRegion d e) := by
  intro p hp
  have hfirst : ContinuousAt
      (fun z : unitInterval × (P.fst × Q.fst) =>
        d.deformation (z.1, z.2.1)) p := by
    fun_prop
  by_cases hv : e.control p.2.2 = 0
  · have hy : p.2.2 ∈ Set.range Q.map :=
      (e.control_eq_zero_iff p.2.2).mp hv
    have hsecond : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          e.deformation
            (z.1 * boundedRatio (d.control z.2.1) (e.control z.2.2), z.2.2)) p := by
      apply e.deformation.continuousAt_comp_arbitrary_time_of_mem
      · exact (continuous_snd.snd).continuousAt
      · exact hy
    exact (hfirst.prodMk hsecond).continuousWithinAt
  · have hratio : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          boundedRatio (d.control z.2.1) (e.control z.2.2)) p :=
      continuousAt_boundedRatio_of_ne_zero
        (fun z => d.control z.2.1) (fun z => e.control z.2.2) p
        (by fun_prop) (by fun_prop) hv
    have htime : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          z.1 * boundedRatio (d.control z.2.1) (e.control z.2.2)) p :=
      continuousAt_fst.mul hratio
    have hsecond : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          e.deformation
            (z.1 * boundedRatio (d.control z.2.1) (e.control z.2.2), z.2.2)) p := by
      exact e.deformation.continuous.continuousAt.comp
        (htime.prodMk (continuous_snd.snd).continuousAt)
    exact (hfirst.prodMk hsecond).continuousWithinAt

private theorem continuousOn_rightPiece :
    ContinuousOn (rightPiece d e) (rightRegion d e) := by
  intro p hp
  have hsecond : ContinuousAt
      (fun z : unitInterval × (P.fst × Q.fst) =>
        e.deformation (z.1, z.2.2)) p := by
    fun_prop
  by_cases hu : d.control p.2.1 = 0
  · have hx : p.2.1 ∈ Set.range P.map :=
      (d.control_eq_zero_iff p.2.1).mp hu
    have hfirst : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          d.deformation
            (z.1 * boundedRatio (e.control z.2.2) (d.control z.2.1), z.2.1)) p := by
      apply d.deformation.continuousAt_comp_arbitrary_time_of_mem
      · exact (continuous_snd.fst).continuousAt
      · exact hx
    exact (hfirst.prodMk hsecond).continuousWithinAt
  · have hratio : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          boundedRatio (e.control z.2.2) (d.control z.2.1)) p :=
      continuousAt_boundedRatio_of_ne_zero
        (fun z => e.control z.2.2) (fun z => d.control z.2.1) p
        (by fun_prop) (by fun_prop) hu
    have htime : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          z.1 * boundedRatio (e.control z.2.2) (d.control z.2.1)) p :=
      continuousAt_fst.mul hratio
    have hfirst : ContinuousAt
        (fun z : unitInterval × (P.fst × Q.fst) =>
          d.deformation
            (z.1 * boundedRatio (e.control z.2.2) (d.control z.2.1), z.2.1)) p := by
      exact d.deformation.continuous.continuousAt.comp
        (htime.prodMk (continuous_snd.fst).continuousAt)
    exact (hfirst.prodMk hsecond).continuousWithinAt

private theorem leftPiece_eq_rightPiece_of_eq
    (p : unitInterval × (P.fst × Q.fst))
    (h : d.control p.2.1 = e.control p.2.2) :
    leftPiece d e p = rightPiece d e p := by
  by_cases hu : d.control p.2.1 = 0
  · have hv : e.control p.2.2 = 0 := h.symm.trans hu
    have hx : p.2.1 ∈ Set.range P.map :=
      (d.control_eq_zero_iff p.2.1).mp hu
    have hy : p.2.2 ∈ Set.range Q.map :=
      (e.control_eq_zero_iff p.2.2).mp hv
    apply Prod.ext
    · change d.deformation (p.1, p.2.1) =
        d.deformation
          (p.1 * boundedRatio (e.control p.2.2) (d.control p.2.1), p.2.1)
      rw [hu, hv, boundedRatio_zero_right, mul_zero, d.deformation.apply_zero]
      exact d.deformation.eq_fst p.1 hx
    · change e.deformation
          (p.1 * boundedRatio (d.control p.2.1) (e.control p.2.2), p.2.2) =
        e.deformation (p.1, p.2.2)
      rw [hu, hv, boundedRatio_zero_right, mul_zero, e.deformation.apply_zero]
      exact (e.deformation.eq_fst p.1 hy).symm
  · have hv : e.control p.2.2 ≠ 0 := by
      rw [← h]
      exact hu
    unfold leftPiece rightPiece
    rw [h] at hu ⊢
    apply Prod.ext <;>
      simp [hu, boundedRatio_self_of_ne_zero]

/-- The glued pushout-product deformation. -/
private noncomputable def productDeformation
    (p : unitInterval × (P.fst × Q.fst)) : P.fst × Q.fst :=
  by
    classical
    exact Set.piecewise (leftRegion d e) (leftPiece d e) (rightPiece d e) p

private theorem productDeformation_of_le
    (p : unitInterval × (P.fst × Q.fst))
    (h : d.control p.2.1 ≤ e.control p.2.2) :
    productDeformation d e p = leftPiece d e p := by
  classical
  unfold productDeformation
  apply Set.piecewise_eq_of_mem
  exact h

private theorem productDeformation_of_not_le
    (p : unitInterval × (P.fst × Q.fst))
    (h : ¬ d.control p.2.1 ≤ e.control p.2.2) :
    productDeformation d e p = rightPiece d e p := by
  classical
  unfold productDeformation
  apply Set.piecewise_eq_of_notMem
  exact h

private theorem continuous_productDeformation : Continuous (productDeformation d e) := by
  classical
  apply continuous_piecewise
  · intro p hp
    apply leftPiece_eq_rightPiece_of_eq d e p
    exact frontier_le_subset_eq
      (continuous_controlLeft (Q := Q) d)
      (continuous_controlRight (P := P) e) hp
  · simpa only [(isClosed_leftRegion d e).closure_eq] using
      continuousOn_leftPiece d e
  · apply (continuousOn_rightPiece d e).mono
    have hclosure : closure (leftRegion d e)ᶜ ⊆ rightRegion d e := by
      simpa only [leftRegion, rightRegion, Set.compl_ofPred, not_le] using
        (closure_lt_subset_le
          (continuous_controlRight (P := P) e)
          (continuous_controlLeft (Q := Q) d))
    exact hclosure

/-- Endpoint of the glued pushout-product deformation. -/
private noncomputable def productEndpoint : C(P.fst × Q.fst, P.fst × Q.fst) :=
  ⟨fun p => productDeformation d e (1, p),
    (continuous_productDeformation d e).comp
      (continuous_const.prodMk continuous_id)⟩

/-- The glued deformation as a homotopy relative to the product-pair
subspace. -/
private noncomputable def productHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id (P.fst × Q.fst))
      (productEndpoint d e) (Set.range (TopPair.prodObj P Q).map) where
  toFun := productDeformation d e
  continuous_toFun := continuous_productDeformation d e
  map_zero_left p := by
    by_cases h : d.control p.1 ≤ e.control p.2
    · rw [productDeformation_of_le d e (0, p) h]
      simp [leftPiece]
    · rw [productDeformation_of_not_le d e (0, p) h]
      simp [rightPiece]
  map_one_left p := rfl
  prop' t p hp := by
    change productDeformation d e (t, p) = p
    have hp' : p ∈ (Set.range P.map).unionProd (Set.range Q.map) := by
      simpa only [TopPair.range_prodObj_map P Q] using hp
    rcases (Set.mem_unionProd.mp hp') with hx | hy
    · have hu : d.control p.1 = 0 :=
        (d.control_eq_zero_iff p.1).mpr hx
      have hle : d.control p.1 ≤ e.control p.2 := by
        rw [hu]
        exact (e.control p.2).property.1
      rw [productDeformation_of_le d e (t, p) hle]
      apply Prod.ext
      · exact d.deformation.eq_fst t hx
      · simp [leftPiece, hu]
    · have hv : e.control p.2 = 0 :=
        (e.control_eq_zero_iff p.2).mpr hy
      by_cases hle : d.control p.1 ≤ e.control p.2
      · have hu : d.control p.1 = 0 :=
          le_antisymm (hv ▸ hle) (d.control p.1).property.1
        have hx : p.1 ∈ Set.range P.map :=
          (d.control_eq_zero_iff p.1).mp hu
        rw [productDeformation_of_le d e (t, p) hle]
        apply Prod.ext
        · exact d.deformation.eq_fst t hx
        · simp [leftPiece, hu]
      · rw [productDeformation_of_not_le d e (t, p) hle]
        apply Prod.ext
        · simp [rightPiece, hv]
        · exact e.deformation.eq_fst t hy

/-- Product of the two controls. -/
private noncomputable def productControl : C(P.fst × Q.fst, unitInterval) :=
  ⟨fun p => d.control p.1 * e.control p.2,
    (d.control.continuous.comp continuous_fst).mul
      (e.control.continuous.comp continuous_snd)⟩

/-- Product NDR data exists with the expected control and deformation
faces. -/
theorem exists_prod :
    ∃ c : TopPair.NDRData (TopPair.prodObj P Q),
      (∀ p, c.control p = d.control p.1 * e.control p.2) ∧
      (∀ t p, d.control p.1 ≤ e.control p.2 →
        c.deformation (t, p) =
          (d.deformation (t, p.1),
            e.deformation
              (t * boundedRatio (d.control p.1) (e.control p.2), p.2))) ∧
      (∀ t p, ¬ d.control p.1 ≤ e.control p.2 →
        c.deformation (t, p) =
          (d.deformation
              (t * boundedRatio (e.control p.2) (d.control p.1), p.1),
            e.deformation (t, p.2))) := by
  refine ⟨?w, ?_, ?_, ?_⟩
  · refine
      { control := productControl d e,
        endpoint := productEndpoint d e,
        deformation := productHomotopyRel d e,
        control_eq_zero_iff := ?_,
        control_deformation_le := ?_,
        endpoint_mem_range := ?_ }
    · intro p
      rw [TopPair.range_prodObj_map P Q, Set.mem_unionProd]
      change d.control p.1 * e.control p.2 = 0 ↔ _
      rw [mul_eq_zero, d.control_eq_zero_iff, e.control_eq_zero_iff]
    · intro t p
      with_unfolding_all
        change productControl d e (productDeformation d e (t, p)) ≤
          productControl d e p
      by_cases hle : d.control p.1 ≤ e.control p.2
      · rw [productDeformation_of_le d e (t, p) hle]
        change d.control (d.deformation (t, p.1)) *
            e.control (e.deformation
              (t * boundedRatio (d.control p.1) (e.control p.2), p.2)) ≤
          d.control p.1 * e.control p.2
        exact mul_le_mul (d.control_deformation_le t p.1)
          (e.control_deformation_le
            (t * boundedRatio (d.control p.1) (e.control p.2)) p.2)
          (e.control (e.deformation
            (t * boundedRatio (d.control p.1) (e.control p.2), p.2))).property.1
          (d.control p.1).property.1
      · rw [productDeformation_of_not_le d e (t, p) hle]
        change d.control (d.deformation
              (t * boundedRatio (e.control p.2) (d.control p.1), p.1)) *
            e.control (e.deformation (t, p.2)) ≤
          d.control p.1 * e.control p.2
        exact mul_le_mul
          (d.control_deformation_le
            (t * boundedRatio (e.control p.2) (d.control p.1)) p.1)
          (e.control_deformation_le t p.2)
          (e.control (e.deformation (t, p.2))).property.1
          (d.control p.1).property.1
    · intro p hp
      rw [TopPair.range_prodObj_map P Q, Set.mem_unionProd]
      change (productDeformation d e (1, p)).1 ∈ Set.range P.map ∨
        (productDeformation d e (1, p)).2 ∈ Set.range Q.map
      by_cases hle : d.control p.1 ≤ e.control p.2
      · rw [productDeformation_of_le d e (1, p) hle]
        left
        change d.deformation (1, p.1) ∈ Set.range P.map
        rw [d.deformation.apply_one]
        apply d.endpoint_mem_range p.1
        by_contra hu
        have hu1 : d.control p.1 = 1 :=
          le_antisymm (d.control p.1).property.2 (not_lt.mp hu)
        have hv1 : e.control p.2 = 1 := by
          exact le_antisymm unitInterval.le_one'
            (by simpa only [hu1] using hle)
        change d.control p.1 * e.control p.2 < 1 at hp
        rw [hu1, hv1, one_mul] at hp
        exact (lt_irrefl (1 : unitInterval)) hp
      · rw [productDeformation_of_not_le d e (1, p) hle]
        right
        change e.deformation (1, p.2) ∈ Set.range Q.map
        rw [e.deformation.apply_one]
        apply e.endpoint_mem_range p.2
        exact lt_of_lt_of_le (lt_of_not_ge hle) (d.control p.1).property.2
  · intro p
    rfl
  · intro t p h
    exact productDeformation_of_le d e (t, p) h
  · intro t p h
    exact productDeformation_of_not_le d e (t, p) h

/-- Controlled NDR data on the product pair. -/
noncomputable def prod : TopPair.NDRData (TopPair.prodObj P Q) :=
  Classical.choose (exists_prod d e)

@[simp]
theorem prod_control_apply (p : P.fst × Q.fst) :
    (d.prod e).control p = d.control p.1 * e.control p.2 :=
  (Classical.choose_spec (exists_prod d e)).1 p

/-- The product deformation on the left region runs the left factor at full
speed. -/
theorem prod_deformation_of_le (t : unitInterval) (p : P.fst × Q.fst)
    (h : d.control p.1 ≤ e.control p.2) :
    (d.prod e).deformation (t, p) =
      (d.deformation (t, p.1),
        e.deformation
          (t * boundedRatio (d.control p.1) (e.control p.2), p.2)) :=
  (Classical.choose_spec (exists_prod d e)).2.1 t p h

/-- The product deformation on the right region runs the right factor at
full speed. -/
theorem prod_deformation_of_not_le (t : unitInterval) (p : P.fst × Q.fst)
    (h : ¬ d.control p.1 ≤ e.control p.2) :
    (d.prod e).deformation (t, p) =
      (d.deformation
          (t * boundedRatio (e.control p.2) (d.control p.1), p.1),
        e.deformation (t, p.2)) :=
  (Classical.choose_spec (exists_prod d e)).2.2 t p h

/-- The controlled product neighborhood is exactly the union of the two
open factor neighborhoods. -/
theorem prod_neighborhood :
    (d.prod e).neighborhood = d.neighborhood.unionProd e.neighborhood := by
  ext p
  rw [NDRData.mem_neighborhood, prod_control_apply, Set.mem_unionProd,
    NDRData.mem_neighborhood, NDRData.mem_neighborhood]
  constructor
  · intro h
    by_cases hu : d.control p.1 < 1
    · exact Or.inl hu
    · right
      by_contra hv
      have hu1 : d.control p.1 = 1 :=
        le_antisymm unitInterval.le_one' (not_lt.mp hu)
      have hv1 : e.control p.2 = 1 :=
        le_antisymm unitInterval.le_one' (not_lt.mp hv)
      rw [hu1, hv1, one_mul] at h
      exact (lt_irrefl (1 : unitInterval)) h
  · rintro (hu | hv)
    · calc
        d.control p.1 * e.control p.2 ≤ d.control p.1 * 1 :=
          mul_le_mul_of_nonneg_left unitInterval.le_one'
            unitInterval.nonneg'
        _ = d.control p.1 := mul_one _
        _ < 1 := hu
    · calc
        d.control p.1 * e.control p.2 ≤ 1 * e.control p.2 :=
          mul_le_mul_of_nonneg_right unitInterval.le_one'
            unitInterval.nonneg'
        _ = e.control p.2 := one_mul _
        _ < 1 := hv

/-- The two canonical open neighborhood pairs satisfy product-union
excision. -/
theorem neighborhoodPair_isProductUnionExcisive :
    TopPair.IsProductUnionExcisive
      (TopPair.ofSubset d.neighborhood)
      (TopPair.ofSubset e.neighborhood) := by
  apply TopPair.isProductUnionExcisive_of_isOpen_ranges
  · have hRange : Set.range (TopPair.ofSubset d.neighborhood).map =
        d.neighborhood := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hRange]
    exact d.isOpen_neighborhood
  · have hRange : Set.range (TopPair.ofSubset e.neighborhood).map =
        e.neighborhood := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hRange]
    exact e.isOpen_neighborhood

/-- Product NDR data gives chosen good-pair data when both factor
subspaces are nonempty. -/
noncomputable def prodGoodPairData [Nonempty P.snd] [Nonempty Q.snd] :
    TopPair.GoodPairData (TopPair.prodObj P Q) := by
  let a : P.snd := Classical.choice (inferInstance : Nonempty P.snd)
  let b : Q.snd := Classical.choice (inferInstance : Nonempty Q.snd)
  let _ : Nonempty (TopPair.prodObj P Q).snd :=
    ⟨⟨(P.map a, Q.map b),
      Set.mem_unionProd.mpr (Or.inl ⟨a, rfl⟩)⟩⟩
  exact (d.prod e).toGoodPairData

@[simp]
theorem prodGoodPairData_neighborhood
    [Nonempty P.snd] [Nonempty Q.snd] :
    (d.prodGoodPairData e).neighborhood =
      d.neighborhood.unionProd e.neighborhood := by
  rw [prodGoodPairData, NDRData.toGoodPairData_neighborhood,
    prod_neighborhood]

end TopPair.NDRData

end
