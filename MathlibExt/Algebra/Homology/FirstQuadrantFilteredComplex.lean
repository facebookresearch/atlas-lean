/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFiltration

/-!
# Filtered complexes of first-quadrant totals

The degreewise horizontal filtration of a first-quadrant total is stable
under the total differential.  This file defines the filtered differential,
proves its compatibility with the split-monomorphic inclusion into the total,
and packages every stage as a chain complex.

Maps between stages and spectral-object packaging remain separate gates.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

omit [HasZeroObject C] in
@[reassoc]
theorem ιTotal_horizontalProjection
    (k n p q : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.down ℕ) p q n h ≫
        totalToHorizontalFilteredTotal K k n ≫
        horizontalFilteredTotalToTotal K k n =
      if _hp : p ≤ k then
        K.ιTotal (ComplexShape.down ℕ) p q n h
      else 0 := by
  rw [← Category.assoc,
    ιTotal_totalToHorizontalFilteredTotal]
  split_ifs with hp
  · exact horizontalFilteredTotalι_toTotal K k n ⟨⟨(p, q), h⟩, hp⟩
  · exact zero_comp

omit [HasZeroObject C] in
theorem d₁_succ_horizontalProjection
    (k m p q : ℕ) (htotal : (p + 1) + q = m + 1)
    (hp : p + 1 ≤ k) :
    K.d₁ (ComplexShape.down ℕ) (p + 1) q m ≫
        totalToHorizontalFilteredTotal K k m ≫
        horizontalFilteredTotalToTotal K k m =
      K.d₁ (ComplexShape.down ℕ) (p + 1) q m := by
  have hpq : p + q = m := by omega
  have hp' : p ≤ k := by omega
  rw [K.d₁_eq (ComplexShape.down ℕ)
    (ComplexShape.down_mk (p + 1) p rfl) q m hpq]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ιTotal_horizontalProjection, dite_eq_left hp']

omit [HasZeroObject C] in
theorem d₂_succ_horizontalProjection
    (k m p q : ℕ) (htotal : p + (q + 1) = m + 1)
    (hp : p ≤ k) :
    K.d₂ (ComplexShape.down ℕ) p (q + 1) m ≫
        totalToHorizontalFilteredTotal K k m ≫
        horizontalFilteredTotalToTotal K k m =
      K.d₂ (ComplexShape.down ℕ) p (q + 1) m := by
  have hpq : p + q = m := by omega
  rw [K.d₂_eq (ComplexShape.down ℕ) p
    (ComplexShape.down_mk (q + 1) q rfl) m hpq]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ιTotal_horizontalProjection, dite_eq_left hp]

omit [HasZeroObject C] in
theorem d₁_horizontalProjection
    (k m p q : ℕ) (htotal : p + q = m + 1)
    (hp : p ≤ k) :
    K.d₁ (ComplexShape.down ℕ) p q m ≫
        totalToHorizontalFilteredTotal K k m ≫
        horizontalFilteredTotalToTotal K k m =
      K.d₁ (ComplexShape.down ℕ) p q m := by
  cases p with
  | zero =>
      rw [K.d₁_eq_zero (ComplexShape.down ℕ) 0 q m (by simp)]
      simp
  | succ p =>
      exact d₁_succ_horizontalProjection K k m p q (by omega) hp

omit [HasZeroObject C] in
theorem d₂_horizontalProjection
    (k m p q : ℕ) (htotal : p + q = m + 1)
    (hp : p ≤ k) :
    K.d₂ (ComplexShape.down ℕ) p q m ≫
        totalToHorizontalFilteredTotal K k m ≫
        horizontalFilteredTotalToTotal K k m =
      K.d₂ (ComplexShape.down ℕ) p q m := by
  cases q with
  | zero =>
      rw [K.d₂_eq_zero (ComplexShape.down ℕ) p 0 m (by simp)]
      simp
  | succ q =>
      exact d₂_succ_horizontalProjection K k m p q (by omega) hp

omit [HasZeroObject C] in
theorem ιTotal_d_succ_horizontalProjection
    (k m p q : ℕ) (htotal : p + q = m + 1)
    (hp : p ≤ k) :
    K.ιTotal (ComplexShape.down ℕ) p q (m + 1) htotal ≫
        (K.total (ComplexShape.down ℕ)).d (m + 1) m ≫
        totalToHorizontalFilteredTotal K k m ≫
        horizontalFilteredTotalToTotal K k m =
      K.ιTotal (ComplexShape.down ℕ) p q (m + 1) htotal ≫
        (K.total (ComplexShape.down ℕ)).d (m + 1) m := by
  change K.ιTotal (ComplexShape.down ℕ) p q (m + 1) htotal ≫
      (K.D₁ (ComplexShape.down ℕ) (m + 1) m +
        K.D₂ (ComplexShape.down ℕ) (m + 1) m) ≫
      totalToHorizontalFilteredTotal K k m ≫
      horizontalFilteredTotalToTotal K k m =
    K.ιTotal (ComplexShape.down ℕ) p q (m + 1) htotal ≫
      (K.D₁ (ComplexShape.down ℕ) (m + 1) m +
        K.D₂ (ComplexShape.down ℕ) (m + 1) m)
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    K.ι_D₁_assoc, K.ι_D₂_assoc]
  rw [d₁_horizontalProjection K k m p q htotal hp,
    d₂_horizontalProjection K k m p q htotal hp]
  rw [K.ι_D₁, K.ι_D₂]

/-- Differential on the horizontal filtration: include into the total,
apply the total differential, then project back to the allowed horizontal
coordinates. -/
noncomputable def horizontalFilteredTotalD (k n m : ℕ) :
    horizontalFilteredTotalObj K k n ⟶
      horizontalFilteredTotalObj K k m :=
  horizontalFilteredTotalToTotal K k n ≫
    (K.total (ComplexShape.down ℕ)).d n m ≫
      totalToHorizontalFilteredTotal K k m

omit [HasZeroObject C] in
theorem horizontalFilteredTotalD_shape
    (k n m : ℕ) (h : ¬(ComplexShape.down ℕ).Rel n m) :
    horizontalFilteredTotalD K k n m = 0 := by
  unfold horizontalFilteredTotalD
  rw [(K.total (ComplexShape.down ℕ)).shape n m h,
    zero_comp, comp_zero]

omit [HasZeroObject C] in
@[reassoc]
theorem horizontalFilteredTotalD_toTotal
    (k m : ℕ) :
    horizontalFilteredTotalD K k (m + 1) m ≫
        horizontalFilteredTotalToTotal K k m =
      horizontalFilteredTotalToTotal K k (m + 1) ≫
        (K.total (ComplexShape.down ℕ)).d (m + 1) m := by
  apply Sigma.hom_ext
  rintro ⟨⟨⟨p, q⟩, htotal⟩, hp⟩
  unfold horizontalFilteredTotalD
  simp only [Category.assoc]
  have hincl := horizontalFilteredTotalι_toTotal_assoc
    K k (m + 1) ⟨⟨(p, q), htotal⟩, hp⟩
      ((K.total (ComplexShape.down ℕ)).d (m + 1) m ≫
        totalToHorizontalFilteredTotal K k m ≫
          horizontalFilteredTotalToTotal K k m)
  change Sigma.ι (fun pq : DownNatHorizontalFilteredFiber (m + 1) k =>
      (K.X pq.val.val.1).X pq.val.val.2) ⟨⟨(p, q), htotal⟩, hp⟩ ≫
        horizontalFilteredTotalToTotal K k (m + 1) ≫
          ((K.total (ComplexShape.down ℕ)).d (m + 1) m ≫
            totalToHorizontalFilteredTotal K k m ≫
              horizontalFilteredTotalToTotal K k m) = _ at hincl
  rw [hincl]
  rw [ιTotal_d_succ_horizontalProjection K k m p q htotal hp]
  have hincl' := horizontalFilteredTotalι_toTotal_assoc
    K k (m + 1) ⟨⟨(p, q), htotal⟩, hp⟩
      ((K.total (ComplexShape.down ℕ)).d (m + 1) m)
  change Sigma.ι (fun pq : DownNatHorizontalFilteredFiber (m + 1) k =>
      (K.X pq.val.val.1).X pq.val.val.2) ⟨⟨(p, q), htotal⟩, hp⟩ ≫
        horizontalFilteredTotalToTotal K k (m + 1) ≫
          (K.total (ComplexShape.down ℕ)).d (m + 1) m = _ at hincl'
  rw [hincl']

noncomputable instance horizontalFilteredTotalToTotal_isSplitMono
    (k n : ℕ) : IsSplitMono (horizontalFilteredTotalToTotal K k n) :=
  IsSplitMono.mk ⟨horizontalFilteredTotalToTotalSplitMono K k n⟩

/-- The horizontal filtration in stage `k`, packaged as a chain complex. -/
noncomputable def horizontalFilteredTotalComplex (k : ℕ) :
    ChainComplex C ℕ where
  X := horizontalFilteredTotalObj K k
  d := horizontalFilteredTotalD K k
  shape := horizontalFilteredTotalD_shape K k
  d_comp_d' n m l hnm hml := by
    obtain rfl : n = m + 1 := hnm.symm
    obtain rfl : m = l + 1 := hml.symm
    apply (cancel_mono (horizontalFilteredTotalToTotal K k l)).1
    rw [Category.assoc, horizontalFilteredTotalD_toTotal]
    rw [← Category.assoc, horizontalFilteredTotalD_toTotal]
    simp

end HomologicalComplex₂

end

