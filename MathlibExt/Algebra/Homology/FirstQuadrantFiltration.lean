/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantTotal

/-!
# Degreewise horizontal filtration of a first-quadrant total

For a first-quadrant bicomplex, this file constructs in each total degree
the finite coproduct of summands whose horizontal coordinate is at most a
chosen stage.  It provides the inclusion into the full total degree, an
explicit coordinate projection, and a split-monomorphism witness.

The differential and filtered-complex packaging are separate gates.
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

/-- Degree `n` of the horizontal filtration at stage `k`. -/
noncomputable def horizontalFilteredTotalObj (k n : ℕ) : C :=
  ∐ fun pq : DownNatHorizontalFilteredFiber n k =>
    (K.X pq.val.val.1).X pq.val.val.2

/-- Inclusion of one allowed bidegree in a horizontal filtration object. -/
noncomputable def horizontalFilteredTotalι (k n : ℕ)
    (pq : DownNatHorizontalFilteredFiber n k) :
    (K.X pq.val.val.1).X pq.val.val.2 ⟶
      horizontalFilteredTotalObj K k n :=
  by
    change (K.X pq.val.val.1).X pq.val.val.2 ⟶
      ∐ fun pq : DownNatHorizontalFilteredFiber n k =>
        (K.X pq.val.val.1).X pq.val.val.2
    exact Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2) pq

/-- Inclusion of the horizontal filtration object into the full total
degree. -/
noncomputable def horizontalFilteredTotalToTotal (k n : ℕ) :
    horizontalFilteredTotalObj K k n ⟶
      (K.total (ComplexShape.down ℕ)).X n :=
  by
    change (∐ fun pq : DownNatHorizontalFilteredFiber n k =>
        (K.X pq.val.val.1).X pq.val.val.2) ⟶
      ∐ fun pq : DownNatTotalFiber n =>
        (K.X pq.val.1).X pq.val.2
    exact Sigma.map'
      (fun pq : DownNatHorizontalFilteredFiber n k => pq.1)
      (fun _ => 𝟙 _)

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalι_toTotal (k n : ℕ)
    (pq : DownNatHorizontalFilteredFiber n k) :
    horizontalFilteredTotalι K k n pq ≫
        horizontalFilteredTotalToTotal K k n =
      K.ιTotal (ComplexShape.down ℕ) pq.val.val.1 pq.val.val.2 n
        pq.val.property := by
  unfold horizontalFilteredTotalι horizontalFilteredTotalToTotal
  change Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2) pq ≫
      Sigma.map'
        (f := fun pq : DownNatTotalFiber n =>
          (K.X pq.val.1).X pq.val.2)
        (g := fun pq : DownNatHorizontalFilteredFiber n k =>
          (K.X pq.val.val.1).X pq.val.val.2)
        (fun pq : DownNatHorizontalFilteredFiber n k => pq.1)
        (fun pq => 𝟙 ((K.X pq.val.val.1).X pq.val.val.2)) =
    Sigma.ι (fun pq : DownNatTotalFiber n =>
      (K.X pq.val.1).X pq.val.2) pq.1
  exact (Sigma.ι_comp_map'
    (f := fun pq : DownNatTotalFiber n =>
      (K.X pq.val.1).X pq.val.2)
    (g := fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2)
    (fun pq : DownNatHorizontalFilteredFiber n k => pq.1)
    (fun pq => 𝟙 ((K.X pq.val.val.1).X pq.val.val.2)) pq).trans
      (Category.id_comp _)

/-- Projection from the full total degree onto horizontal coordinates at
most `k`. -/
noncomputable def totalToHorizontalFilteredTotal (k n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶
      horizontalFilteredTotalObj K k n :=
  K.totalDesc (fun p q h =>
    if hp : p ≤ k then
      horizontalFilteredTotalι K k n ⟨⟨(p, q), h⟩, hp⟩
    else 0)

omit [HasZeroObject C] in
@[reassoc]
theorem ιTotal_totalToHorizontalFilteredTotal
    (k n p q : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.down ℕ) p q n h ≫
        totalToHorizontalFilteredTotal K k n =
      if hp : p ≤ k then
        horizontalFilteredTotalι K k n ⟨⟨(p, q), h⟩, hp⟩
      else 0 := by
  exact K.ι_totalDesc _ p q h

omit [HasZeroObject C] in
/-- The filtration inclusion is split by the coordinate projection. -/
theorem horizontalFilteredTotalToTotal_comp_retraction (k n : ℕ) :
    horizontalFilteredTotalToTotal K k n ≫
        totalToHorizontalFilteredTotal K k n =
      𝟙 (horizontalFilteredTotalObj K k n) := by
  apply Sigma.hom_ext
  rintro ⟨pq, hp⟩
  have hincl := horizontalFilteredTotalι_toTotal K k n ⟨pq, hp⟩
  change Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2) ⟨pq, hp⟩ ≫
        horizontalFilteredTotalToTotal K k n = _ at hincl
  rw [← Category.assoc, hincl,
    ιTotal_totalToHorizontalFilteredTotal, dite_eq_left hp]
  exact (Category.comp_id _).symm

/-- Explicit split-monomorphism structure on the filtration inclusion. -/
noncomputable def horizontalFilteredTotalToTotalSplitMono (k n : ℕ) :
    SplitMono (horizontalFilteredTotalToTotal K k n) where
  retraction := totalToHorizontalFilteredTotal K k n
  id := horizontalFilteredTotalToTotal_comp_retraction K k n

end HomologicalComplex₂

end

