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
# Finite horizontal coordinates and their degreewise splitting

Let C be a preadditive category with a zero object and finite coproducts,
and let K be a bicomplex with both indices in ℕ and both differentials
lowering degree. Its total-degree n object is
T_n = ⨁_(p+q=n) K_(p,q).

The horizontal stage k is the finite coproduct
F_k T_n = ⨁_(p+q=n, p≤k) K_(p,q).
Including these coordinates gives i_(k,n) : F_k T_n → T_n.
The coordinate projection r_(k,n) retains each allowed summand and
sends all p > k summands to zero. It satisfies r_(k,n)i_(k,n) = id,
so every stage inclusion is a split monomorphism in C.
The category object and morphism universes are independent.
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

/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, the degree-n
object at horizontal stage k is
F_k T_n = ⨁_(p+q=n, p≤k) K_(p,q).
Both the total-degree equation and the horizontal bound determine
the finite index set. -/
noncomputable def horizontalFilteredTotalObj (k n : ℕ) : C :=
  ∐ fun pq : DownNatHorizontalFilteredFiber n k =>
    (K.X pq.val.val.1).X pq.val.val.2

/-- For a nonnegative homological bicomplex K and p+q=n with
p≤k, the filtered summand inclusion is
K_(p,q) → F_k T_n = ⨁_(a+b=n, a≤k) K_(a,b).
It is the corresponding coproduct leg in the preadditive target
category with finite coproducts. -/
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

/-- For a nonnegative homological bicomplex K, the map
i_(k,n) : F_k T_n → Tot(K)_n includes the finite summands
with p+q=n and p≤k into the full antidiagonal coproduct.
It acts by the identity on each retained bidegree. -/
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

/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts, the coordinate projection
r_(k,n) : Tot(K)_n → F_k T_n is the filtered inclusion on each
summand with p≤k and zero on each summand with p>k.
The total-degree condition is p+q=n. -/
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
/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts, the maps
F_k T_n → Tot(K)_n → F_k T_n satisfy r_(k,n) ∘ i_(k,n) = id.
The splitting is degreewise and is determined by the retained
horizontal coordinates p≤k. -/
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

/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts, the inclusion
i_(k,n) : F_k T_n → Tot(K)_n has split-monomorphism data with
retraction r_(k,n), the projection to horizontal coordinates p≤k.
Its retraction identity is r_(k,n)i_(k,n) = id. -/
noncomputable def horizontalFilteredTotalToTotalSplitMono (k n : ℕ) :
    SplitMono (horizontalFilteredTotalToTotal K k n) where
  retraction := totalToHorizontalFilteredTotal K k n
  id := horizontalFilteredTotalToTotal_comp_retraction K k n

end HomologicalComplex₂

end
