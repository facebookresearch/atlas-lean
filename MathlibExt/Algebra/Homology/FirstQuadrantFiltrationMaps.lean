/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFilteredComplex

/-!
# Stage inclusions and degreewise exhaustiveness of the horizontal filtration

Let C be preadditive with a zero object and finite coproducts, and let K
be a nonnegative homological bicomplex. For k≤l, the finite coordinate
inclusion F_k T_n → F_l T_n sends each summand K_(p,q), p+q=n,
p≤k, to the same summand at stage l.

These maps commute with the restricted differentials and form chain
maps F_k T → F_l T, compatible with both inclusions into Tot(K).
If n≤k, the projection Tot(K)_n → F_k T_n is also inverse to its
inclusion, so F_k T_n ≅ Tot(K)_n. The comparison concerns the chosen
degree n; the category object and morphism worlds are independent.
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

def horizontalFilteredTotalIndexMap
    {k l n : ℕ} (h : k ≤ l) :
    DownNatHorizontalFilteredFiber n k →
      DownNatHorizontalFilteredFiber n l :=
  fun pq => ⟨pq.1, pq.2.trans h⟩

def horizontalFilteredTotalMapComponent
    {k l n : ℕ} (h : k ≤ l)
    (pq : DownNatHorizontalFilteredFiber n k) :
    (K.X pq.val.val.1).X pq.val.val.2 ⟶
      (K.X (horizontalFilteredTotalIndexMap (n := n) h pq).val.val.1).X
        (horizontalFilteredTotalIndexMap (n := n) h pq).val.val.2 :=
  eqToHom (by rfl)

/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts, k≤l gives
F_k T_n → F_l T_n by including the same bidegrees p+q=n, p≤k.
Each component is the identity on K_(p,q) and uses p≤k≤l. -/
noncomputable def horizontalFilteredTotalMap
    {k l : ℕ} (h : k ≤ l) (n : ℕ) :
    horizontalFilteredTotalObj K k n ⟶
      horizontalFilteredTotalObj K l n := by
  change (∐ fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2) ⟶
    ∐ fun pq : DownNatHorizontalFilteredFiber n l =>
      (K.X pq.val.val.1).X pq.val.val.2
  exact Sigma.map'
    (f := fun pq : DownNatHorizontalFilteredFiber n l =>
      (K.X pq.val.val.1).X pq.val.val.2)
    (g := fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2)
    (horizontalFilteredTotalIndexMap (n := n) h)
    (horizontalFilteredTotalMapComponent K (n := n) h)

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalι_map
    {k l : ℕ} (h : k ≤ l) (n : ℕ)
    (pq : DownNatHorizontalFilteredFiber n k) :
    horizontalFilteredTotalι K k n pq ≫
      horizontalFilteredTotalMap K h n =
      horizontalFilteredTotalι K l n
        (horizontalFilteredTotalIndexMap (n := n) h pq) := by
  unfold horizontalFilteredTotalι horizontalFilteredTotalMap
  change Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2) pq ≫
      Sigma.map'
        (f := fun pq : DownNatHorizontalFilteredFiber n l =>
          (K.X pq.val.val.1).X pq.val.val.2)
        (g := fun pq : DownNatHorizontalFilteredFiber n k =>
          (K.X pq.val.val.1).X pq.val.val.2)
        (horizontalFilteredTotalIndexMap (n := n) h)
        (horizontalFilteredTotalMapComponent K (n := n) h) = _
  exact (Sigma.ι_comp_map'
    (f := fun pq : DownNatHorizontalFilteredFiber n l =>
      (K.X pq.val.val.1).X pq.val.val.2)
    (g := fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2)
    (horizontalFilteredTotalIndexMap (n := n) h)
    (horizontalFilteredTotalMapComponent K (n := n) h) pq).trans (by
      unfold horizontalFilteredTotalMapComponent
      simp)

omit [HasZeroObject C] in
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalMap_toTotal
    {k l : ℕ} (h : k ≤ l) (n : ℕ) :
    horizontalFilteredTotalMap K h n ≫
        horizontalFilteredTotalToTotal K l n =
      horizontalFilteredTotalToTotal K k n := by
  apply Sigma.hom_ext
  intro pq
  have hmap := horizontalFilteredTotalι_map K h n pq
  change Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
      (K.X pq.val.val.1).X pq.val.val.2) pq ≫
        horizontalFilteredTotalMap K h n =
      horizontalFilteredTotalι K l n
        (horizontalFilteredTotalIndexMap (n := n) h pq) at hmap
  have htoL := horizontalFilteredTotalι_toTotal K l n
    (horizontalFilteredTotalIndexMap (n := n) h pq)
  have htoK := horizontalFilteredTotalι_toTotal K k n pq
  calc
    Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
          (K.X pq.val.val.1).X pq.val.val.2) pq ≫
        (horizontalFilteredTotalMap K h n ≫
          horizontalFilteredTotalToTotal K l n) =
      (Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
          (K.X pq.val.val.1).X pq.val.val.2) pq ≫
        horizontalFilteredTotalMap K h n) ≫
          horizontalFilteredTotalToTotal K l n :=
      (Category.assoc _ _ _).symm
    _ =
      horizontalFilteredTotalι K l n
          (horizontalFilteredTotalIndexMap (n := n) h pq) ≫
        horizontalFilteredTotalToTotal K l n := by rw [hmap]
    _ = K.ιTotal (ComplexShape.down ℕ) pq.val.val.1 pq.val.val.2 n
          pq.val.property := htoL
    _ = horizontalFilteredTotalι K k n pq ≫
          horizontalFilteredTotalToTotal K k n := htoK.symm
    _ = Sigma.ι (fun pq : DownNatHorizontalFilteredFiber n k =>
          (K.X pq.val.val.1).X pq.val.val.2) pq ≫
        horizontalFilteredTotalToTotal K k n := rfl

/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, the degreewise
inclusions for k≤l define a chain map F_k T → F_l T.
It is compatible with the two inclusions into Tot(K). -/
noncomputable def horizontalFilteredTotalComplexMap
    {k l : ℕ} (h : k ≤ l) :
    horizontalFilteredTotalComplex K k ⟶
      horizontalFilteredTotalComplex K l where
  f := horizontalFilteredTotalMap K h
  comm' := by
    intro n m hnm
    obtain rfl : n = m + 1 := hnm.symm
    change horizontalFilteredTotalMap K h (m + 1) ≫
        horizontalFilteredTotalD K l (m + 1) m =
      horizontalFilteredTotalD K k (m + 1) m ≫
        horizontalFilteredTotalMap K h m
    apply (cancel_mono (horizontalFilteredTotalToTotal K l m)).1
    calc
      (horizontalFilteredTotalMap K h (m + 1) ≫
          horizontalFilteredTotalD K l (m + 1) m) ≫
            horizontalFilteredTotalToTotal K l m =
        horizontalFilteredTotalMap K h (m + 1) ≫
          (horizontalFilteredTotalD K l (m + 1) m ≫
            horizontalFilteredTotalToTotal K l m) :=
        Category.assoc _ _ _
      _ = horizontalFilteredTotalMap K h (m + 1) ≫
          (horizontalFilteredTotalToTotal K l (m + 1) ≫
            (K.total (ComplexShape.down ℕ)).d (m + 1) m) := by
        rw [horizontalFilteredTotalD_toTotal]
      _ = (horizontalFilteredTotalMap K h (m + 1) ≫
          horizontalFilteredTotalToTotal K l (m + 1)) ≫
            (K.total (ComplexShape.down ℕ)).d (m + 1) m :=
        (Category.assoc _ _ _).symm
      _ = horizontalFilteredTotalToTotal K k (m + 1) ≫
          (K.total (ComplexShape.down ℕ)).d (m + 1) m := by
        rw [horizontalFilteredTotalMap_toTotal]
      _ = horizontalFilteredTotalD K k (m + 1) m ≫
          horizontalFilteredTotalToTotal K k m :=
        (horizontalFilteredTotalD_toTotal K k m).symm
      _ = horizontalFilteredTotalD K k (m + 1) m ≫
          (horizontalFilteredTotalMap K h m ≫
            horizontalFilteredTotalToTotal K l m) := by
        rw [horizontalFilteredTotalMap_toTotal]
      _ = (horizontalFilteredTotalD K k (m + 1) m ≫
          horizontalFilteredTotalMap K h m) ≫
            horizontalFilteredTotalToTotal K l m :=
        (Category.assoc _ _ _).symm

omit [HasZeroObject C] in
/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts and n≤k, the maps
Tot(K)_n → F_k T_n → Tot(K)_n satisfy i_(k,n)r_(k,n) = id.
Every bidegree on the antidiagonal has p≤n≤k. -/
theorem totalToHorizontalFilteredTotal_comp_toTotal_of_le
    (k n : ℕ) (h : n ≤ k) :
    totalToHorizontalFilteredTotal K k n ≫
        horizontalFilteredTotalToTotal K k n =
      𝟙 ((K.total (ComplexShape.down ℕ)).X n) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [ιTotal_horizontalProjection,
    dite_eq_left ((downNatTotalFiber_fst_le n ⟨(p, q), hpq⟩).trans h)]
  rw [Category.comp_id]

/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts and n≤k, the explicit isomorphism
F_k T_n ≅ Tot(K)_n has forward map i_(k,n), the coordinate inclusion,
and inverse r_(k,n), the total-to-stage projection. -/
noncomputable def horizontalFilteredTotalIsoOfLE
    (k n : ℕ) (h : n ≤ k) :
    horizontalFilteredTotalObj K k n ≅
      (K.total (ComplexShape.down ℕ)).X n where
  hom := horizontalFilteredTotalToTotal K k n
  inv := totalToHorizontalFilteredTotal K k n
  hom_inv_id := horizontalFilteredTotalToTotal_comp_retraction K k n
  inv_hom_id := totalToHorizontalFilteredTotal_comp_toTotal_of_le K k n h

end HomologicalComplex₂

end
