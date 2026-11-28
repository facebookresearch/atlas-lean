/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationDiagram

/-!
# Bicomplex maps act functorially on horizontally filtered totals

Let C be preadditive with a zero object and finite coproducts, and let K,L
be nonnegative homological bicomplexes. A bicomplex map f : K → L
preserves each finite horizontal stage
F_k T_n = ⨁_(p+q=n, p≤k) K_(p,q).

The stage map applies f_(p,q) on every retained summand. It commutes
with the restricted differential, with the inclusion into the signed
total complex and with every stage increase k≤l.
Thus K ↦ (Tot(K),F_• Tot(K)) is a functor to filtered chain complexes
in C, indexed by ℕ. Its underlying map is Tot(f), and its stage-k
map is F_k(f). The category object and morphism worlds are independent.
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
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- For f : K → L between nonnegative homological bicomplexes
in a preadditive category with a zero object and finite coproducts,
the degreewise stage map F_k(f)_n : F_k Tot(K)_n → F_k Tot(L)_n
applies f_(p,q) on each summand with p+q=n and p≤k,
then includes it in the corresponding L-summand. -/
noncomputable def horizontalFilteredTotalMapOfBicomplex
    (f : K ⟶ L) (k n : ℕ) :
    horizontalFilteredTotalObj K k n ⟶
      horizontalFilteredTotalObj L k n :=
  Sigma.desc fun pq : DownNatHorizontalFilteredFiber n k ↦
    (f.f pq.val.val.1).f pq.val.val.2 ≫
      horizontalFilteredTotalι L k n pq

omit [HasZeroObject C] in
/-- For f : K → L between nonnegative homological bicomplexes,
and an allowed bidegree p+q=n, p≤k, the stage map satisfies
F_k(f)_n ∘ ι_(K,p,q)^k = ι_(L,p,q)^k ∘ f_(p,q).
This is the component formula for the finite coproduct map. -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalι_mapOfBicomplex
    (f : K ⟶ L) (k n : ℕ)
    (pq : DownNatHorizontalFilteredFiber n k) :
    horizontalFilteredTotalι K k n pq ≫
        horizontalFilteredTotalMapOfBicomplex f k n =
      (f.f pq.val.val.1).f pq.val.val.2 ≫
        horizontalFilteredTotalι L k n pq := by
  apply Sigma.ι_comp_desc

omit [HasZeroObject C] in
/-- For a bicomplex map f : K → L in a preadditive category
with finite coproducts, the stage maps satisfy
i_(L,k,n) ∘ F_k(f)_n = Tot(f)_n ∘ i_(K,k,n).
The equality is in total degree n and respects the bound p≤k. -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalMapOfBicomplex_toTotal
    (f : K ⟶ L) (k n : ℕ) :
    horizontalFilteredTotalMapOfBicomplex f k n ≫
        horizontalFilteredTotalToTotal L k n =
      horizontalFilteredTotalToTotal K k n ≫
        (total.map f (ComplexShape.down ℕ)).f n := by
  apply Sigma.hom_ext
  intro pq
  change horizontalFilteredTotalι K k n pq ≫
      (horizontalFilteredTotalMapOfBicomplex f k n ≫
        horizontalFilteredTotalToTotal L k n) =
    horizontalFilteredTotalι K k n pq ≫
      (horizontalFilteredTotalToTotal K k n ≫
        (total.map f (ComplexShape.down ℕ)).f n)
  rw [← Category.assoc,
    horizontalFilteredTotalι_mapOfBicomplex,
    Category.assoc, horizontalFilteredTotalι_toTotal,
    ← Category.assoc, horizontalFilteredTotalι_toTotal,
    HomologicalComplex₂.ιTotal_map]

/-- For f : K → L between nonnegative homological bicomplexes
in a preadditive category with a zero object and finite coproducts,
the maps applying f_(p,q) on the coordinates p≤k define
F_k(f) : F_k Tot(K) → F_k Tot(L) as a chain map.
They commute with the restricted signed total differentials. -/
noncomputable def horizontalFilteredTotalComplexMapOfBicomplex
    (f : K ⟶ L) (k : ℕ) :
    horizontalFilteredTotalComplex K k ⟶
      horizontalFilteredTotalComplex L k where
  f := horizontalFilteredTotalMapOfBicomplex f k
  comm' := by
    intro n m hnm
    obtain rfl : n = m + 1 := hnm.symm
    dsimp only [horizontalFilteredTotalComplex]
    apply (cancel_mono
      (horizontalFilteredTotalToTotal L k m)).1
    simp only [Category.assoc,
      horizontalFilteredTotalD_toTotal,
      horizontalFilteredTotalMapOfBicomplex_toTotal_assoc,
      horizontalFilteredTotalMapOfBicomplex_toTotal]
    rw [(total.map f (ComplexShape.down ℕ)).comm (m + 1) m]
    rw [horizontalFilteredTotalD_toTotal_assoc]

omit [HasZeroObject C] in
/-- For a bicomplex map f : K → L in a preadditive category
with finite coproducts, the chain maps satisfy
i_(L,k) ∘ F_k(f) = Tot(f) ∘ i_(K,k).
Both paths go from the stage-k K-subcomplex to Tot(L). -/
@[reassoc (attr := simp)]
theorem horizontalFilteredTotalComplexMapOfBicomplex_toTotal
    (f : K ⟶ L) (k : ℕ) :
    horizontalFilteredTotalComplexMapOfBicomplex f k ≫
        horizontalFilteredTotalComplexToTotal L k =
      horizontalFilteredTotalComplexToTotal K k ≫
        total.map f (ComplexShape.down ℕ) := by
  ext n
  dsimp only [HomologicalComplex.comp_f,
    horizontalFilteredTotalComplexMapOfBicomplex,
    horizontalFilteredTotalComplexToTotal]
  exact horizontalFilteredTotalMapOfBicomplex_toTotal f k n

omit [HasZeroObject C] in
/-- For a bicomplex map f : K → L and k≤l, the stage maps satisfy
j_(L,k,l) ∘ F_k(f) = F_l(f) ∘ j_(K,k,l),
where j_(k,l) includes the finite horizontal coordinates of stage k
into stage l. This is a square of chain complexes. -/
theorem horizontalFilteredTotalComplexMapOfBicomplex_naturality
    (f : K ⟶ L) {k l : ℕ} (h : k ≤ l) :
    horizontalFilteredTotalComplexMapOfBicomplex f k ≫
        horizontalFilteredTotalComplexMap L h =
      horizontalFilteredTotalComplexMap K h ≫
        horizontalFilteredTotalComplexMapOfBicomplex f l := by
  ext n
  dsimp only [HomologicalComplex.comp_f,
    horizontalFilteredTotalComplexMapOfBicomplex,
    horizontalFilteredTotalComplexMap]
  apply (cancel_mono
    (horizontalFilteredTotalToTotal L l n)).1
  simp only [Category.assoc,
    horizontalFilteredTotalMapOfBicomplex_toTotal,
    horizontalFilteredTotalMap_toTotal_assoc,
    horizontalFilteredTotalMap_toTotal]

/-- For a nonnegative homological bicomplex K in a preadditive
category with a zero object and finite coproducts, the filtered
object has underlying chain complex Tot(K) and stage-k subcomplex
F_k T with terms ⨁_(p+q=n,p≤k) K_(p,q).
Its filtration is indexed by ℕ. -/
noncomputable def horizontalTotalFilteredObject
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    CategoryTheory.FilteredObject (ChainComplex C ℕ) ℕ where
  X := K.total (ComplexShape.down ℕ)
  filtration := horizontalTotalFiltration K

/-- For f : K → L between nonnegative homological bicomplexes,
the induced filtered morphism has underlying chain map Tot(f)
and stage-k chain map F_k(f).
Their commuting squares with the stage inclusions make a morphism
of ℕ-filtered chain complexes. -/
noncomputable def horizontalTotalFilteredObjectMap (f : K ⟶ L) :
    horizontalTotalFilteredObject K ⟶
      horizontalTotalFilteredObject L :=
  CategoryTheory.FilteredObject.homMk
    (total.map f (ComplexShape.down ℕ))
    (fun k ↦ horizontalFilteredTotalComplexMapOfBicomplex f k)
    (fun k ↦ horizontalFilteredTotalComplexMapOfBicomplex_toTotal f k)

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFilteredObjectMap_hom (f : K ⟶ L) :
    (horizontalTotalFilteredObjectMap f).hom =
      total.map f (ComplexShape.down ℕ) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFilteredObjectMap_natTrans_app
    (f : K ⟶ L) (k : ℕ) :
    (horizontalTotalFilteredObjectMap f).natTrans.app k =
      horizontalFilteredTotalComplexMapOfBicomplex f k :=
  rfl

/-- For a preadditive category C with a zero object and finite
coproducts, the assignment K ↦ (Tot(K),F_• Tot(K)) defines
a functor from nonnegative homological bicomplexes to
FilteredObject(ChainComplex(C,ℕ),ℕ).
On maps it uses Tot(f) and all finite-stage maps F_k(f). -/
noncomputable def horizontalTotalFilteredObjectFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      CategoryTheory.FilteredObject (ChainComplex C ℕ) ℕ where
  obj := horizontalTotalFilteredObject
  map := horizontalTotalFilteredObjectMap
  map_id K := by
    apply CategoryTheory.FilteredObject.hom_ext
    exact total.map_id K (ComplexShape.down ℕ)
  map_comp f g := by
    apply CategoryTheory.FilteredObject.hom_ext
    exact total.map_comp f g (ComplexShape.down ℕ)

end HomologicalComplex₂

end
