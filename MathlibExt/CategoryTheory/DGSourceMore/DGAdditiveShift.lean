/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/AdditiveClosure/Shift.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: module/namespace paths are adapted for Atlas, and the
universes of the final independent section are redeclared explicitly.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGAdditiveClosure
public import MathlibExt.CategoryTheory.DGSourceMore.DGShiftClosure

/-!
# Shifts of finite sums of shifted objects

Let `C` be a differential graded category.  The shift `X[r] ↦ X[r + n]` of the shift closure of
`C` (`MathlibExt.DGSource.DGShiftClosure.shiftFunctor`) induces a DG functor on the additive closure of the
shift closure, sending `⊕ᵢ Xᵢ[rᵢ]` to `⊕ᵢ Xᵢ[rᵢ + n]` and leaving every matrix entry unchanged as
a morphism of `C`.

The summandwise comparison morphisms `Xᵢ[rᵢ] ⟶ Xᵢ[rᵢ + n]` of the shift closure
(`MathlibExt.DGSource.DGShiftClosure.toShift`), whose underlying morphisms are `(-1)^(n * rᵢ)` times the
identity, assemble into the diagonal matrix `MathlibExt.DGSource.DGAdditiveClosure.toShift` of degree `-n`
from `⊕ᵢ Xᵢ[rᵢ]` to `⊕ᵢ Xᵢ[rᵢ + n]`.  It is closed, has the diagonal matrix
`MathlibExt.DGSource.DGAdditiveClosure.fromShift` of degree `n` as its inverse, and is natural up to the
Koszul sign, `f ≫ σ_N = (-1)^(n * p) • σ_M ≫ f⟦n⟧` for `f` of degree `p`.  These are the
comparison morphisms of shifts of twisted objects (see
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedShift.lean`).

A DG functor `F : C ⥤ D` induces a DG functor between the additive closures of the shift closures,
sending `⊕ᵢ Xᵢ[rᵢ]` to `⊕ᵢ (F Xᵢ)[rᵢ]`.  It commutes with shifting every summand and preserves the
comparison morphisms, since it is applied entrywise and preserves identities.

## Main definitions

* `MathlibExt.DGSource.DGAdditiveClosure.toShift` and `MathlibExt.DGSource.DGAdditiveClosure.fromShift`: the diagonal
  comparison matrices `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` of degree `-n` and
  `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` of degree `n`.

## Main results

* `MathlibExt.DGSource.DGAdditiveClosure.dgDifferential_toShift` and
  `MathlibExt.DGSource.DGAdditiveClosure.dgDifferential_fromShift`: the comparison morphisms are closed.
* `MathlibExt.DGSource.DGAdditiveClosure.dgComp_toShift_fromShift` and
  `MathlibExt.DGSource.DGAdditiveClosure.dgComp_fromShift_toShift`: they are mutually inverse.
* `MathlibExt.DGSource.DGAdditiveClosure.dgComp_toShift` and `MathlibExt.DGSource.DGAdditiveClosure.dgComp_fromShift`:
  they are natural up to the Koszul sign.
* `CategoryTheory.EnrichedFunctor.mapDGShiftClosure_mapDGAdditiveClosure_dgMap_shiftFunctor`,
  `CategoryTheory.EnrichedFunctor.mapDGShiftClosure_mapDGAdditiveClosure_dgMap_toShift` and
  `CategoryTheory.EnrichedFunctor.mapDGShiftClosure_mapDGAdditiveClosure_dgMap_fromShift`: the DG
  functor induced by a DG functor commutes with the shifts and preserves the comparison morphisms.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

namespace DGAdditiveClosure

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

variable (R) in
/-- The comparison morphism `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` of degree `-n`: the diagonal matrix of
the comparison morphisms `MathlibExt.DGSource.DGShiftClosure.toShift` of the summands. -/
noncomputable def toShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    DGHom R (-n) M ((DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.obj M) :=
  (dgHomEquiv R _ _ (-n)).symm fun i ↦ by
    classical
    exact Pi.single i (DGShiftClosure.toShift R (M.X i) n)

variable (R) in
/-- The comparison morphism `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` of degree `n`: the diagonal matrix of
the inverse comparison morphisms `MathlibExt.DGSource.DGShiftClosure.fromShift` of the summands. -/
noncomputable def fromShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    DGHom R n ((DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.obj M) M :=
  (dgHomEquiv R _ _ n).symm fun i ↦ by
    classical
    exact Pi.single i (DGShiftClosure.fromShift R (M.X i) n)

/-- The diagonal entries of `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` are the comparison morphisms of the
summands. -/
@[simp]
theorem dgHomEquiv_toShift_self (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) (i : M.ι) :
    dgHomEquiv R _ _ (-n) (toShift R M n) i i = DGShiftClosure.toShift R (M.X i) n := by
  simp [toShift]

/-- The off-diagonal entries of `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` vanish. -/
@[simp]
theorem dgHomEquiv_toShift_of_ne (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ)
    {i j : M.ι} (h : i ≠ j) : dgHomEquiv R _ _ (-n) (toShift R M n) i j = 0 := by
  classical
  simp [toShift, Pi.single_eq_of_ne (Ne.symm h)]

/-- The diagonal entries of `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` are the inverse comparison morphisms of
the summands. -/
@[simp]
theorem dgHomEquiv_fromShift_self (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) (i : M.ι) :
    dgHomEquiv R _ _ n (fromShift R M n) i i = DGShiftClosure.fromShift R (M.X i) n := by
  simp [fromShift]

/-- The off-diagonal entries of `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` vanish. -/
@[simp]
theorem dgHomEquiv_fromShift_of_ne (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ)
    {i j : M.ι} (h : i ≠ j) : dgHomEquiv R _ _ n (fromShift R M n) i j = 0 := by
  classical
  simp [fromShift, Pi.single_eq_of_ne (Ne.symm h)]

/-- Multiplying a column on the left by the diagonal comparison matrix picks out one entry. -/
private theorem sum_dgComp_toShift {M : DGAdditiveClosure (DGShiftClosure C)} {n q m : ℤ}
    {Z : DGShiftClosure C} (g : ∀ j, DGHom R q ((DGShiftClosure.shiftFunctor R n).obj (M.X j)) Z)
    (h : -n + q = m) (i : M.ι) :
    ∑ j, dgComp R (dgHomEquiv R _ _ (-n) (toShift R M n) i j) (g j) h =
      dgComp R (DGShiftClosure.toShift R (M.X i) n) (g i) h := by
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by
    rw [dgHomEquiv_toShift_of_ne M n (Ne.symm hj), zero_dgComp]) (by simp),
    dgHomEquiv_toShift_self]

/-- Multiplying a row on the right by the diagonal comparison matrix picks out one entry. -/
private theorem sum_toShift_dgComp {M : DGAdditiveClosure (DGShiftClosure C)} {n p m : ℤ}
    {Z : DGShiftClosure C} (f : ∀ j, DGHom R p Z (M.X j)) (h : p + -n = m) (k : M.ι) :
    ∑ j, dgComp R (f j) (dgHomEquiv R _ _ (-n) (toShift R M n) j k) h =
      dgComp R (f k) (DGShiftClosure.toShift R (M.X k) n) h := by
  rw [Finset.sum_eq_single k (fun j _ hj ↦ by
    rw [dgHomEquiv_toShift_of_ne M n hj, dgComp_zero]) (by simp),
    dgHomEquiv_toShift_self]

/-- Multiplying a column on the left by the diagonal inverse comparison matrix picks out one
entry. -/
private theorem sum_dgComp_fromShift {M : DGAdditiveClosure (DGShiftClosure C)} {n q m : ℤ}
    {Z : DGShiftClosure C} (g : ∀ j, DGHom R q (M.X j) Z) (h : n + q = m) (i : M.ι) :
    ∑ j, dgComp R (dgHomEquiv R _ _ n (fromShift R M n) i j) (g j) h =
      dgComp R (DGShiftClosure.fromShift R (M.X i) n) (g i) h := by
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by
    rw [dgHomEquiv_fromShift_of_ne M n (Ne.symm hj), zero_dgComp]) (by simp),
    dgHomEquiv_fromShift_self]

/-- Multiplying a row on the right by the diagonal inverse comparison matrix picks out one
entry. -/
-- The sum runs over the summands of the shift of `M`, as in a product with `fromShift R M n`,
-- so that it matches such products syntactically.
private theorem sum_fromShift_dgComp {M : DGAdditiveClosure (DGShiftClosure C)} {n p m : ℤ}
    {Z : DGShiftClosure C} (f : ∀ j, DGHom R p Z ((DGShiftClosure.shiftFunctor R n).obj (M.X j)))
    (h : p + n = m) (k : M.ι) :
    ∑ j : ((DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.obj M).ι,
      dgComp R (f j) (dgHomEquiv R _ _ n (fromShift R M n) j k) h =
      dgComp R (f k) (DGShiftClosure.fromShift R (M.X k) n) h := by
  rw [Finset.sum_eq_single k (fun j _ hj ↦ by
    rw [dgHomEquiv_fromShift_of_ne M n hj, dgComp_zero]) (by simp),
    dgHomEquiv_fromShift_self]

/-- **The comparison morphisms are natural up to the Koszul sign**: for `f : M ⟶ N` of degree
`p`, `f` followed by `N ⟶ N⟦n⟧` is `(-1)^(n * p)` times `M ⟶ M⟦n⟧` followed by the shift of
`f`. -/
theorem dgComp_toShift {M N : DGAdditiveClosure (DGShiftClosure C)} (n : ℤ) {p m : ℤ}
    (f : DGHom R p M N) (h : p + -n = m) :
    dgComp R f (toShift R N n) h = (n * p).negOnePow • dgComp R (toShift R M n)
      ((DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.dgMap p f) (by omega) :=
  dgHom_ext R fun i k ↦ by
    rw [map_zsmul_unit, Pi.smul_apply, Pi.smul_apply, dgHomEquiv_dgComp, dgHomEquiv_dgComp,
      sum_toShift_dgComp, sum_dgComp_toShift, EnrichedFunctor.dgMap_mapDGAdditiveClosure,
      EnrichedFunctor.dgHomEquiv_mapDGAdditiveClosureHom, DGShiftClosure.dgComp_toShift]

/-- **The inverse comparison morphisms are natural up to the Koszul sign**: for `f : M ⟶ N` of
degree `p`, the shift of `f` followed by `N⟦n⟧ ⟶ N` is `(-1)^(n * p)` times `M⟦n⟧ ⟶ M` followed
by `f`. -/
theorem dgComp_fromShift {M N : DGAdditiveClosure (DGShiftClosure C)} (n : ℤ) {p m : ℤ}
    (f : DGHom R p M N) (h : p + n = m) :
    dgComp R ((DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.dgMap p f)
      (fromShift R N n) h = (n * p).negOnePow • dgComp R (fromShift R M n) f (by omega) :=
  dgHom_ext R fun i k ↦ by
    rw [map_zsmul_unit, Pi.smul_apply, Pi.smul_apply, dgHomEquiv_dgComp, dgHomEquiv_dgComp,
      sum_fromShift_dgComp, sum_dgComp_fromShift, EnrichedFunctor.dgMap_mapDGAdditiveClosure,
      EnrichedFunctor.dgHomEquiv_mapDGAdditiveClosureHom, DGShiftClosure.dgComp_fromShift]

/-- The comparison morphism `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` is closed, as a diagonal matrix of
closed morphisms. -/
@[simp↓]
theorem dgDifferential_toShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    dgDifferential R (-n) (toShift R M n) = 0 :=
  dgHom_ext R fun i j ↦ by
    rw [dgHomEquiv_dgDifferential, map_zero, Pi.zero_apply, Pi.zero_apply]
    rcases eq_or_ne i j with rfl | h
    · rw [dgHomEquiv_toShift_self, DGShiftClosure.dgDifferential_toShift]
    · rw [dgHomEquiv_toShift_of_ne M n h, map_zero]

/-- The comparison morphisms `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` compose to the identity. -/
@[simp↓]
theorem dgComp_toShift_fromShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    dgComp R (toShift R M n) (fromShift R M n) (neg_add_cancel n) = dgId R M :=
  dgHom_ext R fun i k ↦ by
    rw [dgHomEquiv_dgComp, sum_dgComp_toShift]
    rcases eq_or_ne i k with rfl | h
    · rw [dgHomEquiv_fromShift_self, DGShiftClosure.dgComp_toShift_fromShift,
        dgHomEquiv_dgId_self]
    · rw [dgHomEquiv_fromShift_of_ne M n h, dgComp_zero, dgHomEquiv_dgId_of_ne R M h]

/-- The comparison morphisms `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` compose to the
identity. -/
@[simp↓]
theorem dgComp_fromShift_toShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    dgComp R (fromShift R M n) (toShift R M n) (add_neg_cancel n) =
      dgId R ((DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.obj M) :=
  dgHom_ext R fun i k ↦ by
    rw [dgHomEquiv_dgComp, sum_toShift_dgComp]
    rcases eq_or_ne i k with rfl | h
    · rw [dgHomEquiv_fromShift_self, DGShiftClosure.dgComp_fromShift_toShift,
        dgHomEquiv_dgId_self]
    · rw [dgHomEquiv_fromShift_of_ne M n h, zero_dgComp, dgHomEquiv_dgId_of_ne R _ h]

/-- The comparison morphism `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` is closed, as the inverse of a closed
morphism. -/
@[simp↓]
theorem dgDifferential_fromShift (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    dgDifferential R n (fromShift R M n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_toShift M n) (neg_add_cancel n)
    (dgComp_toShift_fromShift M n) (dgComp_fromShift_toShift M n)

end DGAdditiveClosure

end MathlibExt.DGSource

namespace CategoryTheory.EnrichedFunctor

open MathlibExt.DGSource

universe v u u₂

/-! ### Functoriality -/

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u₂} [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- The DG functor induced by `F` on additive closures of shift closures commutes with shifting
every summand: a matrix of morphisms has the same image under the two composites. -/
theorem mapDGShiftClosure_mapDGAdditiveClosure_dgMap_shiftFunctor (n : ℤ)
    {M N : DGAdditiveClosure (DGShiftClosure C)} {p : ℤ} (f : DGHom R p M N) :
    F.mapDGShiftClosure.mapDGAdditiveClosure.dgMap p
        ((DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.dgMap p f) =
      (DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.dgMap p
        (F.mapDGShiftClosure.mapDGAdditiveClosure.dgMap p f) :=
  DGAdditiveClosure.dgHom_ext R fun i j ↦ by
    -- `dgHomEquiv_mapDGAdditiveClosureHom` states its objects as structure literals, which match
    -- `G.mapDGAdditiveClosure.obj M` only once `M` is given: the outer entry of the right side is
    -- rewritten by naming its objects.
    rw [dgMap_mapDGAdditiveClosure, dgHomEquiv_mapDGAdditiveClosureHom,
      dgMap_mapDGAdditiveClosure, dgHomEquiv_mapDGAdditiveClosureHom, dgMap_mapDGShiftClosure,
      DGShiftClosure.dgMap_shiftFunctor, dgMap_mapDGAdditiveClosure,
      dgHomEquiv_mapDGAdditiveClosureHom (DGShiftClosure.shiftFunctor R n)
        (M := F.mapDGShiftClosure.mapDGAdditiveClosure.obj M)
        (N := F.mapDGShiftClosure.mapDGAdditiveClosure.obj N),
      dgMap_mapDGAdditiveClosure, dgHomEquiv_mapDGAdditiveClosureHom, dgMap_mapDGShiftClosure,
      DGShiftClosure.dgMap_shiftFunctor, mapDGShiftClosureHom_shiftHomEquiv]

/-- The DG functor induced by `F` sends the comparison morphism `⊕ᵢ Xᵢ[rᵢ] ⟶ ⊕ᵢ Xᵢ[rᵢ + n]` to the
comparison morphism of the image. -/
theorem mapDGShiftClosure_mapDGAdditiveClosure_dgMap_toShift
    (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    F.mapDGShiftClosure.mapDGAdditiveClosure.dgMap (-n) (DGAdditiveClosure.toShift R M n) =
      DGAdditiveClosure.toShift R (F.mapDGShiftClosure.mapDGAdditiveClosure.obj M) n :=
  DGAdditiveClosure.dgHom_ext R fun i j ↦ by
    rw [dgMap_mapDGAdditiveClosure, dgHomEquiv_mapDGAdditiveClosureHom]
    rcases eq_or_ne i j with rfl | h
    · rw [DGAdditiveClosure.dgHomEquiv_toShift_self M n i,
        DGAdditiveClosure.dgHomEquiv_toShift_self (F.mapDGShiftClosure.mapDGAdditiveClosure.obj M),
        dgMap_mapDGShiftClosure, mapDGShiftClosureHom_toShift]
    · rw [DGAdditiveClosure.dgHomEquiv_toShift_of_ne M n h,
        DGAdditiveClosure.dgHomEquiv_toShift_of_ne (F.mapDGShiftClosure.mapDGAdditiveClosure.obj M)
          n h, map_zero]

/-- The DG functor induced by `F` sends the comparison morphism `⊕ᵢ Xᵢ[rᵢ + n] ⟶ ⊕ᵢ Xᵢ[rᵢ]` to the
comparison morphism of the image. -/
theorem mapDGShiftClosure_mapDGAdditiveClosure_dgMap_fromShift
    (M : DGAdditiveClosure (DGShiftClosure C)) (n : ℤ) :
    F.mapDGShiftClosure.mapDGAdditiveClosure.dgMap n (DGAdditiveClosure.fromShift R M n) =
      DGAdditiveClosure.fromShift R (F.mapDGShiftClosure.mapDGAdditiveClosure.obj M) n :=
  DGAdditiveClosure.dgHom_ext R fun i j ↦ by
    rw [dgMap_mapDGAdditiveClosure, dgHomEquiv_mapDGAdditiveClosureHom]
    rcases eq_or_ne i j with rfl | h
    · rw [DGAdditiveClosure.dgHomEquiv_fromShift_self M n i,
        DGAdditiveClosure.dgHomEquiv_fromShift_self
          (F.mapDGShiftClosure.mapDGAdditiveClosure.obj M),
        dgMap_mapDGShiftClosure, mapDGShiftClosureHom_fromShift]
    · rw [DGAdditiveClosure.dgHomEquiv_fromShift_of_ne M n h,
        DGAdditiveClosure.dgHomEquiv_fromShift_of_ne
          (F.mapDGShiftClosure.mapDGAdditiveClosure.obj M) n h, map_zero]

end CategoryTheory.EnrichedFunctor
