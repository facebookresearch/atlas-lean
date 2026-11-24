/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Shift.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGAdditiveShift
public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedObject

/-!
# Shifts of twisted objects

Let `C` be a differential graded category.  The twisted objects `(⊕ᵢ Xᵢ[rᵢ], δ)` of the additive
closure of the shift closure of `C` are shifted summandwise: the shift by `n` is the twisted object
`(⊕ᵢ Xᵢ[rᵢ + n], δ)`, whose twisting matrix has the same entries as `δ`, viewed as morphisms of
`C`.  Since `Hom(Xᵢ[rᵢ + n], Xⱼ[rⱼ + n]) = Hom(Xᵢ, Xⱼ)[rⱼ - rᵢ] = Hom(Xᵢ[rᵢ], Xⱼ[rⱼ])` in the shift
closure, with the same differential and composition signs, this is the image of the twisted object
under the DG functor induced by the shift `X[r] ↦ X[r + n]` of the shift closure
(`MathlibExt.DGSource.DGShiftClosure.shiftFunctor`).  So the shift is a DG functor
`MathlibExt.DGSource.DGTwistedObject.shiftFunctor n`, which does not change the matrix entries of morphisms.

What makes `P⟦n⟧` the shift of `P` is a closed invertible morphism `P ⟶ P⟦n⟧` of degree `-n`:
composing with it identifies `Hom(Z, P⟦n⟧)` with `Hom(Z, P)[n]` and `Hom(P⟦n⟧, Z)` with
`Hom(P, Z)[-n]`.  It is the diagonal matrix `MathlibExt.DGSource.DGTwistedObject.toShift` whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`
(`MathlibExt.DGSource.DGShiftClosure.toShift`), that is, the comparison morphism
`MathlibExt.DGSource.DGAdditiveClosure.toShift` of the underlying objects.  The signs make it natural up to
the Koszul sign, `f ≫ σ_Q = (-1)^(n * p) • σ_P ≫ f⟦n⟧` for `f` of degree `p`
(`MathlibExt.DGSource.DGTwistedObject.dgComp_toShift`).  Applied to the twisting matrix, of degree one, this
says that `σ_P` is closed for the twisted differential `d σ + (-1)^n • σ ≫ δ⟦n⟧ - δ ≫ σ`.  Without
the signs it would not be: the identity entries alone would leave the error
`((-1)^n - (-1)^(n * (1 + rⱼ - rᵢ))) • δᵢⱼ` in the entry from `Xᵢ` to `Xⱼ`.  The diagonal matrix
`MathlibExt.DGSource.DGTwistedObject.fromShift` with the same entries is its inverse, of degree `n`.

The shifts do not compose strictly: `P⟦a⟧⟦b⟧` has summands `Xᵢ[rᵢ + a + b]` and `P⟦a + b⟧` has
summands `Xᵢ[rᵢ + (a + b)]`.  They are identified by closed degree-zero isomorphisms built from the
comparison morphisms: `MathlibExt.DGSource.DGTwistedObject.shiftAddHom P a b` is the composite
`P⟦a + b⟧ ⟶ P ⟶ P⟦b⟧ ⟶ P⟦a⟧⟦b⟧` whose last map is the shift by `b` of `P ⟶ P⟦a⟧`.  Composing
directly through `P ⟶ P⟦a⟧ ⟶ P⟦a⟧⟦b⟧` instead gives `(-1)^(a * b)` times `shiftAddHom P a b`
(`MathlibExt.DGSource.DGTwistedObject.shiftAddHom_eq_negOnePow_smul_dgComp`), by the Koszul-sign naturality of
the comparison morphisms.  This second description makes the associativity and unit coherences of
these isomorphisms a cancellation of comparison morphisms, the signs `(-1)^((a + b) * c + a * b)`
and `(-1)^(a * (b + c) + b * c)` agreeing.

In the same way the shifts commute up to the closed degree-zero isomorphism
`MathlibExt.DGSource.DGTwistedObject.shiftCommHom P a b`, the composite of comparison morphisms
`P⟦a⟧⟦b⟧ ⟶ P⟦a⟧ ⟶ P ⟶ P⟦b⟧ ⟶ P⟦b⟧⟦a⟧`.  The shift by `b` of the comparison morphism `P⟦a⟧ ⟶ P`
is `(-1)^(a * b)` times this isomorphism followed by the comparison morphism `P⟦b⟧⟦a⟧ ⟶ P⟦b⟧`
(`MathlibExt.DGSource.DGTwistedObject.dgMap_fromShift`); this is the sign by which the shift of a cone differs
from the cone of the shifted morphism.

Shifts are the second ingredient, with extensions (see
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedExtension.lean`), of the cone `(Q ⊕ P⟦1⟧, δ)` of a closed
degree-zero morphism `u : P ⟶ Q` of twisted objects, along the closed degree-one morphism
`P⟦1⟧ ⟶ P ⟶ Q`.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.shiftFunctor`: the DG functor shifting every summand of a twisted
  object by `n`.
* `MathlibExt.DGSource.DGTwistedObject.toShift` and `MathlibExt.DGSource.DGTwistedObject.fromShift`: the comparison
  morphisms `P ⟶ P⟦n⟧` of degree `-n` and `P⟦n⟧ ⟶ P` of degree `n`.
* `MathlibExt.DGSource.DGTwistedObject.shiftAddHom` and `MathlibExt.DGSource.DGTwistedObject.shiftAddInv`: the mutually
  inverse closed degree-zero morphisms `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` and `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧`.
* `MathlibExt.DGSource.DGTwistedObject.shiftCommHom`: the closed degree-zero isomorphism
  `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧`.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_toShift` and `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_fromShift`:
  the comparison morphisms are those of the underlying objects of the additive closure.
* `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_twist_shiftFunctor_obj` and
  `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_dgMap_shiftFunctor`: the shift does not change the matrix
  entries of the twist or of a morphism, as morphisms of `C`.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_toShift` and
  `MathlibExt.DGSource.DGTwistedObject.dgDifferential_fromShift`: the comparison morphisms are closed.
* `MathlibExt.DGSource.DGTwistedObject.dgComp_toShift_fromShift` and
  `MathlibExt.DGSource.DGTwistedObject.dgComp_fromShift_toShift`: they are mutually inverse (with `_assoc`
  forms for reassociated composites).
* `MathlibExt.DGSource.DGTwistedObject.dgComp_toShift` and `MathlibExt.DGSource.DGTwistedObject.dgComp_fromShift`: they
  are natural up to the Koszul sign, and `MathlibExt.DGSource.DGTwistedObject.toShift_dgComp_dgMap_assoc` and
  `MathlibExt.DGSource.DGTwistedObject.dgMap_dgComp_fromShift_assoc` are the sign-free forms for degree-zero
  morphisms.
* `MathlibExt.DGSource.DGTwistedObject.dgComp_shiftAddHom_shiftAddInv` and
  `MathlibExt.DGSource.DGTwistedObject.dgComp_shiftAddInv_shiftAddHom`: the comparisons of iterated shifts are
  inverse.
* `MathlibExt.DGSource.DGTwistedObject.dgMap_dgComp_shiftAddHom`: `shiftAddHom` is natural.
* `MathlibExt.DGSource.DGTwistedObject.shiftAddHom_assoc`, `MathlibExt.DGSource.DGTwistedObject.shiftAddHom_zero_add` and
  `MathlibExt.DGSource.DGTwistedObject.shiftAddHom_add_zero`: the associativity and unit coherences of
  `shiftAddHom`.
* `MathlibExt.DGSource.DGTwistedObject.dgComp_shiftCommHom_shiftCommHom`: `shiftCommHom P a b` and
  `shiftCommHom P b a` are inverse, and
  `MathlibExt.DGSource.DGTwistedObject.shiftCommHom_eq_dgComp_shiftAddInv` expresses `shiftCommHom` through
  the comparisons of iterated shifts.
* `MathlibExt.DGSource.DGTwistedObject.dgMap_fromShift`: the shift of a comparison morphism, and
  `MathlibExt.DGSource.DGTwistedObject.dgMap_fromShift_self` its form for the shift by its own degree, where
  `MathlibExt.DGSource.DGTwistedObject.shiftCommHom_self` makes the comparison of shifts the identity.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/- `matrixEquiv` is a local name for `MathlibExt.DGSource.DGAdditiveClosure.dgHomEquiv`, which identifies a
morphism of the additive closure with its matrix of entries; the unqualified name `dgHomEquiv`
refers to `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv` in this namespace. -/
open DGAdditiveClosure renaming dgHomEquiv → matrixEquiv

/-! ### The shift functor -/

/-- The DG functor shifting the twisted objects of the additive closure of the shift closure by
`n`: it sends `(⊕ᵢ Xᵢ[rᵢ], δ)` to `(⊕ᵢ Xᵢ[rᵢ + n], δ)`, the entries of the twisting matrix and of
every morphism being unchanged as morphisms of `C`. -/
-- This is reducible so that the summands of the shift of `P` are reducibly indexed by those of
-- `P`.
noncomputable abbrev shiftFunctor (n : ℤ) :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))
      (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) :=
  (DGShiftClosure.shiftFunctor R n).mapDGAdditiveClosure.mapDGTwistedObject

variable {R}

/-- The shift does not change the entries of the twisting matrix, as morphisms of `C`. -/
theorem dgHomEquiv_twist_shiftFunctor_obj (n : ℤ)
    (P : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (i j : P.obj.ι) :
    matrixEquiv R _ _ 1 ((shiftFunctor R n).obj P).twist i j =
      DGShiftClosure.shiftHomEquiv R _ _ n 1 (matrixEquiv R _ _ 1 P.twist i j) := by
  dsimp only [EnrichedFunctor.mapDGTwistedObjectObj]
  rw [EnrichedFunctor.dgMap_mapDGAdditiveClosure]
  exact (EnrichedFunctor.dgHomEquiv_mapDGAdditiveClosureHom _ P.twist i j).trans
    (DGShiftClosure.dgMap_shiftFunctor R n _)

/-- The shift does not change the entries of a morphism, as morphisms of `C`. -/
theorem dgHomEquiv_dgMap_shiftFunctor (n : ℤ)
    {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {p : ℤ} (f : DGHom R p P Q)
    (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ p (dgHomEquiv R _ _ p ((shiftFunctor R n).dgMap p f)) i j =
      DGShiftClosure.shiftHomEquiv R _ _ n p (matrixEquiv R _ _ p (dgHomEquiv R P Q p f) i j) := by
  rw [EnrichedFunctor.dgMap_mapDGTwistedObject, EnrichedFunctor.dgHomEquiv_mapDGTwistedObjectHom,
    EnrichedFunctor.dgMap_mapDGAdditiveClosure]
  exact (EnrichedFunctor.dgHomEquiv_mapDGAdditiveClosureHom _ _ i j).trans
    (DGShiftClosure.dgMap_shiftFunctor R n _)

/-- The shift of an object of the additive closure with the zero twist is the shifted object with
the zero twist. -/
theorem shiftFunctor_obj_ofObj (n : ℤ) (M : DGAdditiveClosure (DGShiftClosure C)) :
    (shiftFunctor R n).obj (ofObj R M) =
      ofObj R ⟨M.ι, fun i ↦ ⟨(M.X i).obj, (M.X i).shift + n⟩⟩ :=
  eq_ofObj_of_twist_eq_zero R (map_zero _)

/-! ### The comparison morphisms of twisted objects -/

variable (P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (n : ℤ)

/-- The comparison morphism `P ⟶ P⟦n⟧` of degree `-n`: the diagonal matrix whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`. -/
noncomputable def toShift : DGHom R (-n) P ((shiftFunctor R n).obj P) :=
  (dgHomEquiv R _ _ (-n)).symm (DGAdditiveClosure.toShift R P.obj n)

/-- The comparison morphism `P⟦n⟧ ⟶ P` of degree `n`: the diagonal matrix whose entry at the
summand `Xᵢ[rᵢ]` is `(-1)^(n * rᵢ)` times the identity of `Xᵢ`. -/
noncomputable def fromShift : DGHom R n ((shiftFunctor R n).obj P) P :=
  (dgHomEquiv R _ _ n).symm (DGAdditiveClosure.fromShift R P.obj n)

/-- The matrix of `P ⟶ P⟦n⟧` is the comparison morphism of the underlying objects. -/
@[simp]
theorem dgHomEquiv_toShift :
    dgHomEquiv R _ _ (-n) (toShift P n) = DGAdditiveClosure.toShift R P.obj n :=
  LinearEquiv.apply_symm_apply _ _

/-- The matrix of `P⟦n⟧ ⟶ P` is the inverse comparison morphism of the underlying objects. -/
@[simp]
theorem dgHomEquiv_fromShift :
    dgHomEquiv R _ _ n (fromShift P n) = DGAdditiveClosure.fromShift R P.obj n :=
  LinearEquiv.apply_symm_apply _ _

/-- **The comparison morphisms are natural up to the Koszul sign**: for `f : P ⟶ Q` of degree
`p`, `f` followed by `Q ⟶ Q⟦n⟧` is `(-1)^(n * p)` times `P ⟶ P⟦n⟧` followed by the shift of
`f`. -/
theorem dgComp_toShift {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {p m : ℤ} (f : DGHom R p P Q) (h : p + -n = m) :
    dgComp R f (toShift Q n) h =
      (n * p).negOnePow • dgComp R (toShift P n) ((shiftFunctor R n).dgMap p f) (by omega) :=
  (dgHomEquiv R _ _ _).injective <| by
    rw [map_zsmul_unit, dgHomEquiv_dgComp, dgHomEquiv_dgComp, dgHomEquiv_toShift,
      dgHomEquiv_toShift, EnrichedFunctor.dgMap_mapDGTwistedObject,
      EnrichedFunctor.dgHomEquiv_mapDGTwistedObjectHom,
      DGAdditiveClosure.dgComp_toShift]

/-- **The inverse comparison morphisms are natural up to the Koszul sign**: for `f : P ⟶ Q` of
degree `p`, the shift of `f` followed by `Q⟦n⟧ ⟶ Q` is `(-1)^(n * p)` times `P⟦n⟧ ⟶ P` followed
by `f`. -/
theorem dgComp_fromShift {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {p m : ℤ} (f : DGHom R p P Q) (h : p + n = m) :
    dgComp R ((shiftFunctor R n).dgMap p f) (fromShift Q n) h =
      (n * p).negOnePow • dgComp R (fromShift P n) f (by omega) :=
  (dgHomEquiv R _ _ _).injective <| by
    rw [map_zsmul_unit, dgHomEquiv_dgComp, dgHomEquiv_dgComp, dgHomEquiv_fromShift,
      dgHomEquiv_fromShift, EnrichedFunctor.dgMap_mapDGTwistedObject,
      EnrichedFunctor.dgHomEquiv_mapDGTwistedObjectHom,
      DGAdditiveClosure.dgComp_fromShift]

/-- **The comparison morphism `P ⟶ P⟦n⟧` is closed** for the twisted differential: by
naturality, `δ ≫ σ = (-1)^n • σ ≫ δ⟦n⟧`, which cancels the twisting terms of `D σ`. -/
@[simp↓]
theorem dgDifferential_toShift : dgDifferential R (-n) (toShift P n) = 0 :=
  (dgHomEquiv R _ _ (-n + 1)).injective <| by
    rw [dgHomEquiv_dgDifferential, map_zero, dgHomEquiv_toShift,
      DGAdditiveClosure.dgDifferential_toShift, DGAdditiveClosure.dgComp_toShift, mul_one,
      Int.negOnePow_neg, zero_add]
    exact sub_self _

/-- The comparison morphisms `P ⟶ P⟦n⟧ ⟶ P` compose to the identity of `P`. -/
@[simp↓]
theorem dgComp_toShift_fromShift :
    dgComp R (toShift P n) (fromShift P n) (neg_add_cancel n) = dgId R P :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, dgHomEquiv_toShift,
      dgHomEquiv_fromShift, DGAdditiveClosure.dgComp_toShift_fromShift]

/-- The comparison morphisms `P⟦n⟧ ⟶ P ⟶ P⟦n⟧` compose to the identity of `P⟦n⟧`. -/
@[simp↓]
theorem dgComp_fromShift_toShift :
    dgComp R (fromShift P n) (toShift P n) (add_neg_cancel n) =
      dgId R ((shiftFunctor R n).obj P) :=
  (dgHomEquiv R _ _ 0).injective <| by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, dgHomEquiv_toShift,
      dgHomEquiv_fromShift, DGAdditiveClosure.dgComp_fromShift_toShift]

/-- The comparison morphisms `P ⟶ P⟦n⟧ ⟶ P` followed by `x` compose to `x`. -/
@[simp↓]
theorem dgComp_toShift_fromShift_assoc
    {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {q m : ℤ} (x : DGHom R q P Z)
    (h : n + q = m) (h' : -n + m = q) :
    dgComp R (toShift P n) (dgComp R (fromShift P n) x h) h' = x := by
  rw [← dgComp_assoc R _ _ x (neg_add_cancel n) h (by omega), dgComp_toShift_fromShift,
    dgId_dgComp]

/-- The comparison morphisms `P⟦n⟧ ⟶ P ⟶ P⟦n⟧` followed by `x` compose to `x`. -/
@[simp↓]
theorem dgComp_fromShift_toShift_assoc
    {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {q m : ℤ}
    (x : DGHom R q ((shiftFunctor R n).obj P) Z) (h : -n + q = m) (h' : n + m = q) :
    dgComp R (fromShift P n) (dgComp R (toShift P n) x h) h' = x := by
  rw [← dgComp_assoc R _ _ x (add_neg_cancel n) h (by omega), dgComp_fromShift_toShift,
    dgId_dgComp]

/-- **The comparison morphisms are natural in degree zero**: for `f : P ⟶ Q` of degree zero,
`P ⟶ P⟦n⟧` followed by the shift of `f` and `x` is `f` followed by `Q ⟶ Q⟦n⟧` and `x`. -/
theorem toShift_dgComp_dgMap_assoc
    {P Q Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} (f : DGHom R 0 P Q)
    {q m : ℤ} (x : DGHom R q ((shiftFunctor R n).obj Q) Z) (h : -n + q = m) :
    dgComp R (toShift P n) (dgComp R ((shiftFunctor R n).dgMap 0 f) x (zero_add q)) h =
      dgComp R f (dgComp R (toShift Q n) x h) (zero_add m) := by
  rw [← dgComp_assoc R _ _ x (add_zero (-n)) (zero_add q) (by omega),
    ← dgComp_assoc R f _ x (zero_add (-n)) h (by omega), dgComp_toShift n f (zero_add (-n)),
    mul_zero, Int.negOnePow_zero, one_smul]

/-- **The inverse comparison morphisms are natural in degree zero**: for `f : P ⟶ Q` of degree
zero, the shift of `f` followed by `Q⟦n⟧ ⟶ Q` and `x` is `P⟦n⟧ ⟶ P` followed by `f` and `x`. -/
theorem dgMap_dgComp_fromShift_assoc
    {P Q Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} (f : DGHom R 0 P Q)
    {q m : ℤ} (x : DGHom R q Q Z) (h : n + q = m) :
    dgComp R ((shiftFunctor R n).dgMap 0 f) (dgComp R (fromShift Q n) x h) (zero_add m) =
      dgComp R (fromShift P n) (dgComp R f x (zero_add q)) h := by
  rw [← dgComp_assoc R _ _ x (zero_add n) h (by omega), dgComp_fromShift n f (zero_add n),
    mul_zero, Int.negOnePow_zero, one_smul,
    dgComp_assoc R _ f x (add_zero n) (zero_add q) (by omega)]

/-- The comparison morphism `P⟦n⟧ ⟶ P` is closed, as the inverse of a closed morphism. -/
@[simp↓]
theorem dgDifferential_fromShift : dgDifferential R n (fromShift P n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_toShift P n) (neg_add_cancel n)
    (dgComp_toShift_fromShift P n) (dgComp_fromShift_toShift P n)

/-! ### Degree bookkeeping

The coherences below compare composites of comparison morphisms whose degrees are integer
expressions such as `-a + -b` and `a + -(a + b)`, which agree only propositionally.  The general
rewriting rules `MathlibExt.DGSource.dgComp_assoc_eq_castDeg`, `MathlibExt.DGSource.castDeg_dgComp_eq_castDeg`,
`MathlibExt.DGSource.dgComp_castDeg_eq_castDeg` and `MathlibExt.DGSource.dgId_dgComp_eq_castDeg`, together with the
following rules for the comparison morphisms, bring such composites to a normal form: a degree
transport `castDeg` of a right-associated composite whose intermediate degrees are the sums of the
degrees of the factors.  Two composites of the same factors then agree up to the outer degree
transport.  The rules are applied with `simp -proj`, which keeps the shifted objects
`(shiftFunctor R n).obj P` folded so that the comparison lemmas about
`MathlibExt.DGSource.DGTwistedObject.toShift` and `MathlibExt.DGSource.DGTwistedObject.fromShift` keep matching. -/

section calculus

variable {P Q} {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}

private theorem dgComp_fromShift_toShift' (n : ℤ) {m : ℤ} (h : n + -n = m) :
    dgComp R (fromShift P n) (toShift P n) h = castDeg R (by omega) (dgId R _) := by
  obtain rfl : m = 0 := by omega
  rw [dgComp_fromShift_toShift, castDeg_self]

private theorem dgComp_toShift_fromShift' (n : ℤ) {m : ℤ} (h : -n + n = m) :
    dgComp R (toShift P n) (fromShift P n) h = castDeg R (by omega) (dgId R _) := by
  obtain rfl : m = 0 := by omega
  rw [dgComp_toShift_fromShift, castDeg_self]

private theorem dgComp_toShift_fromShift_assoc' (n : ℤ) {q m m' : ℤ} (x : DGHom R q P Z)
    (h : n + q = m) (h' : -n + m = m') :
    dgComp R (toShift P n) (dgComp R (fromShift P n) x h) h' = castDeg R (by omega) x := by
  obtain rfl : m' = q := by omega
  simpa only [castDeg_self] using dgComp_toShift_fromShift_assoc P n x h h'

private theorem dgComp_fromShift_toShift_assoc' (n : ℤ) {q m m' : ℤ}
    (x : DGHom R q ((shiftFunctor R n).obj P) Z) (h : -n + q = m) (h' : n + m = m') :
    dgComp R (fromShift P n) (dgComp R (toShift P n) x h) h' = castDeg R (by omega) x := by
  obtain rfl : m' = q := by omega
  simpa only [castDeg_self] using dgComp_fromShift_toShift_assoc P n x h h'

private theorem toShift_dgComp_dgMap (n : ℤ) (f : DGHom R 0 P Q) {m : ℤ} (h : -n + 0 = m) :
    dgComp R (toShift P n) ((shiftFunctor R n).dgMap 0 f) h =
      castDeg R (by omega) (dgComp R f (toShift Q n) rfl) := by
  subst h
  rw [dgComp_toShift n f rfl, mul_zero, Int.negOnePow_zero, one_smul,
    dgComp_eq_castDeg_dgComp R (n := 0 + -n), castDeg_castDeg, castDeg_self]

private theorem toShift_dgComp_dgMap_assoc' (n : ℤ) (f : DGHom R 0 P Q) {q m m' : ℤ}
    (x : DGHom R q ((shiftFunctor R n).obj Q) Z) (h : 0 + q = m) (h' : -n + m = m') :
    dgComp R (toShift P n) (dgComp R ((shiftFunctor R n).dgMap 0 f) x h) h' =
      castDeg R (by omega) (dgComp R f (dgComp R (toShift Q n) x rfl) rfl) := by
  subst h h'
  rw [← dgComp_assoc R _ _ x rfl rfl (by omega), toShift_dgComp_dgMap,
    castDeg_dgComp_eq_castDeg, dgComp_assoc_eq_castDeg, castDeg_castDeg]

private theorem dgMap_dgComp_fromShift_assoc' (n : ℤ) (f : DGHom R 0 P Q) {q m m' : ℤ}
    (x : DGHom R q Q Z) (h : n + q = m) (h' : 0 + m = m') :
    dgComp R ((shiftFunctor R n).dgMap 0 f) (dgComp R (fromShift Q n) x h) h' =
      castDeg R (by omega) (dgComp R (fromShift P n) (dgComp R f x rfl) rfl) := by
  subst h h'
  rw [← dgComp_assoc R _ _ x rfl rfl (by omega), dgComp_fromShift n f rfl, mul_zero,
    Int.negOnePow_zero, one_smul, dgComp_assoc_eq_castDeg]

end calculus

/-! ### The comparison of iterated shifts -/

section comparison

/-- The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧`, a closed degree-zero isomorphism: the comparison
morphisms `P⟦a + b⟧ ⟶ P ⟶ P⟦b⟧` followed by the shift by `b` of the comparison morphism
`P ⟶ P⟦a⟧`. -/
noncomputable def shiftAddHom (a b : ℤ) :
    DGHom R 0 ((shiftFunctor R (a + b)).obj P)
      ((shiftFunctor R b).obj ((shiftFunctor R a).obj P)) :=
  dgComp R (fromShift P (a + b))
    (dgComp R (toShift P b) ((shiftFunctor R b).dgMap (-a) (toShift P a)) (add_comm _ _))
    (by omega)

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧`, inverse to `MathlibExt.DGSource.DGTwistedObject.shiftAddHom`: the
shift by `b` of the comparison morphism `P⟦a⟧ ⟶ P` followed by the comparison morphisms
`P⟦b⟧ ⟶ P ⟶ P⟦a + b⟧`. -/
noncomputable def shiftAddInv (a b : ℤ) :
    DGHom R 0 ((shiftFunctor R b).obj ((shiftFunctor R a).obj P))
      ((shiftFunctor R (a + b)).obj P) :=
  dgComp R ((shiftFunctor R b).dgMap a (fromShift P a))
    (dgComp R (fromShift P b) (toShift P (a + b)) rfl) (by omega)

/-- The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` is `P⟦a + b⟧ ⟶ P ⟶ P⟦b⟧` followed by the shift of
`P ⟶ P⟦a⟧`. -/
theorem shiftAddHom_def (a b : ℤ) :
    shiftAddHom P a b = dgComp R (fromShift P (a + b))
      (dgComp R (toShift P b) ((shiftFunctor R b).dgMap (-a) (toShift P a)) (add_comm _ _))
      (by omega) :=
  (rfl)

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` is the shift of `P⟦a⟧ ⟶ P` followed by
`P⟦b⟧ ⟶ P ⟶ P⟦a + b⟧`. -/
theorem shiftAddInv_def (a b : ℤ) :
    shiftAddInv P a b = dgComp R ((shiftFunctor R b).dgMap a (fromShift P a))
      (dgComp R (fromShift P b) (toShift P (a + b)) rfl) (by omega) :=
  (rfl)

/-- Through `P ⟶ P⟦a⟧ ⟶ P⟦a⟧⟦b⟧` instead, the comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` acquires the
Koszul sign `(-1)^(a * b)`. -/
theorem shiftAddHom_eq_negOnePow_smul_dgComp (a b : ℤ) :
    shiftAddHom P a b = (a * b).negOnePow • dgComp R (fromShift P (a + b))
      (dgComp R (toShift P a) (toShift ((shiftFunctor R a).obj P) b) rfl) (by omega) := by
  rw [shiftAddHom_def, dgComp_toShift b (toShift P a) rfl, dgComp_units_smul]
  simp [smul_smul, mul_comm b a]

/-- Through `P⟦a⟧⟦b⟧ ⟶ P⟦a⟧ ⟶ P` instead, the comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` acquires the
Koszul sign `(-1)^(a * b)`. -/
theorem shiftAddInv_eq_negOnePow_smul_dgComp (a b : ℤ) :
    shiftAddInv P a b = (a * b).negOnePow • dgComp R (fromShift ((shiftFunctor R a).obj P) b)
      (dgComp R (fromShift P a) (toShift P (a + b)) rfl) (by omega) := by
  rw [shiftAddInv_def, ← dgComp_assoc R _ _ _ rfl rfl (by omega), dgComp_fromShift b _ rfl,
    units_smul_dgComp, dgComp_assoc R _ _ _ _ rfl (by omega), mul_comm b a]

/-- The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` is closed. -/
@[simp↓]
theorem dgDifferential_shiftAddHom (a b : ℤ) : dgDifferential R 0 (shiftAddHom P a b) = 0 := by
  simp -proj only [shiftAddHom_eq_negOnePow_smul_dgComp, map_zsmul_unit, dgDifferential_dgComp,
    dgDifferential_fromShift, dgDifferential_toShift, zero_dgComp, dgComp_zero, smul_zero,
    add_zero]

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` is closed. -/
@[simp↓]
theorem dgDifferential_shiftAddInv (a b : ℤ) : dgDifferential R 0 (shiftAddInv P a b) = 0 := by
  simp -proj only [shiftAddInv_eq_negOnePow_smul_dgComp, map_zsmul_unit, dgDifferential_dgComp,
    dgDifferential_fromShift, dgDifferential_toShift, zero_dgComp, dgComp_zero, smul_zero,
    add_zero]

/-- The comparisons `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftAddHom_shiftAddInv (a b : ℤ) :
    dgComp R (shiftAddHom P a b) (shiftAddInv P a b) (add_zero 0) = dgId R _ := by
  simp -proj only [shiftAddHom_eq_negOnePow_smul_dgComp, shiftAddInv_eq_negOnePow_smul_dgComp,
    units_smul_dgComp, dgComp_units_smul, smul_smul, Int.units_mul_self, one_smul,
    dgComp_assoc_eq_castDeg, dgComp_toShift_fromShift_assoc', dgComp_castDeg_eq_castDeg,
    castDeg_castDeg, dgComp_fromShift_toShift', castDeg_self]

/-- The comparisons `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftAddInv_shiftAddHom (a b : ℤ) :
    dgComp R (shiftAddInv P a b) (shiftAddHom P a b) (add_zero 0) = dgId R _ := by
  simp -proj only [shiftAddHom_eq_negOnePow_smul_dgComp, shiftAddInv_eq_negOnePow_smul_dgComp,
    units_smul_dgComp, dgComp_units_smul, smul_smul, Int.units_mul_self, one_smul,
    dgComp_assoc_eq_castDeg, dgComp_toShift_fromShift_assoc', dgComp_fromShift_toShift_assoc',
    dgComp_castDeg_eq_castDeg, castDeg_castDeg, dgComp_fromShift_toShift', castDeg_self]

variable {P} in
/-- **The comparison `P⟦a + b⟧ ⟶ P⟦a⟧⟦b⟧` is natural** in degree-zero morphisms `f : P ⟶ Q`. -/
theorem dgMap_dgComp_shiftAddHom {Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    (a b : ℤ) (f : DGHom R 0 P Q) :
    dgComp R ((shiftFunctor R (a + b)).dgMap 0 f) (shiftAddHom Q a b) (add_zero 0) =
      dgComp R (shiftAddHom P a b)
        ((shiftFunctor R b).dgMap 0 ((shiftFunctor R a).dgMap 0 f)) (add_zero 0) := by
  simp -proj only [shiftAddHom_eq_negOnePow_smul_dgComp, units_smul_dgComp, dgComp_units_smul,
    dgComp_assoc_eq_castDeg, dgMap_dgComp_fromShift_assoc', castDeg_castDeg,
    dgComp_castDeg_eq_castDeg, toShift_dgComp_dgMap_assoc', toShift_dgComp_dgMap]

/-- **Associativity of the comparisons**: `P⟦a + b + c⟧ ⟶ P⟦a + b⟧⟦c⟧ ⟶ P⟦a⟧⟦b⟧⟦c⟧` agrees with
`P⟦a + b + c⟧ ⟶ P⟦a + (b + c)⟧ ⟶ P⟦a⟧⟦b + c⟧ ⟶ P⟦a⟧⟦b⟧⟦c⟧`, whose first map is the comparison
`P⟦a + b + c⟧ ⟶ P ⟶ P⟦a + (b + c)⟧`. -/
theorem shiftAddHom_assoc (a b c : ℤ) :
    dgComp R (shiftAddHom P (a + b) c) ((shiftFunctor R c).dgMap 0 (shiftAddHom P a b))
        (add_zero 0) =
      dgComp R (dgComp R (fromShift P (a + b + c)) (toShift P (a + (b + c))) (by omega))
        (dgComp R (shiftAddHom P a (b + c)) (shiftAddHom ((shiftFunctor R a).obj P) b c)
          (add_zero 0)) (add_zero 0) := by
  rw [shiftAddHom_eq_negOnePow_smul_dgComp P (a + b) c]
  simp -proj only [units_smul_dgComp, dgComp_assoc_eq_castDeg, toShift_dgComp_dgMap,
    dgComp_castDeg_eq_castDeg, castDeg_castDeg]
  simp -proj only [shiftAddHom_eq_negOnePow_smul_dgComp, units_smul_dgComp, dgComp_units_smul,
    smul_smul, dgComp_assoc_eq_castDeg, dgComp_toShift_fromShift_assoc', dgComp_castDeg_eq_castDeg,
    castDeg_castDeg, map_zsmul_unit]
  congr 1
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 1
  ring

/-- **Left unit law of the comparisons**: `P⟦0 + n⟧ ⟶ P⟦0⟧⟦n⟧` is the comparison
`P⟦0 + n⟧ ⟶ P ⟶ P⟦n⟧` followed by the shift by `n` of `P ⟶ P⟦0⟧`. -/
theorem shiftAddHom_zero_add (n : ℤ) :
    shiftAddHom P 0 n =
      dgComp R (dgComp R (fromShift P (0 + n)) (toShift P n) (by omega))
        ((shiftFunctor R n).dgMap 0 (toShift P 0)) (add_zero 0) := by
  simp -proj only [shiftAddHom_eq_negOnePow_smul_dgComp, dgComp_assoc_eq_castDeg,
    toShift_dgComp_dgMap, dgComp_castDeg_eq_castDeg, castDeg_castDeg, zero_mul,
    Int.negOnePow_zero, one_smul]
  exact dgComp_eq_castDeg_dgComp R _ _ _

/-- **Right unit law of the comparisons**: `P⟦n + 0⟧ ⟶ P⟦n⟧⟦0⟧` is the comparison
`P⟦n + 0⟧ ⟶ P ⟶ P⟦n⟧` followed by `P⟦n⟧ ⟶ P⟦n⟧⟦0⟧`. -/
theorem shiftAddHom_add_zero (n : ℤ) :
    shiftAddHom P n 0 =
      dgComp R (dgComp R (fromShift P (n + 0)) (toShift P n) (by omega))
        (toShift ((shiftFunctor R n).obj P) 0) (add_zero 0) := by
  simp -proj only [shiftAddHom_eq_negOnePow_smul_dgComp, dgComp_assoc_eq_castDeg, mul_zero,
    Int.negOnePow_zero, one_smul]
  exact dgComp_eq_castDeg_dgComp R _ _ _

end comparison

/-! ### The commutation of shifts -/

section commutation

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧`, a closed degree-zero isomorphism: the comparison
morphisms `P⟦a⟧⟦b⟧ ⟶ P⟦a⟧ ⟶ P ⟶ P⟦b⟧ ⟶ P⟦b⟧⟦a⟧`. -/
noncomputable def shiftCommHom (a b : ℤ) :
    DGHom R 0 ((shiftFunctor R b).obj ((shiftFunctor R a).obj P))
      ((shiftFunctor R a).obj ((shiftFunctor R b).obj P)) :=
  dgComp R (fromShift ((shiftFunctor R a).obj P) b)
    (dgComp R (fromShift P a)
      (dgComp R (toShift P b) (toShift ((shiftFunctor R b).obj P) a) rfl) rfl) (by omega)

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧` is `P⟦a⟧⟦b⟧ ⟶ P⟦a⟧ ⟶ P ⟶ P⟦b⟧ ⟶ P⟦b⟧⟦a⟧`. -/
theorem shiftCommHom_def (a b : ℤ) :
    shiftCommHom P a b = dgComp R (fromShift ((shiftFunctor R a).obj P) b)
      (dgComp R (fromShift P a)
        (dgComp R (toShift P b) (toShift ((shiftFunctor R b).obj P) a) rfl) rfl) (by omega) :=
  (rfl)

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧` is closed. -/
@[simp↓]
theorem dgDifferential_shiftCommHom (a b : ℤ) : dgDifferential R 0 (shiftCommHom P a b) = 0 := by
  simp -proj only [shiftCommHom_def, dgDifferential_dgComp, dgDifferential_fromShift,
    dgDifferential_toShift, zero_dgComp, dgComp_zero, smul_zero, add_zero]

/-- The comparisons `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧ ⟶ P⟦a⟧⟦b⟧` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftCommHom_shiftCommHom (a b : ℤ) :
    dgComp R (shiftCommHom P a b) (shiftCommHom P b a) (add_zero 0) = dgId R _ := by
  simp -proj only [shiftCommHom_def, dgComp_assoc_eq_castDeg, dgComp_toShift_fromShift_assoc',
    dgComp_fromShift_toShift_assoc', dgComp_castDeg_eq_castDeg, castDeg_castDeg,
    dgComp_fromShift_toShift', castDeg_self]

/-- The comparisons `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧ ⟶ P⟦a⟧⟦b⟧` followed by `x` are `x`. -/
@[simp↓]
theorem dgComp_shiftCommHom_shiftCommHom_assoc (a b : ℤ)
    {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {m : ℤ}
    (x : DGHom R m ((shiftFunctor R b).obj ((shiftFunctor R a).obj P)) Z) :
    dgComp R (shiftCommHom P a b) (dgComp R (shiftCommHom P b a) x (zero_add m)) (zero_add m) =
      x := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add m) (by omega),
    dgComp_shiftCommHom_shiftCommHom, dgId_dgComp]

/-- A sign times the comparison `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧`, followed by the same sign times the
comparison `P⟦b⟧⟦a⟧ ⟶ P⟦a⟧⟦b⟧` and then `x`, is `x`. -/
theorem units_smul_dgComp_shiftCommHom_units_smul_dgComp_shiftCommHom (ε : ℤˣ) (a b : ℤ)
    {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {m : ℤ}
    (x : DGHom R m ((shiftFunctor R b).obj ((shiftFunctor R a).obj P)) Z) :
    ε • dgComp R (shiftCommHom P a b) (ε • dgComp R (shiftCommHom P b a) x (zero_add m))
      (zero_add m) = x := by
  rw [dgComp_units_smul, smul_smul, Int.units_mul_self, one_smul,
    dgComp_shiftCommHom_shiftCommHom_assoc]

/-- The comparison `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧` is the comparison `P⟦a⟧⟦b⟧ ⟶ P⟦a + b⟧`, followed by the
comparison `P⟦a + b⟧ ⟶ P ⟶ P⟦b + a⟧` and the comparison `P⟦b + a⟧ ⟶ P⟦b⟧⟦a⟧`. -/
theorem shiftCommHom_eq_dgComp_shiftAddInv (a b : ℤ) :
    shiftCommHom P a b = dgComp R (shiftAddInv P a b)
      (dgComp R (dgComp R (fromShift P (a + b)) (toShift P (b + a)) (by omega))
        (shiftAddHom P b a) (add_zero 0)) (add_zero 0) := by
  simp -proj only [shiftCommHom_def, shiftAddHom_eq_negOnePow_smul_dgComp,
    shiftAddInv_eq_negOnePow_smul_dgComp, units_smul_dgComp, dgComp_units_smul, map_zsmul_unit,
    smul_smul, mul_comm b a, Int.units_mul_self, one_smul, dgComp_assoc_eq_castDeg,
    dgComp_toShift_fromShift_assoc', dgComp_castDeg_eq_castDeg, castDeg_castDeg]
  exact dgComp_eq_castDeg_dgComp R _ _ _

/-- **The shift of a comparison morphism**: the shift by `b` of the comparison morphism
`P⟦a⟧ ⟶ P` is `(-1)^(a * b)` times the comparison `P⟦a⟧⟦b⟧ ⟶ P⟦b⟧⟦a⟧` followed by the
comparison morphism `P⟦b⟧⟦a⟧ ⟶ P⟦b⟧`. -/
theorem dgMap_fromShift (a b : ℤ) :
    (shiftFunctor R b).dgMap a (fromShift P a) =
      (a * b).negOnePow • dgComp R (shiftCommHom P a b)
        (fromShift ((shiftFunctor R b).obj P) a) (zero_add a) := by
  -- After composing with `P⟦b⟧ ⟶ P ⟶ P⟦b⟧`, the naturality of `P⟦b⟧ ⟶ P` applies to the shift
  -- of `P⟦a⟧ ⟶ P`.
  rw [← dgComp_dgId R ((shiftFunctor R b).dgMap a (fromShift P a)),
    ← dgComp_fromShift_toShift P b,
    ← dgComp_assoc R _ _ _ rfl (add_neg_cancel b) (by omega),
    dgComp_fromShift b (fromShift P a) rfl, units_smul_dgComp, mul_comm b a]
  congr 1
  simp -proj only [shiftCommHom_def, dgComp_assoc_eq_castDeg, dgComp_castDeg_eq_castDeg,
    castDeg_castDeg, dgComp_toShift_fromShift', dgComp_dgId_eq_castDeg]

/-- The comparison `P⟦a⟧⟦a⟧ ⟶ P⟦a⟧⟦a⟧` exchanging two equal shifts is the identity. -/
@[simp↓]
theorem shiftCommHom_self (a : ℤ) : shiftCommHom P a a = dgId R _ := by
  simp -proj only [shiftCommHom_def, dgComp_fromShift_toShift_assoc', dgComp_castDeg_eq_castDeg,
    castDeg_castDeg, dgComp_fromShift_toShift', castDeg_self]

/-- **The shift of a comparison morphism by its own degree**: the shift by `a` of the comparison
morphism `P⟦a⟧ ⟶ P` is `(-1)^(a * a)` times the comparison morphism `P⟦a⟧⟦a⟧ ⟶ P⟦a⟧`. -/
theorem dgMap_fromShift_self (a : ℤ) :
    (shiftFunctor R a).dgMap a (fromShift P a) =
      (a * a).negOnePow • fromShift ((shiftFunctor R a).obj P) a := by
  rw [dgMap_fromShift, shiftCommHom_self, dgId_dgComp]

end commutation

end DGTwistedObject

end MathlibExt.DGSource
