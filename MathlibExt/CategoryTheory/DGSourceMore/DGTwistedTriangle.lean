/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Triangle.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedCone
public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedHomotopyShift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Cone triangles in the homotopy category of twisted objects

Let `C` be a differential graded category and let `H⁰` be the homotopy category of the twisted
objects of the additive closure of the shift closure of `C`, with the shift of
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedHomotopyShift.lean`.  This file equips `H⁰` with the cone
triangles of Bondal and Kapranov as distinguished triangles, and proves the axioms of a
pretriangulated category for them, except for the converse half of the rotation axiom.  The
twisting matrices of the objects of `H⁰` are not required to be one-sided, so `H⁰` contains, and is
in general larger than, the pretriangulated envelope of Bondal and Kapranov, which consists of the
one-sided twisted objects.

A closed degree-zero morphism `u : P ⟶ Q` has the **cone triangle**
`P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` (`MathlibExt.DGSource.DGTwistedObject.coneTriangle`), formed by the classes of `u`,
of the inclusion of `Q` into the cone and of the projection of the cone onto `P⟦1⟧`.  A triangle
of `H⁰` is **distinguished** when it is isomorphic to a cone triangle
(`MathlibExt.DGSource.DGTwistedObject.distinguishedTriangles`).

* `H⁰` has a zero object, a twisted object with no summands
  (`MathlibExt.DGSource.DGTwistedObject.isZero_of_isEmpty`).  The contractible triangle
  `X ⟶ X ⟶ 0 ⟶ X⟦1⟧` is isomorphic to the cone triangle of the identity, since `Cone(id)` is
  contractible.
* Every morphism of `H⁰` is the class of a closed morphism, so it is the base of its cone
  triangle.
* Cones are functorial in homotopy-commutative squares: closed `a : P ⟶ P'`, `b : Q ⟶ Q'` and a
  degree `-1` morphism `k` with `d k = u ≫ b - a ≫ u'` induce the closed morphism
  `cone u ⟶ cone u'` (`MathlibExt.DGSource.DGTwistedObject.coneHomOfHomotopy`) which is `b` on `Q`, the shift
  of `a` on `P⟦1⟧`, and minus `P⟦1⟧ ⟶ P` followed by `k` in the block from `P⟦1⟧` to `Q'`.  Hence
  a commutative square between the bases of two distinguished triangles extends to a morphism of
  triangles.
* The rotation `Q ⟶ cone u ⟶ P⟦1⟧ ⟶ Q⟦1⟧` of the cone triangle, whose last morphism is minus the
  shift of `u`, is isomorphic to the cone triangle of the inclusion `v : Q ⟶ cone u`.  The
  comparison `P⟦1⟧ ⟶ cone v` (`MathlibExt.DGSource.DGTwistedObject.coneRotateHom`) is the inclusion of `P⟦1⟧`
  into `cone u`, plus minus the shift of `u` into `Q⟦1⟧`; the projection
  `cone v ⟶ cone u ⟶ P⟦1⟧` is a strict left inverse, and a right inverse up to the homotopy given
  by the projections onto `Q`, the comparison morphism `Q ⟶ Q⟦1⟧` and the inclusion of `Q⟦1⟧`.

The converse half of the rotation axiom, that a triangle whose rotation is distinguished is
distinguished, is proved in `MathlibExt/CategoryTheory/DGSourceMore/DGTwistedPretriangulated.lean`, which
assembles the pretriangulated structure.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.coneTriangle`: the cone triangle of a closed degree-zero morphism.
* `MathlibExt.DGSource.DGTwistedObject.coneHomOfHomotopy` and
  `MathlibExt.DGSource.DGTwistedObject.coneTriangleHomOfHomotopy`: the morphisms of cones and of cone
  triangles induced by a homotopy-commutative square.
* `MathlibExt.DGSource.DGTwistedObject.coneRotateIso` and `MathlibExt.DGSource.DGTwistedObject.coneTriangleRotateIso`:
  the isomorphism `P⟦1⟧ ≅ cone (Q ⟶ cone u)` and the induced isomorphism between the rotated cone
  triangle and a cone triangle.
* `MathlibExt.DGSource.DGTwistedObject.distinguishedTriangles`: the triangles isomorphic to cone triangles.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_coneHomOfHomotopy` and
  `MathlibExt.DGSource.DGTwistedObject.dgDifferential_coneHomOfHomotopy_zero`: homotopy-commutative and
  strictly commutative squares induce closed morphisms of cones.
* `MathlibExt.DGSource.DGTwistedObject.isomorphic_distinguished`,
  `MathlibExt.DGSource.DGTwistedObject.contractible_distinguished`,
  `MathlibExt.DGSource.DGTwistedObject.distinguished_cocone_triangle` and
  `MathlibExt.DGSource.DGTwistedObject.complete_distinguished_triangle_morphism`: four of the axioms of a
  pretriangulated category, in the form of the fields of
  `CategoryTheory.Pretriangulated`.
* `MathlibExt.DGSource.DGTwistedObject.rotate_mem_distinguishedTriangles`: the rotation of a distinguished
  triangle is distinguished.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, whose distinguished triangles of
  the homotopy category of cochain complexes, and whose proofs of the axioms from functoriality
  of mapping cones, are followed here.
-/

public section

open CategoryTheory Limits Pretriangulated

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

open DGHomotopyCategory

variable {R : Type v} [CommRing R]

variable {C : Type u} [DGCategory R C]

/-! ### The triangle of a cone -/

section coneTriangle

variable {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}

/-- The **cone triangle** `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` of a closed degree-zero morphism `u` of
twisted objects, in the homotopy category: the morphisms are the classes of `u`, of the inclusion
of `Q` into the cone, and of the projection of the cone onto `P⟦1⟧`. -/
-- The body is exposed so that the objects of the triangle are definitionally those of `u` and of
-- its cone, as the types of the morphisms in `MathlibExt.DGSource.DGTwistedObject.coneTriangle_mor₁` and its
-- companions require.
@[expose]
noncomputable def coneTriangle (u : DGHom R 0 P Q) (hu : dgDifferential R 0 u = 0) :
    Triangle (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :=
  Triangle.mk (homOf R u ((mem_dgCycles R).mpr hu))
    (homOf R (extensionInl R (dgDifferential_coneMorphism hu))
      ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)))
    (homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
      ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)))

variable (u : DGHom R 0 P Q) (hu : dgDifferential R 0 u = 0)

@[simp]
theorem coneTriangle_obj₁ : (coneTriangle u hu).obj₁ = DGHomotopyCategory.of R P :=
  (rfl)

@[simp]
theorem coneTriangle_obj₂ : (coneTriangle u hu).obj₂ = DGHomotopyCategory.of R Q :=
  (rfl)

@[simp]
theorem coneTriangle_obj₃ : (coneTriangle u hu).obj₃ = DGHomotopyCategory.of R (cone u hu) :=
  (rfl)

@[simp]
theorem coneTriangle_mor₁ : (coneTriangle u hu).mor₁ = homOf R u ((mem_dgCycles R).mpr hu) :=
  (rfl)

@[simp]
theorem coneTriangle_mor₂ :
    (coneTriangle u hu).mor₂ = homOf R (extensionInl R (dgDifferential_coneMorphism hu))
      ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) :=
  (rfl)

@[simp]
theorem coneTriangle_mor₃ :
    (coneTriangle u hu).mor₃ = homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
      ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) :=
  (rfl)

end coneTriangle

/-! ### Morphisms of cones -/

section coneHom

variable {P Q P' Q' : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
  {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0)
  {u' : DGHom R 0 P' Q'} (hu' : dgDifferential R 0 u' = 0)

/-- The degree-zero morphism `cone u ⟶ cone u'` induced by degree-zero morphisms `a : P ⟶ P'`,
`b : Q ⟶ Q'` and a degree `-1` morphism `k : P ⟶ Q'`: `b` on the summand `Q`, the shift of `a`
on the summand `P⟦1⟧`, and minus `P⟦1⟧ ⟶ P` followed by `k` in the block from `P⟦1⟧` to `Q'`.
It is closed when `a` and `b` are closed and `d k = u ≫ b - a ≫ u'`
(`MathlibExt.DGSource.DGTwistedObject.dgDifferential_coneHomOfHomotopy`). -/
noncomputable def coneHomOfHomotopy (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') : DGHom R 0 (cone u hu) (cone u' hu') :=
  dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
      (dgComp R b (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0)) (add_zero 0) +
    dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
      (dgComp R ((shiftFunctor R 1).dgMap 0 a)
        (extensionInr R (dgDifferential_coneMorphism hu')) (add_zero 0)) (add_zero 0) +
    dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
      (dgComp R (-dgComp R (fromShift P 1) k (add_neg_cancel 1))
        (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0)) (add_zero 0)

theorem coneHomOfHomotopy_def (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') :
    coneHomOfHomotopy hu hu' a b k =
      dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
          (dgComp R b (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0))
          (add_zero 0) +
        dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
          (dgComp R ((shiftFunctor R 1).dgMap 0 a)
            (extensionInr R (dgDifferential_coneMorphism hu')) (add_zero 0)) (add_zero 0) +
        dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
          (dgComp R (-dgComp R (fromShift P 1) k (add_neg_cancel 1))
            (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0)) (add_zero 0) :=
  (rfl)

/-- **The morphism of cones induced by a homotopy-commutative square is closed**: if `a` and `b`
are closed and `d k = u ≫ b - a ≫ u'`, then the differential of
`MathlibExt.DGSource.DGTwistedObject.coneHomOfHomotopy` vanishes. -/
theorem dgDifferential_coneHomOfHomotopy {a : DGHom R 0 P P'} {b : DGHom R 0 Q Q'}
    {k : DGHom R (-1) P Q'} (ha : dgDifferential R 0 a = 0) (hb : dgDifferential R 0 b = 0)
    (hk : dgDifferential R (-1) k = dgComp R u b (add_zero 0) - dgComp R a u' (add_zero 0)) :
    dgDifferential R 0 (coneHomOfHomotopy hu hu' a b k) = 0 := by
  have ha' : dgDifferential R 0 ((shiftFunctor R 1).dgMap 0 a) = 0 :=
    (shiftFunctor R 1).dgDifferential_dgMap_eq_zero ha
  -- After the Leibniz rule, every term is the projection onto `P⟦1⟧` followed by a degree-one
  -- morphism `P⟦1⟧ ⟶ cone u'`; these are brought to the form `P⟦1⟧ ⟶ P ⟶ Q' ⟶ cone u'`.
  have h₁ : dgComp R (dgComp R (extensionSnd R (dgDifferential_coneMorphism hu)) (coneMorphism R u)
        (zero_add 1)) (dgComp R b (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0))
        (add_zero 1) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
        (dgComp R (fromShift P 1) (dgComp R (dgComp R u b (add_zero 0))
          (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0)) (add_zero 1))
        (zero_add 1) := by
    rw [dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega), dgComp_coneMorphism,
      dgComp_assoc R u b _ (add_zero 0) (add_zero 0) (by omega)]
  have h₂ : dgComp R ((shiftFunctor R 1).dgMap 0 a)
        (dgComp R (coneMorphism R u') (extensionInl R (dgDifferential_coneMorphism hu'))
          (add_zero 1)) (zero_add 1) =
      dgComp R (fromShift P 1) (dgComp R (dgComp R a u' (add_zero 0))
        (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0)) (add_zero 1) := by
    rw [dgComp_coneMorphism, dgMap_dgComp_fromShift_assoc,
      dgComp_assoc R a u' _ (add_zero 0) (add_zero 0) (by omega)]
  have h₃ (x : DGHom R 0 P Q') : dgComp R (dgComp R (fromShift P 1) x (add_zero 1))
        (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 1) =
      dgComp R (fromShift P 1) (dgComp R x (extensionInl R (dgDifferential_coneMorphism hu'))
        (add_zero 0)) (add_zero 1) :=
    dgComp_assoc R _ _ _ (add_zero 1) (add_zero 0) (by omega)
  simp -proj only [coneHomOfHomotopy_def, map_add, map_neg, dgDifferential_dgComp,
    dgDifferential_extensionFst, dgDifferential_extensionSnd, dgDifferential_extensionInl,
    dgDifferential_extensionInr, dgDifferential_fromShift, ha', hb, hk, zero_dgComp, dgComp_zero,
    smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul, Int.negOnePow_one,
    Units.neg_smul, sub_eq_add_neg, neg_dgComp, dgComp_neg, dgComp_add, add_dgComp, h₁, h₂, h₃]
  abel

/-- **A strictly commutative square induces a closed morphism of cones**: if `a` and `b` are closed
and `u ≫ b = a ≫ u'`, then the morphism of cones induced by `a` and `b` with zero homotopy is
closed. -/
theorem dgDifferential_coneHomOfHomotopy_zero {a : DGHom R 0 P P'} {b : DGHom R 0 Q Q'}
    (ha : dgDifferential R 0 a = 0) (hb : dgDifferential R 0 b = 0)
    (h : dgComp R u b (add_zero 0) = dgComp R a u' (add_zero 0)) :
    dgDifferential R 0 (coneHomOfHomotopy hu hu' a b 0) = 0 :=
  dgDifferential_coneHomOfHomotopy hu hu' ha hb (by rw [map_zero, h, sub_self])

/-- The inclusion of `Q` into `cone u` followed by the morphism of cones induced by `a`, `b` and
`k` is `b` followed by the inclusion of `Q'` into `cone u'`. -/
@[simp↓]
theorem dgComp_extensionInl_coneHomOfHomotopy (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') :
    dgComp R (extensionInl R (dgDifferential_coneMorphism hu)) (coneHomOfHomotopy hu hu' a b k)
        (add_zero 0) =
      dgComp R b (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0) := by
  simp only [coneHomOfHomotopy_def, dgComp_add, dgComp_extensionInl_extensionFst_assoc,
    dgComp_extensionInl_extensionSnd_assoc, add_zero]

/-- The inclusion of `Q` into `cone u` followed by the morphism of cones induced by `a`, `b` and
`k` and then `x` is `b` followed by the inclusion of `Q'` into `cone u'` and then `x`. -/
@[simp↓]
theorem dgComp_extensionInl_coneHomOfHomotopy_assoc (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {n : ℤ}
    (x : DGHom R n (cone u' hu') Z) :
    dgComp R (extensionInl R (dgDifferential_coneMorphism hu))
        (dgComp R (coneHomOfHomotopy hu hu' a b k) x (zero_add n)) (zero_add n) =
      dgComp R b (dgComp R (extensionInl R (dgDifferential_coneMorphism hu')) x (zero_add n))
        (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInl_coneHomOfHomotopy,
    dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega)]

/-- The morphism of cones induced by `a`, `b` and `k` followed by the projection of `cone u'`
onto `P'⟦1⟧` is the projection of `cone u` onto `P⟦1⟧` followed by the shift of `a`. -/
@[simp↓]
theorem dgComp_coneHomOfHomotopy_extensionSnd (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') :
    dgComp R (coneHomOfHomotopy hu hu' a b k) (extensionSnd R (dgDifferential_coneMorphism hu'))
        (add_zero 0) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism hu)) ((shiftFunctor R 1).dgMap 0 a)
        (add_zero 0) := by
  simp only [coneHomOfHomotopy_def, add_dgComp,
    dgComp_assoc R _ _ (extensionSnd R (dgDifferential_coneMorphism hu')) (add_zero 0)
      (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, dgComp_dgId,
    zero_add, add_zero]

/-- The morphism of cones induced by `a`, `b` and `k` followed by the projection of `cone u'`
onto `P'⟦1⟧` and then `x` is the projection of `cone u` onto `P⟦1⟧` followed by the shift of `a`
and then `x`. -/
@[simp↓]
theorem dgComp_coneHomOfHomotopy_extensionSnd_assoc (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {n : ℤ}
    (x : DGHom R n ((shiftFunctor R 1).obj P') Z) :
    dgComp R (coneHomOfHomotopy hu hu' a b k)
        (dgComp R (extensionSnd R (dgDifferential_coneMorphism hu')) x (zero_add n)) (zero_add n) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
        (dgComp R ((shiftFunctor R 1).dgMap 0 a) x (zero_add n)) (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_coneHomOfHomotopy_extensionSnd,
    dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega)]

/-- The inclusion of `P⟦1⟧` into `cone u` followed by the morphism of cones induced by `a`, `b`
and `k` is the shift of `a` followed by the inclusion of `P'⟦1⟧` into `cone u'`, minus
`P⟦1⟧ ⟶ P` followed by `k` and the inclusion of `Q'` into `cone u'`. -/
@[simp↓]
theorem dgComp_extensionInr_coneHomOfHomotopy (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') :
    dgComp R (extensionInr R (dgDifferential_coneMorphism hu)) (coneHomOfHomotopy hu hu' a b k)
        (add_zero 0) =
      dgComp R ((shiftFunctor R 1).dgMap 0 a) (extensionInr R (dgDifferential_coneMorphism hu'))
          (add_zero 0) -
        dgComp R (dgComp R (fromShift P 1) k (add_neg_cancel 1))
          (extensionInl R (dgDifferential_coneMorphism hu')) (add_zero 0) := by
  simp only [coneHomOfHomotopy_def, dgComp_add, dgComp_extensionInr_extensionFst_assoc,
    dgComp_extensionInr_extensionSnd_assoc, zero_add, neg_dgComp, sub_eq_add_neg]

/-- The inclusion of `P⟦1⟧` into `cone u`, followed by the morphism of cones induced by `a` and
`b` with zero homotopy and then `x`, is the shift of `a` followed by the inclusion of `P'⟦1⟧` into
`cone u'` and then `x`. -/
@[simp↓]
theorem dgComp_extensionInr_coneHomOfHomotopy_zero_assoc (a : DGHom R 0 P P')
    (b : DGHom R 0 Q Q') {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {n : ℤ}
    (x : DGHom R n (cone u' hu') Z) :
    dgComp R (extensionInr R (dgDifferential_coneMorphism hu))
        (dgComp R (coneHomOfHomotopy hu hu' a b 0) x (zero_add n)) (zero_add n) =
      dgComp R ((shiftFunctor R 1).dgMap 0 a)
        (dgComp R (extensionInr R (dgDifferential_coneMorphism hu')) x (zero_add n))
        (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInr_coneHomOfHomotopy, dgComp_zero, zero_dgComp, sub_zero,
    dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega)]

/-- The morphism of cones induced by `a`, `b` and `k` followed by the projection of `cone u'`
onto `Q'` is the projection of `cone u` onto `Q` followed by `b`, minus the projection onto
`P⟦1⟧` followed by `P⟦1⟧ ⟶ P` and `k`. -/
@[simp↓]
theorem dgComp_coneHomOfHomotopy_extensionFst (a : DGHom R 0 P P') (b : DGHom R 0 Q Q')
    (k : DGHom R (-1) P Q') :
    dgComp R (coneHomOfHomotopy hu hu' a b k) (extensionFst R (dgDifferential_coneMorphism hu'))
        (add_zero 0) =
      dgComp R (extensionFst R (dgDifferential_coneMorphism hu)) b (add_zero 0) -
        dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
          (dgComp R (fromShift P 1) k (add_neg_cancel 1)) (add_zero 0) := by
  simp only [coneHomOfHomotopy_def, add_dgComp,
    dgComp_assoc R _ _ (extensionFst R (dgDifferential_coneMorphism hu')) (add_zero 0)
      (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionFst, dgComp_extensionInr_extensionFst, dgComp_zero, dgComp_dgId,
    add_zero, neg_dgComp, dgComp_neg, sub_eq_add_neg]

/-- The morphism of cones induced by `a` and `b` with zero homotopy, followed by the projection of
`cone u'` onto `Q'` and then `x`, is the projection of `cone u` onto `Q` followed by `b` and then
`x`. -/
@[simp↓]
theorem dgComp_coneHomOfHomotopy_zero_extensionFst_assoc (a : DGHom R 0 P P')
    (b : DGHom R 0 Q Q') {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {n : ℤ}
    (x : DGHom R n Q' Z) :
    dgComp R (coneHomOfHomotopy hu hu' a b 0)
        (dgComp R (extensionFst R (dgDifferential_coneMorphism hu')) x (zero_add n)) (zero_add n) =
      dgComp R (extensionFst R (dgDifferential_coneMorphism hu)) (dgComp R b x (zero_add n))
        (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_coneHomOfHomotopy_extensionFst, dgComp_zero, dgComp_zero, sub_zero,
    dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega)]

/-- **The morphism of cone triangles induced by a homotopy-commutative square**: closed morphisms
`a : P ⟶ P'` and `b : Q ⟶ Q'` with `d k = u ≫ b - a ≫ u'` give the morphism of triangles
`(a, b, MathlibExt.DGSource.DGTwistedObject.coneHomOfHomotopy a b k)` from the cone triangle of `u` to the
cone triangle of `u'`. -/
noncomputable def coneTriangleHomOfHomotopy {a : DGHom R 0 P P'} {b : DGHom R 0 Q Q'}
    {k : DGHom R (-1) P Q'} (ha : dgDifferential R 0 a = 0) (hb : dgDifferential R 0 b = 0)
    (hk : dgDifferential R (-1) k = dgComp R u b (add_zero 0) - dgComp R a u' (add_zero 0)) :
    coneTriangle u hu ⟶ coneTriangle u' hu' where
  hom₁ := homOf R a ((mem_dgCycles R).mpr ha)
  hom₂ := homOf R b ((mem_dgCycles R).mpr hb)
  hom₃ := homOf R (coneHomOfHomotopy hu hu' a b k)
    ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy hu hu' ha hb hk))
  -- Each square is first proved for the representatives in the homotopy category; the objects of
  -- the cone triangles agree with theirs by `rfl` but cannot be rewritten inside the implicit
  -- objects of the composites.
  comm₁ := by
    have h : homOf R u ((mem_dgCycles R).mpr hu) ≫ homOf R b ((mem_dgCycles R).mpr hb) =
        homOf R a ((mem_dgCycles R).mpr ha) ≫ homOf R u' ((mem_dgCycles R).mpr hu') := by
      rw [homOf_comp, homOf_comp, homOf_eq_iff, mem_dgBoundaries, dgCompZero_def, dgCompZero_def]
      exact ⟨k, hk⟩
    exact h
  comm₂ := by
    have h : homOf R (extensionInl R (dgDifferential_coneMorphism hu))
          ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) ≫
          homOf R (coneHomOfHomotopy hu hu' a b k)
            ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy hu hu' ha hb hk)) =
        homOf R b ((mem_dgCycles R).mpr hb) ≫
          homOf R (extensionInl R (dgDifferential_coneMorphism hu'))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) := by
      simp only [homOf_comp, dgCompZero_def, dgComp_extensionInl_coneHomOfHomotopy]
    exact h
  comm₃ := by
    have h : homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
          ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
          homOf R ((shiftFunctor R 1).dgMap 0 a) ((shiftFunctor R 1).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr ha)) =
        homOf R (coneHomOfHomotopy hu hu' a b k)
            ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy hu hu' ha hb hk)) ≫
          homOf R (extensionSnd R (dgDifferential_coneMorphism hu'))
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
      simp only [homOf_comp, dgCompZero_def, dgComp_coneHomOfHomotopy_extensionSnd]
    rw [← shiftFunctor_map_homOf] at h
    exact h

section

variable {a : DGHom R 0 P P'} {b : DGHom R 0 Q Q'} {k : DGHom R (-1) P Q'}
  (ha : dgDifferential R 0 a = 0) (hb : dgDifferential R 0 b = 0)
  (hk : dgDifferential R (-1) k = dgComp R u b (add_zero 0) - dgComp R a u' (add_zero 0))

@[simp]
theorem coneTriangleHomOfHomotopy_hom₁ :
    (coneTriangleHomOfHomotopy hu hu' ha hb hk).hom₁ = homOf R a ((mem_dgCycles R).mpr ha) :=
  (rfl)

@[simp]
theorem coneTriangleHomOfHomotopy_hom₂ :
    (coneTriangleHomOfHomotopy hu hu' ha hb hk).hom₂ = homOf R b ((mem_dgCycles R).mpr hb) :=
  (rfl)

@[simp]
theorem coneTriangleHomOfHomotopy_hom₃ :
    (coneTriangleHomOfHomotopy hu hu' ha hb hk).hom₃ =
      homOf R (coneHomOfHomotopy hu hu' a b k)
        ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy hu hu' ha hb hk)) :=
  (rfl)

end

/-- **A commutative square in the homotopy category extends to a morphism of cone triangles**:
if the classes of closed morphisms `a : P ⟶ P'` and `b : Q ⟶ Q'` satisfy `u ≫ b = a ≫ u'` in the
homotopy category, then there is a morphism of cone triangles with first components `a` and
`b`. -/
theorem exists_coneTriangle_hom (a : (coneTriangle u hu).obj₁ ⟶ (coneTriangle u' hu').obj₁)
    (b : (coneTriangle u hu).obj₂ ⟶ (coneTriangle u' hu').obj₂)
    (fac : (coneTriangle u hu).mor₁ ≫ b = a ≫ (coneTriangle u' hu').mor₁) :
    ∃ φ : coneTriangle u hu ⟶ coneTriangle u' hu', φ.hom₁ = a ∧ φ.hom₂ = b := by
  obtain ⟨a, ha, rfl⟩ := exists_homOf_eq R (X := P) (Y := P') a
  obtain ⟨b, hb, rfl⟩ := exists_homOf_eq R (X := Q) (Y := Q') b
  -- The objects of the cone triangles are those of the representatives by `rfl`, but cannot be
  -- rewritten inside the implicit objects of the composites.
  have fac' : homOf R u ((mem_dgCycles R).mpr hu) ≫ homOf R b hb =
      homOf R a ha ≫ homOf R u' ((mem_dgCycles R).mpr hu') := fac
  rw [homOf_comp, homOf_comp, homOf_eq_iff, mem_dgBoundaries, dgCompZero_def,
    dgCompZero_def] at fac'
  obtain ⟨k, hk⟩ := fac'
  exact ⟨_,
    coneTriangleHomOfHomotopy_hom₁ hu hu' ((mem_dgCycles R).mp ha) ((mem_dgCycles R).mp hb) hk,
    coneTriangleHomOfHomotopy_hom₂ hu hu' ((mem_dgCycles R).mp ha) ((mem_dgCycles R).mp hb) hk⟩

end coneHom

/-! ### Rotation of a cone triangle -/

section rotate

variable {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
  {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0)

/-- The comparison morphism `P⟦1⟧ ⟶ cone (Q ⟶ cone u)` from the third object of the rotated cone
triangle of `u` to the cone of the inclusion of `Q` into `cone u`: the inclusion of `P⟦1⟧` into
`cone u` followed by the inclusion of `cone u`, plus minus the shift of `u` followed by the
inclusion of `Q⟦1⟧`.  It is a homotopy equivalence with inverse
`MathlibExt.DGSource.DGTwistedObject.coneRotateInv`. -/
noncomputable def coneRotateHom :
    DGHom R 0 ((shiftFunctor R 1).obj P)
      (cone (extensionInl R (dgDifferential_coneMorphism hu))
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))) :=
  dgComp R (extensionInr R (dgDifferential_coneMorphism hu))
      (extensionInl R (dgDifferential_coneMorphism
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0) +
    dgComp R (-(shiftFunctor R 1).dgMap 0 u)
      (extensionInr R (dgDifferential_coneMorphism
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0)

/-- The comparison morphism `cone (Q ⟶ cone u) ⟶ P⟦1⟧`: the projection onto `cone u` followed by
the projection onto `P⟦1⟧`. -/
noncomputable def coneRotateInv :
    DGHom R 0
      (cone (extensionInl R (dgDifferential_coneMorphism hu))
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))
      ((shiftFunctor R 1).obj P) :=
  dgComp R (extensionFst R (dgDifferential_coneMorphism
      (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))))
    (extensionSnd R (dgDifferential_coneMorphism hu)) (add_zero 0)

theorem coneRotateHom_def :
    coneRotateHom hu =
      dgComp R (extensionInr R (dgDifferential_coneMorphism hu))
          (extensionInl R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0) +
        dgComp R (-(shiftFunctor R 1).dgMap 0 u)
          (extensionInr R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0) :=
  (rfl)

theorem coneRotateInv_def :
    coneRotateInv hu =
      dgComp R (extensionFst R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))))
        (extensionSnd R (dgDifferential_coneMorphism hu)) (add_zero 0) :=
  (rfl)

/-- The comparison morphism `P⟦1⟧ ⟶ cone (Q ⟶ cone u)` is closed. -/
theorem dgDifferential_coneRotateHom : dgDifferential R 0 (coneRotateHom hu) = 0 := by
  have hu₁ : dgDifferential R 0 ((shiftFunctor R 1).dgMap 0 u) = 0 :=
    (shiftFunctor R 1).dgDifferential_dgMap_eq_zero hu
  -- Both terms are `P⟦1⟧ ⟶ P ⟶ Q ⟶ cone u ⟶ cone (Q ⟶ cone u)`, with opposite signs.
  have h : dgComp R (dgComp R (coneMorphism R u) (extensionInl R (dgDifferential_coneMorphism hu))
        (add_zero 1)) (extensionInl R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 1) =
      dgComp R ((shiftFunctor R 1).dgMap 0 u)
        (dgComp R (coneMorphism R (extensionInl R (dgDifferential_coneMorphism hu)))
          (extensionInl R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 1))
        (zero_add 1) := by
    rw [dgComp_assoc R _ _ _ (add_zero 1) (add_zero 0) (by omega), dgComp_coneMorphism,
      dgComp_coneMorphism, dgMap_dgComp_fromShift_assoc]
  simp -proj only [coneRotateHom_def, map_add, map_neg, dgDifferential_dgComp,
    dgDifferential_extensionInl, dgDifferential_extensionInr, hu₁, zero_dgComp, dgComp_zero,
    smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul, neg_dgComp, h, add_neg_cancel]

/-- The comparison morphism `cone (Q ⟶ cone u) ⟶ P⟦1⟧` is closed. -/
theorem dgDifferential_coneRotateInv : dgDifferential R 0 (coneRotateInv hu) = 0 := by
  simp -proj only [coneRotateInv_def, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionSnd, dgComp_zero, smul_zero, add_zero, neg_dgComp, neg_eq_zero]
  rw [dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega), dgComp_coneMorphism,
    dgComp_extensionInl_extensionSnd, dgComp_zero, dgComp_zero]

/-- The comparison morphism `P⟦1⟧ ⟶ cone (Q ⟶ cone u)` followed by the projection onto `cone u`
is the inclusion of `P⟦1⟧` into `cone u`. -/
@[simp↓]
theorem dgComp_coneRotateHom_extensionFst :
    dgComp R (coneRotateHom hu) (extensionFst R (dgDifferential_coneMorphism
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0) =
      extensionInr R (dgDifferential_coneMorphism hu) := by
  simp only [coneRotateHom_def, add_dgComp,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionFst, dgComp_extensionInr_extensionFst, dgComp_zero, dgComp_dgId,
    add_zero]

/-- The comparison morphism `P⟦1⟧ ⟶ cone (Q ⟶ cone u)` followed by the projection onto `Q⟦1⟧`
is minus the shift of `u`. -/
@[simp↓]
theorem dgComp_coneRotateHom_extensionSnd :
    dgComp R (coneRotateHom hu) (extensionSnd R (dgDifferential_coneMorphism
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0) =
      -(shiftFunctor R 1).dgMap 0 u := by
  simp only [coneRotateHom_def, add_dgComp,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, dgComp_dgId,
    zero_add]

/-- The inclusion of `cone u` into `cone (Q ⟶ cone u)` followed by the comparison morphism
`cone (Q ⟶ cone u) ⟶ P⟦1⟧` is the projection of `cone u` onto `P⟦1⟧`. -/
@[simp↓]
theorem dgComp_extensionInl_coneRotateInv :
    dgComp R (extensionInl R (dgDifferential_coneMorphism
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (coneRotateInv hu)
        (add_zero 0) =
      extensionSnd R (dgDifferential_coneMorphism hu) := by
  simp only [coneRotateInv_def, dgComp_extensionInl_extensionFst_assoc]

/-- The inclusion of `Q⟦1⟧` into `cone (Q ⟶ cone u)` followed by the comparison morphism
`cone (Q ⟶ cone u) ⟶ P⟦1⟧` vanishes. -/
@[simp↓]
theorem dgComp_extensionInr_coneRotateInv :
    dgComp R (extensionInr R (dgDifferential_coneMorphism
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (coneRotateInv hu)
        (add_zero 0) =
      0 := by
  simp only [coneRotateInv_def, dgComp_extensionInr_extensionFst_assoc]

/-- The comparison morphism `P⟦1⟧ ⟶ cone (Q ⟶ cone u)` followed by its inverse
`cone (Q ⟶ cone u) ⟶ P⟦1⟧` is the identity. -/
@[simp↓]
theorem dgComp_coneRotateHom_coneRotateInv :
    dgComp R (coneRotateHom hu) (coneRotateInv hu) (add_zero 0) =
      dgId R ((shiftFunctor R 1).obj P) := by
  rw [coneRotateInv_def, ← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_coneRotateHom_extensionFst, dgComp_extensionInr_extensionSnd]

/-- The differential of the projection of `cone u` onto `Q`, followed by `Q ⟶ Q⟦1⟧` and the
inclusion of `Q⟦1⟧` into `cone (Q ⟶ cone u)`: this degree `-1` morphism is the homotopy behind
both the rotation isomorphism and the commutativity of its second square. -/
private theorem dgDifferential_extensionFst_toShift_extensionInr :
    dgDifferential R (-1)
        (dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
          (dgComp R (toShift Q 1) (extensionInr R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero (-1)))
          (zero_add (-1))) =
      -dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
          (dgComp R ((shiftFunctor R 1).dgMap 0 u) (extensionInr R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0))
          (add_zero 0) -
        dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
          (dgComp R (extensionInl R (dgDifferential_coneMorphism hu))
            (extensionInl R (dgDifferential_coneMorphism
              (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0))
          (add_zero 0) := by
  -- `P⟦1⟧ ⟶ P ⟶ Q ⟶ Q⟦1⟧` is the shift of `u` after `P⟦1⟧ ⟶ P ⟶ P⟦1⟧`, the identity.
  have h₁ : dgComp R (dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
        (coneMorphism R u) (zero_add 1))
        (dgComp R (toShift Q 1) (extensionInr R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero (-1)))
        (add_neg_cancel 1) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
        (dgComp R ((shiftFunctor R 1).dgMap 0 u) (extensionInr R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0))
        (add_zero 0) := by
    rw [dgComp_assoc R _ _ _ (zero_add 1) (add_neg_cancel 1) (by omega), dgComp_coneMorphism,
      ← toShift_dgComp_dgMap_assoc, dgComp_fromShift_toShift_assoc]
  rw [dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_dgComp_toShift_extensionInr_cone (dgDifferential_extensionInl R _), neg_dgComp,
    h₁, Int.negOnePow_zero, one_smul, dgComp_neg, sub_eq_add_neg]

/-- The second square of the rotated cone triangle commutes up to homotopy: the projection of
`cone u` onto `P⟦1⟧` followed by the comparison morphism `P⟦1⟧ ⟶ cone (Q ⟶ cone u)` and the
inclusion of `cone u` into `cone (Q ⟶ cone u)` differ by a boundary. -/
private theorem dgDifferential_extensionFst_toShift_extensionInr_eq_sub :
    dgDifferential R (-1)
        (dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
          (dgComp R (toShift Q 1) (extensionInr R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero (-1)))
          (zero_add (-1))) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism hu)) (coneRotateHom hu) (add_zero 0) -
        extensionInl R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))) := by
  rw [dgDifferential_extensionFst_toShift_extensionInr hu]
  refine extension_dgHom_ext ?_ ?_ <;>
    simp only [coneRotateHom_def, sub_eq_add_neg, dgComp_add, neg_dgComp, dgComp_neg,
      dgComp_extensionInl_extensionFst_assoc, dgComp_extensionInl_extensionSnd_assoc,
      dgComp_extensionInr_extensionFst_assoc, dgComp_extensionInr_extensionSnd_assoc, neg_zero,
      zero_add, add_zero]
  abel

/-- The comparison morphism `cone (Q ⟶ cone u) ⟶ P⟦1⟧` followed by `P⟦1⟧ ⟶ cone (Q ⟶ cone u)`
is homotopic to the identity. -/
private theorem dgDifferential_extensionFst_dgComp_eq_sub :
    dgDifferential R (-1)
        (dgComp R (extensionFst R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))))
          (dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
            (dgComp R (toShift Q 1) (extensionInr R (dgDifferential_coneMorphism
              (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero (-1)))
            (zero_add (-1))) (zero_add (-1))) =
      dgComp R (coneRotateInv hu) (coneRotateHom hu) (add_zero 0) - dgId R _ := by
  -- `Q⟦1⟧ ⟶ Q ⟶ cone u ⟶ Q ⟶ Q⟦1⟧` is the identity.
  have h : dgComp R (dgComp R (extensionSnd R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))))
        (coneMorphism R (extensionInl R (dgDifferential_coneMorphism hu))) (zero_add 1))
        (dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
          (dgComp R (toShift Q 1) (extensionInr R (dgDifferential_coneMorphism
            (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero (-1)))
          (zero_add (-1))) (add_neg_cancel 1) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))))
        (extensionInr R (dgDifferential_coneMorphism
          (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)))) (add_zero 0) := by
    rw [dgComp_assoc R _ _ _ (zero_add 1) (add_neg_cancel 1) (by omega), dgComp_coneMorphism,
      dgComp_extensionInl_extensionFst_assoc, dgComp_fromShift_toShift_assoc]
  rw [dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionFst_toShift_extensionInr hu, neg_dgComp, h, Int.negOnePow_zero,
    one_smul]
  refine extension_dgHom_ext (extension_dgHom_ext ?_ ?_) ?_ <;>
    simp only [coneRotateHom_def, coneRotateInv_def, sub_eq_add_neg, dgComp_add, neg_dgComp,
      dgComp_neg, dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_extensionInl_extensionFst_assoc, dgComp_extensionInl_extensionSnd_assoc,
      dgComp_extensionInr_extensionFst_assoc, dgComp_extensionInr_extensionSnd_assoc,
      dgComp_dgId, neg_zero, zero_add, add_zero]
  abel

/-- **The rotation isomorphism**: in the homotopy category, the shift `P⟦1⟧` is isomorphic to the
cone of the inclusion of `Q` into `cone u`, through the comparison morphisms
`MathlibExt.DGSource.DGTwistedObject.coneRotateHom` and `MathlibExt.DGSource.DGTwistedObject.coneRotateInv`. -/
noncomputable def coneRotateIso :
    DGHomotopyCategory.of R ((shiftFunctor R 1).obj P) ≅
      DGHomotopyCategory.of R (cone (extensionInl R (dgDifferential_coneMorphism hu))
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))) where
  hom := homOf R (coneRotateHom hu) ((mem_dgCycles R).mpr (dgDifferential_coneRotateHom hu))
  inv := homOf R (coneRotateInv hu) ((mem_dgCycles R).mpr (dgDifferential_coneRotateInv hu))
  hom_inv_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_coneRotateHom_coneRotateInv hu)
  inv_hom_id := by
    rw [homOf_comp, ← homOf_dgId, homOf_eq_iff, mem_dgBoundaries, dgCompZero_def]
    exact ⟨_, dgDifferential_extensionFst_dgComp_eq_sub hu⟩

@[simp]
theorem coneRotateIso_hom :
    (coneRotateIso hu).hom =
      homOf R (coneRotateHom hu) ((mem_dgCycles R).mpr (dgDifferential_coneRotateHom hu)) :=
  (rfl)

@[simp]
theorem coneRotateIso_inv :
    (coneRotateIso hu).inv =
      homOf R (coneRotateInv hu) ((mem_dgCycles R).mpr (dgDifferential_coneRotateInv hu)) :=
  (rfl)

/-- **The rotation of a cone triangle is a cone triangle**: the rotated triangle
`Q ⟶ cone u ⟶ P⟦1⟧ ⟶ Q⟦1⟧` of the cone triangle of `u`, whose last morphism is minus the shift of
`u`, is isomorphic to the cone triangle of the inclusion of `Q` into `cone u`, by the identities
and the rotation isomorphism. -/
noncomputable def coneTriangleRotateIso :
    (coneTriangle u hu).rotate ≅
      coneTriangle (extensionInl R (dgDifferential_coneMorphism hu))
        (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneRotateIso hu)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      -- The objects agree by `rfl` but cannot be rewritten inside the implicit objects.
      have h : homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫ (coneRotateIso hu).hom =
          homOf R (extensionInl R (dgDifferential_coneMorphism
              (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) := by
        rw [coneRotateIso_hom, homOf_comp, homOf_eq_iff, mem_dgBoundaries, dgCompZero_def]
        exact ⟨_, dgDifferential_extensionFst_toShift_extensionInr_eq_sub hu⟩
      exact h.trans (Category.id_comp _).symm)
    (by
      have h : homOf R (-(shiftFunctor R 1).dgMap 0 u)
            ((dgCycles R _ _).neg_mem ((shiftFunctor R 1).dgMap_mem_dgCycles
              ((mem_dgCycles R).mpr hu))) =
          (coneRotateIso hu).hom ≫ homOf R (extensionSnd R (dgDifferential_coneMorphism
              (dgDifferential_extensionInl R (dgDifferential_coneMorphism hu))))
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
        rw [coneRotateIso_hom]
        exact (homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (dgComp_coneRotateHom_extensionSnd hu)).symm
      refine (congrArg (fun f ↦ _ ≫ f) ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map_id _)).trans
        ((Category.comp_id _).trans ?_)
      exact ((congrArg Neg.neg (shiftFunctor_map_homOf 1 u ((mem_dgCycles R).mpr hu))).trans
        (homOf_neg R _ _).symm).trans h)

end rotate

/-! ### Distinguished triangles -/

section distinguished

variable (R C) in
/-- The **distinguished triangles** of the homotopy category of twisted objects: the triangles
isomorphic to the cone triangle `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` of a closed degree-zero morphism
`u`. -/
def distinguishedTriangles :
    Set (Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))) :=
  {T | ∃ (P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (u : DGHom R 0 P Q)
    (hu : dgDifferential R 0 u = 0), Nonempty (T ≅ coneTriangle u hu)}

theorem mem_distinguishedTriangles_iff
    {T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))} :
    T ∈ distinguishedTriangles R C ↔
      ∃ (P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))) (u : DGHom R 0 P Q)
        (hu : dgDifferential R 0 u = 0), Nonempty (T ≅ coneTriangle u hu) :=
  Iff.rfl

/-- The cone triangle of a closed degree-zero morphism is distinguished. -/
theorem coneTriangle_mem_distinguishedTriangles
    {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} (u : DGHom R 0 P Q)
    (hu : dgDifferential R 0 u = 0) : coneTriangle u hu ∈ distinguishedTriangles R C :=
  ⟨P, Q, u, hu, ⟨Iso.refl _⟩⟩

/-- A triangle isomorphic to a distinguished triangle is distinguished. -/
theorem isomorphic_distinguished
    (T₁ : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT₁ : T₁ ∈ distinguishedTriangles R C) (T₂ : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles R C := by
  obtain ⟨P, Q, u, hu, ⟨e'⟩⟩ := hT₁
  exact ⟨P, Q, u, hu, ⟨e ≪≫ e'⟩⟩

/-- **The contractible triangle `X ⟶ X ⟶ 0 ⟶ X⟦1⟧` is distinguished**: it is isomorphic to the
cone triangle of the identity, whose cone is contractible. -/
theorem contractible_distinguished
    (X : DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :
    contractibleTriangle X ∈ distinguishedTriangles R C := by
  obtain ⟨P, rfl⟩ := of_surjective R X
  have h := isZero_of_cone_dgId R P
  refine ⟨P, P, dgId R P, dgDifferential_dgId R P,
    ⟨Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) h.isoZero.symm ?_ (h.eq_of_tgt _ _)
      ((isZero_zero _).eq_of_src _ _)⟩⟩
  exact (Category.comp_id _).trans ((homOf_dgId R P).symm.trans (Category.id_comp _).symm)

/-- **Every morphism is the base of a distinguished triangle**: a morphism `X ⟶ Y` of the
homotopy category, represented by a closed degree-zero morphism `u`, extends to the cone
triangle of `u`. -/
theorem distinguished_cocone_triangle
    {X Y : DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))}
    (f : X ⟶ Y) :
    ∃ (Z : DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))
      (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distinguishedTriangles R C := by
  obtain ⟨P, rfl⟩ := of_surjective R X
  obtain ⟨Q, rfl⟩ := of_surjective R Y
  obtain ⟨u, hu, rfl⟩ := exists_homOf_eq R f
  exact ⟨_, _, _, coneTriangle_mem_distinguishedTriangles u ((mem_dgCycles R).mp hu)⟩

/-- **A commutative square between the bases of two distinguished triangles extends to a morphism
of triangles.** -/
theorem complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT₁ : T₁ ∈ distinguishedTriangles R C) (hT₂ : T₂ ∈ distinguishedTriangles R C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨P₁, Q₁, u₁, hu₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨P₂, Q₂, u₂, hu₂, ⟨e₂⟩⟩ := hT₂
  -- Transport the square to the cone triangles, extend it there, and transport back.
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_coneTriangle_hom hu₁ hu₂ (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
    (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) (by
      have comm₁₁ := e₁.inv.comm₁
      have comm₁₂ := e₂.hom.comm₁
      simp only [Category.assoc, reassoc_of% comm₁₁, reassoc_of% fac, comm₁₂])
  let γ := e₁.hom ≫ φ ≫ e₂.inv
  refine ⟨γ.hom₃, ?_, ?_⟩
  · have comm₂ := γ.comm₂
    simp only [γ, triangleCategory_comp, TriangleMorphism.comp_hom₂, hφ₂, Category.assoc,
      Iso.hom_inv_id_triangle_hom₂, Category.comp_id, Iso.hom_inv_id_triangle_hom₂_assoc] at comm₂
    exact comm₂
  · have comm₃ := γ.comm₃
    simp only [γ, triangleCategory_comp, TriangleMorphism.comp_hom₁, hφ₁, Category.assoc,
      Iso.hom_inv_id_triangle_hom₁, Category.comp_id, Iso.hom_inv_id_triangle_hom₁_assoc] at comm₃
    exact comm₃

/-- **The rotation of a distinguished triangle is distinguished**: the rotation of a cone triangle
is isomorphic to the cone triangle of the inclusion of `Q` into `cone u`. -/
theorem rotate_mem_distinguishedTriangles
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT : T ∈ distinguishedTriangles R C) : T.rotate ∈ distinguishedTriangles R C := by
  obtain ⟨P, Q, u, hu, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, _, ⟨(rotate _).mapIso e ≪≫ coneTriangleRotateIso hu⟩⟩

end distinguished

end DGTwistedObject

end MathlibExt.DGSource
