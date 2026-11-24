/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Triangulated.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedPretriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The homotopy category of twisted objects is triangulated

Let `C` be a differential graded category and let `H⁰` be the homotopy category of the twisted
objects of the additive closure of the shift closure of `C`, with the pretriangulated structure of
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedPretriangulated.lean`, whose distinguished triangles are the
triangles isomorphic to cone triangles `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧`.  This file proves the octahedral
axiom, so that `H⁰` is a triangulated category.

Let `u : P ⟶ Q` and `v : Q ⟶ S` be closed degree-zero morphisms with composite `w = u ≫ v`.  The
strictly commutative squares `(𝟙 P, v)` from `u` to `w` and `(u, 𝟙 S)` from `w` to `v` induce
closed morphisms of cones `m₁ : cone u ⟶ cone w` and `m₃ : cone w ⟶ cone v`
(`MathlibExt.DGSource.DGTwistedObject.coneHomOfHomotopy` with zero homotopy), and the triangle

`cone u ⟶ cone w ⟶ cone v ⟶ (cone u)⟦1⟧`

whose last morphism is the projection of `cone v` onto `Q⟦1⟧` followed by the shift of the
inclusion of `Q` into `cone u` (`MathlibExt.DGSource.DGTwistedObject.coneCompTriangle`) is distinguished.
Indeed `cone v` is isomorphic in `H⁰` to the cone `K` of `m₁`, compatibly with the triangles:

* the comparison `cone v ⟶ K` (`MathlibExt.DGSource.DGTwistedObject.coneCompHom`) includes `S` through
  `cone w` and `Q⟦1⟧` through `(cone u)⟦1⟧`;
* the comparison `K ⟶ cone v` (`MathlibExt.DGSource.DGTwistedObject.coneCompInv`) is `m₃` on `cone w` and
  the projection onto `Q⟦1⟧` on `(cone u)⟦1⟧`;
* the first composite is the identity, and the second is homotopic to the identity through the
  degree `-1` endomorphism of `K` which sends the summand `P⟦1⟧` of `cone w` to the summand
  `P⟦1⟧⟦1⟧` of `(cone u)⟦1⟧`.

The sign of this homotopy comes from the shift of the comparison morphism `P⟦1⟧ ⟶ P`, which is
minus the comparison morphism `P⟦1⟧⟦1⟧ ⟶ P⟦1⟧`
(`MathlibExt.DGSource.DGTwistedObject.dgMap_fromShift_self`).  Together with the four commutativity relations
between `m₁`, `m₃` and the cone triangles, this gives the octahedra required by
`CategoryTheory.IsTriangulated.mk'`.

Every triangulated subcategory of `H⁰` closed under isomorphisms is closed under extensions of
twisted objects (`MathlibExt.DGSource.DGTwistedObject.prop_extension`): the extension of `Q` by `P` along a
closed degree-one morphism `g : Q ⟶ P` is isomorphic to the cone of the closed degree-zero
morphism `Q⟦-1⟧ ⟶ P` underlying `g`.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.coneCompHom` and `MathlibExt.DGSource.DGTwistedObject.coneCompInv`: the closed
  comparison morphisms between `cone v` and the cone of `m₁ : cone u ⟶ cone (u ≫ v)`.
* `MathlibExt.DGSource.DGTwistedObject.coneCompIso`: the induced isomorphism in the homotopy category.
* `MathlibExt.DGSource.DGTwistedObject.coneCompTriangle`: the triangle
  `cone u ⟶ cone (u ≫ v) ⟶ cone v ⟶ (cone u)⟦1⟧`.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.dgComp_coneCompHom_coneCompInv`: the comparison `cone v ⟶ K ⟶ cone v`
  is the identity.
* `MathlibExt.DGSource.DGTwistedObject.coneCompTriangle_mem_distinguishedTriangles`: the triangle
  `cone u ⟶ cone (u ≫ v) ⟶ cone v ⟶ (cone u)⟦1⟧` is distinguished.
* `MathlibExt.DGSource.DGTwistedObject.isTriangulated`: the homotopy category of twisted objects is
  triangulated.
* `MathlibExt.DGSource.DGTwistedObject.prop_extension`: a triangulated subcategory closed under isomorphisms
  is closed under extensions of twisted objects.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`, whose triangle
  `CochainComplex.mappingConeCompTriangle`, homotopy equivalence
  `CochainComplex.mappingConeCompHomotopyEquiv` and deduction of the octahedral axiom through
  `CategoryTheory.IsTriangulated.mk'` for the homotopy category of cochain complexes are followed
  here.
-/

public section

open CategoryTheory Pretriangulated

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

open DGHomotopyCategory

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### The cone of `cone u ⟶ cone (u ≫ v)` -/

section coneComp

variable {P Q S : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
  {u : DGHom R 0 P Q} {v : DGHom R 0 Q S} {w : DGHom R 0 P S}
  (hu : dgDifferential R 0 u = 0) (hv : dgDifferential R 0 v = 0)
  (hw : dgDifferential R 0 w = 0) (huv : dgComp R u v (add_zero 0) = w)

include hu hv hw huv

/-- The morphism of cones `cone u ⟶ cone w` induced by the identity of `P` and by `v`, for
`w = u ≫ v`, is closed. -/
theorem dgDifferential_coneHomOfHomotopy_dgId_zero :
    dgDifferential R 0 (coneHomOfHomotopy hu hw (dgId R P) v 0) = 0 :=
  dgDifferential_coneHomOfHomotopy_zero hu hw (dgDifferential_dgId R P) hv
    (by rw [huv, dgId_dgComp])

/-- The morphism of cones `cone w ⟶ cone v` induced by `u` and the identity of `S`, for
`w = u ≫ v`, is closed. -/
theorem dgDifferential_coneHomOfHomotopy_zero_dgId :
    dgDifferential R 0 (coneHomOfHomotopy hw hv u (dgId R S) 0) = 0 :=
  dgDifferential_coneHomOfHomotopy_zero hw hv hu (dgDifferential_dgId R S)
    (by rw [dgComp_dgId, huv])

omit huv in
/-- The composite `cone u ⟶ cone w ⟶ cone v` of the morphisms of cones induced by `(𝟙 P, v)` and
`(u, 𝟙 S)` is the projection onto `Q` followed by `v` and the inclusion of `S`, plus the projection
onto `P⟦1⟧` followed by the shift of `u` and the inclusion of `Q⟦1⟧`. -/
private theorem dgComp_coneHomOfHomotopy_dgId_zero_coneHomOfHomotopy :
    dgComp R (coneHomOfHomotopy hu hw (dgId R P) v 0) (coneHomOfHomotopy hw hv u (dgId R S) 0)
        (add_zero 0) =
      dgComp R (extensionFst R (dgDifferential_coneMorphism hu))
          (dgComp R v (extensionInl R (dgDifferential_coneMorphism hv)) (add_zero 0)) (add_zero 0) +
        dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
          (dgComp R ((shiftFunctor R 1).dgMap 0 u)
            (extensionInr R (dgDifferential_coneMorphism hv)) (add_zero 0)) (add_zero 0) := by
  refine extension_dgHom_ext ?_ ?_
  · simp -proj only [dgComp_add, dgComp_extensionInl_coneHomOfHomotopy_assoc,
      dgComp_extensionInl_coneHomOfHomotopy, dgId_dgComp, dgComp_extensionInl_extensionFst_assoc,
      dgComp_extensionInl_extensionSnd_assoc, add_zero]
  · rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (by omega),
      dgComp_extensionInr_coneHomOfHomotopy]
    simp -proj only [EnrichedFunctor.dgMap_dgId, dgComp_zero, zero_dgComp, sub_zero, dgId_dgComp,
      dgComp_extensionInr_coneHomOfHomotopy, dgComp_add, dgComp_extensionInr_extensionFst_assoc,
      dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- The comparison morphism `cone v ⟶ cone (cone u ⟶ cone w)`, for `w = u ≫ v`: on the summand `S`
the inclusion of `S` into `cone w` followed by the inclusion of `cone w`, and on the summand `Q⟦1⟧`
the shift of the inclusion of `Q` into `cone u` followed by the inclusion of `(cone u)⟦1⟧`.  It is a
homotopy equivalence with inverse `MathlibExt.DGSource.DGTwistedObject.coneCompInv`. -/
noncomputable def coneCompHom :
    DGHom R 0 (cone v hv)
      (cone (coneHomOfHomotopy hu hw (dgId R P) v 0)
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)) :=
  dgComp R (extensionFst R (dgDifferential_coneMorphism hv))
      (dgComp R (extensionInl R (dgDifferential_coneMorphism hw))
        (extensionInl R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0)) (add_zero 0) +
    dgComp R (extensionSnd R (dgDifferential_coneMorphism hv))
      (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        (extensionInr R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0)) (add_zero 0)

/-- The comparison morphism `cone (cone u ⟶ cone w) ⟶ cone v`, for `w = u ≫ v`: on the summand
`cone w` the morphism of cones induced by `u` and the identity of `S`, and on the summand
`(cone u)⟦1⟧` the shift of the projection of `cone u` onto `Q` followed by the inclusion of
`Q⟦1⟧`. -/
noncomputable def coneCompInv :
    DGHom R 0
      (cone (coneHomOfHomotopy hu hw (dgId R P) v 0)
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)) (cone v hv) :=
  dgComp R (extensionFst R (dgDifferential_coneMorphism
      (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
    (coneHomOfHomotopy hw hv u (dgId R S) 0) (add_zero 0) +
  dgComp R (extensionSnd R (dgDifferential_coneMorphism
      (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
    (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
      (extensionInr R (dgDifferential_coneMorphism hv)) (add_zero 0)) (add_zero 0)

theorem coneCompHom_def :
    coneCompHom hu hv hw huv =
      dgComp R (extensionFst R (dgDifferential_coneMorphism hv))
          (dgComp R (extensionInl R (dgDifferential_coneMorphism hw))
            (extensionInl R (dgDifferential_coneMorphism
              (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0))
          (add_zero 0) +
        dgComp R (extensionSnd R (dgDifferential_coneMorphism hv))
          (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
            (extensionInr R (dgDifferential_coneMorphism
              (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0))
          (add_zero 0) :=
  (rfl)

theorem coneCompInv_def :
    coneCompInv hu hv hw huv =
      dgComp R (extensionFst R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
        (coneHomOfHomotopy hw hv u (dgId R S) 0) (add_zero 0) +
      dgComp R (extensionSnd R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
        (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
          (extensionInr R (dgDifferential_coneMorphism hv)) (add_zero 0)) (add_zero 0) :=
  (rfl)

/-- The comparison morphism `cone v ⟶ cone (cone u ⟶ cone w)` is closed. -/
theorem dgDifferential_coneCompHom : dgDifferential R 0 (coneCompHom hu hv hw huv) = 0 := by
  -- Both terms are `cone v ⟶ Q⟦1⟧ ⟶ Q ⟶ S ⟶ cone w ⟶ cone (cone u ⟶ cone w)`, with opposite
  -- signs.
  simp -proj only [coneCompHom, map_add, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionSnd, dgDifferential_extensionInl, dgDifferential_extensionInr,
    (shiftFunctor R 1).dgDifferential_dgMap_eq_zero (dgDifferential_extensionInl R _),
    zero_dgComp, dgComp_zero, smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul,
    neg_dgComp, coneMorphism_def]
  rw [dgComp_assoc R (extensionSnd R (dgDifferential_coneMorphism hv)) _ _ (zero_add 1)
      (add_zero 1) (by omega),
    dgComp_assoc R (fromShift Q 1) v _ (add_zero 1) (zero_add 0) (by omega),
    dgComp_assoc R (fromShift (cone u hu) 1) _ _ (add_zero 1) (add_zero 0) (by omega),
    dgMap_dgComp_fromShift_assoc, dgComp_extensionInl_coneHomOfHomotopy_assoc, neg_add_cancel]

/-- The comparison morphism `cone (cone u ⟶ cone w) ⟶ cone v` is closed. -/
theorem dgDifferential_coneCompInv : dgDifferential R 0 (coneCompInv hu hv hw huv) = 0 := by
  -- After the Leibniz rule, every term is the projection onto `(cone u)⟦1⟧` followed by a
  -- degree-one morphism `(cone u)⟦1⟧ ⟶ cone v`; these are brought to the form
  -- `(cone u)⟦1⟧ ⟶ X⟦1⟧ ⟶ X ⟶ cone v` for the two summands `X` of `cone u`.
  have h : dgComp R (dgComp R (fromShift (cone u hu) 1) (coneHomOfHomotopy hu hw (dgId R P) v 0)
        (add_zero 1)) (coneHomOfHomotopy hw hv u (dgId R S) 0) (add_zero 1) =
      dgComp R ((shiftFunctor R 1).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
          (dgComp R (fromShift Q 1)
            (dgComp R v (extensionInl R (dgDifferential_coneMorphism hv)) (add_zero 0))
            (add_zero 1)) (zero_add 1) +
        dgComp R ((shiftFunctor R 1).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
          (dgComp R (fromShift ((shiftFunctor R 1).obj P) 1)
            (dgComp R ((shiftFunctor R 1).dgMap 0 u)
              (extensionInr R (dgDifferential_coneMorphism hv)) (add_zero 0)) (add_zero 1))
          (zero_add 1) := by
    rw [dgComp_assoc R _ _ _ (add_zero 1) (add_zero 0) (by omega),
      dgComp_coneHomOfHomotopy_dgId_zero_coneHomOfHomotopy, dgComp_add,
      dgMap_dgComp_fromShift_assoc, dgMap_dgComp_fromShift_assoc]
  simp -proj only [coneCompInv, map_add, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionSnd, dgDifferential_extensionInr,
    dgDifferential_coneHomOfHomotopy_zero_dgId hu hv hw huv,
    ← EnrichedFunctor.dgMap_dgDifferential, map_neg, EnrichedFunctor.dgMap_dgComp,
    zero_dgComp, dgComp_zero, smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul,
    neg_dgComp, coneMorphism_def, dgMap_fromShift_self]
  rw [dgComp_assoc R (extensionSnd R _) _ _ (zero_add 1) (add_zero 1) (by omega), h,
    dgComp_assoc R _ _ (extensionInr R _) (zero_add 1) (add_zero 1) (by omega),
    dgComp_assoc R _ _ (extensionInr R _) (add_zero 1) (zero_add 0) (by omega),
    dgComp_assoc R (fromShift Q 1) v _ (add_zero 1) (zero_add 0) (by omega)]
  simp only [mul_one, Int.negOnePow_one, Units.neg_smul, one_smul, neg_dgComp, dgComp_neg,
    neg_neg, dgComp_add]
  abel

/-- The comparison morphism `cone v ⟶ cone (cone u ⟶ cone w)` followed by its inverse
`cone (cone u ⟶ cone w) ⟶ cone v` is the identity. -/
@[simp↓]
theorem dgComp_coneCompHom_coneCompInv :
    dgComp R (coneCompHom hu hv hw huv) (coneCompInv hu hv hw huv) (add_zero 0) =
      dgId R (cone v hv) := by
  refine extension_dgHom_ext ?_ ?_ <;>
    simp -proj only [coneCompHom, coneCompInv, add_dgComp, dgComp_add,
      dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_extensionInl_extensionFst_assoc, dgComp_extensionInl_extensionSnd_assoc,
      dgComp_extensionInr_extensionFst_assoc, dgComp_extensionInr_extensionSnd_assoc,
      dgComp_extensionInl_coneHomOfHomotopy, dgId_dgComp, dgComp_dgId,
      (shiftFunctor R 1).dgMap_dgComp_dgMap_assoc_of_eq_dgId
        (dgComp_extensionInl_extensionFst R _), dgComp_zero, add_zero, zero_add]

/-- The inclusion of `cone w` into `cone (cone u ⟶ cone w)` followed by the comparison morphism
`cone (cone u ⟶ cone w) ⟶ cone v` is the morphism of cones induced by `u` and the identity of
`S`. -/
@[simp↓]
theorem dgComp_extensionInl_coneCompInv :
    dgComp R (extensionInl R (dgDifferential_coneMorphism
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (coneCompInv hu hv hw huv)
        (add_zero 0) =
      coneHomOfHomotopy hw hv u (dgId R S) 0 := by
  simp -proj only [coneCompInv, dgComp_add, dgComp_extensionInl_extensionFst_assoc,
    dgComp_extensionInl_extensionSnd_assoc, add_zero]

/-- The comparison morphism `cone v ⟶ cone (cone u ⟶ cone w)` followed by the projection onto
`(cone u)⟦1⟧` is the projection of `cone v` onto `Q⟦1⟧` followed by the shift of the inclusion of
`Q` into `cone u`. -/
@[simp↓]
theorem dgComp_coneCompHom_extensionSnd :
    dgComp R (coneCompHom hu hv hw huv) (extensionSnd R (dgDifferential_coneMorphism
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0) =
      dgComp R (extensionSnd R (dgDifferential_coneMorphism hv))
        ((shiftFunctor R 1).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        (add_zero 0) := by
  simp -proj only [coneCompHom, add_dgComp,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, dgComp_dgId,
    zero_add]

/-- The inclusion of `(cone u)⟦1⟧` into `cone (cone u ⟶ cone w)` followed by the comparison
morphism `cone (cone u ⟶ cone w) ⟶ cone v` is the shift of the projection of `cone u` onto `Q`
followed by the inclusion of `Q⟦1⟧` into `cone v`. -/
@[simp↓]
theorem dgComp_extensionInr_coneCompInv :
    dgComp R (extensionInr R (dgDifferential_coneMorphism
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (coneCompInv hu hv hw huv)
        (add_zero 0) =
      dgComp R ((shiftFunctor R 1).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
        (extensionInr R (dgDifferential_coneMorphism hv)) (add_zero 0) := by
  simp -proj only [coneCompInv, dgComp_add, dgComp_extensionInr_extensionFst_assoc,
    dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- The inclusion of `S` into `cone v` followed by the comparison morphism
`cone v ⟶ cone (cone u ⟶ cone w)` is the inclusion of `S` into `cone w` followed by the inclusion
of `cone w`. -/
@[simp↓]
theorem dgComp_extensionInl_coneCompHom :
    dgComp R (extensionInl R (dgDifferential_coneMorphism hv)) (coneCompHom hu hv hw huv)
        (add_zero 0) =
      dgComp R (extensionInl R (dgDifferential_coneMorphism hw))
        (extensionInl R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0) := by
  simp -proj only [coneCompHom, dgComp_add, dgComp_extensionInl_extensionFst_assoc,
    dgComp_extensionInl_extensionSnd_assoc, add_zero]

/-- The inclusion of `Q⟦1⟧` into `cone v` followed by the comparison morphism
`cone v ⟶ cone (cone u ⟶ cone w)` is the shift of the inclusion of `Q` into `cone u` followed by
the inclusion of `(cone u)⟦1⟧`. -/
@[simp↓]
theorem dgComp_extensionInr_coneCompHom :
    dgComp R (extensionInr R (dgDifferential_coneMorphism hv)) (coneCompHom hu hv hw huv)
        (add_zero 0) =
      dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        (extensionInr R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0) := by
  simp -proj only [coneCompHom, dgComp_add, dgComp_extensionInr_extensionFst_assoc,
    dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- The comparison morphism `cone v ⟶ cone (cone u ⟶ cone w)` followed by the projection onto
`cone w` is the projection of `cone v` onto `S` followed by the inclusion of `S` into `cone w`. -/
@[simp↓]
theorem dgComp_coneCompHom_extensionFst :
    dgComp R (coneCompHom hu hv hw huv) (extensionFst R (dgDifferential_coneMorphism
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0) =
      dgComp R (extensionFst R (dgDifferential_coneMorphism hv))
        (extensionInl R (dgDifferential_coneMorphism hw)) (add_zero 0) := by
  simp -proj only [coneCompHom, add_dgComp,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionFst, dgComp_extensionInr_extensionFst, dgComp_zero, dgComp_dgId,
    add_zero]

/-- The homotopy between the identity of `cone (cone u ⟶ cone w)` and the comparison morphism to
`cone v` followed by its inverse: the projection onto `cone w`, then onto `P⟦1⟧`, the comparison
morphism `P⟦1⟧ ⟶ P⟦1⟧⟦1⟧`, the shift of the inclusion of `P⟦1⟧` into `cone u`, and the inclusion of
`(cone u)⟦1⟧`. -/
private noncomputable def coneCompHomotopy :
    DGHom R (-1)
      (cone (coneHomOfHomotopy hu hw (dgId R P) v 0)
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))
      (cone (coneHomOfHomotopy hu hw (dgId R P) v 0)
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)) :=
  dgComp R (extensionFst R (dgDifferential_coneMorphism
      (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
    (dgComp R (extensionSnd R (dgDifferential_coneMorphism hw))
      (dgComp R (toShift ((shiftFunctor R 1).obj P) 1)
        (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
          (extensionInr R (dgDifferential_coneMorphism
            (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0))
        (add_zero (-1))) (zero_add (-1))) (zero_add (-1))

omit hv huv in
/-- The first cancellation in the differential of `coneCompHomotopy`: the comparison morphisms
`P⟦1⟧⟦1⟧ ⟶ P⟦1⟧ ⟶ P⟦1⟧⟦1⟧` cancel in the term coming from the projection onto `cone w`. -/
private theorem dgComp_extensionSnd_comparison_cancel
    (hm₁ : dgDifferential R 0 (coneHomOfHomotopy hu hw (dgId R P) v 0) = 0) :
    dgComp R (dgComp R (extensionSnd R (dgDifferential_coneMorphism hm₁))
      (dgComp R (fromShift (cone u hu) 1) (coneHomOfHomotopy hu hw (dgId R P) v 0) (add_zero 1))
      (zero_add 1))
      (dgComp R (extensionSnd R (dgDifferential_coneMorphism hw))
        (dgComp R (toShift ((shiftFunctor R 1).obj P) 1)
          (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
            (extensionInr R (dgDifferential_coneMorphism hm₁)) (add_zero 0)) (add_zero (-1)))
        (zero_add (-1))) (add_neg_cancel 1) =
    dgComp R (extensionSnd R (dgDifferential_coneMorphism hm₁))
      (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
        (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
          (extensionInr R (dgDifferential_coneMorphism hm₁)) (add_zero 0)) (add_zero 0))
      (add_zero 0) := by
  rw [dgComp_assoc R (extensionSnd R (dgDifferential_coneMorphism hm₁)) _ _ (zero_add 1)
      (add_neg_cancel 1) (by omega),
    dgComp_assoc R (fromShift (cone u hu) 1) _ _ (add_zero 1) (zero_add (-1)) (by omega),
    dgComp_coneHomOfHomotopy_extensionSnd_assoc, EnrichedFunctor.dgMap_dgId, dgId_dgComp,
    ← dgMap_dgComp_fromShift_assoc, dgComp_fromShift_toShift_assoc]

/-- The comparison morphism `cone (cone u ⟶ cone w) ⟶ cone v` followed by its inverse, through
the summands `S` and `P⟦1⟧` of `cone w` and `Q⟦1⟧` of `(cone u)⟦1⟧`. -/
private theorem dgComp_coneCompInv_coneCompHom :
    dgComp R (coneCompInv hu hv hw huv) (coneCompHom hu hv hw huv) (add_zero 0) =
      dgComp R (extensionFst R (dgDifferential_coneMorphism
            (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
          (dgComp R (extensionFst R (dgDifferential_coneMorphism hw))
            (dgComp R (extensionInl R (dgDifferential_coneMorphism hw))
              (extensionInl R (dgDifferential_coneMorphism
                (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0))
            (add_zero 0)) (add_zero 0) +
        dgComp R (extensionFst R (dgDifferential_coneMorphism
            (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
          (dgComp R (extensionSnd R (dgDifferential_coneMorphism hw))
            (dgComp R ((shiftFunctor R 1).dgMap 0 u)
              (dgComp R ((shiftFunctor R 1).dgMap 0
                  (extensionInl R (dgDifferential_coneMorphism hu)))
                (extensionInr R (dgDifferential_coneMorphism
                  (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0))
              (add_zero 0)) (add_zero 0)) (add_zero 0) +
        dgComp R (extensionSnd R (dgDifferential_coneMorphism
            (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
          (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
            (dgComp R ((shiftFunctor R 1).dgMap 0
                (extensionInl R (dgDifferential_coneMorphism hu)))
              (extensionInr R (dgDifferential_coneMorphism
                (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv))) (add_zero 0))
            (add_zero 0)) (add_zero 0) := by
  simp -proj only [coneCompHom, coneCompInv, add_dgComp, dgComp_add,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_coneHomOfHomotopy_zero_extensionFst_assoc,
    dgComp_coneHomOfHomotopy_extensionSnd_assoc, dgComp_extensionInr_extensionFst_assoc,
    dgComp_extensionInr_extensionSnd_assoc, dgId_dgComp, dgComp_zero, add_zero]
  abel

omit hv huv in
/-- The identity of `cone (cone u ⟶ cone w)`, through the summands `S` and `P⟦1⟧` of `cone w` and
`Q⟦1⟧` and `P⟦1⟧⟦1⟧` of `(cone u)⟦1⟧`. -/
private theorem dgId_cone_coneHomOfHomotopy_dgId_zero
    (hm₁ : dgDifferential R 0 (coneHomOfHomotopy hu hw (dgId R P) v 0) = 0) :
    dgId R (cone (coneHomOfHomotopy hu hw (dgId R P) v 0) hm₁) =
      dgComp R (extensionFst R (dgDifferential_coneMorphism hm₁))
          (dgComp R (extensionFst R (dgDifferential_coneMorphism hw))
            (dgComp R (extensionInl R (dgDifferential_coneMorphism hw))
              (extensionInl R (dgDifferential_coneMorphism hm₁)) (add_zero 0)) (add_zero 0))
          (add_zero 0) +
        dgComp R (extensionFst R (dgDifferential_coneMorphism hm₁))
          (dgComp R (extensionSnd R (dgDifferential_coneMorphism hw))
            (dgComp R (extensionInr R (dgDifferential_coneMorphism hw))
              (extensionInl R (dgDifferential_coneMorphism hm₁)) (add_zero 0)) (add_zero 0))
          (add_zero 0) +
        dgComp R (extensionSnd R (dgDifferential_coneMorphism hm₁))
          (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
            (dgComp R ((shiftFunctor R 1).dgMap 0
                (extensionInl R (dgDifferential_coneMorphism hu)))
              (extensionInr R (dgDifferential_coneMorphism hm₁)) (add_zero 0)) (add_zero 0))
          (add_zero 0) +
        dgComp R (extensionSnd R (dgDifferential_coneMorphism hm₁))
          (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
            (dgComp R ((shiftFunctor R 1).dgMap 0
                (extensionInr R (dgDifferential_coneMorphism hu)))
              (extensionInr R (dgDifferential_coneMorphism hm₁)) (add_zero 0)) (add_zero 0))
          (add_zero 0) := by
  refine extension_dgHom_ext ?_ ?_ <;>
    simp -proj only [dgComp_dgId, dgComp_add, dgComp_extensionInl_extensionFst_assoc,
      dgComp_extensionInl_extensionSnd_assoc, dgComp_extensionInr_extensionFst_assoc,
      dgComp_extensionInr_extensionSnd_assoc, add_zero, zero_add] <;>
    rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      ← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0), ← add_dgComp]
  · rw [extension_total, dgId_dgComp]
  · rw [← EnrichedFunctor.dgMap_dgComp, ← EnrichedFunctor.dgMap_dgComp, ← map_add,
      extension_total,
      EnrichedFunctor.dgMap_dgId, dgId_dgComp]

/-- The comparison morphism `cone (cone u ⟶ cone w) ⟶ cone v` followed by its inverse
`cone v ⟶ cone (cone u ⟶ cone w)` is homotopic to the identity. -/
private theorem dgDifferential_coneCompHomotopy :
    dgDifferential R (-1) (coneCompHomotopy hu hv hw huv) =
      dgComp R (coneCompInv hu hv hw huv) (coneCompHom hu hv hw huv) (add_zero 0) -
        dgId R (cone (coneHomOfHomotopy hu hw (dgId R P) v 0)
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)) := by
  have hm₁ := dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv
  -- By the Leibniz rule the differential of the homotopy has three terms, from the differentials
  -- of the projection onto `cone w` (`h₁`), of the shift of the inclusion of `P⟦1⟧` into `cone u`
  -- (`h₂`) and of the inclusion of `(cone u)⟦1⟧` (`h₃`).  In each of them the comparison
  -- morphisms `P⟦1⟧⟦1⟧ ⟶ P⟦1⟧ ⟶ P⟦1⟧⟦1⟧` or `P⟦1⟧ ⟶ P⟦1⟧⟦1⟧ ⟶ P⟦1⟧` cancel.
  have h₁ := dgComp_extensionSnd_comparison_cancel hu hw hm₁
  have h₂ : dgComp R (toShift ((shiftFunctor R 1).obj P) 1)
        (dgComp R (dgComp R (dgComp R (fromShift ((shiftFunctor R 1).obj P) 1)
          ((shiftFunctor R 1).dgMap 0 u) (add_zero 1))
          ((shiftFunctor R 1).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
          (add_zero 1)) (extensionInr R (dgDifferential_coneMorphism hm₁)) (add_zero 1))
        (neg_add_cancel 1) =
      dgComp R ((shiftFunctor R 1).dgMap 0 u)
        (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
          (extensionInr R (dgDifferential_coneMorphism hm₁)) (add_zero 0)) (add_zero 0) := by
    rw [dgComp_assoc R _ _ (extensionInr R (dgDifferential_coneMorphism hm₁)) (add_zero 1)
        (add_zero 0) (by omega),
      dgComp_assoc R (fromShift ((shiftFunctor R 1).obj P) 1) _ _ (add_zero 1) (zero_add 0)
        (by omega),
      dgComp_toShift_fromShift_assoc]
  have h₃ : dgComp R (toShift ((shiftFunctor R 1).obj P) 1)
        (dgComp R ((shiftFunctor R 1).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
          (dgComp R (dgComp R (fromShift (cone u hu) 1) (coneHomOfHomotopy hu hw (dgId R P) v 0)
            (add_zero 1)) (extensionInl R (dgDifferential_coneMorphism hm₁)) (add_zero 1))
          (zero_add 1)) (neg_add_cancel 1) =
      dgComp R (extensionInr R (dgDifferential_coneMorphism hw))
        (extensionInl R (dgDifferential_coneMorphism hm₁)) (add_zero 0) := by
    rw [dgComp_assoc R (fromShift (cone u hu) 1) _ _ (add_zero 1) (add_zero 0) (by omega),
      dgMap_dgComp_fromShift_assoc, dgComp_toShift_fromShift_assoc,
      dgComp_extensionInr_coneHomOfHomotopy_zero_assoc, EnrichedFunctor.dgMap_dgId, dgId_dgComp]
  -- Finally, expand the differential of the homotopy by the Leibniz rule.
  simp -proj only [coneCompHomotopy, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionSnd, dgDifferential_extensionInr, dgDifferential_toShift,
    ← EnrichedFunctor.dgMap_dgDifferential, EnrichedFunctor.dgMap_dgComp, zero_dgComp,
    zero_add, Int.negOnePow_zero, one_smul, neg_dgComp, coneMorphism_def, dgMap_fromShift_self,
    units_smul_dgComp, dgComp_units_smul, dgComp_add, h₁, h₂, h₃,
    dgComp_coneCompInv_coneCompHom hu hv hw huv,
    dgId_cone_coneHomOfHomotopy_dgId_zero hu hw hm₁]
  simp only [mul_one, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg,
    neg_add]
  abel

/-- **The comparison isomorphism** `cone v ≅ cone (cone u ⟶ cone w)` in the homotopy category, for
`w = u ≫ v`, through the comparison morphisms `MathlibExt.DGSource.DGTwistedObject.coneCompHom` and
`MathlibExt.DGSource.DGTwistedObject.coneCompInv`. -/
noncomputable def coneCompIso :
    DGHomotopyCategory.of R (cone v hv) ≅
      DGHomotopyCategory.of R (cone (coneHomOfHomotopy hu hw (dgId R P) v 0)
        (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)) where
  hom := homOf R (coneCompHom hu hv hw huv)
    ((mem_dgCycles R).mpr (dgDifferential_coneCompHom hu hv hw huv))
  inv := homOf R (coneCompInv hu hv hw huv)
    ((mem_dgCycles R).mpr (dgDifferential_coneCompInv hu hv hw huv))
  hom_inv_id :=
    homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_coneCompHom_coneCompInv hu hv hw huv)
  inv_hom_id := by
    rw [homOf_comp, ← homOf_dgId, homOf_eq_iff, mem_dgBoundaries, dgCompZero_def]
    exact ⟨_, dgDifferential_coneCompHomotopy hu hv hw huv⟩

@[simp]
theorem coneCompIso_hom :
    (coneCompIso hu hv hw huv).hom = homOf R (coneCompHom hu hv hw huv)
      ((mem_dgCycles R).mpr (dgDifferential_coneCompHom hu hv hw huv)) :=
  (rfl)

@[simp]
theorem coneCompIso_inv :
    (coneCompIso hu hv hw huv).inv = homOf R (coneCompInv hu hv hw huv)
      ((mem_dgCycles R).mpr (dgDifferential_coneCompInv hu hv hw huv)) :=
  (rfl)

/-- The triangle `cone u ⟶ cone w ⟶ cone v ⟶ (cone u)⟦1⟧` of the octahedral axiom, for
`w = u ≫ v`: the classes of the morphisms of cones induced by `(𝟙 P, v)` and by `(u, 𝟙 S)`, and of
the projection of `cone v` onto `Q⟦1⟧` followed by the shift of the inclusion of `Q` into
`cone u`. -/
-- The body is exposed so that the triangle is definitionally the one required by the octahedral
-- axiom in `MathlibExt.DGSource.DGTwistedObject.isTriangulated`.
@[expose]
noncomputable def coneCompTriangle :
    Triangle (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :=
  Triangle.mk
    (homOf R (coneHomOfHomotopy hu hw (dgId R P) v 0)
      ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
    (homOf R (coneHomOfHomotopy hw hv u (dgId R S) 0)
      ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy_zero_dgId hu hv hw huv)))
    (homOf R (extensionSnd R (dgDifferential_coneMorphism hv))
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
      (homOf R (extensionInl R (dgDifferential_coneMorphism hu))
        ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)))⟦(1 : ℤ)⟧')

@[simp]
theorem coneCompTriangle_obj₁ :
    (coneCompTriangle hu hv hw huv).obj₁ = DGHomotopyCategory.of R (cone u hu) :=
  (rfl)

@[simp]
theorem coneCompTriangle_obj₂ :
    (coneCompTriangle hu hv hw huv).obj₂ = DGHomotopyCategory.of R (cone w hw) :=
  (rfl)

@[simp]
theorem coneCompTriangle_obj₃ :
    (coneCompTriangle hu hv hw huv).obj₃ = DGHomotopyCategory.of R (cone v hv) :=
  (rfl)

@[simp]
theorem coneCompTriangle_mor₁ :
    (coneCompTriangle hu hv hw huv).mor₁ = homOf R (coneHomOfHomotopy hu hw (dgId R P) v 0)
      ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)) :=
  (rfl)

@[simp]
theorem coneCompTriangle_mor₂ :
    (coneCompTriangle hu hv hw huv).mor₂ = homOf R (coneHomOfHomotopy hw hv u (dgId R S) 0)
      ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy_zero_dgId hu hv hw huv)) :=
  (rfl)

@[simp]
theorem coneCompTriangle_mor₃ :
    (coneCompTriangle hu hv hw huv).mor₃ =
      homOf R (extensionSnd R (dgDifferential_coneMorphism hv))
          ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
        (homOf R (extensionInl R (dgDifferential_coneMorphism hu))
          ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)))⟦(1 : ℤ)⟧' :=
  (rfl)

/-- **The triangle of the octahedral axiom is distinguished**: the triangle
`cone u ⟶ cone w ⟶ cone v ⟶ (cone u)⟦1⟧` is isomorphic to the cone triangle of
`cone u ⟶ cone w`, by the identities and the comparison isomorphism
`cone v ≅ cone (cone u ⟶ cone w)`. -/
theorem coneCompTriangle_mem_distinguishedTriangles :
    coneCompTriangle hu hv hw huv ∈ distinguishedTriangles R C := by
  refine isomorphic_distinguished _ (coneTriangle_mem_distinguishedTriangles _
    (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneCompIso hu hv hw huv)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ?_ ?_)
  -- The objects of the triangles agree with those of the representatives by `rfl`, but cannot be
  -- rewritten inside the implicit objects of the composites.
  · -- The second morphism is the inclusion of `cone w` followed by the inverse comparison.
    have h : homOf R (coneHomOfHomotopy hw hv u (dgId R S) 0)
          ((mem_dgCycles R).mpr (dgDifferential_coneHomOfHomotopy_zero_dgId hu hv hw huv)) ≫
          (coneCompIso hu hv hw huv).hom =
        homOf R (extensionInl R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
          ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) := by
      rw [← homOf_comp_eq_homOf_of_dgComp_eq R
          ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _))
          ((mem_dgCycles R).mpr (dgDifferential_coneCompInv hu hv hw huv)) _
          (dgComp_extensionInl_coneCompInv hu hv hw huv),
        ← coneCompIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact h.trans (Category.id_comp _).symm
  · have h : homOf R (extensionSnd R (dgDifferential_coneMorphism hv))
          ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
          homOf R ((shiftFunctor R 1).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
            ((shiftFunctor R 1).dgMap_mem_dgCycles
              ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _))) =
        (coneCompIso hu hv hw huv).hom ≫ homOf R (extensionSnd R (dgDifferential_coneMorphism
          (dgDifferential_coneHomOfHomotopy_dgId_zero hu hv hw huv)))
          ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
      simp only [coneCompIso_hom, homOf_comp, dgCompZero_def, dgComp_coneCompHom_extensionSnd]
    rw [← shiftFunctor_map_homOf 1 _ ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _))] at h
    exact (congrArg (fun f ↦ _ ≫ f) ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map_id _)).trans
      ((Category.comp_id _).trans h)

end coneComp

/-! ### The octahedral axiom -/

/-- **The homotopy category of twisted objects is triangulated.**  Every composable pair of
morphisms of the homotopy category is represented by closed morphisms `u : P ⟶ Q` and
`v : Q ⟶ S`, and the cone triangles of `u`, `v` and `u ≫ v` fit into the octahedron whose third
triangle is `MathlibExt.DGSource.DGTwistedObject.coneCompTriangle`. -/
instance isTriangulated :
    IsTriangulated
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) := by
  refine IsTriangulated.mk' fun X₁ X₂ X₃ f g ↦ ?_
  obtain ⟨P, rfl⟩ := of_surjective R X₁
  obtain ⟨Q, rfl⟩ := of_surjective R X₂
  obtain ⟨S, rfl⟩ := of_surjective R X₃
  obtain ⟨u, hu, rfl⟩ := exists_homOf_eq R f
  obtain ⟨v, hv, rfl⟩ := exists_homOf_eq R g
  have hw := dgCompZero_mem_dgCycles R hu hv
  rw [mem_dgCycles] at hu hv hw
  have huv : dgComp R u v (add_zero 0) = dgCompZero R u v := (dgCompZero_def R u v).symm
  refine ⟨_, _, _, _, _, _, homOf R u ((mem_dgCycles R).mpr hu),
    homOf R v ((mem_dgCycles R).mpr hv), Iso.refl _, Iso.refl _, Iso.refl _,
    (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm,
    _, _, coneTriangle_mem_distinguishedTriangles u hu,
    _, _, coneTriangle_mem_distinguishedTriangles v hv,
    homOf R (extensionInl R (dgDifferential_coneMorphism hw))
      ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)),
    homOf R (extensionSnd R (dgDifferential_coneMorphism hw))
      ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)),
    by rw [homOf_comp]; exact coneTriangle_mem_distinguishedTriangles _ hw,
    ⟨{ m₁ := (coneCompTriangle hu hv hw huv).mor₁
       m₃ := (coneCompTriangle hu hv hw huv).mor₂
       comm₁ := by
         simp only [coneCompTriangle_mor₁, homOf_comp, dgCompZero_def,
           dgComp_extensionInl_coneHomOfHomotopy]
       comm₂ := homOf_comp_eq_homOf_of_dgComp_eq R _ _
         ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) (by
           rw [dgComp_coneHomOfHomotopy_extensionSnd, EnrichedFunctor.dgMap_dgId, dgComp_dgId])
       comm₃ := by
         simp only [coneCompTriangle_mor₂, homOf_comp, dgCompZero_def,
           dgComp_extensionInl_coneHomOfHomotopy, dgId_dgComp]
       comm₄ := by
         rw [shiftFunctor_map_homOf]
         exact (homOf_comp R _ _ _ _).trans (homOf_comp_eq_homOf_of_dgComp_eq R _ _ _
           ((dgComp_coneHomOfHomotopy_extensionSnd hw hv u (dgId R S) 0).trans
             (dgCompZero_def R _ _).symm)).symm
       mem := coneCompTriangle_mem_distinguishedTriangles hu hv hw huv }⟩⟩

/-! ### Triangulated subcategories are closed under extensions -/

section extension

open ObjectProperty

variable {S : ObjectProperty
    (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))}
  [S.IsTriangulated] [S.IsClosedUnderIsomorphisms]

/-- **A triangulated subcategory closed under isomorphisms is closed under extensions of twisted
objects**: the extension of `Q` by `P` along a closed degree-one morphism `g : Q ⟶ P` is
isomorphic to the cone of the closed degree-zero morphism `Q⟦-1⟧ ⟶ Q ⟶ P` underlying `g`, the
third object of a distinguished triangle whose first two objects are `Q⟦-1⟧` and `P`. -/
theorem prop_extension {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0) (hP : S (of R P)) (hQ : S (of R Q)) :
    S (of R (extension P Q g hg)) := by
  have hu : dgDifferential R 0 (dgComp R (fromShift Q (-1)) g (neg_add_cancel 1)) = 0 := by
    rw [dgDifferential_dgComp, dgDifferential_fromShift, hg, zero_dgComp, dgComp_zero, smul_zero,
      add_zero]
  -- `Q` is isomorphic to `Q⟦-1⟧⟦1⟧` through the comparison morphisms of the shifts.
  refine S.prop_of_iso (extensionIsoOfIso R
      (φ := dgComp R (toShift Q (-1)) (toShift ((shiftFunctor R (-1)).obj Q) 1) (by omega))
      (ψ := dgComp R (fromShift ((shiftFunctor R (-1)).obj Q) 1) (fromShift Q (-1)) (by omega))
      ?_ ?_ ?_ ?_).symm
    (S.ext_of_isTriangulatedClosed₃ _ (coneTriangle_mem_distinguishedTriangles _ hu)
      (by rw [coneTriangle_obj₁, ← shiftFunctor_obj_of]; exact S.le_shift (-1) _ hQ) hP)
  · rw [dgDifferential_dgComp, dgDifferential_toShift, dgDifferential_toShift, zero_dgComp,
      dgComp_zero, smul_zero, add_zero]
  · rw [dgComp_assoc R (p := -(-1)) (q := -1) (r := 0) (pq := 0) (qr := -1) (n := 0) _ _ _
      (by omega) (by omega) (by omega), dgComp_toShift_fromShift_assoc, dgComp_toShift_fromShift]
  · rw [dgComp_assoc R (p := 1) (q := -1) (r := 0) (pq := 0) (qr := -1) (n := 0) _ _ _
      (by omega) (by omega) (by omega), dgComp_fromShift_toShift_assoc, dgComp_fromShift_toShift]
  · rw [coneMorphism_def, dgComp_assoc R (p := -(-1)) (q := -1) (r := 1) (pq := 0) (qr := 0)
      (n := 1) _ _ _ (by omega) (by omega) (by omega), dgComp_toShift_fromShift_assoc,
      dgComp_toShift_fromShift_assoc]

end extension

end DGTwistedObject

end MathlibExt.DGSource
