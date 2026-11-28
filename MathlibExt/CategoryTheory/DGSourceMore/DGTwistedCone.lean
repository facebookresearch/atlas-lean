/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Cone.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedExtension
public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedShift

/-!
# The cone of a closed morphism of twisted objects

Let `C` be a differential graded category and let `u : P ⟶ Q` be a closed degree-zero morphism
of twisted objects of the additive closure of the shift closure of `C`.  Its **cone**
`MathlibExt.DGSource.DGTwistedObject.cone u` is the twisted object `(Q ⊕ P⟦1⟧, δ)` whose twisting matrix
has the twists of `Q` and of the shift `P⟦1⟧` on the diagonal and, in the block from `P⟦1⟧` to
`Q`, the degree-one morphism `P⟦1⟧ ⟶ P ⟶ Q` obtained by composing `u` with the comparison
morphism `MathlibExt.DGSource.DGTwistedObject.fromShift` (`MathlibExt.DGSource.DGTwistedObject.coneMorphism`).  It is the
extension of `P⟦1⟧` by `Q` along this morphism (see
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedExtension.lean`), which supplies its Maurer–Cartan equation,
the closed degree-zero morphisms `Q ⟶ cone u ⟶ P⟦1⟧` with zero composite, and their graded
splitting.  In particular, a closed morphism `f : X ⟶ Y` of `C`, viewed as a morphism of one-term
twisted objects `X[0] ⟶ Y[0]`, has a cone whose underlying object is `Y[0] ⊕ X[1]`.

These maps give the candidate triangle `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` of the pretriangulated envelope.
In the homotopy category both remaining consecutive composites vanish: `u` followed by the
inclusion of `Q` is the differential of minus the comparison morphism `P ⟶ P⟦1⟧` followed by the
inclusion of `P⟦1⟧`, and the projection onto `P⟦1⟧` followed by the shift of `u` is the
differential of minus the projection onto `Q` followed by the comparison morphism `Q ⟶ Q⟦1⟧`.
The second computation uses the Koszul-sign naturality of the comparison morphisms
(`MathlibExt.DGSource.DGTwistedObject.dgComp_toShift`), whose sign is trivial in degree zero.

The cone depends only on the homotopy class of `u`: if `u - u' = d k` for a degree `-1`
morphism `k : P ⟶ Q`, then `cone u` and `cone u'` are isomorphic in the homotopy category, by the
isomorphism of extensions along homotopic morphisms applied to minus `P⟦1⟧ ⟶ P` followed by `k`.

The cone of the zero morphism is the extension along zero, the direct sum `Q ⊕ P⟦1⟧` of twisted
objects.  If `u` has an inverse `u' : Q ⟶ P` of degree zero, then `u'` followed by the comparison
morphism `P ⟶ P⟦1⟧` is a degree `-1` inverse of the twisting entry `P⟦1⟧ ⟶ Q`, so the cone of an
isomorphism, and in particular `Cone(id_P)`, is contractible: it is a zero object of the
homotopy category.

The shift of a cone is the cone of the shifted morphism: for `n : ℤ`, the closed degree-zero
isomorphism `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` (`MathlibExt.DGSource.DGTwistedObject.shiftConeHom`) is the shift of
the projection onto `Q` on the summand `Q⟦n⟧`, and `(-1)^n` times the comparison
`P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` of `MathlibExt.DGSource.DGTwistedObject.shiftCommHom` on the summand `P⟦1⟧⟦n⟧`.  It is
closed because the shift by `n` of the twisting entry `P⟦1⟧ ⟶ P ⟶ Q` of `cone u` is `(-1)^n`
times this comparison followed by the twisting entry `P⟦n⟧⟦1⟧ ⟶ P⟦n⟧ ⟶ Q⟦n⟧` of `cone (u⟦n⟧)`
(`MathlibExt.DGSource.DGTwistedObject.dgMap_coneMorphism`).

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.coneMorphism`: a degree-zero morphism `P ⟶ Q` as the degree-one
  morphism `P⟦1⟧ ⟶ Q`.
* `MathlibExt.DGSource.DGTwistedObject.cone`: the cone of a closed degree-zero morphism.
* `MathlibExt.DGSource.DGTwistedObject.coneIsoOfHomotopy`: the isomorphism in the homotopy category between
  the cones of homotopic morphisms.
* `MathlibExt.DGSource.DGTwistedObject.shiftConeHom` and `MathlibExt.DGSource.DGTwistedObject.shiftConeInv`: the mutually
  inverse closed degree-zero morphisms `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` and
  `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧`.
* `MathlibExt.DGSource.DGTwistedObject.shiftConeIso`: the induced isomorphism `(cone u)⟦n⟧ ≅ cone (u⟦n⟧)` in
  the homotopy category.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_coneMorphism`: the degree-one morphism underlying a
  closed morphism is closed.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_dgComp_toShift_extensionInr_cone` and
  `MathlibExt.DGSource.DGTwistedObject.homOf_comp_homOf_extensionInl_cone_eq_zero`: `u` followed by the
  inclusion of `Q` into the cone is a boundary, so it vanishes in the homotopy category.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_dgComp_extensionFst_toShift_cone` and
  `MathlibExt.DGSource.DGTwistedObject.homOf_extensionSnd_cone_comp_map_homOf_eq_zero`: the projection of the
  cone onto `P⟦1⟧` followed by the shift of `u` is a boundary, so it vanishes in the homotopy
  category.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_neg_dgComp_fromShift`: a homotopy from `u` to `u'`
  gives a homotopy between the twisting entries of their cones.
* `MathlibExt.DGSource.DGTwistedObject.cone_zero`: the cone of the zero morphism is the direct sum
  `Q ⊕ P⟦1⟧`.
* `MathlibExt.DGSource.DGTwistedObject.isZero_cone_of_dgComp_eq_dgId`: the cone of an isomorphism is a zero
  object of the homotopy category.
* `MathlibExt.DGSource.DGTwistedObject.isZero_of_cone_dgId`: `Cone(id_P)` is contractible.
* `MathlibExt.DGSource.DGTwistedObject.dgMap_coneMorphism`: the shift of the twisting entry of a cone.
* `MathlibExt.DGSource.DGTwistedObject.dgComp_shiftConeHom_shiftConeInv` and
  `MathlibExt.DGSource.DGTwistedObject.dgComp_shiftConeInv_shiftConeHom`: the comparisons of cones are
  inverse.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, whose isomorphism
  `CochainComplex.mappingCone.shiftIso` between shifted mapping cones and mapping cones of shifted
  morphisms is followed for the shifts of cones.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]
  {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}

variable (R) in
/-- A degree-zero morphism `u : P ⟶ Q` of twisted objects, as the degree-one morphism
`P⟦1⟧ ⟶ P ⟶ Q`: the comparison morphism `MathlibExt.DGSource.DGTwistedObject.fromShift` followed by `u`. -/
noncomputable def coneMorphism (u : DGHom R 0 P Q) : DGHom R 1 ((shiftFunctor R 1).obj P) Q :=
  dgComp R (fromShift P 1) u (add_zero 1)

/-- The degree-one morphism underlying `u` is `P⟦1⟧ ⟶ P` followed by `u`. -/
theorem coneMorphism_def (u : DGHom R 0 P Q) :
    coneMorphism R u = dgComp R (fromShift P 1) u (add_zero 1) :=
  (rfl)

variable (P Q) in
/-- The degree-one morphism underlying the zero morphism is zero. -/
@[simp]
theorem coneMorphism_zero : coneMorphism R (0 : DGHom R 0 P Q) = 0 :=
  dgComp_zero R _ _

/-- The degree-one morphism underlying a sum is the sum of the underlying morphisms. -/
@[simp]
theorem coneMorphism_add (u u' : DGHom R 0 P Q) :
    coneMorphism R (u + u') = coneMorphism R u + coneMorphism R u' :=
  dgComp_add R _ _ _ _

/-- The degree-one morphism underlying `-u` is minus the one underlying `u`. -/
@[simp]
theorem coneMorphism_neg (u : DGHom R 0 P Q) : coneMorphism R (-u) = -coneMorphism R u :=
  dgComp_neg R _ _ _

/-- The degree-one morphism underlying a difference is the difference of the underlying
morphisms. -/
@[simp]
theorem coneMorphism_sub (u u' : DGHom R 0 P Q) :
    coneMorphism R (u - u') = coneMorphism R u - coneMorphism R u' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, coneMorphism_add, coneMorphism_neg]

/-- The degree-one morphism `P⟦1⟧ ⟶ Q` underlying a closed morphism `u : P ⟶ Q` is closed. -/
theorem dgDifferential_coneMorphism {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0) :
    dgDifferential R 1 (coneMorphism R u) = 0 := by
  rw [coneMorphism_def, dgDifferential_dgComp, dgDifferential_fromShift, hu, zero_dgComp,
    dgComp_zero, smul_zero, add_zero]

/-- The morphism `P⟦1⟧ ⟶ Q` underlying `u` followed by `k` is `P⟦1⟧ ⟶ P` followed by `u` and `k`;
unlike `MathlibExt.DGSource.DGTwistedObject.coneMorphism_def`, this rewrites `coneMorphism R u` only where it
is composed, not where it is the twist of a cone. -/
theorem dgComp_coneMorphism {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
    {q n : ℤ} (u : DGHom R 0 P Q) (k : DGHom R q Q Z) (h : 1 + q = n) :
    dgComp R (coneMorphism R u) k h = dgComp R (fromShift P 1) (dgComp R u k (zero_add q)) h :=
  dgComp_assoc R _ _ _ (add_zero 1) (zero_add q) (by omega)

/-- The **cone** of a closed degree-zero morphism `u : P ⟶ Q` of twisted objects: the twisted
object `(Q ⊕ P⟦1⟧, δ)` whose twisting matrix has the twists of `Q` and `P⟦1⟧` on the diagonal
and the morphism `P⟦1⟧ ⟶ P ⟶ Q` underlying `u` in the block from `P⟦1⟧` to `Q`. -/
-- This is reducible so that the cone is reducibly an extension, whose API then applies.
noncomputable abbrev cone (u : DGHom R 0 P Q) (hu : dgDifferential R 0 u = 0) :
    DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)) :=
  extension Q ((shiftFunctor R 1).obj P) (coneMorphism R u) (dgDifferential_coneMorphism hu)

/-! ### The triangle of a cone -/

section triangle

variable {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0)

/-- **The composite `P ⟶ Q ⟶ cone u` is null-homotopic**: the comparison morphism `P ⟶ P⟦1⟧`
followed by the inclusion of `P⟦1⟧` into the cone has differential minus `u` followed by the
inclusion of `Q`. -/
theorem dgDifferential_dgComp_toShift_extensionInr_cone :
    dgDifferential R (-1)
        (dgComp R (toShift P 1) (extensionInr R (dgDifferential_coneMorphism hu))
          (add_zero (-1))) =
      -dgComp R u (extensionInl R (dgDifferential_coneMorphism hu)) (add_zero 0) := by
  rw [dgDifferential_dgComp, dgDifferential_toShift, zero_dgComp, zero_add,
    dgDifferential_extensionInr, dgComp_coneMorphism, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, dgComp_toShift_fromShift_assoc]

/-- **The composite `P ⟶ Q ⟶ cone u` vanishes in the homotopy category.** -/
theorem homOf_comp_homOf_extensionInl_cone_eq_zero :
    DGHomotopyCategory.homOf R u ((mem_dgCycles R).mpr hu) ≫
        DGHomotopyCategory.homOf R (extensionInl R (dgDifferential_coneMorphism hu))
          ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) =
      0 :=
  DGHomotopyCategory.homOf_comp_eq_zero_of_dgDifferential_eq_neg R _ _
    (dgDifferential_dgComp_toShift_extensionInr_cone hu)

/-- **The composite `cone u ⟶ P⟦1⟧ ⟶ Q⟦1⟧` is null-homotopic**: the projection of the cone onto
`Q` followed by the comparison morphism `Q ⟶ Q⟦1⟧` has differential minus the projection onto
`P⟦1⟧` followed by the shift of `u`. -/
theorem dgDifferential_dgComp_extensionFst_toShift_cone :
    dgDifferential R (-1)
        (dgComp R (extensionFst R (dgDifferential_coneMorphism hu)) (toShift Q 1)
          (zero_add (-1))) =
      -dgComp R (extensionSnd R (dgDifferential_coneMorphism hu))
        ((shiftFunctor R 1).dgMap 0 u) (add_zero 0) := by
  rw [dgDifferential_dgComp, dgDifferential_toShift, dgComp_zero, smul_zero, add_zero,
    dgDifferential_extensionFst, neg_dgComp,
    dgComp_assoc R _ (coneMorphism R u) _ (zero_add 1) (add_neg_cancel 1) (by omega),
    dgComp_coneMorphism,
    dgComp_toShift 1 u (zero_add (-1)), mul_zero, Int.negOnePow_zero, one_smul,
    dgComp_fromShift_toShift_assoc]

/-- **The composite `cone u ⟶ P⟦1⟧ ⟶ Q⟦1⟧` vanishes in the homotopy category.** -/
theorem homOf_extensionSnd_cone_comp_map_homOf_eq_zero :
    DGHomotopyCategory.homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
        (shiftFunctor R 1).mapDGHomotopyCategory.map (X := DGHomotopyCategory.of R P)
          (Y := DGHomotopyCategory.of R Q)
          (DGHomotopyCategory.homOf R u ((mem_dgCycles R).mpr hu)) =
      0 := by
  have h : DGHomotopyCategory.homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) ≫
      DGHomotopyCategory.homOf R ((shiftFunctor R 1).dgMap 0 u)
        ((shiftFunctor R 1).dgMap_mem_dgCycles ((mem_dgCycles R).mpr hu)) = 0 :=
    DGHomotopyCategory.homOf_comp_eq_zero_of_dgDifferential_eq_neg R _ _
      (dgDifferential_dgComp_extensionFst_toShift_cone hu)
  rw [(shiftFunctor R 1).mapDGHomotopyCategory_map_homOf u]
  -- `h` is the claim up to `MathlibExt.DGSource.EnrichedFunctor.mapDGHomotopyCategory_obj_of`, which holds by
  -- `rfl` but cannot be rewritten inside the implicit object of the composite.
  exact h

end triangle

variable (P Q) in
/-- **The cone of the zero morphism is the direct sum** `Q ⊕ P⟦1⟧`: the extension along the zero
morphism, whose twisting matrix has the twists of `Q` and `P⟦1⟧` on the diagonal and vanishes
off it. -/
@[simp]
theorem cone_zero :
    cone (0 : DGHom R 0 P Q) (map_zero _) =
      extension Q ((shiftFunctor R 1).obj P) 0 (map_zero _) := by
  simp only [cone, coneMorphism_zero]

/-! ### Cones of homotopic morphisms -/

/-- If `u - u' = d k` for a degree `-1` morphism `k : P ⟶ Q`, then the twisting entries of the
cones of `u` and `u'` differ by the differential of minus `P⟦1⟧ ⟶ P` followed by `k`. -/
theorem dgDifferential_neg_dgComp_fromShift {u u' : DGHom R 0 P Q} {k : DGHom R (-1) P Q}
    (hk : dgDifferential R (-1) k = u - u') :
    dgDifferential R 0 (-dgComp R (fromShift P 1) k (add_neg_cancel 1)) =
      coneMorphism R u - coneMorphism R u' := by
  rw [map_neg, dgDifferential_dgComp, dgDifferential_fromShift, zero_dgComp, hk,
    ← coneMorphism_sub, coneMorphism_def]
  simp only [zero_add, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg]

/-- **Cones of homotopic morphisms are isomorphic**: if `u - u' = d k` for a degree `-1`
morphism `k : P ⟶ Q`, then `cone u` and `cone u'` are isomorphic in the homotopy category.  The
isomorphism is the identity on `Q` and on `P⟦1⟧`, together with minus `P⟦1⟧ ⟶ P` followed by `k`
in the block from `P⟦1⟧` to `Q`. -/
-- This is reducible so that the API of `MathlibExt.DGSource.DGTwistedObject.extensionIsoOfHomotopy` applies.
noncomputable abbrev coneIsoOfHomotopy {u u' : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0)
    (hu' : dgDifferential R 0 u' = 0) {k : DGHom R (-1) P Q}
    (hk : dgDifferential R (-1) k = u - u') :
    DGHomotopyCategory.of R (cone u hu) ≅ DGHomotopyCategory.of R (cone u' hu') :=
  extensionIsoOfHomotopy R (dgDifferential_neg_dgComp_fromShift hk)

/-! ### Cones of isomorphisms are contractible -/

section contractible

variable {u : DGHom R 0 P Q} {u' : DGHom R 0 Q P}

/-- **The cone of an isomorphism is contractible**: if the closed degree-zero morphism
`u : P ⟶ Q` has a two-sided inverse `u' : Q ⟶ P` of degree zero, then its cone is a zero object
of the homotopy category of twisted objects. -/
theorem isZero_cone_of_dgComp_eq_dgId (hu : dgDifferential R 0 u = 0)
    (huu' : dgComp R u u' (add_zero 0) = dgId R P) (hu'u : dgComp R u' u (add_zero 0) = dgId R Q) :
    Limits.IsZero (DGHomotopyCategory.of R (cone u hu)) := by
  refine isZero_extension_of_dgComp_eq_dgId R _
    (g' := dgComp R u' (toShift P 1) (zero_add (-1))) ?_ ?_
  · rw [coneMorphism_def, dgComp_assoc R (fromShift P 1) u _ (add_zero 1) (zero_add (-1))
        (by omega),
      ← dgComp_assoc R u u' _ (add_zero 0) (zero_add (-1)) (by omega), huu', dgId_dgComp,
      dgComp_fromShift_toShift]
  · rw [coneMorphism_def, dgComp_assoc R u' (toShift P 1) _ (zero_add (-1)) (neg_add_cancel 1)
        (by omega),
      dgComp_toShift_fromShift_assoc, hu'u]

variable (R P) in
/-- **The cone of an identity is contractible**: `Cone(id_P)` is a zero object of the homotopy
category of twisted objects. -/
theorem isZero_of_cone_dgId :
    Limits.IsZero (DGHomotopyCategory.of R (cone (dgId R P) (dgDifferential_dgId R P))) :=
  isZero_cone_of_dgComp_eq_dgId _ (dgComp_dgId R _) (dgComp_dgId R _)

end contractible

/-! ### Shifts of cones -/

section shiftCone

open DGHomotopyCategory

/-- **The shift of the twisting entry of a cone**: the shift by `n` of the degree-one morphism
`P⟦1⟧ ⟶ P ⟶ Q` underlying `u` is `(-1)^n` times the comparison `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` followed by
the degree-one morphism `P⟦n⟧⟦1⟧ ⟶ P⟦n⟧ ⟶ Q⟦n⟧` underlying the shift of `u`. -/
theorem dgMap_coneMorphism (u : DGHom R 0 P Q) (n : ℤ) :
    (shiftFunctor R n).dgMap 1 (coneMorphism R u) =
      n.negOnePow • dgComp R (shiftCommHom P 1 n)
        (coneMorphism R ((shiftFunctor R n).dgMap 0 u)) (zero_add 1) := by
  rw [coneMorphism_def, coneMorphism_def, EnrichedFunctor.dgMap_dgComp, dgMap_fromShift,
    one_mul, units_smul_dgComp, dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega)]

variable {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0) (n : ℤ)

/-- The comparison `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)`: the shift of the projection onto `Q` followed by
the inclusion of `Q⟦n⟧`, plus `(-1)^n` times the shift of the projection onto `P⟦1⟧` followed by
the comparison `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` and the inclusion of `P⟦n⟧⟦1⟧`.  It is a closed isomorphism
with inverse `MathlibExt.DGSource.DGTwistedObject.shiftConeInv`. -/
noncomputable def shiftConeHom :
    DGHom R 0 ((shiftFunctor R n).obj (cone u hu))
      (cone ((shiftFunctor R n).dgMap 0 u) ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)) :=
  dgComp R ((shiftFunctor R n).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
      (extensionInl R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) +
    n.negOnePow • dgComp R ((shiftFunctor R n).dgMap 0
        (extensionSnd R (dgDifferential_coneMorphism hu)))
      (dgComp R (shiftCommHom P 1 n) (extensionInr R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0)) (add_zero 0)

/-- The comparison `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧`: the projection onto `Q⟦n⟧` followed by the shift
of the inclusion of `Q`, plus `(-1)^n` times the projection onto `P⟦n⟧⟦1⟧` followed by the
comparison `P⟦n⟧⟦1⟧ ⟶ P⟦1⟧⟦n⟧` and the shift of the inclusion of `P⟦1⟧`. -/
noncomputable def shiftConeInv :
    DGHom R 0
      (cone ((shiftFunctor R n).dgMap 0 u) ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))
      ((shiftFunctor R n).obj (cone u hu)) :=
  dgComp R (extensionFst R (dgDifferential_coneMorphism
      ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
      ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu))) (add_zero 0) +
    n.negOnePow • dgComp R (extensionSnd R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
      (dgComp R (shiftCommHom P n 1)
        ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        (add_zero 0)) (add_zero 0)

theorem shiftConeHom_def :
    shiftConeHom hu n =
      dgComp R ((shiftFunctor R n).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu)))
          (extensionInl R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) +
        n.negOnePow • dgComp R ((shiftFunctor R n).dgMap 0
            (extensionSnd R (dgDifferential_coneMorphism hu)))
          (dgComp R (shiftCommHom P 1 n) (extensionInr R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0)) (add_zero 0) :=
  (rfl)

theorem shiftConeInv_def :
    shiftConeInv hu n =
      dgComp R (extensionFst R (dgDifferential_coneMorphism
          ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
          ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
          (add_zero 0) +
        n.negOnePow • dgComp R (extensionSnd R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
          (dgComp R (shiftCommHom P n 1)
            ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
            (add_zero 0)) (add_zero 0) :=
  (rfl)

/-- The shift of the inclusion of `Q` into `cone u` followed by the comparison
`(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` is the inclusion of `Q⟦n⟧`. -/
@[simp↓]
theorem dgComp_dgMap_extensionInl_shiftConeHom :
    dgComp R ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        (shiftConeHom hu n) (add_zero 0) =
      extensionInl R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)) := by
  simp only [shiftConeHom_def, dgComp_add, dgComp_units_smul,
    (shiftFunctor R n).dgMap_dgComp_dgMap_assoc_of_eq_dgId (dgComp_extensionInl_extensionFst R _),
    (shiftFunctor R n).dgMap_dgComp_dgMap_assoc_of_eq_zero (dgComp_extensionInl_extensionSnd R _),
    smul_zero, add_zero]

/-- The shift of the inclusion of `P⟦1⟧` into `cone u` followed by the comparison
`(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` is `(-1)^n` times the comparison `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧` followed by
the inclusion of `P⟦n⟧⟦1⟧`. -/
@[simp↓]
theorem dgComp_dgMap_extensionInr_shiftConeHom :
    dgComp R ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        (shiftConeHom hu n) (add_zero 0) =
      n.negOnePow • dgComp R (shiftCommHom P 1 n) (extensionInr R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) := by
  simp only [shiftConeHom_def, dgComp_add, dgComp_units_smul,
    (shiftFunctor R n).dgMap_dgComp_dgMap_assoc_of_eq_zero (dgComp_extensionInr_extensionFst R _),
    (shiftFunctor R n).dgMap_dgComp_dgMap_assoc_of_eq_dgId (dgComp_extensionInr_extensionSnd R _),
    zero_add]

/-- The comparison `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` followed by the projection onto `P⟦n⟧⟦1⟧` is
`(-1)^n` times the shift of the projection onto `P⟦1⟧` followed by the comparison
`P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧`. -/
@[simp↓]
theorem dgComp_shiftConeHom_extensionSnd :
    dgComp R (shiftConeHom hu n) (extensionSnd R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (add_zero 0) =
      n.negOnePow • dgComp R ((shiftFunctor R n).dgMap 0
        (extensionSnd R (dgDifferential_coneMorphism hu))) (shiftCommHom P 1 n) (add_zero 0) := by
  simp only [shiftConeHom_def, add_dgComp, units_smul_dgComp,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, dgComp_dgId,
    zero_add]

/-- The inclusion of `Q⟦n⟧` into `cone (u⟦n⟧)` followed by the comparison
`cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` is the shift of the inclusion of `Q`. -/
@[simp↓]
theorem dgComp_extensionInl_shiftConeInv :
    dgComp R (extensionInl R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (shiftConeInv hu n) (add_zero 0) =
      (shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)) := by
  simp only [shiftConeInv_def, dgComp_add, dgComp_units_smul,
    dgComp_extensionInl_extensionFst_assoc, dgComp_extensionInl_extensionSnd_assoc, smul_zero,
    add_zero]

/-- The inclusion of `P⟦n⟧⟦1⟧` into `cone (u⟦n⟧)` followed by the comparison
`cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` is `(-1)^n` times the comparison `P⟦n⟧⟦1⟧ ⟶ P⟦1⟧⟦n⟧` followed by the
shift of the inclusion of `P⟦1⟧`. -/
@[simp↓]
theorem dgComp_extensionInr_shiftConeInv :
    dgComp R (extensionInr R (dgDifferential_coneMorphism
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu))) (shiftConeInv hu n) (add_zero 0) =
      n.negOnePow • dgComp R (shiftCommHom P n 1)
        ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        (add_zero 0) := by
  simp only [shiftConeInv_def, dgComp_add, dgComp_units_smul,
    dgComp_extensionInr_extensionFst_assoc, dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- Morphisms out of `(cone u)⟦n⟧` are determined by their composites with the shifts of the
inclusions of `Q` and of `P⟦1⟧`. -/
private theorem shiftFunctor_cone_dgHom_ext
    {Z : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))} {m : ℤ}
    {f f' : DGHom R m ((shiftFunctor R n).obj (cone u hu)) Z}
    (hl : dgComp R ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
      f (zero_add m) =
      dgComp R ((shiftFunctor R n).dgMap 0 (extensionInl R (dgDifferential_coneMorphism hu)))
        f' (zero_add m))
    (hr : dgComp R ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
      f (zero_add m) =
      dgComp R ((shiftFunctor R n).dgMap 0 (extensionInr R (dgDifferential_coneMorphism hu)))
        f' (zero_add m)) :
    f = f' := by
  rw [← dgId_dgComp R f, ← dgId_dgComp R f', ← EnrichedFunctor.dgMap_dgId,
    ← extension_total R
      (dgDifferential_coneMorphism hu),
    map_add, EnrichedFunctor.dgMap_dgComp, EnrichedFunctor.dgMap_dgComp, add_dgComp, add_dgComp,
    dgComp_assoc R _ _ f (add_zero 0) (zero_add m) (by omega),
    dgComp_assoc R _ _ f (add_zero 0) (zero_add m) (by omega),
    dgComp_assoc R _ _ f' (add_zero 0) (zero_add m) (by omega),
    dgComp_assoc R _ _ f' (add_zero 0) (zero_add m) (by omega), hl, hr]

/-- The comparisons `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftConeHom_shiftConeInv :
    dgComp R (shiftConeHom hu n) (shiftConeInv hu n) (add_zero 0) = dgId R _ := by
  refine shiftFunctor_cone_dgHom_ext hu n ?_ ?_ <;>
    rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0), dgComp_dgId]
  · rw [dgComp_dgMap_extensionInl_shiftConeHom, dgComp_extensionInl_shiftConeInv]
  · rw [dgComp_dgMap_extensionInr_shiftConeHom, units_smul_dgComp,
      dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_extensionInr_shiftConeInv,
      units_smul_dgComp_shiftCommHom_units_smul_dgComp_shiftCommHom]

/-- The comparisons `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` compose to the identity. -/
@[simp↓]
theorem dgComp_shiftConeInv_shiftConeHom :
    dgComp R (shiftConeInv hu n) (shiftConeHom hu n) (add_zero 0) = dgId R _ := by
  refine extension_dgHom_ext ?_ ?_ <;>
    rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0), dgComp_dgId]
  · rw [dgComp_extensionInl_shiftConeInv, dgComp_dgMap_extensionInl_shiftConeHom]
  · rw [dgComp_extensionInr_shiftConeInv, units_smul_dgComp,
      dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_dgMap_extensionInr_shiftConeHom,
      units_smul_dgComp_shiftCommHom_units_smul_dgComp_shiftCommHom]

/-- **The comparison `(cone u)⟦n⟧ ⟶ cone (u⟦n⟧)` is closed.** -/
@[simp↓]
theorem dgDifferential_shiftConeHom : dgDifferential R 0 (shiftConeHom hu n) = 0 := by
  -- Both terms are the shift of the projection onto `P⟦1⟧`, followed by the comparison
  -- `P⟦1⟧⟦n⟧ ⟶ P⟦n⟧⟦1⟧`, the twisting entry of `cone (u⟦n⟧)` and the inclusion of `Q⟦n⟧`,
  -- with opposite signs.
  have hfst : dgDifferential R 0
      ((shiftFunctor R n).dgMap 0 (extensionFst R (dgDifferential_coneMorphism hu))) =
      -(n.negOnePow • dgComp R
        ((shiftFunctor R n).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
        (dgComp R (shiftCommHom P 1 n) (coneMorphism R ((shiftFunctor R n).dgMap 0 u))
          (zero_add 1)) (zero_add 1)) := by
    rw [← EnrichedFunctor.dgMap_dgDifferential, dgDifferential_extensionFst, map_neg,
      EnrichedFunctor.dgMap_dgComp, dgMap_coneMorphism, dgComp_units_smul]
  have hsnd : dgDifferential R 0
      ((shiftFunctor R n).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu))) = 0 :=
    (shiftFunctor R n).dgDifferential_dgMap_eq_zero (dgDifferential_extensionSnd R _)
  simp -proj only [shiftConeHom_def, map_add, map_zsmul_unit, dgDifferential_dgComp, hfst, hsnd,
    dgDifferential_extensionInl, dgDifferential_shiftCommHom, dgDifferential_extensionInr,
    zero_dgComp, dgComp_zero, smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul]
  rw [neg_dgComp, units_smul_dgComp, dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega),
    dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) (by omega), neg_add_cancel]

/-- The comparison `cone (u⟦n⟧) ⟶ (cone u)⟦n⟧` is closed, as the inverse of a closed
morphism. -/
@[simp↓]
theorem dgDifferential_shiftConeInv : dgDifferential R 0 (shiftConeInv hu n) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_shiftConeHom hu n) (add_zero 0)
    (dgComp_shiftConeHom_shiftConeInv hu n) (dgComp_shiftConeInv_shiftConeHom hu n)

/-- **The shift of a cone is the cone of the shift**: in the homotopy category, `(cone u)⟦n⟧` is
isomorphic to `cone (u⟦n⟧)`, through the comparisons `MathlibExt.DGSource.DGTwistedObject.shiftConeHom` and
`MathlibExt.DGSource.DGTwistedObject.shiftConeInv`. -/
noncomputable def shiftConeIso :
    DGHomotopyCategory.of R ((shiftFunctor R n).obj (cone u hu)) ≅
      DGHomotopyCategory.of R (cone ((shiftFunctor R n).dgMap 0 u)
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)) where
  hom := homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n))
  inv := homOf R (shiftConeInv hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeInv hu n))
  hom_inv_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_shiftConeHom_shiftConeInv hu n)
  inv_hom_id := homOf_comp_eq_id_of_dgComp_eq_dgId R _ _ (dgComp_shiftConeInv_shiftConeHom hu n)

@[simp]
theorem shiftConeIso_hom :
    (shiftConeIso hu n).hom =
      homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n)) :=
  (rfl)

@[simp]
theorem shiftConeIso_inv :
    (shiftConeIso hu n).inv =
      homOf R (shiftConeInv hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeInv hu n)) :=
  (rfl)

end shiftCone

end DGTwistedObject

end MathlibExt.DGSource
