/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Extension.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: module/namespace paths are adapted for Atlas, and the
universes of the final independent section are redeclared explicitly.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGAdditiveClosure
public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedObject

/-!
# Extensions of twisted objects

Let `P` and `Q` be twisted objects of the additive closure of a differential graded category `E`,
and let `g : Q ⟶ P` be a closed morphism of degree one of twisted objects.  The **extension**
`MathlibExt.DGSource.DGTwistedObject.extension P Q g` is the twisted object `(P ⊕ Q, δ)` whose underlying
object is the direct sum `P ⊕ Q` in the additive closure and whose twisting matrix `δ` has the
twists `δ_P` and `δ_Q` on the diagonal blocks, `g` in the block from `Q` to `P`, and zero in the
block from `P` to `Q`.  Blockwise, the Maurer–Cartan equation `d δ = dgComp δ δ` is the
Maurer–Cartan equations of `δ_P` and `δ_Q` together with `d g = dgComp δ_Q g + dgComp g δ_P`, and
the last equation says exactly that `g` is closed for the twisted differential
(`MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionTwist`).

The extension comes with inclusions `MathlibExt.DGSource.DGTwistedObject.extensionInl`,
`MathlibExt.DGSource.DGTwistedObject.extensionInr` and projections `MathlibExt.DGSource.DGTwistedObject.extensionFst`,
`MathlibExt.DGSource.DGTwistedObject.extensionSnd` of degree zero satisfying the biproduct equations.  The
inclusion of `P` and the projection onto `Q` are closed, so `P ⟶ extension P Q g ⟶ Q` is a
sequence of closed degree-zero morphisms with zero composite, split as graded objects.  The
splitting need not be closed: the differential of the inclusion of `Q` is `g` followed by the
inclusion of `P`, and the differential of the projection onto `P` is minus the projection onto `Q`
followed by `g`.

If `g` is invertible, with inverse `g' : P ⟶ Q` of degree `-1`, the extension is contractible:
minus the projection onto `P`, followed by `g'` and the inclusion of `Q`, is a degree `-1`
endomorphism whose differential is the identity, so the extension is a zero object of the
homotopy category.

The extension depends only on the homotopy class of `g`, up to isomorphism in the homotopy
category.  If `g - g' = d k` for a degree-zero morphism `k : Q ⟶ P`, then the identity on the
summands together with `k` in the block from `Q` to `P` is a closed morphism
`extension P Q g ⟶ extension P Q g'`, with inverse the same construction for `-k`.

The extension is functorial in the second summand: a closed degree-zero morphism `φ : Q ⟶ Q'`
with `φ` followed by `g'` equal to `g` induces a closed morphism
`extension P Q g ⟶ extension P Q' g'`, the identity on `P` and `φ` on `Q`, and an isomorphism `φ`
induces an isomorphism in the homotopy category.

With `Q` the shift `P'⟦1⟧` of a twisted object `P'` and `g` the degree-one morphism
`P'⟦1⟧ ⟶ P' ⟶ P` underlying a closed degree-zero morphism `u : P' ⟶ P`, the extension is the
cone of `u`, the basic construction of the pretriangulated envelope of Bondal and Kapranov; see
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedCone.lean`.

A DG functor `G : E ⥤ E'` preserves extensions: the image under the induced DG functor of
`extension P Q g` is isomorphic in the homotopy category to the extension of the images of `P`
and `Q` along the image of `g`, through the closed morphisms built from the images of the
projections and inclusions of one extension and the inclusions and projections of the other.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.extensionTwist`: the block twisting matrix of an extension.
* `MathlibExt.DGSource.DGTwistedObject.extension`: the extension of `Q` by `P` along `g`.
* `MathlibExt.DGSource.DGTwistedObject.extensionInl`, `MathlibExt.DGSource.DGTwistedObject.extensionInr`,
  `MathlibExt.DGSource.DGTwistedObject.extensionFst`, `MathlibExt.DGSource.DGTwistedObject.extensionSnd`: the inclusions
  of and projections to the two summands.
* `MathlibExt.DGSource.DGTwistedObject.extensionHomOfHomotopy`: the morphism of extensions induced by a
  degree-zero morphism `k : Q ⟶ P`.
* `MathlibExt.DGSource.DGTwistedObject.extensionIsoOfHomotopy`: the isomorphism in the homotopy category
  between extensions along homotopic morphisms.
* `MathlibExt.DGSource.DGTwistedObject.extensionMap`: the morphism of extensions induced by a morphism of
  second summands.
* `MathlibExt.DGSource.DGTwistedObject.extensionIsoOfIso`: the isomorphism in the homotopy category between
  extensions along isomorphic second summands.
* `CategoryTheory.EnrichedFunctor.mapExtensionIso`: the isomorphism in the homotopy category
  between the image of an extension under a DG functor and the extension of the images.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionTwist`: the Maurer–Cartan equation.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionInl`,
  `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionSnd`: the inclusion of `P` and the projection
  onto `Q` are closed.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionInr`,
  `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionFst`: the differentials of the other two
  structure maps.
* `MathlibExt.DGSource.DGTwistedObject.dgComp_extensionInl_extensionSnd` and the other biproduct equations:
  the composite `P ⟶ extension P Q g ⟶ Q` vanishes, and the inclusions and projections exhibit
  the extension as the direct sum of `P` and `Q` as a graded object.
* `MathlibExt.DGSource.DGTwistedObject.extension_dgHom_ext`: morphisms out of an extension are determined by
  their composites with the two inclusions.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_neg_dgComp_extensionFst_extensionInr` and
  `MathlibExt.DGSource.DGTwistedObject.isZero_extension_of_dgComp_eq_dgId`: an extension along an invertible
  morphism is contractible.
* `MathlibExt.DGSource.DGTwistedObject.isZero_of_isEmpty`: a twisted object with no summands is a zero object
  of the homotopy category; in particular the homotopy category has a zero object.
* `MathlibExt.DGSource.DGTwistedObject.extensionHomOfHomotopy_zero`: the zero morphism induces the identity.
* `MathlibExt.DGSource.DGTwistedObject.dgComp_extensionInl_extensionHomOfHomotopy`,
  `MathlibExt.DGSource.DGTwistedObject.dgComp_extensionHomOfHomotopy_extensionSnd` and their forms
  `MathlibExt.DGSource.DGTwistedObject.homOf_extensionInl_comp_extensionIsoOfHomotopy_hom`,
  `MathlibExt.DGSource.DGTwistedObject.extensionIsoOfHomotopy_hom_comp_homOf_extensionSnd` in the homotopy
  category: the morphism induced by `k` commutes with the inclusion of `P` and the projection
  onto `Q`.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionHomOfHomotopy` and
  `MathlibExt.DGSource.DGTwistedObject.dgComp_extensionHomOfHomotopy_neg`: the morphism induced by a homotopy
  `k` from `g` to `g'` is closed, and the morphisms induced by `k` and `-k` are mutually inverse.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionMap` and
  `MathlibExt.DGSource.DGTwistedObject.dgComp_extensionMap`: the morphism of extensions induced by a closed
  morphism compatible with the gluing morphisms is closed, and these morphisms compose.
* `CategoryTheory.EnrichedFunctor.dgComp_dgMap_extensionInl_mapExtensionHom`,
  `CategoryTheory.EnrichedFunctor.dgComp_mapExtensionHom_extensionSnd` and their companions: the
  comparison of the image of an extension with the extension of the images commutes with the
  structure maps.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

variable (R : Type v) [CommRing R] {E : Type u} [DGCategory R E]

open DGAdditiveClosure (dgHom_ext)

/- `matrixEquiv` is a local name for `MathlibExt.DGSource.DGAdditiveClosure.dgHomEquiv`, which identifies a
morphism of the additive closure with its matrix of entries; the unqualified name `dgHomEquiv`
refers to `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv` in this namespace. -/
open DGAdditiveClosure renaming dgHomEquiv → matrixEquiv

/-! ### Matrix entries of morphisms of twisted objects of the additive closure -/

variable {R} in
/-- Morphisms of twisted objects of the additive closure are determined by their matrix
entries. -/
private theorem dgHom_ext' {M N : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    {f f' : DGHom R n M N}
    (h : ∀ i j, matrixEquiv R _ _ n (dgHomEquiv R M N n f) i j =
      matrixEquiv R _ _ n (dgHomEquiv R M N n f') i j) :
    f = f' :=
  (dgHomEquiv R M N n).injective (dgHom_ext R h)

variable {R} in
/-- The twisted differential of a morphism of twisted objects of the additive closure,
entrywise. -/
theorem dgDifferential_apply {M N : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    (f : DGHom R n M N) (i : M.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ (n + 1) (dgHomEquiv R M N (n + 1) (dgDifferential R n f)) i j =
      dgDifferential R n (matrixEquiv R _ _ n (dgHomEquiv R M N n f) i j) +
        n.negOnePow • ∑ k, dgComp R (matrixEquiv R _ _ n (dgHomEquiv R M N n f) i k)
          (matrixEquiv R _ _ 1 N.twist k j) rfl -
        ∑ k, dgComp R (matrixEquiv R _ _ 1 M.twist i k)
          (matrixEquiv R _ _ n (dgHomEquiv R M N n f) k j)
          (add_comm 1 n) := by
  rw [dgHomEquiv_dgDifferential]
  simp only [map_sub, map_add, map_zsmul_unit, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    DGAdditiveClosure.dgHomEquiv_dgDifferential, DGAdditiveClosure.dgHomEquiv_dgComp]

variable {R} in
/-- Composition of twisted objects of the additive closure, entrywise. -/
theorem dgComp_apply {L M N : DGTwistedObject R (DGAdditiveClosure E)} {p q n : ℤ}
    (f : DGHom R p L M) (f' : DGHom R q M N) (h : p + q = n) (i : L.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ n (dgHomEquiv R L N n (dgComp R f f' h)) i j =
      ∑ k, dgComp R (matrixEquiv R _ _ p (dgHomEquiv R L M p f) i k)
        (matrixEquiv R _ _ q (dgHomEquiv R M N q f') k j) h := by
  rw [dgHomEquiv_dgComp, DGAdditiveClosure.dgHomEquiv_dgComp]

/-- The identity of a twisted object of the additive closure, entrywise. -/
private theorem dgId_apply (M : DGTwistedObject R (DGAdditiveClosure E)) (i j : M.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R M M 0 (dgId R M)) i j =
      matrixEquiv R _ _ 0 (dgId R M.obj) i j := by
  rw [dgHomEquiv_dgId]

variable {R} in
/-- The twisted differential of a degree-zero morphism of twisted objects of the additive
closure, entrywise. -/
theorem dgDifferential_apply_zero {M N : DGTwistedObject R (DGAdditiveClosure E)}
    (f : DGHom R 0 M N) (i : M.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ 1 (dgHomEquiv R M N 1 (dgDifferential R 0 f)) i j =
      ((dgHomComplex R (M.obj.X i) (N.obj.X j)).d 0 1).hom
          (matrixEquiv R _ _ 0 (dgHomEquiv R M N 0 f) i j) +
        ∑ k, dgComp R (matrixEquiv R _ _ 0 (dgHomEquiv R M N 0 f) i k)
          (matrixEquiv R _ _ 1 N.twist k j) (zero_add 1) -
        ∑ k, dgComp R (matrixEquiv R _ _ 1 M.twist i k)
          (matrixEquiv R _ _ 0 (dgHomEquiv R M N 0 f) k j) (add_zero 1) := by
  have h := dgDifferential_apply f i j
  rw [Int.negOnePow_zero, one_smul] at h
  -- `h` is the claim up to the definitional equality of the degrees `0 + 1` and `1`.
  exact h

/-- The entries of the identity of an object of the additive closure are closed, with the
differential written in degree `1` rather than `0 + 1`. -/
private theorem d_zero_one_dgHomEquiv_dgId (M : DGAdditiveClosure E) (i j : M.ι) :
    ((dgHomComplex R (M.X i) (M.X j)).d 0 1).hom (matrixEquiv R _ _ 0 (dgId R M) i j) = 0 :=
  DGAdditiveClosure.dgDifferential_dgHomEquiv_dgId R M i j

/-- The Maurer–Cartan equation of a twisted object of the additive closure, entrywise. -/
private theorem dgDifferential_twist_apply (M : DGTwistedObject R (DGAdditiveClosure E))
    (i j : M.obj.ι) :
    dgDifferential R 1 (matrixEquiv R _ _ 1 M.twist i j) =
      ∑ k, dgComp R (matrixEquiv R _ _ 1 M.twist i k)
      (matrixEquiv R _ _ 1 M.twist k j) rfl := by
  rw [← DGAdditiveClosure.dgHomEquiv_dgDifferential, dgDifferential_twist,
    DGAdditiveClosure.dgHomEquiv_dgComp]

variable {R} in
/-- A closed degree-one morphism `g : Q ⟶ P` of twisted objects of the additive closure,
entrywise: `d g = dgComp δ_Q g + dgComp g δ_P`. -/
private theorem dgDifferential_apply_of_closed {P Q : DGTwistedObject R (DGAdditiveClosure E)}
    {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0) (i : Q.obj.ι) (j : P.obj.ι) :
    dgDifferential R 1 (matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j) =
      ∑ k, dgComp R (matrixEquiv R _ _ 1 Q.twist i k)
          (matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) k j) rfl +
        ∑ k, dgComp R (matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i k)
          (matrixEquiv R _ _ 1 P.twist k j) rfl := by
  have h := dgDifferential_apply g i j
  rw [hg, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply, Int.negOnePow_one, Units.neg_smul,
    one_smul] at h
  rw [← sub_eq_zero, ← h.symm]
  abel

/-! ### The twisting matrix of an extension -/

/-- The twisting matrix of an extension: `δ_P` and `δ_Q` on the diagonal blocks, `g` in the
block from `Q` to `P`, and zero in the block from `P` to `Q`. -/
private noncomputable def extensionTwistMatrix (P Q : DGTwistedObject R (DGAdditiveClosure E))
    (g : DGHom R 1 Q P) :
    ∀ i j : (P.obj.sum Q.obj).ι, DGHom R 1 ((P.obj.sum Q.obj).X i) ((P.obj.sum Q.obj).X j)
  | .inl i, .inl j => matrixEquiv R _ _ 1 P.twist i j
  | .inl _, .inr _ => 0
  | .inr i, .inl j => matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j
  | .inr i, .inr j => matrixEquiv R _ _ 1 Q.twist i j

/-- The **twisting matrix of an extension** of `Q` by `P` along a degree-one morphism
`g : Q ⟶ P`: the degree-one endomorphism of `P ⊕ Q` with the twists of `P` and `Q` on the
diagonal blocks, `g` in the block from `Q` to `P`, and zero in the block from `P` to `Q`. -/
noncomputable def extensionTwist (P Q : DGTwistedObject R (DGAdditiveClosure E))
    (g : DGHom R 1 Q P) : DGHom R 1 (P.obj.sum Q.obj) (P.obj.sum Q.obj) :=
  (matrixEquiv R _ _ 1).symm (extensionTwistMatrix R P Q g)

section extensionTwist

variable (P Q : DGTwistedObject R (DGAdditiveClosure E)) (g : DGHom R 1 Q P)

/-- The block of the twisting matrix of an extension on the summands of `P` is the twist of
`P`. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inl_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inl i) (.inl j) =
      matrixEquiv R _ _ 1 P.twist i j :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

/-- The block of the twisting matrix of an extension from the summands of `P` to those of `Q`
vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inl_inr (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inl i) (.inr j) = 0 :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

/-- The block of the twisting matrix of an extension from the summands of `Q` to those of `P` is
`g`. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inr_inl (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inr i) (.inl j) =
      matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

/-- The block of the twisting matrix of an extension on the summands of `Q` is the twist of
`Q`. -/
@[simp↓]
theorem dgHomEquiv_extensionTwist_inr_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extensionTwist R P Q g) (.inr i) (.inr j) =
      matrixEquiv R _ _ 1 Q.twist i j :=
  congrFun (congrFun (LinearEquiv.apply_symm_apply (matrixEquiv R _ _ 1) _) _) _

end extensionTwist

variable {R} in
/-- The twisting matrix of an extension along a closed morphism satisfies the Maurer–Cartan
equation. -/
theorem dgDifferential_extensionTwist {P Q : DGTwistedObject R (DGAdditiveClosure E)}
    {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0) :
    dgDifferential R 1 (extensionTwist R P Q g) =
      dgComp R (extensionTwist R P Q g) (extensionTwist R P Q g) rfl :=
  dgHom_ext R fun i j ↦ by
    rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, DGAdditiveClosure.dgHomEquiv_dgComp,
      Fintype.sum_sum_type]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [↓dgHomEquiv_extensionTwist_inl_inl, ↓dgHomEquiv_extensionTwist_inl_inr,
        ↓dgHomEquiv_extensionTwist_inr_inl, ↓dgHomEquiv_extensionTwist_inr_inr, zero_dgComp,
        dgComp_zero, map_zero, Finset.sum_const_zero, add_zero, zero_add]
    · exact dgDifferential_twist_apply R P i j
    · rw [dgDifferential_apply_of_closed hg]
      exact add_comm _ _
    · exact dgDifferential_twist_apply R Q i j

/-! ### The extension -/

variable {R} in
/-- The **extension** of `Q` by `P` along a closed degree-one morphism `g : Q ⟶ P` of twisted
objects of the additive closure: the twisted object `(P ⊕ Q, δ)` whose twisting matrix has the
twists of `P` and `Q` on the diagonal and `g` in the block from `Q` to `P`.  Its Maurer–Cartan
equation is `MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionTwist`. -/
-- This is reducible so that the underlying object of the extension is reducibly `P ⊕ Q` and its
-- twist reducibly `MathlibExt.DGSource.DGTwistedObject.extensionTwist`, whose entry lemmas then apply.
noncomputable abbrev extension (P Q : DGTwistedObject R (DGAdditiveClosure E)) (g : DGHom R 1 Q P)
    (hg : dgDifferential R 1 g = 0) : DGTwistedObject R (DGAdditiveClosure E) where
  obj := P.obj.sum Q.obj
  twist := extensionTwist R P Q g
  dgDifferential_twist := dgDifferential_extensionTwist hg

section twist

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0)

/- The entries of the twist of an extension, stated with the twist written as a projection of the
extension, the form in which it appears in the matrix entries of morphisms out of and into the
extension; `simp` does not see through this projection to the entry lemmas of
`MathlibExt.DGSource.DGTwistedObject.extensionTwist`. -/

@[simp↓]
theorem dgHomEquiv_twist_extension_inl_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inl i) (.inl j) =
      matrixEquiv R _ _ 1 P.twist i j :=
  dgHomEquiv_extensionTwist_inl_inl R P Q g i j

@[simp↓]
theorem dgHomEquiv_twist_extension_inl_inr (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inl i) (.inr j) = 0 :=
  dgHomEquiv_extensionTwist_inl_inr R P Q g i j

@[simp↓]
theorem dgHomEquiv_twist_extension_inr_inl (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inr i) (.inl j) =
      matrixEquiv R _ _ 1 (dgHomEquiv R Q P 1 g) i j :=
  dgHomEquiv_extensionTwist_inr_inl R P Q g i j

@[simp↓]
theorem dgHomEquiv_twist_extension_inr_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 1 (extension P Q g hg).twist (.inr i) (.inr j) =
      matrixEquiv R _ _ 1 Q.twist i j :=
  dgHomEquiv_extensionTwist_inr_inr R P Q g i j

end twist

/-! ### The structure maps of an extension -/

section structureMaps

variable (P Q : DGTwistedObject R (DGAdditiveClosure E))

/-- The matrix of the inclusion of `P` into `P ⊕ Q`. -/
private noncomputable def inlMatrix :
    ∀ (i : P.obj.ι) (k : (P.obj.sum Q.obj).ι), DGHom R 0 (P.obj.X i) ((P.obj.sum Q.obj).X k)
  | i, .inl j => matrixEquiv R _ _ 0 (dgId R P.obj) i j
  | _, .inr _ => 0

/-- The matrix of the inclusion of `Q` into `P ⊕ Q`. -/
private noncomputable def inrMatrix :
    ∀ (i : Q.obj.ι) (k : (P.obj.sum Q.obj).ι), DGHom R 0 (Q.obj.X i) ((P.obj.sum Q.obj).X k)
  | _, .inl _ => 0
  | i, .inr j => matrixEquiv R _ _ 0 (dgId R Q.obj) i j

/-- The matrix of the projection of `P ⊕ Q` onto `P`. -/
private noncomputable def fstMatrix :
    ∀ (k : (P.obj.sum Q.obj).ι) (j : P.obj.ι), DGHom R 0 ((P.obj.sum Q.obj).X k) (P.obj.X j)
  | .inl i, j => matrixEquiv R _ _ 0 (dgId R P.obj) i j
  | .inr _, _ => 0

/-- The matrix of the projection of `P ⊕ Q` onto `Q`. -/
private noncomputable def sndMatrix :
    ∀ (k : (P.obj.sum Q.obj).ι) (j : Q.obj.ι), DGHom R 0 ((P.obj.sum Q.obj).X k) (Q.obj.X j)
  | .inl _, _ => 0
  | .inr i, j => matrixEquiv R _ _ 0 (dgId R Q.obj) i j

variable {P Q} {g : DGHom R 1 Q P} (hg : dgDifferential R 1 g = 0)

/-- The inclusion `P ⟶ extension P Q g` of the first summand, a closed morphism of degree
zero. -/
noncomputable def extensionInl : DGHom R 0 P (extension P Q g hg) :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (inlMatrix R P Q))

/-- The inclusion `Q ⟶ extension P Q g` of the second summand, a morphism of degree zero which
need not be closed: its differential is `g` followed by the inclusion of `P`. -/
noncomputable def extensionInr : DGHom R 0 Q (extension P Q g hg) :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (inrMatrix R P Q))

/-- The projection `extension P Q g ⟶ P` onto the first summand, a morphism of degree zero
which need not be closed: its differential is minus the projection onto `Q` followed by `g`. -/
noncomputable def extensionFst : DGHom R 0 (extension P Q g hg) P :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (fstMatrix R P Q))

/-- The projection `extension P Q g ⟶ Q` onto the second summand, a closed morphism of degree
zero. -/
noncomputable def extensionSnd : DGHom R 0 (extension P Q g hg) Q :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (sndMatrix R P Q))

/-- Entries of a morphism of twisted objects defined from its matrix. -/
private theorem dgHomEquiv_symm_symm_apply {M N : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    (F : ∀ i j, DGHom R n (M.obj.X i) (N.obj.X j)) (i : M.obj.ι) (j : N.obj.ι) :
    matrixEquiv R _ _ n
      (dgHomEquiv R M N n ((dgHomEquiv R M N n).symm ((matrixEquiv R _ _ n).symm F))) i j =
        F i j := by
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The block of the inclusion of `P` into an extension on the summands of `P` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionInl_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInl R hg)) i (.inl j) =
      matrixEquiv R _ _ 0 (dgId R P.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := P) (N := (extension P Q g hg)) (inlMatrix R P Q) i (Sum.inl j)

/-- The block of the inclusion of `P` into an extension to the summands of `Q` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionInl_inr (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInl R hg)) i (.inr j) = 0 :=
  dgHomEquiv_symm_symm_apply R (M := P) (N := (extension P Q g hg)) (inlMatrix R P Q) i (Sum.inr j)

/-- The block of the inclusion of `Q` into an extension to the summands of `P` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionInr_inl (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInr R hg)) i (.inl j) = 0 :=
  dgHomEquiv_symm_symm_apply R (M := Q) (N := (extension P Q g hg)) (inrMatrix R P Q) i (Sum.inl j)

/-- The block of the inclusion of `Q` into an extension on the summands of `Q` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionInr_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionInr R hg)) i (.inr j) =
      matrixEquiv R _ _ 0 (dgId R Q.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := Q) (N := (extension P Q g hg)) (inrMatrix R P Q) i (Sum.inr j)

/-- The block of the projection of an extension onto `P` on the summands of `P` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionFst_inl (i j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionFst R hg)) (.inl i) j =
      matrixEquiv R _ _ 0 (dgId R P.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := P) (fstMatrix R P Q) (Sum.inl i) j

/-- The block of the projection of an extension onto `P` from the summands of `Q` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionFst_inr (i : Q.obj.ι) (j : P.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionFst R hg)) (.inr i) j = 0 :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := P) (fstMatrix R P Q) (Sum.inr i) j

/-- The block of the projection of an extension onto `Q` from the summands of `P` vanishes. -/
@[simp↓]
theorem dgHomEquiv_extensionSnd_inl (i : P.obj.ι) (j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionSnd R hg)) (.inl i) j = 0 :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := Q) (sndMatrix R P Q) (Sum.inl i) j

/-- The block of the projection of an extension onto `Q` on the summands of `Q` is the
identity. -/
@[simp↓]
theorem dgHomEquiv_extensionSnd_inr (i j : Q.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (extensionSnd R hg)) (.inr i) j =
      matrixEquiv R _ _ 0 (dgId R Q.obj) i j :=
  dgHomEquiv_symm_symm_apply R (M := (extension P Q g hg)) (N := Q) (sndMatrix R P Q) (Sum.inr i) j

end structureMaps

/-! ### Differentials of the structure maps -/

section differentials

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0)

/-- The inclusion of `P` into an extension is closed. -/
@[simp↓]
theorem dgDifferential_extensionInl : dgDifferential R 0 (extensionInl R hg) = 0 :=
  dgHom_ext' (n := 1) fun i k ↦ by
    rw [dgDifferential_apply_zero, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply,
      Fintype.sum_sum_type]
    rcases k with j | j <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

/-- The projection of an extension onto `Q` is closed. -/
@[simp↓]
theorem dgDifferential_extensionSnd : dgDifferential R 0 (extensionSnd R hg) = 0 :=
  dgHom_ext' (n := 1) fun k j ↦ by
    rw [dgDifferential_apply_zero, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply,
      Fintype.sum_sum_type]
    rcases k with i | i <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

/-- The differential of the inclusion of `Q` into an extension along `g` is `g` followed by the
inclusion of `P`. -/
theorem dgDifferential_extensionInr :
    dgDifferential R 0 (extensionInr R hg) = dgComp R g (extensionInl R hg) (add_zero 1) :=
  dgHom_ext' (n := 1) fun i k ↦ by
    rw [dgDifferential_apply_zero, dgComp_apply, Fintype.sum_sum_type]
    rcases k with j | j <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

/-- The differential of the projection of an extension along `g` onto `P` is minus the
projection onto `Q` followed by `g`. -/
theorem dgDifferential_extensionFst :
    dgDifferential R 0 (extensionFst R hg) = -dgComp R (extensionSnd R hg) g (zero_add 1) :=
  dgHom_ext' (n := 1) fun k j ↦ by
    rw [dgDifferential_apply_zero, map_neg, map_neg, Pi.neg_apply, Pi.neg_apply, dgComp_apply,
      Fintype.sum_sum_type]
    rcases k with i | i <;> simp [-DGCategoryData.dgId_toDGCategory, d_zero_one_dgHomEquiv_dgId,
      ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inl_inr,
      ↓dgHomEquiv_twist_extension_inr_inl, ↓dgHomEquiv_twist_extension_inr_inr]

end differentials

/-! ### The biproduct equations -/

section biproduct

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0)

/-- The inclusion of `P` into an extension followed by the projection onto `P` is the
identity. -/
@[simp↓]
theorem dgComp_extensionInl_extensionFst :
    dgComp R (extensionInl R hg) (extensionFst R hg) (add_zero 0) = dgId R P :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, dgId_apply, Fintype.sum_sum_type]
    simp [-DGCategoryData.dgId_toDGCategory]

/-- The inclusion of `P` into an extension followed by the projection onto `Q` vanishes. -/
@[simp↓]
theorem dgComp_extensionInl_extensionSnd :
    dgComp R (extensionInl R hg) (extensionSnd R hg) (add_zero 0) = 0 :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply, Fintype.sum_sum_type]
    simp

/-- The inclusion of `Q` into an extension followed by the projection onto `P` vanishes. -/
@[simp↓]
theorem dgComp_extensionInr_extensionFst :
    dgComp R (extensionInr R hg) (extensionFst R hg) (add_zero 0) = 0 :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply, Fintype.sum_sum_type]
    simp

/-- The inclusion of `Q` into an extension followed by the projection onto `Q` is the
identity. -/
@[simp↓]
theorem dgComp_extensionInr_extensionSnd :
    dgComp R (extensionInr R hg) (extensionSnd R hg) (add_zero 0) = dgId R Q :=
  dgHom_ext' fun i j ↦ by
    rw [dgComp_apply, dgId_apply, Fintype.sum_sum_type]
    simp [-DGCategoryData.dgId_toDGCategory]

/-- **An extension is the direct sum of `P` and `Q` as a graded object**: the projections
followed by the inclusions sum to the identity. -/
theorem extension_total :
    dgComp R (extensionFst R hg) (extensionInl R hg) (add_zero 0) +
      dgComp R (extensionSnd R hg) (extensionInr R hg) (add_zero 0) = dgId R _ :=
  dgHom_ext' fun a b ↦ by
    rw [map_add, map_add, Pi.add_apply, Pi.add_apply, dgComp_apply, dgComp_apply, dgId_apply]
    rcases a with i | i <;> rcases b with j | j
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inl_inl]
      simp [-DGCategoryData.dgId_toDGCategory]
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inl_inr]
      simp
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inr_inl]
      simp
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inr_inr]
      simp [-DGCategoryData.dgId_toDGCategory]

variable {R hg} in
/-- **Morphisms out of an extension are determined by their restrictions to the summands**: two
morphisms out of an extension agree once they agree after the inclusions of `P` and of `Q`. -/
theorem extension_dgHom_ext {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    {f f' : DGHom R n (extension P Q g hg) Z}
    (hl : dgComp R (extensionInl R hg) f (zero_add n) =
      dgComp R (extensionInl R hg) f' (zero_add n))
    (hr : dgComp R (extensionInr R hg) f (zero_add n) =
      dgComp R (extensionInr R hg) f' (zero_add n)) :
    f = f' := by
  rw [← dgId_dgComp R f, ← dgId_dgComp R f',
    ← extension_total R hg, add_dgComp,
    add_dgComp, dgComp_assoc R _ _ f (add_zero 0) (zero_add n) (by omega),
    dgComp_assoc R _ _ f (add_zero 0) (zero_add n) (by omega),
    dgComp_assoc R _ _ f' (add_zero 0) (zero_add n) (by omega),
    dgComp_assoc R _ _ f' (add_zero 0) (zero_add n) (by omega), hl, hr]

/-- The inclusion of `P` followed by the projection onto `P` and then `x` is `x`. -/
@[simp↓]
theorem dgComp_extensionInl_extensionFst_assoc
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ} (x : DGHom R n P Z) :
    dgComp R (extensionInl R hg) (dgComp R (extensionFst R hg) x (zero_add n)) (zero_add n) =
      x := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInl_extensionFst, dgId_dgComp]

/-- The inclusion of `P` followed by the projection onto `Q` and then `x` vanishes. -/
@[simp↓]
theorem dgComp_extensionInl_extensionSnd_assoc
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ} (x : DGHom R n Q Z) :
    dgComp R (extensionInl R hg) (dgComp R (extensionSnd R hg) x (zero_add n)) (zero_add n) =
      0 := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInl_extensionSnd, zero_dgComp]

/-- The inclusion of `Q` followed by the projection onto `P` and then `x` vanishes. -/
@[simp↓]
theorem dgComp_extensionInr_extensionFst_assoc
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ} (x : DGHom R n P Z) :
    dgComp R (extensionInr R hg) (dgComp R (extensionFst R hg) x (zero_add n)) (zero_add n) =
      0 := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInr_extensionFst, zero_dgComp]

/-- The inclusion of `Q` followed by the projection onto `Q` and then `x` is `x`. -/
@[simp↓]
theorem dgComp_extensionInr_extensionSnd_assoc
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ} (x : DGHom R n Q Z) :
    dgComp R (extensionInr R hg) (dgComp R (extensionSnd R hg) x (zero_add n)) (zero_add n) =
      x := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInr_extensionSnd, dgId_dgComp]

end biproduct

/-! ### Extensions along invertible morphisms are contractible -/

section contractible

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0) {g' : DGHom R (-1) P Q}

/-- **The contracting homotopy of an extension along an invertible morphism**: if the closed
degree-one morphism `g : Q ⟶ P` has an inverse `g' : P ⟶ Q` of degree `-1`, then the differential
of minus the projection onto `P`, followed by `g'` and the inclusion of `Q`, is the identity of the
extension. -/
theorem dgDifferential_neg_dgComp_extensionFst_extensionInr
    (hgg' : dgComp R g g' (add_neg_cancel 1) = dgId R Q)
    (hg'g : dgComp R g' g (neg_add_cancel 1) = dgId R P) :
    dgDifferential R (-1)
        (-dgComp R (dgComp R (extensionFst R hg) g' (zero_add (-1))) (extensionInr R hg)
          (add_zero (-1))) =
      dgId R (extension P Q g hg) := by
  -- The inverse pairs cancel inside the two terms produced by the Leibniz rule.
  have hsnd : dgComp R (dgComp R (extensionSnd R hg) g (zero_add 1)) g' (add_neg_cancel 1) =
      extensionSnd R hg := by
    rw [dgComp_assoc R _ g g' (zero_add 1) (add_neg_cancel 1) (by omega), hgg', dgComp_dgId]
  have hfst : dgComp R (dgComp R (extensionFst R hg) g' (zero_add (-1)))
      (dgComp R g (extensionInl R hg) (add_zero 1)) (neg_add_cancel 1) =
      dgComp R (extensionFst R hg) (extensionInl R hg) (add_zero 0) := by
    rw [dgComp_assoc R _ g' _ (zero_add (-1)) (neg_add_cancel 1) (by omega),
      ← dgComp_assoc R g' g _ (neg_add_cancel 1) (add_zero 1) (by omega), hg'g, dgId_dgComp]
  -- Expand by the Leibniz rule; `g'` is closed, being inverse to the closed morphism `g`.
  rw [map_neg, dgDifferential_dgComp, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionInr, dgDifferential_eq_zero_of_dgComp_eq_dgId R hg _ hgg' hg'g]
  simp only [dgComp_zero, smul_zero, add_zero, neg_dgComp, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, hsnd, hfst]
  rw [← extension_total R hg]
  abel

/-- **An extension along an invertible morphism is contractible**: if the closed degree-one
morphism `g : Q ⟶ P` has an inverse of degree `-1`, then the extension of `Q` by `P` along `g` is
a zero object of the homotopy category. -/
theorem isZero_extension_of_dgComp_eq_dgId (hgg' : dgComp R g g' (add_neg_cancel 1) = dgId R Q)
    (hg'g : dgComp R g' g (neg_add_cancel 1) = dgId R P) :
    Limits.IsZero (DGHomotopyCategory.of R (extension P Q g hg)) :=
  (DGHomotopyCategory.isZero_of_iff_dgId_mem_dgBoundaries R _).mpr
    ((mem_dgBoundaries R).mpr
      ⟨_, dgDifferential_neg_dgComp_extensionFst_extensionInr R hg hgg' hg'g⟩)

end contractible

/-! ### The zero object -/

section zero

variable {R} in
/-- **A twisted object with no summands is a zero object of the homotopy category**: its identity
is the empty matrix, which is the differential of the zero morphism. -/
theorem isZero_of_isEmpty (P : DGTwistedObject R (DGAdditiveClosure E)) [IsEmpty P.obj.ι] :
    Limits.IsZero (DGHomotopyCategory.of R P) :=
  (DGHomotopyCategory.isZero_of_iff_dgId_mem_dgBoundaries R P).mpr ((mem_dgBoundaries R).mpr
    ⟨0, (dgHomEquiv R P P 0).injective (dgHom_ext R fun i ↦ isEmptyElim i)⟩)

/-- The homotopy category of twisted objects of an additive closure has a zero object: the empty
direct sum with the zero twist. -/
instance : Limits.HasZeroObject (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure E))) :=
  ⟨⟨_, isZero_of_isEmpty (ofObj R (⟨PEmpty, PEmpty.elim⟩ : DGAdditiveClosure E))⟩⟩

end zero

/-! ### Extensions along homotopic morphisms are isomorphic -/

section homotopy

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g g' : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0) (hg' : dgDifferential R 1 g' = 0)

/-- The degree-zero morphism `extension P Q g ⟶ extension P Q g'` induced by a degree-zero
morphism `k : Q ⟶ P`: the identity on the summands `P` and `Q`, together with `k` in the block
from `Q` to `P`.  It is closed when `d k = g - g'`
(`MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionHomOfHomotopy`). -/
noncomputable def extensionHomOfHomotopy (k : DGHom R 0 Q P) :
    DGHom R 0 (extension P Q g hg) (extension P Q g' hg') :=
  dgComp R (extensionFst R hg) (extensionInl R hg') (add_zero 0) +
    dgComp R (extensionSnd R hg) (extensionInr R hg') (add_zero 0) +
    dgComp R (extensionSnd R hg) (dgComp R k (extensionInl R hg') (add_zero 0)) (add_zero 0)

theorem extensionHomOfHomotopy_def (k : DGHom R 0 Q P) :
    extensionHomOfHomotopy R hg hg' k =
      dgComp R (extensionFst R hg) (extensionInl R hg') (add_zero 0) +
        dgComp R (extensionSnd R hg) (extensionInr R hg') (add_zero 0) +
        dgComp R (extensionSnd R hg) (dgComp R k (extensionInl R hg') (add_zero 0)) (add_zero 0) :=
  (rfl)

/-- The morphism of extensions induced by the zero morphism is the identity. -/
@[simp]
theorem extensionHomOfHomotopy_zero :
    extensionHomOfHomotopy R hg hg 0 = dgId R (extension P Q g hg) := by
  rw [extensionHomOfHomotopy_def, zero_dgComp, dgComp_zero, add_zero,
    extension_total]

/-- **The morphism of extensions induced by a homotopy is closed**: if `d k = g - g'`, then the
differential of `MathlibExt.DGSource.DGTwistedObject.extensionHomOfHomotopy` vanishes. -/
theorem dgDifferential_extensionHomOfHomotopy {k : DGHom R 0 Q P}
    (hk : dgDifferential R 0 k = g - g') :
    dgDifferential R 0 (extensionHomOfHomotopy R hg hg' k) = 0 := by
  rw [extensionHomOfHomotopy_def, map_add, map_add, dgDifferential_dgComp, dgDifferential_dgComp,
    dgDifferential_dgComp, dgDifferential_dgComp, dgDifferential_extensionFst,
    dgDifferential_extensionSnd, dgDifferential_extensionInl, dgDifferential_extensionInr, hk,
    neg_dgComp, dgComp_assoc R _ g _ (zero_add 1) (add_zero 1) (by omega), sub_eq_add_neg,
    add_dgComp, neg_dgComp]
  simp only [dgComp_zero, zero_dgComp, smul_zero, add_zero, zero_add, Int.negOnePow_zero,
    one_smul, dgComp_add, dgComp_neg]
  abel

/-- The inclusion of `P` followed by the morphism of extensions induced by `k` is the inclusion
of `P`. -/
@[simp↓]
theorem dgComp_extensionInl_extensionHomOfHomotopy (k : DGHom R 0 Q P) :
    dgComp R (extensionInl R hg) (extensionHomOfHomotopy R hg hg' k) (add_zero 0) =
      extensionInl R hg' := by
  simp only [extensionHomOfHomotopy_def, dgComp_add, dgComp_extensionInl_extensionFst_assoc,
    dgComp_extensionInl_extensionSnd_assoc, add_zero]

/-- The inclusion of `Q` followed by the morphism of extensions induced by `k` is the inclusion
of `Q` plus `k` followed by the inclusion of `P`. -/
theorem dgComp_extensionInr_extensionHomOfHomotopy (k : DGHom R 0 Q P) :
    dgComp R (extensionInr R hg) (extensionHomOfHomotopy R hg hg' k) (add_zero 0) =
      extensionInr R hg' + dgComp R k (extensionInl R hg') (add_zero 0) := by
  simp only [extensionHomOfHomotopy_def, dgComp_add, dgComp_extensionInr_extensionFst_assoc,
    dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- The morphism of extensions induced by `k` followed by the projection onto `Q` is the
projection onto `Q`. -/
@[simp↓]
theorem dgComp_extensionHomOfHomotopy_extensionSnd (k : DGHom R 0 Q P) :
    dgComp R (extensionHomOfHomotopy R hg hg' k) (extensionSnd R hg') (add_zero 0) =
      extensionSnd R hg := by
  simp only [extensionHomOfHomotopy_def, add_dgComp,
    dgComp_assoc R _ _ (extensionSnd R hg') (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, add_zero,
    zero_add, dgComp_dgId]

/-- The morphism of extensions induced by `k` followed by the projection onto `P` is the
projection onto `P` plus the projection onto `Q` followed by `k`. -/
theorem dgComp_extensionHomOfHomotopy_extensionFst (k : DGHom R 0 Q P) :
    dgComp R (extensionHomOfHomotopy R hg hg' k) (extensionFst R hg') (add_zero 0) =
      extensionFst R hg + dgComp R (extensionSnd R hg) k (add_zero 0) := by
  simp only [extensionHomOfHomotopy_def, add_dgComp,
    dgComp_assoc R _ _ (extensionFst R hg') (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionFst, dgComp_extensionInr_extensionFst, dgComp_zero, add_zero,
    dgComp_dgId]

/-- **The morphisms of extensions induced by `k` and `-k` are mutually inverse.** -/
theorem dgComp_extensionHomOfHomotopy_neg (k : DGHom R 0 Q P) :
    dgComp R (extensionHomOfHomotopy R hg hg' k) (extensionHomOfHomotopy R hg' hg (-k))
      (add_zero 0) = dgId R (extension P Q g hg) := by
  simp only [extensionHomOfHomotopy_def, add_dgComp, dgComp_add, neg_dgComp, dgComp_neg,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionFst_assoc, dgComp_extensionInl_extensionSnd_assoc,
    dgComp_extensionInr_extensionFst_assoc, dgComp_extensionInr_extensionSnd_assoc, dgComp_zero,
    add_zero]
  rw [← extension_total R hg]
  abel

variable {hg hg'} in
/-- **Extensions along homotopic morphisms are isomorphic**: if `g - g' = d k` for a degree-zero
morphism `k : Q ⟶ P`, then `extension P Q g` and `extension P Q g'` are isomorphic in the
homotopy category, through the morphisms induced by `k` and `-k`. -/
noncomputable def extensionIsoOfHomotopy {k : DGHom R 0 Q P}
    (hk : dgDifferential R 0 k = g - g') :
    DGHomotopyCategory.of R (extension P Q g hg) ≅ DGHomotopyCategory.of R (extension P Q g' hg')
    where
  hom := DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg hg' k)
    ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg hg' hk))
  inv := DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg' hg (-k))
    ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg' hg
      (by rw [map_neg, hk, neg_sub])))
  hom_inv_id := by
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, dgComp_extensionHomOfHomotopy_neg,
      DGHomotopyCategory.homOf_dgId]
  inv_hom_id := by
    have h := dgComp_extensionHomOfHomotopy_neg R hg' hg (-k)
    rw [neg_neg] at h
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, h, DGHomotopyCategory.homOf_dgId]

variable {hg hg'} in
@[simp]
theorem extensionIsoOfHomotopy_hom {k : DGHom R 0 Q P} (hk : dgDifferential R 0 k = g - g') :
    (extensionIsoOfHomotopy R (hg := hg) (hg' := hg') hk).hom =
      DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg hg' k)
        ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg hg' hk)) :=
  (rfl)

variable {hg hg'} in
@[simp]
theorem extensionIsoOfHomotopy_inv {k : DGHom R 0 Q P} (hk : dgDifferential R 0 k = g - g') :
    (extensionIsoOfHomotopy R (hg := hg) (hg' := hg') hk).inv =
      DGHomotopyCategory.homOf R (extensionHomOfHomotopy R hg' hg (-k))
        ((mem_dgCycles R).mpr (dgDifferential_extensionHomOfHomotopy R hg' hg
          (by rw [map_neg, hk, neg_sub]))) :=
  (rfl)

variable {hg hg'} in
/-- In the homotopy category, the inclusion of `P` followed by the isomorphism of extensions
along homotopic morphisms is the inclusion of `P`. -/
theorem homOf_extensionInl_comp_extensionIsoOfHomotopy_hom {k : DGHom R 0 Q P}
    (hk : dgDifferential R 0 k = g - g') :
    DGHomotopyCategory.homOf R (extensionInl R hg)
        ((mem_dgCycles R).mpr (dgDifferential_extensionInl R hg)) ≫
        (extensionIsoOfHomotopy R hk).hom =
      DGHomotopyCategory.homOf R (extensionInl R hg')
        ((mem_dgCycles R).mpr (dgDifferential_extensionInl R hg')) := by
  simp only [extensionIsoOfHomotopy_hom, DGHomotopyCategory.homOf_comp, dgCompZero_def,
    dgComp_extensionInl_extensionHomOfHomotopy]

variable {hg hg'} in
/-- In the homotopy category, the isomorphism of extensions along homotopic morphisms followed by
the projection onto `Q` is the projection onto `Q`. -/
theorem extensionIsoOfHomotopy_hom_comp_homOf_extensionSnd {k : DGHom R 0 Q P}
    (hk : dgDifferential R 0 k = g - g') :
    (extensionIsoOfHomotopy R hk).hom ≫
        DGHomotopyCategory.homOf R (extensionSnd R hg')
          ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R hg')) =
      DGHomotopyCategory.homOf R (extensionSnd R hg)
        ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R hg)) := by
  simp only [extensionIsoOfHomotopy_hom, DGHomotopyCategory.homOf_comp, dgCompZero_def,
    dgComp_extensionHomOfHomotopy_extensionSnd]

end homotopy

/-! ### Extensions along isomorphic second summands are isomorphic -/

section map

variable {P Q Q' : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  {g' : DGHom R 1 Q' P} (hg : dgDifferential R 1 g = 0) (hg' : dgDifferential R 1 g' = 0)

/-- The degree-zero morphism `extension P Q g ⟶ extension P Q' g'` induced by a degree-zero
morphism `φ : Q ⟶ Q'`: the identity on the summand `P` and `φ` on the second summand.  It is
closed when `φ` is closed and `φ` followed by `g'` is `g`
(`MathlibExt.DGSource.DGTwistedObject.dgDifferential_extensionMap`). -/
noncomputable def extensionMap (φ : DGHom R 0 Q Q') :
    DGHom R 0 (extension P Q g hg) (extension P Q' g' hg') :=
  dgComp R (extensionFst R hg) (extensionInl R hg') (add_zero 0) +
    dgComp R (extensionSnd R hg) (dgComp R φ (extensionInr R hg') (add_zero 0)) (add_zero 0)

theorem extensionMap_def (φ : DGHom R 0 Q Q') :
    extensionMap R hg hg' φ =
      dgComp R (extensionFst R hg) (extensionInl R hg') (add_zero 0) +
        dgComp R (extensionSnd R hg) (dgComp R φ (extensionInr R hg') (add_zero 0)) (add_zero 0) :=
  (rfl)

/-- The morphism of extensions induced by the identity is the identity. -/
@[simp↓]
theorem extensionMap_dgId : extensionMap R hg hg (dgId R Q) = dgId R (extension P Q g hg) := by
  rw [extensionMap_def, dgId_dgComp,
    extension_total]

/-- **The morphism of extensions induced by a closed morphism compatible with the gluing morphisms
is closed**: if `φ : Q ⟶ Q'` is closed and `φ` followed by `g'` is `g`, then the differential of
`MathlibExt.DGSource.DGTwistedObject.extensionMap` vanishes. -/
theorem dgDifferential_extensionMap {φ : DGHom R 0 Q Q'} (hφ : dgDifferential R 0 φ = 0)
    (h : dgComp R φ g' (zero_add 1) = g) :
    dgDifferential R 0 (extensionMap R hg hg' φ) = 0 := by
  rw [extensionMap_def, map_add]
  simp only [dgDifferential_dgComp, dgDifferential_extensionFst, dgDifferential_extensionInl,
    dgDifferential_extensionSnd, dgDifferential_extensionInr, hφ, neg_dgComp, dgComp_zero,
    zero_dgComp, smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul]
  rw [dgComp_assoc R _ g (extensionInl R hg') (zero_add 1) (add_zero 1) (by omega),
    ← dgComp_assoc R φ g' (extensionInl R hg') (zero_add 1) (add_zero 1) (by omega), h]
  abel

/-- The inclusion of `P` followed by the morphism of extensions induced by `φ` is the inclusion
of `P`. -/
@[simp↓]
theorem dgComp_extensionInl_extensionMap (φ : DGHom R 0 Q Q') :
    dgComp R (extensionInl R hg) (extensionMap R hg hg' φ) (add_zero 0) = extensionInl R hg' := by
  simp only [extensionMap_def, dgComp_add, dgComp_extensionInl_extensionFst_assoc,
    dgComp_extensionInl_extensionSnd_assoc, add_zero]

/-- The inclusion of `Q` followed by the morphism of extensions induced by `φ` is `φ` followed by
the inclusion of `Q'`. -/
@[simp↓]
theorem dgComp_extensionInr_extensionMap (φ : DGHom R 0 Q Q') :
    dgComp R (extensionInr R hg) (extensionMap R hg hg' φ) (add_zero 0) =
      dgComp R φ (extensionInr R hg') (add_zero 0) := by
  simp only [extensionMap_def, dgComp_add, dgComp_extensionInr_extensionFst_assoc,
    dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- The morphism of extensions induced by `φ` followed by the projection onto `P` is the
projection onto `P`. -/
@[simp↓]
theorem dgComp_extensionMap_extensionFst (φ : DGHom R 0 Q Q') :
    dgComp R (extensionMap R hg hg' φ) (extensionFst R hg') (add_zero 0) = extensionFst R hg := by
  simp only [extensionMap_def, add_dgComp,
    dgComp_assoc R _ _ (extensionFst R hg') (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionFst, dgComp_extensionInr_extensionFst, dgComp_zero, add_zero,
    dgComp_dgId]

/-- The morphism of extensions induced by `φ` followed by the projection onto `Q'` is the
projection onto `Q` followed by `φ`. -/
@[simp↓]
theorem dgComp_extensionMap_extensionSnd (φ : DGHom R 0 Q Q') :
    dgComp R (extensionMap R hg hg' φ) (extensionSnd R hg') (add_zero 0) =
      dgComp R (extensionSnd R hg) φ (add_zero 0) := by
  simp only [extensionMap_def, add_dgComp,
    dgComp_assoc R _ _ (extensionSnd R hg') (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, zero_add,
    dgComp_dgId]

/-- The inclusion of `P`, followed by the morphism of extensions induced by `φ` and then `x`, is
the inclusion of `P` followed by `x`. -/
@[simp↓]
theorem dgComp_extensionInl_extensionMap_assoc (φ : DGHom R 0 Q Q')
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    (x : DGHom R n (extension P Q' g' hg') Z) :
    dgComp R (extensionInl R hg) (dgComp R (extensionMap R hg hg' φ) x (zero_add n))
        (zero_add n) =
      dgComp R (extensionInl R hg') x (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInl_extensionMap]

/-- The inclusion of `Q`, followed by the morphism of extensions induced by `φ` and then `x`, is
`φ` followed by the inclusion of `Q'` and then `x`. -/
@[simp↓]
theorem dgComp_extensionInr_extensionMap_assoc (φ : DGHom R 0 Q Q')
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ}
    (x : DGHom R n (extension P Q' g' hg') Z) :
    dgComp R (extensionInr R hg) (dgComp R (extensionMap R hg hg' φ) x (zero_add n))
        (zero_add n) =
      dgComp R φ (dgComp R (extensionInr R hg') x (zero_add n)) (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionInr_extensionMap, dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega)]

/-- The morphism of extensions induced by `φ`, followed by the projection onto `P` and then `x`,
is the projection onto `P` followed by `x`. -/
@[simp↓]
theorem dgComp_extensionMap_extensionFst_assoc (φ : DGHom R 0 Q Q')
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ} (x : DGHom R n P Z) :
    dgComp R (extensionMap R hg hg' φ) (dgComp R (extensionFst R hg') x (zero_add n))
        (zero_add n) =
      dgComp R (extensionFst R hg) x (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionMap_extensionFst]

/-- The morphism of extensions induced by `φ`, followed by the projection onto `Q'` and then `x`,
is the projection onto `Q` followed by `φ` and then `x`. -/
@[simp↓]
theorem dgComp_extensionMap_extensionSnd_assoc (φ : DGHom R 0 Q Q')
    {Z : DGTwistedObject R (DGAdditiveClosure E)} {n : ℤ} (x : DGHom R n Q' Z) :
    dgComp R (extensionMap R hg hg' φ) (dgComp R (extensionSnd R hg') x (zero_add n))
        (zero_add n) =
      dgComp R (extensionSnd R hg) (dgComp R φ x (zero_add n)) (zero_add n) := by
  rw [← dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega),
    dgComp_extensionMap_extensionSnd, dgComp_assoc R _ _ x (add_zero 0) (zero_add n) (by omega)]

/-- **The morphisms of extensions compose**: the morphisms induced by `φ : Q ⟶ Q'` and
`ψ : Q' ⟶ Q''` compose to the morphism induced by `φ` followed by `ψ`. -/
@[simp↓]
theorem dgComp_extensionMap {Q'' : DGTwistedObject R (DGAdditiveClosure E)} {g'' : DGHom R 1 Q'' P}
    (hg'' : dgDifferential R 1 g'' = 0) (φ : DGHom R 0 Q Q') (ψ : DGHom R 0 Q' Q'') :
    dgComp R (extensionMap R hg hg' φ) (extensionMap R hg' hg'' ψ) (add_zero 0) =
      extensionMap R hg hg'' (dgComp R φ ψ (add_zero 0)) := by
  simp only [extensionMap_def, add_dgComp, dgComp_add,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionFst_assoc, dgComp_extensionInl_extensionSnd_assoc,
    dgComp_extensionInr_extensionFst_assoc, dgComp_extensionInr_extensionSnd_assoc, dgComp_zero,
    add_zero, zero_add]

variable {hg hg'} in
/-- **Extensions along isomorphic second summands are isomorphic**: if `φ : Q ⟶ Q'` is a closed
degree-zero morphism with two-sided inverse `ψ` and `φ` followed by `g'` is `g`, then
`extension P Q g` and `extension P Q' g'` are isomorphic in the homotopy category, through the
morphisms induced by `φ` and `ψ`. -/
noncomputable def extensionIsoOfIso {φ : DGHom R 0 Q Q'} {ψ : DGHom R 0 Q' Q}
    (hφ : dgDifferential R 0 φ = 0) (hφψ : dgComp R φ ψ (add_zero 0) = dgId R Q)
    (hψφ : dgComp R ψ φ (add_zero 0) = dgId R Q') (h : dgComp R φ g' (zero_add 1) = g) :
    DGHomotopyCategory.of R (extension P Q g hg) ≅ DGHomotopyCategory.of R (extension P Q' g' hg')
    where
  hom := DGHomotopyCategory.homOf R (extensionMap R hg hg' φ)
    ((mem_dgCycles R).mpr (dgDifferential_extensionMap R hg hg' hφ h))
  inv := DGHomotopyCategory.homOf R (extensionMap R hg' hg ψ)
    ((mem_dgCycles R).mpr (dgDifferential_extensionMap R hg' hg
      (dgDifferential_eq_zero_of_dgComp_eq_dgId R hφ (add_zero 0) hφψ hψφ)
      (by rw [← h, ← dgComp_assoc R ψ φ g' (add_zero 0) (zero_add 1) (by omega), hψφ,
        dgId_dgComp])))
  hom_inv_id := by
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, dgComp_extensionMap, hφψ,
      extensionMap_dgId, DGHomotopyCategory.homOf_dgId]
  inv_hom_id := by
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def, dgComp_extensionMap, hψφ,
      extensionMap_dgId, DGHomotopyCategory.homOf_dgId]

variable {hg hg'} in
@[simp]
theorem extensionIsoOfIso_hom {φ : DGHom R 0 Q Q'} {ψ : DGHom R 0 Q' Q}
    (hφ : dgDifferential R 0 φ = 0) (hφψ : dgComp R φ ψ (add_zero 0) = dgId R Q)
    (hψφ : dgComp R ψ φ (add_zero 0) = dgId R Q') (h : dgComp R φ g' (zero_add 1) = g) :
    (extensionIsoOfIso R (hg := hg) (hg' := hg') hφ hφψ hψφ h).hom =
      DGHomotopyCategory.homOf R (extensionMap R hg hg' φ)
        ((mem_dgCycles R).mpr (dgDifferential_extensionMap R hg hg' hφ h)) :=
  (rfl)

variable {hg hg'} in
@[simp]
theorem extensionIsoOfIso_inv {φ : DGHom R 0 Q Q'} {ψ : DGHom R 0 Q' Q}
    (hφ : dgDifferential R 0 φ = 0) (hφψ : dgComp R φ ψ (add_zero 0) = dgId R Q)
    (hψφ : dgComp R ψ φ (add_zero 0) = dgId R Q') (h : dgComp R φ g' (zero_add 1) = g) :
    (extensionIsoOfIso R (hg := hg) (hg' := hg') hφ hφψ hψφ h).inv =
      DGHomotopyCategory.homOf R (extensionMap R hg' hg ψ)
        ((mem_dgCycles R).mpr (dgDifferential_extensionMap R hg' hg
          (dgDifferential_eq_zero_of_dgComp_eq_dgId R hφ (add_zero 0) hφψ hψφ)
          (by rw [← h, ← dgComp_assoc R ψ φ g' (add_zero 0) (zero_add 1) (by omega), hψφ,
            dgId_dgComp]))) :=
  (rfl)

end map

end DGTwistedObject

end MathlibExt.DGSource

namespace CategoryTheory.EnrichedFunctor

open MathlibExt.DGSource DGTwistedObject

universe v u u₂

variable {R : Type v} [CommRing R] {E : Type u} {E' : Type u₂} [DGCategory R E]
  [DGCategory R E'] (G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) E E')

/-! ### Images of extensions -/

section extension

variable {P Q : DGTwistedObject R (DGAdditiveClosure E)} {g : DGHom R 1 Q P}
  (hg : dgDifferential R 1 g = 0)

/-- The comparison `G (extension P Q g) ⟶ extension (G P) (G Q) (G g)` of the image of an
extension under the DG functor induced by `G` with the extension of the images: the images of
the projections followed by the inclusions of the target. -/
noncomputable def mapExtensionHom :
    DGHom R 0 (G.mapDGAdditiveClosure.mapDGTwistedObject.obj (extension P Q g hg))
      (extension (G.mapDGAdditiveClosure.mapDGTwistedObject.obj P)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.obj Q)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 1 g)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.dgDifferential_dgMap_eq_zero hg)) :=
  dgComp R (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionFst R hg))
      (extensionInl R _) (add_zero 0) +
    dgComp R (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionSnd R hg))
      (extensionInr R _) (add_zero 0)

/-- The comparison `extension (G P) (G Q) (G g) ⟶ G (extension P Q g)`, inverse to
`CategoryTheory.EnrichedFunctor.mapExtensionHom`: the projections of the source followed by the
images of the inclusions. -/
noncomputable def mapExtensionInv :
    DGHom R 0 (extension (G.mapDGAdditiveClosure.mapDGTwistedObject.obj P)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.obj Q)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 1 g)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.dgDifferential_dgMap_eq_zero hg))
      (G.mapDGAdditiveClosure.mapDGTwistedObject.obj (extension P Q g hg)) :=
  dgComp R (extensionFst R _)
      (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInl R hg)) (add_zero 0) +
    dgComp R (extensionSnd R _)
      (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInr R hg)) (add_zero 0)

/-- The comparison of the image of an extension with the extension of the images is the images of
the projections followed by the inclusions. -/
theorem mapExtensionHom_def :
    mapExtensionHom G hg =
      dgComp R (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionFst R hg))
          (extensionInl R _) (add_zero 0) +
        dgComp R (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionSnd R hg))
          (extensionInr R _) (add_zero 0) :=
  (rfl)

/-- The inverse comparison is the projections followed by the images of the inclusions. -/
theorem mapExtensionInv_def :
    mapExtensionInv G hg =
      dgComp R (extensionFst R _)
          (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInl R hg)) (add_zero 0) +
        dgComp R (extensionSnd R _)
          (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInr R hg)) (add_zero 0) :=
  (rfl)

/-- The comparison of the image of an extension with the extension of the images is closed. -/
@[simp↓]
theorem dgDifferential_mapExtensionHom : dgDifferential R 0 (mapExtensionHom G hg) = 0 := by
  have hfst : dgDifferential R 0
      (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionFst R hg)) =
        -dgComp R (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionSnd R hg))
          (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 1 g) (zero_add 1) := by
    rw [← dgMap_dgDifferential, dgDifferential_extensionFst, map_neg,
      dgMap_dgComp]
  rw [mapExtensionHom_def, map_add, dgDifferential_dgComp, dgDifferential_dgComp, hfst,
    G.mapDGAdditiveClosure.mapDGTwistedObject.dgDifferential_dgMap_eq_zero
      (dgDifferential_extensionSnd R hg)]
  simp only [dgDifferential_extensionInl, dgDifferential_extensionInr, neg_dgComp, zero_dgComp,
    dgComp_zero, smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul]
  exact neg_add_eq_zero.2 (dgComp_assoc R _ _ _ (zero_add 1) (add_zero 1) rfl)


/-- The image of the inclusion of `P` followed by the comparison is the inclusion of `G P`. -/
@[simp↓]
theorem dgComp_dgMap_extensionInl_mapExtensionHom :
    dgComp R (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInl R hg))
      (mapExtensionHom G hg) (add_zero 0) = extensionInl R _ := by
  rw [mapExtensionHom_def, dgComp_add,
    dgMap_dgComp_dgMap_assoc_of_eq_dgId _ (dgComp_extensionInl_extensionFst R hg),
    dgMap_dgComp_dgMap_assoc_of_eq_zero _ (dgComp_extensionInl_extensionSnd R hg),
    add_zero]

/-- The image of the inclusion of `Q` followed by the comparison is the inclusion of `G Q`. -/
@[simp↓]
theorem dgComp_dgMap_extensionInr_mapExtensionHom :
    dgComp R (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInr R hg))
      (mapExtensionHom G hg) (add_zero 0) = extensionInr R _ := by
  rw [mapExtensionHom_def, dgComp_add,
    dgMap_dgComp_dgMap_assoc_of_eq_zero _ (dgComp_extensionInr_extensionFst R hg),
    dgMap_dgComp_dgMap_assoc_of_eq_dgId _ (dgComp_extensionInr_extensionSnd R hg),
    zero_add]

/-- The comparison followed by the projection onto `G Q` is the image of the projection onto
`Q`. -/
@[simp↓]
theorem dgComp_mapExtensionHom_extensionSnd :
    dgComp R (mapExtensionHom G hg) (extensionSnd R _) (add_zero 0) =
      G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionSnd R hg) := by
  simp only [mapExtensionHom_def, add_dgComp,
    dgComp_assoc R _ _ (extensionSnd R _) (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_extensionSnd, dgComp_extensionInr_extensionSnd, dgComp_zero, zero_add,
    dgComp_dgId]

/-- The inclusion of `G P` followed by the inverse comparison is the image of the inclusion of
`P`. -/
@[simp↓]
theorem dgComp_extensionInl_mapExtensionInv :
    dgComp R (extensionInl R _) (mapExtensionInv G hg) (add_zero 0) =
      G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInl R hg) := by
  simp only [mapExtensionInv_def, dgComp_add, dgComp_extensionInl_extensionFst_assoc,
    dgComp_extensionInl_extensionSnd_assoc, add_zero]

/-- The inclusion of `G Q` followed by the inverse comparison is the image of the inclusion of
`Q`. -/
@[simp↓]
theorem dgComp_extensionInr_mapExtensionInv :
    dgComp R (extensionInr R _) (mapExtensionInv G hg) (add_zero 0) =
      G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 0 (extensionInr R hg) := by
  simp only [mapExtensionInv_def, dgComp_add, dgComp_extensionInr_extensionFst_assoc,
    dgComp_extensionInr_extensionSnd_assoc, zero_add]

/-- The comparison of the image of an extension with the extension of the images, followed by its
inverse, is the identity. -/
@[simp↓]
theorem dgComp_mapExtensionHom_mapExtensionInv :
    dgComp R (mapExtensionHom G hg) (mapExtensionInv G hg) (add_zero 0) = dgId R _ := by
  rw [mapExtensionHom_def, add_dgComp,
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
    dgComp_extensionInl_mapExtensionInv, dgComp_extensionInr_mapExtensionInv,
    ← dgMap_dgComp, ← dgMap_dgComp, ← map_add,
    extension_total,
    dgMap_dgId]

/-- The inverse comparison followed by the comparison is the identity of the extension of the
images. -/
@[simp↓]
theorem dgComp_mapExtensionInv_mapExtensionHom :
    dgComp R (mapExtensionInv G hg) (mapExtensionHom G hg) (add_zero 0) = dgId R _ := by
  refine extension_dgHom_ext ?_ ?_
  · rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_extensionInl_mapExtensionInv, dgComp_dgMap_extensionInl_mapExtensionHom, dgComp_dgId]
  · rw [← dgComp_assoc R _ _ _ (add_zero 0) (add_zero 0) (add_zero 0),
      dgComp_extensionInr_mapExtensionInv, dgComp_dgMap_extensionInr_mapExtensionHom, dgComp_dgId]

/-- The inverse comparison of the extension of the images with the image of an extension is
closed. -/
@[simp↓]
theorem dgDifferential_mapExtensionInv : dgDifferential R 0 (mapExtensionInv G hg) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_mapExtensionHom G hg) (add_zero 0)
    (dgComp_mapExtensionHom_mapExtensionInv G hg) (dgComp_mapExtensionInv_mapExtensionHom G hg)

/-- **A DG functor preserves extensions**: the image of `extension P Q g` under the DG functor
induced by `G` is isomorphic in the homotopy category to the extension of the images along the
image of `g`. -/
noncomputable def mapExtensionIso :
    DGHomotopyCategory.of R (G.mapDGAdditiveClosure.mapDGTwistedObject.obj (extension P Q g hg)) ≅
      DGHomotopyCategory.of R (extension (G.mapDGAdditiveClosure.mapDGTwistedObject.obj P)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.obj Q)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.dgMap 1 g)
        (G.mapDGAdditiveClosure.mapDGTwistedObject.dgDifferential_dgMap_eq_zero hg)) where
  hom := DGHomotopyCategory.homOf R (mapExtensionHom G hg)
    ((mem_dgCycles R).mpr (dgDifferential_mapExtensionHom G hg))
  inv := DGHomotopyCategory.homOf R (mapExtensionInv G hg)
    ((mem_dgCycles R).mpr (dgDifferential_mapExtensionInv G hg))
  hom_inv_id := DGHomotopyCategory.homOf_comp_eq_id_of_dgComp_eq_dgId R _ _
    (dgComp_mapExtensionHom_mapExtensionInv G hg)
  inv_hom_id := DGHomotopyCategory.homOf_comp_eq_id_of_dgComp_eq_dgId R _ _
    (dgComp_mapExtensionInv_mapExtensionHom G hg)

@[simp]
theorem mapExtensionIso_hom :
    (mapExtensionIso G hg).hom = DGHomotopyCategory.homOf R (mapExtensionHom G hg)
      ((mem_dgCycles R).mpr (dgDifferential_mapExtensionHom G hg)) :=
  (rfl)

@[simp]
theorem mapExtensionIso_inv :
    (mapExtensionIso G hg).inv = DGHomotopyCategory.homOf R (mapExtensionInv G hg)
      ((mem_dgCycles R).mpr (dgDifferential_mapExtensionInv G hg)) :=
  (rfl)

end extension

end CategoryTheory.EnrichedFunctor
