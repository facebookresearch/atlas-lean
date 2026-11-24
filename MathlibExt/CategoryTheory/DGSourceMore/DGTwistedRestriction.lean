/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Restrict.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedExtension

/-!
# Restricting twisted objects to sets of summands

Let `T = (⊕ᵢ Xᵢ, δ)` be a twisted object of the additive closure of a differential graded category
`E`, and let `q` be a predicate on its summands.  The entries of the restricted matrix
`(δᵢⱼ)_{q i, q j}` satisfy the Maurer–Cartan equation as soon as no path `Xᵢ ⟶ Xₖ ⟶ Xⱼ` of two
entries of `δ` leaves the summands satisfying `q` and comes back, that is
`δᵢₖ` followed by `δₖⱼ` vanishes whenever `q i`, `q j` and `¬ q k`.  The restriction
`MathlibExt.DGSource.DGTwistedObject.restrict` is then the twisted object `(⊕_{q i} Xᵢ, δ|_q)`.

The main case is a predicate `p` such that `δ` has no entry from a summand satisfying `p` to one
which does not.  Both `p` and its complement then satisfy the condition above: the summands
satisfying `p` span a twisted sub-object `P`, those not satisfying `p` a twisted quotient `Q`, and
the remaining entries of `δ`, from the summands of `Q` to those of `P`, form a closed degree-one
morphism `g : Q ⟶ P` (`MathlibExt.DGSource.DGTwistedObject.restrictHom`).  Regrouping the summands identifies
`T` with the extension of `Q` by `P` along `g`, by mutually inverse closed degree-zero morphisms
whose entries are identities (`MathlibExt.DGSource.DGTwistedObject.extensionRestrictIso`).  For a one-sided
twisted complex and `p` the summands other than one of maximal level, this exhibits the twisted
complex as an extension of a single summand by a one-sided twisted complex with fewer summands;
see `MathlibExt/CategoryTheory/DGSourceMore/DGOneSided.lean`.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.restrictTwist`: the restricted twisting matrix `δ|_q`.
* `MathlibExt.DGSource.DGTwistedObject.restrict`: the restriction of a twisted object of the additive closure
  to the summands satisfying a predicate.
* `MathlibExt.DGSource.DGTwistedObject.restrictHom`: the degree-one morphism from the summands not satisfying
  `p` to those satisfying `p`, made of the remaining entries of the twist.
* `MathlibExt.DGSource.DGTwistedObject.toExtensionRestrict` and
  `MathlibExt.DGSource.DGTwistedObject.ofExtensionRestrict`: the regrouping morphisms between `T` and the
  extension of its restriction to `¬ p` by its restriction to `p`.
* `MathlibExt.DGSource.DGTwistedObject.extensionRestrictIso`: the induced isomorphism in the homotopy
  category.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_restrictTwist`: the Maurer–Cartan equation of the
  restricted twisting matrix.
* `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv_twist_restrict`: the twist of a restriction is the
  restricted matrix.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_restrictHom`: the connecting morphism is closed.
* `MathlibExt.DGSource.DGTwistedObject.dgDifferential_toExtensionRestrict`,
  `MathlibExt.DGSource.DGTwistedObject.dgComp_toExtensionRestrict_ofExtensionRestrict` and
  `MathlibExt.DGSource.DGTwistedObject.dgComp_ofExtensionRestrict_toExtensionRestrict`: the regrouping
  morphisms are closed and mutually inverse.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
-/

public section

open CategoryTheory

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

/- `matrixEquiv` is a local name for `MathlibExt.DGSource.DGAdditiveClosure.dgHomEquiv`, which identifies a
morphism of the additive closure with its matrix of entries; the unqualified name `dgHomEquiv`
refers to `MathlibExt.DGSource.DGTwistedObject.dgHomEquiv` in this namespace. -/
open DGAdditiveClosure renaming dgHomEquiv → matrixEquiv

variable {R : Type v} [CommRing R] {E : Type u} [DGCategory R E]
  (T : DGTwistedObject R (DGAdditiveClosure E))

/-! ### The restriction to a set of summands -/

section restrict

variable (q : T.obj.ι → Prop) [DecidablePred q]

/-- The **restricted twisting matrix** `δ|_q`: the degree-one endomorphism of `⊕_{q i} Xᵢ` whose
entries are the entries of the twist of `T` between summands satisfying `q`. -/
noncomputable def restrictTwist :
    DGHom R 1 (⟨{i // q i}, fun i ↦ T.obj.X i⟩ : DGAdditiveClosure E)
      ⟨{i // q i}, fun i ↦ T.obj.X i⟩ :=
  (matrixEquiv R _ _ 1).symm fun i j ↦ matrixEquiv R _ _ 1 T.twist i j

/-- The entries of the restricted twisting matrix are entries of the twist of `T`. -/
@[simp↓]
theorem dgHomEquiv_restrictTwist (i j : {i // q i}) :
    matrixEquiv R _ _ 1 (T.restrictTwist q) i j = matrixEquiv R _ _ 1 T.twist i j := by
  rw [restrictTwist, LinearEquiv.apply_symm_apply]

/-- The restricted twisting matrix `δ|_q` satisfies the Maurer–Cartan equation once no path of two
entries of `δ` leaves the summands satisfying `q` and comes back: the terms of `∑ₖ δᵢₖ δₖⱼ`
indexed by summands outside `q` then vanish. -/
theorem dgDifferential_restrictTwist
    (hq : ∀ i j k, q i → q j → ¬ q k →
      dgComp R (matrixEquiv R _ _ 1 T.twist i k) (matrixEquiv R _ _ 1 T.twist k j) rfl = 0) :
    dgDifferential R 1 (T.restrictTwist q) =
      dgComp R (T.restrictTwist q) (T.restrictTwist q) rfl :=
  DGAdditiveClosure.dgHom_ext R fun i j ↦ by
    rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, DGAdditiveClosure.dgHomEquiv_dgComp]
    simp only [↓dgHomEquiv_restrictTwist]
    rw [← DGAdditiveClosure.dgHomEquiv_dgDifferential, dgDifferential_twist,
      DGAdditiveClosure.dgHomEquiv_dgComp, ← Fintype.sum_subtype_add_sum_subtype q, add_eq_left]
    exact Finset.sum_eq_zero fun k _ ↦ hq i j k i.2 j.2 k.2

/-- The **restriction** of a twisted object `(⊕ᵢ Xᵢ, δ)` of the additive closure to the summands
satisfying `q`: the twisted object `(⊕_{q i} Xᵢ, δ|_q)` with the restricted twisting matrix.  It
satisfies the Maurer–Cartan equation because no path of two entries of `δ` leaves the summands
satisfying `q` and comes back. -/
-- This is reducible so that the summands of the restriction are reducibly indexed by the
-- subtype `{i // q i}`, in which the matrix entries of its twist and morphisms are stated, and
-- its twist is reducibly `MathlibExt.DGSource.DGTwistedObject.restrictTwist`.
noncomputable abbrev restrict
    (hq : ∀ i j k, q i → q j → ¬ q k →
      dgComp R (matrixEquiv R _ _ 1 T.twist i k) (matrixEquiv R _ _ 1 T.twist k j) rfl = 0) :
    DGTwistedObject R (DGAdditiveClosure E) where
  obj := ⟨{i // q i}, fun i ↦ T.obj.X i⟩
  twist := T.restrictTwist q
  dgDifferential_twist := T.dgDifferential_restrictTwist q hq

variable {q} (hq : ∀ i j k, q i → q j → ¬ q k →
  dgComp R (matrixEquiv R _ _ 1 T.twist i k) (matrixEquiv R _ _ 1 T.twist k j) rfl = 0)

/-- The twisting matrix of a restriction is the restricted twisting matrix. -/
@[simp↓]
theorem dgHomEquiv_twist_restrict (i j : {i // q i}) :
    matrixEquiv R _ _ 1 (T.restrict q hq).twist i j = matrixEquiv R _ _ 1 T.twist i j :=
  T.dgHomEquiv_restrictTwist q i j

end restrict

/-! ### Splitting along a set of summands closed under the twist -/

section split

variable {T} {p : T.obj.ι → Prop}
  (hp : ∀ i j, p i → ¬ p j → matrixEquiv R _ _ 1 T.twist i j = 0)
include hp

/-- If `δ` has no entry from a summand satisfying `p` to one which does not, then the summands
satisfying `p` satisfy the condition of `MathlibExt.DGSource.DGTwistedObject.restrict`. -/
theorem dgComp_twist_eq_zero_left (i j k : T.obj.ι) (hi : p i) (_ : p j) (hk : ¬ p k) :
    dgComp R (matrixEquiv R _ _ 1 T.twist i k) (matrixEquiv R _ _ 1 T.twist k j) rfl = 0 := by
  rw [hp i k hi hk, zero_dgComp]

/-- If `δ` has no entry from a summand satisfying `p` to one which does not, then the summands
not satisfying `p` satisfy the condition of `MathlibExt.DGSource.DGTwistedObject.restrict`. -/
theorem dgComp_twist_eq_zero_right (i j k : T.obj.ι) (_ : ¬ p i) (hj : ¬ p j)
    (hk : ¬ ¬ p k) :
    dgComp R (matrixEquiv R _ _ 1 T.twist i k) (matrixEquiv R _ _ 1 T.twist k j) rfl = 0 := by
  rw [hp k j (not_not.mp hk) hj, dgComp_zero]

variable [DecidablePred p]

/-- The **connecting morphism** of the splitting of `T` along `p`: the degree-one morphism from the
restriction of `T` to the summands not satisfying `p` to its restriction to the summands
satisfying `p`, whose entries are the corresponding entries of the twist of `T`. -/
noncomputable def restrictHom :
    DGHom R 1 (T.restrict (¬ p ·) (dgComp_twist_eq_zero_right hp))
      (T.restrict p (dgComp_twist_eq_zero_left hp)) :=
  (dgHomEquiv R _ _ 1).symm ((matrixEquiv R _ _ 1).symm fun i j ↦ matrixEquiv R _ _ 1 T.twist i j)

/-- The entries of the connecting morphism are entries of the twist of `T`. -/
@[simp↓]
theorem dgHomEquiv_restrictHom (i : {i // ¬ p i}) (j : {i // p i}) :
    matrixEquiv R _ _ 1 (dgHomEquiv R _ _ 1 (restrictHom hp)) i j =
      matrixEquiv R _ _ 1 T.twist i j := by
  rw [restrictHom, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **The connecting morphism is closed**: entrywise, its twisted differential is the
Maurer–Cartan defect `d δᵢⱼ - ∑ₖ δᵢₖ δₖⱼ` of `T`, the sum running over the summands satisfying
`p` and those not satisfying it. -/
theorem dgDifferential_restrictHom : dgDifferential R 1 (restrictHom hp) = 0 :=
  (dgHomEquiv R _ _ _).injective <| DGAdditiveClosure.dgHom_ext R fun i j ↦ by
    rw [dgDifferential_apply, map_zero, map_zero, Pi.zero_apply, Pi.zero_apply]
    simp only [↓dgHomEquiv_restrictHom, ↓dgHomEquiv_twist_restrict, Int.negOnePow_one,
      Units.neg_smul, one_smul]
    rw [← DGAdditiveClosure.dgHomEquiv_dgDifferential, dgDifferential_twist,
      DGAdditiveClosure.dgHomEquiv_dgComp, ← Fintype.sum_subtype_add_sum_subtype p]
    abel

/-! ### Regrouping the summands -/

/-- The extension of the restriction of `T` to the summands not satisfying `p` by its restriction
to the summands satisfying `p`, along the connecting morphism. -/
local notation "extensionRestrict" hp =>
  extension (restrict _ _ (dgComp_twist_eq_zero_left hp))
    (restrict _ _ (dgComp_twist_eq_zero_right hp)) (restrictHom hp)
    (dgDifferential_restrictHom hp)

/-- The matrix of the regrouping morphism `T ⟶ P ⊕ Q`: the identity from each summand of `T` to its
copy in `P` or in `Q`. -/
private noncomputable def toExtensionRestrictMatrix :
    ∀ (i : T.obj.ι) (k : (extensionRestrict hp).obj.ι),
      DGHom R 0 (T.obj.X i) ((extensionRestrict hp).obj.X k)
  | i, .inl j => matrixEquiv R _ _ 0 (dgId R T.obj) i j
  | i, .inr j => matrixEquiv R _ _ 0 (dgId R T.obj) i j

/-- The matrix of the regrouping morphism `P ⊕ Q ⟶ T`: the identity from each summand of `P` or
`Q` to its copy in `T`. -/
private noncomputable def ofExtensionRestrictMatrix :
    ∀ (k : (extensionRestrict hp).obj.ι) (i : T.obj.ι),
      DGHom R 0 ((extensionRestrict hp).obj.X k) (T.obj.X i)
  | .inl j, i => matrixEquiv R _ _ 0 (dgId R T.obj) j i
  | .inr j, i => matrixEquiv R _ _ 0 (dgId R T.obj) j i

/-- The **regrouping morphism** `T ⟶ P ⊕ Q` from `T` to the extension of its restriction to the
summands not satisfying `p` by its restriction to the summands satisfying `p`: the identity from
each summand of `T` to its copy. -/
noncomputable def toExtensionRestrict : DGHom R 0 T (extensionRestrict hp) :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (toExtensionRestrictMatrix hp))

/-- The **regrouping morphism** `P ⊕ Q ⟶ T`, inverse to
`MathlibExt.DGSource.DGTwistedObject.toExtensionRestrict`: the identity from each summand of the extension to
its copy in `T`. -/
noncomputable def ofExtensionRestrict : DGHom R 0 (extensionRestrict hp) T :=
  (dgHomEquiv R _ _ 0).symm ((matrixEquiv R _ _ 0).symm (ofExtensionRestrictMatrix hp))

/-- The entries of the regrouping morphism `T ⟶ P ⊕ Q` into the summands of `P` are entries of
the identity of `T`. -/
@[simp↓]
theorem dgHomEquiv_toExtensionRestrict_inl (i : T.obj.ι) (j : {i // p i}) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (toExtensionRestrict hp)) i (.inl j) =
      matrixEquiv R _ _ 0 (dgId R T.obj) i j := by
  rw [toExtensionRestrict, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The entries of the regrouping morphism `T ⟶ P ⊕ Q` into the summands of `Q` are entries of
the identity of `T`. -/
@[simp↓]
theorem dgHomEquiv_toExtensionRestrict_inr (i : T.obj.ι) (j : {i // ¬ p i}) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (toExtensionRestrict hp)) i (.inr j) =
      matrixEquiv R _ _ 0 (dgId R T.obj) i j := by
  rw [toExtensionRestrict, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The entries of the regrouping morphism `P ⊕ Q ⟶ T` out of the summands of `P` are entries of
the identity of `T`. -/
@[simp↓]
theorem dgHomEquiv_ofExtensionRestrict_inl (j : {i // p i}) (i : T.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (ofExtensionRestrict hp)) (.inl j) i =
      matrixEquiv R _ _ 0 (dgId R T.obj) j i := by
  rw [ofExtensionRestrict, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The entries of the regrouping morphism `P ⊕ Q ⟶ T` out of the summands of `Q` are entries of
the identity of `T`. -/
@[simp↓]
theorem dgHomEquiv_ofExtensionRestrict_inr (j : {i // ¬ p i}) (i : T.obj.ι) :
    matrixEquiv R _ _ 0 (dgHomEquiv R _ _ 0 (ofExtensionRestrict hp)) (.inr j) i =
      matrixEquiv R _ _ 0 (dgId R T.obj) j i := by
  rw [ofExtensionRestrict, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- **The regrouping morphism `T ⟶ P ⊕ Q` is closed**: entrywise, both composites with the twists
are the corresponding entry of the twist of `T`, using that `δ` has no entry from a summand
satisfying `p` to one which does not. -/
theorem dgDifferential_toExtensionRestrict : dgDifferential R 0 (toExtensionRestrict hp) = 0 :=
  (dgHomEquiv R _ _ _).injective <| DGAdditiveClosure.dgHom_ext R fun i k ↦ by
    rw [dgDifferential_apply, Fintype.sum_sum_type, map_zero, map_zero, Pi.zero_apply,
      Pi.zero_apply]
    rcases k with j | j
    · simp only [↓dgHomEquiv_toExtensionRestrict_inl, ↓dgHomEquiv_toExtensionRestrict_inr,
        ↓dgHomEquiv_twist_extension_inl_inl, ↓dgHomEquiv_twist_extension_inr_inl,
        ↓dgHomEquiv_twist_restrict, ↓dgHomEquiv_restrictHom,
        ↓DGAdditiveClosure.dgDifferential_dgHomEquiv_dgId,
        ↓DGAdditiveClosure.sum_dgComp_dgHomEquiv_dgId, Int.negOnePow_zero, one_smul, zero_add]
      rw [Fintype.sum_subtype_add_sum_subtype p fun m ↦ dgComp R
          (matrixEquiv R _ _ 0 (dgId R T.obj) i m) (matrixEquiv R _ _ 1 T.twist m j) (zero_add 1),
        DGAdditiveClosure.sum_dgHomEquiv_dgId_dgComp, sub_self]
    · simp only [↓dgHomEquiv_toExtensionRestrict_inl, ↓dgHomEquiv_toExtensionRestrict_inr,
        ↓dgHomEquiv_twist_extension_inl_inr, ↓dgHomEquiv_twist_extension_inr_inr,
        ↓dgHomEquiv_twist_restrict, ↓DGAdditiveClosure.dgDifferential_dgHomEquiv_dgId,
        ↓DGAdditiveClosure.sum_dgComp_dgHomEquiv_dgId, Int.negOnePow_zero, one_smul, zero_add]
      -- The vanishing block from `P` to `Q` consists of entries of `δ`, by `hp`.
      rw [Finset.sum_congr rfl fun x _ ↦ by rw [← hp x j x.2 j.2],
        Fintype.sum_subtype_add_sum_subtype p fun m ↦ dgComp R
          (matrixEquiv R _ _ 0 (dgId R T.obj) i m) (matrixEquiv R _ _ 1 T.twist m j) (zero_add 1),
        DGAdditiveClosure.sum_dgHomEquiv_dgId_dgComp, sub_self]

/-- The regrouping morphisms `T ⟶ P ⊕ Q ⟶ T` compose to the identity of `T`. -/
@[simp↓]
theorem dgComp_toExtensionRestrict_ofExtensionRestrict :
    dgComp R (toExtensionRestrict hp) (ofExtensionRestrict hp) (add_zero 0) = dgId R T :=
  (dgHomEquiv R _ _ _).injective <| DGAdditiveClosure.dgHom_ext R fun i i' ↦ by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, DGAdditiveClosure.dgHomEquiv_dgComp,
      Fintype.sum_sum_type]
    simp only [↓dgHomEquiv_toExtensionRestrict_inl, ↓dgHomEquiv_toExtensionRestrict_inr,
      ↓dgHomEquiv_ofExtensionRestrict_inl, ↓dgHomEquiv_ofExtensionRestrict_inr]
    rw [Fintype.sum_subtype_add_sum_subtype p fun m ↦ dgComp R
        (matrixEquiv R _ _ 0 (dgId R T.obj) i m) (matrixEquiv R _ _ 0 (dgId R T.obj) m i')
        (add_zero 0),
      DGAdditiveClosure.sum_dgHomEquiv_dgId_dgComp]

/-- The regrouping morphisms `P ⊕ Q ⟶ T ⟶ P ⊕ Q` compose to the identity of `P ⊕ Q`. -/
@[simp↓]
theorem dgComp_ofExtensionRestrict_toExtensionRestrict :
    dgComp R (ofExtensionRestrict hp) (toExtensionRestrict hp) (add_zero 0) =
      dgId R (extensionRestrict hp) :=
  (dgHomEquiv R _ _ _).injective <| DGAdditiveClosure.dgHom_ext R fun k k' ↦ by
    rw [dgHomEquiv_dgComp, dgHomEquiv_dgId, DGAdditiveClosure.dgHomEquiv_dgComp]
    rcases k with j | j <;> rcases k' with j' | j' <;>
      simp only [↓dgHomEquiv_toExtensionRestrict_inl, ↓dgHomEquiv_toExtensionRestrict_inr,
        ↓dgHomEquiv_ofExtensionRestrict_inl, ↓dgHomEquiv_ofExtensionRestrict_inr,
        ↓DGAdditiveClosure.sum_dgHomEquiv_dgId_dgComp]
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inl_inl, DGAdditiveClosure.dgHomEquiv_dgId_subtype]
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inl_inr]
      exact DGAdditiveClosure.dgHomEquiv_dgId_of_ne R _ fun h ↦ j'.2 (h ▸ j.2)
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inr_inl]
      exact DGAdditiveClosure.dgHomEquiv_dgId_of_ne R _ fun h ↦ j.2 (h ▸ j'.2)
    · rw [DGAdditiveClosure.dgHomEquiv_dgId_sum_inr_inr, DGAdditiveClosure.dgHomEquiv_dgId_subtype]

/-- The regrouping morphism `P ⊕ Q ⟶ T` is closed, as the inverse of a closed morphism. -/
theorem dgDifferential_ofExtensionRestrict : dgDifferential R 0 (ofExtensionRestrict hp) = 0 :=
  dgDifferential_eq_zero_of_dgComp_eq_dgId R (dgDifferential_toExtensionRestrict hp) (add_zero 0)
    (dgComp_toExtensionRestrict_ofExtensionRestrict hp)
    (dgComp_ofExtensionRestrict_toExtensionRestrict hp)

/-- **A twisted object is the extension of its restrictions along a set of summands closed under
the twist**: if `δ` has no entry from a summand satisfying `p` to one which does not, then `T` is
isomorphic in the homotopy category to the extension of its restriction to the summands not
satisfying `p` by its restriction to the summands satisfying `p`, along the connecting morphism
`MathlibExt.DGSource.DGTwistedObject.restrictHom`.  The isomorphism regroups the summands. -/
noncomputable def extensionRestrictIso :
    DGHomotopyCategory.of R T ≅ DGHomotopyCategory.of R (extensionRestrict hp) where
  hom := DGHomotopyCategory.homOf R (toExtensionRestrict hp)
    ((mem_dgCycles R).mpr (dgDifferential_toExtensionRestrict hp))
  inv := DGHomotopyCategory.homOf R (ofExtensionRestrict hp)
    ((mem_dgCycles R).mpr (dgDifferential_ofExtensionRestrict hp))
  hom_inv_id := by
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def,
      dgComp_toExtensionRestrict_ofExtensionRestrict, DGHomotopyCategory.homOf_dgId]
  inv_hom_id := by
    simp only [DGHomotopyCategory.homOf_comp, dgCompZero_def,
      dgComp_ofExtensionRestrict_toExtensionRestrict, DGHomotopyCategory.homOf_dgId]

@[simp]
theorem extensionRestrictIso_hom :
    (extensionRestrictIso hp).hom = DGHomotopyCategory.homOf R (toExtensionRestrict hp)
      ((mem_dgCycles R).mpr (dgDifferential_toExtensionRestrict hp)) :=
  (rfl)

@[simp]
theorem extensionRestrictIso_inv :
    (extensionRestrictIso hp).inv = DGHomotopyCategory.homOf R (ofExtensionRestrict hp)
      ((mem_dgCycles R).mpr (dgDifferential_ofExtensionRestrict hp)) :=
  (rfl)

end split

end DGTwistedObject

end MathlibExt.DGSource
