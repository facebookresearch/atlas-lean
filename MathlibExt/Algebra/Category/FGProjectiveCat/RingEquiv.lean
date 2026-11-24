/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import MathlibExt.Algebra.Category.ModuleCat.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Finite projective modules under a ring equivalence

Restriction of scalars along a ring equivalence preserves and reflects finite
generation and projectivity.  This file restricts Mathlib's literal
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv` to `FGProjectiveCat` and
records its identity, inverse, and composition coherence.

This is a lower-layer restriction-of-scalars API.  It does not use Morita
equivalence, K-theory, an integer-algebra bridge, C-star structure, or a
textbook carrier.
-/

@[expose] public section

open CategoryTheory

universe v uR uS uT

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private def restrictScalarsCarrierSemilinearEquiv
    (e : R ≃+* S) (M : ModuleCat.{v} S) :
    let _ : RingHomInvPair e.toRingHom e.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv e
    let _ : RingHomInvPair e.symm.toRingHom e.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm e
    ((ModuleCat.restrictScalars e.toRingHom).obj M) ≃ₛₗ[e.toRingHom] M :=
  let _ : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  let _ : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  { toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private theorem projective_restrictScalars_iff
    (e : R ≃+* S) (M : ModuleCat.{v} S) :
    Module.Projective S M ↔
      Module.Projective R
        ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let _ : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  let _ : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  constructor
  · intro h
    let _ : Module.Projective S M := h
    exact Module.Projective.of_equiv
      (restrictScalarsCarrierSemilinearEquiv e M).symm
  · intro h
    let _ : Module.Projective R
        ((ModuleCat.restrictScalars e.toRingHom).obj M) := h
    exact Module.Projective.of_equiv
      (restrictScalarsCarrierSemilinearEquiv e M)

private theorem isFGProjective_restrictScalars_iff
    (e : R ≃+* S) (M : ModuleCat.{v} S) :
    ModuleCat.isFGProjective R
        ((ModuleCat.restrictScalars e.toRingHom).obj M) ↔
      ModuleCat.isFGProjective S M := by
  let E : ModuleCat.{v} S ≌ ModuleCat.{v} R :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have hfinite :
      Module.Finite S M ↔ Module.Finite R (E.functor.obj M) :=
    ModuleCat.finite_iff E M
  have hprojective :
      Module.Projective S M ↔ Module.Projective R (E.functor.obj M) :=
    projective_restrictScalars_iff e M
  change
    (Module.Finite R (E.functor.obj M) ∧
        Module.Projective R (E.functor.obj M)) ↔
      Module.Finite S M ∧ Module.Projective S M
  exact ⟨fun h => ⟨hfinite.mpr h.1, hprojective.mpr h.2⟩,
    fun h => ⟨hfinite.mp h.1, hprojective.mp h.2⟩⟩

/-- Restriction of scalars along a ring equivalence, restricted to finitely
generated projective modules.

For `e : R ≃+* S`, the forward functor has orientation
`FGProjectiveCat S ⥤ FGProjectiveCat R`, exactly matching
`ModuleCat.restrictScalars e.toRingHom`.  Ring universes are independent and
the module-carrier universe `v` is shared by source and target. -/
noncomputable def restrictScalarsEquivalenceOfRingEquiv (e : R ≃+* S) :
    FGProjectiveCat.{v} S ≌ FGProjectiveCat.{v} R :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory <| by
    funext M
    exact propext (isFGProjective_restrictScalars_iff e M)

@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_functor_obj_obj
    (e : R ≃+* S) (M : FGProjectiveCat.{v} S) :
    ((restrictScalarsEquivalenceOfRingEquiv e).functor.obj M).obj =
      (ModuleCat.restrictScalars e.toRingHom).obj M.obj :=
  rfl

@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_functor_map_hom
    (e : R ≃+* S) {M N : FGProjectiveCat.{v} S} (f : M ⟶ N) :
    ((restrictScalarsEquivalenceOfRingEquiv e).functor.map f).hom =
      (ModuleCat.restrictScalars e.toRingHom).map f.hom :=
  rfl

instance restrictScalarsEquivalenceOfRingEquiv_functor_additive
    (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e).functor.Additive := by
  dsimp only [restrictScalarsEquivalenceOfRingEquiv,
    Equivalence.congrFullSubcategory]
  infer_instance

instance restrictScalarsEquivalenceOfRingEquiv_functor_isExact
    (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e).functor.IsExact :=
  ExactCategory.isExact_splitSource _

instance restrictScalarsEquivalenceOfRingEquiv_inverse_isExact
    (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e).inverse.IsExact :=
  ExactCategory.isExact_splitSource _

/-- Restriction along the identity ring equivalence is naturally isomorphic to
the identity on finite projectives. -/
noncomputable def restrictScalarsEquivalenceOfRingEquivId
    (R : Type uR) [Ring R] :
    (restrictScalarsEquivalenceOfRingEquiv
      (RingEquiv.refl R)).functor ≅ 𝟭 (FGProjectiveCat.{v} R) :=
  NatIso.ofComponents
    (fun M => (ModuleCat.isFGProjective (R := R)).isoMk
      ((ModuleCat.restrictScalarsId R).app M.obj))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact (ModuleCat.restrictScalarsId R).hom.naturality f.hom)

/-- Restriction along `e.symm` is the inverse of restriction along `e`. -/
noncomputable def restrictScalarsEquivalenceOfRingEquivSymm
    (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e.symm).functor ≅
      (restrictScalarsEquivalenceOfRingEquiv e).inverse :=
  NatIso.ofComponents
    (fun _ => (ModuleCat.isFGProjective (R := S)).isoMk (Iso.refl _))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      rfl)

/-- Restriction along a composite ring equivalence is naturally isomorphic to
successive restriction of scalars.  The order is contravariant:
`restrict (e.trans f) ≅ restrict f ⋙ restrict e`. -/
noncomputable def restrictScalarsEquivalenceOfRingEquivComp
    {T : Type uT} [Ring T] (e : R ≃+* S) (f : S ≃+* T) :
    (restrictScalarsEquivalenceOfRingEquiv (e.trans f)).functor ≅
      (restrictScalarsEquivalenceOfRingEquiv f).functor ⋙
        (restrictScalarsEquivalenceOfRingEquiv e).functor := by
  let hcomp : (e.trans f).toRingHom = f.toRingHom.comp e.toRingHom := by
    ext x
    rfl
  exact NatIso.ofComponents
    (fun M => (ModuleCat.isFGProjective (R := R)).isoMk
      ((ModuleCat.restrictScalarsComp'
        e.toRingHom f.toRingHom (e.trans f).toRingHom hcomp).app M.obj))
    (by
      intro X Y g
      apply ObjectProperty.hom_ext
      exact ModuleCat.restrictScalarsComp'App_hom_naturality
        e.toRingHom f.toRingHom (e.trans f).toRingHom hcomp g.hom)

end FGProjectiveCat
