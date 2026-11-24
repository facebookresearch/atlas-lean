/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionCoherence
public import Mathlib.CategoryTheory.Equivalence

/-!
# Native scalar-extension functor coherence

The original tensor comparisons and shrink coordinates give natural
identity and composition isomorphisms between the actual native scalar
functors. Source, intermediate and target ring universes remain independent.
-/

public section
noncomputable section

open CategoryTheory
open ModuleCat.RingHomScalarExtension

universe uR uS uT

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

private def idComponent (R : Type uR) [Ring R] (P : FGProjectiveCat.{uR} R) :
    (ringScalarExtension (RingHom.id R)).obj P ≃ₗ[R] P :=
  (ringScalarExtensionCoordinates (RingHom.id R) P).trans (identityTensorLinearEquiv R P)

private theorem idComponent_naturality (R : Type uR) [Ring R]
    {P Q : FGProjectiveCat.{uR} R} (h : P ⟶ Q) :
    (idComponent R Q).toLinearMap.comp ((ringScalarExtension (RingHom.id R)).map h).hom.hom =
      h.hom.hom.comp (idComponent R P).toLinearMap := by
  apply LinearMap.ext
  intro x
  change identityTensorLinearEquiv R Q
      (ringScalarExtensionCoordinates (RingHom.id R) Q
        (((ringScalarExtension (RingHom.id R)).map h).hom.hom x)) =
    h.hom.hom (identityTensorLinearEquiv R P
      (ringScalarExtensionCoordinates (RingHom.id R) P x))
  have hc := LinearMap.congr_fun (ringScalarExtensionCoordinates_naturality (RingHom.id R) h) x
  change ringScalarExtensionCoordinates (RingHom.id R) Q
      (((ringScalarExtension (RingHom.id R)).map h).hom.hom x) =
    linearMap (RingHom.id R) h.hom.hom
      (ringScalarExtensionCoordinates (RingHom.id R) P x) at hc
  rw [hc]
  exact LinearMap.congr_fun (identityTensorLinearEquiv_naturality R h.hom.hom)
    (ringScalarExtensionCoordinates (RingHom.id R) P x)

/-- The actual native identity scalar functor contracts by its canonical tensor unitor. -/
def ringScalarExtensionIdIso (R : Type uR) [Ring R] :
    ringScalarExtension (RingHom.id R) ≅ 𝟭 (FGProjectiveCat.{uR} R) :=
  NatIso.ofComponents
    (fun P => (ModuleCat.isFGProjective.{uR} R).isoMk (idComponent R P).toModuleIso)
    (by
      intro P Q h
      apply FGProjectiveCat.hom_ext
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (idComponent_naturality R h) x)

private theorem idIso_hom_apply_computed (R : Type uR) [Ring R]
    (P : FGProjectiveCat.{uR} R) (x : (ringScalarExtension (RingHom.id R)).obj P) :
    ((ringScalarExtensionIdIso R).hom.app P).hom.hom x =
      identityTensorLinearEquiv R P (ringScalarExtensionCoordinates (RingHom.id R) P x) :=
  rfl

/-- The original identity morphism contracts the actual tensor coordinate of every element. -/
theorem ringScalarExtensionIdIso_hom_apply (R : Type uR) [Ring R]
    (P : FGProjectiveCat.{uR} R) (x : (ringScalarExtension (RingHom.id R)).obj P) :
    ((ringScalarExtensionIdIso R).hom.app P).hom.hom x =
      identityTensorLinearEquiv R P (ringScalarExtensionCoordinates (RingHom.id R) P x) :=
  idIso_hom_apply_computed R P x

/-- The original inverse identity morphism inserts the actual unit tensor and shrink coordinate. -/
theorem ringScalarExtensionIdIso_inv_apply (R : Type uR) [Ring R]
    (P : FGProjectiveCat.{uR} R) (p : P) :
    ((ringScalarExtensionIdIso R).inv.app P).hom.hom p =
      (ringScalarExtensionCoordinates (RingHom.id R) P).symm
        (pure (RingHom.id R) P 1 p) := by
  change (idComponent R P).symm p = _
  change (ringScalarExtensionCoordinates (RingHom.id R) P).symm
      ((identityTensorLinearEquiv R P).symm p) = _
  rw [identityTensorLinearEquiv_symm]

/-- Whole linear-map naturality retains the original native identity scalar morphisms. -/
theorem ringScalarExtensionIdIso_naturality (R : Type uR) [Ring R]
    {P Q : FGProjectiveCat.{uR} R} (h : P ⟶ Q) :
    ((ringScalarExtensionIdIso R).hom.app Q).hom.hom.comp
        ((ringScalarExtension (RingHom.id R)).map h).hom.hom =
      h.hom.hom.comp ((ringScalarExtensionIdIso R).hom.app P).hom.hom :=
  idComponent_naturality R h

private def compComponent (f : R →+* S) (g : S →+* T) (P : FGProjectiveCat.{uR} R) :
    (ringScalarExtension g).obj ((ringScalarExtension f).obj P) ≃ₗ[T]
      (ringScalarExtension (g.comp f)).obj P :=
  (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).trans
    ((tensorLinearEquiv g (ringScalarExtensionCoordinates f P)).trans
      ((compositionLinearEquiv f g P).trans (ringScalarExtensionCoordinates (g.comp f) P).symm))

private theorem compComponent_coordinates (f : R →+* S) (g : S →+* T)
    (P : FGProjectiveCat.{uR} R) (x : (ringScalarExtension g).obj ((ringScalarExtension f).obj P)) :
    ringScalarExtensionCoordinates (g.comp f) P (compComponent f g P x) =
      compositionLinearEquiv f g P
        (tensorLinearEquiv g (ringScalarExtensionCoordinates f P)
          (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P) x)) := by
  simp only [compComponent, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

private theorem compComponent_naturality (f : R →+* S) (g : S →+* T)
    {P Q : FGProjectiveCat.{uR} R} (h : P ⟶ Q) :
    (compComponent f g Q).toLinearMap.comp
        ((ringScalarExtension g).map ((ringScalarExtension f).map h)).hom.hom =
      ((ringScalarExtension (g.comp f)).map h).hom.hom.comp
        (compComponent f g P).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (ringScalarExtensionCoordinates (g.comp f) Q).injective
  change ringScalarExtensionCoordinates (g.comp f) Q
      (compComponent f g Q
        (((ringScalarExtension g).map ((ringScalarExtension f).map h)).hom.hom x)) =
    ringScalarExtensionCoordinates (g.comp f) Q
      (((ringScalarExtension (g.comp f)).map h).hom.hom (compComponent f g P x))
  have hg := LinearMap.congr_fun
    (ringScalarExtensionCoordinates_naturality g ((ringScalarExtension f).map h)) x
  change ringScalarExtensionCoordinates g ((ringScalarExtension f).obj Q)
      (((ringScalarExtension g).map ((ringScalarExtension f).map h)).hom.hom x) =
    linearMap g ((ringScalarExtension f).map h).hom.hom
      (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P) x) at hg
  have hf := congrArg
    (fun k : (ringScalarExtension f).obj P →ₗ[S] tensor f Q => linearMap g k)
    (ringScalarExtensionCoordinates_naturality f h)
  rw [linearMap_comp, linearMap_comp] at hf
  have hlift (z : tensor g ((ringScalarExtension f).obj P)) :
      tensorLinearEquiv g (ringScalarExtensionCoordinates f Q)
          (linearMap g ((ringScalarExtension f).map h).hom.hom z) =
        linearMap g (linearMap f h.hom.hom)
          (tensorLinearEquiv g (ringScalarExtensionCoordinates f P) z) := by
    rw [tensorLinearEquiv_value, tensorLinearEquiv_value]
    exact LinearMap.congr_fun hf z
  have hgf := LinearMap.congr_fun
    (ringScalarExtensionCoordinates_naturality (g.comp f) h) (compComponent f g P x)
  change ringScalarExtensionCoordinates (g.comp f) Q
      (((ringScalarExtension (g.comp f)).map h).hom.hom (compComponent f g P x)) =
    linearMap (g.comp f) h.hom.hom
      (ringScalarExtensionCoordinates (g.comp f) P (compComponent f g P x)) at hgf
  rw [compComponent_coordinates, hgf, compComponent_coordinates]
  rw [hg, hlift]
  exact LinearMap.congr_fun (compositionLinearEquiv_naturality f g h.hom.hom)
    (tensorLinearEquiv g (ringScalarExtensionCoordinates f P)
      (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P) x))

/-- The actual native scalar functors compose through the canonical balanced tensor comparison. -/
def ringScalarExtensionCompIso (f : R →+* S) (g : S →+* T) :
    ringScalarExtension f ⋙ ringScalarExtension g ≅ ringScalarExtension (g.comp f) :=
  NatIso.ofComponents
    (fun P => (ModuleCat.isFGProjective.{uT} T).isoMk (compComponent f g P).toModuleIso)
    (by
      intro P Q h
      apply FGProjectiveCat.hom_ext
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (compComponent_naturality f g h) x)

/-- The whole composition morphism retains the three original tensor/shrink coordinates. -/
theorem ringScalarExtensionCompIso_hom_coordinates (f : R →+* S) (g : S →+* T)
    (P : FGProjectiveCat.{uR} R) (x : (ringScalarExtension g).obj ((ringScalarExtension f).obj P)) :
    ringScalarExtensionCoordinates (g.comp f) P
        (((ringScalarExtensionCompIso f g).hom.app P).hom.hom x) =
      compositionLinearEquiv f g P
        (tensorLinearEquiv g (ringScalarExtensionCoordinates f P)
          (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P) x)) :=
  compComponent_coordinates f g P x

private theorem compIso_inv_coordinates_computed (f : R →+* S) (g : S →+* T)
    (P : FGProjectiveCat.{uR} R) (y : (ringScalarExtension (g.comp f)).obj P) :
    ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)
        (((ringScalarExtensionCompIso f g).inv.app P).hom.hom y) =
      (tensorLinearEquiv g (ringScalarExtensionCoordinates f P)).symm
        ((compositionLinearEquiv f g P).symm (ringScalarExtensionCoordinates (g.comp f) P y)) := by
  change ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)
    ((compComponent f g P).symm y) = _
  simp only [compComponent, LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_symm]

/-- The whole inverse composition morphism uses the actual inverse tensor and shrink maps. -/
theorem ringScalarExtensionCompIso_inv_coordinates (f : R →+* S) (g : S →+* T)
    (P : FGProjectiveCat.{uR} R) (y : (ringScalarExtension (g.comp f)).obj P) :
    ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)
        (((ringScalarExtensionCompIso f g).inv.app P).hom.hom y) =
      (tensorLinearEquiv g (ringScalarExtensionCoordinates f P)).symm
        ((compositionLinearEquiv f g P).symm (ringScalarExtensionCoordinates (g.comp f) P y)) :=
  compIso_inv_coordinates_computed f g P y

/-- Original nested pure tensors map to their ordered coefficient product, with both shrink maps. -/
theorem ringScalarExtensionCompIso_hom_nested_pure (f : R →+* S) (g : S →+* T)
    (P : FGProjectiveCat.{uR} R) (t : T) (s : S) (p : P) :
    ringScalarExtensionCoordinates (g.comp f) P
        (((ringScalarExtensionCompIso f g).hom.app P).hom.hom
          ((ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).symm
            (pure g ((ringScalarExtension f).obj P) t
              ((ringScalarExtensionCoordinates f P).symm (pure f P s p))))) =
      pure (g.comp f) P (t * g s) p := by
  rw [ringScalarExtensionCompIso_hom_coordinates, LinearEquiv.apply_symm_apply,
    tensorLinearEquiv_pure, LinearEquiv.apply_symm_apply, compositionLinearEquiv_pure]

/-- The original inverse comparison inserts the intermediate unit in the original coordinates. -/
theorem ringScalarExtensionCompIso_inv_pure (f : R →+* S) (g : S →+* T)
    (P : FGProjectiveCat.{uR} R) (t : T) (p : P) :
    ((ringScalarExtensionCompIso f g).inv.app P).hom.hom
        ((ringScalarExtensionCoordinates (g.comp f) P).symm (pure (g.comp f) P t p)) =
      (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).symm
        (pure g ((ringScalarExtension f).obj P) t
          ((ringScalarExtensionCoordinates f P).symm (pure f P 1 p))) := by
  apply (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).injective
  rw [ringScalarExtensionCompIso_inv_coordinates, LinearEquiv.apply_symm_apply,
    compositionLinearEquiv_symm_pure, tensorLinearEquiv_symm_value, linearMap_pure,
    LinearEquiv.apply_symm_apply]
  rfl

/-- Whole native morphism naturality retains the original two successive categorical maps. -/
theorem ringScalarExtensionCompIso_naturality (f : R →+* S) (g : S →+* T)
    {P Q : FGProjectiveCat.{uR} R} (h : P ⟶ Q) :
    ((ringScalarExtensionCompIso f g).hom.app Q).hom.hom.comp
        ((ringScalarExtension g).map ((ringScalarExtension f).map h)).hom.hom =
      ((ringScalarExtension (g.comp f)).map h).hom.hom.comp
        ((ringScalarExtensionCompIso f g).hom.app P).hom.hom :=
  compComponent_naturality f g h

/-- The constructed inverse input for scalar extension along an actual ring equivalence. -/
def ringScalarExtensionEquivUnitIso (e : R ≃+* S) :
    𝟭 (FGProjectiveCat.{uR} R) ≅
      ringScalarExtension e.toRingHom ⋙ ringScalarExtension e.symm.toRingHom :=
  ((ringScalarExtensionCompIso e.toRingHom e.symm.toRingHom) ≪≫
    eqToIso (congrArg (fun h : R →+* R => ringScalarExtension h)
      e.symm_toRingHom_comp_toRingHom) ≪≫ ringScalarExtensionIdIso R).symm

/-- The constructed counit input uses the same original inverse ring homomorphism. -/
def ringScalarExtensionEquivCounitIso (e : R ≃+* S) :
    ringScalarExtension e.symm.toRingHom ⋙ ringScalarExtension e.toRingHom ≅
      𝟭 (FGProjectiveCat.{uS} S) :=
  ringScalarExtensionCompIso e.symm.toRingHom e.toRingHom ≪≫
    eqToIso (congrArg (fun h : S →+* S => ringScalarExtension h)
      e.toRingHom_comp_symm_toRingHom) ≪≫ ringScalarExtensionIdIso S

/-- Actual native scalar extension along a ring equivalence is a categorical equivalence.
Both functors are literal canonical scalar-extension programs in their native ring universes. -/
def ringScalarExtensionEquivalence (e : R ≃+* S) :
    FGProjectiveCat.{uR} R ≌ FGProjectiveCat.{uS} S :=
  CategoryTheory.Equivalence.mk
    (ringScalarExtension e.toRingHom) (ringScalarExtension e.symm.toRingHom)
    (ringScalarExtensionEquivUnitIso e) (ringScalarExtensionEquivCounitIso e)

private theorem scalarEquivalence_functor_computed (e : R ≃+* S) :
    (ringScalarExtensionEquivalence e).functor = ringScalarExtension e.toRingHom := rfl

/-- The forward functor is the original native scalar extension. -/
theorem ringScalarExtensionEquivalence_functor (e : R ≃+* S) :
    (ringScalarExtensionEquivalence e).functor = ringScalarExtension e.toRingHom :=
  scalarEquivalence_functor_computed e

private theorem scalarEquivalence_inverse_computed (e : R ≃+* S) :
    (ringScalarExtensionEquivalence e).inverse = ringScalarExtension e.symm.toRingHom := rfl

/-- The inverse functor is scalar extension along the original inverse ring equivalence. -/
theorem ringScalarExtensionEquivalence_inverse (e : R ≃+* S) :
    (ringScalarExtensionEquivalence e).inverse = ringScalarExtension e.symm.toRingHom :=
  scalarEquivalence_inverse_computed e

universe uU uP

private theorem tensorComp_id_left (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    (compositionLinearEquiv (RingHom.id R) f P).toLinearMap =
      linearMap f (identityTensorLinearEquiv R P).toLinearMap := by
  apply linearMap_ext f (tensor (RingHom.id R) P)
  intro s x
  let := rightModule (RingHom.id R)
  let a : tensor (RingHom.id R) P →+ tensor f P :=
    (compositionLinearEquiv (RingHom.id R) f P).toLinearMap.toAddMonoidHom.comp
      (pure f (tensor (RingHom.id R) P) s).toAddMonoidHom
  let b : tensor (RingHom.id R) P →+ tensor f P :=
    (linearMap f (identityTensorLinearEquiv R P).toLinearMap).toAddMonoidHom.comp
      (pure f (tensor (RingHom.id R) P) s).toAddMonoidHom
  have hab : a = b := by
    apply TensorProduct.Balanced.addHom_ext ℤ R R P
    intro r p
    change compositionLinearEquiv (RingHom.id R) f P
        (pure f (tensor (RingHom.id R) P) s (pure (RingHom.id R) P r p)) =
      linearMap f (identityTensorLinearEquiv R P).toLinearMap
        (pure f (tensor (RingHom.id R) P) s (pure (RingHom.id R) P r p))
    rw [compositionLinearEquiv_pure, linearMap_pure]
    change pure f P (s * f r) p =
      pure f P s (identityTensorLinearEquiv R P (pure (RingHom.id R) P r p))
    rw [identityTensorLinearEquiv_pure]
    exact pure_balance f P r s p
  exact DFunLike.congr_fun hab x

private theorem tensorComp_id_right (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    (compositionLinearEquiv f (RingHom.id S) P).toLinearMap =
      (identityTensorLinearEquiv S (tensor f P)).toLinearMap := by
  apply linearMap_ext (RingHom.id S) (tensor f P)
  intro s x
  let := rightModule f
  let a : tensor f P →+ tensor f P :=
    (compositionLinearEquiv f (RingHom.id S) P).toLinearMap.toAddMonoidHom.comp
      (pure (RingHom.id S) (tensor f P) s).toAddMonoidHom
  let b : tensor f P →+ tensor f P :=
    (identityTensorLinearEquiv S (tensor f P)).toLinearMap.toAddMonoidHom.comp
      (pure (RingHom.id S) (tensor f P) s).toAddMonoidHom
  have hab : a = b := by
    apply TensorProduct.Balanced.addHom_ext ℤ R S P
    intro t p
    change compositionLinearEquiv f (RingHom.id S) P
        (pure (RingHom.id S) (tensor f P) s (pure f P t p)) =
      identityTensorLinearEquiv S (tensor f P)
        (pure (RingHom.id S) (tensor f P) s (pure f P t p))
    rw [compositionLinearEquiv_pure, identityTensorLinearEquiv_pure, smul_pure]
    rfl
  exact DFunLike.congr_fun hab x

private theorem tensorComp_assoc {U : Type uU} [Ring U]
    (f : R →+* S) (g : S →+* T) (h : T →+* U)
    (P : Type uP) [AddCommGroup P] [Module R P] :
    (compositionLinearEquiv (g.comp f) h P).toLinearMap.comp
        (linearMap h (compositionLinearEquiv f g P).toLinearMap) =
      (compositionLinearEquiv f (h.comp g) P).toLinearMap.comp
        (compositionLinearEquiv g h (tensor f P)).toLinearMap := by
  apply linearMap_ext h (tensor g (tensor f P))
  intro u x
  let := rightModule g
  let a : tensor g (tensor f P) →+ tensor (h.comp (g.comp f)) P :=
    ((compositionLinearEquiv (g.comp f) h P).toLinearMap.comp
      (linearMap h (compositionLinearEquiv f g P).toLinearMap)).toAddMonoidHom.comp
        (pure h (tensor g (tensor f P)) u).toAddMonoidHom
  let b : tensor g (tensor f P) →+ tensor (h.comp (g.comp f)) P :=
    ((compositionLinearEquiv f (h.comp g) P).toLinearMap.comp
      (compositionLinearEquiv g h (tensor f P)).toLinearMap).toAddMonoidHom.comp
        (pure h (tensor g (tensor f P)) u).toAddMonoidHom
  have hab : a = b := by
    apply TensorProduct.Balanced.addHom_ext ℤ S T (tensor f P)
    intro t y
    let := rightModule f
    let c : tensor f P →+ tensor (h.comp (g.comp f)) P :=
      a.comp (pure g (tensor f P) t).toAddMonoidHom
    let d : tensor f P →+ tensor (h.comp (g.comp f)) P :=
      b.comp (pure g (tensor f P) t).toAddMonoidHom
    have hcd : c = d := by
      apply TensorProduct.Balanced.addHom_ext ℤ R S P
      intro s p
      change compositionLinearEquiv (g.comp f) h P
          (linearMap h (compositionLinearEquiv f g P).toLinearMap
            (pure h (tensor g (tensor f P)) u (pure g (tensor f P) t (pure f P s p)))) =
        compositionLinearEquiv f (h.comp g) P
          (compositionLinearEquiv g h (tensor f P)
            (pure h (tensor g (tensor f P)) u (pure g (tensor f P) t (pure f P s p))))
      rw [linearMap_pure]
      change compositionLinearEquiv (g.comp f) h P
          (pure h (tensor (g.comp f) P) u
            (compositionLinearEquiv f g P (pure g (tensor f P) t (pure f P s p)))) =
        compositionLinearEquiv f (h.comp g) P
          (compositionLinearEquiv g h (tensor f P)
            (pure h (tensor g (tensor f P)) u (pure g (tensor f P) t (pure f P s p))))
      rw [compositionLinearEquiv_pure, compositionLinearEquiv_pure,
        compositionLinearEquiv_pure, compositionLinearEquiv_pure]
      change pure (h.comp (g.comp f)) P (u * h (t * g s)) p =
        pure (h.comp (g.comp f)) P ((u * h t) * h (g s)) p
      rw [h.map_mul, mul_assoc]
    exact DFunLike.congr_fun hcd y
  exact DFunLike.congr_fun hab x

/-- The original scalar comparison for an initial identity is the whiskered identity unitor. -/
theorem ringScalarExtensionCompIso_id_left (f : R →+* S) :
    ringScalarExtensionCompIso (RingHom.id R) f ≪≫
        eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.comp_id f)) =
      Functor.isoWhiskerRight (ringScalarExtensionIdIso R) (ringScalarExtension f) ≪≫
        (ringScalarExtension f).leftUnitor := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  change compComponent (RingHom.id R) f P x =
    (((ringScalarExtension f).map ((ringScalarExtensionIdIso R).hom.app P)).hom.hom x)
  apply (ringScalarExtensionCoordinates f P).injective
  have hc := compComponent_coordinates (RingHom.id R) f P x
  have hm := LinearMap.congr_fun
    (ringScalarExtensionCoordinates_naturality f ((ringScalarExtensionIdIso R).hom.app P)) x
  change ringScalarExtensionCoordinates f P
      (((ringScalarExtension f).map ((ringScalarExtensionIdIso R).hom.app P)).hom.hom x) =
    linearMap f (idComponent R P).toLinearMap
      (ringScalarExtensionCoordinates f ((ringScalarExtension (RingHom.id R)).obj P) x) at hm
  calc
    ringScalarExtensionCoordinates f P (compComponent (RingHom.id R) f P x) =
        compositionLinearEquiv (RingHom.id R) f P
          (tensorLinearEquiv f (ringScalarExtensionCoordinates (RingHom.id R) P)
            (ringScalarExtensionCoordinates f ((ringScalarExtension (RingHom.id R)).obj P) x)) := hc
    _ = linearMap f (identityTensorLinearEquiv R P).toLinearMap
        (tensorLinearEquiv f (ringScalarExtensionCoordinates (RingHom.id R) P)
          (ringScalarExtensionCoordinates f ((ringScalarExtension (RingHom.id R)).obj P) x)) :=
      LinearMap.congr_fun (tensorComp_id_left f P) _
    _ = linearMap f (idComponent R P).toLinearMap
        (ringScalarExtensionCoordinates f ((ringScalarExtension (RingHom.id R)).obj P) x) := by
      rw [tensorLinearEquiv_value]
      change linearMap f (identityTensorLinearEquiv R P).toLinearMap
          (linearMap f (ringScalarExtensionCoordinates (RingHom.id R) P).toLinearMap _) =
        linearMap f ((identityTensorLinearEquiv R P).toLinearMap.comp
          (ringScalarExtensionCoordinates (RingHom.id R) P).toLinearMap) _
      exact (LinearMap.congr_fun (linearMap_comp f
        (ringScalarExtensionCoordinates (RingHom.id R) P).toLinearMap
        (identityTensorLinearEquiv R P).toLinearMap) _).symm
    _ = ringScalarExtensionCoordinates f P
        (((ringScalarExtension f).map ((ringScalarExtensionIdIso R).hom.app P)).hom.hom x) :=
      hm.symm

/-- The original scalar comparison for a terminal identity is the whiskered identity unitor. -/
theorem ringScalarExtensionCompIso_id_right (f : R →+* S) :
    ringScalarExtensionCompIso f (RingHom.id S) ≪≫
        eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.id_comp f)) =
      Functor.isoWhiskerLeft (ringScalarExtension f) (ringScalarExtensionIdIso S) ≪≫
        (ringScalarExtension f).rightUnitor := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  change compComponent f (RingHom.id S) P x =
    idComponent S ((ringScalarExtension f).obj P) x
  apply (ringScalarExtensionCoordinates f P).injective
  calc
    ringScalarExtensionCoordinates f P (compComponent f (RingHom.id S) P x) =
        compositionLinearEquiv f (RingHom.id S) P
          (tensorLinearEquiv (RingHom.id S) (ringScalarExtensionCoordinates f P)
            (ringScalarExtensionCoordinates (RingHom.id S) ((ringScalarExtension f).obj P) x)) :=
      compComponent_coordinates f (RingHom.id S) P x
    _ = identityTensorLinearEquiv S (tensor f P)
        (tensorLinearEquiv (RingHom.id S) (ringScalarExtensionCoordinates f P)
          (ringScalarExtensionCoordinates (RingHom.id S) ((ringScalarExtension f).obj P) x)) :=
      LinearMap.congr_fun (tensorComp_id_right f P) _
    _ = ringScalarExtensionCoordinates f P
        (identityTensorLinearEquiv S ((ringScalarExtension f).obj P)
          (ringScalarExtensionCoordinates (RingHom.id S) ((ringScalarExtension f).obj P) x)) := by
      rw [tensorLinearEquiv_value]
      exact LinearMap.congr_fun
        (identityTensorLinearEquiv_naturality S (ringScalarExtensionCoordinates f P).toLinearMap) _
    _ = ringScalarExtensionCoordinates f P (idComponent S ((ringScalarExtension f).obj P) x) := rfl

private theorem compIso_assoc_apply {U : Type uU} [Ring U]
    (f : R →+* S) (g : S →+* T) (h : T →+* U) (P : FGProjectiveCat.{uR} R)
    (x : (ringScalarExtension h).obj
      ((ringScalarExtension g).obj ((ringScalarExtension f).obj P))) :
    ((ringScalarExtensionCompIso (g.comp f) h).hom.app P).hom.hom
        (((ringScalarExtension h).map ((ringScalarExtensionCompIso f g).hom.app P)).hom.hom x) =
      ((ringScalarExtensionCompIso f (h.comp g)).hom.app P).hom.hom
        (((ringScalarExtensionCompIso g h).hom.app ((ringScalarExtension f).obj P)).hom.hom x) := by
  apply (ringScalarExtensionCoordinates (h.comp (g.comp f)) P).injective
  let A := (ringScalarExtension f).obj P
  let B := (ringScalarExtension g).obj A
  let D := (ringScalarExtension (g.comp f)).obj P
  let z := ringScalarExtensionCoordinates h B x
  let v := linearMap h (ringScalarExtensionCoordinates g A).toLinearMap z
  let w := linearMap h (linearMap g (ringScalarExtensionCoordinates f P).toLinearMap) v
  have hj : (ringScalarExtensionCoordinates (g.comp f) P).toLinearMap.comp
      ((ringScalarExtensionCompIso f g).hom.app P).hom.hom =
    (compositionLinearEquiv f g P).toLinearMap.comp
      ((linearMap g (ringScalarExtensionCoordinates f P).toLinearMap).comp
        (ringScalarExtensionCoordinates g A).toLinearMap) := by
    apply LinearMap.ext
    intro y
    have hy := ringScalarExtensionCompIso_hom_coordinates f g P y
    rw [tensorLinearEquiv_value] at hy
    exact hy
  have hlift := congrArg (fun k : B →ₗ[T] tensor (g.comp f) P => linearMap h k) hj
  simp only [linearMap_comp] at hlift
  have hm := LinearMap.congr_fun
    (ringScalarExtensionCoordinates_naturality h ((ringScalarExtensionCompIso f g).hom.app P)) x
  change ringScalarExtensionCoordinates h D
      (((ringScalarExtension h).map ((ringScalarExtensionCompIso f g).hom.app P)).hom.hom x) =
    linearMap h ((ringScalarExtensionCompIso f g).hom.app P).hom.hom z at hm
  have hn := LinearMap.congr_fun
    (compositionLinearEquiv_naturality g h (ringScalarExtensionCoordinates f P).toLinearMap) v
  change compositionLinearEquiv g h (tensor f P) w =
    linearMap (h.comp g) (ringScalarExtensionCoordinates f P).toLinearMap
      (compositionLinearEquiv g h A v) at hn
  calc
    ringScalarExtensionCoordinates (h.comp (g.comp f)) P
        (((ringScalarExtensionCompIso (g.comp f) h).hom.app P).hom.hom
          (((ringScalarExtension h).map ((ringScalarExtensionCompIso f g).hom.app P)).hom.hom x)) =
        compositionLinearEquiv (g.comp f) h P
          (tensorLinearEquiv h (ringScalarExtensionCoordinates (g.comp f) P)
            (ringScalarExtensionCoordinates h D
              (((ringScalarExtension h).map
                ((ringScalarExtensionCompIso f g).hom.app P)).hom.hom x))) :=
      ringScalarExtensionCompIso_hom_coordinates (g.comp f) h P _
    _ = compositionLinearEquiv (g.comp f) h P
        (linearMap h (compositionLinearEquiv f g P).toLinearMap w) := by
      rw [tensorLinearEquiv_value, hm]
      exact congrArg (compositionLinearEquiv (g.comp f) h P)
        (LinearMap.congr_fun hlift z)
    _ = compositionLinearEquiv f (h.comp g) P
        (compositionLinearEquiv g h (tensor f P) w) :=
      LinearMap.congr_fun (tensorComp_assoc f g h P) w
    _ = compositionLinearEquiv f (h.comp g) P
        (linearMap (h.comp g) (ringScalarExtensionCoordinates f P).toLinearMap
          (compositionLinearEquiv g h A v)) :=
      congrArg (compositionLinearEquiv f (h.comp g) P) hn
    _ = ringScalarExtensionCoordinates (h.comp (g.comp f)) P
        (((ringScalarExtensionCompIso f (h.comp g)).hom.app P).hom.hom
          (((ringScalarExtensionCompIso g h).hom.app A).hom.hom x)) := by
      change compositionLinearEquiv f (h.comp g) P
          (linearMap (h.comp g) (ringScalarExtensionCoordinates f P).toLinearMap
            (compositionLinearEquiv g h A v)) =
        ringScalarExtensionCoordinates ((h.comp g).comp f) P
          (((ringScalarExtensionCompIso f (h.comp g)).hom.app P).hom.hom
            (((ringScalarExtensionCompIso g h).hom.app A).hom.hom x))
      rw [ringScalarExtensionCompIso_hom_coordinates f (h.comp g) P,
        ringScalarExtensionCompIso_hom_coordinates g h A,
        tensorLinearEquiv_value, tensorLinearEquiv_value]

private theorem comparisonWhiskerRight_hom_app
    {C : Type*} {D : Type*} {E : Type*} {A : Type*}
    [Category* C] [Category* D] [Category* E] [Category* A]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ A) {K : C ⥤ E} {L : C ⥤ A}
    (α : F ⋙ G ≅ K) (β : K ⋙ H ≅ L) (X : C) :
    (Functor.isoWhiskerRight α H ≪≫ β).hom.app X = H.map (α.hom.app X) ≫ β.hom.app X := by
  rfl

private theorem comparisonWhiskerLeft_hom_app
    {C : Type*} {D : Type*} {E : Type*} {A : Type*}
    [Category* C] [Category* D] [Category* E] [Category* A]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ A) {M : D ⥤ A} {L : C ⥤ A}
    (β : G ⋙ H ≅ M) (γ : F ⋙ M ≅ L) (X : C) :
    (Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F β ≪≫ γ).hom.app X =
      β.hom.app (F.obj X) ≫ γ.hom.app X := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp]

private theorem compIso_assoc_app {U : Type uU} [Ring U]
    (f : R →+* S) (g : S →+* T) (h : T →+* U) (P : FGProjectiveCat.{uR} R) :
    (ringScalarExtension h).map ((ringScalarExtensionCompIso f g).hom.app P) ≫
        (ringScalarExtensionCompIso (g.comp f) h).hom.app P =
      (ringScalarExtensionCompIso g h).hom.app ((ringScalarExtension f).obj P) ≫
        (ringScalarExtensionCompIso f (h.comp g)).hom.app P := by
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  exact compIso_assoc_apply f g h P x

private theorem compIso_assoc_hom {U : Type uU} [Ring U]
    (f : R →+* S) (g : S →+* T) (h : T →+* U) :
    (Functor.isoWhiskerRight (ringScalarExtensionCompIso f g) (ringScalarExtension h) ≪≫
        ringScalarExtensionCompIso (g.comp f) h).hom =
      (Functor.associator (ringScalarExtension f) (ringScalarExtension g) (ringScalarExtension h) ≪≫
        Functor.isoWhiskerLeft (ringScalarExtension f) (ringScalarExtensionCompIso g h) ≪≫
        ringScalarExtensionCompIso f (h.comp g)).hom := by
  apply NatTrans.ext
  funext P
  exact (comparisonWhiskerRight_hom_app (ringScalarExtension f) (ringScalarExtension g)
    (ringScalarExtension h) (ringScalarExtensionCompIso f g)
    (ringScalarExtensionCompIso (g.comp f) h) P).trans
      ((compIso_assoc_app f g h P).trans
        (comparisonWhiskerLeft_hom_app (ringScalarExtension f) (ringScalarExtension g)
          (ringScalarExtension h) (ringScalarExtensionCompIso g h)
          (ringScalarExtensionCompIso f (h.comp g)) P).symm)

/-- The two original native scalar-comparison routes agree as whole natural isomorphisms. -/
theorem ringScalarExtensionCompIso_assoc {U : Type uU} [Ring U]
    (f : R →+* S) (g : S →+* T) (h : T →+* U) :
    Functor.isoWhiskerRight (ringScalarExtensionCompIso f g) (ringScalarExtension h) ≪≫
        ringScalarExtensionCompIso (g.comp f) h =
      Functor.associator (ringScalarExtension f) (ringScalarExtension g) (ringScalarExtension h) ≪≫
        Functor.isoWhiskerLeft (ringScalarExtension f) (ringScalarExtensionCompIso g h) ≪≫
        ringScalarExtensionCompIso f (h.comp g) :=
  Iso.ext (compIso_assoc_hom f g h)

end FGProjectiveCat

end
