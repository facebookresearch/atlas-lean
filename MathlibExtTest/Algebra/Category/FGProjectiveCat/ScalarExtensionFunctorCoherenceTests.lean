/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionFunctorCoherence

/-!
# Clients for native scalar-extension functor coherence

These clients use the original categorical maps and their tensor/shrink
coordinates. Ring worlds and raw module worlds remain independent.
-/

public section
noncomputable section

open CategoryTheory FGProjectiveCat ModuleCat.RingHomScalarExtension

universe uR uS uT uP uQ

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

example (f : R →+* S) (g : S →+* T) {P : Type uP} {Q : Type uQ}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (h : P →ₗ[R] Q) (x : tensor g (tensor f P)) :
    compositionLinearEquiv f g Q (linearMap g (linearMap f h) x) =
      linearMap (g.comp f) h (compositionLinearEquiv f g P x) :=
  LinearMap.congr_fun (compositionLinearEquiv_naturality f g h) x

example (f : R →+* S) {P Q : FGProjectiveCat.{uR} R} (h : P ⟶ Q) (s : S) (p : P) :
    ringScalarExtensionCoordinates f Q
        (((ringScalarExtension f).map h).hom.hom
          ((ringScalarExtensionCoordinates f P).symm (pure f P s p))) =
      pure f Q s (h.hom.hom p) := by
  have hn := LinearMap.congr_fun (ringScalarExtensionCoordinates_naturality f h)
    ((ringScalarExtensionCoordinates f P).symm (pure f P s p))
  change ringScalarExtensionCoordinates f Q
      (((ringScalarExtension f).map h).hom.hom
        ((ringScalarExtensionCoordinates f P).symm (pure f P s p))) =
    linearMap f h.hom.hom
      (ringScalarExtensionCoordinates f P
        ((ringScalarExtensionCoordinates f P).symm (pure f P s p))) at hn
  rw [hn, LinearEquiv.apply_symm_apply, linearMap_pure]

example (P : FGProjectiveCat.{uR} R) (r : R) (p : P) :
    ((ringScalarExtensionIdIso R).hom.app P).hom.hom
        ((ringScalarExtensionCoordinates (RingHom.id R) P).symm
          (pure (RingHom.id R) P r p)) = r • p := by
  rw [ringScalarExtensionIdIso_hom_apply, LinearEquiv.apply_symm_apply,
    identityTensorLinearEquiv_pure]

example (P : FGProjectiveCat.{uR} R) (p : P) :
    ringScalarExtensionCoordinates (RingHom.id R) P
        (((ringScalarExtensionIdIso R).inv.app P).hom.hom p) =
      pure (RingHom.id R) P 1 p := by
  rw [ringScalarExtensionIdIso_inv_apply, LinearEquiv.apply_symm_apply]

example {P Q : FGProjectiveCat.{uR} R} (h : P ⟶ Q)
    (x : (ringScalarExtension (RingHom.id R)).obj P) :
    ((ringScalarExtensionIdIso R).hom.app Q).hom.hom
        (((ringScalarExtension (RingHom.id R)).map h).hom.hom x) =
      h.hom.hom (((ringScalarExtensionIdIso R).hom.app P).hom.hom x) :=
  LinearMap.congr_fun (ringScalarExtensionIdIso_naturality R h) x

example (f : R →+* S) (g : S →+* T) {P Q : FGProjectiveCat.{uR} R}
    (h : P ⟶ Q) (t : T) (s : S) (p : P) :
    ringScalarExtensionCoordinates (g.comp f) Q
        (((ringScalarExtensionCompIso f g).hom.app Q).hom.hom
          (((ringScalarExtension g).map ((ringScalarExtension f).map h)).hom.hom
            ((ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).symm
              (pure g ((ringScalarExtension f).obj P) t
                ((ringScalarExtensionCoordinates f P).symm (pure f P s p)))))) =
      pure (g.comp f) Q (t * g s) (h.hom.hom p) := by
  let x := (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).symm
    (pure g ((ringScalarExtension f).obj P) t
      ((ringScalarExtensionCoordinates f P).symm (pure f P s p)))
  calc
    ringScalarExtensionCoordinates (g.comp f) Q
        (((ringScalarExtensionCompIso f g).hom.app Q).hom.hom
          (((ringScalarExtension g).map ((ringScalarExtension f).map h)).hom.hom x)) =
        ringScalarExtensionCoordinates (g.comp f) Q
          (((ringScalarExtension (g.comp f)).map h).hom.hom
            (((ringScalarExtensionCompIso f g).hom.app P).hom.hom x)) :=
      congrArg (ringScalarExtensionCoordinates (g.comp f) Q)
        (LinearMap.congr_fun (ringScalarExtensionCompIso_naturality f g h) x)
    _ = linearMap (g.comp f) h.hom.hom
        (ringScalarExtensionCoordinates (g.comp f) P
          (((ringScalarExtensionCompIso f g).hom.app P).hom.hom x)) :=
      LinearMap.congr_fun (ringScalarExtensionCoordinates_naturality (g.comp f) h)
        (((ringScalarExtensionCompIso f g).hom.app P).hom.hom x)
    _ = linearMap (g.comp f) h.hom.hom (pure (g.comp f) P (t * g s) p) :=
      congrArg (linearMap (g.comp f) h.hom.hom)
        (ringScalarExtensionCompIso_hom_nested_pure f g P t s p)
    _ = pure (g.comp f) Q (t * g s) (h.hom.hom p) :=
      linearMap_pure (g.comp f) h.hom.hom (t * g s) p

example (f : R →+* S) (g : S →+* T) (P : FGProjectiveCat.{uR} R) (t : T) (p : P) :
    ((ringScalarExtensionCompIso f g).inv.app P).hom.hom
        ((ringScalarExtensionCoordinates (g.comp f) P).symm (pure (g.comp f) P t p)) =
      (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).symm
        (pure g ((ringScalarExtension f).obj P) t
          ((ringScalarExtensionCoordinates f P).symm (pure f P 1 p))) :=
  ringScalarExtensionCompIso_inv_pure f g P t p

example (f : R →+* S) (g : S →+* T) (P : FGProjectiveCat.{uR} R)
    (x : (ringScalarExtension g).obj ((ringScalarExtension f).obj P)) :
    ((ringScalarExtensionCompIso f g).inv.app P).hom.hom
        (((ringScalarExtensionCompIso f g).hom.app P).hom.hom x) = x := by
  have hi := congrArg (fun h => h.hom.hom x) ((ringScalarExtensionCompIso f g).hom_inv_id_app P)
  exact hi

example (e : R ≃+* S) (P : FGProjectiveCat.{uR} R) :
    (ringScalarExtensionEquivalence e).functor.obj P =
      (ringScalarExtension e.toRingHom).obj P :=
  congrArg (fun F : FGProjectiveCat.{uR} R ⥤ FGProjectiveCat.{uS} S => F.obj P)
    (ringScalarExtensionEquivalence_functor e)

example (e : R ≃+* S) {P Q : FGProjectiveCat.{uS} S} (h : P ⟶ Q) :
    HEq ((ringScalarExtensionEquivalence e).inverse.map h)
      ((ringScalarExtension e.symm.toRingHom).map h) := by
  rw [ringScalarExtensionEquivalence_inverse]

example (e : R ≃+* S) (P : FGProjectiveCat.{uR} R) :
    let E := ringScalarExtensionEquivalence e
    E.functor.map (E.unitIso.hom.app P) ≫ E.counitIso.hom.app (E.functor.obj P) =
      𝟙 (E.functor.obj P) := by
  exact (ringScalarExtensionEquivalence e).functor_unitIso_comp P

example (f : R →+* S) (P : FGProjectiveCat.{uR} R)
    (x : (ringScalarExtension f).obj ((ringScalarExtension (RingHom.id R)).obj P)) :
    (((ringScalarExtensionCompIso (RingHom.id R) f ≪≫
        eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.comp_id f))).hom.app P).hom.hom x) =
      (((ringScalarExtension f).map ((ringScalarExtensionIdIso R).hom.app P)).hom.hom x) := by
  have he := congrArg
    (fun E : ringScalarExtension (RingHom.id R) ⋙ ringScalarExtension f ≅ ringScalarExtension f =>
      E.hom.app P) (ringScalarExtensionCompIso_id_left f)
  have hm : (ringScalarExtensionCompIso (RingHom.id R) f ≪≫
      eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.comp_id f))).hom.app P =
      (ringScalarExtension f).map ((ringScalarExtensionIdIso R).hom.app P) := by
    have he' : (ringScalarExtensionCompIso (RingHom.id R) f ≪≫
        eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.comp_id f))).hom.app P =
        (ringScalarExtension f).map ((ringScalarExtensionIdIso R).hom.app P) ≫
          𝟙 ((ringScalarExtension f).obj P) := by
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Functor.leftUnitor_hom_app] using he
    exact he'.trans (Category.comp_id _)
  exact congrArg (fun k => k.hom.hom x) hm

example (f : R →+* S) (P : FGProjectiveCat.{uR} R)
    (x : (ringScalarExtension (RingHom.id S)).obj ((ringScalarExtension f).obj P)) :
    (((ringScalarExtensionCompIso f (RingHom.id S) ≪≫
        eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.id_comp f))).hom.app P).hom.hom x) =
      (((ringScalarExtensionIdIso S).hom.app ((ringScalarExtension f).obj P)).hom.hom x) := by
  have he := congrArg
    (fun E : ringScalarExtension f ⋙ ringScalarExtension (RingHom.id S) ≅ ringScalarExtension f =>
      E.hom.app P) (ringScalarExtensionCompIso_id_right f)
  have hm : (ringScalarExtensionCompIso f (RingHom.id S) ≪≫
      eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.id_comp f))).hom.app P =
      (ringScalarExtensionIdIso S).hom.app ((ringScalarExtension f).obj P) := by
    have he' : (ringScalarExtensionCompIso f (RingHom.id S) ≪≫
        eqToIso (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.id_comp f))).hom.app P =
        (ringScalarExtensionIdIso S).hom.app ((ringScalarExtension f).obj P) ≫
          𝟙 ((ringScalarExtension f).obj P) := by
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] using he
    exact he'.trans (Category.comp_id _)
  exact congrArg (fun k => k.hom.hom x) hm

universe uU

variable {U : Type uU} [Ring U]

example (f : R →+* S) (g : S →+* T) (h : T →+* U) (P : FGProjectiveCat.{uR} R)
    (x : (ringScalarExtension h).obj ((ringScalarExtension g).obj ((ringScalarExtension f).obj P))) :
    (((Functor.isoWhiskerRight (ringScalarExtensionCompIso f g) (ringScalarExtension h) ≪≫
        ringScalarExtensionCompIso (g.comp f) h).hom.app P).hom.hom x) =
      (((Functor.associator (ringScalarExtension f) (ringScalarExtension g) (ringScalarExtension h) ≪≫
        Functor.isoWhiskerLeft (ringScalarExtension f) (ringScalarExtensionCompIso g h) ≪≫
        ringScalarExtensionCompIso f (h.comp g)).hom.app P).hom.hom x) :=
  congrArg
    (fun E : (ringScalarExtension f ⋙ ringScalarExtension g) ⋙ ringScalarExtension h ≅
      ringScalarExtension (h.comp (g.comp f)) => (E.hom.app P).hom.hom x)
    (ringScalarExtensionCompIso_assoc f g h)

private theorem originalNestedTriple (f : R →+* S) (g : S →+* T) (h : T →+* U) (P : FGProjectiveCat.{uR} R)
    (u : U) (t : T) (s : S) (p : P) :
    let A := (ringScalarExtension f).obj P
    let B := (ringScalarExtension g).obj A
    let x := (ringScalarExtensionCoordinates h B).symm
      (pure h B u ((ringScalarExtensionCoordinates g A).symm
        (pure g A t ((ringScalarExtensionCoordinates f P).symm (pure f P s p)))))
    ringScalarExtensionCoordinates (h.comp (g.comp f)) P
        (((ringScalarExtensionCompIso (g.comp f) h).hom.app P).hom.hom
          (((ringScalarExtension h).map ((ringScalarExtensionCompIso f g).hom.app P)).hom.hom x)) =
      pure (h.comp (g.comp f)) P (u * h (t * g s)) p := by
  dsimp only
  let A := (ringScalarExtension f).obj P
  let B := (ringScalarExtension g).obj A
  let D := (ringScalarExtension (g.comp f)).obj P
  let v := (ringScalarExtensionCoordinates g A).symm
    (pure g A t ((ringScalarExtensionCoordinates f P).symm (pure f P s p)))
  let x := (ringScalarExtensionCoordinates h B).symm (pure h B u v)
  have hm := LinearMap.congr_fun
    (ringScalarExtensionCoordinates_naturality h ((ringScalarExtensionCompIso f g).hom.app P)) x
  have hz : ringScalarExtensionCoordinates h B x = pure h B u v :=
    (ringScalarExtensionCoordinates h B).apply_symm_apply _
  have hp : linearMap h ((ringScalarExtensionCompIso f g).hom.app P).hom.hom (pure h B u v) =
      pure h D u (((ringScalarExtensionCompIso f g).hom.app P).hom.hom v) :=
    linearMap_pure h ((ringScalarExtensionCompIso f g).hom.app P).hom.hom u v
  calc
    ringScalarExtensionCoordinates (h.comp (g.comp f)) P
        (((ringScalarExtensionCompIso (g.comp f) h).hom.app P).hom.hom
          (((ringScalarExtension h).map ((ringScalarExtensionCompIso f g).hom.app P)).hom.hom x)) =
        compositionLinearEquiv (g.comp f) h P
          (tensorLinearEquiv h (ringScalarExtensionCoordinates (g.comp f) P)
            (ringScalarExtensionCoordinates h D
              (((ringScalarExtension h).map ((ringScalarExtensionCompIso f g).hom.app P)).hom.hom x))) :=
      ringScalarExtensionCompIso_hom_coordinates (g.comp f) h P _
    _ = compositionLinearEquiv (g.comp f) h P
        (tensorLinearEquiv h (ringScalarExtensionCoordinates (g.comp f) P)
          (linearMap h ((ringScalarExtensionCompIso f g).hom.app P).hom.hom
            (ringScalarExtensionCoordinates h B x))) :=
      congrArg (fun z => compositionLinearEquiv (g.comp f) h P
        (tensorLinearEquiv h (ringScalarExtensionCoordinates (g.comp f) P) z)) hm
    _ = compositionLinearEquiv (g.comp f) h P
        (tensorLinearEquiv h (ringScalarExtensionCoordinates (g.comp f) P)
          (pure h D u (((ringScalarExtensionCompIso f g).hom.app P).hom.hom v))) :=
      congrArg (fun z => compositionLinearEquiv (g.comp f) h P
        (tensorLinearEquiv h (ringScalarExtensionCoordinates (g.comp f) P) z))
        ((congrArg (linearMap h ((ringScalarExtensionCompIso f g).hom.app P).hom.hom) hz).trans hp)
    _ = compositionLinearEquiv (g.comp f) h P
        (pure h (tensor (g.comp f) P) u
          (ringScalarExtensionCoordinates (g.comp f) P
            (((ringScalarExtensionCompIso f g).hom.app P).hom.hom v))) :=
      congrArg (compositionLinearEquiv (g.comp f) h P)
        (tensorLinearEquiv_pure h (ringScalarExtensionCoordinates (g.comp f) P) u _)
    _ = compositionLinearEquiv (g.comp f) h P
        (pure h (tensor (g.comp f) P) u (pure (g.comp f) P (t * g s) p)) :=
      congrArg (fun z => compositionLinearEquiv (g.comp f) h P
        (pure h (tensor (g.comp f) P) u z))
        (ringScalarExtensionCompIso_hom_nested_pure f g P t s p)
    _ = pure (h.comp (g.comp f)) P (u * h (t * g s)) p :=
      compositionLinearEquiv_pure (g.comp f) h P u (t * g s) p

#print axioms FGProjectiveCat.ringScalarExtensionIdIso
#print axioms FGProjectiveCat.ringScalarExtensionCompIso
#print axioms FGProjectiveCat.ringScalarExtensionEquivalence
#print axioms FGProjectiveCat.ringScalarExtensionCompIso_id_left
#print axioms FGProjectiveCat.ringScalarExtensionCompIso_id_right
#print axioms FGProjectiveCat.ringScalarExtensionCompIso_assoc

end
