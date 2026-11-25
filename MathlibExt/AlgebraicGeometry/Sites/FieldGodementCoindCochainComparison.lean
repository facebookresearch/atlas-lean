/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldPointCoindMonadComparison
public import MathlibExt.CategoryTheory.Monad.CrossPowerTransport
public import MathlibExt.AlgebraicTopology.SimplicialObject.CofaceComparison
public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementCofacePairingCoherence
public import MathlibExt.AlgebraicGeometry.Sites.FieldTensorCoefficientRestriction
public import MathlibExt.AlgebraicGeometry.Sites.FieldGlobalSectionsInvariants

/-!
# Actual iterated point-to-coinduction comparison over the prescribed field point

The original field Galois functor intertwines the actual prescribed point
monad with the actual diagonal continuous coinduction monad. Its checked
unit identity gives every original coface square on the iterated powers.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC uD vD uE vE u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections

open CategoryTheory.Monad

-- Retain the original field-facing public comparison names.
export CategoryTheory.Monad (crossMonadPowerIso)
export AlgebraicTopology.CosimplicialCup (cofaceIsoWhiskerNatIso)

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency.types false in
/-- The original field tensor-of-germs isomorphism is natural as an actual
Galois-module arrow, with the same original coefficient tensor map. -/
theorem fieldPointTensorGaloisIso_naturality
    {F F' G G' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map (smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) f g) ≫
        (fieldPointTensorGaloisIso.{u, w} k Ω F' G').hom =
      (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom ≫
        fieldTensorCoefficientModuleMap.{u, w} k Ω (J.map f) (J.map g) := by
  intro J
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  apply P.map_injective
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  change DiscreteAbelianAction.homToAdd (fieldPointTensorGaloisIso.{u, w} k Ω F' G').hom
      (DiscreteAbelianAction.homToAdd (J.map
          (smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) f g)) x) =
    DiscreteAbelianAction.homToAdd (fieldTensorCoefficientModuleMap.{u, w} k Ω (J.map f) (J.map g))
      (DiscreteAbelianAction.homToAdd (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom x)
  rw [fieldPointTensorGaloisIso_hom_apply, fieldPointTensorGaloisIso_hom_apply,
    fieldTensorCoefficientModuleMap_hom_apply]
  have h := fieldPointTensorTopRepIso_naturality.{u, w} k Ω f g
  exact congrArg (fun t => t.hom x) h

/-- The original prescribed-point iterates, under the same original field Galois
functor, are the actual iterates of diagonal continuous coinduction. -/
def fieldPrescribedPointCoindPowerIso (n : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := fieldPrescribedPointMonad.{u, w} k Ω
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.obj ((Monad.monadPow T n).obj F) ≅ (Monad.monadPow S n).obj (J.obj F) :=
  crossMonadPowerIso (fieldPrescribedPointMonad.{u, w} k Ω)
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω) n F

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original coefficient morphism commutes with the actual iterated
point-to-coinduction comparison. -/
theorem fieldPrescribedPointCoindPowerIso_naturality (n : ℕ)
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : F ⟶ G) :
    let T := fieldPrescribedPointMonad.{u, w} k Ω
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map ((Monad.monadPow T n).map f) ≫
        (fieldPrescribedPointCoindPowerIso.{u, w} k Ω n G).hom =
      (fieldPrescribedPointCoindPowerIso.{u, w} k Ω n F).hom ≫
        (Monad.monadPow S n).map (J.map f) :=
  crossMonadPowerIso_naturality (fieldPrescribedPointMonad.{u, w} k Ω)
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω) n f

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine checked point unit yields every original source-ordered unit
insertion square on the actual iterated point and coinduction powers. -/
theorem fieldPrescribedPointCoindPowerIso_etaAtPos (n : ℕ) (i : Fin (n + 1))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := fieldPrescribedPointMonad.{u, w} k Ω
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map (Monad.etaAtPos T n i F) ≫
        (fieldPrescribedPointCoindPowerIso.{u, w} k Ω (n + 1) F).hom =
      (fieldPrescribedPointCoindPowerIso.{u, w} k Ω n F).hom ≫
        Monad.etaAtPos S n i (J.obj F) :=
  crossMonadPowerIso_etaAtPos (fieldPrescribedPointMonad.{u, w} k Ω)
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω)
    (fieldPrescribedPointCoindFunctorIso_unit.{u, w} k Ω) n i F

set_option backward.isDefEq.respectTransparency.types false in
/-- The same actual comparison preserves every original right-counted coface
insertion used by the canonical monad coresolution. -/
theorem fieldPrescribedPointCoindPowerIso_barEtaAtPos (n : ℕ) (i : Fin (n + 1))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := fieldPrescribedPointMonad.{u, w} k Ω
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map (Monad.barEtaAtPos T n i F) ≫
        (fieldPrescribedPointCoindPowerIso.{u, w} k Ω (n + 1) F).hom =
      (fieldPrescribedPointCoindPowerIso.{u, w} k Ω n F).hom ≫
        Monad.barEtaAtPos S n i (J.obj F) :=
  fieldPrescribedPointCoindPowerIso_etaAtPos.{u, w} k Ω n i.rev F

/-- The genuine full Godement-to-prescribed-point comparison followed by the
actual original point-to-coinduction comparison. -/
def fieldGodementCoindFunctorIso :
    (smallEtaleGodementMonad.{u, w} (Spec (.of k))).toFunctor ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)).toFunctor :=
  Functor.isoWhiskerRight (fieldGodementPrescribedPointEndofunctorIso.{u, w} k Ω)
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) ≪≫
    fieldPrescribedPointCoindFunctorIso.{u, w} k Ω

set_option backward.isDefEq.respectTransparency.types false in
/-- The same actual composite carries the original Godement unit to the
original diagonal coinduction unit at the prescribed field fiber. -/
theorem fieldGodementCoindFunctorIso_unit
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map (T.η.app F) ≫ (fieldGodementCoindFunctorIso.{u, w} k Ω).hom.app F =
      S.η.app (J.obj F) := by
  intro T S J
  let P := fieldPrescribedPointMonad.{u, w} k Ω
  let a := fieldGodementPrescribedPointEndofunctorIso.{u, w} k Ω
  let b := fieldPrescribedPointCoindFunctorIso.{u, w} k Ω
  have hu : T.η.app F ≫ a.hom.app F = P.η.app F :=
    (fieldGodementPrescribedPointMonadIso.{u, w} k Ω).hom.app_η F
  change J.map (T.η.app F) ≫ (J.map (a.hom.app F) ≫ b.hom.app F) = S.η.app (J.obj F)
  rw [← Category.assoc, ← J.map_comp, hu]
  exact fieldPrescribedPointCoindFunctorIso_unit.{u, w} k Ω F

/-- Actual original Godement iterates at the prescribed field point are the
actual original coinduction iterates of the same Galois fiber. -/
def fieldGodementCoindPowerIso (n : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.obj ((Monad.monadPow T n).obj F) ≅ (Monad.monadPow S n).obj (J.obj F) :=
  crossMonadPowerIso (smallEtaleGodementMonad.{u, w} (Spec (.of k)))
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldGodementCoindFunctorIso.{u, w} k Ω) n F

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual full Godement/coinduction power comparison retains every
original coefficient morphism under the same original field Galois functor. -/
theorem fieldGodementCoindPowerIso_naturality (n : ℕ)
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : F ⟶ G) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map ((Monad.monadPow T n).map f) ≫ (fieldGodementCoindPowerIso.{u, w} k Ω n G).hom =
      (fieldGodementCoindPowerIso.{u, w} k Ω n F).hom ≫ (Monad.monadPow S n).map (J.map f) :=
  crossMonadPowerIso_naturality (smallEtaleGodementMonad.{u, w} (Spec (.of k)))
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldGodementCoindFunctorIso.{u, w} k Ω) n f

/-- The successor comparison is the actual previous comparison at the
Godement object followed by the same original base functor isomorphism. -/
theorem fieldGodementCoindPowerIso_succ_hom (n : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    (fieldGodementCoindPowerIso.{u, w} k Ω (n + 1) F).hom =
      (fieldGodementCoindPowerIso.{u, w} k Ω n (T.obj F)).hom ≫
        (Monad.monadPow S n).map ((fieldGodementCoindFunctorIso.{u, w} k Ω).hom.app F) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual original right-counted Godement coface insertion is carried
to the corresponding original diagonal coinduction insertion. -/
theorem fieldGodementCoindPowerIso_barEtaAtPos (n : ℕ) (i : Fin (n + 1))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map (Monad.barEtaAtPos T n i F) ≫
        (fieldGodementCoindPowerIso.{u, w} k Ω (n + 1) F).hom =
      (fieldGodementCoindPowerIso.{u, w} k Ω n F).hom ≫
        Monad.barEtaAtPos S n i (J.obj F) :=
  crossMonadPowerIso_etaAtPos (smallEtaleGodementMonad.{u, w} (Spec (.of k)))
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldGodementCoindFunctorIso.{u, w} k Ω)
    (fieldGodementCoindFunctorIso_unit.{u, w} k Ω) n i.rev F

/-- The actual canonical degree coordinates identify the original Godement
coresolution under J with the actual original coinduction coresolution. -/
def fieldGodementCoindCoresolutionTermIso
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.obj ((smallEtaleGodementCoresolution.{u, w} (Spec (.of k)) F).obj (SimplexCategory.mk n)) ≅
      (Monad.coresolution S (J.obj F)).obj (SimplexCategory.mk n) :=
  (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapIso
      (Monad.coresolutionObjIso (smallEtaleGodementMonad.{u, w} (Spec (.of k))) F n) ≪≫
    fieldGodementCoindPowerIso.{u, w} k Ω (n + 1) F ≪≫
      (Monad.coresolutionObjIso (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) n).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual original Godement coface commutes with the canonical
prescribed-point/coinduction coresolution degree comparison. -/
theorem fieldGodementCoindCoresolutionTermIso_coface
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (n : ℕ) (i : Fin (n + 2)) :
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map ((smallEtaleGodementCoresolution.{u, w} (Spec (.of k)) F).δ i) ≫
        (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F (n + 1)).hom =
      (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F n).hom ≫
        (Monad.coresolution S (J.obj F)).δ i := by
  intro S J
  let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
  let a := fun n => J.mapIso (Monad.coresolutionObjIso T F n)
  let b := fun n => fieldGodementCoindPowerIso.{u, w} k Ω (n + 1) F
  let c := fun n => Monad.coresolutionObjIso S (J.obj F) n
  let d := (smallEtaleGodementCoresolution.{u, w} (Spec (.of k)) F).δ i
  let t := Monad.barEtaAtPos T (n + 1) i F
  let s := Monad.barEtaAtPos S (n + 1) i (J.obj F)
  let z := (Monad.coresolution S (J.obj F)).δ i
  have ha : J.map d ≫ (a (n + 1)).hom = (a n).hom ≫ J.map t :=
    (J.map_comp d (Monad.coresolutionObjIso T F (n + 1)).hom).symm.trans
      ((congrArg J.map (Monad.coresolutionObjIso_coface T F i)).trans
        (J.map_comp (Monad.coresolutionObjIso T F n).hom t))
  have hb : J.map t ≫ (b (n + 1)).hom = (b n).hom ≫ s :=
    fieldGodementCoindPowerIso_barEtaAtPos.{u, w} k Ω (n + 1) i F
  have hc : z ≫ (c (n + 1)).hom = (c n).hom ≫ s :=
    Monad.coresolutionObjIso_coface S (J.obj F) i
  exact threeCoordinateSquares (J.map d) (J.map t) s z
    (a n) (a (n + 1)) (b n) (b (n + 1)) (c n) (c (n + 1)) ha hb hc

/-- The actual prescribed-field degree isomorphisms with all original coface
squares, on the same original Galois module objects. -/
def fieldGodementCoindCofaceIso
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    CosimplicialCup.CofaceIso
      ((smallEtaleGodementCoresolution.{u, w} (Spec (.of k)) F) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)) where
  app n := fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F n
  coface n i := fieldGodementCoindCoresolutionTermIso_coface.{u, w} k Ω F n i

/-- The actual Γ-to-invariants comparison and the original prescribed-field
coface isomorphisms identify the same original Godement sections degrees. -/
def fieldGodementCoindSectionsCofaceIso
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    CosimplicialCup.CofaceIso (smallEtaleGodementSectionsCosimplicial.{u, w} (Spec (.of k)) F)
      (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) ⋙
          DiscreteAbelianAction.invariantsFunctor) :=
  cofaceIsoWhiskerNatIso
    (smallEtaleGodementCoresolution.{u, w} (Spec (.of k)) F)
    (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F))
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    DiscreteAbelianAction.invariantsFunctor
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω)
    (fieldGodementCoindCofaceIso.{u, w} k Ω F)

/-- The same actual original coface degree maps give a comparison of the
original Godement sections complex with the actual coinduction invariants complex. -/
def fieldGodementCoindSectionsComplexIso
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleGodementSectionsComplex.{u, w} (Spec (.of k)) F ≅
      AlternatingCofaceMapComplex.obj
        (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) ⋙
            DiscreteAbelianAction.invariantsFunctor) :=
  (smallEtaleGodementAlternatingSectionsIso.{u, w} (Spec (.of k)) F).symm ≪≫
    (fieldGodementCoindSectionsCofaceIso.{u, w} k Ω F).alternatingIso

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical coinduction invariants complex is the algebraic
complex of the same original continuous homogeneous cochains, at ranks `{0,u,w}`. -/
def fieldCoindInvariantCochainIso (M : FieldCohomologyModule.{u, w} k Ω) :
    AlternatingCofaceMapComplex.obj
        (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M ⋙
          DiscreteAbelianAction.invariantsFunctor) ≅
      (ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M := by
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let V := TopRep.invariantsFunctor ℤ Gal(Ω/k)
  let U := ContinuousCohomology.discreteCoefficientForget.{max u w}
  let Q := V ⋙ U
  let A := Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M ⋙ P
  let a : AlternatingCofaceMapComplex.obj (A ⋙ Q) ≅
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)) :=
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
      (fun i j hij => additiveAlternatingCofaceComm Q A i j hij)
  exact a ≪≫ (Q.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (DiscreteAbelianAction.coindCoresolutionComplexIso.{u, w} Gal(Ω/k) M)

/-- The original Godement sections complex maps to the same original
continuous coefficient complex through the actual prescribed field point. -/
def fieldGodementOriginalContinuousCochainIso
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleGodementSectionsComplex.{u, w} (Spec (.of k)) F ≅
      (ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) :=
  fieldGodementCoindSectionsComplexIso.{u, w} k Ω F ≪≫
    fieldCoindInvariantCochainIso.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)

end AlgebraicGeometry.Scheme.DerivedSections
