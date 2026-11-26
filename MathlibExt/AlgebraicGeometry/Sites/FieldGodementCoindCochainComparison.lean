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
# Iterated Godement and coinduction comparisons over a field

Let k have prescribed separable closure Ω, Φ be its Galois stalk functor, T the field Godement
monad, and S the diagonal continuous coinduction monad. The prescribed point comparison gives
Φ(TF) ≅ S(ΦF) and preserves the unit.

Iterating gives natural power isomorphisms and termwise coresolution isomorphisms compatible
with every coface. The Γ/invariant comparison then identifies Godement sections with
invariants of the coinduction coresolution, yielding an alternating cochain-complex
isomorphism. The coinduction invariant complex is the continuous homogeneous
coefficient complex, so the Godement sections complex computes those same cochains at height
max(u,w).
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
/-- Let k have prescribed separable closure Ω, Φ be its Galois stalk, and f : F → F′, g : G → G′
sheaf maps. The Galois-module tensor comparison t satisfies
Φ(f⊗g)≫t_{F′,G′}.hom=t_{F,G}.hom≫(Φf⊗Φg). The target tensor has the diagonal Galois action and
the underlying integer tensor of coefficient groups. -/
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

/-- For a field k, prescribed separable closure Ω, prescribed point monad T_Ω, diagonal
coinduction monad S, and Galois stalk Φ, there is an isomorphism Φ(T_Ω^nF) ≅ S^n(ΦF) for every
n∈ℕ and small-étale sheaf F. It iterates the fixed point-to-coinduction endofunctor
comparison. -/
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
/-- Let k have prescribed separable closure Ω, f : F → G be a sheaf map, and e_n : Φ(T_Ω^n−) ≅
S^nΦ the prescribed point power comparison. Then Φ(T_Ω^n f)≫e_n(G).hom=e_n(F).hom≫S^n(Φf). -/
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
/-- For k,Ω with IsSepClosure k Ω, let e_n compare Φ(T_Ω^nF) with S^nΦF. For i∈Fin(n+1),
Φ(etaAtPos(T_Ω,n,i,F))≫e_{n+1}(F).hom=e_n(F).hom≫etaAtPos(S,n,i,ΦF). The equality uses the
same raw insertion position. -/
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
/-- Let k have prescribed separable closure Ω and e_n be the point-to-coinduction power
comparison. For i∈Fin(n+1),
Φ(barEtaAtPos(T_Ω,n,i,F))≫e_{n+1}.hom=e_n.hom≫barEtaAtPos(S,n,i,ΦF). Both bar insertions use
the reversed finite position i.rev. -/
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

/-- For a field k and prescribed separable closure Ω, compose the Godement-to-prescribed-point
comparison with the point-to-coinduction comparison. This gives T_G⋙Φ ≅ Φ⋙S, where S is
diagonal continuous coinduction on discrete Galois modules and Φ the geometric Galois stalk
functor. -/
def fieldGodementCoindFunctorIso :
    (smallEtaleGodementMonad.{u, w} (Spec (.of k))).toFunctor ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)).toFunctor :=
  Functor.isoWhiskerRight (fieldGodementPrescribedPointEndofunctorIso.{u, w} k Ω)
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) ≪≫
    fieldPrescribedPointCoindFunctorIso.{u, w} k Ω

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k have prescribed separable closure Ω and c : Φ(T_GF) ≅ S(ΦF) be the Godement/coinduction
endofunctor comparison. Then Φ(η_G,F)≫c_F.hom=η_S,ΦF. The target unit is the equivariant
constant-function inclusion into diagonal coinduction. -/
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

/-- For a field k, prescribed separable closure Ω, Godement monad T_G, coinduction monad S, and
Galois stalk Φ, there are isomorphisms Φ(T_G^nF) ≅ S^n(ΦF) for every n∈ℕ. They are obtained
from the fixed cross-endofunctor isomorphism and retain the same coefficient object ΦF. -/
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
/-- Let k have prescribed separable closure Ω, f : F → G be a sheaf map, and e_n compare Φ(T_G^n−)
with S^nΦ. Then Φ(T_G^n f)≫e_n(G).hom=e_n(F).hom≫S^n(Φf) for every n∈ℕ. -/
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

/-- For a field k with prescribed separable closure Ω, let T_G be Godement, S coinduction, c_F :
Φ(T_GF) ≅ SΦF, and e_n the power comparison. Its successor satisfies
e_{n+1}(F).hom=e_n(T_GF).hom≫S^n(c_F.hom). This is the specified recursive comparison map. -/
theorem fieldGodementCoindPowerIso_succ_hom (n : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    (fieldGodementCoindPowerIso.{u, w} k Ω (n + 1) F).hom =
      (fieldGodementCoindPowerIso.{u, w} k Ω n (T.obj F)).hom ≫
        (Monad.monadPow S n).map ((fieldGodementCoindFunctorIso.{u, w} k Ω).hom.app F) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k have prescribed separable closure Ω, Φ its Galois stalk, and e_n : Φ(T_G^nF) ≅ S^nΦF.
For i∈Fin(n+1), Φ(barEtaAtPos(T_G,n,i,F))≫e_{n+1}.hom=e_n.hom≫barEtaAtPos(S,n,i,ΦF). The
insertion uses the right-counted bar convention on both sides. -/
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

/-- For a field k and prescribed separable closure Ω, the nth term of the Godement coresolution of
F, after applying Φ, is isomorphic to the nth term of the monad coresolution of S at ΦF. The
map uses the Godement degree chart to T_G^{n+1}F, the power comparison e_{n+1}, and the
inverse coinduction degree chart. -/
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
/-- Let k have prescribed separable closure Ω, c_n be the Godement/coinduction coresolution term
charts, and i∈Fin(n+2). Then Φ(d_G^i)≫c_{n+1}.hom=c_n.hom≫d_S^i. The equality compares the
same coface in the two degree-n and degree-(n+1) terms. -/
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

/-- For a field k, prescribed separable closure Ω, and sheaf F, the term isomorphisms
Φ(Core_{T_G}F)_n ≅ Core_S(ΦF)_n for all n form a CofaceIso. Its coface equations are those of
fieldGodementCoindCoresolutionTermIso_coface; this is the coface-compatible data used for
alternating differentials. -/
def fieldGodementCoindCofaceIso
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    CosimplicialCup.CofaceIso
      ((smallEtaleGodementCoresolution.{u, w} (Spec (.of k)) F) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)) where
  app n := fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F n
  coface n i := fieldGodementCoindCoresolutionTermIso_coface.{u, w} k Ω F n i

/-- Let k have prescribed separable closure Ω and F be a small-étale sheaf. Apply Γ≅Φ⋙Inv to each
Godement coresolution term and combine it with the coinduction term CofaceIso. This gives a
CofaceIso from the Godement sections cosimplicial object to Core_S(ΦF) followed by Galois
invariants. -/
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

/-- For a field k and prescribed separable closure Ω, the Godement sections complex of F is
isomorphic to the alternating coface complex of Core_S(ΦF) followed by invariants. The map is
the inverse Godement alternating-sections comparison followed by the alternating isomorphism
of the sections CofaceIso. -/
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
/-- Let k have prescribed separable closure Ω and M be a discrete continuous Galois module of
height max(u,w). The alternating complex of invariants of Core_S(M) is isomorphic to
ContinuousCohomology.discreteCoefficientCochainFunctor(G)(M). This is the additive-group
complex of continuous homogeneous coefficient cochains, obtained from the coinduction
coresolution comparison and the invariants/forgetful functors. -/
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

/-- For a field k, prescribed separable closure Ω, and small-étale additive-group sheaf F of
height max(u,w), the Godement sections complex is isomorphic to the continuous homogeneous
coefficient cochain complex of Gal(Ω/k) with coefficient ΦF. It composes the
Godement/coinduction-invariants comparison with fieldCoindInvariantCochainIso. -/
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
