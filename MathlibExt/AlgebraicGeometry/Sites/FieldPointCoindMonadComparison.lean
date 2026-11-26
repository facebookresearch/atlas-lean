/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementPrescribedTensorPairing
public import MathlibExt.AlgebraicGeometry.Sites.FieldGaloisSkyscraperComparison
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionCoresolution

/-!
# Point monad and continuous Galois coinduction

Let Ω/k be a separable closure of fields in universe u and c = max(u, w).
Let E send an abelian étale sheaf on Spec k to its geometric stalk with
continuous Gal(Ω/k)-action. For the point adjunction L ⊣ S at Spec Ω,
write T = S L for the sheaf point monad.

There is a natural isomorphism E T ≅ Coind E, where Coind(M) = C(G, M)
has diagonal action (g • φ)(x) = g • φ(g⁻¹x).
It commutes with sheaf coefficient maps and carries the point-monad
unit to the constant-function unit of coinduction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
Let E be the geometric-stalk Galois functor on abelian étale sheaves
over Spec k with coefficients in c, and T the monad of the point
stalk–skyscraper adjunction. This is the natural isomorphism
E(T(F)) ≅ Coind(E(F)), with Coind the diagonal continuous-function functor. -/
def fieldPrescribedPointCoindFunctorIso :
    (fieldPrescribedPointMonad.{u, w} k Ω).toFunctor ⋙ fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ DiscreteAbelianAction.coind.{u, w} :=
  Functor.isoWhiskerLeft
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
      (A := AddCommGrpCat.{max u w}))
    (fieldGaloisSkyscraperCoindIso.{u, w} k Ω) ≪≫
      Functor.isoWhiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (DiscreteAbelianAction.coindUntwistNatIso.{u, w} Gal(Ω/k))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For a morphism f : F → F′ of abelian étale sheaves with coefficients
in c, the comparison θ : E T ≅ Coind E satisfies
θ_F′ ∘ E(T(f)) = Coind(E(f)) ∘ θ_F.
Thus its square is natural in the sheaf coefficient map. -/
theorem fieldGaloisPointCoindIso_naturality
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : F ⟶ G) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldPrescribedPointMonad.{u, w} k Ω).map f) ≫
      (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.app G =
    (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.app F ≫
      DiscreteAbelianAction.coind.{u, w}.map
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) :=
  (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.naturality f

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an abelian étale sheaf F on Spec k with coefficients in c,
the comparison θ_F : E(T(F)) ≅ Coind(E(F)) satisfies
θ_F ∘ E(η_F) = const_(E(F)), where η is the point-monad unit.
It sends each stalk element to its constant continuous function. -/
theorem fieldPrescribedPointCoindFunctorIso_unit
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldPrescribedPointMonad.{u, w} k Ω).η.app F) ≫
      (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.app F =
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)).η.app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) := by
  rw [DiscreteAbelianAction.coindMonad_unit]
  exact fieldGaloisPointCoindIso_unit.{u, w} k Ω F

end AlgebraicGeometry.Scheme.DerivedSections
