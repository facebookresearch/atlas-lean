/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionAdjunction
public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Geometric skyscrapers and continuous Galois coinduction

Let k,Ω be fields of universe u with Ω a prescribed separable closure, G=Gal(Ω/k) with its
Krull topology, and Φ the geometric stalk functor to discrete continuous G-actions on additive
groups of height max(u,w). Transporting the geometric point adjunction identifies Φ∘x_* as the
right adjoint of the forgetful G-action functor.

It is naturally isomorphic to continuous functions G → M with left-shift action, by z ↦ (g ↦
ε_M(g⁻¹·z)). For a sheaf Q with Galois stalk A, the coefficient untwist f(g) ↦ g·f(g)
identifies Φ(x_*x^*Q) with diagonal coinduction of A. The point unit becomes the
constant-function map a ↦ (g ↦ a), and evaluation at 1 is the geometric counit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u w c d b v₁ v₂ v₃

set_option backward.isDefEq.respectTransparency.types false in
private theorem equivalenceUnitMap {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] (E : C ≌ D) (Q : C) :
    E.functor.map (E.unitIso.hom.app Q) = E.counitIso.inv.app (E.functor.obj Q) := by
  apply (cancel_mono (E.counitIso.hom.app (E.functor.obj Q))).1
  exact (E.functor_unitIso_comp Q).trans
    (E.counitIso.inv_hom_id_app (E.functor.obj Q)).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem transportedPointCounit {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] {B : Type b} [Category.{v₃} B]
    (E : C ≌ D) (U : D ⥤ B) (H : B ⥤ C) (adj : E.functor ⋙ U ⊣ H)
    (e : E.inverse ⋙ (E.functor ⋙ U) ≅ U)
    (he : ∀ A : D, e.hom.app A = U.map (E.counitIso.hom.app A)) (M : B) :
    ((E.symm.toAdjunction.comp adj).ofNatIsoLeft e).counit.app M = adj.counit.app M := by
  have hi (A : D) : e.inv.app A = U.map (E.counitIso.inv.app A) := by
    apply (cancel_mono (e.hom.app A)).1
    rw [e.inv_hom_id_app, he A, ← U.map_comp, E.counitIso.inv_hom_id_app, U.map_id]
    rfl
  change e.inv.app (E.functor.obj (H.obj M)) ≫
    (E.symm.toAdjunction.comp adj).counit.app M = adj.counit.app M
  rw [Adjunction.comp_counit_app]
  change e.inv.app (E.functor.obj (H.obj M)) ≫
    (U.map (E.functor.map (E.unitIso.inv.app (H.obj M))) ≫ adj.counit.app M) =
      adj.counit.app M
  rw [hi, ← equivalenceUnitMap E (H.obj M), ← Category.assoc,
    ← U.map_comp, ← E.functor.map_comp, E.unitIso.hom_inv_id_app,
    E.functor.map_id]
  dsimp only [Functor.id_obj]
  exact (congrArg
    (fun f : U.obj (E.functor.obj (H.obj M)) ⟶ U.obj (E.functor.obj (H.obj M)) =>
      f ≫ adj.counit.app M) (U.map_id (E.functor.obj (H.obj M)))).trans
    (Category.id_comp (adj.counit.app M))

set_option backward.isDefEq.respectTransparency.types false in
private theorem transportedPointUnit {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] {B : Type b} [Category.{v₃} B]
    (E : C ≌ D) (U : D ⥤ B) (H : B ⥤ C) (adj : E.functor ⋙ U ⊣ H)
    (e : E.inverse ⋙ (E.functor ⋙ U) ≅ U)
    (he : ∀ A : D, e.hom.app A = U.map (E.counitIso.hom.app A)) (Q : C) :
    ((E.symm.toAdjunction.comp adj).ofNatIsoLeft e).unit.app (E.functor.obj Q) =
      E.functor.map (adj.unit.app Q) := by
  change (E.symm.toAdjunction.comp adj).unit.app (E.functor.obj Q) ≫
    E.functor.map (H.map (e.hom.app (E.functor.obj Q))) = E.functor.map (adj.unit.app Q)
  rw [Adjunction.comp_unit_app]
  change (E.counitIso.inv.app (E.functor.obj Q) ≫
    E.functor.map (adj.unit.app (E.inverse.obj (E.functor.obj Q)))) ≫
      E.functor.map (H.map (e.hom.app (E.functor.obj Q))) = E.functor.map (adj.unit.app Q)
  have hn : E.unitIso.hom.app Q ≫ adj.unit.app (E.inverse.obj (E.functor.obj Q)) =
      adj.unit.app Q ≫ H.map (U.map (E.functor.map (E.unitIso.hom.app Q))) :=
    adj.unit.naturality (E.unitIso.hom.app Q)
  rw [he, ← equivalenceUnitMap E Q, ← E.functor.map_comp, hn, E.functor.map_comp,
    Category.assoc, ← E.functor.map_comp, ← H.map_comp, ← U.map_comp,
    E.functor_unitIso_comp, U.map_id]
  dsimp only [Functor.id_obj]
  have hi := (congrArg E.functor.map (H.map_id (U.obj (E.functor.obj Q)))).trans
    (E.functor.map_id (H.obj (U.obj (E.functor.obj Q))))
  exact (congrArg
    (fun f : E.functor.obj (H.obj (U.obj (E.functor.obj Q))) ⟶
        E.functor.obj (H.obj (U.obj (E.functor.obj Q))) =>
      E.functor.map (adj.unit.app Q) ≫ f) hi).trans
    (Category.comp_id (E.functor.map (adj.unit.app Q)))

private theorem rightAdjointUnitComparison {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] {F : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : F ⊣ R₁) (adj₂ : F ⊣ R₂) (A B : C)
    (η : A ⟶ R₁.obj (F.obj A)) (i : R₂.obj (F.obj A) ⟶ B) (j : A ⟶ B)
    (hη : η = adj₁.unit.app A) (hi : adj₂.unit.app A ≫ i = j) :
    η ≫ ((Adjunction.rightAdjointUniq adj₁ adj₂).hom.app (F.obj A) ≫ i) = j := by
  rw [hη, ← Category.assoc]
  exact (congrArg (fun f : A ⟶ R₂.obj (F.obj A) => f ≫ i)
    (Adjunction.unit_rightAdjointUniq_hom_app adj₁ adj₂ A)).trans hi

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k,Ω be fields with IsSepClosure k Ω, G=Gal(Ω/k), and Φ the geometric Galois stalk
equivalence at coefficient height max(u,w). The forgetful functor from discrete continuous
G-actions to additive groups is left adjoint to M ↦ Φ(x_*M), where x_* is the prescribed
geometric skyscraper functor. -/
def fieldGaloisSkyscraperAdjunction :
    DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k) ⊣
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ⋙ fieldGeometricStalkGaloisFunctor.{u, w} k Ω :=
  (((fieldSheafGaloisEquivalence.{u, w} k Ω).symm.toAdjunction).comp
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))).ofNatIsoLeft (fieldModuleForgetIso.{u, w} k Ω)

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k, prescribed separable closure Ω, and M∈AddCommGrpCat.{max(u,w)}, the counit of
the forgetful-Galois/skyscraper-stalk adjunction at M equals the geometric stalk–skyscraper
counit ε_M : x^*x_*M → M. -/
theorem fieldGaloisSkyscraperAdjunction_counit (M : AddCommGrpCat.{max u w}) :
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω).counit.app M =
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app M := by
  exact transportedPointCounit (fieldSheafGaloisEquivalence.{u, w} k Ω)
    (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)) _
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))
    (fieldModuleForgetIso.{u, w} k Ω) (fieldModuleForgetIso_hom.{u, w} k Ω) M

set_option backward.isDefEq.respectTransparency.types false in
/-- Let Q be an additive-group small-étale sheaf over a field k with prescribed separable closure
Ω. At its Galois stalk A=Φ(Q), the transported adjunction unit equals Φ applied to the
geometric point unit Q → x_*x^*Q. Its target is Φ(x_*x^*Q). -/
theorem fieldGaloisSkyscraperAdjunction_unit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω).unit.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
            (A := AddCommGrpCat.{max u w})).unit.app Q) := by
  exact transportedPointUnit (fieldSheafGaloisEquivalence.{u, w} k Ω)
    (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)) _
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))
    (fieldModuleForgetIso.{u, w} k Ω) (fieldModuleForgetIso_hom.{u, w} k Ω) Q

set_option backward.isDefEq.respectTransparency.types false in
/-- For k,Ω with IsSepClosure k Ω and G=Gal(Ω/k), there is a natural isomorphism M ↦ Φ(x_*M) ≅
C(G,M) in discrete continuous G-actions. Here M is an additive group of height max(u,w) with
trivial coefficient action and C(G,M) has left-shift action (h·f)(g)=f(h⁻¹g). The isomorphism
is the right-adjoint comparison for the forgetful functor. -/
def fieldGaloisSkyscraperCoindIso :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ⋙ fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
      DiscreteAbelianAction.forgetCoindFunctor.{u, w} Gal(Ω/k) :=
  Adjunction.rightAdjointUniq (fieldGaloisSkyscraperAdjunction.{u, w} k Ω)
    (DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k have prescribed separable closure Ω, M an additive-group coefficient, and z∈Φ(x_*M).
Under the left-shift coinduction comparison e_M, its function value at 1 satisfies
e_M(z)(1)=ε_M(z), where ε_M is the geometric stalk–skyscraper counit. -/
theorem fieldGaloisSkyscraperCoindIso_counit_apply (M : AddCommGrpCat.{max u w})
    (z : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj M))) :
    DiscreteAbelianAction.coindFunction.{u, w} (DiscreteAbelianAction.trivialObject Gal(Ω/k) M)
        (DiscreteAbelianAction.homToAdd
            ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z) 1 =
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app M).hom z := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω)
    (DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k)) M
  have hv := ConcreteCategory.congr_hom h z
  change ((DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k)).counit.app M).hom
      (DiscreteAbelianAction.homToAdd ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z) =
    ((fieldGaloisSkyscraperAdjunction.{u, w} k Ω).counit.app M).hom z at hv
  exact (DiscreteAbelianAction.forgetCoindAdjunction_counit_apply.{u, w} Gal(Ω/k) M _).symm.trans
    (hv.trans (congrArg (fun f => f.hom z) (fieldGaloisSkyscraperAdjunction_counit.{u, w} k Ω M)))

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k, prescribed separable closure Ω, additive group M, z∈Φ(x_*M), and g∈Gal(Ω/k),
the skyscraper/coinduction comparison satisfies e_M(z)(g)=ε_M(g⁻¹·z). The G-action on z is its
geometric stalk action, and the target function has trivial coefficient action. -/
theorem fieldGaloisSkyscraperCoindIso_apply (M : AddCommGrpCat.{max u w})
    (z : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj M)))
    (g : Gal(Ω/k)) :
    DiscreteAbelianAction.coindFunction.{u, w} (DiscreteAbelianAction.trivialObject Gal(Ω/k) M)
        (DiscreteAbelianAction.homToAdd
            ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z) g =
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app M).hom (g⁻¹ • z) := by
  have h := DiscreteAbelianAction.forgetCoindEquivariantValue.{u, w} Gal(Ω/k) _ M
    ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z g
  exact h.symm.trans (fieldGaloisSkyscraperCoindIso_counit_apply.{u, w} k Ω M (g⁻¹ • z))

/-- Let k have prescribed separable closure Ω and f : M → N be an additive-group map of height
max(u,w). The comparison e satisfies Φ(x_*f)≫e_N.hom=e_M.hom≫Coind(trivial(f)). This
identifies the sheaf-induced map with postcomposition of continuous coinduced functions by f. -/
theorem fieldGaloisSkyscraperCoindIso_naturality {M N : AddCommGrpCat.{max u w}} (f : M ⟶ N) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).map f) ≫
      (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app N =
    (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M ≫
      DiscreteAbelianAction.coind.{u, w}.map (DiscreteAbelianAction.trivialMap Gal(Ω/k) f) :=
  (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.naturality f

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k, prescribed separable closure Ω, and small-étale sheaf Q, write A=Φ(Q). The
isomorphism Φ(x_*x^*Q) ≅ Coind(A) is the left-shift skyscraper comparison followed by the
coefficient untwist f(g)↦g·f(g). The target has diagonal action (h·f)(g)=h·f(h⁻¹g), using the
Galois action on A. -/
def fieldGaloisPointCoindIso
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
              (A := AddCommGrpCat.{max u w})).obj Q)) ≅
      DiscreteAbelianAction.coind.{u, w}.obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
  (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).app
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
          (A := AddCommGrpCat.{max u w})).obj Q) ≪≫
    DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k)
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)

set_option backward.isDefEq.respectTransparency.types false in
private theorem fieldGaloisPointCoindIsoHomModel
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGaloisPointCoindIso.{u, w} k Ω Q).hom =
      (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app
        ((DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) ≫
        (DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k)
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k have prescribed separable closure Ω, Q a small-étale additive-group sheaf, A=Φ(Q), η=Φ(Q
→ x_*x^*Q), and i : Φ(x_*x^*Q) ≅ Coind(A) the diagonal comparison. Then η≫i.hom=coindIota_A,
the equivariant inclusion taking a∈A to the constant function g↦a. -/
theorem fieldGaloisPointCoindIso_unit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let A : FieldCohomologyModule.{u, w} k Ω := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q
    let T : FieldCohomologyModule.{u, w} k Ω :=
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
          (A := AddCommGrpCat.{max u w})).obj
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
            (A := AddCommGrpCat.{max u w})).obj Q))
    let η : A ⟶ T := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
        (A := AddCommGrpCat.{max u w})).unit.app Q)
    let i : T ≅ DiscreteAbelianAction.coind.{u, w}.obj A := fieldGaloisPointCoindIso.{u, w} k Ω Q
    η ≫ i.hom = DiscreteAbelianAction.coindIota.{u, w}.app A := by
  intro A T η i
  have hη : η = (fieldGaloisSkyscraperAdjunction.{u, w} k Ω).unit.app A :=
    (fieldGaloisSkyscraperAdjunction_unit.{u, w} k Ω Q).symm
  have h := rightAdjointUnitComparison
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω)
    (DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k)) A
    (DiscreteAbelianAction.coind.{u, w}.obj A) η
    (DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k) A).hom
    (DiscreteAbelianAction.coindIota.{u, w}.app A) hη
    (DiscreteAbelianAction.forgetCoindAdjunction_unit_untwist.{u, w} Gal(Ω/k) A)
  have hi := fieldGaloisPointCoindIsoHomModel.{u, w} k Ω Q
  exact (congrArg (fun f : T ⟶ DiscreteAbelianAction.coind.{u, w}.obj A => η ≫ f) hi).trans h

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k, prescribed separable closure Ω, small-étale sheaf Q, a∈Φ(Q), and g∈Gal(Ω/k),
the point-unit map followed by the diagonal coinduction comparison has value a at g. Thus its
continuous function is constant with the given vector. -/
theorem fieldGaloisPointCoindIso_unit_apply
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (a : DiscreteAbelianAction.underlying ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
    (g : Gal(Ω/k)) :
    DiscreteAbelianAction.coindFunction.{u, w} ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
      (DiscreteAbelianAction.homToAdd
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
              (A := AddCommGrpCat.{max u w})).unit.app Q) ≫
            (fieldGaloisPointCoindIso.{u, w} k Ω Q).hom) a) g = a := by
  have h := fieldGaloisPointCoindIso_unit.{u, w} k Ω Q
  exact (congrArg (fun f => DiscreteAbelianAction.coindFunction.{u, w}
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
        (DiscreteAbelianAction.homToAdd f a) g) h).trans
    (DiscreteAbelianAction.coindIota_apply.{u, w}
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) a g)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k have prescribed separable closure Ω, Q be a small-étale additive-group sheaf, and
z∈Φ(x_*x^*Q). The diagonal coinduction comparison satisfies i_Q(z)(1)=ε_{x^*Q}(z). The
coefficient untwist leaves evaluation at the identity unchanged. -/
theorem fieldGaloisPointCoindIso_eval_one
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (z : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
              (A := AddCommGrpCat.{max u w})).obj Q)))) :
    DiscreteAbelianAction.coindFunction.{u, w} ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
        (DiscreteAbelianAction.homToAdd (fieldGaloisPointCoindIso.{u, w} k Ω Q).hom z) 1 =
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
            (A := AddCommGrpCat.{max u w})).obj Q)).hom z := by
  let A := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q
  let M :=
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
        (A := AddCommGrpCat.{max u w})).obj Q
  let e := (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M
  have h₁ := DiscreteAbelianAction.coindUntwistIso_eval_one.{u, w} Gal(Ω/k) A
    (DiscreteAbelianAction.homToAdd e z)
  have h₂ := fieldGaloisSkyscraperCoindIso_counit_apply.{u, w} k Ω M z
  change DiscreteAbelianAction.coindFunction.{u, w} A
      (DiscreteAbelianAction.homToAdd (DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k) A).hom
        (DiscreteAbelianAction.homToAdd e z)) 1 = _
  exact h₁.trans h₂

end AlgebraicGeometry.Scheme.DerivedSections
