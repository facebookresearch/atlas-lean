/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.Closed
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod.EquivalenceFunctionTransport
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C)
  {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

/-- The selected module monoidal structure is the actual balanced relative tensor. -/
local instance originalModuleMonoidal : MonoidalCategory (Mod C A.X) :=
  Mod.instMonoidalCategory A

/-- The selected module closed structure uses the balanced internal-Hom adjunction. -/
local instance originalModuleClosed : MonoidalClosed (Mod C A.X) :=
  Mod.instMonoidalClosed A

/-- The actual original module internal Hom is transported through both complete original carrier
functors. -/
def sourceFunctor : (Mod C A.X)ᵒᵖ ⥤ (D ⥤ D) :=
  MonoidalClosed.internalHom ⋙
    (Functor.whiskeringLeft D (Mod C A.X) (Mod C A.X)).obj E.inverse ⋙
      (Functor.whiskeringRight D (Mod C A.X) D).obj E.functor

/-- The whole transported source value retains the original module internal-Hom functor and both
carrier functors. -/
theorem sourceFunctor_obj (M : Mod C A.X) :
    (sourceFunctor A E).obj (.op M) = E.inverse ⋙ Mod.internalHomOfEqualizer A M ⋙ E.functor := rfl

/-- Balanced smash with the given actual original module source has its original transported
internal-Hom adjunction. -/
def sourceAdjunction (M : Mod C A.X) :
    E.inverse ⋙ (Mod.relativeTensor A).obj M ⋙ E.functor ⊣
      (sourceFunctor A E).obj (.op M) := by
  let adj := (E.symm.toAdjunction.comp (Mod.relativeTensorInternalHomAdjunction A M)).comp
    E.toAdjunction
  exact adj.ofNatIsoRight (eqToIso (sourceFunctor_obj A E M)).symm

/-- The complete original internal Hom is lawful in both actual carrier variables. -/
def bifunctor : Dᵒᵖ ⥤ (D ⥤ D) := E.inverse.op ⋙ sourceFunctor A E

/-- The given entire original carrier object fixes the actual function functor. -/
def functor (X : D) : D ⥤ D := (bifunctor A E).obj (.op X)

/-- The whole original transported tensor object retains both actual inverse objects. -/
def smashObject (X Y : D) : D :=
  E.functor.obj (((Mod.relativeTensor A).obj (E.inverse.obj X)).obj (E.inverse.obj Y))

/-- The original balanced relative tensor retains its actual first carrier input. -/
def smashFunctor (X : D) : D ⥤ D :=
  { E.inverse ⋙ (Mod.relativeTensor A).obj (E.inverse.obj X) ⋙ E.functor with
    obj := smashObject A E X }

/-- The complete original balanced adjunction is carried through both actual carrier adjunctions. -/
def adjunction (X : D) : smashFunctor A E X ⊣ functor A E X := by
  let adj := (E.symm.toAdjunction.comp
    (Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj X))).comp E.toAdjunction
  exact adj.ofNatIsoRight (eqToIso (sourceFunctor_obj A E (E.inverse.obj X))).symm

/-- Every entire original carrier source map has its actual contravariant function map. -/
def precompose {X Y : D} (f : X ⟶ Y) : functor A E Y ⟶ functor A E X :=
  (bifunctor A E).map f.op

/-- A genuine original source comparison identifies the entire transported function functor with the
actual carrier-source function functor. -/
def sourceComparison (M : Mod C A.X) (X : D) (e : M ≅ E.inverse.obj X) :
    (sourceFunctor A E).obj (.op M) ≅ functor A E X :=
  (sourceFunctor A E).mapIso e.symm.op


/-- Every actual target map retains its whole original module internal-Hom map. -/
theorem functor_map (X : D) {Y Z : D} (f : Y ⟶ Z) :
    (functor A E X).map f =
      E.functor.map ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).map (E.inverse.map f)) := rfl

omit [HasEqualizers C] in
/-- Every balanced target map retains its original full relative-tensor module map. -/
theorem smashFunctor_map (X : D) {Y Z : D} (f : Y ⟶ Z) :
    (smashFunctor A E X).map f =
      E.functor.map (((Mod.relativeTensor A).obj (E.inverse.obj X)).map (E.inverse.map f)) := rfl

/-- Every full actual source map retains the same original closed module pre-map. -/
theorem precompose_app {X Y : D} (f : X ⟶ Y) (Z : D) :
    (precompose A E f).app Z =
      E.functor.map ((MonoidalClosed.pre (E.inverse.map f)).app (E.inverse.obj Z)) := rfl


/-- The actual unit keeps the two original carrier units and the balanced unit. -/
theorem adjunction_unit_app (X Y : D) :
    (adjunction A E X).unit.app Y =
      E.symm.toAdjunction.unit.app Y ≫
        E.functor.map ((Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj X)).unit.app
          (E.inverse.obj Y)) ≫
        E.functor.map ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).map
          (E.toAdjunction.unit.app
            (((Mod.relativeTensor A).obj (E.inverse.obj X)).obj (E.inverse.obj Y)))) := by
  let L := (Mod.relativeTensor A).obj (E.inverse.obj X)
  let R := Mod.internalHomOfEqualizer A (E.inverse.obj X)
  let a : L ⊣ R := Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj X)
  let b : E.inverse ⋙ L ⊣ R ⋙ E.functor := E.symm.toAdjunction.comp a
  let c : E.inverse ⋙ L ⋙ E.functor ⊣ E.inverse ⋙ R ⋙ E.functor :=
    b.comp E.toAdjunction
  let e : E.inverse ⋙ R ⋙ E.functor ≅ functor A E X :=
    (eqToIso (sourceFunctor_obj A E (E.inverse.obj X))).symm
  have h0 := congrArg (fun z => z.app Y) (Adjunction.ofNatIsoRight_unit c e)
  have he (Z : D) : e.hom.app Z = 𝟙 _ := rfl
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, he] at h0
  have h0' : (adjunction A E X).unit.app Y = c.unit.app Y :=
    h0.trans (Category.comp_id (c.unit.app Y))
  have h1 := Adjunction.comp_unit_app b E.toAdjunction Y
  have h2 := Adjunction.comp_unit_app E.symm.toAdjunction a Y
  change c.unit.app Y = b.unit.app Y ≫
    E.functor.map (R.map (E.toAdjunction.unit.app (L.obj (E.inverse.obj Y)))) at h1
  change b.unit.app Y = E.symm.toAdjunction.unit.app Y ≫
    E.functor.map (a.unit.app (E.inverse.obj Y)) at h2
  rw [h2] at h1
  exact h0'.trans (h1.trans (Category.assoc _ _ _))

/-- The actual counit keeps both original carrier counits and the balanced counit. -/
theorem adjunction_counit_app (X Y : D) :
    (adjunction A E X).counit.app Y =
      E.functor.map (((Mod.relativeTensor A).obj (E.inverse.obj X)).map
        (E.symm.toAdjunction.counit.app
          ((Mod.internalHomOfEqualizer A (E.inverse.obj X)).obj (E.inverse.obj Y)))) ≫
        E.functor.map ((Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj X)).counit.app
          (E.inverse.obj Y)) ≫
        E.toAdjunction.counit.app Y := by
  let L := (Mod.relativeTensor A).obj (E.inverse.obj X)
  let R := Mod.internalHomOfEqualizer A (E.inverse.obj X)
  let a : L ⊣ R := Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj X)
  let b : E.inverse ⋙ L ⊣ R ⋙ E.functor := E.symm.toAdjunction.comp a
  let c : E.inverse ⋙ L ⋙ E.functor ⊣ E.inverse ⋙ R ⋙ E.functor :=
    b.comp E.toAdjunction
  let e : E.inverse ⋙ R ⋙ E.functor ≅ functor A E X :=
    (eqToIso (sourceFunctor_obj A E (E.inverse.obj X))).symm
  have h0 := congrArg (fun z => z.app Y) (Adjunction.ofNatIsoRight_counit c e)
  have he (Z : D) : e.inv.app Z = 𝟙 _ := rfl
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, he] at h0
  have hmap := (E.inverse ⋙ L ⋙ E.functor).map_id ((functor A E X).obj Y)
  have h0' : (adjunction A E X).counit.app Y = c.counit.app Y :=
    h0.trans ((congrArg (fun z => z ≫ c.counit.app Y) hmap).trans (Category.id_comp _))
  have h1 := Adjunction.comp_counit_app b E.toAdjunction Y
  have h2 := Adjunction.comp_counit_app E.symm.toAdjunction a (E.inverse.obj Y)
  change c.counit.app Y = E.functor.map (b.counit.app (E.inverse.obj Y)) ≫
    E.toAdjunction.counit.app Y at h1
  change b.counit.app (E.inverse.obj Y) =
    L.map (E.symm.toAdjunction.counit.app (R.obj (E.inverse.obj Y))) ≫
    a.counit.app (E.inverse.obj Y) at h2
  rw [h2, E.functor.map_comp, Category.assoc] at h1
  exact h0'.trans h1

/-- Both original carrier functors transport the entire covariant balanced source. -/
def smashBifunctor : D ⥤ (D ⥤ D) :=
  E.inverse ⋙ Mod.relativeTensor A ⋙
    (Functor.whiskeringLeft D (Mod C A.X) (Mod C A.X)).obj E.inverse ⋙
      (Functor.whiskeringRight D (Mod C A.X) D).obj E.functor

omit [HasEqualizers C] in
/-- The covariant source functor uses the original entire balanced smash value. -/
theorem smashBifunctor_obj (X : D) :
    (smashBifunctor A E).obj X = smashFunctor A E X := rfl

/-- Every original whole source map has its actual covariant balanced smash map. -/
def sourceSmashMap {X Y : D} (f : X ⟶ Y) : smashFunctor A E X ⟶ smashFunctor A E Y :=
  (smashBifunctor A E).map f

omit [HasEqualizers C] in
/-- Every source-smash component keeps its full original module tensor map. -/
theorem sourceSmashMap_app {X Y : D} (f : X ⟶ Y) (Z : D) :
    (sourceSmashMap A E f).app Z =
      E.functor.map (((Mod.relativeTensor A).map (E.inverse.map f)).app (E.inverse.obj Z)) := rfl

/-- The original unit is natural in the full source object and its balanced source map. -/
theorem adjunction_unit_source {X Y : D} (f : X ⟶ Y) (Z : D) :
    (adjunction A E Y).unit.app Z ≫ (precompose A E f).app ((smashFunctor A E Y).obj Z) =
      (adjunction A E X).unit.app Z ≫ (functor A E X).map ((sourceSmashMap A E f).app Z) := by
  let M := E.inverse.obj X
  let M' := E.inverse.obj Y
  let N := E.inverse.obj Z
  let g : M ⟶ M' := E.inverse.map f
  let T := ((Mod.relativeTensor A).obj M).obj N
  let T' := ((Mod.relativeTensor A).obj M').obj N
  let t : T ⟶ T' := ((Mod.relativeTensor A).map g).app N
  let R := Mod.internalHomOfEqualizer A M
  let R' := Mod.internalHomOfEqualizer A M'
  let eta : N ⟶ R.obj T := (Mod.relativeTensorInternalHomAdjunction A M).unit.app N
  let etaPrime : N ⟶ R'.obj T' := (Mod.relativeTensorInternalHomAdjunction A M').unit.app N
  let θ : T ⟶ E.inverse.obj (E.functor.obj T) := E.toAdjunction.unit.app T
  let θ' : T' ⟶ E.inverse.obj (E.functor.obj T') := E.toAdjunction.unit.app T'
  let P : R' ⟶ R := MonoidalClosed.pre g
  let u : Z ⟶ E.functor.obj N := E.symm.toAdjunction.unit.app Z
  have hp := P.naturality θ'
  have heta : etaPrime ≫ P.app T' = eta ≫ R.map t :=
    MonoidalClosed.coev_app_comp_pre_app (X := N) g
  have hθ : t ≫ θ' = θ ≫ E.inverse.map (E.functor.map t) := by
    simpa only [Functor.id_map, Functor.comp_map] using E.toAdjunction.unit.naturality t
  have h : etaPrime ≫ R'.map θ' ≫ (MonoidalClosed.pre g).app (E.inverse.obj (E.functor.obj T')) =
      eta ≫ R.map θ ≫ R.map (E.inverse.map (E.functor.map t)) := by
    change etaPrime ≫ R'.map θ' ≫ P.app (E.inverse.obj (E.functor.obj T')) = _
    rw [hp, ← Category.assoc, heta, Category.assoc]
    rw [← R.map_comp, hθ, R.map_comp]
  rw [adjunction_unit_app, adjunction_unit_app,
    precompose_app, functor_map, sourceSmashMap_app]
  change (u ≫ E.functor.map etaPrime ≫ E.functor.map (R'.map θ')) ≫
      E.functor.map (P.app (E.inverse.obj (E.functor.obj T'))) =
    (u ≫ E.functor.map eta ≫ E.functor.map (R.map θ)) ≫
      E.functor.map (R.map (E.inverse.map (E.functor.map t)))
  have h' : etaPrime ≫ R'.map θ' ≫ P.app (E.inverse.obj (E.functor.obj T')) =
      eta ≫ R.map θ ≫ R.map (E.inverse.map (E.functor.map t)) := h
  have hL : E.functor.map (etaPrime ≫ R'.map θ' ≫ P.app (E.inverse.obj (E.functor.obj T'))) =
      E.functor.map etaPrime ≫ E.functor.map (R'.map θ') ≫
        E.functor.map (P.app (E.inverse.obj (E.functor.obj T'))) :=
    (E.functor.map_comp etaPrime (R'.map θ' ≫ P.app (E.inverse.obj (E.functor.obj T')))).trans
      (congrArg (fun z => E.functor.map etaPrime ≫ z)
        (E.functor.map_comp (R'.map θ') (P.app (E.inverse.obj (E.functor.obj T')))))
  have hR : E.functor.map (eta ≫ R.map θ ≫ R.map (E.inverse.map (E.functor.map t))) =
      E.functor.map eta ≫ E.functor.map (R.map θ) ≫
        E.functor.map (R.map (E.inverse.map (E.functor.map t))) :=
    (E.functor.map_comp eta (R.map θ ≫ R.map (E.inverse.map (E.functor.map t)))).trans
      (congrArg (fun z => E.functor.map eta ≫ z)
        (E.functor.map_comp (R.map θ) (R.map (E.inverse.map (E.functor.map t)))))
  have hFinal := (congrArg (fun z => u ≫ z) hL.symm).trans
    ((congrArg (fun z => u ≫ E.functor.map z) h').trans (congrArg (fun z => u ≫ z) hR))
  simpa only [Category.assoc] using hFinal

/-- The original counit is natural in the full source object and its original pre-map. -/
theorem adjunction_counit_source {X Y : D} (f : X ⟶ Y) (Z : D) :
    (sourceSmashMap A E f).app ((functor A E Y).obj Z) ≫ (adjunction A E Y).counit.app Z =
      (smashFunctor A E X).map ((precompose A E f).app Z) ≫ (adjunction A E X).counit.app Z := by
  let M := E.inverse.obj X
  let M' := E.inverse.obj Y
  let N := E.inverse.obj Z
  let g : M ⟶ M' := E.inverse.map f
  let R := Mod.internalHomOfEqualizer A M
  let R' := Mod.internalHomOfEqualizer A M'
  let H := R'.obj N
  let K := R.obj N
  let p : H ⟶ K := (MonoidalClosed.pre g).app N
  let ε : E.inverse.obj (E.functor.obj K) ⟶ K := E.symm.toAdjunction.counit.app K
  let ε' : E.inverse.obj (E.functor.obj H) ⟶ H :=
    E.symm.toAdjunction.counit.app H
  let ev : M ⊗ K ⟶ N := (Mod.relativeTensorInternalHomAdjunction A M).counit.app N
  let ev' : M' ⊗ H ⟶ N := (Mod.relativeTensorInternalHomAdjunction A M').counit.app N
  let v : E.functor.obj N ⟶ Z := E.toAdjunction.counit.app Z
  have hε : E.inverse.map (E.functor.map p) ≫ ε = ε' ≫ p := by
    simpa only [Functor.id_map, Functor.comp_map,
      Equivalence.symm_functor, Equivalence.symm_inverse] using
      E.symm.toAdjunction.counit.naturality p
  have hex : (g ▷ E.inverse.obj (E.functor.obj H)) ≫ (M' ◁ ε') =
      (M ◁ ε') ≫ (g ▷ H) := (whisker_exchange g ε').symm
  have hev : (M ◁ p) ≫ ev = (g ▷ H) ≫ ev' :=
    MonoidalClosed.id_tensor_pre_app_comp_ev g N
  have h : (g ▷ E.inverse.obj (E.functor.obj H)) ≫ (M' ◁ ε') ≫ ev' =
      (M ◁ E.inverse.map (E.functor.map p)) ≫ (M ◁ ε) ≫ ev := by
    rw [← Category.assoc, hex, Category.assoc, ← hev]
    rw [← whiskerLeft_comp_assoc, ← hε, whiskerLeft_comp, Category.assoc]
  rw [sourceSmashMap_app, adjunction_counit_app,
    smashFunctor_map, precompose_app, adjunction_counit_app]
  change E.functor.map (g ▷ E.inverse.obj (E.functor.obj H)) ≫
      E.functor.map (M' ◁ ε') ≫ E.functor.map ev' ≫ v =
    E.functor.map (M ◁ E.inverse.map (E.functor.map p)) ≫
      E.functor.map (M ◁ ε) ≫ E.functor.map ev ≫ v
  simpa only [E.functor.map_comp, Category.assoc] using
    congrArg (fun z => E.functor.map z ≫ v) h


/-- The actual transported balanced adjunction is natural in its source parameter. -/
def parametrizedAdjunction : smashBifunctor A E ⊣₂ bifunctor A E :=
  ParametrizedAdjunction.mk' (fun X => adjunction A E X) (by
    intro X Y f Z W g
    let g' : (smashFunctor A E Y).obj Z ⟶ W := g
    change (adjunction A E X).homEquiv Z W ((sourceSmashMap A E f).app Z ≫ g') =
      (adjunction A E Y).homEquiv Z W g' ≫ (precompose A E f).app W
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, (functor A E X).map_comp]
    rw [← Category.assoc, ← adjunction_unit_source A E f Z]
    simpa only [Category.assoc] using
      congrArg (fun q => (adjunction A E Y).unit.app Z ≫ q)
        ((precompose A E f).naturality g').symm)

/-- Each fixed component is the original three-factor transported adjunction. -/
theorem parametrizedAdjunction_adj (X : D) :
    (parametrizedAdjunction A E).adj X = adjunction A E X := rfl

end CategoryTheory.Mod.EquivalenceFunctionTransport

/- The nine original names are still used by the pending native consumers of
PR9556, PR9571, PR9588 and the R checkpoint. These exports resolve to the
canonical declarations above and introduce no additional proof family. -/
namespace NativeOmegaPreparation.ModuleFunctionTransport

export CategoryTheory.Mod.EquivalenceFunctionTransport
  (sourceFunctor sourceFunctor_obj sourceAdjunction bifunctor functor smashFunctor
    adjunction precompose sourceComparison)

end NativeOmegaPreparation.ModuleFunctionTransport
