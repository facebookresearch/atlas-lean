/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monad.MonoidalBar
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Monad.Monadicity
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# Limits, colimits, and free internal modules

This file identifies Mathlib's existing category `Mod C A` of internal left
modules with the Eilenberg--Moore category for the monad `A ⊗ -`.  It uses
that comparison to create limits, preservation-conditional colimits, and
reflexive coequalizers, and constructs the free-forgetful adjunction.  It also
transfers local presentability from the ambient category.

The reflexive coequalizer result is deliberately separate from arbitrary
colimit creation: the latter still requires preservation of the relevant
shape by `tensorLeft A`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe w v u

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable (A : C) [MonObj A]

/-- The tensor-monad algebra determined by an internal `A`-module. -/
@[reducible] def toTensorMonadAlgebra :
    Mod C A ⥤ (Monad.tensorMonad A).Algebra where
  obj M :=
    { A := M.X
      a := by
        change A ⊗ M.X ⟶ M.X
        exact ModObj.smul (M := A) (X := M.X)
      unit := by
        change ((λ_ M.X).inv ≫ (η[A] ▷ M.X)) ≫
          ModObj.smul (M := A) (X := M.X) = 𝟙 M.X
        rw [Category.assoc, ModObj.one_smul_self, Iso.inv_hom_id]
      assoc := by
        change ((α_ A A M.X).inv ≫ (μ[A] ▷ M.X)) ≫
          ModObj.smul (M := A) (X := M.X) =
          (A ◁ ModObj.smul (M := A) (X := M.X)) ≫
            ModObj.smul (M := A) (X := M.X)
        rw [Category.assoc]
        exact (ModObj.mul_smul_self_flip (M := A) M.X).symm }
  map f :=
    { f := f.hom
      h := by
        change (A ◁ f.hom) ≫ ModObj.smul (M := A) (X := _) =
          ModObj.smul (M := A) (X := _) ≫ f.hom
        exact (IsModHom.smul_hom (A := A) (f := f.hom)).symm }

/-- The internal `A`-module determined by a tensor-monad algebra. -/
@[reducible] def ofTensorMonadAlgebra :
    (Monad.tensorMonad A).Algebra ⥤ Mod C A := by
  let modObj (X : (Monad.tensorMonad A).Algebra) : ModObj A X.A := by
    let a : A ⊗ X.A ⟶ X.A := by
      change (Monad.tensorMonad A).obj X.A ⟶ X.A
      exact X.a
    have hUnit : ((λ_ X.A).inv ≫ (η[A] ▷ X.A)) ≫ a = 𝟙 X.A := by
      have h := X.unit
      change ((λ_ X.A).inv ≫ (η[A] ▷ X.A)) ≫ a = 𝟙 X.A at h
      exact h
    have hAssoc : ((α_ A A X.A).inv ≫ (μ[A] ▷ X.A)) ≫ a =
        (A ◁ a) ≫ a := by
      have h := X.assoc
      change ((α_ A A X.A).inv ≫ (μ[A] ▷ X.A)) ≫ a =
        (A ◁ a) ≫ a at h
      exact h
    exact
      { smul := a
        one_smul := by
          rw [← cancel_epi (λ_ X.A).inv]
          calc
            (λ_ X.A).inv ≫ (η[A] ▷ X.A) ≫ a =
                ((λ_ X.A).inv ≫ (η[A] ▷ X.A)) ≫ a := by
                  rw [Category.assoc]
            _ = 𝟙 X.A := hUnit
            _ = (λ_ X.A).inv ≫ (λ_ X.A).hom := by simp
        mul_smul := by
          rw [← cancel_epi (α_ A A X.A).inv]
          calc
            (α_ A A X.A).inv ≫ (μ[A] ▷ X.A) ≫ a =
                ((α_ A A X.A).inv ≫ (μ[A] ▷ X.A)) ≫ a := by
                  rw [Category.assoc]
            _ = (A ◁ a) ≫ a := hAssoc
            _ = (α_ A A X.A).inv ≫
                (α_ A A X.A).hom ≫ (A ◁ a) ≫ a := by simp }
  exact
    { obj := fun X ↦ { X := X.A, mod := modObj X }
      map := fun {X Y} f ↦ by
        letI : ModObj A X.A := modObj X
        letI : ModObj A Y.A := modObj Y
        exact Mod.Hom.mk' f.f f.h.symm }

/-- The equivalence between internal `A`-modules and algebras over `A ⊗ -`. -/
@[reducible] def tensorMonadEquivalence :
    Mod C A ≌ (Monad.tensorMonad A).Algebra where
  functor := toTensorMonadAlgebra A
  inverse := ofTensorMonadAlgebra A
  unitIso :=
    NatIso.ofComponents (fun M ↦
      { hom := Mod.Hom.mk' (𝟙 M.X) (by
          change ModObj.smul (M := A) (X := M.X) ≫ 𝟙 M.X =
            (A ◁ 𝟙 M.X) ≫ ModObj.smul (M := A) (X := M.X)
          rw [MonoidalCategory.whiskerLeft_id, Category.id_comp,
            Category.comp_id])
        inv := Mod.Hom.mk' (𝟙 M.X) (by
          change ModObj.smul (M := A) (X := M.X) ≫ 𝟙 M.X =
            (A ◁ 𝟙 M.X) ≫ ModObj.smul (M := A) (X := M.X)
          rw [MonoidalCategory.whiskerLeft_id, Category.id_comp,
            Category.comp_id])
        hom_inv_id := by
          apply Mod.hom_ext
          change (𝟙 M.X) ≫ 𝟙 M.X = 𝟙 M.X
          simp
        inv_hom_id := by
          apply Mod.hom_ext
          change (𝟙 M.X) ≫ 𝟙 M.X = 𝟙 M.X
          simp }) (fun f ↦ by
            apply Mod.hom_ext
            change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
            simp)
  counitIso :=
    NatIso.ofComponents (fun X ↦
      Monad.Algebra.isoMk (Iso.refl X.A) (by
        dsimp [ofTensorMonadAlgebra, toTensorMonadAlgebra]
        change (Monad.tensorMonad A).map (𝟙 X.A) ≫ X.a =
          X.a ≫ 𝟙 X.A
        rw [Functor.map_id, Category.id_comp, Category.comp_id])) (fun f ↦ by
          apply Monad.Algebra.Hom.ext
          change f.f ≫ 𝟙 _ = 𝟙 _ ≫ f.f
          simp)
  functor_unitIso_comp X := by
    apply Monad.Algebra.Hom.ext
    change (𝟙 X.X) ≫ 𝟙 X.X = 𝟙 X.X
    simp

/-- The forgetful functor from internal `A`-modules creates all limits. -/
@[instance_reducible]
noncomputable def forgetCreatesLimits :
    CreatesLimitsOfSize.{w, w} (Mod.forget (D := C) A) := by
  let E := tensorMonadEquivalence A
  let forgetIso : E.functor ⋙ (Monad.tensorMonad A).forget ≅ Mod.forget A :=
    NatIso.ofComponents (fun M ↦ Iso.refl M.X) (fun f ↦ by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : CreatesLimitsOfSize.{w, w} E.functor :=
    Functor.createsLimitsOfIsEquivalence E.functor
  letI : CreatesLimitsOfSize.{w, w} (Monad.tensorMonad A).forget :=
    Monad.forgetCreatesLimits
  letI : CreatesLimitsOfSize.{w, w}
      (E.functor ⋙ (Monad.tensorMonad A).forget) :=
    compCreatesLimits E.functor (Monad.tensorMonad A).forget
  exact createsLimitsOfNatIso forgetIso

/-- Internal `A`-modules have all limits that the ambient category has. -/
theorem hasLimits [HasLimitsOfSize.{w, w} C] :
    HasLimitsOfSize.{w, w} (Mod C A) := by
  let _ := forgetCreatesLimits.{w} A
  exact hasLimits_of_hasLimits_createsLimits (Mod.forget A)

/-- The module forgetful functor creates the coequalizer of each reflexive
parallel pair when `A ⊗ -` preserves reflexive coequalizers.  This does not
assert creation of nonreflexive or arbitrary colimits. -/
@[instance_reducible]
noncomputable def forgetCreatesReflexiveCoequalizers
    [Monad.PreservesColimitOfIsReflexivePair (tensorLeft A)]
    {M N : Mod C A} (f g : M ⟶ N) [IsReflexivePair f g] :
    CreatesColimit (parallelPair f g) (Mod.forget A) := by
  let E := tensorMonadEquivalence A
  let T := Monad.tensorMonad A
  let D := parallelPair f g ⋙ E.functor
  let U := D ⋙ T.forget
  let s := commonSection f g
  let sU : U.obj WalkingParallelPair.one ⟶ U.obj WalkingParallelPair.zero :=
    (E.functor.map s).f
  have hsUl : sU ≫ U.map WalkingParallelPairHom.left =
      𝟙 (U.obj WalkingParallelPair.one) := by
    change (E.functor.map s).f ≫ (E.functor.map f).f = 𝟙 _
    rw [← Monad.Algebra.comp_f, ← E.functor.map_comp,
      section_comp_left, E.functor.map_id, Monad.Algebra.id_f]
  have hsUr : sU ≫ U.map WalkingParallelPairHom.right =
      𝟙 (U.obj WalkingParallelPair.one) := by
    change (E.functor.map s).f ≫ (E.functor.map g).f = 𝟙 _
    rw [← Monad.Algebra.comp_f, ← E.functor.map_comp,
      section_comp_right, E.functor.map_id, Monad.Algebra.id_f]
  letI : IsReflexivePair (U.map WalkingParallelPairHom.left)
      (U.map WalkingParallelPairHom.right) :=
    IsReflexivePair.mk' sU hsUl hsUr
  let V := U ⋙ (T : C ⥤ C)
  let sV : V.obj WalkingParallelPair.one ⟶ V.obj WalkingParallelPair.zero :=
    T.map sU
  have hsVl : sV ≫ V.map WalkingParallelPairHom.left =
      𝟙 (V.obj WalkingParallelPair.one) := by
    change T.map sU ≫ T.map (U.map WalkingParallelPairHom.left) = 𝟙 _
    rw [← T.map_comp, hsUl, T.map_id]
  have hsVr : sV ≫ V.map WalkingParallelPairHom.right =
      𝟙 (V.obj WalkingParallelPair.one) := by
    change T.map sU ≫ T.map (U.map WalkingParallelPairHom.right) = 𝟙 _
    rw [← T.map_comp, hsUr, T.map_id]
  letI : IsReflexivePair (V.map WalkingParallelPairHom.left)
      (V.map WalkingParallelPairHom.right) :=
    IsReflexivePair.mk' sV hsVl hsVr
  letI : Monad.PreservesColimitOfIsReflexivePair (T : C ⥤ C) := by
    dsimp only [T, Monad.tensorMonad]
    infer_instance
  letI : PreservesColimit
      (parallelPair (U.map WalkingParallelPairHom.left)
        (U.map WalkingParallelPairHom.right)) (T : C ⥤ C) :=
    Monad.PreservesColimitOfIsReflexivePair.out _ _
  letI : PreservesColimit U (T : C ⥤ C) :=
    preservesColimit_of_iso_diagram (T : C ⥤ C)
      (diagramIsoParallelPair U).symm
  letI : PreservesColimit
      (parallelPair (V.map WalkingParallelPairHom.left)
        (V.map WalkingParallelPairHom.right)) (T : C ⥤ C) :=
    Monad.PreservesColimitOfIsReflexivePair.out _ _
  letI : PreservesColimit V (T : C ⥤ C) :=
    preservesColimit_of_iso_diagram (T : C ⥤ C)
      (diagramIsoParallelPair V).symm
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : CreatesColimitsOfSize.{0, 0} E.functor :=
    Functor.createsColimitsOfIsEquivalence E.functor
  letI : CreatesColimit D T.forget := Monad.forgetCreatesColimit D
  letI : CreatesColimit (parallelPair f g) (E.functor ⋙ T.forget) :=
    compCreatesColimit E.functor T.forget
  let forgetIso : E.functor ⋙ T.forget ≅ Mod.forget A :=
    NatIso.ofComponents (fun X ↦ Iso.refl X.X) (fun h ↦ by
      change h.hom ≫ 𝟙 _ = 𝟙 _ ≫ h.hom
      simp)
  exact createsColimitOfNatIso forgetIso

/-- If tensoring on the left by `A` preserves colimits, then the module
forgetful functor creates them. -/
@[instance_reducible]
noncomputable def forgetCreatesColimits
    [PreservesColimitsOfSize.{w, w} (tensorLeft A)] :
    CreatesColimitsOfSize.{w, w} (Mod.forget (D := C) A) := by
  let E := tensorMonadEquivalence A
  let forgetIso : E.functor ⋙ (Monad.tensorMonad A).forget ≅ Mod.forget A :=
    NatIso.ofComponents (fun M ↦ Iso.refl M.X) (fun f ↦ by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : CreatesColimitsOfSize.{w, w} E.functor :=
    Functor.createsColimitsOfIsEquivalence E.functor
  letI : PreservesColimitsOfSize.{w, w}
      ((Monad.tensorMonad A : Monad C) : C ⥤ C) := by
    dsimp only [Monad.tensorMonad]
    infer_instance
  letI : CreatesColimitsOfSize.{w, w} (Monad.tensorMonad A).forget :=
    Monad.forgetCreatesColimits
  letI : CreatesColimitsOfSize.{w, w}
      (E.functor ⋙ (Monad.tensorMonad A).forget) :=
    compCreatesColimits E.functor (Monad.tensorMonad A).forget
  exact createsColimitsOfNatIso forgetIso

/-- Internal `A`-modules have all colimits preserved by `A ⊗ -`. -/
theorem hasColimits [HasColimitsOfSize.{w, w} C]
    [PreservesColimitsOfSize.{w, w} (tensorLeft A)] :
    HasColimitsOfSize.{w, w} (Mod C A) := by
  let _ := forgetCreatesColimits.{w} A
  exact hasColimits_of_hasColimits_createsColimits (Mod.forget A)

/-- The free internal `A`-module functor. -/
@[reducible] noncomputable def free : C ⥤ Mod C A :=
  (Monad.tensorMonad A).free ⋙ (tensorMonadEquivalence A).inverse

/-- The underlying object of the free module on `X` is `A ⊗ X`. -/
theorem free_obj (X : C) : ((free A).obj X).X = A ⊗ X := rfl

/-- The underlying map of the free module map is tensoring by `A`, with the
carrier transports displayed explicitly. -/
theorem free_map {X Y : C} (f : X ⟶ Y) :
    eqToHom (free_obj A X) ≫ (A ◁ f) =
      ((free A).map f).hom ≫ eqToHom (free_obj A Y) := by
  change (𝟙 (A ⊗ X)) ≫ (A ◁ f) = (A ◁ f) ≫ 𝟙 (A ⊗ Y)
  simp

/-- Free internal `A`-modules are left adjoint to the forgetful functor. -/
@[reducible] noncomputable def freeForgetAdjunction :
    free A ⊣ Mod.forget A := by
  let E := tensorMonadEquivalence A
  let forgetIso : E.functor ⋙ (Monad.tensorMonad A).forget ≅ Mod.forget A :=
    NatIso.ofComponents (fun M ↦ Iso.refl M.X) (fun f ↦ by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  exact ((Monad.adj (Monad.tensorMonad A)).comp E.symm.toAdjunction).ofNatIsoRight
    forgetIso

private def freeHomEquiv (X : C) (M : Mod C A) :
    (X ⟶ M.X) ≃ ((free A).obj X ⟶ M) :=
  (freeForgetAdjunction A).homEquiv X M |>.symm

/-- The unit of the free-forgetful adjunction is the monoid unit followed by
the displayed free-module carrier identification. -/
theorem freeForgetAdjunction_unit_app (X : C) :
    (freeForgetAdjunction A).unit.app X =
      (λ_ X).inv ≫ (η[A] ▷ X) ≫ eqToHom (free_obj A X).symm := by
  let E := tensorMonadEquivalence A
  let T := Monad.tensorMonad A
  let forgetIso : E.functor ⋙ T.forget ≅ Mod.forget A :=
    NatIso.ofComponents (fun M ↦ Iso.refl M.X) (fun f ↦ by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  have hE : (E.counitInv.app (T.free.obj X)).f =
      𝟙 (T.free.obj X).A := rfl
  have hForget : forgetIso.hom.app (E.inverse.obj (T.free.obj X)) =
      𝟙 (E.inverse.obj (T.free.obj X)).X := rfl
  change ((((Monad.adj T).comp E.symm.toAdjunction).ofNatIsoRight
    forgetIso).unit.app X) = _
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.ofNatIsoRight_unit,
    Equivalence.symm_inverse, Equivalence.symm_functor, NatTrans.comp_app,
    Adjunction.comp_unit_app, Monad.adj_unit,
    Equivalence.toAdjunction_unit, Equivalence.symm_unit,
    Functor.whiskerLeft_app, Monad.forget_map]
  rw [hE, hForget]
  have hLeft :
      ((T.η.app X ≫ 𝟙 (T.free.obj X).A) ≫
          𝟙 (E.inverse.obj (T.free.obj X)).X) ≍ T.η.app X := by
    exact (heq_of_eq (Category.comp_id _)).trans
      (heq_of_eq (Category.comp_id _))
  have hEta : T.η.app X = (λ_ X).inv ≫ (η[A] ▷ X) := by
    dsimp only [T]
    exact Monad.tensorMonad_eta_app A X
  apply eq_of_heq
  exact (hLeft.trans (heq_of_eq hEta)).trans
    ((comp_eqToHom_heq
      ((λ_ X).inv ≫ (η[A] ▷ X)) (free_obj A X).symm).symm.trans
        (heq_of_eq (Category.assoc (λ_ X).inv (η[A] ▷ X)
          (eqToHom (free_obj A X).symm))))

/-- The underlying map of the free-forgetful counit is the module action. -/
theorem freeForgetAdjunction_counit_app_hom (M : Mod C A) :
    ((freeForgetAdjunction A).counit.app M).hom =
      eqToHom (free_obj A M.X) ≫
        ModObj.smul (M := A) (X := M.X) := by
  let E := tensorMonadEquivalence A
  let T := Monad.tensorMonad A
  let forgetIso : E.functor ⋙ T.forget ≅ Mod.forget A :=
    NatIso.ofComponents (fun M ↦ Iso.refl M.X) (fun f ↦ by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  have hForget : forgetIso.inv.app M = 𝟙 M.X := rfl
  have hFreeMap :
      (E.inverse.map (T.free.map (forgetIso.inv.app M))).hom =
        T.map (forgetIso.inv.app M) := rfl
  have hCounit :
      (E.inverse.map ((Monad.adj T).counit.app (E.functor.obj M))).hom =
        ((toTensorMonadAlgebra A).obj M).a := by
    change
      ((ofTensorMonadAlgebra A).map
        ((Monad.adj (Monad.tensorMonad A)).counit.app
          ((toTensorMonadAlgebra A).obj M))).hom =
        ((toTensorMonadAlgebra A).obj M).a
    rw [Monad.adj_counit]
    rfl
  have hUnitInv : (E.unitInv.app M).hom = 𝟙 M.X := rfl
  have hSmul : ((toTensorMonadAlgebra A).obj M).a =
      ModObj.smul (M := A) (X := M.X) := rfl
  change (((((Monad.adj T).comp E.symm.toAdjunction).ofNatIsoRight
    forgetIso).counit.app M).hom) = _
  simp only [Functor.comp_obj, Functor.id_obj,
    Adjunction.ofNatIsoRight_counit, Equivalence.symm_inverse,
    Equivalence.symm_functor, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_map, Adjunction.comp_counit_app,
    Equivalence.toAdjunction_counit, Equivalence.symm_counit,
    Mod.comp_hom']
  rw [hFreeMap, hCounit, hUnitInv, hForget]
  have hAction : T.map (𝟙 M.X) ≫ ((toTensorMonadAlgebra A).obj M).a =
      ((toTensorMonadAlgebra A).obj M).a := by simp
  have hLeft :
      T.map (𝟙 M.X) ≫ ((toTensorMonadAlgebra A).obj M).a ≫ 𝟙 M.X ≍
        ((toTensorMonadAlgebra A).obj M).a := by
    rw [Category.comp_id]
    exact heq_of_eq hAction
  apply eq_of_heq
  exact (hLeft.trans (heq_of_eq hSmul)).trans
    (eqToHom_comp_heq (ModObj.smul (M := A) (X := M.X))
      (free_obj A M.X)).symm

/-- The module morphism adjunct to an underlying map `g` is tensoring `g`
on the left by `A`, followed by the target module action. -/
theorem freeForgetAdjunction_homEquiv_symm_apply_hom {X : C}
    (M : Mod C A) (g : X ⟶ M.X) :
    (((freeForgetAdjunction A).homEquiv X M).symm g).hom =
      eqToHom (free_obj A X) ≫ (A ◁ g) ≫
        ModObj.smul (M := A) (X := M.X) := by
  have hAdj := Adjunction.homEquiv_counit
    (freeForgetAdjunction A) X M g
  have hHom := congrArg
    (fun q : (free A).obj X ⟶ M ↦ q.hom) hAdj
  have hHom' :
      (((freeForgetAdjunction A).homEquiv X M).symm g).hom ≍
        ((free A).map g).hom ≫
          ((freeForgetAdjunction A).counit.app M).hom :=
    (heq_of_eq hHom).trans (by rfl)
  have hFormula :
        ((free A).map g).hom ≫
          ((freeForgetAdjunction A).counit.app M).hom =
      eqToHom (free_obj A X) ≫ (A ◁ g) ≫
        ModObj.smul (M := A) (X := M.X) := by
    rw [freeForgetAdjunction_counit_app_hom,
      ← Category.assoc, ← free_map, Category.assoc]
  exact eq_of_heq (hHom'.trans (heq_of_eq hFormula))

/-- The underlying map corresponding to a free-module morphism is obtained
by precomposing with the displayed unit of the free-forgetful adjunction. -/
theorem freeForgetAdjunction_homEquiv_apply {X : C} (M : Mod C A)
    (k : (free A).obj X ⟶ M) :
    (freeForgetAdjunction A).homEquiv X M k =
      (λ_ X).inv ≫ (η[A] ▷ X) ≫
        eqToHom (free_obj A X).symm ≫ k.hom := by
  have hAdj := Adjunction.homEquiv_unit
    (freeForgetAdjunction A) X M k
  have hForget : (Mod.forget A).map k = k.hom := rfl
  have hAdj' :
      (freeForgetAdjunction A).homEquiv X M k =
        (freeForgetAdjunction A).unit.app X ≫ k.hom :=
    hAdj.trans (congrArg
      (fun z ↦ (freeForgetAdjunction A).unit.app X ≫ z) hForget)
  have hUnitComp := congrArg (fun z ↦ z ≫ k.hom)
    (freeForgetAdjunction_unit_app A X)
  have hAssoc :
      ((λ_ X).inv ≫ (η[A] ▷ X) ≫
          eqToHom (free_obj A X).symm) ≫ k.hom =
        (λ_ X).inv ≫ (η[A] ▷ X) ≫
          eqToHom (free_obj A X).symm ≫ k.hom := by
    simp only [Category.assoc]
  exact hAdj'.trans (hUnitComp.trans hAssoc)


private theorem forgetReflectsIsomorphisms :
    (Mod.forget (D := C) A).ReflectsIsomorphisms := by
  constructor
  intro M N f hf
  let _ : IsIso f.hom := hf
  let fInv : N ⟶ M := Mod.Hom.mk' (inv f.hom) (by
    change ModObj.smul (M := A) (X := N.X) ≫ inv f.hom =
      (A ◁ inv f.hom) ≫ ModObj.smul (M := A) (X := M.X)
    rw [← cancel_mono f.hom]
    simp [Category.assoc])
  exact ⟨⟨fInv, by
    apply Mod.hom_ext
    change f.hom ≫ inv f.hom = 𝟙 M.X
    simp, by
    apply Mod.hom_ext
    change inv f.hom ≫ f.hom = 𝟙 N.X
    simp⟩⟩

private theorem forgetIsCardinalAccessible (κ : Cardinal.{w})
    [Fact κ.IsRegular] [HasCardinalFilteredColimits.{w} C κ]
    [(tensorLeft A).IsCardinalAccessible κ] :
    (Mod.forget (D := C) A).IsCardinalAccessible κ := by
  constructor
  intro J _ _
  let _ : HasColimitsOfShape J C :=
    HasCardinalFilteredColimits.hasColimitsOfShape C κ J
  let _ : PreservesColimitsOfShape J (tensorLeft A) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (tensorLeft A) κ J
  let E := tensorMonadEquivalence A
  let forgetIso : E.functor ⋙ (Monad.tensorMonad A).forget ≅
      Mod.forget (D := C) A :=
    NatIso.ofComponents (fun M ↦ Iso.refl M.X) (fun f ↦ by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  let _ : E.functor.IsEquivalence := E.isEquivalence_functor
  let _ : CreatesColimitsOfSize.{w, w} E.functor :=
    Functor.createsColimitsOfIsEquivalence E.functor
  let _ : PreservesColimitsOfShape J
      ((Monad.tensorMonad A : Monad C) : C ⥤ C) := by
    dsimp only [Monad.tensorMonad]
    infer_instance
  let _ : CreatesColimitsOfShape J (Monad.tensorMonad A).forget :=
    Monad.forgetCreatesColimitsOfShape
  let _ : CreatesColimitsOfShape J
      (E.functor ⋙ (Monad.tensorMonad A).forget) :=
    compCreatesColimitsOfShape E.functor (Monad.tensorMonad A).forget
  let _ : CreatesColimitsOfShape J (Mod.forget (D := C) A) :=
    createsColimitsOfShapeOfNatIso forgetIso
  let _ : HasColimitsOfShape J (Mod C A) :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
      (Mod.forget A)
  exact preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape
    (Mod.forget A)

private theorem freeStrongGenerator (P : ObjectProperty C)
    (hP : P.IsStrongGenerator) :
    (P.strictMap (free A)).IsStrongGenerator := by
  let faithfulForget : (Mod.forget (D := C) A).Faithful :=
    ⟨fun h ↦ Mod.hom_ext _ _ h⟩
  let _ := faithfulForget
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨hP.isSeparating.strictMap_leftAdjoint
    (freeForgetAdjunction A), ?_⟩
  intro M N i hi hsurj
  let _ : Mono i.hom :=
    { right_cancellation := by
        intro Z a b hab
        let a' : Z ⟶ (Mod.forget A).obj M := a
        let b' : Z ⟶ (Mod.forget A).obj M := b
        have hab' : a' ≫ (Mod.forget A).map i =
            b' ≫ (Mod.forget A).map i := hab
        have ha := (freeForgetAdjunction A).homEquiv_naturality_right_symm
          a' i
        have hb := (freeForgetAdjunction A).homEquiv_naturality_right_symm
          b' i
        have hModule :
            ((freeForgetAdjunction A).homEquiv Z M).symm a' ≫ i =
            ((freeForgetAdjunction A).homEquiv Z M).symm b' ≫ i := by
          calc
            _ = ((freeForgetAdjunction A).homEquiv Z N).symm
                (a' ≫ (Mod.forget A).map i) := ha.symm
            _ = ((freeForgetAdjunction A).homEquiv Z N).symm
                (b' ≫ (Mod.forget A).map i) := congrArg _ hab'
            _ = _ := hb
        have hFree := (cancel_mono i).1 hModule
        have hab'' : a' = b' :=
          ((freeForgetAdjunction A).homEquiv Z M).symm.injective hFree
        exact hab'' }
  let _ : IsIso i.hom := hP.isIso_of_mono i.hom (fun G hG g ↦ by
    let g' : G ⟶ (Mod.forget A).obj N := g
    obtain ⟨h, hh⟩ := hsurj ((free A).obj G)
      (P.strictMap_obj (free A) hG)
      (freeHomEquiv A G N g')
    refine ⟨(freeForgetAdjunction A).homEquiv G M h, ?_⟩
    change (freeForgetAdjunction A).homEquiv G M h ≫
      (Mod.forget A).map i = g'
    have hh' := congrArg (fun q ↦
      (freeForgetAdjunction A).homEquiv G N q) hh
    rw [(freeForgetAdjunction A).homEquiv_naturality_right] at hh'
    change (freeForgetAdjunction A).homEquiv G M h ≫
      (Mod.forget A).map i =
        (freeForgetAdjunction A).homEquiv G N
          ((freeForgetAdjunction A).homEquiv G N |>.symm g') at hh'
    exact hh'.trans
      (Equiv.apply_symm_apply ((freeForgetAdjunction A).homEquiv G N) g'))
  let _ : IsIso ((Mod.forget A).map i) := inferInstanceAs (IsIso i.hom)
  let _ := forgetReflectsIsomorphisms A
  exact isIso_of_reflects_iso i (Mod.forget A)

/-- If the ambient category is locally presentable and `A ⊗ -` preserves
colimits, then the category of internal `A`-modules is locally presentable. -/
theorem isLocallyPresentable [IsLocallyPresentable.{w} C]
    [PreservesColimitsOfSize.{w, w} (tensorLeft A)] :
    IsLocallyPresentable.{w} (Mod C A) := by
  obtain ⟨κ, hκ, hC⟩ := IsLocallyPresentable.exists_cardinal C
  let _ := hκ
  let _ := hC
  have hMod : IsCardinalLocallyPresentable (Mod C A) κ := by
    let faithfulForget : (Mod.forget (D := C) A).Faithful :=
      ⟨fun h ↦ Mod.hom_ext _ _ h⟩
    let _ := faithfulForget
    let _ := forgetIsCardinalAccessible A κ
    let _ : HasColimitsOfSize.{w, w} (Mod C A) := hasColimits A
    let _ : LocallySmall.{w} (Mod C A) :=
      locallySmall_of_faithful.{w} (Mod.forget A)
    obtain ⟨P, hPSmall, hPStrong, hPPresentable⟩ :=
      (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator C κ).1
        (inferInstance : IsCardinalLocallyPresentable C κ)
    let _ := hPSmall
    rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
    refine ⟨P.strictMap (free A), inferInstance,
      freeStrongGenerator A P hPStrong, ?_⟩
    intro Y hY
    rcases hY with ⟨X, hX⟩
    let _ : IsCardinalPresentable X κ := hPPresentable X hX
    exact (freeForgetAdjunction A).isCardinalPresentable_leftAdjoint_obj κ X
  exact ⟨⟨κ, hκ, hMod⟩⟩

end CategoryTheory.Mod
