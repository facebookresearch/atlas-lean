/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/InternalHom.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Bimodule

/-!
# Internal homs of modules over an internal monoid

Let `A` be a monoid object in a closed monoidal category `C` with equalizers. For left
`A`-modules `M` and `N`, the object `Hom_A(M, N)` of `A`-linear maps is the equalizer of the two
maps `[M, N] ⇉ [A ⊗ M, N]` of internal homs given by precomposition with the action on `M` and by
postcomposition with the action on `N`. Tensoring a module on the right with an object of `C`,
`K ↦ M ⊗ K` with `A` acting on `M`, is left adjoint to `Hom_A(M, -)`: module maps `M ⊗ K ⟶ N`
are the maps `K ⟶ Hom_A(M, N)`. No braiding is needed for this.

When `C` is braided and `A` is commutative, `Hom_A(M, N)` is itself a left `A`-module, with
`(a • f) m = f (a • m)`, and module maps act on it by postcomposition. The action is built from the
right action `m ⊗ a ↦ a • m` of the canonical bimodule `Mod.toBimod.obj M`. This is the internal
  hom
`Mod.internalHom M` of left `A`-modules. For symmetric spectra, the modules over the commutative
sphere monoid of symmetric sequences, it is the function spectrum.

## Main definitions

* `Mod.tensorLeft M`: the functor `K ↦ M ⊗ K` from `C` to left `A`-modules.
* `Mod.tensorRight K`: the functor `M ↦ M ⊗ K` on left `A`-modules.
* `Mod.ihom M`: the functor `N ↦ Hom_A(M, N)` from left `A`-modules to `C`, with the inclusion
  `Mod.ihomι M N : Hom_A(M, N) ⟶ [M, N]` and the factorization `Mod.ihomLift`.
* `Mod.ihomAdjunction M : Mod.tensorLeft M ⊣ Mod.ihom M`.
* `Mod.internalHom M`: over a commutative monoid, `Hom_A(M, -)` as a functor of left
  `A`-modules.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory MonObj MonoidalClosed Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

/-- With `A` acting on the left factor, `M ⊗ K` is a left `A`-module. For `M = A` this is the
free module `MathlibExt.SpectraSource.freeModObj A K`. Its action uses the
multiplication of `A`, and the literal carrier is `A ⊗ K`. -/
@[instance_reducible]
def tensorLeftModObj (M : Mod C A) (K : C) : ModObj A (M.X ⊗ K) where
  smul := (α_ A M.X K).inv ≫ γ[A, M.X] ▷ K
  one_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight]
    simp
  mul_smul := by
    simp only [selfLeftAction_actionObj, selfLeftAction_actionHomLeft,
      selfLeftAction_actionHomRight, selfLeftAction_actionAssocIso, Category.assoc,
      whiskerLeft_comp]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, ModObj.mul_smul_self]
    simp only [comp_whiskerRight, associator_inv_naturality_middle_assoc]
    have h : (α_ (A ⊗ A) M.X K).inv ≫ (α_ A A M.X).hom ▷ K =
        (α_ A A (M.X ⊗ K)).hom ≫ A ◁ (α_ A M.X K).inv ≫ (α_ A (A ⊗ M.X) K).inv := by
      monoidal
    simp [reassoc_of% h]

/-- Tensoring a left `A`-module `M` on the right: `K ↦ M ⊗ K`, with `A` acting on `M`. -/
-- An abbreviation so that the underlying objects are tensor products without transports.
abbrev tensorLeft (M : Mod C A) : C ⥤ Mod C A where
  obj K := letI := tensorLeftModObj M K; ⟨M.X ⊗ K⟩
  map {K L} f := by
    letI := tensorLeftModObj M K
    letI := tensorLeftModObj M L
    exact Hom.mk' (M.X ◁ f) (by
      dsimp only [ModObj.smul, tensorLeftModObj]
      simp only [selfLeftAction_actionHomRight, Category.assoc,
        associator_inv_naturality_right_assoc, whisker_exchange])
  map_id K := by ext; simp
  map_comp f g := by ext; simp

/-- The action on `M ⊗ K` is the action on `M`. -/
@[simp]
lemma tensorLeft_smul (M : Mod C A) (K : C) :
    ((tensorLeft M).obj K).mod.smul = (α_ A M.X K).inv ≫ γ[A, M.X] ▷ K := (rfl)

/-- Tensor a module on the right by an object, retaining its action on the left factor. -/
abbrev tensorRight (V : C) : Mod C A ⥤ Mod C A where
  obj M := (Mod.tensorLeft M).obj V
  map {M N} f := Hom.mk' (M := (Mod.tensorLeft M).obj V)
    (N := (Mod.tensorLeft N).obj V) (f.hom ▷ V) (by
    simp only [tensorLeft_smul, selfLeftAction_actionHomRight, Category.assoc]
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight,
      IsModHom.smul_hom, comp_whiskerRight, selfLeftAction_actionHomRight])
  map_id M := by ext; simp
  map_comp f g := by ext; simp

/-- Tensoring a module with the unit object gives back the module: the right unitor
`M ⊗ 𝟙 ≅ M` is `A`-linear. -/
def tensorLeftUnitIso (M : Mod C A) : (tensorLeft M).obj (𝟙_ C) ≅ M where
  hom := Hom.mk' (ρ_ M.X).hom (by simp)
  inv := Hom.mk' (ρ_ M.X).inv (by simp)

-- The body of `tensorLeftUnitIso` is not exposed, so its projections are proved with `by rfl`.
/-- The isomorphism `M ⊗ 𝟙 ≅ M` is the right unitor. -/
@[simp]
lemma tensorLeftUnitIso_hom_hom (M : Mod C A) : (tensorLeftUnitIso M).hom.hom = (ρ_ M.X).hom := by
  rfl

/-- The inverse of the isomorphism `M ⊗ 𝟙 ≅ M` is the inverse right unitor. -/
@[simp]
lemma tensorLeftUnitIso_inv_hom (M : Mod C A) : (tensorLeftUnitIso M).inv.hom = (ρ_ M.X).inv := by
  rfl

section ihom

variable [MonoidalClosed C]

/-- Precomposition with the action of `A` on `M`, as a map `[M, N] ⟶ [A ⊗ M, N]`. -/
private noncomputable def ihomPrecomp (M N : Mod C A) :
    (M.X ⟶[C] N.X) ⟶ ((A ⊗ M.X) ⟶[C] N.X) :=
  (MonoidalClosed.pre γ[A, M.X]).app N.X

/-- Postcomposition with the action of `A` on `N`, as a map `[M, N] ⟶ [A ⊗ M, N]`. -/
private noncomputable def ihomPostcomp (M N : Mod C A) :
    (M.X ⟶[C] N.X) ⟶ ((A ⊗ M.X) ⟶[C] N.X) :=
  curry ((α_ A M.X _).hom ≫ A ◁ (ihom.ev M.X).app N.X ≫ γ[A, N.X])

/-- A map `K ⟶ [M, N]` equalizes precomposition with the action on `M` and postcomposition with
the action on `N` exactly when its uncurried form `M ⊗ K ⟶ N` is `A`-linear. -/
private lemma comp_ihomPrecomp_eq_iff {M N : Mod C A} {K : C} (f : K ⟶ (M.X ⟶[C] N.X)) :
    f ≫ ihomPrecomp M N = f ≫ ihomPostcomp M N ↔
      (α_ A M.X K).inv ≫ γ[A, M.X] ▷ K ≫ uncurry f = A ◁ uncurry f ≫ γ[A, N.X] := by
  conv_lhs => rw [← curry_uncurry f]
  rw [ihomPrecomp, ihomPostcomp, curry_pre_app, ← curry_natural_left,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, whiskerLeft_curry_ihom_ev_app,
    curry_injective.eq_iff, Iso.inv_comp_eq]

variable [HasEqualizers C]

/-- The object `Hom_A(M, -)` of `A`-linear maps out of a left `A`-module `M`. Its value at `N`
is the equalizer of precomposition with the action on `M` and postcomposition with the action
on `N`, as maps `[M, N] ⇉ [A ⊗ M, N]` of internal homs. -/
noncomputable def ihom (M : Mod C A) : Mod C A ⥤ C where
  obj N := equalizer (ihomPrecomp M N) (ihomPostcomp M N)
  map {N N'} g := equalizer.lift (equalizer.ι _ _ ≫ (CategoryTheory.ihom M.X).map g.hom) (by
    rw [comp_ihomPrecomp_eq_iff, uncurry_natural_right, whiskerLeft_comp, Category.assoc,
      reassoc_of% (comp_ihomPrecomp_eq_iff _).1 (equalizer.condition _ _)]
    simp)
  map_id N := by ext; simp
  map_comp f g := by ext; simp

/-- The inclusion `Hom_A(M, N) ⟶ [M, N]` of `A`-linear maps into all maps. -/
noncomputable def ihomι (M N : Mod C A) : (ihom M).obj N ⟶ (M.X ⟶[C] N.X) :=
  equalizer.ι _ _

instance (M N : Mod C A) : Mono (ihomι M N) :=
  equalizer.ι_mono

/-- Maps into `Hom_A(M, N)` are determined by their composites with the inclusion into
`[M, N]`. -/
@[ext]
lemma ihom_hom_ext {M N : Mod C A} {K : C} {f g : K ⟶ (ihom M).obj N}
    (h : f ≫ ihomι M N = g ≫ ihomι M N) : f = g :=
  (cancel_mono _).1 h

/-- Maps into `Hom_A(M, N)` are determined by their uncurried forms `M ⊗ K ⟶ N`. -/
private lemma ihom_hom_ext_uncurry {M N : Mod C A} {K : C} {f g : K ⟶ (ihom M).obj N}
    (h : M.X ◁ f ≫ uncurry (ihomι M N) = M.X ◁ g ≫ uncurry (ihomι M N)) : f = g := by
  ext
  apply uncurry_injective
  simpa only [uncurry_natural_left] using h

/-- The inclusion of `A`-linear maps is natural in the target module. -/
@[reassoc (attr := simp)]
lemma ihom_map_comp_ihomι (M : Mod C A) {N N' : Mod C A} (g : N ⟶ N') :
    (ihom M).map g ≫ ihomι M N' = ihomι M N ≫ (CategoryTheory.ihom M.X).map g.hom :=
  equalizer.lift_ι _ _

/-- A map `K ⟶ [M, N]` whose uncurried form `M ⊗ K ⟶ N` is `A`-linear factors through
`Hom_A(M, N)`. -/
noncomputable def ihomLift {M N : Mod C A} {K : C} (f : K ⟶ (M.X ⟶[C] N.X))
    (hf : (α_ A M.X K).inv ≫ γ[A,M.X] ▷ K ≫ uncurry f = A ◁ uncurry f ≫ γ[A,N.X]) :
    K ⟶ (ihom M).obj N :=
  equalizer.lift f ((comp_ihomPrecomp_eq_iff f).2 hf)

/-- The factorization through `Hom_A(M, N)` recovers the given map. -/
@[reassoc (attr := simp)]
lemma ihomLift_ihomι {M N : Mod C A} {K : C} (f : K ⟶ (M.X ⟶[C] N.X))
    (hf : (α_ A M.X K).inv ≫ γ[A,M.X] ▷ K ≫ uncurry f = A ◁ uncurry f ≫ γ[A,N.X]) :
    ihomLift f hf ≫ ihomι M N = f :=
  equalizer.lift_ι _ _

/-- Evaluation of `A`-linear maps is natural in the target module. -/
private lemma whiskerLeft_ihom_map_comp_uncurry_ihomι (M : Mod C A) {N N' : Mod C A}
    (g : N ⟶ N') :
    M.X ◁ (ihom M).map g ≫ uncurry (ihomι M N') = uncurry (ihomι M N) ≫ g.hom := by
  rw [← uncurry_natural_left, ihom_map_comp_ihomι, uncurry_natural_right]

/-- The uncurried inclusion `M ⊗ Hom_A(M, N) ⟶ N`, evaluation of `A`-linear maps, is
`A`-linear. -/
@[reassoc]
lemma smul_comp_uncurry_ihomι (M N : Mod C A) :
    (α_ A M.X _).inv ≫ γ[A, M.X] ▷ _ ≫ uncurry (ihomι M N) =
      A ◁ uncurry (ihomι M N) ≫ γ[A, N.X] :=
  (comp_ihomPrecomp_eq_iff _).1 (equalizer.condition _ _)

/-- Module maps `M ⊗ K ⟶ N` correspond to maps `K ⟶ Hom_A(M, N)` by currying. -/
noncomputable def ihomHomEquiv (M : Mod C A) (K : C) (N : Mod C A) :
    ((tensorLeft M).obj K ⟶ N) ≃ (K ⟶ (ihom M).obj N) where
  toFun f := ihomLift (curry f.hom) (by
    have hf := f.isModHom.smul_hom
    rw [tensorLeft_smul, selfLeftAction_actionHomRight, Category.assoc] at hf
    rw [uncurry_curry, hf])
  invFun g := Hom.mk' (uncurry (g ≫ ihomι M N)) (by
    simp only [tensorLeft_smul, selfLeftAction_actionHomRight, uncurry_natural_left,
      Category.assoc]
    rw [whiskerLeft_comp_assoc, ← smul_comp_uncurry_ihomι, associator_inv_naturality_right_assoc,
      whisker_exchange_assoc])
  left_inv f := by ext; simp
  right_inv g := by ext; simp

/-- Currying a module map `M ⊗ K ⟶ N` into `Hom_A(M, N)`, followed by the inclusion into
`[M, N]`, is the ordinary currying. -/
@[reassoc (attr := simp)]
lemma ihomHomEquiv_apply_comp_ihomι (M : Mod C A) {K : C} {N : Mod C A}
    (f : (tensorLeft M).obj K ⟶ N) :
    ihomHomEquiv M K N f ≫ ihomι M N = curry f.hom := by
  simp [ihomHomEquiv]

/-- The inverse bijection uncurries a map `K ⟶ Hom_A(M, N)`. -/
@[simp]
lemma ihomHomEquiv_symm_apply_hom (M : Mod C A) {K : C} {N : Mod C A}
    (g : K ⟶ (ihom M).obj N) :
    ((ihomHomEquiv M K N).symm g).hom = uncurry (g ≫ ihomι M N) := (rfl)

/-- The adjunction `M ⊗ - ⊣ Hom_A(M, -)` between `C` and left `A`-modules. -/
noncomputable def ihomAdjunction (M : Mod C A) : tensorLeft M ⊣ ihom M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := ihomHomEquiv M
      homEquiv_naturality_left_symm := by
        intro K K' N f g
        ext
        rw [ihomHomEquiv_symm_apply_hom, comp_hom', ihomHomEquiv_symm_apply_hom, Category.assoc,
          uncurry_natural_left]
        rfl
      homEquiv_naturality_right := by
        intro K N N' f g
        ext
        rw [ihomHomEquiv_apply_comp_ihomι, Category.assoc, ihom_map_comp_ihomι,
          ihomHomEquiv_apply_comp_ihomι_assoc, comp_hom', curry_natural_right] }

/-- The bijection of the adjunction `M ⊗ - ⊣ Hom_A(M, -)` is given by currying. -/
@[simp]
lemma ihomAdjunction_homEquiv (M : Mod C A) :
    (ihomAdjunction M).homEquiv = ihomHomEquiv M :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- The counit of the adjunction `M ⊗ - ⊣ Hom_A(M, -)` evaluates `A`-linear maps. -/
@[simp]
lemma ihomAdjunction_counit_app_hom (M N : Mod C A) :
    ((ihomAdjunction M).counit.app N).hom = uncurry (ihomι M N) := by
  simp only [ihomAdjunction, Adjunction.mkOfHomEquiv_counit_app]
  exact (ihomHomEquiv_symm_apply_hom M (𝟙 _)).trans (by rw [Category.id_comp]; rfl)

end ihom

section commutative

variable [BraidedCategory C] [IsCommMonObj A] [MonoidalClosed C] [HasEqualizers C]

/-- Evaluation after acting on the argument, `m ⊗ (a ⊗ f) ↦ f (a • m)`, as an `A`-linear map
`M ⊗ (A ⊗ Hom_A(M, N)) ⟶ N`. -/
private noncomputable def ihomSmulAux (M N : Mod C A) :
    (tensorLeft M).obj (A ⊗ (ihom M).obj N) ⟶ N :=
  Hom.mk' ((α_ M.X A _).inv ≫ (toBimod.obj M).actRight ▷ _ ≫ uncurry (ihomι M N)) (by
    simp only [tensorLeft_smul, selfLeftAction_actionHomRight, whiskerLeft_comp, Category.assoc]
    rw [← smul_comp_uncurry_ihomι, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, ← (Iso.inv_comp_eq _).2 (toBimod.obj M).middle_assoc,
      associator_inv_naturality_left_assoc]
    simp only [comp_whiskerRight, Category.assoc]
    have h : (α_ A M.X (A ⊗ (ihom M).obj N)).inv ≫ (α_ (A ⊗ M.X) A ((ihom M).obj N)).inv =
        A ◁ (α_ M.X A ((ihom M).obj N)).inv ≫ (α_ A (M.X ⊗ A) ((ihom M).obj N)).inv ≫
          (α_ A M.X A).inv ▷ (ihom M).obj N := by
      monoidal
    simp only [selfLeftAction_actionObj]
    rw [reassoc_of% h])

/-- The action on `Hom_A(M, N)` is precomposition with the action on `M`. -/
@[reassoc]
private lemma whiskerLeft_ihomSmul_comp_uncurry_ihomι (M N : Mod C A) :
    M.X ◁ ihomHomEquiv M _ N (ihomSmulAux M N) ≫ uncurry (ihomι M N) =
      (α_ M.X A _).inv ≫ (toBimod.obj M).actRight ▷ _ ≫ uncurry (ihomι M N) := by
  rw [← uncurry_natural_left, ihomHomEquiv_apply_comp_ihomι, uncurry_curry]
  rfl

/-- Over a commutative monoid `A`, the object `Hom_A(M, N)` of `A`-linear maps is a left
`A`-module, with `(a • f) m = f (a • m)`. -/
@[instance_reducible]
noncomputable def ihomModObj (M N : Mod C A) : ModObj A ((ihom M).obj N) where
  smul := ihomHomEquiv M _ N (ihomSmulAux M N)
  one_smul := by
    apply ihom_hom_ext_uncurry
    simp only [selfLeftAction_actionObj, selfLeftAction_actionHomLeft,
      selfLeftAction_actionUnitIso, whiskerLeft_comp, Category.assoc]
    rw [whiskerLeft_ihomSmul_comp_uncurry_ihomι, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, (toBimod.obj M).actRight_one]
    simp
  mul_smul := by
    apply ihom_hom_ext_uncurry
    simp only [selfLeftAction_actionObj, selfLeftAction_actionHomLeft,
      selfLeftAction_actionHomRight, selfLeftAction_actionAssocIso, whiskerLeft_comp,
      Category.assoc]
    -- Expand both actions as precomposition with the right action on `M`, then compare the two
    -- right actions on `M ⊗ A ⊗ A` by associativity of the right action.
    rw [whiskerLeft_ihomSmul_comp_uncurry_ihomι, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      whiskerLeft_ihomSmul_comp_uncurry_ihomι, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, (Iso.inv_comp_eq _).1 (toBimod.obj M).right_assoc.symm]
    simp only [comp_whiskerRight, Category.assoc]
    have h : M.X ◁ (α_ A A ((ihom M).obj N)).hom ≫ (α_ M.X A (A ⊗ (ihom M).obj N)).inv ≫
        (α_ (M.X ⊗ A) A ((ihom M).obj N)).inv ≫ (α_ M.X A A).hom ▷ (ihom M).obj N =
          (α_ M.X (A ⊗ A) ((ihom M).obj N)).inv := by
      monoidal
    rw [reassoc_of% h]

/-- The internal hom of left modules over a commutative monoid `A`: `Hom_A(M, N)`, the object of
`A`-linear maps, with `A` acting through its action on `M`. -/
-- An abbreviation so that the underlying objects are `Hom_A(M, N)` without transports.
noncomputable abbrev internalHom (M : Mod C A) : Mod C A ⥤ Mod C A where
  obj N := letI := ihomModObj M N; ⟨(ihom M).obj N⟩
  map {N N'} g := by
    letI := ihomModObj M N
    letI := ihomModObj M N'
    exact Hom.mk' ((ihom M).map g) (by
      apply ihom_hom_ext_uncurry
      simp only [selfLeftAction_actionObj, selfLeftAction_actionHomRight, whiskerLeft_comp,
        Category.assoc, whiskerLeft_ihom_map_comp_uncurry_ihomι]
      dsimp only [ModObj.smul, ihomModObj]
      simp only [selfLeftAction_actionObj]
      rw [whiskerLeft_ihomSmul_comp_uncurry_ihomι_assoc, whiskerLeft_ihomSmul_comp_uncurry_ihomι,
        associator_inv_naturality_right_assoc, whisker_exchange_assoc,
        whiskerLeft_ihom_map_comp_uncurry_ihomι])
  map_id N := by ext; simp
  map_comp f g := by ext; simp

/-- The action of `A` on `Hom_A(M, N)` is precomposition with the action on `M`:
`(a • f) m = f (a • m)`. -/
@[reassoc]
lemma whiskerLeft_internalHom_smul_comp_uncurry_ihomι (M N : Mod C A) :
    M.X ◁ ((internalHom M).obj N).mod.smul ≫ uncurry (ihomι M N) =
      (α_ M.X A _).inv ≫ ((β_ A M.X).inv ≫ γ[A, M.X]) ▷ _ ≫ uncurry (ihomι M N) :=
  whiskerLeft_ihomSmul_comp_uncurry_ihomι M N

end commutative

end CategoryTheory.Mod
