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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.LeftGroupAdjunction
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Exact balanced tensor functors with projective factors

For an associative ring `R`, let `P` be categorically projective in a module category. If `P`
is a right `R`-module, tensoring `P ⊗_R -` sends monomorphisms of left modules to
monomorphisms of additive groups. If `P` is a left module, the same holds for `- ⊗_R P` on
right modules.

Together with the tensor adjunctions, these statements give preservation of homology in either
variable when the fixed factor is projective. The ring and common module-carrier universes are
independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.BalancedTensor

variable (R : Type u) [Ring R]

private def characterUp : AddCircle (1 : ℚ) →+ ULift.{v} (AddCircle (1 : ℚ)) where
  toFun := ULift.up
  map_zero' := rfl
  map_add' _ _ := rfl

private def characterDown : ULift.{v} (AddCircle (1 : ℚ)) →+ AddCircle (1 : ℚ) where
  toFun := ULift.down
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem homGroupPrecomp_surjective_of_injective
    {N N' : ModuleCat.{v} R} (g : N ⟶ N') (hg : Function.Injective g.hom) :
    let I := AddCommGrpCat.of (ULift.{v} (AddCircle (1 : ℚ)))
    letI := ChainComplex.homGroupModule R N I
    letI := ChainComplex.homGroupModule R N' I
    Function.Surjective (homGroupPrecomp R g I) := by
  dsimp only
  let I := AddCommGrpCat.of (ULift.{v} (AddCircle (1 : ℚ)))
  let := ChainComplex.homGroupModule R N I
  let := ChainComplex.homGroupModule R N' I
  intro ψ
  obtain ⟨ψ', hψ'⟩ := CharacterModule.dual_surjective_of_injective
    (g.hom.restrictScalars ℤ) hg (characterDown.comp ψ.hom)
  refine ⟨AddCommGrpCat.ofHom (characterUp.comp ψ'), ?_⟩
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  apply ULift.ext
  exact DFunLike.congr_fun hψ' n

/-- Tensoring a monomorphism with a projective right module remains monic.

Let `P` be categorically projective in `ModuleCat Rᵐᵒᵖ` and `g : N ⟶ N'` a monomorphism of
left `R`-modules. The induced additive-group map `P ⊗_R g` is a monomorphism. -/
theorem mono_groupBifunctor_obj_map_of_projective
    (P : ModuleCat.{v} Rᵐᵒᵖ) [Projective P]
    {N N' : ModuleCat.{v} R} (g : N ⟶ N') [Mono g] :
    Mono (((groupBifunctor R).obj P).map g) := by
  classical
  let I := AddCommGrpCat.of (ULift.{v} (AddCircle (1 : ℚ)))
  let := ChainComplex.homGroupModule R N I
  let := ChainComplex.homGroupModule R N' I
  let E := ModuleCat.of Rᵐᵒᵖ ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I)
  let E' := ModuleCat.of Rᵐᵒᵖ ((forget₂ (ModuleCat R) AddCommGrpCat).obj N' ⟶ I)
  let e : E' ⟶ E := ModuleCat.ofHom (homGroupPrecomp R g I)
  let : Epi e := (ModuleCat.epi_iff_surjective e).2
    (homGroupPrecomp_surjective_of_injective R g ((ModuleCat.mono_iff_injective g).1 inferInstance))
  rw [AddCommGrpCat.mono_iff_injective]
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  let ψ : ((groupBifunctor R).obj P).obj N ⟶ I :=
    AddCommGrpCat.ofHom (characterUp.comp χ)
  let a : P ⟶ E := ModuleCat.ofHom (groupCurry R P N I ψ)
  let b : P ⟶ E' := Projective.factorThru a e
  have hba : b ≫ e = a := Projective.factorThru_comp a e
  let ψ' := groupUncurry R P N' I b.hom
  have hψ : ((groupBifunctor R).obj P).map g ≫ ψ' = ψ := by
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply groupHom_ext R P N I
    intro p n
    have h := congrArg (fun f : P ⟶ E => (f.hom p).hom n) hba
    change ((homGroupPrecomp R g I) (b.hom p)).hom n = (groupCurry R P N I ψ p).hom n at h
    rw [homGroupPrecomp_apply, groupCurry_mk] at h
    change ψ'.hom ((((groupBifunctor R).obj P).map g).hom
        (TensorProduct.Balanced.mk ℤ R P N p n)) =
      ψ.hom (TensorProduct.Balanced.mk ℤ R P N p n)
    rw [groupBifunctor_obj_map_mk, groupUncurry_mk]
    exact h
  have hz := congrArg
    (fun f : ((groupBifunctor R).obj P).obj N ⟶ I => f.hom x) hψ
  have hzero : ψ.hom x = 0 := by
    change ψ'.hom ((((groupBifunctor R).obj P).map g).hom x) = ψ.hom x at hz
    rw [hx, map_zero] at hz
    exact hz.symm
  have hχ : ULift.up (χ x) = (0 : ULift.{v} (AddCircle (1 : ℚ))) := hzero
  exact congrArg ULift.down hχ

/-- Tensoring a monomorphism with a projective left module remains monic.

Let `P` be categorically projective in `ModuleCat R` and `g : A ⟶ A'` a monomorphism of right
`R`-modules. The induced additive-group map `g ⊗_R P` is a monomorphism. -/
theorem mono_groupBifunctor_flip_obj_map_of_projective
    (P : ModuleCat.{v} R) [Projective P]
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (g : A ⟶ A') [Mono g] :
    Mono ((((groupBifunctor R).flip.obj P).map g)) := by
  classical
  let I := AddCommGrpCat.of (ULift.{v} (AddCircle (1 : ℚ)))
  let := ChainComplex.homGroupModule Rᵐᵒᵖ A I
  let := ChainComplex.homGroupModule Rᵐᵒᵖ A' I
  let := leftHomGroupModule R A I
  let := leftHomGroupModule R A' I
  let E := ModuleCat.of R ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A ⟶ I)
  let E' := ModuleCat.of R ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).obj A' ⟶ I)
  let e : E' ⟶ E := ModuleCat.ofHom (leftHomGroupPrecomp R g I)
  have he : Function.Surjective (leftHomGroupPrecomp R g I) :=
    homGroupPrecomp_surjective_of_injective Rᵐᵒᵖ g
      ((ModuleCat.mono_iff_injective g).1 inferInstance)
  let : Epi e := (ModuleCat.epi_iff_surjective e).2 he
  rw [AddCommGrpCat.mono_iff_injective]
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  let ψ : ((groupBifunctor R).obj A).obj P ⟶ I :=
    AddCommGrpCat.ofHom (characterUp.comp χ)
  let a : P ⟶ E := ModuleCat.ofHom (groupCurryLeft R A P I ψ)
  let b : P ⟶ E' := Projective.factorThru a e
  have hba : b ≫ e = a := Projective.factorThru_comp a e
  let ψ' := groupUncurryLeft R A' P I b.hom
  have hψ : (((groupBifunctor R).map g).app P) ≫ ψ' = ψ := by
    let : Module ℤ P := Module.compHom P (algebraMap ℤ R)
    apply groupHom_ext R A P I
    intro x p
    have h := congrArg (fun f : P ⟶ E => (f.hom p).hom x) hba
    change ((leftHomGroupPrecomp R g I) (b.hom p)).hom x =
      (groupCurryLeft R A P I ψ p).hom x at h
    rw [leftHomGroupPrecomp_apply, groupCurryLeft_mk] at h
    change ψ'.hom ((((groupBifunctor R).map g).app P).hom
        (groupPure R A P x p)) = ψ.hom (groupPure R A P x p)
    have hMap : (((groupBifunctor R).map g).app P).hom (groupPure R A P x p) =
        groupPure R A' P (g.hom x) p :=
      groupBifunctor_map_mk R g P x p
    have hValue := groupUncurryLeft_mk R A' P I b.hom (g.hom x) p
    exact (congrArg ψ'.hom hMap).trans (hValue.trans h)
  have hz := congrArg (fun f : ((groupBifunctor R).obj A).obj P ⟶ I => f.hom x) hψ
  have hzero : ψ.hom x = 0 := by
    change ψ'.hom ((((groupBifunctor R).flip.obj P).map g).hom x) = ψ.hom x at hz
    rw [hx, map_zero] at hz
    exact hz.symm
  have hχ : ULift.up (χ x) = (0 : ULift.{v} (AddCircle (1 : ℚ))) := hzero
  exact congrArg ULift.down hχ

/-- Tensor functor with a projective right factor preserves homology.

For a categorically projective right `R`-module `P`, the group-valued balanced tensor functor
`P ⊗_R -` preserves homology. -/
theorem groupBifunctor_obj_preservesHomology_of_projective
    (P : ModuleCat.{v} Rᵐᵒᵖ) [Projective P] :
    ((groupBifunctor R).obj P).PreservesHomology := by
  let F := (groupBifunctor R).obj P
  let : PreservesFiniteColimits F := inferInstance
  apply ((Functor.exact_tfae F).out 1 3).1
  intro S hS
  let : Mono S.f := hS.mono_f
  let : Mono (F.map S.f) := mono_groupBifunctor_obj_map_of_projective R P S.f
  have h := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).1
    inferInstance S hS
  let : Epi (F.map S.g) := h.2
  let : Mono (S.map F).f := by
    change Mono (F.map S.f)
    infer_instance
  let : Epi (S.map F).g := by
    change Epi (F.map S.g)
    infer_instance
  exact ⟨h.1⟩

/-- Tensor functor with a projective left factor preserves homology.

For a categorically projective left `R`-module `P`, the group-valued balanced tensor functor
`- ⊗_R P` preserves homology. -/
theorem groupBifunctor_flip_obj_preservesHomology_of_projective
    (P : ModuleCat.{v} R) [Projective P] :
    ((groupBifunctor R).flip.obj P).PreservesHomology := by
  let F := (groupBifunctor R).flip.obj P
  let : F.Additive := by
    refine ⟨?_⟩
    intro A A' f g
    exact congrArg (fun t : (groupBifunctor R).obj A ⟶ (groupBifunctor R).obj A' =>
      t.app P) ((groupBifunctor R).map_add (f := f) (g := g))
  let : PreservesFiniteColimits F := inferInstance
  apply ((Functor.exact_tfae F).out 1 3).1
  intro S hS
  let : Mono S.f := hS.mono_f
  let : Mono (F.map S.f) := mono_groupBifunctor_flip_obj_map_of_projective R P S.f
  have h := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).1
    inferInstance S hS
  let : Epi (F.map S.g) := h.2
  let : Mono (S.map F).f := by
    change Mono (F.map S.f)
    infer_instance
  let : Epi (S.map F).g := by
    change Epi (F.map S.g)
    infer_instance
  exact ⟨h.1⟩

end ModuleCat.BalancedTensor
