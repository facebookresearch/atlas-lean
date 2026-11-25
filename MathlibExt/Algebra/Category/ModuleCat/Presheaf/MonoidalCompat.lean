/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou
-/

/-
Author: @toskua
-/

module

-- Additional author credit: Junyan Xu.




public import MathlibExt.Algebra.Category.Grp.Monoidal
public import MathlibExt.CategoryTheory.Limits.Shapes.EqualizersCompat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Tensor products of module presheaves as coequalizers

The maps `tensorDistrib`, `actₗ` and `actᵣ` present tensor products of module
presheaves by scalar balancing. Their reflexive coequalizer cocones are
constructed in abelian groups, with the unit section and scalar-action
compatibilities.
-/

@[expose] public section

open _root_.CategoryTheory CategoryTheory MonoidalCategory BraidedCategory Category Limits
open scoped _root_.AddCommGrpCat AddCommGrpCat

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

/-!
# Tensor products of module presheaves as coequalizers

The maps `tensorDistrib`, `actₗ` and `actᵣ` present tensor products of module
presheaves by scalar balancing. Their reflexive coequalizer cocones are
constructed in abelian groups, with the unit section and scalar-action
compatibilities.
-/

open TensorProduct

/-- Additive maps from a tensor product agree if they agree on all pure tensors. -/
private theorem _root_.TensorProduct.extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- Additive maps from a threefold tensor product agree if they agree on
all pure tensors. -/
private theorem _root_.TensorProduct.ext_threefoldAdd {R R₂ : Type*} [CommSemiring R]
    [CommSemiring R₂] {M N M₂ P₃ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid P₃]
    [Module R M] [Module R N] [Module R₂ M₂]
    [Module R₂ M] [SMulCommClass R R₂ M]
    {F : Type*} [FunLike F (M ⊗[R] N ⊗[R₂] M₂) P₃]
    [AddMonoidHomClass F (M ⊗[R] N ⊗[R₂] M₂) P₃]
    {g h : F} (H : ∀ (x : M) (y : N) (z : M₂), g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) :
    g = h := by
  apply TensorProduct.extAdd
  intro xy z
  induction xy using TensorProduct.inductionOn with
  | tmul m n => exact H m n z
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]

instance modulePresheafAbCompat (M : PresheafOfModules.{u} (R ⋙ forget₂ ..)) (U : Cᵒᵖ) :
    Module (R.obj U) (M.presheaf.obj U) :=
  inferInstanceAs (Module (R.obj U) (M.obj U))

/-- The scalar action on the underlying abelian-group presheaf at an object. -/
@[nolint defsWithUnderscore]
abbrev instModuleCarrierObjOppositeCommRingCatCarrierAbPresheaf_mathlibExt
    (M : PresheafOfModules.{u} (R ⋙ forget₂ ..)) (U : Cᵒᵖ) :
    Module (R.obj U) (M.presheaf.obj U) :=
  modulePresheafAbCompat M U

attribute [deprecated modulePresheafAbCompat (since := "2026-11-10")]
  instModuleCarrierObjOppositeCommRingCatCarrierAbPresheaf_mathlibExt

variable (M N : PresheafOfModules.{u} (R ⋙ forget₂ ..))

/-- The canonical morphism from the pointwise tensor product over `ℤ` to the tensor
product over `R`. -/
noncomputable def tensorDistrib : M.presheaf ⊗ N.presheaf ⟶ (M ⊗ N).presheaf where
  app U := AddCommGrpCat.ofHom
    (mapOfCompatibleSMul (R.obj U) ℤ ℤ (M.obj U) (N.obj U)).toAddMonoidHom
  naturality _ _ _ := by ext1; exact TensorProduct.extAdd fun _ _ ↦ rfl

instance : Epi (tensorDistrib M N) where
  left_cancellation _ _ h := by
    ext U x
    obtain ⟨y, rfl⟩ := mapOfCompatibleSMul_surjective _ ℤ ℤ _ _ x
    exact congr(($h).app U y)

/-- The presheaf of rings, viewed as a presheaf of abelian groups. -/
noncomputable abbrev ringAb (R : Cᵒᵖ ⥤ CommRingCat.{u}) : Cᵒᵖ ⥤ Ab.{u} :=
  (unit (R ⋙ forget₂ ..)).presheaf

/-- The unit section of a presheaf of commutative rings regarded as a presheaf of abelian groups. -/
noncomputable def unitSection (R : Cᵒᵖ ⥤ CommRingCat.{u}) : 𝟙_ _ ⟶ ringAb R where
  app U := AddCommGrpCat.ofHom <| (Int.castAddHom (R.obj U)).comp AddEquiv.ulift.toAddMonoidHom
  naturality U V f := by ext ⟨z⟩; exact (map_intCast (R.map f).hom z).symm

/-- The action of the presheaf of rings on a presheaf of modules, written on the left. -/
noncomputable def act : ringAb R ⊗ M.presheaf ⟶ M.presheaf where
  app U := AddCommGrpCat.ofHom <| TensorProduct.liftAddHom (smulAddHom (R.obj U) _)
    fun n (r : R.obj U) m ↦ show (n • r) • m = r • (n • m) by rw [smul_comm, smul_assoc]
  naturality U V f := by ext1; exact TensorProduct.extAdd fun r m ↦ (M.map_smul ..).symm

/-- The first of the two maps whose coequalizer is the tensor product: it sends
`m ⊗ (r ⊗ n)` to `(r • m) ⊗ n`. -/
noncomputable def actₗ : (M.presheaf ⊗ ringAb R) ⊗ N.presheaf ⟶ M.presheaf ⊗ N.presheaf :=
  ((β_ _ _).hom ≫ act M) ▷ N.presheaf

/-- The second of the two maps whose coequalizer is the tensor product: it sends
`m ⊗ (r ⊗ n)` to `m ⊗ (r • n)`. -/
noncomputable def actᵣ : (M.presheaf ⊗ ringAb R) ⊗ N.presheaf ⟶ M.presheaf ⊗ N.presheaf :=
  (α_ _ _ _).hom ≫ (M.presheaf ◁ act N)

/-- The common section of `act₁` and `act₂`. -/
noncomputable def actSection : M.presheaf ⊗ N.presheaf ⟶ (M.presheaf ⊗ ringAb R) ⊗ N.presheaf :=
  ((ρ_ _).inv ≫ (_ ◁ unitSection R)) ▷ _

lemma act_tensorDistrib : actₗ M N ≫ tensorDistrib M N = actᵣ M N ≫ tensorDistrib M N := by
  ext U : 3
  refine TensorProduct.ext_threefoldAdd fun m (r : R.obj U) n ↦ ?_
  exact smul_tmul (R := R.obj U) r m n

@[simp] lemma actSection_comp_actₗ : actSection M N ≫ actₗ M N = 𝟙 _ := by
  ext U : 3
  exact TensorProduct.extAdd fun m n ↦ congr(($(congr($(Int.cast_one
    (R := R.obj U)) • m).trans <| one_smul (R.obj U) m)) ⊗ₜ n)

@[simp] lemma actSection_comp_actᵣ : actSection M N ≫ actᵣ M N = 𝟙 _ := by
  ext U : 3
  exact TensorProduct.extAdd fun m n ↦ congr((m ⊗ₜ $(congr($(Int.cast_one
    (R := R.obj U)) • n).trans <| one_smul (R.obj U) n)))

/-- The colimit cocone realizing the tensor product as a reflexive coequalizer. -/
noncomputable def reflexiveColimitCoconeAb :
    ColimitCocone (reflexivePair (actₗ M N) (actᵣ M N) (actSection M N)) :=
  let c := ReflexiveCofork.mk _ (act_tensorDistrib M N)
{ cocone := c
  isColimit :=
    have : Epi c.toCofork.π := inferInstanceAs (Epi (tensorDistrib M N))
    ReflexiveCofork.isColimitEquiv _ _ <| Cofork.IsColimit.ofEpi _ (fun c ↦
    { app U := AddCommGrpCat.ofHom <| TensorProduct.liftAddHom ((LinearMap.toAddMonoidHom'.comp
        (TensorProduct.mk ℤ (M.obj U) (N.obj U)).toAddMonoidHom).compr₂ ((c.ι.app .one).app U).hom)
        fun r m n ↦ congr($(Cofork.condition c).app U ((m ⊗ₜ r) ⊗ₜ n))
      naturality U V f := by
        ext1
        exact TensorProduct.extAdd fun m n ↦ congr_arg (· (m ⊗ₜ n)) ((c.ι.app .one).naturality f) })
    (fun c ↦ by ext _ : 3; exact TensorProduct.extAdd fun _ _ ↦ rfl) }

/-- The colimit cocone realizing the tensor product as a coequalizer. -/
noncomputable def colimitCoconeAb : ColimitCocone (parallelPair (actₗ M N) (actᵣ M N)) where
  cocone := _
  isColimit := (ReflexiveCofork.isColimitEquiv _ _).symm (reflexiveColimitCoconeAb M N).isColimit

end PresheafOfModules

end
