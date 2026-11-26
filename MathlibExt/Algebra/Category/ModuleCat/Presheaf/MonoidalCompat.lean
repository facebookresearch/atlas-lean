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
# Tensor products of module presheaves by scalar balancing

For module presheaves M and N over a commutative ring presheaf R, their underlying additive
presheaves have a tensor product over the integers. Quotienting by the relations (r·m) ⊗ n = m
⊗ (r·n) gives the additive presheaf underlying M ⊗_R N.

The two scalar-action maps form a reflexive pair: inserting 1 ∈ R is a common section. The
canonical map from the integer tensor product to the R-tensor product is their coequalizer in
presheaves of abelian groups.
-/

@[expose] public section

open _root_.CategoryTheory CategoryTheory MonoidalCategory BraidedCategory Category Limits
open scoped _root_.AddCommGrpCat AddCommGrpCat

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

/-!
# The reflexive pair expressing scalar balancing

The left map sends (m ⊗ r) ⊗ n to (r·m) ⊗ n, and the right map sends it to m ⊗ (r·n). Their
common section sends m ⊗ n to (m ⊗ 1) ⊗ n. The map to the R-tensor product coequalizes the
pair and has the corresponding universal property.
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

/-- The section module of an underlying additive presheaf.

At U, the carrier of the additive presheaf underlying M retains its module structure over the
commutative ring R(U). -/
instance modulePresheafAbCompat (M : PresheafOfModules.{u} (R ⋙ forget₂ ..)) (U : Cᵒᵖ) :
    Module (R.obj U) (M.presheaf.obj U) :=
  inferInstanceAs (Module (R.obj U) (M.obj U))

/-- The module structure on the additive presheaf carrier.

The additive presheaf carrier at U is given the same R(U)-module structure as the section
module M(U). -/
@[nolint defsWithUnderscore]
abbrev instModuleCarrierObjOppositeCommRingCatCarrierAbPresheaf_mathlibExt
    (M : PresheafOfModules.{u} (R ⋙ forget₂ ..)) (U : Cᵒᵖ) :
    Module (R.obj U) (M.presheaf.obj U) :=
  modulePresheafAbCompat M U

attribute [deprecated modulePresheafAbCompat (since := "2026-11-10")]
  instModuleCarrierObjOppositeCommRingCatCarrierAbPresheaf_mathlibExt

variable (M N : PresheafOfModules.{u} (R ⋙ forget₂ ..))

/-- The map from integer tensor products to ring tensor products.

For each U, send m ⊗_ℤ n to m ⊗_{R(U)} n. These maps define a morphism from M.presheaf ⊗
N.presheaf to the additive presheaf of M ⊗_R N. -/
noncomputable def tensorDistrib : M.presheaf ⊗ N.presheaf ⟶ (M ⊗ N).presheaf where
  app U := AddCommGrpCat.ofHom
    (mapOfCompatibleSMul (R.obj U) ℤ ℤ (M.obj U) (N.obj U)).toAddMonoidHom
  naturality _ _ _ := by ext1; exact TensorProduct.extAdd fun _ _ ↦ rfl

instance : Epi (tensorDistrib M N) where
  left_cancellation _ _ h := by
    ext U x
    obtain ⟨y, rfl⟩ := mapOfCompatibleSMul_surjective _ ℤ ℤ _ _ x
    exact congr(($h).app U y)

/-- The additive presheaf of coefficient rings.

Forget multiplication in the ring presheaf R to obtain its presheaf of additive abelian
groups, the additive presheaf of the module tensor unit. -/
noncomputable abbrev ringAb (R : Cᵒᵖ ⥤ CommRingCat.{u}) : Cᵒᵖ ⥤ Ab.{u} :=
  (unit (R ⋙ forget₂ ..)).presheaf

/-- The integer unit map into the coefficient ring presheaf.

At U, the additive tensor unit maps to R(U) by sending a lifted integer n to its ring cast. -/
noncomputable def unitSection (R : Cᵒᵖ ⥤ CommRingCat.{u}) : 𝟙_ _ ⟶ ringAb R where
  app U := AddCommGrpCat.ofHom <| (Int.castAddHom (R.obj U)).comp AddEquiv.ulift.toAddMonoidHom
  naturality U V f := by ext ⟨z⟩; exact (map_intCast (R.map f).hom z).symm

/-- The scalar action on an additive module presheaf.

At U, the map R(U) ⊗_ℤ M(U) → M(U) sends r ⊗ m to r·m. -/
noncomputable def act : ringAb R ⊗ M.presheaf ⟶ M.presheaf where
  app U := AddCommGrpCat.ofHom <| TensorProduct.liftAddHom (smulAddHom (R.obj U) _)
    fun n (r : R.obj U) m ↦ show (n • r) • m = r • (n • m) by rw [smul_comm, smul_assoc]
  naturality U V f := by ext1; exact TensorProduct.extAdd fun r m ↦ (M.map_smul ..).symm

/-- The scalar action on the first tensor factor.

The left balancing map sends (m ⊗ r) ⊗ n to (r·m) ⊗ n in the integer tensor product of
additive presheaves. -/
noncomputable def actₗ : (M.presheaf ⊗ ringAb R) ⊗ N.presheaf ⟶ M.presheaf ⊗ N.presheaf :=
  ((β_ _ _).hom ≫ act M) ▷ N.presheaf

/-- The scalar action on the second tensor factor.

The right balancing map sends (m ⊗ r) ⊗ n to m ⊗ (r·n), with the tensor associator included. -/
noncomputable def actᵣ : (M.presheaf ⊗ ringAb R) ⊗ N.presheaf ⟶ M.presheaf ⊗ N.presheaf :=
  (α_ _ _ _).hom ≫ (M.presheaf ◁ act N)

/-- The unit section of the scalar-balancing pair.

Insert the ring unit to send m ⊗ n to (m ⊗ 1) ⊗ n. This is a common section of the left and
right action maps. -/
noncomputable def actSection : M.presheaf ⊗ N.presheaf ⟶ (M.presheaf ⊗ ringAb R) ⊗ N.presheaf :=
  ((ρ_ _).inv ≫ (_ ◁ unitSection R)) ▷ _

/-- The ring tensor quotient coequalizes both scalar actions.

The left and right balancing maps have the same composite with tensorDistrib, expressing (r·m)
⊗_R n = m ⊗_R (r·n). -/
lemma act_tensorDistrib : actₗ M N ≫ tensorDistrib M N = actᵣ M N ≫ tensorDistrib M N := by
  ext U : 3
  refine TensorProduct.ext_threefoldAdd fun m (r : R.obj U) n ↦ ?_
  exact smul_tmul (R := R.obj U) r m n

/-- The unit section retracts the first scalar action.

Inserting the ring unit and then applying the left scalar action gives the identity on the
integer tensor product. -/
@[simp] lemma actSection_comp_actₗ : actSection M N ≫ actₗ M N = 𝟙 _ := by
  ext U : 3
  exact TensorProduct.extAdd fun m n ↦ congr(($(congr($(Int.cast_one
    (R := R.obj U)) • m).trans <| one_smul (R.obj U) m)) ⊗ₜ n)

/-- The unit section retracts the second scalar action.

Inserting the ring unit and then applying the right scalar action gives the identity on the
integer tensor product. -/
@[simp] lemma actSection_comp_actᵣ : actSection M N ≫ actᵣ M N = 𝟙 _ := by
  ext U : 3
  exact TensorProduct.extAdd fun m n ↦ congr((m ⊗ₜ $(congr($(Int.cast_one
    (R := R.obj U)) • n).trans <| one_smul (R.obj U) n)))

/-- The reflexive coequalizer of scalar balancing.

The additive presheaf of M ⊗_R N, with tensorDistrib, is a colimit cocone of the reflexive
pair given by the two scalar actions and their unit section. -/
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

/-- The coequalizer presentation of a module-presheaf tensor product.

The map tensorDistrib presents the additive presheaf of M ⊗_R N as the coequalizer of the left
and right scalar-action maps. -/
noncomputable def colimitCoconeAb : ColimitCocone (parallelPair (actₗ M N) (actᵣ M N)) where
  cocone := _
  isColimit := (ReflexiveCofork.isColimitEquiv _ _).symm (reflexiveColimitCoconeAb M N).isColimit

end PresheafOfModules

end
