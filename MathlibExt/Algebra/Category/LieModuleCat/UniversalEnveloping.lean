/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Basic
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Induction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Lie modules and universal-enveloping-algebra modules

A left module over `U(L)` restricts to a Lie module through `ι : L → U(L)`.
Conversely, the universal property extends a Lie representation to an
associative representation of `U(L)`. These constructions give an equivalence
of the two module categories, with identity maps on the coefficient carriers.
The scalar, Lie, and coefficient universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

namespace LieModuleCat.UniversalEnveloping

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

attribute [local instance] LieRing.ofAssociativeRing

/-- Native restriction retains the U-module carrier and its original scalar image. -/
@[implicit_reducible]
def restrictObj (M : ModuleCat.{w} U) : LieModuleCat.{w} R L := by
  letI : Module R M := Module.compHom M (algebraMap R U)
  letI : IsScalarTower R U M := IsScalarTower.of_compHom R U M
  letI : LieRingModule U M := LieRingModule.ofAssociativeModule
  letI : LieModule R U M := LieModule.ofAssociativeModule
  letI : LieRingModule L M := LieRingModule.compLieHom M (UniversalEnvelopingAlgebra.ι R)
  letI : LieModule R L M := LieModule.compLieHom M (UniversalEnvelopingAlgebra.ι R)
  exact LieModuleCat.of R L M

/-- The left Lie action is precisely the left action of the native Lie generator. -/
@[simp]
theorem restrictObj_lie (M : ModuleCat.{w} U) (x : L) (m : restrictObj R L M) :
    ⁅x, m⁆ = @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul
      (UniversalEnvelopingAlgebra.ι R x) (show M from m) := rfl

/-- Ground scalars are the native scalar restriction, not an extra caller dictionary. -/
@[simp]
theorem restrictObj_smul (M : ModuleCat.{w} U) (r : R) (m : restrictObj R L M) :
    r • m = @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul
      (algebraMap R U r) (show M from m) := rfl

/-- An original U-linear morphism is the same native function as a Lie-module morphism. -/
def restrictMap {M N : ModuleCat.{w} U} (f : M ⟶ N) :
    restrictObj R L M ⟶ restrictObj R L N where
  toLinearMap := ((ModuleCat.restrictScalars (algebraMap R U)).map f).hom
  map_lie' := by
    intro x m
    change f.hom ((UniversalEnvelopingAlgebra.ι R x) • (show M from m)) =
      (UniversalEnvelopingAlgebra.ι R x) • (f.hom (show M from m) : N)
    exact f.hom.map_smul _ (show M from m)

@[simp]
theorem restrictMap_apply {M N : ModuleCat.{w} U} (f : M ⟶ N) (m : M) :
    restrictMap R L f m = f.hom m := rfl

/-- Native scalar restriction and Lie pullback are functorial on the original modules. -/
def restrictFunctor : ModuleCat.{w} U ⥤ LieModuleCat.{w} R L where
  obj := restrictObj R L
  map := restrictMap R L
  map_id M := by
    apply LieModuleHom.ext
    intro m
    rfl
  map_comp f g := by
    apply LieModuleHom.ext
    intro m
    rfl

/-- The canonical associative representation supplied by the native universal property. -/
def representation (M : LieModuleCat.{w} R L) : U →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)

theorem representation_ι (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    representation R L M (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
  rw [representation, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The left U-action on an original Lie-module carrier. -/
@[instance_reducible]
def representationModule (M : LieModuleCat.{w} R L) : Module U M :=
  Module.compHom M (representation R L M).toRingHom

/-- The canonical represented module retains the original carrier. -/
@[implicit_reducible]
def representObj (M : LieModuleCat.{w} R L) : ModuleCat.{w} U :=
  letI := representationModule R L M
  ModuleCat.of U M

@[simp]
theorem representObj_smul (M : LieModuleCat.{w} R L) (a : U) (m : representObj R L M) :
    a • m = representation R L M a (m : M) := rfl

/-- Restricting the represented scalar action recovers the original ground action. -/
theorem representation_algebraMap (M : LieModuleCat.{w} R L) (r : R) (m : M) :
    representation R L M (algebraMap R U r) m = r • m := by
  rw [(representation R L M).commutes]
  rfl

/-- The represented-to-restricted round trip keeps the original Lie action. -/
theorem restrict_represent_lie (M : LieModuleCat.{w} R L) (x : L)
    (m : restrictObj R L (representObj R L M)) :
    ⁅x, m⁆ = @Bracket.bracket L M M.lieRingModule.toBracket x (show M from m) := by
  rw [restrictObj_lie]
  change representation R L M (UniversalEnvelopingAlgebra.ι R x) (show M from m) = _
  exact representation_ι R L M x (show M from m)

/-- The same round trip keeps the original ground scalar action. -/
theorem restrict_represent_smul (M : LieModuleCat.{w} R L) (r : R)
    (m : restrictObj R L (representObj R L M)) :
    r • m = @SMul.smul R M M.moduleStructure.toDistribMulAction.toMulAction.toSMul
      r (show M from m) := by
  rw [restrictObj_smul]
  change representation R L M (algebraMap R U r) (show M from m) = _
  exact representation_algebraMap R L M r (show M from m)

/-- Enveloping-algebra induction through the scalar, generator, sum, and product cases. -/
private theorem native_induction {P : U → Prop}
    (hR : ∀ r : R, P (algebraMap R U r))
    (hι : ∀ x : L, P (UniversalEnvelopingAlgebra.ι R x))
    (hMul : ∀ a b : U, P a → P b → P (a * b))
    (hAdd : ∀ a b : U, P a → P b → P (a + b)) (a : U) : P a :=
  UniversalEnvelopingAlgebra.induction R L hR hι hMul hAdd a

/-- A native Lie-module morphism intertwines the lifted associative representations. -/
theorem representation_map {M N : LieModuleCat.{w} R L} (f : M ⟶ N) (a : U) (m : M) :
    f (representation R L M a m) = representation R L N a (f m) := by
  let f' : M →ₗ⁅R,L⁆ N := f
  change f' (representation R L M a m) = representation R L N a (f' m)
  have h : ∀ a : U, ∀ m : M,
      f' (representation R L M a m) = representation R L N a (f' m) :=
    fun a => native_induction R L (P := fun a => ∀ m : M,
      f' (representation R L M a m) = representation R L N a (f' m))
      (by
        intro r m
        rw [representation_algebraMap, representation_algebraMap]
        exact f'.map_smul r m)
      (by
        intro x m
        rw [representation_ι, representation_ι]
        exact f'.map_lie x m)
      (by
        intro a b ha hb m
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb])
      (by
        intro a b ha hb m
        rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
        exact (f'.map_add _ _).trans (congrArg₂ (· + ·) (ha m) (hb m))) a
  exact h a m

/-- The original native Lie-module map becomes U-linear by compatibility of the associative
representations. -/
def representMap {M N : LieModuleCat.{w} R L} (f : M ⟶ N) :
    representObj R L M ⟶ representObj R L N := by
  let F : M →ₗ⁅R,L⁆ N := f.hom
  letI := representationModule R L M
  letI := representationModule R L N
  exact ModuleCat.ofHom
    { toFun := F
      map_add' := F.map_add
      map_smul' := by
        intro a m
        change F (representation R L M a m) = representation R L N a (F m)
        exact representation_map R L f a m }

@[simp]
theorem representMap_apply {M N : LieModuleCat.{w} R L} (f : M ⟶ N) (m : M) :
    (representMap R L f).hom m = f m := rfl

/-- Canonical associative representations are functorial in native Lie-module maps. -/
def representFunctor : LieModuleCat.{w} R L ⥤ ModuleCat.{w} U where
  obj := representObj R L
  map := representMap R L
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

/-- Lifting the restricted generator action returns the original U-action. -/
theorem representation_restrict (M : ModuleCat.{w} U) :
    representation R L (restrictObj R L M) =
      (show U →ₐ[R] Module.End R (restrictObj R L M) from by
        letI : Module U (restrictObj R L M) := M.isModule
        letI : IsScalarTower R U (restrictObj R L M) := IsScalarTower.of_compHom R U M
        exact Algebra.lsmul (A := U) R R (restrictObj R L M)) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  apply LinearMap.ext
  intro m
  change representation R L (restrictObj R L M) (UniversalEnvelopingAlgebra.ι R x) m =
    @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul
      (UniversalEnvelopingAlgebra.ι R x) (show M from m)
  rw [representation_ι, restrictObj_lie]

/-- The represented restriction has exactly the original left U-module action. -/
theorem represent_restrict_smul (M : ModuleCat.{w} U) (a : U)
    (m : representObj R L (restrictObj R L M)) :
    a • m = @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul
      a (show M from m) := by
  change representation R L (restrictObj R L M) a m =
    @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul a (show M from m)
  rw [representation_restrict]
  rfl

/-- The unit keeps the original carrier and both scalar/Lie actions. -/
def unitIso (M : LieModuleCat.{w} R L) :
    M ≅ restrictObj R L (representObj R L M) where
  hom :=
    { toLinearMap :=
        { toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro r m
            change @SMul.smul R M M.moduleStructure.toDistribMulAction.toMulAction.toSMul r m =
              @SMul.smul R (restrictObj R L (representObj R L M))
                (restrictObj R L (representObj R L M)).moduleStructure.toDistribMulAction.toMulAction.toSMul r m
            exact (restrict_represent_smul R L M r m).symm }
      map_lie' := by
        intro x m
        simpa only [id_eq] using (restrict_represent_lie R L M x m).symm }
  inv :=
    { toLinearMap :=
        { toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro r m
            change @SMul.smul R (restrictObj R L (representObj R L M))
                (restrictObj R L (representObj R L M)).moduleStructure.toDistribMulAction.toMulAction.toSMul r m =
              @SMul.smul R M M.moduleStructure.toDistribMulAction.toMulAction.toSMul r m
            exact restrict_represent_smul R L M r m }
      map_lie' := by
        intro x m
        simpa only [id_eq] using restrict_represent_lie R L M x m }
  hom_inv_id := by
    apply LieModuleHom.ext
    intro m
    rfl
  inv_hom_id := by
    apply LieModuleHom.ext
    intro m
    rfl

/-- The counit keeps the original left U-module carrier and action. -/
def counitIso (M : ModuleCat.{w} U) :
    representObj R L (restrictObj R L M) ≅ M where
  hom := (ModuleCat.homEquiv (M := representObj R L (restrictObj R L M)) (N := M)).symm
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a m
        exact represent_restrict_smul R L M a m }
  inv := (ModuleCat.homEquiv (M := M) (N := representObj R L (restrictObj R L M))).symm
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a m
        exact (represent_restrict_smul R L M a m).symm }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

/-- The unit is natural for every native Lie-module morphism. -/
def unitNatIso :
    𝟭 (LieModuleCat.{w} R L) ≅ representFunctor R L ⋙ restrictFunctor R L :=
  NatIso.ofComponents (unitIso R L) (by
    intro M N f
    apply LieModuleHom.ext
    intro m
    rfl)

/-- The counit is natural for every original U-linear morphism. -/
def counitNatIso :
    restrictFunctor R L ⋙ representFunctor R L ≅ 𝟭 (ModuleCat.{w} U) :=
  NatIso.ofComponents (counitIso R L) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl)

/-- Canonical representations and restriction identify the native categories,
without a basis, PBW theorem or scalar-size hypothesis. -/
def equivalence : LieModuleCat.{w} R L ≌ ModuleCat.{w} U where
  functor := representFunctor R L
  inverse := restrictFunctor R L
  unitIso := unitNatIso R L
  counitIso := counitNatIso R L
  functor_unitIso_comp M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

@[simp]
theorem unitIso_hom_apply (M : LieModuleCat.{w} R L) (m : M) :
    (unitIso R L M).hom m = m := rfl

@[simp]
theorem counitIso_hom_apply (M : ModuleCat.{w} U)
    (m : representObj R L (restrictObj R L M)) :
    (counitIso R L M).hom.hom m = m := rfl

/-- The generator action characterizes the associative representation uniquely. -/
theorem representation_unique (M : LieModuleCat.{w} R L)
    (ρ : U →ₐ[R] Module.End R M)
    (hρ : ∀ (x : L) (m : M), ρ (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    ρ = representation R L M := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  apply LinearMap.ext
  intro m
  change ρ (UniversalEnvelopingAlgebra.ι R x) m =
    representation R L M (UniversalEnvelopingAlgebra.ι R x) m
  rw [representation_ι]
  exact hρ x m

/-- A U-linear morphism between represented modules recovers the original Lie-module map. -/
def toLieMap {M N : LieModuleCat.{w} R L}
    (f : representObj R L M ⟶ representObj R L N) : M ⟶ N :=
  (unitIso R L M).hom ≫ restrictMap R L f ≫ (unitIso R L N).inv

@[simp]
theorem toLieMap_apply {M N : LieModuleCat.{w} R L}
    (f : representObj R L M ⟶ representObj R L N) (m : M) :
    toLieMap R L f m = f.hom m := rfl

/-- The native Hom equivalence uses the original functions in both directions. -/
def homEquiv (M N : LieModuleCat.{w} R L) :
    (M ⟶ N) ≃ (representObj R L M ⟶ representObj R L N) where
  toFun := representMap R L
  invFun := toLieMap R L
  left_inv f := by
    apply LieModuleHom.ext
    intro m
    rfl
  right_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

/-- Canonical representations retain addition of original Lie-module maps. -/
instance representFunctor_additive : (representFunctor R L).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

/-- Native scalar/Lie restriction retains addition of original U-linear maps. -/
instance restrictFunctor_additive : (restrictFunctor R L).Additive where
  map_add {M N} f g := by
    apply LieModuleHom.ext
    intro m
    rfl

/-- Forgetting the restricted Lie action is the original native scalar restriction. -/
def restrictForgetIso : restrictFunctor R L ⋙ LieModuleCat.forget R L ≅
    ModuleCat.restrictScalars (algebraMap R U) :=
  NatIso.ofComponents (fun M => Iso.refl _) (by
    intro M N f
    rfl)

end LieModuleCat.UniversalEnveloping
