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
# Lie modules and modules over the universal enveloping algebra

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `U = U_R(L)` its universal
enveloping algebra. A left `U`-module restricts to a left `L`-module by `[x,m] = ι(x) • m`,
with ground action `r • m = algebraMap(R,U)(r) • m`.

The universal property extends the representation `L → End_R(M)` of a left Lie module to `U
→ₐ[R] End_R(M)`. Extension and restriction give inverse equivalences of module categories. The
unit, counit, and hom-set bijection retain coefficient values, and the scalar-ring, Lie-
algebra, and coefficient-carrier universes are independent.
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

/-- A Lie module obtained from an enveloping-algebra module.

For a left `U_R(L)`-module `M`, restrict scalars along `R → U_R(L)` and define `[x,m] = ι(x) •
m`. The coefficient carrier is `M`. -/
@[implicit_reducible]
def restrictObj (M : ModuleCat.{w} U) : LieModuleCat.{w} R L := by
  letI : Module R M := Module.compHom M (algebraMap R U)
  letI : IsScalarTower R U M := IsScalarTower.of_compHom R U M
  letI : LieRingModule U M := LieRingModule.ofAssociativeModule
  letI : LieModule R U M := LieModule.ofAssociativeModule
  letI : LieRingModule L M := LieRingModule.compLieHom M (UniversalEnvelopingAlgebra.ι R)
  letI : LieModule R L M := LieModule.compLieHom M (UniversalEnvelopingAlgebra.ι R)
  exact LieModuleCat.of R L M

/-- The generator action in an enveloping-module restriction.

For `x ∈ L` and `m ∈ M`, the restricted Lie action is left multiplication by the universal
generator: `[x,m] = ι(x) • m`. -/
@[simp]
theorem restrictObj_lie (M : ModuleCat.{w} U) (x : L) (m : restrictObj R L M) :
    ⁅x, m⁆ = @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul
      (UniversalEnvelopingAlgebra.ι R x) (show M from m) := rfl

/-- The ground action in an enveloping-module restriction.

For `r ∈ R` and `m ∈ M`, the restricted scalar action is `algebraMap(R,U)(r) • m` using the
given `U`-module action. -/
@[simp]
theorem restrictObj_smul (M : ModuleCat.{w} U) (r : R) (m : restrictObj R L M) :
    r • m = @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul
      (algebraMap R U r) (show M from m) := rfl

/-- A Lie-module map obtained from an enveloping-module map.

A `U_R(L)`-linear morphism defines an `R`-linear map between the restricted Lie modules,
commuting with each generator action. -/
def restrictMap {M N : ModuleCat.{w} U} (f : M ⟶ N) :
    restrictObj R L M ⟶ restrictObj R L N where
  toLinearMap := ((ModuleCat.restrictScalars (algebraMap R U)).map f).hom
  map_lie' := by
    intro x m
    change f.hom ((UniversalEnvelopingAlgebra.ι R x) • (show M from m)) =
      (UniversalEnvelopingAlgebra.ι R x) • (f.hom (show M from m) : N)
    exact f.hom.map_smul _ (show M from m)

/-- The value of an enveloping-module map after Lie restriction.

For `f : M ⟶ N`, the restricted Lie-module map has value `f.hom(m)` at `m ∈ M`. -/
@[simp]
theorem restrictMap_apply {M N : ModuleCat.{w} U} (f : M ⟶ N) (m : M) :
    restrictMap R L f m = f.hom m := rfl

/-- The restriction functor from enveloping modules to Lie modules.

This sends a left `U_R(L)`-module to its Lie action through `ι : L → U_R(L)` and retains the
values of its module morphisms. -/
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

/-- The enveloping-algebra representation of a Lie module.

For a left Lie module `M`, the universal property gives `U_R(L) →ₐ[R] End_R(M)` extending the
action map `L → End_R(M)`. -/
def representation (M : LieModuleCat.{w} R L) : U →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)

/-- The lifted representation on a Lie generator.

For `x ∈ L` and `m ∈ M`, the extended representation satisfies `ρ(ι(x))(m) = [x,m]`. -/
theorem representation_ι (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    representation R L M (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
  rw [representation, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The enveloping-module action on a Lie-module carrier.

The representation `ρ : U_R(L) →ₐ[R] End_R(M)` defines a left `U_R(L)`-module structure on `M`
by `a • m = ρ(a)(m)`. -/
@[instance_reducible]
def representationModule (M : LieModuleCat.{w} R L) : Module U M :=
  Module.compHom M (representation R L M).toRingHom

/-- The enveloping-module object associated to a Lie module.

A left Lie module `M` is regarded as a left `U_R(L)`-module via its extended representation,
retaining its coefficient carrier. -/
@[implicit_reducible]
def representObj (M : LieModuleCat.{w} R L) : ModuleCat.{w} U :=
  letI := representationModule R L M
  ModuleCat.of U M

/-- The action formula for an associated enveloping module.

For `a ∈ U_R(L)`, its action on the represented module is `a • m = ρ(a)(m)`, where `ρ` extends
the Lie representation. -/
@[simp]
theorem representObj_smul (M : LieModuleCat.{w} R L) (a : U) (m : representObj R L M) :
    a • m = representation R L M a (m : M) := rfl

/-- The lifted representation on ground scalars.

For `r ∈ R`, the extended representation acts by the given coefficient scalar action:
`ρ(algebraMap(R,U)(r))(m) = r • m`. -/
theorem representation_algebraMap (M : LieModuleCat.{w} R L) (r : R) (m : M) :
    representation R L M (algebraMap R U r) m = r • m := by
  rw [(representation R L M).commutes]
  rfl

/-- Recovery of the Lie action after representation and restriction.

Extending a Lie module to `U_R(L)` and restricting back to `L` gives the same bracket action
on its coefficient carrier. -/
theorem restrict_represent_lie (M : LieModuleCat.{w} R L) (x : L)
    (m : restrictObj R L (representObj R L M)) :
    ⁅x, m⁆ = @Bracket.bracket L M M.lieRingModule.toBracket x (show M from m) := by
  rw [restrictObj_lie]
  change representation R L M (UniversalEnvelopingAlgebra.ι R x) (show M from m) = _
  exact representation_ι R L M x (show M from m)

/-- Recovery of ground scalars after representation and restriction.

Extending a Lie module to `U_R(L)` and restricting back gives the same `R`-scalar action on
its coefficient carrier. -/
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

/-- Intertwining of lifted enveloping-algebra representations.

For a Lie-module map `f : M → N`, every `a ∈ U_R(L)` satisfies `f(ρ_M(a)(m)) = ρ_N(a)(f(m))`. -/
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

/-- The enveloping-module map associated to a Lie-module morphism.

A Lie-module map is linear over `U_R(L)` for the extended representations, hence defines a
morphism between the associated enveloping modules. -/
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

/-- The value of a represented Lie-module morphism.

For a Lie-module map `f : M ⟶ N`, the associated `U_R(L)`-linear morphism has value `f(m)`. -/
@[simp]
theorem representMap_apply {M N : LieModuleCat.{w} R L} (f : M ⟶ N) (m : M) :
    (representMap R L f).hom m = f m := rfl

/-- The representation functor to enveloping modules.

This sends a left Lie module to its extended `U_R(L)`-action and a Lie-module morphism to the
corresponding enveloping-linear map. -/
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

/-- Recovery of an enveloping representation from its Lie restriction.

The representation obtained by restricting a `U_R(L)`-module to `L` and extending again equals
its given left multiplication representation. -/
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

/-- Recovery of the enveloping action after Lie restriction.

For a left `U_R(L)`-module `M`, restricting to `L` and representing again retains `a • m` for
every `a ∈ U_R(L)`. -/
theorem represent_restrict_smul (M : ModuleCat.{w} U) (a : U)
    (m : representObj R L (restrictObj R L M)) :
    a • m = @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul
      a (show M from m) := by
  change representation R L (restrictObj R L M) a m =
    @SMul.smul U M M.isModule.toDistribMulAction.toMulAction.toSMul a (show M from m)
  rw [representation_restrict]
  rfl

/-- The unit isomorphism for Lie-module representation.

A Lie module is isomorphic to the Lie restriction of its associated enveloping module. Both
component maps are identity functions, preserving the ground and Lie actions. -/
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

/-- The counit isomorphism for enveloping-module restriction.

The enveloping module associated to the Lie restriction of a `U_R(L)`-module `M` is isomorphic
to `M` by identity functions on its carrier. -/
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

/-- Naturality of the Lie-module unit isomorphism.

The identity functor on Lie modules is naturally isomorphic to representation followed by
restriction, with the carrier-identity unit as its components. -/
def unitNatIso :
    𝟭 (LieModuleCat.{w} R L) ≅ representFunctor R L ⋙ restrictFunctor R L :=
  NatIso.ofComponents (unitIso R L) (by
    intro M N f
    apply LieModuleHom.ext
    intro m
    rfl)

/-- Naturality of the enveloping-module counit isomorphism.

Restriction followed by representation is naturally isomorphic to the identity functor on
`U_R(L)`-modules, with the carrier-identity counit as its components. -/
def counitNatIso :
    restrictFunctor R L ⋙ representFunctor R L ≅ 𝟭 (ModuleCat.{w} U) :=
  NatIso.ofComponents (counitIso R L) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl)

/-- The equivalence of Lie modules and enveloping-algebra modules.

For a commutative ring `R` and an `R`-Lie algebra `L`, extension of the Lie representation and
restriction along `ι` give an equivalence `LieModuleCat R L ≌ ModuleCat (U_R(L))` in each
coefficient universe. -/
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

/-- The coefficient formula for the Lie-module unit.

The forward unit isomorphism sends every coefficient element `m` to itself. -/
@[simp]
theorem unitIso_hom_apply (M : LieModuleCat.{w} R L) (m : M) :
    (unitIso R L M).hom m = m := rfl

/-- The coefficient formula for the enveloping-module counit.

The forward counit isomorphism sends every coefficient element `m` to itself. -/
@[simp]
theorem counitIso_hom_apply (M : ModuleCat.{w} U)
    (m : representObj R L (restrictObj R L M)) :
    (counitIso R L M).hom.hom m = m := rfl

/-- Uniqueness of the representation extending a Lie action.

If an `R`-algebra homomorphism `ρ : U_R(L) → End_R(M)` satisfies `ρ(ι(x))(m) = [x,m]` for all
`x ∈ L` and `m ∈ M`, it equals the universal extended representation. -/
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

/-- The Lie-module map recovered from an enveloping-linear map.

A morphism between the enveloping modules associated to `M` and `N` defines a Lie-module map
by restriction and the unit isomorphisms. -/
def toLieMap {M N : LieModuleCat.{w} R L}
    (f : representObj R L M ⟶ representObj R L N) : M ⟶ N :=
  (unitIso R L M).hom ≫ restrictMap R L f ≫ (unitIso R L N).inv

/-- The value of a recovered Lie-module map.

For an enveloping-linear map `f` between represented modules, its recovered Lie-module map has
value `f.hom(m)`. -/
@[simp]
theorem toLieMap_apply {M N : LieModuleCat.{w} R L}
    (f : representObj R L M ⟶ representObj R L N) (m : M) :
    toLieMap R L f m = f.hom m := rfl

/-- The hom-set bijection between Lie maps and enveloping-linear maps.

For Lie modules `M` and `N`, extending and restricting maps give a bijection between `M ⟶ N`
and the `U_R(L)`-linear morphisms of their associated enveloping modules. Both directions
retain coefficient values. -/
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

/-- Additivity of the enveloping representation functor.

Passing from Lie-module maps to enveloping-linear maps preserves addition. -/
instance representFunctor_additive : (representFunctor R L).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

/-- Additivity of enveloping-module Lie restriction.

Restricting `U_R(L)`-module maps to Lie-module maps preserves addition. -/
instance restrictFunctor_additive : (restrictFunctor R L).Additive where
  map_add {M N} f g := by
    apply LieModuleHom.ext
    intro m
    rfl

/-- The scalar-module comparison after enveloping restriction.

Lie restriction followed by forgetting the Lie action is naturally isomorphic to scalar
restriction along `R → U_R(L)`, with identity component maps. -/
def restrictForgetIso : restrictFunctor R L ⋙ LieModuleCat.forget R L ≅
    ModuleCat.restrictScalars (algebraMap R U) :=
  NatIso.ofComponents (fun M => Iso.refl _) (by
    intro M N f
    rfl)

end LieModuleCat.UniversalEnveloping
