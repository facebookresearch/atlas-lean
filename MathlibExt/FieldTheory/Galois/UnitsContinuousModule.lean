/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Action.DiscreteAbelian
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Topology.Algebra.MulAction

/-!
# Discrete Galois modules of field units

For a Galois extension L/K, write the abelian group Lˣ additively and lift its carrier to the
specified coefficient universe. The coefficient module is a discrete ℤ-module: multiplication,
inversion and integer powers of units become addition, negation and integer scalar
multiplication. A Galois automorphism acts by its usual map on units. Each unit lies in a
finite Galois intermediate field, so its stabilizer is open and the action is continuous in
the Krull topology.

Compatible embeddings K → K′ and L → L′ induce restriction Gal(L′/K′) → Gal(L/K),
characterized by e(g|L(x)) = g(e(x)). With both extensions Galois this restriction is
continuous. The extension embedding induces a continuous equivariant ℤ-linear map from the
restricted source unit module to the target unit module. These maps obey identity and
composition laws and commute with changing the coefficient lift height, with all field
universes independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Topology
universe u v w a b c d

namespace GaloisUnits
variable (K : Type u) (L : Type v) [Field L]

/-- The lifted additive group of field units.

For a field L, this carrier is ULift (Additive Lˣ) at the stated coefficient height. Addition
represents multiplication of units, and integer scalar multiplication represents integer
powers. The type parameter K determines a universe height but requires no field structure in
this definition. -/
abbrev Carrier (_K : Type u) (L : Type v) [Field L] :=
  ULift.{max u w} (Additive Lˣ)

/-- A unit in the lifted additive carrier.

Send a unit a ∈ Lˣ to ULift.up (Additive.ofMul a) in Carrier K L. -/
def up (a : Lˣ) : Carrier.{u, v, w} K L := ULift.up (Additive.ofMul a)
/-- The unit underlying a lifted additive element.

For x ∈ Carrier K L, remove the universe lift and the additive notation to recover an element
of Lˣ. -/
def down (x : Carrier.{u, v, w} K L) : Lˣ := x.down.toMul

/-- Removing the lift of a unit.

For a ∈ Lˣ, down(up(a)) = a. -/
@[simp] theorem down_up (a : Lˣ) : down K L (up.{u, v, w} K L a) = a := rfl
/-- Reconstructing a lifted unit element.

For x ∈ Carrier K L, up(down(x)) = x. -/
@[simp] theorem up_down (x : Carrier.{u, v, w} K L) : up K L (down K L x) = x := rfl

/-- The discrete topology on the additive unit carrier.

Carrier K L is given the bottom topology, so every subset is open. -/
instance carrierTopology : TopologicalSpace (Carrier.{u, v, w} K L) := ⊥
/-- Discreteness of the unit coefficient topology.

The selected topology on Carrier K L is discrete. -/
instance carrierDiscrete : DiscreteTopology (Carrier.{u, v, w} K L) := ⟨rfl⟩

variable [Field K] [Algebra K L]

/-- The Galois action on lifted field units.

For an extension L/K, a K-automorphism g acts by mapping the underlying unit through g and
lifting it back to Carrier K L. This action preserves the additive group structure. -/
instance carrierAction : DistribMulAction Gal(L/K) (Carrier.{u, v, w} K L) where
  smul g x := up K L (Units.map g.toRingEquiv.toMonoidHom (down K L x))
  one_smul x := by
    apply ULift.ext
    apply Units.ext
    rfl
  mul_smul g h x := by
    apply ULift.ext
    apply Units.ext
    rfl
  smul_zero g := by
    apply ULift.ext
    apply Units.ext
    exact map_one g
  smul_add g x y := by
    apply ULift.ext
    apply Units.ext
    exact map_mul g (down K L x).val (down K L y).val

/-- The Galois action on a lifted unit.

For g ∈ Gal(L/K) and a ∈ Lˣ, g·up(a) = up(Units.map(g)(a)). -/
@[simp] theorem action_up (g : Gal(L/K)) (a : Lˣ) :
    g • up.{u, v, w} K L a = up K L (Units.map g.toRingEquiv.toMonoidHom a) := rfl

/-- Field values of the Galois unit action.

For x ∈ Carrier K L, the value in L of down(g·x) equals g applied to the value of down(x). -/
@[simp] theorem down_action_val (g : Gal(L/K)) (x : Carrier.{u, v, w} K L) :
    (down K L (g • x)).val = g (down K L x).val := rfl

variable [IsGalois K L]

/-- A finite Galois intermediate field containing a unit.

For a Galois extension L/K and a ∈ Lˣ, this is the finite Galois intermediate field generated
by the singleton containing the value of a. -/
def unitField (a : Lˣ) : FiniteGaloisIntermediateField K L :=
  FiniteGaloisIntermediateField.adjoin K ({a.val} : Set L)

/-- The unit value belongs to its finite Galois field.

For a ∈ Lˣ, its value lies in the intermediate field unitField K L a. -/
theorem unit_mem_field (a : Lˣ) : a.val ∈ (unitField K L a).toIntermediateField :=
  FiniteGaloisIntermediateField.subset_adjoin K ({a.val} : Set L) (by simp)

/-- Fixing a unit field fixes the unit coefficient.

The fixing subgroup of unitField K L a is contained in the stabilizer of up(a) for the Galois
action on Carrier K L. -/
theorem fixing_le_stabilizer (a : Lˣ) :
    (unitField K L a).fixingSubgroup ≤
      MulAction.stabilizer Gal(L/K) (up.{u, v, w} K L a) := by
  intro g hg
  change g • up K L a = up K L a
  apply ULift.ext
  apply Units.ext
  exact (IntermediateField.mem_fixingSubgroup_iff _ g).mp hg a.val (unit_mem_field K L a)

/-- Open stabilizers of lifted units.

For a Galois extension L/K and x ∈ Carrier K L, the stabilizer of x is open in the Krull
topology on Gal(L/K). -/
theorem stabilizer_open (x : Carrier.{u, v, w} K L) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
  convert stabilizer_isOpen_of_isIntegral (K := K) (L := L) (down K L x).val using 1
  ext g
  change (g • x = x) ↔ g (down K L x).val = (down K L x).val
  constructor
  · intro h
    exact congrArg (fun y => (down K L y).val) h
  · intro h
    apply ULift.ext
    apply Units.ext
    exact h

/-- Continuity of the Galois action on discrete units.

For a Galois extension L/K, the action Gal(L/K) × Carrier K L → Carrier K L is continuous,
since each coefficient element has an open stabilizer. -/
instance carrierContinuousAction : ContinuousSMul Gal(L/K) (Carrier.{u, v, w} K L) :=
  (continuousSMul_iff_stabilizer_isOpen).mpr (stabilizer_open K L)

/-- The discrete Galois module of field units.

For a Galois extension L/K, bundle the lifted additive group of Lˣ, its discrete topology and
its continuous Galois action as a discrete abelian module. The coefficient height accommodates
the independent base-field, extension-field and lift universes. -/
def moduleObj : DiscreteAbelianAction.{v, max u (max v w)} Gal(L/K) :=
  DiscreteAbelianAction.of Gal(L/K) (Carrier.{u, v, w} K L)

/-- The carrier of the bundled unit module.

The underlying type of moduleObj K L is Carrier K L at the specified universe height. -/
theorem module_carrier :
    (DiscreteAbelianAction.underlying (moduleObj.{u, v, w} K L) : Type _) =
      Carrier.{u, v, w} K L := rfl

end GaloisUnits


namespace GaloisUnits

/-- Compatible embeddings of two field extensions.

A field-extension map consists of embeddings K → K′ and L → L′ whose square with the two
algebra maps commutes. The four fields may lie in independent universes. -/
structure FieldMap (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (K' : Type a) (L' : Type b) [Field K'] [Field L'] [Algebra K' L'] where
  /-- The base-field embedding of a field-extension map.

This component is the ring homomorphism K → K′ in the commuting field-extension square. -/
  base : K →+* K'
  /-- The extension-field embedding of a field-extension map.

This component is the ring homomorphism L → L′ in the commuting field-extension square. -/
  extension : L →+* L'
/-- The scalar square of the field embeddings.

The extension embedding composed with K → L equals the base embedding composed with K′ → L′. -/
  comm : extension.comp (algebraMap K L) = (algebraMap K' L').comp base

namespace FieldMap
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {K' : Type a} {L' : Type b} [Field K'] [Field L'] [Algebra K' L']

/-- The scalar square evaluated at a base-field element.

For x ∈ K, the extension embedding sends algebraMap K L x to algebraMap K′ L′ applied to the
base image of x. -/
@[simp] theorem comm_apply (e : FieldMap K L K' L') (x : K) :
    e.extension (algebraMap K L x) = algebraMap K' L' (e.base x) :=
  congrArg (fun f : K →+* L' => f x) e.comm

variable [IsGalois K L]

/-- Restriction of an automorphism along field embeddings.

For a compatible embedding pair e and a Galois source extension L/K, an automorphism of L′/K′
restricts to an automorphism of L/K. Normality of the source extension makes the image of L
stable. -/
def restrictElem (e : FieldMap K L K' L') (g : Gal(L'/K')) : Gal(L/K) := by
  letI : Algebra K K' := e.base.toAlgebra
  letI : Algebra K L' := ((algebraMap K' L').comp e.base).toAlgebra
  letI : Algebra L L' := e.extension.toAlgebra
  letI : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq' e.comm.symm
  exact (g.restrictScalars K).restrictNormal L

/-- The field-value equation for restricted automorphisms.

For g ∈ Gal(L′/K′) and x ∈ L, e.extension(restrictElem(e,g)(x)) = g(e.extension(x)). -/
theorem restrictElem_comm (e : FieldMap K L K' L') (g : Gal(L'/K')) (x : L) :
    e.extension (restrictElem e g x) = g (e.extension x) := by
  let : Algebra K K' := e.base.toAlgebra
  let : Algebra K L' := ((algebraMap K' L').comp e.base).toAlgebra
  let : Algebra L L' := e.extension.toAlgebra
  let : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq' e.comm.symm
  change algebraMap L L' ((g.restrictScalars K).restrictNormal L x) =
    (g.restrictScalars K) (algebraMap L L' x)
  exact AlgEquiv.restrictNormal_commutes _ _ _

/-- The homomorphism restricting Galois automorphisms.

A compatible field-extension embedding with Galois source L/K gives a group homomorphism
Gal(L′/K′) → Gal(L/K) by restricting automorphisms. -/
def restrictHom (e : FieldMap K L K' L') : Gal(L'/K') →* Gal(L/K) where
  toFun := restrictElem e
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply e.extension.injective
    rw [restrictElem_comm]
    rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    apply e.extension.injective
    change e.extension (restrictElem e (g * h) x) =
      e.extension (restrictElem e g (restrictElem e h x))
    rw [restrictElem_comm, restrictElem_comm, restrictElem_comm]
    rfl

/-- Coordinates of the Galois restriction homomorphism.

For every g ∈ Gal(L′/K′) and x ∈ L, applying e.extension after restriction agrees with
applying g after e.extension. -/
@[simp] theorem restrictHom_comm (e : FieldMap K L K' L') (g : Gal(L'/K')) (x : L) :
    e.extension (restrictHom e g x) = g (e.extension x) := restrictElem_comm e g x

variable [IsGalois K' L']

/-- Krull continuity of Galois restriction.

For compatible embeddings between Galois extensions L/K and L′/K′, the restriction
homomorphism Gal(L′/K′) → Gal(L/K) is continuous for their Krull topologies. -/
theorem restrictHom_continuous (e : FieldMap K L K' L') : Continuous (restrictHom e) := by
  apply continuous_of_continuousAt_one (restrictHom e)
  apply continuousAt_def.mpr
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K L U).mp hU
  let : FiniteDimensional K E := hE
  let basis := Module.finBasis K E
  let F := FiniteGaloisIntermediateField.adjoin K'
    (Set.range (fun i => e.extension ((basis i : E) : L)))
  have hF : (F.fixingSubgroup : Set Gal(L'/K')) ∈ 𝓝 (1 : Gal(L'/K')) :=
    (F.toIntermediateField.fixingSubgroup_isOpen).mem_nhds F.fixingSubgroup.one_mem
  apply Filter.mem_of_superset hF
  intro g hg
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E (restrictHom e g)).mpr
  intro x hx
  have hb (i : Fin (Module.finrank K E)) :
      restrictHom e g ((basis i : E) : L) = ((basis i : E) : L) := by
    apply e.extension.injective
    rw [restrictHom_comm]
    apply (IntermediateField.mem_fixingSubgroup_iff F.toIntermediateField g).mp hg
    exact FiniteGaloisIntermediateField.subset_adjoin K' _ (Set.mem_range_self i)
  have hlin : (restrictHom e g).toLinearMap.comp E.val.toLinearMap = E.val.toLinearMap :=
    basis.ext hb
  exact congrArg (fun f : E →ₗ[K] L => f ⟨x, hx⟩) hlin

/-- The continuous Galois restriction homomorphism.

For a map between Galois extensions, bundle restriction Gal(L′/K′) → Gal(L/K) with its Krull
continuity. -/
def restrictContinuous (e : FieldMap K L K' L') : Gal(L'/K') →ₜ* Gal(L/K) :=
  ⟨restrictHom e, restrictHom_continuous e⟩

end FieldMap
end GaloisUnits



namespace GaloisUnits

section Operations
variable (K : Type u) (L : Type v) [Field L]
/-- The multiplicative unit becomes additive zero.

The lifted element up(1) equals 0 in Carrier K L. -/
@[simp] theorem up_one : up.{u, v, w} K L 1 = 0 := rfl
/-- Multiplication of units becomes addition.

For x,y ∈ Lˣ, up(xy) = up(x) + up(y). -/
@[simp] theorem up_mul (x y : Lˣ) :
    up.{u, v, w} K L (x * y) = up K L x + up K L y := rfl
/-- Inversion of units becomes negation.

For x ∈ Lˣ, up(x⁻¹) = −up(x). -/
@[simp] theorem up_inv (x : Lˣ) : up.{u, v, w} K L x⁻¹ = -up K L x := rfl
/-- Integer powers become integer scalar multiplication.

For x ∈ Lˣ and n ∈ ℤ, up(xⁿ) = n·up(x) in the additive unit module. -/
@[simp] theorem up_zpow (x : Lˣ) (n : ℤ) :
    up.{u, v, w} K L (x ^ n) = n • up K L x := rfl
end Operations


namespace FieldMap
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {K' : Type a} {L' : Type b} [Field K'] [Field L'] [Algebra K' L']
variable {K'' : Type c} {L'' : Type d} [Field K''] [Field L''] [Algebra K'' L'']

/-- The identity map of a field extension.

The identity field-extension map L/K → L/K has identity base and extension embeddings. -/
def id (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : FieldMap K L K L where
  base := RingHom.id K
  extension := RingHom.id L
  comm := rfl

/-- Composition of compatible field-extension embeddings.

For e : (L/K) → (L′/K′) and f : (L′/K′) → (L″/K″), compose the base embeddings and the
extension embeddings in that order. Their scalar squares compose. -/
def comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    FieldMap K L K'' L'' where
  base := f.base.comp e.base
  extension := f.extension.comp e.extension
  comm := by
    ext x
    change f.extension (e.extension (algebraMap K L x)) =
      algebraMap K'' L'' (f.base (e.base x))
    rw [e.comm_apply, f.comm_apply]

/-- The additive unit map induced by an extension embedding.

Apply e.extension to the underlying unit, then lift its image to the target additive unit
carrier. This additive homomorphism uses the common coefficient height containing all stated
field and lift universes. -/
def coefficientAddHom (e : FieldMap K L K' L') :
    Carrier.{u, v, max a (max b w)} K L →+
      Carrier.{a, b, max u (max v w)} K' L' where
  toFun x :=
    up.{a, b, max u (max v w)} K' L'
      (Units.map e.extension.toMonoidHom (down.{u, v, max a (max b w)} K L x))
  map_zero' := by
    apply ULift.ext
    apply Units.ext
    exact map_one e.extension
  map_add' x y := by
    apply ULift.ext
    apply Units.ext
    exact map_mul e.extension
      (down.{u, v, max a (max b w)} K L x).val (down.{u, v, max a (max b w)} K L y).val

/-- The induced additive map on lifted units.

For x ∈ Lˣ, the unit coefficient map sends up(x) to up(Units.map(e.extension)(x)) in the
target carrier. -/
@[simp] theorem coefficientAddHom_up (e : FieldMap K L K' L') (x : Lˣ) :
    coefficientAddHom.{u, v, w, a, b} e (up.{u, v, max a (max b w)} K L x) =
      up.{a, b, max u (max v w)} K' L' (Units.map e.extension.toMonoidHom x) := rfl

/-- The underlying unit of an induced coefficient image.

Removing the target lift from the additive coefficient image of x gives
Units.map(e.extension)(down(x)). -/
@[simp] theorem down_coefficientAddHom (e : FieldMap K L K' L')
    (x : Carrier.{u, v, max a (max b w)} K L) :
    down.{a, b, max u (max v w)} K' L' (coefficientAddHom.{u, v, w, a, b} e x) =
      Units.map e.extension.toMonoidHom (down.{u, v, max a (max b w)} K L x) := rfl

variable [IsGalois K L] [IsGalois K' L'] [IsGalois K'' L'']

/-- Restriction along identity field embeddings.

For g ∈ Gal(L/K), restricting g along the identity field-extension map returns g. -/
@[simp] theorem restrictHom_id (g : Gal(L/K)) : restrictHom (id K L) g = g := by
  apply AlgEquiv.ext
  intro x
  exact restrictHom_comm (id K L) g x

omit [IsGalois K'' L''] in
/-- Contravariant composition of Galois restriction.

For composable field-extension embeddings e and f, restriction along f ∘ e sends g to
restrict(e,restrict(f,g)). The equation needs Galois source and middle extensions, with the
target automorphism group as stated. -/
theorem restrictHom_comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L')
    (g : Gal(L''/K'')) : restrictHom (comp f e) g = restrictHom e (restrictHom f g) := by
  apply AlgEquiv.ext
  intro x
  apply e.extension.injective
  apply f.extension.injective
  exact (restrictHom_comm (comp f e) g x).trans
    ((congrArg f.extension (restrictHom_comm e (restrictHom f g) x)).trans
      (restrictHom_comm f g (e.extension x))).symm

omit [IsGalois K' L'] in
/-- Uniqueness from the restriction value equation.

A group homomorphism ρ : Gal(L′/K′) → Gal(L/K) satisfying e.extension(ρ(g)(x)) =
g(e.extension(x)) for every g and x equals the restriction homomorphism. -/
theorem restrictHom_unique (e : FieldMap K L K' L') (ρ : Gal(L'/K') →* Gal(L/K))
    (hρ : ∀ (g : Gal(L'/K')) (x : L), e.extension (ρ g x) = g (e.extension x)) :
    ρ = restrictHom e := by
  ext g x
  apply e.extension.injective
  exact (hρ g x).trans (restrictHom_comm e g x).symm

/-- The unit module restricted along the Galois map.

This is the lifted additive unit module of L, regarded as a Gal(L′/K′)-module via the
continuous restriction induced by e. -/
abbrev sourceModule (e : FieldMap K L K' L') :
    DiscreteAbelianAction.{b, max u (max v (max a (max b w)))} Gal(L'/K') :=
  (restrictModules (restrictContinuous e)).obj
    (moduleObj.{u, v, max a (max b w)} K L)

/-- The target unit module for an extension embedding.

This is the lifted additive unit module of L′ with its Gal(L′/K′)-action, at the common
coefficient height of the field-extension diagram. -/
abbrev targetModule (_e : FieldMap K L K' L') :
    DiscreteAbelianAction.{b, max u (max v (max a (max b w)))} Gal(L'/K') :=
  moduleObj.{a, b, max u (max v w)} K' L'

/-- Equivariance of the induced additive unit map.

The unit map induced by e.extension intertwines the restricted Gal(L′/K′)-action on source
units with the Galois action on target units, by the automorphism restriction equation. -/
def coefficientEquivariant (e : FieldMap K L K' L') :
    DiscreteAbelianAction.EquivariantAddHom (sourceModule.{u, v, w, a, b} e)
      (targetModule.{u, v, w, a, b} e) :=
  ⟨coefficientAddHom.{u, v, w, a, b} e, fun h x => by
    apply ULift.ext
    apply Units.ext
    exact restrictHom_comm e h (down.{u, v, max a (max b w)} K L x).val⟩

/-- The continuous equivariant unit coefficient morphism.

The additive unit map induced by e.extension is a morphism from the restricted source unit
module to the target unit module. It is continuous and ℤ-linear on the stated lifted carriers. -/
def coefficientMap (e : FieldMap K L K' L') :
    sourceModule.{u, v, w, a, b} e ⟶ targetModule.{u, v, w, a, b} e :=
  DiscreteAbelianAction.ofAddHom (coefficientEquivariant.{u, v, w, a, b} e)

/-- The additive map underlying the coefficient morphism.

Forgetting the bundled continuous module morphism coefficientMap e gives coefficientAddHom e. -/
@[simp] theorem coefficientMap_addHom (e : FieldMap K L K' L') :
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) =
      coefficientAddHom.{u, v, w, a, b} e := rfl

/-- Unit coordinates of the bundled coefficient morphism.

On up(x) for x ∈ Lˣ, the bundled coefficient morphism returns the target lift of
Units.map(e.extension)(x). -/
theorem coefficientMap_up (e : FieldMap K L K' L') (x : Lˣ) :
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
      (up.{u, v, max a (max b w)} K L x) =
      up.{a, b, max u (max v w)} K' L' (Units.map e.extension.toMonoidHom x) := rfl

/-- Integer linearity of the coefficient morphism.

For n ∈ ℤ and a source coefficient element x, the coefficient morphism satisfies f(n·x) =
n·f(x). -/
theorem coefficientMap_int (e : FieldMap K L K' L') (n : ℤ)
    (x : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e)) :
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) (n • x) =
      n • DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) x :=
  (coefficientMap.{u, v, w, a, b} e).hom.hom.hom.hom.map_smul n x

/-- Continuity of the coefficient morphism on carriers.

The additive function underlying coefficientMap e is continuous between the discrete unit
coefficient carriers. -/
theorem coefficientMap_continuous (e : FieldMap K L K' L') :
    Continuous (DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)) :=
  (coefficientMap.{u, v, w, a, b} e).hom.hom.hom.hom.continuous

end FieldMap
end GaloisUnits


universe r
namespace GaloisUnits


section UniverseComparisons
variable (K : Type u) (L : Type v) [Field L]

/-- The additive equivalence between coefficient heights.

Two lifts of Additive Lˣ at the stated heights are additively equivalent by removing one lift
and inserting the other. Their underlying unit is unchanged. -/
def universeEquiv : Carrier.{u, v, w} K L ≃+ Carrier.{u, v, a} K L where
  toFun x := up.{u, v, a} K L (down.{u, v, w} K L x)
  invFun x := up.{u, v, w} K L (down.{u, v, a} K L x)
  left_inv _x := rfl
  right_inv _x := rfl
  map_add' _x _y := rfl

/-- Lifted unit values under a change of height.

The coefficient-height equivalence sends up(x) at the source height to up(x) at the target
height. -/
@[simp] theorem universeEquiv_up (x : Lˣ) :
    universeEquiv.{u, v, w, a} K L (up K L x) = up K L x := rfl
/-- Underlying units under a change of height.

Removing the lift after the coefficient-height equivalence gives the same unit as removing the
source lift. -/
@[simp] theorem universeEquiv_down (x : Carrier.{u, v, w} K L) :
    down K L (universeEquiv.{u, v, w, a} K L x) = down K L x := rfl
/-- An unchanged coefficient height gives the identity.

The additive universe comparison from a height to itself is the identity equivalence of
Carrier K L. -/
@[simp] theorem universeEquiv_id : universeEquiv.{u, v, w, w} K L =
    AddEquiv.refl (Carrier.{u, v, w} K L) := rfl
/-- Composition of coefficient-height equivalences.

Changing the lift height from w to a and then from a to b equals the direct additive
comparison from w to b. -/
@[simp] theorem universeEquiv_comp :
    (universeEquiv.{u, v, w, a} K L).trans (universeEquiv.{u, v, a, b} K L) =
      universeEquiv.{u, v, w, b} K L := rfl

/-- The continuous integer-linear coefficient-height equivalence.

The additive comparison between two lifted copies of Lˣ is a continuous ℤ-linear equivalence.
Its inverse is continuous because both coefficient carriers are discrete. -/
def universeContinuousEquiv : Carrier.{u, v, w} K L ≃L[ℤ] Carrier.{u, v, a} K L where
  toLinearEquiv :=
    { __ := universeEquiv.{u, v, w, a} K L
      map_smul' := fun n x => map_zsmul (universeEquiv.{u, v, w, a} K L) n x }
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

variable [Field K] [Algebra K L]
/-- Changing coefficient height commutes with the Galois action.

For g ∈ Gal(L/K), the additive universe equivalence sends g·x to g times the image of x. -/
@[simp] theorem universeEquiv_action (g : Gal(L/K)) (x : Carrier.{u, v, w} K L) :
    universeEquiv.{u, v, w, a} K L (g • x) =
      g • universeEquiv.{u, v, w, a} K L x := rfl
end UniverseComparisons

section ActualFieldModule
variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The Krull-topological Galois group as a profinite group.

For a Galois extension L/K, this is the profinite group of K-automorphisms of L with the Krull
topology. -/
def profiniteGroup := InfiniteGalois.profiniteGalGrp K L
/-- The carrier of the profinite Galois group.

The underlying group type of profiniteGroup K L is Gal(L/K). -/
@[simp] theorem profiniteGroup_carrier : (profiniteGroup K L : Type v) = Gal(L/K) := rfl

/-- The fixing subgroup of a unit field is open.

For a unit x ∈ Lˣ, the fixing subgroup of its finite Galois intermediate field is open in
Gal(L/K) with the Krull topology. -/
theorem unitField_fixing_open (x : Lˣ) : IsOpen ((unitField K L x).fixingSubgroup : Set Gal(L/K)) :=
  (unitField K L x).toIntermediateField.fixingSubgroup_isOpen

/-- A unit of its finite Galois intermediate field.

The unit x ∈ Lˣ defines a unit in unitField K L x, with the same nonzero field value. -/
def unitInField (x : Lˣ) : (unitField K L x).toIntermediateFieldˣ :=
  Units.mk0 ⟨x.val, unit_mem_field K L x⟩ (by
    intro h
    exact x.ne_zero (congrArg Subtype.val h))

/-- Embedding the intermediate-field unit back into the extension.

Mapping unitInField K L x along the intermediate-field inclusion into L recovers x ∈ Lˣ. -/
theorem unitInField_val (x : Lˣ) :
    Units.map (unitField K L x).toIntermediateField.val.toMonoidHom (unitInField K L x) = x := by
  apply Units.ext
  rfl

/-- Coordinates of the bundled Galois module action.

The action morphism of g on moduleObj K L sends up(x) to the lift of the unit obtained by
applying g to x. -/
@[simp] theorem module_action_up (g : Gal(L/K)) (x : Lˣ) :
    ((moduleObj.{u, v, w} K L).obj.obj.ρ g).asHom.hom (up K L x) =
      up K L (Units.map g.toRingEquiv.toMonoidHom x) := rfl

/-- Integer linearity of each Galois action morphism.

The bundled action endomorphism associated to g preserves integer scalar multiplication:
ρ(g)(n·x) = n·ρ(g)(x). -/
theorem module_action_int (g : Gal(L/K)) (n : ℤ)
    (x : DiscreteAbelianAction.underlying (moduleObj.{u, v, w} K L)) :
    ((moduleObj K L).obj.obj.ρ g).asHom.hom (n • x) =
      n • ((moduleObj K L).obj.obj.ρ g).asHom.hom x :=
  ((moduleObj K L).obj.obj.ρ g).asHom.hom.map_smul n x
end ActualFieldModule

namespace FieldMap
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {K' : Type a} {L' : Type b} [Field K'] [Field L'] [Algebra K' L']
variable {K'' : Type c} {L'' : Type d} [Field K''] [Field L''] [Algebra K'' L'']

/-- The additive coefficient map for an identity embedding.

The unit map induced by identity field embeddings is the identity additive homomorphism of the
common-height coefficient carrier. -/
@[simp] theorem coefficientAddHom_id :
    coefficientAddHom.{u, v, w, u, v} (id K L) =
      AddMonoidHom.id (Carrier.{u, v, max u (max v w)} K L) := by
  ext x
  rfl

/-- Composition of additive unit coefficient maps.

For composable e and f, applying their unit coefficient maps successively equals the
coefficient map induced by f ∘ e, at the common height of the whole diagram. -/
theorem coefficientAddHom_comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    (coefficientAddHom.{a, b, max u (max v w), c, d} f).comp
        (coefficientAddHom.{u, v, max c (max d w), a, b} e) =
      coefficientAddHom.{u, v, max a (max b w), c, d} (comp f e) := by
  ext x
  rfl

/-- The coefficient-height square for field embeddings.

Changing the target coefficient height after applying the additive unit map equals first
changing the source height and then applying the unit map for e at the new height. -/
theorem coefficientAddHom_universe (e : FieldMap K L K' L')
    (x : Carrier.{u, v, max a (max b w)} K L) :
    universeEquiv.{a, b, max u (max v w), max u (max v r)} K' L'
        (coefficientAddHom.{u, v, w, a, b} e x) =
      coefficientAddHom.{u, v, r, a, b} e
        (universeEquiv.{u, v, max a (max b w), max a (max b r)} K L x) := rfl

variable [IsGalois K L] [IsGalois K' L']
/-- The continuous restriction map for identity embeddings.

The continuous Galois restriction along the identity field-extension map is the identity
continuous group homomorphism. -/
@[simp] theorem restrictContinuous_id : restrictContinuous (id K L) =
    ContinuousMonoidHom.id Gal(L/K) := by
  ext g x
  exact congrArg (fun f : Gal(L/K) => f x) (restrictHom_id g)

variable [IsGalois K'' L'']
/-- Composition of continuous Galois restriction maps.

For composable e and f between Galois extensions, restriction along f ∘ e equals restriction
along f followed by restriction along e. -/
theorem restrictContinuous_comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    restrictContinuous (comp f e) = (restrictContinuous e).comp (restrictContinuous f) := by
  ext g x
  exact congrArg (fun h : Gal(L/K) => h x) (restrictHom_comp f e g)

/-- Identification of the source for an identity coefficient map.

Restriction along the identity Galois map canonically identifies the source unit module of the
identity field embedding with its target unit module. This isomorphism is the identity on unit
elements. -/
def coefficientIdentitySourceIso : sourceModule.{u, v, w, u, v} (id K L) ≅
    targetModule.{u, v, w, u, v} (id K L) :=
  (restrictModulesCongr _ _ (restrictContinuous_id (K := K) (L := L))).app
      (moduleObj.{u, v, max u (max v w)} K L) ≪≫
    restrictModulesId.app (moduleObj.{u, v, max u (max v w)} K L)

/-- The bundled coefficient map for identity embeddings.

The coefficient morphism induced by the identity field-extension map equals the forward
morphism of the canonical identity-source isomorphism. -/
@[simp] theorem coefficientMap_id : coefficientMap.{u, v, w, u, v} (id K L) =
    coefficientIdentitySourceIso.hom := by
  apply (DiscreteAbelianAction.forget Gal(L/K)).map_injective
  ext x
  rfl

/-- Identification of iterated restriction sources.

For e and f, the unit module restricted along the composite Galois map is canonically
isomorphic to the source for e restricted along the Galois map for f. This comparison
preserves coefficient elements. -/
def coefficientCompositionSourceIso (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    sourceModule.{u, v, max a (max b w), c, d} (comp f e) ≅
      (restrictModules (restrictContinuous f)).obj
        (sourceModule.{u, v, max c (max d w), a, b} e) :=
  (restrictModulesCongr _ _ (restrictContinuous_comp f e)).app
      (moduleObj.{u, v, max a (max b (max c (max d w)))} K L) ≪≫
    (restrictModulesComp (restrictContinuous e) (restrictContinuous f)).app
      (moduleObj.{u, v, max a (max b (max c (max d w)))} K L)

/-- Composition of bundled unit coefficient morphisms.

After the canonical source comparison, the restriction of the coefficient morphism for e
followed by the coefficient morphism for f equals the coefficient morphism for f ∘ e. -/
theorem coefficientMap_comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    (coefficientCompositionSourceIso.{u, v, w, a, b, c, d} f e).hom ≫
        (restrictModules (restrictContinuous f)).map
          (coefficientMap.{u, v, max c (max d w), a, b} e) ≫
        coefficientMap.{a, b, max u (max v w), c, d} f =
      coefficientMap.{u, v, max a (max b w), c, d} (comp f e) := by
  apply (DiscreteAbelianAction.forget Gal(L''/K'')).map_injective
  ext x
  rfl
end FieldMap
end GaloisUnits


namespace GaloisUnits

section ClosureSpecialization
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
/-- The unit module of a specified separable closure.

For a separable closure Ω/k with both fields in universe u, this is the discrete
Gal(Ω/k)-module of lifted units of Ω at coefficient height max(u,w). -/
def separableClosureModule : DiscreteAbelianAction.{u, max u w} Gal(Ω/k) :=
  moduleObj.{u, u, w} k Ω
/-- Identification of the separable-closure unit module.

The unit module assigned to a specified separable closure Ω/k is moduleObj k Ω at the stated
coefficient height. -/
@[simp] theorem separableClosureModule_eq :
    separableClosureModule.{u, w} k Ω = moduleObj.{u, u, w} k Ω := rfl
end ClosureSpecialization

namespace FieldMap
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {K' : Type a} {L' : Type b} [Field K'] [Field L'] [Algebra K' L']
variable [IsGalois K L] [IsGalois K' L']

/-- Uniqueness of continuous Galois restriction.

A continuous group homomorphism satisfying e.extension(ρ(g)(x)) = g(e.extension(x)) for every
automorphism g and field element x equals the constructed continuous restriction. -/
theorem restrictContinuous_unique (e : FieldMap K L K' L')
    (ρ : Gal(L'/K') →ₜ* Gal(L/K))
    (hρ : ∀ (g : Gal(L'/K')) (x : L), e.extension (ρ g x) = g (e.extension x)) :
    ρ = restrictContinuous e := by
  ext g x
  apply e.extension.injective
  exact (hρ g x).trans (restrictHom_comm e g x).symm

/-- Coordinate laws for restriction and unit coefficient maps.

For a compatible map e between Galois extensions, these laws state the restriction value
equation and uniqueness, source and target unit carriers, unit and inverse coordinates,
equivariance, ℤ-linearity, continuity and compatibility with coefficient-height changes. -/
structure OriginalCoordinateLaws (e : FieldMap K L K' L') : Prop where
/-- The restriction equation in the field-map coordinate laws.

For each g and x, extension of the restricted value equals the target automorphism applied to
e.extension(x). -/
  restriction_values : ∀ (g : Gal(L'/K')) (x : L),
    e.extension (restrictContinuous e g x) = g (e.extension x)
/-- Uniqueness in the field-map coordinate laws.

Any continuous Galois homomorphism obeying the same field-value restriction equation equals
restrictContinuous e. -/
  restriction_unique : ∀ (ρ : Gal(L'/K') →ₜ* Gal(L/K)),
    (∀ (g : Gal(L'/K')) (x : L), e.extension (ρ g x) = g (e.extension x)) →
      ρ = restrictContinuous e
/-- Continuity in the field-map restriction laws.

The constructed Galois restriction is continuous in the Krull topologies. -/
  restriction_continuous : Continuous (restrictContinuous e)
/-- The source carrier in the field-map coordinate laws.

The restricted source coefficient module has the lifted additive unit carrier of L at the
stated common height. -/
  original_source : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e) =
    Carrier.{u, v, max a (max b w)} K L
/-- The target carrier in the field-map coordinate laws.

The target coefficient module has the lifted additive unit carrier of L′ at the stated common
height. -/
  original_target : DiscreteAbelianAction.underlying (targetModule.{u, v, w, a, b} e) =
    Carrier.{a, b, max u (max v w)} K' L'
/-- Unit images in the field-map coordinate laws.

The coefficient morphism sends up(x) to the target lift of Units.map(e.extension)(x). -/
  unit_values : ∀ x : Lˣ,
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
        (up.{u, v, max a (max b w)} K L x) =
      up.{a, b, max u (max v w)} K' L' (Units.map e.extension.toMonoidHom x)
/-- Underlying unit images in the field-map coordinate laws.

Removing the target lift from the coefficient image gives e.extension applied to the source
unit. -/
  down_values : ∀ x : Carrier.{u, v, max a (max b w)} K L,
    down.{a, b, max u (max v w)} K' L'
        (DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) x) =
      Units.map e.extension.toMonoidHom (down.{u, v, max a (max b w)} K L x)
/-- Inverse unit images in the field-map coordinate laws.

The coefficient image of up(x⁻¹) equals the negative of the coefficient image of up(x). -/
  inverse_values : ∀ x : Lˣ,
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
        (up.{u, v, max a (max b w)} K L x⁻¹) =
      -DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
        (up.{u, v, max a (max b w)} K L x)
/-- Equivariance in the field-map coordinate laws.

The coefficient morphism sends g·x in the restricted source module to g times its coefficient
image. -/
  actual_equivariance : ∀ (g : Gal(L'/K'))
    (x : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e)),
    DiscreteAbelianAction.homToAdd (coefficientMap e) (g • x) =
      g • DiscreteAbelianAction.homToAdd (coefficientMap e) x
/-- Integer linearity in the field-map coordinate laws.

The coefficient morphism sends n·x to n times its image for every n ∈ ℤ. -/
  actual_integer_linearity : ∀ (n : ℤ)
    (x : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e)),
    DiscreteAbelianAction.homToAdd (coefficientMap e) (n • x) =
      n • DiscreteAbelianAction.homToAdd (coefficientMap e) x
/-- Coefficient continuity in the field-map coordinate laws.

The additive function underlying the coefficient morphism is continuous. -/
  actual_continuity : Continuous
    (DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e))
/-- The universe square in the field-map coordinate laws.

Changing target coefficient height after the unit map equals changing source height before the
unit map. -/
  coefficient_universe_square : ∀ x : Carrier.{u, v, max a (max b w)} K L,
    universeEquiv.{a, b, max u (max v w), max u (max v r)} K' L'
        (coefficientAddHom.{u, v, w, a, b} e x) =
      coefficientAddHom.{u, v, r, a, b} e
        (universeEquiv.{u, v, max a (max b w), max a (max b r)} K L x)

/-- The restriction and coefficient coordinate laws hold.

Every compatible embedding pair between Galois extensions satisfies all the restriction, unit-
map and coefficient-height formulas collected in OriginalCoordinateLaws. -/
theorem original_coordinate_laws (e : FieldMap K L K' L') :
    OriginalCoordinateLaws.{u, v, w, a, b, r} e where
  restriction_values := restrictHom_comm e
  restriction_unique := restrictContinuous_unique e
  restriction_continuous := (restrictContinuous e).continuous
  original_source := rfl
  original_target := rfl
  unit_values := coefficientMap_up.{u, v, w, a, b} e
  down_values := down_coefficientAddHom.{u, v, w, a, b} e
  inverse_values := fun x => by
    change coefficientAddHom.{u, v, w, a, b} e (-up.{u, v, max a (max b w)} K L x) =
      -coefficientAddHom.{u, v, w, a, b} e (up.{u, v, max a (max b w)} K L x)
    exact map_neg _ _
  actual_equivariance :=
    DiscreteAbelianAction.homToAdd_equivariant (coefficientMap.{u, v, w, a, b} e)
  actual_integer_linearity := coefficientMap_int.{u, v, w, a, b} e
  actual_continuity := coefficientMap_continuous.{u, v, w, a, b} e
  coefficient_universe_square := coefficientAddHom_universe.{u, v, w, a, b, r} e
end FieldMap

/-- Galois unit module and functoriality laws.

For a Galois extension L/K, this collection states the lifted unit coordinates, Galois action
and continuity, finite intermediate-field properties, functorial restriction and coefficient
maps, and coefficient-height equivalences. It also includes the specialization to any
specified separable closure. -/
structure OriginalGaloisUnitsContinuousModuleLaws (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] : Prop where
/-- The underlying carrier in the unit module laws.

The discrete module of units has carrier ULift (Additive Lˣ) at the specified height. -/
  original_carrier : DiscreteAbelianAction.underlying (moduleObj.{u, v, w} K L) =
    Carrier.{u, v, w} K L
/-- The profinite group carrier in the unit module laws.

The underlying type of the profinite Krull-topological group is Gal(L/K). -/
  original_profinite_group : (profiniteGroup K L : Type v) = Gal(L/K)
/-- The unit lifting inverse law.

For x ∈ Lˣ, removing the lift of up(x) returns x. -/
  inverse_down_up : ∀ x : Lˣ, down K L (up.{u, v, w} K L x) = x
/-- The coefficient reconstruction inverse law.

For x in the lifted unit carrier, lifting its underlying unit returns x. -/
  inverse_up_down : ∀ x : Carrier.{u, v, w} K L, up K L (down K L x) = x
/-- The zero coordinate in the unit module laws.

The lifted multiplicative unit is additive zero. -/
  original_one : up.{u, v, w} K L 1 = 0
/-- The product coordinate in the unit module laws.

Lifting xy gives the sum of the lifted units x and y. -/
  original_product : ∀ x y : Lˣ, up.{u, v, w} K L (x * y) = up K L x + up K L y
/-- The inverse coordinate in the unit module laws.

Lifting x⁻¹ gives the negative of the lifted unit x. -/
  original_inverse : ∀ x : Lˣ, up.{u, v, w} K L x⁻¹ = -up K L x
/-- The integer-power coordinate in the unit module laws.

Lifting xⁿ gives n times the lifted unit x for n ∈ ℤ. -/
  original_integer_power : ∀ (x : Lˣ) (n : ℤ), up.{u, v, w} K L (x ^ n) = n • up K L x
/-- The action coordinate in the unit module laws.

The bundled action of g sends a lifted unit to the lift of its image under g. -/
  original_left_action : ∀ (g : Gal(L/K)) (x : Lˣ),
    ((moduleObj.{u, v, w} K L).obj.obj.ρ g).asHom.hom (up K L x) =
      up K L (Units.map g.toRingEquiv.toMonoidHom x)
/-- The identity action law on lifted units.

The identity Galois automorphism fixes every element of the unit coefficient carrier. -/
  action_identity : ∀ x : Carrier.{u, v, w} K L, (1 : Gal(L/K)) • x = x
/-- The composition action law on lifted units.

For g,h ∈ Gal(L/K), (gh)·x = g·(h·x). -/
  action_multiplication : ∀ (g h : Gal(L/K)) (x : Carrier.{u, v, w} K L),
    (g * h) • x = g • (h • x)
/-- The additive action law on lifted units.

For each Galois automorphism g, g·(x+y) = g·x + g·y. -/
  action_addition : ∀ (g : Gal(L/K)) (x y : Carrier.{u, v, w} K L),
    g • (x + y) = g • x + g • y
/-- Integer linearity in the unit action laws.

Each bundled Galois action morphism preserves integer scalar multiplication. -/
  action_integer_linearity : ∀ (g : Gal(L/K)) (n : ℤ)
    (x : DiscreteAbelianAction.underlying (moduleObj.{u, v, w} K L)),
    ((moduleObj K L).obj.obj.ρ g).asHom.hom (n • x) =
      n • ((moduleObj K L).obj.obj.ρ g).asHom.hom x
/-- Finite-field containment in the unit module laws.

Every unit value lies in its associated finite Galois intermediate field. -/
  each_unit_own_field : ∀ x : Lˣ, x.val ∈ (unitField K L x).toIntermediateField
/-- Finite-field unit coordinates in the unit module laws.

Embedding the associated intermediate-field unit into L recovers the given unit. -/
  each_unit_own_field_value : ∀ x : Lˣ,
    Units.map (unitField K L x).toIntermediateField.val.toMonoidHom (unitInField K L x) = x
/-- Open fixing subgroups in the unit module laws.

The fixing subgroup of each unit's finite Galois field is open in the Krull topology. -/
  each_unit_open_fixing : ∀ x : Lˣ, IsOpen ((unitField K L x).fixingSubgroup : Set Gal(L/K))
/-- Fixing subgroup containment in the unit module laws.

The fixing subgroup of a unit's finite field lies in the stabilizer of its lifted coefficient. -/
  each_unit_fixing_stabilizer : ∀ x : Lˣ,
    (unitField K L x).fixingSubgroup ≤ MulAction.stabilizer Gal(L/K) (up.{u, v, w} K L x)
/-- Open coefficient stabilizers in the unit module laws.

Every lifted unit coefficient has an open Galois stabilizer. -/
  each_stabilizer_open : ∀ x : Carrier.{u, v, w} K L,
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K))
/-- Joint Galois action continuity in the unit module laws.

The function (g,x) ↦ g·x from Gal(L/K) times the discrete unit carrier to that carrier is
continuous. -/
  joint_action_continuity : Continuous (fun p : Gal(L/K) × Carrier.{u, v, w} K L => p.1 • p.2)
/-- Functorial coordinates for all compatible field embeddings.

Every compatible embedding into another Galois extension satisfies the restriction and
coefficient-map laws, with target field universes independent of the source. -/
  every_compatible_field_map : ∀ (K' : Type a) (L' : Type b)
    [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L'] (e : FieldMap K L K' L'),
    FieldMap.OriginalCoordinateLaws.{u, v, w, a, b, r} e
/-- The restriction identity in the unit module laws.

Restriction along identity field embeddings is the identity continuous Galois homomorphism. -/
  restriction_identity : FieldMap.restrictContinuous (FieldMap.id K L) =
    ContinuousMonoidHom.id Gal(L/K)
/-- The coefficient identity in the unit module laws.

The unit coefficient morphism of an identity embedding equals the canonical identity-source
comparison. -/
  coefficient_identity : FieldMap.coefficientMap.{u, v, w, u, v} (FieldMap.id K L) =
    FieldMap.coefficientIdentitySourceIso.hom
/-- Restriction composition for all Galois field diagrams.

For every composable pair of compatible embeddings between Galois extensions, the composite
restriction is the contravariant composite of their continuous restriction maps. -/
  every_restriction_composition : ∀ (K' : Type a) (L' : Type b) (K'' : Type c) (L'' : Type d)
    [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L']
    [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
    (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L'),
    FieldMap.restrictContinuous (FieldMap.comp f e) =
      (FieldMap.restrictContinuous e).comp (FieldMap.restrictContinuous f)
/-- Coefficient composition for all Galois field diagrams.

For every composable pair of compatible embeddings, the restricted first unit morphism
followed by the second, with the canonical source comparison, is the unit morphism of the
composite. -/
  every_coefficient_composition : ∀ (K' : Type a) (L' : Type b) (K'' : Type c) (L'' : Type d)
    [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L']
    [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
    (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L'),
    (FieldMap.coefficientCompositionSourceIso.{u, v, w, a, b, c, d} f e).hom ≫
        (restrictModules (FieldMap.restrictContinuous f)).map
          (FieldMap.coefficientMap.{u, v, max c (max d w), a, b} e) ≫
        FieldMap.coefficientMap.{a, b, max u (max v w), c, d} f =
      FieldMap.coefficientMap.{u, v, max a (max b w), c, d} (FieldMap.comp f e)
/-- Unit coordinates in the coefficient-height laws.

Changing the lift height sends each lifted unit to the lift of the same unit. -/
  universe_original_values : ∀ x : Lˣ,
    universeEquiv.{u, v, w, r} K L (up K L x) = up K L x
/-- Underlying unit coordinates in the coefficient-height laws.

Changing the lift height leaves the underlying unit unchanged. -/
  universe_original_down : ∀ x : Carrier.{u, v, w} K L,
    down K L (universeEquiv.{u, v, w, r} K L x) = down K L x
/-- The identity in the coefficient-height laws.

The additive comparison at an unchanged height is the identity equivalence. -/
  universe_identity : universeEquiv.{u, v, w, w} K L = AddEquiv.refl _
/-- Composition in the coefficient-height laws.

Two successive lift-height comparisons equal the direct comparison. -/
  universe_composition :
    (universeEquiv.{u, v, w, r} K L).trans (universeEquiv.{u, v, r, a} K L) =
      universeEquiv.{u, v, w, a} K L
/-- The Galois action square in the coefficient-height laws.

Changing coefficient height commutes with each Galois automorphism action. -/
  universe_action_square : ∀ (g : Gal(L/K)) (x : Carrier.{u, v, w} K L),
    universeEquiv.{u, v, w, r} K L (g • x) = g • universeEquiv.{u, v, w, r} K L x
/-- Continuity in both directions of height comparison.

The ℤ-linear coefficient-height equivalence and its inverse are continuous on the discrete
carriers. -/
  universe_continuity_both : Continuous (universeContinuousEquiv.{u, v, w, r} K L) ∧
    Continuous (universeContinuousEquiv.{u, v, w, r} K L).symm
/-- The specified separable closure in the unit module laws.

For any specified separable closure Ω/k in the stated universe, its unit module is moduleObj k
Ω at coefficient height max(u,w). -/
  chosen_separable_closure : ∀ (k Ω : Type u)
    [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω],
    separableClosureModule.{u, w} k Ω = moduleObj.{u, u, w} k Ω

/-- The unit module laws for every Galois extension.

For every Galois extension L/K, the discrete lifted unit module satisfies the action, finite-
field, restriction, coefficient-map and universe-comparison laws. Compatible field embeddings
and arbitrary coefficient-height changes obey the recorded identity, composition and
coordinate formulas. -/
theorem original_galois_units_continuous_module
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    OriginalGaloisUnitsContinuousModuleLaws.{u, v, w, a, b, c, d, r} K L where
  original_carrier := module_carrier K L
  original_profinite_group := profiniteGroup_carrier K L
  inverse_down_up := down_up K L
  inverse_up_down := up_down K L
  original_one := up_one K L
  original_product := up_mul K L
  original_inverse := up_inv K L
  original_integer_power := up_zpow K L
  original_left_action := module_action_up K L
  action_identity := one_smul Gal(L/K)
  action_multiplication := mul_smul
  action_addition := smul_add
  action_integer_linearity := module_action_int K L
  each_unit_own_field := unit_mem_field K L
  each_unit_own_field_value := unitInField_val K L
  each_unit_open_fixing := unitField_fixing_open K L
  each_unit_fixing_stabilizer := fixing_le_stabilizer K L
  each_stabilizer_open := stabilizer_open K L
  joint_action_continuity := continuous_smul
  every_compatible_field_map := fun _ _ => FieldMap.original_coordinate_laws
  restriction_identity := FieldMap.restrictContinuous_id
  coefficient_identity := FieldMap.coefficientMap_id
  every_restriction_composition := fun _ _ _ _ => FieldMap.restrictContinuous_comp
  every_coefficient_composition := fun _ _ _ _ => FieldMap.coefficientMap_comp
  universe_original_values := universeEquiv_up K L
  universe_original_down := universeEquiv_down K L
  universe_identity := universeEquiv_id K L
  universe_composition := universeEquiv_comp K L
  universe_action_square := universeEquiv_action K L
  universe_continuity_both := ⟨(universeContinuousEquiv K L).continuous,
    (universeContinuousEquiv K L).symm.continuous⟩
  chosen_separable_closure := separableClosureModule_eq

end GaloisUnits
