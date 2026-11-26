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

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Topology
universe u v w a b c d

namespace GaloisUnits
variable (K : Type u) (L : Type v) [Field L]

/-- Exactly one copy of the original additive unit group. -/
abbrev Carrier (_K : Type u) (L : Type v) [Field L] :=
  ULift.{max u w} (Additive Lˣ)

/-- A unit of `L`, as an element of the lifted additive copy `Carrier K L`. -/
def up (a : Lˣ) : Carrier.{u, v, w} K L := ULift.up (Additive.ofMul a)
/-- The unit of `L` underlying an element of `Carrier K L`; inverse to `up`. -/
def down (x : Carrier.{u, v, w} K L) : Lˣ := x.down.toMul

@[simp] theorem down_up (a : Lˣ) : down K L (up.{u, v, w} K L a) = a := rfl
@[simp] theorem up_down (x : Carrier.{u, v, w} K L) : up K L (down K L x) = x := rfl

instance carrierTopology : TopologicalSpace (Carrier.{u, v, w} K L) := ⊥
instance carrierDiscrete : DiscreteTopology (Carrier.{u, v, w} K L) := ⟨rfl⟩

variable [Field K] [Algebra K L]

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

@[simp] theorem action_up (g : Gal(L/K)) (a : Lˣ) :
    g • up.{u, v, w} K L a = up K L (Units.map g.toRingEquiv.toMonoidHom a) := rfl

@[simp] theorem down_action_val (g : Gal(L/K)) (x : Carrier.{u, v, w} K L) :
    (down K L (g • x)).val = g (down K L x).val := rfl

variable [IsGalois K L]

/-- Each original unit has its own actual finite Galois field. -/
def unitField (a : Lˣ) : FiniteGaloisIntermediateField K L :=
  FiniteGaloisIntermediateField.adjoin K ({a.val} : Set L)

theorem unit_mem_field (a : Lˣ) : a.val ∈ (unitField K L a).toIntermediateField :=
  FiniteGaloisIntermediateField.subset_adjoin K ({a.val} : Set L) (by simp)

theorem fixing_le_stabilizer (a : Lˣ) :
    (unitField K L a).fixingSubgroup ≤
      MulAction.stabilizer Gal(L/K) (up.{u, v, w} K L a) := by
  intro g hg
  change g • up K L a = up K L a
  apply ULift.ext
  apply Units.ext
  exact (IntermediateField.mem_fixingSubgroup_iff _ g).mp hg a.val (unit_mem_field K L a)

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

instance carrierContinuousAction : ContinuousSMul Gal(L/K) (Carrier.{u, v, w} K L) :=
  (continuousSMul_iff_stabilizer_isOpen).mpr (stabilizer_open K L)

/-- The fixed actual discrete continuous module; no finiteness of its carrier. -/
def moduleObj : DiscreteAbelianAction.{v, max u (max v w)} Gal(L/K) :=
  DiscreteAbelianAction.of Gal(L/K) (Carrier.{u, v, w} K L)

theorem module_carrier :
    (DiscreteAbelianAction.underlying (moduleObj.{u, v, w} K L) : Type _) =
      Carrier.{u, v, w} K L := rfl

end GaloisUnits


namespace GaloisUnits

/-- Actual compatible embeddings of the original field data. -/
structure FieldMap (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (K' : Type a) (L' : Type b) [Field K'] [Field L'] [Algebra K' L'] where
  /-- The embedding of base fields. -/
  base : K →+* K'
  /-- The embedding of extension fields, compatible with `base` by `comm`. -/
  extension : L →+* L'
  comm : extension.comp (algebraMap K L) = (algebraMap K' L').comp base

namespace FieldMap
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {K' : Type a} {L' : Type b} [Field K'] [Field L'] [Algebra K' L']

@[simp] theorem comm_apply (e : FieldMap K L K' L') (x : K) :
    e.extension (algebraMap K L x) = algebraMap K' L' (e.base x) :=
  congrArg (fun f : K →+* L' => f x) e.comm

variable [IsGalois K L]

/-- Original restriction, using normality only of the source extension L/K. -/
def restrictElem (e : FieldMap K L K' L') (g : Gal(L'/K')) : Gal(L/K) := by
  letI : Algebra K K' := e.base.toAlgebra
  letI : Algebra K L' := ((algebraMap K' L').comp e.base).toAlgebra
  letI : Algebra L L' := e.extension.toAlgebra
  letI : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq' e.comm.symm
  exact (g.restrictScalars K).restrictNormal L

/-- The exact equation at every original field value. -/
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

/-- The neutral group restriction is constructed from the original embeddings. -/
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

@[simp] theorem restrictHom_comm (e : FieldMap K L K' L') (g : Gal(L'/K')) (x : L) :
    e.extension (restrictHom e g x) = g (e.extension x) := restrictElem_comm e g x

variable [IsGalois K' L']

/-- Krull continuity from finite basis values in the same target extension. -/
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

/-- The actual continuous restriction, with no surjectivity requirement. -/
def restrictContinuous (e : FieldMap K L K' L') : Gal(L'/K') →ₜ* Gal(L/K) :=
  ⟨restrictHom e, restrictHom_continuous e⟩

end FieldMap
end GaloisUnits



namespace GaloisUnits

section Operations
variable (K : Type u) (L : Type v) [Field L]
@[simp] theorem up_one : up.{u, v, w} K L 1 = 0 := rfl
@[simp] theorem up_mul (x y : Lˣ) :
    up.{u, v, w} K L (x * y) = up K L x + up K L y := rfl
@[simp] theorem up_inv (x : Lˣ) : up.{u, v, w} K L x⁻¹ = -up K L x := rfl
@[simp] theorem up_zpow (x : Lˣ) (n : ℤ) :
    up.{u, v, w} K L (x ^ n) = n • up K L x := rfl
end Operations


namespace FieldMap
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {K' : Type a} {L' : Type b} [Field K'] [Field L'] [Algebra K' L']
variable {K'' : Type c} {L'' : Type d} [Field K''] [Field L''] [Algebra K'' L'']

/-- Identity on both original fields. -/
def id (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : FieldMap K L K L where
  base := RingHom.id K
  extension := RingHom.id L
  comm := rfl

/-- Compose the two actual field embeddings and their original scalar square. -/
def comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    FieldMap K L K'' L'' where
  base := f.base.comp e.base
  extension := f.extension.comp e.extension
  comm := by
    ext x
    change f.extension (e.extension (algebraMap K L x)) =
      algebraMap K'' L'' (f.base (e.base x))
    rw [e.comm_apply, f.comm_apply]

/-- The original unit function on the single copies at one common size. -/
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

@[simp] theorem coefficientAddHom_up (e : FieldMap K L K' L') (x : Lˣ) :
    coefficientAddHom.{u, v, w, a, b} e (up.{u, v, max a (max b w)} K L x) =
      up.{a, b, max u (max v w)} K' L' (Units.map e.extension.toMonoidHom x) := rfl

@[simp] theorem down_coefficientAddHom (e : FieldMap K L K' L')
    (x : Carrier.{u, v, max a (max b w)} K L) :
    down.{a, b, max u (max v w)} K' L' (coefficientAddHom.{u, v, w, a, b} e x) =
      Units.map e.extension.toMonoidHom (down.{u, v, max a (max b w)} K L x) := rfl

variable [IsGalois K L] [IsGalois K' L'] [IsGalois K'' L'']

@[simp] theorem restrictHom_id (g : Gal(L/K)) : restrictHom (id K L) g = g := by
  apply AlgEquiv.ext
  intro x
  exact restrictHom_comm (id K L) g x

omit [IsGalois K'' L''] in
/-- Restriction reverses the actual composition of field embeddings. -/
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
/-- Original value commutation determines the constructed restriction uniquely. -/
theorem restrictHom_unique (e : FieldMap K L K' L') (ρ : Gal(L'/K') →* Gal(L/K))
    (hρ : ∀ (g : Gal(L'/K')) (x : L), e.extension (ρ g x) = g (e.extension x)) :
    ρ = restrictHom e := by
  ext g x
  apply e.extension.injective
  exact (hρ g x).trans (restrictHom_comm e g x).symm

/-- The actual restricted source module, using the stock continuous restriction. -/
abbrev sourceModule (e : FieldMap K L K' L') :
    DiscreteAbelianAction.{b, max u (max v (max a (max b w)))} Gal(L'/K') :=
  (restrictModules (restrictContinuous e)).obj
    (moduleObj.{u, v, max a (max b w)} K L)

/-- The single-copy target module at that same common size. -/
abbrev targetModule (_e : FieldMap K L K' L') :
    DiscreteAbelianAction.{b, max u (max v (max a (max b w)))} Gal(L'/K') :=
  moduleObj.{a, b, max u (max v w)} K' L'

/-- Equivariance follows from the actual original field restriction equation. -/
def coefficientEquivariant (e : FieldMap K L K' L') :
    DiscreteAbelianAction.EquivariantAddHom (sourceModule.{u, v, w, a, b} e)
      (targetModule.{u, v, w, a, b} e) :=
  ⟨coefficientAddHom.{u, v, w, a, b} e, fun h x => by
    apply ULift.ext
    apply Units.ext
    exact restrictHom_comm e h (down.{u, v, max a (max b w)} K L x).val⟩

/-- The genuine continuous integer-linear equivariant arrow on the original unit map. -/
def coefficientMap (e : FieldMap K L K' L') :
    sourceModule.{u, v, w, a, b} e ⟶ targetModule.{u, v, w, a, b} e :=
  DiscreteAbelianAction.ofAddHom (coefficientEquivariant.{u, v, w, a, b} e)

@[simp] theorem coefficientMap_addHom (e : FieldMap K L K' L') :
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) =
      coefficientAddHom.{u, v, w, a, b} e := rfl

theorem coefficientMap_up (e : FieldMap K L K' L') (x : Lˣ) :
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
      (up.{u, v, max a (max b w)} K L x) =
      up.{a, b, max u (max v w)} K' L' (Units.map e.extension.toMonoidHom x) := rfl

/-- Integer linearity is that of the actual stored continuous-linear arrow. -/
theorem coefficientMap_int (e : FieldMap K L K' L') (n : ℤ)
    (x : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e)) :
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) (n • x) =
      n • DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) x :=
  (coefficientMap.{u, v, w, a, b} e).hom.hom.hom.hom.map_smul n x

/-- Continuity is carried by the same coefficient arrow, not a separate certificate. -/
theorem coefficientMap_continuous (e : FieldMap K L K' L') :
    Continuous (DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)) :=
  (coefficientMap.{u, v, w, a, b} e).hom.hom.hom.hom.continuous

end FieldMap
end GaloisUnits


universe r
namespace GaloisUnits


section UniverseComparisons
variable (K : Type u) (L : Type v) [Field L]

/-- The specified universe change uses the original units, with exactly one copy on each side. -/
def universeEquiv : Carrier.{u, v, w} K L ≃+ Carrier.{u, v, a} K L where
  toFun x := up.{u, v, a} K L (down.{u, v, w} K L x)
  invFun x := up.{u, v, w} K L (down.{u, v, a} K L x)
  left_inv _x := rfl
  right_inv _x := rfl
  map_add' _x _y := rfl

@[simp] theorem universeEquiv_up (x : Lˣ) :
    universeEquiv.{u, v, w, a} K L (up K L x) = up K L x := rfl
@[simp] theorem universeEquiv_down (x : Carrier.{u, v, w} K L) :
    down K L (universeEquiv.{u, v, w, a} K L x) = down K L x := rfl
@[simp] theorem universeEquiv_id : universeEquiv.{u, v, w, w} K L =
    AddEquiv.refl (Carrier.{u, v, w} K L) := rfl
@[simp] theorem universeEquiv_comp :
    (universeEquiv.{u, v, w, a} K L).trans (universeEquiv.{u, v, a, b} K L) =
      universeEquiv.{u, v, w, b} K L := rfl

/-- The actual continuous integer-linear universe comparison and its inverse. -/
def universeContinuousEquiv : Carrier.{u, v, w} K L ≃L[ℤ] Carrier.{u, v, a} K L where
  toLinearEquiv :=
    { __ := universeEquiv.{u, v, w, a} K L
      map_smul' := fun n x => map_zsmul (universeEquiv.{u, v, w, a} K L) n x }
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

variable [Field K] [Algebra K L]
@[simp] theorem universeEquiv_action (g : Gal(L/K)) (x : Carrier.{u, v, w} K L) :
    universeEquiv.{u, v, w, a} K L (g • x) =
      g • universeEquiv.{u, v, w, a} K L x := rfl
end UniverseComparisons

section ActualFieldModule
variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The stock profinite group is the original Krull-topological Galois group. -/
def profiniteGroup := InfiniteGalois.profiniteGalGrp K L
@[simp] theorem profiniteGroup_carrier : (profiniteGroup K L : Type v) = Gal(L/K) := rfl

/-- The actual finite field's fixing subgroup is open in the prescribed topology. -/
theorem unitField_fixing_open (x : Lˣ) : IsOpen ((unitField K L x).fixingSubgroup : Set Gal(L/K)) :=
  (unitField K L x).toIntermediateField.fixingSubgroup_isOpen

/-- The original unit as a unit of its own finite Galois field. -/
def unitInField (x : Lˣ) : (unitField K L x).toIntermediateFieldˣ :=
  Units.mk0 ⟨x.val, unit_mem_field K L x⟩ (by
    intro h
    exact x.ne_zero (congrArg Subtype.val h))

theorem unitInField_val (x : Lˣ) :
    Units.map (unitField K L x).toIntermediateField.val.toMonoidHom (unitInField K L x) = x := by
  apply Units.ext
  rfl

/-- The bundled coefficient action retains the exact original left action. -/
@[simp] theorem module_action_up (g : Gal(L/K)) (x : Lˣ) :
    ((moduleObj.{u, v, w} K L).obj.obj.ρ g).asHom.hom (up K L x) =
      up K L (Units.map g.toRingEquiv.toMonoidHom x) := rfl

/-- Integer linearity of the same stored action endomorphism. -/
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

@[simp] theorem coefficientAddHom_id :
    coefficientAddHom.{u, v, w, u, v} (id K L) =
      AddMonoidHom.id (Carrier.{u, v, max u (max v w)} K L) := by
  ext x
  rfl

/-- Literal original unit functions compose at the one common size of the whole diagram. -/
theorem coefficientAddHom_comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    (coefficientAddHom.{a, b, max u (max v w), c, d} f).comp
        (coefficientAddHom.{u, v, max c (max d w), a, b} e) =
      coefficientAddHom.{u, v, max a (max b w), c, d} (comp f e) := by
  ext x
  rfl

/-- Field and coefficient-universe changes commute on every original unit. -/
theorem coefficientAddHom_universe (e : FieldMap K L K' L')
    (x : Carrier.{u, v, max a (max b w)} K L) :
    universeEquiv.{a, b, max u (max v w), max u (max v r)} K' L'
        (coefficientAddHom.{u, v, w, a, b} e x) =
      coefficientAddHom.{u, v, r, a, b} e
        (universeEquiv.{u, v, max a (max b w), max a (max b r)} K L x) := rfl

variable [IsGalois K L] [IsGalois K' L']
@[simp] theorem restrictContinuous_id : restrictContinuous (id K L) =
    ContinuousMonoidHom.id Gal(L/K) := by
  ext g x
  exact congrArg (fun f : Gal(L/K) => f x) (restrictHom_id g)

variable [IsGalois K'' L'']
/-- The fixed continuous restrictions compose contravariantly. -/
theorem restrictContinuous_comp (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    restrictContinuous (comp f e) = (restrictContinuous e).comp (restrictContinuous f) := by
  ext g x
  exact congrArg (fun h : Gal(L/K) => h x) (restrictHom_comp f e g)

/-- The actual identity-source comparison has the original identity unit function. -/
def coefficientIdentitySourceIso : sourceModule.{u, v, w, u, v} (id K L) ≅
    targetModule.{u, v, w, u, v} (id K L) :=
  (restrictModulesCongr _ _ (restrictContinuous_id (K := K) (L := L))).app
      (moduleObj.{u, v, max u (max v w)} K L) ≪≫
    restrictModulesId.app (moduleObj.{u, v, max u (max v w)} K L)

@[simp] theorem coefficientMap_id : coefficientMap.{u, v, w, u, v} (id K L) =
    coefficientIdentitySourceIso.hom := by
  apply (DiscreteAbelianAction.forget Gal(L/K)).map_injective
  ext x
  rfl

/-- The stock restriction composition fixes the actual source of the composite coefficient arrow. -/
def coefficientCompositionSourceIso (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L') :
    sourceModule.{u, v, max a (max b w), c, d} (comp f e) ≅
      (restrictModules (restrictContinuous f)).obj
        (sourceModule.{u, v, max c (max d w), a, b} e) :=
  (restrictModulesCongr _ _ (restrictContinuous_comp f e)).app
      (moduleObj.{u, v, max a (max b (max c (max d w)))} K L) ≪≫
    (restrictModulesComp (restrictContinuous e) (restrictContinuous f)).app
      (moduleObj.{u, v, max a (max b (max c (max d w)))} K L)

/-- The SAME continuous-linear equivariant coefficient arrows compose with that
canonical source comparison. -/
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
/-- The SAME construction on any prescribed separable closure, at exactly max(u,w). -/
def separableClosureModule : DiscreteAbelianAction.{u, max u w} Gal(Ω/k) :=
  moduleObj.{u, u, w} k Ω
@[simp] theorem separableClosureModule_eq :
    separableClosureModule.{u, w} k Ω = moduleObj.{u, u, w} k Ω := rfl
end ClosureSpecialization

namespace FieldMap
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {K' : Type a} {L' : Type b} [Field K'] [Field L'] [Algebra K' L']
variable [IsGalois K L] [IsGalois K' L']

/-- Characteristic original values determine the actual continuous restriction uniquely. -/
theorem restrictContinuous_unique (e : FieldMap K L K' L')
    (ρ : Gal(L'/K') →ₜ* Gal(L/K))
    (hρ : ∀ (g : Gal(L'/K')) (x : L), e.extension (ρ g x) = g (e.extension x)) :
    ρ = restrictContinuous e := by
  ext g x
  apply e.extension.injective
  exact (hρ g x).trans (restrictHom_comm e g x).symm

/-- All original field coordinates of the fixed continuous restriction and
SAME coefficient arrow. -/
structure OriginalCoordinateLaws (e : FieldMap K L K' L') : Prop where
  restriction_values : ∀ (g : Gal(L'/K')) (x : L),
    e.extension (restrictContinuous e g x) = g (e.extension x)
  restriction_unique : ∀ (ρ : Gal(L'/K') →ₜ* Gal(L/K)),
    (∀ (g : Gal(L'/K')) (x : L), e.extension (ρ g x) = g (e.extension x)) →
      ρ = restrictContinuous e
  restriction_continuous : Continuous (restrictContinuous e)
  original_source : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e) =
    Carrier.{u, v, max a (max b w)} K L
  original_target : DiscreteAbelianAction.underlying (targetModule.{u, v, w, a, b} e) =
    Carrier.{a, b, max u (max v w)} K' L'
  unit_values : ∀ x : Lˣ,
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
        (up.{u, v, max a (max b w)} K L x) =
      up.{a, b, max u (max v w)} K' L' (Units.map e.extension.toMonoidHom x)
  down_values : ∀ x : Carrier.{u, v, max a (max b w)} K L,
    down.{a, b, max u (max v w)} K' L'
        (DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e) x) =
      Units.map e.extension.toMonoidHom (down.{u, v, max a (max b w)} K L x)
  inverse_values : ∀ x : Lˣ,
    DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
        (up.{u, v, max a (max b w)} K L x⁻¹) =
      -DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e)
        (up.{u, v, max a (max b w)} K L x)
  actual_equivariance : ∀ (g : Gal(L'/K'))
    (x : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e)),
    DiscreteAbelianAction.homToAdd (coefficientMap e) (g • x) =
      g • DiscreteAbelianAction.homToAdd (coefficientMap e) x
  actual_integer_linearity : ∀ (n : ℤ)
    (x : DiscreteAbelianAction.underlying (sourceModule.{u, v, w, a, b} e)),
    DiscreteAbelianAction.homToAdd (coefficientMap e) (n • x) =
      n • DiscreteAbelianAction.homToAdd (coefficientMap e) x
  actual_continuity : Continuous
    (DiscreteAbelianAction.homToAdd (coefficientMap.{u, v, w, a, b} e))
  coefficient_universe_square : ∀ x : Carrier.{u, v, max a (max b w)} K L,
    universeEquiv.{a, b, max u (max v w), max u (max v r)} K' L'
        (coefficientAddHom.{u, v, w, a, b} e x) =
      coefficientAddHom.{u, v, r, a, b} e
        (universeEquiv.{u, v, max a (max b w), max a (max b r)} K L x)

/-- Every compatible embedding pair supplies all coordinates without a restriction certificate. -/
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

/-- The complete original unit-module source contract fixes every constructed object, map,
finite field, Krull restriction, and coefficient-universe comparison. -/
structure OriginalGaloisUnitsContinuousModuleLaws (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] : Prop where
  original_carrier : DiscreteAbelianAction.underlying (moduleObj.{u, v, w} K L) =
    Carrier.{u, v, w} K L
  original_profinite_group : (profiniteGroup K L : Type v) = Gal(L/K)
  inverse_down_up : ∀ x : Lˣ, down K L (up.{u, v, w} K L x) = x
  inverse_up_down : ∀ x : Carrier.{u, v, w} K L, up K L (down K L x) = x
  original_one : up.{u, v, w} K L 1 = 0
  original_product : ∀ x y : Lˣ, up.{u, v, w} K L (x * y) = up K L x + up K L y
  original_inverse : ∀ x : Lˣ, up.{u, v, w} K L x⁻¹ = -up K L x
  original_integer_power : ∀ (x : Lˣ) (n : ℤ), up.{u, v, w} K L (x ^ n) = n • up K L x
  original_left_action : ∀ (g : Gal(L/K)) (x : Lˣ),
    ((moduleObj.{u, v, w} K L).obj.obj.ρ g).asHom.hom (up K L x) =
      up K L (Units.map g.toRingEquiv.toMonoidHom x)
  action_identity : ∀ x : Carrier.{u, v, w} K L, (1 : Gal(L/K)) • x = x
  action_multiplication : ∀ (g h : Gal(L/K)) (x : Carrier.{u, v, w} K L),
    (g * h) • x = g • (h • x)
  action_addition : ∀ (g : Gal(L/K)) (x y : Carrier.{u, v, w} K L),
    g • (x + y) = g • x + g • y
  action_integer_linearity : ∀ (g : Gal(L/K)) (n : ℤ)
    (x : DiscreteAbelianAction.underlying (moduleObj.{u, v, w} K L)),
    ((moduleObj K L).obj.obj.ρ g).asHom.hom (n • x) =
      n • ((moduleObj K L).obj.obj.ρ g).asHom.hom x
  each_unit_own_field : ∀ x : Lˣ, x.val ∈ (unitField K L x).toIntermediateField
  each_unit_own_field_value : ∀ x : Lˣ,
    Units.map (unitField K L x).toIntermediateField.val.toMonoidHom (unitInField K L x) = x
  each_unit_open_fixing : ∀ x : Lˣ, IsOpen ((unitField K L x).fixingSubgroup : Set Gal(L/K))
  each_unit_fixing_stabilizer : ∀ x : Lˣ,
    (unitField K L x).fixingSubgroup ≤ MulAction.stabilizer Gal(L/K) (up.{u, v, w} K L x)
  each_stabilizer_open : ∀ x : Carrier.{u, v, w} K L,
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K))
  joint_action_continuity : Continuous (fun p : Gal(L/K) × Carrier.{u, v, w} K L => p.1 • p.2)
  every_compatible_field_map : ∀ (K' : Type a) (L' : Type b)
    [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L'] (e : FieldMap K L K' L'),
    FieldMap.OriginalCoordinateLaws.{u, v, w, a, b, r} e
  restriction_identity : FieldMap.restrictContinuous (FieldMap.id K L) =
    ContinuousMonoidHom.id Gal(L/K)
  coefficient_identity : FieldMap.coefficientMap.{u, v, w, u, v} (FieldMap.id K L) =
    FieldMap.coefficientIdentitySourceIso.hom
  every_restriction_composition : ∀ (K' : Type a) (L' : Type b) (K'' : Type c) (L'' : Type d)
    [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L']
    [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
    (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L'),
    FieldMap.restrictContinuous (FieldMap.comp f e) =
      (FieldMap.restrictContinuous e).comp (FieldMap.restrictContinuous f)
  every_coefficient_composition : ∀ (K' : Type a) (L' : Type b) (K'' : Type c) (L'' : Type d)
    [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L']
    [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
    (f : FieldMap K' L' K'' L'') (e : FieldMap K L K' L'),
    (FieldMap.coefficientCompositionSourceIso.{u, v, w, a, b, c, d} f e).hom ≫
        (restrictModules (FieldMap.restrictContinuous f)).map
          (FieldMap.coefficientMap.{u, v, max c (max d w), a, b} e) ≫
        FieldMap.coefficientMap.{a, b, max u (max v w), c, d} f =
      FieldMap.coefficientMap.{u, v, max a (max b w), c, d} (FieldMap.comp f e)
  universe_original_values : ∀ x : Lˣ,
    universeEquiv.{u, v, w, r} K L (up K L x) = up K L x
  universe_original_down : ∀ x : Carrier.{u, v, w} K L,
    down K L (universeEquiv.{u, v, w, r} K L x) = down K L x
  universe_identity : universeEquiv.{u, v, w, w} K L = AddEquiv.refl _
  universe_composition :
    (universeEquiv.{u, v, w, r} K L).trans (universeEquiv.{u, v, r, a} K L) =
      universeEquiv.{u, v, w, a} K L
  universe_action_square : ∀ (g : Gal(L/K)) (x : Carrier.{u, v, w} K L),
    universeEquiv.{u, v, w, r} K L (g • x) = g • universeEquiv.{u, v, w, r} K L x
  universe_continuity_both : Continuous (universeContinuousEquiv.{u, v, w, r} K L) ∧
    Continuous (universeContinuousEquiv.{u, v, w, r} K L).symm
  chosen_separable_closure : ∀ (k Ω : Type u)
    [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω],
    separableClosureModule.{u, w} k Ω = moduleObj.{u, u, w} k Ω

/-- The full construction for every algebraic Galois extension, finite or infinite,
with every original compatible field map and one-copy universe comparison. -/
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
