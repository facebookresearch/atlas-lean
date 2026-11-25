/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Logic.Function.Basic

/-!
# FiniteTensorInterfaces

Fixed finite-index tensors, component transport maps, and preservation of colimits in each
tensor slot.
-/

/- Source proof segment: FixedIndexTensor -/
section source_FixedIndexTensor
/-!
# Fixed finite tensor indices and source slot preservation

Finite tensor inputs retain their actual fixed finite index type.
One-slot functors change precisely one object while keeping every
other tensor input fixed. Separate preservation below is the source
colimit hypothesis, not a joint finite tensor colimit outcome.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui uc uh ud uhD us

namespace CategoryTheory

open Limits

variable {I : Type ui} {C : Type uc} [Category.{uh} C]

namespace Pi

/-- The actual component map of a one-slot replacement, with its
dependent endpoint transports retained. -/
def replaceMap [DecidableEq I] (A : I → C) (i : I) {X Y : C} (f : X ⟶ Y) :
    Function.update A i X ⟶ Function.update A i Y :=
  fun j => if h : j = i then
      eqToHom (by rw [h, Function.update_self]) ≫ f ≫
        eqToHom (by rw [h, Function.update_self])
    else
      eqToHom (Function.update_of_ne h X A) ≫
        eqToHom (Function.update_of_ne h Y A).symm

/-- The varying component is the original arrow, with its actual
endpoint equalities retained as heterogeneous equality. -/
theorem replaceMap_at [DecidableEq I] (A : I → C) (i : I)
    {X Y : C} (f : X ⟶ Y) : HEq (replaceMap A i f i) f := by
  dsimp only [replaceMap]
  rw [dite_eq_left rfl]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- Every other component is the original identity arrow, with its
actual endpoint equalities retained. -/
theorem replaceMap_other [DecidableEq I] (A : I → C) (i j : I) (h : j ≠ i)
    {X Y : C} (f : X ⟶ Y) : HEq (replaceMap A i f j) (𝟙 (A j)) := by
  dsimp only [replaceMap]
  rw [dite_eq_right h]
  exact (eqToHom_comp_heq _ _).trans (eqToHom_heq_id_dom _ _ _)

/-- Replace one object of an indexed family by a varying object,
retaining every other original object. -/
def replaceFunctor [DecidableEq I] (A : I → C) (i : I) : C ⥤ (I → C) where
  obj X := Function.update A i X
  map := replaceMap A i
  map_id X := by
    funext j
    by_cases h : j = i
    · subst j
      have hr : HEq (𝟙 (Function.update A i X i)) (𝟙 X) :=
        (eqToHom_heq_id_dom _ _ (Function.update_self i X A)).symm.trans
          (eqToHom_heq_id_cod _ _ (Function.update_self i X A))
      exact eq_of_heq ((replaceMap_at A i (𝟙 X)).trans hr.symm)
    · have hr : HEq (𝟙 (Function.update A i X j)) (𝟙 (A j)) :=
        (eqToHom_heq_id_dom _ _ (Function.update_of_ne h X A)).symm.trans
          (eqToHom_heq_id_cod _ _ (Function.update_of_ne h X A))
      exact eq_of_heq ((replaceMap_other A i j h (𝟙 X)).trans hr.symm)
  map_comp := by
    intro X Y Z f g
    funext j
    change replaceMap A i (f ≫ g) j = replaceMap A i f j ≫ replaceMap A i g j
    by_cases h : j = i
    · subst j
      have hr := heq_comp (Function.update_self i X A) (Function.update_self i Y A)
        (Function.update_self i Z A) (replaceMap_at A i f) (replaceMap_at A i g)
      exact eq_of_heq ((replaceMap_at A i (f ≫ g)).trans hr.symm)
    · have hr := heq_comp (Function.update_of_ne h X A) (Function.update_of_ne h Y A)
        (Function.update_of_ne h Z A) (replaceMap_other A i j h f) (replaceMap_other A i j h g)
      have hh : HEq (replaceMap A i f j ≫ replaceMap A i g j) (𝟙 (A j)) :=
        hr.trans (heq_of_eq (Category.id_comp (𝟙 (A j))))
      exact eq_of_heq ((replaceMap_other A i j h (f ≫ g)).trans hh.symm)

/-- Replacement leaves the original objects outside the chosen
slot, and uses the varying object at the chosen slot. -/
@[simp]
theorem replaceFunctor_obj [DecidableEq I] (A : I → C) (i : I) (X : C) :
    (replaceFunctor A i).obj X = Function.update A i X :=
  rfl

/-- The varying slot receives precisely the original input map. -/
@[simp]
theorem replaceFunctor_map_at [DecidableEq I] (A : I → C) (i : I)
    {X Y : C} (f : X ⟶ Y) :
    HEq ((replaceFunctor A i).map f i) f :=
  replaceMap_at A i f

/-- Every retained slot receives its identity map. -/
@[simp]
theorem replaceFunctor_map_other [DecidableEq I] (A : I → C) (i j : I) (h : j ≠ i)
    {X Y : C} (f : X ⟶ Y) :
    HEq ((replaceFunctor A i).map f j) (𝟙 (A j)) :=
  replaceMap_other A i j h f

end Pi

namespace FiniteFamily

/-- A family with its original fixed finite input type, functorial
in the actual component maps and without a relabelling. -/
def fixedIndexFunctor (I : FintypeCat.{0}) : (I → C) ⥤ FiniteFamily C where
  obj A := ⟨I, A⟩
  map f :=
    { equiv := Equiv.refl I
      hom i := f i }
  map_id A := by
    apply Hom_ext
    · rfl
    · intro i
      exact HEq.rfl
  map_comp f g := by
    apply Hom_ext
    · rfl
    · intro i
      exact HEq.rfl

end FiniteFamily

/-- The actual unbiased heterogeneous tensor functor at a fixed
finite index, including the empty index. -/
def fixedIndexTensorFunctor [FiniteTensor C] (I : FintypeCat.{0}) : (I → C) ⥤ C :=
  FiniteFamily.fixedIndexFunctor I ⋙ FiniteTensor.tensor

namespace Functor

variable {D : Type ud} [Category.{uhD} D]

/-- The source separate-colimit hypothesis for a family functor:
each varying slot preserves the required small colimits with all
other objects fixed. No joint colimit assertion is included. -/
class PreservesColimitsInEachSlot [DecidableEq I] (F : (I → C) ⥤ D) : Prop where
  preserves : ∀ (A : I → C) (i : I),
    PreservesColimitsOfSize.{us, us} (Pi.replaceFunctor A i ⋙ F)

end Functor

#print axioms Pi.replaceFunctor
#print axioms FiniteFamily.fixedIndexFunctor
#print axioms fixedIndexTensorFunctor

end CategoryTheory
end
end
end source_FixedIndexTensor

/- Source proof segment: TensorSlotPreservation -/
section source_TensorSlotPreservation
/-!
# Required source colimit preservation of finite tensor slots

This condition records only preservation with one actual tensor
input varying and all other original objects fixed. A source binary
symmetric tensor producer must derive it from its separate small
tensor preservation. It includes no monad, algebra, free adjunction,
or joint-colimit construction as an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u us

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C] [FiniteTensor C]

/-- The required small-colimit preservation of each original finite
tensor slot, for arbitrary fixed finite tensor inputs. -/
class FiniteTensorPreservesColimitsInEachSlot : Prop where
  preserves (I : FintypeCat.{0}) :
    @Functor.PreservesColimitsInEachSlot.{0, u, v, u, v, us} _ C _ C _ (Classical.decEq I)
      (fixedIndexTensorFunctor I)

end CategoryTheory
end
end
end source_TensorSlotPreservation

/- Source proof segment: IdentityComponentMaps -/
section source_IdentityComponentMaps
/-!
# Actual finite family maps with original identity components
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.FiniteFamily

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A finite family map relabels original objects with identity
transport components at every original source input. -/
def Hom.HasIdentityComponents {X Y : FiniteFamily C} (f : X ⟶ Y) : Prop :=
  ∀ i, ∃ h : X.obj i = Y.obj (f.equiv i), f.hom i = eqToHom h

/-- Original identity component maps are determined by their
actual original input bijection. -/
theorem Hom.ext_identityComponents {X Y : FiniteFamily C} {f g : X ⟶ Y}
    (he : f.equiv = g.equiv) (hf : f.HasIdentityComponents) (hg : g.HasIdentityComponents) :
      f = g := by
  obtain ⟨ef, ff⟩ := f
  obtain ⟨eg, gg⟩ := g
  cases he
  apply Hom_ext (f := {equiv := ef, hom := ff}) (g := {equiv := ef, hom := gg}) rfl
  intro i
  obtain ⟨h, hh⟩ := hf i
  obtain ⟨k, hk⟩ := hg i
  have hp : h = k := Subsingleton.elim _ _
  exact heq_of_eq (hh.trans ((congrArg eqToHom hp).trans hk.symm))

/-- An original finite-family identity has identity components. -/
theorem Hom.hasIdentityComponents_id (X : FiniteFamily C) :
    (𝟙 X : X ⟶ X).HasIdentityComponents := fun _ => ⟨rfl, rfl⟩

/-- An original object-preserving relabelling uses only equality
transports, hence has identity components. -/
theorem isoOfReindex_identityComponents {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (h : ∀ i, X.obj i = Y.obj (e i)) :
    (isoOfReindex e h).hom.HasIdentityComponents := by
  intro i
  exact ⟨h i, rfl⟩

/-- Compose original identity-component reindexings with their
actual composite input bijection. -/
theorem Hom.HasIdentityComponents.comp {X Y Z : FiniteFamily C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f.HasIdentityComponents) (hg : g.HasIdentityComponents) :
    (f ≫ g).HasIdentityComponents := by
  intro i
  obtain ⟨h, hh⟩ := hf i
  obtain ⟨k, hk⟩ := hg (f.equiv i)
  refine ⟨h.trans k, ?_⟩
  change f.hom i ≫ g.hom (f.equiv i) = eqToHom _
  rw [hh, hk, eqToHom_trans]

#print axioms Hom.HasIdentityComponents.comp

end CategoryTheory.FiniteFamily
end
end source_IdentityComponentMaps

/- Source proof segment: IdentityComponentIsomorphisms -/
section source_IdentityComponentIsomorphisms
/-!
# Original equality-transport components under finite-family isomorphism inverses
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.FiniteFamily

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Inverting an original object-preserving finite-family
relabeling retains only equality-transport components. -/
theorem isoOfReindex_inv_identityComponents {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (h : ∀ i, X.obj i = Y.obj (e i)) :
    (isoOfReindex e h).inv.HasIdentityComponents := by
  intro i
  have hobj : Y.obj i = X.obj (e.symm i) :=
    (congrArg Y.obj (e.apply_symm_apply i)).symm.trans (h (e.symm i)).symm
  refine ⟨hobj, ?_⟩
  change eqToHom (congrArg Y.obj (e.apply_symm_apply i).symm) ≫
      eqToHom (h (e.symm i)).symm = eqToHom hobj
  exact eqToHom_trans (congrArg Y.obj (e.apply_symm_apply i).symm) (h (e.symm i)).symm

/-- Componentwise equality isomorphisms on the original finite
objects give identity-transport maps under their full input bijection. -/
theorem isoOfComponents_eqToIso_identityComponents {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (h : ∀ i, X.obj i = Y.obj (e i)) :
    (isoOfComponents e (fun i => eqToIso (h i))).hom.HasIdentityComponents :=
  isoOfReindex_identityComponents e h

/-- The actual inverse of componentwise equality isomorphisms
retains all original object transports through the inverse index map. -/
theorem isoOfComponents_eqToIso_inv_identityComponents {X Y : FiniteFamily C}
    (e : X.index ≃ Y.index) (h : ∀ i, X.obj i = Y.obj (e i)) :
    (isoOfComponents e (fun i => eqToIso (h i))).inv.HasIdentityComponents :=
  isoOfReindex_inv_identityComponents e h

#print axioms isoOfReindex_inv_identityComponents

end CategoryTheory.FiniteFamily
end
end
end source_IdentityComponentIsomorphisms

/- Source proof segment: IdentityComponentFunctorMaps -/
section source_IdentityComponentFunctorMaps
/-!
# Functorial maps of original finite-family equality transports
-/

@[expose] public section

set_option autoImplicit false

universe u v uD vD

namespace CategoryTheory.FiniteFamily

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]

/-- An arbitrary actual functor carries the original
object-preserving finite reindexing components to the corresponding
original equality transports of its images. -/
theorem Hom.HasIdentityComponents.map (F : C ⥤ D)
    {X Y : FiniteFamily C} {f : X ⟶ Y} (hf : f.HasIdentityComponents) :
    ((FiniteFamily.map F).map f).HasIdentityComponents := by
  intro i
  obtain ⟨h, hh⟩ := hf i
  refine ⟨congrArg F.obj h, ?_⟩
  change F.map (f.hom i) = eqToHom _
  rw [hh]
  exact eqToHom_map F h

#print axioms Hom.HasIdentityComponents.map

end CategoryTheory.FiniteFamily
end
end source_IdentityComponentFunctorMaps

/- Source proof segment: FiniteFamilyEqualityComponents -/
section source_FiniteFamilyEqualityComponents
/-!
# Original finite-family object equality transports at every input position
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.FiniteFamily

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Equality transport between original finite families gives
only the corresponding original object equality components. -/
theorem eqToHom_identityComponents {X Y : FiniteFamily C} (h : X = Y) :
    (eqToHom h).HasIdentityComponents := by
  cases h
  exact Hom.hasIdentityComponents_id X

/-- Equality transport in an inner finite family preserves the
original object at each input reached by its actual input bijection. -/
theorem eqToHom_object_eq {X Y : FiniteFamily C} (h : X = Y) (i : X.index) :
    X.obj i = Y.obj ((eqToHom h).equiv i) := by
  cases h
  rfl

/-- Its actual component is the equality transport of that
original component object, through the original index transport. -/
theorem eqToHom_component {X Y : FiniteFamily C} (h : X = Y) (i : X.index) :
    (eqToHom h).hom i = eqToHom (eqToHom_object_eq h i) := by
  cases h
  rfl

#print axioms eqToHom_component

end CategoryTheory.FiniteFamily
end
end source_FiniteFamilyEqualityComponents

/- Source proof segment: IdentityComponentFlatten -/
section source_IdentityComponentFlatten
/-!
# Flatten actual original finite-family equality-transport components
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.FiniteFamily

open CategoryTheory

variable {C : Type u} [Category.{v} C]

private theorem equalityComponentIdentity {X Y : FiniteFamily C} (h : X = Y)
    (g : X ⟶ Y) (hg : g = eqToHom h) (i : X.index) :
    ∃ ho : X.obj i = Y.obj (g.equiv i), g.hom i = eqToHom ho := by
  subst g
  exact ⟨eqToHom_object_eq h i, eqToHom_component h i⟩

/-- Flattening an original finite family of object-equality
transports retains the corresponding original equality transport
at every actual dependent-sum input position. -/
theorem Hom.HasIdentityComponents.flatten
    {X Y : FiniteFamily (FiniteFamily C)} {f : X ⟶ Y} (hf : f.HasIdentityComponents) :
    ((FiniteFamily.flatten (C := C)).map f).HasIdentityComponents := by
  intro p
  rcases p with ⟨i, j⟩
  obtain ⟨h, hh⟩ := hf i
  exact equalityComponentIdentity h (f.hom i) hh j

#print axioms Hom.HasIdentityComponents.flatten

end CategoryTheory.FiniteFamily
end
end source_IdentityComponentFlatten

/- Source proof segment: IdentityComponentFiberFlatten -/
section source_IdentityComponentFiberFlatten
@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.FiniteFamily

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Original fiberwise identity transports remain identity
transports after the actual dependent-sum flattening map. -/
theorem Hom.HasIdentityComponents.flatten_fibers
    {X Y : FiniteFamily (FiniteFamily C)} {f : X ⟶ Y}
    (hf : ∀ i, (f.hom i).HasIdentityComponents) :
    ((FiniteFamily.flatten (C := C)).map f).HasIdentityComponents := by
  intro p
  exact hf p.1 p.2

end CategoryTheory.FiniteFamily
end
end source_IdentityComponentFiberFlatten

/- Source proof segment: IdentityComponentIsoInverse -/
section source_IdentityComponentIsoInverse
/-!
# Inverse of any actual equality-transport finite-family isomorphism
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.FiniteFamily

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The inverse of an actual finite-family isomorphism whose
forward components are original equality transports also has
only original equality transport components. -/
theorem Hom.HasIdentityComponents.iso_inv {X Y : FiniteFamily C} (e : X ≅ Y)
    (he : e.hom.HasIdentityComponents) : e.inv.HasIdentityComponents := by
  classical
  let h : ∀ i, X.obj i = Y.obj (e.hom.equiv i) := fun i => (he i).choose
  let r := isoOfReindex e.hom.equiv h
  have hr : r.hom = e.hom := by
    exact Hom.ext_identityComponents (f := r.hom) (g := e.hom) rfl
      (isoOfReindex_identityComponents e.hom.equiv h) he
  have hi : r = e := Iso.ext hr
  exact hi ▸ isoOfReindex_inv_identityComponents e.hom.equiv h

#print axioms Hom.HasIdentityComponents.iso_inv

end CategoryTheory.FiniteFamily
end
end source_IdentityComponentIsoInverse
