/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import MathlibExt.CategoryTheory.Functor.Isofibration

/-!
# Inner fibrations inducing isofibrations on homotopy categories

`SSet.innerIsoFibrations` consists of maps `f : X ⟶ Y` that are inner
fibrations and whose induced functor `SSet.hoFunctor.map f` is an
isofibration of ordinary categories:

```text
SSet.innerIsoFibrations =
  SSet.innerFibrations ⊓
    CategoryTheory.isofibrations.inverseImage SSet.hoFunctor.
```
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet

/-- Inner fibrations whose induced functors on homotopy categories are
isofibrations. This property is defined for arbitrary simplicial sets. -/
def innerIsoFibrations : MorphismProperty SSet.{u} :=
  SSet.innerFibrations.{u} ⊓
    CategoryTheory.isofibrations.{u}.inverseImage SSet.hoFunctor.{u}

variable {X Y : SSet.{u}}

/-- Membership is the conjunction of inner fibrancy and isofibrancy of
the induced functor on homotopy categories. -/
theorem innerIsoFibrations.mem_iff (f : X ⟶ Y) :
    innerIsoFibrations f ↔
      innerFibrations f ∧ (hoFunctor.map f).toFunctor.IsIsofibration :=
  Iff.rfl

/-- The raw intersection contains identities and is stable under composition. -/
instance innerIsoFibrations.isMultiplicative :
    innerIsoFibrations.{u}.IsMultiplicative :=
  inferInstanceAs ((SSet.innerFibrations.{u} ⊓
    CategoryTheory.isofibrations.{u}.inverseImage
      SSet.hoFunctor.{u}).IsMultiplicative)

/-- The raw intersection is stable under composition with isomorphisms. -/
instance innerIsoFibrations.respectsIso :
    innerIsoFibrations.{u}.RespectsIso :=
  inferInstanceAs ((SSet.innerFibrations.{u} ⊓
    CategoryTheory.isofibrations.{u}.inverseImage
      SSet.hoFunctor.{u}).RespectsIso)

/-- The raw intersection is stable under retracts. -/
instance innerIsoFibrations.isStableUnderRetracts :
    innerIsoFibrations.{u}.IsStableUnderRetracts :=
  inferInstanceAs ((SSet.innerFibrations.{u} ⊓
    CategoryTheory.isofibrations.{u}.inverseImage
      SSet.hoFunctor.{u}).IsStableUnderRetracts)

/-- A functor into a discrete category with a unique object is an
isofibration: every isomorphism to lift is an identity. -/
private theorem isIsofibration_of_unique_isDiscrete {C : Type u} [Category.{u} C]
    {D : Type u} [Category.{u} D] [Unique D] [IsDiscrete D] (F : C ⥤ D) :
    F.IsIsofibration where
  exists_lift := by
    intro X Y g
    exact ⟨X, Iso.refl X, Subsingleton.elim _ _, by
      apply Iso.ext
      exact Subsingleton.elim _ _⟩

/-- The induced functor on homotopy categories of a terminal map is
an isofibration. -/
private theorem hoFunctor_map_terminalFrom_isIsofibration (X : SSet.{u}) :
    (hoFunctor.map (terminal.from X)).toFunctor.IsIsofibration := by
  let e : hoFunctor.obj (⊤_ SSet.{u}) ≅ Cat.of (Discrete PUnit.{u + 1}) :=
    hoFunctor.terminalIso ≪≫
      terminalIsoIsTerminal Cat.isTerminalDiscretePUnit
  rw [← CategoryTheory.isofibrations.mem_iff,
    ← CategoryTheory.isofibrations.cancel_right_of_respectsIso
      (hoFunctor.map (terminal.from X)) e.hom,
    CategoryTheory.isofibrations.mem_iff]
  exact isIsofibration_of_unique_isDiscrete (D := Discrete PUnit.{u + 1}) _

/-- A simplicial set is a quasicategory exactly when its terminal map
is an inner fibration inducing an isofibration on homotopy categories. -/
theorem innerIsoFibrations.terminalFrom_iff_quasicategory (X : SSet.{u}) :
    innerIsoFibrations (terminal.from X) ↔ Quasicategory X := by
  rw [innerIsoFibrations.mem_iff]
  constructor
  · intro h
    exact ((innerFibration_iff _).symm.trans
      (quasicategory_iff_innerFibration X).symm).1 h.1
  · intro h
    exact ⟨(innerFibration_iff _).1
        ((quasicategory_iff_innerFibration X).1 h),
      hoFunctor_map_terminalFrom_isIsofibration X⟩

end SSet
