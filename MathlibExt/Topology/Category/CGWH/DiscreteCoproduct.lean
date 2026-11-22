/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Point
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Discrete CGWH spaces as coproducts of the native point

The carrier is the literal lifted index with discrete topology. Its point
injections and universal map give a coproduct without a colimit-existence premise.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CGWH

/-- The actual discrete CGWH object on the lifted index. -/
def discreteObj (I : Type w) : CGWH.{u, max v w} := by
  letI : TopologicalSpace (ULift.{v} I) := ⊥
  letI : DiscreteTopology (ULift.{v} I) := ⟨rfl⟩
  exact CGWH.of (ULift.{v} I)

/-- The named object retains its original discrete topology. -/
theorem discreteObj_discreteTopology (I : Type w) :
    DiscreteTopology (discreteObj.{u, v, w} I) :=
  ⟨rfl⟩

/-- The injection from the native point retains the literal lifted index. -/
def discreteObjIncl (I : Type w) (i : I) :
    point.{u, max v w} ⟶ discreteObj.{u, v, w} I :=
  (pointHomEquiv _).symm (ULift.up i)

@[simp]
theorem discreteObjIncl_apply (I : Type w) (i : I) (p : PUnit) :
    discreteObjIncl.{u, v, w} I i p = ULift.up i :=
  rfl

/-- The native point injections form a cofan with the actual discrete carrier. -/
def discreteCofan (I : Type w) :
    Cofan (fun _ : I => point.{u, max v w}) :=
  Cofan.mk (discreteObj.{u, v, w} I) (discreteObjIncl I)

/-- The universal map evaluates each leg at the unique native point. -/
def discreteCofanDesc (I : Type w)
    (c : Cofan (fun _ : I => point.{u, max v w})) :
    discreteObj.{u, v, w} I ⟶ c.pt := by
  letI := discreteObj_discreteTopology.{u, v, w} I
  exact ConcreteCategory.ofHom
    (show C(discreteObj.{u, v, w} I, c.pt) from
      ⟨fun x => c.inj (show ULift.{v} I from x).down PUnit.unit,
        continuous_of_discreteTopology⟩)

@[simp]
theorem discreteCofanDesc_apply (I : Type w)
    (c : Cofan (fun _ : I => point.{u, max v w})) (i : I) :
    discreteCofanDesc.{u, v, w} I c (ULift.up i) = c.inj i PUnit.unit :=
  rfl

/-- The literal discrete cofan satisfies the complete coproduct universal property. -/
def discreteCofanIsColimit (I : Type w) :
    IsColimit (discreteCofan.{u, v, w} I) := by
  refine Cofan.IsColimit.mk _ (discreteCofanDesc I) ?_ ?_
  · intro c i
    apply ConcreteCategory.hom_ext
    intro p
    change c.inj i PUnit.unit = c.inj i p
    rcases p with ⟨⟩
    rfl
  · intro c m h
    apply ConcreteCategory.hom_ext
    intro x
    have hx := congrArg
      (fun f : point.{u, max v w} ⟶ c.pt => f PUnit.unit)
      (h (show ULift.{v} I from x).down)
    change m (ULift.up (show ULift.{v} I from x).down) =
      c.inj (show ULift.{v} I from x).down PUnit.unit at hx
    exact hx

/-- The actual colimiting cofan supplies point-coproduct existence. -/
theorem discreteObjHasCoproduct (I : Type w) :
    HasCoproduct (fun _ : I => point.{u, max v w}) :=
  HasColimit.mk ⟨discreteCofan I, discreteCofanIsColimit I⟩

/-- Comparison with any chosen coproduct retains the actual discrete carrier. -/
def discreteCoproductIso (I : Type w)
    [HasCoproduct (fun _ : I => point.{u, max v w})] :
    discreteObj.{u, v, w} I ≅ ∐ fun _ : I => point.{u, max v w} :=
  (discreteCofanIsColimit I).coconePointUniqueUpToIso
    (coproductIsCoproduct (fun _ : I => point.{u, max v w}))

@[reassoc (attr := simp)]
theorem discreteCoproductIso_generator (I : Type w)
    [HasCoproduct (fun _ : I => point.{u, max v w})] (i : I) :
    discreteObjIncl.{u, v, w} I i ≫ (discreteCoproductIso I).hom =
      Sigma.ι (fun _ : I => point.{u, max v w}) i :=
  (discreteCofanIsColimit I).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun _ : I => point.{u, max v w})) ⟨i⟩

/-- An empty discrete index gives the actual initial carrier. -/
def discreteObjIsInitial (I : Type w) [IsEmpty I] :
    IsInitial (discreteObj.{u, v, w} I) :=
  IsInitial.ofUniqueHom
    (fun Y => ConcreteCategory.ofHom
      (show C(discreteObj.{u, v, w} I, Y) from
        ⟨fun x => isEmptyElim (show ULift.{v} I from x).down,
          by let _ := discreteObj_discreteTopology.{u, v, w} I
             exact continuous_of_discreteTopology⟩))
    (fun _ _ => by
      apply ConcreteCategory.hom_ext
      intro x
      exact isEmptyElim (show ULift.{v} I from x).down)

/-- A singleton discrete index is the native one-point CGWH object. -/
def discreteObjPointIso :
    discreteObj.{u, v, w} PUnit.{w + 1} ≅ point.{u, max v w} where
  hom := ConcreteCategory.ofHom
    ⟨fun _ => PUnit.unit, continuous_const⟩
  inv := (pointHomEquiv _).symm (ULift.up PUnit.unit)
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    change ULift.up PUnit.unit = x
    rcases x with ⟨⟨⟩⟩
    rfl
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro x
    change PUnit at x
    rcases x with ⟨⟩
    rfl

end CGWH
