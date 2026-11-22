/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedTopCat
public import MathlibExt.Topology.Category.TopCat.ZerothHomotopy
public import MathlibExt.Topology.Homotopy.HomotopyGroupMap
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Homotopy groups of pointed topological spaces

This file packages the existing cube-based homotopy types as functors on
pointed topological spaces.  All degrees form a Type-valued functor, while
positive degrees additionally form a group-valued functor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u w

namespace PointedTopCat

/-- The point selected by a pointed topological space. -/
def underlyingBasepoint (X : PointedTopCat.{u}) : X.right :=
  X.hom PUnit.unit

/-- A pointed map preserves the selected point. -/
theorem underlyingBasepoint_naturality
    {X Y : PointedTopCat.{u}} (f : X ⟶ Y) :
    f.right (underlyingBasepoint X) = underlyingBasepoint Y :=
  ConcreteCategory.congr_hom (Under.w f) PUnit.unit

/-- The equivalence of homotopy groups induced by an equality of basepoints. -/
noncomputable def homotopyGroupBasepointCastEquiv
    (N : Type w) {Y : Type u} [TopologicalSpace Y]
    {y y' : Y} (h : y = y') :
    HomotopyGroup N Y y ≃ HomotopyGroup N Y y' := by
  subst y'
  exact Equiv.refl _

private theorem homotopyGroupBasepointCastEquiv_apply_back
    (N : Type w) {Y : Type u} [TopologicalSpace Y]
    {y y' : Y} (h : y = y') (a : HomotopyGroup N Y y) :
    cast (congrArg (fun z => HomotopyGroup N Y z) h.symm)
        (homotopyGroupBasepointCastEquiv N h a) = a := by
  subst y'
  rfl

private theorem homotopyGroupBasepointCastEquiv_map_trans
    (N : Type w) {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x' : X} {y : Y}
    (h : x = x') (h' : f x' = y)
    (a : HomotopyGroup N X x) :
    homotopyGroupBasepointCastEquiv N
        ((congrArg (fun z => f z) h).trans h')
        (HomotopyGroup.map f a) =
      homotopyGroupBasepointCastEquiv N h'
        (HomotopyGroup.map f
          (homotopyGroupBasepointCastEquiv N h a)) := by
  subst x'
  subst y
  rfl

/-- The degree-`n` cube-based homotopy type, functorial in pointed spaces. -/
noncomputable def homotopyGroupTypeFunctor (n : ℕ) :
    PointedTopCat.{u} ⥤ Type u where
  obj X := HomotopyGroup.Pi n X.right (underlyingBasepoint X)
  map {X Y} f := ↾fun a =>
    homotopyGroupBasepointCastEquiv (Fin n)
      (underlyingBasepoint_naturality f)
      (HomotopyGroup.map f.right.hom a)
  map_id X := by
    ext a
    change homotopyGroupBasepointCastEquiv (Fin n) _
        (HomotopyGroup.map (ContinuousMap.id X.right) a) = a
    rw [HomotopyGroup.map_id]
    have h : underlyingBasepoint_naturality (𝟙 X) = rfl :=
      Subsingleton.elim _ _
    rw [h]
    rfl
  map_comp {X Y Z} f g := by
    ext a
    change homotopyGroupBasepointCastEquiv (Fin n) _
        (HomotopyGroup.map (g.right.hom.comp f.right.hom) a) =
      homotopyGroupBasepointCastEquiv (Fin n)
        (underlyingBasepoint_naturality g)
        (HomotopyGroup.map g.right.hom
          (homotopyGroupBasepointCastEquiv (Fin n)
            (underlyingBasepoint_naturality f)
            (HomotopyGroup.map f.right.hom a)))
    rw [HomotopyGroup.map_comp]
    have h : underlyingBasepoint_naturality (f ≫ g) =
        (congrArg (fun z => g.right z)
          (underlyingBasepoint_naturality f)).trans
            (underlyingBasepoint_naturality g) :=
      Subsingleton.elim _ _
    rw [h]
    exact homotopyGroupBasepointCastEquiv_map_trans
      (Fin n) g.right.hom
      (underlyingBasepoint_naturality f)
      (underlyingBasepoint_naturality g)
      (HomotopyGroup.map f.right.hom a)

/-- Object formula for the all-degree homotopy functor. -/
@[simp]
theorem homotopyGroupTypeFunctor_obj (n : ℕ) (X : PointedTopCat.{u}) :
    (homotopyGroupTypeFunctor n).obj X =
      HomotopyGroup.Pi n X.right (underlyingBasepoint X) :=
  rfl

/-- After reversing point transport, the all-degree functor map is the
existing cube-map construction. -/
theorem homotopyGroupTypeFunctor_map (n : ℕ)
    {X Y : PointedTopCat.{u}} (f : X ⟶ Y)
    (a : (homotopyGroupTypeFunctor n).obj X) :
    cast
        (congrArg
          (fun y => HomotopyGroup.Pi n Y.right y)
          (underlyingBasepoint_naturality f).symm)
        ((homotopyGroupTypeFunctor n).map f a) =
      HomotopyGroup.map f.right.hom a := by
  change cast (congrArg _ (underlyingBasepoint_naturality f).symm)
      (homotopyGroupBasepointCastEquiv (Fin n)
        (underlyingBasepoint_naturality f)
        (HomotopyGroup.map f.right.hom a)) = _
  exact homotopyGroupBasepointCastEquiv_apply_back
    (Fin n) (underlyingBasepoint_naturality f)
    (HomotopyGroup.map f.right.hom a)

/-- The multiplicative homotopy-group equivalence induced by an equality of basepoints. -/
noncomputable def homotopyGroupBasepointCastMulEquiv
    (n : ℕ) {Y : Type u} [TopologicalSpace Y]
    {y y' : Y} (h : y = y') :
    HomotopyGroup.Pi (n + 1) Y y ≃*
      HomotopyGroup.Pi (n + 1) Y y' := by
  subst y'
  exact MulEquiv.refl _

/-- The positive-degree homotopy-group homomorphism induced by a pointed map. -/
noncomputable def homotopyGroupPositiveMapHom
    (n : ℕ) {X Y : PointedTopCat.{u}} (f : X ⟶ Y) :
    HomotopyGroup.Pi (n + 1) X.right (underlyingBasepoint X) →*
      HomotopyGroup.Pi (n + 1) Y.right (underlyingBasepoint Y) :=
  (homotopyGroupBasepointCastMulEquiv n
    (underlyingBasepoint_naturality f)).toMonoidHom.comp
      (HomotopyGroup.mapHom (N := Fin (n + 1)) f.right.hom)

private theorem homotopyGroupBasepointCastMulEquiv_apply_eq_cast
    (n : ℕ) {Y : Type u} [TopologicalSpace Y]
    {y y' : Y} (h : y = y')
    (a : HomotopyGroup.Pi (n + 1) Y y) :
    homotopyGroupBasepointCastMulEquiv n h a =
      homotopyGroupBasepointCastEquiv (Fin (n + 1)) h a := by
  subst y'
  rfl

private theorem homotopyGroupPositiveMapHom_apply
    (n : ℕ) {X Y : PointedTopCat.{u}} (f : X ⟶ Y)
    (a : HomotopyGroup.Pi (n + 1) X.right (underlyingBasepoint X)) :
    homotopyGroupPositiveMapHom n f a =
      (homotopyGroupTypeFunctor (n + 1)).map f a := by
  change homotopyGroupBasepointCastMulEquiv n
      (underlyingBasepoint_naturality f)
      (HomotopyGroup.map f.right.hom a) =
    homotopyGroupBasepointCastEquiv (Fin (n + 1))
      (underlyingBasepoint_naturality f)
      (HomotopyGroup.map f.right.hom a)
  exact homotopyGroupBasepointCastMulEquiv_apply_eq_cast n _ _

/-- Positive cube-based homotopy groups, functorial as bundled groups. -/
noncomputable def homotopyGroupPositiveFunctor (n : ℕ) :
    PointedTopCat.{u} ⥤ GrpCat.{u} where
  obj X := GrpCat.of
    (HomotopyGroup.Pi (n + 1) X.right (underlyingBasepoint X))
  map f := GrpCat.ofHom (homotopyGroupPositiveMapHom n f)
  map_id X := by
    apply GrpCat.hom_ext
    ext a
    change homotopyGroupPositiveMapHom n (𝟙 X) a = a
    rw [homotopyGroupPositiveMapHom_apply]
    exact ConcreteCategory.congr_hom
      ((homotopyGroupTypeFunctor (n + 1)).map_id X) a
  map_comp f g := by
    apply GrpCat.hom_ext
    ext a
    change homotopyGroupPositiveMapHom n (f ≫ g) a =
      homotopyGroupPositiveMapHom n g
        (homotopyGroupPositiveMapHom n f a)
    rw [homotopyGroupPositiveMapHom_apply,
      homotopyGroupPositiveMapHom_apply,
      homotopyGroupPositiveMapHom_apply]
    exact ConcreteCategory.congr_hom
      ((homotopyGroupTypeFunctor (n + 1)).map_comp f g) a

/-- Object formula for the positive homotopy-group functor. -/
@[simp]
theorem homotopyGroupPositiveFunctor_obj (n : ℕ)
    (X : PointedTopCat.{u}) :
    (homotopyGroupPositiveFunctor n).obj X =
      GrpCat.of
        (HomotopyGroup.Pi (n + 1) X.right (underlyingBasepoint X)) :=
  rfl

/-- The underlying function of the positive-degree group map is the map of
the all-degree Type functor. -/
@[simp]
theorem homotopyGroupPositiveFunctor_map (n : ℕ)
    {X Y : PointedTopCat.{u}} (f : X ⟶ Y)
    (a : HomotopyGroup.Pi (n + 1) X.right (underlyingBasepoint X)) :
    (@GrpCat.Hom.hom
      (GrpCat.of (HomotopyGroup.Pi (n + 1) X.right (underlyingBasepoint X)))
      (GrpCat.of (HomotopyGroup.Pi (n + 1) Y.right (underlyingBasepoint Y)))
      ((homotopyGroupPositiveFunctor n).map f)) a =
      (homotopyGroupTypeFunctor (n + 1)).map f a :=
  homotopyGroupPositiveMapHom_apply n f a

/-- Forgetting the group structure on the positive-degree functor recovers
the all-degree functor in degree `n + 1`. -/
noncomputable def homotopyGroupPositiveFunctorForgetIso (n : ℕ) :
    homotopyGroupPositiveFunctor n ⋙ CategoryTheory.forget GrpCat ≅
      homotopyGroupTypeFunctor (n + 1) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    ext a
    exact homotopyGroupPositiveFunctor_map n f a)

/-- Degree zero agrees with the ordinary set of path components. -/
noncomputable def homotopyGroupZeroEquivZerothHomotopy
    (X : PointedTopCat.{u}) :
    (homotopyGroupTypeFunctor 0).obj X ≃ ZerothHomotopy X.right :=
  HomotopyGroup.pi0EquivZerothHomotopy

/-- The degree-zero comparison is natural in pointed maps. -/
theorem homotopyGroupZeroEquivZerothHomotopy_naturality
    {X Y : PointedTopCat.{u}} (f : X ⟶ Y)
    (a : (homotopyGroupTypeFunctor 0).obj X) :
    homotopyGroupZeroEquivZerothHomotopy Y
        ((homotopyGroupTypeFunctor 0).map f a) =
      TopCat.zerothHomotopyMap f.right
        (homotopyGroupZeroEquivZerothHomotopy X a) := by
  have hcast {Z : Type u} [TopologicalSpace Z] {z z' : Z}
      (h : z = z') (q : HomotopyGroup.Pi 0 Z z) :
      HomotopyGroup.pi0EquivZerothHomotopy
          (homotopyGroupBasepointCastEquiv (Fin 0) h q) =
        HomotopyGroup.pi0EquivZerothHomotopy q := by
    subst z'
    rfl
  change HomotopyGroup.pi0EquivZerothHomotopy
      (homotopyGroupBasepointCastEquiv (Fin 0)
        (underlyingBasepoint_naturality f)
        (HomotopyGroup.map f.right.hom a)) = _
  rw [hcast]
  induction a using Quotient.inductionOn with
  | _ p => rfl

/-- Degree one agrees multiplicatively with the fundamental group. -/
noncomputable def homotopyGroupOneMulEquivFundamentalGroup
    (X : PointedTopCat.{u}) :
    (homotopyGroupPositiveFunctor 0).obj X ≃*
      FundamentalGroup X.right (underlyingBasepoint X) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup

end PointedTopCat
