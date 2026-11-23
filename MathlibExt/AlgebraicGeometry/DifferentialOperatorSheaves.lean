/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.GeometricDifferentialOperators
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Differential operators on the actual local ring presheaf

An operator acts naturally on every subopen, not only on global functions.
This distinction is essential on compact complex manifolds. The bounded-order
condition is the source's actual coefficient-commutator recursion at each
subopen. Sheafifying the uniformly finite-order presheaf permits locally
bounded orders. Module categories use the resulting native ring sheaf.

This realizes the ordinary differential-operator carrier needed by the
holonomic and enhanced Riemann--Hilbert interfaces. Holonomicity, good
filtration, characteristic support and realization maps are additional
geometric constructions, not an arbitrary property attached to this ring.
The ordinary differential-operator recursion is source-covered by
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/RingTheory/DifferentialOperator/Defs.lean (Apache 2.0).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.RingTheory.GeometricDifferentialOperators

variable (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)

abbrev Inside (U : Opens M) := {V : Opens M // V ≤ U}

def restrictionLinear {U V : Opens M} (h : V ≤ U) :
    (O.obj (op U)) →ₗ[k] (O.obj (op V)) :=
  (O.map (homOfLE h).op).hom.toLinearMap

def naturalOperators (U : Opens M) :
    Subring (∀ V : Inside M U, Module.End k (O.obj (op V.val))) where
  carrier := {P | ∀ (V W : Inside M U) (h : W.val ≤ V.val),
    (restrictionLinear k M O h).comp (P V) = (P W).comp (restrictionLinear k M O h)}
  zero_mem' := by intro V W h; simp
  one_mem' := by intro V W h; ext x; rfl
  add_mem' := by
    intro P Q hP hQ V W h
    ext x
    change restrictionLinear k M O h (P V x + Q V x) =
      P W (restrictionLinear k M O h x) + Q W (restrictionLinear k M O h x)
    rw [map_add]
    exact congrArg₂ (· + ·) (LinearMap.congr_fun (hP V W h) x)
      (LinearMap.congr_fun (hQ V W h) x)
  neg_mem' := by
    intro P hP V W h
    ext x
    change restrictionLinear k M O h (-P V x) = -P W (restrictionLinear k M O h x)
    rw [map_neg]
    exact congrArg Neg.neg (LinearMap.congr_fun (hP V W h) x)
  mul_mem' := by
    intro P Q hP hQ V W h
    ext x
    change restrictionLinear k M O h (P V (Q V x)) =
      P W (Q W (restrictionLinear k M O h x))
    calc
      _ = P W (restrictionLinear k M O h (Q V x)) :=
        LinearMap.congr_fun (hP V W h) (Q V x)
      _ = _ := congrArg (P W) (LinearMap.congr_fun (hQ V W h) x)

def restrictNatural {U V : Opens M} (h : V ≤ U) :
    naturalOperators k M O U →+* naturalOperators k M O V where
  toFun P := ⟨fun W ↦ P.val ⟨W.val, W.property.trans h⟩,
    fun W Z hz ↦ P.property ⟨W.val, W.property.trans h⟩
      ⟨Z.val, Z.property.trans h⟩ hz⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def UniformFiniteOrder {U : Opens M} (P : naturalOperators k M O U) : Prop :=
  ∃ n : ℕ, ∀ V : Inside M U, OrderLE k (O.obj (op V.val)) n (P.val V)

def finiteOperatorRing (U : Opens M) : Subring (naturalOperators k M O U) :=
  Subring.closure {P | UniformFiniteOrder k M O P}

theorem restriction_finiteOrder {U V : Opens M} (h : V ≤ U)
    (P : naturalOperators k M O U) (hP : UniformFiniteOrder k M O P) :
    UniformFiniteOrder k M O (restrictNatural k M O h P) := by
  obtain ⟨n, hn⟩ := hP
  exact ⟨n, fun W ↦ hn ⟨W.val, W.property.trans h⟩⟩

def restrictFinite {U V : Opens M} (h : V ≤ U) :
    finiteOperatorRing k M O U →+* finiteOperatorRing k M O V :=
  ((restrictNatural k M O h).comp (finiteOperatorRing k M O U).subtype).codRestrict
    (finiteOperatorRing k M O V) (by
      have hh : finiteOperatorRing k M O U ≤
          (finiteOperatorRing k M O V).comap (restrictNatural k M O h) := by
        apply Subring.closure_le.mpr
        intro P hP
        exact Subring.subset_closure (restriction_finiteOrder k M O h P hP)
      intro P
      exact hh P.property)

def operatorPresheaf : (Opens M)ᵒᵖ ⥤ RingCat.{0} where
  obj U := RingCat.of (finiteOperatorRing k M O U.unop)
  map f := RingCat.ofHom (restrictFinite k M O f.unop.le)
  map_id U := by ext P V x; rfl
  map_comp f g := by ext P V x; rfl

/-- The differential ring sheaf is the native sheafification of the fixed
finite-order local-operator presheaf, under its true sheafification input. -/
def differentialRing [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}] :
    Sheaf (Opens.grothendieckTopology M) RingCat.{0} :=
  (presheafToSheaf (Opens.grothendieckTopology M) RingCat.{0}).obj (operatorPresheaf k M O)

abbrev DModule [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}] :=
  SheafOfModules.{0} (differentialRing k M O)

end MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves
