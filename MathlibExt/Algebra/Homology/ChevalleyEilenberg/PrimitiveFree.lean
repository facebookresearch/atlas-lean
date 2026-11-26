/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.PrimitiveCoordinates
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveFree
public import Mathlib.Algebra.Homology.Single

/-!
# Primitive CE chains of a free Lie module

For an R-Lie algebra L free as a module over a commutative ring, homogeneous primitive chains
are zero outside degree one. The primitive differential is zero in every degree, and the
degree-one component is canonically equivalent to L.

These coordinates give a chain isomorphism from the primitive kernel complex to L concentrated
in degree one. The carrier L is lifted by ULift.{u} into ModuleCat.{max u v} R. The
construction imposes no characteristic or finite-basis condition.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]


/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. For n : ℕ with n ≠ 1, primitiveDegree R L n = ⊥. -/
theorem primitiveDegree_eq_bot [Module.Free R L] (n : ℕ) (hn : n ≠ 1) :
    primitiveDegree R L n = ⊥ := by
  apply le_antisymm
  · intro a ha
    have h : a = 0 := ExteriorAlgebra.primitive_homogeneous_eq_zero R L n hn a
      ((mem_primitiveDegree R L n a).mp ha)
    simpa only [h] using (⊥ : Submodule R (⋀[R]^n L)).zero_mem
  · exact bot_le

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. For n ≠ 1 and a : P.X n, one has a = 0. -/
theorem nativePrimitiveDegree_eq_zero [Module.Free R L] (n : ℕ) (hn : n ≠ 1)
    (a : (nativePrimitiveComplex R L).X n) : a = 0 := by
  apply (nativePrimitiveDegreeEquiv R L n).injective
  have h : nativePrimitiveDegreeEquiv R L n a = 0 := by
    apply Subtype.ext
    exact ExteriorAlgebra.primitive_homogeneous_eq_zero R L n hn
      (nativePrimitiveDegreeEquiv R L n a : ⋀[R]^n L)
      ((mem_primitiveDegree R L n _).mp (nativePrimitiveDegreeEquiv R L n a).property)
  simpa only [map_zero] using h

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. For n : ℕ with n ≠ 1, IsZero (P.X n) holds. -/
theorem isZero_nativePrimitiveDegree [Module.Free R L] (n : ℕ) (hn : n ≠ 1) :
    IsZero ((nativePrimitiveComplex R L).X n) := by
  letI : Subsingleton ((nativePrimitiveComplex R L).X n) :=
    ⟨fun a b => (nativePrimitiveDegree_eq_zero R L n hn a).trans
      (nativePrimitiveDegree_eq_zero R L n hn b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. For every n : ℕ, primitiveDifferential R L n = 0 on
consecutive homogeneous primitive submodules. -/
theorem primitiveDifferential_eq_zero [Module.Free R L] (n : ℕ) :
    primitiveDifferential R L n = 0 := by
  cases n with
  | zero => exact primitiveDifferential_zero R L
  | succ n =>
      apply LinearMap.ext
      intro a
      have ha : a = 0 := by
        apply Subtype.ext
        exact ExteriorAlgebra.primitive_homogeneous_eq_zero R L ((n + 1) + 1) (by omega)
          a.1 ((mem_primitiveDegree R L ((n + 1) + 1) a.1).mp a.2)
      rw [ha, map_zero, LinearMap.zero_apply]

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. For n : ℕ, P.d (n + 1) n = 0. -/
theorem nativePrimitiveComplex_d_succ_zero [Module.Free R L] (n : ℕ) :
    (nativePrimitiveComplex R L).d (n + 1) n = 0 := by
  let e := (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n).mapIso
    (nativePrimitiveCoordinateIso R L)
  apply (cancel_mono e.hom).mp
  have hc := (nativePrimitiveCoordinateIso R L).hom.comm (n + 1) n
  have hd : (primitiveComplex R L).d (n + 1) n = 0 := by
    rw [primitiveComplex_d_succ, primitiveDifferential_eq_zero, ModuleCat.ofHom_zero]
    rfl
  have hZero := congrArg (fun d => (nativePrimitiveCoordinateIso R L).hom.f (n + 1) ≫ d) hd
  have hc' := hc.symm.trans (hZero.trans comp_zero)
  exact hc'.trans (zero_comp).symm

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. For any i,j : ℕ, P.d i j = 0, including nonadjacent
indices. -/
theorem nativePrimitiveComplex_d_eq_zero [Module.Free R L] (i j : ℕ) :
    (nativePrimitiveComplex R L).d i j = 0 := by
  by_cases h : j + 1 = i
  · subst i
    exact nativePrimitiveComplex_d_succ_zero R L j
  · exact (nativePrimitiveComplex R L).shape i j h

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. primitiveSingle R L is single at degree 1 of ModuleCat.of R (ULift.{u} L), with
shape down ℕ and zero objects in all other degrees. -/
def primitiveSingle : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.down ℕ) 1).obj
    (ModuleCat.of R (ULift.{u} L))

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. nativePrimitiveOneIso identifies P.X 1 with ModuleCat.of R (ULift.{u} L), using the
homogeneous primitive-one equivalence followed by the module lift. -/
def nativePrimitiveOneIso : (nativePrimitiveComplex R L).X 1 ≅ ModuleCat.of R (ULift.{u} L) :=
  ((nativePrimitiveDegreeOneEquiv R L).trans
    (ULift.moduleEquiv : ULift.{u} L ≃ₗ[R] L).symm).toModuleIso

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. nativePrimitiveToSingle : P ⟶ primitiveSingle R L has its
degree-one coordinate nativePrimitiveOneIso.hom and zero components in other degrees. -/
def nativePrimitiveToSingle [Module.Free R L] : nativePrimitiveComplex R L ⟶ primitiveSingle R L :=
  HomologicalComplex.mkHomToSingle (nativePrimitiveOneIso R L).hom
    (fun i _ => by rw [nativePrimitiveComplex_d_eq_zero, zero_comp])

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. nativePrimitiveFromSingle : primitiveSingle R L ⟶ P uses
nativePrimitiveOneIso.inv in degree one and zero components elsewhere. -/
def nativePrimitiveFromSingle [Module.Free R L] : primitiveSingle R L ⟶ nativePrimitiveComplex R L :=
  HomologicalComplex.mkHomFromSingle (nativePrimitiveOneIso R L).inv
    (fun j _ => by rw [nativePrimitiveComplex_d_eq_zero, comp_zero])

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Free R L. nativePrimitiveSingleIso : P ≅ primitiveSingle R L has
forward map nativePrimitiveToSingle and inverse nativePrimitiveFromSingle. -/
def nativePrimitiveSingleIso [Module.Free R L] :
    nativePrimitiveComplex R L ≅ primitiveSingle R L where
  hom := nativePrimitiveToSingle R L
  inv := nativePrimitiveFromSingle R L
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases h : n = 1
    · subst n
      change (nativePrimitiveToSingle R L).f 1 ≫ (nativePrimitiveFromSingle R L).f 1 = 𝟙 _
      rw [show (nativePrimitiveToSingle R L).f 1 = (nativePrimitiveOneIso R L).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).inv from HomologicalComplex.mkHomToSingle_f _ _,
        show (nativePrimitiveFromSingle R L).f 1 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
            (ModuleCat.of R (ULift.{u} L))).hom ≫ (nativePrimitiveOneIso R L).inv from
              HomologicalComplex.mkHomFromSingle_f _ _]
      have hs := (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
        (ModuleCat.of R (ULift.{u} L))).inv_hom_id
      have h := congrArg (fun f => (nativePrimitiveOneIso R L).hom ≫ f ≫
        (nativePrimitiveOneIso R L).inv) hs
      exact (Category.assoc _ _ _).trans (h.trans (by
        rw [Category.id_comp]
        exact (nativePrimitiveOneIso R L).hom_inv_id))
    · apply (isZero_nativePrimitiveDegree R L n h).eq_of_src
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases h : n = 1
    · subst n
      change (nativePrimitiveFromSingle R L).f 1 ≫ (nativePrimitiveToSingle R L).f 1 = 𝟙 _
      rw [show (nativePrimitiveToSingle R L).f 1 = (nativePrimitiveOneIso R L).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).inv from HomologicalComplex.mkHomToSingle_f _ _,
        show (nativePrimitiveFromSingle R L).f 1 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
            (ModuleCat.of R (ULift.{u} L))).hom ≫ (nativePrimitiveOneIso R L).inv from
              HomologicalComplex.mkHomFromSingle_f _ _]
      have hs := (nativePrimitiveOneIso R L).inv_hom_id
      have h := congrArg (fun f =>
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).inv) hs
      exact (Category.assoc _ _ _).trans (h.trans (by
        rw [Category.id_comp]
        exact (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).hom_inv_id))
    · apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 1
        (ModuleCat.of R (ULift.{u} L)) n h).eq_of_src

end ChevalleyEilenberg
