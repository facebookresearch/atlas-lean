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
# Primitive chains for free Lie carriers

For a Lie algebra whose underlying module over a commutative ring is free, the primitive chain
complex vanishes outside degree one. Its differential is zero, and it is canonically
isomorphic to the Lie carrier concentrated in degree one.

A universe lift places the Lie carrier in the common module category while retaining the
ground-ring action.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]


/-- On a free module, the homogeneous primitive submodule vanishes outside degree one. -/
theorem primitiveDegree_eq_bot [Module.Free R L] (n : ℕ) (hn : n ≠ 1) :
    primitiveDegree R L n = ⊥ := by
  apply le_antisymm
  · intro a ha
    have h : a = 0 := ExteriorAlgebra.primitive_homogeneous_eq_zero R L n hn a
      ((mem_primitiveDegree R L n a).mp ha)
    simpa only [h] using (⊥ : Submodule R (⋀[R]^n L)).zero_mem
  · exact bot_le

/-- On a free module, every element of a primitive component outside degree one is zero. -/
theorem nativePrimitiveDegree_eq_zero [Module.Free R L] (n : ℕ) (hn : n ≠ 1)
    (a : (nativePrimitiveComplex R L).X n) : a = 0 := by
  apply (nativePrimitiveDegreeEquiv R L n).injective
  have h : nativePrimitiveDegreeEquiv R L n a = 0 := by
    apply Subtype.ext
    exact ExteriorAlgebra.primitive_homogeneous_eq_zero R L n hn
      (nativePrimitiveDegreeEquiv R L n a : ⋀[R]^n L)
      ((mem_primitiveDegree R L n _).mp (nativePrimitiveDegreeEquiv R L n a).property)
  simpa only [map_zero] using h

/-- The primitive object in any other degree is a zero object. -/
theorem isZero_nativePrimitiveDegree [Module.Free R L] (n : ℕ) (hn : n ≠ 1) :
    IsZero ((nativePrimitiveComplex R L).X n) := by
  letI : Subsingleton ((nativePrimitiveComplex R L).X n) :=
    ⟨fun a b => (nativePrimitiveDegree_eq_zero R L n hn a).trans
      (nativePrimitiveDegree_eq_zero R L n hn b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Every restricted primitive differential is zero on a free module. -/
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

/-- The primitive differential vanishes on every adjacent pair of degrees. -/
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

/-- Every primitive differential is zero, including the off-shape components. -/
theorem nativePrimitiveComplex_d_eq_zero [Module.Free R L] (i j : ℕ) :
    (nativePrimitiveComplex R L).d i j = 0 := by
  by_cases h : j + 1 = i
  · subst i
    exact nativePrimitiveComplex_d_succ_zero R L j
  · exact (nativePrimitiveComplex R L).shape i j h

/-- The Lie module in the working universe, concentrated in degree one. -/
def primitiveSingle : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.down ℕ) 1).obj
    (ModuleCat.of R (ULift.{u} L))

/-- The degree-one primitive component identifies with the carrier after lifting. -/
def nativePrimitiveOneIso : (nativePrimitiveComplex R L).X 1 ≅ ModuleCat.of R (ULift.{u} L) :=
  ((nativePrimitiveDegreeOneEquiv R L).trans
    (ULift.moduleEquiv : ULift.{u} L ≃ₗ[R] L).symm).toModuleIso

/-- The primitive complex maps to the degree-one singleton by the coordinates. -/
def nativePrimitiveToSingle [Module.Free R L] : nativePrimitiveComplex R L ⟶ primitiveSingle R L :=
  HomologicalComplex.mkHomToSingle (nativePrimitiveOneIso R L).hom
    (fun i _ => by rw [nativePrimitiveComplex_d_eq_zero, zero_comp])

/-- The degree-one singleton maps back to the primitive kernel by the inverse coordinates. -/
def nativePrimitiveFromSingle [Module.Free R L] : primitiveSingle R L ⟶ nativePrimitiveComplex R L :=
  HomologicalComplex.mkHomFromSingle (nativePrimitiveOneIso R L).inv
    (fun j _ => by rw [nativePrimitiveComplex_d_eq_zero, comp_zero])

/-- Over every commutative ring, the primitive complex of a free Lie module is the Lie module
concentrated in degree one, with the necessary universe comparison. -/
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
