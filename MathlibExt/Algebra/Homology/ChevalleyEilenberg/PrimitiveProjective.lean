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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.PrimitiveFree
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveProjective

/-!
# Primitive chains for projective Lie carriers

For a Lie algebra whose underlying module over a commutative ring is projective, homogeneous
primitive chains vanish outside degree one and the primitive differential is zero. The
primitive complex is isomorphic to the Lie carrier concentrated in degree one.

The categorical carrier uses the corresponding universe lift, and the construction agrees with
the free-carrier specialization.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The homogeneous primitive submodule vanishes outside degree one on a projective module. -/
theorem primitiveDegree_eq_bot_of_projective [Module.Projective R L] (n : ℕ) (hn : n ≠ 1) :
    primitiveDegree R L n = ⊥ := by
  apply le_antisymm
  · intro a ha
    have h : a = 0 := ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective R L n hn a
      ((mem_primitiveDegree R L n a).mp ha)
    simpa only [h] using (⊥ : Submodule R (⋀[R]^n L)).zero_mem
  · exact bot_le

/-- Every primitive component outside degree one is zero on a projective module. -/
theorem nativePrimitiveDegree_eq_zero_of_projective [Module.Projective R L]
    (n : ℕ) (hn : n ≠ 1) (a : (nativePrimitiveComplex R L).X n) : a = 0 := by
  apply (nativePrimitiveDegreeEquiv R L n).injective
  have h : nativePrimitiveDegreeEquiv R L n a = 0 := by
    apply Subtype.ext
    exact ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective R L n hn
      (nativePrimitiveDegreeEquiv R L n a : ⋀[R]^n L)
      ((mem_primitiveDegree R L n _).mp (nativePrimitiveDegreeEquiv R L n a).property)
  simpa only [map_zero] using h

/-- The component is a zero object in every other degree. -/
theorem isZero_nativePrimitiveDegree_of_projective [Module.Projective R L]
    (n : ℕ) (hn : n ≠ 1) : IsZero ((nativePrimitiveComplex R L).X n) := by
  letI : Subsingleton ((nativePrimitiveComplex R L).X n) :=
    ⟨fun a b => (nativePrimitiveDegree_eq_zero_of_projective R L n hn a).trans
      (nativePrimitiveDegree_eq_zero_of_projective R L n hn b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The restricted primitive differential is zero for projective underlying modules. -/
theorem primitiveDifferential_eq_zero_of_projective [Module.Projective R L] (n : ℕ) :
    primitiveDifferential R L n = 0 := by
  cases n with
  | zero => exact primitiveDifferential_zero R L
  | succ n =>
      apply LinearMap.ext
      intro a
      have ha : a = 0 := by
        apply Subtype.ext
        exact ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective R L ((n + 1) + 1)
          (by omega) a.1 ((mem_primitiveDegree R L ((n + 1) + 1) a.1).mp a.2)
      rw [ha, map_zero, LinearMap.zero_apply]

/-- The primitive differential vanishes on every adjacent pair of degrees. -/
theorem nativePrimitiveComplex_d_succ_zero_of_projective [Module.Projective R L] (n : ℕ) :
    (nativePrimitiveComplex R L).d (n + 1) n = 0 := by
  let e := (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n).mapIso
    (nativePrimitiveCoordinateIso R L)
  apply (cancel_mono e.hom).mp
  have hc := (nativePrimitiveCoordinateIso R L).hom.comm (n + 1) n
  have hd : (primitiveComplex R L).d (n + 1) n = 0 := by
    rw [primitiveComplex_d_succ, primitiveDifferential_eq_zero_of_projective, ModuleCat.ofHom_zero]
    rfl
  have hZero := congrArg (fun d => (nativePrimitiveCoordinateIso R L).hom.f (n + 1) ≫ d) hd
  exact (hc.symm.trans (hZero.trans comp_zero)).trans (zero_comp).symm

/-- Every primitive differential is zero on a projective module. -/
theorem nativePrimitiveComplex_d_eq_zero_of_projective [Module.Projective R L] (i j : ℕ) :
    (nativePrimitiveComplex R L).d i j = 0 := by
  by_cases h : j + 1 = i
  · subst i
    exact nativePrimitiveComplex_d_succ_zero_of_projective R L j
  · exact (nativePrimitiveComplex R L).shape i j h

/-- The degree-one coordinate and zero objects supply the singleton components. -/
def nativePrimitiveProjectiveDegreeIso [Module.Projective R L] (n : ℕ) :
    (nativePrimitiveComplex R L).X n ≅ (primitiveSingle R L).X n := by
  by_cases h : n = 1
  · subst n
    exact nativePrimitiveOneIso R L ≪≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
        (ModuleCat.of R (ULift.{u} L))).symm
  · exact (isZero_nativePrimitiveDegree_of_projective R L n h).iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 1
        (ModuleCat.of R (ULift.{u} L)) n h)

/-- The primitive complex of a projective Lie module is its carrier in degree one, in every
characteristic and with the universe comparison. -/
def nativePrimitiveSingleIsoOfProjective [Module.Projective R L] :
    nativePrimitiveComplex R L ≅ primitiveSingle R L :=
  HomologicalComplex.Hom.isoOfComponents (nativePrimitiveProjectiveDegreeIso R L)
    (fun i j _ => by
      simp only [primitiveSingle, HomologicalComplex.single_obj_d,
        nativePrimitiveComplex_d_eq_zero_of_projective, comp_zero, zero_comp])

/-- The projective comparison has exactly the degree-one coordinate. -/
theorem nativePrimitiveSingleIsoOfProjective_hom_f_one [Module.Projective R L] :
    (nativePrimitiveSingleIsoOfProjective R L).hom.f 1 =
      (nativePrimitiveOneIso R L).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).inv := by
  change (nativePrimitiveProjectiveDegreeIso R L 1).hom = _
  simp only [nativePrimitiveProjectiveDegreeIso, dif_pos rfl, dite_true,
    Iso.trans_hom, Iso.symm_hom]
  rfl

/-- The projective theorem preserves the free specialization as the same isomorphism. -/
theorem nativePrimitiveSingleIsoOfProjective_eq_of_free [Module.Free R L] :
    nativePrimitiveSingleIsoOfProjective R L = nativePrimitiveSingleIso R L := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro n
  by_cases h : n = 1
  · subst n
    rw [nativePrimitiveSingleIsoOfProjective_hom_f_one]
    change (nativePrimitiveOneIso R L).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).inv = (nativePrimitiveToSingle R L).f 1
    rw [nativePrimitiveToSingle, HomologicalComplex.mkHomToSingle_f]
  · apply (isZero_nativePrimitiveDegree_of_projective R L n h).eq_of_src

end ChevalleyEilenberg
