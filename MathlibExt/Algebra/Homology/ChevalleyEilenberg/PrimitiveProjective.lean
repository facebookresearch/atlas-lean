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
# Primitive CE chains of a projective Lie module

For an R-Lie algebra L projective as a module over a commutative ring, homogeneous primitive
chains vanish outside degree one. The restricted primitive differential is zero, and the
primitive complex is isomorphic to the lifted Lie carrier concentrated in degree one.

The isomorphism uses the primitive-one coordinate in degree one and the unique comparison of
zero objects elsewhere. Under freeness it equals the free-module comparison. These results
apply over every commutative ring.
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
coalgebra. Assume Module.Projective R L. For n : ℕ with n ≠ 1, primitiveDegree R L n = ⊥. -/
theorem primitiveDegree_eq_bot_of_projective [Module.Projective R L] (n : ℕ) (hn : n ≠ 1) :
    primitiveDegree R L n = ⊥ := by
  apply le_antisymm
  · intro a ha
    have h : a = 0 := ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective R L n hn a
      ((mem_primitiveDegree R L n a).mp ha)
    simpa only [h] using (⊥ : Submodule R (⋀[R]^n L)).zero_mem
  · exact bot_le

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. For n ≠ 1 and a : P.X n, one has a = 0. -/
theorem nativePrimitiveDegree_eq_zero_of_projective [Module.Projective R L]
    (n : ℕ) (hn : n ≠ 1) (a : (nativePrimitiveComplex R L).X n) : a = 0 := by
  apply (nativePrimitiveDegreeEquiv R L n).injective
  have h : nativePrimitiveDegreeEquiv R L n a = 0 := by
    apply Subtype.ext
    exact ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective R L n hn
      (nativePrimitiveDegreeEquiv R L n a : ⋀[R]^n L)
      ((mem_primitiveDegree R L n _).mp (nativePrimitiveDegreeEquiv R L n a).property)
  simpa only [map_zero] using h

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. For n ≠ 1, IsZero (P.X n) holds. -/
theorem isZero_nativePrimitiveDegree_of_projective [Module.Projective R L]
    (n : ℕ) (hn : n ≠ 1) : IsZero ((nativePrimitiveComplex R L).X n) := by
  letI : Subsingleton ((nativePrimitiveComplex R L).X n) :=
    ⟨fun a b => (nativePrimitiveDegree_eq_zero_of_projective R L n hn a).trans
      (nativePrimitiveDegree_eq_zero_of_projective R L n hn b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. For every n : ℕ, primitiveDifferential R L n = 0. -/
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

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. For n : ℕ, P.d (n + 1) n = 0. -/
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

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. For all i,j : ℕ, P.d i j = 0. -/
theorem nativePrimitiveComplex_d_eq_zero_of_projective [Module.Projective R L] (i j : ℕ) :
    (nativePrimitiveComplex R L).d i j = 0 := by
  by_cases h : j + 1 = i
  · subst i
    exact nativePrimitiveComplex_d_succ_zero_of_projective R L j
  · exact (nativePrimitiveComplex R L).shape i j h

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. nativePrimitiveProjectiveDegreeIso n identifies P.X n
with (primitiveSingle R L).X n. At n = 1 it uses nativePrimitiveOneIso and the single-object
coordinate, and elsewhere both objects are zero. -/
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

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. nativePrimitiveSingleIsoOfProjective : P ≅
primitiveSingle R L is the chain isomorphism with components
nativePrimitiveProjectiveDegreeIso. -/
def nativePrimitiveSingleIsoOfProjective [Module.Projective R L] :
    nativePrimitiveComplex R L ≅ primitiveSingle R L :=
  HomologicalComplex.Hom.isoOfComponents (nativePrimitiveProjectiveDegreeIso R L)
    (fun i j _ => by
      simp only [primitiveSingle, HomologicalComplex.single_obj_d,
        nativePrimitiveComplex_d_eq_zero_of_projective, comp_zero, zero_comp])

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. Assume Module.Projective R L. Its degree-one forward component is
nativePrimitiveOneIso.hom followed by the inverse single-object self coordinate into
(primitiveSingle R L).X 1. -/
theorem nativePrimitiveSingleIsoOfProjective_hom_f_one [Module.Projective R L] :
    (nativePrimitiveSingleIsoOfProjective R L).hom.f 1 =
      (nativePrimitiveOneIso R L).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
          (ModuleCat.of R (ULift.{u} L))).inv := by
  change (nativePrimitiveProjectiveDegreeIso R L 1).hom = _
  simp only [nativePrimitiveProjectiveDegreeIso, dif_pos rfl, dite_true,
    Iso.trans_hom, Iso.symm_hom]
  rfl

/-- Let R : Type u be a commutative ring and L : Type v an R-Lie algebra. Let P be its primitive
CE kernel complex, whose homogeneous submodules solve Δ(a) = 1⊗a + a⊗1 in the exterior
coalgebra. If Module.Free R L holds, nativePrimitiveSingleIsoOfProjective R L =
nativePrimitiveSingleIso R L as chain-complex isomorphisms. -/
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
