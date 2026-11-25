/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorBalance
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.RingTheory.Flat.CategoryTheory
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseCompatibility
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Length

/-!
# Canonical balance and braiding of the original native Tor

The existing derived-bifunctor balance compares the two original resolution
variables. Deriving the actual tensor braiding then exchanges them. These
canonical natural isomorphisms retain the original native Tor objects and
arbitrary ring and module universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

universe u v

namespace ModuleCat.UniverseTensor

variable (R : Type u) [CommRing R]

/-- Canonical balance followed by the derived original braiding gives the
full two-variable native Tor symmetry in the actual module universe. -/
def nativeTorSymmetryNatIso (q : ℕ) :
    Tor (ModuleCat.{max u v} R) q ≅ (Tor (ModuleCat.{max u v} R) q).flip := by
  let C := ModuleCat.{max u v} R
  let F : C ⥤ C ⥤ C := curriedTensor C
  let T := Tor C q
  let B : Functor.LeftDerivedBalance.deriveFirst F q ≅ T.flip :=
    NatIso.ofComponents
      (fun M => NatIso.ofComponents
        (fun N => (CategoryTheory.NatIso.leftDerived
          (BraidedCategory.tensorLeftIsoTensorRight N).symm q).app M)
        (fun {N N'} g => by
          let e := (BraidedCategory.tensorLeftIsoTensorRight N).symm
          let e' := (BraidedCategory.tensorLeftIsoTensorRight N').symm
          let a : tensorRight N ⟶ tensorRight N' := (tensoringRight C).map g
          let b : tensorLeft N ⟶ tensorLeft N' := (tensoringLeft C).map g
          have w : a ≫ e'.hom = e.hom ≫ b := by
            have h := (BraidedCategory.curriedBraidingNatIso C).symm.hom.naturality g
            exact h
          have h := CategoryTheory.NatIso.leftDerived_hom_naturality e e' a b w q
          exact congrArg (fun t => t.app M) h))
      (fun {M M'} f => by
        apply NatTrans.ext
        funext N
        exact (CategoryTheory.NatIso.leftDerived
          (BraidedCategory.tensorLeftIsoTensorRight N).symm q).hom.naturality f)
  let E : Functor.LeftDerivedBalance.deriveSecond F q ≅
      Functor.LeftDerivedBalance.deriveFirst F q :=
    Functor.LeftDerivedBalance.balanceIso F
      (fun P hP => by
        let : Projective P := hP
        let : Module.Flat R P := inferInstance
        apply Functor.preservesHomology_of_map_exact
        intro S hS
        rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
        exact Module.Flat.lTensor_exact P hS)
      (fun P hP => by
        let : Projective P := hP
        let : Module.Flat R P := inferInstance
        apply Functor.preservesHomology_of_map_exact
        intro S hS
        rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
        exact Module.Flat.rTensor_exact P hS) q
  exact E ≪≫ B

/-- The canonical symmetry component keeps the original ordered native Tor
objects, with independent ring and coefficient-carrier universes. -/
def nativeTorSymmetry (M N : ModuleCat.{max u v} R) (q : ℕ) :
    (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) ≅
      (((Tor (ModuleCat.{max u v} R) q).obj N).obj M) :=
  ((nativeTorSymmetryNatIso R q).app M).app N

/-- The actual native Tor terms have equal lengths in the two original
Serre intersection orientations. -/
theorem nativeTor_length_symm (M N : ModuleCat.{max u v} R) (q : ℕ) :
    Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) =
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj N).obj M) :=
  (nativeTorSymmetry R M N q).toLinearEquiv.length_eq

end ModuleCat.UniverseTensor
