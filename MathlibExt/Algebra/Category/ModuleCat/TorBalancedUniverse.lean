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
# Symmetry of Tor over a commutative ring

Let `R : Type u` be a commutative ring and work with module carriers in universe `max u v`.
The balance isomorphism between the two resolution variables, followed by the derived tensor
braiding, gives a natural symmetry `Tor_q^R(M, N) ≅ Tor_q^R(N, M)` in every natural degree.

This symmetry gives equality of the module lengths of the two Tor objects. The length
statement includes infinite lengths and imposes no finite-length hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

universe u v

namespace ModuleCat.UniverseTensor

variable (R : Type u) [CommRing R]

/-- Tor bifunctor is naturally isomorphic to its variable flip.

For every natural `q`, balance of the two tensor derivations and the derived braiding give a
natural isomorphism from the Tor bifunctor to its flip in `ModuleCat.{max u v} R`. -/
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

/-- Symmetry isomorphism of two Tor module objects.

For modules `M` and `N` in `ModuleCat.{max u v} R`, evaluate the Tor symmetry to obtain
`Tor_q^R(M, N) ≅ Tor_q^R(N, M)`. -/
def nativeTorSymmetry (M N : ModuleCat.{max u v} R) (q : ℕ) :
    (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) ≅
      (((Tor (ModuleCat.{max u v} R) q).obj N).obj M) :=
  ((nativeTorSymmetryNatIso R q).app M).app N

/-- Module length of Tor is symmetric in its two inputs.

For every natural `q`, `Module.length R (Tor_q^R(M, N)) = Module.length R (Tor_q^R(N, M))`.
The equality follows from the linear equivalence induced by Tor symmetry. -/
theorem nativeTor_length_symm (M N : ModuleCat.{max u v} R) (q : ℕ) :
    Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) =
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj N).obj M) :=
  (nativeTorSymmetry R M N q).toLinearEquiv.length_eq

end ModuleCat.UniverseTensor
