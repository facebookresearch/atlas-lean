/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Chain complexes reduced modulo a ring element

The existing `QuotSMulTop.map` is linear over the original ring.  Since the
quotient modules are naturally modules over `R ⧸ Ideal.span {x}`, the same map
is also linear over that quotient ring.  This file packages the latter map as
`QuotSMulTop.mapLinear` and applies it degreewise to a chain complex.

The quotient complex keeps the original index type and carrier universes.  Its
term in degree `i` is `QuotSMulTop x (C.X i)`, and its differential is induced
by `C.d i j`.  The public term and differential formulas make these choices
available to downstream exactness arguments without unfolding the structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w z

namespace QuotSMulTop

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The map induced on quotients by `f`, regarded as linear over
`R ⧸ Ideal.span {x}`. -/
def mapLinear (x : R) (f : M →ₗ[R] N) :
    QuotSMulTop x M →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N :=
  (map x f).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))

/-- Restricting `mapLinear` back to `R` recovers the original quotient map. -/
@[simp]
theorem mapLinear_restrictScalars (x : R) (f : M →ₗ[R] N) :
    (mapLinear x f).restrictScalars R = map x f :=
  rfl

/-- `mapLinear` sends the class of `m` to the class of `f m`. -/
@[simp]
theorem mapLinear_apply_mk (x : R) (f : M →ₗ[R] N) (m : M) :
    mapLinear x f (Submodule.Quotient.mk m) =
      (Submodule.Quotient.mk (f m) : QuotSMulTop x N) :=
  rfl

/-- A surjective linear map induces a surjective quotient-ring linear map. -/
theorem mapLinear_surjective (x : R) {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : Function.Surjective (mapLinear x f) :=
  map_surjective x hf

/-- Quotient reduction preserves an exact pair whose second map is surjective. -/
theorem mapLinear_exact
    {P : Type z} [AddCommGroup P] [Module R P]
    (x : R) {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (mapLinear x f) (mapLinear x g) :=
  map_exact x hfg hg

/-- Quotient reduction sends the zero map to the zero map. -/
@[simp]
theorem mapLinear_zero (x : R) :
    mapLinear x (0 : M →ₗ[R] N) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- Quotient reduction sends the identity map to the identity map. -/
@[simp]
theorem mapLinear_id (x : R) :
    mapLinear x (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- Quotient reduction respects composition. -/
@[simp]
theorem mapLinear_comp
    {P : Type z} [AddCommGroup P] [Module R P]
    (x : R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    mapLinear x (g.comp f) = (mapLinear x g).comp (mapLinear x f) := by
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

end QuotSMulTop

namespace ChainComplex

variable {R : Type u} [CommRing R]
variable {ι : Type w} [AddRightCancelSemigroup ι] [One ι]

/-- Reduce every term and differential of a chain complex modulo `x`.

The resulting complex is linear over `R ⧸ Ideal.span {x}` and uses the same
indexing and complex shape as the original complex. -/
def quotSMulTop (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) :
    ChainComplex (ModuleCat.{v} (R ⧸ Ideal.span {x})) ι where
  X i := ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (C.X i))
  d i j := ModuleCat.ofHom (QuotSMulTop.mapLinear x (C.d i j).hom)
  shape i j hij := by
    apply ModuleCat.hom_ext
    simp [C.shape i j hij]
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    have hzero := congrArg ModuleCat.Hom.hom (C.d_comp_d i j k)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at hzero
    rw [← QuotSMulTop.mapLinear_comp, hzero, QuotSMulTop.mapLinear_zero]

/-- The degree-`i` term of the quotient complex is the quotient of the
degree-`i` term of the original complex. -/
@[simp]
theorem quotSMulTop_X (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) (i : ι) :
    (C.quotSMulTop x).X i =
      ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (C.X i)) :=
  rfl

/-- The differential of the quotient complex is induced by the original
differential. -/
@[simp]
theorem quotSMulTop_d (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) (i j : ι) :
    (C.quotSMulTop x).d i j =
      ModuleCat.ofHom (QuotSMulTop.mapLinear x (C.d i j).hom) :=
  rfl

/-- Linear-map form of `ChainComplex.quotSMulTop_d`. -/
@[simp]
theorem quotSMulTop_d_hom
    (C : ChainComplex (ModuleCat.{v} R) ι) (x : R) (i j : ι) :
    ((C.quotSMulTop x).d i j).hom =
      QuotSMulTop.mapLinear x (C.d i j).hom :=
  rfl

end ChainComplex
