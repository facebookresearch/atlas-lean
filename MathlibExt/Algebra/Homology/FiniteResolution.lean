/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import MathlibExt.Algebra.Homology.ChainComplexAugmentation

/-!
# Finite resolutions in an abelian target

This file packages a nonfunctorial finite resolution of an object `X` in an
abelian category `A` by objects of a preadditive category `P`.  The terms form
a bounded nonnegative chain complex in `P`; after applying an additive functor
`i : P ⥤ A`, an augmentation to the complex concentrated at `X` in degree zero
is required to be a quasi-isomorphism.

The structure records one resolution at a time.  It does not choose
resolutions functorially and does not assert comparison or independence of
resolution choices.

## Main definitions

* `CategoryTheory.Abelian.FiniteResolution`
* `CategoryTheory.Abelian.FiniteResolution.mappedComplex`

## Main results

* `CategoryTheory.Abelian.FiniteResolution.mappedComplex_isZero_above`
* `CategoryTheory.Abelian.FiniteResolution.single`
* `CategoryTheory.Abelian.FiniteResolution.ofShortExact`
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory Limits ChainComplex HomologicalComplex

universe vP uP vA uA

namespace CategoryTheory.Abelian

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- A bounded nonnegative complex in `P` whose image under `i` resolves `X`.

No functorial choice of finite resolutions is asserted.  The bound is
inclusive: terms in degrees strictly greater than `bound` are zero. -/
structure FiniteResolution (i : P ⥤ A) [i.Additive] (X : A) where
  /-- The resolving nonnegative chain complex. -/
  complex : ChainComplex P ℕ
  /-- The augmentation of the mapped complex to `X` in degree zero. -/
  augmentation :
    ((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj complex) ⟶
      (ChainComplex.single₀ A).obj X
  /-- The augmentation is a quasi-isomorphism. -/
  [quasiIso : QuasiIso augmentation]
  /-- An inclusive upper bound for the support of `complex`. -/
  bound : ℕ
  /-- Terms strictly above `bound` are zero objects. -/
  isZero_above : ∀ n : ℕ, bound < n → IsZero (complex.X n)

attribute [instance] FiniteResolution.quasiIso

namespace FiniteResolution

variable {i : P ⥤ A} [i.Additive] {X : A}

/-- The resolving complex after applying the additive functor `i`. -/
noncomputable abbrev mappedComplex (R : FiniteResolution i X) :
    ChainComplex A ℕ :=
  (i.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex

/-- The mapped resolution is zero in every degree strictly above its bound. -/
theorem mappedComplex_isZero_above (R : FiniteResolution i X)
    (n : ℕ) (hn : R.bound < n) :
    IsZero (R.mappedComplex.X n) :=
  i.map_isZero (R.isZero_above n hn)

/-- A chain complex concentrated in degree zero is zero above any natural
bound.  In particular, this applies when the common bound is zero. -/
theorem single₀_isZero_above (X : A) (N n : ℕ) (hn : N < n) :
    IsZero (((ChainComplex.single₀ A).obj X).X n) :=
  HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down ℕ) 0 X n (by omega)

/-- The degree-zero component of the augmentation, with target the resolved
object rather than the definitionally equal single-complex carrier. -/
noncomputable abbrev augmentation₀ (Q : FiniteResolution i X) :
    Q.mappedComplex.X 0 ⟶ X :=
  Q.augmentation.f 0

/-- The mapped finite resolution is exact in every positive degree. -/
theorem mappedComplex_exactAt_succ (Q : FiniteResolution i X) (n : ℕ) :
    Q.mappedComplex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' Q.augmentation (n + 1)
    (ChainComplex.exactAt_succ_single_obj X n)]
  infer_instance

/-- The adjacent mapped short complex is exact in every positive degree. -/
theorem mappedExact_succ (Q : FiniteResolution i X) (n : ℕ) :
    (ShortComplex.mk
      (Q.mappedComplex.d (n + 2) (n + 1))
      (Q.mappedComplex.d (n + 1) n)
      (Q.mappedComplex.d_comp_d (n + 2) (n + 1) n)).Exact := by
  have hQ := Q.mappedComplex_exactAt_succ n
  rw [HomologicalComplex.exactAt_iff' Q.mappedComplex
    (n + 2) (n + 1) n (by simp) (by simp)] at hQ
  simpa only [HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor'] using hQ

@[reassoc (attr := simp)]
theorem mappedComplex_d_comp_augmentation_f_zero
    (Q : FiniteResolution i X) :
    i.map (Q.complex.d 1 0) ≫ Q.augmentation₀ = 0 := by
  change Q.mappedComplex.d 1 0 ≫ Q.augmentation₀ = 0
  rw [← Q.augmentation.comm 1 0]
  simp

/-- The first mapped differential followed by the augmentation is exact. -/
theorem mappedExact₀ (Q : FiniteResolution i X) :
    (ShortComplex.mk _ _ Q.mappedComplex_d_comp_augmentation_f_zero).Exact := by
  exact ChainComplex.exact_augmentation Q.augmentation

/-- The degree-zero component of a finite-resolution augmentation is an
epimorphism. This is theorem-valued so it introduces no global instance. -/
theorem augmentation_f_zero_epi (Q : FiniteResolution i X) :
    Epi Q.augmentation₀ := by
  exact ChainComplex.epi_augmentation_f_zero Q.augmentation

/-- The degree-zero finite resolution of an object in the image. -/
noncomputable def single [HasZeroObject P] (i : P ⥤ A) [i.Additive]
    (P₀ : P) : FiniteResolution i (i.obj P₀) := by
  let ε :=
    (HomologicalComplex.singleMapHomologicalComplex
      i (ComplexShape.down ℕ) 0).hom.app P₀
  haveI : IsIso ε := inferInstance
  exact
    { complex := (ChainComplex.single₀ P).obj P₀
      augmentation := ε
      bound := 0
      isZero_above := fun n hn =>
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 P₀ n (by omega) }

section Prepend

variable [i.Full] [i.Faithful]
variable {K Y : A} (P₀ : P)
variable (f : K ⟶ i.obj P₀) (g : i.obj P₀ ⟶ Y)
variable (hzero : f ≫ g = 0)
variable (hS : (ShortComplex.mk f g hzero).ShortExact)
variable (Q : FiniteResolution i K)

include hS
/-- Prepend a source object across a short exact sequence. -/
noncomputable def ofShortExact : FiniteResolution i Y := by
  let d : Q.complex.X 0 ⟶ P₀ :=
    i.preimage (Q.augmentation₀ ≫ f)
  have hd_map : i.map d = Q.augmentation₀ ≫ f :=
    i.map_preimage _
  have hd_zero : Q.complex.d 1 0 ≫ d = 0 := by
    apply i.map_injective
    rw [i.map_comp, i.map_zero, hd_map]
    change i.map (Q.complex.d 1 0) ≫ Q.augmentation₀ ≫ f = 0
    simpa only [Category.assoc, zero_comp] using
      Q.mappedComplex_d_comp_augmentation_f_zero_assoc f
  let C : ChainComplex P ℕ :=
    ChainComplex.augment Q.complex d hd_zero
  have hC_d_one_zero :
      ((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).d 1 0 =
        Q.augmentation₀ ≫ f := by
    change i.map d = _
    exact hd_map
  have hC_d_succ_succ (n : ℕ) :
      ((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).d
          (n + 2) (n + 1) =
        Q.mappedComplex.d (n + 1) n := by
    change i.map (Q.complex.d (n + 1) n) = _
    rfl
  have hε_zero :
      ((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).d 1 0 ≫ g = 0 := by
    rw [hC_d_one_zero]
    calc
      (Q.augmentation₀ ≫ f) ≫ g =
          Q.augmentation₀ ≫ (f ≫ g) := Category.assoc _ _ _
      _ = 0 := by rw [hzero, comp_zero]
  let ε : ((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ⟶
      (ChainComplex.single₀ A).obj Y :=
    (ChainComplex.toSingle₀Equiv _ Y).symm ⟨g, hε_zero⟩
  have hε_f_zero : ε.f 0 = g := by
    dsimp only [ε]
    apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero
  have hexact_zero :
      (ShortComplex.mk
        (((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).d 1 0)
        (ε.f 0) (by rw [hε_f_zero]; exact hε_zero)).Exact := by
    let T : ShortComplex A :=
      ShortComplex.mk (Q.augmentation₀ ≫ f) g
        (by rw [Category.assoc, hzero, comp_zero])
    let S : ShortComplex A := ShortComplex.mk f g hzero
    let _ : Epi Q.augmentation₀ := Q.augmentation_f_zero_epi
    let α : T ⟶ S :=
      { τ₁ := Q.augmentation₀
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    have hT : T.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mpr hS.exact
    simpa only [T, hC_d_one_zero, hε_f_zero] using hT
  have hexact_one :
      ((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    let S : ShortComplex A :=
      ShortComplex.mk (i.map (Q.complex.d 1 0)) Q.augmentation₀
        Q.mappedComplex_d_comp_augmentation_f_zero
    let T : ShortComplex A :=
      ShortComplex.mk (i.map (Q.complex.d 1 0))
        (Q.augmentation₀ ≫ f)
        (by simpa only [Category.assoc, zero_comp] using
          Q.mappedComplex_d_comp_augmentation_f_zero_assoc f)
    let _ : Mono f := hS.mono_f
    let α : S ⟶ T :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := f }
    have hT : T.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp Q.mappedExact₀
    simpa [HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', hC_d_one_zero,
      hC_d_succ_succ, hd_map, T, C] using hT
  have hexact_succ_succ (n : ℕ) :
      ((i.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).ExactAt
        (n + 2) := by
    rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1)
      (by simp) (by simp)]
    simpa only [HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', hC_d_succ_succ] using
        Q.mappedExact_succ n
  have hε : QuasiIso ε := by
    constructor
    intro n
    cases n with
    | zero =>
        exact (ChainComplex.quasiIsoAt_zero_iff_exact_and_epi_augmentation ε).mpr
          ⟨hexact_zero, by
            rw [hε_f_zero]
            exact hS.epi_g⟩
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · cases n with
          | zero => exact hexact_one
          | succ n => exact hexact_succ_succ n
        · exact ChainComplex.exactAt_succ_single_obj Y n
  exact
    { complex := C
      augmentation := ε
      quasiIso := hε
      bound := Q.bound + 1
      isZero_above := by
        intro n hn
        cases n with
        | zero => omega
        | succ n =>
            change IsZero (Q.complex.X n)
            exact Q.isZero_above n (by omega) }

@[simp]
theorem ofShortExact_complex_X_zero :
    (ofShortExact P₀ f g hzero hS Q).complex.X 0 = P₀ := by
  rfl

@[simp]
theorem ofShortExact_complex_X_succ (n : ℕ) :
    (ofShortExact P₀ f g hzero hS Q).complex.X (n + 1) =
      Q.complex.X n := by
  rfl

theorem ofShortExact_mappedComplex_d_one_zero :
    (ofShortExact P₀ f g hzero hS Q).mappedComplex.d 1 0 =
      Q.augmentation₀ ≫ f := by
  change i.map (i.preimage (Q.augmentation₀ ≫ f)) = _
  exact i.map_preimage _

theorem ofShortExact_mappedComplex_d_succ_succ (n : ℕ) :
    (ofShortExact P₀ f g hzero hS Q).mappedComplex.d
        (n + 2) (n + 1) =
      Q.mappedComplex.d (n + 1) n := by
  rfl

@[simp]
theorem ofShortExact_augmentation_f_zero :
    (ofShortExact P₀ f g hzero hS Q).augmentation.f 0 = g := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

@[simp]
theorem ofShortExact_bound :
    (ofShortExact P₀ f g hzero hS Q).bound = Q.bound + 1 := by
  rfl

end Prepend

end FiniteResolution

end CategoryTheory.Abelian

end
