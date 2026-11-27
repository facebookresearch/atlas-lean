/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.FiniteResolution

/-!
# Tests for nonfunctorial finite resolutions

These tests exercise degree-zero resolutions, zero padding, mapped
exactness, the public short-exact prepend computations, helper privacy, and
unrelated per-object bounds.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Abelian.FiniteResolution.Tests

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The identity functor gives a resolution concentrated in degree zero.  An
arbitrary larger bound records harmless zero padding. -/
noncomputable def identityResolution (X : A) (N : ℕ) :
    CategoryTheory.Abelian.FiniteResolution (𝟭 A) X where
  complex := (ChainComplex.single₀ A).obj X
  augmentation := 𝟙 _
  bound := N
  isZero_above n hn :=
    HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) 0 X n (by omega)

example (X : A) : (identityResolution X 0).bound = 0 := rfl

example (X : A) (N n : ℕ) (hn : N < n) :
    IsZero ((identityResolution X N).mappedComplex.X n) :=
  (identityResolution X N).mappedComplex_isZero_above n hn

example (X : A) (N n : ℕ) (hn : N < n) :
    IsZero (((ChainComplex.single₀ A).obj X).X n) :=
  single₀_isZero_above X N n hn

example : IsZero ((identityResolution (0 : A) 0).complex.X 0) := by
  change IsZero (0 : A)
  exact isZero_zero A

/-- Different objects may carry unrelated support bounds. -/
example (X Y : A) :
    Nonempty (CategoryTheory.Abelian.FiniteResolution (𝟭 A) X) ∧
      Nonempty (CategoryTheory.Abelian.FiniteResolution (𝟭 A) Y) :=
  ⟨⟨identityResolution X 0⟩, ⟨identityResolution Y 2⟩⟩

section GenericConstructors

universe vP uP vA uA

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
  [HasZeroObject P]
variable {B : Type uA} [Category.{vA} B] [Abelian B]
variable {i : P ⥤ B} [i.Additive] [i.Full] [i.Faithful]

example (P₀ : P) : FiniteResolution i (i.obj P₀) :=
  FiniteResolution.single i P₀

variable {X : B} (QX : FiniteResolution i X)

example (n : ℕ) :
    (ShortComplex.mk
      (QX.mappedComplex.d (n + 2) (n + 1))
      (QX.mappedComplex.d (n + 1) n)
      (QX.mappedComplex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  QX.mappedExact_succ n

/-- error: -/
#guard_msgs (error, substring := true) in
#synth Epi QX.augmentation₀

section Computations

variable {K Y : B} (P₀ : P)
variable (f : K ⟶ i.obj P₀) (g : i.obj P₀ ⟶ Y)
variable (hzero : f ≫ g = 0)
variable (hS : (ShortComplex.mk f g hzero).ShortExact)
variable (Q : FiniteResolution i K)

example : (FiniteResolution.ofShortExact P₀ f g hzero hS Q).complex.X 0 = P₀ :=
  FiniteResolution.ofShortExact_complex_X_zero P₀ f g hzero hS Q

example (n : ℕ) :
    (FiniteResolution.ofShortExact P₀ f g hzero hS Q).complex.X (n + 1) =
      Q.complex.X n :=
  FiniteResolution.ofShortExact_complex_X_succ P₀ f g hzero hS Q n

example :
    (FiniteResolution.ofShortExact P₀ f g hzero hS Q).mappedComplex.d 1 0 =
      Q.augmentation₀ ≫ f :=
  FiniteResolution.ofShortExact_mappedComplex_d_one_zero P₀ f g hzero hS Q

example (n : ℕ) :
    (FiniteResolution.ofShortExact P₀ f g hzero hS Q).mappedComplex.d
        (n + 2) (n + 1) = Q.mappedComplex.d (n + 1) n :=
  FiniteResolution.ofShortExact_mappedComplex_d_succ_succ
    P₀ f g hzero hS Q n

example :
    (FiniteResolution.ofShortExact P₀ f g hzero hS Q).augmentation.f 0 = g :=
  FiniteResolution.ofShortExact_augmentation_f_zero P₀ f g hzero hS Q

example :
    (FiniteResolution.ofShortExact P₀ f g hzero hS Q).bound = Q.bound + 1 :=
  FiniteResolution.ofShortExact_bound P₀ f g hzero hS Q

end Computations

end GenericConstructors

/-- error: -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.Abelian.FiniteResolution.prependD

/-- error: -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.Abelian.FiniteResolution.prependComplex

/-- error: -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.Abelian.FiniteResolution.prependAugmentation

/-- error: -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.Abelian.FiniteResolution.prependAugmentation_quasiIso

#print axioms CategoryTheory.Abelian.FiniteResolution.single
#print axioms CategoryTheory.Abelian.FiniteResolution.mappedExact_succ
#print axioms CategoryTheory.Abelian.FiniteResolution.ofShortExact

end CategoryTheory.Abelian.FiniteResolution.Tests

end
