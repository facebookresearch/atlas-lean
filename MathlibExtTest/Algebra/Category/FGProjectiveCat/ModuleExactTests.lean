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

import MathlibExt.Algebra.Category.FGProjectiveCat.ModuleExact
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Arbitrary-ring clients of the finite projective exact structure
-/

open CategoryTheory Limits

universe v u

variable {R : Type u} [Ring R]

example (S : ShortComplex (FGProjectiveCat.{v} R))
    (h : (S.map (FGProjectiveCat.toModuleCat (R := R))).ShortExact) :
    Nonempty S.Splitting :=
  ⟨FGProjectiveCat.splittingOfModuleShortExact S h⟩

example (P Q : FGProjectiveCat.{v} R) :
    ((ShortComplex.mk (biprod.inl : P ⟶ P ⊞ Q) biprod.snd (by simp)).map
      (FGProjectiveCat.toModuleCat (R := R))).ShortExact :=
  (FGProjectiveCat.isAdmissibleExact_iff_moduleShortExact _).mp
    (ExactCategory.isAdmissibleExact_split P Q)

example (S : ShortComplex (FGProjectiveCat.{0} (MvPolynomial ℕ ℤ)))
    (h : (S.map (FGProjectiveCat.toModuleCat (R := MvPolynomial ℕ ℤ))).ShortExact) :
    ExactCategory.IsAdmissibleExact S :=
  (FGProjectiveCat.isAdmissibleExact_iff_moduleShortExact S).mpr h
