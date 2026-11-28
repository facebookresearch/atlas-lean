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

public import MathlibExt.Algebra.Module.PIDProjectiveSubmodule
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Projective dimension and higher Ext over a principal ideal domain

Let R be a commutative principal ideal domain in universe u, and assume its underlying set has a
representative in the module universe v. Every R-module M in v has projective dimension at most
one: the kernel of a free presentation is a submodule of a free module and is free over R.
This applies
to arbitrary modules without a finite-generation or finite-rank restriction.

When Ext groups of this module category are defined in universe w, Ext^p_R(M,A)=0 for all p≥2
and all modules M,A in v. The statements give vanishing as a subsingleton group, as a zero
additive-group object, and as equality of every Ext class to zero.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable {R : Type u} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [Small.{v} R]

/-- Let R be a commutative principal ideal domain in universe u, whose underlying set can be
represented in the module universe v. For every R-module M in v, pd(M)≤1. A projective presentation
comes from a free module, and its kernel is free because R is a principal ideal domain. Neither
finite generation of M nor finite rank of the presenting free module is assumed. -/
theorem hasProjectiveDimensionLE_one_of_isPrincipalIdealRing
    (M : ModuleCat.{v} R) : HasProjectiveDimensionLE M 1 := by
  let S := M.projectiveShortComplex
  have hS : S.ShortExact := M.shortExact_projectiveShortComplex
  have hFree₁ : Module.Free R S.X₁ := by
    change Module.Free R (LinearMap.ker _)
    exact Module.Free.submodule_of_isPrincipalIdealRing _
  let _ : Module.Free R S.X₁ := hFree₁
  let _ : Projective S.X₁ := by infer_instance
  let _ : Projective S.X₂ := by infer_instance
  change HasProjectiveDimensionLT S.X₃ 2
  exact (hS.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).2 inferInstance

/-- Let R be a commutative principal ideal domain in universe u, whose underlying set can be
represented in the module universe v. Assume Ext groups of R-Mod_v are defined in universe w.
For M,A in that category and p∈ℕ with p≥2, Ext^p_R(M,A) is subsingleton. The
projective-dimension bound pd(M)≤1 excludes every higher extension class. -/
theorem subsingleton_ext_of_two_le_of_isPrincipalIdealRing
    [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p) :
    Subsingleton (Abelian.Ext.{w} M A p) := by
  let _ : HasProjectiveDimensionLE M 1 :=
    hasProjectiveDimensionLE_one_of_isPrincipalIdealRing M
  exact HasProjectiveDimensionLT.subsingleton M 2 p hp A

/-- Let R be a commutative principal ideal domain in universe u, whose underlying set can be
represented in the module universe v. Assume Ext groups of R-Mod_v are defined in universe w.
For R-modules M,A in v and p≥2, the additive-group object associated to Ext^p_R(M,A) is zero.
This is categorical vanishing of the same subsingleton higher Ext group. -/
theorem isZero_ext_of_two_le_of_isPrincipalIdealRing
    [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p) :
    IsZero (AddCommGrpCat.of (Abelian.Ext.{w} M A p)) := by
  let _ : Subsingleton (Abelian.Ext.{w} M A p) :=
    subsingleton_ext_of_two_le_of_isPrincipalIdealRing M A p hp
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Let R be a commutative principal ideal domain in universe u, whose underlying set can be
represented in the module universe v. Assume Ext groups of R-Mod_v are defined in universe w.
For M,A in v, p≥2 and x∈Ext^p_R(M,A), one has x=0. The assertion uses the arbitrary-module
projective bound and applies to every class in the stated degree. -/
theorem ext_eq_zero_of_two_le_of_isPrincipalIdealRing
    [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p)
    (x : Abelian.Ext.{w} M A p) : x = 0 :=
  (subsingleton_ext_of_two_le_of_isPrincipalIdealRing M A p hp).elim _ _

end ModuleCat

end
