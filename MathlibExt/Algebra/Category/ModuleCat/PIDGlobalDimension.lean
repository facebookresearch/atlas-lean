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
# Projective dimension of modules over a PID

Every module over a commutative principal ideal domain has projective
dimension at most one. Consequently, its higher Ext groups vanish from
degree two onward. No finite-generation or finite-rank hypothesis is used.
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

/-- Every module over a commutative principal ideal domain has projective
dimension at most one. -/
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

/-- Ext groups out of a module over a PID are subsingleton in every degree
at least two. -/
theorem subsingleton_ext_of_two_le_of_isPrincipalIdealRing
    [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p) :
    Subsingleton (Abelian.Ext.{w} M A p) := by
  let _ : HasProjectiveDimensionLE M 1 :=
    hasProjectiveDimensionLE_one_of_isPrincipalIdealRing M
  exact HasProjectiveDimensionLT.subsingleton M 2 p hp A

/-- The Ext-group object out of a module over a PID is zero in every degree
at least two. -/
theorem isZero_ext_of_two_le_of_isPrincipalIdealRing
    [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p) :
    IsZero (AddCommGrpCat.of (Abelian.Ext.{w} M A p)) := by
  let _ : Subsingleton (Abelian.Ext.{w} M A p) :=
    subsingleton_ext_of_two_le_of_isPrincipalIdealRing M A p hp
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Every element of an Ext group out of a module over a PID is zero in
degree at least two. -/
theorem ext_eq_zero_of_two_le_of_isPrincipalIdealRing
    [HasExt.{w} (ModuleCat.{v} R)]
    (M A : ModuleCat.{v} R) (p : ℕ) (hp : 2 ≤ p)
    (x : Abelian.Ext.{w} M A p) : x = 0 :=
  (subsingleton_ext_of_two_le_of_isPrincipalIdealRing M A p hp).elim _ _

end ModuleCat

end
