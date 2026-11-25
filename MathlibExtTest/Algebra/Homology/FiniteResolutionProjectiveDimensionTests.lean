/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionProjectiveDimension

/-!
# Direct clients of actual finite-resolution dimension bounds

The source and target object/morphism universes are independent. The
clients use the original finite resolution, mapped projective objects,
Ext class, and projective-dimension predicates.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uA vA

open CategoryTheory CategoryTheory.Limits

namespace FiniteResolutionProjectiveDimensionClients

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive] {X : A}
variable (Q : Abelian.FiniteResolution i X)
variable (hproj : ∀ P₀ : P, Projective (i.obj P₀))

example (n : ℕ) (hn : Q.bound < n) :
    letI := HasExt.standard A
    ∀ (Y : A) (α : Abelian.Ext X Y n), α = 0 :=
  Q.ext_eq_zero_above hproj n hn

example : HasProjectiveDimensionLE X Q.bound :=
  Q.hasProjectiveDimensionLE hproj

example (n : ℕ) (hn : Q.bound ≤ n) : HasProjectiveDimensionLE X n :=
  Q.hasProjectiveDimensionLE_of_bound_le hproj n hn

example : projectiveDimension X ≤ Q.bound :=
  Q.projectiveDimension_le_bound hproj

end FiniteResolutionProjectiveDimensionClients

end
