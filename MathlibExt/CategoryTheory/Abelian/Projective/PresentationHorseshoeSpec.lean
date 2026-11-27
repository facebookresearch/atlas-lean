/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.Projective.PresentationHorseshoe
public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeSplitCoordinates

/-!
# Endpoint coordinates for the projective presentation horseshoe

For short exact `A → B → X` in an abelian category with `A,B`
projective, the split presentation horseshoe has middle degree-zero
term `A ⊞ B`, middle degree-one term `A`, and zero higher terms.
Its splittings give endpoint biproduct coordinates, with left inclusion,
right projection and the signed presentation differential.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- Let `C` be abelian and `S : A → B → X` short exact, with
`A,B` projective. The degreewise row splittings give an endpoint coordinate
specification of the presentation horseshoe: middle terms are
biproducts of endpoint terms, the maps are left inclusion and right
projection, and the differential has the endpoint block form. -/
def presentationHorseshoeSpec : (presentationHorseshoe S hS).Spec :=
  HorseshoeData.specOfSplittings (presentationHorseshoe S hS)
    (fun n => presentationHorseshoeSplitting S hS n)

end CategoryTheory.ProjectiveResolution
