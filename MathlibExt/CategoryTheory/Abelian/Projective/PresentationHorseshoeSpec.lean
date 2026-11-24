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
## Original coordinates for the projective presentation horseshoe
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- The original splitting supplies its horseshoe coordinate specification. -/
def presentationHorseshoeSpec : (presentationHorseshoe S hS).Spec :=
  HorseshoeData.specOfSplittings (presentationHorseshoe S hS)
    (fun n => presentationHorseshoeSplitting S hS n)

end CategoryTheory.ProjectiveResolution
