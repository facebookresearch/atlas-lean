/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.GeneratorBasis

/-!
# Original simplex covers of the marked presentation basis

Each original basis object has its actual standard-simplex carrier.
The minimally marked source maps into that object by the unchanged
underlying identity. For every original basis map into a total space,
this supplies its actual simplex cover over the same space.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.GeneratorBasis

/-- The original standard-simplex dimension of each actual marked basis label. -/
def dimension (i : Generator.{u}) : ℕ :=
  match i with
  | some n => n
  | none => 1

/-- The basis carrier is exactly its original standard simplex, with both native identity maps. -/
def underlyingIso (i : Generator.{u}) :
    (generatorFunctor.obj i).toSSet ≅ (Δ[dimension i] : SSet.{u}) := by
  cases i <;> exact Iso.refl _

/-- The original minimal simplex enters the marked basis object with the same underlying identity. -/
def minimumInclusion (i : Generator.{u}) : min (Δ[dimension i] : SSet.{u}) ⟶ generatorFunctor.obj i := by
  cases i with
  | none => exact toMax (𝟙 (Δ[1] : SSet.{u}))
  | some n => exact 𝟙 (min (Δ[n] : SSet.{u}))

/-- The actual minimum inclusion retains precisely the original underlying inverse carrier identity. -/
theorem minimumInclusion_hom (i : Generator.{u}) :
    (minimumInclusion i).hom = (underlyingIso i).inv := by cases i <;> rfl

/-- The original whole simplex of a basis map is read from its actual identity carrier coordinate. -/
def sourceSimplex (X : Marked.{u}) (i : Index X) : Index X :=
  simplex X ⦋dimension i.left⦌ (SSet.yonedaEquiv ((underlyingIso i.left).inv ≫ i.hom.hom))

/-- Every original marked basis map has its actual minimally marked simplex cover over the same total space. -/
def cover (X : Marked.{u}) (i : Index X) : sourceSimplex X i ⟶ i :=
  CostructuredArrow.homMk ⟨minimumInclusion i.left⟩ (Hom.ext
    ((congrArg (fun f => f ≫ i.hom.hom) (minimumInclusion_hom i.left)).trans
      (SSet.yonedaEquiv.symm_apply_apply ((underlyingIso i.left).inv ≫ i.hom.hom)).symm))

/-- The whole cover map is the same original underlying carrier inverse, not a chosen replacement. -/
theorem cover_hom (X : Marked.{u}) (i : Index X) :
    (generatorFunctor.map (cover X i).left).hom = (underlyingIso i.left).inv :=
  minimumInclusion_hom i.left

end SSet.Marked.GeneratorBasis
