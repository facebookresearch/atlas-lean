/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Actual products of categorical nerves

The original pointwise category and its projections are the pinned
`CategoryTheory.pi` and `Pi.eval`. Assembly reuses `Functor.pi'`.
The resulting actual nerve/product isomorphism preserves every original
object, arrow, scalar operator and projection, including an empty index.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.NerveProducts
variable {I : Type u} (C : I → Type u) [∀ i, Category.{u} (C i)]

/-- The actual family of original categorical nerves. -/
abbrev nerves (i : I) : SSet.{u} := nerve (C i)

/-- Original nerve projections into the actual product of the coordinate nerves. -/
def toProduct : nerve (∀ i, C i) ⟶ ∏ᶜ nerves C :=
  Limits.Pi.lift (fun i => nerveMap (CategoryTheory.Pi.eval C i))

/-- Each actual product projection is the original categorical nerve projection map. -/
theorem toProduct_π (i : I) :
    toProduct C ≫ Limits.Pi.π (nerves C) i = nerveMap (CategoryTheory.Pi.eval C i) :=
  Limits.Pi.lift_comp_π _ _

/-- Assemble the same original coordinate simplices by the pinned whole categorical product
functor. -/
def fromProduct : ∏ᶜ nerves C ⟶ nerve (∀ i, C i) where
  app q := ↾fun p => CategoryTheory.Functor.pi'
    (fun i => (Limits.Pi.π (nerves C) i).app q p)
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg (fun F => CategoryTheory.Functor.pi' F)
      (funext (fun i => congr($((Limits.Pi.π (nerves C) i).naturality f) p)))

/-- The actual original nerve of the pointwise product category is the whole product of its
nerves. -/
def nervePiIso : nerve (∀ i, C i) ≅ ∏ᶜ nerves C where
  hom := toProduct C
  inv := fromProduct C
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    have hp : (fun i => (Limits.Pi.π (nerves C) i).app q ((toProduct C).app q p)) =
        fun i => p ⋙ CategoryTheory.Pi.eval C i :=
      funext (fun i => congr($(toProduct_π C i).app q p))
    have h := congrArg (fun F => CategoryTheory.Functor.pi' F) hp
    have he : CategoryTheory.Functor.pi' (fun i => p ⋙ CategoryTheory.Pi.eval C i) = p := by
      refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro x y f
      change p.map f = 𝟙 _ ≫ p.map f ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    exact h.trans he
  inv_hom_id := by
    apply Limits.Pi.hom_ext
    intro i
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    exact congr($(toProduct_π C i).app q ((fromProduct C).app q p))

/-- Whole original coordinate projection readback for the actual nerve/product isomorphism. -/
theorem nervePiIso_π (i : I) :
    (nervePiIso C).hom ≫ Limits.Pi.π (nerves C) i = nerveMap (CategoryTheory.Pi.eval C i) :=
  toProduct_π C i

end CategoryTheory.CoherentRealization.NerveProducts
