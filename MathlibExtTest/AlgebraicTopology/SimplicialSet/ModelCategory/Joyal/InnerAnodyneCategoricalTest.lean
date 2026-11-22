/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical

/-!
# Inner anodyne extensions are categorical: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical`:
the inclusion of morphism properties
`SSet.innerAnodyneExtensions ≤ SSet.categoricalEquivalences`, its membership
form, the trivial-fibration statement for precomposition into a
quasicategory (including the unpacked lifting property against individual
boundary inclusions), and the corollary that every inner horn inclusion is
a categorical equivalence, in particular the concrete inner horns
`Λ[2, 1].ι`, `Λ[3, 1].ι`, and `Λ[3, 2].ι`.
-/

@[expose] public section

open CategoryTheory MonoidalClosed MonoidalCategory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace InnerAnodyneCategoricalTest

section MainInclusion

/-- The headline inclusion, at a variable universe and at universe `0`. -/
example : SSet.innerAnodyneExtensions.{u} ≤ SSet.categoricalEquivalences.{u} :=
  SSet.innerAnodyneExtensions_le_categoricalEquivalences

example : SSet.innerAnodyneExtensions.{0} ≤ SSet.categoricalEquivalences.{0} :=
  SSet.innerAnodyneExtensions_le_categoricalEquivalences

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Membership form: an inner anodyne extension is a categorical equivalence. -/
example (hf : SSet.innerAnodyneExtensions f) : SSet.categoricalEquivalences f :=
  SSet.categoricalEquivalences.of_innerAnodyneExtensions hf

/-- The same membership obtained by applying the inclusion directly. -/
example (hf : SSet.innerAnodyneExtensions f) : SSet.categoricalEquivalences f :=
  SSet.innerAnodyneExtensions_le_categoricalEquivalences f hf

/-- Composites of inner anodyne extensions are categorical equivalences,
via the membership form and the composition closure of
`SSet.categoricalEquivalences` from the formal calculus. -/
example (hf : SSet.innerAnodyneExtensions f) (hg : SSet.innerAnodyneExtensions g) :
    SSet.categoricalEquivalences (f ≫ g) :=
  MorphismProperty.comp_mem _ f g
    (SSet.categoricalEquivalences.of_innerAnodyneExtensions hf)
    (SSet.categoricalEquivalences.of_innerAnodyneExtensions hg)

/-- Whiskering an inner anodyne extension with any simplicial set is a
categorical equivalence, via the upstream whiskering stability of inner
anodyne extensions. -/
example (hf : SSet.innerAnodyneExtensions f) (W : SSet.{u}) :
    SSet.categoricalEquivalences (f ▷ W) :=
  SSet.categoricalEquivalences.of_innerAnodyneExtensions
    (SSet.innerAnodyneExtensions.whiskerRight hf W)

example (hf : SSet.innerAnodyneExtensions f) (W : SSet.{u}) :
    SSet.categoricalEquivalences (W ◁ f) :=
  SSet.categoricalEquivalences.of_innerAnodyneExtensions
    (SSet.innerAnodyneExtensions.whiskerLeft hf W)

end MainInclusion

section TrivialFibrationForm

variable {X Y : SSet.{u}} {f : X ⟶ Y} (hf : SSet.innerAnodyneExtensions f)
variable (C : SSet.{u}) [SSet.Quasicategory C]

/-- Precomposition with an inner anodyne extension into a quasicategory has
the right lifting property against the generating cofibrations. -/
example :
    SSet.modelCategoryQuillen.I.rlp ((MonoidalClosed.pre f).app C) :=
  SSet.rlp_I_pre_app_of_innerAnodyneExtensions hf C

/-- Unpacked: precomposition lifts against each individual boundary
inclusion. -/
example (n : ℕ) :
    HasLiftingProperty ∂Δ[n].ι ((MonoidalClosed.pre f).app C) :=
  SSet.rlp_I_pre_app_of_innerAnodyneExtensions hf C _
    (SSet.modelCategoryQuillen.boundary_ι_mem_I n)

/-- The same statement with the target replaced by an internal hom into the
quasicategory, which is again a quasicategory by the upstream instance. -/
example (A : SSet.{u}) :
    SSet.modelCategoryQuillen.I.rlp
      ((MonoidalClosed.pre f).app ((ihom A).obj C)) :=
  SSet.rlp_I_pre_app_of_innerAnodyneExtensions hf _

/-- The defining `hFun` consequence, obtained from the membership form
through the characterization `SSet.categoricalEquivalences.mem_iff`:
precomposition with an inner anodyne extension induces an equivalence of
homotopy categories of functor objects. -/
example :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f).app C)).toFunctor.IsEquivalence :=
  (SSet.categoricalEquivalences.mem_iff f).1
    (SSet.categoricalEquivalences.of_innerAnodyneExtensions hf) C inferInstance

end TrivialFibrationForm

section InnerHorns

/-- Every inner horn inclusion, in the generality in which inner horns are
stated, is a categorical equivalence. -/
example {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) :
    SSet.categoricalEquivalences.{u} Λ[n, i].ι :=
  SSet.categoricalEquivalences.horn_ι h0 hn

/-- Concrete inner horns in dimensions `2` and `3`. -/
example : SSet.categoricalEquivalences.{u} Λ[2, (1 : Fin 3)].ι :=
  SSet.categoricalEquivalences.horn_ι (by decide) (by decide)

example : SSet.categoricalEquivalences.{u} Λ[3, (1 : Fin 4)].ι :=
  SSet.categoricalEquivalences.horn_ι (by decide) (by decide)

example : SSet.categoricalEquivalences.{u} Λ[3, (2 : Fin 4)].ι :=
  SSet.categoricalEquivalences.horn_ι (by decide) (by decide)

/-- A concrete inner horn at universe `0`. -/
example : SSet.categoricalEquivalences.{0} Λ[2, (1 : Fin 3)].ι :=
  SSet.categoricalEquivalences.horn_ι (by decide) (by decide)

end InnerHorns

end InnerAnodyneCategoricalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
