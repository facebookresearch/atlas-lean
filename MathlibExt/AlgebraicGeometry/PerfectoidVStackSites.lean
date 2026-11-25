/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
public import MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry

/-!
# Actual groupoid v-stack sites

A stack uses the native groupoid-valued pseudofunctor and effective
descent. Its site is the native CoGrothendieck category: arrows retain
their actual base map and the actual comparison in the fibre groupoid.
The topology is restricted from the actual geometric base topology.
Thus stabilizers and comparison isomorphisms remain in the site.

Two applications are the full universe-bounded small v-sheaf base and
the actual affine p-adic untilt base. The former gives groupoid v-stacks on small v-sheaves,
without Scholze's smallness condition (a surjection from a perfectoid space with small kernel
pair, Def. 12.4), and the latter gives the affine basis used for geometric
coefficient limits. No stack is replaced by its sheaf of isomorphism
classes.

Sources: Scholze, arXiv:1709.07343v4, Definitions 12.4 and 14.1;
Vistoli, Notes on Grothendieck Topologies, Fibered Categories and
Descent Theory. Generic groupoid/pseudofunctor descent is native Mathlib.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PerfectoidVStackSites

open CategoryTheory CategoryTheory.Bicategory
open PerfectoidSliceSites AffineUntiltingGeometry

universe u v w

/-- A genuine groupoid stack for the specified actual geometric site. -/
structure GroupoidStack (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) where
  pseudofunctor : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}
  groupoid : ∀ c : C, IsGroupoid (pseudofunctor.obj (.mk (.op c)))
  descent : pseudofunctor.IsStack J

attribute [instance] GroupoidStack.groupoid GroupoidStack.descent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The actual comparison-preserving morphisms of groupoid stacks. -/
abbrev GroupoidStack.Hom (F G : GroupoidStack.{u, v, w} C J) :=
  Pseudofunctor.StrongTrans F.pseudofunctor G.pseudofunctor

/-- Actual objects and arrows over the stack, including all fibre comparisons. -/
abbrev StackSite (F : GroupoidStack.{u, v, w} C J) :=
  Pseudofunctor.CoGrothendieck F.pseudofunctor

/-- The actual geometric base map of each stack-site object and arrow. -/
abbrev projection (F : GroupoidStack.{u, v, w} C J) : StackSite F ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget F.pseudofunctor

/-- The stack site's topology is the native restricted geometric topology. -/
def stackTopology (F : GroupoidStack.{u, v, w} C J) : GrothendieckTopology (StackSite F) :=
  (projection F).restrictedTopology J

/-- A sieve covers when its actual projected arrows generate a geometric cover. -/
theorem projected_cover {F : GroupoidStack.{u, v, w} C J} {U : StackSite F}
    (R : Sieve U) (h : R.functorPushforward (projection F) ∈ J ((projection F).obj U)) :
    R ∈ stackTopology F U := Functor.mem_restrictedTopology_of_functorPushforward_mem h

/-- The actual map of stack sites, induced by the whole strong transformation. -/
def mapSite {F G : GroupoidStack.{u, v, w} C J} (f : F.Hom G) :
    StackSite F ⥤ StackSite G := Pseudofunctor.CoGrothendieck.map f

/-- Native inverse image from the actual stack-site map. -/
def inverseImage (A : Type*) [Category A]
    {F G : GroupoidStack.{u, v, w} C J} (f : F.Hom G)
    [(mapSite f).IsContinuous (stackTopology F) (stackTopology G)] :
    Sheaf (stackTopology G) A ⥤ Sheaf (stackTopology F) A :=
  (mapSite f).sheafPushforwardContinuous A _ _

variable (p : ℕ) [Fact p.Prime]

/-- Groupoid-valued v-stacks on the site of small v-sheaves. No smallness condition is imposed:
Scholze's small v-stacks (Def. 12.4) are the v-stacks admitting a surjection from a perfectoid space
whose kernel pair is a small v-sheaf, and that condition is not encoded here. -/
abbrev VStack := GroupoidStack.{2, 1, 1} (SmallVSheaf p) (vTopology p)

/-- The affine-basis groupoid stack model retaining actual p-adic untilts. -/
abbrev PerfdVStack := GroupoidStack.{1, 0, 1} (AffineUntilting p) (originalVTopology p)

end MathlibExt.AlgebraicGeometry.PerfectoidVStackSites
