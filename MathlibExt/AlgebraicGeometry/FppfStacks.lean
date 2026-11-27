/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported from TauCetiProject/TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/AlgebraicGeometry/Stack/Basic.lean and StackInGroupoids.lean.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates: consolidate the
definitions and the fibrewise-equivalence lemmas in one module, in the
namespace `AlgebraicGeometry.FppfStacks`.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Pseudofunctors on schemes

Prestacks and stacks over the big category of schemes are phrased in terms of `Cat`-valued
pseudofunctors on `LocallyDiscrete Scheme.{u}ᵒᵖ`, in the sense of Mathlib's
`Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`. This file names their carrier type.

## Main declarations

* `AlgebraicGeometry.FppfStacks.SchPseudofunctor`: `Cat`-valued pseudofunctors on schemes.
-/

public section

open CategoryTheory Bicategory

namespace AlgebraicGeometry.FppfStacks

open _root_.AlgebraicGeometry

universe u

/-- `Cat`-valued pseudofunctors on schemes, contravariant in the scheme: pseudofunctors from the
locally discrete bicategory on the opposite of the category of schemes to `Cat`. Prestacks and
stacks over the big category of schemes are such pseudofunctors, satisfying
`Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`. -/
abbrev SchPseudofunctor := Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}

end AlgebraicGeometry.FppfStacks

/-!
# Stacks in groupoids over schemes

A stack in groupoids over schemes is a `Cat`-valued pseudofunctor on schemes
(a `SchPseudofunctor`) whose fibre categories are groupoids and which is a stack, in the sense of
Mathlib's `Pseudofunctor.IsStack`, for the fppf topology (Stacks, Definitions 026F and 02ZI).
Morphisms of stacks in groupoids are strong transformations of the underlying pseudofunctors.

## Main declarations

* `AlgebraicGeometry.FppfStacks.StackInGroupoids`: stacks in groupoids over schemes for the fppf
  topology.
* `AlgebraicGeometry.FppfStacks.StackInGroupoids.Hom`: morphisms of stacks in groupoids, the strong
  transformations of the underlying pseudofunctors. Identities and composites are Mathlib's
  `Pseudofunctor.StrongTrans.id` and `Pseudofunctor.StrongTrans.vcomp`.
* `AlgebraicGeometry.FppfStacks.StackInGroupoids.Hom.IsFiberwiseEquiv`: a morphism whose component
  on every scheme is an equivalence of fibre groupoids. It holds for identities, is closed under
  composition, and satisfies two-out-of-three.

## References

* [Stacks Project, Definition 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Definition 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

public section

open CategoryTheory Bicategory Opposite

namespace AlgebraicGeometry.FppfStacks

open _root_.AlgebraicGeometry

universe u

/-- A stack in groupoids over schemes: a `Cat`-valued pseudofunctor on schemes whose fibre
categories are groupoids and which is a stack for the fppf topology (Stacks, Definitions 026F
and 02ZI). -/
@[stacks 02ZI]
structure StackInGroupoids where
  /-- The underlying pseudofunctor on schemes. -/
  toSchPseudofunctor : SchPseudofunctor.{u}
  /-- Every fibre category is a groupoid. -/
  isGroupoid (T : Scheme.{u}) : IsGroupoid (toSchPseudofunctor.obj (.mk (op T)))
  /-- The underlying pseudofunctor is a stack for the fppf topology. -/
  isStack : toSchPseudofunctor.IsStack Scheme.fppfTopology

namespace StackInGroupoids

attribute [instance] StackInGroupoids.isGroupoid StackInGroupoids.isStack

/-- Morphisms of stacks in groupoids: strong transformations of the underlying pseudofunctors. -/
abbrev Hom (X Y : StackInGroupoids.{u}) : Type (u + 1) :=
  Pseudofunctor.StrongTrans X.toSchPseudofunctor Y.toSchPseudofunctor

namespace Hom

/-- A morphism of stacks in groupoids is a fiberwise equivalence if its component on every
scheme is an equivalence of fibre groupoids. -/
def IsFiberwiseEquiv {X Y : StackInGroupoids.{u}} (f : Hom X Y) : Prop :=
  ∀ T : Scheme.{u}, (f.app (.mk (op T))).toFunctor.IsEquivalence

lemma isFiberwiseEquiv_iff {X Y : StackInGroupoids.{u}} (f : Hom X Y) :
    f.IsFiberwiseEquiv ↔ ∀ T : Scheme.{u}, (f.app (.mk (op T))).toFunctor.IsEquivalence :=
  Iff.rfl

@[simp]
lemma isFiberwiseEquiv_id (X : StackInGroupoids.{u}) :
    IsFiberwiseEquiv (Pseudofunctor.StrongTrans.id X.toSchPseudofunctor) := fun _ ↦
  inferInstanceAs (Functor.id _).IsEquivalence

variable {X Y Z : StackInGroupoids.{u}} {f : Hom X Y} {g : Hom Y Z}

lemma IsFiberwiseEquiv.comp (hf : f.IsFiberwiseEquiv) (hg : g.IsFiberwiseEquiv) :
    IsFiberwiseEquiv (Pseudofunctor.StrongTrans.vcomp f g) := fun T ↦
  have := hf T
  have := hg T
  inferInstanceAs ((f.app (.mk (op T))).toFunctor ⋙ (g.app (.mk (op T))).toFunctor).IsEquivalence

/-- If `g` and the composite `Pseudofunctor.StrongTrans.vcomp f g` are fiberwise equivalences,
so is `f`. -/
lemma IsFiberwiseEquiv.of_comp_right (hg : g.IsFiberwiseEquiv)
    (hfg : IsFiberwiseEquiv (Pseudofunctor.StrongTrans.vcomp f g)) : f.IsFiberwiseEquiv := fun T ↦
  have := hg T
  have : ((f.app (.mk (op T))).toFunctor ⋙ (g.app (.mk (op T))).toFunctor).IsEquivalence :=
    hfg T
  Functor.isEquivalence_of_comp_right _ (g.app (.mk (op T))).toFunctor

/-- If `f` and the composite `Pseudofunctor.StrongTrans.vcomp f g` are fiberwise equivalences,
so is `g`. -/
lemma IsFiberwiseEquiv.of_comp_left (hf : f.IsFiberwiseEquiv)
    (hfg : IsFiberwiseEquiv (Pseudofunctor.StrongTrans.vcomp f g)) : g.IsFiberwiseEquiv := fun T ↦
  have := hf T
  have : ((f.app (.mk (op T))).toFunctor ⋙ (g.app (.mk (op T))).toFunctor).IsEquivalence :=
    hfg T
  Functor.isEquivalence_of_comp_left (f.app (.mk (op T))).toFunctor _

end Hom

end StackInGroupoids

end AlgebraicGeometry.FppfStacks
