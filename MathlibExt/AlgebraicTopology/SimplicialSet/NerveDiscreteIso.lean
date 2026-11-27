/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# The nerve of a discrete category

A simplex in the nerve of a discrete category is determined by its vertex
at zero. This gives the canonical isomorphism with the constant simplicial
set on the original object type, in every universe.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

/-- A chain in a discrete category is canonically its value at vertex zero. -/
noncomputable def nerveDiscreteObjEquiv (X : Type u)
    (a : SimplexCategoryᵒᵖ) :
    (nerve (Discrete X)).obj a ≃ X where
  toFun F := (F.obj 0).as
  invFun x := (Functor.const (Fin (a.unop.len + 1))).obj (Discrete.mk x)
  left_inv F := by
    fapply CategoryTheory.Functor.ext
    · intro i
      apply Discrete.ext
      exact Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le i)))
    · intro i j f
      exact Subsingleton.elim _ _
  right_inv _ := rfl

/-- The nerve of a discrete category is the constant simplicial set on its
object type. -/
noncomputable def nerveDiscreteIso (X : Type u) :
    nerve (Discrete X) ≅ (Functor.const SimplexCategoryᵒᵖ).obj X :=
  NatIso.ofComponents (fun a => (nerveDiscreteObjEquiv X a).toIso) (by
    intro a b k
    apply ConcreteCategory.hom_ext
    intro F
    exact (Discrete.eq_of_hom
      (F.map (homOfLE (Fin.zero_le (k.unop.toOrderHom 0))))).symm)

/-- The canonical discrete-nerve comparison reads the literal first vertex. -/
theorem nerveDiscreteIso_hom_app_apply (X : Type u) (a : SimplexCategoryᵒᵖ)
    (F : (nerve (Discrete X)).obj a) :
    (nerveDiscreteIso X).hom.app a F = (F.obj 0).as := rfl

/-- The canonical comparison commutes with every map of object types. -/
theorem nerveDiscreteIso_natural {X Y : Type u} (f : X ⟶ Y) :
    nerveMap (Discrete.functor (fun x => Discrete.mk (f x))) ≫ (nerveDiscreteIso Y).hom =
      (nerveDiscreteIso X).hom ≫ (Functor.const SimplexCategoryᵒᵖ).map f := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro F
  rfl

end SSet
