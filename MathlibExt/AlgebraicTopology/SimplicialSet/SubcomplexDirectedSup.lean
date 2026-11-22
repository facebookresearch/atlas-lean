/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Finite simplicial sets factor through directed suprema of subcomplexes

Given a monotone directed nonempty family `F : J → X.Subcomplex` and a map from a
finite simplicial set into the supremum `⨆ j, F j`, the map factors through some
`F j`.  This is the pure `SSet` infrastructure used by the minimal-subfibration
chain-closure step.

The argument is categorical:

* the lattice supremum is the colimit in the preorder `X.Subcomplex` via
  `Preorder.colimitCoconeOfIsLUB` applied to `isLUB_iSup`;
* `SSet.Subcomplex.toSSetFunctor` preserves filtered colimits;
* a finite simplicial set is finitely presentable, hence every map to a filtered
  colimit factors through some stage via `IsFinitelyPresentable.exists_hom_of_isColimit`.

No fibration, minimality, Zorn, Kan, weak-equivalence, or topological content is
introduced.  The only directedness/nonemptiness assumption is that `J` be
filtered, which for a preorder is equivalent to directed + nonempty.
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SSet.Subcomplex

variable {X : SSet.{u}} {J : Type u} [Preorder J]

private noncomputable def coconeOfFamily {F : J → X.Subcomplex} (hF : Monotone F) :
    Cocone (hF.functor ⋙ toSSetFunctor (X := X)) :=
  toSSetFunctor.mapCocone (Preorder.colimitCoconeOfIsLUB hF.functor isLUB_iSup).cocone

private noncomputable def isColimit_coconeOfFamily {F : J → X.Subcomplex}
    (hF : Monotone F) [IsFiltered J] :
    IsColimit (coconeOfFamily hF) :=
  isColimitOfPreserves toSSetFunctor
    (Preorder.colimitCoconeOfIsLUB hF.functor isLUB_iSup).isColimit

/-- Finite simplicial sets factor through some stage of a directed supremum of
subcomplexes.

Given:

* `X : SSet`,
* a directed nonempty index preorder `J`,
* a monotone family `F : J → X.Subcomplex`,
* a finite simplicial set `A` and a map `f : A ⟶ ⨆ j, F j`,

there exist `j : J` and `g : A ⟶ F j` such that `g ≫ homOfLE (le_iSup F j) = f`.

The proof proceeds via the categorical colimit description of `⨆ F`,
preservation of filtered colimits by `Subcomplex.toSSetFunctor`, and finite
presentability of finite simplicial sets.

This is the pure-`SSet` provider required by the minimal-subfibration chain-closure
packet; it makes no fibration or minimality claim. -/
theorem finite_factors_through_directed_iSup {F : J → X.Subcomplex}
    (hF : Monotone F) [IsDirectedOrder J] [Nonempty J]
    {A : SSet.{u}} [SSet.Finite A]
    (f : A ⟶ (⨆ j, F j : X.Subcomplex)) :
    ∃ (j : J) (g : A ⟶ (F j : SSet.{u})),
      g ≫ homOfLE (le_iSup F j) = f := by
  have : IsFiltered J := inferInstance
  let c := coconeOfFamily (X := X) hF
  have hc : IsColimit c := isColimit_coconeOfFamily (X := X) hF
  have hι : ∀ j, c.ι.app j = homOfLE (le_iSup F j : F j ≤ ⨆ k, F k) := fun _ => rfl
  obtain ⟨j, g, hg⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit (J := J)
      (D := hF.functor ⋙ toSSetFunctor) hc f
  refine ⟨j, g, ?_⟩
  rw [hι j] at hg
  exact hg

end SSet.Subcomplex
