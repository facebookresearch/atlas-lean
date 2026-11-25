/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Basic
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact postcomposition of cohomological δ-functors

An additive exact functor transports the degree functors, connecting maps
and exactness conditions of a cohomological δ-functor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CohomologicalDeltaFunctor

section ExactDeltaPostcomposition

universe uA vA uB vB uD vD
variable {A₀ : Type uA} [Category.{vA} A₀] [Preadditive A₀]
  {B₀ : Type uB} [Category.{vB} B₀] [Abelian B₀]
  {D₀ : Type uD} [Category.{vD} D₀] [Abelian D₀]
variable (F₀ : B₀ ⥤ D₀) [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]

/-- Exact output composition retains every delta degree and its connector map. -/
def exactDeltaPostcompose (T : CohomologicalDeltaFunctor A₀ B₀) :
    CohomologicalDeltaFunctor A₀ D₀ where
  T q := T.T q ⋙ F₀
  additive _q := inferInstance
  connecting q :=
    { app S := F₀.map ((T.connecting q).app S)
      naturality S U f := by
        simpa only [Functor.map_comp, Functor.comp_map, Functor.comp_obj] using
          congrArg F₀.map ((T.connecting q).naturality f) }
  exactLeft q S := by
    obtain ⟨h, hh⟩ := T.exactLeft q S
    refine ⟨?_, ?_⟩
    · exact (F₀.map_comp _ _).symm.trans ((congrArg F₀.map h).trans (F₀.map_zero _ _))
    · exact hh.map F₀
  exactMiddle q S := by
    obtain ⟨h, hh⟩ := T.exactMiddle q S
    refine ⟨?_, ?_⟩
    · exact (F₀.map_comp _ _).symm.trans ((congrArg F₀.map h).trans (F₀.map_zero _ _))
    · exact hh.map F₀
  exactRight q S := by
    obtain ⟨h, hh⟩ := T.exactRight q S
    refine ⟨?_, ?_⟩
    · exact (F₀.map_comp _ _).symm.trans ((congrArg F₀.map h).trans (F₀.map_zero _ _))
    · exact hh.map F₀
  monoZero S := by
    let : Mono ((T.T 0).map S.obj.f) := T.monoZero S
    change Mono (F₀.map ((T.T 0).map S.obj.f))
    infer_instance

end ExactDeltaPostcomposition

end CategoryTheory.CohomologicalDeltaFunctor
