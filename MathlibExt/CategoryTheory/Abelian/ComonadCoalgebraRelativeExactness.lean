/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.ComonadCoalgebra
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Relative exactness for comonad coalgebras

For a right exact coefficient functor, exactness on coalgebras is detected
on cofree objects. The coaction splits after the specified functor, providing
the required monomorphism comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Comonad
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (G : Comonad C) [G.toFunctor.Additive] [PreservesFiniteLimits G.toFunctor]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

omit [Abelian D] [F.Additive] [PreservesFiniteColimits F] in
/-- The split coaction detects monomorphisms after a right exact coefficient functor. -/
theorem forgetComposite_preservesMonomorphisms
    (h : PreservesFiniteLimits (G.toFunctor ⋙ F)) :
    (G.forget ⋙ F).PreservesMonomorphisms := by
  let := G.coalgebraAbelian
  have : PreservesFiniteLimits (G.toFunctor ⋙ F) := h
  constructor
  intro X Y f hf
  have : Mono f := hf
  have : Mono (G.forget.map f) := inferInstance
  have hmap : Mono ((G.toFunctor ⋙ F).map (G.forget.map f)) := inferInstance
  have hs : F.map X.a ≫ F.map (G.ε.app X.A) = 𝟙 (F.obj X.A) := by
    rw [← F.map_comp, X.counit, F.map_id]
  have hcoaction : Mono (F.map X.a) := mono_of_mono_fac hs
  have hn : F.map X.a ≫ (G.toFunctor ⋙ F).map (G.forget.map f) =
      (G.forget ⋙ F).map f ≫ F.map Y.a := by
    change F.map X.a ≫ F.map (G.map f.f) = F.map f.f ≫ F.map Y.a
    rw [← F.map_comp, ← F.map_comp, f.h]
  have hcomp : Mono (F.map X.a ≫ (G.toFunctor ⋙ F).map (G.forget.map f)) :=
    @mono_comp _ _ _ _ _ (F.map X.a) hcoaction ((G.toFunctor ⋙ F).map (G.forget.map f)) hmap
  have : Mono ((G.forget ⋙ F).map f ≫ F.map Y.a) := hn ▸ hcomp
  exact mono_of_mono ((G.forget ⋙ F).map f) (F.map Y.a)

/-- Relative left exactness of a coefficient functor is equivalent to left exactness on the cofree tensor functor. -/
theorem forgetComposite_preservesFiniteLimits_iff :
    PreservesFiniteLimits (G.forget ⋙ F) ↔ PreservesFiniteLimits (G.toFunctor ⋙ F) := by
  let := G.coalgebraAbelian
  constructor
  · intro h
    have : PreservesFiniteLimits (G.forget ⋙ F) := h
    have : G.cofree.IsRightAdjoint := G.adj.isRightAdjoint
    change PreservesFiniteLimits (G.cofree ⋙ (G.forget ⋙ F))
    infer_instance
  · intro h
    have : (G.forget ⋙ F).PreservesMonomorphisms := G.forgetComposite_preservesMonomorphisms F h
    have hc :
        PreservesFiniteColimits (G.forget ⋙ F) ↔
        (∀ S : ShortComplex G.Coalgebra,
          S.ShortExact → (S.map (G.forget ⋙ F)).Exact ∧ Epi ((G.forget ⋙ F).map S.g)) :=
      (Functor.preservesFiniteColimits_tfae (G.forget ⋙ F)).out 4 1
    have he :
        (∀ S : ShortComplex G.Coalgebra,
          S.ShortExact → (S.map (G.forget ⋙ F)).ShortExact) ↔
        PreservesFiniteLimits (G.forget ⋙ F) ∧ PreservesFiniteColimits (G.forget ⋙ F) :=
      (Functor.exact_tfae (G.forget ⋙ F)).out 1 4
    refine (he.mp ?_).1
    intro S hS
    have hr := (hc.mp inferInstance) S hS
    have : Mono S.f := hS.mono_f
    have : Epi ((G.forget ⋙ F).map S.g) := hr.2
    have : Mono ((G.forget ⋙ F).map S.f) := inferInstance
    change (S.map (G.forget ⋙ F)).ShortExact
    exact
      { exact := hr.1
        mono_f := by
          change Mono ((G.forget ⋙ F).map S.f)
          infer_instance
        epi_g := by
          change Epi ((G.forget ⋙ F).map S.g)
          exact hr.2 }

end CategoryTheory.Comonad
