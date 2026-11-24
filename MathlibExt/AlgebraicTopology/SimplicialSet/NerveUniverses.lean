/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Full faithfulness of the nerve with separate universes

The pinned nerve adjunction exposes full faithfulness with equal object
and morphism universes. The same native nerve and strict Segal APIs give
full faithfulness with separate universes. Reconstruct the original
object and arrow maps, prove identity and composition by the original
nerve triangles, then recover every simplex by strict Segal uniqueness.
No object or simplicial value universe is changed.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.NerveUniverses

variable {C D : Type v} [Category.{u} C] [Category.{u} D]

/-- Recover the original ordinary functor from the original full nerve map. -/
def functorOfMap (φ : nerve C ⟶ nerve D) : C ⥤ D where
  obj x := nerveEquiv (φ.app (op ⦋0⦌) (show (nerve C) _⦋0⦌ from nerveEquiv.symm x))
  map f := nerve.homEquiv ((nerve.edgeMk f).map φ)
  map_id x := by
    let s : (nerve C) _⦋0⦌ := nerveEquiv.symm x
    have hi : (SSet.Edge.id s).map φ = SSet.Edge.id (φ.app (op ⦋0⦌) s) := SSet.Edge.map_id s φ
    have h : nerve.homEquiv ((SSet.Edge.id s).map φ) = 𝟙 (nerveEquiv (φ.app (op ⦋0⦌) s)) :=
      (congrArg nerve.homEquiv hi).trans (nerve.homEquiv_id _)
    exact (congrArg (fun e => nerve.homEquiv (e.map φ)) (nerve.edgeMk_id x)).trans h
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).mpr rfl
    exact (nerve.homEquiv_comp (h.map φ)).symm

/-- The reconstructed functor recovers every original simplex of the nerve map. -/
theorem nerveMap_functorOfMap (φ : nerve C ⟶ nerve D) : nerveMap (functorOfMap φ) = φ := by
  ext n s
  have h : (SSet.truncation (n.unop.len + 1)).map (nerveMap (functorOfMap φ)) =
      (SSet.truncation (n.unop.len + 1)).map φ := by
    apply SSet.Truncated.IsStrictSegal.hom_ext
    intro f
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective f
    exact (nerveMap_app_mk₁ (functorOfMap φ) f).trans
      ((nerve.mk₁_homEquiv_apply ((nerve.edgeMk f).map φ)).trans
        (ComposableArrows.mk₁_hom (φ.app (op ⦋1⦌) (ComposableArrows.mk₁ f))))
  have ha := NatTrans.congr_app h (op ⟨n.unop, by simp⟩)
  exact ConcreteCategory.congr_hom ha s

/-- Reading the nerve of an ordinary functor returns that whole original functor. -/
theorem functorOfMap_nerveMap (F : C ⥤ D) : functorOfMap (nerveMap F) = F := by
  refine CategoryTheory.Functor.hext (F := functorOfMap (nerveMap F)) (G := F)
    ?_ ?_
  · intro x
    change nerveEquiv ((nerveMap F).app (op ⦋0⦌) (ComposableArrows.mk₀ x)) = F.obj x
    exact congrArg nerveEquiv (nerveMap_app_mk₀ F x)
  intro x y f
  exact heq_of_eq (nerve.homEquiv_edgeMk_map_nerveMap f F)

end CategoryTheory.NerveUniverses

namespace CategoryTheory

/-- Native full faithfulness of the same nerve functor with separate object and morphism universes. -/
def nerveFunctor.fullyFaithfulUniverses : nerveFunctor.{u, v}.FullyFaithful where
  preimage φ := (NerveUniverses.functorOfMap φ).toCatHom
  map_preimage φ := NerveUniverses.nerveMap_functorOfMap φ
  preimage_map F := by
    apply Cat.ext
    exact NerveUniverses.functorOfMap_nerveMap F.toFunctor

instance (priority := 900) nerveFunctor.fullUniverses : nerveFunctor.{u, v}.Full :=
  (nerveFunctor.fullyFaithfulUniverses).full

instance (priority := 900) nerveFunctor.faithfulUniverses : nerveFunctor.{u, v}.Faithful :=
  (nerveFunctor.fullyFaithfulUniverses).faithful

end CategoryTheory
