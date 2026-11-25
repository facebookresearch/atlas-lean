/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFiller
public import MathlibExt.AlgebraicTopology.SimplicialSet.CountabilityHom
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Countability of the actual labelled attachment

Finite domains give countably many attaching maps into a countable simplicial
set. The complete labelled target coproduct is countable in each degree, and
the actual attachment pushout is its quotient together with the old degree.
Counting all degrees then bounds the full nondegenerate simplex set.

This is the finite/countable specialization of the replacement size argument
in Cisinski's Lemma 2.4.37. Generator monicity is not needed for countability.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.labelledFreeFiller

variable {I : Type u} [Countable I] {K D : I → SSet.{u}}
variable (j : ∀ i, K i ⟶ D i) [∀ i, (K i).Finite] [∀ i, Countable (D i).N]

private lemma countable_obj (X : SSet.{u}) [Countable X.N] (n : ℕ) :
    Countable ((labelledFreeFiller j).obj X _⦋n⦌) := by
  let c := attachCells j X
  let E : SSet.{u} ⥤ Type u := (evaluation _ _).obj (op ⦋n⦌)
  have : ∀ i : I, Countable (K i ⟶ X) := fun i => countable_hom_of_finite (K i) X
  have : Countable c.ι := by
    change Countable (Index K X)
    infer_instance
  have : ∀ i : c.ι, Countable (D (c.π i) _⦋n⦌) := fun i =>
    countable_obj_of_countable_N (D (c.π i)) (op ⦋n⦌)
  let cofan : Cofan (fun i : c.ι => D (c.π i) _⦋n⦌) :=
    Cofan.mk (c.cofan₂.pt _⦋n⦌) (fun i => (c.cofan₂.inj i).app (op ⦋n⦌))
  have hc : IsColimit cofan :=
    isColimitCofanMkObjOfIsColimit E (fun i : c.ι => D (c.π i))
      (fun i => c.cofan₂.inj i) c.isColimit₂
  have hsurj : Function.Surjective
      (fun q : Σ i : c.ι, D (c.π i) _⦋n⦌ => cofan.inj q.1 q.2) := by
    intro z
    obtain ⟨i, d, hd⟩ := Cofan.inj_jointly_surjective_of_isColimit hc z
    exact ⟨⟨i, d⟩, hd⟩
  have : Countable (c.cofan₂.pt _⦋n⦌) := hsurj.countable
  have : Countable (X _⦋n⦌) := countable_obj_of_countable_N X (op ⦋n⦌)
  have hpushout := c.isPushout.map E
  have hcover : Function.Surjective
      (fun q : X _⦋n⦌ ⊕ c.cofan₂.pt _⦋n⦌ => q.elim
        (((unit j).app X).app (op ⦋n⦌)) (c.g₂.app (op ⦋n⦌))) := by
    intro z
    obtain ⟨x, hx⟩ | ⟨d, hd⟩ := Types.eq_or_eq_of_isPushout hpushout z
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr d, hd⟩
  exact hcover.countable

/-- A countable labelled family with finite domains and countable targets
preserves countability of the full nondegenerate simplex set. -/
theorem countable_N (X : SSet.{u}) [Countable X.N] :
    Countable ((labelledFreeFiller j).obj X).N := by
  have : ∀ n : ℕ, Countable ((labelledFreeFiller j).obj X _⦋n⦌) :=
    countable_obj j X
  apply Function.Injective.countable
    (f := fun s : ((labelledFreeFiller j).obj X).N =>
      (⟨s.dim, s.simplex⟩ : Σ n : ℕ, (labelledFreeFiller j).obj X _⦋n⦌))
  intro s t h
  apply (N.ext_iff s t).2
  rw [S.ext_iff']
  obtain hd := congr_arg Sigma.fst h
  exact ⟨hd, by
    have hx := Sigma.mk.inj_iff.1 h
    apply eq_of_heq
    change HEq (cast _ s.simplex) t.simplex
    exact (cast_heq_iff_heq _ _ _).2 hx.2⟩

end SSet.labelledFreeFiller
