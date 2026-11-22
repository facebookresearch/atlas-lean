/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFreeFiller
public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerCountability
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Countability of the chosen omega attachment

The actual stages are countable by the original labelled attachment theorem
and their specified zero and successor isomorphisms. Each degree of the chosen
colimit is a surjective image of all natural-number stage values. Counting all
degrees then counts its entire nondegenerate simplex set.

This is the project countable specialization of Cisinski's Construction 2.4.36
and Lemma 2.4.37, and of Construction 1.2.34 and Proposition 1.2.35 in the
2006 monograph. No subcomplex-union or fibrancy conclusion is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.joyalInterval

private lemma stage_countable_N (X : SSet.{u}) [Countable X.N] (n : ℕ) :
    Countable ((auxiliaryOmegaStages.{u}.obj n).obj X).N := by
  induction n with
  | zero =>
    exact Countable.of_equiv X.N
      (N.orderIsoOfIso (auxiliaryOmegaStagesZeroIso.{u}.app X)).toEquiv.symm
  | succ n ih =>
    have : ∀ i : AuxiliaryGeneratorIndex.{u}, (auxiliaryGeneratorArrow i).left.Finite :=
      finite_auxiliaryGeneratorArrow_source
    have : ∀ i : AuxiliaryGeneratorIndex.{u}, Countable (auxiliaryGeneratorArrow i).right.N :=
      fun i => by
        have : (auxiliaryGeneratorArrow i).right.Finite := finite_auxiliaryGeneratorArrow_target i
        infer_instance
    have : Countable (auxiliaryFreeFiller.obj ((auxiliaryOmegaStages.{u}.obj n).obj X)).N := by
      change Countable ((labelledFreeFiller
        (fun i : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow i).hom)).obj _).N
      exact labelledFreeFiller.countable_N _ _
    exact Countable.of_equiv
      (auxiliaryFreeFiller.obj ((auxiliaryOmegaStages.{u}.obj n).obj X)).N
      (N.orderIsoOfIso ((auxiliaryOmegaStagesSuccIso.{u} n).app X)).toEquiv.symm

private lemma omega_countable_obj (X : SSet.{u}) [Countable X.N] (k : ℕ) :
    Countable (auxiliaryOmegaFreeFiller.{u}.obj X _⦋k⦌) := by
  have : ∀ n : ℕ, Countable ((auxiliaryOmegaStages.{u}.obj n).obj X _⦋k⦌) := fun n => by
    have := stage_countable_N X n
    exact countable_obj_of_countable_N _ (op ⦋k⦌)
  let E : (SSet.{u} ⥤ SSet.{u}) ⥤ SSet.{u} := (evaluation _ _).obj X
  let Eₖ : SSet.{u} ⥤ Type u := (evaluation _ _).obj (op ⦋k⦌)
  have hc := isColimitOfPreserves Eₖ
    (isColimitOfPreserves E (colimit.isColimit auxiliaryOmegaStages.{u}))
  have hsurj : Function.Surjective
      (fun s : Σ n : ℕ, (auxiliaryOmegaStages.{u}.obj n).obj X _⦋k⦌ =>
        ((colimit.ι auxiliaryOmegaStages.{u} s.1).app X).app (op ⦋k⦌) s.2) := by
    intro z
    obtain ⟨n, s, hs⟩ := Types.jointly_surjective_of_isColimit hc z
    exact ⟨⟨n, s⟩, hs⟩
  exact hsurj.countable

/-- The actual chosen omega functor preserves countability of the full
nondegenerate simplex set in the original value universe. -/
theorem auxiliaryOmegaFreeFiller_countable_N (X : SSet.{u}) [Countable X.N] :
    Countable (auxiliaryOmegaFreeFiller.{u}.obj X).N := by
  have : ∀ k : ℕ, Countable (auxiliaryOmegaFreeFiller.{u}.obj X _⦋k⦌) :=
    omega_countable_obj X
  apply Function.Injective.countable
    (f := fun s : (auxiliaryOmegaFreeFiller.{u}.obj X).N =>
      (⟨s.dim, s.simplex⟩ : Σ k : ℕ, auxiliaryOmegaFreeFiller.{u}.obj X _⦋k⦌))
  intro s t h
  apply (N.ext_iff s t).2
  rw [S.ext_iff']
  obtain hd := congr_arg Sigma.fst h
  exact ⟨hd, by
    have hx := Sigma.mk.inj_iff.1 h
    apply eq_of_heq
    change HEq (cast _ s.simplex) t.simplex
    exact (cast_heq_iff_heq _ _ _).2 hx.2⟩

end SSet.joyalInterval
