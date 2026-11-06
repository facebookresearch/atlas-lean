/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source equalities allow arbitrary contexts; right-coset equalities allow right contexts only. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCosetRelation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A genuine coset step distinguishes actual equations from subgroup and earlier coset facts. -/
inductive Y522CosetMove (alphabet equationSource fixedSource : Type*) (earlier : ℕ)
  | equation (source : equationSource) (backward inverted : Bool)
      (before after : List (alphabet × Bool))
  | fixed (source : fixedSource) (backward : Bool) (after : List (alphabet × Bool))
  | prior (reference : Fin earlier) (backward : Bool) (after : List (alphabet × Bool))

/-- The exact literal word pair selected by one source or chronological right-coset step. -/
def y522CosetMoveEquation {alphabet equationSource fixedSource : Type*} {earlier : ℕ}
    (equations : equationSource → Y322WordEquation alphabet)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (prior : Fin earlier → Y322WordEquation alphabet) :
    Y522CosetMove alphabet equationSource fixedSource earlier → Y322WordEquation alphabet
  | .equation source backward inverted before after =>
      y322EquationContext (y322EquationOrient (equations source) backward inverted) before after
  | .fixed source backward after =>
      y322EquationContext (y322EquationOrient (fixed source) backward false) [] after
  | .prior reference backward after =>
      y322EquationContext (y322EquationOrient (prior reference) backward false) [] after

/-- Swapping a literal coset word pair is valid; inversion of both sides is not permitted. -/
theorem y522EquationOrient_coset {alphabet G : Type*} [Group G] (values : alphabet → G)
    (H : Subgroup G) (equation : Y322WordEquation alphabet)
    (h : equation.CosetValid values H) (backward : Bool) :
    (y322EquationOrient equation backward false).CosetValid values H := by
  cases backward with
  | false => exact h
  | true => exact y522CosetRelation_symm H h

/-- Only a common right word is transported through an earlier literal coset fact. -/
theorem y522EquationContext_coset_right {alphabet G : Type*} [Group G]
    (values : alphabet → G) (H : Subgroup G) (equation : Y322WordEquation alphabet)
    (h : equation.CosetValid values H) (after : List (alphabet × Bool)) :
    (y322EquationContext equation [] after).CosetValid values H := by
  unfold Y322WordEquation.CosetValid y322EquationContext
  simp only [List.nil_append, y322EquationWordValue_append]
  exact y522CosetRelation_right H h _

/-- Every selected step follows from actual source equalities or valid actual right-coset facts. -/
theorem y522CosetMoveEquation_valid {alphabet equationSource fixedSource G : Type*}
    [Group G] {earlier : ℕ} (values : alphabet → G) (H : Subgroup G)
    (equations : equationSource → Y322WordEquation alphabet)
    (he : ∀ s, (equations s).Valid values)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (hf : ∀ s, (fixed s).CosetValid values H)
    (prior : Fin earlier → Y322WordEquation alphabet)
    (hp : ∀ i, (prior i).CosetValid values H)
    (move : Y522CosetMove alphabet equationSource fixedSource earlier) :
    (y522CosetMoveEquation equations fixed prior move).CosetValid values H := by
  cases move with
  | equation source backward inverted before after =>
    apply y522CosetRelation_of_eq H
    exact y322EquationContext_valid values _
      (y322EquationOrient_valid values _ (he source) backward inverted) before after
  | fixed source backward after =>
    exact y522EquationContext_coset_right values H _
      (y522EquationOrient_coset values H _ (hf source) backward) after
  | prior reference backward after =>
    exact y522EquationContext_coset_right values H _
      (y522EquationOrient_coset values H _ (hp reference) backward) after

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
