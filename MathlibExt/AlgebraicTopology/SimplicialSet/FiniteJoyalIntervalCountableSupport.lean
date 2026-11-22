/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFiniteSupport
public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexCountability
public import MathlibExt.AlgebraicTopology.SimplicialSet.Countability
public import Mathlib.Data.Set.Countable

/-!
# Simultaneous countable support for the chosen replacement

Take the actual supremum of the finite supports of all selected simplices.
It has countably many nondegenerate simplices and countably many simplices
in total. Functoriality along its original inclusions retains every chosen
replacement preimage, in its original dimension, including degeneracies.

This is the project finite/countable support specialization of the bounded
support statement in Cisinski's Lemma 2.4.37.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- Every countable set of all replacement simplices has one actual
countable supporting subcomplex, with every original inclusion preimage. -/
theorem exists_countable_support (Y : SSet.{u})
    (T : Set (Σ n : ℕ, auxiliaryOmegaFreeFiller.obj Y _⦋n⦌)) (hT : T.Countable) :
    ∃ V : Y.Subcomplex, Countable (V : SSet.{u}).N ∧
      Countable (Σ n : ℕ, (V : SSet.{u}) _⦋n⦌) ∧
      ∀ t ∈ T, ∃ v : auxiliaryOmegaFreeFiller.obj (V : SSet.{u}) _⦋t.1⦌,
        (auxiliaryOmegaFreeFiller.map V.ι).app (op ⦋t.1⦌) v = t.2 := by
  classical
  have : Countable ↥T := hT.to_subtype
  choose U hU v hv using fun t : ↥T ↦ exists_finite_support Y t.val.2
  have : ∀ t : ↥T, SSet.Finite (U t : SSet.{u}) := hU
  let V : Y.Subcomplex := ⨆ t : ↥T, U t
  have hN : Countable (V : SSet.{u}).N := Subcomplex.countable_N_iSup U
  have : Countable (V : SSet.{u}).N := hN
  refine ⟨V, hN, countable_sigma_obj_of_countable_N (V : SSet.{u}), ?_⟩
  intro t ht
  let s : ↥T := ⟨t, ht⟩
  let i : (U s : SSet.{u}) ⟶ (V : SSet.{u}) :=
    Subcomplex.homOfLE (le_iSup U s)
  refine ⟨(auxiliaryOmegaFreeFiller.map i).app (op ⦋t.1⦌) (v s), ?_⟩
  change (auxiliaryOmegaFreeFiller.map i ≫ auxiliaryOmegaFreeFiller.map V.ι).app
    (op ⦋t.1⦌) (v s) = t.2
  rw [← Functor.map_comp, Subcomplex.homOfLE_ι]
  exact hv s

end SSet.joyalInterval
