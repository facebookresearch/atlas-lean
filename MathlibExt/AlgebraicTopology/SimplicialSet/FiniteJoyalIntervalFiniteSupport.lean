/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteSubcomplexColimit
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Finite support of every simplex in the chosen replacement

The chosen omega functor preserves the actual finite-subcomplex cover.
Evaluating its mapped colimit in any degree gives a jointly surjective
family of original inclusion maps. Every replacement simplex therefore
has a literal preimage in the replacement of one finite subcomplex.

This is the finite simplicial specialization of the support step in
Cisinski's Lemma 2.4.37, using the actual chosen finitary replacement.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- Every simplex of the actual replacement comes from the replacement
of a finite subcomplex, along its original inclusion. -/
theorem exists_finite_support (Y : SSet.{u}) {n : ℕ}
    (z : auxiliaryOmegaFreeFiller.obj Y _⦋n⦌) :
    ∃ V : Y.Subcomplex, SSet.Finite (V : SSet.{u}) ∧
      ∃ v : auxiliaryOmegaFreeFiller.obj (V : SSet.{u}) _⦋n⦌,
        (auxiliaryOmegaFreeFiller.map V.ι).app (op ⦋n⦌) v = z := by
  let L := auxiliaryOmegaFreeFiller.{u}
  let E : SSet.{u} ⥤ Type u := (evaluation _ _).obj (op ⦋n⦌)
  have hc := isColimitOfPreserves E
    (isColimitOfPreserves L (Subcomplex.isColimit_finiteSubcomplex Y))
  obtain ⟨V, v, hv⟩ := Types.jointly_surjective_of_isColimit hc z
  exact ⟨V.val, V.property, v, hv⟩

end SSet.joyalInterval
