/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Opposite/Functor.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.EnrichedOppositeFunctor
public import MathlibExt.CategoryTheory.DGSource.DGOpposite
public import MathlibExt.CategoryTheory.DGSource.DGFunctor

/-!
# Opposite differential graded functors

The opposite of a DG functor uses its original chain map on each reversed Hom complex. Thus
its action on homogeneous morphisms is unchanged after reversing sources and targets. This is
the functorial counterpart of the Koszul-signed opposite DG category.

## References

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

namespace CategoryTheory.EnrichedFunctor

open Opposite MathlibExt.DGSource

universe v u₁ u₂

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
  [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- The opposite DG functor acts on a homogeneous morphism by the original functor's
degreewise map, with its source and target reversed. -/
theorem op_dgMap {X Y : Cᵒᵖ} (n : ℤ) (f : DGHom R n Y.unop X.unop) :
    F.op.dgMap n (X := X) (Y := Y) f = F.dgMap n f := by
  simp only [dgMap_apply, op_map]
  -- Opposite Hom complexes are definitionally the original complexes with endpoints reversed.
  rfl

end CategoryTheory.EnrichedFunctor
