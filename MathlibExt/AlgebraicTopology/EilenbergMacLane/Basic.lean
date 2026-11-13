/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Keith Mills
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Topology 442

/-!
# Eilenberg-MacLane Space

## References

* Hatcher Chapter 4 of 'Algebraic Topology';
  https://ncatlab.org/nlab/show/Eilenberg-Mac+Lane+space (for `IsEilenbergMaclaneSpace`)
-/

namespace MetaMathlibExt

-- Topology 442: Eilenberg-MacLane Space

/-- A connected space X is an Eilenberg-MacLane space K(G,n) if all homotopy groups πᵢ(X) are
trivial for i ≠ n and πₙ(X) ≅ G.
-/
def IsEilenbergMaclaneSpace (X G : Type*) [TopologicalSpace X] [Group G] (n : PNat) : Prop :=
  Nonempty X ∧
    ∀ (x : X), Nonempty (HomotopyGroup.Pi n X x ≃* G)
      ∧ ∀ (i : ℕ), (i ≠ n → Subsingleton (HomotopyGroup.Pi i X x))

end MetaMathlibExt

end
