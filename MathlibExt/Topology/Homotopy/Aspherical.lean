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

-- Source: Lean Definition Library (Airtable) records: Topology 368

/-!
# Aspherical

## References

* Hatcher's "Algebraic Topology" (p. 343), Davis and Kirk's "Lecture Notes in Algebraic Topology"
  (Section, 7.8 on Aspherical Spaces) (for `IsAspherical`)

## References

* Hatcher's "Algebraic Topology" (p. 343), Davis and Kirk's "Lecture Notes in Algebraic Topology"
  (Section, 7.8 on Aspherical Spaces) (for `IsAspherical`)

## References

* Hatcher's "Algebraic Topology" (p. 343), Davis and Kirk's "Lecture Notes in Algebraic Topology"
  (Section, 7.8 on Aspherical Spaces) (for `IsAspherical`)

## References

* Hatcher's "Algebraic Topology" (p. 343), Davis and Kirk's "Lecture Notes in Algebraic Topology"
  (Section, 7.8 on Aspherical Spaces) (for `IsAspherical`)

## References

* Hatcher's "Algebraic Topology" (p. 343), Davis and Kirk's "Lecture Notes in Algebraic Topology"
  (Section, 7.8 on Aspherical Spaces) (for `IsAspherical`)

## References

* Hatcher's "Algebraic Topology" (p. 343), Davis and Kirk's "Lecture Notes in Algebraic Topology"
  (Section, 7.8 on Aspherical Spaces) (for `IsAspherical`)

## References

* Hatcher's "Algebraic Topology" (p. 343), Davis and Kirk's "Lecture Notes in Algebraic Topology"
  (Section, 7.8 on Aspherical Spaces) (for `IsAspherical`)
-/

namespace MetaMathlibExt

-- Topology 368: Aspherical

/-- A topological space X is aspherical if its homotopy groups πₙ(X) are
trivial when n ≠ 1.
-/
def IsAspherical (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (n : ℕ), n ≠ 1 → Subsingleton (HomotopyGroup.Pi n X x)

end MetaMathlibExt

end
