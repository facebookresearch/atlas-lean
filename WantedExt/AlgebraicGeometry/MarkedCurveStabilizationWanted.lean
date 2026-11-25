/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

@[expose] public section

/-!
# Forgetting one marking and stabilizing

This family-level packet requests Knudsen's actual contraction after
forgetting a marking, with compatibility of sections, structure-sheaf
images and uniqueness. Existing graph contractions are numerical input;
they are not substituted for the morphism of curve families.

Source: F. F. Knudsen, The projectivity of the moduli space of stable
curves II, Math. Scand. 52 (1983), 161--199, §1.
https://stacks.math.columbia.edu/tag/0E7N
-/

namespace WantedExt.AlgebraicGeometry.MarkedCurveStabilization

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

universe u

/-- The unique stable marked model after forgetting the last marking. -/
public def_wanted forgetAndStabilize
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Over (Spec (.of k))) [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (n g : ℕ) (range : 0 < 2 * (g : ℤ) - 2 + n)
    (C : MarkedFamily S.left (n + 1) g) (hC : IsStable C) :
    StabilizationModel n g C

end WantedExt.AlgebraicGeometry.MarkedCurveStabilization
