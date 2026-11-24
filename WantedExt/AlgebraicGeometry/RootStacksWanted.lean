/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RootStacks

/-!
# General root-stack construction on schemes

Construct the actual fppf stack with the prescribed line/section root
groupoids and normalized module pullbacks. Its fibres can be empty; this
does not claim a global nth root on the base scheme. No invertibility of n
is required for this fppf construction. DM/étale atlas comparisons require
that extra hypothesis and remain separate geometry.

Source: Cadman, *Using stacks to impose tangency conditions on curves*,
Definition 2.2.1 and Remark 2.2.2, pp. 4--5:
https://www.charlescadman.com/raw/pdf/stacks.pdf
https://doi.org/10.1353/ajm.2007.0007

Actual module pullback coherence and the local polynomial quotient algebra
are completed Mathlib support, not new Wanted requests. The shared
construction/descent provider and normalized root/atlas comparisons are
the deferred items below. The general algebraic-stack and 2-fibre primitives
are completed public source support credited in GeneralStackGeometry.

The Artin assertion uses the algebraic fibre-product construction of
Definition 2.2.1 and its actual-root description in Remark 2.2.2. The DM
assertion is Theorem 2.3.3, printed p. 7, with the exponent invertible on X.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RootStacksWanted

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.RootStacks

universe u

def_wanted root_stack (X : Scheme.{u}) (L : X.Modules)
    (_line : IsLineBundle L) (s : Section L) (n : ℕ) (_positive : 0 < n) :
    RootStack L s n

/-- The normalized positive-exponent root stack has an actual smooth atlas
and representable diagonal, even when the exponent is not invertible. -/
theorem_wanted root_stack_artin (X : Scheme.{u}) (L : X.Modules)
    (_line : IsLineBundle L) (s : Section L) (n : ℕ) (_positive : 0 < n)
    (R : RootStack L s n) : R.toRelativeStack.IsArtinStack

/-- Invertibility of the exponent gives the actual étale-atlas/DM conclusion
on the same computed relative-stack carrier. -/
theorem_wanted root_stack_deligne_mumford (X : Scheme.{u}) (L : X.Modules)
    (_line : IsLineBundle L) (s : Section L) (n : ℕ) (_positive : 0 < n)
    (_invertible : IsUnit (n : Γ(X, ⊤))) (R : RootStack L s n) :
    R.toRelativeStack.IsDeligneMumfordStack

end WantedExt.AlgebraicGeometry.RootStacksWanted
