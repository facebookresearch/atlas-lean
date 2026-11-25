/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MonomialModelRetractions
public import Batteries.Util.ProofWanted

/-!
# Geometric monomial retractions and discrepancy normalization

These requests concern the geometric coefficient-to-function-field bridge
and its normalization. Generic power-series/valuation/completion primitives
remain native or explicit source-integration inputs. Reference:
Blum--Jonsson, arXiv1706.04548v2, §§3--5, Theorems A/C.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MonomialModelRetractions

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.CenteredValuationSections

/-- Geometric realization of the supported-monomial formula in the actual function field. -/
def_wanted monomialRetraction
    {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) (x : V.X.left)
    (C : CompletionChart V x) (w : Fin C.dimension → ℝ) (hw : ∀ i, 0 < w i) :
    MonomialRetraction C w

/-- The chart supremum computes the log discrepancy of a divisorial valuation: let $k$ be an
algebraically closed field of characteristic zero, $P$ a log pair over $k$ whose proper birational
models all admit the comparison data (`HasModelCalculus P`), $v$ a real valuation of the function
field centred on the variety of $P$, and `R` a divisorial realization of $v$: a prime divisor $E$ on
a proper birational model and $c > 0$ with $\operatorname{ord}_v = c \cdot \operatorname{ord}_E$ on
the function field. Then the supremum over discrepancy charts of $v$ (`extendedDiscrepancy v`, in
the extended reals) equals $c \cdot a(E)$, where $a(E)$ is the log discrepancy of $E$. -/
theorem_wanted divisorial_discrepancy
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (P : LogPair k n) [HasModelCalculus P] (v : CenteredValuation P.variety)
    (R : DivisorialRealization v) :
    extendedDiscrepancy v =
      ((R.scale * LogPairs.logDiscrepancy R.model R.prime : ℝ) : EReal)

end MathlibExt.AlgebraicGeometry.MonomialModelRetractions
