/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.DeBruijnNewman

@[expose] public section

namespace MathlibExt.NumberTheory.DeBruijnNewmanWanted

open MathlibExt.NumberTheory.DeBruijnNewman

/-!
# Catalogue bounds for the de Bruijn--Newman constant

The published endpoint bounds from Optimization Problems record 21a, in
their atomic zero-reality form against `H` and `ZerosAllReal`. The 2026
certified record rows (`0.1965`, `0.1875`) are recorded in the Sources
entry and omitted here. Newman's threshold theorem, which converts
these into bounds on `deBruijnNewmanConstant`, is not formalized.
-/

/-- Source: Rodgers and Tao, *The de Bruijn--Newman constant is
non-negative*, Forum Math. Pi 8 (2020): at every negative deformation
time, `H` has a nonreal zero. Known literature result; its proof is
not supplied here. -/
theorem_wanted rodgersTaoNegativeTime_wanted :
    ∀ lam : ℝ, lam < 0 → ¬ ZerosAllReal lam

/-- Source: Platt and Trudgian, *The Riemann hypothesis is true up to
3·10¹²*, Bull. Lond. Math. Soc. 53 (2021), via the Polymath15
criterion: at time `1 / 5` all zeros of `H` are real (catalogue upper
bound `0.2`). Known literature result; its proof and computation are
not supplied here. -/
theorem_wanted plattTrudgianUpperBound_wanted :
    ZerosAllReal (1 / 5 : ℝ)

end MathlibExt.NumberTheory.DeBruijnNewmanWanted
