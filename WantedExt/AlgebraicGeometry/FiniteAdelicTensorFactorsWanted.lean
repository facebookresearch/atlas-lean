/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors
public import MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactorsCompletedPlaceNorm

/-!
# Finite-extension local factor construction and normalization requests

These requests use the whole completed tensor algebra. Residue rank alone
must not replace nilpotent composition length. No separability is assumed.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 3.4 and 5.3.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FiniteAdelicTensorFactors

open MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors

/-- Split the actual finite tensor algebra into its local Artinian factors. -/
public def_wanted completedTensorFactors (K E F : Type) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E] : Factorization K E F

/-- Local length times local residue rank sums to the actual field degree. -/
public theorem_wanted totalLocalDegree (K E F : Type) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E]
    (D : Factorization K E F) : totalWeight D = Module.finrank K E

end WantedExt.AlgebraicGeometry.FiniteAdelicTensorFactors
