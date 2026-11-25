/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StableCurveStackModels

/-!
# Stable marked-curve stack realization

The source fibre groupoid, scheme pullbacks, markings, arrows and native
pseudofunctor unit/composition normalizations are defined in MathlibExt.
This constructor supplies their fppf stack realization, DM/finite-type
scope and the actual pure dimension. It assumes no clutching, psi, or
double-ramification formula.
Source: Deligne--Mumford stable curves; JPPZ arXiv:1602.04705v2,
Sections 0.3.2--0.3.3, printed pp8--9.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.StableCurveStackModelsWanted

open MathlibExt.AlgebraicGeometry.StableCurveStackModels

def_wanted stableMarkedCurveStack (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g n : ℕ) (stable_range : 0 < 2 * (g : ℤ) - 2 + n) :
    StableCurveStackModel (k := k) g n

end WantedExt.AlgebraicGeometry.StableCurveStackModelsWanted
