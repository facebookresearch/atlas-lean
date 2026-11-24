/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ThetaQuotientSources
public import Batteries.Util.ProofWanted

/-!
# The normalized multiplicative-group actions on the Θ and nodal sources

The classes `ContractingAction` and `OppositeWeightAction` in
`ThetaQuotientSources` fix the actual coactions `X ↦ T ⊗ X` on the affine line
and `s ↦ T ⊗ s`, `t ↦ T⁻¹ ⊗ t` on `Spec R[s,t]/(st - π)`. These requests
construct the corresponding scheme actions over every base ring.

Reference: Alper–Halpern-Leistner–Heinloth, arXiv:1812.01128v5, §2.3 and §3.5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ThetaQuotientSources

open MathlibExt.AlgebraicGeometry.ThetaQuotientSources

/-- The weight-one contracting action of `𝔾ₘ` on `𝔸¹`. -/
def_wanted contractingAction (R : Type) [CommRing R] : ContractingAction R

/-- The weight `(1, -1)` action of `𝔾ₘ` on the nodal surface `st = π`. -/
def_wanted oppositeWeightAction (R : Type) [CommRing R] (π : R) : OppositeWeightAction R π

end WantedExt.AlgebraicGeometry.ThetaQuotientSources
