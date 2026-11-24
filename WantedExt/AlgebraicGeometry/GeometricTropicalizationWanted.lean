/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ValuativeTropicalization

/-!
# General geometric tropical lifting and initial-support comparison

For any complete algebraically closed nontrivially valued rank-one field,
any finite torus and any actual closed ideal, lift an actual residue point
of the translated initial scheme to a torus point of the original scheme.
The normalized coordinates are genuine units of the native valuation ring,
with their residue coordinates fixed. Thus both the valuation vector and
leading residue data are pinned to actual maps.

The support comparison uses the literal initial ideal and closure of actual
valued points. There is no arbitrary tropicalization, balanced weight or
virtual/cohomological carrier in either statement.

Source: W. Gubler, *A guide to tropicalizations*,
https://arxiv.org/abs/1108.6126, Theorem5.6 and Proposition11.5; Definitions5.1
and13.4 pin initial schemes and multiplicities. TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9 already proves weight-initial algebra,
flat Rees degeneration and Newton--Puiseux; these are covered dependencies,
not re-requested as missing primitives.

Broader rational cone-complex/balancing, multiplicity independence, family,
intersection/proper-image and analytic-skeleton providers remain explicit
work. Public contracts make task statements possible; proof readiness still
requires their actual constructions and compatibility proofs.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeometricTropicalizationWanted

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ValuativeTropicalization

/-- Tropical lifting with actual residue/coordinate normalization. All
geometric field hypotheses are explicit binders of the stored declaration. -/
public def_wanted initialPointLift {K : Type} [Field K] [Valued K NNReal]
    [CompleteSpace K] [IsAlgClosed K]
    (_nontrivial : (Valued.v : Valuation K NNReal).IsNontrivial) {n : ℕ}
    (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ)
    (p : Point (initialIdeal I t) (Residue (K := K))) : InitialPointLift I t p

/-- The general fundamental tropical support theorem at every realized
weight, with the actual initial scheme and valued-point closure fixed. -/
public theorem_wanted initial_support {K : Type} [Field K] [Valued K NNReal]
    [CompleteSpace K] [IsAlgClosed K]
    (_nontrivial : (Valued.v : Valuation K NNReal).IsNontrivial) {n : ℕ}
    (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ) :
    initialIdeal I t ≠ ⊤ ↔ weightVector t ∈ tropicalizationOver (L := K) I

end WantedExt.AlgebraicGeometry.GeometricTropicalizationWanted
