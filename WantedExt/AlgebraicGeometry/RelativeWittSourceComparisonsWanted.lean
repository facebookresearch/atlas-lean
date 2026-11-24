/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
public import MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels

/-!
# Direct Witt normalization and general reductive ind-geometry requests

Source: Zhu, arXiv:1407.8519v3, formula (0.1.2), pp. 2--3,
Theorem 1.4, p. 9, Proposition 1.20, p. 16, and Section 1.4.
All perfect residue-field and coefficient hypotheses are explicit.

The direct `W(R)` lattice transport uses the actual proved tensor and
localized ring equivalences. The general reductive target is the
original fpqc positive-loop quotient. Finite convolution maps retain
the actual twisted quotient, native multiplication, proper scheme fibres
and every transition/colimit square. Generic etale quotient descent and
the original Witt/loop maps are completed public inputs.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeWittSourceComparisons

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
open MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels
open MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
open MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels
open MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels

/-- Normalize the original tensor lattice functor to actual W(R) submodules. -/
public def_wanted unramifiedLatticeTransport
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (perfect : Function.Bijective (fun x : k ↦ x ^ p)) (n : ℕ)
    (D : ScalarExtension p k (WittVector p k) (p : WittVector p k) n) :
    LatticeComparison p k n D

/-- Supply the direct source functor and native matrix actions without a chosen tensor provider. -/
public def_wanted unramifiedLatticeFunctor
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (perfect : Function.Bijective (fun x : k ↦ x ^ p)) (n : ℕ) :
    UnramifiedModel p k n

/-- Realize the original reductive quotient as actual proper ind-perfections. -/
public def_wanted reductiveGrassmannianGeometry
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
    (C : CoefficientData p k B pi)
    (G : Over (Spec (.of B))) [GrpObj G] [IsReductive (Spec (.of B)) G] :
    GrassmannianGeometry p k B pi G

/-- Realize proper convolution through the original native twisted-product map. -/
public def_wanted reductiveConvolutionGeometry
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
    (C : CoefficientData p k B pi)
    (G : Over (Spec (.of B))) [GrpObj G] [IsReductive (Spec (.of B)) G]
    (M : GrassmannianGeometry p k B pi G) : ConvolutionGeometry p k B pi G M

end WantedExt.AlgebraicGeometry.RelativeWittSourceComparisons
