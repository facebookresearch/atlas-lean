/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

/-!
# Deligne–Illusie decomposition on actual prime-field de Rham sheaves

The de Rham object is the actual sheafification of the sectionwise
Kähler/exterior-power complex with its normalized differential. The
right side consists of its actual differential-form sheaves placed in
their cohomological degrees. Under `dim X < p` this is the full complex,
so the truncation appearing in the general theorem is unnecessary.

The lift is an actual proper smooth scheme over `W₂(F_p)` whose special
fibre square is cartesian via the zeroth Witt coordinate. Ordinary de Rham
and Cartier constructions already have public Axiom implementations;
their existence is not requested again.

References: P. Deligne–L. Illusie, *Relèvements modulo p² et décomposition
du complexe de de Rham*, Invent. Math. 89 (1987), 247–270, Théorème 2.1.
The scope and derived decomposition are also displayed in Achinger–Suh,
*Some refinements of the Deligne–Illusie theorem*, §1A, p. 465.
https://msp.org/ant/2023/17-2/ant-v17-n2-p06-p.pdf
The Axiom HodgeSpreadingOut/CharZero implementation explicitly takes this
characteristic-p theorem as `hDI`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DeligneIllusie

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

attribute [local instance] HasDerivedCategory.standard

/-- The genuine derived de Rham splitting, with actual geometric lift. -/
public theorem_wanted deligneIllusie
    (p : ℕ) [Fact p.Prime] (X : PrimeFieldScheme p) (d : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom] (hd : d < p)
    (D : Differential p X)
    (Y : Over (Spec (CommRingCat.of.{0}
      (TruncatedWittVector p 2 (ZMod p)))))
    [IsProper Y.hom] [Smooth Y.hom]
    (j : X.left ⟶ Y.left)
    (hfibre : IsPullback j X.hom Y.hom
      (Spec.map (CommRingCat.ofHom (wittReduction p)))) :
    Nonempty (D.derived ≅ ∐ fun i : Fin (d + 1) =>
      (DerivedCategory.singleFunctor X.left.Modules (i : ℤ)).obj
        (forms p X i))

end WantedExt.AlgebraicGeometry.DeligneIllusie
