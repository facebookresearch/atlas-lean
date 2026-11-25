/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import MathlibExt.AlgebraicGeometry.AbelianVerschiebung

/-!
# Actual higher-dimensional abelian Verschiebung

Construct V on an actual dimension-g abelian variety over F_p, with
F∘V=V∘F=[p] and finite-flat geometric degree p^g. The F operator, group
multiplication, identity section and torsion fibres are fixed constructions.
The input is not replaced by a bare F/V module or a chosen period map.

The elliptic F/V case and nonzero general multiplication isogenies have
existing source implementations. This packet requests their actual
higher-dimensional geometric F/V counterpart over the prime field.

Reference: Mumford, *Abelian Varieties*, §15; Milne, *Abelian Varieties*.
https://www.jmilne.org/math/CourseNotes/AV.pdf
Explicit public construction: Edixhoven–van der Geer–Moonen,
*Abelian Varieties*, Chapter 5, §2, Proposition (5.20), p. 80
(and (5.15), p. 76 for Frobenius degree).
https://gerard.vdgeer.net/AV.pdf
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AbelianVerschiebung

open CategoryTheory CategoryTheory.MonObj _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianVerschiebung

/-- Geometric Verschiebung of the actual abelian variety, in every dimension. -/
public def_wanted verschiebung
    (p : ℕ) [Fact p.Prime] (A : PrimeFieldScheme p) (g : ℕ)
    [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    [SmoothOfRelativeDimension g A.hom] [GeometricallyConnected A.hom] :
    VerschiebungData A g

end WantedExt.AlgebraicGeometry.AbelianVerschiebung
