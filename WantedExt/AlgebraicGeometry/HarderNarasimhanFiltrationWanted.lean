/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Harder–Narasimhan existence for actual curve bundles

The requested filtration has actual bundle inclusions and categorical
cokernels. Its slopes come from actual coherent cohomology, and its
semistability condition tests saturated subbundles. On a smooth curve this
is equivalent to testing all coherent subsheaves of intermediate rank.

Reference: Huybrechts–Lehn, *The Geometry of Moduli Spaces of Sheaves*,
Chapter 1, https://doi.org/10.1017/CBO9780511711985.

Covered reflexive-module operations are not requested again. This packet
is the geometric slope-filtration provider for smooth proper curves.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HarderNarasimhanFiltrationWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration

universe u

theorem_wanted exists_harderNarasimhanFiltration
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (E : C.left.Modules) (r : ℕ) (hr : 0 < r)
    (hE : IsVectorBundle E r) : Nonempty (Filtration C.hom E r)

end WantedExt.AlgebraicGeometry.HarderNarasimhanFiltrationWanted
