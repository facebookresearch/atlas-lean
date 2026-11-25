/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModelContracts
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# DG algebras as monoid objects in cochain complexes

A differential graded algebra over `k` is a monoid object in cochain complexes of `k`-modules,
with the source monoidal structure (whose braiding carries the Koszul sign). This module holds only
that alias, so that consumers of DG algebras do not import the cyclic-bar API of
`MathlibExt.Algebra.Homology.DGCyclicBarModels`.
-/

@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology

open _root_.CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts

universe u

/-- A differential graded algebra over `k`: a monoid object in cochain complexes of
`k`-modules. -/
abbrev DGAlgebra (k : Type u) [CommRing k] := Mon (Cochains k)

end MathlibExt.Algebra.Homology

namespace MathlibExt.Algebra.Homology.DGCyclicBarModels

-- `DGAlgebra` stays available where clients open the cyclic-bar namespace.
export MathlibExt.Algebra.Homology (DGAlgebra)

end MathlibExt.Algebra.Homology.DGCyclicBarModels
