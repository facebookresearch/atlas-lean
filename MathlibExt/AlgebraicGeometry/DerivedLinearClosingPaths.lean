/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
public import MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
public import MathlibExt.Algebra.Homology.RelativeCochainHomotopies
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
# Actual closing-data paths from normalized cochain homotopies

A path has the actual source/target vertices under native Dold--Kan
realization. Its degree-one normalized coefficient is fixed by the
given cochain homotopy applied to the actual degree-zero source cycle.
This fixes the whole one-simplex, not an arbitrary path with matching
endpoints. Relative source homotopies can be the computed cylinder lifts.

Reference: Dold--Kan and PTVV1111.3209v4 §2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths

open _root_.CategoryTheory _root_.Opposite
open CochainComplex CochainComplex.HomComplex
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The actual coefficient of a closing-data realization simplex. -/
def coefficient (K : GlobalComplex k) (m : ℕ) (x : ((realize k).obj K) _⦋m⦌) :
    K.X (-(m : ℤ)) := (coefficientMap K m).hom x

/-- The actual cochain-homotopy path, normalized on its complete degree-one coefficient. -/
structure LinearPath {F P : GlobalComplex k} (a b : F ⟶ P)
    (h : Cochain F P (-1))
    (dh : δ (-1) 0 h = Cochain.ofHom b - Cochain.ofHom a)
    (ω : ((realize k).obj F) _⦋0⦌) where
  edge : SSet.Edge (X := (realize k).obj P)
    (((realize k).map a).app (op ⦋0⦌) ω) (((realize k).map b).app (op ⦋0⦌) ω)
  normalized : coefficient P 1 edge.edge =
    (h.v 0 (-1) (by omega)).hom (coefficient F 0 ω)

end MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths
