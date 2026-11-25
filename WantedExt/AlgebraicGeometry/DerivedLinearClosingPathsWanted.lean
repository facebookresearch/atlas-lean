/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths
public import Batteries.Util.ProofWanted

/-!
# Wanted native Dold--Kan realization of the prescribed cochain homotopy

The output one-simplex has both endpoints and its normalized coefficient
fixed by actual cochain maps. Dold--Kan uniquely supplies that simplex.
Reference: Dold--Kan; PTVV1111.3209v4 §2.2.
-/

open _root_.CategoryTheory _root_.Opposite
open CochainComplex.HomComplex
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths
open scoped Simplicial

universe u

def_wanted native_linear_closing_path (k : Type u) [CommRing k]
    (F P : GlobalComplex k) (a b : F ⟶ P) (h : Cochain F P (-1))
    (dh : δ (-1) 0 h = Cochain.ofHom b - Cochain.ofHom a)
    (ω : ((realize k).obj F) _⦋0⦌) : LinearPath a b h dh ω
