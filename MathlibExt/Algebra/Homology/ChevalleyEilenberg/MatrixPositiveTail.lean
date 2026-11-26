/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Matrix
public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTail

/-!
# Positive tails of finite matrix CE complexes

Let `k` be a commutative ring and `A` a unital `k`-algebra. The positive tail of the matrix CE
complex has term `⋀^(p+1)[k] gl_m(A)` in displayed degree `p`, and zero extension induces its
size maps.

The full complex's boundary from degree one to zero is zero. Consequently the tail cycles and
homology in degree `p` are canonically the full cycles and homology in degree `p+1`. The
comparison preserves cycle inclusions, homology projections, and size naturality.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- The positive exterior tail of a finite matrix CE complex.

Restrict the matrix complex along `p ↦ p+1`, retaining its canonical differential. -/
abbrev matrixPositiveTail (m : ℕ) := ChainComplex.positiveTail (matrixComplex k A m)

/-- The positive-tail map of a finite matrix size inclusion.

Restrict the canonical matrix zero-extension chain map to positive exterior degrees. -/
def matrixPositiveTailMap {m n : ℕ} (h : m ≤ n) : matrixPositiveTail k A m ⟶ matrixPositiveTail k A n :=
  ChainComplex.positiveTailMap (matrixZeroCornerMap k A h)

/-- The shifted component of a matrix positive-tail size map.

Its displayed degree-`p` component is the full matrix CE size-map component in degree `p+1`. -/
theorem matrixPositiveTailMap_f {m n : ℕ} (h : m ≤ n) (p : ℕ) :
    (matrixPositiveTailMap k A h).f p = (matrixZeroCornerMap k A h).f (p + 1) := rfl

/-- The exterior formula for a positive-tail matrix size map.

A wedge of `p+1` matrices maps to the wedge of their top-left zero extensions. -/
theorem matrixPositiveTailMap_pure {m n : ℕ} (h : m ≤ n) (p : ℕ)
    (v : Fin (p + 1) → Matrix (Fin m) (Fin m) A) :
    ((matrixPositiveTailMap k A h).f p).hom (exteriorPower.ιMulti k (p + 1) v) =
      exteriorPower.ιMulti k (p + 1) (fun i => Matrix.zeroExtend h (v i)) :=
  matrixZeroCornerMap_pure k A h (p + 1) v

/-- The cycle comparison for positive matrix CE tails.

The tail cycle object in degree `p` is isomorphic to the full matrix CE cycles in degree
`p+1`. -/
def matrixPositiveTailCyclesIso (m p : ℕ) :
    (matrixPositiveTail k A m).cycles p ≅ (matrixComplex k A m).cycles (p + 1) :=
  ChainComplex.positiveTailCyclesIso (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

/-- The homology comparison for positive matrix CE tails.

The tail homology in degree `p` is isomorphic to full matrix CE homology in degree `p+1`. -/
def matrixPositiveTailHomologyIso (m p : ℕ) :
    (matrixPositiveTail k A m).homology p ≅ matrixHomology k A m (p + 1) :=
  ChainComplex.positiveTailHomologyIso (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

/-- The inclusion formula for the positive-tail cycle comparison.

The cycle comparison followed by full cycle inclusion is the positive-tail cycle inclusion. -/
theorem matrixPositiveTailCyclesIso_i (m p : ℕ) :
    (matrixPositiveTailCyclesIso k A m p).hom ≫ (matrixComplex k A m).iCycles (p + 1) =
      (matrixPositiveTail k A m).iCycles p :=
  ChainComplex.positiveTailCyclesIso_i (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

/-- The projection formula for the positive-tail homology comparison.

The cycle comparison followed by the full homology projection equals the tail homology
projection followed by the homology comparison. -/
theorem matrixPositiveTailHomologyIso_π (m p : ℕ) :
    (matrixPositiveTailCyclesIso k A m p).hom ≫ (matrixComplex k A m).homologyπ (p + 1) =
      (matrixPositiveTail k A m).homologyπ p ≫ (matrixPositiveTailHomologyIso k A m p).hom :=
  ChainComplex.positiveTailHomologyIso_π (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

/-- Naturality of the positive-tail matrix homology comparison.

The tail homology map of zero extension commutes with the comparison to full homology in the
next degree. -/
theorem matrixPositiveTailHomologyIso_naturality {m n : ℕ} (h : m ≤ n) (p : ℕ) :
    HomologicalComplex.homologyMap (matrixPositiveTailMap k A h) p ≫
        (matrixPositiveTailHomologyIso k A n p).hom =
      (matrixPositiveTailHomologyIso k A m p).hom ≫ matrixZeroCornerHomologyMap k A h (p + 1) :=
  ChainComplex.positiveTailHomologyIso_naturality (matrixZeroCornerMap k A h)
    (matrixComplex_d_one_zero k A m) (matrixComplex_d_one_zero k A n) p

end ChevalleyEilenberg
