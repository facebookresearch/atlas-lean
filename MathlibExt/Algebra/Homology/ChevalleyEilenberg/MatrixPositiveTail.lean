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
# Positive tails of finite matrix Chevalley–Eilenberg complexes

The positive tail of a finite matrix Chevalley–Eilenberg complex has exterior degree p + 1 in
chain degree p. Top-left zero extension restricts to these tails.

Because the boundary from exterior degree one to zero vanishes, their cycles and homology
identify with the cycles and homology of the original complex in the next degree.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- The positive tail of the finite-matrix CE complex. -/
abbrev matrixPositiveTail (m : ℕ) := ChainComplex.positiveTail (matrixComplex k A m)

/-- Its finite zero-corner map, with no independently chosen map. -/
def matrixPositiveTailMap {m n : ℕ} (h : m ≤ n) : matrixPositiveTail k A m ⟶ matrixPositiveTail k A n :=
  ChainComplex.positiveTailMap (matrixZeroCornerMap k A h)

theorem matrixPositiveTailMap_f {m n : ℕ} (h : m ≤ n) (p : ℕ) :
    (matrixPositiveTailMap k A h).f p = (matrixZeroCornerMap k A h).f (p + 1) := rfl

theorem matrixPositiveTailMap_pure {m n : ℕ} (h : m ≤ n) (p : ℕ)
    (v : Fin (p + 1) → Matrix (Fin m) (Fin m) A) :
    ((matrixPositiveTailMap k A h).f p).hom (exteriorPower.ιMulti k (p + 1) v) =
      exteriorPower.ιMulti k (p + 1) (fun i => Matrix.zeroExtend h (v i)) :=
  matrixZeroCornerMap_pure k A h (p + 1) v

/-- The positive-tail cycles are the degree-`p+1` cycles. -/
def matrixPositiveTailCyclesIso (m p : ℕ) :
    (matrixPositiveTail k A m).cycles p ≅ (matrixComplex k A m).cycles (p + 1) :=
  ChainComplex.positiveTailCyclesIso (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

/-- The positive-tail homology is the degree-`p+1` homology. -/
def matrixPositiveTailHomologyIso (m p : ℕ) :
    (matrixPositiveTail k A m).homology p ≅ matrixHomology k A m (p + 1) :=
  ChainComplex.positiveTailHomologyIso (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

theorem matrixPositiveTailCyclesIso_i (m p : ℕ) :
    (matrixPositiveTailCyclesIso k A m p).hom ≫ (matrixComplex k A m).iCycles (p + 1) =
      (matrixPositiveTail k A m).iCycles p :=
  ChainComplex.positiveTailCyclesIso_i (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

theorem matrixPositiveTailHomologyIso_π (m p : ℕ) :
    (matrixPositiveTailCyclesIso k A m p).hom ≫ (matrixComplex k A m).homologyπ (p + 1) =
      (matrixPositiveTail k A m).homologyπ p ≫ (matrixPositiveTailHomologyIso k A m p).hom :=
  ChainComplex.positiveTailHomologyIso_π (matrixComplex k A m) (matrixComplex_d_one_zero k A m) p

/-- The shifted homology maps are natural under the matrix zero corners. -/
theorem matrixPositiveTailHomologyIso_naturality {m n : ℕ} (h : m ≤ n) (p : ℕ) :
    HomologicalComplex.homologyMap (matrixPositiveTailMap k A h) p ≫
        (matrixPositiveTailHomologyIso k A n p).hom =
      (matrixPositiveTailHomologyIso k A m p).hom ≫ matrixZeroCornerHomologyMap k A h (p + 1) :=
  ChainComplex.positiveTailHomologyIso_naturality (matrixZeroCornerMap k A h)
    (matrixComplex_d_one_zero k A m) (matrixComplex_d_one_zero k A n) p

end ChevalleyEilenberg
