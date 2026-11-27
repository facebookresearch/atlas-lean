/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels

@[expose] public noncomputable section

open MathlibExt.AlgebraicGeometry.IntegralChowChernModels

namespace IntegralChowChernModelsTest

variable {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ} (D : ChernConstruction X E r)

/-- `c₀` is the identity (up to the degree cast `d = d - 0`). -/
example (d : ℤ) (x : Chow X d) : chernCap D 0 d x = chowCast X (by simp) x := by
  simp [chernCap]

/-- Chern classes above the rank vanish. -/
example (n : ℕ) (hn : r < n) (d : ℤ) : chernCap D n d = 0 := by
  simp [chernCap, show n ≠ 0 by omega, show ¬n ≤ r by omega]

/-- Below the rank, `cₙ` is the recursively inverted signed Segre series. -/
example (n : ℕ) (hn₀ : n ≠ 0) (hn : n ≤ r) (d : ℤ) :
    chernCap D n d = chernRec (D.projective (by omega)) n d := by
  simp [chernCap, hn₀, hn]

/-- With the quotient convention the sign cancels in degree one: `c₁ = s₁`. -/
example (hr : 0 < r) (d : ℤ) (x : Chow X d) :
    chernRec (D.projective hr) 1 d x =
      chowCast X (by omega)
        (projectiveSegre (D.projective hr) 1 (d - ((0 : ℕ) : ℤ))
          (chernRec (D.projective hr) 0 d x)) := by
  rw [chernRec.eq_2]
  simp [Int.negOnePow_one]

/-- Powers of the first Chern cap start at the identity. -/
example {L : X.scheme.left.Modules} (V : LineTotalModel X L) (C : LineChowComparison V)
    (d : ℤ) (x : Chow X d) : firstChernPower V C 0 d x = chowCast X (by simp) x := by
  simp [firstChernPower]

/-- The cycle coordinates accept Noetherian schemes in any universe. -/
example (Y : AlgebraicGeometry.Scheme.{1}) [AlgebraicGeometry.IsNoetherian Y] :
    AlgebraicGeometry.AlgebraicCycle Y ℤ →ₗ[ℤ] (Y →₀ ℤ) :=
  AlgebraicGeometry.IntegralOperationalChow.cycleCoordinates Y

end IntegralChowChernModelsTest
