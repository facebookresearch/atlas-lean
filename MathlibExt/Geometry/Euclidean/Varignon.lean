/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.TwoD
import Mathlib.Analysis.Convex.Independent
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
open scoped EuclideanSpace

/-- **Varignon's theorem.** Let $A$, $B$, $C$, $D$ be any four points of the Euclidean plane
$\mathbb{R}^2$, degenerate and self-crossing configurations included, and let $P$, $Q$, $R$,
$S$ be the midpoints of $AB$, $BC$, $CD$, $DA$, that is $2P = A + B$, $2Q = B + C$,
$2R = C + D$ and $2S = D + A$. Write $[XYZ]$ for the oriented area of the triangle $XYZ$,
positive when $X$, $Y$, $Z$ are listed counterclockwise. Then $P + R = Q + S$, so the diagonals
of $PQRS$ bisect each other and $PQRS$ is a possibly degenerate parallelogram, and
$$2([PQR] + [PRS]) = [ABC] + [ACD],$$
that is, the signed area of $PQRS$ is half the signed area of $ABCD$.

Proves `Wanted` entry `varignon`.

Source: https://en.wikipedia.org/wiki/Varignon%27s_theorem.
`A B C D` are arbitrary points in the Euclidean plane, including degenerate or
self-crossing configurations.
`P Q R S` are the midpoints of sides AB, BC, CD, DA (`2 • P = A + B`, etc.).
Conclusion: `P + R = Q + S` (the diagonals of PQRS bisect each other, i.e. PQRS is a
parallelogram via parallel opposite sides / bisecting diagonals), and twice the signed area of
PQRS, expressed through `EuclideanGeometry.orientedTriangleArea`, equals the signed area of ABCD.
-/
theorem varignon :
  ∀ (A B C D P Q R S : EuclideanSpace ℝ (Fin 2)),
    2 • P = A + B → 2 • Q = B + C → 2 • R = C + D → 2 • S = D + A →
    P + R = Q + S ∧
    2 * (EuclideanGeometry.orientedTriangleArea P Q R +
      EuclideanGeometry.orientedTriangleArea P R S) =
      EuclideanGeometry.orientedTriangleArea A B C +
        EuclideanGeometry.orientedTriangleArea A C D := by
  intro A B C D P Q R S hP hQ hR hS
  have hP0 : 2 * P 0 = A 0 + B 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hP
    simpa using h
  have hP1 : 2 * P 1 = A 1 + B 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hP
    simpa using h
  have hQ0 : 2 * Q 0 = B 0 + C 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hQ
    simpa using h
  have hQ1 : 2 * Q 1 = B 1 + C 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hQ
    simpa using h
  have hR0 : 2 * R 0 = C 0 + D 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hR
    simpa using h
  have hR1 : 2 * R 1 = C 1 + D 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hR
    simpa using h
  have hS0 : 2 * S 0 = D 0 + A 0 := by
    have h := congrArg (fun X => X (0 : Fin 2)) hS
    simpa using h
  have hS1 : 2 * S 1 = D 1 + A 1 := by
    have h := congrArg (fun X => X (1 : Fin 2)) hS
    simpa using h
  have hPR : P + R = Q + S := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> linarith
  refine ⟨hPR, ?_⟩
  simp only [EuclideanGeometry.orientedTriangleArea_eq_det]
  simp [Matrix.det_fin_three]
  have sP0 : P 0 = (A 0 + B 0) / 2 := by linarith
  have sP1 : P 1 = (A 1 + B 1) / 2 := by linarith
  have sQ0 : Q 0 = (B 0 + C 0) / 2 := by linarith
  have sQ1 : Q 1 = (B 1 + C 1) / 2 := by linarith
  have sR0 : R 0 = (C 0 + D 0) / 2 := by linarith
  have sR1 : R 1 = (C 1 + D 1) / 2 := by linarith
  have sS0 : S 0 = (D 0 + A 0) / 2 := by linarith
  have sS1 : S 1 = (D 1 + A 1) / 2 := by linarith
  rw [sP0, sP1, sQ0, sQ1, sR0, sR1, sS0, sS1]
  ring

end

end MetaMathlibExt
