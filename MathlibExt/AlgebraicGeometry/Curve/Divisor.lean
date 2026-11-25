/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finsupp.Basic

/-!
# Divisors on a curve

This file defines divisors on an abstract type of points as formal finite integer linear
combinations of those points.
-/

@[expose] public section

/-- **Divisors on a curve.** For a set $C$ (the points of a curve), a divisor on $C$ is a finitely
supported function $D \colon C \to \mathbb{Z}$. Its support is the finite set of points
$P \in C$ with $D(P) \neq 0$. -/
abbrev CurveDivisor (C : Type*) := C →₀ ℤ

namespace CurveDivisor

variable {C : Type*}

/-- **Coefficient of a divisor at a point.** For a divisor $D$ on a set of points $C$ and a
point $P \in C$, the coefficient of $D$ at $P$ is the integer $D(P)$. -/
def coeff (D : CurveDivisor C) (P : C) : ℤ := D P

@[simp]
theorem coeff_single (P : C) (n : ℤ) :
    coeff (Finsupp.single P n) P = n := by
  classical
  simp [coeff]

end CurveDivisor
