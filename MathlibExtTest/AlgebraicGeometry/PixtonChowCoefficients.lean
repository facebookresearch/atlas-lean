/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PixtonChowPolynomialModels
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Source checks for the first edge terms: c, -c^2 psi/2, and the mixed
c^3 psi_h psi_h'/3. The mixed coefficient detects the missing binomial
factor; the sign detects reversing the exponential. An undecorated edge
still contributes codimension one, so it cannot occur in degree zero.
-/

open MathlibExt.AlgebraicGeometry.PixtonChowOperators
open MathlibExt.AlgebraicGeometry.UniversalCurveStability

example (c : ℚ) : edgeCoefficient c 0 0 = c := by
  simp [edgeCoefficient]

example (c : ℚ) : edgeCoefficient c 1 0 = -(c ^ 2) / 2 := by
  norm_num [edgeCoefficient]

example (c : ℚ) : edgeCoefficient c 1 1 = c ^ 3 / 3 := by
  norm_num [edgeCoefficient, Nat.factorial]
  ring

example {g n d : ℕ} (G : StableGraph g n) (e : Exponent G d)
    (edge : 0 < G.edges) : decoratedCodimension G e ≠ 0 := by
  unfold decoratedCodimension
  omega
