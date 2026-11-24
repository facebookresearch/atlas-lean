/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import MathlibExt.AlgebraicGeometry.QuiverGIT

/-!
# King's finite-quiver reductive numerical criterion

This is a concrete geometric invariant theory comparison on actual arrow
matrices and the actual product of vertex general linear groups.
Source: A. King, *Moduli of representations of finite-dimensional algebras*,
Quart. J. Math. 45 (1994), pp515--530, §3; M. Reineke,
https://arxiv.org/abs/0802.2147, §3, Theorem3.8. The character convention
`f(g⋅M)=χθ(g)^m f(M)` fixes the numerical inequality `θ(dim W)≥0`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.QuiverGITWanted

open MathlibExt.AlgebraicGeometry.QuiverGIT

/-- Nonvanishing of an actual determinant-character polynomial
semi-invariant is equivalent to the actual subrepresentation dimension
inequalities. The zero total weight is necessary for the central scalar
subgroup, which acts trivially on the arrow matrices. -/
public theorem_wanted king_numerical_criterion (Q : FiniteQuiver)
    (d : Q.Vertex → ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (θ : Q.Vertex → ℤ) (hθ : dimensionWeight Q d θ = 0)
    (M : Representation Q d k) :
    CharacterSemistable Q d k θ M ↔ NumericallySemistable Q d k θ M

end WantedExt.AlgebraicGeometry.QuiverGITWanted
