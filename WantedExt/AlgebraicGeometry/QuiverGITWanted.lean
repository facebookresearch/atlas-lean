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

/-- King's criterion: let $Q$ be a finite quiver, $d$ a dimension vector, $k$ an algebraically
closed field of characteristic zero and $\theta$ an integer weight with $\sum_v \theta_v d_v = 0$. A
representation $M$ of $Q$ of dimension $d$ over $k$ has a semi-invariant polynomial $f$ of some
weight $\chi_\theta^m$ with $m > 0$ (that is, $f(g \cdot M') = \chi_\theta(g)^m f(M')$ for all $g$
and $M'$, where $\chi_\theta(g) = \prod_v \det(g_v)^{\theta_v}$) with $f(M) \neq 0$ if and only if
$\sum_v \theta_v \dim W_v \ge 0$ for every subrepresentation $W$ of $M$. -/
public theorem_wanted king_numerical_criterion (Q : FiniteQuiver)
    (d : Q.Vertex → ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (θ : Q.Vertex → ℤ) (hθ : dimensionWeight Q d θ = 0)
    (M : Representation Q d k) :
    CharacterSemistable Q d k θ M ↔ NumericallySemistable Q d k θ M

end WantedExt.AlgebraicGeometry.QuiverGITWanted
