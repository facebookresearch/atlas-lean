/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Connected.Basic

@[expose] public section

namespace MathlibExt.Algebra.Polynomial.ScottishBook148Wanted

/--
Let `P` be a nonzero real polynomial in `n` variables. Its zero set does
not cut (separate) Euclidean space, i.e. the complement of the zero set is
connected, if and only if every irreducible factor of `P` over the reals is
always nonnegative or always nonpositive (as a function). The complement of
a real algebraic hypersurface is semialgebraic, so connectedness of the
complement is equivalent to the path-connectedness used by Rojas.
Source: H. Auerbach, Problem 148 of the Scottish Book; both necessity and
sufficiency proved by J. M. Rojas, "About Herman Auerbach's problem on
factors of real polynomials with connected zero set complement", 2015 (see
the commentary in Mauldin (ed.), The Scottish Book, 2nd ed., 2015).
-/
theorem_wanted auerbachPolynomialZeroSetSeparatesIffFactorsSignDefinite :
    ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ), P ≠ 0 →
      IsConnected {x : Fin n → ℝ | (MvPolynomial.eval x) P ≠ 0} ↔
        ∀ Q : MvPolynomial (Fin n) ℝ, Irreducible Q → Q ∣ P →
          (∀ x : Fin n → ℝ, 0 ≤ (MvPolynomial.eval x) Q) ∨
            ∀ x : Fin n → ℝ, (MvPolynomial.eval x) Q ≤ 0

end MathlibExt.Algebra.Polynomial.ScottishBook148Wanted
