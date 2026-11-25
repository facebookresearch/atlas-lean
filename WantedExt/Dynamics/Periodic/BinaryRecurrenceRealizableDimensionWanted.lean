/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Finrank
@[expose] public section

namespace MetaMathlibExt

/-! # Binary recurrence realizable subspace
-/

/--
**Realizable span of a nondegenerate binary recurrence.** Let $B$ and $C$ be integers with
$C \neq 0$, and suppose the recurrence is nondegenerate: whenever $\alpha \neq \beta$ are
complex roots of $x^2 - Bx + C$, we have $(\alpha/\beta)^n \neq 1$ for every integer $n \geq 1$.
Put $\Delta = B^2 - 4C$. Let $R$ be the set of complex sequences $(u_n)_{n \geq 0}$ coming from
integer sequences $u$ that satisfy $u_{n+2} = B u_{n+1} - C u_n$ for all $n \geq 0$ and for
which there are a set $X$ and a map $T \colon X \to X$ such that, for every $n \geq 0$, the set
of points $x \in X$ with $T^{n+1}(x) = x$ is finite and has exactly $|u_n|$ elements. Then the
complex linear span of $R$ has dimension $0$ if $\Delta < 0$, dimension $1$ if $\Delta = 0$ or
$\Delta > 0$ is not the square of an integer, and dimension $2$ if $\Delta > 0$ is the square
of an integer.

Source: G. Everest, A. J. van der Poorten, Y. Puri, and T. Ward, "Integer
Sequences and Periodic Points," Journal of Integer Sequences 5 (2002),
Article 02.2.3, Theorem (label binaryrec), lines 243–254,
https://cs.uwaterloo.ca/journals/JIS/VOL5/Ward/ward2.tex
-/
public theorem_wanted binaryrec_realizable_subspace_dim (B C : ℤ) (hC : C ≠ 0)
    (hNondeg : ∀ α β : ℂ, α ^ 2 - (B : ℂ) * α + (C : ℂ) = 0 →
      β ^ 2 - (B : ℂ) * β + (C : ℂ) = 0 → α ≠ β →
      ∀ n : ℕ, 0 < n → (α / β) ^ n ≠ 1) :
    let Δ : ℤ := B ^ 2 - 4 * C;
    let R : Set (ℕ → ℂ) :=
      {w | ∃ u : ℕ → ℤ, (∀ n : ℕ, u (n + 2) = B * u (n + 1) - C * u n) ∧
        (∃ (X : Type) (T : X → X),
          ∀ n : ℕ, ∃ S : Set X, S = {x | T^[n + 1] x = x} ∧ S.Finite ∧
            S.ncard = (u n).natAbs) ∧
        w = fun n => (u n : ℂ)};
    (Δ < 0 → Module.finrank ℂ ↥(Submodule.span ℂ R) = 0) ∧
      ((Δ = 0 ∨ (0 < Δ ∧ ¬ IsSquare Δ)) →
        Module.finrank ℂ ↥(Submodule.span ℂ R) = 1) ∧
      ((0 < Δ ∧ IsSquare Δ) → Module.finrank ℂ ↥(Submodule.span ℂ R) = 2)

end MetaMathlibExt
