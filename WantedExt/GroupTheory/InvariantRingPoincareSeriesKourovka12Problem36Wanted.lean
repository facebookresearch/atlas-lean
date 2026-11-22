/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Poincaré series of modular invariant rings (Kourovka Notebook Problem 12.36)

Kourovka Notebook, Archive of Solved Problems, Problem 12.36 (D. Carlisle, P. H. Kropholler): for `G
≤ GL(V)`, `V` an `n`-dimensional space over `𝔽ₚ`, the Poincaré series `∑ₘ bₘ tᵐ` of `T = S(V*)^G`
has a Laurent expansion `∑_{i ≥ -n} aᵢ (1 - t)ⁱ` about `t = 1` with `a_{-n} = 1/|G|`. Conjecture:
`a_{-n+1} = r/(2|G|)`, where `r = ∑_W ((p - 1) α_W + s_W - 1)` over the maximal subspaces `W` of
`V`, `|G_W| = p^{α_W} s_W` with `p ∤ s_W`, and `G_W` is the pointwise stabilizer of `W`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.InvariantRingPoincareSeriesKourovka12Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.36 (D.
Carlisle, P. H. Kropholler). UnsolvedMath record UM-00700855 (`KOU-12.36`), dataset
ulamai/UnsolvedMath v1.8.0.

`V = 𝔽ₚⁿ` with `G` acting on column vectors, `S(V*) = 𝔽ₚ[x₀, …, x_{n-1}]` (coordinate functions),
and `T` consists of the polynomials `f` with `f(g x) = f(x)` (formal linear substitution) for all `g
∈ G`; `bₘ = dim Tₘ`. The Laurent expansion is encoded by polynomials `A, B ∈ ℚ[t]` with `B(1) ≠ 0`
and `B (1 - t)ⁿ P = A` in `ℚ⟦t⟧`. For every `G` such `A, B` exist: `P` is rational (Hilbert-Serre)
and, as the problem states, `(1 - t)ⁿ P` has no pole at `t = 1`. Any two such pairs `(A, B)`, `(A₂,
B₂)` satisfy `A B₂ = A₂ B` (multiply `B (1 - t)ⁿ P = A` by `B₂`), so the rational function `A/B = (1
- t)ⁿ P = ∑ᵢ aᵢ₋ₙ (1 - t)ⁱ` is determined by `G` and the stated value is `a_{-n+1} = -(A/B)'(1)` for
every choice. Maximal subspaces are the coatoms of the subspace lattice (for `n = 0` there are none,
`r = 0`, and both sides vanish). For `n = 1` and `|G| = d` the statement reads `(d - 1)/(2d) = (d -
1)/(2d)`.
-/

open MvPolynomial

/-- Precomposition of polynomial functions on `V = 𝔽ₚⁿ` with the matrix `g`: the linear
substitution `xᵢ ↦ ∑ⱼ gᵢⱼ xⱼ` of `S(V*) = 𝔽ₚ[x₀, …, x_{n-1}]`. -/
noncomputable def linSubst {p n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) :
    MvPolynomial (Fin n) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin n) (ZMod p) :=
  aeval fun i => ∑ j, C (g i j) * X j

/-- The homogeneous component of degree `m` of the invariant ring `T = S(V*)^G`. -/
noncomputable def invariantComponent {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p))) (m : ℕ) :
    Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)) :=
  homogeneousSubmodule (Fin n) (ZMod p) m ⊓
    ⨅ g ∈ G, LinearMap.ker
      ((linSubst (g : Matrix (Fin n) (Fin n) (ZMod p))).toLinearMap - LinearMap.id)

/-- The Poincaré series `∑ₘ bₘ tᵐ` of `T`, with `bₘ = dim Tₘ`. -/
noncomputable def poincareSeries {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p))) :
    PowerSeries ℚ :=
  PowerSeries.mk fun m => (Module.finrank (ZMod p) (invariantComponent G m) : ℚ)

/-- The pointwise stabilizer `G_W` of a subspace `W ≤ V` in `G`. -/
def pointwiseStabilizer {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p)))
    (W : Submodule (ZMod p) (Fin n → ZMod p)) : Set (GL (Fin n) (ZMod p)) :=
  {g | g ∈ G ∧ ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) (ZMod p)).mulVec w = w}

/-- The term `(p - 1) α_W + s_W - 1` of `r`, where `|G_W| = p^{α_W} s_W` with `p ∤ s_W`. -/
noncomputable def hyperplaneTerm {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p)))
    (W : Submodule (ZMod p) (Fin n → ZMod p)) : ℚ :=
  let N := Nat.card (pointwiseStabilizer G W)
  (((p - 1) * N.factorization p : ℕ) : ℚ) + ((N / p ^ N.factorization p : ℕ) : ℚ) - 1

/-- `r = ∑_W ((p - 1) α_W + s_W - 1)`, the sum over the maximal subspaces `W` of `V`. -/
noncomputable def hyperplaneSum {p n : ℕ} (G : Subgroup (GL (Fin n) (ZMod p))) : ℚ :=
  ∑ᶠ (W : Submodule (ZMod p) (Fin n → ZMod p)) (_ : IsCoatom W), hyperplaneTerm G W

/-- Kourovka 12.36 (D. Carlisle, P. H. Kropholler): for `G ≤ GL(V)`, `V = 𝔽ₚⁿ`, the Laurent
expansion `∑_{i ≥ -n} aᵢ (1 - t)ⁱ` of the Poincaré series of `S(V*)^G` at `t = 1` has
`a_{-n+1} = r / (2 |G|)`. The expansion is encoded by polynomials `A`, `B` with `B(1) ≠ 0` and
`B (1 - t)ⁿ P(t) = A`: then `(1 - t)ⁿ P = A / B = a_{-n} + a_{-n+1} (1 - t) + ⋯`, so
`a_{-n+1} = -(A / B)'(1) = (A(1) B'(1) - A'(1) B(1)) / B(1)²`. -/
def poincareSeriesSecondCoefficient : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (n : ℕ) (G : Subgroup (GL (Fin n) (ZMod p))),
    ∃ A B : Polynomial ℚ, B.eval 1 ≠ 0 ∧
      ((B * (1 - Polynomial.X) ^ n : Polynomial ℚ) : PowerSeries ℚ) * poincareSeries G =
        (A : PowerSeries ℚ) ∧
      (A.eval 1 * (Polynomial.derivative B).eval 1 - (Polynomial.derivative A).eval 1 * B.eval 1) /
          B.eval 1 ^ 2 = hyperplaneSum G / (2 * Nat.card G)

/--
Resolved true: the Kourovka Archive records the conjecture as proved by Benson and Crawley-Boevey
(Bull. London Math. Soc. 27 (1995)), with a second proof by Neeman (Comment. Math. Helv. 70 (1995))
based on the Grothendieck-Riemann-Roch theorem. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 12.36 (D. Carlisle, P. H. Kropholler); resolution: D. J. Benson
and W. W. Crawley-Boevey, Bull. London Math. Soc. 27 (1995), no. 5, 435-440; A. Neeman, Comment.
Math. Helv. 70 (1995), no. 3, 339-349, Kourovka Archive, Problem 12.36: the conjecture is proved.
-/
public theorem_wanted poincareSeriesSecondCoefficient_holds : poincareSeriesSecondCoefficient

end MathlibExt.GroupTheory.InvariantRingPoincareSeriesKourovka12Problem36Wanted
