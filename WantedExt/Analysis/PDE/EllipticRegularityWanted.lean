/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.PDE.PoissonDirichlet

/-!
# Interior regularity of weak elliptic solutions

The interior `H²` estimate for divergence-form elliptic equations with `C¹` principal
coefficients. The weak formulation uses smooth compactly supported test functions.

## References

* P. Howard, *Second order elliptic PDE: interior H² regularity*, MATH 612 lecture slides, Texas
  A&M University, Spring 2020, https://people.tamu.edu/~phoward/m612/s20/elliptic7.pdf:
  Theorem 6.3.1 (interior `H²` regularity).
* The slides follow L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies
  in Mathematics 19 (2010), Chapter 6, and number results by the book's sections. The book is
  cited through the slides.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.EllipticRegularityWanted

open MeasureTheory
open scoped ContDiff ENNReal
open MathlibExt.Analysis.SobolevMorreyWanted.Analysis.SobolevMorreyProblem (E)

/-- **Interior `H²` regularity.** Let `U ⊆ ℝⁿ` be bounded and open, and let the coefficients
satisfy `aⁱʲ = aʲⁱ`, `aⁱʲ ∈ C¹(U)` and bounded on `U`, `bⁱ, c ∈ L^∞(U)`, and uniform ellipticity
`θ |ξ|² ≤ ∑ aⁱʲ(x) ξᵢ ξⱼ` on `U` with `θ > 0`. For every open `V` with `closure V` compact and
contained in `U` (`V ⊂⊂ U`) there is a constant `C` such that every weak solution `u ∈ H¹(U)` of
`L u = f` with `f ∈ L²(U)` has weak derivatives up to order two on `V` in `L²(V)`, and
`‖u‖_{L²(V)} + ∑ᵢ ‖∂ᵢ u‖_{L²(V)} + ∑ᵢⱼ ‖∂ⱼ ∂ᵢ u‖_{L²(V)} ≤ C (‖f‖_{L²(U)} + ‖u‖_{L²(U)})`.

This is Theorem 6.3.1 of P. Howard, MATH 612 slides *Interior H² regularity* (Texas A&M, 2020),
the interior `H²`-regularity theorem of §6.3.1 of Evans, *Partial Differential Equations*,
2nd ed. (cited through the slides). Here `C` is chosen before `u` and `f`, so it depends only on
`U`, `V` and the coefficients, as in the source. The left side is a norm equivalent to the
`H²(V)` norm, and `u ∈ H²_loc(U)` is the conclusion for all such `V`. Ellipticity is assumed at
every point of `U` rather than almost everywhere, which is equivalent for continuous
coefficients. -/
theorem_wanted interior_H2_regularity {n : ℕ} {U V : Set (E n)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (a : Fin n → Fin n → E n → ℝ) (b : Fin n → E n → ℝ)
    (c : E n → ℝ) (ha_symm : ∀ i j x, a i j x = a j i x)
    (ha_C1 : ∀ i j, ContDiffOn ℝ 1 (a i j) U) (ha_bdd : ∀ i j, ∃ M, ∀ x ∈ U, |a i j x| ≤ M)
    (hb : ∀ i, MemLp (b i) ∞ (volume.restrict U)) (hc : MemLp c ∞ (volume.restrict U))
    {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x ∈ U, ∀ ξ : Fin n → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, ∀ u f : E n → ℝ, MemLp f 2 (volume.restrict U) → IsWeakSolutionOn U a b c f u →
      ∃ Du : Fin n → E n → ℝ, ∃ D2u : Fin n → Fin n → E n → ℝ,
        (∀ i, MemLp (Du i) 2 (volume.restrict V) ∧ IsWeakPartialDerivOn V i u (Du i)) ∧
        (∀ i j, MemLp (D2u i j) 2 (volume.restrict V) ∧
          IsWeakPartialDerivOn V j (Du i) (D2u i j)) ∧
        eLpNorm u 2 (volume.restrict V) + ∑ i, eLpNorm (Du i) 2 (volume.restrict V) +
            ∑ i, ∑ j, eLpNorm (D2u i j) 2 (volume.restrict V) ≤
          ENNReal.ofReal C * (eLpNorm f 2 (volume.restrict U) + eLpNorm u 2 (volume.restrict U))

end MathlibExt.Analysis.PDE.EllipticRegularityWanted
