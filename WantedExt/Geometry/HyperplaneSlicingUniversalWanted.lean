/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Geometry.HyperplaneSlicingUniversalWanted

/-!
# Hyperplane slicing conjecture

Formalization of the hyperplane slicing conjecture collected from Oberwolfach Reports.

Source report: Mini-Workshop: Stochastic Analysis for Poisson Point Processes
(2013), Oberwolfach Reports, DOI 10.4171/owr/2013/09, pp. 483--520.
Stable identifier: [OWR-12337-001].

## Clause list

Every hypothesis, side condition, and quantifier domain in the source:

1. There exists a constant `c : ℝ` (one shared universal witness).
2. `0 < c`.
3. For every dimension `n : ℕ` (universal over `n`).
4. `1 ≤ n` (presupposed by "`(n-1)`-dimensional" hyperplane section).
5. For every `K : Set (EuclideanSpace ℝ (Fin n))` (that is, `K ⊆ ℝⁿ`).
6. `K` is convex (`Convex ℝ K`).
7. `K` is compact (`IsCompact K`).
8. `K` has nonempty interior (`Set.Nonempty (interior K)`).
9. `K` has `n`-dimensional Lebesgue volume `1` (`MeasureTheory.volume K = 1`).
10. There exists `H : Set (EuclideanSpace ℝ (Fin n))` (hyperplane).
11. `H` is a hyperplane (`∃ f t, f ≠ 0 ∧ H = {x | f x = t}` for a linear functional `f`).
12. The section is `K ∩ H`.
13. There exists an isometry `φ : EuclideanSpace ℝ (Fin (n - 1)) → EuclideanSpace ℝ (Fin n)`
    with `Isometry φ` and `Set.range φ = H`, identifying `H` with `ℝⁿ⁻¹`.
14. The `(n-1)`-dimensional volume of `K ∩ H`, measured as
    `MeasureTheory.volume (Set.preimage φ (K ∩ H))`, is at least `c`
    (`ENNReal.ofReal c ≤ ...`).
-/

/-- **Convex bodies in $\mathbb{R}^n$.** A set $K$ in the $n$-dimensional Euclidean space
$\mathbb{R}^n$ is a convex body when it is convex, compact and has nonempty interior.

Source: `OWR-12337-001` (DOI 10.4171/owr/2013/09): "convex body `K ⊆ ℝⁿ`". -/
def IsConvexBody (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ Set.Nonempty (interior K)

/-- **Hyperplanes in $\mathbb{R}^n$.** A set $H$ in the $n$-dimensional Euclidean space
$\mathbb{R}^n$ is a hyperplane when $H = \{x \in \mathbb{R}^n : f(x) = t\}$ for some nonzero
linear functional $f \colon \mathbb{R}^n \to \mathbb{R}$ and some $t \in \mathbb{R}$.

Source: `OWR-12337-001` (DOI 10.4171/owr/2013/09): "hyperplane section". -/
def IsHyperplane (n : ℕ) (H : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (f : LinearMap (RingHom.id ℝ) (EuclideanSpace ℝ (Fin n)) ℝ) (t : ℝ), f ≠ 0 ∧
    H = {x : EuclideanSpace ℝ (Fin n) | f x = t}

/-- **Hyperplane slicing conjecture.** The statement that there is a constant $c > 0$ such that
for every $n \ge 1$ and every convex body $K \subseteq \mathbb{R}^n$ (a convex compact set with
nonempty interior) of Lebesgue volume $1$ there exist a hyperplane $H \subseteq \mathbb{R}^n$ (a
set $\{x : f(x) = t\}$ for a nonzero linear functional $f$ on $\mathbb{R}^n$ and some
$t \in \mathbb{R}$) and an isometry $\varphi \colon \mathbb{R}^{n-1} \to \mathbb{R}^n$ with image
$H$ such that the $(n-1)$-dimensional Lebesgue volume of $\varphi^{-1}(K \cap H)$ is at least $c$.

Source: `OWR-12337-001` (DOI 10.4171/owr/2013/09), where it is posed as an open problem; it has
since been resolved. -/
def conjecture : Prop :=
  ∃ (c : ℝ), 0 < c ∧
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (K : Set (EuclideanSpace ℝ (Fin n))),
        IsConvexBody n K →
          MeasureTheory.volume K = 1 →
            ∃ (H : Set (EuclideanSpace ℝ (Fin n))),
              IsHyperplane n H ∧
                ∃ (φ : EuclideanSpace ℝ (Fin (n - 1)) → EuclideanSpace ℝ (Fin n)),
                  Isometry φ ∧ Set.range φ = H ∧
                    ENNReal.ofReal c ≤ MeasureTheory.volume (Set.preimage φ (K ∩ H))

/--
**Hyperplane slicing theorem.** There is a constant $c > 0$ such that for every $n \ge 1$ and
every convex body $K \subseteq \mathbb{R}^n$ (a convex compact set with nonempty interior) of
Lebesgue volume $1$ there exist a hyperplane $H \subseteq \mathbb{R}^n$ (a set
$\{x : f(x) = t\}$ for a nonzero linear functional $f$ on $\mathbb{R}^n$ and some
$t \in \mathbb{R}$) and an isometry $\varphi \colon \mathbb{R}^{n-1} \to \mathbb{R}^n$ with image
$H$ such that the $(n-1)$-dimensional Lebesgue volume of $\varphi^{-1}(K \cap H)$ is at least $c$.

This is Bourgain's slicing conjecture, proved by Klartag and Lehec building on Guan's bound
(Theorem 1.1); equivalently, the isotropic constant of convex bodies is bounded by a universal
constant.

Source: B. Klartag, J. Lehec, Affirmative resolution of Bourgain's slicing
problem using Guan's bound, Geometric and Functional Analysis (2025), arXiv:2412.15044,
https://arxiv.org/abs/2412.15044. Moved from
`OpenConjectures/Geometry/HyperplaneSlicingUniversal`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.HyperplaneSlicingUniversalWanted
