/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hibi's conjecture on symmetric h*-vectors (Oberwolfach Reports 39/2004, Conjecture 2)

Oberwolfach workshop Ehrhart Quasipolynomials (2004), C. A. Athanasiadis, On the unimodality of
h*-vectors, Conjecture 2 (due to Hibi): if `h*_i = h*_{d-i}` for all `0 ≤ i ≤ d`, then `h*(P)` is
unimodal.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.WeightedProjectiveSimplexIDPWanted

@[expose] public section

namespace MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted

/-!
Source: C. A. Athanasiadis, On the unimodality of h*-vectors, in Ehrhart Quasipolynomials: Algebra,
Combinatorics, and Geometry, Oberwolfach Reports 1 (2004), no. 39, p. 2078, Conjecture 2, DOI
10.4171/OWR/2004/39. UnsolvedMath record UM-30000109 (`OWR-741-003`), dataset ulamai/UnsolvedMath
v1.8.0.

A `d`-dimensional integral polytope is taken full-dimensional in `ℝ^d`, the convex hull of a finite
set of integer points with nonempty interior; every `d`-dimensional integral polytope is lattice
equivalent to one (and Mustaţă-Payne's polytope, a lattice polytope for the lattice `ℤ⁶ + ℤ f`,
becomes one in a basis of that lattice). The `h*`-polynomial is `MetaMathlibExt.IsHStarPolynomial`
(the source's identity `∑ i(P, r) t^r = h*(t) / (1 - t)^{d+1}`) and unimodality is
`MetaMathlibExt.IsUnimodal`, both reused from
`WantedExt.Combinatorics.WeightedProjectiveSimplexIDPWanted`. Conjecture 1 of the same abstract
(standard Gorenstein `R_P` implies unimodal `h*`) is already stated as
`conjectureGorensteinIDPUnimodal` in the OpenConjectures entry `IntegerDecompositionUnimodalHStar`.
-/

open MetaMathlibExt

/-- The lattice polytope in `ℝ^d` spanned by the finite set `S ⊆ ℤ^d` of integer points. -/
def latticePolytope {d : ℕ} (S : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  convexHull ℝ ((fun v : Fin d → ℤ => fun i => (v i : ℝ)) '' (S : Set (Fin d → ℤ)))

/-- Hibi's conjecture (Conjecture 2 of C. A. Athanasiadis, Oberwolfach Report 39/2004, p. 2078): if
a `d`-dimensional integral polytope `P` has `h*_i = h*_{d-i}` for all `0 ≤ i ≤ d`, then its
`h*`-vector `(h*_0, …, h*_d)` is unimodal. Stated for full-dimensional lattice polytopes in `ℝ^d`
(every `d`-dimensional integral polytope is lattice-equivalent to one); `h*` is the polynomial `h`
with `∑_t #(tP ∩ ℤ^d) X^t · (1 - X)^{d+1} = h` (`MetaMathlibExt.IsHStarPolynomial`). -/
def hibiSymmetricUnimodal : Prop :=
  ∀ (d : ℕ) (S : Finset (Fin d → ℤ)), (interior (latticePolytope S)).Nonempty →
    ∀ h : Polynomial ℤ, IsHStarPolynomial (latticePolytope S) h →
      (∀ i ≤ d, h.coeff i = h.coeff (d - i)) → IsUnimodal h

/--
Resolved false: Mustaţă and Payne (Example 1.1) give a reflexive `6`-dimensional lattice polytope
with `h*`-vector `(1, 6, 8, 6, 8, 6, 1)`, which satisfies `h*_i = h*_{6-i}` and is not unimodal.
Source: C. A. Athanasiadis, On the unimodality of h*-vectors, in Ehrhart Quasipolynomials: Algebra,
Combinatorics, and Geometry, Oberwolfach Reports 1 (2004), no. 39, p. 2078, Conjecture 2, DOI
10.4171/OWR/2004/39; resolution: M. Mustaţă and S. Payne, Ehrhart polynomials and stringy Betti
numbers, Math. Ann. 333 (2005), 787-795, DOI 10.1007/s00208-005-0691-x, arXiv:math/0504486, Example
1.1: for f = (e1 + ... + e6)/3, N = ℤ⁶ + ℤ f and P the polytope with vertices e1, ..., e6, e1 - f,
..., e6 - f, P is reflexive with δ_P = (1, 6, 8, 6, 8, 6, 1), a counterexample to Hibi's conjecture
for d = 6 (abstract: 'counterexamples to Hibi's conjecture on the unimodality of delta-vectors of
reflexive polytopes'), https://arxiv.org/abs/math/0504486.
-/
public theorem_wanted hibiSymmetricUnimodal_refuted : ¬ hibiSymmetricUnimodal

end MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted
