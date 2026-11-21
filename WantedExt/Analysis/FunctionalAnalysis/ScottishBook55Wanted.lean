/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55Wanted

/-- Mazur's Problem 55 from the Scottish Book, in the Banach-space
form: every continuous polynomial `W`, of arbitrary finite degree, that
is bounded on an `ε`-neighbourhood of an unbounded set `R` factors as
`W = V ∘ φ`, where `φ x = L x + a` is a continuous affine map into a
normed space `F` with `φ(R)` bounded, and `V` is a continuous
polynomial on `F`.

Continuous polynomials are encoded here, both for `W` on `E` and for
`V` on `F`, as finite sums of diagonals of continuous multilinear
maps, `W x = ∑ j, P j (fun _ => x)` and `V y = ∑ j, A j (fun _ => y)`,
the `j = 0` terms being the constant terms. Over `ℝ` every continuous
polynomial has this form, by polarization, and every such sum is a
continuous polynomial, so this is the usual notion, covering every
finite degree.

Both features of the factorisation are essential. With a scalar factor
(`F = ℝ`) the claim already fails in finite dimensions: on `ℝ³` with
`R` the first coordinate axis, `W x = x₂² + x₃²` is bounded near `R`
but no `V (L x + c)` equals it, since for `L ≠ 0` the function `W` is
unbounded on every level set of `L`, and for `L = 0` it would be
constant. And the inhomogeneous terms (`j = 0` and `j = 1` above)
matter because Pestov's counterexample is inhomogeneous. In finite
dimensions the answer with a general normed-space factor is positive
(Auerbach). -/
def ScottishBookProblem55Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : Set E) (n : ℕ)
    (P : (j : Fin (n + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => E) ℝ),
    (∀ M : ℝ, ∃ r ∈ R, M < ‖r‖) →
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x r < ε) → |∑ j, P j (fun _ => x)| ≤ C) →
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (L : E →L[ℝ] F) (a : F) (d : ℕ)
      (A : (j : Fin (d + 1)) →
        ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => F) ℝ),
      (∀ x : E, (∑ j, P j (fun _ => x)) = ∑ j, A j (fun _ => L x + a)) ∧
      ∃ M : ℝ, ∀ r ∈ R, ‖L r + a‖ ≤ M

/--
Mazur's Problem 55 is false in the Banach-space form above. It already
fails for continuous polynomials of degree at most two, which refutes
the claim for arbitrary finite degree. Pestov constructs a
scalar-valued inhomogeneous 2-polynomial `W` on `ℓ²` that is bounded on
an `ε`-neighbourhood of an unbounded set `R` but unbounded on
`(1 / 2) R`. A continuous affine map with bounded image on `R` also has
bounded image on `(1 / 2) R`, and a continuous polynomial is bounded on
bounded sets, so no factorisation `W = V ∘ φ` of the required form can
exist.

Source: S. Mazur, Problem 55 of the Scottish Book; V. Pestov, "Two 1935
questions of Mazur about polynomials in Banach spaces: a
counter-example" (1997), arXiv:funct-an/9705002, Sections 2-3. The same
counterexample refutes Problem 75. In finite dimensions the answer is
positive (Auerbach), with a normed-space-valued affine factor rather
than a single scalar coordinate, so the infinite-dimensional Banach
setting is essential.
-/
theorem_wanted mazur55_refuted : ¬ ScottishBookProblem55Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55Wanted
