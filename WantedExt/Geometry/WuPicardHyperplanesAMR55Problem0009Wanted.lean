/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Holomorphic maps of ℂⁿ omitting n + 2 hyperplanes of ℙⁿ (Chern, Problem IX; Wu's conjecture)

S.-S. Chern, Differential geometry; its past and its future (ICM 1970), Problem and Conjecture IX
(H. Wu): let `B` be the set of `n + 2` hyperplanes of `ℙⁿ(ℂ)` in general position (any `n + 1` of
them are the faces of a non-degenerate `n`-simplex). Then there is no non-degenerate holomorphic
mapping `ℂⁿ → ℙⁿ(ℂ) - B`. A holomorphic mapping is non-degenerate if its Jacobian matrix has maximum
rank at some point.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace MathlibExt.Geometry.WuPicardHyperplanesAMR55Problem0009Wanted

/-!
Source: S.-S. Chern, Differential geometry; its past and its future, Actes Congrès Intern. Math.
(Nice, 1970), Tome 1, 41-53, Problem and Conjecture IX, pp. 50-51. UnsolvedMath record UM-05600009
(`AMR-055-0009`), dataset ulamai/UnsolvedMath v1.8.0.

Maps `ℂⁿ → ℙⁿ(ℂ)` are written in homogeneous coordinates as entire maps `F : ℂⁿ → ℂⁿ⁺¹` (every
holomorphic map `ℂⁿ → ℙⁿ(ℂ)` has such a lift, since holomorphic line bundles on `ℂⁿ` are trivial);
omitting the hyperplane `H i = 0` means `H i ∘ F` has no zero, which also forces `F z ≠ 0`. The
Jacobian of the induced map has rank `n` at `z` exactly when `F z, ∂₁F(z), …, ∂ₙF(z)` are linearly
independent, so degeneracy is the vanishing of that determinant everywhere. General position: every
subfamily of `n+1` forms is linearly independent. `n ≥ 1`: `ℙ⁰` has no hyperplanes.
-/

/-- The `(n + 1) × (n + 1)` matrix whose columns are `F z, ∂₁F(z), …, ∂ₙF(z)` for a map
`F : ℂⁿ → ℂⁿ⁺¹`. When `F` is a holomorphic lift (homogeneous coordinates) of a map `f : ℂⁿ → ℙⁿ(ℂ)`
with `F z ≠ 0`, its determinant is nonzero exactly when the Jacobian of `f` has rank `n` at `z`
(in an affine chart where `F₀(z) ≠ 0` it equals `F₀(z)^{n+1}` times the Jacobian determinant). -/
noncomputable def liftJacobianMatrix {n : ℕ} (F : (Fin n → ℂ) → Fin (n + 1) → ℂ)
    (z : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i k =>
    (Fin.cons (F z) (fun j : Fin n => fderiv ℂ F z (Pi.single j 1)) : Fin (n + 1) → Fin (n + 1) → ℂ)
      k i

/-- Wu's conjecture (Chern, 1970, Problem IX): for `n ≥ 1` and `n + 2` hyperplanes of `ℙⁿ(ℂ)` in
general position (given by linear forms `H 0, …, H (n+1)` on `ℂⁿ⁺¹`, any `n + 1` of them linearly
independent), every holomorphic map `ℂⁿ → ℙⁿ(ℂ)` omitting the hyperplanes is degenerate: written
in homogeneous coordinates as an entire map `F : ℂⁿ → ℂⁿ⁺¹` with every `H i ∘ F` nowhere zero, its
Jacobian has rank less than `n` everywhere. -/
def noNondegenerateMapOmittingHyperplanes : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ H : Fin (n + 2) → Module.Dual ℂ (Fin (n + 1) → ℂ),
    (∀ s : Finset (Fin (n + 2)), s.card = n + 1 → LinearIndependent ℂ fun i : s => H i) →
    ∀ F : (Fin n → ℂ) → Fin (n + 1) → ℂ, Differentiable ℂ F →
      (∀ z i, H i (F z) ≠ 0) → ∀ z, (liftJacobianMatrix F z).det = 0

/--
Resolved true: an entire holomorphic map `ℂⁿ → ℙⁿ(ℂ)` omitting `n + 2` hyperplanes in general
position is degenerate (theorem of A. Bloch, reproved by M. Green; Griffiths derives it from the
Ahlfors lemma and the curvature of `ℙⁿ` minus the hyperplanes). Source: S.-S. Chern, Differential
geometry; its past and its future, Actes Congrès Intern. Math. (Nice, 1970), Tome 1, 41-53, Problem
and Conjecture IX, pp. 50-51; resolution: P. A. Griffiths, Entire Holomorphic Mappings in One and
Several Complex Variables, Annals of Mathematics Studies 85, Princeton University Press (1976),
Chapter 2, §(c), Corollary (2.23) (a compact complex manifold M with a simple normal crossings
divisor D, c1(K_M) + c1([D]) > 0: an entire holomorphic mapping C^n → M - D is necessarily
degenerate) and the paragraph after it, p. 56: 'Taking M = P^n and D to be a set of n+2 hyperplanes
A_j in general position, we find the theorem of A. Bloch, reproved independently by Mark Green, that
an entire holomorphic mapping f : C^n → P^n - {A_1 + ... + A_{n+2}} is degenerate. For n = 1 this is
the Picard theorem.',
https://press.princeton.edu/books/paperback/9780691081724/entire-holomorphic-mappings-in-one-and-several-complex-variables-am-85-volume-85.
-/
public theorem_wanted noNondegenerateMapOmittingHyperplanes_holds :
    noNondegenerateMapOmittingHyperplanes

end MathlibExt.Geometry.WuPicardHyperplanesAMR55Problem0009Wanted
