/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bézout's theorem (projective, with multiplicity)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.AlgebraicGeometry.Bezout` — bezout_projective_multiplicity (manifest `manifests/problems/bezout_projective_multiplicity.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.AlgebraicGeometry.BezoutWanted` namespace. Mathematical
statements are unchanged, except for one correction recorded as a Lean variant:
`intersectionMultiplicity` now takes `Module.length` over the local ring
`localRingAt q` (the ring of the quotient module), not over `K`. Source: É. Bézout, *Théorie générale des équations algébriques*, Paris, 1779. Modern projective formulation: see Eisenbud, *Commutative Algebra*, Chapter 12, or Hartshorne, *Algebraic Geometry*, Ch. I §7. Listed as §50 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.BezoutWanted
namespace AlgebraicGeometry

/-!
# Bézout's theorem (projective, with multiplicity)

For `n` homogeneous polynomials `f_1, …, f_n` of total degrees
`d_1, …, d_n ≥ 1` in `n + 1` variables over an algebraically closed
field with finite common projective zero set, the sum of intersection
multiplicities at the common zeros equals `∏ d_k`. §50 of Knill's
*Some Fundamental Theorems in Mathematics*.

The intersection multiplicity is constructed via the affine cone
(Eisenbud, *Commutative Algebra*, Ch. 12). For `p ∈ ℙⁿ` with rep
`v ≠ 0`, choose any index `i` with `v_i ≠ 0`, let
`q_j = v_j / v_i` (so `q_i = 1`), localise `K[X_0, …, X_n]` at the
maximal ideal of `q`, and take the `Module.length` over the local ring of the
quotient by `(f_1, …, f_n, X_i − 1)`. The `X_i − 1` factor cuts the
affine cone down to the transverse hyperplane slice.
-/

open scoped LinearAlgebra.Projectivization
open MvPolynomial

variable {K : Type*} [Field K]

/-- The projective space `ℙⁿ(K)`. -/
abbrev ProjSpace (K : Type*) [DivisionRing K] (n : ℕ) :=
  ℙ K (Fin (n + 1) → K)

/-- The projective vanishing set, defined by evaluating `f` on a chosen
representative `Projectivization.rep p`.

This is representative-independent only when `f` is homogeneous of
positive degree (`f(λv) = λᵈ f(v)`); the theorem below uses it only
under that hypothesis. -/
def vanishingSet {n : ℕ} (f : MvPolynomial (Fin (n + 1)) K) :
    Set (ProjSpace K n) :=
  {p | MvPolynomial.eval (Projectivization.rep p) f = 0}

/-- A chosen index `i : Fin (n+1)` with `p.rep i ≠ 0`. -/
noncomputable def chartIndex {n : ℕ} (p : ProjSpace K n) : Fin (n + 1) :=
  Classical.choose (Function.ne_iff.mp p.rep_nonzero)

lemma chartIndex_rep_ne_zero {n : ℕ} (p : ProjSpace K n) :
    Projectivization.rep p (chartIndex p) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp p.rep_nonzero)

/-- Affine cone coordinates of `p` on the chart `X_{chartIndex p} = 1`. -/
noncomputable def affineConeCoord {n : ℕ} (p : ProjSpace K n) :
    Fin (n + 1) → K :=
  fun j => Projectivization.rep p j / Projectivization.rep p (chartIndex p)

/-- Evaluation ring-hom `K[X_0, …, X_n] →+* K` sending `X_j ↦ q_j`. -/
noncomputable def evalAt {n : ℕ} (q : Fin (n + 1) → K) :
    MvPolynomial (Fin (n + 1)) K →+* K :=
  MvPolynomial.eval q

lemma evalAt_surjective {n : ℕ} (q : Fin (n + 1) → K) :
    Function.Surjective (evalAt q) := by
  intro k
  refine ⟨MvPolynomial.C k, ?_⟩
  simp [evalAt, MvPolynomial.eval_C]

/-- Maximal ideal of `K[X_0, …, X_n]` at the affine point `q`. -/
noncomputable def maxIdealAt {n : ℕ} (q : Fin (n + 1) → K) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker (evalAt q)

instance maxIdealAt_isMaximal {n : ℕ} (q : Fin (n + 1) → K) :
    (maxIdealAt q).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evalAt_surjective q)

instance maxIdealAt_isPrime {n : ℕ} (q : Fin (n + 1) → K) :
    (maxIdealAt q).IsPrime :=
  (maxIdealAt_isMaximal q).isPrime

/-- The local ring of `𝔸^{n+1}` at the affine point `q`. -/
noncomputable abbrev localRingAt {n : ℕ} (q : Fin (n + 1) → K) :=
  Localization.AtPrime (maxIdealAt q)

/-- Intersection multiplicity at a projective point of homogeneous
polynomials, via the affine-cone construction. `Module.length` over the local ring
returns `⊤` on non-proper / positive-dimensional components and a
natural number on a zero-dimensional intersection point. -/
noncomputable def intersectionMultiplicity {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (p : ProjSpace K n) : ℕ∞ :=
  let q := affineConeCoord p
  let i := chartIndex p
  let φ : MvPolynomial (Fin (n + 1)) K →+* localRingAt q := algebraMap _ _
  let I : Ideal (localRingAt q) :=
    Ideal.span ((Set.range fun k : Fin n => φ (f k)) ∪ {φ (X i - C 1)})
  Module.length (localRingAt q) (localRingAt q ⧸ I)

/- **Bézout's theorem (with multiplicity).** Given `n` homogeneous
polynomials `f_k` in `n + 1` variables, each of total degree exactly
`d_k ≥ 1`, over an algebraically closed field with finite common
projective zero set, the sum of intersection multiplicities equals
`∏ d_k`. The `totalDegree` hypothesis rules out the zero polynomial
(which is `IsHomogeneous d` for every `d` but has `totalDegree = 0`). -/
/-- Source: É. Bézout, *Théorie générale des équations algébriques*, Paris, 1779. Modern projective formulation: see Eisenbud, *Commutative Algebra*, Chapter 12, or Hartshorne, *Algebraic Geometry*, Ch. I §7. Listed as §50 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `bezout_projective_multiplicity`. -/
public theorem_wanted bezout_multiplicity [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ) (_hd : ∀ k, (f k).IsHomogeneous (d k))
    (_hdeg : ∀ k, (f k).totalDegree = d k)
    (_hd_pos : ∀ k, 1 ≤ d k)
    (_hfin : (⋂ k, vanishingSet (f k)).Finite) :
    ∑ᶠ p ∈ (⋂ k, vanishingSet (f k)), intersectionMultiplicity f p
      = (∏ k, d k : ℕ∞)

end AlgebraicGeometry

end MathlibExt.AlgebraicGeometry.BezoutWanted
