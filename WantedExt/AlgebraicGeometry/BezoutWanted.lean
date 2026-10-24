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

/-- **Projective space.** For a division ring $K$ and $n \in \mathbb{N}$, the projective space
$\mathbb{P}^n(K)$ is the projectivization of $K^{n+1}$: the set of nonzero vectors of $K^{n+1}$
modulo multiplication by nonzero scalars, equivalently the lines through the origin. -/
abbrev ProjSpace (K : Type*) [DivisionRing K] (n : ℕ) :=
  ℙ K (Fin (n + 1) → K)

/-- **Projective vanishing set.** For a field $K$ and a polynomial $f \in K[X_0, \dots, X_n]$, the
vanishing set of $f$ is the set of points $p \in \mathbb{P}^n(K)$ such that $f(v) = 0$, where
$v \in K^{n+1} \setminus \{0\}$ is the chosen representative of $p$.

When $f$ is homogeneous of degree $d$, $f(\lambda v) = \lambda^d f(v)$, so this set does not depend
on the choice of representatives. -/
def vanishingSet {n : ℕ} (f : MvPolynomial (Fin (n + 1)) K) :
    Set (ProjSpace K n) :=
  {p | MvPolynomial.eval (Projectivization.rep p) f = 0}

/-- **Chart index of a projective point.** For a field $K$ and a point $p \in \mathbb{P}^n(K)$
with chosen representative $v = (v_0, \dots, v_n) \in K^{n+1} \setminus \{0\}$, the chart index of
$p$ is a fixed choice of an index $i \in \{0, \dots, n\}$ with $v_i \neq 0$. -/
noncomputable def chartIndex {n : ℕ} (p : ProjSpace K n) : Fin (n + 1) :=
  Classical.choose (Function.ne_iff.mp p.rep_nonzero)

lemma chartIndex_rep_ne_zero {n : ℕ} (p : ProjSpace K n) :
    Projectivization.rep p (chartIndex p) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp p.rep_nonzero)

/-- **Affine coordinates of a projective point.** For a field $K$ and a point
$p \in \mathbb{P}^n(K)$, let $v = (v_0, \dots, v_n) \in K^{n+1} \setminus \{0\}$ be the chosen
representative of $p$ and $i$ its chart index (a chosen index with $v_i \neq 0$). The affine cone
coordinates of $p$ are the vector $q \in K^{n+1}$ with $q_j = v_j / v_i$ for every $j$; in
particular $q_i = 1$. -/
noncomputable def affineConeCoord {n : ℕ} (p : ProjSpace K n) :
    Fin (n + 1) → K :=
  fun j => Projectivization.rep p j / Projectivization.rep p (chartIndex p)

/-- **Evaluation at an affine point.** For a field $K$ and a point
$q = (q_0, \dots, q_n) \in K^{n+1}$, this is the ring homomorphism $K[X_0, \dots, X_n] \to K$
sending each polynomial $g$ to its value $g(q)$; it fixes $K$ and sends $X_j$ to $q_j$. -/
noncomputable def evalAt {n : ℕ} (q : Fin (n + 1) → K) :
    MvPolynomial (Fin (n + 1)) K →+* K :=
  MvPolynomial.eval q

lemma evalAt_surjective {n : ℕ} (q : Fin (n + 1) → K) :
    Function.Surjective (evalAt q) := by
  intro k
  refine ⟨MvPolynomial.C k, ?_⟩
  simp [evalAt, MvPolynomial.eval_C]

/-- **Maximal ideal of an affine point.** For a field $K$ and a point $q \in K^{n+1}$, this is the
ideal of $K[X_0, \dots, X_n]$ consisting of the polynomials $g$ with $g(q) = 0$, that is, the
kernel of evaluation at $q$.

It is a maximal ideal, since evaluation at $q$ is surjective onto $K$. -/
noncomputable def maxIdealAt {n : ℕ} (q : Fin (n + 1) → K) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker (evalAt q)

instance maxIdealAt_isMaximal {n : ℕ} (q : Fin (n + 1) → K) :
    (maxIdealAt q).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evalAt_surjective q)

instance maxIdealAt_isPrime {n : ℕ} (q : Fin (n + 1) → K) :
    (maxIdealAt q).IsPrime :=
  (maxIdealAt_isMaximal q).isPrime

/-- **Local ring of affine space at a point.** For a field $K$ and a point $q \in K^{n+1}$, this is
the localization of $K[X_0, \dots, X_n]$ at the maximal ideal of $q$ (the ideal of polynomials
vanishing at $q$), that is, the local ring of affine space $\mathbb{A}^{n+1}$ at $q$. -/
noncomputable abbrev localRingAt {n : ℕ} (q : Fin (n + 1) → K) :=
  Localization.AtPrime (maxIdealAt q)

/-- **Intersection multiplicity at a projective point.** Let $K$ be a field and
$f_1, \dots, f_n \in K[X_0, \dots, X_n]$. For a point $p \in \mathbb{P}^n(K)$, let $i$ be its chart
index, $q \in K^{n+1}$ its affine cone coordinates (so $q_i = 1$), and $\mathcal{O}_q$ the
localization of $K[X_0, \dots, X_n]$ at the maximal ideal of $q$. The intersection multiplicity
of $f_1, \dots, f_n$ at $p$ is the length, as an $\mathcal{O}_q$-module, of the quotient of
$\mathcal{O}_q$ by the ideal generated by $f_1, \dots, f_n$ and $X_i - 1$; it is an element of
$\mathbb{N} \cup \{\infty\}$.

The value is $\infty$ exactly when this quotient does not have finite length, for example along
a positive-dimensional component of the common zero set. -/
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
/-- **Bézout's theorem (with multiplicity).** Let $K$ be an algebraically closed field, let
$n \in \mathbb{N}$, and let $f_1, \dots, f_n \in K[X_0, \dots, X_n]$ and integers
$d_1, \dots, d_n \ge 1$ be such that each $f_k$ is homogeneous of degree $d_k$ and has total
degree exactly $d_k$. Suppose the common projective zero set
$Z = V(f_1) \cap \dots \cap V(f_n) \subseteq \mathbb{P}^n(K)$ is finite. Then
$\sum_{p \in Z} i_p(f_1, \dots, f_n) = d_1 d_2 \cdots d_n$ in $\mathbb{N} \cup \{\infty\}$,
where $i_p(f_1, \dots, f_n)$ is the intersection multiplicity of $f_1, \dots, f_n$ at $p$.

The total degree hypothesis rules out $f_k = 0$, which is homogeneous of every degree but has
total degree $0$.

Source: É. Bézout, *Théorie générale des équations algébriques*, Paris, 1779. Modern projective formulation: see Eisenbud, *Commutative Algebra*, Chapter 12, or Hartshorne, *Algebraic Geometry*, Ch. I §7. Listed as §50 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `bezout_projective_multiplicity`. -/
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
