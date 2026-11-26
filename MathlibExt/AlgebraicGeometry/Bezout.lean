/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/AlgebraicGeometry/Bezout.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), module `LeanEval.AlgebraicGeometry.Bezout`, problem
`bezout_projective_multiplicity`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/bezout_projective_multiplicity.toml`, rev 1, submitter Kim Morrison, status
archived): the definitions `ProjSpace`, `vanishingSet`, `chartIndex`, `affineConeCoord`, `evalAt`,
`maxIdealAt`, `localRingAt` and `intersectionMultiplicity`, the lemmas `chartIndex_rep_ne_zero`
and `evalAt_surjective`, the instances `maxIdealAt_isMaximal` and `maxIdealAt_isPrime`, and the
statement of `bezout_multiplicity`, with the docstrings and comments they had in the former wanted
module `WantedExt/AlgebraicGeometry/BezoutWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.AlgebraicGeometry.BezoutWanted` namespace. Mathematical statements are unchanged,
except for one correction recorded as a Lean variant: `intersectionMultiplicity` now takes
`Module.length` over the local ring `localRingAt q` (the ring of the quotient module), not over
`K`. Later changes (ATLAS, 2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/AlgebraicGeometry/BezoutWanted.lean` to this `MathlibExt` module with unchanged names,
statements and docstrings, and the imports were replaced by the Mathlib and `MathlibExt` imports
the proof needs. The proof of `chartIndex_rep_ne_zero` now cites `Projectivization.rep_ne_zero`
instead of its deprecated alias `Projectivization.rep_nonzero`.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`bezout_multiplicity`, the private lemmas it uses and the module documentation.

Source: É. Bézout, *Théorie générale des équations algébriques*, Paris, 1779. Modern projective
formulation: see Eisenbud, *Commutative Algebra*, Chapter 12, or Hartshorne, *Algebraic Geometry*,
Ch. I §7. Listed as §50 in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import MathlibExt.RingTheory.Depth.CohenMacaulaySystemOfParameters

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

## Main results

* `bezout_multiplicity`: Bézout's theorem with multiplicity. If `f_1, …, f_n` are homogeneous of
  degrees `d_k ≥ 1` in `n + 1` variables over an algebraically closed field and have finitely many
  common zeros in `ℙⁿ`, then their intersection multiplicities at these zeros sum to `∏ d_k`.

## Proof outline

Write `S = K[X_0, …, X_n]` and `J = (f_1, …, f_n)`.

* The field `K` is infinite and the common zero set `Z` is finite, so some linear form `ℓ`
  vanishes at no point of `Z`. Then `0` is the only common zero of `f_1, …, f_n, ℓ` in `K^{n+1}`.
* The localization of `S` at the ideal of the origin is a Cohen–Macaulay local ring of dimension
  `n + 1`: the variables form a regular sequence in it. By the Nullstellensatz,
  `f_1, …, f_n, ℓ` is a system of parameters there, hence a regular sequence
  (`IsLocalRing.isRegular_of_systemOfParameters`). These polynomials are homogeneous, so they form
  a regular sequence in `S` as well.
* If `g` is homogeneous of degree `e` and a nonzerodivisor modulo a homogeneous ideal `I`, the
  Hilbert functions satisfy `h_{I + (g)}(m) = h_I(m) - h_I(m - e)`. So the Hilbert series of
  `S ⧸ J` is `∏ (1 - t ^ d_k) / (1 - t) ^ (n + 1)`, and the Hilbert function of `S ⧸ J` is
  `∏ d_k` in all large degrees.
* Since `ℓ` is a nonzerodivisor modulo `J`, the degree-`m` part of `S ⧸ J` maps isomorphically
  onto `A = S ⧸ (J + (ℓ - 1))` for every large `m`, so `A` has dimension `∏ d_k` over `K`.
* The finite-dimensional algebra `A` is Artinian, so its dimension is the sum of the dimensions of
  its localizations at its primes (`IsArtinianRing.finrank_eq_sum_primeSpectrum`). By the
  Nullstellensatz these primes correspond to the points of `Z`, through the representatives `v`
  with `ℓ(v) = 1`.
* At a point with chart index `i`, the substitutions `X_j ↦ X_j / ℓ` and `X_j ↦ X_j / X_i`
  identify the localization of `A` at that point with the local ring whose length defines the
  intersection multiplicity. The residue field of this local ring is `K`, so its length equals its
  dimension over `K`.
-/

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.BezoutWanted
namespace AlgebraicGeometry

open scoped LinearAlgebra.Projectivization
open MvPolynomial

variable {K : Type*} [Field K]

set_option linter.dupNamespace false in
/-- **Projective space.** For a division ring $K$ and $n \in \mathbb{N}$, the projective space
$\mathbb{P}^n(K)$ is the projectivization of $K^{n+1}$: the set of nonzero vectors of $K^{n+1}$
modulo multiplication by nonzero scalars, equivalently the lines through the origin. -/
abbrev ProjSpace (K : Type*) [DivisionRing K] (n : ℕ) :=
  ℙ K (Fin (n + 1) → K)

set_option linter.dupNamespace false in
/-- **Projective vanishing set.** For a field $K$ and a polynomial $f \in K[X_0, \dots, X_n]$, the
vanishing set of $f$ is the set of points $p \in \mathbb{P}^n(K)$ such that $f(v) = 0$, where
$v \in K^{n+1} \setminus \{0\}$ is the chosen representative of $p$.

When $f$ is homogeneous of degree $d$, $f(\lambda v) = \lambda^d f(v)$, so this set does not depend
on the choice of representatives. -/
def vanishingSet {n : ℕ} (f : MvPolynomial (Fin (n + 1)) K) :
    Set (ProjSpace K n) :=
  {p | MvPolynomial.eval (Projectivization.rep p) f = 0}

set_option linter.dupNamespace false in
/-- **Chart index of a projective point.** For a field $K$ and a point $p \in \mathbb{P}^n(K)$
with chosen representative $v = (v_0, \dots, v_n) \in K^{n+1} \setminus \{0\}$, the chart index of
$p$ is a fixed choice of an index $i \in \{0, \dots, n\}$ with $v_i \neq 0$. -/
noncomputable def chartIndex {n : ℕ} (p : ProjSpace K n) : Fin (n + 1) :=
  Classical.choose (Function.ne_iff.mp p.rep_nonzero)

set_option linter.dupNamespace false in
lemma chartIndex_rep_ne_zero {n : ℕ} (p : ProjSpace K n) :
    Projectivization.rep p (chartIndex p) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp p.rep_ne_zero)

set_option linter.dupNamespace false in
/-- **Affine coordinates of a projective point.** For a field $K$ and a point
$p \in \mathbb{P}^n(K)$, let $v = (v_0, \dots, v_n) \in K^{n+1} \setminus \{0\}$ be the chosen
representative of $p$ and $i$ its chart index (a chosen index with $v_i \neq 0$). The affine cone
coordinates of $p$ are the vector $q \in K^{n+1}$ with $q_j = v_j / v_i$ for every $j$; in
particular $q_i = 1$. -/
noncomputable def affineConeCoord {n : ℕ} (p : ProjSpace K n) :
    Fin (n + 1) → K :=
  fun j => Projectivization.rep p j / Projectivization.rep p (chartIndex p)

set_option linter.dupNamespace false in
/-- **Evaluation at an affine point.** For a field $K$ and a point
$q = (q_0, \dots, q_n) \in K^{n+1}$, this is the ring homomorphism $K[X_0, \dots, X_n] \to K$
sending each polynomial $g$ to its value $g(q)$; it fixes $K$ and sends $X_j$ to $q_j$. -/
noncomputable def evalAt {n : ℕ} (q : Fin (n + 1) → K) :
    MvPolynomial (Fin (n + 1)) K →+* K :=
  MvPolynomial.eval q

set_option linter.dupNamespace false in
lemma evalAt_surjective {n : ℕ} (q : Fin (n + 1) → K) :
    Function.Surjective (evalAt q) := by
  intro k
  refine ⟨MvPolynomial.C k, ?_⟩
  simp [evalAt, MvPolynomial.eval_C]

set_option linter.dupNamespace false in
/-- **Maximal ideal of an affine point.** For a field $K$ and a point $q \in K^{n+1}$, this is the
ideal of $K[X_0, \dots, X_n]$ consisting of the polynomials $g$ with $g(q) = 0$, that is, the
kernel of evaluation at $q$.

It is a maximal ideal, since evaluation at $q$ is surjective onto $K$. -/
noncomputable def maxIdealAt {n : ℕ} (q : Fin (n + 1) → K) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker (evalAt q)

set_option linter.dupNamespace false in
instance maxIdealAt_isMaximal {n : ℕ} (q : Fin (n + 1) → K) :
    (maxIdealAt q).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evalAt_surjective q)

set_option linter.dupNamespace false in
instance maxIdealAt_isPrime {n : ℕ} (q : Fin (n + 1) → K) :
    (maxIdealAt q).IsPrime :=
  (maxIdealAt_isMaximal q).isPrime

set_option linter.dupNamespace false in
/-- **Local ring of affine space at a point.** For a field $K$ and a point $q \in K^{n+1}$, this is
the localization of $K[X_0, \dots, X_n]$ at the maximal ideal of $q$ (the ideal of polynomials
vanishing at $q$), that is, the local ring of affine space $\mathbb{A}^{n+1}$ at $q$. -/
noncomputable abbrev localRingAt {n : ℕ} (q : Fin (n + 1) → K) :=
  Localization.AtPrime (maxIdealAt q)

set_option linter.dupNamespace false in
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

/-!
### The dimension of an affine complete intersection via Hilbert functions

Let `S = K[X₀, …, Xₙ]`, let `f₁, …, fₙ` be homogeneous polynomials of degrees `d₁, …, dₙ` forming
a regular sequence, and let `ℓ` be a linear form which is a nonzerodivisor modulo
`J = (f₁, …, fₙ)`. Then `S ⧸ (J + (ℓ - 1))` is a finite-dimensional `K`-vector space of dimension
`d₁ ⋯ dₙ` (`BezoutHilbert.finrank_quotient_eq_prod`).

#### Proof outline

* For an ideal `I` let `hilbFn I m` be the codimension of the degree `m` part of `I` in the space of
  homogeneous polynomials of degree `m`, and `hilbSeries I` its generating series. If `I` is
  homogeneous and `g` is homogeneous of degree `e` and a nonzerodivisor modulo `I`, then
  `hilbSeries (I ⊔ span {g}) = (1 - X ^ e) * hilbSeries I`. Since
  `hilbSeries ⊥ * (1 - X) ^ (n + 1) = 1`, we get
  `(1 - X) * hilbSeries J = ∏ k, (1 + X + ⋯ + X ^ (d k - 1))`, so that `hilbFn J m = ∏ k, d k`
  for all large `m`.
* A homogeneous polynomial lying in `J + (ℓ - 1)` already lies in `J`: homogenizing with respect
  to `ℓ` kills multiples of `ℓ - 1`. Hence the image `degImage J ℓ m` of the degree `m`
  polynomials in `S ⧸ (J + (ℓ - 1))` has dimension `hilbFn J m`. These images increase with `m`
  (multiplication by `ℓ`) and exhaust the quotient, so they stabilize to the whole quotient.
-/

namespace BezoutHilbert

attribute [local instance] MvPolynomial.gradedAlgebra

section Graded

variable {σ : Type*}

private theorem isHomogeneous_span (s : Set (MvPolynomial σ K))
    (hs : ∀ p ∈ s, ∃ e, p.IsHomogeneous e) :
    (Ideal.span s).IsHomogeneous (homogeneousSubmodule σ K) :=
  Ideal.homogeneous_span _ s hs

private theorem decompose_eq (p : MvPolynomial σ K) (i : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ K) p i : MvPolynomial σ K) =
      homogeneousComponent i p :=
  decomposition.decompose'_apply p i

private theorem homogeneousComponent_mul_of_le {g : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (h : e ≤ m) (p : MvPolynomial σ K) :
    homogeneousComponent m (g * p) = g * homogeneousComponent (m - e) p := by
  have := DirectSum.coe_decompose_mul_of_left_mem_of_le (homogeneousSubmodule σ K) (b := p) hg h
  rwa [decompose_eq, decompose_eq] at this

private theorem homogeneousComponent_mul_of_lt {g : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (h : m < e) (p : MvPolynomial σ K) :
    homogeneousComponent m (g * p) = 0 := by
  have := DirectSum.coe_decompose_mul_of_left_mem_of_not_le (homogeneousSubmodule σ K) (b := p)
    (n := m) hg (not_le.mpr h)
  rwa [decompose_eq] at this

private theorem mul_mem_homogeneousSubmodule {g y : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (hem : e ≤ m) (hy : y ∈ homogeneousSubmodule σ K (m - e)) :
    g * y ∈ homogeneousSubmodule σ K m := by
  have := hg.mul hy
  rwa [Nat.add_sub_cancel' hem] at this

end Graded

section HilbertFunction

variable {σ : Type*}

private instance finiteDimensional_homogeneousSubmodule [Finite σ] (m : ℕ) :
    FiniteDimensional K (homogeneousSubmodule σ K m) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K m)

/-- The degree `m` part of an ideal, as a `K`-subspace of the polynomial ring. -/
private noncomputable def degPart (I : Ideal (MvPolynomial σ K)) (m : ℕ) :
    Submodule K (MvPolynomial σ K) :=
  I.restrictScalars K ⊓ homogeneousSubmodule σ K m

private instance finiteDimensional_degPart [Finite σ] (I : Ideal (MvPolynomial σ K)) (m : ℕ) :
    FiniteDimensional K (degPart I m) :=
  Submodule.finiteDimensional_of_le inf_le_right

/-- The Hilbert function of `S ⧸ I` in degree `m`, as an integer. -/
private noncomputable def hilbFn (I : Ideal (MvPolynomial σ K)) (m : ℕ) : ℤ :=
  Module.finrank K (homogeneousSubmodule σ K m) - Module.finrank K (degPart I m)

private theorem degPart_sup_of_le {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) {g : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (hem : e ≤ m) :
    degPart (I ⊔ Ideal.span {g}) m =
      degPart I m ⊔ (homogeneousSubmodule σ K (m - e)).map (LinearMap.mulLeft K g) := by
  apply le_antisymm
  · rintro x ⟨hxI, hxm⟩
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.mp hxI
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hx : i + a * g = homogeneousComponent m i + g * homogeneousComponent (m - e) a := by
      conv_lhs => rw [← homogeneousComponent_eq_self hxm]
      rw [map_add, mul_comm a g, homogeneousComponent_mul_of_le hg hem]
    rw [hx]
    exact Submodule.add_mem_sup ⟨homogeneousComponent_mem_of_mem hI hi m,
      homogeneousComponent_mem m i⟩ ⟨_, homogeneousComponent_mem _ a, rfl⟩
  · refine sup_le (inf_le_inf_right _ fun x hx => Ideal.mem_sup_left hx) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)),
      mul_mem_homogeneousSubmodule hg hem hy⟩

private theorem degPart_sup_of_lt {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) {g : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (hem : m < e) :
    degPart (I ⊔ Ideal.span {g}) m = degPart I m := by
  apply le_antisymm
  · rintro x ⟨hxI, hxm⟩
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.mp hxI
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hx : i + a * g = homogeneousComponent m i := by
      conv_lhs => rw [← homogeneousComponent_eq_self hxm]
      rw [map_add, mul_comm a g, homogeneousComponent_mul_of_lt hg hem, add_zero]
    rw [hx]
    exact ⟨homogeneousComponent_mem_of_mem hI hi m, homogeneousComponent_mem m i⟩
  · exact inf_le_inf_right _ fun x hx => Ideal.mem_sup_left hx

private theorem degPart_inf_map {I : Ideal (MvPolynomial σ K)} {g : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (hem : e ≤ m) (hreg : ∀ x, g * x ∈ I → x ∈ I) :
    degPart I m ⊓ (homogeneousSubmodule σ K (m - e)).map (LinearMap.mulLeft K g) =
      (degPart I (m - e)).map (LinearMap.mulLeft K g) := by
  apply le_antisymm
  · rintro _ ⟨⟨hxI, -⟩, ⟨y, hy, rfl⟩⟩
    exact ⟨y, ⟨hreg y hxI, hy⟩, rfl⟩
  · rintro _ ⟨y, ⟨hyI, hy⟩, rfl⟩
    exact ⟨⟨I.mul_mem_left g hyI, mul_mem_homogeneousSubmodule hg hem hy⟩, ⟨y, hy, rfl⟩⟩

private theorem finrank_map_mulLeft {g : MvPolynomial σ K} (hg : g ≠ 0)
    (W : Submodule K (MvPolynomial σ K)) :
    Module.finrank K (W.map (LinearMap.mulLeft K g)) = Module.finrank K W :=
  (Submodule.equivMapOfInjective _ (fun _ _ h => mul_left_cancel₀ hg h) W).finrank_eq.symm

private theorem hilbFn_sup_of_le [Finite σ] {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) {g : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (hg0 : g ≠ 0) (hreg : ∀ x, g * x ∈ I → x ∈ I) (hem : e ≤ m) :
    hilbFn (I ⊔ Ideal.span {g}) m = hilbFn I m - hilbFn I (m - e) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (degPart I m)
    ((homogeneousSubmodule σ K (m - e)).map (LinearMap.mulLeft K g))
  rw [← degPart_sup_of_le hI hg hem, degPart_inf_map hg hem hreg, finrank_map_mulLeft hg0,
    finrank_map_mulLeft hg0] at h
  unfold hilbFn
  omega

private theorem hilbFn_sup_of_lt {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) {g : MvPolynomial σ K} {e m : ℕ}
    (hg : g.IsHomogeneous e) (hem : m < e) :
    hilbFn (I ⊔ Ideal.span {g}) m = hilbFn I m := by
  rw [hilbFn, hilbFn, degPart_sup_of_lt hI hg hem]

private theorem hilbFn_top (m : ℕ) : hilbFn (⊤ : Ideal (MvPolynomial σ K)) m = 0 := by
  rw [hilbFn, degPart, Submodule.restrictScalars_top, top_inf_eq, sub_self]

/-- The Hilbert series of `S ⧸ I`. -/
private noncomputable def hilbSeries (I : Ideal (MvPolynomial σ K)) : PowerSeries ℤ :=
  PowerSeries.mk (hilbFn I)

open PowerSeries in
/-- Adding a homogeneous nonzerodivisor of degree `e` multiplies the Hilbert series by
`1 - X ^ e`. -/
private theorem hilbSeries_sup [Finite σ] {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) {g : MvPolynomial σ K} {e : ℕ}
    (hg : g.IsHomogeneous e) (hreg : ∀ x, g * x ∈ I → x ∈ I) :
    hilbSeries (I ⊔ Ideal.span {g}) = (1 - PowerSeries.X ^ e) * hilbSeries I := by
  by_cases hg0 : g = 0
  · have hItop : I = ⊤ := by
      refine (Ideal.eq_top_iff_one I).mpr (hreg 1 ?_)
      rw [hg0, zero_mul]
      exact I.zero_mem
    have htop : hilbSeries (⊤ : Ideal (MvPolynomial σ K)) = 0 := by
      ext m
      rw [hilbSeries, coeff_mk, hilbFn_top, map_zero]
    rw [hItop, top_sup_eq, htop, mul_zero]
  · ext m
    rw [hilbSeries, hilbSeries, coeff_mk, sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_mk]
    split_ifs with hem
    · rw [coeff_mk, hilbFn_sup_of_le hI hg hg0 hreg hem]
    · rw [hilbFn_sup_of_lt hI hg (not_le.mp hem), sub_zero]

end HilbertFunction

section Count

private theorem natCard_degree_eq (n d : ℕ) :
    Nat.card {s : Fin (n + 1) →₀ ℕ // s.degree = d} = (n + d).choose n := by
  classical
  let e : {s : Fin (n + 1) →₀ ℕ // s.degree = d} ≃ Sym (Fin (n + 1)) d :=
    { toFun := fun s => ⟨Finsupp.toMultiset s.1, by
        have h2 := s.2
        rw [Finsupp.degree_apply] at h2
        rw [Finsupp.card_toMultiset]
        simpa [Finsupp.sum] using h2⟩
      invFun := fun t => ⟨Multiset.toFinsupp (t : Multiset (Fin (n + 1))), by
        rw [Finsupp.degree_apply]
        have h2 : (t : Multiset (Fin (n + 1))).card = d := t.2
        simp [h2]⟩
      left_inv := fun s => by
        apply Subtype.ext
        simp
      right_inv := fun t => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

private theorem finrank_homogeneousSubmodule (n d : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (n + 1)) K d) = (n + d).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {x : Fin (n + 1) →₀ ℕ | x.degree = d})).trans
      (natCard_degree_eq n d)

end Count

section Series

open PowerSeries

variable {n : ℕ}

private theorem hilbSeries_bot :
    hilbSeries (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) * (1 - PowerSeries.X) ^ (n + 1) = 1 := by
  have h : hilbSeries (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) =
      PowerSeries.mk fun m => (((n + m).choose n : ℕ) : ℤ) := by
    ext m
    rw [hilbSeries, coeff_mk, coeff_mk, hilbFn, degPart, Submodule.restrictScalars_bot,
      bot_inf_eq, finrank_bot, finrank_homogeneousSubmodule, Nat.cast_zero, sub_zero]
  rw [h]
  exact mk_add_choose_mul_one_sub_pow_eq_one ℤ n

/-- The ideal generated by the first `k` members of a family. -/
private noncomputable def idealUpTo (f : Fin n → MvPolynomial (Fin (n + 1)) K) (k : ℕ) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span (f '' {j | (j : ℕ) < k})

private theorem idealUpTo_zero (f : Fin n → MvPolynomial (Fin (n + 1)) K) :
    idealUpTo f 0 = ⊥ := by
  simp [idealUpTo]

private theorem idealUpTo_succ (f : Fin n → MvPolynomial (Fin (n + 1)) K) {k : ℕ} (hk : k < n) :
    idealUpTo f (k + 1) = idealUpTo f k ⊔ Ideal.span {f ⟨k, hk⟩} := by
  have h : {j : Fin n | (j : ℕ) < k + 1} = {j : Fin n | (j : ℕ) < k} ∪ {⟨k, hk⟩} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
    omega
  rw [idealUpTo, idealUpTo, h, Set.image_union, Set.image_singleton, Ideal.span_union]

private theorem idealUpTo_self (f : Fin n → MvPolynomial (Fin (n + 1)) K) :
    idealUpTo f n = Ideal.span (Set.range f) := by
  have h : {j : Fin n | (j : ℕ) < n} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
  rw [idealUpTo, h, Set.image_univ]

/-- The degrees, extended by zero to all natural numbers. -/
private def degExt (d : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then d ⟨i, h⟩ else 0

private theorem hilbSeries_idealUpTo (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ) (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hreg : ∀ k : Fin n, ∀ x, f k * x ∈ Ideal.span (f '' {j | j < k}) →
      x ∈ Ideal.span (f '' {j | j < k})) :
    ∀ k ≤ n, (1 - PowerSeries.X) ^ (n + 1) * hilbSeries (idealUpTo f k) =
      ∏ i ∈ Finset.range k, (1 - PowerSeries.X ^ degExt d i) := by
  intro k hk
  induction k with
  | zero => rw [idealUpTo_zero, Finset.prod_range_zero, mul_comm, hilbSeries_bot]
  | succ k ih =>
    have hk' : k < n := by omega
    have hI : (idealUpTo f k).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
      isHomogeneous_span _ fun _ ⟨j, _, hj⟩ => ⟨d j, hj ▸ hd j⟩
    rw [idealUpTo_succ f hk', hilbSeries_sup hI (hd ⟨k, hk'⟩) (hreg ⟨k, hk'⟩),
      Finset.prod_range_succ, ← ih (by omega), degExt, dite_eq_left hk']
    ring

private theorem hilbSeries_span (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hreg : ∀ k : Fin n, ∀ x, f k * x ∈ Ideal.span (f '' {j | j < k}) →
      x ∈ Ideal.span (f '' {j | j < k})) :
    (1 - PowerSeries.X) ^ (n + 1) * hilbSeries (Ideal.span (Set.range f)) =
      ∏ k, (1 - PowerSeries.X ^ d k) := by
  rw [← idealUpTo_self, hilbSeries_idealUpTo f d hd hreg n le_rfl, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [degExt, dite_eq_left i.isLt]

end Series

section Eventual

open PowerSeries

variable {n : ℕ}

private theorem one_sub_X_ne_zero : (1 - PowerSeries.X : PowerSeries ℤ) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  simp at this

private theorem hilbFn_eq_sum {σ : Type*} (I : Ideal (MvPolynomial σ K)) (P : Polynomial ℤ)
    (h : (1 - PowerSeries.X) * hilbSeries I = (P : PowerSeries ℤ)) (m : ℕ) :
    hilbFn I m = ∑ i ∈ Finset.range (m + 1), P.coeff i := by
  induction m with
  | zero =>
    have := congrArg (coeff 0) h
    rw [sub_mul, one_mul, map_sub, coeff_zero_X_mul, sub_zero, hilbSeries, coeff_mk,
      Polynomial.coeff_coe] at this
    rw [this, Finset.sum_range_one]
  | succ m ih =>
    have := congrArg (coeff (m + 1)) h
    rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, hilbSeries, coeff_mk, coeff_mk,
      Polynomial.coeff_coe] at this
    rw [Finset.sum_range_succ, ← ih, ← this]
    ring

private theorem coe_prod_geom (d : Fin n → ℕ) :
    ((∏ k, ∑ i ∈ Finset.range (d k), Polynomial.X ^ i : Polynomial ℤ) : PowerSeries ℤ) =
      ∏ k, ∑ i ∈ Finset.range (d k), PowerSeries.X ^ i := by
  simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, map_sum, map_pow]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

private theorem eval_prod_geom (d : Fin n → ℕ) :
    (∏ k, ∑ i ∈ Finset.range (d k), Polynomial.X ^ i : Polynomial ℤ).eval 1 =
      ∏ k, (d k : ℤ) := by
  simp [Polynomial.eval_prod, Polynomial.eval_geom_sum]

/-- The Hilbert function of `S ⧸ J` is eventually equal to `∏ k, d k`. -/
private theorem eventually_hilbFn (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hreg : ∀ k : Fin n, ∀ x, f k * x ∈ Ideal.span (f '' {j | j < k}) →
      x ∈ Ideal.span (f '' {j | j < k})) :
    ∃ m₀, ∀ m, m₀ ≤ m → hilbFn (Ideal.span (Set.range f)) m = ∏ k, (d k : ℤ) := by
  let P : Polynomial ℤ := ∏ k, ∑ i ∈ Finset.range (d k), Polynomial.X ^ i
  have h1 : (1 - PowerSeries.X : PowerSeries ℤ) ^ n *
      ((1 - PowerSeries.X) * hilbSeries (Ideal.span (Set.range f))) =
      (1 - PowerSeries.X) ^ n * (P : PowerSeries ℤ) := by
    rw [← mul_assoc, ← pow_succ, hilbSeries_span f d hd hreg, coe_prod_geom]
    calc ∏ k, (1 - PowerSeries.X ^ d k)
        = ∏ k, ((1 - PowerSeries.X) * ∑ i ∈ Finset.range (d k), PowerSeries.X ^ i) :=
          Finset.prod_congr rfl fun k _ => (mul_neg_geom_sum _ _).symm
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 := mul_left_cancel₀ (pow_ne_zero n one_sub_X_ne_zero) h1
  refine ⟨P.natDegree, fun m hm => ?_⟩
  rw [hilbFn_eq_sum _ P h2, ← eval_prod_geom d,
    Polynomial.eval_eq_sum_range' (by omega : P.natDegree < m + 1)]
  simp

end Eventual

section Dehomogenize

variable {σ : Type*}

/-- Homogenization in degree `D` with respect to the linear form `ℓ`. -/
private noncomputable def homogenize (ℓ : MvPolynomial σ K) (D : ℕ) (p : MvPolynomial σ K) :
    MvPolynomial σ K :=
  ∑ t ∈ Finset.range (D + 1), ℓ ^ (D - t) * homogeneousComponent t p

private theorem homogenize_add (ℓ : MvPolynomial σ K) (D : ℕ) (p q : MvPolynomial σ K) :
    homogenize ℓ D (p + q) = homogenize ℓ D p + homogenize ℓ D q := by
  simp only [homogenize, map_add, mul_add, Finset.sum_add_distrib]

private theorem homogenize_sub (ℓ : MvPolynomial σ K) (D : ℕ) (p q : MvPolynomial σ K) :
    homogenize ℓ D (p - q) = homogenize ℓ D p - homogenize ℓ D q := by
  simp only [homogenize, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem homogenize_mem {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) (ℓ : MvPolynomial σ K) (D : ℕ)
    {p : MvPolynomial σ K} (hp : p ∈ J) : homogenize ℓ D p ∈ J :=
  J.sum_mem fun t _ => J.mul_mem_left _ (homogeneousComponent_mem_of_mem hJ hp t)

private theorem homogenize_of_isHomogeneous (ℓ : MvPolynomial σ K) {D m : ℕ} (hmD : m ≤ D)
    {x : MvPolynomial σ K} (hx : x.IsHomogeneous m) :
    homogenize ℓ D x = ℓ ^ (D - m) * x := by
  simp [homogenize, homogeneousComponent_of_mem hx, Nat.lt_succ_iff.mpr hmD]

private theorem homogenize_succ (ℓ : MvPolynomial σ K) (D : ℕ) (p : MvPolynomial σ K) :
    homogenize ℓ (D + 1) p = ℓ * homogenize ℓ D p + homogeneousComponent (D + 1) p := by
  rw [homogenize, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, homogenize,
    Finset.mul_sum, add_left_inj]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show D + 1 - t = D - t + 1 by omega, pow_succ]
  ring

private theorem homogenize_succ_mul {ℓ : MvPolynomial σ K} (hℓ : ℓ.IsHomogeneous 1) (D : ℕ)
    (p : MvPolynomial σ K) : homogenize ℓ (D + 1) (ℓ * p) = ℓ * homogenize ℓ D p := by
  rw [homogenize, Finset.sum_range_succ', homogeneousComponent_mul_of_lt hℓ zero_lt_one,
    mul_zero, add_zero, homogenize, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [homogeneousComponent_mul_of_le hℓ (by omega : 1 ≤ t + 1), Nat.add_sub_cancel,
    Nat.add_sub_add_right]
  ring

/-- Homogenization in high degree kills multiples of `ℓ - 1`. -/
private theorem homogenize_mul_sub_one {ℓ : MvPolynomial σ K} (hℓ : ℓ.IsHomogeneous 1) {D : ℕ}
    {p : MvPolynomial σ K} (hp : p.totalDegree < D + 1) :
    homogenize ℓ (D + 1) (p * (ℓ - 1)) = 0 := by
  rw [show p * (ℓ - 1) = ℓ * p - p by ring, homogenize_sub, homogenize_succ_mul hℓ,
    homogenize_succ, homogeneousComponent_eq_zero _ _ hp, add_zero, sub_self]

private theorem mem_of_pow_mul_mem {J : Ideal (MvPolynomial σ K)} {ℓ : MvPolynomial σ K}
    (hℓreg : ∀ x, ℓ * x ∈ J → x ∈ J) (k : ℕ) {x : MvPolynomial σ K} (hx : ℓ ^ k * x ∈ J) :
    x ∈ J := by
  induction k with
  | zero => rwa [pow_zero, one_mul] at hx
  | succ k ih => exact ih (hℓreg _ (by rwa [pow_succ', mul_assoc] at hx))

/-- A homogeneous polynomial in `J + (ℓ - 1)` lies in `J`. -/
private theorem mem_of_mem_sup {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) {ℓ : MvPolynomial σ K}
    (hℓ : ℓ.IsHomogeneous 1) (hℓreg : ∀ x, ℓ * x ∈ J → x ∈ J) {m : ℕ} {x : MvPolynomial σ K}
    (hx : x.IsHomogeneous m) (hxL : x ∈ J ⊔ Ideal.span {ℓ - 1}) : x ∈ J := by
  obtain ⟨j, hj, z, hz, rfl⟩ := Submodule.mem_sup.mp hxL
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have h : homogenize ℓ (m + y.totalDegree + 1) (j + y * (ℓ - 1)) ∈ J := by
    rw [homogenize_add, homogenize_mul_sub_one hℓ (D := m + y.totalDegree) (by omega), add_zero]
    exact homogenize_mem hJ ℓ _ hj
  rw [homogenize_of_isHomogeneous ℓ (by omega) hx] at h
  exact mem_of_pow_mul_mem hℓreg _ h

variable (J : Ideal (MvPolynomial σ K)) (ℓ : MvPolynomial σ K)

/-- The image of the homogeneous polynomials of degree `m` in `S ⧸ (J + (ℓ - 1))`. -/
private noncomputable def degImage (m : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ (J ⊔ Ideal.span {ℓ - 1})) :=
  (homogeneousSubmodule σ K m).map (Ideal.Quotient.mkₐ K (J ⊔ Ideal.span {ℓ - 1})).toLinearMap

private instance finiteDimensional_degImage [Finite σ] (m : ℕ) :
    FiniteDimensional K (degImage J ℓ m) :=
  Module.Finite.map _ _

variable {J ℓ}

private theorem degImage_le_succ (hℓ : ℓ.IsHomogeneous 1) (m : ℕ) :
    degImage J ℓ m ≤ degImage J ℓ (m + 1) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨ℓ * x, ?_, ?_⟩
  · have := hℓ.mul hx
    rwa [add_comm] at this
  · simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, by ring⟩)

private theorem degImage_mono (hℓ : ℓ.IsHomogeneous 1) : Monotone (degImage J ℓ) :=
  monotone_nat_of_le_succ (degImage_le_succ hℓ)

private theorem mk_mem_degImage (hℓ : ℓ.IsHomogeneous 1) (p : MvPolynomial σ K) :
    Ideal.Quotient.mk (J ⊔ Ideal.span {ℓ - 1}) p ∈ degImage J ℓ p.totalDegree := by
  have h : Ideal.Quotient.mk (J ⊔ Ideal.span {ℓ - 1}) p =
      ∑ t ∈ Finset.range (p.totalDegree + 1),
        Ideal.Quotient.mk (J ⊔ Ideal.span {ℓ - 1}) (homogeneousComponent t p) := by
    rw [← map_sum, sum_homogeneousComponent]
  rw [h]
  refine Submodule.sum_mem _ fun t ht => ?_
  exact degImage_mono hℓ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
    ⟨_, homogeneousComponent_mem t p, rfl⟩

private theorem finrank_degImage [Finite σ] (hJ : J.IsHomogeneous (homogeneousSubmodule σ K))
    (hℓ : ℓ.IsHomogeneous 1) (hℓreg : ∀ x, ℓ * x ∈ J → x ∈ J) (m : ℕ) :
    (Module.finrank K (degImage J ℓ m) : ℤ) = hilbFn J m := by
  let ψ := (Ideal.Quotient.mkₐ K (J ⊔ Ideal.span {ℓ - 1})).toLinearMap ∘ₗ
    (homogeneousSubmodule σ K m).subtype
  have hrange : LinearMap.range ψ = degImage J ℓ m := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker : LinearMap.ker ψ = (degPart J m).comap (homogeneousSubmodule σ K m).subtype := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro h
      exact ⟨mem_of_mem_sup hJ hℓ hℓreg hx (Ideal.Quotient.eq_zero_iff_mem.mp h), hx⟩
    · rintro ⟨h, -⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left h)
  have h := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe (p := degPart J m)
    (q := homogeneousSubmodule σ K m) inf_le_right).finrank_eq] at h
  rw [hilbFn]
  omega

end Dehomogenize

/-- If `f₁, …, fₙ` are homogeneous of degrees `d₁, …, dₙ` and form a regular sequence in
`K[X₀, …, Xₙ]`, and the linear form `ℓ` is a nonzerodivisor modulo `J = (f₁, …, fₙ)`, then
`K[X₀, …, Xₙ] ⧸ (J + (ℓ - 1))` is finite-dimensional of dimension `d₁ ⋯ dₙ`. -/
private theorem finrank_quotient_eq_prod {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ) (hd : ∀ k, (f k).IsHomogeneous (d k))
    (hreg : ∀ k : Fin n, ∀ x, f k * x ∈ Ideal.span (f '' {j | j < k}) →
      x ∈ Ideal.span (f '' {j | j < k}))
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hℓreg : ∀ x, ℓ * x ∈ Ideal.span (Set.range f) → x ∈ Ideal.span (Set.range f)) :
    Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1})) ∧
      Module.finrank K (MvPolynomial (Fin (n + 1)) K ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1})) = ∏ k, d k := by
  have hJ : (Ideal.span (Set.range f)).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
    isHomogeneous_span _ fun _ ⟨k, hk⟩ => ⟨d k, hk ▸ hd k⟩
  obtain ⟨m₀, hm₀⟩ := eventually_hilbFn f d hd hreg
  have hfr : ∀ m, m₀ ≤ m →
      Module.finrank K (degImage (Ideal.span (Set.range f)) ℓ m) = ∏ k, d k := by
    intro m hm
    have := finrank_degImage hJ hℓ hℓreg m
    rw [hm₀ m hm] at this
    exact_mod_cast this
  have htop : degImage (Ideal.span (Set.range f)) ℓ m₀ = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hle := degImage_mono (J := Ideal.span (Set.range f)) hℓ
      (le_max_left m₀ p.totalDegree)
    rw [Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr _ le_rfl, hfr _ (le_max_left _ _)])]
    exact degImage_mono hℓ (le_max_right _ _) (mk_mem_degImage hℓ p)
  have hfin : Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1})) := by
    rw [Module.finite_def, ← htop]
    exact (homogeneousSubmodule_fg _ K m₀).map _
  refine ⟨hfin, ?_⟩
  rw [← finrank_top, ← htop, hfr m₀ le_rfl]

end BezoutHilbert

/-!
### Regular sequences of homogeneous polynomials with only the trivial common zero

Let `K` be an algebraically closed field and `S = K[X₀, …, Xₙ]`. If `f₁, …, fₙ` are homogeneous
of positive degree and `ℓ` is a linear form whose only common zero with the `fₖ` is the origin,
then `f₁, …, fₙ, ℓ` is a regular sequence in `S`.

The proof passes through the local ring `R₀` of `S` at the origin:

* `R₀` is Cohen–Macaulay of dimension `n + 1`, because the variables form a regular sequence in
  `R₀` generating its maximal ideal;
* by the Nullstellensatz, the images of `f₁, …, fₙ, ℓ` form a system of parameters of `R₀`, hence
  a regular sequence (`IsLocalRing.isRegular_of_systemOfParameters`);
* a graded descent argument brings the nonzerodivisor statements back to `S`.
-/

namespace BezoutRegular

section Graded

variable {σ : Type*}

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma decompose_eq (x : MvPolynomial σ K) (m : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ K) x m : MvPolynomial σ K) =
      homogeneousComponent m x :=
  MvPolynomial.decomposition.decompose'_apply x m

/-- Homogeneous components of an element of an ideal spanned by homogeneous polynomials lie in
that ideal. -/
private lemma homogeneousComponent_mem_span {s : Set (MvPolynomial σ K)}
    (hs : ∀ p ∈ s, ∃ e, p.IsHomogeneous e) {x : MvPolynomial σ K} (hx : x ∈ Ideal.span s)
    (m : ℕ) : homogeneousComponent m x ∈ Ideal.span s := by
  have H := Ideal.homogeneous_span (homogeneousSubmodule σ K) s
    (fun p hp ↦ (hs p hp).imp fun e he ↦ he)
  have := H m hx
  rwa [decompose_eq] at this

private lemma homogeneousComponent_mul_left {g : MvPolynomial σ K} {e : ℕ}
    (hg : g.IsHomogeneous e) (x : MvPolynomial σ K) (m : ℕ) :
    homogeneousComponent (m + e) (g * x) = g * homogeneousComponent m x := by
  have := DirectSum.coe_decompose_mul_of_left_mem_of_le (homogeneousSubmodule σ K) (b := x)
    (n := m + e) (show g ∈ homogeneousSubmodule σ K e from hg) (by omega)
  rwa [Nat.add_sub_cancel, decompose_eq, decompose_eq] at this

private lemma homogeneousComponent_mul_right {x : MvPolynomial σ K} {m : ℕ}
    (hx : x.IsHomogeneous m) (t : MvPolynomial σ K) :
    homogeneousComponent m (t * x) = C (t.coeff 0) * x := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (homogeneousSubmodule σ K) (a := t)
    (n := m) (show x ∈ homogeneousSubmodule σ K m from hx) le_rfl
  rwa [Nat.sub_self, decompose_eq, decompose_eq, homogeneousComponent_zero] at this

private lemma coeff_zero_eq_zero {p : MvPolynomial σ K} {e : ℕ} (hp : p.IsHomogeneous e)
    (he : 1 ≤ e) : p.coeff 0 = 0 :=
  hp.coeff_eq_zero (by simp only [map_zero]; omega)

end Graded

section Origin

variable {σ : Type*}

variable (K σ) in
/-- The ideal of polynomials with zero constant coefficient. -/
private noncomputable abbrev m0 : Ideal (MvPolynomial σ K) :=
  RingHom.ker (constantCoeff (σ := σ) (R := K))

private instance m0_isPrime : (m0 K σ).IsPrime := RingHom.ker_isPrime _

variable (K σ) in
/-- The local ring of the polynomial ring at the origin. -/
private abbrev R0 := Localization.AtPrime (m0 K σ)

private lemma mem_m0_iff {p : MvPolynomial σ K} : p ∈ m0 K σ ↔ p.coeff 0 = 0 :=
  RingHom.mem_ker

/-- Graded descent: a homogeneous polynomial which is a nonzerodivisor modulo a homogeneous ideal
after localizing at the origin is already a nonzerodivisor modulo that ideal. -/
private lemma mem_of_mul_mem {s : Set (MvPolynomial σ K)} (hs : ∀ p ∈ s, ∃ e, p.IsHomogeneous e)
    {g : MvPolynomial σ K} {e : ℕ} (hg : g.IsHomogeneous e)
    (hreg : ∀ y : R0 K σ, algebraMap _ (R0 K σ) g * y ∈ (Ideal.span s).map (algebraMap _ _) →
      y ∈ (Ideal.span s).map (algebraMap _ _))
    {x : MvPolynomial σ K} (hx : g * x ∈ Ideal.span s) : x ∈ Ideal.span s := by
  rw [← sum_homogeneousComponent x]
  refine Ideal.sum_mem _ fun m _ ↦ ?_
  have h1 : g * homogeneousComponent m x ∈ Ideal.span s := by
    rw [← homogeneousComponent_mul_left hg]
    exact homogeneousComponent_mem_span hs hx _
  have h2 := hreg (algebraMap _ _ (homogeneousComponent m x))
    (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ h1)
  obtain ⟨t, ht, htx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (m0 K σ).primeCompl _ _ _).mp h2
  have h3 := homogeneousComponent_mem_span hs htx m
  rw [homogeneousComponent_mul_right (homogeneousComponent_isHomogeneous m x)] at h3
  have ht0 : t.coeff 0 ≠ 0 := fun h ↦ (Ideal.mem_primeCompl_iff.mp ht) (mem_m0_iff.mpr h)
  have := Ideal.mul_mem_left _ (C (t.coeff 0)⁻¹) h3
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ ht0, C_1, one_mul] at this

end Origin

section Sequences

/-- Regularity on `R ⧸ I • ⊤` is the nonzerodivisor property modulo `I`. -/
private lemma isSMulRegular_quotient_iff {R : Type*} [CommRing R] {I : Ideal R} {r : R} :
    IsSMulRegular (R ⧸ (I • ⊤ : Submodule R R)) r ↔ ∀ y, r * y ∈ I → y ∈ I := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  constructor
  · intro h y hy
    have h1 : r • (Submodule.Quotient.mk y : R ⧸ (I • ⊤ : Submodule R R)) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      simpa using hy
    simpa using (Submodule.Quotient.mk_eq_zero _).mp (h _ h1)
  · intro h a ha
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using h y (by simpa using ha)

private lemma mem_take_ofFn {α : Type*} {n : ℕ} (g : Fin n → α) (k : ℕ) (a : α) :
    a ∈ (List.ofFn g).take k ↔ ∃ j : Fin n, (j : ℕ) < k ∧ g j = a := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_ofFn] at hj
    exact ⟨⟨j, by omega⟩, show j < k by omega, (List.getElem_ofFn _).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by simp only [List.length_ofFn]; omega, List.getElem_ofFn _⟩

private lemma ofList_take_ofFn {R : Type*} [CommRing R] {n : ℕ} (g : Fin n → R) (k : Fin n) :
    Ideal.ofList ((List.ofFn g).take k) = Ideal.span (g '' {j | j < k}) := by
  rw [Ideal.ofList]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq, mem_take_ofFn, Set.mem_image, Fin.lt_def]

end Sequences

section Variables

private lemma X_mul_mem_span_X {N : ℕ} (i : Fin N) {p : MvPolynomial (Fin N) K}
    (hp : X i * p ∈ Ideal.span (X '' {j | j < i})) : p ∈ Ideal.span (X '' {j | j < i}) := by
  rw [mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hmem : Finsupp.single i 1 + m ∈ (X i * p).support := by
    rw [support_X_mul]
    exact Finset.mem_map_of_mem _ hm
  obtain ⟨j, hj, hmj⟩ := hp _ hmem
  refine ⟨j, hj, ?_⟩
  have hji : i ≠ j := (ne_of_lt (show j < i from hj)).symm
  simpa [Finsupp.single_apply, hji] using hmj

/-- The variables form a weakly regular sequence in the polynomial ring. -/
private lemma isWeaklyRegular_X (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin N) K)
      (List.ofFn (X : Fin N → MvPolynomial (Fin N) K)) := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin]
  intro i
  have hi : (i : ℕ) < N := by simpa using i.2
  have h1 : (List.ofFn (X : Fin N → MvPolynomial (Fin N) K))[(i : ℕ)] = X ⟨i, hi⟩ :=
    List.getElem_ofFn _
  have h2 := ofList_take_ofFn (X : Fin N → MvPolynomial (Fin N) K) ⟨i, hi⟩
  simp only at h2
  rw [Fin.getElem_fin, h1, h2, isSMulRegular_quotient_iff]
  exact fun y hy ↦ X_mul_mem_span_X _ hy

variable (K) in
/-- The images of the variables in the local ring at the origin. -/
private noncomputable abbrev xsX (N : ℕ) : List (R0 K (Fin N)) :=
  (List.ofFn (X : Fin N → MvPolynomial (Fin N) K)).map (algebraMap _ (R0 K (Fin N)))

private lemma isWeaklyRegular_xsX (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (R0 K (Fin N)) (xsX K N) := by
  have : Module.Flat (MvPolynomial (Fin N) K) (R0 K (Fin N)) :=
    IsLocalization.flat _ (m0 K (Fin N)).primeCompl
  have h := (isWeaklyRegular_X (K := K) N).isWeaklyRegular_lTensor (M₂ := R0 K (Fin N))
  rw [(TensorProduct.rid _ _).isWeaklyRegular_congr] at h
  exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff _ _ _).mpr h

private lemma algebraMap_mem_maximalIdeal {N : ℕ} {p : MvPolynomial (Fin N) K}
    (hp : p.coeff 0 = 0) :
    algebraMap _ (R0 K (Fin N)) p ∈ IsLocalRing.maximalIdeal (R0 K (Fin N)) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (m0 K (Fin N)) p).mpr (mem_m0_iff.mpr hp)

private lemma xsX_mem (N : ℕ) : ∀ r ∈ xsX K N, r ∈ IsLocalRing.maximalIdeal (R0 K (Fin N)) := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact algebraMap_mem_maximalIdeal (by simp)

private lemma isRegular_xsX (N : ℕ) :
    RingTheory.Sequence.IsRegular (R0 K (Fin N)) (xsX K N) :=
  (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (xsX_mem N)).mpr
    (isWeaklyRegular_xsX N)

private lemma ofList_ofFn_X (N : ℕ) :
    Ideal.ofList (List.ofFn (X : Fin N → MvPolynomial (Fin N) K)) = m0 K (Fin N) := by
  ext p
  rw [mem_m0_iff]
  have : {r | r ∈ List.ofFn (X : Fin N → MvPolynomial (Fin N) K)} = X '' Set.univ := by
    ext r
    simp [List.mem_ofFn]
  rw [Ideal.ofList, this, mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra h0
    obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.mpr h0)
    exact hi rfl
  · intro h m hm
    by_contra hne
    have hm0 : m = 0 := Finsupp.ext fun i ↦ by_contra fun hi ↦ hne ⟨i, trivial, hi⟩
    subst hm0
    exact (mem_support_iff.mp hm) h

private lemma maximalIdeal_le_radical {N : ℕ} {J : Ideal (R0 K (Fin N))}
    (h : ∀ i, algebraMap _ (R0 K (Fin N)) (X i : MvPolynomial (Fin N) K) ∈ J.radical) :
    IsLocalRing.maximalIdeal (R0 K (Fin N)) ≤ J.radical := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (m0 K (Fin N)), Ideal.map_le_iff_le_comap]
  intro p hp
  rw [← ofList_ofFn_X] at hp
  refine (Ideal.span_le.mpr ?_ : Ideal.ofList _ ≤ J.radical.comap _) hp
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  exact Ideal.mem_comap.mpr (h i)

/-- A quotient of a local ring by an ideal whose radical is the maximal ideal has dimension
zero. -/
private lemma ringKrullDim_quotient_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    {I : Ideal R} (h1 : I ≤ IsLocalRing.maximalIdeal R)
    (h2 : IsLocalRing.maximalIdeal R ≤ I.radical) : ringKrullDim (R ⧸ I) = 0 := by
  have : PrimeSpectrum.zeroLocus (I : Set R) = {IsLocalRing.closedPoint R} := by
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_singleton_iff]
    constructor
    · intro hp
      ext1
      exact le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top)
        (h2.trans ((p.2.radical_le_iff).mpr hp))
    · rintro rfl
      exact h1
  rw [ringKrullDim_quotient, this]
  exact Order.krullDim_eq_zero_of_unique

private lemma ringKrullDim_quotient_xsX (N : ℕ) :
    ringKrullDim (R0 K (Fin N) ⧸ Ideal.ofList (xsX K N)) = 0 := by
  refine ringKrullDim_quotient_eq_zero (Ideal.span_le.mpr (xsX_mem N))
    (maximalIdeal_le_radical fun i ↦ Ideal.le_radical (Ideal.subset_span ?_))
  exact List.mem_map_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- The local ring at the origin has dimension `N`. -/
private lemma ringKrullDim_R0 (N : ℕ) : ringKrullDim (R0 K (Fin N)) = N := by
  have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ (isRegular_xsX (K := K) N)
  rw [ringKrullDim_quotient_xsX, zero_add] at h
  simpa using h.symm

/-- The local ring at the origin has depth `N`. -/
private lemma depth_R0 (N : ℕ) :
    IsLocalRing.depth (ModuleCat.of (R0 K (Fin N)) (R0 K (Fin N))) = N := by
  rw [IsLocalRing.depth_eq_sSup_length_isRegular]
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨rs, hrs, hmem, rfl⟩
    have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hrs
    rw [ringKrullDim_R0] at h
    have : Nontrivial (R0 K (Fin N) ⧸ Ideal.ofList rs) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
        (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.span_le.mpr hmem))
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := R0 K (Fin N) ⧸ Ideal.ofList rs)
    have : ((rs.length : ℕ) : WithBot ℕ∞) ≤ ((N : ℕ) : WithBot ℕ∞) :=
      h ▸ le_add_of_nonneg_left h0
    exact_mod_cast this
  · exact le_sSup ⟨_, isRegular_xsX N, xsX_mem N, by simp⟩

end Variables

section Parameters

/-- The sequence `f₁, …, fₙ, ℓ` in the local ring at the origin. -/
private noncomputable abbrev xsF {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (ℓ : MvPolynomial (Fin (n + 1)) K) : List (R0 K (Fin (n + 1))) :=
  (List.ofFn f ++ [ℓ]).map (algebraMap _ _)

private lemma xsF_mem {n : ℕ} {f : Fin n → MvPolynomial (Fin (n + 1)) K} {d : Fin n → ℕ}
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (hd_pos : ∀ k, 1 ≤ d k)
    {ℓ : MvPolynomial (Fin (n + 1)) K} (hℓ : ℓ.IsHomogeneous 1) :
    ∀ y ∈ xsF f ℓ, y ∈ IsLocalRing.maximalIdeal (R0 K (Fin (n + 1))) := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
    exact algebraMap_mem_maximalIdeal (coeff_zero_eq_zero (hd k) (hd_pos k))
  · rw [List.mem_singleton.mp hp]
    exact algebraMap_mem_maximalIdeal (coeff_zero_eq_zero hℓ le_rfl)

/-- By the Nullstellensatz, every variable lies in the radical of `(f₁, …, fₙ, ℓ)`. -/
private lemma X_mem_radical [IsAlgClosed K] {n : ℕ} {f : Fin n → MvPolynomial (Fin (n + 1)) K}
    {ℓ : MvPolynomial (Fin (n + 1)) K}
    (hzero : ∀ v : Fin (n + 1) → K, (∀ k, eval v (f k) = 0) → eval v ℓ = 0 → v = 0)
    (i : Fin (n + 1)) : X i ∈ (Ideal.ofList (List.ofFn f ++ [ℓ])).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), mem_vanishingIdeal_iff]
  intro v hv
  rw [mem_zeroLocus_iff] at hv
  have hv0 : v = 0 := hzero v
    (fun k ↦ by simpa using hv (f k) (Ideal.subset_span (by simp)))
    (by simpa using hv ℓ (Ideal.subset_span (by simp)))
  simp [hv0]

/-- The images of `f₁, …, fₙ, ℓ` form a system of parameters of the local ring at the
origin. -/
private lemma ringKrullDim_quotient_xsF [IsAlgClosed K] {n : ℕ}
    {f : Fin n → MvPolynomial (Fin (n + 1)) K} {d : Fin n → ℕ}
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (hd_pos : ∀ k, 1 ≤ d k)
    {ℓ : MvPolynomial (Fin (n + 1)) K} (hℓ : ℓ.IsHomogeneous 1)
    (hzero : ∀ v : Fin (n + 1) → K, (∀ k, eval v (f k) = 0) → eval v ℓ = 0 → v = 0) :
    ringKrullDim (R0 K (Fin (n + 1)) ⧸ Ideal.ofList (xsF f ℓ)) = 0 := by
  refine ringKrullDim_quotient_eq_zero (Ideal.span_le.mpr (xsF_mem hd hd_pos hℓ))
    (maximalIdeal_le_radical fun i ↦ ?_)
  rw [xsF, ← Ideal.map_ofList]
  exact Ideal.map_radical_le _ (Ideal.mem_map_of_mem _ (X_mem_radical hzero i))

private lemma isRegular_xsF [IsAlgClosed K] {n : ℕ}
    {f : Fin n → MvPolynomial (Fin (n + 1)) K} {d : Fin n → ℕ}
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (hd_pos : ∀ k, 1 ≤ d k)
    {ℓ : MvPolynomial (Fin (n + 1)) K} (hℓ : ℓ.IsHomogeneous 1)
    (hzero : ∀ v : Fin (n + 1) → K, (∀ k, eval v (f k) = 0) → eval v ℓ = 0 → v = 0) :
    RingTheory.Sequence.IsRegular (R0 K (Fin (n + 1))) (xsF f ℓ) := by
  have hCM : (IsLocalRing.depth (ModuleCat.of (R0 K (Fin (n + 1))) (R0 K (Fin (n + 1)))) :
      WithBot ℕ∞) = ringKrullDim (R0 K (Fin (n + 1))) := by
    rw [depth_R0, ringKrullDim_R0]
    rfl
  exact IsLocalRing.isRegular_of_systemOfParameters hCM (ringKrullDim_R0 (n + 1)) _
    (by simp) (xsF_mem hd hd_pos hℓ) (ringKrullDim_quotient_xsF hd hd_pos hℓ hzero)

private lemma getElem_xsF {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (k : Fin n) (h : (k : ℕ) < (xsF f ℓ).length) :
    (xsF f ℓ)[(k : ℕ)] = algebraMap _ _ (f k) := by
  simp [xsF, List.getElem_append_left]

private lemma ofList_take_xsF {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (k : Fin n) :
    Ideal.ofList ((xsF f ℓ).take k) =
      (Ideal.span (f '' {j | j < k})).map (algebraMap _ (R0 K (Fin (n + 1)))) := by
  rw [← ofList_take_ofFn, Ideal.map_ofList, xsF, ← List.map_take,
    List.take_append_of_le_length (by simp only [List.length_ofFn]; omega)]

private lemma getElem_xsF_last {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (h : n < (xsF f ℓ).length) :
    (xsF f ℓ)[n] = algebraMap _ _ ℓ := by
  simp only [xsF, List.getElem_map]
  rw [List.getElem_concat_length (by simp)]

private lemma ofList_take_xsF_last {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (ℓ : MvPolynomial (Fin (n + 1)) K) :
    Ideal.ofList ((xsF f ℓ).take n) =
      (Ideal.span (Set.range f)).map (algebraMap _ (R0 K (Fin (n + 1)))) := by
  rw [xsF, ← List.map_take, List.take_left' (by simp), ← Ideal.map_ofList, Ideal.ofList]
  congr 2
  ext p
  simp [List.mem_ofFn]

end Parameters

/-- If homogeneous polynomials `f₁, …, fₙ` of positive degrees and a linear form `ℓ` in
`K[X₀, …, Xₙ]`, with `K` algebraically closed, have only the trivial common zero, then
`f₁, …, fₙ, ℓ` is a regular sequence: each `fₖ` is a nonzerodivisor modulo `(fⱼ : j < k)`, and `ℓ`
is a nonzerodivisor modulo `(f₁, …, fₙ)`. -/
private theorem regular_of_zero_only [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (hd_pos : ∀ k, 1 ≤ d k)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hzero : ∀ v : Fin (n + 1) → K, (∀ k, eval v (f k) = 0) → eval v ℓ = 0 → v = 0) :
    (∀ k : Fin n, ∀ x, f k * x ∈ Ideal.span (f '' {j | j < k}) →
      x ∈ Ideal.span (f '' {j | j < k})) ∧
    (∀ x, ℓ * x ∈ Ideal.span (Set.range f) → x ∈ Ideal.span (Set.range f)) := by
  have hw := (isRegular_xsF hd hd_pos hℓ hzero).toIsWeaklyRegular
  refine ⟨fun k x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hk : (k : ℕ) < (xsF f ℓ).length := by
      simp only [List.length_map, List.length_append, List.length_ofFn, List.length_singleton]
      omega
    have h1 := hw.regular_mod_prev k hk
    rw [getElem_xsF, ofList_take_xsF, isSMulRegular_quotient_iff] at h1
    refine mem_of_mul_mem (fun p hp ↦ ?_) (hd k) h1 hx
    obtain ⟨j, -, rfl⟩ := hp
    exact ⟨d j, hd j⟩
  · have hn : n < (xsF f ℓ).length := by simp
    have h1 := hw.regular_mod_prev n hn
    rw [getElem_xsF_last, ofList_take_xsF_last, isSMulRegular_quotient_iff] at h1
    refine mem_of_mul_mem (fun p hp ↦ ?_) hℓ h1 hx
    obtain ⟨j, rfl⟩ := hp
    exact ⟨d j, hd j⟩

end BezoutRegular

/-!
### Intersection multiplicity in two affine slices of the cone

Let `f₁, …, fₙ` be homogeneous in `K[X₀, …, Xₙ]`, let `ℓ` be a linear form and let `p` be a
projective point with `ℓ(p) ≠ 0`. The ring used by `intersectionMultiplicity` (the local ring at
the chart point `q` of `p`, cut by the `f_k` and `X_i - 1`) is isomorphic, as a `K`-algebra, to the
localization of `K[X] ⧸ (f, ℓ - 1)` at the point `v = ℓ(p)⁻¹ • p`. The two maps are the
substitutions `X_j ↦ X_j / ℓ` and `X_j ↦ X_j / X_i`. Since the residue field of the local ring at
`q` is `K`, the length over that local ring equals the dimension over `K`.
-/

namespace BezoutChart

section General

/-- Scaling every variable by a ring element `u` scales a homogeneous polynomial by `u ^ d`. -/
private lemma aeval_mul_of_isHomogeneous {σ R : Type*} [CommSemiring R] [Algebra K R]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d) (x : σ → R) (u : R) :
    aeval (fun j ↦ x j * u) F = u ^ d * aeval x F := by
  simp only [aeval_def, eval₂_eq, mul_pow, Finset.mul_sum, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [← hF.degree_eq_sum_deg_support hs]
  ring

/-- Evaluating at the images of the variables under an algebra map gives that algebra map. -/
private lemma aeval_algHom_X {σ R : Type*} [CommSemiring R] [Algebra K R]
    (φ : MvPolynomial σ K →ₐ[K] R) (F : MvPolynomial σ K) :
    aeval (fun j ↦ φ (X j)) F = φ F := by
  conv_rhs => rw [aeval_unique φ]
  rfl

/-- If `φ` sends each `X j` to `y j` modulo the maximal ideal, then the residue of `φ s` is the
value of `s` at `y`. -/
private lemma residue_algHom_eq {σ R : Type*} [CommRing R] [IsLocalRing R] [Algebra K R]
    (φ : MvPolynomial σ K →ₐ[K] R) (y : σ → K)
    (hy : ∀ j, IsLocalRing.residue R (φ (X j)) = algebraMap K _ (y j))
    (s : MvPolynomial σ K) :
    IsLocalRing.residue R (φ s) = algebraMap K _ (eval y s) := by
  have : (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)).comp φ =
      (Algebra.ofId K _).comp (aeval y) := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    simpa using hy j
  simpa using congrArg (fun g ↦ g s) this

private lemma isUnit_of_residue_algHom {σ R : Type*} [CommRing R] [IsLocalRing R] [Algebra K R]
    (φ : MvPolynomial σ K →ₐ[K] R) (y : σ → K)
    (hy : ∀ j, IsLocalRing.residue R (φ (X j)) = algebraMap K _ (y j))
    {s : MvPolynomial σ K} (hs : eval y s ≠ 0) : IsUnit (φ s) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, residue_algHom_eq φ y hy s]
  exact (map_ne_zero_iff _ (algebraMap K _).injective).mpr hs

/-- The residue of the image of `g a` in a localization at a prime is the value of `a` at `v`,
when `g` sends the polynomials vanishing at `v` into the prime. -/
private lemma residue_algebraMap_eq {σ R : Type*} [CommRing R] [Algebra K R]
    (P : Ideal R) [P.IsPrime] (g : MvPolynomial σ K →ₐ[K] R) (v : σ → K)
    (hv : ∀ a, eval v a = 0 → g a ∈ P) (a : MvPolynomial σ K) :
    IsLocalRing.residue (Localization.AtPrime P) (algebraMap R _ (g a)) =
      algebraMap K _ (eval v a) := by
  have h : g (a - C (eval v a)) ∈ P := hv _ (by simp)
  have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr h
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, map_sub, sub_eq_zero] at h2
  rw [h2, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K (Localization.AtPrime P) (IsLocalRing.ResidueField _)]
  rfl

end General

section Construction

variable {n : ℕ} {J : Ideal (MvPolynomial (Fin (n + 1)) K)}
  (P : Ideal (MvPolynomial (Fin (n + 1)) K ⧸ J)) [P.IsPrime]
  {q : Fin (n + 1) → K} (I : Ideal (localRingAt q))

/-- The substitution `X j ↦ X j * u` from polynomials into the local ring at `q`. -/
private noncomputable def alpha0 (u : localRingAt q) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] localRingAt q :=
  aeval fun j ↦ algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X j) * u

private lemma alpha0_X (u : localRingAt q) (j : Fin (n + 1)) :
    alpha0 u (X j) = algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X j) * u :=
  aeval_X _ _

private lemma alpha0_of_isHomogeneous (u : localRingAt q) {F : MvPolynomial (Fin (n + 1)) K}
    {e : ℕ} (hF : F.IsHomogeneous e) :
    alpha0 u F = u ^ e * algebraMap _ (localRingAt q) F := by
  rw [alpha0, aeval_mul_of_isHomogeneous hF]
  congr 1
  exact aeval_algHom_X (IsScalarTower.toAlgHom K _ (localRingAt q)) F

/-- The map `alpha0` descended to the quotient by `J`. -/
private noncomputable def alpha1 (u : localRingAt q) (hJ : ∀ a ∈ J, alpha0 u a ∈ I) :
    (MvPolynomial (Fin (n + 1)) K ⧸ J) →ₐ[K] localRingAt q ⧸ I :=
  Ideal.Quotient.liftₐ J ((Ideal.Quotient.mkₐ K I).comp (alpha0 u))
    fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hJ a ha)

private lemma alpha1_mk (u : localRingAt q) (hJ : ∀ a ∈ J, alpha0 u a ∈ I)
    (a : MvPolynomial (Fin (n + 1)) K) :
    alpha1 I u hJ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk I (alpha0 u a) :=
  rfl

/-- The map `alpha1` extended to the localization at `P`. -/
private noncomputable def alpha (u : localRingAt q) (hJ : ∀ a ∈ J, alpha0 u a ∈ I)
    (hunits : ∀ y : P.primeCompl, IsUnit (alpha1 I u hJ y)) :
    Localization.AtPrime P →ₐ[K] localRingAt q ⧸ I :=
  IsLocalization.liftAlgHom (A := K) (R := MvPolynomial (Fin (n + 1)) K ⧸ J) (M := P.primeCompl)
    (S := Localization.AtPrime P) (P := localRingAt q ⧸ I) (f := alpha1 I u hJ) hunits

private lemma alpha_algebraMap (u : localRingAt q) (hJ : ∀ a ∈ J, alpha0 u a ∈ I)
    (hunits : ∀ y : P.primeCompl, IsUnit (alpha1 I u hJ y)) (a : MvPolynomial (Fin (n + 1)) K) :
    alpha P I u hJ hunits (algebraMap _ _ (Ideal.Quotient.mk J a)) =
      Ideal.Quotient.mk I (alpha0 u a) :=
  IsLocalization.lift_eq _ _

/-- The substitution `X j ↦ X j * t` from polynomials into the localization at `P`. -/
private noncomputable def beta0 (t : Localization.AtPrime P) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] Localization.AtPrime P :=
  aeval fun j ↦ algebraMap _ (Localization.AtPrime P) (Ideal.Quotient.mk J (X j)) * t

private lemma beta0_X (t : Localization.AtPrime P) (j : Fin (n + 1)) :
    beta0 P t (X j) = algebraMap _ (Localization.AtPrime P) (Ideal.Quotient.mk J (X j)) * t :=
  aeval_X _ _

private lemma beta0_of_isHomogeneous (t : Localization.AtPrime P)
    {F : MvPolynomial (Fin (n + 1)) K} {e : ℕ} (hF : F.IsHomogeneous e) :
    beta0 P t F = t ^ e * algebraMap _ (Localization.AtPrime P) (Ideal.Quotient.mk J F) := by
  rw [beta0, aeval_mul_of_isHomogeneous hF]
  congr 1
  exact aeval_algHom_X
    ((IsScalarTower.toAlgHom K _ (Localization.AtPrime P)).comp (Ideal.Quotient.mkₐ K J)) F

/-- The map `beta0` extended to the local ring at `q`. -/
private noncomputable def beta1 (t : Localization.AtPrime P)
    (hunits : ∀ s : (maxIdealAt q).primeCompl, IsUnit (beta0 P t s)) :
    localRingAt q →ₐ[K] Localization.AtPrime P :=
  IsLocalization.liftAlgHom (M := (maxIdealAt q).primeCompl) (f := beta0 P t) hunits

private lemma beta1_algebraMap (t : Localization.AtPrime P)
    (hunits : ∀ s : (maxIdealAt q).primeCompl, IsUnit (beta0 P t s))
    (a : MvPolynomial (Fin (n + 1)) K) :
    beta1 P t hunits (algebraMap _ (localRingAt q) a) = beta0 P t a :=
  IsLocalization.lift_eq _ _

/-- The map `beta1` descended to the quotient by `I`. -/
private noncomputable def beta (t : Localization.AtPrime P)
    (hunits : ∀ s : (maxIdealAt q).primeCompl, IsUnit (beta0 P t s))
    (hI : ∀ a ∈ I, beta1 P t hunits a = 0) :
    localRingAt q ⧸ I →ₐ[K] Localization.AtPrime P :=
  Ideal.Quotient.liftₐ I (beta1 P t hunits) hI

private lemma beta_mk (t : Localization.AtPrime P)
    (hunits : ∀ s : (maxIdealAt q).primeCompl, IsUnit (beta0 P t s))
    (hI : ∀ a ∈ I, beta1 P t hunits a = 0) (x : localRingAt q) :
    beta P I t hunits hI (Ideal.Quotient.mk I x) = beta1 P t hunits x :=
  rfl

/-- `beta ∘ alpha` is the identity of the localization at `P`. -/
private lemma beta_comp_alpha (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hℓJ : Ideal.Quotient.mk J ℓ = 1) (u : localRingAt q)
    (hu : algebraMap _ (localRingAt q) ℓ * u = 1)
    (hJ : ∀ a ∈ J, alpha0 u a ∈ I) (hαu : ∀ y : P.primeCompl, IsUnit (alpha1 I u hJ y))
    (t : Localization.AtPrime P) (hβu : ∀ s : (maxIdealAt q).primeCompl, IsUnit (beta0 P t s))
    (hI : ∀ a ∈ I, beta1 P t hβu a = 0) :
    (beta P I t hβu hI).comp (alpha P I u hJ hαu) = AlgHom.id K _ := by
  have h1 : t * beta1 P t hβu u = 1 := by
    have h := congrArg (beta1 P t hβu) hu
    rwa [map_mul, map_one, beta1_algebraMap, beta0_of_isHomogeneous P t hℓ, hℓJ, map_one,
      pow_one, mul_one] at h
  apply IsLocalization.algHom_ext P.primeCompl
  apply Ideal.Quotient.algHom_ext
  refine MvPolynomial.algHom_ext fun j ↦ ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply, Algebra.algHom,
    IsScalarTower.coe_toAlgHom', alpha_algebraMap, alpha0_X, beta_mk, map_mul, beta1_algebraMap,
    beta0_X]
  rw [mul_assoc, h1, mul_one]

/-- `alpha ∘ beta` is the identity of the quotient of the local ring at `q`. -/
private lemma alpha_comp_beta (i : Fin (n + 1))
    (hXi : Ideal.Quotient.mk I (algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i)) =
      1)
    (u : localRingAt q) (hJ : ∀ a ∈ J, alpha0 u a ∈ I)
    (hαu : ∀ y : P.primeCompl, IsUnit (alpha1 I u hJ y)) (t : Localization.AtPrime P)
    (ht : algebraMap _ (Localization.AtPrime P) (Ideal.Quotient.mk J (X i)) * t = 1)
    (hβu : ∀ s : (maxIdealAt q).primeCompl, IsUnit (beta0 P t s))
    (hI : ∀ a ∈ I, beta1 P t hβu a = 0) :
    (alpha P I u hJ hαu).comp (beta P I t hβu hI) = AlgHom.id K _ := by
  have h1 : Ideal.Quotient.mk I u * alpha P I u hJ hαu t = 1 := by
    have h := congrArg (alpha P I u hJ hαu) ht
    rwa [map_mul, map_one, alpha_algebraMap, alpha0_X, map_mul, hXi, one_mul] at h
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (maxIdealAt q).primeCompl
  refine MvPolynomial.algHom_ext fun j ↦ ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply, Algebra.algHom,
    IsScalarTower.coe_toAlgHom', beta_mk, beta1_algebraMap, beta0_X, map_mul, alpha_algebraMap,
    alpha0_X]
  rw [mul_assoc, h1, mul_one]

/-- Residues in the local ring at `x` are values at `x`. -/
private lemma residue_localRingAt (x : Fin (n + 1) → K) (a : MvPolynomial (Fin (n + 1)) K) :
    IsLocalRing.residue (localRingAt x) (algebraMap _ _ a) = algebraMap K _ (eval x a) :=
  residue_algebraMap_eq (maxIdealAt x) (AlgHom.id K _) x (fun _ h ↦ RingHom.mem_ker.mpr h) a

/-- Residues in the localization at `P` are values at `v`. -/
private lemma residue_atPrime (v : Fin (n + 1) → K)
    (hv : ∀ a, eval v a = 0 → Ideal.Quotient.mk J a ∈ P) (a : MvPolynomial (Fin (n + 1)) K) :
    IsLocalRing.residue (Localization.AtPrime P) (algebraMap _ _ (Ideal.Quotient.mk J a)) =
      algebraMap K _ (eval v a) :=
  residue_algebraMap_eq P (Ideal.Quotient.mkₐ K J) v hv a

private lemma residue_alpha0 (ℓ : MvPolynomial (Fin (n + 1)) K) (u : localRingAt q)
    (hu : algebraMap _ (localRingAt q) ℓ * u = 1) (j : Fin (n + 1)) :
    IsLocalRing.residue (localRingAt q) (alpha0 u (X j)) = algebraMap K _ (q j / eval q ℓ) := by
  have h := congrArg (IsLocalRing.residue (localRingAt q)) hu
  rw [map_mul, map_one, residue_localRingAt] at h
  rw [alpha0_X, map_mul, residue_localRingAt, eval_X, eq_inv_of_mul_eq_one_right h, ← map_inv₀,
    ← map_mul, div_eq_mul_inv]

private lemma residue_beta0 (v : Fin (n + 1) → K)
    (hv : ∀ a, eval v a = 0 → Ideal.Quotient.mk J a ∈ P) (i : Fin (n + 1))
    (t : Localization.AtPrime P)
    (ht : algebraMap _ (Localization.AtPrime P) (Ideal.Quotient.mk J (X i)) * t = 1)
    (j : Fin (n + 1)) :
    IsLocalRing.residue (Localization.AtPrime P) (beta0 P t (X j)) =
      algebraMap K _ (v j / v i) := by
  have h := congrArg (IsLocalRing.residue (Localization.AtPrime P)) ht
  rw [map_mul, map_one, residue_atPrime P v hv, eval_X] at h
  rw [beta0_X, map_mul, residue_atPrime P v hv, eval_X, eq_inv_of_mul_eq_one_right h,
    ← map_inv₀, ← map_mul, div_eq_mul_inv]

/-- Elements outside `P` are sent to units by `alpha1`. -/
private lemma alpha1_isUnit (v : Fin (n + 1) → K)
    (hv : ∀ a, eval v a = 0 → Ideal.Quotient.mk J a ∈ P) (u : localRingAt q)
    (hJ : ∀ a ∈ J, alpha0 u a ∈ I)
    (hres : ∀ j, IsLocalRing.residue (localRingAt q) (alpha0 u (X j)) = algebraMap K _ (v j))
    (y : P.primeCompl) : IsUnit (alpha1 I u hJ y) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y : MvPolynomial (Fin (n + 1)) K ⧸ J)
  have hva : eval v a ≠ 0 := fun h0 ↦ y.2 (ha ▸ hv a h0)
  rw [← ha, alpha1_mk]
  exact (isUnit_of_residue_algHom (alpha0 u) v hres hva).map _

/-- Polynomials not vanishing at `q` are sent to units by `beta0`. -/
private lemma beta0_isUnit (t : Localization.AtPrime P)
    (hres : ∀ j, IsLocalRing.residue (Localization.AtPrime P) (beta0 P t (X j)) =
      algebraMap K _ (q j))
    (s : (maxIdealAt q).primeCompl) : IsUnit (beta0 P t s) :=
  isUnit_of_residue_algHom (R := Localization.AtPrime P) (beta0 P t) q hres (s := s)
    fun h ↦ s.2 (RingHom.mem_ker.mpr h)

end Construction

section Slices

variable {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
  (hd : ∀ k, (f k).IsHomogeneous (d k)) (ℓ : MvPolynomial (Fin (n + 1)) K)

include hd in
private lemma le_comap_alpha0 (hℓ : ℓ.IsHomogeneous 1) {q : Fin (n + 1) → K} (i : Fin (n + 1))
    (u : localRingAt q) (hu : algebraMap _ (localRingAt q) ℓ * u = 1) :
    Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1} ≤
      Ideal.comap (alpha0 u)
        (Ideal.span ((Set.range fun k ↦ algebraMap _ (localRingAt q) (f k)) ∪
          {algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i - C 1)})) := by
  refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, alpha0_of_isHomogeneous u (hd k)]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl ⟨k, rfl⟩))
  · rintro _ rfl
    rw [SetLike.mem_coe, Ideal.mem_comap, map_sub (alpha0 u), map_one (alpha0 u),
      alpha0_of_isHomogeneous u hℓ, pow_one, mul_comm, hu, sub_self]
    exact Ideal.zero_mem _

include hd in
private lemma le_ker_beta1
    (P : Ideal (MvPolynomial (Fin (n + 1)) K ⧸ (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1})))
    [P.IsPrime] {q : Fin (n + 1) → K} (i : Fin (n + 1)) (t : Localization.AtPrime P)
    (ht : algebraMap _ (Localization.AtPrime P)
      (Ideal.Quotient.mk (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}) (X i)) * t = 1)
    (hβu : ∀ s : (maxIdealAt q).primeCompl, IsUnit (beta0 P t s)) :
    Ideal.span ((Set.range fun k ↦ algebraMap _ (localRingAt q) (f k)) ∪
        {algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i - C 1)}) ≤
      RingHom.ker (beta1 P t hβu) := by
  refine Ideal.span_le.mpr ?_
  rintro _ (⟨k, rfl⟩ | rfl)
  · have hk : Ideal.Quotient.mk (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}) (f k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.subset_span ⟨k, rfl⟩))
    rw [SetLike.mem_coe, RingHom.mem_ker, beta1_algebraMap, beta0_of_isHomogeneous P t (hd k), hk,
      map_zero, mul_zero]
  · rw [SetLike.mem_coe, RingHom.mem_ker, beta1_algebraMap, map_sub, C_1, map_one, beta0_X, ht,
      sub_self]

include hd in
/-- The local ring at `q` cut by the `f k` and `X i - 1` is isomorphic to the localization at `P`
of the slice `ℓ = 1`. -/
private lemma nonempty_algEquiv (hℓ : ℓ.IsHomogeneous 1)
    (P : Ideal (MvPolynomial (Fin (n + 1)) K ⧸ (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1})))
    [P.IsPrime] (v q : Fin (n + 1) → K) (i : Fin (n + 1))
    (hv : ∀ a, eval v a = 0 → Ideal.Quotient.mk _ a ∈ P) (hℓq : eval q ℓ ≠ 0) (hvi : v i ≠ 0)
    (hqv : ∀ j, q j / eval q ℓ = v j) (hvq : ∀ j, v j / v i = q j) :
    Nonempty ((localRingAt q ⧸
        Ideal.span ((Set.range fun k ↦ algebraMap _ (localRingAt q) (f k)) ∪
          {algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i - C 1)})) ≃ₐ[K]
      Localization.AtPrime P) := by
  have hL : IsUnit (algebraMap _ (localRingAt q) ℓ) := IsLocalization.map_units (localRingAt q)
    (⟨ℓ, fun h ↦ hℓq (RingHom.mem_ker.mp h)⟩ : (maxIdealAt q).primeCompl)
  obtain ⟨u, hu⟩ := hL.exists_right_inv
  have hT : IsUnit (algebraMap _ (Localization.AtPrime P)
      (Ideal.Quotient.mk (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}) (X i))) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit (R := Localization.AtPrime P) _).mp ?_
    rw [residue_atPrime P v hv, eval_X]
    exact (map_ne_zero_iff _ (algebraMap K _).injective).mpr hvi
  obtain ⟨t, ht⟩ := hT.exists_right_inv
  have hℓJ : Ideal.Quotient.mk (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}) ℓ = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  have hXi : Ideal.Quotient.mk
      (Ideal.span ((Set.range fun k ↦ algebraMap _ (localRingAt q) (f k)) ∪
        {algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i - C 1)}))
      (algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i)) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
      show algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i) - 1 =
        algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (X i - C 1) by
        rw [map_sub, C_1, map_one]]
    exact Ideal.subset_span (Or.inr rfl)
  have hJ : ∀ a ∈ Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}, alpha0 u a ∈ _ :=
    fun a ha ↦ Ideal.mem_comap.mp (le_comap_alpha0 f d hd ℓ hℓ i u hu ha)
  have hαu := alpha1_isUnit P _ v hv u hJ fun j ↦ (residue_alpha0 ℓ u hu j).trans (by rw [hqv])
  have hβu := beta0_isUnit P t fun j ↦ (residue_beta0 P v hv i t ht j).trans (by rw [hvq])
  have hI : ∀ a ∈ Ideal.span _, beta1 P t hβu a = 0 :=
    fun a ha ↦ RingHom.mem_ker.mp (le_ker_beta1 f d hd ℓ P i t ht hβu ha)
  exact ⟨AlgEquiv.ofAlgHom (beta P _ t hβu hI) (alpha P _ u hJ hαu)
    (beta_comp_alpha P _ ℓ hℓ hℓJ u hu hJ hαu t hβu hI)
    (alpha_comp_beta P _ i hXi u hJ hαu t ht hβu hI)⟩

end Slices

section Length

variable {n : ℕ}

/-- The residue field of the local ring at `q` is `K`. -/
private lemma length_residueField_localRingAt (q : Fin (n + 1) → K) :
    Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField (localRingAt q)) = 1 := by
  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField (localRingAt q))) := by
    intro x
    obtain ⟨a, rfl⟩ := (maxIdealAt q).algebraMap_residueField_surjective x
    refine ⟨algebraMap K _ (eval q a), ?_⟩
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin (n + 1)) K) (localRingAt q)
        (IsLocalRing.ResidueField (localRingAt q)) a,
      IsLocalRing.ResidueField.algebraMap_eq, residue_localRingAt]
  rw [Module.length_eq_rank, Module.rank_of_bijective_algebraMap ⟨RingHom.injective _, hsurj⟩]
  simp

/-- A quotient of the local ring at `q` that is isomorphic to a finite-dimensional `K`-algebra has
length equal to the dimension of that algebra. -/
private lemma length_eq_finrank_of_algEquiv {q : Fin (n + 1) → K} (I : Ideal (localRingAt q))
    {B : Type*} [CommRing B] [Algebra K B] [Module.Finite K B]
    (e : (localRingAt q ⧸ I) ≃ₐ[K] B) :
    Module.length (localRingAt q) (localRingAt q ⧸ I) = Module.finrank K B := by
  have h := IsLocalRing.length_restrictScalars K (localRingAt q) (localRingAt q ⧸ I)
  rw [length_residueField_localRingAt, mul_one] at h
  rw [← h, e.toLinearEquiv.length_eq, Module.length_eq_finrank]

/-- Localizations of a finite-dimensional algebra are finite-dimensional. -/
private lemma finite_atPrime {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    (P : Ideal A) [P.IsPrime] : Module.Finite K (Localization.AtPrime P) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K A (Localization.AtPrime P)).toLinearMap
    (IsArtinianRing.localization_surjective P.primeCompl _)

end Length

/-- The intersection multiplicity at `p` is the dimension of the localization at `p` of the
slice `ℓ = 1` of the affine cone, for any linear form `ℓ` with `ℓ(p) ≠ 0`. -/
private theorem intersectionMultiplicity_eq_finrank {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}))]
    (p : ProjSpace K n) (hℓp : eval p.rep ℓ ≠ 0)
    (P : Ideal (MvPolynomial (Fin (n + 1)) K ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}))) [P.IsPrime]
    (hP : P = (maxIdealAt ((eval p.rep ℓ)⁻¹ • p.rep)).map (Ideal.Quotient.mk _)) :
    intersectionMultiplicity f p = (Module.finrank K (Localization.AtPrime P) : ℕ∞) := by
  have : Module.Finite K (Localization.AtPrime P) := finite_atPrime P
  have hw : p.rep (chartIndex p) ≠ 0 := chartIndex_rep_ne_zero p
  have hq : affineConeCoord p = (p.rep (chartIndex p))⁻¹ • p.rep := by
    funext j
    simp [affineConeCoord, div_eq_inv_mul]
  have hℓq : eval (affineConeCoord p) ℓ = (p.rep (chartIndex p))⁻¹ * eval p.rep ℓ := by
    rw [hq, hℓ.eval_smul, pow_one]
  have hv : ∀ a, eval ((eval p.rep ℓ)⁻¹ • p.rep) a = 0 →
      Ideal.Quotient.mk (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}) a ∈ P := by
    intro a h
    rw [hP]
    exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr h)
  have h1 : eval (affineConeCoord p) ℓ ≠ 0 := by
    rw [hℓq]
    exact mul_ne_zero (inv_ne_zero hw) hℓp
  have h2 : ((eval p.rep ℓ)⁻¹ • p.rep) (chartIndex p) ≠ 0 := mul_ne_zero (inv_ne_zero hℓp) hw
  have h3 : ∀ j, affineConeCoord p j / eval (affineConeCoord p) ℓ =
      ((eval p.rep ℓ)⁻¹ • p.rep) j := by
    intro j
    rw [hℓq]
    simp only [affineConeCoord, Pi.smul_apply, smul_eq_mul]
    field_simp
  have h4 : ∀ j, ((eval p.rep ℓ)⁻¹ • p.rep) j / ((eval p.rep ℓ)⁻¹ • p.rep) (chartIndex p) =
      affineConeCoord p j := by
    intro j
    simp only [affineConeCoord, Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨e⟩ := nonempty_algEquiv f d hd ℓ hℓ P ((eval p.rep ℓ)⁻¹ • p.rep) (affineConeCoord p)
    (chartIndex p) hv h1 h2 h3 h4
  exact length_eq_finrank_of_algEquiv (B := Localization.AtPrime P) _ e

end BezoutChart

/-! ### Assembling the proof -/

/-- A linear form `∑ j, t ^ j X_j` avoiding finitely many projective points. -/
private theorem exists_linear_form [Infinite K] {n : ℕ} (Z : Set (ProjSpace K n)) (hZ : Z.Finite) :
    ∃ ℓ : MvPolynomial (Fin (n + 1)) K, ℓ.IsHomogeneous 1 ∧
      ∀ p ∈ Z, eval (Projectivization.rep p) ℓ ≠ 0 := by
  classical
  let g : ProjSpace K n → Polynomial K := fun p =>
    ∑ j : Fin (n + 1), Polynomial.C (Projectivization.rep p j) * Polynomial.X ^ (j : ℕ)
  have hcoeff : ∀ p (i : Fin (n + 1)), (g p).coeff i = Projectivization.rep p i := by
    intro p i
    simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact ite_eq_right_iff.mpr fun h => absurd (Fin.ext h.symm) hji
    · simp
  have hg : ∀ p, g p ≠ 0 := by
    intro p hp
    apply Projectivization.rep_ne_zero p
    funext i
    rw [← hcoeff p i, hp, Polynomial.coeff_zero, Pi.zero_apply]
  have hbad : (⋃ p ∈ Z, {t : K | (g p).eval t = 0}).Finite :=
    hZ.biUnion fun p _ => Polynomial.finite_setOfPred_isRoot (hg p)
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  refine ⟨∑ j : Fin (n + 1), C (t ^ (j : ℕ)) * X j, ?_, ?_⟩
  · exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _
  · intro p hp
    have hval : eval (Projectivization.rep p) (∑ j : Fin (n + 1), C (t ^ (j : ℕ)) * X j) =
        (g p).eval t := by
      simp only [g, map_sum, map_mul, eval_C, eval_X, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hval]
    intro h0
    exact ht (Set.mem_biUnion hp h0)

/-- The scaled representative `ℓ(v)⁻¹ • v` of a point lies on the slice `ℓ = 1`. -/
private theorem eval_slice {n : ℕ} (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (v : Fin (n + 1) → K) (hv : eval v ℓ ≠ 0) : eval ((eval v ℓ)⁻¹ • v) ℓ = 1 := by
  rw [hℓ.eval_smul, pow_one, inv_mul_cancel₀ hv]

private theorem eval_smul_eq_zero {n : ℕ} {g : MvPolynomial (Fin (n + 1)) K} {e : ℕ}
    (hg : g.IsHomogeneous e) (c : K) (v : Fin (n + 1) → K) (hv : eval v g = 0) :
    eval (c • v) g = 0 := by
  rw [hg.eval_smul, hv, mul_zero]

private theorem maxIdealAt_eq_vanishingIdeal {n : ℕ} (x : Fin (n + 1) → K) :
    maxIdealAt x = vanishingIdeal K {x} := by
  ext g
  rw [mem_vanishingIdeal_singleton_iff]
  simp [maxIdealAt, evalAt, RingHom.mem_ker]

private theorem eq_of_maxIdealAt_eq {n : ℕ} {x y : Fin (n + 1) → K}
    (h : maxIdealAt x = maxIdealAt y) : x = y := by
  funext j
  have hx : X j - C (x j) ∈ maxIdealAt x := by
    simp [maxIdealAt, evalAt, RingHom.mem_ker]
  rw [h] at hx
  have hx' : y j - x j = 0 := by simpa [maxIdealAt, evalAt, RingHom.mem_ker] using hx
  exact (sub_eq_zero.mp hx').symm

private theorem mk_smul_rep {n : ℕ} (p : ProjSpace K n) {c : K} (hc : c ≠ 0) :
    Projectivization.mk K (c • p.rep) (smul_ne_zero hc p.rep_ne_zero) = p := by
  conv_rhs => rw [← Projectivization.mk_rep p]
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨c, rfl⟩

private theorem eval_zero_of_isHomogeneous_one {n : ℕ} {ℓ : MvPolynomial (Fin (n + 1)) K}
    (hℓ : ℓ.IsHomogeneous 1) : eval (0 : Fin (n + 1) → K) ℓ = 0 := by
  simpa using hℓ.eval_smul (0 : K) (0 : Fin (n + 1) → K)

private theorem sum_eq_finrank [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k))
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hℓZ : ∀ p ∈ ⋂ k, vanishingSet (f k), eval p.rep ℓ ≠ 0)
    [Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1}))]
    (hfin : (⋂ k, vanishingSet (f k)).Finite) :
    ∑ᶠ p ∈ (⋂ k, vanishingSet (f k)), intersectionMultiplicity f p
      = (Module.finrank K (MvPolynomial (Fin (n + 1)) K ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1})) : ℕ∞) := by
  classical
  set J' : Ideal (MvPolynomial (Fin (n + 1)) K) :=
    Ideal.span (Set.range f) ⊔ Ideal.span {ℓ - 1} with hJ'
  set A := MvPolynomial (Fin (n + 1)) K ⧸ J'
  set Z := ⋂ k, vanishingSet (f k) with hZ
  let v : ProjSpace K n → Fin (n + 1) → K := fun p => (eval p.rep ℓ)⁻¹ • p.rep
  have hmemZ : ∀ p, p ∈ Z ↔ ∀ k, eval p.rep (f k) = 0 := by
    intro p
    simp [hZ, vanishingSet, Set.mem_iInter]
  have hJ'le : ∀ p ∈ Z, J' ≤ maxIdealAt (v p) := by
    intro p hp
    rw [hJ', sup_le_iff, Ideal.span_le, Ideal.span_le]
    constructor
    · rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, maxIdealAt, evalAt, RingHom.mem_ker]
      exact eval_smul_eq_zero (hd k) _ _ ((hmemZ p).1 hp k)
    · intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      simp only [SetLike.mem_coe, maxIdealAt, evalAt, RingHom.mem_ker, map_sub, map_one]
      rw [eval_slice ℓ hℓ _ (hℓZ p hp), sub_self]
  let P : ProjSpace K n → Ideal A := fun p => (maxIdealAt (v p)).map (Ideal.Quotient.mk J')
  have hker : ∀ p ∈ Z, RingHom.ker (Ideal.Quotient.mk J') ≤ maxIdealAt (v p) := by
    intro p hp
    rw [Ideal.mk_ker]
    exact hJ'le p hp
  have hcomap : ∀ p ∈ Z, (P p).comap (Ideal.Quotient.mk J') = maxIdealAt (v p) := by
    intro p hp
    exact Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective _ |>.trans
      (sup_eq_left.mpr (hker p hp))
  have hPmax : ∀ p ∈ Z, (P p).IsMaximal := by
    intro p hp
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      (maxIdealAt_isMaximal (v p))).resolve_left fun htop => ?_
    have h := hcomap p hp
    rw [show P p = ⊤ from htop, Ideal.comap_top] at h
    exact (maxIdealAt_isMaximal (v p)).ne_top h.symm
  have hmk : ∀ p (hp : p ∈ Z), Projectivization.mk K (v p)
      (smul_ne_zero (inv_ne_zero (hℓZ p hp)) p.rep_ne_zero) = p :=
    fun p hp => mk_smul_rep p (inv_ne_zero (hℓZ p hp))
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    IsArtinianRing.finrank_eq_sum_primeSpectrum A K, Nat.cast_sum]
  refine Finset.sum_bij (fun p hp => (⟨P p, (hPmax p (hfin.mem_toFinset.mp hp)).isPrime⟩ :
    PrimeSpectrum A)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro p hp p' hp' hpp'
    rw [Set.Finite.mem_toFinset] at hp hp'
    have h1 : P p = P p' := congrArg PrimeSpectrum.asIdeal hpp'
    have h2 : v p = v p' := eq_of_maxIdealAt_eq (by rw [← hcomap p hp, ← hcomap p' hp', h1])
    rw [← hmk p hp, ← hmk p' hp']
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨1, by rw [one_smul]; exact h2.symm⟩
  · intro Q _
    have hQmax : Q.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime Q.asIdeal
    have hMmax : (Q.asIdeal.comap (Ideal.Quotient.mk J')).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hMmax
    have hJ'M : ∀ g ∈ J', aeval x g = 0 := by
      intro g hg
      have hg' : g ∈ Q.asIdeal.comap (Ideal.Quotient.mk J') := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hg]
        exact Q.asIdeal.zero_mem
      rw [hx] at hg'
      exact (mem_vanishingIdeal_singleton_iff x g).mp hg'
    have hfx : ∀ k, eval x (f k) = 0 := by
      intro k
      have := hJ'M (f k) (Ideal.mem_sup_left (Ideal.subset_span ⟨k, rfl⟩))
      simpa [MvPolynomial.coe_aeval_eq_eval] using this
    have hℓx : eval x ℓ = 1 := by
      have := hJ'M (ℓ - 1) (Ideal.mem_sup_right (Ideal.subset_span rfl))
      have h' : eval x ℓ - 1 = 0 := by simpa [MvPolynomial.coe_aeval_eq_eval] using this
      exact sub_eq_zero.mp h'
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [eval_zero_of_isHomogeneous_one hℓ] at hℓx
      exact zero_ne_one hℓx
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K x hx0
    set p := Projectivization.mk K x hx0 with hp_def
    have ha' : p.rep = (a : K) • x := by rw [← ha, Units.smul_def]
    have hpZ : p ∈ Z := by
      rw [hmemZ]
      intro k
      rw [ha']
      exact eval_smul_eq_zero (hd k) _ _ (hfx k)
    have hvp : v p = x := by
      simp only [v]
      rw [ha', hℓ.eval_smul, hℓx, pow_one, mul_one, smul_smul, inv_mul_cancel₀ a.ne_zero,
        one_smul]
    refine ⟨p, hfin.mem_toFinset.mpr hpZ, ?_⟩
    ext1
    change P p = Q.asIdeal
    simp only [P, hvp, maxIdealAt_eq_vanishingIdeal, ← hx]
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  · intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    have := (hPmax p hp).isPrime
    exact BezoutChart.intersectionMultiplicity_eq_finrank f d hd ℓ hℓ p (hℓZ p hp) (P p) rfl

/- **Bézout's theorem (with multiplicity).** Given `n` homogeneous
polynomials `f_k` in `n + 1` variables, each of total degree exactly
`d_k ≥ 1`, over an algebraically closed field with finite common
projective zero set, the sum of intersection multiplicities equals
`∏ d_k`. The `totalDegree` hypothesis rules out the zero polynomial
(which is `IsHomogeneous d` for every `d` but has `totalDegree = 0`). -/
set_option linter.dupNamespace false in
/-- **Bézout's theorem (with multiplicity).** Let $K$ be an algebraically closed field, let
$n \in \mathbb{N}$, and let $f_1, \dots, f_n \in K[X_0, \dots, X_n]$ and integers
$d_1, \dots, d_n \ge 1$ be such that each $f_k$ is homogeneous of degree $d_k$ and has total
degree exactly $d_k$. Suppose the common projective zero set
$Z = V(f_1) \cap \dots \cap V(f_n) \subseteq \mathbb{P}^n(K)$ is finite. Then
$\sum_{p \in Z} i_p(f_1, \dots, f_n) = d_1 d_2 \cdots d_n$ in $\mathbb{N} \cup \{\infty\}$,
where $i_p(f_1, \dots, f_n)$ is the intersection multiplicity of $f_1, \dots, f_n$ at $p$.

The total degree hypothesis rules out $f_k = 0$, which is homogeneous of every degree but has
total degree $0$.

Source: É. Bézout, *Théorie générale des équations algébriques*, Paris, 1779. Modern projective
formulation: see Eisenbud, *Commutative Algebra*, Chapter 12, or Hartshorne, *Algebraic Geometry*,
Ch. I §7. Listed as §50 in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `bezout_projective_multiplicity`. -/
theorem bezout_multiplicity [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (d : Fin n → ℕ) (_hd : ∀ k, (f k).IsHomogeneous (d k))
    (_hdeg : ∀ k, (f k).totalDegree = d k)
    (_hd_pos : ∀ k, 1 ≤ d k)
    (_hfin : (⋂ k, vanishingSet (f k)).Finite) :
    ∑ᶠ p ∈ (⋂ k, vanishingSet (f k)), intersectionMultiplicity f p
      = (∏ k, d k : ℕ∞) := by
  obtain ⟨ℓ, hℓ, hℓZ⟩ := exists_linear_form _ _hfin
  have hzero : ∀ v : Fin (n + 1) → K, (∀ k, eval v (f k) = 0) → eval v ℓ = 0 → v = 0 := by
    intro v hv hℓv
    by_contra hv0
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv0
    set p := Projectivization.mk K v hv0
    have ha' : p.rep = (a : K) • v := by rw [← ha, Units.smul_def]
    have hpZ : p ∈ ⋂ k, vanishingSet (f k) := by
      simp only [Set.mem_iInter, vanishingSet, Set.mem_ofPred_eq]
      intro k
      rw [ha']
      exact eval_smul_eq_zero (_hd k) _ _ (hv k)
    apply hℓZ p hpZ
    rw [ha']
    exact eval_smul_eq_zero hℓ _ _ hℓv
  obtain ⟨hreg, hℓreg⟩ := BezoutRegular.regular_of_zero_only f d _hd _hd_pos ℓ hℓ hzero
  obtain ⟨hfinite, hrank⟩ := BezoutHilbert.finrank_quotient_eq_prod f d _hd hreg ℓ hℓ hℓreg
  rw [sum_eq_finrank f d _hd ℓ hℓ hℓZ _hfin, hrank, Nat.cast_prod]

end AlgebraicGeometry

end MathlibExt.AlgebraicGeometry.BezoutWanted
