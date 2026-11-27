/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.RamifiedPrimes

/-!
# The reduced-trace sets $S_{a,b}$ and reduced characteristic polynomials

For $a, b$ in a field $K$, `QuaternionAlgebra.reducedTraceSet K a b` is the set of reduced traces
$2x_1$ of the elements $x_1 + x_2 i + x_3 j + x_4 ij$ of reduced norm
$x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2 = 1$ of the quaternion algebra `ℍ[K,a,b]`. For
$a, b \in \mathbb{Q}^\times$ it is B. Poonen's $S_{a,b}$ when $K = \mathbb{Q}$ and his
$S_{a,b}(\mathbb{Q}_p)$ when $K = \mathbb{Q}_p$.

The results, for an element $\alpha$ of `ℍ[K,a,b]` with reduced characteristic polynomial
$x^2 - \operatorname{trd}(\alpha)\, x + \operatorname{nrd}(\alpha)$:

* `QuaternionAlgebra.sq_sub_two_mul_re_mul_add_normForm`: $\alpha$ is a root of it;
* `QuaternionAlgebra.eq_reducedCharpoly_of_aeval_eq_zero`: for $\alpha \notin K$, every monic
  $g \in K[x]$ of degree $2$ with $g(\alpha) = 0$ is it;
* `QuaternionAlgebra.mem_reducedTraceSet_iff_exists_reducedCharpoly`: $s \in S_{a,b}$ exactly when
  $x^2 - sx + 1$ is the reduced characteristic polynomial of some $\alpha$;
* `QuaternionAlgebra.exists_reducedCharpoly_eq_of_nonempty_algEquiv` and
  `Rat.exists_reducedCharpoly_eq_of_not_mem_quaternionRamifiedPrimes`: if the algebra splits, in
  particular at a prime $p \notin \Delta_{a,b}$ over $\mathbb{Q}_p$, every monic quadratic is a
  reduced characteristic polynomial;
* `Rat.reducedTraceSet_padic_eq_univ_of_not_mem_quaternionRamifiedPrimes`: so
  $S_{a,b}(\mathbb{Q}_p) = \mathbb{Q}_p$ for $p \notin \Delta_{a,b}$, part (i) of Poonen's
  Lemma 2.1.
-/

set_option autoImplicit false

@[expose] public section

open scoped Quaternion

open Polynomial

namespace QuaternionAlgebra

variable {K : Type*} [Field K]

variable (K) in
/-- **The reduced-trace sets $S_{a,b}$.** For $a, b$ in a field $K$, the set of reduced traces of
the elements of reduced norm $1$ of the quaternion algebra `ℍ[K,a,b]`, with $i^2 = a$,
$j^2 = b$ and $ij = -ji$:
$\{2x_1 : x_1, x_2, x_3, x_4 \in K,\ x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2 = 1\}$.

For $a, b \in \mathbb{Q}^\times$, this is Poonen's $S_{a,b}$ for $K = \mathbb{Q}$, and his
$S_{a,b}(\mathbb{Q}_p)$, defined in the same way for $H_{a,b} \otimes \mathbb{Q}_p$, for
$K = \mathbb{Q}_p$ (`reducedTraceSet ℚ_[p] a b`). The definition makes sense for all $a, b$ in any
field.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, §2, p. 2 of the author's version with the corrections
of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "Let $S_{a,b}$ be the set of
reduced traces of elements of $H_{a,b}$ of reduced norm 1. For $p \in \mathcal{P}$, define
$S_{a,b}(\mathbb{Q}_p)$ similarly for $H_{a,b} \otimes \mathbb{Q}_p$." The reduced trace $2x_1$ and
reduced norm $x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2$ are $x + \bar x$ and $x \bar x$ for the
conjugate $\bar x$ (`star`), as in the formula of Poonen's Theorem 3.1, p. 4. -/
def reducedTraceSet (a b : K) : Set K :=
  {s | ∃ x₁ x₂ x₃ x₄ : K, x₁ ^ 2 - a * x₂ ^ 2 - b * x₃ ^ 2 + a * b * x₄ ^ 2 = 1 ∧ 2 * x₁ = s}

/-- **$S_{a,b}$ is symmetric.** For $a, b$ in a field $K$ and $s \in K$, $-s \in S_{a,b}$ if and
only if $s \in S_{a,b}$, since $\operatorname{nrd}(-x) = \operatorname{nrd}(x)$ and
$\operatorname{trd}(-x) = -\operatorname{trd}(x)$. -/
theorem neg_mem_reducedTraceSet_iff {a b s : K} :
    -s ∈ reducedTraceSet K a b ↔ s ∈ reducedTraceSet K a b := by
  constructor
  · rintro ⟨x₁, x₂, x₃, x₄, h, hs⟩
    exact ⟨-x₁, -x₂, -x₃, -x₄, by linear_combination h, by linear_combination -hs⟩
  · rintro ⟨x₁, x₂, x₃, x₄, h, hs⟩
    exact ⟨-x₁, -x₂, -x₃, -x₄, by linear_combination h, by linear_combination -hs⟩

/-- **An element of $H_{a,b}$ is a root of its reduced characteristic polynomial.** In the
quaternion algebra `ℍ[R,a,b]` over a commutative ring $R$, every
$\alpha = x_1 + x_2 i + x_3 j + x_4 ij$ satisfies
$\alpha^2 - \operatorname{trd}(\alpha)\, \alpha + \operatorname{nrd}(\alpha) = 0$, with
$\operatorname{trd}(\alpha) = 2x_1$ and
$\operatorname{nrd}(\alpha) = x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2$.

The source states this for $H_{a,b} \otimes \mathbb{Q}_p$; it holds over every commutative ring.

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
<https://doi.org/10.1007/978-3-030-56694-4>, 3.3.9, p. 39 (an element of a quaternion algebra is a
root of its reduced characteristic polynomial), as cited for the first sentence of the proof of
Lemma 2.1 of B. Poonen, "Characterizing integers among rational numbers with a
universal-existential formula", Amer. J. Math. 131 (2009), 675–682: "We have
$s \in S_{a,b}(\mathbb{Q}_p)$ if and only if $x^2 - sx + 1$ is the reduced characteristic polynomial
of an element of $H_{a,b} \otimes \mathbb{Q}_p$." -/
theorem sq_sub_two_mul_re_mul_add_normForm {R : Type*} [CommRing R] {a b : R}
    (α : ℍ[R,a,b]) :
    α ^ 2 - algebraMap R ℍ[R,a,b] (2 * α.re) * α +
      algebraMap R ℍ[R,a,b] (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) =
      0 := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, pow_two] <;> ring

/-- **For $\alpha \notin K$, a monic quadratic vanishing at $\alpha$ is its reduced characteristic
polynomial.** Let $a, b$ be elements of a field $K$ and let $\alpha \in$ `ℍ[K,a,b]` not lie in
$K$. If $g \in K[x]$ is monic of degree $2$ with $g(\alpha) = 0$, then
$g = x^2 - \operatorname{trd}(\alpha)\, x + \operatorname{nrd}(\alpha)$, with
$\operatorname{trd}(\alpha) = 2x_1$ and
$\operatorname{nrd}(\alpha) = x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2$ for
$\alpha = x_1 + x_2 i + x_3 j + x_4 ij$.

The proof: $g$ minus the reduced characteristic polynomial has degree at most $1$ and vanishes at
$\alpha$, so it is $0$ as $\alpha \notin K$. The source states this for
$H_{a,b} \otimes \mathbb{Q}_p$; it holds over every field.

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
<https://doi.org/10.1007/978-3-030-56694-4>, 3.3.9, p. 39 (for $\alpha$ outside the base field the
reduced characteristic polynomial is the minimal polynomial of $\alpha$). -/
theorem eq_reducedCharpoly_of_aeval_eq_zero {a b : K} {α : ℍ[K,a,b]}
    (hα : α ∉ Set.range (algebraMap K ℍ[K,a,b])) {g : K[X]} (hg : g.Monic)
    (hdeg : g.natDegree = 2) (h : aeval α g = 0) :
    g = X ^ 2 - C (2 * α.re) * X +
      C (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) := by
  set h' : K[X] := X ^ 2 - C (2 * α.re) * X +
    C (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) with hh'
  have hh'm : h'.Monic := by rw [hh']; monicity!
  have hh'd : h'.natDegree = 2 := by rw [hh']; compute_degree!
  have hh'a : aeval α h' = 0 := by
    rw [hh']
    simpa [Algebra.smul_def] using sq_sub_two_mul_re_mul_add_normForm α
  set d := g - h' with hd
  have hdeg' : d.degree ≤ 1 := by
    have hlt := degree_sub_lt_left (p := g) (q := h')
      (by rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hh'm.ne_zero, hdeg, hh'd])
      hg.ne_zero (by rw [hg.leadingCoeff, hh'm.leadingCoeff])
    rw [degree_eq_natDegree hg.ne_zero, hdeg] at hlt
    exact Order.le_of_lt_succ hlt
  have hda : aeval α d = 0 := by rw [hd, map_sub, h, hh'a, sub_zero]
  have hdeq := eq_X_add_C_of_degree_le_one hdeg'
  rw [hdeq] at hda
  simp only [map_add, map_mul, aeval_C, aeval_X] at hda
  have h1 : d.coeff 1 = 0 := by
    by_contra h1
    apply hα
    refine ⟨-(d.coeff 1)⁻¹ * d.coeff 0, ?_⟩
    have hu : algebraMap K ℍ[K,a,b] (d.coeff 1) * α =
        -algebraMap K ℍ[K,a,b] (d.coeff 0) := eq_neg_of_add_eq_zero_left hda
    have hinv :
        algebraMap K ℍ[K,a,b] (d.coeff 1)⁻¹ * algebraMap K ℍ[K,a,b] (d.coeff 1) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ h1, map_one]
    calc algebraMap K ℍ[K,a,b] (-(d.coeff 1)⁻¹ * d.coeff 0)
        = algebraMap K ℍ[K,a,b] (d.coeff 1)⁻¹ * -algebraMap K ℍ[K,a,b] (d.coeff 0) := by
          rw [map_mul, map_neg, neg_mul, mul_neg]
      _ = α := by rw [← hu, ← mul_assoc, hinv, one_mul]
  have h0 : d.coeff 0 = 0 := by
    rw [h1, map_zero, zero_mul, zero_add] at hda
    exact (map_eq_zero_iff _ (algebraMap K ℍ[K,a,b]).injective).1 hda
  have hd0 : d = 0 := by rw [hdeq, h1, h0, map_zero, zero_mul, zero_add]
  exact sub_eq_zero.1 hd0

/-- **$S_{a,b}$ by reduced characteristic polynomials.** For $a, b$ in a field $K$ and $s \in K$,
$s \in S_{a,b}$ if and only if $x^2 - sx + 1$ is the reduced characteristic polynomial
$x^2 - \operatorname{trd}(\alpha)\, x + \operatorname{nrd}(\alpha)$ of some
$\alpha \in$ `ℍ[K,a,b]`, with $\operatorname{trd}(\alpha) = 2x_1$ and
$\operatorname{nrd}(\alpha) = x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2$ for
$\alpha = x_1 + x_2 i + x_3 j + x_4 ij$.

The source states this for $K = \mathbb{Q}_p$; it holds over every field.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.1, first sentence, p. 2 of the
author's version with the corrections of April 15, 2019
(<https://math.mit.edu/~poonen/papers/ae.pdf>): "We have $s \in S_{a,b}(\mathbb{Q}_p)$ if and only
if $x^2 - sx + 1$ is the reduced characteristic polynomial of an element of
$H_{a,b} \otimes \mathbb{Q}_p$." -/
theorem mem_reducedTraceSet_iff_exists_reducedCharpoly {a b s : K} :
    s ∈ reducedTraceSet K a b ↔ ∃ α : ℍ[K,a,b],
      X ^ 2 - C (2 * α.re) * X +
        C (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) =
      (X ^ 2 - C s * X + 1 : K[X]) := by
  constructor
  · rintro ⟨x₁, x₂, x₃, x₄, h, rfl⟩
    refine ⟨⟨x₁, x₂, x₃, x₄⟩, ?_⟩
    simp only
    rw [h, C_1]
  · rintro ⟨α, hα⟩
    have h1 := congrArg (fun q : K[X] => q.coeff 1) hα
    have h0 := congrArg (fun q : K[X] => q.coeff 0) hα
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, coeff_one,
      coeff_X_zero] at h1 h0
    norm_num at h1 h0
    exact ⟨α.re, α.imI, α.imJ, α.imK, h0, h1⟩

/-- **In a split quaternion algebra every monic quadratic is a reduced characteristic
polynomial.** Let $a, b$ be elements of a field $K$ such that `ℍ[K,a,b]` is isomorphic to the
matrix algebra $M_2(K)$. Then every monic $f \in K[x]$ of degree $2$ is the reduced characteristic
polynomial $x^2 - \operatorname{trd}(\alpha)\, x + \operatorname{nrd}(\alpha)$ of some
$\alpha \in$ `ℍ[K,a,b]`.

The proof: for $f = x^2 + c_1 x + c_0$, the companion matrix
$C = \begin{pmatrix} 0 & -c_0 \\ 1 & -c_1 \end{pmatrix}$ satisfies $f(C) = 0$ and is not scalar, so
its preimage $\alpha$ lies outside $K$ and $f(\alpha) = 0$; then $f$ is the reduced characteristic
polynomial of $\alpha$ (`QuaternionAlgebra.eq_reducedCharpoly_of_aeval_eq_zero`).

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.1(i), p. 3 of the author's version
with the corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "If
$p \notin \Delta_{a,b}$, then $H_{a,b} \otimes \mathbb{Q}_p \simeq M_2(\mathbb{Q}_p)$, and any monic
quadratic polynomial is a characteristic polynomial." The source states this over $\mathbb{Q}_p$;
it holds over every field. -/
theorem exists_reducedCharpoly_eq_of_nonempty_algEquiv {a b : K}
    (hsplit : Nonempty (ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)) {f : K[X]} (hf : f.Monic)
    (hdeg : f.natDegree = 2) :
    ∃ α : ℍ[K,a,b], f = X ^ 2 - C (2 * α.re) * X +
      C (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) := by
  obtain ⟨φ⟩ := hsplit
  -- `f = X ^ 2 + C c₁ * X + C c₀`.
  set d := f - X ^ 2 with hd
  have hdeg' : d.degree ≤ 1 := by
    have hX : (X ^ 2 : K[X]).Monic := monic_X_pow 2
    have hlt := degree_sub_lt_left (p := f) (q := X ^ 2)
      (by rw [degree_eq_natDegree hf.ne_zero, hdeg, degree_X_pow]) hf.ne_zero
      (by rw [hf.leadingCoeff, hX.leadingCoeff])
    rw [degree_eq_natDegree hf.ne_zero, hdeg] at hlt
    exact Order.le_of_lt_succ hlt
  set c₁ := d.coeff 1
  set c₀ := d.coeff 0
  have hfeq : f = X ^ 2 + C c₁ * X + C c₀ := by
    have := eq_X_add_C_of_degree_le_one hdeg'
    rw [hd] at this
    linear_combination this
  -- The companion matrix.
  set M : Matrix (Fin 2) (Fin 2) K := !![0, -c₀; 1, -c₁] with hM
  have hMf : aeval M f = 0 := by
    rw [hfeq]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, pow_two, Matrix.mul_apply, Matrix.algebraMap_matrix_apply]
    ring
  set α := φ.symm M with hαdef
  have hαf : aeval α f = 0 := by
    rw [hαdef, aeval_algEquiv, AlgHom.comp_apply, hMf, map_zero]
  have hαK : α ∉ Set.range (algebraMap K ℍ[K,a,b]) := by
    rintro ⟨k, hk⟩
    have hMk : M = algebraMap K (Matrix (Fin 2) (Fin 2) K) k := by
      rw [← φ.apply_symm_apply M, ← hαdef, ← hk, AlgEquiv.commutes]
    have := congrFun (congrFun hMk 1) 0
    simp [hM, Matrix.algebraMap_matrix_apply] at this
  exact ⟨α, eq_reducedCharpoly_of_aeval_eq_zero hαK hf hdeg hαf⟩

/-- **A split quaternion algebra has $S_{a,b} = K$.** Let $a, b$ be elements of a field $K$ such
that `ℍ[K,a,b]` is isomorphic to the matrix algebra $M_2(K)$. Then every $s \in K$ is the reduced
trace of an element of reduced norm $1$: `reducedTraceSet K a b = Set.univ`.

The proof: $x^2 - sx + 1$ is a reduced characteristic polynomial
(`QuaternionAlgebra.exists_reducedCharpoly_eq_of_nonempty_algEquiv`).

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, Lemma 2.1(i) and its proof, pp. 2–3 of the author's
version with the corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>):
"If $p \notin \Delta_{a,b}$, then $S_{a,b}(\mathbb{Q}_p) = \mathbb{Q}_p$." The source states this
over $\mathbb{Q}_p$; it holds over every field. -/
theorem reducedTraceSet_eq_univ_of_nonempty_algEquiv {a b : K}
    (hsplit : Nonempty (ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)) :
    reducedTraceSet K a b = Set.univ := by
  refine Set.eq_univ_of_forall fun s => ?_
  have hm : (X ^ 2 - C s * X + 1 : K[X]).Monic := by monicity!
  have hd : (X ^ 2 - C s * X + 1 : K[X]).natDegree = 2 := by compute_degree!
  obtain ⟨α, hα⟩ := exists_reducedCharpoly_eq_of_nonempty_algEquiv hsplit hm hd
  exact mem_reducedTraceSet_iff_exists_reducedCharpoly.2 ⟨α, hα.symm⟩

end QuaternionAlgebra

namespace Rat

/-- **At a prime $p \notin \Delta_{a,b}$, every monic quadratic is a reduced characteristic
polynomial.** Let $a, b \in \mathbb{Q}$ and let $p$ be a prime with $p \notin \Delta_{a,b}$. Then
every monic $f \in \mathbb{Q}_p[x]$ of degree $2$ is the reduced characteristic polynomial
$x^2 - \operatorname{trd}(\alpha)\, x + \operatorname{nrd}(\alpha)$ of some
$\alpha \in H_{a,b} \otimes \mathbb{Q}_p$ = `ℍ[ℚ_[p],a,b]`.

The source takes $a, b \in \mathbb{Q}^\times$; the statement holds for all $a, b$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.1(i), p. 3 of the author's version
with the corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "If
$p \notin \Delta_{a,b}$, then $H_{a,b} \otimes \mathbb{Q}_p \simeq M_2(\mathbb{Q}_p)$, and any monic
quadratic polynomial is a characteristic polynomial." -/
theorem exists_reducedCharpoly_eq_of_not_mem_quaternionRamifiedPrimes {a b : ℚ} {p : ℕ}
    [Fact p.Prime] (hp : ⟨p, Fact.out⟩ ∉ quaternionRamifiedPrimes a b) {f : ℚ_[p][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2) :
    ∃ α : ℍ[ℚ_[p],(a : ℚ_[p]),(b : ℚ_[p])], f = X ^ 2 - C (2 * α.re) * X +
      C (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) := by
  have hsplit : Nonempty (ℍ[ℚ_[p],(a : ℚ_[p]),(b : ℚ_[p])] ≃ₐ[ℚ_[p]]
      Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    by_contra h
    exact hp (not_nonempty_iff.1 h)
  exact QuaternionAlgebra.exists_reducedCharpoly_eq_of_nonempty_algEquiv hsplit hf hdeg

/-- **$S_{a,b}(\mathbb{Q}_p) = \mathbb{Q}_p$ at a prime $p \notin \Delta_{a,b}$.** Let
$a, b \in \mathbb{Q}$ and let $p$ be a prime that does not ramify in $H_{a,b}$. Then every
$s \in \mathbb{Q}_p$ is the reduced trace of an element of reduced norm $1$ of
$H_{a,b} \otimes \mathbb{Q}_p$: `reducedTraceSet ℚ_[p] a b = Set.univ`.

This is part (i) of Poonen's Lemma 2.1. The source takes $a, b \in \mathbb{Q}^\times$; the
statement holds for all $a, b$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, Lemma 2.1(i), p. 2 of the author's version with the
corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "If
$p \notin \Delta_{a,b}$, then $S_{a,b}(\mathbb{Q}_p) = \mathbb{Q}_p$." -/
theorem reducedTraceSet_padic_eq_univ_of_not_mem_quaternionRamifiedPrimes {a b : ℚ} {p : ℕ}
    [Fact p.Prime] (hp : ⟨p, Fact.out⟩ ∉ quaternionRamifiedPrimes a b) :
    QuaternionAlgebra.reducedTraceSet ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = Set.univ := by
  apply QuaternionAlgebra.reducedTraceSet_eq_univ_of_nonempty_algEquiv
  by_contra h
  exact hp (not_nonempty_iff.1 h)

end Rat
