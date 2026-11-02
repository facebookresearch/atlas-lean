/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.LinearCode
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

/-!
# Reed-Solomon codes and the Berlekamp-Welch decoder

Fix `n` evaluation points `α : Fin n → F`, pairwise distinct, in a field `F`. The **Reed-Solomon
code** `RS(α, k)` consists of the evaluation vectors `(p(α₀), …, p(α_{n-1}))` of the polynomials
`p` of degree less than `k`.

* `encode α p`: the encoder, evaluation at the points.
* `card_eval_eq_zero_le`: a nonzero polynomial vanishes at no more of the points than its degree.
  Hence for `k ≤ n` the encoder is injective on polynomials of degree less than `k`
  (`finrank_code`: the code has dimension `k`), and a nonzero codeword has weight at least
  `n - k + 1` (`le_hammingNorm_encode`).
* `minDist_code` (**Reed-Solomon codes are MDS**): for `1 ≤ k ≤ n`, over any field, the minimum
  distance is exactly `n - k + 1`. The lower bound is the root count; the upper bound is attained
  by the codeword of `∏_{j < k - 1} (X - αⱼ)`. Over a finite field this is equality in the
  Singleton bound (`minDist_code_eq_singleton`, against `minDist_le_of_ne_bot`, which rests on
  MathlibExt's Singleton bound).
* **Berlekamp-Welch.** With error budget `e`, the key equations for a received word `y` ask for a
  monic `E` of degree `e` and a `Q` of degree less than `e + k` with `Q(αᵢ) = yᵢ E(αᵢ)` for all
  `i` (`IsKeySolution`); they are linear in the coefficients.
  * `exists_isKeySolution`: if `y` is within distance `e` of the encoding of `p`, the error
    locator `E = ∏_{yᵢ ≠ p(αᵢ)} (X - αᵢ) · X^{e - #errors}` and `Q = p E` solve them.
  * `eq_mul_of_isKeySolution`: if moreover `2e + k ≤ n`, *every* solution has `Q = p E`, so
    `Q /ₘ E = p` (`divByMonic_eq_of_isKeySolution`).
  * `KeySolver` packages any procedure that returns a solution of the key equations whenever one
    exists. With `E` monic of degree `e` the key equations are an affine system in the remaining
    coefficients, so Gaussian elimination is such a solver (Mathlib provides none;
    `KeySolver.ofChoice` is a classical one). `decode S y` runs the solver, divides, and accepts
    the quotient only if it has degree less than `k` and lies within distance `e` of `y`.
    **`decode_eq_some_iff`**: for `2e + k ≤ n` the decoder returns `p` exactly when `p` is within
    distance `e`; it fails exactly when no codeword is (`decode_eq_none_iff`).
    **`decode_encode_add`**: every error of weight at most `⌊(n - k)/2⌋` is corrected.

## References

* I. S. Reed, G. Solomon, "Polynomial codes over certain finite fields", *Journal of the SIAM* 8
  (1960), 300-304.
* L. R. Welch, E. R. Berlekamp, "Error correction for algebraic block codes", US Patent 4,633,470
  (1986).
* P. Gemmell, M. Sudan, "Highly resilient correctors for polynomials", *Information Processing
  Letters* 43 (1992), 169-174 (the key-equation formulation used here).
* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory* (draft), the chapters "Reed-Solomon
  codes" and "Efficient decoding of Reed-Solomon codes".
-/

namespace Cslib.CodingTheory.ReedSolomon

open Polynomial LinearCode Module Finset

variable {F : Type*} [Field F] {n k e : ℕ}

/-! ### The code -/

/-- **Reed-Solomon encoder.** For a field $F$ and points $\alpha_0, \dots, \alpha_{n-1} \in F$,
the encoding of a polynomial $p \in F[X]$ is the word $(p(\alpha_0), \dots, p(\alpha_{n-1}))$
in $F^n$. -/
noncomputable def encode (α : Fin n → F) (p : F[X]) : Fin n → F := fun i ↦ p.eval (α i)

/-- **Reed-Solomon encoder as a linear map.** For a field $F$ and points
$\alpha_0, \dots, \alpha_{n-1} \in F$, the $F$-linear map $F[X] \to F^n$ sending a polynomial
$p$ to $(p(\alpha_0), \dots, p(\alpha_{n-1}))$. -/
noncomputable def encodeLin (α : Fin n → F) : F[X] →ₗ[F] (Fin n → F) where
  toFun := encode α
  map_add' p q := funext fun i ↦ eval_add
  map_smul' c p := funext fun i ↦ by simp [encode, smul_eq_C_mul]

/-- **Reed-Solomon code.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in F$ and
let $k$ be a natural number. The Reed-Solomon code $\mathrm{RS}(\alpha, k)$ is the linear code
of length $n$ over $F$ consisting of the words $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ for the
polynomials $p \in F[X]$ of degree less than $k$. -/
noncomputable def code (α : Fin n → F) (k : ℕ) : LinearCode F (Fin n) :=
  (degreeLT F k).map (encodeLin α)

theorem encode_add (α : Fin n → F) (p q : F[X]) : encode α (p + q) = encode α p + encode α q :=
  (encodeLin α).map_add p q

theorem encode_sub (α : Fin n → F) (p q : F[X]) : encode α (p - q) = encode α p - encode α q :=
  (encodeLin α).map_sub p q

theorem mem_code {α : Fin n → F} {c : Fin n → F} :
    c ∈ code α k ↔ ∃ p : F[X], p.degree < k ∧ encode α p = c := by
  simp [code, mem_degreeLT, encodeLin]

theorem encode_mem_code (α : Fin n → F) {p : F[X]} (hp : p.degree < k) : encode α p ∈ code α k :=
  mem_code.mpr ⟨p, hp, rfl⟩

variable [DecidableEq F]

/-- **Root count at distinct points.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1}$
be pairwise distinct elements of $F$, and let $p \in F[X]$ be a nonzero polynomial. Then the
number of indices $i < n$ with $p(\alpha_i) = 0$ is at most the degree of $p$. -/
theorem card_eval_eq_zero_le {α : Fin n → F} (hα : Function.Injective α) {p : F[X]}
    (hp : p ≠ 0) : #{i | p.eval (α i) = 0} ≤ p.natDegree := by
  classical
  calc #{i | p.eval (α i) = 0} = #(({i | p.eval (α i) = 0} : Finset (Fin n)).image α) :=
        (card_image_of_injective _ hα).symm
    _ ≤ #p.roots.toFinset := card_le_card (by
        intro x hx
        simp only [mem_image, mem_filter, mem_univ, true_and] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simpa [Multiset.mem_toFinset, mem_roots hp] using hi)
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

theorem hammingNorm_encode (α : Fin n → F) (p : F[X]) :
    hammingNorm (encode α p) = n - #{i | p.eval (α i) = 0} := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i ↦ p.eval (α i) = 0)
  rw [card_univ, Fintype.card_fin] at h
  have h2 : hammingNorm (encode α p) = #{i | ¬p.eval (α i) = 0} := by
    simp only [hammingNorm, encode, ne_eq]
    congr 1
  omega

/-- **Nonzero Reed-Solomon codewords are heavy.** Let $F$ be a field, let $\alpha_0, \dots,
\alpha_{n-1} \in F$ be pairwise distinct and let $k \le n$. For every nonzero polynomial
$p \in F[X]$ of degree less than $k$, the encoding $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ has at
least $n - k + 1$ nonzero coordinates. -/
theorem le_hammingNorm_encode {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n)
    {p : F[X]} (hp : p ≠ 0) (hdeg : p.degree < k) : n - k + 1 ≤ hammingNorm (encode α p) := by
  have h1 := card_eval_eq_zero_le hα hp
  have h2 : p.natDegree < k := (natDegree_lt_iff_degree_lt hp).mpr hdeg
  rw [hammingNorm_encode]
  omega

omit [DecidableEq F] in
/-- **The Reed-Solomon encoder is injective on low-degree polynomials.** Let $F$ be a field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $k \le n$. If two polynomials
$p, q \in F[X]$ of degree less than $k$ satisfy $p(\alpha_i) = q(\alpha_i)$ for every $i < n$,
then $p = q$. -/
theorem injOn_encode {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n) :
    Set.InjOn (encode α) (degreeLT F k : Set F[X]) := by
  classical
  intro p hp q hq h
  rw [SetLike.mem_coe, mem_degreeLT] at hp hq
  by_contra hne
  have hpq : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (p - q).degree < k := (degree_sub_le p q).trans_lt (max_lt hp hq)
  have := le_hammingNorm_encode hα hkn hpq hdeg
  rw [encode_sub, h, sub_self, hammingNorm_zero] at this
  omega

omit [DecidableEq F] in
/-- **Dimension of a Reed-Solomon code.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in
F$ be pairwise distinct and let $k \le n$. The Reed-Solomon code of the points $\alpha$ with
parameter $k$ has dimension $k$ over $F$. -/
theorem finrank_code {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n) :
    finrank F (code α k) = k := by
  have hinj : Function.Injective ((encodeLin α).domRestrict (degreeLT F k)) := by
    intro p q h
    exact Subtype.ext (injOn_encode hα hkn p.2 q.2 h)
  rw [code, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj,
    (degreeLTEquiv F k).finrank_eq, finrank_fin_fun]

/-- **Lower bound on the minimum distance of a Reed-Solomon code.** Let $F$ be a field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $k \in \mathbb{N}$. The
Reed-Solomon code of the points $\alpha$ with parameter $k$ has minimum distance at least
$\max(n - k, 0) + 1$. -/
theorem le_minDist_code {α : Fin n → F} (hα : Function.Injective α) :
    ((n - k + 1 : ℕ) : ℕ∞) ≤ (code α k).minDist := by
  by_cases hkn : k ≤ n
  · rw [minDist_eq_minWeight, le_minWeight_iff]
    intro c hc hne
    obtain ⟨p, hdeg, rfl⟩ := mem_code.mp hc
    have hp : p ≠ 0 := by rintro rfl; exact hne (funext fun i ↦ by simp [encode])
    exact_mod_cast le_hammingNorm_encode hα hkn hp hdeg
  · rw [show n - k + 1 = 1 by omega]
    exact_mod_cast one_le_minDist (code α k)

/-- **A low-weight Reed-Solomon codeword.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1}
\in F$ (not necessarily distinct) and let $1 \le k \le n$. There is a nonzero polynomial
$p \in F[X]$ of degree less than $k$ whose encoding $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ has at
most $n - k + 1$ nonzero coordinates.

One such polynomial is $\prod_{j < k - 1} (X - \alpha_j)$. -/
theorem exists_codeword_hammingNorm_le (α : Fin n → F) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ p : F[X], p ≠ 0 ∧ p.degree < k ∧ hammingNorm (encode α p) ≤ n - k + 1 := by
  set T : Finset (Fin n) := {j | j.val < k - 1} with hT
  have hTcard : #T = k - 1 := by
    have : T = (Finset.range (k - 1)).attachFin (fun m hm ↦ by
        rw [Finset.mem_range] at hm; omega) := by
      ext j
      simp [hT]
    rw [this, card_attachFin, card_range]
  set p : F[X] := ∏ j ∈ T, (X - C (α j)) with hp
  have hmonic : p.Monic := monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C (α j)
  have hdeg : p.natDegree = k - 1 := by
    rw [hp, natDegree_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C (α j)]
    simp [hTcard]
  refine ⟨p, hmonic.ne_zero, ?_, ?_⟩
  · rw [degree_eq_natDegree hmonic.ne_zero, hdeg]
    exact_mod_cast (by omega : k - 1 < k)
  · have hsub : T ⊆ ({i | p.eval (α i) = 0} : Finset (Fin n)) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and]
      rw [hp, eval_prod]
      exact prod_eq_zero hj (by simp)
    have := card_le_card hsub
    rw [hammingNorm_encode]
    omega

/-- **Reed-Solomon codes are MDS.** Let $F$ be a field (not necessarily finite), let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $1 \le k \le n$. The
Reed-Solomon code of the points $\alpha$ with parameter $k$ has minimum distance exactly
$n - k + 1$.

The lower bound counts roots; the upper bound is attained by the encoding of
$\prod_{j < k - 1} (X - \alpha_j)$. -/
theorem minDist_code {α : Fin n → F} (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (code α k).minDist = (n - k + 1 : ℕ) := by
  refine le_antisymm ?_ (le_minDist_code hα)
  obtain ⟨p, hp, hdeg, hnorm⟩ := exists_codeword_hammingNorm_le α hk hkn
  have hne : encode α p ≠ 0 := by
    intro h0
    have := le_hammingNorm_encode hα hkn hp hdeg
    rw [h0, hammingNorm_zero] at this
    omega
  calc (code α k).minDist ≤ hammingDist (encode α p) 0 :=
        minDist_le (encode_mem_code α hdeg) (code α k).zero_mem hne
    _ ≤ (n - k + 1 : ℕ) := by rw [hammingDist_zero_right]; exact_mod_cast hnorm

/-- **Reed-Solomon codes meet the Singleton bound.** Let $F$ be a finite field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $1 \le k \le n$. The
Reed-Solomon code $C$ of the points $\alpha$ with parameter $k$ has minimum distance
$d = n - \dim C + 1$, so the Singleton bound $d \le n - \dim C + 1$ for linear codes holds with
equality.

The upper bound is the Singleton bound for linear codes; the lower bound counts roots. -/
theorem minDist_code_eq_singleton [Finite F] {α : Fin n → F} (hα : Function.Injective α)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (code α k).minDist = (n - finrank F (code α k) + 1 : ℕ) := by
  have hne : code α k ≠ ⊥ := by
    intro h
    have h1 : encode α (1 : F[X]) ∈ code α k :=
      encode_mem_code α (by rw [degree_one]; exact_mod_cast hk)
    rw [h, Submodule.mem_bot] at h1
    have := congrFun h1 ⟨0, by omega⟩
    simp [encode] at this
  refine le_antisymm (minDist_le_of_ne_bot hne) ?_
  rw [finrank_code hα hkn]
  exact le_minDist_code hα

/-! ### Berlekamp-Welch decoding -/

/-- **Berlekamp-Welch key equations.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in
F$, let $k, e \in \mathbb{N}$ and let $y \in F^n$ be a received word. A pair of polynomials
$(Q, E)$ over $F$ solves the key equations for $y$ when $E$ is monic of degree $e$, $Q$ has degree
less than $e + k$, and $Q(\alpha_i) = y_i E(\alpha_i)$ for every $i < n$. -/
def IsKeySolution (α : Fin n → F) (k e : ℕ) (y : Fin n → F) (Q E : F[X]) : Prop :=
  E.Monic ∧ E.natDegree = e ∧ Q.degree < (e + k : ℕ) ∧ ∀ i, Q.eval (α i) = y i * E.eval (α i)

/-- **The key equations are solvable.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in
F$ and let $p \in F[X]$ have degree less than $k$. If a received word $y \in F^n$ differs from the
encoding $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ in at most $e$ coordinates, then the
Berlekamp-Welch key equations for $y$ with parameters $k$ and $e$ have a solution $(Q, E)$.

A solution is the error locator polynomial, padded to degree $e$, together with $Q = pE$. -/
theorem exists_isKeySolution (α : Fin n → F) {p : F[X]} (hp : p.degree < k) {y : Fin n → F}
    (he : hammingDist y (encode α p) ≤ e) : ∃ Q E, IsKeySolution α k e y Q E := by
  set S : Finset (Fin n) := {i | y i ≠ encode α p i} with hS
  have hSe : #S ≤ e := he
  set E : F[X] := (∏ i ∈ S, (X - C (α i))) * X ^ (e - #S) with hE
  have hmonic : E.Monic :=
    (monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (α i)).mul (monic_X_pow _)
  have hdegE : E.natDegree = e := by
    rw [hE, (monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (α i)).natDegree_mul
      (monic_X_pow _), natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (α i)]
    simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one, natDegree_X_pow]
    omega
  refine ⟨p * E, E, hmonic, hdegE, ?_, fun i ↦ ?_⟩
  · rcases eq_or_ne p 0 with rfl | hp0
    · simp
    have h1 : p.natDegree < k := (natDegree_lt_iff_degree_lt hp0).mpr hp
    rw [degree_mul, degree_eq_natDegree hp0, degree_eq_natDegree hmonic.ne_zero, hdegE]
    exact_mod_cast (by omega : p.natDegree + e < e + k)
  · rw [eval_mul]
    by_cases hi : i ∈ S
    · have : E.eval (α i) = 0 := by
        rw [hE, eval_mul, eval_prod, prod_eq_zero hi (by simp), zero_mul]
      rw [this, mul_zero, mul_zero]
    · simp only [hS, mem_filter, mem_univ, true_and, not_not] at hi
      rw [hi, encode]

/-- **Every solution of the key equations reveals the message.** Let $F$ be a field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $k, e$ be natural numbers
with $2e + k \le n$. Let $p \in F[X]$ have degree less than $k$, and let $y \in F^n$ be
within Hamming distance $e$ of $(p(\alpha_0), \dots, p(\alpha_{n-1}))$. If $(Q, E)$ solves
the key equations for $y$ ($E$ is monic of degree $e$, $\deg Q < e + k$, and
$Q(\alpha_i) = y_i E(\alpha_i)$ for all $i < n$), then $Q = pE$.

The difference $Q - pE$ has degree less than $e + k$ and vanishes at the at least
$n - e \ge e + k$ error-free points. -/
theorem eq_mul_of_isKeySolution {α : Fin n → F} (hα : Function.Injective α) (h2e : 2 * e + k ≤ n)
    {p : F[X]} (hp : p.degree < k) {y : Fin n → F} (he : hammingDist y (encode α p) ≤ e)
    {Q E : F[X]} (hsol : IsKeySolution α k e y Q E) : Q = p * E := by
  classical
  obtain ⟨hmonic, hdegE, hQ, hkey⟩ := hsol
  by_contra hne
  set R := Q - p * E with hR
  have hR0 : R ≠ 0 := sub_ne_zero.mpr hne
  have hpE : (p * E).degree < (e + k : ℕ) := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    have h1 : p.natDegree < k := (natDegree_lt_iff_degree_lt hp0).mpr hp
    rw [degree_mul, degree_eq_natDegree hp0, degree_eq_natDegree hmonic.ne_zero, hdegE]
    exact_mod_cast (by omega : p.natDegree + e < e + k)
  have hRdeg : R.natDegree < e + k :=
    (natDegree_lt_iff_degree_lt hR0).mpr ((degree_sub_le _ _).trans_lt (max_lt hQ hpE))
  -- `R` vanishes at every error-free point.
  have hsub : ({i | y i = encode α p i} : Finset (Fin n)) ⊆
      ({i | R.eval (α i) = 0} : Finset (Fin n)) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [hR, eval_sub, eval_mul, hkey i, hi, encode, sub_self]
  have hgood : n - e ≤ #({i | y i = encode α p i} : Finset (Fin n)) := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun i ↦ y i = encode α p i)
    rw [card_univ, Fintype.card_fin] at h
    have : #({i | ¬y i = encode α p i} : Finset (Fin n)) = hammingDist y (encode α p) := rfl
    omega
  have := (card_le_card hsub).trans (card_eval_eq_zero_le hα hR0)
  omega

/-- **The quotient of a key-equation solution is the message.** Let $F$ be a field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $k, e$ be natural numbers
with $2e + k \le n$. Let $p \in F[X]$ have degree less than $k$, and let $y \in F^n$ be
within Hamming distance $e$ of $(p(\alpha_0), \dots, p(\alpha_{n-1}))$. If $(Q, E)$ solves
the key equations for $y$ ($E$ is monic of degree $e$, $\deg Q < e + k$, and
$Q(\alpha_i) = y_i E(\alpha_i)$ for all $i < n$), then the quotient of $Q$ by $E$ is $p$. -/
theorem divByMonic_eq_of_isKeySolution {α : Fin n → F} (hα : Function.Injective α)
    (h2e : 2 * e + k ≤ n) {p : F[X]} (hp : p.degree < k) {y : Fin n → F}
    (he : hammingDist y (encode α p) ≤ e) {Q E : F[X]} (hsol : IsKeySolution α k e y Q E) :
    Q /ₘ E = p := by
  rw [eq_mul_of_isKeySolution hα h2e hp he hsol, mul_comm, mul_divByMonic_cancel_left _ hsol.1]

/-- **Solver for the key equations.** For a field $F$, points $\alpha_0, \dots, \alpha_{n-1} \in F$
and parameters $k, e \in \mathbb{N}$, a solver for the Berlekamp-Welch key equations is a
procedure that takes a received word $y \in F^n$ and either returns a pair of polynomials
$(Q, E)$ over $F$ or reports failure, such that every returned pair solves the key equations for
$y$, and a pair is returned whenever the key equations for $y$ have a solution.

(The key equations are a linear system in the coefficients of $Q$ and of $E$; Gaussian
elimination is a solver.) -/
structure KeySolver (α : Fin n → F) (k e : ℕ) where
  /-- The solving procedure. -/
  solve : (Fin n → F) → Option (F[X] × F[X])
  /-- Returned pairs solve the key equations. -/
  sound : ∀ y QE, solve y = some QE → IsKeySolution α k e y QE.1 QE.2
  /-- A solution is returned whenever one exists. -/
  complete : ∀ y, (∃ Q E, IsKeySolution α k e y Q E) → (solve y).isSome

/-- **A key-equation solver by choice.** For points $\alpha_0, \dots, \alpha_{n-1}$ in a field
$F$ and natural numbers $k$ and $e$, this is the solver for the key equations that, on a received
word $y \in F^n$, returns a pair $(Q, E)$ of polynomials solving the key equations for $y$ (that
is, $E$ is monic of degree $e$, $\deg Q < e + k$ and $Q(\alpha_i) = y_i E(\alpha_i)$ for all $i$),
picked by the axiom of choice, whenever such a pair exists, and reports failure otherwise. -/
noncomputable def KeySolver.ofChoice (α : Fin n → F) (k e : ℕ) : KeySolver α k e where
  solve y := by
    classical
    exact if h : ∃ Q E, IsKeySolution α k e y Q E then some (h.choose, h.choose_spec.choose)
      else none
  sound y QE h := by
    classical
    split_ifs at h with hex
    · cases h
      exact hex.choose_spec.choose_spec
  complete y hex := by
    classical
    simp [hex]

/-- **Berlekamp-Welch decoder.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in F$,
let $k, e$ be natural numbers and let $S$ be a solver for the key equations with error budget
$e$. On a received word $y \in F^n$ the decoder runs $S$ on $y$ and reports failure if $S$
returns nothing. If $S$ returns a pair $(Q, E)$ (the solver guarantees that $E$ is monic),
let $q$ be the quotient of $Q$ by $E$; the decoder returns $q$ if $q$ has degree less than $k$
and the Hamming distance between $y$ and $(q(\alpha_0), \dots, q(\alpha_{n-1}))$ is at most
$e$, and reports failure otherwise.

Its only nontrivial step is the solver. -/
noncomputable def decode {α : Fin n → F} (S : KeySolver α k e) (y : Fin n → F) : Option F[X] :=
  (S.solve y).bind fun QE ↦
    if (QE.1 /ₘ QE.2).degree < k ∧ hammingDist y (encode α (QE.1 /ₘ QE.2)) ≤ e then
      some (QE.1 /ₘ QE.2)
    else none

/-- **What the decoder returns.** Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in F$
be pairwise distinct, let $k, e$ be natural numbers with $2e + k \le n$ (the unique-decoding
regime), and let $S$ be a solver for the key equations with error budget $e$. For every
polynomial $p \in F[X]$ and every received word $y \in F^n$, the Berlekamp-Welch decoder with
solver $S$ returns $p$ on $y$ if and only if $p$ has degree less than $k$ and the Hamming
distance between $y$ and $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ is at most $e$. -/
theorem decode_eq_some_iff {α : Fin n → F} (hα : Function.Injective α) (h2e : 2 * e + k ≤ n)
    (S : KeySolver α k e) {p : F[X]} {y : Fin n → F} :
    decode S y = some p ↔ p.degree < k ∧ hammingDist y (encode α p) ≤ e := by
  constructor
  · intro h
    simp only [decode, Option.bind_eq_some_iff] at h
    obtain ⟨QE, -, hif⟩ := h
    split_ifs at hif with hcond
    cases hif
    exact hcond
  · rintro ⟨hp, he⟩
    obtain ⟨QE, hQE⟩ :=
      Option.isSome_iff_exists.mp (S.complete y (exists_isKeySolution α hp he))
    have hdiv := divByMonic_eq_of_isKeySolution hα h2e hp he (S.sound y QE hQE)
    simp only [decode, hQE, Option.bind_some, hdiv, hp, he, and_self, ↓reduceIte]

/-- **The decoder fails exactly when no codeword is close.** Let $F$ be a field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct, let $k, e$ be natural numbers
with $2e + k \le n$, and let $S$ be a solver for the key equations with error budget $e$.
For every received word $y \in F^n$, the Berlekamp-Welch decoder with solver $S$ reports
failure on $y$ if and only if, for every polynomial $p \in F[X]$ of degree less than $k$, the
Hamming distance between $y$ and $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ is greater than $e$. -/
theorem decode_eq_none_iff {α : Fin n → F} (hα : Function.Injective α) (h2e : 2 * e + k ≤ n)
    (S : KeySolver α k e) {y : Fin n → F} :
    decode S y = none ↔ ∀ p : F[X], p.degree < k → e < hammingDist y (encode α p) := by
  constructor
  · intro h p hp
    by_contra hle
    have := (decode_eq_some_iff hα h2e S).mpr ⟨hp, not_lt.mp hle⟩
    rw [h] at this
    cases this
  · intro h
    cases hd : decode S y with
    | none => rfl
    | some p =>
      obtain ⟨hp, he⟩ := (decode_eq_some_iff hα h2e S).mp hd
      exact absurd he (not_le.mpr (h p hp))

/-- **Berlekamp-Welch corrects every error of weight at most $\lfloor (n-k)/2 \rfloor$.** Let
$F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct, let $k \le n$,
put $t = \lfloor (n-k)/2 \rfloor$, and let $S$ be a solver for the key equations with error
budget $t$. For every polynomial $p \in F[X]$ of degree less than $k$ and every error word
$\varepsilon \in F^n$ with at most $t$ nonzero entries, the Berlekamp-Welch decoder with
solver $S$, run on the received word
$(p(\alpha_0) + \varepsilon_0, \dots, p(\alpha_{n-1}) + \varepsilon_{n-1})$, returns $p$. -/
theorem decode_encode_add {α : Fin n → F} (hα : Function.Injective α) (hkn : k ≤ n)
    (S : KeySolver α k ((n - k) / 2)) {p : F[X]} (hp : p.degree < k) {err : Fin n → F}
    (herr : hammingNorm err ≤ (n - k) / 2) : decode S (encode α p + err) = some p := by
  refine (decode_eq_some_iff hα (by omega) S).mpr ⟨hp, ?_⟩
  rwa [hammingDist_eq_hammingNorm_sub, add_sub_cancel_left]

end Cslib.CodingTheory.ReedSolomon
