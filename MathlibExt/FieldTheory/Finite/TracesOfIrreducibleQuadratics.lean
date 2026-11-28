/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Trace

/-!
# The set $U_q$ of traces of irreducible quadratics $x^2 - sx + 1$

For a field $K$, `FiniteField.tracesOfIrreducibleQuadratics K` is the set of $s \in K$ such that
$x^2 - sx + 1$ is irreducible in $K[x]$. For the finite field $K = \mathbb{F}_q$ this is the set
$U_q$ of B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, §2.

The results:

* `FiniteField.mem_tracesOfIrreducibleQuadratics_iff`: $s \in U_K$ if and only if no $r \in K$
  satisfies $r^2 - sr + 1 = 0$;
* `FiniteField.neg_mem_tracesOfIrreducibleQuadratics_iff`,
  `FiniteField.nonempty_tracesOfIrreducibleQuadratics` and
  `FiniteField.zero_mem_tracesOfIrreducibleQuadratics_add_self`: $-U_q = U_q$,
  $U_q \ne \emptyset$ and $0 \in U_q + U_q$;
* `FiniteField.tracesOfIrreducibleQuadratics_eq_image_trace`: for a field extension
  $L \supseteq \mathbb{F}_q$ of degree $2$, $U_q$ is the set of traces of the elements of $L$ of
  norm $1$ that are not in $\mathbb{F}_q$.
-/

set_option autoImplicit false

@[expose] public section

open Polynomial

open scoped Pointwise

namespace FiniteField

variable {K : Type*} [Field K]

variable (K) in
/-- **The set $U_q$ of traces of irreducible quadratics $x^2 - sx + 1$.** For a field $K$, the set
of $s \in K$ such that $x^2 - sx + 1$ is irreducible in $K[x]$.

For the finite field $K = \mathbb{F}_q$ with $q$ elements, this is the set $U_q$ of B. Poonen.
The definition makes sense over every field, and the field need not be finite here.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, §2, p. 2 of the author's version with the
corrections of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "For any prime
power $q$, let $U_q$ be the set of $s \in \mathbb{F}_q$ such that $x^2 - sx + 1$ is irreducible in
$\mathbb{F}_q[x]$." -/
def tracesOfIrreducibleQuadratics : Set K :=
  {s | Irreducible (X ^ 2 - C s * X + 1 : K[X])}

/-- The polynomial $x^2 - sx + 1$ has degree $2$. -/
private theorem natDegree_X_sq_sub_C_mul_X_add_one (s : K) :
    (X ^ 2 - C s * X + 1 : K[X]).natDegree = 2 := by
  compute_degree!

/-- **Membership in $U_q$ by roots.** For a field $K$ and $s \in K$, the polynomial
$x^2 - sx + 1$ is irreducible in $K[x]$, that is, $s \in U_K$, if and only if no $r \in K$
satisfies $r^2 - sr + 1 = 0$. A polynomial of degree $2$ is irreducible exactly when it has no
root (`Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three`). -/
theorem mem_tracesOfIrreducibleQuadratics_iff {s : K} :
    s ∈ tracesOfIrreducibleQuadratics K ↔ ∀ r : K, r ^ 2 - s * r + 1 ≠ 0 := by
  have hd := natDegree_X_sq_sub_C_mul_X_add_one s
  have hne : (X ^ 2 - C s * X + 1 : K[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hd
    exact absurd hd (by norm_num)
  change Irreducible _ ↔ _
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  simp [mem_roots hne, IsRoot]

/-- **$U_q$ is symmetric.** For a field $K$ and $s \in K$, $-s \in U_K$ if and only if $s \in U_K$:
$r$ is a root of $x^2 - sx + 1$ exactly when $-r$ is a root of $x^2 + sx + 1$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, p. 3 of the author's version with
the corrections of April 15, 2019: "Also, $-U_q = U_q$". The source takes $K = \mathbb{F}_q$; the
statement holds over every field. -/
theorem neg_mem_tracesOfIrreducibleQuadratics_iff {s : K} :
    -s ∈ tracesOfIrreducibleQuadratics K ↔ s ∈ tracesOfIrreducibleQuadratics K := by
  simp only [mem_tracesOfIrreducibleQuadratics_iff]
  constructor
  · intro h r hr
    exact h (-r) (by linear_combination hr)
  · intro h r hr
    exact h (-r) (by linear_combination hr)

/-- **$U_q$ is preserved by ring isomorphisms.** For a ring isomorphism $e \colon K \to K'$ of
fields and $s \in K$, $e(s) \in U_{K'}$ if and only if $s \in U_K$. -/
theorem map_mem_tracesOfIrreducibleQuadratics_iff {K' : Type*} [Field K'] (e : K ≃+* K')
    {s : K} :
    e s ∈ tracesOfIrreducibleQuadratics K' ↔ s ∈ tracesOfIrreducibleQuadratics K := by
  simp only [mem_tracesOfIrreducibleQuadratics_iff]
  constructor
  · intro h r hr
    exact h (e r) (by rw [← map_pow, ← map_mul, ← map_sub, ← map_one e, ← map_add, hr, map_zero])
  · intro h r hr
    refine h (e.symm r) ?_
    apply e.injective
    rw [map_add, map_sub, map_mul, map_pow, map_one, RingEquiv.apply_symm_apply, map_zero, hr]

/-- **$U_q$ is nonempty.** For a finite field $K$, there is $s \in K$ with $x^2 - sx + 1$
irreducible in $K[x]$.

The proof counts: if every $x^2 - sx + 1$ had a root $r$, then $r \ne 0$ and $s = r + r^{-1}$, so
$r \mapsto r + r^{-1}$ would map the $q - 1$ elements of $K^\times$ onto the $q$ elements of $K$.
Poonen's proof instead uses the description of $U_q$ by traces and the $q + 1$ elements of norm $1$
of $\mathbb{F}_{q^2}$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, Lemma 2.3, p. 3 of the author's version with the
corrections of April 15, 2019: "For any prime power $q$, the set $U_q$ is nonempty." -/
theorem nonempty_tracesOfIrreducibleQuadratics [Finite K] :
    (tracesOfIrreducibleQuadratics K).Nonempty := by
  classical
  have := Fintype.ofFinite K
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsurj : Function.Surjective (fun r : Kˣ => (r : K) + (r : K)⁻¹) := by
    intro s
    have hs : s ∉ tracesOfIrreducibleQuadratics K := by
      rw [h]
      exact Set.notMem_empty s
    rw [mem_tracesOfIrreducibleQuadratics_iff] at hs
    push Not at hs
    obtain ⟨r, hr⟩ := hs
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    refine ⟨Units.mk0 r hr0, ?_⟩
    simp only [Units.val_mk0]
    rw [inv_eq_of_mul_eq_one_right (by linear_combination -hr : r * (s - r) = 1)]
    ring
  have hle := Fintype.card_le_of_surjective _ hsurj
  rw [Fintype.card_units] at hle
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  omega

/-- **$0 \in U_q + U_q$.** For a finite field $K$, $0 = s + s'$ for some $s, s' \in U_K$: take any
$s \in U_K$ and $s' = -s$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, p. 3 of the author's version with
the corrections of April 15, 2019: "Also, $-U_q = U_q$, so $0 \in U_q + U_q$." -/
theorem zero_mem_tracesOfIrreducibleQuadratics_add_self [Finite K] :
    (0 : K) ∈ tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K := by
  obtain ⟨s, hs⟩ := nonempty_tracesOfIrreducibleQuadratics (K := K)
  exact ⟨s, hs, -s, neg_mem_tracesOfIrreducibleQuadratics_iff.2 hs, add_neg_cancel s⟩

/-- **$U_q$ as the set of traces of the norm-one elements of $\mathbb{F}_{q^2}$ outside
$\mathbb{F}_q$.** Let $K$ be a finite field and let $L$ be a field extension of $K$ of degree $2$.
Then the set $U_K$ of $s \in K$ with $x^2 - sx + 1$ irreducible in $K[x]$ is the set of traces
$\operatorname{Tr}_{L/K}(\beta)$ of the elements $\beta \in L$ that are not in $K$ and have norm
$N_{L/K}(\beta) = 1$.

With $q = \# K$, the trace and the norm are $\operatorname{Tr}_{L/K}(\beta) = \beta + \beta^q$ and
$N_{L/K}(\beta) = \beta^{q+1}$ (`FiniteField.algebraMap_trace_eq_sum_pow`,
`FiniteField.algebraMap_norm_eq_pow`), the forms the source uses. The proof: if $\beta \notin K$
has norm $1$ and trace $s$, the roots of $x^2 - sx + 1$ in $L$ are $\beta$ and
$\beta^q = s - \beta$, neither in $K$. Conversely, if $x^2 - sx + 1$ is irreducible, then
$K[x]/(x^2 - sx + 1)$ is a field of degree $2$ over $K$, so it embeds in $L$
(`FiniteField.nonempty_algHom_of_finrank_dvd`) and gives a root $\beta \in L \setminus K$. As
$\beta$ is also a root of $x^2 - \operatorname{Tr}(\beta)\, x + N(\beta)$, comparing the two
equations gives $\operatorname{Tr}(\beta) = s$ and $N(\beta) = 1$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, first sentence, p. 3 of the
author's version with the corrections of April 15, 2019: "We have
$U_q = \operatorname{Tr}(\{\beta \in \mathbb{F}_{q^2} - \mathbb{F}_q : N(\beta) = 1\})$, where
$\operatorname{Tr}$ and $N$ are the trace and norm for $\mathbb{F}_{q^2}/\mathbb{F}_q$." -/
theorem tracesOfIrreducibleQuadratics_eq_image_trace [Finite K] {L : Type*} [Field L]
    [Algebra K L] (hL : Module.finrank K L = 2) :
    tracesOfIrreducibleQuadratics K =
      Algebra.trace K L '' {β : L | β ∉ Set.range (algebraMap K L) ∧ Algebra.norm K β = 1} := by
  classical
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have : Finite L := Module.finite_of_finite K
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have htr : ∀ β : L, algebraMap K L (Algebra.trace K L β) = β + β ^ q := by
    intro β
    rw [FiniteField.algebraMap_trace_eq_sum_pow, hL]
    simp [Finset.sum_range_succ, hq]
  have hnorm : ∀ β : L, algebraMap K L (Algebra.norm K β) = β ^ (q + 1) := by
    intro β
    rw [FiniteField.algebraMap_norm_eq_pow, Module.natCard_eq_pow_finrank (K := K), hL, ← hq]
    congr 1
    have h1 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
      ring
    rw [h1, Nat.mul_div_cancel _ (show 0 < q - 1 by omega)]
  ext s
  rw [mem_tracesOfIrreducibleQuadratics_iff]
  constructor
  · intro hs
    -- A root of `X ^ 2 - C s * X + 1` in `L`, from an embedding of `K[X] / (X ^ 2 - C s * X + 1)`.
    have hirr : Irreducible (X ^ 2 - C s * X + 1 : K[X]) :=
      mem_tracesOfIrreducibleQuadratics_iff.2 hs
    have hd := natDegree_X_sq_sub_C_mul_X_add_one s
    have hne : (X ^ 2 - C s * X + 1 : K[X]) ≠ 0 := hirr.ne_zero
    have : Fact (Irreducible (X ^ 2 - C s * X + 1 : K[X])) := ⟨hirr⟩
    have hE : Module.finrank K (AdjoinRoot (X ^ 2 - C s * X + 1 : K[X])) = 2 := by
      rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hd]
    obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
      (F := K) (K := AdjoinRoot (X ^ 2 - C s * X + 1 : K[X])) (L := L) (by rw [hE, hL])
    set β := φ (AdjoinRoot.root (X ^ 2 - C s * X + 1 : K[X])) with hβdef
    have hβ : β ^ 2 - algebraMap K L s * β + 1 = 0 := by
      have h0 := congrArg φ (AdjoinRoot.eval₂_root (X ^ 2 - C s * X + 1 : K[X]))
      simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, eval₂_one,
        map_add, map_sub, map_mul, map_pow, map_one, map_zero] at h0
      rw [← hβdef, ← AdjoinRoot.algebraMap_eq, AlgHom.commutes] at h0
      exact h0
    have hβK : β ∉ Set.range (algebraMap K L) := by
      rintro ⟨r, hr⟩
      apply hs r
      apply (algebraMap K L).injective
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, hr]
      exact hβ
    -- Compare with `β ^ 2 - Tr β * β + N β = 0`.
    have hlin : algebraMap K L (Algebra.trace K L β - s) * β =
        algebraMap K L (Algebra.norm K β - 1) := by
      rw [map_sub, map_sub, htr, hnorm, map_one]
      linear_combination hβ
    have htrs : Algebra.trace K L β = s := by
      by_contra hts
      apply hβK
      refine ⟨(Algebra.trace K L β - s)⁻¹ * (Algebra.norm K β - 1), ?_⟩
      rw [map_mul, ← hlin, map_inv₀, ← mul_assoc,
        inv_mul_cancel₀ ((_root_.map_ne_zero _).2 (sub_ne_zero.2 hts)), one_mul]
    refine ⟨β, ⟨hβK, ?_⟩, htrs⟩
    rw [htrs, sub_self, map_zero, zero_mul, eq_comm, map_eq_zero_iff _ (algebraMap K L).injective,
      sub_eq_zero] at hlin
    exact hlin
  · rintro ⟨β, ⟨hβK, hβN⟩, rfl⟩ r hr
    have hr' := congrArg (algebraMap K L) hr
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, htr] at hr'
    have hN : β ^ (q + 1) = 1 := by rw [← hnorm, hβN, map_one]
    have hfac : (algebraMap K L r - β) * (algebraMap K L r - β ^ q) = 0 := by
      linear_combination hr' + hN
    rcases mul_eq_zero.1 hfac with h | h
    · exact hβK ⟨r, sub_eq_zero.1 h⟩
    · apply hβK
      refine ⟨Algebra.trace K L β - r, ?_⟩
      rw [map_sub, htr, sub_eq_zero.1 h]
      ring

end FiniteField
