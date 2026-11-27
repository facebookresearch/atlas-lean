/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.NormTrace
public import MathlibExt.NumberTheory.NumberField.Order
public import MathlibExt.RingTheory.ConductorIdeal

@[expose] public section

/-!
# Ideals of an order in a number field: indices, norms and the conductor

An order of a number field `K` is a `ℤ`-subalgebra `O` of `K` with `NumberField.IsOrder K O`:
it lies in the ring of integers `integralClosure ℤ K` and has fraction field `K`. We prove:

* `Submodule.det_toMatrix_ne_zero_and_natCard_quotient`: for a finite free `ℤ`-module `M` with
  basis `b` and a submodule `N` with a basis `bN` indexed by the same finite type, the transition
  matrix `T` has `det T ≠ 0`, the quotient `M ⧸ N` is finite, and `#(M ⧸ N) = |det T|`;
* `NumberField.IsOrder.ideal_finite_index`: a nonzero ideal `𝔟` of `O` contains a positive integer
  `m`, `O ⧸ 𝔟` is finite with `#(O ⧸ 𝔟) ∣ m ^ [K : ℚ]` for every such `m`, and a nonzero prime
  ideal of `O` is maximal;
* `NumberField.IsOrder.natCard_quotient_span_singleton_eq_abs_norm`: for `β ≠ 0` in `O`,
  `#(O ⧸ βO) = |N_{K/ℚ}(β)|`;
* `NumberField.IsOrder.setOf_mul_mem_eq`: a nonzero ideal `𝔟` of `O` with `𝔟 + 𝔠 = O`, where
  `𝔠` is the conductor of `O`, has multiplier ring `{x ∈ K | x𝔟 ⊆ 𝔟} = O`.

Along the way: `O` is a finite free `ℤ`-module of rank `[K : ℚ]` (`moduleFinite`, `moduleFree`,
`finrank_eq`) and `K` is the localization of `O` at the nonzero integers (`isLocalization`).

Sources: F. Keune, *Number Fields*, Radboud University Press (2023), Lemma 1.40 (p. 20),
Lemma 3.17 (p. 57) and Proposition 3.20 (p. 58); A. V. Sutherland, MIT 18.783 Lecture 17
(Fall 2023), p. 2, Definitions 17.3–17.4 and Lemma 17.5 (pp. 2–3); K. Conrad, *The conductor
ideal of an order*, Definition 1.1 (p. 1), Theorem 3.1 (p. 5) and footnote 4 (p. 14).
-/

open Module

section FullRank

/-- **The index of a subgroup of full rank as a determinant.** Let $M$ be a free abelian group
with a basis $(\alpha_i)_{i \in \iota}$, $\iota$ finite, and let $N \subseteq M$ be a subgroup
with a basis $(\beta_j)_{j \in \iota}$ indexed by the same set (so $N$ is free of the same rank).
Let $T$ be the matrix with $\beta_j = \sum_i T_{ij} \alpha_i$ (`b.toMatrix`). Then
$\det T \neq 0$, the quotient $M/N$ is finite, and $(M : N) = \#(M/N) = |\det T|$.

This is F. Keune, *Number Fields*, 2023, Lemma 1.40 (p. 20), for bases indexed by
$\{1, \dots, n\}$; here they are indexed by any finite type. Keune's transition matrix is $T$ or
its transpose, which has the same determinant. The equality alone is Mathlib's
`Submodule.natAbs_det_basis_change` (and `AddSubgroup.index_eq_natAbs_det`); neither asserts
$\det T \neq 0$ or the finiteness of $M/N$ (`Nat.card` of an infinite type is $0$). -/
theorem Submodule.det_toMatrix_ne_zero_and_natCard_quotient {M : Type*} [AddCommGroup M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) :
    (b.toMatrix fun i => (bN i : M)).det ≠ 0 ∧ Finite (M ⧸ N) ∧
      Nat.card (M ⧸ N) = (b.toMatrix fun i => (bN i : M)).det.natAbs := by
  have : Module.Free ℤ M := Module.Free.of_basis b
  have : Module.Finite ℤ M := Module.Finite.of_basis b
  have hcard : Nat.card (M ⧸ N) = (b.toMatrix fun i => (bN i : M)).det.natAbs := by
    rw [← Submodule.natAbs_det_basis_change b N bN, Basis.det_apply]
    rfl
  have hdet : (b.toMatrix fun i => (bN i : M)).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    have hsum : ∑ j, v j • bN j = 0 := by
      apply Subtype.val_injective
      apply b.repr.injective
      ext i
      have := congrFun hTv i
      simpa [Matrix.mulVec, dotProduct, Basis.toMatrix_apply, map_sum, mul_comm] using this
    funext j
    exact Fintype.linearIndependent_iff.mp bN.linearIndependent v hsum j
  refine ⟨hdet, ?_, hcard⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact Int.natAbs_ne_zero.mpr hdet

end FullRank

private theorem Ideal.natCard_quotient_dvd_of_le {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I ≤ J) : Nat.card (R ⧸ J) ∣ Nat.card (R ⧸ I) := by
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
  exact AddSubgroup.index_dvd_of_le fun _ hx => h hx

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- **A nonzero element of an order divides a positive integer.** Let $O$ be an order in a
number field $K$ (`NumberField.IsOrder`) and $\beta \in O$, $\beta \neq 0$. Then the principal
ideal $\beta O$ contains a positive integer $m$. If $f \in \mathbb{Z}[X]$ is the minimal
polynomial of $\beta$, one can take $m = |f(0)|$, as $(f(\beta) - f(0))/\beta \in O$
(A. V. Sutherland, MIT 18.783 Lecture 17, Fall 2023, p. 2). -/
theorem exists_natCast_mem_span_singleton (hO : NumberField.IsOrder K O) {β : O}
    (hβ : β ≠ 0) : ∃ m : ℕ, 0 < m ∧ (m : O) ∈ Ideal.span {β} := by
  have hint : IsIntegral ℤ (β : K) := hO.le_integralClosure β.2
  have hβK : (β : K) ≠ 0 := fun h => hβ (Subtype.ext h)
  set g := minpoly ℤ (β : K) with hg
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h
    apply minpoly.coeff_zero_ne_zero (A := ℚ) hint.tower_top hβK
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, Polynomial.coeff_map, ← hg, h,
      map_zero]
  obtain ⟨h, hh⟩ := Polynomial.X_dvd_sub_C (p := g)
  have hev : Polynomial.aeval β g = 0 := by
    apply Subtype.val_injective
    change O.val (Polynomial.aeval β g) = O.val 0
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact minpoly.aeval ℤ (β : K)
  have hc : ((g.coeff 0 : ℤ) : O) ∈ Ideal.span {β} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨-Polynomial.aeval β h, ?_⟩
    have := congrArg (Polynomial.aeval β) hh
    rw [map_sub, hev, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, eq_intCast] at this
    linear_combination this
  refine ⟨(g.coeff 0).natAbs, Int.natAbs_pos.mpr hg0, ?_⟩
  have e : (((g.coeff 0).natAbs : ℕ) : O) = ((|g.coeff 0| : ℤ) : O) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [e]
  rcases abs_choice (g.coeff 0) with h1 | h1 <;> rw [h1]
  · exact hc
  · rw [Int.cast_neg]
    exact neg_mem hc

/-- **A nonzero ideal of an order contains a positive integer.** Let $O$ be an order in a number
field $K$ and $\mathfrak{b} \neq 0$ an ideal of $O$. Then some positive integer $m$ lies in
$\mathfrak{b}$ (F. Keune, *Number Fields*, 2023, proof of Lemma 3.17, p. 57, for
$O = \mathcal{O}_K$). -/
theorem exists_natCast_mem (hO : NumberField.IsOrder K O) {b : Ideal O} (hb : b ≠ ⊥) :
    ∃ m : ℕ, 0 < m ∧ (m : O) ∈ b := by
  obtain ⟨β, hβb, hβ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨m, hm, hmem⟩ := hO.exists_natCast_mem_span_singleton hβ
  exact ⟨m, hm, (Ideal.span_singleton_le_iff_mem b).mpr hβb hmem⟩

/-- **A number field is the localization of an order at the nonzero integers.** Let $O$ be an
order in a number field $K$. Then $K$, with the inclusion $O \subseteq K$, is the localization
of $O$ at the image of the nonzero integers: every element of $K$ is $a/m$ with $a \in O$ and
$m$ a positive integer. -/
theorem isLocalization (hO : NumberField.IsOrder K O) :
    IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)) K where
  map_units y := by
    obtain ⟨y, n, hn, rfl⟩ := y
    rw [← IsScalarTower.algebraMap_apply ℤ O K, isUnit_iff_ne_zero, eq_intCast,
      Int.cast_ne_zero]
    exact nonZeroDivisors.ne_zero hn
  surj z := by
    obtain ⟨a, b, hb, rfl⟩ := hO.exists_div_eq z
    obtain ⟨m, hm, hmem⟩ := hO.exists_natCast_mem_span_singleton hb
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    have hbK : (b : K) ≠ 0 := fun h => hb (Subtype.ext h)
    refine ⟨⟨a * t, ⟨(m : O), (m : ℤ),
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm.ne'), by simp⟩⟩, ?_⟩
    change (a : K) / b * ((m : O) : K) = ((a * t : O) : K)
    rw [← ht]
    push_cast
    field_simp
  exists_of_eq {x y} h := ⟨1, by rw [Subtype.ext h]⟩

/-- **An order is a finitely generated abelian group.** Let $O$ be an order in a number field
$K$. Then $O$ is a finitely generated $\mathbb{Z}$-module, as a submodule of the finitely
generated $\mathbb{Z}$-module $\mathcal{O}_K$. -/
theorem moduleFinite (hO : NumberField.IsOrder K O) : Module.Finite ℤ O := by
  have : IsNoetherian ℤ (NumberField.RingOfIntegers K) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ (NumberField.RingOfIntegers K)
  have : IsNoetherian ℤ (integralClosure ℤ K) :=
    inferInstanceAs (IsNoetherian ℤ (NumberField.RingOfIntegers K))
  exact Module.Finite.of_injective (Subalgebra.inclusion hO.le_integralClosure).toLinearMap
    (Subalgebra.inclusion_injective hO.le_integralClosure)

/-- **An order is a free abelian group.** Let $O$ be an order in a number field $K$. Then $O$ is
a free $\mathbb{Z}$-module: it is finitely generated and torsion-free. -/
theorem moduleFree (hO : NumberField.IsOrder K O) : Module.Free ℤ O := by
  have := hO.moduleFinite
  exact Module.free_of_finite_type_torsion_free'

/-- **The rank of an order.** Let $O$ be an order in a number field $K$. Then $O$ is a free
$\mathbb{Z}$-module of rank $[K : \mathbb{Q}]$: a $\mathbb{Z}$-basis of $O$ is a
$\mathbb{Q}$-basis of $K$. -/
theorem finrank_eq (hO : NumberField.IsOrder K O) : finrank ℤ O = finrank ℚ K := by
  have := hO.moduleFinite
  have := hO.moduleFree
  have := hO.isLocalization
  let b := Module.Free.chooseBasis ℤ O
  rw [finrank_eq_card_basis b,
    finrank_eq_card_basis (b.localizationLocalization ℚ (nonZeroDivisors ℤ) K)]

/-- **The index of a principal ideal of an order, as an integer norm.** Let $O$ be an order in
a number field $K$ and $\beta \in O$, $\beta \neq 0$. Then
$\#(O/\beta O) = |N_{O/\mathbb{Z}}(\beta)|$, where $N_{O/\mathbb{Z}}(\beta)$ (`Algebra.norm ℤ`)
is the determinant of multiplication by $\beta$ on the free $\mathbb{Z}$-module $O$. -/
theorem natCard_quotient_span_singleton (hO : NumberField.IsOrder K O) {β : O} (hβ : β ≠ 0) :
    Nat.card (O ⧸ Ideal.span {β}) = (Algebra.norm ℤ β).natAbs := by
  have := hO.moduleFinite
  have := hO.moduleFree
  let N : Submodule ℤ O := (Ideal.span {β}).restrictScalars ℤ
  let f : O →+ N :=
    { toFun := fun x => ⟨β * x, Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self β)⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [mul_add] }
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · exact mul_left_cancel₀ hβ (congrArg Subtype.val hxy)
    · obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp z.2
      exact ⟨a, Subtype.ext (by simp [f, ← ha, mul_comm])⟩
  have h := Submodule.natAbs_det_equiv N (AddEquiv.ofBijective f hf)
  have hlin : N.subtype ∘ₗ ((AddEquiv.ofBijective f hf : O ≃+ N) : O →+ N).toIntLinearMap =
      Algebra.lmul ℤ O β :=
    LinearMap.ext fun x => rfl
  rw [hlin, ← Algebra.norm_apply] at h
  rw [h]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {β})).toEquiv.symm

/-- **The index of a principal ideal of an order.** Let $K$ be a number field, $O$ an order in
$K$ (`NumberField.IsOrder`), and for $\beta \in K$ let $N_{K/\mathbb{Q}}(\beta)$
(`Algebra.norm ℚ`) be the determinant of the $\mathbb{Q}$-linear map $x \mapsto \beta x$ of
$K$. Then for every nonzero $\beta \in O$,
$$[O : \beta O] = \#(O/\beta O) = \bigl|N_{K/\mathbb{Q}}(\beta)\bigr|,$$
as an identity of rational numbers.

This is A. V. Sutherland, MIT 18.783 Lecture 17 (Fall 2023), Lemma 17.5 (p. 3), with the norm of
Definition 17.3 (p. 2), and K. Conrad, *The conductor ideal of an order*, footnote 4 (p. 14);
F. Keune, *Number Fields*, 2023, Proposition 3.20 (p. 58), proves it for $O = \mathcal{O}_K$. -/
theorem natCard_quotient_span_singleton_eq_abs_norm (hO : NumberField.IsOrder K O) {β : O}
    (hβ : β ≠ 0) :
    (Nat.card (O ⧸ Ideal.span {β}) : ℚ) = |Algebra.norm ℚ (β : K)| := by
  have := hO.moduleFinite
  have := hO.moduleFree
  have := hO.isLocalization
  rw [hO.natCard_quotient_span_singleton hβ, Nat.cast_natAbs, Int.cast_abs]
  congr 1
  have h := Algebra.norm_localization ℤ (Rₘ := ℚ) (Sₘ := K) (nonZeroDivisors ℤ) β
  rw [eq_intCast] at h
  exact h.symm

/-- **The index of the ideal generated by a positive integer.** Let $O$ be an order in a number
field $K$ of degree $n = [K : \mathbb{Q}]$ and $m$ a positive integer. Then
$\#(O/mO) = m^n$. -/
theorem natCard_quotient_natCast (hO : NumberField.IsOrder K O) {m : ℕ} (hm : 0 < m) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ finrank ℚ K := by
  have := hO.moduleFree
  have hm0 : (m : O) ≠ 0 := by
    intro h
    have h' : ((m : O) : K) = 0 := by rw [h]; rfl
    push_cast at h'
    exact hm.ne' (by exact_mod_cast h')
  rw [hO.natCard_quotient_span_singleton hm0, ← hO.finrank_eq,
    show (m : O) = algebraMap ℤ O (m : ℤ) by simp, Algebra.norm_algebraMap, Int.natAbs_pow,
    Int.natAbs_natCast]

/-- **The index of an ideal containing a positive integer.** Let $O$ be an order in a number
field $K$ of degree $n$, $\mathfrak{b}$ an ideal of $O$ and $m$ a positive integer in
$\mathfrak{b}$. Then $\#(O/\mathfrak{b})$ divides $m^n$. -/
theorem natCard_quotient_dvd_pow (hO : NumberField.IsOrder K O) {b : Ideal O} {m : ℕ}
    (hm : 0 < m) (hmb : (m : O) ∈ b) : Nat.card (O ⧸ b) ∣ m ^ finrank ℚ K := by
  rw [← hO.natCard_quotient_natCast hm]
  exact Ideal.natCard_quotient_dvd_of_le ((Ideal.span_singleton_le_iff_mem b).mpr hmb)

/-- **Nonzero ideals of an order have finite index.** Let $O$ be an order in a number field $K$
and $\mathfrak{b} \neq 0$ an ideal of $O$. Then the ring $O/\mathfrak{b}$ is finite (Mathlib's
`Ideal.finiteQuotientOfFreeOfNeBot`, as $O$ is a finite free $\mathbb{Z}$-module). -/
theorem finite_quotient (hO : NumberField.IsOrder K O) {b : Ideal O} (hb : b ≠ ⊥) :
    Finite (O ⧸ b) := by
  have := hO.moduleFinite
  have := hO.moduleFree
  exact Ideal.finiteQuotientOfFreeOfNeBot b hb

/-- **Nonzero prime ideals of an order are maximal.** Let $O$ be an order in a number field $K$
and $\mathfrak{p} \neq 0$ a prime ideal of $O$. Then $\mathfrak{p}$ is a maximal ideal: the
finite integral domain $O/\mathfrak{p}$ is a field. -/
theorem isMaximal_of_isPrime (hO : NumberField.IsOrder K O) {b : Ideal O} (hb : b ≠ ⊥)
    [b.IsPrime] : b.IsMaximal := by
  have := hO.finite_quotient hb
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

/-- **Nonzero ideals of an order have finite index.** Let $K$ be a number field of degree
$n = [K : \mathbb{Q}]$, let $O$ be an order in $K$ (`NumberField.IsOrder`: a subring of $K$
contained in $\mathcal{O}_K$ with fraction field $K$; it is then a free $\mathbb{Z}$-module of
rank $n$, `NumberField.IsOrder.finrank_eq`), and let $\mathfrak{b}$ be a nonzero ideal of $O$.
Then:
1. $\mathfrak{b}$ contains a positive integer $m$;
2. the ring $O/\mathfrak{b}$ is finite, and its number of elements divides $m^n$ for every
   positive integer $m \in \mathfrak{b}$;
3. if $\mathfrak{b}$ is a prime ideal, it is a maximal ideal of $O$.

F. Keune, *Number Fields*, 2023, Lemma 3.17 with its proof (p. 57), proves (1) and (2) for
$O = \mathcal{O}_K$; A. V. Sutherland, MIT 18.783 Lecture 17 (Fall 2023), Definition 17.4
(p. 3), uses $[O : \mathfrak{a}] = \#(O/\mathfrak{a}) \in \mathbb{Z}_{>0}$ for a nonzero ideal of an
order. -/
theorem ideal_finite_index (hO : NumberField.IsOrder K O) {b : Ideal O} (hb : b ≠ ⊥) :
    (∃ m : ℕ, 0 < m ∧ (m : O) ∈ b) ∧ Finite (O ⧸ b) ∧
      (∀ m : ℕ, 0 < m → (m : O) ∈ b → Nat.card (O ⧸ b) ∣ m ^ finrank ℚ K) ∧
      (b.IsPrime → b.IsMaximal) :=
  ⟨hO.exists_natCast_mem hb, hO.finite_quotient hb,
    fun _ hm hmb => hO.natCard_quotient_dvd_pow hm hmb,
    fun h => by have := h; exact hO.isMaximal_of_isPrime hb⟩

/-- **The multiplier ring of an ideal coprime to the conductor.** Let $K$ be a number field with
ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`), let $O$ be an order in $K$
(`NumberField.IsOrder`), and let
$\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq O\}$ be its conductor, the
conductor ideal (`Subalgebra.conductorIdeal`) of $O$ viewed as a subring of $\mathcal{O}_K$. Let
$\mathfrak{b}$ be a nonzero ideal of $O$ with $\mathfrak{b} + \mathfrak{c} = O$, where
$\mathfrak{c} \subseteq O$ is viewed as an ideal of $O$ (its preimage under
$O \hookrightarrow \mathcal{O}_K$). Then
$$\{x \in K : x\mathfrak{b} \subseteq \mathfrak{b}\} = O.$$

This is K. Conrad, *The conductor ideal of an order*, Theorem 3.1 (p. 5), with the conductor of
Definition 1.1 (p. 1). -/
theorem setOf_mul_mem_eq (hO : NumberField.IsOrder K O) {b : Ideal O} (hb : b ≠ ⊥)
    (hbc : b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure) = ⊤) :
    {x : K | ∀ y ∈ b, ∃ z ∈ b, (z : K) = x * y} = (O : Set K) := by
  have := hO.moduleFinite
  have : IsNoetherian ℤ O := isNoetherian_of_isNoetherianRing_of_finite ℤ O
  ext x
  constructor
  · intro hx
    let N : Submodule ℤ K := (b.restrictScalars ℤ).map (O.val.toLinearMap)
    have hN0 : N ≠ ⊥ := by
      obtain ⟨β, hβb, hβ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      exact (Submodule.ne_bot_iff _).mpr ⟨β, ⟨β, hβb, rfl⟩, fun h => hβ (Subtype.ext h)⟩
    have hNfg : N.FG := (IsNoetherian.noetherian (b.restrictScalars ℤ)).map _
    have hxN : ∀ n ∈ N, x • n ∈ N := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hx y hy
      exact ⟨z, hz, by simpa [smul_eq_mul] using hzx⟩
    have hxint : IsIntegral ℤ x := isIntegral_of_smul_mem_submodule N hN0 hNfg x hxN
    have h1 : (1 : O) ∈ b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
        (Subalgebra.inclusion hO.le_integralClosure) := hbc ▸ Submodule.mem_top
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp h1
    obtain ⟨z, hz, hzx⟩ := hx β hβ
    have hγx : (γ : K) * x ∈ O :=
      Subalgebra.mem_conductorIdeal.mp (Ideal.mem_comap.mp hγ) ⟨x, hxint⟩
    have hβγK : (β : K) + γ = 1 := congrArg Subtype.val hβγ
    have hxe : x = (z : K) + (γ : K) * x := by
      rw [hzx]
      linear_combination (-x) * hβγK
    rw [SetLike.mem_coe, hxe]
    exact O.add_mem z.2 hγx
  · intro hxO y hy
    exact ⟨⟨x, hxO⟩ * y, b.mul_mem_left _ hy, rfl⟩

end NumberField.IsOrder

end
