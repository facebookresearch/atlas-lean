/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.Order.LiminfLimsup
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic

@[expose] public section

namespace MathlibExt.FieldTheory.EssentialDimensionSymmetric

open Polynomial MvPolynomial IntermediateField Filter

/-!
# Essential dimension of symmetric groups via the general polynomial

For `n ≥ 1`, let `Eₙ = ℂ(x₁, …, xₙ)` be the function field in `n`
indeterminates and let `Fₙ = ℂ(a₁, …, aₙ) ⊆ Eₙ`, where `aₖ` is the
`k`-th elementary symmetric function of the `xᵢ`. The extension
`Eₙ / Fₙ` is the splitting field extension of the general polynomial
`Xⁿ - a₁Xⁿ⁻¹ + ⋯ + (-1)ⁿaₙ`.

A *descent* is a pair of intermediate fields `F₀ ⊆ Fₙ` and `E₀ ⊆ Eₙ`
with `F₀ ⊆ E₀`, `E₀ ⊓ Fₙ = F₀`, `E₀ ⊔ Fₙ = Eₙ`, such that `E₀` is
generated over `F₀` by the roots in `Eₙ` of a separable polynomial over
`F₀` splitting in `Eₙ`. The essential dimension `edSn n` is the least
transcendence degree of such an `F₀`: the least number of parameters
needed to define the general polynomial up to Tschirnhaus
transformation. Buhler--Reichstein proved this parameter count equals
the essential dimension `ed_ℂ(Sₙ)`; the catalogue defines `C₇₉` through
this polynomial formulation, and that identification is the scope of
this file (the equivalence with the torsor-theoretic essential
dimension for arbitrary `Sₙ`-torsors is not formalized).

Main results: the coefficient fields have transcendence degree `n`,
the trivial descent gives `edSn n ≤ n`, and therefore the asymptotic
ratio `essDimRatio = limsup (edSn n / n)` satisfies `essDimRatio ≤ 1`.

Source: Optimization Problems, constants/79a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`.
-/

/-- **The function field $\mathbb{C}(x_1, \dots, x_n)$.** For $n \in \mathbb{N}$, the function
field $\mathbb{C}(x_1, \dots, x_n)$ is the fraction field of the polynomial ring
$\mathbb{C}[x_1, \dots, x_n]$ in $n$ indeterminates. -/
abbrev rootsField (n : ℕ) : Type :=
  FractionRing (MvPolynomial (Fin n) ℂ)

/-- **The roots $x_i$.** For $n \in \mathbb{N}$ and $i \in \{1, \dots, n\}$, $x_i$ is the $i$-th
indeterminate of the polynomial ring $\mathbb{C}[x_1, \dots, x_n]$, viewed as an element of its
fraction field, the function field $\mathbb{C}(x_1, \dots, x_n)$.

These elements are the roots of the general polynomial. -/
noncomputable def root (n : ℕ) (i : Fin n) : rootsField n :=
  algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) (X i)

/-- **The coefficients of the general polynomial.** For $0 \le i < n$, the coefficient
$a_{i+1}$ is the $(i+1)$-st elementary symmetric function of $x_1, \dots, x_n$, as an element of
the function field $\mathbb{C}(x_1, \dots, x_n)$. -/
noncomputable def coeff (n : ℕ) (i : Fin n) : rootsField n :=
  algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n)
    (esymm (Fin n) ℂ (i.val + 1))

/-- **Coefficient field of the general polynomial.** For a natural number $n$, let
$\mathbb{C}(x_1, \dots, x_n)$ be the field of rational functions in $n$ indeterminates and,
for $1 \le k \le n$, let $a_k$ be the $k$-th elementary symmetric function of
$x_1, \dots, x_n$. The coefficient field $\mathbb{C}(a_1, \dots, a_n)$ is the intermediate
field of $\mathbb{C} \subseteq \mathbb{C}(x_1, \dots, x_n)$ generated over $\mathbb{C}$ by
$a_1, \dots, a_n$. -/
noncomputable def generalBaseField (n : ℕ) :
    IntermediateField ℂ (rootsField n) :=
  IntermediateField.adjoin ℂ (Set.range (coeff n))

/-- **Coefficients in the coefficient field.** For $0 \le i < n$, the coefficient $a_{i+1}$,
the $(i+1)$-st elementary symmetric function of $x_1, \dots, x_n$, regarded as an element of the
coefficient field $\mathbb{C}(a_1, \dots, a_n)$. -/
noncomputable def coeffElem (n : ℕ) (i : Fin n) : ↥(generalBaseField n) :=
  ⟨coeff n i, by exact (IntermediateField.subset_adjoin ℂ _) (Set.mem_range_self i)⟩

theorem val_coeffElem (n : ℕ) (i : Fin n) :
    ((coeffElem n i : ↥(generalBaseField n)) : rootsField n) = coeff n i :=
  rfl

/-- **The roots $x_i$ are pairwise distinct.** For every $n \in \mathbb{N}$, the elements
$x_1, \dots, x_n$ of the function field $\mathbb{C}(x_1, \dots, x_n)$ are pairwise distinct:
$x_i = x_j$ implies $i = j$. -/
theorem root_injective (n : ℕ) : Function.Injective (root n) := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n)) :=
    IsFractionRing.injective _ _
  intro i j h
  have h2 : (X i : MvPolynomial (Fin n) ℂ) = X j := hinj h
  exact MvPolynomial.X_injective h2

/-- **Algebraic independence of the elementary symmetric polynomials.** For every natural number
$n$, the elementary symmetric polynomials $e_1, \dots, e_n \in \mathbb{C}[X_1, \dots, X_n]$ are
algebraically independent over $\mathbb{C}$.

This follows from the fundamental theorem of symmetric polynomials. -/
theorem algebraicIndependent_esymm (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun i : Fin n => esymm (Fin n) ℂ (i.val + 1) :
        Fin n → MvPolynomial (Fin n) ℂ) := by
  have h1 : (MvPolynomial.aeval (fun i : Fin n => esymm (Fin n) ℂ (i.val + 1)) :
        MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ) =
      (symmetricSubalgebra (Fin n) ℂ).val.comp
        (esymmAlgEquiv (Fin n) ℂ (by simp)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [esymmAlgEquiv, esymmAlgHom]
  show Function.Injective _
  rw [h1]
  exact Subtype.val_injective.comp (AlgEquiv.injective _)

/-- **Injective algebra maps preserve algebraic independence.** Let $A$ and $B$ be commutative
$\mathbb{C}$-algebras, let $f : A \to B$ be an injective $\mathbb{C}$-algebra homomorphism, and
let $(x_i)_{i \in \iota}$ be a family in $A$ that is algebraically independent over
$\mathbb{C}$. Then the family $(f(x_i))_{i \in \iota}$ is algebraically independent over
$\mathbb{C}$. -/
theorem algebraicIndependent_map {ι : Type*} {A B : Type*}
    [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    {x : ι → A} (hx : AlgebraicIndependent ℂ x) (f : A →ₐ[ℂ] B)
    (hf : Function.Injective f) :
    AlgebraicIndependent ℂ (f ∘ x) := by
  have hcomp : MvPolynomial.aeval (f ∘ x) = f.comp (MvPolynomial.aeval x) := by
    ext i
    simp
  show Function.Injective (MvPolynomial.aeval (f ∘ x))
  rw [hcomp]
  exact hf.comp hx

/-- **The coefficients are algebraically independent.** For every natural number $n$, the
coefficients $a_1, \dots, a_n$ of the general polynomial, the elementary symmetric functions of
$x_1, \dots, x_n$, are algebraically independent over $\mathbb{C}$ in the function field
$\mathbb{C}(x_1, \dots, x_n)$. -/
theorem algebraicIndependent_coeff (n : ℕ) :
    AlgebraicIndependent ℂ (coeff n) := by
  classical
  let f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] rootsField n :=
    { algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) with
      commutes' := fun r =>
        (IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin n) ℂ)
          (rootsField n) r).symm }
  have hco : coeff n =
      f ∘ (fun i : Fin n => esymm (Fin n) ℂ (i.val + 1)) := rfl
  rw [hco]
  exact algebraicIndependent_map (algebraicIndependent_esymm n) f
    (IsFractionRing.injective _ _)

/-- **The roots are algebraically independent.** For every natural number $n$, the roots
$x_1, \dots, x_n$ are algebraically independent over $\mathbb{C}$ in the function field
$\mathbb{C}(x_1, \dots, x_n)$. -/
theorem algebraicIndependent_root (n : ℕ) :
    AlgebraicIndependent ℂ (root n) := by
  classical
  let f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] rootsField n :=
    { algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) with
      commutes' := fun r =>
        (IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin n) ℂ)
          (rootsField n) r).symm }
  have hro : root n = f ∘ (X : Fin n → MvPolynomial (Fin n) ℂ) := rfl
  rw [hro]
  exact algebraicIndependent_map (algebraicIndependent_X (Fin n) ℂ) f
    (IsFractionRing.injective _ _)

/-- **Polynomials in the roots.** For every natural number $n$ and every polynomial
$p \in \mathbb{C}[X_1, \dots, X_n]$, the image of $p$ in the function field
$\mathbb{C}(x_1, \dots, x_n)$ lies in the $\mathbb{C}$-subalgebra generated by the roots
$x_1, \dots, x_n$. -/
theorem algebraMap_mem_adjoin_roots (n : ℕ)
    (p : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) p ∈
      Algebra.adjoin ℂ (Set.range (root n)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) (C a) =
        algebraMap ℂ (rootsField n) a := by
      rw [show (C a : MvPolynomial (Fin n) ℂ) = algebraMap ℂ _ a by
        simp [MvPolynomial.algebraMap_eq]]
      exact (IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin n) ℂ)
        (rootsField n) a).symm
    rw [h]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    exact Algebra.subset_adjoin ⟨i, rfl⟩

/-- **Rational functions are algebraic over the polynomial subalgebra.** For a natural number
$n$, every element of the field $\mathbb{C}(x_1, \dots, x_n)$ of rational functions in $n$
indeterminates is algebraic over the $\mathbb{C}$-subalgebra generated by $x_1, \dots, x_n$:
it is a ratio of two polynomials in $x_1, \dots, x_n$. -/
theorem isAlgebraic_adjoin_roots (n : ℕ) :
    Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range (root n)))
      (rootsField n) := by
  rw [Algebra.isAlgebraic_iff]
  intro z _hz
  obtain ⟨⟨p, q⟩, hz⟩ :=
    IsLocalization.surj (nonZeroDivisors (MvPolynomial (Fin n) ℂ)) z
  have hq0 : (q : MvPolynomial (Fin n) ℂ) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp q.2
  have hqimg : algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) (q : _) ≠ 0 := by
    intro h
    apply hq0
    apply IsFractionRing.injective (MvPolynomial (Fin n) ℂ) (rootsField n)
    rw [h, map_zero]
  refine ⟨(Polynomial.C
      (⟨algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n)
        (q : MvPolynomial (Fin n) ℂ), algebraMap_mem_adjoin_roots n q⟩ :
        ↥(Algebra.adjoin ℂ (Set.range (root n)))) * Polynomial.X -
    Polynomial.C
      (⟨algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) p,
        algebraMap_mem_adjoin_roots n p⟩ :
        ↥(Algebra.adjoin ℂ (Set.range (root n)))) :
      Polynomial (Algebra.adjoin ℂ (Set.range (root n)))), ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (Polynomial.coeff · 1) hzero
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, Polynomial.coeff_C,
      if_neg (by norm_num : (1 : ℕ) ≠ 0), sub_zero, Polynomial.coeff_zero] at hcoeff
    exact hqimg (congrArg Subtype.val hcoeff)
  · dsimp only at hz
    rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_eq_zero_of_eq (by rw [mul_comm]; exact hz)

/-- **Transcendence degree of $\mathbb{C}(x_1, \dots, x_n)$.** For every $n \in \mathbb{N}$, the
function field $\mathbb{C}(x_1, \dots, x_n)$ has transcendence degree $n$ over $\mathbb{C}$, as a
cardinal. -/
theorem trdeg_rootsField (n : ℕ) :
    Algebra.trdeg ℂ (rootsField n) = Cardinal.mk (Fin n) := by
  apply le_antisymm
  · haveI := isAlgebraic_adjoin_roots n
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := ℂ)
      (s := Set.range (root n)) (A := rootsField n)
    have hEq : Cardinal.mk (Set.range (root n)) = Cardinal.mk (Fin n) :=
      Cardinal.lift_inj.mp (Cardinal.mk_range_eq_of_injective
        (root_injective n))
    rwa [hEq] at h
  · exact (algebraicIndependent_root n).cardinalMk_le_trdeg

/-- **Numeric transcendence degree.** For a field $F$ that is a $\mathbb{C}$-algebra, the numeric
transcendence degree of $F$ is its transcendence degree over $\mathbb{C}$ as a natural number when
that degree is finite, and $0$ when it is infinite. -/
noncomputable def transDegNat (F : Type) [Field F] [Algebra ℂ F] : ℕ :=
  (Algebra.trdeg ℂ F).toNat

theorem transDegNat_eq_of_trdeg_eq {F : Type} [Field F] [Algebra ℂ F]
    {n : ℕ} (h : Algebra.trdeg ℂ F = Cardinal.mk (Fin n)) :
    transDegNat F = n := by
  rw [transDegNat, h]
  simp

theorem transDegNat_rootsField (n : ℕ) :
    transDegNat (rootsField n) = n :=
  transDegNat_eq_of_trdeg_eq (trdeg_rootsField n)

/-- **Elementary symmetric polynomials evaluated at the roots.** For all natural numbers $n$
and $k$, the image of the $k$-th elementary symmetric polynomial
$e_k \in \mathbb{C}[X_1, \dots, X_n]$ in the function field $\mathbb{C}(x_1, \dots, x_n)$ is the
$k$-th elementary symmetric function of the multiset of roots $\{x_1, \dots, x_n\}$, that is,
the sum of the products $x_{i_1} \cdots x_{i_k}$ over all $i_1 < \dots < i_k$. -/
theorem algebraMap_esymm (n k : ℕ) :
    algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n)
        (esymm (Fin n) ℂ k) =
      (Finset.univ.val.map (root n)).esymm k := by
  rw [Multiset.esymm, Multiset.powersetCard_map,
    ← Finset.map_val_val_powersetCard, Multiset.map_map]
  rw [MvPolynomial.esymm, map_sum]
  show ((Finset.powersetCard k Finset.univ).val.map
      (fun x => algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n)
        (∏ i ∈ x, MvPolynomial.X i))).sum = _
  rw [Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl (fun t _ => ?_)
  rw [Function.comp_def, Function.comp_def, map_prod]
  rfl

/-- **Coefficients indexed by degree.** Let $n$ be a natural number, for $1 \le k \le n$ let $a_k$
be the $k$-th elementary symmetric function of $x_1, \dots, x_n$ in the function field
$\mathbb{C}(x_1, \dots, x_n)$, and let $\mathbb{C}(a_1, \dots, a_n)$ be the coefficient field. For
each natural number $k$, the element $c_k$ of $\mathbb{C}(a_1, \dots, a_n)$ is defined by
$c_0 = 1$, $c_k = a_k$ for $1 \le k \le n$, and $c_k = 0$ for $k > n$.

In a variable $X$, the general polynomial is $\sum_{k=0}^{n} (-1)^k c_k X^{n-k}$. -/
noncomputable def coeffNat (n : ℕ) (k : ℕ) : ↥(generalBaseField n) :=
  if h0 : k = 0 then 1
  else if h2 : k ≤ n then
    coeffElem n ⟨k - 1, Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero h0) h2⟩
  else 0

theorem val_coeffNat (n k : ℕ) :
    ((coeffNat n k : ↥(generalBaseField n)) : rootsField n) =
      (Finset.univ.val.map (root n)).esymm k := by
  rw [coeffNat]
  by_cases h0 : k = 0
  · rw [dif_pos h0, h0]
    simp [Multiset.esymm_zero]
  · rw [dif_neg h0]
    by_cases hkn : k ≤ n
    · rw [dif_pos hkn]
      have hk : (⟨k - 1, Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero h0) hkn⟩ : Fin n).val + 1 = k := by
        show k - 1 + 1 = k
        omega
      rw [val_coeffElem, coeff, hk]
      exact algebraMap_esymm n k
    · rw [dif_neg hkn]
      have hcard : Multiset.card (Finset.univ.val.map (root n)) = n := by
        simp
      have hlt : Multiset.card (Finset.univ.val.map (root n)) < k := by
        omega
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty k hlt]
      simp

/-- **General polynomial.** For a natural number $n$, let $x_1, \dots, x_n$ be the
indeterminates of the rational function field $\mathbb{C}(x_1, \dots, x_n)$, let $a_0 = 1$ and,
for $1 \le k \le n$, let $a_k$ be the $k$-th elementary symmetric function of
$x_1, \dots, x_n$. The general polynomial of degree $n$ is the polynomial
$\sum_{j=0}^{n} (-1)^j a_j X^{n-j} = X^n - a_1 X^{n-1} + \cdots + (-1)^n a_n$ with
coefficients in the coefficient field $\mathbb{C}(a_1, \dots, a_n)$. -/
noncomputable def generalPolynomial (n : ℕ) :
    Polynomial (generalBaseField n) :=
  ∑ j ∈ Finset.range (n + 1),
    (-1) ^ j * (Polynomial.C (coeffNat n j) * Polynomial.X ^ (n - j))

theorem map_generalPolynomial (n : ℕ) :
    (generalPolynomial n).map
        (algebraMap (generalBaseField n) (rootsField n)) =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (root n i)) := by
  have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (root n i))) =
      ((Finset.univ.val.map (root n)).map
        fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.map_map]
    rfl
  have hcard : Multiset.card (Finset.univ.val.map (root n)) = n := by
    simp
  rw [hprod, Multiset.prod_X_sub_X_eq_sum_esymm, hcard, generalPolynomial,
    Polynomial.map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
    Polynomial.map_C, Polynomial.map_X]
  rw [show algebraMap (generalBaseField n) (rootsField n) (coeffNat n j) =
      ((coeffNat n j : ↥(generalBaseField n)) : rootsField n) from rfl,
    val_coeffNat]

/-- **Distinct linear factors are coprime.** For a natural number $n$ and distinct elements
$a \ne b$ of the field $\mathbb{C}(x_1, \dots, x_n)$ of rational functions in $n$
indeterminates, the polynomials $X - a$ and $X - b$ are coprime in
$\mathbb{C}(x_1, \dots, x_n)[X]$: there are polynomials $u$ and $v$ with
$u (X - a) + v (X - b) = 1$. -/
theorem isCoprime_X_sub_C_of_ne (n : ℕ) {a b : rootsField n} (h : a ≠ b) :
    IsCoprime (Polynomial.X - Polynomial.C a)
      (Polynomial.X - Polynomial.C b) := by
  have hba : (b - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  refine ⟨Polynomial.C (b - a)⁻¹, -Polynomial.C (b - a)⁻¹, ?_⟩
  have h2 : (Polynomial.X - Polynomial.C a) -
        (Polynomial.X - Polynomial.C b) =
      Polynomial.C (b - a) := by
    rw [sub_sub_sub_cancel_left, ← map_sub]
  exact calc Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C a) +
        -Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C b)
      = Polynomial.C (b - a)⁻¹ *
          ((Polynomial.X - Polynomial.C a) -
            (Polynomial.X - Polynomial.C b)) := by ring
    _ = Polynomial.C (b - a)⁻¹ * Polynomial.C (b - a) := by rw [h2]
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hba, map_one]

/-- **The product of the linear factors $X - x_i$ is separable.** For every $n \in \mathbb{N}$,
the polynomial $\prod_{i=1}^{n} (X - x_i)$ over the function field
$\mathbb{C}(x_1, \dots, x_n)$ is separable. -/
theorem separable_prod_roots (n : ℕ) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (root n i))).Separable := by
  have key : ∀ s : Finset (Fin n),
      (∏ i ∈ s, (Polynomial.X - Polynomial.C (root n i))).Separable := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.prod_insert has]
      refine Polynomial.Separable.mul Polynomial.separable_X_sub_C ih ?_
      refine IsCoprime.prod_right (fun i hi => ?_)
      refine isCoprime_X_sub_C_of_ne n ?_
      exact (root_injective n).ne (fun h => has (h ▸ hi))
  exact key Finset.univ

/-- **The roots generate the function field.** For every natural number $n$, the intermediate
field of $\mathbb{C}(x_1, \dots, x_n)$ generated over $\mathbb{C}$ by the roots
$x_1, \dots, x_n$ is the whole function field $\mathbb{C}(x_1, \dots, x_n)$. -/
theorem adjoin_roots_eq_top (n : ℕ) :
    IntermediateField.adjoin ℂ (Set.range (root n)) = ⊤ := by
  apply top_unique
  intro z _hz
  obtain ⟨⟨p, q⟩, hz⟩ :=
    IsLocalization.surj (nonZeroDivisors (MvPolynomial (Fin n) ℂ)) z
  have hq0 : (q : MvPolynomial (Fin n) ℂ) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp q.2
  have hqimg : algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) (q : _) ≠ 0 := by
    intro h
    apply hq0
    apply IsFractionRing.injective (MvPolynomial (Fin n) ℂ) (rootsField n)
    rw [h, map_zero]
  have hle : Algebra.adjoin ℂ (Set.range (root n)) ≤
      (IntermediateField.adjoin ℂ (Set.range (root n))).toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    exact (IntermediateField.subset_adjoin ℂ _) hx
  dsimp only at hz
  have hz2 : z = algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) p /
      algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) (q : _) := by
    rw [eq_div_iff hqimg]
    exact hz
  rw [hz2]
  exact div_mem (hle (algebraMap_mem_adjoin_roots n p))
    (hle (algebraMap_mem_adjoin_roots n q))

/-- **Each $x_i$ is a root of the general polynomial.** For $n \in \mathbb{N}$, let
$E_n = \mathbb{C}(x_1, \dots, x_n)$, let $a_k$ be the $k$-th elementary symmetric function of
$x_1, \dots, x_n$, and let $f_n = X^n - a_1 X^{n-1} + \cdots + (-1)^n a_n$ be the general
polynomial, with coefficients in $F_n = \mathbb{C}(a_1, \dots, a_n) \subseteq E_n$. Then
$f_n(x_i) = 0$ in $E_n$ for every $i \in \{1, \dots, n\}$. -/
theorem root_mem_generalPolynomial_roots (n : ℕ) (i : Fin n) :
    Polynomial.aeval (root n i) (generalPolynomial n) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    map_generalPolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- **Transcendence degree of the coefficient field.** For $n \in \mathbb{N}$, let $a_k$ be the
$k$-th elementary symmetric function of $x_1, \dots, x_n$ in $\mathbb{C}(x_1, \dots, x_n)$. The
coefficient field $F_n = \mathbb{C}(a_1, \dots, a_n)$ of the general polynomial has numeric
transcendence degree $n$ over $\mathbb{C}$. -/
theorem transDegNat_generalBaseField (n : ℕ) :
    transDegNat (generalBaseField n) = n := by
  apply transDegNat_eq_of_trdeg_eq
  apply le_antisymm
  · have h := trdeg_le_of_injective
      (generalBaseField n).val Subtype.val_injective
    rwa [trdeg_rootsField] at h
  · have hindep : AlgebraicIndependent ℂ (coeffElem n) := by
      have hcomp : (generalBaseField n).val ∘ (coeffElem n) =
          coeff n := rfl
      apply AlgebraicIndependent.of_comp (generalBaseField n).val
      rw [hcomp]
      exact algebraicIndependent_coeff n
    exact hindep.cardinalMk_le_trdeg

/-- **Descent of the general polynomial extension.** For a natural number $n$, let
$E = \mathbb{C}(x_1, \dots, x_n)$ be the field of rational functions in $n$ indeterminates and
let $F = \mathbb{C}(a_1, \dots, a_n) \subseteq E$ be the coefficient field of the general
polynomial, where $a_k$ is the $k$-th elementary symmetric function of $x_1, \dots, x_n$. A
pair $(F_0, E_0)$ of intermediate fields of $\mathbb{C} \subseteq E$ is a descent when
$F_0 \subseteq F$, $F_0 \subseteq E_0$, $E_0 \cap F = F_0$, the compositum of $E_0$ and $F$ is
all of $E$, and there is a nonzero polynomial $p$ with coefficients in $F_0$ whose image in
$E[X]$ splits and is separable, such that $E_0$ is the field generated over $F_0$ by the
roots of $p$ in $E$.

Splitting and separability are imposed in $E$, where they say that the roots of $p$ are all
present and distinct. -/
def IsDescent (n : ℕ) (F0 E0 : IntermediateField ℂ (rootsField n)) :
    Prop :=
  F0 ≤ generalBaseField n ∧ F0 ≤ E0 ∧
    E0 ⊓ generalBaseField n = F0 ∧ E0 ⊔ generalBaseField n = ⊤ ∧
    ∃ p : Polynomial F0, p ≠ 0 ∧
      (p.map (algebraMap F0 (rootsField n))).Splits ∧
      (p.map (algebraMap F0 (rootsField n))).Separable ∧
      (IntermediateField.adjoin F0
        {x : rootsField n | Polynomial.aeval x p = 0}).restrictScalars
          ℂ = E0

/-- **The roots of the general polynomial generate the function field.** For $n \in \mathbb{N}$,
let $E_n = \mathbb{C}(x_1, \dots, x_n)$, let $a_k$ be the $k$-th elementary symmetric function
of $x_1, \dots, x_n$, let $F_n = \mathbb{C}(a_1, \dots, a_n) \subseteq E_n$ be the coefficient
field, and let $f_n = X^n - a_1 X^{n-1} + \cdots + (-1)^n a_n \in F_n[X]$ be the general
polynomial. The subfield of $E_n$ generated over $F_n$ by all roots of $f_n$ in $E_n$ is $E_n$
itself. -/
theorem restrictScalars_adjoin_generalPolynomial (n : ℕ) :
    (IntermediateField.adjoin (generalBaseField n)
      {x : rootsField n |
        Polynomial.aeval x (generalPolynomial n) = 0}).restrictScalars
        ℂ = ⊤ := by
  apply top_unique
  rw [← adjoin_roots_eq_top n]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  exact (IntermediateField.subset_adjoin (generalBaseField n) _)
    (root_mem_generalPolynomial_roots n i)

/-- **The trivial descent.** For every natural number $n$, the pair $(F, E)$ is a descent of
the general polynomial extension, where $E = \mathbb{C}(x_1, \dots, x_n)$ is the field of
rational functions in $n$ indeterminates and $F = \mathbb{C}(a_1, \dots, a_n)$ is the
coefficient field, generated over $\mathbb{C}$ by the elementary symmetric functions
$a_1, \dots, a_n$ of $x_1, \dots, x_n$.

The general polynomial serves as the defining polynomial of this descent. -/
theorem isDescent_generalBaseField (n : ℕ) :
    IsDescent n (generalBaseField n) ⊤ := by
  refine ⟨le_rfl, le_top, by simp, by simp,
    generalPolynomial n, ?_, ?_, ?_,
    restrictScalars_adjoin_generalPolynomial n⟩
  · intro hzero
    have hmap : (generalPolynomial n).map
        (algebraMap (generalBaseField n) (rootsField n)) ≠ 0 := by
      rw [map_generalPolynomial]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
        simp [Polynomial.X_sub_C_ne_zero])
    exact hmap (by rw [hzero]; simp)
  · rw [map_generalPolynomial]
    exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C _)
  · rw [map_generalPolynomial]
    exact separable_prod_roots n

/-- **Essential dimension of the symmetric group.** For a natural number $n$, let
$\mathbb{C}(x_1, \dots, x_n)$ be the field of rational functions in $n$ indeterminates. The
essential dimension of $S_n$ over $\mathbb{C}$, in the general-polynomial parameter sense, is
the least natural number $d$ such that some intermediate field $F_0$ of
$\mathbb{C} \subseteq \mathbb{C}(x_1, \dots, x_n)$ of transcendence degree at most $d$ over
$\mathbb{C}$ admits an intermediate field $E_0$ for which $(F_0, E_0)$ is a descent of the
general polynomial extension.

The transcendence degree is read as a natural number (an infinite degree would count as $0$;
this does not occur, since $F_0$ lies in the coefficient field). -/
noncomputable def edSn (n : ℕ) : ℕ :=
  sInf {d : ℕ | ∃ F0 E0 : IntermediateField ℂ (rootsField n),
    IsDescent n F0 E0 ∧ transDegNat F0 ≤ d}

/-- **Trivial upper bound for the essential dimension of $S_n$.** For every natural
number $n$, the essential dimension of the symmetric group $S_n$ over $\mathbb{C}$, in the
general-polynomial parameter sense, is at most $n$.

The bound comes from the trivial descent, whose parameter field is the coefficient field of
the general polynomial, of transcendence degree $n$. -/
theorem edSn_le (n : ℕ) : edSn n ≤ n := by
  apply Nat.sInf_le
  exact ⟨generalBaseField n, ⊤, isDescent_generalBaseField n,
    le_of_eq (transDegNat_generalBaseField n)⟩

/-- **Asymptotic essential-dimension ratio of the symmetric groups.** The catalogue constant
$C_{79}$ is the limit superior, as $n \to \infty$, of $\operatorname{ed}_{\mathbb{C}}(S_n) / n$,
where $\operatorname{ed}_{\mathbb{C}}(S_n)$ is the essential dimension of the symmetric group
$S_n$ over $\mathbb{C}$ in the general-polynomial parameter sense. -/
noncomputable def essDimRatio : ℝ :=
  Filter.limsup (fun n : ℕ => (edSn n : ℝ) / n) Filter.atTop

/-- **The essential-dimension ratio of the symmetric groups is at most one.** The constant
$C_{79}$, the limit superior as $n \to \infty$ of $\operatorname{ed}_{\mathbb{C}}(S_n) / n$ with
the essential dimension of $S_n$ over $\mathbb{C}$ taken in the general-polynomial parameter
sense, satisfies $C_{79} \le 1$. -/
theorem essDimRatio_le_one : essDimRatio ≤ 1 := by
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (edSn n : ℝ) / n ≤ 1 := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    rw [div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)]
    exact_mod_cast edSn_le n
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ => (edSn n : ℝ) / n) := by
    refine ⟨0, fun a ha => ?_⟩
    have h0 : ∀ᶠ x in Filter.map (fun n : ℕ => (edSn n : ℝ) / n)
        Filter.atTop, (0 : ℝ) ≤ x :=
      Filter.eventually_map.mpr
        (Filter.Eventually.of_forall (fun n => by positivity))
    obtain ⟨x, hx0, hxa⟩ := (h0.and ha).exists
    exact hx0.trans hxa
  show Filter.limsup (fun n : ℕ => (edSn n : ℝ) / n) Filter.atTop ≤ 1
  exact Filter.limsup_le_of_le hcob hev

end MathlibExt.FieldTheory.EssentialDimensionSymmetric
