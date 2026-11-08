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

/-- The function field `ℂ(x₁, …, xₙ)`. -/
abbrev rootsField (n : ℕ) : Type :=
  FractionRing (MvPolynomial (Fin n) ℂ)

/-- The root `xᵢ` of the general polynomial, as an element of the
function field. -/
noncomputable def root (n : ℕ) (i : Fin n) : rootsField n :=
  algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n) (X i)

/-- The coefficient `aₖ₊₁`: the `(k+1)`-st elementary symmetric
function of the roots, as an element of the function field. -/
noncomputable def coeff (n : ℕ) (i : Fin n) : rootsField n :=
  algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n)
    (esymm (Fin n) ℂ (i.val + 1))

/-- The coefficient field `ℂ(a₁, …, aₙ)` of the general polynomial. -/
noncomputable def generalBaseField (n : ℕ) :
    IntermediateField ℂ (rootsField n) :=
  IntermediateField.adjoin ℂ (Set.range (coeff n))

/-- The coefficient `aₖ₊₁` as an element of the coefficient field. -/
noncomputable def coeffElem (n : ℕ) (i : Fin n) : ↥(generalBaseField n) :=
  ⟨coeff n i, by exact (IntermediateField.subset_adjoin ℂ _) (Set.mem_range_self i)⟩

theorem val_coeffElem (n : ℕ) (i : Fin n) :
    ((coeffElem n i : ↥(generalBaseField n)) : rootsField n) = coeff n i :=
  rfl

/-- The roots are pairwise distinct. -/
theorem root_injective (n : ℕ) : Function.Injective (root n) := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) ℂ) (rootsField n)) :=
    IsFractionRing.injective _ _
  intro i j h
  have h2 : (X i : MvPolynomial (Fin n) ℂ) = X j := hinj h
  exact MvPolynomial.X_injective h2

/-- The elementary symmetric polynomials are algebraically independent,
by the fundamental theorem (`esymmAlgEquiv` is an isomorphism). -/
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

/-- Algebraic independence transports along injective algebra maps. -/
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

/-- The coefficients `a₁, …, aₙ` are algebraically independent in the
function field. -/
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

/-- The roots are algebraically independent in the function field. -/
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

/-- Every element of the polynomial ring maps into the subalgebra
generated by the roots. -/
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

/-- Every element of the function field is algebraic over the subalgebra
generated by the roots: it is a ratio of two polynomials in the roots. -/
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

/-- The transcendence degree of the function field over `ℂ` is `n`, as a
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

/-- The numeric transcendence degree of a field over `ℂ`. -/
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

/-- Evaluating an elementary symmetric polynomial at the roots gives
the elementary symmetric function of the root multiset. -/
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

/-- A coefficient of the general polynomial indexed by a natural number:
`1` in degree `0`, `aₖ` for `1 ≤ k ≤ n`, and `0` beyond. -/
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

/-- The general polynomial `Xⁿ - a₁Xⁿ⁻¹ + ⋯ + (-1)ⁿaₙ` over the
coefficient field, written in the Vieta sum form. -/
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

/-- Distinct linear factors are coprime. -/
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

/-- The product of the distinct linear factors is separable. -/
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

/-- The roots generate the function field over `ℂ`. -/
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

/-- Each root is a root of the general polynomial. -/
theorem root_mem_generalPolynomial_roots (n : ℕ) (i : Fin n) :
    Polynomial.aeval (root n i) (generalPolynomial n) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    map_generalPolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The coefficient field has transcendence degree `n`. -/
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

/-- A descent of the general polynomial extension to a parameter field
`F₀`: an intermediate field `E₀` between `F₀` and the function field,
linearly disjoint from the coefficient field over `F₀` in the lattice
sense (`E₀ ⊓ F = F₀`, `E₀ ⊔ F = ⊤`), generated over `F₀` by the roots
of a polynomial over `F₀` that splits separably in the function field.
The separability and splitting are imposed after mapping to the
function field, where they say the roots are distinct and all present. -/
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

/-- The root field of the general polynomial, restricted to `ℂ`, is the
whole function field: the roots are roots of the general polynomial and
generate it. -/
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

/-- The trivial descent: the coefficient field itself, with the general
polynomial as the defining polynomial. -/
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

/-- The essential dimension of the symmetric group `Sₙ` over `ℂ`, in
the general-polynomial parameter sense: the least transcendence degree
of a descent parameter field. -/
noncomputable def edSn (n : ℕ) : ℕ :=
  sInf {d : ℕ | ∃ F0 E0 : IntermediateField ℂ (rootsField n),
    IsDescent n F0 E0 ∧ transDegNat F0 ≤ d}

/-- The trivial descent bounds the essential dimension by `n`. -/
theorem edSn_le (n : ℕ) : edSn n ≤ n := by
  apply Nat.sInf_le
  exact ⟨generalBaseField n, ⊤, isDescent_generalBaseField n,
    le_of_eq (transDegNat_generalBaseField n)⟩

/-- The asymptotic essential-dimension ratio, catalogue constant
`C₇₉ = limsup (ed_ℂ(Sₙ) / n)` in the general-polynomial parameter
sense of this file. -/
noncomputable def essDimRatio : ℝ :=
  Filter.limsup (fun n : ℕ => (edSn n : ℝ) / n) Filter.atTop

/-- The proved elementary upper bound `C₇₉ ≤ 1`. -/
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
