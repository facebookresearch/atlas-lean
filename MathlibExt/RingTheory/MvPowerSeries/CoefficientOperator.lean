/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/Taylor.lean and PDeriv.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
use canonical linear maps, order, and derivations for the coefficient operator.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Coefficient operators on multivariate power series

For arbitrary variables and a family `O` of rational linear coefficient maps,
`coefficientOperator O` is the formal operator `∑ i, X i * O i`. Each coefficient
is a finite sum over its exponent's support, including for infinite variables.
Coefficient lifting is the canonical `LinearMap.compLeft`; degree bounds use
`MvPowerSeries.order`.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

/-- The operator `∑ i, X i * O i`, defined by finite coefficient sums. -/
noncomputable def coefficientOperator (O : σ → A →ₗ[ℚ] A) :
    MvPowerSeries σ A →ₗ[ℚ] MvPowerSeries σ A := by
  classical
  exact LinearMap.pi fun d => ∑ i ∈ d.support,
    (O i).comp (LinearMap.proj (d - Finsupp.single i 1))

/-- The coefficient of the formal operator is a sum over the exponent support. -/
@[simp] theorem coeff_coefficientOperator (O : σ → A →ₗ[ℚ] A)
    (f : MvPowerSeries σ A) (d : σ →₀ ℕ) :
    coeff d (coefficientOperator O f) =
      ∑ i ∈ d.support, O i (coeff (d - Finsupp.single i 1) f) := by
  classical
  unfold MvPowerSeries at f ⊢
  change (∑ i ∈ d.support,
    (O i).comp (LinearMap.proj (d - Finsupp.single i 1))) f = _
  rw [LinearMap.sum_apply]
  rfl

private theorem degree_sub_single {d : σ →₀ ℕ} {i : σ}
    (hi : i ∈ d.support) : (d - Finsupp.single i 1).degree + 1 = d.degree := by
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le
    (Finsupp.single_le_iff.2
      (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))))
  simpa only [map_add, Finsupp.degree_single] using h

/-- A coefficient operator raises every natural lower bound on order by one. -/
theorem add_one_le_order_coefficientOperator (O : σ → A →ₗ[ℚ] A)
    {f : MvPowerSeries σ A} {n : ℕ} (hf : (n : ℕ∞) ≤ f.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (coefficientOperator O f).order := by
  apply nat_le_order
  intro d hd
  rw [coeff_coefficientOperator]
  apply Finset.sum_eq_zero
  intro i hi
  have hdeg := degree_sub_single hi
  have hlt : (d - Finsupp.single i 1).degree < n := by omega
  rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt) hf), map_zero]

/-- Iteration raises every natural lower bound on order by the number of steps. -/
theorem add_le_order_iterate_coefficientOperator (O : σ → A →ₗ[ℚ] A)
    {f : MvPowerSeries σ A} {d : ℕ} (hf : (d : ℕ∞) ≤ f.order) (n : ℕ) :
    ((d + n : ℕ) : ℕ∞) ≤ ((coefficientOperator O)^[n] f).order := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simpa only [Nat.add_assoc] using add_one_le_order_coefficientOperator O ih

/-- The `n`th iterate has no coefficient in total degree less than `n`. -/
theorem coeff_iterate_coefficientOperator_eq_zero (O : σ → A →ₗ[ℚ] A)
    (f : MvPowerSeries σ A) {d : σ →₀ ℕ} {n : ℕ} (hd : d.degree < n) :
    coeff d ((coefficientOperator O)^[n] f) = 0 := by
  have horder : (n : ℕ∞) ≤ ((coefficientOperator O)^[n] f).order := by
    simpa using (add_le_order_iterate_coefficientOperator O (d := 0) (f := f) (by simp) n)
  exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) horder)

/-- At any exponent, sum over any finite set containing its support. -/
theorem coeff_coefficientOperator_eq_sum (O : σ → A →ₗ[ℚ] A)
    (f : MvPowerSeries σ A) {d : σ →₀ ℕ} {s : Finset σ}
    (hs : d.support ⊆ s) :
    coeff d (coefficientOperator O f) =
      coeff d (∑ i ∈ s, (X i : MvPowerSeries σ A) *
        id (α := MvPowerSeries σ A) ((O i).compLeft (σ →₀ ℕ) f)) := by
  classical
  have h (i : σ) : coeff d ((X i : MvPowerSeries σ A) *
        id (α := MvPowerSeries σ A) ((O i).compLeft (σ →₀ ℕ) f)) =
      if i ∈ d.support then O i (coeff (d - Finsupp.single i 1) f) else 0 := by
    rw [X_def, coeff_monomial_mul, one_mul]
    change (if Finsupp.single i 1 ≤ d then
      O i (coeff (d - Finsupp.single i 1) f) else 0) = _
    apply if_congr _ rfl rfl
    rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.one_le_iff_ne_zero]
  rw [coeff_coefficientOperator, map_sum]
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hs]

/-- Partial differentiation commutes with canonical coefficient lifting. -/
theorem pderiv_compLeft (D : A →ₗ[ℚ] A) (i : σ) (f : MvPowerSeries σ A) :
    pderiv i (D.compLeft (σ →₀ ℕ) f) = D.compLeft (σ →₀ ℕ) (pderiv i f) := by
  ext d
  have hleft : coeff d (pderiv i (D.compLeft (σ →₀ ℕ) f)) =
      D (coeff (d + Finsupp.single i 1) f) * ((d i : A) + 1) :=
    coeff_pderiv (D.compLeft (σ →₀ ℕ) f) d
  have hright : coeff d (D.compLeft (σ →₀ ℕ) (pderiv i f)) =
      D (coeff (d + Finsupp.single i 1) f * ((d i : A) + 1)) :=
    congrArg D (coeff_pderiv f d)
  have h (a : A) : a * ((d i : A) + 1) = (d i + 1) • a := by
    rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  have hmap : D (coeff (d + Finsupp.single i 1) f) * ((d i : A) + 1) =
      D (coeff (d + Finsupp.single i 1) f * ((d i : A) + 1)) := by
    rw [h, h, map_nsmul]
  exact hleft.trans (hmap.trans hright.symm)

open Classical in
private theorem pderiv_X_compLeft (O : σ → A →ₗ[ℚ] A) (i j : σ)
    (f : MvPowerSeries σ A) :
    pderiv i ((X j : MvPowerSeries σ A) *
      id (α := MvPowerSeries σ A) ((O j).compLeft (σ →₀ ℕ) f)) =
      (X j : MvPowerSeries σ A) *
        id (α := MvPowerSeries σ A) ((O j).compLeft (σ →₀ ℕ) (pderiv i f)) +
      if j = i then id (α := MvPowerSeries σ A) ((O j).compLeft (σ →₀ ℕ) f) else 0 := by
  classical
  have hp : pderiv i (id (α := MvPowerSeries σ A) ((O j).compLeft (σ →₀ ℕ) f)) =
      id (α := MvPowerSeries σ A) ((O j).compLeft (σ →₀ ℕ) (pderiv i f)) :=
    pderiv_compLeft (O j) i f
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
  split_ifs with h
  · rw [h, pderiv_X_self, mul_one]
  · rw [pderiv_X_of_ne h, mul_zero]

/-- The operator derivative is the operator of the derivative plus the lifted `O i`. -/
theorem pderiv_coefficientOperator (O : σ → A →ₗ[ℚ] A) (i : σ)
    (f : MvPowerSeries σ A) :
    pderiv i (coefficientOperator O f) = coefficientOperator O (pderiv i f) +
      id (α := MvPowerSeries σ A) ((O i).compLeft (σ →₀ ℕ) f) := by
  classical
  ext d
  have hs : (d + Finsupp.single i 1).support ⊆ insert i d.support := by
    refine Finsupp.support_add.trans (Finset.union_subset (Finset.subset_insert _ _) ?_)
    exact Finsupp.support_single_subset.trans
      (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))
  rw [coeff_pderiv, coeff_coefficientOperator_eq_sum O f hs, ← coeff_pderiv, map_sum]
  simp only [pderiv_X_compLeft]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ i,
    ite_eq_left (Finset.mem_insert_self _ _), map_add, map_add,
    ← coeff_coefficientOperator_eq_sum O _ (Finset.subset_insert _ _)]

/-- Lifted coefficient maps commute with the operator under the source pairwise premise. -/
theorem compLeft_coefficientOperator {O : σ → A →ₗ[ℚ] A}
    (hc : ∀ i j a, O i (O j a) = O j (O i a)) (i : σ) (f : MvPowerSeries σ A) :
    (O i).compLeft (σ →₀ ℕ) (coefficientOperator O f) =
      coefficientOperator O ((O i).compLeft (σ →₀ ℕ) f) := by
  ext d
  change O i (coeff d (coefficientOperator O f)) =
    coeff d (coefficientOperator O ((O i).compLeft (σ →₀ ℕ) f))
  have h : coeff d (coefficientOperator O ((O i).compLeft (σ →₀ ℕ) f)) =
      ∑ j ∈ d.support, O j (O i (coeff (d - Finsupp.single j 1) f)) :=
    coeff_coefficientOperator O ((O i).compLeft (σ →₀ ℕ) f) d
  rw [h, coeff_coefficientOperator, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact hc i j _

private theorem compLeft_derivation_mul (D : Derivation ℚ A A)
    (f g : MvPowerSeries σ A) :
    id (α := MvPowerSeries σ A) (D.toLinearMap.compLeft (σ →₀ ℕ) (f * g)) =
      f * id (α := MvPowerSeries σ A) (D.toLinearMap.compLeft (σ →₀ ℕ) g) +
      id (α := MvPowerSeries σ A) (D.toLinearMap.compLeft (σ →₀ ℕ) f) * g := by
  classical
  ext d
  change D (coeff d (f * g)) = coeff d (_ + _)
  rw [map_add, coeff_mul, coeff_mul, coeff_mul, map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  change D (coeff p.1 f * coeff p.2 g) =
    coeff p.1 f * D (coeff p.2 g) + D (coeff p.1 f) * coeff p.2 g
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm (coeff p.2 g)]

/-- A family of coefficient derivations gives the source product rule, without commutation. -/
theorem coefficientOperator_mul (D : σ → Derivation ℚ A A)
    (f g : MvPowerSeries σ A) :
    coefficientOperator (fun i => (D i).toLinearMap) (f * g) =
      f * coefficientOperator (fun i => (D i).toLinearMap) g +
      coefficientOperator (fun i => (D i).toLinearMap) f * g := by
  classical
  ext d
  let L (i : σ) (h : MvPowerSeries σ A) : MvPowerSeries σ A :=
    (D i).toLinearMap.compLeft (σ →₀ ℕ) h
  have hsum : (∑ i ∈ d.support, X i * L i (f * g)) =
      f * (∑ i ∈ d.support, X i * L i g) +
      (∑ i ∈ d.support, X i * L i f) * g := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h : L i (f * g) = f * L i g + L i f * g :=
      compLeft_derivation_mul (D i) f g
    rw [h]
    ring
  have hs (p : (σ →₀ ℕ) × (σ →₀ ℕ)) (hp : p ∈ Finset.antidiagonal d) :
      p.1.support ⊆ d.support ∧ p.2.support ⊆ d.support := by
    have h := Finset.mem_antidiagonal.1 hp
    exact ⟨Finsupp.support_mono (h ▸ le_self_add),
      Finsupp.support_mono (h ▸ le_add_self)⟩
  have heq (h : MvPowerSeries σ A) :
      coeff d (coefficientOperator (fun i => (D i).toLinearMap) h) =
        coeff d (∑ i ∈ d.support, X i * L i h) :=
    coeff_coefficientOperator_eq_sum _ h (Finset.Subset.refl _)
  rw [heq, hsum, map_add, map_add, coeff_mul, coeff_mul, coeff_mul, coeff_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    rw [coeff_coefficientOperator_eq_sum _ g (hs p hp).2]
    rfl
  · apply Finset.sum_congr rfl
    intro p hp
    rw [coeff_coefficientOperator_eq_sum _ f (hs p hp).1]
    rfl

end MvPowerSeries
