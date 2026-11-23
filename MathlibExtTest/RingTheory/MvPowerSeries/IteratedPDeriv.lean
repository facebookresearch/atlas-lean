/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.IteratedPDeriv
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open MvPowerSeries

private noncomputable def sourcePdL {σ R : Type*} [CommRing R] :
    List σ → MvPowerSeries σ R → MvPowerSeries σ R
  | [], F => F
  | i :: L, F => sourcePdL L (pderiv i F)

private theorem sourcePdL_eq_iteratedPDeriv {σ R : Type*} [CommRing R]
    (L : List σ) (F : MvPowerSeries σ R) : sourcePdL L F = iteratedPDeriv L F := by
  induction L generalizing F with
  | nil => rfl
  | cons i L ih => exact ih (pderiv i F)

-- The empty list and an empty variable type still give the identity operator.
example {σ R : Type*} [CommRing R] (F : MvPowerSeries σ R) : iteratedPDeriv [] F = F := rfl

example (F : MvPowerSeries Empty ℚ) : iteratedPDeriv [] F = F := rfl

-- Repeated variables keep their multiplicity rather than collapsing to a set.
example (x : ℕ) : Multiset.toFinsupp ([x, x] : Multiset ℕ) = Finsupp.single x 2 := by
  rw [Multiset.toFinsupp_coe_list_eq_sum]
  simp [← Finsupp.single_add]

example : constantCoeff (iteratedPDeriv [(), ()]
    ((X () : MvPowerSeries Unit ℚ) ^ 2)) = 2 := by
  change coeff 0 (pderiv () (pderiv () ((X () : MvPowerSeries Unit ℚ) ^ 2))) = 2
  rw [coeff_pderiv, coeff_pderiv]
  norm_num [coeff_X_pow, ← Finsupp.single_add]

-- Two mixed derivatives of variable 0 and one of variable 1 give a populated constant.
example : constantCoeff (iteratedPDeriv ([0, 1, 0] : List (Fin 2))
    ((X 0 : MvPowerSeries (Fin 2) ℚ) ^ 2 * X 1)) = 2 := by
  change coeff 0 (pderiv (0 : Fin 2) (pderiv (1 : Fin 2)
    (pderiv (0 : Fin 2) ((X 0 : MvPowerSeries (Fin 2) ℚ) ^ 2 * X 1)))) = 2
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, X_pow_eq, X_def, monomial_mul_monomial]
  have h : (0 + Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 +
      Finsupp.single 0 1 : Fin 2 →₀ ℕ) = Finsupp.single 0 2 + Finsupp.single 1 1 := by
    rw [zero_add, add_right_comm, ← Finsupp.single_add]
  rw [h, coeff_monomial_same]
  norm_num [Finsupp.add_apply, Finsupp.single_apply]

-- At a nonzero multi-index, the same list extracts the coefficient 6 at X₀.
example : coeff (Finsupp.single (0 : Fin 2) 1)
    (iteratedPDeriv ([0, 1, 0] : List (Fin 2))
      ((X 0 : MvPowerSeries (Fin 2) ℚ) ^ 3 * X 1)) = 6 := by
  change coeff (Finsupp.single (0 : Fin 2) 1)
    (pderiv (0 : Fin 2) (pderiv (1 : Fin 2)
      (pderiv (0 : Fin 2) ((X 0 : MvPowerSeries (Fin 2) ℚ) ^ 3 * X 1)))) = 6
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, X_pow_eq, X_def, monomial_mul_monomial]
  have h : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 0 1 + Finsupp.single 1 1 +
      Finsupp.single 0 1 : Fin 2 →₀ ℕ) = Finsupp.single 0 3 + Finsupp.single 1 1 := by
    rw [← Finsupp.single_add, add_right_comm, ← Finsupp.single_add]
  rw [h, coeff_monomial_same]
  norm_num [Finsupp.add_apply, Finsupp.single_apply]

example {σ R : Type*} [CommRing R] (L K : List σ) (F : MvPowerSeries σ R) :
    iteratedPDeriv (L ++ K) F = iteratedPDeriv K (iteratedPDeriv L F) := by
  rw [iteratedPDeriv_append, LinearMap.comp_apply]

example {σ R : Type*} [CommRing R] (i j : σ) (F : MvPowerSeries σ R) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := pderiv_pderiv i j F

example {σ R : Type*} [CommRing R] (i : σ) (L : List σ) (F : MvPowerSeries σ R) :
    pderiv i (iteratedPDeriv L F) = iteratedPDeriv L (pderiv i F) :=
  pderiv_iteratedPDeriv i L F

-- Source linearity laws come directly from the operator's LinearMap interface.
example {σ R : Type*} [CommRing R] (L : List σ) (F G : MvPowerSeries σ R) :
    iteratedPDeriv L (F + G) = iteratedPDeriv L F + iteratedPDeriv L G := map_add _ _ _

example {σ R : Type*} [CommRing R] (L : List σ) :
    iteratedPDeriv L (0 : MvPowerSeries σ R) = 0 := map_zero _

example {σ R : Type*} [CommRing R] (L : List σ) (c : R) (F : MvPowerSeries σ R) :
    iteratedPDeriv L (C c * F) = C c * iteratedPDeriv L F := by
  simp only [← smul_eq_C_mul, map_smul]

example {σ R ι : Type*} [CommRing R] (L : List σ) (s : Finset ι)
    (F : ι → MvPowerSeries σ R) :
    iteratedPDeriv L (∑ j ∈ s, F j) = ∑ j ∈ s, iteratedPDeriv L (F j) := map_sum _ _ _

open scoped Classical

-- Both complete source equations, including their definitions and ℚ scalar action.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (L : List σ) (β : σ →₀ ℕ)
    (F : MvPowerSeries σ R) :
    (β + (L.map fun i => Finsupp.single i 1).sum).prod
        (fun _ n => (n.factorial : ℚ)) •
      coeff (β + (L.map fun i => Finsupp.single i 1).sum) F =
    β.prod (fun _ n => (n.factorial : ℚ)) • coeff β (sourcePdL L F) := by
  rw [sourcePdL_eq_iteratedPDeriv, ← Multiset.toFinsupp_coe_list_eq_sum]
  exact factorial_smul_coeff_iteratedPDeriv_rat L β F

example {σ R : Type*} [CommRing R] [Algebra ℚ R] (L : List σ)
    (F : MvPowerSeries σ R) :
    ((L.map fun i => Finsupp.single i 1).sum).prod (fun _ n => (n.factorial : ℚ)) •
        coeff (L.map fun i => Finsupp.single i 1).sum F = constantCoeff (sourcePdL L F) := by
  rw [sourcePdL_eq_iteratedPDeriv, ← Multiset.toFinsupp_coe_list_eq_sum]
  exact factorial_smul_coeff_eq_constantCoeff_iteratedPDeriv_rat L F

-- The source factorial definition is exactly the cast of the natural product.
example {σ : Type*} (α : σ →₀ ℕ) :
    α.prod (fun _ n => (n.factorial : ℚ)) = ((α.prod (fun _ n => n.factorial) : ℕ) : ℚ) :=
  (Nat.cast_finsuppProd α (fun _ n => n.factorial)).symm

-- A rational scalar acting on any rational algebra agrees with the natural scalar.
example {R : Type*} [CommRing R] [Algebra ℚ R] (n : ℕ) (a : R) :
    (n : ℚ) • a = n • a := Nat.cast_smul_eq_nsmul ℚ n a

-- Positive characteristic forbids cancelling the factorial: the coefficient is 1,
-- while the constant coefficient of the double derivative is 0.
example : coeff (Finsupp.single () 2) ((X () : MvPowerSeries Unit (ZMod 2)) ^ 2) = 1 := by
  simp [coeff_X_pow]

example : constantCoeff (iteratedPDeriv [(), ()]
    ((X () : MvPowerSeries Unit (ZMod 2)) ^ 2)) = 0 := by
  change coeff 0 (pderiv () (pderiv () ((X () : MvPowerSeries Unit (ZMod 2)) ^ 2))) = 0
  rw [coeff_pderiv, coeff_pderiv]
  norm_num [coeff_X_pow, ← Finsupp.single_add]
  decide

example : (2 : ℕ) • coeff (Finsupp.single () 2)
    ((X () : MvPowerSeries Unit (ZMod 2)) ^ 2) =
      constantCoeff (iteratedPDeriv [(), ()]
        ((X () : MvPowerSeries Unit (ZMod 2)) ^ 2)) := by
  have h := factorial_smul_coeff_eq_constantCoeff_iteratedPDeriv [(), ()]
    ((X () : MvPowerSeries Unit (ZMod 2)) ^ 2)
  simp only [Multiset.toFinsupp_coe_list_eq_sum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, ← Finsupp.single_add] at h
  rw [Finsupp.prod_single_index (by rfl)] at h
  exact h

-- The source induction on a multi-index is canonical induction on its multiset.
example {σ : Type*} {p : (σ →₀ ℕ) → Prop} (h0 : p 0)
    (hs : ∀ α i, p α → p (α + Finsupp.single i 1)) (α : σ →₀ ℕ) : p α := by
  have hm (s : Multiset σ) : p (Multiset.toFinsupp s) := by
    induction s using Multiset.induction_on with
    | empty => simpa only [Multiset.toFinsupp_zero] using h0
    | cons i s ih =>
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
        add_comm]
      exact hs _ i ih
  simpa only [Finsupp.toMultiset_toFinsupp] using hm (Finsupp.toMultiset α)

example {σ : Type*} : (0 : σ →₀ ℕ).prod (fun _ n => (n.factorial : ℚ)) = 1 :=
  Finsupp.prod_zero_index

-- The one-step source Borel equation, with its rational factorials.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (β : σ →₀ ℕ) (i : σ)
    (F : MvPowerSeries σ R) :
    (β + Finsupp.single i 1).prod (fun _ n => (n.factorial : ℚ)) •
        coeff (β + Finsupp.single i 1) F =
      β.prod (fun _ n => (n.factorial : ℚ)) • coeff β (pderiv i F) := by
  simpa [Multiset.toFinsupp_coe_list_eq_sum, iteratedPDeriv] using
    factorial_smul_coeff_iteratedPDeriv_rat [i] β F

-- The source factorial update is obtained without a second factorial definition.
example {σ : Type*} (α : σ →₀ ℕ) (i : σ) :
    (α + Finsupp.single i 1).prod (fun _ n => (n.factorial : ℚ)) =
      ((α i : ℚ) + 1) * α.prod (fun _ n => (n.factorial : ℚ)) := by
  have h := factorial_smul_coeff_iteratedPDeriv_rat [i] α
    (monomial (α + Finsupp.single i 1) (1 : ℚ))
  simpa [Multiset.toFinsupp_coe_list_eq_sum, iteratedPDeriv, coeff_pderiv,
    coeff_monomial_same, smul_eq_mul, mul_comm] using h

example {R : Type*} [CommRing R] [Algebra ℚ R] (a : R) (n : ℕ) :
    a * ((n : R) + 1) = ((n : ℚ) + 1) • a := by
  rw [Algebra.smul_def, map_add, map_natCast, map_one, mul_comm]

example {σ R : Type*} [CommRing R] (i : σ) (c : R) (F : MvPowerSeries σ R) :
    pderiv i (C c * F) = C c * pderiv i F := by
  simp only [← smul_eq_C_mul, Derivation.map_smul]
