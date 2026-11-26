/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.AlgebraicGeometry.SeshadriConstant
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Single
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SeshadriConstantWanted

open MathlibExt.AlgebraicGeometry.SeshadriConstant

/-!
# Submaximal upper bound for the ten-point Seshadri constant

This module proves `submaximalUpperBound_wanted`: the generic ten-point
Seshadri constant of `ℙ²`, in the affine-chart model, is at most `1/√10`.
The proof counts monomials of bounded degree against multiplicity
conditions and passes to the limit over increasing multiplicities.

Source: Carlos Galindo, Francisco Monserrat, Carlos-Jesús Moreno-Ávila and
Julio-José Moyano-Fernández, _On the valuative Nagata conjecture_, the general
submaximal upper bound; Optimization Problems, record 74a.
-/

private noncomputable def pairToExp (s : Σ _ : ℕ, ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) s.1 + Finsupp.single (1 : Fin 2) s.2

private theorem pairToExp_zero (s : Σ _ : ℕ, ℕ) : pairToExp s 0 = s.1 := by
  simp [pairToExp]

private theorem pairToExp_one (s : Σ _ : ℕ, ℕ) : pairToExp s 1 = s.2 := by
  simp [pairToExp]

private theorem monomialDegree_pairToExp (s : Σ _ : ℕ, ℕ) :
    monomialDegree (pairToExp s) = s.1 + s.2 := by
  unfold monomialDegree
  rw [Fin.sum_univ_two, pairToExp_zero, pairToExp_one]

private theorem pairToExp_injective : Function.Injective pairToExp := by
  intro s t h
  have h0 := congrArg (fun e => e (0 : Fin 2)) h
  have h1 := congrArg (fun e => e (1 : Fin 2)) h
  simp only [pairToExp_zero] at h0
  simp only [pairToExp_one] at h1
  obtain ⟨a, b⟩ := s
  obtain ⟨c, d⟩ := t
  change a = c at h0
  change b = d at h1
  subst h0
  subst h1
  rfl

private theorem exp_eq_pairToExp_self (e : Fin 2 →₀ ℕ) :
    e = pairToExp ⟨e 0, e 1⟩ := by
  apply Finsupp.ext
  intro i
  have h : ∀ j : Fin 2, e j = pairToExp ⟨e 0, e 1⟩ j := by
    rw [Fin.forall_fin_two]
    constructor
    · rw [pairToExp_zero]
    · rw [pairToExp_one]
  exact h i

private def pairsLE (d : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  Finset.sigma (Finset.range (d + 1)) (fun a => Finset.range (d + 1 - a))

private theorem mem_pairsLE (d : ℕ) (s : Σ _ : ℕ, ℕ) :
    s ∈ pairsLE d ↔ s.1 + s.2 ≤ d := by
  simp only [pairsLE, Finset.mem_sigma, Finset.mem_range]
  omega

private theorem card_pairsLE (d : ℕ) : 2 * (pairsLE d).card = (d + 1) * (d + 2) := by
  have hcard : (pairsLE d).card = ∑ a ∈ Finset.range (d + 1), (d + 1 - a) := by
    rw [pairsLE, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.card_range]
  have hrefl : ∑ a ∈ Finset.range (d + 1), (d + 1 - a)
      = ∑ a ∈ Finset.range (d + 1), (a + 1) := by
    have h := Finset.sum_range_reflect (fun j => j + 1) (d + 1)
    have hpt : ∀ j ∈ Finset.range (d + 1), (d + 1 - j) = ((d + 1) - 1 - j) + 1 := by
      intro j hj
      simp only [Finset.mem_range] at hj
      omega
    calc ∑ a ∈ Finset.range (d + 1), (d + 1 - a)
        = ∑ j ∈ Finset.range (d + 1), (((d + 1) - 1 - j) + 1) :=
          Finset.sum_congr rfl hpt
      _ = ∑ j ∈ Finset.range (d + 1), (j + 1) := h
  have hsum : ∑ a ∈ Finset.range (d + 1), (a + 1)
      = (∑ a ∈ Finset.range (d + 1), a) + (d + 1) := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_range]
  have hgauss := Finset.sum_range_id_mul_two (d + 1)
  have hd1 : (d + 1) - 1 = d := by omega
  rw [hd1] at hgauss
  rw [hcard, hrefl, hsum]
  linear_combination hgauss

private def pairsLT (m : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  Finset.sigma (Finset.range m) (fun a => Finset.range (m - a))

private theorem mem_pairsLT (m : ℕ) (s : Σ _ : ℕ, ℕ) :
    s ∈ pairsLT m ↔ s.1 + s.2 < m := by
  simp only [pairsLT, Finset.mem_sigma, Finset.mem_range]
  omega

private theorem card_pairsLT (m : ℕ) : 2 * (pairsLT m).card = m * (m + 1) := by
  cases m with
  | zero =>
    simp [pairsLT]
  | succ k =>
    have hcard : (pairsLT (k + 1)).card
        = ∑ a ∈ Finset.range (k + 1), (k + 1 - a) := by
      rw [pairsLT, Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.card_range]
    have hrefl : ∑ a ∈ Finset.range (k + 1), (k + 1 - a)
        = ∑ a ∈ Finset.range (k + 1), (a + 1) := by
      have h := Finset.sum_range_reflect (fun j => j + 1) (k + 1)
      have hpt : ∀ j ∈ Finset.range (k + 1),
          (k + 1 - j) = ((k + 1) - 1 - j) + 1 := by
        intro j hj
        simp only [Finset.mem_range] at hj
        omega
      calc ∑ a ∈ Finset.range (k + 1), (k + 1 - a)
          = ∑ j ∈ Finset.range (k + 1), (((k + 1) - 1 - j) + 1) :=
            Finset.sum_congr rfl hpt
        _ = ∑ j ∈ Finset.range (k + 1), (j + 1) := h
    have hsum : ∑ a ∈ Finset.range (k + 1), (a + 1)
        = (∑ a ∈ Finset.range (k + 1), a) + (k + 1) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, Finset.card_range]
    have hgauss := Finset.sum_range_id_mul_two (k + 1)
    have hk1 : (k + 1) - 1 = k := by omega
    rw [hk1] at hgauss
    rw [hcard, hrefl, hsum]
    linear_combination hgauss

private noncomputable def expsLE (d : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (pairsLE d).map ⟨pairToExp, pairToExp_injective⟩

private noncomputable def expsLT (m : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (pairsLT m).map ⟨pairToExp, pairToExp_injective⟩

private theorem card_expsLE (d : ℕ) : 2 * (expsLE d).card = (d + 1) * (d + 2) := by
  simpa [expsLE] using card_pairsLE d

private theorem card_expsLT (m : ℕ) : 2 * (expsLT m).card = m * (m + 1) := by
  simpa [expsLT] using card_pairsLT m

private theorem mem_expsLE_of_degree_le {d : ℕ} {e : Fin 2 →₀ ℕ}
    (h : monomialDegree e ≤ d) : e ∈ expsLE d := by
  have he : e = pairToExp ⟨e 0, e 1⟩ := exp_eq_pairToExp_self e
  have hdeg : e 0 + e 1 ≤ d := by
    have hm : monomialDegree e = e 0 + e 1 := by
      unfold monomialDegree
      rw [Fin.sum_univ_two]
    omega
  have hmem : (⟨e 0, e 1⟩ : Σ _ : ℕ, ℕ) ∈ pairsLE d :=
    (mem_pairsLE d _).mpr hdeg
  rw [he]
  exact Finset.mem_map.mpr ⟨⟨e 0, e 1⟩, hmem, rfl⟩

private theorem degree_le_of_mem_expsLE {d : ℕ} {e : Fin 2 →₀ ℕ}
    (h : e ∈ expsLE d) : monomialDegree e ≤ d := by
  simp only [expsLE, Finset.mem_map] at h
  obtain ⟨s, hs, rfl⟩ := h
  change monomialDegree (pairToExp s) ≤ d
  rw [monomialDegree_pairToExp]
  exact (mem_pairsLE d _).mp hs

private theorem mem_expsLT_of_degree_lt {m : ℕ} {e : Fin 2 →₀ ℕ}
    (h : monomialDegree e < m) : e ∈ expsLT m := by
  have he : e = pairToExp ⟨e 0, e 1⟩ := exp_eq_pairToExp_self e
  have hdeg : e 0 + e 1 < m := by
    have hm : monomialDegree e = e 0 + e 1 := by
      unfold monomialDegree
      rw [Fin.sum_univ_two]
    omega
  have hmem : (⟨e 0, e 1⟩ : Σ _ : ℕ, ℕ) ∈ pairsLT m :=
    (mem_pairsLT m _).mpr hdeg
  rw [he]
  exact Finset.mem_map.mpr ⟨⟨e 0, e 1⟩, hmem, rfl⟩

private theorem degree_lt_of_mem_expsLT {m : ℕ} {e : Fin 2 →₀ ℕ}
    (h : e ∈ expsLT m) : monomialDegree e < m := by
  simp only [expsLT, Finset.mem_map] at h
  obtain ⟨s, hs, rfl⟩ := h
  change monomialDegree (pairToExp s) < m
  rw [monomialDegree_pairToExp]
  exact (mem_pairsLT m _).mp hs

private noncomputable def shiftedLin (a : AffinePoint) :
    PlanePolynomial →ₗ[ℂ] PlanePolynomial :=
  (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i))).toLinearMap

private theorem shiftedLin_apply (a : AffinePoint) (f : PlanePolynomial) :
    shiftedLin a f = shifted f a :=
  rfl

private noncomputable def condLin (x : Fin 10 → AffinePoint)
    (t : Fin 10 × (Fin 2 →₀ ℕ)) : PlanePolynomial →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ t.2).comp (shiftedLin (x t.1))

private theorem condLin_apply (x : Fin 10 → AffinePoint)
    (t : Fin 10 × (Fin 2 →₀ ℕ)) (f : PlanePolynomial) :
    condLin x t f = (shifted f (x t.1)).coeff t.2 := by
  simp [condLin, shiftedLin_apply]

private noncomputable def polyLin (d : ℕ) : ((expsLE d) → ℂ) →ₗ[ℂ] PlanePolynomial :=
  ∑ e : (expsLE d), ((MvPolynomial.monomial (e : Fin 2 →₀ ℕ)).comp (LinearMap.proj e))

private theorem polyLin_apply (d : ℕ) (v : (expsLE d) → ℂ) :
    polyLin d v
      = ∑ e : (expsLE d), MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e) := by
  simp [polyLin]

private noncomputable def condMatrix (x : Fin 10 → AffinePoint) (d m : ℕ) :
    ((expsLE d) → ℂ) →ₗ[ℂ] ((Fin 10 × (expsLT m)) → ℂ) :=
  LinearMap.pi
    (fun t => (condLin x (t.1, (t.2 : Fin 2 →₀ ℕ))).comp (polyLin d))

private theorem condMatrix_apply (x : Fin 10 → AffinePoint) (d m : ℕ)
    (v : (expsLE d) → ℂ) (t : Fin 10 × (expsLT m)) :
    condMatrix x d m v t
      = (shifted (polyLin d v) (x t.1)).coeff (t.2 : Fin 2 →₀ ℕ) := by
  simp [condMatrix, condLin_apply]

private theorem finrank_lt_of_dim_gt {d m : ℕ}
    (h : 10 * (m * (m + 1)) < (d + 1) * (d + 2)) :
    Module.finrank ℂ ((Fin 10 × (expsLT m)) → ℂ)
      < Module.finrank ℂ ((expsLE d) → ℂ) := by
  rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, Fintype.card_coe]
  have hLE := card_expsLE d
  have hLT := card_expsLT m
  omega

private theorem exists_ne_zero_ker (x : Fin 10 → AffinePoint) (d m : ℕ)
    (h : 10 * (m * (m + 1)) < (d + 1) * (d + 2)) :
    ∃ v : (expsLE d) → ℂ, v ≠ 0 ∧ condMatrix x d m v = 0 := by
  have hlt := finrank_lt_of_dim_gt h
  have hker : (condMatrix x d m).ker ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨v, hmem, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hne, LinearMap.mem_ker.mp hmem⟩

private theorem coeff_polyLin (d : ℕ) (v : (expsLE d) → ℂ) (e0 : (expsLE d)) :
    (polyLin d v).coeff (e0 : Fin 2 →₀ ℕ) = v e0 := by
  rw [polyLin_apply]
  have hmap := map_sum (MvPolynomial.lcoeff ℂ (e0 : Fin 2 →₀ ℕ))
    (fun e : (expsLE d) => MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e))
    Finset.univ
  simp only [MvPolynomial.lcoeff_apply] at hmap
  have hif : ∀ e : (expsLE d),
      (MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e)).coeff (e0 : Fin 2 →₀ ℕ)
        = (if e = e0 then v e else 0) := by
    intro e
    rw [MvPolynomial.coeff_monomial]
    by_cases he : e = e0
    · subst he
      simp
    · have hne : (e : Fin 2 →₀ ℕ) ≠ (e0 : Fin 2 →₀ ℕ) :=
        fun hcon => he (Subtype.ext hcon)
      simp [hne, he]
  calc ((∑ e : (expsLE d),
        MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e)).coeff (e0 : Fin 2 →₀ ℕ))
      = ∑ e : (expsLE d),
          (MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e)).coeff
            (e0 : Fin 2 →₀ ℕ) := hmap
    _ = ∑ e : (expsLE d), (if e = e0 then v e else 0) :=
        Finset.sum_congr rfl (fun e _ => hif e)
    _ = v e0 := by simp

private theorem polyLin_ne_zero_of_ne_zero {d : ℕ} {v : (expsLE d) → ℂ}
    (hv : v ≠ 0) : polyLin d v ≠ 0 := by
  obtain ⟨e0, he0⟩ : ∃ e, v e ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  have hcoeff := coeff_polyLin d v e0
  intro hf
  rw [hf] at hcoeff
  simp at hcoeff
  exact he0 hcoeff.symm

private theorem monomial_totalDegree_le_of_mem {d : ℕ} {e : Fin 2 →₀ ℕ}
    (h : e ∈ expsLE d) (c : ℂ) :
    (MvPolynomial.monomial e c).totalDegree ≤ d := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPolynomial.totalDegree_monomial _ hc]
    have hdeg : monomialDegree e ≤ d := degree_le_of_mem_expsLE h
    have hsum : e.sum (fun x e => e) = monomialDegree e := by
      unfold monomialDegree
      rw [Finsupp.sum_fintype _ _ (fun i => rfl)]
    rw [hsum]
    exact hdeg

private theorem totalDegree_polyLin_le (d : ℕ) (v : (expsLE d) → ℂ) :
    (polyLin d v).totalDegree ≤ d := by
  rw [polyLin_apply]
  suffices h : ∀ s : Finset (expsLE d),
      (∑ e ∈ s, MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e)).totalDegree ≤ d by
    have hu := h Finset.univ
    simpa using hu
  intro s
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    have hmono : (MvPolynomial.monomial (a : Fin 2 →₀ ℕ) (v a)).totalDegree ≤ d :=
      monomial_totalDegree_le_of_mem a.2 (v a)
    calc (MvPolynomial.monomial (a : Fin 2 →₀ ℕ) (v a)
          + ∑ e ∈ s, MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e)).totalDegree
        ≤ max (MvPolynomial.monomial (a : Fin 2 →₀ ℕ) (v a)).totalDegree
            (∑ e ∈ s, MvPolynomial.monomial (e : Fin 2 →₀ ℕ) (v e)).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ d := max_le hmono ih

private theorem le_multiplicity_of_coeff_eq_zero {f : PlanePolynomial}
    {a : AffinePoint} {m : ℕ} (hf : f ≠ 0)
    (h : ∀ e : Fin 2 →₀ ℕ, monomialDegree e < m → (shifted f a).coeff e = 0) :
    m ≤ SeshadriConstant.multiplicity f a := by
  have hshift : shifted f a ≠ 0 := by
    intro hcon
    rw [shifted_eq_zero_iff] at hcon
    exact hf hcon
  obtain ⟨e0, he0⟩ := MvPolynomial.support_nonempty.mpr hshift
  have hne : (shifted f a).support.Nonempty := ⟨e0, he0⟩
  have hmin_mem := Finset.min'_mem ((shifted f a).support.image monomialDegree)
    (Finset.image_nonempty.mpr hne)
  rw [Finset.mem_image] at hmin_mem
  obtain ⟨e1, he1sup, hdeg⟩ := hmin_mem
  have hcoeff_ne : (shifted f a).coeff e1 ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he1sup
  have hle : m ≤ monomialDegree e1 := by
    by_contra hcon
    push Not at hcon
    exact hcoeff_ne (h e1 hcon)
  have hmult : SeshadriConstant.multiplicity f a = monomialDegree e1 := by
    unfold SeshadriConstant.multiplicity
    rw [dite_eq_left hne]
    exact hdeg.symm
  rw [hmult]
  exact hle

private theorem exists_poly_of_dim_gt (x : Fin 10 → AffinePoint) (d m : ℕ)
    (h : 10 * (m * (m + 1)) < (d + 1) * (d + 2)) :
    ∃ f : PlanePolynomial, f ≠ 0 ∧ f.totalDegree ≤ d ∧
      ∀ i, m ≤ SeshadriConstant.multiplicity f (x i) := by
  obtain ⟨v, hvne, hker⟩ := exists_ne_zero_ker x d m h
  have hfne : polyLin d v ≠ 0 := polyLin_ne_zero_of_ne_zero hvne
  refine ⟨polyLin d v, hfne, totalDegree_polyLin_le d v, ?_⟩
  intro i
  apply le_multiplicity_of_coeff_eq_zero hfne
  intro e he
  have hmem : e ∈ expsLT m := mem_expsLT_of_degree_lt he
  have hzero : condMatrix x d m v (i, ⟨e, hmem⟩) = 0 := by
    simpa using congrFun hker (i, ⟨e, hmem⟩)
  rw [condMatrix_apply] at hzero
  exact hzero

private theorem ratio_le_of_poly {x : Fin 10 → AffinePoint} {f : PlanePolynomial}
    {d m : ℕ} (hdeg : f.totalDegree ≤ d)
    (hmult : ∀ i, m ≤ SeshadriConstant.multiplicity f (x i))
    (hmpos : 0 < m) (hdpos : 0 < d) :
    (f.totalDegree : ℝ) / ((∑ i, SeshadriConstant.multiplicity f (x i) : ℕ) : ℝ)
      ≤ (d : ℝ) / (10 * (m : ℝ)) := by
  have hsum_ge : 10 * m ≤ ∑ i, SeshadriConstant.multiplicity f (x i) := by
    have hle : ∑ _i : Fin 10, m ≤ ∑ i, SeshadriConstant.multiplicity f (x i) :=
      Finset.sum_le_sum (fun i _ => hmult i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using hle
  have hsum_pos : 0 < ∑ i, SeshadriConstant.multiplicity f (x i) :=
    lt_of_lt_of_le (Nat.mul_pos (by decide) hmpos) hsum_ge
  have hSpos : (0 : ℝ) < ((∑ i, SeshadriConstant.multiplicity f (x i) : ℕ) : ℝ) := by
    exact_mod_cast hsum_pos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have h10mpos : (0 : ℝ) < 10 * (m : ℝ) := by positivity
  have hdegR : (f.totalDegree : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdeg
  have hsumR : 10 * (m : ℝ) ≤ ((∑ i, SeshadriConstant.multiplicity f (x i) : ℕ) : ℝ) := by
    exact_mod_cast hsum_ge
  calc (f.totalDegree : ℝ) / ((∑ i, SeshadriConstant.multiplicity f (x i) : ℕ) : ℝ)
      ≤ (d : ℝ) / ((∑ i, SeshadriConstant.multiplicity f (x i) : ℕ) : ℝ) :=
        (div_le_div_iff_of_pos_right hSpos).mpr hdegR
    _ ≤ (d : ℝ) / (10 * (m : ℝ)) :=
        (div_le_div_iff_of_pos_left hdR hSpos h10mpos).mpr hsumR

private theorem sqrt10_sq : (Real.sqrt 10) ^ 2 = 10 :=
  Real.sq_sqrt (by positivity)

private theorem sqrt10_gt_three : 3 < Real.sqrt 10 := by
  have hsq := sqrt10_sq
  have hnn : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  by_contra hcon
  push Not at hcon
  have hle : (Real.sqrt 10) ^ 2 ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ hnn hcon 2
  rw [hsq] at hle
  norm_num at hle

private theorem sqrt10_ne_zero : Real.sqrt 10 ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

private theorem sqrt10_div_ten : Real.sqrt 10 / 10 = 1 / Real.sqrt 10 := by
  have hsne := sqrt10_ne_zero
  have hsq := sqrt10_sq
  rw [div_eq_div_iff (by norm_num) hsne]
  linear_combination hsq

private theorem dim_lt_of_ge {M D s : ℝ} (hs_sq : s ^ 2 = 10) (hs_gt3 : 3 < s)
    (hM0 : 0 ≤ M) (hDge : s * M + 2 ≤ D) :
    10 * (M * (M + 1)) < (D + 1) * (D + 2) := by
  have hs0 : 0 ≤ s := by linarith
  have hmul : 0 ≤ s * M := mul_nonneg hs0 hM0
  have hsM2_nonneg : 0 ≤ s * M + 2 := by linarith
  have hD2 : (s * M + 2) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hsM2_nonneg hDge 2
  have hexpand : (s * M + 2) ^ 2 = 10 * M ^ 2 + 4 * (s * M) + 4 := by
    linear_combination (M ^ 2 * hs_sq)
  have hD2' : 10 * M ^ 2 + 4 * (s * M) + 4 ≤ D ^ 2 := by
    rw [← hexpand]
    exact hD2
  have h7s : (0 : ℝ) ≤ 7 * s - 10 := by linarith
  have hM7s : (0 : ℝ) ≤ M * (7 * s - 10) := mul_nonneg hM0 h7s
  have hE : M * (7 * s - 10) = 7 * (s * M) - 10 * M := by ring
  rw [hE] at hM7s
  linarith

private theorem exists_ratio_le_add (x : Fin 10 → AffinePoint) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ r ∈ seshadriRatios x, r ≤ 1 / Real.sqrt 10 + ε := by
  set y : ℝ := 3 / (10 * ε) with hy_def
  set m : ℕ := ⌈y⌉₊ + 1 with hm_def
  set d : ℕ := ⌈Real.sqrt 10 * (m : ℝ)⌉₊ + 2 with hd_def
  have hmpos : 0 < m := by omega
  have hdpos : 0 < d := by omega
  have hypos : 0 < y := by
    rw [hy_def]
    positivity
  have hm_gt_y : y < (m : ℝ) := by
    have hceil : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
    have hm_eq : (m : ℝ) = (⌈y⌉₊ : ℝ) + 1 := by
      rw [hm_def, Nat.cast_add, Nat.cast_one]
    linarith
  have hd_ge : Real.sqrt 10 * (m : ℝ) + 2 ≤ (d : ℝ) := by
    have hceil : Real.sqrt 10 * (m : ℝ) ≤ (⌈Real.sqrt 10 * (m : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hd_eq : (d : ℝ) = (⌈Real.sqrt 10 * (m : ℝ)⌉₊ : ℝ) + 2 := by
      rw [hd_def, Nat.cast_add]
      simp
    linarith
  have hd_lt : (d : ℝ) < Real.sqrt 10 * (m : ℝ) + 3 := by
    have hceil : (⌈Real.sqrt 10 * (m : ℝ)⌉₊ : ℝ)
        < Real.sqrt 10 * (m : ℝ) + 1 := by
      apply Nat.ceil_lt_add_one
      positivity
    have hd_eq : (d : ℝ) = (⌈Real.sqrt 10 * (m : ℝ)⌉₊ : ℝ) + 2 := by
      rw [hd_def, Nat.cast_add]
      simp
    linarith
  have hdim : 10 * (m * (m + 1)) < (d + 1) * (d + 2) := by
    have hR : (10 : ℝ) * ((m : ℝ) * ((m : ℝ) + 1))
        < ((d : ℝ) + 1) * ((d : ℝ) + 2) :=
      dim_lt_of_ge sqrt10_sq sqrt10_gt_three (by positivity) hd_ge
    exact_mod_cast hR
  obtain ⟨f, hfne, hdeg, hmult⟩ := exists_poly_of_dim_gt x d m hdim
  have hsum_ge : 10 * m ≤ ∑ i, SeshadriConstant.multiplicity f (x i) := by
    have hle : ∑ _i : Fin 10, m ≤ ∑ i, SeshadriConstant.multiplicity f (x i) :=
      Finset.sum_le_sum (fun i _ => hmult i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using hle
  have hsum_pos : 0 < ∑ i, SeshadriConstant.multiplicity f (x i) :=
    lt_of_lt_of_le (Nat.mul_pos (by decide) hmpos) hsum_ge
  have hratio := ratio_le_of_poly hdeg hmult hmpos hdpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have h10Mpos : (0 : ℝ) < 10 * (m : ℝ) := by positivity
  have h3le : 3 / (10 * (m : ℝ)) ≤ ε := by
    have h10εpos : (0 : ℝ) < 10 * ε := by positivity
    have h3lt : (3 : ℝ) < (m : ℝ) * (10 * ε) := by
      have hy_lt := hm_gt_y
      rw [hy_def, div_lt_iff₀ h10εpos] at hy_lt
      exact hy_lt
    have h3le' : (3 : ℝ) ≤ ε * (10 * (m : ℝ)) := by
      have heq : (m : ℝ) * (10 * ε) = ε * (10 * (m : ℝ)) := by ring
      linarith
    rw [div_le_iff₀ h10Mpos]
    exact h3le'
  have hdm_le : (d : ℝ) / (10 * (m : ℝ)) ≤ 1 / Real.sqrt 10 + ε := by
    have hdltd : (d : ℝ) / (10 * (m : ℝ))
        ≤ (Real.sqrt 10 * (m : ℝ) + 3) / (10 * (m : ℝ)) :=
      (div_le_div_iff_of_pos_right h10Mpos).mpr (le_of_lt hd_lt)
    have hsplit : (Real.sqrt 10 * (m : ℝ) + 3) / (10 * (m : ℝ))
        = Real.sqrt 10 / 10 + 3 / (10 * (m : ℝ)) := by
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
      rw [add_div]
      congr 1
      exact mul_div_mul_right _ _ hmne
    calc (d : ℝ) / (10 * (m : ℝ))
          ≤ (Real.sqrt 10 * (m : ℝ) + 3) / (10 * (m : ℝ)) := hdltd
      _ = Real.sqrt 10 / 10 + 3 / (10 * (m : ℝ)) := hsplit
      _ = 1 / Real.sqrt 10 + 3 / (10 * (m : ℝ)) := by rw [sqrt10_div_ten]
      _ ≤ 1 / Real.sqrt 10 + ε := by linarith
  refine ⟨(f.totalDegree : ℝ)
    / ((∑ i, SeshadriConstant.multiplicity f (x i) : ℕ) : ℝ),
    ⟨f, hfne, hsum_pos, rfl⟩, ?_⟩
  calc (f.totalDegree : ℝ)
        / ((∑ i, SeshadriConstant.multiplicity f (x i) : ℕ) : ℝ)
      ≤ (d : ℝ) / (10 * (m : ℝ)) := hratio
    _ ≤ 1 / Real.sqrt 10 + ε := hdm_le

private theorem affine_le (x : Fin 10 → AffinePoint) :
    affineSeshadriConstant x ≤ 1 / Real.sqrt 10 := by
  by_contra hcon
  push Not at hcon
  set ε : ℝ := (affineSeshadriConstant x - 1 / Real.sqrt 10) / 2 with hε_def
  have hεpos : 0 < ε := by
    rw [hε_def]
    linarith
  obtain ⟨r, hmem, hle⟩ := exists_ratio_le_add x ε hεpos
  have hsInf_le : affineSeshadriConstant x ≤ r :=
    csInf_le (bddBelow_seshadriRatios x) hmem
  have hcon2 : 1 / Real.sqrt 10 + ε < affineSeshadriConstant x := by
    rw [hε_def]
    linarith
  linarith

private def stdPts : Fin 10 → AffinePoint :=
  fun i j => if j = 0 then (i : ℂ) else 0

private theorem stdPts_injective : Function.Injective stdPts := by
  intro i k h
  have h0 : ((i : ℕ) : ℂ) = ((k : ℕ) : ℂ) := by
    simpa [stdPts] using congrFun h 0
  exact Fin.ext (by exact_mod_cast h0)

/-- **Submaximal upper bound for the ten-point Seshadri constant.**
The generic ten-point Seshadri constant of $\mathbb{P}^2$, in the affine-chart model, is at most
$1/\sqrt{10}$.

Source: the general submaximal upper bound `ε ≤ √(D²/r)` for
`D = 𝒪_{ℙ²}(1)` and `r = 10`. -/
theorem submaximalUpperBound_wanted :
    seshadriConstant10 ≤ 1 / Real.sqrt 10 := by
  unfold seshadriConstant10 genericSeshadriConstant
  apply csSup_le
  · exact ⟨affineSeshadriConstant stdPts, stdPts, stdPts_injective, rfl⟩
  · intro r hr
    obtain ⟨x, _, rfl⟩ := hr
    exact affine_le x

end MathlibExt.AlgebraicGeometry.SeshadriConstantWanted
