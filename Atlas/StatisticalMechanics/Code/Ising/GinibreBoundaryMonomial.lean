/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Ising.GinibreBoundary

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in


theorem IsSpinMonomial.xnor {f : ConfigSpace V -> Real}
    (hf : IsSpinMonomial f) (a q : ConfigSpace V) :
    f (xnor a q) = f a * f q := by
  obtain ⟨m, hm⟩ := hf
  simp only [hm, monomial, spin_xnor, mul_pow]
  exact Finset.prod_mul_distrib

omit [DecidableEq V] in

theorem IsSpinMonomial.eq_pm {f : ConfigSpace V -> Real}
    (hf : IsSpinMonomial f) (s : ConfigSpace V) :
    f s = 1 ∨ f s = -1 := by
  obtain ⟨m, hm⟩ := hf
  apply mul_self_eq_one_iff.mp
  simp only [hm, monomial, ← Finset.prod_mul_distrib, ← mul_pow]
  exact Finset.prod_eq_one fun x _ => by rw [spin_sq, one_pow]

omit [DecidableEq V] in
theorem IsSpinMonomial.one_add_nonneg {f : ConfigSpace V -> Real}
    (hf : IsSpinMonomial f) (s : ConfigSpace V) :
    0 <= 1 + f s := by
  rcases hf.eq_pm s with h | h <;> rw [h] <;> norm_num

omit [DecidableEq V] in
theorem IsSpinMonomial.one_sub_nonneg {f : ConfigSpace V -> Real}
    (hf : IsSpinMonomial f) (s : ConfigSpace V) :
    0 <= 1 - f s := by
  rcases hf.eq_pm s with h | h <;> rw [h] <;> norm_num


theorem ginibre_cross_monomial_inner_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (f g : ConfigSpace V -> Real)
    (hf : IsSpinMonomial f) (hg : IsSpinMonomial g)
    (q : ConfigSpace V) :
    0 <= ∑ a : ConfigSpace V,
      wJ E J hPlus a * wJ E J h (xnor a q) *
        ((f a + f (xnor a q)) * (g a - g (xnor a q))) := by
  let Kq : Sym2 V -> Real := fun e => J e * (1 + bond q e)
  let hq : V -> Real := fun v => hPlus v + h v * spin q v
  let c : Real := (1 + f q) * (1 - g q)
  have hKq : ∀ e ∈ E, 0 <= Kq e := by
    intro e he
    exact mul_nonneg (hJ e he) (one_add_bond_nonneg q e)
  have hhq : forall v, 0 <= hq v :=
    fun v => ginibre_inducedField_nonneg hPlus h hdom q v
  have hc : 0 <= c :=
    mul_nonneg (hf.one_add_nonneg q) (hg.one_sub_nonneg q)
  have hfg : IsSpinMonomial (fun a => f a * g a) := hf.mul hg
  have hkernel : 0 <= ∑ a : ConfigSpace V,
      (f a * g a) *
        ((∏ e ∈ E,
            (Real.cosh (Kq e) + bond a e * Real.sinh (Kq e))) *
          ∏ v : V,
            (Real.cosh (hq v) + spin a v * Real.sinh (hq v))) := by
    exact inner_sum_nonneg' E
      (fun e => Real.cosh (Kq e)) (fun e => Real.sinh (Kq e))
      (fun v => Real.cosh (hq v)) (fun v => Real.sinh (hq v))
      (fun _ _ => (Real.cosh_pos _).le)
      (fun e he => Real.sinh_nonneg_iff.mpr (hKq e he))
      (fun _ => (Real.cosh_pos _).le)
      (fun v => Real.sinh_nonneg_iff.mpr (hhq v))
      (fun a => f a * g a) hfg
  have hweighted : 0 <= ∑ a : ConfigSpace V,
      c * ((f a * g a) * wJ E Kq hq a) := by
    rw [← Finset.mul_sum]
    exact mul_nonneg hc (by
      simpa only [ghsvp_wJ_factor] using hkernel)
  convert hweighted using 1
  apply Finset.sum_congr rfl
  intro a _
  rw [ginibre_crossWeight_factor, hf.xnor, hg.xnor]
  have hfsq : f a * f a = 1 := mul_self_eq_one_iff.mpr (hf.eq_pm a)
  have hgsq : g a * g a = 1 := mul_self_eq_one_iff.mpr (hg.eq_pm a)
  dsimp [Kq, hq, c]
  nlinarith


theorem ginibre_cross_monomial_numerator_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (f g : ConfigSpace V -> Real)
    (hf : IsSpinMonomial f) (hg : IsSpinMonomial g) :
    0 <= ∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
      wJ E J hPlus a * wJ E J h b *
        ((f a + f b) * (g a - g b)) := by
  rw [← Fintype.sum_prod_type']
  rw [sum_dbl_reindex (fun p : ConfigSpace V × ConfigSpace V =>
    wJ E J hPlus p.1 * wJ E J h p.2 *
      ((f p.1 + f p.2) * (g p.1 - g p.2)))]
  rw [Fintype.sum_prod_type_right]
  exact Finset.sum_nonneg fun q _ =>
    ginibre_cross_monomial_inner_nonneg E J hPlus h hJ hdom f g hf hg q


theorem ginibre_boundary_monomial_correlation
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (f g : ConfigSpace V -> Real)
    (hf : IsSpinMonomial f) (hg : IsSpinMonomial g) :
    expJ E J hPlus (fun s => f s * g s) -
        expJ E J h (fun s => f s * g s) >=
      expJ E J hPlus f * expJ E J h g -
        expJ E J hPlus g * expJ E J h f := by
  have hnum := ginibre_cross_monomial_numerator_nonneg
    E J hPlus h hJ hdom f g hf hg
  have hZp : 0 < ZJ E J hPlus := ZJ_pos E J hPlus
  have hZh : 0 < ZJ E J h := ZJ_pos E J h
  have hden : 0 < ZJ E J hPlus * ZJ E J h := mul_pos hZp hZh
  have hfactor (u v : ConfigSpace V -> Real) :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b * (u a * v b)) =
      (∑ a : ConfigSpace V, u a * wJ E J hPlus a) *
        ∑ b : ConfigSpace V, v b * wJ E J h b := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hdouble :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b *
          ((f a + f b) * (g a - g b))) =
        (∑ a : ConfigSpace V, (f a * g a) * wJ E J hPlus a) *
            ZJ E J h -
          ZJ E J hPlus *
            (∑ b : ConfigSpace V, (f b * g b) * wJ E J h b) -
          (∑ a : ConfigSpace V, f a * wJ E J hPlus a) *
            (∑ b : ConfigSpace V, g b * wJ E J h b) +
          (∑ a : ConfigSpace V, g a * wJ E J hPlus a) *
            ∑ b : ConfigSpace V, f b * wJ E J h b := by
    have hexpand (a b : ConfigSpace V) :
        wJ E J hPlus a * wJ E J h b *
            ((f a + f b) * (g a - g b)) =
          wJ E J hPlus a * wJ E J h b * ((f a * g a) * 1) -
            wJ E J hPlus a * wJ E J h b * (1 * (f b * g b)) -
            wJ E J hPlus a * wJ E J h b * (f a * g b) +
            wJ E J hPlus a * wJ E J h b * (g a * f b) := by ring
    simp_rw [hexpand]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hfactor (fun a => f a * g a) (fun _ => 1),
      hfactor (fun _ => 1) (fun b => f b * g b),
      hfactor f g, hfactor g f]
    simp only [one_mul]
    unfold ZJ
    ring
  have hquot : 0 <=
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b *
          ((f a + f b) * (g a - g b))) /
        (ZJ E J hPlus * ZJ E J h) := div_nonneg hnum hden.le
  rw [hdouble] at hquot
  unfold expJ
  field_simp [hZp.ne', hZh.ne'] at hquot ⊢
  nlinarith



theorem ginibre_boundary_monomial_product_mono
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (f g : ConfigSpace V -> Real)
    (hf : IsSpinMonomial f) (hg : IsSpinMonomial g) :
    expJ E J h (fun s => f s * g s) <=
      expJ E J hPlus (fun s => f s * g s) := by
  have hfg := ginibre_boundary_monomial_correlation
    E J hPlus h hJ hdom f g hf hg
  have hgf := ginibre_boundary_monomial_correlation
    E J hPlus h hJ hdom g f hg hf
  have hp : expJ E J hPlus (fun s => g s * f s) =
      expJ E J hPlus (fun s => f s * g s) := by
    congr 1
    funext s
    ring
  have hm : expJ E J h (fun s => g s * f s) =
      expJ E J h (fun s => f s * g s) := by
    congr 1
    funext s
    ring
  rw [hp, hm] at hgf
  linarith

end

end StatMech.Ising
