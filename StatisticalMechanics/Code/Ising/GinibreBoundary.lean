/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.Ising.GHSVertexPartition
import Code.Ising.GKS2

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem ginibre_crossWeight_factor
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (a q : ConfigSpace V) :
    wJ E J hPlus a * wJ E J h (xnor a q) =
      wJ E (fun e => J e * (1 + bond q e))
        (fun v => hPlus v + h v * spin q v) a := by
  unfold wJ
  rw [← Real.exp_add]
  congr 1
  simp_rw [bond_xnor, spin_xnor]
  have hedge :
      (∑ e ∈ E, J e * bond a e) +
          ∑ e ∈ E, J e * (bond a e * bond q e) =
        ∑ e ∈ E, J e * (1 + bond q e) * bond a e := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hfield :
      (∑ v : V, hPlus v * spin a v) +
          ∑ v : V, h v * (spin a v * spin q v) =
        ∑ v : V, (hPlus v + h v * spin q v) * spin a v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [show
    (∑ e ∈ E, J e * bond a e) + (∑ v : V, hPlus v * spin a v) +
        ((∑ e ∈ E, J e * (bond a e * bond q e)) +
          ∑ v : V, h v * (spin a v * spin q v)) =
      ((∑ e ∈ E, J e * bond a e) +
        ∑ e ∈ E, J e * (bond a e * bond q e)) +
      ((∑ v : V, hPlus v * spin a v) +
        ∑ v : V, h v * (spin a v * spin q v)) by ring,
    hedge, hfield]



theorem ginibre_inducedField_nonneg
    (hPlus h : V -> Real) (hdom : forall v, |h v| <= hPlus v)
    (q : ConfigSpace V) (v : V) :
    0 <= hPlus v + h v * spin q v := by
  rcases spin_eq_pm q v with hq | hq
  · rw [hq, mul_one]
    linarith [(abs_le.mp (hdom v)).1]
  · rw [hq, mul_neg_one]
    exact sub_nonneg.mpr (abs_le.mp (hdom v)).2



theorem ginibre_cross_inner_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (x y : V) (q : ConfigSpace V) :
    0 <= ∑ a : ConfigSpace V,
      wJ E J hPlus a * wJ E J h (xnor a q) *
        ((spin a x + spin (xnor a q) x) *
          (spin a y - spin (xnor a q) y)) := by
  let Kq : Sym2 V -> Real := fun e => J e * (1 + bond q e)
  let hq : V -> Real := fun v => hPlus v + h v * spin q v
  let c : Real := (1 + spin q x) * (1 - spin q y)
  have hKq : ∀ e ∈ E, 0 <= Kq e := by
    intro e he
    exact mul_nonneg (hJ e he) (one_add_bond_nonneg q e)
  have hhq : forall v, 0 <= hq v :=
    fun v => ginibre_inducedField_nonneg hPlus h hdom q v
  have hc : 0 <= c := by
    apply mul_nonneg (one_add_spin_nonneg q x)
    rcases spin_eq_pm q y with hy | hy <;> rw [hy] <;> norm_num
  have hobs : IsSpinMonomial
      (fun a : ConfigSpace V => spin a x * spin a y) :=
    (isSpinMonomial_spin x).mul (isSpinMonomial_spin y)
  have hkernel : 0 <= ∑ a : ConfigSpace V,
      (spin a x * spin a y) *
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
      (fun a => spin a x * spin a y) hobs
  have hweighted : 0 <= ∑ a : ConfigSpace V,
      c * ((spin a x * spin a y) * wJ E Kq hq a) := by
    rw [← Finset.mul_sum]
    exact mul_nonneg hc (by
      simpa only [ghsvp_wJ_factor] using hkernel)
  convert hweighted using 1
  apply Finset.sum_congr rfl
  intro a _
  rw [ginibre_crossWeight_factor]
  simp only [spin_xnor]
  dsimp [Kq, hq, c]
  ring


theorem ginibre_cross_numerator_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (x y : V) :
    0 <= ∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
      wJ E J hPlus a * wJ E J h b *
        ((spin a x + spin b x) * (spin a y - spin b y)) := by
  rw [← Fintype.sum_prod_type']
  rw [sum_dbl_reindex (fun p : ConfigSpace V × ConfigSpace V =>
    wJ E J hPlus p.1 * wJ E J h p.2 *
      ((spin p.1 x + spin p.2 x) * (spin p.1 y - spin p.2 y)))]
  rw [Fintype.sum_prod_type_right]
  exact Finset.sum_nonneg fun q _ =>
    ginibre_cross_inner_nonneg E J hPlus h hJ hdom x y q





theorem ginibre_boundary_correlation
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (x y : V) :
    expJ E J hPlus (fun s => spin s x * spin s y) -
        expJ E J h (fun s => spin s x * spin s y) >=
      expJ E J hPlus (fun s => spin s x) *
          expJ E J h (fun s => spin s y) -
        expJ E J hPlus (fun s => spin s y) *
          expJ E J h (fun s => spin s x) := by
  have hnum := ginibre_cross_numerator_nonneg
    E J hPlus h hJ hdom x y
  have hZp : 0 < ZJ E J hPlus := ZJ_pos E J hPlus
  have hZh : 0 < ZJ E J h := ZJ_pos E J h
  have hden : 0 < ZJ E J hPlus * ZJ E J h := mul_pos hZp hZh
  have hfactor (f g : ConfigSpace V -> Real) :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b * (f a * g b)) =
      (∑ a : ConfigSpace V, f a * wJ E J hPlus a) *
        ∑ b : ConfigSpace V, g b * wJ E J h b := by
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
          ((spin a x + spin b x) * (spin a y - spin b y))) =
        (∑ a : ConfigSpace V,
            (spin a x * spin a y) * wJ E J hPlus a) * ZJ E J h -
          ZJ E J hPlus *
            (∑ b : ConfigSpace V,
              (spin b x * spin b y) * wJ E J h b) -
          (∑ a : ConfigSpace V, spin a x * wJ E J hPlus a) *
            (∑ b : ConfigSpace V, spin b y * wJ E J h b) +
          (∑ a : ConfigSpace V, spin a y * wJ E J hPlus a) *
            ∑ b : ConfigSpace V, spin b x * wJ E J h b := by
    have hexpand (a b : ConfigSpace V) :
        wJ E J hPlus a * wJ E J h b *
            ((spin a x + spin b x) * (spin a y - spin b y)) =
          wJ E J hPlus a * wJ E J h b *
              ((spin a x * spin a y) * 1) -
            wJ E J hPlus a * wJ E J h b *
              (1 * (spin b x * spin b y)) -
            wJ E J hPlus a * wJ E J h b *
              (spin a x * spin b y) +
            wJ E J hPlus a * wJ E J h b *
              (spin a y * spin b x) := by ring
    simp_rw [hexpand]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hfactor (fun a => spin a x * spin a y) (fun _ => 1),
      hfactor (fun _ => 1) (fun b => spin b x * spin b y),
      hfactor (fun a => spin a x) (fun b => spin b y),
      hfactor (fun a => spin a y) (fun b => spin b x)]
    simp only [one_mul, mul_one]
    unfold ZJ
    ring
  have hidentity :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b *
          ((spin a x + spin b x) * (spin a y - spin b y))) /
          (ZJ E J hPlus * ZJ E J h) =
        (expJ E J hPlus (fun s => spin s x * spin s y) -
            expJ E J h (fun s => spin s x * spin s y)) -
          (expJ E J hPlus (fun s => spin s x) *
              expJ E J h (fun s => spin s y) -
            expJ E J hPlus (fun s => spin s y) *
              expJ E J h (fun s => spin s x)) := by
    rw [hdouble]
    unfold expJ
    field_simp [hZp.ne', hZh.ne']
    ring
  have hquot : 0 <=
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b *
          ((spin a x + spin b x) * (spin a y - spin b y))) /
          (ZJ E J hPlus * ZJ E J h) := div_nonneg hnum hden.le
  rw [hidentity] at hquot
  linarith




theorem ginibre_boundary_twoPoint_mono
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (x y : V) :
    expJ E J h (fun s => spin s x * spin s y) <=
      expJ E J hPlus (fun s => spin s x * spin s y) := by
  have hxy := ginibre_boundary_correlation E J hPlus h hJ hdom x y
  have hyx := ginibre_boundary_correlation E J hPlus h hJ hdom y x
  have hp : expJ E J hPlus (fun s => spin s y * spin s x) =
      expJ E J hPlus (fun s => spin s x * spin s y) := by
    congr 1
    funext s
    ring
  have hm : expJ E J h (fun s => spin s y * spin s x) =
      expJ E J h (fun s => spin s x * spin s y) := by
    congr 1
    funext s
    ring
  rw [hp, hm] at hyx
  linarith


theorem ginibre_boundary_bond_mono
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (e : Sym2 V) :
    expJ E J h (fun s => bond s e) <=
      expJ E J hPlus (fun s => bond s e) := by
  induction e with
  | h x y =>
      simpa only [bond_mk] using
        ginibre_boundary_twoPoint_mono E J hPlus h hJ hdom x y



theorem ginibre_cross_one_inner_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (x : V) (epsilon : Real)
    (hepsilon : forall q : ConfigSpace V,
      0 <= 1 + epsilon * spin q x)
    (q : ConfigSpace V) :
    0 <= ∑ a : ConfigSpace V,
      wJ E J hPlus a * wJ E J h (xnor a q) *
        (spin a x + epsilon * spin (xnor a q) x) := by
  let Kq : Sym2 V -> Real := fun e => J e * (1 + bond q e)
  let hq : V -> Real := fun v => hPlus v + h v * spin q v
  let c : Real := 1 + epsilon * spin q x
  have hKq : ∀ e ∈ E, 0 <= Kq e := by
    intro e he
    exact mul_nonneg (hJ e he) (one_add_bond_nonneg q e)
  have hhq : forall v, 0 <= hq v :=
    fun v => ginibre_inducedField_nonneg hPlus h hdom q v
  have hobs : IsSpinMonomial (fun a : ConfigSpace V => spin a x) :=
    isSpinMonomial_spin x
  have hkernel : 0 <= ∑ a : ConfigSpace V,
      spin a x *
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
      (fun a => spin a x) hobs
  have hweighted : 0 <= ∑ a : ConfigSpace V,
      c * (spin a x * wJ E Kq hq a) := by
    rw [← Finset.mul_sum]
    exact mul_nonneg (hepsilon q) (by
      simpa only [ghsvp_wJ_factor] using hkernel)
  convert hweighted using 1
  apply Finset.sum_congr rfl
  intro a _
  rw [ginibre_crossWeight_factor]
  simp only [spin_xnor]
  dsimp [Kq, hq, c]
  ring


theorem ginibre_boundary_onePoint_signed_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (x : V) (epsilon : Real)
    (hepsilon : forall q : ConfigSpace V,
      0 <= 1 + epsilon * spin q x) :
    0 <= expJ E J hPlus (fun s => spin s x) +
      epsilon * expJ E J h (fun s => spin s x) := by
  have hnum : 0 <= ∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
      wJ E J hPlus a * wJ E J h b *
        (spin a x + epsilon * spin b x) := by
    rw [← Fintype.sum_prod_type']
    rw [sum_dbl_reindex (fun p : ConfigSpace V × ConfigSpace V =>
      wJ E J hPlus p.1 * wJ E J h p.2 *
        (spin p.1 x + epsilon * spin p.2 x))]
    rw [Fintype.sum_prod_type_right]
    exact Finset.sum_nonneg fun q _ =>
      ginibre_cross_one_inner_nonneg E J hPlus h hJ hdom x epsilon hepsilon q
  have hZp : 0 < ZJ E J hPlus := ZJ_pos E J hPlus
  have hZh : 0 < ZJ E J h := ZJ_pos E J h
  have hfactor (f g : ConfigSpace V -> Real) :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b * (f a * g b)) =
      (∑ a : ConfigSpace V, f a * wJ E J hPlus a) *
        ∑ b : ConfigSpace V, g b * wJ E J h b := by
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
          (spin a x + epsilon * spin b x)) =
        (∑ a : ConfigSpace V, spin a x * wJ E J hPlus a) * ZJ E J h +
          epsilon * ZJ E J hPlus *
            ∑ b : ConfigSpace V, spin b x * wJ E J h b := by
    rw [show
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b *
          (spin a x + epsilon * spin b x)) =
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b * (spin a x * 1)) +
      epsilon * (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b * (1 * spin b x)) by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        ring]
    rw [hfactor (fun a => spin a x) (fun _ => 1),
      hfactor (fun _ => 1) (fun b => spin b x)]
    simp only [one_mul, mul_one]
    unfold ZJ
    ring
  have hden : 0 < ZJ E J hPlus * ZJ E J h := mul_pos hZp hZh
  have hquot : 0 <=
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ E J hPlus a * wJ E J h b *
          (spin a x + epsilon * spin b x)) /
        (ZJ E J hPlus * ZJ E J h) := div_nonneg hnum hden.le
  rw [hdouble] at hquot
  unfold expJ
  field_simp [hZp.ne', hZh.ne'] at hquot
  field_simp [hZp.ne', hZh.ne']
  nlinarith



theorem ginibre_boundary_abs_onePoint_le
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (x : V) :
    |expJ E J h (fun s => spin s x)| <=
      expJ E J hPlus (fun s => spin s x) := by
  have hadd := ginibre_boundary_onePoint_signed_nonneg
    E J hPlus h hJ hdom x 1 (fun q => by
      simpa using one_add_spin_nonneg q x)
  have hsub := ginibre_boundary_onePoint_signed_nonneg
    E J hPlus h hJ hdom x (-1) (fun q => by
      rcases spin_eq_pm q x with hq | hq <;> rw [hq] <;> norm_num)
  rw [abs_le]
  constructor <;> linarith




theorem ginibre_chain_correlation_telescope
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (v : Nat -> V) (N : Nat) (m : Real)
    (hconst : forall j, j <= N ->
      expJ E J hPlus (fun s => spin s (v j)) = m) :
    m * (expJ E J h (fun s => spin s (v N)) -
        expJ E J h (fun s => spin s (v 0))) <=
      ∑ j ∈ Finset.range N,
        (expJ E J hPlus
              (fun s => spin s (v j) * spin s (v (j + 1))) -
          expJ E J h
              (fun s => spin s (v j) * spin s (v (j + 1)))) := by
  let q : Nat -> Real := fun j =>
    expJ E J h (fun s => spin s (v j))
  have hstep (j : Nat) (hj : j ∈ Finset.range N) :
      m * (q (j + 1) - q j) <=
        expJ E J hPlus
              (fun s => spin s (v j) * spin s (v (j + 1))) -
          expJ E J h
              (fun s => spin s (v j) * spin s (v (j + 1))) := by
    have hg := ginibre_boundary_correlation E J hPlus h hJ hdom
      (v j) (v (j + 1))
    rw [hconst j (Nat.le_of_lt (Finset.mem_range.mp hj)),
      hconst (j + 1) (Finset.mem_range.mp hj)] at hg
    dsimp [q]
    linarith
  calc
    m * (expJ E J h (fun s => spin s (v N)) -
        expJ E J h (fun s => spin s (v 0))) =
        ∑ j ∈ Finset.range N, m * (q (j + 1) - q j) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ <= _ := Finset.sum_le_sum hstep




theorem ginibre_chain_correlation_ge_two_mul_sq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (hPlus h : V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e)
    (hdom : forall v, |h v| <= hPlus v)
    (v : Nat -> V) (N : Nat) (m : Real)
    (hconst : forall j, j <= N ->
      expJ E J hPlus (fun s => spin s (v j)) = m)
    (hbottom : expJ E J h (fun s => spin s (v 0)) = -m)
    (htop : expJ E J h (fun s => spin s (v N)) = m) :
    2 * m ^ 2 <=
      ∑ j ∈ Finset.range N,
        (expJ E J hPlus
              (fun s => spin s (v j) * spin s (v (j + 1))) -
          expJ E J h
              (fun s => spin s (v j) * spin s (v (j + 1)))) := by
  have htel := ginibre_chain_correlation_telescope
    E J hPlus h hJ hdom v N m hconst
  rw [hbottom, htop] at htel
  nlinarith

end

end StatMech.Ising
