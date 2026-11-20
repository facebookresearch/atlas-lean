/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Mathlib
import Code.Ising.GHSDuplicateVariable
import Code.Ising.GHSVertexPartition
import Code.Inequalities.FKG

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





theorem ghsL_ursell_eq_four_duplicate_cov (β h : ℝ) (o x y : V) :
    isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s x)
              * isingExpectation G β h (fun s => spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s y)
              * isingExpectation G β h (fun s => spin s x)
          + 2 * isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x)
              * isingExpectation G β h (fun s => spin s y)
      = 4 * (isingExp2 G β h
              (fun a b => uvar a b o * uvar a b x * tvar a b y)
            - isingExp2 G β h (fun a b => uvar a b o * uvar a b x)
                * isingExp2 G β h (fun a b => tvar a b y)) := by
  have huu := ghsDV_cov2_eq_two_uu G β h o x
  have ht := ghsDV_onePt_eq_tt G β h y
  have hthree :
      (fun a b => uvar a b o * uvar a b x * tvar a b y)
        = (fun a b =>
            (1 / 8 : ℝ) * (spin a o * (spin a x * spin a y))
            + (1 / 8 : ℝ) * ((spin a o * spin a x) * spin b y)
            + (-1 / 8 : ℝ) * ((spin a o * spin a y) * spin b x)
            + (-1 / 8 : ℝ) * (spin a o * (spin b x * spin b y))
            + (-1 / 8 : ℝ) * ((spin a x * spin a y) * spin b o)
            + (-1 / 8 : ℝ) * (spin a x * (spin b o * spin b y))
            + (1 / 8 : ℝ) * (spin a y * (spin b o * spin b x))
            + (1 / 8 : ℝ) * (spin b o * (spin b x * spin b y))) := by
    funext a b
    simp only [uvar, tvar]
    ring
  rw [hthree]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor,
    isingExp2_factor_a, isingExp2_factor_b]
  unfold cov2 at huu
  unfold onePt at ht
  rw [show isingExp2 G β h (fun a b => uvar a b o * uvar a b x) =
      (isingExpectation G β h (fun s => spin s o * spin s x)
        - isingExpectation G β h (fun s => spin s o)
          * isingExpectation G β h (fun s => spin s x)) / 2 by linarith [huu]]
  rw [← ht]
  ring


theorem ghsL_pair_of_duplicate_cov_nonpos (β h : ℝ) (o x y : V)
    (hcov : isingExp2 G β h
              (fun a b => uvar a b o * uvar a b x * tvar a b y)
            ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x)
                * isingExp2 G β h (fun a b => tvar a b y)) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
  rw [← sub_nonpos]
  rw [ghsThreePoint_eq_ursell, ghsL_ursell_eq_four_duplicate_cov]
  linarith




def ghsLAgreement (a b : ConfigSpace V) : ConfigSpace V := fun v => decide (a v = b v)


def ghsLMate (q a : ConfigSpace V) : ConfigSpace V := fun v => if q v then a v else !a v

@[simp] theorem ghsLAgreement_mate (q a : ConfigSpace V) :
    ghsLAgreement (V := V) a (ghsLMate q a) = q := by
  funext v
  unfold ghsLAgreement ghsLMate
  by_cases hq : q v <;> cases a v <;> simp [hq]

@[simp] theorem ghsLMate_agreement (a b : ConfigSpace V) :
    ghsLMate (ghsLAgreement (V := V) a b) a = b := by
  funext v
  unfold ghsLAgreement ghsLMate
  cases ha : a v <;> cases hb : b v <;> simp [ha, hb]



theorem ghsL_uvar_mate (q a : ConfigSpace V) (v : V) :
    uvar a (ghsLMate q a) v = if q v then 0 else spin a v := by
  unfold uvar ghsLMate spin
  by_cases hq : q v <;> cases ha : a v <;> norm_num [hq, ha]



theorem ghsL_tvar_mate (q a : ConfigSpace V) (v : V) :
    tvar a (ghsLMate q a) v = if q v then spin a v else 0 := by
  unfold tvar ghsLMate spin
  by_cases hq : q v <;> cases ha : a v <;> norm_num [hq, ha]


def ghsLAgreeFinset (q : ConfigSpace V) : Finset V :=
  Finset.univ.filter (fun v => q v = true)

@[simp] theorem mem_ghsLAgreeFinset (q : ConfigSpace V) (v : V) :
    v ∈ ghsLAgreeFinset q ↔ q v = true := by
  simp [ghsLAgreeFinset]

theorem ghsLAgreeFinset_monotone : Monotone (ghsLAgreeFinset : ConfigSpace V → Finset V) := by
  intro q r hqr v hv
  rw [mem_ghsLAgreeFinset] at hv ⊢
  have := hqr v
  cases hr : r v
  · exact False.elim ((not_lt_of_ge this) (by simpa [hv, hr] using Bool.false_lt_true))
  · rfl

@[simp] theorem ghsLAgreeFinset_sup (q r : ConfigSpace V) :
    ghsLAgreeFinset (q ⊔ r) = ghsLAgreeFinset q ∪ ghsLAgreeFinset r := by
  ext v
  cases hq : q v <;> cases hr : r v <;> simp [ghsLAgreeFinset, hq, hr]

@[simp] theorem ghsLAgreeFinset_inf (q r : ConfigSpace V) :
    ghsLAgreeFinset (q ⊓ r) = ghsLAgreeFinset q ∩ ghsLAgreeFinset r := by
  ext v
  cases hq : q v <;> cases hr : r v <;> simp [ghsLAgreeFinset, hq, hr]



theorem ghsL_bond_add_mate (q a : ConfigSpace V) (e : Sym2 V) :
    bond a e + bond (ghsLMate q a) e =
      if Sharpness.edgeInside (ghsLAgreeFinset q) e then 2 * bond a e
      else if Sharpness.edgeInside (ghsLAgreeFinset q)ᶜ e then 2 * bond a e
      else 0 := by
  induction e with
  | h x y =>
      simp only [bond_mk]
      unfold ghsLMate spin Sharpness.edgeInside
      by_cases hx : q x <;> by_cases hy : q y <;>
        cases hax : a x <;> cases hay : a y <;>
        norm_num [mem_ghsLAgreeFinset, hx, hy, hax, hay]


theorem ghsL_spin_add_mate (q a : ConfigSpace V) (v : V) :
    spin a v + spin (ghsLMate q a) v =
      if q v then 2 * spin a v else 0 := by
  unfold ghsLMate spin
  by_cases hq : q v <;> cases ha : a v <;> norm_num [hq, ha]


theorem ghsL_bondSum_split (q a : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, bond a e) +
        ∑ e ∈ G.edgeFinset, bond (ghsLMate q a) e =
      2 * (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e)
        + 2 * (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, bond a e) := by
  rw [← Finset.sum_add_distrib]
  simp_rw [ghsL_bond_add_mate]
  unfold ghsvp_vertexEdges
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hA : Sharpness.edgeInside (ghsLAgreeFinset q) e
  · have hAc : ¬ Sharpness.edgeInside (ghsLAgreeFinset q)ᶜ e := by
      induction e with
      | h x y => simp_all [Sharpness.edgeInside]
    simp [hA, hAc]
  · by_cases hAc : Sharpness.edgeInside (ghsLAgreeFinset q)ᶜ e
    · simp [hA, hAc]
    · simp [hA, hAc]


theorem ghsL_spinSum_split (q a : ConfigSpace V) :
    (∑ v : V, spin a v) + ∑ v : V, spin (ghsLMate q a) v =
      2 * ∑ v ∈ ghsLAgreeFinset q, spin a v := by
  rw [← Finset.sum_add_distrib]
  simp_rw [ghsL_spin_add_mate]
  rw [Finset.mul_sum]
  simp [ghsLAgreeFinset, Finset.sum_filter]


noncomputable def ghsLTWeight (β h : ℝ) (q a : ConfigSpace V) : ℝ :=
  Real.exp (2 * β *
    ((∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e)
      + h * ∑ v ∈ ghsLAgreeFinset q, spin a v))


noncomputable def ghsLUWeight (β : ℝ) (q a : ConfigSpace V) : ℝ :=
  Real.exp (2 * β *
    ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, bond a e)


theorem ghsL_duplicateWeight_eq_tWeight_mul_uWeight (β h : ℝ)
    (q a : ConfigSpace V) :
    isingWeight G β h a * isingWeight G β h (ghsLMate q a) =
      ghsLTWeight G β h q a * ghsLUWeight G β q a := by
  unfold isingWeight ghsLTWeight ghsLUWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hb := ghsL_bondSum_split G q a
  have hs := ghsL_spinSum_split q a
  calc
    -β * hamiltonian G h a + -β * hamiltonian G h (ghsLMate q a) =
        β * ((∑ e ∈ G.edgeFinset, bond a e) +
          ∑ e ∈ G.edgeFinset, bond (ghsLMate q a) e) +
        β * h * ((∑ v : V, spin a v) + ∑ v : V, spin (ghsLMate q a) v) := by
      unfold hamiltonian
      ring
    _ = 2 * β *
          ((∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e) +
            h * ∑ v ∈ ghsLAgreeFinset q, spin a v) +
        2 * β * ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, bond a e := by
      rw [hb, hs]
      ring


def ghsLSplitEquiv (q : ConfigSpace V) :
    ConfigSpace V ≃
      ((v : {v : V // q v = true}) → Bool) ×
        ((v : {v : V // ¬ q v = true}) → Bool) :=
  Equiv.piEquivPiSubtypeProd (fun v => q v = true) (fun _ => Bool)


theorem ghsL_split_sum_product (q : ConfigSpace V)
    (f : ((v : {v : V // q v = true}) → Bool) → ℝ)
    (g : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ) :
    (∑ a : ConfigSpace V, f (ghsLSplitEquiv q a).1 * g (ghsLSplitEquiv q a).2) =
      (∑ st, f st) * ∑ su, g su := by
  let T := (v : {v : V // q v = true}) → Bool
  let U := (v : {v : V // ¬ q v = true}) → Bool
  calc
    (∑ a : ConfigSpace V, f (ghsLSplitEquiv q a).1 * g (ghsLSplitEquiv q a).2) =
        ∑ p : T × U, f p.1 * g p.2 :=
      Equiv.sum_comp (ghsLSplitEquiv q) (fun p : T × U => f p.1 * g p.2)
    _ = (∑ st, f st) * ∑ su, g su := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro st _
      rw [Finset.mul_sum]


theorem ghsL_split_cross_product (q : ConfigSpace V)
    (f₀ f₁ : ((v : {v : V // q v = true}) → Bool) → ℝ)
    (g₀ g₁ : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ) :
    (∑ a : ConfigSpace V,
        f₀ (ghsLSplitEquiv q a).1 * g₀ (ghsLSplitEquiv q a).2) *
      (∑ a : ConfigSpace V,
        f₁ (ghsLSplitEquiv q a).1 * g₁ (ghsLSplitEquiv q a).2) =
    (∑ a : ConfigSpace V,
        f₀ (ghsLSplitEquiv q a).1 * g₁ (ghsLSplitEquiv q a).2) *
      (∑ a : ConfigSpace V,
        f₁ (ghsLSplitEquiv q a).1 * g₀ (ghsLSplitEquiv q a).2) := by
  simp_rw [ghsL_split_sum_product]
  ring


def ghsLTComplete (q : ConfigSpace V)
    (st : (v : {v : V // q v = true}) → Bool) : ConfigSpace V :=
  (ghsLSplitEquiv q).symm (st, fun _ => false)


def ghsLUComplete (q : ConfigSpace V)
    (su : (v : {v : V // ¬ q v = true}) → Bool) : ConfigSpace V :=
  (ghsLSplitEquiv q).symm (fun _ => false, su)

theorem ghsLTComplete_eq_on (q a : ConfigSpace V) {v : V} (hv : q v = true) :
    ghsLTComplete q (ghsLSplitEquiv q a).1 v = a v := by
  simp [ghsLTComplete, ghsLSplitEquiv, hv]

theorem ghsLUComplete_eq_on (q a : ConfigSpace V) {v : V} (hv : ¬ q v = true) :
    ghsLUComplete q (ghsLSplitEquiv q a).2 v = a v := by
  simp [ghsLUComplete, ghsLSplitEquiv, hv]


theorem ghsLTWeight_split (β h : ℝ) (q a : ConfigSpace V) :
    ghsLTWeight G β h q a =
      ghsLTWeight G β h q (ghsLTComplete q (ghsLSplitEquiv q a).1) := by
  unfold ghsLTWeight
  have hb :
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e) =
        ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
          bond (ghsLTComplete q (ghsLSplitEquiv q a).1) e := by
    apply Finset.sum_congr rfl
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    induction e with
    | h x y =>
        have hx : q x = true := mem_ghsLAgreeFinset q x |>.mp (hi x (by simp))
        have hy : q y = true := mem_ghsLAgreeFinset q y |>.mp (hi y (by simp))
        simp only [bond_mk]
        rw [show spin (ghsLTComplete q (ghsLSplitEquiv q a).1) x = spin a x by
          unfold spin; rw [ghsLTComplete_eq_on q a hx]]
        rw [show spin (ghsLTComplete q (ghsLSplitEquiv q a).1) y = spin a y by
          unfold spin; rw [ghsLTComplete_eq_on q a hy]]
  have hs : (∑ v ∈ ghsLAgreeFinset q, spin a v) =
      ∑ v ∈ ghsLAgreeFinset q, spin (ghsLTComplete q (ghsLSplitEquiv q a).1) v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hq := (mem_ghsLAgreeFinset q v).mp hv
    unfold spin
    rw [ghsLTComplete_eq_on q a hq]
  rw [hb, hs]


theorem ghsLUWeight_split (β : ℝ) (q a : ConfigSpace V) :
    ghsLUWeight G β q a =
      ghsLUWeight G β q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsLUWeight
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    induction e with
    | h x y =>
        have hx : ¬ q x = true := by
          simpa using (Finset.mem_compl.mp (hi x (by simp)))
        have hy : ¬ q y = true := by
          simpa using (Finset.mem_compl.mp (hi y (by simp)))
        simp only [bond_mk]
        rw [show spin (ghsLUComplete q (ghsLSplitEquiv q a).2) x = spin a x by
          unfold spin; rw [ghsLUComplete_eq_on q a hx]]
        rw [show spin (ghsLUComplete q (ghsLSplitEquiv q a).2) y = spin a y by
          unfold spin; rw [ghsLUComplete_eq_on q a hy]]


theorem ghsL_tvar_split (q a : ConfigSpace V) (y : V) :
    tvar a (ghsLMate q a) y =
      tvar (ghsLTComplete q (ghsLSplitEquiv q a).1)
        (ghsLMate q (ghsLTComplete q (ghsLSplitEquiv q a).1)) y := by
  rw [ghsL_tvar_mate, ghsL_tvar_mate]
  by_cases hy : q y
  · simp only [if_pos hy]
    unfold spin
    rw [ghsLTComplete_eq_on q a hy]
  · simp [hy]


theorem ghsL_uvar_mul_split (q a : ConfigSpace V) (o x : V) :
    uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x =
      uvar (ghsLUComplete q (ghsLSplitEquiv q a).2)
          (ghsLMate q (ghsLUComplete q (ghsLSplitEquiv q a).2)) o *
        uvar (ghsLUComplete q (ghsLSplitEquiv q a).2)
          (ghsLMate q (ghsLUComplete q (ghsLSplitEquiv q a).2)) x := by
  simp only [ghsL_uvar_mate]
  by_cases ho : q o <;> by_cases hx : q x
  · simp [ho]
  · simp [ho]
  · simp [hx]
  · simp only [if_neg ho, if_neg hx]
    congr 1 <;> unfold spin
    · rw [ghsLUComplete_eq_on q a ho]
    · rw [ghsLUComplete_eq_on q a hx]


def ghsLXnorEquiv :
    (ConfigSpace V × ConfigSpace V) ≃ (ConfigSpace V × ConfigSpace V) where
  toFun p := (ghsLAgreement p.1 p.2, p.1)
  invFun p := (p.2, ghsLMate p.1 p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp


theorem ghsL_sum_pair_xnor (F : ConfigSpace V → ConfigSpace V → ℝ) :
    (∑ a : ConfigSpace V, ∑ b : ConfigSpace V, F a b)
      = ∑ q : ConfigSpace V, ∑ a : ConfigSpace V, F a (ghsLMate q a) := by
  calc
    (∑ a : ConfigSpace V, ∑ b : ConfigSpace V, F a b) =
        ∑ p : ConfigSpace V × ConfigSpace V, F p.1 p.2 :=
      (Fintype.sum_prod_type (fun p : ConfigSpace V × ConfigSpace V => F p.1 p.2)).symm
    _ = ∑ p : ConfigSpace V × ConfigSpace V,
        (fun qa => F qa.2 (ghsLMate qa.1 qa.2)) ((ghsLXnorEquiv (V := V)) p) := by
      apply Finset.sum_congr rfl
      intro p _
      simp [ghsLXnorEquiv]
    _ = ∑ qa : ConfigSpace V × ConfigSpace V,
        F qa.2 (ghsLMate qa.1 qa.2) :=
      Equiv.sum_comp (ghsLXnorEquiv (V := V))
        (fun qa => F qa.2 (ghsLMate qa.1 qa.2))
    _ = ∑ q : ConfigSpace V, ∑ a : ConfigSpace V, F a (ghsLMate q a) :=
      Fintype.sum_prod_type (fun qa : ConfigSpace V × ConfigSpace V =>
        F qa.2 (ghsLMate qa.1 qa.2))




noncomputable def ghsLFibreWeight (β h : ℝ) (q a : ConfigSpace V) : ℝ :=
  isingWeight G β h a * isingWeight G β h (ghsLMate q a)


noncomputable def ghsLFibreMass (β h : ℝ) (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V, ghsLFibreWeight G β h q a


noncomputable def ghsLFibreNumerator (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V,
    ghsLFibreWeight G β h q a * F a (ghsLMate q a)


noncomputable def ghsLFibreExpectation (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ghsLFibreNumerator G β h F q / ghsLFibreMass G β h q


noncomputable def ghsLAgreementProb (β h : ℝ) (q : ConfigSpace V) : ℝ :=
  ghsLFibreMass G β h q / (isingZ G β h) ^ 2

theorem ghsLFibreWeight_pos (β h : ℝ) (q a : ConfigSpace V) :
    0 < ghsLFibreWeight G β h q a :=
  mul_pos (isingWeight_pos G β h a) (isingWeight_pos G β h (ghsLMate q a))

theorem ghsLFibreMass_pos (β h : ℝ) (q : ConfigSpace V) :
    0 < ghsLFibreMass G β h q := by
  unfold ghsLFibreMass
  apply Finset.sum_pos
  · intro a _
    exact ghsLFibreWeight_pos G β h q a
  · exact Finset.univ_nonempty

theorem ghsLAgreementProb_nonneg (β h : ℝ) :
    0 ≤ ghsLAgreementProb G β h := fun q =>
  div_nonneg (ghsLFibreMass_pos G β h q).le (sq_nonneg _)


theorem ghsLAgreementProb_sum_eq_one (β h : ℝ) :
    ∑ q : ConfigSpace V, ghsLAgreementProb G β h q = 1 := by
  have hreindex := ghsL_sum_pair_xnor (V := V)
    (fun a b => isingWeight G β h a * isingWeight G β h b)
  have hmass : (∑ q : ConfigSpace V, ghsLFibreMass G β h q) = (isingZ G β h) ^ 2 := by
    unfold ghsLFibreMass ghsLFibreWeight isingZ
    rw [← hreindex]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  unfold ghsLAgreementProb
  rw [← Finset.sum_div, hmass]
  exact div_self (pow_ne_zero 2 (isingZ_ne_zero G β h))



theorem ghsLAgreementProb_fkg_of_subsetMass_scale (β h c : ℝ)
    (hc : 0 < c)
    (hscale : ∀ q : ConfigSpace V,
      ghsvp_subsetMass G β h (ghsLAgreeFinset q) = c * ghsLFibreMass G β h q)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    FKGLatticeCondition (ghsLAgreementProb G β h) := by
  intro q r
  have hsub := ghsvp_subsetMass_logSupermodular G β h hβ hh
    (ghsLAgreeFinset q) (ghsLAgreeFinset r)
  rw [← ghsLAgreeFinset_sup, ← ghsLAgreeFinset_inf] at hsub
  simp_rw [hscale] at hsub
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hfibre : ghsLFibreMass G β h q * ghsLFibreMass G β h r ≤
      ghsLFibreMass G β h (q ⊔ r) * ghsLFibreMass G β h (q ⊓ r) := by
    nlinarith [hsub]
  unfold ghsLAgreementProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right hfibre (mul_nonneg (sq_nonneg _) (sq_nonneg _))


theorem ghsLTWeight_eq_wJ_restricted (β h : ℝ) (q a : ConfigSpace V) :
    ghsLTWeight G β h q a =
      Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β)
        (fun x => if x ∈ ghsLAgreeFinset q then 2 * β * h else 0) a := by
  unfold Sharpness.wJ ghsLTWeight
  congr 1
  have hb : (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
      (2 * β) * bond a e) =
      2 * β * ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e := by
    rw [Finset.mul_sum]
  have hf : (∑ x : V,
      (if x ∈ ghsLAgreeFinset q then 2 * β * h else 0) * spin a x) =
      2 * β * h * ∑ x ∈ ghsLAgreeFinset q, spin a x := by
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.mul_sum]
    unfold ghsLAgreeFinset
    apply Finset.sum_congr
    · ext x
      simp
    · simp
  rw [hb, hf]
  ring


theorem ghsLUWeight_eq_wJ (β : ℝ) (q a : ConfigSpace V) :
    ghsLUWeight G β q a =
      Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
        (fun _ => 2 * β) (fun _ => 0) a := by
  unfold ghsLUWeight Sharpness.wJ
  congr 1
  simp
  rw [Finset.mul_sum]


theorem ghsvp_subsetMass_eq_card_mul_fibreMass (β h : ℝ) (q : ConfigSpace V) :
    ghsvp_subsetMass G β h (ghsLAgreeFinset q) =
      (4 * Fintype.card (ConfigSpace V)) * ghsLFibreMass G β h q := by
  let T := (v : {v : V // q v = true}) → Bool
  let U := (v : {v : V // ¬ q v = true}) → Bool
  let fT : T → ℝ := fun st => ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : U → ℝ := fun su => ghsLUWeight G β q (ghsLUComplete q su)
  have hmass : ghsLFibreMass G β h q =
      (∑ st : T, fT st) * ∑ su : U, fU su := by
    unfold ghsLFibreMass ghsLFibreWeight
    calc
      (∑ a : ConfigSpace V,
          isingWeight G β h a * isingWeight G β h (ghsLMate q a)) =
          ∑ a : ConfigSpace V,
            fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
          ghsLTWeight_split, ghsLUWeight_split]
      _ = _ := ghsL_split_sum_product q fT fU
  have ht : ghsvp_tZ G β h (ghsLAgreeFinset q) =
      (∑ st : T, fT st) * Fintype.card U := by
    unfold ghsvp_tZ Sharpness.ZJ
    have hs := ghsL_split_sum_product (V := V) q fT (fun _ : U => (1 : ℝ))
    rw [show (∑ a : ConfigSpace V,
        Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
          (fun _ => 2 * β)
          (fun x => if x ∈ ghsLAgreeFinset q then 2 * β * h else 0) a) =
        ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) by
      apply Finset.sum_congr rfl
      intro a _
      rw [← ghsLTWeight_eq_wJ_restricted, ghsLTWeight_split]
      simp [fT]]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
  have hu : ghsvp_uZ G β (ghsLAgreeFinset q)ᶜ =
      Fintype.card T * ∑ su : U, fU su := by
    unfold ghsvp_uZ Sharpness.ZJ
    have hs := ghsL_split_sum_product (V := V) q (fun _ : T => (1 : ℝ)) fU
    rw [show (∑ a : ConfigSpace V,
        Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
          (fun _ => 2 * β) (fun _ => 0) a) =
        ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 by
      apply Finset.sum_congr rfl
      intro a _
      rw [← ghsLUWeight_eq_wJ, ghsLUWeight_split]
      simp [fU]]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
  have hcard : Fintype.card (ConfigSpace V) = Fintype.card T * Fintype.card U := by
    rw [Fintype.card_congr (ghsLSplitEquiv q), Fintype.card_prod]
  rw [ghsvp_subsetMass_eq_four_mul_tZ_uZ, ht, hu, hmass, hcard]
  norm_num [Nat.cast_mul]
  ring


theorem ghsL_isIngExp2_fibre (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp2 G β h F =
      ∑ q : ConfigSpace V,
        ghsLAgreementProb G β h q * ghsLFibreExpectation G β h F q := by
  unfold isingExp2
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  have hZ : isingZ G β h ≠ 0 := isingZ_ne_zero G β h
  have hlhs :
      (∑ a : ConfigSpace V,
          isingProb G β h a * isingProb G β h (ghsLMate q a) * F a (ghsLMate q a))
        = ghsLFibreNumerator G β h F q / (isingZ G β h) ^ 2 := by
    unfold ghsLFibreNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    unfold isingProb ghsLFibreWeight
    field_simp [hZ]
  rw [hlhs]
  unfold ghsLAgreementProb ghsLFibreExpectation
  field_simp [hm, hZ]


@[simp] theorem ghsLFibreExpectation_const (β h r : ℝ) (q : ConfigSpace V) :
    ghsLFibreExpectation G β h (fun _ _ => r) q = r := by
  unfold ghsLFibreExpectation ghsLFibreNumerator ghsLFibreMass
  have hm : (∑ a : ConfigSpace V, ghsLFibreWeight G β h q a) ≠ 0 :=
    (ghsLFibreMass_pos G β h q).ne'
  rw [← Finset.sum_mul]
  field_simp





theorem ghsL_fkg_antitone_monotone {π : ConfigSpace V → ℝ}
    (hπ₀ : 0 ≤ π) (hnorm : ∑ q, π q = 1) (hπ : FKGLatticeCondition π)
    {f g : ConfigSpace V → ℝ} (hf : Antitone f) (hg : Monotone g) :
    (∑ q, π q * (f q * g q))
      ≤ (∑ q, π q * f q) * (∑ q, π q * g q) := by
  have hneg : Monotone (fun q => -f q) := fun q r hqr => neg_le_neg (hf hqr)
  have h := fkg_inequality hπ₀ hnorm hπ hneg hg
  have h₁ : (∑ q, π q * -f q) = -(∑ q, π q * f q) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have h₂ : (∑ q, π q * (-f q * g q)) = -(∑ q, π q * (f q * g q)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [h₁, h₂] at h
  linarith




noncomputable def ghsLFibreUU (β h : ℝ) (o x : V) (q : ConfigSpace V) : ℝ :=
  ghsLFibreExpectation G β h (fun a b => uvar a b o * uvar a b x) q


noncomputable def ghsLFibreT (β h : ℝ) (y : V) (q : ConfigSpace V) : ℝ :=
  ghsLFibreExpectation G β h (fun a b => tvar a b y) q


noncomputable def ghsLUExpectation (β : ℝ) (q : ConfigSpace V)
    (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsLUWeight G β q a * F a) /
    ∑ a : ConfigSpace V, ghsLUWeight G β q a


noncomputable def ghsLTExpectation (β h : ℝ) (q : ConfigSpace V)
    (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsLTWeight G β h q a * F a) /
    ∑ a : ConfigSpace V, ghsLTWeight G β h q a

theorem ghsLUWeight_pos (β : ℝ) (q a : ConfigSpace V) :
    0 < ghsLUWeight G β q a := by
  unfold ghsLUWeight
  positivity

theorem ghsLTWeight_pos (β h : ℝ) (q a : ConfigSpace V) :
    0 < ghsLTWeight G β h q a := by
  unfold ghsLTWeight
  positivity


theorem ghsLFibreUU_eq_uExpectation (β h : ℝ) (o x : V) (q : ConfigSpace V) :
    ghsLFibreUU G β h o x q = ghsLUExpectation G β q
      (fun a => uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsLUWeight G β q (ghsLUComplete q su)
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hM : ghsLFibreMass G β h q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreMass ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split]
  have hN : ghsLFibreNumerator G β h
      (fun a b => uvar a b o * uvar a b x) q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsLFibreNumerator ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (isingWeight G β h a * isingWeight G β h (ghsLMate q a)) *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split, ghsL_uvar_mul_split]
    ring
  have hZU : (∑ a : ConfigSpace V, ghsLUWeight G β q a) =
      ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLUWeight_split]
    simp [fU]
  have hNU : (∑ a : ConfigSpace V, ghsLUWeight G β q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x)) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLUWeight_split, ghsL_uvar_mul_split]
    ring
  have hcross := ghsL_split_cross_product (V := V) q fT (fun _ => (1 : ℝ))
    (fun su => fU su * uuObs su) fU
  unfold ghsLFibreUU ghsLFibreExpectation ghsLUExpectation
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  have hu : (∑ a : ConfigSpace V, ghsLUWeight G β q a) ≠ 0 := by
    exact (Finset.sum_pos (fun a _ => ghsLUWeight_pos G β q a) Finset.univ_nonempty).ne'
  field_simp [hm, hu]
  rw [hN, hM, hZU]
  rw [show (∑ x_1, ghsLUWeight G β q x_1 * uvar x_1 (ghsLMate q x_1) o *
      uvar x_1 (ghsLMate q x_1) x) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) by
        simpa [mul_assoc] using hNU]
  simpa [mul_comm] using hcross



theorem ghsLFibreUU_eq_disagreementCorr (β h : ℝ) (o x : V) (hox : o ≠ x)
    (q : ConfigSpace V) :
    ghsLFibreUU G β h o x q =
      ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q) := by
  rw [ghsLFibreUU_eq_uExpectation]
  by_cases ho : o ∈ ghsLAgreeFinset q
  · have hqo : q o = true := (mem_ghsLAgreeFinset q o).mp ho
    unfold ghsLUExpectation ghsvp_disagreementCorr
    rw [if_pos (Or.inl ho)]
    simp_rw [ghsL_uvar_mate, if_pos hqo, zero_mul, mul_zero]
    simp
  · by_cases hx : x ∈ ghsLAgreeFinset q
    · have hqx : q x = true := (mem_ghsLAgreeFinset q x).mp hx
      unfold ghsLUExpectation ghsvp_disagreementCorr
      rw [if_pos (Or.inr hx)]
      simp_rw [ghsL_uvar_mate, if_pos hqx, mul_zero]
      simp
    · have hqo : ¬ q o = true := fun h => ho ((mem_ghsLAgreeFinset q o).mpr h)
      have hqx : ¬ q x = true := fun h => hx ((mem_ghsLAgreeFinset q x).mpr h)
      unfold ghsLUExpectation ghsvp_disagreementCorr ghsvp_vertexCorr Sharpness.expJ
      rw [if_neg (not_or_intro ho hx)]
      apply congrArg₂ (· / ·)
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsLUWeight_eq_wJ]
        simp only [ghsL_uvar_mate, if_neg hqo, if_neg hqx]
        unfold spinProd
        rw [Finset.prod_pair hox]
        ring
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsLUWeight_eq_wJ]


theorem ghsLFibreT_eq_tExpectation (β h : ℝ) (y : V) (q : ConfigSpace V) :
    ghsLFibreT G β h y q = ghsLTExpectation G β h q
      (fun a => tvar a (ghsLMate q a) y) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsLUWeight G β q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  have hM : ghsLFibreMass G β h q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreMass ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split]
  have hN : ghsLFibreNumerator G β h (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreNumerator ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (isingWeight G β h a * isingWeight G β h (ghsLMate q a)) *
      tvar a (ghsLMate q a) y = _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split, ghsL_tvar_split]
    ring
  have hZT : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) =
      ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLTWeight_split]
    simp [fT]
  have hNT : (∑ a : ConfigSpace V, ghsLTWeight G β h q a *
      tvar a (ghsLMate q a) y) = ∑ a : ConfigSpace V,
      (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLTWeight_split, ghsL_tvar_split]
    simp [fT, tObs]
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) fU
  unfold ghsLFibreT ghsLFibreExpectation ghsLTExpectation
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  have ht : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) ≠ 0 := by
    exact (Finset.sum_pos (fun a _ => ghsLTWeight_pos G β h q a) Finset.univ_nonempty).ne'
  field_simp [hm, ht]
  rw [hN, hM, hZT, hNT]
  simpa [mul_comm] using hcross.symm


noncomputable def ghsLOutFieldWeight (β h : ℝ) (q a : ConfigSpace V) : ℝ :=
  Real.exp (2 * β * h * ∑ v ∈ (ghsLAgreeFinset q)ᶜ, spin a v)

theorem ghsLOutFieldWeight_split (β h : ℝ) (q a : ConfigSpace V) :
    ghsLOutFieldWeight β h q a =
      ghsLOutFieldWeight β h q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsLOutFieldWeight
  congr 2
  apply Finset.sum_congr rfl
  intro v hv
  have hq : ¬ q v = true := by
    simpa using (Finset.mem_compl.mp hv)
  unfold spin
  rw [ghsLUComplete_eq_on q a hq]



theorem ghsL_wJ_field_eq_tWeight_mul_out (β h : ℝ) (q a : ConfigSpace V) :
    Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β) (fun _ => 2 * β * h) a =
      ghsLTWeight G β h q a * ghsLOutFieldWeight β h q a := by
  unfold Sharpness.wJ ghsLTWeight ghsLOutFieldWeight
  rw [← Real.exp_add]
  congr 1
  have hsplit : (∑ v : V, spin a v) =
      (∑ v ∈ ghsLAgreeFinset q, spin a v) +
        ∑ v ∈ (ghsLAgreeFinset q)ᶜ, spin a v := by
    calc
      (∑ v : V, spin a v) = ∑ v ∈ ghsLAgreeFinset q ∪ (ghsLAgreeFinset q)ᶜ,
          spin a v := by rw [Finset.union_compl]
      _ = _ := Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro v hvA hvAc
        exact (Finset.mem_compl.mp hvAc) hvA)
  rw [show (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
      (fun _ => 2 * β) e * bond a e) =
      2 * β * ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e by
        rw [Finset.mul_sum]]
  rw [show (∑ x : V, (fun _ => 2 * β * h) x * spin a x) =
      2 * β * h * ∑ x : V, spin a x by rw [Finset.mul_sum]]
  rw [hsplit]
  ring


theorem ghsLFibreT_eq_agreementMag (β h : ℝ) (y : V) (q : ConfigSpace V) :
    ghsLFibreT G β h y q =
      ghsvp_agreementMag G β h y (ghsLAgreeFinset q) := by
  rw [ghsLFibreT_eq_tExpectation]
  by_cases hy : y ∈ ghsLAgreeFinset q
  · have hqy : q y = true := (mem_ghsLAgreeFinset q y).mp hy
    unfold ghsvp_agreementMag ghsvp_vertexCorrField Sharpness.expJ
    rw [if_pos hy]
    let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      ghsLTWeight G β h q (ghsLTComplete q st)
    let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      spin (ghsLTComplete q st) y
    let gO : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
      ghsLOutFieldWeight β h q (ghsLUComplete q su)
    have htvar (a : ConfigSpace V) : tvar a (ghsLMate q a) y = spin a y := by
      rw [ghsL_tvar_mate, if_pos hqy]
    have htlocal (a : ConfigSpace V) : spin a y = tObs (ghsLSplitEquiv q a).1 := by
      unfold tObs spin
      rw [ghsLTComplete_eq_on q a hqy]
    have hbase (a : ConfigSpace V) : ghsLTWeight G β h q a =
        fT (ghsLSplitEquiv q a).1 := by
      rw [ghsLTWeight_split]
    have hout (a : ConfigSpace V) : ghsLOutFieldWeight β h q a =
        gO (ghsLSplitEquiv q a).2 := by
      rw [ghsLOutFieldWeight_split]
    have hcross := ghsL_split_cross_product (V := V) q
      (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) gO
    unfold ghsLTExpectation
    have hzt : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) ≠ 0 :=
      (Finset.sum_pos (fun a _ => ghsLTWeight_pos G β h q a) Finset.univ_nonempty).ne'
    have hza : Sharpness.ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β) (fun _ => 2 * β * h) ≠ 0 :=
      (Sharpness.ZJ_pos _ _ _).ne'
    field_simp [hzt, hza]
    have hL1 : (∑ a : ConfigSpace V,
        ghsLTWeight G β h q a * tvar a (ghsLMate q a) y) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase, htvar, htlocal]
      ring
    have hL0 : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) =
        ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase]
      ring
    have hR1 : (∑ a : ConfigSpace V, spinProd {y} a *
        Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
          (fun _ => 2 * β) (fun _ => 2 * β * h) a) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
            gO (ghsLSplitEquiv q a).2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsL_wJ_field_eq_tWeight_mul_out, hbase, hout]
      simp only [spinProd, Finset.prod_singleton]
      rw [htlocal]
      ring
    have hR0 : Sharpness.ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β) (fun _ => 2 * β * h) =
        ∑ a : ConfigSpace V,
          fT (ghsLSplitEquiv q a).1 * gO (ghsLSplitEquiv q a).2 := by
      unfold Sharpness.ZJ
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsL_wJ_field_eq_tWeight_mul_out, hbase, hout]
    rw [hL1, hL0, hR1, hR0]
    simpa [mul_comm] using hcross
  · have hqy : ¬ q y = true := fun h => hy ((mem_ghsLAgreeFinset q y).mpr h)
    unfold ghsvp_agreementMag ghsLTExpectation
    rw [if_neg hy]
    simp_rw [ghsL_tvar_mate, if_neg hqy, mul_zero]
    simp



def GHSLebowitzFibreFactorization (β h : ℝ) (o x y : V) : Prop :=
  ∀ q : ConfigSpace V,
    ghsLFibreExpectation G β h
        (fun a b => uvar a b o * uvar a b x * tvar a b y) q
      = ghsLFibreUU G β h o x q * ghsLFibreT G β h y q


theorem ghsL_fibreFactorization (β h : ℝ) (o x y : V) :
    GHSLebowitzFibreFactorization G β h o x y := by
  intro q
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsLUWeight G β q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hweight (a : ConfigSpace V) : ghsLFibreWeight G β h q a =
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreWeight
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split]
  have htobs (a : ConfigSpace V) : tvar a (ghsLMate q a) y =
      tObs (ghsLSplitEquiv q a).1 := by
    exact ghsL_tvar_split q a y
  have huuobs (a : ConfigSpace V) :
      uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x =
        uuObs (ghsLSplitEquiv q a).2 := by
    exact ghsL_uvar_mul_split q a o x
  have hUUT : ghsLFibreNumerator G β h
      (fun a b => uvar a b o * uvar a b x * tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsLFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsLFibreWeight G β h q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x *
        tvar a (ghsLMate q a) y) = _
    rw [hweight, htobs, huuobs]
    ring
  have hMass : ghsLFibreMass G β h q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreMass
    apply Finset.sum_congr rfl
    intro a _
    exact hweight a
  have hT : ghsLFibreNumerator G β h (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsLFibreWeight G β h q a * tvar a (ghsLMate q a) y = _
    rw [hweight, htobs]
    ring
  have hUU : ghsLFibreNumerator G β h
      (fun a b => uvar a b o * uvar a b x) q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsLFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsLFibreWeight G β h q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [hweight, huuobs]
    ring
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT
    (fun su => fU su * uuObs su) fU
  unfold ghsLFibreUU ghsLFibreT ghsLFibreExpectation
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  field_simp [hm]
  rw [hUUT, hMass, hUU, hT]
  simpa [mul_comm] using hcross


theorem ghsL_duplicate_cov_nonpos_of_fibres (β h : ℝ) (o x y : V)
    (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
    (hfactor : GHSLebowitzFibreFactorization G β h o x y)
    (huu : Antitone (ghsLFibreUU G β h o x))
    (ht : Monotone (ghsLFibreT G β h y)) :
    isingExp2 G β h (fun a b => uvar a b o * uvar a b x * tvar a b y)
      ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x)
          * isingExp2 G β h (fun a b => tvar a b y) := by
  unfold GHSLebowitzFibreFactorization at hfactor
  have hfkg := ghsL_fkg_antitone_monotone (V := V)
    (ghsLAgreementProb_nonneg G β h) (ghsLAgreementProb_sum_eq_one G β h)
    hlattice huu ht
  rw [ghsL_isIngExp2_fibre, ghsL_isIngExp2_fibre, ghsL_isIngExp2_fibre]
  simp_rw [hfactor]
  exact hfkg



theorem ghsLFibreUU_antitone_of_eq (β h : ℝ) (hβ : 0 ≤ β) (o x : V)
    (hdict : ∀ q : ConfigSpace V,
      ghsLFibreUU G β h o x q =
        ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q)) :
    Antitone (ghsLFibreUU G β h o x) := by
  intro q r hqr
  rw [hdict, hdict]
  exact ghsvp_disagreementCorr_antitone G β hβ o x
    (ghsLAgreeFinset_monotone hqr)



theorem ghsLFibreT_monotone_of_eq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (y : V)
    (hdict : ∀ q : ConfigSpace V,
      ghsLFibreT G β h y q = ghsvp_agreementMag G β h y (ghsLAgreeFinset q)) :
    Monotone (ghsLFibreT G β h y) := by
  intro q r hqr
  rw [hdict, hdict]
  exact ghsvp_agreementMag_monotone G β h hβ hh y
    (ghsLAgreeFinset_monotone hqr)


theorem ghsL_pair_of_vertexPartition (β h c : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hc : 0 < c) (o x y : V)
    (hmass : ∀ q : ConfigSpace V,
      ghsvp_subsetMass G β h (ghsLAgreeFinset q) = c * ghsLFibreMass G β h q)
    (huu : ∀ q : ConfigSpace V,
      ghsLFibreUU G β h o x q =
        ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q))
    (ht : ∀ q : ConfigSpace V,
      ghsLFibreT G β h y q = ghsvp_agreementMag G β h y (ghsLAgreeFinset q)) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
  apply ghsL_pair_of_duplicate_cov_nonpos G β h o x y
  exact ghsL_duplicate_cov_nonpos_of_fibres G β h o x y
    (ghsLAgreementProb_fkg_of_subsetMass_scale G β h c hc hmass hβ hh)
    (ghsL_fibreFactorization G β h o x y)
    (ghsLFibreUU_antitone_of_eq G β h hβ o x huu)
    (ghsLFibreT_monotone_of_eq G β h hβ hh y ht)


theorem ghsLAgreementProb_fkg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    FKGLatticeCondition (ghsLAgreementProb G β h) := by
  apply ghsLAgreementProb_fkg_of_subsetMass_scale G β h
    (4 * Fintype.card (ConfigSpace V))
  · have hc : 0 < (Fintype.card (ConfigSpace V) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
    positivity
  · exact ghsvp_subsetMass_eq_card_mul_fibreMass G β h
  · exact hβ
  · exact hh


theorem ghsL_pair (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o x y : V) (hox : o ≠ x) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
  apply ghsL_pair_of_vertexPartition G β h (4 * Fintype.card (ConfigSpace V)) hβ hh
  · have hc : 0 < (Fintype.card (ConfigSpace V) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
    positivity
  · exact ghsvp_subsetMass_eq_card_mul_fibreMass G β h
  · intro q
    exact ghsLFibreUU_eq_disagreementCorr G β h o x hox q
  · intro q
    exact ghsLFibreT_eq_agreementMag G β h y q


theorem ghsL_threePoint (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    GHSThreePointSym G β h o := by
  intro e he
  by_cases hoe : o ∈ e
  · exact ghsThreePoint_of_mem G β h hβ hh o e he hoe
  · induction e with
    | h x y =>
        have hox : o ≠ x := by
          intro h
          subst x
          exact hoe (by simp)
        exact ghsL_pair G β h hβ hh o x y hox


theorem ghsL_pair_of_fibres (β h : ℝ) (o x y : V)
    (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
    (hfactor : GHSLebowitzFibreFactorization G β h o x y)
    (huu : Antitone (ghsLFibreUU G β h o x))
    (ht : Monotone (ghsLFibreT G β h y)) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) :=
  ghsL_pair_of_duplicate_cov_nonpos G β h o x y
    (ghsL_duplicate_cov_nonpos_of_fibres G β h o x y hlattice hfactor huu ht)


theorem ghsL_threePoint_of_fibres (β h : ℝ) (o : V)
    (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
    (hfactor : ∀ x y, GHSLebowitzFibreFactorization G β h o x y)
    (huu : ∀ x, Antitone (ghsLFibreUU G β h o x))
    (ht : ∀ y, Monotone (ghsLFibreT G β h y)) :
    GHSThreePointSym G β h o := by
  intro e _
  induction e with
  | h x y => exact ghsL_pair_of_fibres G β h o x y hlattice (hfactor x y) (huu x) (ht y)

end Ising

end StatMech
