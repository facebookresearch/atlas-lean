/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Ising.GHSLebowitz
import Code.Ising.GHSInhomVertexPartition
import Code.Ising.FiniteVolumeRelabel
import Code.Ising.FiniteVolumeSum
import Code.Sharpness.GHSConcavity

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000

namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



section Relabel

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

theorem ghsi_fieldSum_relabel (sigma : V ≃ W) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) (omega : ConfigSpace W) :
    (∑ x : V, hfV x * spin (isingCfgEquiv sigma omega) x) =
      ∑ y : W, hfW y * spin omega y := by
  have hcomp : (fun x : V => hfV x * spin (isingCfgEquiv sigma omega) x) =
      fun x => hfW (sigma x) * spin omega (sigma x) := by
    funext x
    rw [hhf]
    rfl
  rw [hcomp]
  exact Equiv.sum_comp sigma (fun y : W => hfW y * spin omega y)

theorem ghsi_wJ_const_relabel (sigma : V ≃ W)
    (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) (omega : ConfigSpace W) :
    wJ G.edgeFinset (fun _ => beta) hfV (isingCfgEquiv sigma omega) =
      wJ H.edgeFinset (fun _ => beta) hfW omega := by
  unfold wJ
  congr 1
  rw [show (∑ e ∈ G.edgeFinset, beta * bond (isingCfgEquiv sigma omega) e) =
      beta * ∑ e ∈ G.edgeFinset, bond (isingCfgEquiv sigma omega) e by
    rw [Finset.mul_sum]]
  rw [show (∑ e ∈ H.edgeFinset, beta * bond omega e) =
      beta * ∑ e ∈ H.edgeFinset, bond omega e by rw [Finset.mul_sum]]
  rw [sum_bond_isingCfgEquiv G H sigma hsigma omega,
    ghsi_fieldSum_relabel sigma hfV hfW hhf omega]

theorem ghsi_ZJ_const_relabel (sigma : V ≃ W)
    (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) :
    ZJ G.edgeFinset (fun _ => beta) hfV =
      ZJ H.edgeFinset (fun _ => beta) hfW := by
  unfold ZJ
  rw [← Equiv.sum_comp (isingCfgEquiv sigma)
    (fun omega => wJ G.edgeFinset (fun _ => beta) hfV omega)]
  exact Finset.sum_congr rfl
    (fun omega _ => ghsi_wJ_const_relabel G H sigma hsigma beta hfV hfW hhf omega)

theorem ghsi_expJ_spin_const_relabel (sigma : V ≃ W)
    (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) (x : V) :
    expJ G.edgeFinset (fun _ => beta) hfV (fun omega => spin omega x) =
      expJ H.edgeFinset (fun _ => beta) hfW (fun omega => spin omega (sigma x)) := by
  unfold expJ
  rw [ghsi_ZJ_const_relabel G H sigma hsigma beta hfV hfW hhf]
  rw [← Equiv.sum_comp (isingCfgEquiv sigma)
    (fun omega => spin omega x * wJ G.edgeFinset (fun _ => beta) hfV omega)]
  apply congrArg (fun z => z / ZJ H.edgeFinset (fun _ => beta) hfW)
  apply Finset.sum_congr rfl
  intro omega _
  rw [spin_isingCfgEquiv,
    ghsi_wJ_const_relabel G H sigma hsigma beta hfV hfW hhf]

end Relabel



section Sum

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

theorem ghsi_wJ_sum (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (s : ConfigSpace V) (t : ConfigSpace W) :
    wJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW)
        (isingSumConfigEquiv.symm (s, t)) =
      wJ G.edgeFinset (fun _ => beta) hfV s *
        wJ H.edgeFinset (fun _ => beta) hfW t := by
  unfold wJ
  rw [← Real.exp_add]
  congr 1
  rw [show (∑ e ∈ (G ⊕g H).edgeFinset,
      beta * bond (isingSumConfigEquiv.symm (s, t)) e) =
      beta * ∑ e ∈ (G ⊕g H).edgeFinset,
        bond (isingSumConfigEquiv.symm (s, t)) e by rw [Finset.mul_sum]]
  rw [sum_bond_isingSumConfigEquiv_symm G H s t]
  rw [show (∑ e ∈ G.edgeFinset, beta * bond s e) =
      beta * ∑ e ∈ G.edgeFinset, bond s e by rw [Finset.mul_sum]]
  rw [show (∑ e ∈ H.edgeFinset, beta * bond t e) =
      beta * ∑ e ∈ H.edgeFinset, bond t e by rw [Finset.mul_sum]]
  rw [Fintype.sum_sum_type]
  simp only [spin_isingSumConfigEquiv_symm_inl,
    spin_isingSumConfigEquiv_symm_inr, Sum.elim_inl, Sum.elim_inr]
  ring

theorem ghsi_ZJ_sum (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ) :
    ZJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW) =
      ZJ G.edgeFinset (fun _ => beta) hfV *
        ZJ H.edgeFinset (fun _ => beta) hfW := by
  unfold ZJ
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [ghsi_wJ_sum G H beta hfV hfW]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem ghsi_expJ_spin_sum_inl (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (x : V) :
    expJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW)
        (fun s => spin s (Sum.inl x)) =
      expJ G.edgeFinset (fun _ => beta) hfV (fun s => spin s x) := by
  unfold expJ
  rw [ghsi_ZJ_sum G H]
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [ghsi_wJ_sum G H beta hfV hfW,
    spin_isingSumConfigEquiv_symm_inl]
  have hW : ZJ H.edgeFinset (fun _ => beta) hfW ≠ 0 := (ZJ_pos _ _ _).ne'
  have hnum : (∑ s : ConfigSpace V, ∑ t : ConfigSpace W,
      spin s x * (wJ G.edgeFinset (fun _ => beta) hfV s *
        wJ H.edgeFinset (fun _ => beta) hfW t)) =
      (∑ s : ConfigSpace V, spin s x * wJ G.edgeFinset (fun _ => beta) hfV s) *
        ZJ H.edgeFinset (fun _ => beta) hfW := by
    unfold ZJ
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hnum]
  field_simp

end Sum


noncomputable def ghsiExp2 (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
      wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf b * F a b) /
    (ZJ G.edgeFinset K hf) ^ 2


theorem ghsiExp2_factor (K : Sym2 V → ℝ) (hf : V → ℝ)
    (f g : ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun a b => f a * g b) =
      expJ G.edgeFinset K hf f * expJ G.edgeFinset K hf g := by
  unfold ghsiExp2 expJ
  have hZ : ZJ G.edgeFinset K hf ≠ 0 := (ZJ_pos _ _ _).ne'
  field_simp [hZ]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring


noncomputable def ghsiTWeight (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : ℝ :=
  Real.exp
    ((∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
        (2 * K e) * bond a e) +
      ∑ v ∈ ghsLAgreeFinset q, (2 * hf v) * spin a v)


noncomputable def ghsiUWeight (K : Sym2 V → ℝ) (q a : ConfigSpace V) : ℝ :=
  Real.exp
    (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ,
      (2 * K e) * bond a e)



theorem ghsi_bondSum_split (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, K e * bond a e) +
        ∑ e ∈ G.edgeFinset, K e * bond (ghsLMate q a) e =
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
          (2 * K e) * bond a e) +
        ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ,
          (2 * K e) * bond a e := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, ghsL_bond_add_mate]
  unfold ghsvp_vertexEdges
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hA : edgeInside (ghsLAgreeFinset q) e
  · have hAc : ¬ edgeInside (ghsLAgreeFinset q)ᶜ e := by
      induction e with
      | h x y => simp_all [edgeInside]
    simp [hA, hAc]
    ring
  · by_cases hAc : edgeInside (ghsLAgreeFinset q)ᶜ e
    · simp [hA, hAc]
      ring
    · simp [hA, hAc]


theorem ghsi_fieldSum_split (hf : V → ℝ) (q a : ConfigSpace V) :
    (∑ v : V, hf v * spin a v) +
        ∑ v : V, hf v * spin (ghsLMate q a) v =
      ∑ v ∈ ghsLAgreeFinset q, (2 * hf v) * spin a v := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, ghsL_spin_add_mate]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  unfold ghsLAgreeFinset
  apply Finset.sum_congr rfl
  intro v _
  ring


theorem ghsi_duplicateWeight_eq_tWeight_mul_uWeight
    (K : Sym2 V → ℝ) (hf : V → ℝ) (q a : ConfigSpace V) :
    wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a) =
      ghsiTWeight G K hf q a * ghsiUWeight G K q a := by
  unfold wJ ghsiTWeight ghsiUWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [show
      (∑ e ∈ G.edgeFinset, K e * bond a e) + (∑ x, hf x * spin a x) +
          ((∑ e ∈ G.edgeFinset, K e * bond (ghsLMate q a) e) +
            ∑ x, hf x * spin (ghsLMate q a) x) =
        ((∑ e ∈ G.edgeFinset, K e * bond a e) +
          ∑ e ∈ G.edgeFinset, K e * bond (ghsLMate q a) e) +
        ((∑ x, hf x * spin a x) +
          ∑ x, hf x * spin (ghsLMate q a) x) by ring]
  rw [ghsi_bondSum_split G K q a, ghsi_fieldSum_split hf q a]
  ring


theorem ghsiTWeight_split (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) :
    ghsiTWeight G K hf q a =
      ghsiTWeight G K hf q (ghsLTComplete q (ghsLSplitEquiv q a).1) := by
  unfold ghsiTWeight
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    induction e with
    | h x y =>
      have hx : q x = true := mem_ghsLAgreeFinset q x |>.mp (hi x (by simp))
      have hy : q y = true := mem_ghsLAgreeFinset q y |>.mp (hi y (by simp))
      simp only [bond_mk]
      congr 2 <;> unfold spin
      · rw [ghsLTComplete_eq_on q a hx]
      · rw [ghsLTComplete_eq_on q a hy]
  · apply Finset.sum_congr rfl
    intro v hv
    have hq := (mem_ghsLAgreeFinset q v).mp hv
    congr 1
    unfold spin
    rw [ghsLTComplete_eq_on q a hq]


theorem ghsiUWeight_split (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    ghsiUWeight G K q a =
      ghsiUWeight G K q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsiUWeight
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hi := (Finset.mem_filter.mp he).2
  induction e with
  | h x y =>
    have hx : ¬ q x = true := by
      simpa using (Finset.mem_compl.mp (hi x (by simp)))
    have hy : ¬ q y = true := by
      simpa using (Finset.mem_compl.mp (hi y (by simp)))
    simp only [bond_mk]
    congr 2 <;> unfold spin
    · rw [ghsLUComplete_eq_on q a hx]
    · rw [ghsLUComplete_eq_on q a hy]


theorem ghsiTWeight_eq_wJ_restricted (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) :
    ghsiTWeight G K hf q a =
      wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e)
        (fun x => if x ∈ ghsLAgreeFinset q then 2 * hf x else 0) a := by
  unfold ghsiTWeight wJ
  congr 1
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_univ_mem]


theorem ghsiUWeight_eq_wJ (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    ghsiUWeight G K q a =
      wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
        (fun e => 2 * K e) (fun _ => 0) a := by
  unfold ghsiUWeight wJ
  simp


noncomputable def ghsiFibreWeight (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : ℝ :=
  wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)

noncomputable def ghsiFibreMass (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V, ghsiFibreWeight G K hf q a

noncomputable def ghsiFibreNumerator (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V, ghsiFibreWeight G K hf q a * F a (ghsLMate q a)

noncomputable def ghsiFibreExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ghsiFibreNumerator G K hf F q / ghsiFibreMass G K hf q

noncomputable def ghsiAgreementProb (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) : ℝ :=
  ghsiFibreMass G K hf q / (ZJ G.edgeFinset K hf) ^ 2

theorem ghsiFibreWeight_pos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : 0 < ghsiFibreWeight G K hf q a :=
  mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _)

theorem ghsiFibreMass_pos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) : 0 < ghsiFibreMass G K hf q := by
  unfold ghsiFibreMass
  exact Finset.sum_pos (fun a _ => ghsiFibreWeight_pos G K hf q a)
    Finset.univ_nonempty

theorem ghsiAgreementProb_nonneg (K : Sym2 V → ℝ) (hf : V → ℝ) :
    0 ≤ ghsiAgreementProb G K hf := fun q =>
  div_nonneg (ghsiFibreMass_pos G K hf q).le (sq_nonneg _)

theorem ghsiAgreementProb_sum_eq_one (K : Sym2 V → ℝ) (hf : V → ℝ) :
    ∑ q : ConfigSpace V, ghsiAgreementProb G K hf q = 1 := by
  have hreindex := ghsL_sum_pair_xnor (V := V)
    (fun a b => wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf b)
  have hmass : (∑ q : ConfigSpace V, ghsiFibreMass G K hf q) =
      (ZJ G.edgeFinset K hf) ^ 2 := by
    unfold ghsiFibreMass ghsiFibreWeight ZJ
    rw [← hreindex, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  unfold ghsiAgreementProb
  rw [← Finset.sum_div, hmass]
  exact div_self (pow_ne_zero 2 (ZJ_pos _ _ _).ne')


theorem ghsiAgreementProb_fkg (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x) :
    FKGLatticeCondition (ghsiAgreementProb G K hf) := by
  intro q r
  have hsub := ghsiSubsetMass_logSupermodular G K hf hK hhf
    (ghsLAgreeFinset q) (ghsLAgreeFinset r)
  rw [← ghsLAgreeFinset_sup, ← ghsLAgreeFinset_inf] at hsub
  have hscale : ∀ q : ConfigSpace V,
      ghsiSubsetMass G K hf (ghsLAgreeFinset q) =
        (4 * Fintype.card (ConfigSpace V)) * ghsiFibreMass G K hf q := by
    intro q
    let T := (v : {v : V // q v = true}) → Bool
    let U := (v : {v : V // ¬ q v = true}) → Bool
    let fT : T → ℝ := fun st => ghsiTWeight G K hf q (ghsLTComplete q st)
    let fU : U → ℝ := fun su => ghsiUWeight G K q (ghsLUComplete q su)
    have hmass : ghsiFibreMass G K hf q =
        (∑ st : T, fT st) * ∑ su : U, fU su := by
      unfold ghsiFibreMass ghsiFibreWeight
      calc
        (∑ a : ConfigSpace V,
            wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) =
            ∑ a : ConfigSpace V,
              fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
            ghsiTWeight_split, ghsiUWeight_split]
        _ = _ := ghsL_split_sum_product q fT fU
    have ht : ghsiTZ G K hf (ghsLAgreeFinset q) =
        (∑ st : T, fT st) * Fintype.card U := by
      unfold ghsiTZ ZJ
      have hs := ghsL_split_sum_product (V := V) q fT (fun _ : U => (1 : ℝ))
      rw [show (∑ a : ConfigSpace V,
          wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
            (fun e => 2 * K e)
            (fun x => if x ∈ ghsLAgreeFinset q then 2 * hf x else 0) a) =
          ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) by
        apply Finset.sum_congr rfl
        intro a _
        rw [← ghsiTWeight_eq_wJ_restricted,
          ghsiTWeight_split]
        simp [fT]]
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
    have hu : ghsiUZ G K (ghsLAgreeFinset q)ᶜ =
        Fintype.card T * ∑ su : U, fU su := by
      unfold ghsiUZ ZJ
      have hs := ghsL_split_sum_product (V := V) q (fun _ : T => (1 : ℝ)) fU
      rw [show (∑ a : ConfigSpace V,
          wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
            (fun e => 2 * K e) (fun _ => 0) a) =
          ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 by
        apply Finset.sum_congr rfl
        intro a _
        rw [← ghsiUWeight_eq_wJ,
          ghsiUWeight_split]
        simp [fU]]
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
    have hcard : Fintype.card (ConfigSpace V) = Fintype.card T * Fintype.card U := by
      rw [Fintype.card_congr (ghsLSplitEquiv q), Fintype.card_prod]
    rw [ghsiSubsetMass_eq_four_mul_tZ_uZ, ht, hu, hmass, hcard]
    norm_num [Nat.cast_mul]
    ring
  simp_rw [hscale] at hsub
  have hc : 0 < (4 * Fintype.card (ConfigSpace V) : ℝ) := by
    have := Fintype.card_pos_iff.mpr (show Nonempty (ConfigSpace V) from ⟨fun _ => false⟩)
    positivity
  have hfibre : ghsiFibreMass G K hf q * ghsiFibreMass G K hf r ≤
      ghsiFibreMass G K hf (q ⊔ r) * ghsiFibreMass G K hf (q ⊓ r) := by
    nlinarith [hsub, sq_pos_of_pos hc]
  unfold ghsiAgreementProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right hfibre (mul_nonneg (sq_nonneg _) (sq_nonneg _))



noncomputable def ghsiFibreUU (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x : V) (q : ConfigSpace V) : ℝ :=
  ghsiFibreExpectation G K hf (fun a b => uvar a b o * uvar a b x) q

noncomputable def ghsiFibreT (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (q : ConfigSpace V) : ℝ :=
  ghsiFibreExpectation G K hf (fun a b => tvar a b y) q

noncomputable def ghsiUExpectation (K : Sym2 V → ℝ) (q : ConfigSpace V)
    (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsiUWeight G K q a * F a) /
    ∑ a : ConfigSpace V, ghsiUWeight G K q a

noncomputable def ghsiTExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsiTWeight G K hf q a * F a) /
    ∑ a : ConfigSpace V, ghsiTWeight G K hf q a

theorem ghsiUWeight_pos (K : Sym2 V → ℝ) (q a : ConfigSpace V) :
    0 < ghsiUWeight G K q a := by unfold ghsiUWeight; positivity

theorem ghsiTWeight_pos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : 0 < ghsiTWeight G K hf q a := by
  unfold ghsiTWeight
  positivity

theorem ghsiFibreUU_eq_uExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x : V) (q : ConfigSpace V) :
    ghsiFibreUU G K hf o x q = ghsiUExpectation G K q
      (fun a => uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsiTWeight G K hf q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsiUWeight G K q (ghsLUComplete q su)
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hM : ghsiFibreMass G K hf q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreMass ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split]
  have hN : ghsiFibreNumerator G K hf
      (fun a b => uvar a b o * uvar a b x) q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsiFibreNumerator ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split, ghsL_uvar_mul_split]
    ring
  have hZU : (∑ a : ConfigSpace V, ghsiUWeight G K q a) =
      ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiUWeight_split]
    simp [fU]
  have hNU : (∑ a : ConfigSpace V, ghsiUWeight G K q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x)) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiUWeight_split, ghsL_uvar_mul_split]
    ring
  have hcross := ghsL_split_cross_product (V := V) q fT (fun _ => (1 : ℝ))
    (fun su => fU su * uuObs su) fU
  unfold ghsiFibreUU ghsiFibreExpectation ghsiUExpectation
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  have hu : (∑ a : ConfigSpace V, ghsiUWeight G K q a) ≠ 0 :=
    (Finset.sum_pos (fun a _ => ghsiUWeight_pos G K q a) Finset.univ_nonempty).ne'
  field_simp [hm, hu]
  rw [hN, hM, hZU]
  rw [show (∑ a, ghsiUWeight G K q a * uvar a (ghsLMate q a) o *
      uvar a (ghsLMate q a) x) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) by
      simpa [mul_assoc] using hNU]
  simpa [mul_comm] using hcross

theorem ghsiFibreT_eq_tExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (q : ConfigSpace V) :
    ghsiFibreT G K hf y q = ghsiTExpectation G K hf q
      (fun a => tvar a (ghsLMate q a) y) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsiTWeight G K hf q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsiUWeight G K q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  have hM : ghsiFibreMass G K hf q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreMass ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split]
  have hN : ghsiFibreNumerator G K hf (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreNumerator ghsiFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) *
      tvar a (ghsLMate q a) y = _
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split, ghsL_tvar_split]
    ring
  have hZT : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) =
      ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiTWeight_split]
    simp [fT]
  have hNT : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a *
      tvar a (ghsLMate q a) y) = ∑ a : ConfigSpace V,
      (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsiTWeight_split, ghsL_tvar_split]
    simp [fT, tObs]
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) fU
  unfold ghsiFibreT ghsiFibreExpectation ghsiTExpectation
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  have ht : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) ≠ 0 :=
    (Finset.sum_pos (fun a _ => ghsiTWeight_pos G K hf q a)
      Finset.univ_nonempty).ne'
  field_simp [hm, ht]
  rw [hN, hM, hZT, hNT]
  simpa [mul_comm] using hcross.symm


noncomputable def ghsiDisagreementCorr (K : Sym2 V → ℝ)
    (o x : V) (A : Finset V) : ℝ :=
  if o ∈ A ∨ x ∈ A then 0
  else ghsvp_vertexCorr G.edgeFinset (fun e => 2 * K e) Aᶜ {o, x}


noncomputable def ghsiAgreementMag (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (A : Finset V) : ℝ :=
  if y ∈ A then
    ghsvp_vertexCorrField G.edgeFinset (fun e => 2 * K e) (fun x => 2 * hf x) A {y}
  else 0

theorem ghsiDisagreementCorr_antitone (K : Sym2 V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (o x : V) :
    Antitone (ghsiDisagreementCorr G K o x) := by
  intro A B hAB
  by_cases hA : o ∈ A ∨ x ∈ A
  · have hB : o ∈ B ∨ x ∈ B := hA.elim (fun ho => Or.inl (hAB ho))
      (fun hx => Or.inr (hAB hx))
    simp [ghsiDisagreementCorr, hA, hB]
  · by_cases hB : o ∈ B ∨ x ∈ B
    · simp only [ghsiDisagreementCorr, if_pos hB, if_neg hA]
      apply ghsvp_vertexCorr_nonneg
      intro e
      exact mul_nonneg (by norm_num) (hK e)
    · simp only [ghsiDisagreementCorr, if_neg hA, if_neg hB]
      apply ghsvp_vertexCorr_mono
      · intro e
        exact mul_nonneg (by norm_num) (hK e)
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · intro v hv
        simp only [Finset.mem_compl] at hv ⊢
        exact fun hvA => hv (hAB hvA)

theorem ghsiAgreementMag_monotone (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x) (y : V) :
    Monotone (ghsiAgreementMag G K hf y) := by
  intro A B hAB
  by_cases hB : y ∈ B
  · by_cases hA : y ∈ A
    · simp only [ghsiAgreementMag, if_pos hA, if_pos hB]
      apply ghsvp_vertexCorrField_mono
      · intro e
        exact mul_nonneg (by norm_num) (hK e)
      · intro v
        exact mul_nonneg (by norm_num) (hhf v)
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · exact hAB
    · simp only [ghsiAgreementMag, if_neg hA, if_pos hB]
      apply ghsvp_vertexCorrField_nonneg
      · intro e
        exact mul_nonneg (by norm_num) (hK e)
      · intro v
        exact mul_nonneg (by norm_num) (hhf v)
  · have hA : y ∉ A := fun hy => hB (hAB hy)
    simp [ghsiAgreementMag, hA, hB]

theorem ghsiFibreUU_eq_disagreementCorr (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x : V) (hox : o ≠ x) (q : ConfigSpace V) :
    ghsiFibreUU G K hf o x q =
      ghsiDisagreementCorr G K o x (ghsLAgreeFinset q) := by
  rw [ghsiFibreUU_eq_uExpectation]
  by_cases ho : o ∈ ghsLAgreeFinset q
  · have hqo : q o = true := (mem_ghsLAgreeFinset q o).mp ho
    unfold ghsiUExpectation ghsiDisagreementCorr
    rw [if_pos (Or.inl ho)]
    simp_rw [ghsL_uvar_mate, if_pos hqo, zero_mul, mul_zero]
    simp
  · by_cases hx : x ∈ ghsLAgreeFinset q
    · have hqx : q x = true := (mem_ghsLAgreeFinset q x).mp hx
      unfold ghsiUExpectation ghsiDisagreementCorr
      rw [if_pos (Or.inr hx)]
      simp_rw [ghsL_uvar_mate, if_pos hqx, mul_zero]
      simp
    · have hqo : ¬ q o = true := fun h => ho ((mem_ghsLAgreeFinset q o).mpr h)
      have hqx : ¬ q x = true := fun h => hx ((mem_ghsLAgreeFinset q x).mpr h)
      unfold ghsiUExpectation ghsiDisagreementCorr ghsvp_vertexCorr expJ
      rw [if_neg (not_or_intro ho hx)]
      apply congrArg₂ (· / ·)
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsiUWeight_eq_wJ]
        simp only [ghsL_uvar_mate, if_neg hqo, if_neg hqx]
        unfold spinProd
        rw [Finset.prod_pair hox]
        ring
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsiUWeight_eq_wJ]


noncomputable def ghsiOutFieldWeight (hf : V → ℝ)
    (q a : ConfigSpace V) : ℝ :=
  Real.exp (∑ v ∈ (ghsLAgreeFinset q)ᶜ, (2 * hf v) * spin a v)

theorem ghsiOutFieldWeight_split (hf : V → ℝ) (q a : ConfigSpace V) :
    ghsiOutFieldWeight hf q a =
      ghsiOutFieldWeight hf q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsiOutFieldWeight
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  have hq : ¬ q v = true := by simpa using (Finset.mem_compl.mp hv)
  congr 1
  unfold spin
  rw [ghsLUComplete_eq_on q a hq]

theorem ghsi_wJ_field_eq_tWeight_mul_out (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) :
    wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e) (fun x => 2 * hf x) a =
      ghsiTWeight G K hf q a * ghsiOutFieldWeight hf q a := by
  unfold wJ ghsiTWeight ghsiOutFieldWeight
  rw [← Real.exp_add]
  congr 1
  have hsplit : (∑ v : V, (2 * hf v) * spin a v) =
      (∑ v ∈ ghsLAgreeFinset q, (2 * hf v) * spin a v) +
        ∑ v ∈ (ghsLAgreeFinset q)ᶜ, (2 * hf v) * spin a v := by
    calc
      (∑ v : V, (2 * hf v) * spin a v) =
          ∑ v ∈ ghsLAgreeFinset q ∪ (ghsLAgreeFinset q)ᶜ,
            (2 * hf v) * spin a v := by rw [Finset.union_compl]
      _ = _ := Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro v hvA hvAc
        exact (Finset.mem_compl.mp hvAc) hvA)
  rw [hsplit]
  ring

theorem ghsiFibreT_eq_agreementMag (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (q : ConfigSpace V) :
    ghsiFibreT G K hf y q =
      ghsiAgreementMag G K hf y (ghsLAgreeFinset q) := by
  rw [ghsiFibreT_eq_tExpectation]
  by_cases hy : y ∈ ghsLAgreeFinset q
  · have hqy : q y = true := (mem_ghsLAgreeFinset q y).mp hy
    unfold ghsiAgreementMag ghsvp_vertexCorrField expJ
    rw [if_pos hy]
    let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      ghsiTWeight G K hf q (ghsLTComplete q st)
    let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      spin (ghsLTComplete q st) y
    let gO : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
      ghsiOutFieldWeight hf q (ghsLUComplete q su)
    have htvar (a : ConfigSpace V) : tvar a (ghsLMate q a) y = spin a y := by
      rw [ghsL_tvar_mate, if_pos hqy]
    have htlocal (a : ConfigSpace V) : spin a y = tObs (ghsLSplitEquiv q a).1 := by
      unfold tObs spin
      rw [ghsLTComplete_eq_on q a hqy]
    have hbase (a : ConfigSpace V) : ghsiTWeight G K hf q a =
        fT (ghsLSplitEquiv q a).1 := by rw [ghsiTWeight_split]
    have hout (a : ConfigSpace V) : ghsiOutFieldWeight hf q a =
        gO (ghsLSplitEquiv q a).2 := by rw [ghsiOutFieldWeight_split]
    have hcross := ghsL_split_cross_product (V := V) q
      (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) gO
    unfold ghsiTExpectation
    have hzt : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) ≠ 0 :=
      (Finset.sum_pos (fun a _ => ghsiTWeight_pos G K hf q a)
        Finset.univ_nonempty).ne'
    have hza : ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e) (fun x => 2 * hf x) ≠ 0 := (ZJ_pos _ _ _).ne'
    field_simp [hzt, hza]
    have hL1 : (∑ a : ConfigSpace V,
        ghsiTWeight G K hf q a * tvar a (ghsLMate q a) y) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase, htvar, htlocal]
      ring
    have hL0 : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) =
        ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase]
      ring
    have hR1 : (∑ a : ConfigSpace V, spinProd {y} a *
        wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
          (fun e => 2 * K e) (fun x => 2 * hf x) a) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
            gO (ghsLSplitEquiv q a).2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsi_wJ_field_eq_tWeight_mul_out, hbase, hout]
      simp only [spinProd, Finset.prod_singleton]
      rw [htlocal]
      ring
    have hR0 : ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e) (fun x => 2 * hf x) =
        ∑ a : ConfigSpace V,
          fT (ghsLSplitEquiv q a).1 * gO (ghsLSplitEquiv q a).2 := by
      unfold ZJ
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsi_wJ_field_eq_tWeight_mul_out, hbase, hout]
    rw [hL1, hL0, hR1, hR0]
    simpa [mul_comm] using hcross
  · have hqy : ¬ q y = true := fun h => hy ((mem_ghsLAgreeFinset q y).mpr h)
    unfold ghsiAgreementMag ghsiTExpectation
    rw [if_neg hy]
    simp_rw [ghsL_tvar_mate, if_neg hqy, mul_zero]
    simp



theorem ghsiExp2_fibre (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) :
    ghsiExp2 G K hf F =
      ∑ q : ConfigSpace V,
        ghsiAgreementProb G K hf q * ghsiFibreExpectation G K hf F q := by
  unfold ghsiExp2
  rw [ghsL_sum_pair_xnor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  have hm' : (∑ a : ConfigSpace V,
      wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) ≠ 0 := by
    simpa [ghsiFibreMass, ghsiFibreWeight] using hm
  have hZ : ZJ G.edgeFinset K hf ≠ 0 := (ZJ_pos _ _ _).ne'
  unfold ghsiAgreementProb ghsiFibreExpectation ghsiFibreNumerator ghsiFibreMass
    ghsiFibreWeight
  field_simp [hm, hm', hZ]

theorem ghsi_fibreFactorization (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x y : V) (q : ConfigSpace V) :
    ghsiFibreExpectation G K hf
        (fun a b => uvar a b o * uvar a b x * tvar a b y) q =
      ghsiFibreUU G K hf o x q * ghsiFibreT G K hf y q := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsiTWeight G K hf q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsiUWeight G K q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hweight (a : ConfigSpace V) : ghsiFibreWeight G K hf q a =
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreWeight
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split]
  have htobs (a : ConfigSpace V) : tvar a (ghsLMate q a) y =
      tObs (ghsLSplitEquiv q a).1 := ghsL_tvar_split q a y
  have huuobs (a : ConfigSpace V) :
      uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x =
        uuObs (ghsLSplitEquiv q a).2 := ghsL_uvar_mul_split q a o x
  have hUUT : ghsiFibreNumerator G K hf
      (fun a b => uvar a b o * uvar a b x * tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsiFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsiFibreWeight G K hf q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x *
        tvar a (ghsLMate q a) y) = _
    rw [hweight, htobs, huuobs]
    ring
  have hMass : ghsiFibreMass G K hf q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreMass
    exact Finset.sum_congr rfl (fun a _ => hweight a)
  have hT : ghsiFibreNumerator G K hf (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsiFibreWeight G K hf q a * tvar a (ghsLMate q a) y = _
    rw [hweight, htobs]
    ring
  have hUU : ghsiFibreNumerator G K hf
      (fun a b => uvar a b o * uvar a b x) q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsiFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsiFibreWeight G K hf q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [hweight, huuobs]
    ring
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT
    (fun su => fU su * uuObs su) fU
  unfold ghsiFibreUU ghsiFibreT ghsiFibreExpectation
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  field_simp [hm]
  rw [hUUT, hMass, hUU, hT]
  simpa [mul_comm] using hcross

theorem ghsi_duplicate_cov_nonpos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (o x y : V) (hox : o ≠ x) :
    ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x * tvar a b y) ≤
      ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) *
        ghsiExp2 G K hf (fun a b => tvar a b y) := by
  have hfkg := ghsL_fkg_antitone_monotone
    (ghsiAgreementProb_nonneg G K hf) (ghsiAgreementProb_sum_eq_one G K hf)
    (ghsiAgreementProb_fkg G K hf hK hhf)
    (show Antitone (ghsiFibreUU G K hf o x) from by
      intro q r hqr
      rw [ghsiFibreUU_eq_disagreementCorr G K hf o x hox,
        ghsiFibreUU_eq_disagreementCorr G K hf o x hox]
      exact ghsiDisagreementCorr_antitone G K hK o x
        (ghsLAgreeFinset_monotone hqr))
    (show Monotone (ghsiFibreT G K hf y) from by
      intro q r hqr
      rw [ghsiFibreT_eq_agreementMag G K hf y,
        ghsiFibreT_eq_agreementMag G K hf y]
      exact ghsiAgreementMag_monotone G K hf hK hhf y
        (ghsLAgreeFinset_monotone hqr))
  rw [ghsiExp2_fibre, ghsiExp2_fibre, ghsiExp2_fibre]
  simp_rw [ghsi_fibreFactorization G K hf o x y]
  exact hfkg

theorem ghsiExp2_add (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F H : ConfigSpace V → ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun a b => F a b + H a b) =
      ghsiExp2 G K hf F + ghsiExp2 G K hf H := by
  unfold ghsiExp2
  rw [← add_div]
  congr 1
  simp_rw [mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]

theorem ghsiExp2_const_mul (K : Sym2 V → ℝ) (hf : V → ℝ) (c : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun a b => c * F a b) = c * ghsiExp2 G K hf F := by
  unfold ghsiExp2
  rw [mul_div_assoc']
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem expJ_one (K : Sym2 V → ℝ) (hf : V → ℝ) :
    expJ G.edgeFinset K hf (fun _ => (1 : ℝ)) = 1 := by
  unfold expJ
  have hnum : (∑ s : ConfigSpace V, (1 : ℝ) * wJ G.edgeFinset K hf s) =
      ZJ G.edgeFinset K hf := by simp [ZJ]
  rw [hnum]
  exact div_self (ZJ_pos _ _ _).ne'

theorem ghsiExp2_factor_a (K : Sym2 V → ℝ) (hf : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun a _ => f a) = expJ G.edgeFinset K hf f := by
  have h := ghsiExp2_factor G K hf f (fun _ => (1 : ℝ))
  simpa [expJ_one G K hf] using h

theorem ghsiExp2_factor_b (K : Sym2 V → ℝ) (hf : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun _ b => f b) = expJ G.edgeFinset K hf f := by
  have h := ghsiExp2_factor G K hf (fun _ => (1 : ℝ)) f
  simpa [expJ_one G K hf] using h


theorem ghsi_ursell_eq_four_duplicate_cov
    (K : Sym2 V → ℝ) (hf : V → ℝ) (o x y : V) :
    expJ G.edgeFinset K hf (fun s => spin s o * (spin s x * spin s y)) -
          expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x * spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s y) *
            expJ G.edgeFinset K hf (fun s => spin s x) +
          2 * expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) =
      4 * (ghsiExp2 G K hf
              (fun a b => uvar a b o * uvar a b x * tvar a b y) -
            ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) *
              ghsiExp2 G K hf (fun a b => tvar a b y)) := by
  have hthree :
      (fun a b => uvar a b o * uvar a b x * tvar a b y) =
        (fun a b =>
          (1 / 8 : ℝ) * (spin a o * (spin a x * spin a y)) +
          (1 / 8 : ℝ) * ((spin a o * spin a x) * spin b y) +
          (-1 / 8 : ℝ) * ((spin a o * spin a y) * spin b x) +
          (-1 / 8 : ℝ) * (spin a o * (spin b x * spin b y)) +
          (-1 / 8 : ℝ) * ((spin a x * spin a y) * spin b o) +
          (-1 / 8 : ℝ) * (spin a x * (spin b o * spin b y)) +
          (1 / 8 : ℝ) * (spin a y * (spin b o * spin b x)) +
          (1 / 8 : ℝ) * (spin b o * (spin b x * spin b y))) := by
    funext a b
    simp only [uvar, tvar]
    ring
  rw [hthree]
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor,
    ghsiExp2_factor_a, ghsiExp2_factor_b]
  have huu : ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) =
      (expJ G.edgeFinset K hf (fun s => spin s o * spin s x) -
        expJ G.edgeFinset K hf (fun s => spin s o) *
          expJ G.edgeFinset K hf (fun s => spin s x)) / 2 := by
    have hexp : (fun a b => uvar a b o * uvar a b x) =
        (fun a b =>
          (1 / 4 : ℝ) * (spin a o * spin a x) +
          (-1 / 4 : ℝ) * (spin a o * spin b x) +
          (-1 / 4 : ℝ) * (spin a x * spin b o) +
          (1 / 4 : ℝ) * (spin b o * spin b x)) := by
      funext a b
      simp only [uvar]
      ring
    rw [hexp]
    simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor,
      ghsiExp2_factor_a, ghsiExp2_factor_b]
    ring
  have ht : ghsiExp2 G K hf (fun a b => tvar a b y) =
      expJ G.edgeFinset K hf (fun s => spin s y) := by
    have hexp : (fun a b => tvar a b y) =
        (fun a b => (1 / 2 : ℝ) * spin a y + (1 / 2 : ℝ) * spin b y) := by
      funext a b
      simp only [tvar]
      ring
    rw [hexp]
    simp only [ghsiExp2_add, ghsiExp2_const_mul,
      ghsiExp2_factor_a, ghsiExp2_factor_b]
    ring
  rw [huu, ht]
  ring



theorem ghsi_ursell_nonpos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (o x y : V) (hox : o ≠ x) :
    expJ G.edgeFinset K hf (fun s => spin s o * (spin s x * spin s y)) -
          expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x * spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s y) *
            expJ G.edgeFinset K hf (fun s => spin s x) +
          2 * expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) ≤ 0 := by
  rw [ghsi_ursell_eq_four_duplicate_cov]
  have h := ghsi_duplicate_cov_nonpos G K hf hK hhf o x y hox
  linarith




noncomputable def ghsiDirSpin (dir : V → ℝ) (s : ConfigSpace V) : ℝ :=
  ∑ x, dir x * spin s x


def ghsiFieldLine (hf dir : V → ℝ) (t : ℝ) : V → ℝ :=
  fun x => hf x + t * dir x

theorem ghsi_hasDerivAt_wJ_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (s : ConfigSpace V) (t : ℝ) :
    HasDerivAt (fun u => wJ G.edgeFinset K (ghsiFieldLine hf dir u) s)
      (wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s) t := by
  unfold wJ ghsiFieldLine ghsiDirSpin
  have hfield : HasDerivAt
      (fun u => ∑ x : V, (hf x + u * dir x) * spin s x)
      (∑ x : V, dir x * spin s x) t := by
    have hfun : (fun u => ∑ x : V, (hf x + u * dir x) * spin s x) =
        ∑ x : V, (fun u => (hf x + u * dir x) * spin s x) := by
      rw [Finset.sum_fn]
    rw [hfun]
    apply HasDerivAt.sum
    intro x _
    convert (((hasDerivAt_const t (hf x)).add
      ((hasDerivAt_id t).mul_const (dir x))).mul_const (spin s x)) using 1 <;> ring
  have hexp := ((hasDerivAt_const t
    (∑ e ∈ G.edgeFinset, K e * bond s e)).add hfield).exp
  simpa only [Pi.add_apply, zero_add, mul_comm] using hexp

theorem ghsi_hasDerivAt_Z_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ZJ G.edgeFinset K (ghsiFieldLine hf dir u))
      (∑ s : ConfigSpace V,
        wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s) t := by
  unfold ZJ
  have hfun : (fun u => ∑ s : ConfigSpace V,
      wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) =
      ∑ s : ConfigSpace V,
        (fun u => wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) := by
    rw [Finset.sum_fn]
  rw [hfun]
  exact HasDerivAt.sum (fun s _ => ghsi_hasDerivAt_wJ_fieldLine G K hf dir s t)

theorem ghsi_hasDerivAt_num_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ∑ s : ConfigSpace V,
        f s * wJ G.edgeFinset K (ghsiFieldLine hf dir u) s)
      (∑ s : ConfigSpace V,
        f s * (wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s)) t := by
  have hfun : (fun u => ∑ s : ConfigSpace V,
      f s * wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) =
      ∑ s : ConfigSpace V,
        (fun u => f s * wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) := by
    rw [Finset.sum_fn]
  rw [hfun]
  apply HasDerivAt.sum
  intro s _
  exact (ghsi_hasDerivAt_wJ_fieldLine G K hf dir s t).const_mul (f s)


theorem ghsi_hasDerivAt_expectation_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => expJ G.edgeFinset K (ghsiFieldLine hf dir u) f)
      (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
          (fun s => f s * ghsiDirSpin dir s) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir t) f *
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir)) t := by
  let hft := ghsiFieldLine hf dir t
  have hN := ghsi_hasDerivAt_num_fieldLine G K hf dir f t
  have hZ := ghsi_hasDerivAt_Z_fieldLine G K hf dir t
  have hZne : ZJ G.edgeFinset K hft ≠ 0 := (ZJ_pos _ _ _).ne'
  unfold expJ
  have hdiv := hN.div hZ hZne
  convert hdiv using 1
  · set Z := ZJ G.edgeFinset K hft
    set A := ∑ s : ConfigSpace V,
      f s * (wJ G.edgeFinset K hft s * ghsiDirSpin dir s)
    set B := ∑ s : ConfigSpace V, f s * wJ G.edgeFinset K hft s
    set C := ∑ s : ConfigSpace V, wJ G.edgeFinset K hft s * ghsiDirSpin dir s
    have hA : (∑ s : ConfigSpace V,
        f s * ghsiDirSpin dir s * wJ G.edgeFinset K hft s) = A := by
      change (∑ s : ConfigSpace V,
        f s * ghsiDirSpin dir s * wJ G.edgeFinset K hft s) =
        ∑ s : ConfigSpace V, f s * (wJ G.edgeFinset K hft s * ghsiDirSpin dir s)
      apply Finset.sum_congr rfl
      intro s _
      ring
    have hC : (∑ s : ConfigSpace V,
        ghsiDirSpin dir s * wJ G.edgeFinset K hft s) = C := by
      change (∑ s : ConfigSpace V,
        ghsiDirSpin dir s * wJ G.edgeFinset K hft s) =
        ∑ s : ConfigSpace V, wJ G.edgeFinset K hft s * ghsiDirSpin dir s
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hA, hC]
    change A / Z - B / Z * (C / Z) = (A * Z - B * C) / Z ^ 2
    field_simp


noncomputable def ghsiDirectionalCovariance (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) : ℝ :=
  expJ G.edgeFinset K hf (fun s => f s * ghsiDirSpin dir s) -
    expJ G.edgeFinset K hf f * expJ G.edgeFinset K hf (ghsiDirSpin dir)

theorem ghsi_hasDerivAt_directionalCovariance (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) (t : ℝ) :
    HasDerivAt
      (fun u => ghsiDirectionalCovariance G K (ghsiFieldLine hf dir u) dir f)
      (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
          (fun s => f s * ghsiDirSpin dir s * ghsiDirSpin dir s) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir t)
            (fun s => f s * ghsiDirSpin dir s) *
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) -
        (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
            (fun s => f s * ghsiDirSpin dir s) -
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) f *
            expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir)) *
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir t) f *
          (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
              (fun s => ghsiDirSpin dir s * ghsiDirSpin dir s) -
            expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir) *
              expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir))) t := by
  unfold ghsiDirectionalCovariance
  have h := (ghsi_hasDerivAt_expectation_fieldLine G K hf dir
      (fun s => f s * ghsiDirSpin dir s) t).sub
    ((ghsi_hasDerivAt_expectation_fieldLine G K hf dir f t).mul
      (ghsi_hasDerivAt_expectation_fieldLine G K hf dir (ghsiDirSpin dir) t))
  convert h using 1 <;> ring


noncomputable def ghsiUrsell3 (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x y : V) : ℝ :=
  expJ G.edgeFinset K hf (fun s => spin s o * (spin s x * spin s y)) -
    expJ G.edgeFinset K hf (fun s => spin s o) *
      expJ G.edgeFinset K hf (fun s => spin s x * spin s y) -
    expJ G.edgeFinset K hf (fun s => spin s o * spin s x) *
      expJ G.edgeFinset K hf (fun s => spin s y) -
    expJ G.edgeFinset K hf (fun s => spin s o * spin s y) *
      expJ G.edgeFinset K hf (fun s => spin s x) +
    2 * expJ G.edgeFinset K hf (fun s => spin s o) *
      expJ G.edgeFinset K hf (fun s => spin s x) *
      expJ G.edgeFinset K hf (fun s => spin s y)

theorem ghsiUrsell3_nonpos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (o x y : V) (hox : o ≠ x) :
    ghsiUrsell3 G K hf o x y ≤ 0 := by
  exact ghsi_ursell_nonpos G K hf hK hhf o x y hox

theorem ghsi_expJ_sum {I : Type*} (K : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset I) (f : I → ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf (fun cfg => ∑ i ∈ S, f i cfg) =
      ∑ i ∈ S, expJ G.edgeFinset K hf (f i) := by
  unfold expJ
  change (∑ cfg : ConfigSpace V,
      (∑ i ∈ S, f i cfg) * wJ G.edgeFinset K hf cfg) /
      ZJ G.edgeFinset K hf = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]

theorem ghsi_expJ_const_mul (K : Sym2 V → ℝ) (hf : V → ℝ)
    (c : ℝ) (f : ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf (fun cfg => c * f cfg) =
      c * expJ G.edgeFinset K hf f := by
  unfold expJ
  change (∑ s : ConfigSpace V, (c * f s) * wJ G.edgeFinset K hf s) /
      ZJ G.edgeFinset K hf = c *
        ((∑ s : ConfigSpace V, f s * wJ G.edgeFinset K hf s) /
          ZJ G.edgeFinset K hf)
  rw [show (∑ s : ConfigSpace V, (c * f s) * wJ G.edgeFinset K hf s) =
      c * ∑ s : ConfigSpace V, f s * wJ G.edgeFinset K hf s by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  ring

theorem ghsi_expJ_dirSpin (K : Sym2 V → ℝ) (hf dir : V → ℝ) :
    expJ G.edgeFinset K hf (ghsiDirSpin dir) =
      ∑ x, dir x * expJ G.edgeFinset K hf (fun s => spin s x) := by
  unfold ghsiDirSpin
  rw [ghsi_expJ_sum G K hf Finset.univ]
  apply Finset.sum_congr rfl
  intro x _
  exact ghsi_expJ_const_mul G K hf (dir x) (fun s => spin s x)

theorem ghsi_expJ_mul_dirSpin (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf (fun s => f s * ghsiDirSpin dir s) =
      ∑ x, dir x * expJ G.edgeFinset K hf (fun s => f s * spin s x) := by
  have hfun : (fun s => f s * ghsiDirSpin dir s) =
      (fun s => ∑ x, dir x * (f s * spin s x)) := by
    funext s
    unfold ghsiDirSpin
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfun, ghsi_expJ_sum G K hf Finset.univ]
  apply Finset.sum_congr rfl
  intro x _
  exact ghsi_expJ_const_mul G K hf (dir x) (fun s => f s * spin s x)

theorem ghsi_expJ_mul_dirSpin_sq (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf
        (fun s => f s * ghsiDirSpin dir s * ghsiDirSpin dir s) =
      ∑ x, ∑ y, dir x * dir y *
        expJ G.edgeFinset K hf (fun s => f s * spin s x * spin s y) := by
  rw [ghsi_expJ_mul_dirSpin G K hf dir (fun s => f s * ghsiDirSpin dir s)]
  apply Finset.sum_congr rfl
  intro x _
  have hreorder : expJ G.edgeFinset K hf
      (fun s => f s * ghsiDirSpin dir s * spin s x) =
      expJ G.edgeFinset K hf
        (fun s => (f s * spin s x) * ghsiDirSpin dir s) := by
    congr 1
    funext s
    ring
  rw [hreorder, ghsi_expJ_mul_dirSpin G K hf dir (fun s => f s * spin s x)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring


noncomputable def ghsiCovariance (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x : V) : ℝ :=
  expJ G.edgeFinset K hf (fun s => spin s o * spin s x) -
    expJ G.edgeFinset K hf (fun s => spin s o) *
      expJ G.edgeFinset K hf (fun s => spin s x)

theorem ghsi_directionalCovariance_eq_sum_covariance
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o : V) :
    ghsiDirectionalCovariance G K hf dir (fun s => spin s o) =
      ∑ x, dir x * ghsiCovariance G K hf o x := by
  unfold ghsiDirectionalCovariance ghsiCovariance
  rw [ghsi_expJ_mul_dirSpin G K hf dir (fun s => spin s o),
    ghsi_expJ_dirSpin G K hf dir, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring



theorem ghsi_hasDerivAt_covariance_fieldLine
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o x : V) (t : ℝ) :
    HasDerivAt
      (fun u => ghsiCovariance G K (ghsiFieldLine hf dir u) o x)
      (∑ y, dir y * ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y) t := by
  unfold ghsiCovariance
  have h := (ghsi_hasDerivAt_expectation_fieldLine G K hf dir
      (fun s => spin s o * spin s x) t).sub
    ((ghsi_hasDerivAt_expectation_fieldLine G K hf dir (fun s => spin s o) t).mul
      (ghsi_hasDerivAt_expectation_fieldLine G K hf dir (fun s => spin s x) t))
  convert h using 1
  rw [ghsi_expJ_mul_dirSpin G K (ghsiFieldLine hf dir t) dir
      (fun s => spin s o * spin s x),
    ghsi_expJ_dirSpin G K (ghsiFieldLine hf dir t) dir,
    ghsi_expJ_mul_dirSpin G K (ghsiFieldLine hf dir t) dir (fun s => spin s o),
    ghsi_expJ_mul_dirSpin G K (ghsiFieldLine hf dir t) dir (fun s => spin s x)]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  unfold ghsiUrsell3
  have hassoc : expJ G.edgeFinset K (ghsiFieldLine hf dir t)
      (fun s => spin s o * spin s x * spin s y) =
      expJ G.edgeFinset K (ghsiFieldLine hf dir t)
        (fun s => spin s o * (spin s x * spin s y)) := by
    congr 1
    funext s
    ring
  rw [hassoc]
  ring

theorem ghsi_hasDerivAt_directionalCovariance_ursellSum
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o : V) (t : ℝ) :
    HasDerivAt
      (fun u => ghsiDirectionalCovariance G K (ghsiFieldLine hf dir u) dir
        (fun s => spin s o))
      (∑ x, ∑ y, dir x * dir y *
        ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y) t := by
  have hfun : (fun u => ghsiDirectionalCovariance G K
      (ghsiFieldLine hf dir u) dir (fun s => spin s o)) =
      (fun u => ∑ x, dir x *
        ghsiCovariance G K (ghsiFieldLine hf dir u) o x) := by
    funext u
    exact ghsi_directionalCovariance_eq_sum_covariance G K
      (ghsiFieldLine hf dir u) dir o
  rw [hfun]
  have hsum : HasDerivAt
      (fun u => ∑ x, dir x *
        ghsiCovariance G K (ghsiFieldLine hf dir u) o x)
      (∑ x, dir x *
        (∑ y, dir y * ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y)) t := by
    have hsumfun : (fun u => ∑ x, dir x *
        ghsiCovariance G K (ghsiFieldLine hf dir u) o x) =
        ∑ x : V, (fun u => dir x *
          ghsiCovariance G K (ghsiFieldLine hf dir u) o x) := by
      rw [Finset.sum_fn]
    rw [hsumfun]
    apply HasDerivAt.sum
    intro x _
    exact (ghsi_hasDerivAt_covariance_fieldLine G K hf dir o x t).const_mul (dir x)
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring



theorem ghsi_directionalCovariance_derivValue_eq_ursellSum
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o : V) :
    (expJ G.edgeFinset K hf
          (fun s => spin s o * ghsiDirSpin dir s * ghsiDirSpin dir s) -
        expJ G.edgeFinset K hf (fun s => spin s o * ghsiDirSpin dir s) *
          expJ G.edgeFinset K hf (ghsiDirSpin dir) -
        (expJ G.edgeFinset K hf (fun s => spin s o * ghsiDirSpin dir s) -
          expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (ghsiDirSpin dir)) *
          expJ G.edgeFinset K hf (ghsiDirSpin dir) -
        expJ G.edgeFinset K hf (fun s => spin s o) *
          (expJ G.edgeFinset K hf
              (fun s => ghsiDirSpin dir s * ghsiDirSpin dir s) -
            expJ G.edgeFinset K hf (ghsiDirSpin dir) *
              expJ G.edgeFinset K hf (ghsiDirSpin dir))) =
      ∑ x, ∑ y, dir x * dir y * ghsiUrsell3 G K hf o x y := by
  have hraw := ghsi_hasDerivAt_directionalCovariance G K hf dir
    (fun s => spin s o) 0
  have hsum := ghsi_hasDerivAt_directionalCovariance_ursellSum G K hf dir o 0
  have hline : ghsiFieldLine hf dir 0 = hf := by
    funext x
    simp [ghsiFieldLine]
  rw [hline] at hraw hsum
  exact hraw.unique hsum



theorem ghsi_magnetization_fieldLine_concaveOn
    (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (hdir : ∀ x, 0 ≤ dir x) (o : V) (hdiro : dir o = 0) :
    ConcaveOn ℝ (Ici 0)
      (fun t => expJ G.edgeFinset K (ghsiFieldLine hf dir t)
        (fun s => spin s o)) := by
  let phi : ℝ → ℝ := fun t => expJ G.edgeFinset K (ghsiFieldLine hf dir t)
    (fun s => spin s o)
  have hphi (t : ℝ) : HasDerivAt phi
      (ghsiDirectionalCovariance G K (ghsiFieldLine hf dir t) dir
        (fun s => spin s o)) t := by
    exact ghsi_hasDerivAt_expectation_fieldLine G K hf dir (fun s => spin s o) t
  have hderiv : deriv phi = fun t =>
      ghsiDirectionalCovariance G K (ghsiFieldLine hf dir t) dir
        (fun s => spin s o) := by
    funext t
    exact (hphi t).deriv
  apply Sharpness.shg_concaveOn_of_deriv2_nonpos
  · intro t _
    exact (hphi t).continuousAt.continuousWithinAt
  · intro t _
    exact (hphi t).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t _
    rw [hderiv]
    have hd := ghsi_hasDerivAt_directionalCovariance_ursellSum G K hf dir o t
    exact hd.differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    change deriv (deriv phi) t ≤ 0
    rw [hderiv]
    rw [(ghsi_hasDerivAt_directionalCovariance_ursellSum G K hf dir o t).deriv]
    apply Finset.sum_nonpos
    intro x _
    apply Finset.sum_nonpos
    intro y _
    by_cases hxo : x = o
    · subst x
      rw [hdiro]
      simp
    · have hfield : ∀ z, 0 ≤ ghsiFieldLine hf dir t z := by
        intro z
        unfold ghsiFieldLine
        exact add_nonneg (hhf z) (mul_nonneg ht.le (hdir z))
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (hdir x) (hdir y))
        (ghsiUrsell3_nonpos G K (ghsiFieldLine hf dir t) hK hfield o x y
          (Ne.symm hxo))


theorem ghsi_directionalCovariance_le_secant
    (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (hdir : ∀ x, 0 ≤ dir x) (o : V) (hdiro : dir o = 0)
    {b : ℝ} (hb : 0 < b) :
    ghsiDirectionalCovariance G K (ghsiFieldLine hf dir b) dir
        (fun s => spin s o) ≤
      (expJ G.edgeFinset K (ghsiFieldLine hf dir b) (fun s => spin s o) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir 0) (fun s => spin s o)) / b := by
  let phi : ℝ → ℝ := fun t => expJ G.edgeFinset K (ghsiFieldLine hf dir t)
    (fun s => spin s o)
  have hconc := ghsi_magnetization_fieldLine_concaveOn G K hf dir hK hhf hdir o hdiro
  have hslope := Sharpness.shg_concaveOn_deriv_le_slope phi hconc
    (mem_Ici.mpr le_rfl) (mem_Ici.mpr hb.le) hb
    (ghsi_hasDerivAt_expectation_fieldLine G K hf dir
      (fun s => spin s o) b).differentiableAt
  rw [(ghsi_hasDerivAt_expectation_fieldLine G K hf dir
    (fun s => spin s o) b).deriv] at hslope
  simpa [phi, ghsiDirectionalCovariance, sub_zero] using hslope

end StatMech.Ising
