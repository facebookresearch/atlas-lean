/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.CurrentParityDetermination










open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness



noncomputable def inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (odd : S -> Bool) (a : S -> Nat) : Real :=
  ∏ i, parityEdgeKernel (lambda i.1) (odd i) (a i)

theorem summable_inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    Summable (inhomogeneousFiniteParityKernel S lambda odd) := by
  let g : E -> Nat -> Real := fun e k =>
    if he : e ∈ S then parityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
    else parityEdgeKernel 1 false k
  have hg : forall e, Summable (g e) := by
    intro e
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : forall e k, 0 <= g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact parityEdgeKernel_nonneg (lambda e) (hlambda ⟨e, he⟩) _ _
    · exact parityEdgeKernel_nonneg 1 (by norm_num) _ _
  exact (prod_tsum_fubini g hg hgnn S).1.congr (fun a => by
    unfold inhomogeneousFiniteParityKernel
    apply Fintype.prod_congr
    intro i
    simp [g])

theorem tsum_inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    ∑' a : S -> Nat, inhomogeneousFiniteParityKernel S lambda odd a = 1 := by
  let g : E -> Nat -> Real := fun e k =>
    if he : e ∈ S then parityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
    else parityEdgeKernel 1 false k
  have hg : forall e, Summable (g e) := by
    intro e
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : forall e k, 0 <= g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact parityEdgeKernel_nonneg (lambda e) (hlambda ⟨e, he⟩) _ _
    · exact parityEdgeKernel_nonneg 1 (by norm_num) _ _
  rw [show (∑' a : S -> Nat,
      inhomogeneousFiniteParityKernel S lambda odd a) =
      ∑' a : S -> Nat, ∏ i : S, g i.1 (a i) by
    apply tsum_congr
    intro a
    simp [inhomogeneousFiniteParityKernel, g]]
  rw [← (prod_tsum_fubini g hg hgnn S).2]
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_parityEdgeKernel (lambda e) (hlambda ⟨e, he⟩)
    (odd ⟨e, he⟩)

theorem tsum_ofReal_inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    ∑' a : S -> Nat,
      ENNReal.ofReal (inhomogeneousFiniteParityKernel S lambda odd a) = 1 := by
  have hnonneg : forall a : S -> Nat,
      0 <= inhomogeneousFiniteParityKernel S lambda odd a := by
    intro a
    exact Finset.prod_nonneg fun i _ =>
      parityEdgeKernel_nonneg (lambda i.1) (hlambda i) (odd i) (a i)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_inhomogeneousFiniteParityKernel S lambda hlambda odd),
    tsum_inhomogeneousFiniteParityKernel S lambda hlambda odd]
  simp



noncomputable def inhomogeneousFiniteParityPMF
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    PMF (S -> Nat) :=
  PMF.normalize
    (fun a => ENNReal.ofReal
      (inhomogeneousFiniteParityKernel S lambda odd a))
    (by
      rw [tsum_ofReal_inhomogeneousFiniteParityKernel S lambda hlambda odd]
      exact one_ne_zero)
    (by
      rw [tsum_ofReal_inhomogeneousFiniteParityKernel S lambda hlambda odd]
      exact ENNReal.one_ne_top)

theorem inhomogeneousFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool)
    (a : S -> Nat) :
    inhomogeneousFiniteParityPMF S lambda hlambda odd a =
      ENNReal.ofReal (inhomogeneousFiniteParityKernel S lambda odd a) := by
  rw [inhomogeneousFiniteParityPMF, PMF.normalize_apply,
    tsum_ofReal_inhomogeneousFiniteParityKernel S lambda hlambda odd]
  simp

theorem inhomogeneousFiniteParityPMF_eq_zero_of_ne
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool)
    (a : S -> Nat) (hodd : odd ≠ currentLocalParity a) :
    inhomogeneousFiniteParityPMF S lambda hlambda odd a = 0 := by
  rw [inhomogeneousFiniteParityPMF_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hodd
  unfold inhomogeneousFiniteParityKernel
  apply ENNReal.ofReal_eq_zero.mpr
  apply le_of_eq
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases heven : Even (a i)
  · have hpar : currentLocalParity a i = false := by
      simp [currentLocalParity, heven, Nat.not_odd_iff_even.mpr heven]
    have hoddTrue : odd i = true := by
      cases h : odd i <;> simp_all
    simp [parityEdgeKernel, hoddTrue, Nat.not_odd_iff_even.mpr heven]
  · have hoddNat : Odd (a i) := Nat.not_even_iff_odd.mp heven
    have hpar : currentLocalParity a i = true := by
      simp [currentLocalParity, hoddNat]
    have hoddFalse : odd i = false := by
      cases h : odd i <;> simp_all
    simp [parityEdgeKernel, hoddFalse, heven]

theorem bind_inhomogeneousFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1)
    (p : PMF (S -> Bool)) (a : S -> Nat) :
    p.bind (inhomogeneousFiniteParityPMF S lambda hlambda) a =
      p (currentLocalParity a) *
        inhomogeneousFiniteParityPMF S lambda hlambda
          (currentLocalParity a) a := by
  rw [PMF.bind_apply, tsum_eq_single (currentLocalParity a)]
  intro odd hodd
  rw [inhomogeneousFiniteParityPMF_eq_zero_of_ne
    S lambda hlambda odd a hodd]
  simp

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real) (H : Finset (Sym2 V))
    (m : EdgeCurrent G) : Real :=
  ∏ e : G.edgeFinset, parityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e)

theorem summable_inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) :
    Summable (inhomogeneousParityCurrentKernel G lambda H) := by
  let g : Sym2 V -> Nat -> Real := fun e k =>
    if he : e ∈ G.edgeFinset then
      parityEdgeKernel (lambda e) (e ∈ H) k
    else parityEdgeKernel 1 false k
  have hg : forall e, Summable (g e) := by
    intro e
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : forall e k, 0 <= g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact parityEdgeKernel_nonneg (lambda e) (hlambda ⟨e, he⟩) _ _
    · exact parityEdgeKernel_nonneg 1 (by norm_num) _ _
  exact (prod_tsum_fubini g hg hgnn G.edgeFinset).1.congr (fun m => by
    unfold inhomogeneousParityCurrentKernel
    apply Fintype.prod_congr
    intro e
    change g e.1 (m e) =
      parityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e)
    dsimp only [g]
    rw [dif_pos e.2])

theorem tsum_inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G, inhomogeneousParityCurrentKernel G lambda H m = 1 := by
  let g : Sym2 V -> Nat -> Real := fun e k =>
    if he : e ∈ G.edgeFinset then
      parityEdgeKernel (lambda e) (e ∈ H) k
    else parityEdgeKernel 1 false k
  have hg : forall e, Summable (g e) := by
    intro e
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : forall e k, 0 <= g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact parityEdgeKernel_nonneg (lambda e) (hlambda ⟨e, he⟩) _ _
    · exact parityEdgeKernel_nonneg 1 (by norm_num) _ _
  rw [show (∑' m : EdgeCurrent G,
      inhomogeneousParityCurrentKernel G lambda H m) =
      ∑' m : EdgeCurrent G, ∏ e : G.edgeFinset, g e.1 (m e) by
    apply tsum_congr
    intro m
    unfold inhomogeneousParityCurrentKernel
    apply Fintype.prod_congr
    intro e
    change parityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e) = g e.1 (m e)
    dsimp only [g]
    rw [dif_pos e.2]]
  rw [← (prod_tsum_fubini g hg hgnn G.edgeFinset).2]
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_parityEdgeKernel (lambda e) (hlambda ⟨e, he⟩) (e ∈ H)

theorem tsum_ofReal_inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G,
      ENNReal.ofReal (inhomogeneousParityCurrentKernel G lambda H m) = 1 := by
  have hnonneg : forall m : EdgeCurrent G,
      0 <= inhomogeneousParityCurrentKernel G lambda H m := by
    intro m
    unfold inhomogeneousParityCurrentKernel
    exact Finset.prod_nonneg fun e _ =>
      parityEdgeKernel_nonneg (lambda e.1) (hlambda e) (e.1 ∈ H) (m e)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_inhomogeneousParityCurrentKernel G lambda hlambda H),
    tsum_inhomogeneousParityCurrentKernel G lambda hlambda H]
  simp



noncomputable def inhomogeneousParityCurrentPMF
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) : PMF (EdgeCurrent G) :=
  PMF.normalize
    (fun m => ENNReal.ofReal
      (inhomogeneousParityCurrentKernel G lambda H m))
    (by
      rw [tsum_ofReal_inhomogeneousParityCurrentKernel G lambda hlambda H]
      exact one_ne_zero)
    (by
      rw [tsum_ofReal_inhomogeneousParityCurrentKernel G lambda hlambda H]
      exact ENNReal.one_ne_top)

theorem inhomogeneousParityCurrentPMF_apply
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) (m : EdgeCurrent G) :
    inhomogeneousParityCurrentPMF G lambda hlambda H m =
      ENNReal.ofReal (inhomogeneousParityCurrentKernel G lambda H m) := by
  rw [inhomogeneousParityCurrentPMF, PMF.normalize_apply,
    tsum_ofReal_inhomogeneousParityCurrentKernel G lambda hlambda H]
  simp

theorem inhomogeneousParityCurrentKernel_eq_zero_of_support_ne
    (lambda : Sym2 V -> Real) (H : Finset (Sym2 V))
    (hH : H ⊆ G.edgeFinset) (m : EdgeCurrent G)
    (hm : currentParitySupport G m ≠ H) :
    inhomogeneousParityCurrentKernel G lambda H m = 0 := by
  have hall : ¬ (forall e : G.edgeFinset,
      if e.1 ∈ H then Odd (m e) else Even (m e)) :=
    fun h => hm ((currentParitySupport_eq_iff G H hH m).mpr h)
  push Not at hall
  obtain ⟨e, he⟩ := hall
  unfold inhomogeneousParityCurrentKernel
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  by_cases heH : e.1 ∈ H
  · have hnot : ¬ Odd (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]
  · have hnot : ¬ Even (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]



noncomputable def inhomogeneousParityFiberMass
    (lambda : Sym2 V -> Real) (H : Finset (Sym2 V)) : Real :=
  ∏ e : G.edgeFinset,
    if e.1 ∈ H then Real.sinh (lambda e.1) else Real.cosh (lambda e.1)



theorem weight_eq_inhomogeneousParityFiberMass_mul_kernel
    (beta : Real) (hbeta : 0 < beta) (J : Sym2 V -> Real)
    (hJ : forall e : G.edgeFinset, 0 < J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m = H) :
    weight G beta J (ofEdgeFun G m) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H *
        inhomogeneousParityCurrentKernel G (fun e => beta * J e) H m := by
  have hall := (currentParitySupport_eq_iff G H hH m).mp hm
  unfold inhomogeneousParityFiberMass inhomogeneousParityCurrentKernel
  symm
  calc
    (∏ e : G.edgeFinset,
        if e.1 ∈ H then Real.sinh (beta * J e.1)
        else Real.cosh (beta * J e.1)) *
          ∏ e : G.edgeFinset,
            parityEdgeKernel (beta * J e.1) (e.1 ∈ H) (m e) =
        ∏ e : G.edgeFinset,
          (if e.1 ∈ H then Real.sinh (beta * J e.1)
            else Real.cosh (beta * J e.1)) *
              parityEdgeKernel (beta * J e.1) (e.1 ∈ H) (m e) := by
      exact (Finset.prod_mul_distrib (s := Finset.univ)).symm
    _ = ∏ e : G.edgeFinset, (beta * J e.1) ^ m e / (m e).factorial := by
      apply Fintype.prod_congr
      intro e
      have hlambda : 0 < beta * J e.1 := mul_pos hbeta (hJ e)
      by_cases heH : e.1 ∈ H
      · have ho : Odd (m e) := by simpa [heH] using hall e
        have hsinh : Real.sinh (beta * J e.1) ≠ 0 :=
          ne_of_gt (Real.sinh_pos_iff.2 hlambda)
        simp [parityEdgeKernel, heH, ho, conditionalCurrentTerm]
        field_simp [hsinh]
      · have hev : Even (m e) := by simpa [heH] using hall e
        have hcosh : Real.cosh (beta * J e.1) ≠ 0 :=
          ne_of_gt (Real.cosh_pos (beta * J e.1))
        simp [parityEdgeKernel, heH, hev, conditionalCurrentTerm]
        field_simp [hcosh]
    _ = weight G beta J (ofEdgeFun G m) :=
      (weight_ofEdgeFun G beta J m).symm



theorem fixedParity_weight_tsum_inhomogeneous
    (beta : Real) (hbeta : 0 < beta) (J : Sym2 V -> Real)
    (hJ : forall e : G.edgeFinset, 0 < J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        weight G beta J (ofEdgeFun G m) else 0) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
  let lambda : Sym2 V -> Real := fun e => beta * J e
  have hlambda : forall e : G.edgeFinset, 0 < lambda e.1 := fun e =>
    mul_pos hbeta (hJ e)
  let c := inhomogeneousParityFiberMass G lambda H
  let kernel := inhomogeneousParityCurrentKernel G lambda H
  have hpoint (m : EdgeCurrent G) :
      (if currentParitySupport G m = H then
          weight G beta J (ofEdgeFun G m) else 0) = c * kernel m := by
    by_cases hm : currentParitySupport G m = H
    · rw [if_pos hm]
      exact weight_eq_inhomogeneousParityFiberMass_mul_kernel
        G beta hbeta J hJ H hH m hm
    · rw [if_neg hm]
      have hk : kernel m = 0 := by
        exact inhomogeneousParityCurrentKernel_eq_zero_of_support_ne
          G lambda H hH m hm
      rw [hk, mul_zero]
  rw [tsum_congr hpoint, tsum_mul_left,
    tsum_inhomogeneousParityCurrentKernel G lambda hlambda H, mul_one]

end Graph

end StatMech.FrontierB
