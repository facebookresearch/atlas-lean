/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.InhomogeneousCurrentConditionalPMF









open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising




noncomputable def nonnegativeParityEdgeKernel
    (lambda : ℝ) (odd : Bool) (k : ℕ) : ℝ :=
  if lambda = 0 then if k = (if odd then 1 else 0) then 1 else 0
  else parityEdgeKernel lambda odd k

theorem nonnegativeParityEdgeKernel_nonneg
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (odd : Bool) (k : ℕ) :
    0 ≤ nonnegativeParityEdgeKernel lambda odd k := by
  by_cases hzero : lambda = 0
  · rw [nonnegativeParityEdgeKernel, if_pos hzero]
    by_cases hk : k = (if odd then 1 else 0) <;> simp [hk]
  · rw [nonnegativeParityEdgeKernel, if_neg hzero]
    exact parityEdgeKernel_nonneg lambda
      (lt_of_le_of_ne hlambda (Ne.symm hzero)) odd k

theorem summable_nonnegativeParityEdgeKernel
    {lambda : ℝ} (_hlambda : 0 ≤ lambda) (odd : Bool) :
    Summable (nonnegativeParityEdgeKernel lambda odd) := by
  change Summable (fun k : ℕ =>
    if lambda = 0 then
      if k = (if odd then 1 else 0) then 1 else 0
    else parityEdgeKernel lambda odd k)
  by_cases hzero : lambda = 0
  · simp only [hzero, if_true]
    exact (hasSum_ite_eq (if odd then 1 else 0) (1 : ℝ)).summable
  · simp only [hzero, if_false]
    exact summable_parityEdgeKernel lambda odd

theorem tsum_nonnegativeParityEdgeKernel
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (odd : Bool) :
    ∑' k : ℕ, nonnegativeParityEdgeKernel lambda odd k = 1 := by
  change (∑' k : ℕ, if lambda = 0 then
    if k = (if odd then 1 else 0) then 1 else 0
    else parityEdgeKernel lambda odd k) = 1
  by_cases hzero : lambda = 0
  · simp only [hzero, if_true, tsum_ite_eq]
  · simp only [hzero, if_false]
    exact tsum_parityEdgeKernel lambda
      (lt_of_le_of_ne hlambda (Ne.symm hzero)) odd

theorem nonnegativeParityEdgeKernel_eq_zero_of_parity_ne
    (lambda : ℝ) (odd : Bool) (k : ℕ)
    (hpar : ¬(if odd then Odd k else Even k)) :
    nonnegativeParityEdgeKernel lambda odd k = 0 := by
  by_cases hzero : lambda = 0
  · subst lambda
    cases odd
    · have hk : k ≠ 0 := by
        intro hk
        subst k
        exact hpar (by simp)
      simp [nonnegativeParityEdgeKernel, hk]
    · have hk : k ≠ 1 := by
        intro hk
        subst k
        exact hpar (by simp)
      simp [nonnegativeParityEdgeKernel, hk]
  · cases odd <;> simp_all [nonnegativeParityEdgeKernel,
      parityEdgeKernel]




theorem parityFiberMass_mul_nonnegativeParityEdgeKernel
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (odd : Bool) (k : ℕ)
    (hpar : if odd then Odd k else Even k) :
    (if odd then Real.sinh lambda else Real.cosh lambda) *
        nonnegativeParityEdgeKernel lambda odd k =
      lambda ^ k / k.factorial := by
  by_cases hzero : lambda = 0
  · subst lambda
    cases odd
    · by_cases hk : k = 0
      · subst k
        norm_num [nonnegativeParityEdgeKernel]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        rw [zero_pow (Nat.ne_of_gt hkpos)]
        simp [nonnegativeParityEdgeKernel, hk]
    · have hkpos : 0 < k := Odd.pos hpar
      rw [zero_pow (Nat.ne_of_gt hkpos)]
      simp [nonnegativeParityEdgeKernel]
  · have hlambdaPos : 0 < lambda :=
      lt_of_le_of_ne hlambda (Ne.symm hzero)
    cases odd
    · have heven : Even k := hpar
      have hcosh : Real.cosh lambda ≠ 0 := (Real.cosh_pos lambda).ne'
      simp [nonnegativeParityEdgeKernel, hzero, parityEdgeKernel,
        heven, conditionalCurrentTerm]
      field_simp [hcosh]
    · have hodd : Odd k := hpar
      have hsinh : Real.sinh lambda ≠ 0 :=
        (Real.sinh_pos_iff.2 hlambdaPos).ne'
      simp [nonnegativeParityEdgeKernel, hzero, parityEdgeKernel,
        hodd, conditionalCurrentTerm]
      field_simp [hsinh]



noncomputable def nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (odd : ↑S → Bool) (a : ↑S → ℕ) : ℝ :=
  ∏ i, nonnegativeParityEdgeKernel (lambda i.1) (odd i) (a i)

theorem summable_nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    Summable (nonnegativeFiniteParityKernel S lambda odd) := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then nonnegativeParityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
    else nonnegativeParityEdgeKernel 0 false k
  have hg : ∀ e, Summable (g e) := by
    intro e
    unfold g
    split
    · rename_i he
      exact summable_nonnegativeParityEdgeKernel (hlambda ⟨e, he⟩) _
    · exact summable_nonnegativeParityEdgeKernel le_rfl _
  have hgnn : ∀ e k, 0 ≤ g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact nonnegativeParityEdgeKernel_nonneg (hlambda ⟨e, he⟩) _ _
    · exact nonnegativeParityEdgeKernel_nonneg le_rfl _ _
  exact (prod_tsum_fubini g hg hgnn S).1.congr (fun a => by
    unfold nonnegativeFiniteParityKernel
    apply Fintype.prod_congr
    intro i
    simp [g])

theorem tsum_nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    ∑' a : ↑S → ℕ, nonnegativeFiniteParityKernel S lambda odd a = 1 := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then nonnegativeParityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
    else nonnegativeParityEdgeKernel 0 false k
  have hg : ∀ e, Summable (g e) := by
    intro e
    unfold g
    split
    · rename_i he
      exact summable_nonnegativeParityEdgeKernel (hlambda ⟨e, he⟩) _
    · exact summable_nonnegativeParityEdgeKernel le_rfl _
  have hgnn : ∀ e k, 0 ≤ g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact nonnegativeParityEdgeKernel_nonneg (hlambda ⟨e, he⟩) _ _
    · exact nonnegativeParityEdgeKernel_nonneg le_rfl _ _
  rw [show (∑' a : ↑S → ℕ,
      nonnegativeFiniteParityKernel S lambda odd a) =
      ∑' a : ↑S → ℕ, ∏ i : ↑S, g i.1 (a i) by
    apply tsum_congr
    intro a
    simp [nonnegativeFiniteParityKernel, g]]
  rw [← (prod_tsum_fubini g hg hgnn S).2]
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_nonnegativeParityEdgeKernel (hlambda ⟨e, he⟩) (odd ⟨e, he⟩)

theorem tsum_ofReal_nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    ∑' a : ↑S → ℕ,
      ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a) = 1 := by
  have hnonneg : ∀ a : ↑S → ℕ,
      0 ≤ nonnegativeFiniteParityKernel S lambda odd a := by
    intro a
    exact Finset.prod_nonneg fun i _ =>
      nonnegativeParityEdgeKernel_nonneg (hlambda i) (odd i) (a i)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_nonnegativeFiniteParityKernel S lambda hlambda odd),
    tsum_nonnegativeFiniteParityKernel S lambda hlambda odd]
  simp



noncomputable def nonnegativeFiniteParityPMF
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    PMF (↑S → ℕ) :=
  PMF.normalize
    (fun a => ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a))
    (by
      rw [tsum_ofReal_nonnegativeFiniteParityKernel S lambda hlambda odd]
      exact one_ne_zero)
    (by
      rw [tsum_ofReal_nonnegativeFiniteParityKernel S lambda hlambda odd]
      exact ENNReal.one_ne_top)

theorem nonnegativeFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool)
    (a : ↑S → ℕ) :
    nonnegativeFiniteParityPMF S lambda hlambda odd a =
      ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a) := by
  rw [nonnegativeFiniteParityPMF, PMF.normalize_apply,
    tsum_ofReal_nonnegativeFiniteParityKernel S lambda hlambda odd]
  simp

theorem nonnegativeFiniteParityPMF_eq_zero_of_ne
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool)
    (a : ↑S → Nat) (hodd : odd ≠ currentLocalParity a) :
    nonnegativeFiniteParityPMF S lambda hlambda odd a = 0 := by
  rw [nonnegativeFiniteParityPMF_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hodd
  apply ENNReal.ofReal_eq_zero.mpr
  apply le_of_eq
  unfold nonnegativeFiniteParityKernel
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply nonnegativeParityEdgeKernel_eq_zero_of_parity_ne
  cases h : odd i <;> simp [h, currentLocalParity] at hi ⊢ <;> assumption

theorem bind_nonnegativeFiniteParityPMF_apply
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1)
    (p : PMF (↑S → Bool)) (a : ↑S → Nat) :
    p.bind (nonnegativeFiniteParityPMF S lambda hlambda) a =
      p (currentLocalParity a) *
        nonnegativeFiniteParityPMF S lambda hlambda
          (currentLocalParity a) a := by
  rw [PMF.bind_apply, tsum_eq_single (currentLocalParity a)]
  intro odd hodd
  rw [nonnegativeFiniteParityPMF_eq_zero_of_ne
    S lambda hlambda odd a hodd]
  simp

section Graph

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inhomogeneousParityFiberMass_nonneg
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) :
    0 ≤ inhomogeneousParityFiberMass G lambda H := by
  unfold inhomogeneousParityFiberMass
  exact Finset.prod_nonneg fun e _ => by
    by_cases he : e.1 ∈ H
    · simp only [if_pos he]
      exact Real.sinh_nonneg_iff.mpr (hlambda e)
    · simp only [if_neg he]
      exact (Real.cosh_pos _).le



noncomputable def nonnegativeParityCurrentKernel
    (lambda : Sym2 V → ℝ) (H : Finset (Sym2 V))
    (m : EdgeCurrent G) : ℝ :=
  ∏ e : G.edgeFinset,
    nonnegativeParityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e)

theorem summable_nonnegativeParityCurrentKernel
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) :
    Summable (nonnegativeParityCurrentKernel G lambda H) := by
  simpa only [nonnegativeParityCurrentKernel,
    nonnegativeFiniteParityKernel] using
      summable_nonnegativeFiniteParityKernel G.edgeFinset lambda hlambda
        (fun e : G.edgeFinset => e.1 ∈ H)

theorem tsum_nonnegativeParityCurrentKernel
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G,
      nonnegativeParityCurrentKernel G lambda H m = 1 := by
  simpa only [nonnegativeParityCurrentKernel,
    nonnegativeFiniteParityKernel] using
      tsum_nonnegativeFiniteParityKernel G.edgeFinset lambda hlambda
        (fun e : G.edgeFinset => e.1 ∈ H)

theorem nonnegativeParityCurrentKernel_eq_zero_of_support_ne
    (lambda : Sym2 V → ℝ) (H : Finset (Sym2 V))
    (hH : H ⊆ G.edgeFinset) (m : EdgeCurrent G)
    (hm : currentParitySupport G m ≠ H) :
    nonnegativeParityCurrentKernel G lambda H m = 0 := by
  have hall : ¬(∀ e : G.edgeFinset,
      if e.1 ∈ H then Odd (m e) else Even (m e)) :=
    fun h => hm ((currentParitySupport_eq_iff G H hH m).mpr h)
  push Not at hall
  obtain ⟨e, he⟩ := hall
  unfold nonnegativeParityCurrentKernel
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  apply nonnegativeParityEdgeKernel_eq_zero_of_parity_ne
  by_cases heH : e.1 ∈ H <;> simpa [heH] using he



theorem weight_eq_nonnegativeParityFiberMass_mul_kernel
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m = H) :
    weight G beta J (ofEdgeFun G m) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H *
        nonnegativeParityCurrentKernel G (fun e => beta * J e) H m := by
  have hall := (currentParitySupport_eq_iff G H hH m).mp hm
  unfold inhomogeneousParityFiberMass nonnegativeParityCurrentKernel
  symm
  calc
    (∏ e : G.edgeFinset,
        if e.1 ∈ H then Real.sinh (beta * J e.1)
        else Real.cosh (beta * J e.1)) *
          ∏ e : G.edgeFinset,
            nonnegativeParityEdgeKernel
              (beta * J e.1) (e.1 ∈ H) (m e) =
        ∏ e : G.edgeFinset,
          (if e.1 ∈ H then Real.sinh (beta * J e.1)
            else Real.cosh (beta * J e.1)) *
              nonnegativeParityEdgeKernel
                (beta * J e.1) (e.1 ∈ H) (m e) := by
      exact (Finset.prod_mul_distrib (s := Finset.univ)).symm
    _ = ∏ e : G.edgeFinset,
        (beta * J e.1) ^ m e / (m e).factorial := by
      apply Fintype.prod_congr
      intro e
      by_cases heH : e.1 ∈ H
      · simpa [heH] using
          parityFiberMass_mul_nonnegativeParityEdgeKernel
            (mul_nonneg hbeta.le (hJ e)) true (m e)
            (by simpa [heH] using hall e)
      · simpa [heH] using
          parityFiberMass_mul_nonnegativeParityEdgeKernel
            (mul_nonneg hbeta.le (hJ e)) false (m e)
            (by simpa [heH] using hall e)
    _ = weight G beta J (ofEdgeFun G m) :=
      (weight_ofEdgeFun G beta J m).symm

theorem summable_fixedParity_weight_nonnegative
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    Summable (fun m : EdgeCurrent G =>
      if currentParitySupport G m = H then
        weight G beta J (ofEdgeFun G m) else 0) := by
  let lambda : Sym2 V → ℝ := fun e => beta * J e
  let c := inhomogeneousParityFiberMass G lambda H
  let kernel := nonnegativeParityCurrentKernel G lambda H
  have hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1 := fun e =>
    mul_nonneg hbeta.le (hJ e)
  have hpoint (m : EdgeCurrent G) :
      (if currentParitySupport G m = H then
          weight G beta J (ofEdgeFun G m) else 0) = c * kernel m := by
    by_cases hm : currentParitySupport G m = H
    · rw [if_pos hm]
      exact weight_eq_nonnegativeParityFiberMass_mul_kernel
        G beta hbeta J hJ H hH m hm
    · rw [if_neg hm]
      have hk : kernel m = 0 :=
        nonnegativeParityCurrentKernel_eq_zero_of_support_ne
          G lambda H hH m hm
      rw [hk, mul_zero]
  exact ((summable_nonnegativeParityCurrentKernel G lambda hlambda H).mul_left c).congr
    (fun m => (hpoint m).symm)



theorem fixedParity_weight_tsum_nonnegative
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        weight G beta J (ofEdgeFun G m) else 0) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
  let lambda : Sym2 V → ℝ := fun e => beta * J e
  have hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1 := fun e =>
    mul_nonneg hbeta.le (hJ e)
  let c := inhomogeneousParityFiberMass G lambda H
  let kernel := nonnegativeParityCurrentKernel G lambda H
  have hpoint (m : EdgeCurrent G) :
      (if currentParitySupport G m = H then
          weight G beta J (ofEdgeFun G m) else 0) = c * kernel m := by
    by_cases hm : currentParitySupport G m = H
    · rw [if_pos hm]
      exact weight_eq_nonnegativeParityFiberMass_mul_kernel
        G beta hbeta J hJ H hH m hm
    · rw [if_neg hm]
      have hk : kernel m = 0 :=
        nonnegativeParityCurrentKernel_eq_zero_of_support_ne
          G lambda H hH m hm
      rw [hk, mul_zero]
  rw [tsum_congr hpoint, tsum_mul_left,
    tsum_nonnegativeParityCurrentKernel G lambda hlambda H, mul_one]



noncomputable def sourcelessNonnegativeParityPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    PMF (Finset (Sym2 V)) :=
  PMF.map (currentParitySupport G)
    (sourcelessCurrentPMF G beta J hbeta hJ)



theorem sourcelessNonnegativeParityPMF_apply
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (H : Finset (Sym2 V)) :
    sourcelessNonnegativeParityPMF G beta J hbeta.le hJ H =
      if _hH : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
        ENNReal.ofReal
            (inhomogeneousParityFiberMass G (fun e => beta * J e) H) *
          (ENNReal.ofReal (currentSum G beta J ∅))⁻¹
      else 0 := by
  classical
  rw [sourcelessNonnegativeParityPMF, PMF.map_apply]
  by_cases hvalid : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H
  · rw [dif_pos hvalid]
    have hsources (m : EdgeCurrent G)
        (hm : currentParitySupport G m = H) :
        sources G (ofEdgeFun G m) = ∅ := by
      apply (sources_empty_iff_currentParitySupport_even G m).2
      simpa [hm] using hvalid.2
    let f : EdgeCurrent G → ℝ := fun m =>
      if H = currentParitySupport G m then
        weight G beta J (ofEdgeFun G m) else 0
    have hfnonneg : ∀ m, 0 ≤ f m := by
      intro m
      unfold f
      split
      · unfold weight
        exact Finset.prod_nonneg fun e _ =>
          div_nonneg (pow_nonneg (mul_nonneg hbeta.le (hJ e)) _)
            (Nat.cast_nonneg _)
      · exact le_rfl
    have hfsummable : Summable f := by
      simpa only [f, eq_comm] using
        summable_fixedParity_weight_nonnegative G beta hbeta J
          (fun e => hJ e.1) H hvalid.1
    have hftsum : ∑' m, f m =
        inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
      simpa only [f, eq_comm] using
        fixedParity_weight_tsum_nonnegative G beta hbeta J
          (fun e => hJ e.1) H hvalid.1
    calc
      _ = ∑' m : EdgeCurrent G,
            ENNReal.ofReal (f m) *
              (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        apply tsum_congr
        intro m
        by_cases hm : H = currentParitySupport G m
        · simp [f, hm, sourcelessCurrentPMF, currentPMF_apply,
            currentRawMass, hsources m hm.symm]
        · simp [f, hm]
      _ = (∑' m : EdgeCurrent G, ENNReal.ofReal (f m)) *
            (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        rw [ENNReal.tsum_mul_right]
      _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) *
            (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        rw [ENNReal.ofReal_tsum_of_nonneg hfnonneg hfsummable]
      _ = _ := by rw [hftsum]
  · rw [dif_neg hvalid]
    rw [ENNReal.tsum_eq_zero]
    intro m
    by_cases hm : currentParitySupport G m = H
    · have hsub := currentParitySupport_subset G m
      have hnotEven : ¬ IsEvenSubgraph H := by
        intro heven
        exact hvalid ⟨hm ▸ hsub, heven⟩
      have hsrc : sources G (ofEdgeFun G m) ≠ ∅ := by
        intro hs
        apply hnotEven
        rw [← hm]
        exact (sources_empty_iff_currentParitySupport_even G m).1 hs
      simp [hm, sourcelessCurrentPMF, currentPMF_apply,
        currentRawMass, hsrc]
    · simp [Ne.symm hm]



theorem sourcelessCurrentPMF_apply_eq_nonnegativeParity_factor
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (m : EdgeCurrent G) :
    sourcelessCurrentPMF G beta J hbeta.le hJ m =
      sourcelessNonnegativeParityPMF G beta J hbeta.le hJ
          (currentParitySupport G m) *
        nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
  let H := currentParitySupport G m
  have hH : H ⊆ G.edgeFinset := currentParitySupport_subset G m
  rw [sourcelessNonnegativeParityPMF_apply G beta hbeta J hJ H,
    nonnegativeFiniteParityPMF_apply]
  rw [sourcelessCurrentPMF, currentPMF_apply]
  by_cases hsrc : sources G (ofEdgeFun G m) = ∅
  · have heven : IsEvenSubgraph H :=
      (sources_empty_iff_currentParitySupport_even G m).1 hsrc
    rw [dif_pos ⟨hH, heven⟩]
    have hfactor := weight_eq_nonnegativeParityFiberMass_mul_kernel
      G beta hbeta J (fun e => hJ e.1) H hH m rfl
    have hfiber := inhomogeneousParityFiberMass_nonneg G
      (fun e => beta * J e) (fun e => mul_nonneg hbeta.le (hJ e.1)) H
    have hkernel : nonnegativeParityCurrentKernel G
          (fun e => beta * J e) H m =
        nonnegativeFiniteParityKernel G.edgeFinset (fun e => beta * J e)
          (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
      simp only [nonnegativeParityCurrentKernel,
        nonnegativeFiniteParityKernel, H]
    rw [currentRawMass, if_pos hsrc, hfactor,
      ENNReal.ofReal_mul hfiber]
    change ENNReal.ofReal
          (inhomogeneousParityFiberMass G (fun e => beta * J e) H) *
        ENNReal.ofReal (nonnegativeParityCurrentKernel G
          (fun e => beta * J e) H m) *
          (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ = _
    rw [hkernel]
    ac_rfl
  · have hneven : ¬ IsEvenSubgraph H := by
      intro heven
      exact hsrc ((sources_empty_iff_currentParitySupport_even G m).2 heven)
    rw [dif_neg (fun h => hneven h.2)]
    simp [currentRawMass, hsrc]



theorem sourcelessCurrentPMF_eq_nonnegativeParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) :
    sourcelessCurrentPMF G beta J hbeta.le hJ =
      (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).bind
        (fun H => nonnegativeFiniteParityPMF G.edgeFinset
          (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ H)) := by
  apply PMF.ext
  intro m
  rw [PMF.bind_apply,
    sourcelessCurrentPMF_apply_eq_nonnegativeParity_factor
      G beta hbeta J hJ m]
  symm
  rw [tsum_eq_single (currentParitySupport G m)]
  intro H hne
  by_cases hH : H ⊆ G.edgeFinset
  · have hk : nonnegativeParityCurrentKernel G
        (fun e => beta * J e) H m = 0 :=
      nonnegativeParityCurrentKernel_eq_zero_of_support_ne
        G (fun e => beta * J e) H hH m (Ne.symm hne)
    have hk' : nonnegativeFiniteParityKernel G.edgeFinset
        (fun e => beta * J e) (fun e : G.edgeFinset => e.1 ∈ H) m = 0 := by
      simpa only [nonnegativeFiniteParityKernel,
        nonnegativeParityCurrentKernel] using hk
    rw [nonnegativeFiniteParityPMF_apply]
    rw [hk']
    simp
  · rw [sourcelessNonnegativeParityPMF_apply G beta hbeta J hJ H]
    simp [hH]



theorem sourcelessCurrentPMF_map_eq_nonnegativeParity_bind
    {A : Type*} (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (f : EdgeCurrent G → A) :
    PMF.map f (sourcelessCurrentPMF G beta J hbeta.le hJ) =
      (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).bind
        (fun H => PMF.map f (nonnegativeFiniteParityPMF G.edgeFinset
          (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ H))) := by
  rw [sourcelessCurrentPMF_eq_nonnegativeParity_bind G beta hbeta J hJ,
    PMF.map_bind]

end Graph

end StatMech.FrontierB
