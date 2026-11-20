/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.FiniteCurrentConditional

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem summable_parityCurrentKernel (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) :
    Summable (parityCurrentKernel G beta H) := by
  let g : Sym2 V → ℕ → ℝ := fun e k =>
    parityEdgeKernel beta (e ∈ H) k
  have hg : ∀ e, Summable (g e) := fun e =>
    summable_parityEdgeKernel beta (e ∈ H)
  have hgnn : ∀ e k, 0 ≤ g e k := fun e k =>
    parityEdgeKernel_nonneg beta hbeta (e ∈ H) k
  exact (prod_tsum_fubini g hg hgnn G.edgeFinset).1.congr (fun m => rfl)

theorem tsum_ofReal_parityCurrentKernel (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G, ENNReal.ofReal (parityCurrentKernel G beta H m) = 1 := by
  have hnonneg : ∀ m : EdgeCurrent G,
      0 ≤ parityCurrentKernel G beta H m := by
    intro m
    unfold parityCurrentKernel
    exact Finset.prod_nonneg fun e _ =>
      parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) (m e)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_parityCurrentKernel G beta hbeta H),
    tsum_parityCurrentKernel G beta hbeta H]
  simp

noncomputable def parityCurrentPMF (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) : PMF (EdgeCurrent G) :=
  PMF.normalize (fun m => ENNReal.ofReal (parityCurrentKernel G beta H m))
    (by rw [tsum_ofReal_parityCurrentKernel G beta hbeta H]; exact one_ne_zero)
    (by rw [tsum_ofReal_parityCurrentKernel G beta hbeta H]; exact ENNReal.one_ne_top)

theorem parityCurrentPMF_apply (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (m : EdgeCurrent G) :
    parityCurrentPMF G beta hbeta H m =
      ENNReal.ofReal (parityCurrentKernel G beta H m) := by
  rw [parityCurrentPMF, PMF.normalize_apply,
    tsum_ofReal_parityCurrentKernel G beta hbeta H]
  simp

theorem parityCurrentKernel_eq_zero_of_support_ne
    (beta : ℝ) (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m ≠ H) :
    parityCurrentKernel G beta H m = 0 := by
  have hall : ¬ ∀ e : G.edgeFinset,
      if e.1 ∈ H then Odd (m e) else Even (m e) :=
    fun h => hm ((currentParitySupport_eq_iff G H hH m).mpr h)
  push Not at hall
  obtain ⟨e, he⟩ := hall
  unfold parityCurrentKernel
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  by_cases heH : e.1 ∈ H
  · have hnot : ¬ Odd (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]
  · have hnot : ¬ Even (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]

theorem sourcelessCurrentPMF_apply_eq_parity_factor
    (beta : ℝ) (hbeta : 0 < beta) (m : EdgeCurrent G) :
    sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) m =
      freeParityPMF G beta hbeta.le (currentParitySupport G m) *
        parityCurrentPMF G beta hbeta (currentParitySupport G m) m := by
  let H := currentParitySupport G m
  have hH : H ⊆ G.edgeFinset := currentParitySupport_subset G m
  rw [freeParityPMF_apply, parityCurrentPMF_apply]
  simp only [sourcelessCurrentPMF]
  rw [currentPMF_apply]
  by_cases hsrc : sources G (ofEdgeFun G m) = ∅
  · have heven : IsEvenSubgraph H :=
      (sources_empty_iff_currentParitySupport_even G m).1 hsrc
    have hkernel : 0 ≤ parityCurrentKernel G beta H m := by
      unfold parityCurrentKernel
      exact Finset.prod_nonneg fun e _ =>
        parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) (m e)
    have htanh : 0 ≤ Real.tanh beta ^ H.card :=
      pow_nonneg (tanh_nonneg_of_nonneg hbeta.le) _
    have hcosh : 0 ≤ Real.cosh beta ^ G.edgeFinset.card := by positivity
    have hw : ENNReal.ofReal
          (weight G beta (fun _ => 1) (ofEdgeFun G m)) =
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
          ENNReal.ofReal (Real.tanh beta ^ H.card) *
            ENNReal.ofReal (parityCurrentKernel G beta H m) := by
      rw [weight_eq_parityFiberMass_mul_kernel G beta hbeta H hH m rfl,
        parityFiberMass_closed G beta hbeta.le H hH,
        ENNReal.ofReal_mul (mul_nonneg hcosh htanh),
        ENNReal.ofReal_mul hcosh]
    have hZ : ENNReal.ofReal (currentSum G beta (fun _ => 1) ∅) =
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
          ENNReal.ofReal (freeParityPartition G beta) := by
      rw [currentSum_unit_eq_parityPartition G beta,
        ENNReal.ofReal_mul hcosh]
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card)
    let t : ℝ≥0∞ := ENNReal.ofReal (Real.tanh beta ^ H.card)
    let p : ℝ≥0∞ := ENNReal.ofReal (freeParityPartition G beta)
    let k : ℝ≥0∞ := ENNReal.ofReal (parityCurrentKernel G beta H m)
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    simp only [currentRawMass, hsrc, if_true, freeParityRawMass,
      hH, heven, and_self, H]
    rw [hw, hZ]
    change c * t * k * (c * p)⁻¹ = t * p⁻¹ * k
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
    calc
      c * t * k * (c⁻¹ * p⁻¹) = (c * c⁻¹) * (t * p⁻¹ * k) := by
        ac_rfl
      _ = t * p⁻¹ * k := by rw [ENNReal.mul_inv_cancel hc0 hcTop, one_mul]
  · have hneven : ¬ IsEvenSubgraph H := by
      intro heven
      exact hsrc ((sources_empty_iff_currentParitySupport_even G m).2 heven)
    have hcond : ¬ (currentParitySupport G m ⊆ G.edgeFinset ∧
        IsEvenSubgraph (currentParitySupport G m)) := by
      intro h
      exact hneven (by simpa [H] using h.2)
    simp [currentRawMass, hsrc, freeParityRawMass, hcond]

theorem sourcelessCurrentPMF_eq_parity_bind
    (beta : ℝ) (hbeta : 0 < beta) :
    sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) =
      (freeParityPMF G beta hbeta.le).bind
        (parityCurrentPMF G beta hbeta) := by
  apply PMF.ext
  intro m
  rw [PMF.bind_apply,
    sourcelessCurrentPMF_apply_eq_parity_factor G beta hbeta m]
  symm
  rw [tsum_eq_single (currentParitySupport G m)]
  intro H hne
  by_cases hH : H ⊆ G.edgeFinset
  · have hk : parityCurrentKernel G beta H m = 0 :=
      parityCurrentKernel_eq_zero_of_support_ne G beta H hH m (Ne.symm hne)
    rw [parityCurrentPMF_apply]
    simp [hk]
  · rw [freeParityPMF_apply]
    simp [freeParityRawMass, hH]

theorem sourcelessCurrentPMF_map_eq_parity_bind
    {A : Type*} (beta : ℝ) (hbeta : 0 < beta)
    (f : EdgeCurrent G → A) :
    PMF.map f (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one)) =
      (freeParityPMF G beta hbeta.le).bind
        (fun H => PMF.map f (parityCurrentPMF G beta hbeta H)) := by
  rw [sourcelessCurrentPMF_eq_parity_bind G beta hbeta, PMF.map_bind]

theorem sourcelessCurrentFiniteMarginal_eq_parity_bind
    (beta : ℝ) (hbeta : 0 < beta) (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
          (fun _ => zero_le_one)) =
      (freeParityPMF G beta hbeta.le).bind
        (fun H => PMF.map (restrictCurrent S)
          (parityCurrentPMF G beta hbeta H)) :=
  sourcelessCurrentPMF_map_eq_parity_bind G beta hbeta (restrictCurrent S)

noncomputable def finiteParityKernel {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (odd : ↑S → Bool) (a : ↑S → ℕ) : ℝ :=
  ∏ i, parityEdgeKernel beta (odd i) (a i)

theorem summable_finiteParityKernel {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta) (odd : ↑S → Bool) :
    Summable (finiteParityKernel S beta odd) := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then parityEdgeKernel beta (odd ⟨e, he⟩) k
    else parityEdgeKernel beta false k
  have hg : ∀ i, Summable (g i) := by
    intro i
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : ∀ i k, 0 ≤ g i k := by
    intro i k
    unfold g
    split <;> apply parityEdgeKernel_nonneg beta hbeta
  exact (prod_tsum_fubini g hg hgnn S).1.congr (fun m => by
    unfold finiteParityKernel
    apply Fintype.prod_congr
    intro i
    simp [g])

theorem tsum_ofReal_finiteParityKernel {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta) (odd : ↑S → Bool) :
    ∑' a : ↑S → ℕ, ENNReal.ofReal (finiteParityKernel S beta odd a) = 1 := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then parityEdgeKernel beta (odd ⟨e, he⟩) k
    else parityEdgeKernel beta false k
  have hnonneg : ∀ a : ↑S → ℕ, 0 ≤ finiteParityKernel S beta odd a := by
    intro a
    exact Finset.prod_nonneg fun i _ =>
      parityEdgeKernel_nonneg beta hbeta (odd i) (a i)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_finiteParityKernel S beta hbeta odd)]
  have hg : ∀ i, Summable (g i) := by
    intro i
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : ∀ i k, 0 ≤ g i k := by
    intro i k
    unfold g
    split <;> apply parityEdgeKernel_nonneg beta hbeta
  rw [show (∑' a : ↑S → ℕ, finiteParityKernel S beta odd a) =
      ∑' a : ↑S → ℕ, ∏ i : ↑S, g i.1 (a i) by
    apply tsum_congr
    intro a
    simp [finiteParityKernel, g]]
  rw [← (prod_tsum_fubini g hg hgnn S).2]
  rw [← ENNReal.ofReal_one]
  apply congrArg ENNReal.ofReal
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_parityEdgeKernel beta hbeta (odd ⟨e, he⟩)

noncomputable def finiteParityPMF {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (odd : ↑S → Bool) : PMF (↑S → ℕ) :=
  PMF.normalize (fun a => ENNReal.ofReal (finiteParityKernel S beta odd a))
    (by rw [tsum_ofReal_finiteParityKernel S beta hbeta odd]; exact one_ne_zero)
    (by rw [tsum_ofReal_finiteParityKernel S beta hbeta odd]; exact ENNReal.one_ne_top)

theorem finiteParityPMF_apply {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (odd : ↑S → Bool) (a : ↑S → ℕ) :
    finiteParityPMF S beta hbeta odd a =
      ENNReal.ofReal (finiteParityKernel S beta odd a) := by
  rw [finiteParityPMF, PMF.normalize_apply,
    tsum_ofReal_finiteParityKernel S beta hbeta odd]
  simp

theorem tsum_ofReal_fintypeParityKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (beta : ℝ) (hbeta : 0 < beta) (odd : I → Bool) :
    ∑' a : I → ℕ,
      ENNReal.ofReal (∏ i, parityEdgeKernel beta (odd i) (a i)) = 1 := by
  let U : Finset I := Finset.univ
  let e : ↑U ≃ I := Equiv.ofBijective Subtype.val ⟨fun _ _ h => Subtype.ext h,
    fun i => ⟨⟨i, Finset.mem_univ i⟩, rfl⟩⟩
  let E : (↑U → ℕ) ≃ (I → ℕ) :=
    Equiv.arrowCongr e (Equiv.refl ℕ)
  rw [← E.tsum_eq]
  have hnorm := tsum_ofReal_finiteParityKernel U beta hbeta
    (fun i : ↑U => odd i.1)
  rw [← hnorm]
  apply tsum_congr
  intro a
  congr 1
  unfold finiteParityKernel
  symm
  apply Fintype.prod_equiv e
  intro i
  simp [E, e, U]

section Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private noncomputable def splitEdgeCurrent (S : Finset G.edgeFinset) :
    EdgeCurrent G ≃ ((↑S → ℕ) × ({e : G.edgeFinset // e ∉ S} → ℕ)) :=
  Equiv.piEquivPiSubtypeProd (fun e => e ∈ S) (fun _ => ℕ)

private theorem splitEdgeCurrent_fst (S : Finset G.edgeFinset)
    (m : EdgeCurrent G) :
    (splitEdgeCurrent G S m).1 = restrictCurrent S m := by
  funext e
  rfl

private theorem restrictCurrent_splitEdgeCurrent_symm
    (S : Finset G.edgeFinset) (a : ↑S → ℕ)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) :
    restrictCurrent S ((splitEdgeCurrent G S).symm (a, b)) = a := by
  funext e
  change (Equiv.piEquivPiSubtypeProd (fun x : G.edgeFinset => x ∈ S)
    (fun _ => ℕ)).symm (a, b) e.1 = a e
  rw [Equiv.piEquivPiSubtypeProd_symm_apply]
  simp [e.2]

private noncomputable def complementParityKernel
    (beta : ℝ) (H : Finset (Sym2 V)) (S : Finset G.edgeFinset)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) : ℝ :=
  ∏ e, parityEdgeKernel beta (e.1.1 ∈ H) (b e)

private theorem parityCurrentKernel_split
    (beta : ℝ) (H : Finset (Sym2 V)) (S : Finset G.edgeFinset)
    (a : ↑S → ℕ) (b : {e : G.edgeFinset // e ∉ S} → ℕ) :
    parityCurrentKernel G beta H ((splitEdgeCurrent G S).symm (a, b)) =
      finiteParityKernel S beta (fun e : ↑S => e.1.1 ∈ H) a *
        complementParityKernel G beta H S b := by
  unfold parityCurrentKernel finiteParityKernel complementParityKernel
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset G.edgeFinset) (fun e => e ∈ S)]
  congr 1
  · rw [Finset.prod_subtype (p := fun e => e ∈ S)
      (Finset.univ.filter (fun e => e ∈ S))
      (fun e => by simp)]
    apply Fintype.prod_congr
    intro e
    rw [splitEdgeCurrent, Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [e.2]
  · rw [Finset.prod_subtype (p := fun e => e ∉ S)
      (Finset.univ.filter (fun e => e ∉ S))
      (fun e => by simp)]
    apply Fintype.prod_congr
    intro e
    rw [splitEdgeCurrent, Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [e.2]

private theorem tsum_ofReal_complementParityKernel
    (beta : ℝ) (hbeta : 0 < beta) (H : Finset (Sym2 V))
    (S : Finset G.edgeFinset) :
    ∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
      ENNReal.ofReal (complementParityKernel G beta H S b) = 1 := by
  exact tsum_ofReal_fintypeParityKernel beta hbeta
    (fun e : {e : G.edgeFinset // e ∉ S} => e.1.1 ∈ H)

theorem parityCurrentPMF_map_restrictCurrent
    (beta : ℝ) (hbeta : 0 < beta) (H : Finset (Sym2 V))
    (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S) (parityCurrentPMF G beta hbeta H) =
      finiteParityPMF S beta hbeta (fun e : ↑S => e.1.1 ∈ H) := by
  apply PMF.ext
  intro a
  rw [PMF.map_apply, finiteParityPMF_apply]
  simp_rw [parityCurrentPMF_apply]
  let E := splitEdgeCurrent G S
  rw [← E.symm.tsum_eq]
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single a]
  · simp_rw [show ∀ b, restrictCurrent S (E.symm (a, b)) = a by
      intro b
      exact restrictCurrent_splitEdgeCurrent_symm G S a b]
    simp only [ite_true]
    rw [show (∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
        ENNReal.ofReal
          (parityCurrentKernel G beta H ((splitEdgeCurrent G S).symm (a, b)))) =
        ENNReal.ofReal (finiteParityKernel S beta (fun e : ↑S => e.1.1 ∈ H) a) *
          ∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
            ENNReal.ofReal (complementParityKernel G beta H S b) by
      simp_rw [parityCurrentKernel_split G beta H S a]
      have hlocal : 0 ≤
          finiteParityKernel S beta (fun e : ↑S => e.1.1 ∈ H) a :=
        Finset.prod_nonneg fun i _ =>
          parityEdgeKernel_nonneg beta hbeta (i.1.1 ∈ H) (a i)
      simp_rw [ENNReal.ofReal_mul hlocal]
      rw [ENNReal.tsum_mul_left]]
    rw [tsum_ofReal_complementParityKernel G beta hbeta H S, mul_one]
  · intro a' hne
    have hrestrict : ∀ b, restrictCurrent S (E.symm (a', b)) = a' := by
      intro b
      exact restrictCurrent_splitEdgeCurrent_symm G S a' b
    simp_rw [hrestrict]
    simp [Ne.symm hne]

def restrictParity (S : Finset G.edgeFinset) (H : Finset (Sym2 V)) :
    ↑S → Bool := fun e => decide (e.1.1 ∈ H)

theorem sourcelessCurrentFiniteMarginal_eq_localParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
          (fun _ => zero_le_one)) =
      (PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le)).bind
        (finiteParityPMF S beta hbeta) := by
  rw [sourcelessCurrentFiniteMarginal_eq_parity_bind G beta hbeta S]
  rw [PMF.bind_map]
  congr 1
  funext H
  rw [parityCurrentPMF_map_restrictCurrent G beta hbeta H S]
  rfl

end Ambient


end StatMech.FrontierB
