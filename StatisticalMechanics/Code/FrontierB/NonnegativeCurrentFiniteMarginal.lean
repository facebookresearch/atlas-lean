/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.NonnegativeCurrentConditionalPMF










open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private noncomputable def nonnegativeSplitEdgeCurrent
    (S : Finset G.edgeFinset) :
    EdgeCurrent G ≃ ((↑S → ℕ) × ({e : G.edgeFinset // e ∉ S} → ℕ)) :=
  Equiv.piEquivPiSubtypeProd (fun e => e ∈ S) (fun _ => ℕ)

private theorem restrictCurrent_nonnegativeSplitEdgeCurrent_symm
    (S : Finset G.edgeFinset) (a : ↑S → ℕ)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) :
    restrictCurrent S
        ((nonnegativeSplitEdgeCurrent G S).symm (a, b)) = a := by
  funext e
  change (Equiv.piEquivPiSubtypeProd (fun x : G.edgeFinset => x ∈ S)
    (fun _ => ℕ)).symm (a, b) e.1 = a e
  rw [Equiv.piEquivPiSubtypeProd_symm_apply]
  simp [e.2]

private noncomputable def nonnegativeComplementParityKernel
    (lambda : Sym2 V → ℝ) (H : Finset (Sym2 V))
    (S : Finset G.edgeFinset)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) : ℝ :=
  ∏ e, nonnegativeParityEdgeKernel
    (lambda e.1.1) (e.1.1 ∈ H) (b e)

private theorem nonnegativeParityCurrentKernel_split
    (lambda : Sym2 V → ℝ) (H : Finset (Sym2 V))
    (S : Finset G.edgeFinset) (a : ↑S → ℕ)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) :
    nonnegativeParityCurrentKernel G lambda H
        ((nonnegativeSplitEdgeCurrent G S).symm (a, b)) =
      nonnegativeFiniteParityKernel S
          (fun e : G.edgeFinset => lambda e.1)
          (fun e : ↑S => e.1.1 ∈ H) a *
        nonnegativeComplementParityKernel G lambda H S b := by
  unfold nonnegativeParityCurrentKernel nonnegativeFiniteParityKernel
    nonnegativeComplementParityKernel
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset G.edgeFinset) (fun e => e ∈ S)]
  congr 1
  · rw [Finset.prod_subtype (p := fun e => e ∈ S)
      (Finset.univ.filter (fun e => e ∈ S)) (fun e => by simp)]
    apply Fintype.prod_congr
    intro e
    rw [nonnegativeSplitEdgeCurrent,
      Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [e.2]
  · rw [Finset.prod_subtype (p := fun e => e ∉ S)
      (Finset.univ.filter (fun e => e ∉ S)) (fun e => by simp)]
    apply Fintype.prod_congr
    intro e
    rw [nonnegativeSplitEdgeCurrent,
      Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [e.2]

private theorem tsum_ofReal_fintypeNonnegativeParityKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (lambda : I → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)
    (odd : I → Bool) :
    ∑' a : I → ℕ,
      ENNReal.ofReal
        (∏ i, nonnegativeParityEdgeKernel (lambda i) (odd i) (a i)) = 1 := by
  let U : Finset I := Finset.univ
  let e : ↑U ≃ I := Equiv.ofBijective Subtype.val
    ⟨fun _ _ h => Subtype.ext h,
      fun i => ⟨⟨i, Finset.mem_univ i⟩, rfl⟩⟩
  let E : (↑U → ℕ) ≃ (I → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
  rw [← E.tsum_eq]
  have hnorm := tsum_ofReal_nonnegativeFiniteParityKernel U lambda
    (fun i : ↑U => hlambda i.1) (fun i : ↑U => odd i.1)
  rw [← hnorm]
  apply tsum_congr
  intro a
  congr 1
  unfold nonnegativeFiniteParityKernel
  symm
  apply Fintype.prod_equiv e
  intro i
  simp [E, e, U]

private theorem tsum_ofReal_nonnegativeComplementParityKernel
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) (S : Finset G.edgeFinset) :
    ∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
      ENNReal.ofReal
        (nonnegativeComplementParityKernel G lambda H S b) = 1 := by
  exact tsum_ofReal_fintypeNonnegativeParityKernel
    (fun e : {e : G.edgeFinset // e ∉ S} => lambda e.1.1)
    (fun e => hlambda e.1)
    (fun e : {e : G.edgeFinset // e ∉ S} => e.1.1 ∈ H)



theorem nonnegativeParityPMF_map_restrictCurrent
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (nonnegativeFiniteParityPMF G.edgeFinset lambda hlambda
          (fun e : G.edgeFinset => e.1 ∈ H)) =
      nonnegativeFiniteParityPMF S
        (fun e : G.edgeFinset => lambda e.1)
        (fun e : ↑S => hlambda e.1)
        (fun e : ↑S => e.1.1 ∈ H) := by
  apply PMF.ext
  intro a
  rw [PMF.map_apply, nonnegativeFiniteParityPMF_apply]
  simp_rw [nonnegativeFiniteParityPMF_apply]
  let E := nonnegativeSplitEdgeCurrent G S
  rw [← E.symm.tsum_eq, ENNReal.tsum_prod', tsum_eq_single a]
  · simp_rw [show ∀ b, restrictCurrent S (E.symm (a, b)) = a by
      intro b
      exact restrictCurrent_nonnegativeSplitEdgeCurrent_symm G S a b]
    simp only [ite_true]
    rw [show (∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
        ENNReal.ofReal
          (nonnegativeFiniteParityKernel G.edgeFinset lambda
            (fun e : G.edgeFinset => e.1 ∈ H)
            ((nonnegativeSplitEdgeCurrent G S).symm (a, b)))) =
        ENNReal.ofReal (nonnegativeFiniteParityKernel S
          (fun e : G.edgeFinset => lambda e.1)
          (fun e : ↑S => e.1.1 ∈ H) a) *
          ∑' b : {e : G.edgeFinset // e ∉ S} → ℕ,
            ENNReal.ofReal
              (nonnegativeComplementParityKernel G lambda H S b) by
      simp_rw [show ∀ b,
          nonnegativeFiniteParityKernel G.edgeFinset lambda
              (fun e : G.edgeFinset => e.1 ∈ H)
              ((nonnegativeSplitEdgeCurrent G S).symm (a, b)) =
            nonnegativeParityCurrentKernel G lambda H
              ((nonnegativeSplitEdgeCurrent G S).symm (a, b)) by
        intro b
        rfl]
      simp_rw [nonnegativeParityCurrentKernel_split G lambda H S a]
      have hlocal : 0 ≤ nonnegativeFiniteParityKernel S
          (fun e : G.edgeFinset => lambda e.1)
          (fun e : ↑S => e.1.1 ∈ H) a :=
        Finset.prod_nonneg fun i _ =>
          nonnegativeParityEdgeKernel_nonneg (hlambda i.1) _ _
      simp_rw [ENNReal.ofReal_mul hlocal]
      rw [ENNReal.tsum_mul_left]]
    rw [tsum_ofReal_nonnegativeComplementParityKernel
      G lambda hlambda H S, mul_one]
  · intro a' hne
    have hrestrict : ∀ b, restrictCurrent S (E.symm (a', b)) = a' := by
      intro b
      exact restrictCurrent_nonnegativeSplitEdgeCurrent_symm G S a' b
    simp_rw [hrestrict]
    simp [Ne.symm hne]



theorem sourcelessCurrentFiniteMarginal_eq_nonnegativeParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (sourcelessCurrentPMF G beta J hbeta.le hJ) =
      (PMF.map (restrictParity G S)
        (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ)).bind
          (nonnegativeFiniteParityPMF S
            (fun e : G.edgeFinset => beta * J e.1)
            (fun e : ↑S => mul_nonneg hbeta.le (hJ e.1.1))) := by
  rw [sourcelessCurrentPMF_map_eq_nonnegativeParity_bind
    G beta hbeta J hJ (restrictCurrent S), PMF.bind_map]
  congr 1
  funext H
  rw [nonnegativeParityPMF_map_restrictCurrent G
    (fun e => beta * J e)
    (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1)) H S]
  rfl

end StatMech.FrontierB
