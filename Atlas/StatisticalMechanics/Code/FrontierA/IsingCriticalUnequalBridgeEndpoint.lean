/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalSurfaceBulk









namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section


theorem unequalReplicaExp2_factor
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (f : ConfigSpace V -> Real) (g : ConfigSpace W -> Real) :
    unequalReplicaExp2 G H J hf hg (fun a b => f a * g b) =
      expJ G.edgeFinset (fun _ => J) hf f *
        expJ H.edgeFinset (fun _ => J) hg g := by
  unfold unequalReplicaExp2 expJ
  have hZG : ZJ G.edgeFinset (fun _ => J) hf ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  have hZH : ZJ H.edgeFinset (fun _ => J) hg ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  field_simp [hZG, hZH]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring



theorem unequalReplicaExp2_crossBond
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (x : V) (y : W) :
    unequalReplicaExp2 G H J hf hg (fun a b =>
        bond (isingSumConfigEquiv.symm (a, b))
          s(Sum.inl x, Sum.inr y)) =
      expJ G.edgeFinset (fun _ => J) hf (fun a => spin a x) *
        expJ H.edgeFinset (fun _ => J) hg (fun b => spin b y) := by
  rw [show (fun a b =>
      bond (isingSumConfigEquiv.symm (a, b))
        s(Sum.inl x, Sum.inr y)) =
      (fun a b => spin a x * spin b y) by
    funext a b
    rw [bond_mk, spin_isingSumConfigEquiv_symm_inl,
      spin_isingSumConfigEquiv_symm_inr]]
  exact unequalReplicaExp2_factor G H J hf hg
    (fun a => spin a x) (fun b => spin b y)


theorem unequalReplicaExp2_finset_sum
    {V W I : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (S : Finset I) (F : I -> ConfigSpace V -> ConfigSpace W -> Real) :
    unequalReplicaExp2 G H J hf hg (fun a b =>
        ∑ i ∈ S, F i a b) =
      ∑ i ∈ S, unequalReplicaExp2 G H J hf hg (F i) := by
  unfold unequalReplicaExp2
  rw [← Finset.sum_div]
  congr 1
  calc
    (∑ a, ∑ b,
        wJ G.edgeFinset (fun _ => J) hf a *
          wJ H.edgeFinset (fun _ => J) hg b * ∑ i ∈ S, F i a b) =
        ∑ a, ∑ b, ∑ i ∈ S,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b * F i a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
    _ = ∑ a, ∑ i ∈ S, ∑ b,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b * F i a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, ∑ a, ∑ b,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b * F i a b := by
      rw [Finset.sum_comm]


@[simp] theorem unequalReplicaBridgeMoment_zero
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) :
    unequalReplicaBridgeMoment G H K J hf hg 0 = 1 := by
  unfold unequalReplicaBridgeMoment
  simp only [zero_mul, Real.exp_zero]
  have hfactor := unequalReplicaExp2_factor G H J hf hg
    (fun _ => (1 : Real)) (fun _ => (1 : Real))
  unfold unequalReplicaExp2 at hfactor
  simpa [expJ_one] using hfactor



theorem unequalReplicaBridgeMean_zero
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) :
    unequalReplicaBridgeMean G H K J hf hg 0 =
      unequalReplicaExp2 G H J hf hg
        (unequalReplicaBridgeInteraction G H K) := by
  unfold unequalReplicaBridgeMean
  rw [unequalReplicaBridgeMoment_zero]
  simp only [zero_mul, Real.exp_zero, mul_one, div_one]
  unfold unequalReplicaExp2
  rfl



theorem unequalReplicaBridgeMean_zero_eq_sum_interface
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) :
    unequalReplicaBridgeMean G H K J hf hg 0 =
      ∑ e ∈ StatMech.FK.fis_interface G H K,
        unequalReplicaExp2 G H J hf hg (fun a b =>
          bond (isingSumConfigEquiv.symm (a, b)) e) := by
  rw [unequalReplicaBridgeMean_zero]
  unfold unequalReplicaBridgeInteraction
  exact unequalReplicaExp2_finset_sum G H J hf hg
    (StatMech.FK.fis_interface G H K)
    (fun e a b => bond (isingSumConfigEquiv.symm (a, b)) e)

end

end StatMech.FrontierA
