/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalUnequalBridgeEndpoint








namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness
open Filter Topology

noncomputable section


def oddPrismUpperHalfSurfaceSite (n : Nat) (hn : 0 < n)
    (i j : Fin (2 * n + 1)) : OddPrismUpperBlockSite n :=
  ⟨⟨i, j, ⟨n + 1, by omega⟩⟩, by
    unfold oddPrismAtOrBelowCenter
    simp only
    omega⟩



def oddPrismCentralInterfaceEdge (n : Nat) (hn : 0 < n)
    (i j : Fin (2 * n + 1)) :
    Sym2 (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n) :=
  s(Sum.inl (oddPrismLowerHalfSurfaceSite n i j),
    Sum.inr (oddPrismUpperHalfSurfaceSite n hn i j))


theorem oddPrismCentralInterfaceEdge_injective (n : Nat) (hn : 0 < n) :
    Function.Injective (fun q : Fin (2 * n + 1) × Fin (2 * n + 1) =>
      oddPrismCentralInterfaceEdge n hn q.1 q.2) := by
  intro q r h
  change oddPrismCentralInterfaceEdge n hn q.1 q.2 =
    oddPrismCentralInterfaceEdge n hn r.1 r.2 at h
  unfold oddPrismCentralInterfaceEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hl := Sum.inl.inj h.1
    have hv := congrArg (fun v : OddPrismLowerBlockSite n => v.1) hl
    apply Prod.ext
    · exact congrArg RectangularPrismSite.x hv
    · exact congrArg RectangularPrismSite.y hv
  · exact (Sum.inl_ne_inr h.1).elim


theorem exists_cross_pair_of_mem_fis_interface
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hci : StatMech.FK.fis_CrossInterface G H K)
    {e : Sym2 (V ⊕ W)}
    (he : e ∈ StatMech.FK.fis_interface G H K) :
    ∃ x : V, ∃ y : W, e = s(Sum.inl x, Sum.inr y) := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [StatMech.FK.fis_interface, Finset.mem_sdiff,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases he with ⟨hK, hnot⟩
      rcases x with x | x <;> rcases y with y | y
      · exact False.elim (hnot (hci.inl x y hK))
      · exact ⟨x, y, rfl⟩
      · exact ⟨y, x, Sym2.eq_swap⟩
      · exact False.elim (hnot (hci.inr x y hK))



theorem oddPrismCentralInterfaceEdge_mem (n : Nat) (hn : 0 < n)
    (i j : Fin (2 * n + 1)) :
    oddPrismCentralInterfaceEdge n hn i j ∈
      StatMech.FK.fis_interface
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) := by
  classical
  rw [StatMech.FK.fis_interface, Finset.mem_sdiff]
  constructor
  · rw [SimpleGraph.mem_edgeFinset]
    change (oddPrismUnequalGlueGraph n).Adj
      (Sum.inl (oddPrismLowerHalfSurfaceSite n i j))
      (Sum.inr (oddPrismUpperHalfSurfaceSite n hn i j))
    rw [StatMech.FK.agl_glueGraph_adj]
    show (oddPrismInternalGraph n).Adj
      (oddPrismLowerHalfSurfaceSite n i j).1
      (oddPrismUpperHalfSurfaceSite n hn i j).1
    rw [oddPrismInternalGraph]
    simp only [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, ?_⟩
    · change s((oddPrismLowerHalfSurfaceSite n i j).1,
        (oddPrismUpperHalfSurfaceSite n hn i j).1) ∈
          oddPrismInternalEdges n
      unfold oddPrismInternalEdges
      apply Finset.mem_image.mpr
      let z : Fin (2 * n) := ⟨n, by omega⟩
      refine ⟨(.inr (.inr (i, j, z)) : OddPrismInternalIndex n),
        Finset.mem_univ _, ?_⟩
      simp [oddPrismInternalEdge, oddPrismCentralInterfaceEdge,
        oddPrismUpperHalfSurfaceSite, z]
      congr
    · simp [Sym2.mk_isDiag_iff, oddPrismLowerHalfSurfaceSite,
        oddPrismUpperHalfSurfaceSite]
  · rw [SimpleGraph.mem_edgeFinset]
    intro h
    change (oddPrismLowerBlockGraph n ⊕g oddPrismUpperBlockGraph n).Adj
      (Sum.inl (oddPrismLowerHalfSurfaceSite n i j))
      (Sum.inr (oddPrismUpperHalfSurfaceSite n hn i j)) at h
    simpa only [SimpleGraph.sum_adj] using h



theorem exists_oddPrismCentralInterfaceEdge_eq_of_mem
    (n : Nat) (hn : 0 < n)
    {e : Sym2 (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n)}
    (he : e ∈ StatMech.FK.fis_interface
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)) :
    ∃ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      e = oddPrismCentralInterfaceEdge n hn q.1 q.2 := by
  classical
  rcases exists_cross_pair_of_mem_fis_interface
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface
        (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n)) he with
    ⟨x, y, rfl⟩
  have he' := he
  rw [StatMech.FK.fis_interface, Finset.mem_sdiff] at he'
  have hK := he'.1
  rw [SimpleGraph.mem_edgeFinset] at hK
  change (oddPrismUnequalGlueGraph n).Adj (Sum.inl x) (Sum.inr y) at hK
  rw [StatMech.FK.agl_glueGraph_adj] at hK
  rw [oddPrismInternalGraph] at hK
  simp only [SimpleGraph.fromEdgeSet_adj] at hK
  have hedge : s(x.1, y.1) ∈ oddPrismInternalEdges n := by
    exact hK.1
  unfold oddPrismInternalEdges at hedge
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hedge
  have hxP := x.2
  have hyP := y.2
  unfold oddPrismAtOrBelowCenter at hxP hyP
  rcases q with q | q
  · rw [oddPrismInternalEdge, Sym2.eq_iff] at hq
    rcases hq with hq | hq
    · have hxz : q.2.2.val = x.1.z.val := by
        simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.1)
      have hyz : q.2.2.val = y.1.z.val := by
        simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.2)
      omega
    · have hyz : q.2.2.val = y.1.z.val := by
        simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.1)
      have hxz : q.2.2.val = x.1.z.val := by
        simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.2)
      omega
  · rcases q with q | q
    · rw [oddPrismInternalEdge, Sym2.eq_iff] at hq
      rcases hq with hq | hq
      · have hxz : q.2.2.val = x.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.1)
        have hyz : q.2.2.val = y.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.2)
        omega
      · have hyz : q.2.2.val = y.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.1)
        have hxz : q.2.2.val = x.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.2)
        omega
    · rw [oddPrismInternalEdge, Sym2.eq_iff] at hq
      rcases hq with hq | hq
      · have hxz : q.2.2.val = x.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.1)
        have hyz : q.2.2.val + 1 = y.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.2)
        have hz : q.2.2.val = n := by omega
        have hx : x = oddPrismLowerHalfSurfaceSite n q.1 q.2.1 := by
          apply Subtype.ext
          rw [← hq.1]
          simp [oddPrismLowerHalfSurfaceSite, hz]
        have hy : y = oddPrismUpperHalfSurfaceSite n hn q.1 q.2.1 := by
          apply Subtype.ext
          rw [← hq.2]
          simp [oddPrismUpperHalfSurfaceSite, hz]
        refine ⟨(q.1, q.2.1), ?_⟩
        simp [oddPrismCentralInterfaceEdge, hx, hy]
      · have hyz : q.2.2.val = y.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.1)
        have hxz : q.2.2.val + 1 = x.1.z.val := by
          simpa using congrArg Fin.val (congrArg RectangularPrismSite.z hq.2)
        omega



theorem oddPrism_fis_interface_eq_central_image (n : Nat) (hn : 0 < n) :
    StatMech.FK.fis_interface
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) =
      Finset.univ.image (fun q : Fin (2 * n + 1) × Fin (2 * n + 1) =>
        oddPrismCentralInterfaceEdge n hn q.1 q.2) := by
  classical
  ext e
  constructor
  · intro he
    rcases exists_oddPrismCentralInterfaceEdge_eq_of_mem n hn he with ⟨q, rfl⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
    exact oddPrismCentralInterfaceEdge_mem n hn q.1 q.2



theorem sum_oddPrism_fis_interface (n : Nat) (hn : 0 < n)
    (F : Sym2 (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n) -> Real) :
    (∑ e ∈ StatMech.FK.fis_interface
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n), F e) =
      ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
        F (oddPrismCentralInterfaceEdge n hn q.1 q.2) := by
  rw [oddPrism_fis_interface_eq_central_image n hn,
    Finset.sum_image
      (s := Finset.univ) (oddPrismCentralInterfaceEdge_injective n hn).injOn]



theorem oddPrismUnequalBridgeMean_zero_eq_surfaceProductSum
    (beta : Real) (n : Nat) (hn : 0 < n) :
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0 =
      ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
        expJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1)
            (fun a => spin a (oddPrismLowerHalfSurfaceSite n q.1 q.2)) *
          expJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1)
            (fun b => spin b (oddPrismUpperHalfSurfaceSite n hn q.1 q.2)) := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  rw [unequalReplicaBridgeMean_zero_eq_sum_interface,
    sum_oddPrism_fis_interface n hn]
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismCentralInterfaceEdge
  exact unequalReplicaExp2_crossBond
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1)
    (oddPrismLowerHalfSurfaceSite n q.1 q.2)
    (oddPrismUpperHalfSurfaceSite n hn q.1 q.2)



theorem oddPrismLowerBlockSurfaceSpinMean_eq
    (beta : Real) (n : Nat) (i j : Fin (2 * n + 1)) :
    expJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1)
        (fun a => spin a (oddPrismLowerHalfSurfaceSite n i j)) =
      oddPrismLowerHalfSurfaceSpinMeanAt beta n i j := by
  rfl


theorem oddPrismUpperBlockSurfaceSpinMean_nonneg
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n)
    (i j : Fin (2 * n + 1)) :
    0 <= expJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)
      (fun b => spin b (oddPrismUpperHalfSurfaceSite n hn i j)) := by
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  rw [← spinProd_singleton]
  apply ghsvp_expJ_nonneg
  · exact fun _ _ => hbeta
  · intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)


theorem oddPrismUpperBlockSurfaceSpinMean_le_one
    (beta : Real) (n : Nat) (hn : 0 < n)
    (i j : Fin (2 * n + 1)) :
    expJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)
      (fun b => spin b (oddPrismUpperHalfSurfaceSite n hn i j)) <= 1 := by
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  unfold expJ
  apply (div_le_one (ZJ_pos _ _ _)).2
  unfold ZJ
  apply Finset.sum_le_sum
  intro sigma _
  have hw : 0 <= wJ (oddPrismUpperBlockGraph n).edgeFinset
      (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) sigma :=
    wJ_nonneg _ _ _ _
  have hs : spin sigma (oddPrismUpperHalfSurfaceSite n hn i j) <= 1 :=
    (le_abs_self _).trans
      (abs_spin_le_one sigma (oddPrismUpperHalfSurfaceSite n hn i j))
  simpa [mul_comm] using mul_le_of_le_one_right hw hs



theorem oddPrismUnequalBridgeMean_zero_le_surfaceSpinSum
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0 <=
      ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
        oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 := by
  rw [oddPrismUnequalBridgeMean_zero_eq_surfaceProductSum beta n hn]
  apply Finset.sum_le_sum
  intro q _
  rw [oddPrismLowerBlockSurfaceSpinMean_eq]
  exact mul_le_of_le_one_right
    (oddPrismLowerHalfSurfaceSpinMeanAt_nonneg beta hbeta n q.1 q.2)
    (oddPrismUpperBlockSurfaceSpinMean_le_one beta n hn q.1 q.2)


def oddPrismCriticalLowerHalfSpinAverage (n : Nat) : Real :=
  (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      oddPrismLowerHalfSurfaceSpinMeanAt (Ising.betaC 3) n q.1 q.2) /
    (((2 * n + 1 : Nat) : Real) ^ 2)

theorem oddPrismCriticalLowerHalfSpinAverage_nonneg (n : Nat) :
    0 <= oddPrismCriticalLowerHalfSpinAverage n := by
  unfold oddPrismCriticalLowerHalfSpinAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro q _
    exact oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
      (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
  · positivity



theorem oddPrismCriticalLowerHalfSpinAverage_sq_le (n : Nat) :
    oddPrismCriticalLowerHalfSpinAverage n ^ 2 <=
      oddPrismCriticalLowerHalfSpinSquareAverage n := by
  let f : Fin (2 * n + 1) × Fin (2 * n + 1) -> Real := fun q =>
    oddPrismLowerHalfSurfaceSpinMeanAt (Ising.betaC 3) n q.1 q.2
  have hL : (0 : Real) < ((2 * n + 1 : Nat) : Real) := by positivity
  have hL2 : (0 : Real) < (((2 * n + 1 : Nat) : Real) ^ 2) :=
    sq_pos_of_pos hL
  have hcs : (∑ q, f q) ^ 2 <=
      (((2 * n + 1 : Nat) : Real) ^ 2) * ∑ q, f q ^ 2 := by
    simpa [f, pow_two] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := f))
  unfold oddPrismCriticalLowerHalfSpinAverage
    oddPrismCriticalLowerHalfSpinSquareAverage
  change ((∑ q, f q) / (((2 * n + 1 : Nat) : Real) ^ 2)) ^ 2 <=
    (∑ q, f q ^ 2) / (((2 * n + 1 : Nat) : Real) ^ 2)
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hL2)]
  calc
    (∑ q, f q) ^ 2 <=
        (((2 * n + 1 : Nat) : Real) ^ 2) * ∑ q, f q ^ 2 := hcs
    _ = ((∑ q, f q ^ 2) / (((2 * n + 1 : Nat) : Real) ^ 2)) *
        (((2 * n + 1 : Nat) : Real) ^ 2) ^ 2 := by
      field_simp [hL.ne']


theorem oddPrismCriticalLowerHalfSpinAverage_tendsto_zero :
    Tendsto oddPrismCriticalLowerHalfSpinAverage atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n =>
      Real.sqrt (oddPrismCriticalLowerHalfSpinSquareAverage n))
      atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp
      oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      oddPrismCriticalLowerHalfSpinAverage_nonneg
  · exact Filter.Eventually.of_forall (fun n =>
      (Real.le_sqrt
        (oddPrismCriticalLowerHalfSpinAverage_nonneg n)
        (oddPrismCriticalLowerHalfSpinSquareAverage_nonneg n)).2
          (oddPrismCriticalLowerHalfSpinAverage_sq_le n))
  · exact hsqrt


def oddPrismCriticalUnequalBridgeMeanDensity (n : Nat) : Real :=
  unequalReplicaBridgeMean
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
      (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
      (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0 /
    (((2 * n + 1 : Nat) : Real) ^ 2)

theorem oddPrismCriticalUnequalBridgeMeanDensity_nonneg
    (n : Nat) (hn : 0 < n) :
    0 <= oddPrismCriticalUnequalBridgeMeanDensity n := by
  unfold oddPrismCriticalUnequalBridgeMeanDensity
  apply div_nonneg
  · rw [oddPrismUnequalBridgeMean_zero_eq_surfaceProductSum
      (Ising.betaC 3) n hn]
    apply Finset.sum_nonneg
    intro q _
    apply mul_nonneg
    · rw [oddPrismLowerBlockSurfaceSpinMean_eq]
      exact oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
        (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
    · exact oddPrismUpperBlockSurfaceSpinMean_nonneg
        (Ising.betaC 3) isingBetaC_three_pos.le n hn q.1 q.2
  · positivity

theorem oddPrismCriticalUnequalBridgeMeanDensity_le_lowerAverage
    (n : Nat) (hn : 0 < n) :
    oddPrismCriticalUnequalBridgeMeanDensity n <=
      oddPrismCriticalLowerHalfSpinAverage n := by
  unfold oddPrismCriticalUnequalBridgeMeanDensity
    oddPrismCriticalLowerHalfSpinAverage
  exact div_le_div_of_nonneg_right
    (oddPrismUnequalBridgeMean_zero_le_surfaceSpinSum
      (Ising.betaC 3) isingBetaC_three_pos.le n hn)
    (sq_nonneg _)



theorem oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero :
    Tendsto oddPrismCriticalUnequalBridgeMeanDensity atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact oddPrismCriticalUnequalBridgeMeanDensity_nonneg n (by omega)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact oddPrismCriticalUnequalBridgeMeanDensity_le_lowerAverage n (by omega)
  · exact oddPrismCriticalLowerHalfSpinAverage_tendsto_zero



theorem standardCubicInterfaceDensity_critical_le_unequalMeanDensity
    (n : Nat) (hn : 0 < n)
    (hvar : OddPrismUnequalBridgeVarianceOrder (Ising.betaC 3) n) :
    standardCubicInterfaceDensity (Ising.betaC 3) n <=
      2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n := by
  rw [standardCubicInterfaceDensity_eq_oddPrismUnequalBridge
    (Ising.betaC 3) n hn]
  unfold oddPrismCriticalUnequalBridgeMeanDensity
  calc
    oddPrismUnequalBridgeFreeEnergy (Ising.betaC 3) n /
        (((2 * n + 1 : Nat) : Real) ^ 2) <=
      (2 * Ising.betaC 3 * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
        (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
        (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0) /
          (((2 * n + 1 : Nat) : Real) ^ 2) :=
      div_le_div_of_nonneg_right
        (oddPrismUnequalBridgeFreeEnergy_le_of_variance_order
          (Ising.betaC 3) isingBetaC_three_pos.le n hvar) (sq_nonneg _)
    _ = 2 * Ising.betaC 3 *
        (unequalReplicaBridgeMean
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
          (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
          (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0 /
            (((2 * n + 1 : Nat) : Real) ^ 2)) := by ring



theorem standardCubicInterfaceDensity_critical_tendsto_zero_of_varianceOrder
    (hvar : forall n, OddPrismUnequalBridgeVarianceOrder
      (Ising.betaC 3) n) :
    Tendsto (standardCubicInterfaceDensity (Ising.betaC 3))
      atTop (nhds 0) := by
  have hu : Tendsto (fun n =>
      2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact standardCubicInterfaceDensity_nonneg
      isingBetaC_three_pos.le n (by omega)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact standardCubicInterfaceDensity_critical_le_unequalMeanDensity
      n (by omega) (hvar n)
  · exact hu




theorem rectangularIsingSurfaceTension_critical_eq_zero_of_unequalVarianceOrder
    (hprism : HasPrismCubicalSurfaceComparison (Ising.betaC 3))
    (hvar : forall n, OddPrismUnequalBridgeVarianceOrder
      (Ising.betaC 3) n) :
    rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
  apply tendsto_nhds_unique
    (standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
      isingBetaC_three_pos hprism
      (hasStandardPrismSurfaceComparison (Ising.betaC 3)))
  exact standardCubicInterfaceDensity_critical_tendsto_zero_of_varianceOrder hvar

end

end StatMech.FrontierA
