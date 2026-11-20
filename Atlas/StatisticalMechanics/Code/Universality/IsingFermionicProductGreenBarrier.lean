/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicLocalizedPoissonLinearity










namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section



theorem isingFiniteWeightedLaplacian_mul_of_edgewise
    {V : Type*} [Fintype V]
    (conductance : V -> V -> Real) (f g : V -> Real) (x : V)
    (hedge : forall y, Not (conductance x y = 0) ->
      (f y - f x) * (g y - g x) = 0) :
    isingFiniteWeightedLaplacian conductance (fun y => f y * g y) x =
      f x * isingFiniteWeightedLaplacian conductance g x +
        g x * isingFiniteWeightedLaplacian conductance f x := by
  classical
  unfold isingFiniteWeightedLaplacian
  rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : conductance x y = 0
  · simp [hxy]
  · have hcross := hedge y hxy
    calc
      conductance x y * (f y * g y - f x * g x) =
          f x * (conductance x y * (g y - g x)) +
            g x * (conductance x y * (f y - f x)) +
              conductance x y * ((f y - f x) * (g y - g x)) := by ring
      _ = f x * (conductance x y * (g y - g x)) +
            g x * (conductance x y * (f y - f x)) := by rw [hcross]; ring



theorem isingFiniteWeightedLaplacian_mul_nonpos
    {V : Type*} [Fintype V]
    (conductance : V -> V -> Real) (f g : V -> Real) (x : V)
    (hedge : forall y, Not (conductance x y = 0) ->
      (f y - f x) * (g y - g x) = 0)
    (hf : 0 <= f x) (hg : 0 <= g x)
    (hfLap : isingFiniteWeightedLaplacian conductance f x <= 0)
    (hgLap : isingFiniteWeightedLaplacian conductance g x <= 0) :
    isingFiniteWeightedLaplacian conductance (fun y => f y * g y) x <= 0 := by
  rw [isingFiniteWeightedLaplacian_mul_of_edgewise
    conductance f g x hedge]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hf hgLap)
    (mul_nonpos_of_nonneg_of_nonpos hg hfLap)




theorem isingFiniteWeightedPointPoissonBarrier_le_product
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) (hsource : Not (boundary source))
    (f g : V -> Real)
    (hf_nonneg : forall x, 0 <= f x)
    (hg_nonneg : forall x, 0 <= g x)
    (hden : 0 < f source + g source)
    (hedge : forall x y, Not (conductance x y = 0) ->
      (f y - f x) * (g y - g x) = 0)
    (hf_super : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance f x <= 0)
    (hg_super : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance g x <= 0)
    (hf_source :
      isingFiniteWeightedLaplacian conductance f source <= -1)
    (hg_source :
      isingFiniteWeightedLaplacian conductance g source <= -1) :
    forall x,
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
          hconductance hpositive hhit source x <=
        f x * g x / (f source + g source) := by
  let denominator := f source + g source
  let barrier : V -> Real := fun x =>
    (1 / denominator) * (f x * g x)
  have hbarrier : forall x, barrier x =
      f x * g x / (f source + g source) := by
    intro x
    dsimp only [barrier, denominator]
    ring
  have hcomparison : forall x,
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
          hconductance hpositive hhit source x <= barrier x := by
    apply isingFiniteWeightedPointPoissonBarrier_le_of_superharmonic
      G conductance boundary hconductance hpositive hhit source hsource barrier
    · intro x _
      dsimp only [barrier]
      exact mul_nonneg (one_div_nonneg.mpr hden.le)
        (mul_nonneg (hf_nonneg x) (hg_nonneg x))
    · rw [show barrier = fun x =>
          (1 / denominator) * ((fun y => f y * g y) x) by rfl,
        isingFiniteWeightedLaplacian_const_mul,
        isingFiniteWeightedLaplacian_mul_of_edgewise
          conductance f g source (hedge source)]
      have hf_scale :
          f source * isingFiniteWeightedLaplacian conductance g source <=
            -f source := by
        have := mul_le_mul_of_nonneg_left hg_source (hf_nonneg source)
        linarith
      have hg_scale :
          g source * isingFiniteWeightedLaplacian conductance f source <=
            -g source := by
        have := mul_le_mul_of_nonneg_left hf_source (hg_nonneg source)
        linarith
      dsimp only [denominator]
      rw [one_div]
      apply (inv_mul_le_iff₀ hden).2
      linarith
    · intro x hx _
      rw [show barrier = fun x =>
          (1 / denominator) * ((fun y => f y * g y) x) by rfl,
        isingFiniteWeightedLaplacian_const_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (one_div_nonneg.mpr hden.le)
        (isingFiniteWeightedLaplacian_mul_nonpos conductance f g x
          (hedge x) (hf_nonneg x) (hg_nonneg x)
          (hf_super x hx) (hg_super x hx))
  intro x
  exact (hcomparison x).trans_eq (hbarrier x)



theorem isingFiniteGraphLaplacian_mul_of_edgewise
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f g : V -> Real) (x : V)
    (hedge : forall y, G.Adj x y ->
      (f y - f x) * (g y - g x) = 0) :
    isingFiniteGraphLaplacian G (fun y => f y * g y) x =
      f x * isingFiniteGraphLaplacian G g x +
        g x * isingFiniteGraphLaplacian G f x := by
  classical
  unfold isingFiniteGraphLaplacian
  rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  have hadj : G.Adj x y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hy
  have hcross := hedge y hadj
  calc
    f y * g y - f x * g x =
        f x * (g y - g x) + g x * (f y - f x) +
          (f y - f x) * (g y - g x) := by ring
    _ = f x * (g y - g x) + g x * (f y - f x) := by
      rw [hcross]
      ring




theorem isingFiniteGhostPointPoissonBarrier_le_splitProduct
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (ghostRate rateF rateG : V -> Real)
    (fixed : V -> Prop)
    (hrate : forall x, 0 <= ghostRate x)
    (hsplit : forall x, rateF x + rateG x = ghostRate x)
    (hreach : forall x, exists b,
      (fixed b \/ 0 < ghostRate b) /\ G.Reachable x b)
    (source : V) (hsource : Not (fixed source))
    (f g : V -> Real)
    (hf_nonneg : forall x, 0 <= f x)
    (hg_nonneg : forall x, 0 <= g x)
    (hden : 0 < f source + g source)
    (hedge : forall x y, G.Adj x y ->
      (f y - f x) * (g y - g x) = 0)
    (hf_super : forall x, Not (fixed x) ->
      isingFiniteGraphLaplacian G f x - rateF x * f x <= 0)
    (hg_super : forall x, Not (fixed x) ->
      isingFiniteGraphLaplacian G g x - rateG x * g x <= 0)
    (hf_source : isingFiniteGraphLaplacian G f source -
      rateF source * f source <= -1)
    (hg_source : isingFiniteGraphLaplacian G g source -
      rateG source * g source <= -1) :
    forall x,
      isingFiniteWeightedPointPoissonBarrier
          (isingFiniteGhostGraph G ghostRate)
          (isingFiniteGhostConductance G ghostRate)
          (isingFiniteGhostBoundaryWith fixed)
          (isingFiniteGhostConductance_nonneg G ghostRate hrate)
          (isingFiniteGhostConductance_pos_of_adj G ghostRate)
          (isingFiniteGhostGraph_reachable_boundaryWith
            G ghostRate fixed hreach)
          (some source) (some x) <=
        f x * g x / (f source + g source) := by
  let denominator := f source + g source
  let physicalBarrier : V -> Real := fun x =>
    (1 / denominator) * (f x * g x)
  let barrier : Option V -> Real :=
    isingFiniteGhostExtension 0 physicalBarrier
  have hsource' : Not (isingFiniteGhostBoundaryWith fixed (some source)) :=
    hsource
  have hdecomp : forall x,
      isingFiniteWeightedLaplacian
          (isingFiniteGhostConductance G ghostRate) barrier (some x) =
        (1 / denominator) *
          (f x * (isingFiniteGraphLaplacian G g x - rateG x * g x) +
            g x * (isingFiniteGraphLaplacian G f x - rateF x * f x)) := by
    intro x
    rw [show barrier = isingFiniteGhostExtension 0 physicalBarrier by rfl,
      isingFiniteGhostLaplacian_some]
    have hproduct := isingFiniteGraphLaplacian_mul_of_edgewise
      G f g x (hedge x)
    rw [show isingFiniteGraphLaplacian G physicalBarrier x =
        (1 / denominator) *
          isingFiniteGraphLaplacian G (fun y => f y * g y) x by
      exact isingFiniteGraphLaplacian_const_mul
        G (1 / denominator) (fun y => f y * g y) x,
      hproduct]
    dsimp only [physicalBarrier]
    rw [<- hsplit x]
    ring
  have hcomparison : forall z,
      isingFiniteWeightedPointPoissonBarrier
          (isingFiniteGhostGraph G ghostRate)
          (isingFiniteGhostConductance G ghostRate)
          (isingFiniteGhostBoundaryWith fixed)
          (isingFiniteGhostConductance_nonneg G ghostRate hrate)
          (isingFiniteGhostConductance_pos_of_adj G ghostRate)
          (isingFiniteGhostGraph_reachable_boundaryWith
            G ghostRate fixed hreach)
          (some source) z <= barrier z := by
    apply isingFiniteWeightedPointPoissonBarrier_le_of_superharmonic
      (isingFiniteGhostGraph G ghostRate)
      (isingFiniteGhostConductance G ghostRate)
      (isingFiniteGhostBoundaryWith fixed)
      (isingFiniteGhostConductance_nonneg G ghostRate hrate)
      (isingFiniteGhostConductance_pos_of_adj G ghostRate)
      (isingFiniteGhostGraph_reachable_boundaryWith
        G ghostRate fixed hreach)
      (some source) hsource' barrier
    · intro z _
      cases z with
      | none => exact le_refl 0
      | some x =>
          dsimp only [barrier, isingFiniteGhostExtension, physicalBarrier]
          exact mul_nonneg (one_div_nonneg.mpr hden.le)
            (mul_nonneg (hf_nonneg x) (hg_nonneg x))
    · rw [hdecomp source]
      have hf_scale :
          f source * (isingFiniteGraphLaplacian G g source -
            rateG source * g source) <= -f source := by
        have := mul_le_mul_of_nonneg_left hg_source (hf_nonneg source)
        linarith
      have hg_scale :
          g source * (isingFiniteGraphLaplacian G f source -
            rateF source * f source) <= -g source := by
        have := mul_le_mul_of_nonneg_left hf_source (hg_nonneg source)
        linarith
      dsimp only [denominator]
      rw [one_div]
      apply (inv_mul_le_iff₀ hden).2
      linarith
    · intro z hz _
      cases z with
      | none => exact False.elim (hz trivial)
      | some x =>
          change Not (fixed x) at hz
          rw [hdecomp x]
          exact mul_nonpos_of_nonneg_of_nonpos
            (one_div_nonneg.mpr hden.le)
            (add_nonpos
              (mul_nonpos_of_nonneg_of_nonpos
                (hf_nonneg x) (hg_super x hz))
              (mul_nonpos_of_nonneg_of_nonpos
                (hg_nonneg x) (hf_super x hz)))
  intro x
  have hx := hcomparison (some x)
  dsimp only [barrier, isingFiniteGhostExtension, physicalBarrier] at hx
  dsimp only [denominator] at hx
  simpa [div_eq_mul_inv, mul_comm] using hx

end

end StatMech.Universality
