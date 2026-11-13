/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalBoundaryInfluence
import Code.Ising.LebowitzPfisterReflectionGauge










open Filter MeasureTheory Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section



theorem translatedBox_subset_boxFinset_of_margin
    {d n r : Nat} (x : Site d)
    (hmargin : forall k, (x k).natAbs + r <= n) :
    (boxFinset d r).image (fun y => Multiplicative.ofAdd x • y) <=
      boxFinset d n := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_boxFinset]
  intro k
  have hz' := mem_boxFinset.mp hz k
  change (x k + z k).natAbs <= n
  exact (Int.natAbs_add_le _ _).trans
    ((Nat.add_le_add_left hz' _).trans (hmargin k))




theorem oddPrismLowerHalfSurfaceSite_translatedBox_subset
    (n r : Nat) (i j : Fin (2 * n + 1))
    (hiLower : r <= i.val) (hiUpper : i.val + r <= 2 * n)
    (hjLower : r <= j.val) (hjUpper : j.val + r <= 2 * n) :
    (boxFinset 3 r).image (fun y =>
        Multiplicative.ofAdd
          (rectangularPrismSiteEquivSctBoxDobrushin n
            (oddPrismLowerHalfSurfaceSite n i j).1).1 • y) <=
      boxFinset 3 n := by
  apply translatedBox_subset_boxFinset_of_margin
  intro k
  fin_cases k
  · change ((rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfSurfaceSite n i j).1).1 0).natAbs + r <= n
    rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_zero]
    dsimp [oddPrismLowerHalfSurfaceSite]
    omega
  · change ((rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfSurfaceSite n i j).1).1 1).natAbs + r <= n
    rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_one]
    dsimp [oddPrismLowerHalfSurfaceSite]
    omega
  · change ((rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfSurfaceSite n i j).1).1 2).natAbs + r <= n
    rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_two]
    dsimp [oddPrismLowerHalfSurfaceSite]
    omega


theorem oddPrismPlusSpinMean_nonneg
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    0 <= oddPrismPlusSpinMean beta n v := by
  unfold oddPrismPlusSpinMean
  rw [<- spinProd_singleton]
  apply ghsvp_expJ_nonneg
  · exact fun _ _ => hbeta
  · intro u
    exact mul_nonneg hbeta (Nat.cast_nonneg _)


theorem oddPrismPlusSpinMean_le_one
    (beta : Real) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    oddPrismPlusSpinMean beta n v <= 1 := by
  unfold oddPrismPlusSpinMean expJ
  apply (div_le_one (ZJ_pos _ _ _)).2
  unfold ZJ
  apply Finset.sum_le_sum
  intro sigma _
  have hw : 0 <= wJ (oddPrismInternalEdges n) (fun _ => beta)
      (fun x => beta * oddPrismPlusField n x) sigma :=
    wJ_nonneg _ _ _ _
  have hs : spin sigma v <= 1 :=
    (le_abs_self _).trans (abs_spin_le_one sigma v)
  simpa [mul_comm] using mul_le_of_le_one_right hw hs



theorem isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
    (n r : Nat) (i j : Fin (2 * n + 1))
    (hiLower : r <= i.val) (hiUpper : i.val + r <= 2 * n)
    (hjLower : r <= j.val) (hjUpper : j.val + r <= 2 * n) :
    oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfSurfaceSite n i j).1 <=
      (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} -
        (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} := by
  apply isingCritical_oddPrismPlusSpinMean_le_centeredGap
  exact oddPrismLowerHalfSurfaceSite_translatedBox_subset n r i j
    hiLower hiUpper hjLower hjUpper



theorem isingCritical_oddPrismPlusSurfaceSpinMean_tendsto_zero_of_margin
    (r : Nat -> Nat)
    (i j : (n : Nat) -> Fin (2 * n + 1))
    (hr : Tendsto r atTop atTop)
    (hiLower : forall n, r n <= (i n).val)
    (hiUpper : forall n, (i n).val + r n <= 2 * n)
    (hjLower : forall n, r n <= (j n).val)
    (hjUpper : forall n, (j n).val + r n <= 2 * n) :
    Tendsto (fun n =>
      oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfSurfaceSite n (i n) (j n)).1)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
        isingBetaC_three_pos.le n _
  · exact Filter.Eventually.of_forall fun n =>
      isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
        n (r n) (i n) (j n)
          (hiLower n) (hiUpper n) (hjLower n) (hjUpper n)
  · exact (isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
      (origin 3)).comp hr



private def oddPrismSurfaceLow (n r : Nat) :
    Finset (Fin (2 * n + 1)) :=
  Finset.univ.filter fun i => i.val < r

private def oddPrismSurfaceHigh (n r : Nat) :
    Finset (Fin (2 * n + 1)) :=
  Finset.univ.filter fun i => 2 * n < i.val + r

private def oddPrismSurfaceBoundaryPairs (n r : Nat) :
    Finset (Fin (2 * n + 1) × Fin (2 * n + 1)) :=
  let U : Finset (Fin (2 * n + 1)) := Finset.univ
  oddPrismSurfaceLow n r ×ˢ U ∪
    oddPrismSurfaceHigh n r ×ˢ U ∪
    U ×ˢ oddPrismSurfaceLow n r ∪
    U ×ˢ oddPrismSurfaceHigh n r

private def oddPrismSurfaceInterior (n r : Nat)
    (q : Fin (2 * n + 1) × Fin (2 * n + 1)) : Prop :=
  r <= q.1.val ∧ q.1.val + r <= 2 * n ∧
    r <= q.2.val ∧ q.2.val + r <= 2 * n

private noncomputable def oddPrismSurfaceNonInterior (n r : Nat) :
    Finset (Fin (2 * n + 1) × Fin (2 * n + 1)) :=
  by
    classical
    exact Finset.univ.filter fun q => ¬ oddPrismSurfaceInterior n r q

private theorem oddPrismSurfaceLow_card_le (n r : Nat) :
    (oddPrismSurfaceLow n r).card <= r := by
  let s := oddPrismSurfaceLow n r
  have hinj : Function.Injective (fun i : Fin (2 * n + 1) => i.val) :=
    fun i j h => Fin.ext h
  have himage : Finset.image (fun i : Fin (2 * n + 1) => i.val) s <=
      Finset.range r := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  calc
    s.card = (Finset.image (fun i : Fin (2 * n + 1) => i.val) s).card :=
      (Finset.card_image_of_injective s hinj).symm
    _ <= (Finset.range r).card := Finset.card_le_card himage
    _ = r := Finset.card_range r

private theorem oddPrismSurfaceHigh_card_le (n r : Nat) :
    (oddPrismSurfaceHigh n r).card <= r := by
  let s := oddPrismSurfaceHigh n r
  let f : Fin (2 * n + 1) -> Nat := fun i => 2 * n - i.val
  have hinj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    dsimp [f] at h
    have hi : i.val <= 2 * n := by omega
    have hj : j.val <= 2 * n := by omega
    omega
  have himage : Finset.image f s <= Finset.range r := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have hi' := (Finset.mem_filter.mp hi).2
    have hiv : i.val <= 2 * n := by omega
    dsimp [f]
    omega
  calc
    s.card = (Finset.image f s).card :=
      (Finset.card_image_of_injective s hinj).symm
    _ <= (Finset.range r).card := Finset.card_le_card himage
    _ = r := Finset.card_range r

private theorem oddPrismSurface_not_interior_subset_boundary
    (n r : Nat) :
    oddPrismSurfaceNonInterior n r <=
      oddPrismSurfaceBoundaryPairs n r := by
  classical
  intro q hq
  unfold oddPrismSurfaceNonInterior at hq
  have hnot := (Finset.mem_filter.mp hq).2
  simp only [oddPrismSurfaceInterior] at hnot
  simp only [oddPrismSurfaceBoundaryPairs, Finset.mem_union,
    Finset.mem_product, Finset.mem_univ, and_true,
    oddPrismSurfaceLow, oddPrismSurfaceHigh, Finset.mem_filter,
    true_and]
  omega

private theorem oddPrismSurfaceBoundaryPairs_card_le (n r : Nat) :
    (oddPrismSurfaceBoundaryPairs n r).card <=
      4 * r * (2 * n + 1) := by
  let U : Finset (Fin (2 * n + 1)) := Finset.univ
  have hU : U.card = 2 * n + 1 := by simp [U]
  have hlow := oddPrismSurfaceLow_card_le n r
  have hhigh := oddPrismSurfaceHigh_card_le n r
  have h1 : (oddPrismSurfaceLow n r ×ˢ U).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    exact Nat.mul_le_mul_right _ hlow
  have h2 : (oddPrismSurfaceHigh n r ×ˢ U).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    exact Nat.mul_le_mul_right _ hhigh
  have h3 : (U ×ˢ oddPrismSurfaceLow n r).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    nlinarith
  have h4 : (U ×ˢ oddPrismSurfaceHigh n r).card <= r * (2 * n + 1) := by
    rw [Finset.card_product, hU]
    nlinarith
  have h12 : (oddPrismSurfaceLow n r ×ˢ U ∪
      oddPrismSurfaceHigh n r ×ˢ U).card <=
      (oddPrismSurfaceLow n r ×ˢ U).card +
        (oddPrismSurfaceHigh n r ×ˢ U).card :=
    Finset.card_union_le _ _
  dsimp only [oddPrismSurfaceBoundaryPairs]
  calc
    ((oddPrismSurfaceLow n r ×ˢ U ∪
        oddPrismSurfaceHigh n r ×ˢ U ∪
        U ×ˢ oddPrismSurfaceLow n r) ∪
        U ×ˢ oddPrismSurfaceHigh n r).card <=
      (oddPrismSurfaceLow n r ×ˢ U ∪
        oddPrismSurfaceHigh n r ×ˢ U ∪
        U ×ˢ oddPrismSurfaceLow n r).card +
          (U ×ˢ oddPrismSurfaceHigh n r).card := Finset.card_union_le _ _
    _ <= ((oddPrismSurfaceLow n r ×ˢ U ∪
        oddPrismSurfaceHigh n r ×ˢ U).card +
          (U ×ˢ oddPrismSurfaceLow n r).card) +
          (U ×ˢ oddPrismSurfaceHigh n r).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ <= 4 * r * (2 * n + 1) := by
      rw [show 4 * r * (2 * n + 1) =
        r * (2 * n + 1) + r * (2 * n + 1) +
          r * (2 * n + 1) + r * (2 * n + 1) by ring]
      omega



def oddPrismCriticalSurfaceSpinSquareAverage (n : Nat) : Real :=
  (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfSurfaceSite n q.1 q.2).1 ^ 2) /
    (((2 * n + 1 : Nat) : Real) ^ 2)

private def criticalCenteredSpinUpGap (r : Nat) : Real :=
  (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
      {omega | omega (origin 3) = true} -
    (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
      {omega | omega (origin 3) = true}

private theorem criticalCenteredSpinUpGap_nonneg (r : Nat) :
    0 <= criticalCenteredSpinUpGap r := by
  let c : Fin (2 * r + 1) := ⟨r, by omega⟩
  have hle := isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
    r r c c
      (by change r <= r; exact le_rfl)
      (by change r + r <= 2 * r; omega)
      (by change r <= r; exact le_rfl)
      (by change r + r <= 2 * r; omega)
  exact (oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
    isingBetaC_three_pos.le r _).trans hle

private theorem oddPrismCriticalSurfaceSpinSquareAverage_le
    (n r : Nat) :
    oddPrismCriticalSurfaceSpinSquareAverage n <=
      criticalCenteredSpinUpGap r ^ 2 +
        (4 * r : Real) / (((2 * n + 1 : Nat) : Real)) := by
  classical
  let L := 2 * n + 1
  let U : Finset (Fin (2 * n + 1) × Fin (2 * n + 1)) := Finset.univ
  let good := U.filter (oddPrismSurfaceInterior n r)
  let bad := oddPrismSurfaceNonInterior n r
  let f : Fin (2 * n + 1) × Fin (2 * n + 1) -> Real := fun q =>
    oddPrismPlusSpinMean (Ising.betaC 3) n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1 ^ 2
  unfold oddPrismCriticalSurfaceSpinSquareAverage
  change Finset.univ.sum f / (((2 * n + 1 : Nat) : Real) ^ 2) <=
    criticalCenteredSpinUpGap r ^ 2 +
      (4 * r : Real) / ((2 * n + 1 : Nat) : Real)
  have hsplit : good.sum f + bad.sum f = U.sum f := by
    simpa [good, bad, oddPrismSurfaceNonInterior] using
      (Finset.sum_filter_add_sum_filter_not U
        (oddPrismSurfaceInterior n r) f)
  have hgoodTerm : forall q, q ∈ good ->
      f q <= criticalCenteredSpinUpGap r ^ 2 := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    have hle := isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
      n r q.1 q.2 hq'.1 hq'.2.1 hq'.2.2.1 hq'.2.2.2
    have hm0 := oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
      isingBetaC_three_pos.le n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
    exact (sq_le_sq₀ hm0 (criticalCenteredSpinUpGap_nonneg r)).2 hle
  have hgood : good.sum f <=
      (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 := by
    calc
      good.sum f <= good.card * criticalCenteredSpinUpGap r ^ 2 := by
        simpa using Finset.sum_le_card_nsmul good f
          (criticalCenteredSpinUpGap r ^ 2) hgoodTerm
      _ <= (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 := by
        gcongr
        norm_cast
        simpa [U, L, pow_two] using Finset.card_filter_le U
          (oddPrismSurfaceInterior n r)
  have hbadTerm : forall q, q ∈ bad -> f q <= 1 := by
    intro q _
    have hm0 := oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
      isingBetaC_three_pos.le n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
    have hm1 := oddPrismPlusSpinMean_le_one (Ising.betaC 3) n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
    dsimp [f]
    nlinarith
  have hbadCard : bad.card <= 4 * r * L := by
    exact (Finset.card_le_card
      (oddPrismSurface_not_interior_subset_boundary n r)).trans
        (by simpa [bad, L] using oddPrismSurfaceBoundaryPairs_card_le n r)
  have hbad : bad.sum f <= (4 * r * L : Nat) := by
    calc
      bad.sum f <= bad.card * (1 : Real) := by
        simpa using Finset.sum_le_card_nsmul bad f (1 : Real) hbadTerm
      _ <= (4 * r * L : Nat) := by
        norm_num
        exact_mod_cast hbadCard
  have hsum : U.sum f <=
      (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 +
        (4 * r * L : Nat) := by
    rw [<- hsplit]
    gcongr
  have hL : (0 : Real) < L := by positivity
  rw [div_le_iff₀ (sq_pos_of_pos hL)]
  calc
    U.sum f <= (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 +
        (4 * r * L : Nat) := hsum
    _ = (criticalCenteredSpinUpGap r ^ 2 +
          (4 * r : Real) / L) * (L : Real) ^ 2 := by
      push_cast
      field_simp





theorem oddPrismCriticalSurfaceSpinSquareAverage_tendsto_zero :
    Tendsto oddPrismCriticalSurfaceSpinSquareAverage atTop (nhds 0) := by
  let r : Nat -> Nat := fun n => Nat.sqrt n
  let upper : Nat -> Real := fun n =>
    criticalCenteredSpinUpGap (r n) ^ 2 +
      (4 : Real) * ((r n : Nat) : Real) / (2 * n + 1)
  have hgap : Tendsto (fun n => criticalCenteredSpinUpGap (r n))
      atTop (nhds 0) :=
    (isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
      (origin 3)).comp StatMech.FK.ocs_sqrt_tendsto_atTop
  have hboundary : Tendsto
      (fun n => (4 : Real) * ((r n : Nat) : Real) / (2 * n + 1))
      atTop (nhds 0) := by
    have hratio := StatMech.FK.ocs_sqrt_div_to_zero
    have hdiv : Tendsto (fun n => ((r n : Nat) : Real) / (2 * n + 1))
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun n => by positivity
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hpos : (0 : Real) < n := by exact_mod_cast hn
        have hdenpos : (0 : Real) < 2 * n + 1 := by positivity
        dsimp [r]
        have hsqrt : (0 : Real) <= Nat.sqrt n := by positivity
        exact div_le_div_of_nonneg_left hsqrt hpos (by nlinarith)
      · simpa [r] using hratio
    simpa [mul_div_assoc] using tendsto_const_nhds.mul hdiv
  have hu : Tendsto upper atTop (nhds 0) := by
    simpa [upper] using (hgap.pow 2).add hboundary
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      unfold oddPrismCriticalSurfaceSpinSquareAverage
      positivity
  · exact Filter.Eventually.of_forall fun n => by
      have h := oddPrismCriticalSurfaceSpinSquareAverage_le n (r n)
      simpa [Nat.cast_mul] using h
  · exact hu





noncomputable def oddPrismLowerHalfGraph (n : Nat) :
    SimpleGraph
      {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
        v.z.val <= n} :=
  (oddPrismInternalGraph n).comap Subtype.val


def oddPrismLowerHalfBridgeSites (n : Nat) :
    (Fin (2 * n + 1) × Fin (2 * n + 1)) ->
      {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
        v.z.val <= n} :=
  fun q => oddPrismLowerHalfSurfaceSite n q.1 q.2



noncomputable def oddPrismLowerHalfBridgeFreeEnergy
    (beta : Real) (n : Nat) : Real := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  exact replicaBridgeFreeEnergy (oddPrismLowerHalfGraph n)
    (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (oddPrismLowerHalfBridgeSites n) beta



theorem replicaBridgeMoment_mul_partition_sq
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMoment G J hf sites r *
        ZJ G.edgeFinset J hf ^ 2 =
      ∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b *
          Real.exp (r * replicaBridgeInteraction sites a b) := by
  unfold replicaBridgeMoment ghsiExp2
  field_simp [(ZJ_pos G.edgeFinset J hf).ne']



theorem oddPrismLowerHalfBridgeSiteMean_eq
    (beta : Real) (n : Nat)
    (q : Fin (2 * n + 1) × Fin (2 * n + 1)) :
    letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
    expJ (oddPrismLowerHalfGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1)
        (fun sigma => spin sigma (oddPrismLowerHalfBridgeSites n q)) =
      oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 := by
  dsimp [oddPrismLowerHalfBridgeSites, oddPrismLowerHalfSurfaceSpinMeanAt,
    oddPrismLowerHalfGraph]
  rfl




theorem oddPrismLowerHalfBridgeFreeEnergy_le_of_variance_order
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (hvar :
      letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
      forall t, 0 <= t ->
        replicaBridgeVariance (oddPrismLowerHalfGraph n)
            (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1)
            (oddPrismLowerHalfBridgeSites n) t <=
          replicaBridgeVariance (oddPrismLowerHalfGraph n)
            (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1)
            (oddPrismLowerHalfBridgeSites n) (-t)) :
    oddPrismLowerHalfBridgeFreeEnergy beta n <=
      2 * beta *
        ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
          oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 ^ 2 := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  have h := replicaBridgeFreeEnergy_le_of_variance_order
    (oddPrismLowerHalfGraph n) (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (oddPrismLowerHalfBridgeSites n) beta hbeta hvar
  unfold oddPrismLowerHalfBridgeFreeEnergy
  rw [show (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      (expJ (oddPrismLowerHalfGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1)
        (fun sigma => spin sigma (oddPrismLowerHalfBridgeSites n q))) ^ 2) =
      ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
        oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 ^ 2 by
    apply Finset.sum_congr rfl
    intro q _
    rw [oddPrismLowerHalfBridgeSiteMean_eq]] at h
  exact h



def oddPrismCriticalLowerHalfSpinSquareAverage (n : Nat) : Real :=
  (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      oddPrismLowerHalfSurfaceSpinMeanAt (Ising.betaC 3) n q.1 q.2 ^ 2) /
    (((2 * n + 1 : Nat) : Real) ^ 2)

theorem oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (i j : Fin (2 * n + 1)) :
    0 <= oddPrismLowerHalfSurfaceSpinMeanAt beta n i j := by
  letI : DecidableRel (oddPrismInternalGraph n).Adj := Classical.decRel _
  dsimp only [oddPrismLowerHalfSurfaceSpinMeanAt]
  rw [<- spinProd_singleton]
  apply ghsvp_expJ_nonneg
  · exact fun _ _ => hbeta
  · intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)



theorem oddPrismCriticalLowerHalfSpinSquareAverage_le_plus
    (n : Nat) :
    oddPrismCriticalLowerHalfSpinSquareAverage n <=
      oddPrismCriticalSurfaceSpinSquareAverage n := by
  unfold oddPrismCriticalLowerHalfSpinSquareAverage
    oddPrismCriticalSurfaceSpinSquareAverage
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro q _
  have hlow0 := oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
    (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
  have hplus0 := oddPrismPlusSpinMean_nonneg
    (Ising.betaC 3) isingBetaC_three_pos.le n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
  have hle := oddPrismLowerHalfSurfaceSpinMeanAt_le_plus
    (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
  exact (sq_le_sq₀ hlow0 hplus0).2 hle

theorem oddPrismCriticalLowerHalfSpinSquareAverage_nonneg (n : Nat) :
    0 <= oddPrismCriticalLowerHalfSpinSquareAverage n := by
  unfold oddPrismCriticalLowerHalfSpinSquareAverage
  positivity



theorem oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero :
    Tendsto oddPrismCriticalLowerHalfSpinSquareAverage atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      oddPrismCriticalLowerHalfSpinSquareAverage_nonneg
  · exact Filter.Eventually.of_forall
      oddPrismCriticalLowerHalfSpinSquareAverage_le_plus
  · exact oddPrismCriticalSurfaceSpinSquareAverage_tendsto_zero





noncomputable def unequalReplicaBridgeInteraction
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (a : ConfigSpace V) (b : ConfigSpace W) : Real :=
  ∑ e ∈ StatMech.FK.fis_interface G H K,
    bond (isingSumConfigEquiv.symm (a, b)) e



noncomputable def unequalReplicaExp2
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (F : ConfigSpace V -> ConfigSpace W -> Real) : Real :=
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b * F a b) /
    (ZJ G.edgeFinset (fun _ => J) hf *
      ZJ H.edgeFinset (fun _ => J) hg)


noncomputable def unequalReplicaBridgeMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a b)) /
    (ZJ G.edgeFinset (fun _ => J) hf *
      ZJ H.edgeFinset (fun _ => J) hg)

noncomputable def unequalReplicaBridgeFreeEnergy
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  Real.log (unequalReplicaBridgeMoment G H K J hf hg r) -
    Real.log (unequalReplicaBridgeMoment G H K J hf hg (-r))


noncomputable def unequalReplicaBridgeMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        (unequalReplicaBridgeInteraction G H K a b *
          Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg)) /
    unequalReplicaBridgeMoment G H K J hf hg r



noncomputable def unequalReplicaBridgeVariance
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        (unequalReplicaBridgeInteraction G H K a b ^ 2 *
          Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg)) /
      unequalReplicaBridgeMoment G H K J hf hg r -
    unequalReplicaBridgeMean G H K J hf hg r ^ 2

theorem unequalReplicaBridgeMoment_pos
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    0 < unequalReplicaBridgeMoment G H K J hf hg r := by
  unfold unequalReplicaBridgeMoment
  apply div_pos
  · apply Finset.sum_pos
    · intro a _
      apply Finset.sum_pos
      · intro b _
        exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
          (Real.exp_pos _)
      · exact Finset.univ_nonempty
    · exact Finset.univ_nonempty
  · exact mul_pos (ZJ_pos _ _ _) (ZJ_pos _ _ _)



theorem wJ_crossInterface_factor
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (a : ConfigSpace V) (b : ConfigSpace W) :
    wJ K.edgeFinset (fun _ => J) (Sum.elim hf hg)
        (isingSumConfigEquiv.symm (a, b)) =
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        Real.exp (J * unequalReplicaBridgeInteraction G H K a b) := by
  classical
  unfold wJ unequalReplicaBridgeInteraction
  have hdisj : Disjoint ((G ⊕g H).edgeFinset)
      (StatMech.FK.fis_interface G H K) := by
    rw [StatMech.FK.fis_interface]
    exact Finset.disjoint_sdiff
  rw [StatMech.FK.fis_edgeFinset_eq hcross,
    Finset.sum_union hdisj]
  have hsumBase : (∑ e ∈ (G ⊕g H).edgeFinset,
        J * bond (isingSumConfigEquiv.symm (a, b)) e) =
      J * ∑ e ∈ (G ⊕g H).edgeFinset,
        bond (isingSumConfigEquiv.symm (a, b)) e := by
    rw [Finset.mul_sum]
  have hsumInterface : (∑ e ∈ StatMech.FK.fis_interface G H K,
        J * bond (isingSumConfigEquiv.symm (a, b)) e) =
      J * ∑ e ∈ StatMech.FK.fis_interface G H K,
        bond (isingSumConfigEquiv.symm (a, b)) e := by
    rw [Finset.mul_sum]
  rw [hsumBase, hsumInterface,
    StatMech.Ising.sum_bond_isingSumConfigEquiv_symm]
  simp only [Fintype.sum_sum_type, spin_isingSumConfigEquiv_symm_inl,
    spin_isingSumConfigEquiv_symm_inr]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hG : J * ∑ e ∈ G.edgeFinset, bond a e =
      ∑ e ∈ G.edgeFinset, J * bond a e := by
    simpa using (Finset.mul_sum G.edgeFinset (fun e => bond a e) J)
  have hH : J * ∑ e ∈ H.edgeFinset, bond b e =
      ∑ e ∈ H.edgeFinset, J * bond b e := by
    simpa using (Finset.mul_sum H.edgeFinset (fun e => bond b e) J)
  rw [mul_add, hG, hH]
  ring



theorem ZJ_crossInterface_eq_mul_unequalMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) :
    ZJ K.edgeFinset (fun _ => J) (Sum.elim hf hg) =
      ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg *
          unequalReplicaBridgeMoment G H K J hf hg J := by
  unfold ZJ
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [wJ_crossInterface_factor G H K hcross J hf hg]
  unfold unequalReplicaBridgeMoment
  have hZG : ZJ G.edgeFinset (fun _ => J) hf ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  have hZH : ZJ H.edgeFinset (fun _ => J) hg ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  unfold ZJ at hZG hZH ⊢
  field_simp [hZG, hZH]



theorem unequalReplicaBridgeInteraction_flip_right
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (a : ConfigSpace V) (b : ConfigSpace W) :
    unequalReplicaBridgeInteraction G H K a (FieldGhostDict.flipV b) =
      -unequalReplicaBridgeInteraction G H K a b := by
  classical
  unfold unequalReplicaBridgeInteraction
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      change s(x, y) ∈ K.edgeFinset \ (G ⊕g H).edgeFinset at he
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeFinset] at he
      obtain ⟨hK, hnot⟩ := he
      rcases x with x | x <;> rcases y with y | y
      · exact absurd
          (show (G ⊕g H).Adj (Sum.inl x) (Sum.inl y) from
            hcross.inl x y hK) hnot
      · rw [bond_mk, bond_mk,
          spin_isingSumConfigEquiv_symm_inl,
          spin_isingSumConfigEquiv_symm_inr,
          spin_isingSumConfigEquiv_symm_inl,
          spin_isingSumConfigEquiv_symm_inr,
          FieldGhostDict.spin_flipV]
        ring
      · rw [bond_mk, bond_mk,
          spin_isingSumConfigEquiv_symm_inr,
          spin_isingSumConfigEquiv_symm_inl,
          spin_isingSumConfigEquiv_symm_inr,
          spin_isingSumConfigEquiv_symm_inl,
          FieldGhostDict.spin_flipV]
        ring
      · exact absurd
          (show (G ⊕g H).Adj (Sum.inr x) (Sum.inr y) from
            hcross.inr x y hK) hnot

theorem unequalReplicaExp2_neg
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (F : ConfigSpace V -> ConfigSpace W -> Real) :
    unequalReplicaExp2 G H J hf hg (fun a b => -F a b) =
      -unequalReplicaExp2 G H J hf hg F := by
  unfold unequalReplicaExp2
  simp_rw [mul_neg]
  simp only [Finset.sum_neg_distrib]
  ring



theorem unequalReplicaExp2_flip_right
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (F : ConfigSpace V -> ConfigSpace W -> Real) :
    unequalReplicaExp2 G H J hf (fun x => -hg x) F =
      unequalReplicaExp2 G H J hf hg
        (fun a b => F a (FieldGhostDict.flipV b)) := by
  unfold unequalReplicaExp2
  rw [ghsvp_ZJ_negField]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive (V := W)).toPerm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.Involutive.coe_toPerm]
  rw [ghsvp_wJ_negField_flip]



theorem unequalReplicaBridgeMoment_neg_eq_negRightField
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeMoment G H K J hf hg (-r) =
      unequalReplicaBridgeMoment G H K J hf (fun x => -hg x) r := by
  change unequalReplicaExp2 G H J hf hg (fun a b =>
      Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) =
    unequalReplicaExp2 G H J hf (fun x => -hg x) (fun a b =>
      Real.exp (r * unequalReplicaBridgeInteraction G H K a b))
  rw [unequalReplicaExp2_flip_right]
  congr 1
  funext a b
  rw [unequalReplicaBridgeInteraction_flip_right G H K hcross]
  congr 1
  ring


theorem unequalReplicaBridgeMean_neg_eq_negRightField
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeMean G H K J hf hg (-r) =
      -unequalReplicaBridgeMean G H K J hf (fun x => -hg x) r := by
  unfold unequalReplicaBridgeMean
  change unequalReplicaExp2 G H J hf hg (fun a b =>
      unequalReplicaBridgeInteraction G H K a b *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf hg (-r) = _
  rw [unequalReplicaBridgeMoment_neg_eq_negRightField G H K hcross]
  change _ = -(unequalReplicaExp2 G H J hf (fun x => -hg x) (fun a b =>
      unequalReplicaBridgeInteraction G H K a b *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf (fun x => -hg x) r)
  rw [unequalReplicaExp2_flip_right]
  have hobs : (fun a b =>
      unequalReplicaBridgeInteraction G H K a (FieldGhostDict.flipV b) *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a
          (FieldGhostDict.flipV b))) =
      (fun a b => -(unequalReplicaBridgeInteraction G H K a b *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b))) := by
    funext a b
    rw [unequalReplicaBridgeInteraction_flip_right G H K hcross]
    rw [show r * -unequalReplicaBridgeInteraction G H K a b =
        -r * unequalReplicaBridgeInteraction G H K a b by ring]
    ring
  rw [hobs, unequalReplicaExp2_neg]
  ring



theorem unequalReplicaBridgeVariance_neg_eq_negRightField
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeVariance G H K J hf hg (-r) =
      unequalReplicaBridgeVariance G H K J hf (fun x => -hg x) r := by
  unfold unequalReplicaBridgeVariance
  change unequalReplicaExp2 G H J hf hg (fun a b =>
      unequalReplicaBridgeInteraction G H K a b ^ 2 *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf hg (-r) - _ = _
  rw [unequalReplicaBridgeMoment_neg_eq_negRightField G H K hcross,
    unequalReplicaBridgeMean_neg_eq_negRightField G H K hcross]
  change _ = unequalReplicaExp2 G H J hf (fun x => -hg x) (fun a b =>
      unequalReplicaBridgeInteraction G H K a b ^ 2 *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf (fun x => -hg x) r - _
  rw [unequalReplicaExp2_flip_right]
  have hobs : (fun a b =>
      unequalReplicaBridgeInteraction G H K a (FieldGhostDict.flipV b) ^ 2 *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a
          (FieldGhostDict.flipV b))) =
      (fun a b => unequalReplicaBridgeInteraction G H K a b ^ 2 *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) := by
    funext a b
    rw [unequalReplicaBridgeInteraction_flip_right G H K hcross]
    rw [show r * -unequalReplicaBridgeInteraction G H K a b =
        -r * unequalReplicaBridgeInteraction G H K a b by ring]
    ring
  rw [hobs]
  ring



theorem ZJ_crossInterface_negRight_eq_mul_unequalMoment_neg
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) :
    ZJ K.edgeFinset (fun _ => J) (Sum.elim hf (fun x => -hg x)) =
      ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg *
          unequalReplicaBridgeMoment G H K J hf hg (-J) := by
  unfold ZJ
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [wJ_crossInterface_factor G H K hcross J hf (fun x => -hg x)]
  have hinner (a : ConfigSpace V) :
      (∑ b : ConfigSpace W,
        wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
          Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) =
      ∑ b : ConfigSpace W,
        wJ H.edgeFinset (fun _ => J) hg b *
          Real.exp (-J * unequalReplicaBridgeInteraction G H K a b) := by
    rw [← Equiv.sum_comp
      (FieldGhostDict.flipV_involutive (V := W)).toPerm]
    apply Finset.sum_congr rfl
    intro b _
    change wJ H.edgeFinset (fun _ => J) (fun x => -hg x)
          (FieldGhostDict.flipV b) *
        Real.exp (J * unequalReplicaBridgeInteraction G H K a
          (FieldGhostDict.flipV b)) = _
    rw [ghsvp_wJ_negField_flip,
      unequalReplicaBridgeInteraction_flip_right G H K hcross]
    congr 1
    ring_nf
  have hdouble :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
          Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) =
      ∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
          Real.exp (-J * unequalReplicaBridgeInteraction G H K a b) := by
    apply Finset.sum_congr rfl
    intro a _
    calc
      (∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
              wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
            Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) =
          wJ G.edgeFinset (fun _ => J) hf a *
            (∑ b : ConfigSpace W,
              wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
                Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) := by
            rw [Finset.mul_sum]
            simp only [mul_assoc]
      _ = wJ G.edgeFinset (fun _ => J) hf a *
            (∑ b : ConfigSpace W,
              wJ H.edgeFinset (fun _ => J) hg b *
                Real.exp (-J * unequalReplicaBridgeInteraction G H K a b)) := by
            rw [hinner]
      _ = ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
              wJ H.edgeFinset (fun _ => J) hg b *
            Real.exp (-J * unequalReplicaBridgeInteraction G H K a b) := by
            rw [Finset.mul_sum]
            simp only [mul_assoc]
  rw [hdouble]
  unfold unequalReplicaBridgeMoment
  have hZG : ZJ G.edgeFinset (fun _ => J) hf ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  have hZH : ZJ H.edgeFinset (fun _ => J) hg ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  unfold ZJ at hZG hZH ⊢
  field_simp [hZG, hZH]

theorem hasDerivAt_unequalReplicaBridgeMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (unequalReplicaBridgeMoment G H K J hf hg)
      ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            (unequalReplicaBridgeInteraction G H K a b *
              Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
        (ZJ G.edgeFinset (fun _ => J) hf *
          ZJ H.edgeFinset (fun _ => J) hg)) r := by
  unfold unequalReplicaBridgeMoment
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  have hexp : HasDerivAt
      (fun t : Real => Real.exp
        (t * unequalReplicaBridgeInteraction G H K a b))
      (Real.exp (r * unequalReplicaBridgeInteraction G H K a b) *
        unequalReplicaBridgeInteraction G H K a b) r := by
    simpa using (Real.hasDerivAt_exp
      (r * unequalReplicaBridgeInteraction G H K a b)).comp r
        ((hasDerivAt_id r).mul_const
          (unequalReplicaBridgeInteraction G H K a b))
  convert hexp.const_mul
    (wJ G.edgeFinset (fun _ => J) hf a *
      wJ H.edgeFinset (fun _ => J) hg b) using 1 <;> ring

theorem hasDerivAt_unequalReplicaBridgeWeightedMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (fun t =>
      ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            (unequalReplicaBridgeInteraction G H K a b *
              Real.exp (t * unequalReplicaBridgeInteraction G H K a b))) /
        (ZJ G.edgeFinset (fun _ => J) hf *
          ZJ H.edgeFinset (fun _ => J) hg)))
      ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            (unequalReplicaBridgeInteraction G H K a b ^ 2 *
              Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
        (ZJ G.edgeFinset (fun _ => J) hf *
          ZJ H.edgeFinset (fun _ => J) hg)) r := by
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  have hexp : HasDerivAt
      (fun t : Real => Real.exp
        (t * unequalReplicaBridgeInteraction G H K a b))
      (Real.exp (r * unequalReplicaBridgeInteraction G H K a b) *
        unequalReplicaBridgeInteraction G H K a b) r := by
    simpa using (Real.hasDerivAt_exp
      (r * unequalReplicaBridgeInteraction G H K a b)).comp r
        ((hasDerivAt_id r).mul_const
          (unequalReplicaBridgeInteraction G H K a b))
  convert (hexp.const_mul
      (unequalReplicaBridgeInteraction G H K a b)).const_mul
    (wJ G.edgeFinset (fun _ => J) hf a *
      wJ H.edgeFinset (fun _ => J) hg b) using 1 <;> ring


theorem hasDerivAt_unequalReplicaBridgeMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (unequalReplicaBridgeMean G H K J hf hg)
      (unequalReplicaBridgeVariance G H K J hf hg r) r := by
  let N : Real -> Real := fun t =>
    ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
          wJ H.edgeFinset (fun _ => J) hg b *
          (unequalReplicaBridgeInteraction G H K a b *
            Real.exp (t * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg))
  let N2 : Real :=
    ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
          wJ H.edgeFinset (fun _ => J) hg b *
          (unequalReplicaBridgeInteraction G H K a b ^ 2 *
            Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg))
  let M := unequalReplicaBridgeMoment G H K J hf hg r
  have hN : HasDerivAt N N2 r := by
    simpa only [N, N2] using
      hasDerivAt_unequalReplicaBridgeWeightedMean G H K J hf hg r
  have hM := hasDerivAt_unequalReplicaBridgeMoment G H K J hf hg r
  have hMne : M ≠ 0 :=
    (unequalReplicaBridgeMoment_pos G H K J hf hg r).ne'
  have hquot := hN.div hM hMne
  change HasDerivAt (N / unequalReplicaBridgeMoment G H K J hf hg)
    (unequalReplicaBridgeVariance G H K J hf hg r) r
  convert hquot using 1
  unfold unequalReplicaBridgeVariance unequalReplicaBridgeMean
  dsimp only [N, N2, M]
  field_simp [(unequalReplicaBridgeMoment_pos G H K J hf hg r).ne',
    (ZJ_pos G.edgeFinset (fun _ => J) hf).ne',
    (ZJ_pos H.edgeFinset (fun _ => J) hg).ne']
  have hsecond :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            unequalReplicaBridgeInteraction G H K a b ^ 2 *
          Real.exp (unequalReplicaBridgeInteraction G H K a b * r)) =
      ∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            unequalReplicaBridgeInteraction G H K a b ^ 2 *
          Real.exp (r * unequalReplicaBridgeInteraction G H K a b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm (unequalReplicaBridgeInteraction G H K a b) r]
  rw [hsecond]
  ring

theorem hasDerivAt_log_unequalReplicaBridgeMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (fun t =>
      Real.log (unequalReplicaBridgeMoment G H K J hf hg t))
      (unequalReplicaBridgeMean G H K J hf hg r) r := by
  exact (hasDerivAt_unequalReplicaBridgeMoment G H K J hf hg r).log
    (unequalReplicaBridgeMoment_pos G H K J hf hg r).ne'

theorem hasDerivAt_unequalReplicaBridgeFreeEnergy
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (unequalReplicaBridgeFreeEnergy G H K J hf hg)
      (unequalReplicaBridgeMean G H K J hf hg r +
        unequalReplicaBridgeMean G H K J hf hg (-r)) r := by
  unfold unequalReplicaBridgeFreeEnergy
  have hp := hasDerivAt_log_unequalReplicaBridgeMoment
    G H K J hf hg r
  have hm := (hasDerivAt_log_unequalReplicaBridgeMoment
    G H K J hf hg (-r)).comp r (hasDerivAt_id r).neg
  convert hp.sub hm using 1 <;> ring

theorem hasDerivAt_unequalReplicaBridgeSymmetricMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (fun t =>
      unequalReplicaBridgeMean G H K J hf hg t +
        unequalReplicaBridgeMean G H K J hf hg (-t))
      (unequalReplicaBridgeVariance G H K J hf hg r -
        unequalReplicaBridgeVariance G H K J hf hg (-r)) r := by
  have hp := hasDerivAt_unequalReplicaBridgeMean G H K J hf hg r
  have hm := (hasDerivAt_unequalReplicaBridgeMean
    G H K J hf hg (-r)).comp r (hasDerivAt_id r).neg
  convert hp.add hm using 1 <;> ring



theorem unequalReplicaBridgeFreeEnergy_le_of_variance_order
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (r : Real) (hr : 0 <= r)
    (hvar : forall t, 0 <= t ->
      unequalReplicaBridgeVariance G H K J hf hg t <=
        unequalReplicaBridgeVariance G H K J hf hg (-t)) :
    unequalReplicaBridgeFreeEnergy G H K J hf hg r <=
      2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
  let D : Real -> Real := fun t =>
    unequalReplicaBridgeMean G H K J hf hg t +
      unequalReplicaBridgeMean G H K J hf hg (-t)
  have hdiffD : Differentiable Real D := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
      G H K J hf hg t).differentiableAt
  have hanti : AntitoneOn D (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : Real))
    · exact hdiffD.continuous.continuousOn
    · intro t _
      exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).deriv]
      exact sub_nonpos.mpr (hvar t ht.le)
  have hmean : forall t, 0 <= t -> D t <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    intro t ht
    have hle := hanti (by simp) ht ht
    dsimp only [D] at hle
    rw [neg_zero] at hle
    linarith
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [unequalReplicaBridgeFreeEnergy]
  have hdiffAll : Differentiable Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg t).differentiableAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope
    (unequalReplicaBridgeFreeEnergy G H K J hf hg) hrpos
    hdiffAll.continuous.continuousOn hdiffAll.differentiableOn
  have hderiv : deriv
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) c <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    rw [(hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg c).deriv]
    exact hmean c hc.1.le
  have hzero : unequalReplicaBridgeFreeEnergy G H K J hf hg 0 = 0 := by
    simp [unequalReplicaBridgeFreeEnergy]
  have hmul := mul_le_mul_of_nonneg_right hderiv hrpos.le
  rw [hslope, hzero] at hmul
  simp only [sub_zero] at hmul
  rw [div_mul_cancel₀ _ hrpos.ne'] at hmul
  convert hmul using 1 <;> ring




def oddPrismAtOrBelowCenter (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) : Prop :=
  v.z.val <= n

instance oddPrismAtOrBelowCenter_decidablePred (n : Nat) :
    DecidablePred (oddPrismAtOrBelowCenter n) :=
  fun _ => by
    unfold oddPrismAtOrBelowCenter
    infer_instance

abbrev OddPrismLowerBlockSite (n : Nat) :=
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
    oddPrismAtOrBelowCenter n v}

abbrev OddPrismUpperBlockSite (n : Nat) :=
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
    ¬ oddPrismAtOrBelowCenter n v}


noncomputable abbrev oddPrismLowerBlockGraph (n : Nat) :
    SimpleGraph (OddPrismLowerBlockSite n) :=
  StatMech.FK.agl_left (oddPrismInternalGraph n)
    (oddPrismAtOrBelowCenter n)


noncomputable abbrev oddPrismUpperBlockGraph (n : Nat) :
    SimpleGraph (OddPrismUpperBlockSite n) :=
  StatMech.FK.agl_right (oddPrismInternalGraph n)
    (oddPrismAtOrBelowCenter n)



noncomputable abbrev oddPrismUnequalGlueGraph (n : Nat) :
    SimpleGraph (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n) :=
  StatMech.FK.agl_glueGraph (oddPrismInternalGraph n)
    (oddPrismAtOrBelowCenter n)


noncomputable def oddPrismUnequalBridgeMoment
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact unequalReplicaBridgeMoment
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1) r



noncomputable def oddPrismUnequalBridgeFreeEnergy
    (beta : Real) (n : Nat) : Real :=
  Real.log (oddPrismUnequalBridgeMoment beta n beta) -
    Real.log (oddPrismUnequalBridgeMoment beta n (-beta))

set_option maxHeartbeats 800000 in



theorem oddPrismUnequalGlue_plus_partition
    (beta : Real) (n : Nat) :
    ZJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta)
        (Sum.elim
          (fun v : OddPrismLowerBlockSite n =>
            beta * oddPrismPlusField n v.1)
          (fun v : OddPrismUpperBlockSite n =>
            beta * oddPrismPlusField n v.1)) =
      scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismPlusField n) beta := by
  classical
  let e := StatMech.FK.agl_sumEquiv (oddPrismAtOrBelowCenter n)
  have h := ghsi_ZJ_const_relabel
    (oddPrismUnequalGlueGraph n) (oddPrismInternalGraph n) e
    (by
      intro u v
      simpa [oddPrismUnequalGlueGraph, e] using
        (StatMech.FK.agl_glueGraph_adj
          (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n) u v))
    beta
    (Sum.elim
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))
    (fun v => beta * oddPrismPlusField n v) (by
      intro v
      rcases v with v | v <;> rfl)
  calc
    _ = ZJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v) := h
    _ = _ := by
      unfold scaledInhomogeneousPartition
      rw [oddPrismInternalGraph_edgeFinset]
      simp only [mul_one]

set_option maxHeartbeats 800000 in



theorem oddPrismUnequalGlue_dobrushin_partition
    (beta : Real) (n : Nat) :
    ZJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta)
        (Sum.elim
          (fun v : OddPrismLowerBlockSite n =>
            beta * oddPrismPlusField n v.1)
          (fun v : OddPrismUpperBlockSite n =>
            -(beta * oddPrismPlusField n v.1))) =
      scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismDobrushinField n) beta := by
  classical
  let e := StatMech.FK.agl_sumEquiv (oddPrismAtOrBelowCenter n)
  have hfield : forall v : OddPrismLowerBlockSite n ⊕
      OddPrismUpperBlockSite n,
      Sum.elim
          (fun u : OddPrismLowerBlockSite n =>
            beta * oddPrismPlusField n u.1)
          (fun u : OddPrismUpperBlockSite n =>
            -(beta * oddPrismPlusField n u.1)) v =
        beta * oddPrismDobrushinField n (e v) := by
    intro v
    rcases v with v | v
    · have hv : ¬ n < v.1.z.val := by
        exact Nat.not_lt_of_ge v.2
      simp [e, oddPrismPlusField, oddPrismDobrushinField,
        oddRectangularPrismDobrushinSign, hv]
    · have hv : n < v.1.z.val := by
        simpa [oddPrismAtOrBelowCenter, Nat.not_le] using v.2
      simp [e, oddPrismPlusField, oddPrismDobrushinField,
        oddRectangularPrismDobrushinSign, hv]
  have h := ghsi_ZJ_const_relabel
    (oddPrismUnequalGlueGraph n) (oddPrismInternalGraph n) e
    (by
      intro u v
      simpa [oddPrismUnequalGlueGraph, e] using
        (StatMech.FK.agl_glueGraph_adj
          (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n) u v))
    beta
    (Sum.elim
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
    (fun v : OddPrismUpperBlockSite n =>
        -(beta * oddPrismPlusField n v.1)))
    (fun v => beta * oddPrismDobrushinField n v) hfield
  calc
    _ = ZJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismDobrushinField n v) := h
    _ = _ := by
      unfold scaledInhomogeneousPartition
      rw [oddPrismInternalGraph_edgeFinset]
      simp only [mul_one]



theorem rectangularPrismPlusPartition_eq_unequalBridge
    (beta : Real) (n : Nat) :
    rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n =
      ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        oddPrismUnequalBridgeMoment beta n beta := by
  classical
  rw [← scaledInhomogeneousPartition_oddPrismPlus,
    ← oddPrismUnequalGlue_plus_partition]
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  simpa [oddPrismUnequalBridgeMoment] using
    (ZJ_crossInterface_eq_mul_unequalMoment
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n)) beta
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))



theorem rectangularPrismDobrushinPartition_eq_unequalBridge
    (beta : Real) (n : Nat) :
    rectangularPrismDobrushinPartition 1 beta
        (2 * n + 1) (2 * n + 1) n =
      ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        oddPrismUnequalBridgeMoment beta n (-beta) := by
  classical
  rw [← scaledInhomogeneousPartition_oddPrismDobrushin,
    ← oddPrismUnequalGlue_dobrushin_partition]
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  simpa [oddPrismUnequalBridgeMoment] using
    (ZJ_crossInterface_negRight_eq_mul_unequalMoment_neg
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n)) beta
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))



theorem rectangularDobrushinFreeEnergy_eq_oddPrismUnequalBridge
    (beta : Real) (n : Nat) :
    StatMech.Ising.rectangularDobrushinFreeEnergy 1 beta
        (2 * n + 1) (2 * n + 1) n =
      oddPrismUnequalBridgeFreeEnergy beta n := by
  classical
  let ZL := ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
  let ZU := ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
  have hbase : ZL * ZU ≠ 0 := mul_ne_zero
    (ZJ_pos _ _ _).ne' (ZJ_pos _ _ _).ne'
  have hplus := rectangularPrismPlusPartition_eq_unequalBridge beta n
  have hdobr := rectangularPrismDobrushinPartition_eq_unequalBridge beta n
  have hplusMoment : oddPrismUnequalBridgeMoment beta n beta ≠ 0 := by
    intro hm
    have hz : rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n = 0 := by
      simpa [ZL, ZU, hm] using hplus
    have hp : 0 < rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
      rw [← scaledInhomogeneousPartition_oddPrismPlus]
      unfold scaledInhomogeneousPartition
      exact ZJ_pos _ _ _
    exact hp.ne' hz
  have hdobrMoment : oddPrismUnequalBridgeMoment beta n (-beta) ≠ 0 := by
    intro hm
    have hz : rectangularPrismDobrushinPartition 1 beta
        (2 * n + 1) (2 * n + 1) n = 0 := by
      simpa [ZL, ZU, hm] using hdobr
    have hp : 0 < rectangularPrismDobrushinPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
      rw [← scaledInhomogeneousPartition_oddPrismDobrushin]
      unfold scaledInhomogeneousPartition
      exact ZJ_pos _ _ _
    exact hp.ne' hz
  rw [StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio,
    hplus, hdobr]
  change Real.log (ZL * ZU * oddPrismUnequalBridgeMoment beta n beta) -
      Real.log (ZL * ZU * oddPrismUnequalBridgeMoment beta n (-beta)) = _
  rw [Real.log_mul hbase hplusMoment,
    Real.log_mul hbase hdobrMoment]
  unfold oddPrismUnequalBridgeFreeEnergy
  ring


theorem standardCubicInterfaceDensity_eq_oddPrismUnequalBridge
    (beta : Real) (n : Nat) (hn : 0 < n) :
    standardCubicInterfaceDensity beta n =
      oddPrismUnequalBridgeFreeEnergy beta n /
        (((2 * n + 1 : Nat) : Real) ^ 2) := by
  rw [standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
    beta n hn]
  unfold rectangularPrismInterfaceDensity
  rw [rectangularDobrushinFreeEnergy_eq_oddPrismUnequalBridge]










def OddPrismUnequalBridgeVarianceOrder (beta : Real) (n : Nat) : Prop :=
  forall t, 0 <= t ->
    unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) t <=
      unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) (-t)



def OddPrismUnequalBridgeCrossFieldVarianceOrder
    (beta : Real) (n : Nat) : Prop :=
  forall t, 0 <= t ->
    unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) t <=
      unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => -(beta * oddPrismPlusField n v.1)) t

theorem oddPrismUnequalBridgeVarianceOrder_iff_crossField
    (beta : Real) (n : Nat) :
    OddPrismUnequalBridgeVarianceOrder beta n <->
      OddPrismUnequalBridgeCrossFieldVarianceOrder beta n := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold OddPrismUnequalBridgeVarianceOrder
    OddPrismUnequalBridgeCrossFieldVarianceOrder
  constructor <;> intro h t ht
  · rw [← unequalReplicaBridgeVariance_neg_eq_negRightField
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n))]
    exact h t ht
  · rw [unequalReplicaBridgeVariance_neg_eq_negRightField
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n))]
    exact h t ht



theorem oddPrismUnequalBridgeFreeEnergy_le_of_variance_order
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (hvar : OddPrismUnequalBridgeVarianceOrder beta n) :
    oddPrismUnequalBridgeFreeEnergy beta n <=
      2 * beta * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  change unequalReplicaBridgeFreeEnergy
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) beta
      (fun v => beta * oddPrismPlusField n v.1)
      (fun v => beta * oddPrismPlusField n v.1) beta <= _
  apply unequalReplicaBridgeFreeEnergy_le_of_variance_order
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1) beta hbeta
  exact hvar

end

end StatMech.FrontierA
