/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Code.Universality.IsingFermionicSquareCaratheodory









namespace StatMech.Universality

open Filter Set Topology Metric

noncomputable section



theorem fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable
    (k : Nat) :
    Differentiable Complex
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        k) := by
  change Differentiable Complex (fun z ↦
    fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) z /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
  exact
    (fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_differentiable
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k)
      (fkIsingExpandingSquareScale_pos k)).div_const _



theorem fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic :
    ∀ k, DifferentiableOn Complex
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        k) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U :=
  fun k ↦
    (fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k).differentiableOn




noncomputable def fkIsingExpandingBoundarySquareRadialSupport (k : Nat) :
    Finset (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) := by
  classical
  by_cases hk : 15 ≤ k
  · let n := fkIsingExpandingSquareSide k
    let m := k + 1
    let base := k / 4
    let R := k / 4
    have hm : m ≤ n := by
      simp [m, n, fkIsingExpandingSquareSide]
      nlinarith
    have hfit : base + R + 1 < m := by
      simp [base, R, m]
      omega
    exact Finset.univ.map
      (fkIsingSquareRadialPatchWindowCarrierEmbedding
        n m base base R hm hfit hfit)
  · exact {.source}

theorem fkIsingExpandingBoundarySquareRadialSupport_nonempty (k : Nat) :
    (fkIsingExpandingBoundarySquareRadialSupport k).Nonempty := by
  classical
  rw [fkIsingExpandingBoundarySquareRadialSupport]
  split_ifs <;> simp



theorem fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageNormSq :
    FKIsingCaratheodoryApproximation.HasEventualCompactAverageNormSq
      fkIsingExpandingBoundarySquareCaratheodoryApproximation
      fkIsingExpandingBoundarySquareRadialSupport := by
  intro K _hK _hKU
  refine ⟨4096, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 15] with k hk
  let n := fkIsingExpandingSquareSide k
  let m := k + 1
  let base := k / 4
  let R := k / 4
  let r := k / 8
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hm : m ≤ n := by
    simp [m, n, fkIsingExpandingSquareSide]
    nlinarith
  have hm2 : 2 ≤ m := by simp [m]; omega
  have hr : 0 < r := by simp [r]; omega
  have hfit : base + R + 1 < m := by
    simp [base, R, m]
    omega
  have hleft : r ≤ base := by simp [r, base]; omega
  have hfar : base + R + 1 + r < m := by
    simp [base, R, r, m]
    omega
  have hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m base base R hfit hfit p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r := by
    intro p
    exact fkIsingSquareRadialPatchWindowCell_mem_deepCells_of_margin
      n m base base R r hm hm2 hfit hfit hleft hleft hfar hfar p
  have hmrNat : m ≤ 16 * r := by
    simp [m, r]
    omega
  have hmr : (m : Real) ≤ 16 * (r : Real) := by exact_mod_cast hmrNat
  have hmRNat : m ≤ 4 * (R + 1) := by
    simp [m, R]
    omega
  have hmR : (m : Real) ≤ 4 * (R + 1 : Nat) := by exact_mod_cast hmRNat
  have hmesh : 0 < fkIsingExpandingSquareMesh k :=
    fkIsingExpandingSquareMesh_pos k
  have hmeshLower : 1 / (m : Real) ≤ fkIsingExpandingSquareMesh k := by
    simp only [m, fkIsingExpandingSquareMesh, fkIsingExpandingSquareScale]
    have hnonneg : 0 ≤ 1 / ((k + 1 : Nat) : Real) := by positivity
    nlinarith
  have havg :=
    fkIsingSquareBoundaryRadialPatchWindowCarrier_average_normSq_le
      n m base base R r (fkIsingExpandingSquareMesh k) 16 4
      hn hm hm2 hr hfit hfit hmesh hmeshLower
      (by norm_num) (by norm_num) hmr hmR hdeep
  constructor
  · exact fkIsingExpandingBoundarySquareRadialSupport_nonempty k
  · have hconstant : (16 : Real) * 16 * 4 ^ 2 = 4096 := by norm_num
    rw [hconstant] at havg
    simpa [fkIsingExpandingBoundarySquareRadialSupport, hk, n, m, base, R,
      fkIsingExpandingBoundarySquareCaratheodoryApproximation,
      FKIsingDobrushinDomain.normalizedFermionicObservable,
      fkIsingExpandingSquareMesh, fkIsingExpandingSquareScale] using havg



theorem fkIsingExpandingBoundarySquareRadialSupport_mem_closedBall
    (k : Nat)
    (a : fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
    (hk : 15 ≤ k)
    (ha : a ∈ fkIsingExpandingBoundarySquareRadialSupport k) :
    dist
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
          k a) 0 ≤ 4 := by
  classical
  let n := fkIsingExpandingSquareSide k
  let m := k + 1
  let base := k / 4
  let R := k / 4
  have hm : m ≤ n := by
    simp [m, n, fkIsingExpandingSquareSide]
    nlinarith
  have hm2 : 2 ≤ m := by simp [m]; omega
  have hfit : base + R + 1 < m := by
    simp [base, R, m]
    omega
  rw [fkIsingExpandingBoundarySquareRadialSupport] at ha
  simp only [hk, ↓reduceDIte] at ha
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_map.mp ha
  have hbase := fkIsingSquareRadialPatchWindowCarrier_scaledPosition_norm_le
    n m base base R hm hm2 hfit hfit p
  have hnear := fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    n (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
    (fkIsingSquareRadialPatchWindowCarrier
      n m base base R hm hfit hfit p)
  change dist (fkIsingSquareWiredPerturbedCarrierPosition
      n (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
      (fkIsingSquareRadialPatchWindowCarrier
        n m base base R hm hfit hfit p)) 0 ≤ 4
  rw [dist_zero_right]
  apply le_of_lt
  calc
    ‖fkIsingSquareWiredPerturbedCarrierPosition
        n (fkIsingExpandingSquareSide_pos k)
        (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
        (fkIsingSquareRadialPatchWindowCarrier
          n m base base R hm hfit hfit p)‖ ≤
      ‖((fkIsingExpandingSquareScale k : Real) : Complex) *
        fkIsingSquareWiredCarrierPosition n (fkIsingExpandingSquareSide_pos k)
          (fkIsingSquareRadialPatchWindowCarrier
            n m base base R hm hfit hfit p)‖ +
        dist (fkIsingSquareWiredPerturbedCarrierPosition
          n (fkIsingExpandingSquareSide_pos k)
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
          (fkIsingSquareRadialPatchWindowCarrier
            n m base base R hm hfit hfit p))
          (((fkIsingExpandingSquareScale k : Real) : Complex) *
            fkIsingSquareWiredCarrierPosition n
              (fkIsingExpandingSquareSide_pos k)
              (fkIsingSquareRadialPatchWindowCarrier
                n m base base R hm hfit hfit p)) := by
      simpa [dist_eq_norm] using
        (norm_le_norm_add_norm_sub'
          (fkIsingSquareWiredPerturbedCarrierPosition
            n (fkIsingExpandingSquareSide_pos k)
            (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
            (fkIsingSquareRadialPatchWindowCarrier
              n m base base R hm hfit hfit p))
          (((fkIsingExpandingSquareScale k : Real) : Complex) *
            fkIsingSquareWiredCarrierPosition n
              (fkIsingExpandingSquareSide_pos k)
              (fkIsingSquareRadialPatchWindowCarrier
                n m base base R hm hfit hfit p)))
    _ < 3 + fkIsingExpandingSquareScale k / 10 :=
      add_lt_add_of_le_of_lt
        (by simpa [m, fkIsingExpandingSquareScale] using hbase) hnear
    _ < 4 := by
      have hs : fkIsingExpandingSquareScale k ≤ 1 := by
        rw [fkIsingExpandingSquareScale, one_div]
        apply inv_le_one_of_one_le₀
        norm_num
      linarith



theorem fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactWindowDiameter :
    FKIsingCaratheodoryApproximation.HasEventualCompactWindowDiameter
      fkIsingExpandingBoundarySquareCaratheodoryApproximation
      fkIsingExpandingBoundarySquareRadialSupport := by
  apply
    FKIsingCaratheodoryApproximation.hasEventualCompactWindowDiameter_of_commonBall
  intro K hK _hKU
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  let B := max 4 (C + 4)
  refine ⟨0, B, (show (0 : Real) ≤ 4 by norm_num).trans
    (le_max_left 4 (C + 4)), ?_⟩
  filter_upwards [eventually_ge_atTop 15] with k hk
  have hscale : fkIsingExpandingSquareScale k ≤ 1 := by
    rw [fkIsingExpandingSquareScale, one_div]
    apply inv_le_one_of_one_le₀
    norm_num
  have hmesh : fkIsingExpandingSquareMesh k ≤ 4 := by
    rw [fkIsingExpandingSquareMesh]
    nlinarith
  constructor
  · intro a ha
    exact
      (fkIsingExpandingBoundarySquareRadialSupport_mem_closedBall k a hk ha).trans
        (le_max_left 4 (C + 4))
  · intro e he
    obtain ⟨z, hzK, hznear⟩ := he
    have hzC : dist z 0 ≤ C := hC hzK
    calc
      dist
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
            k e) 0 ≤
        dist
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
              k e) z + dist z 0 := dist_triangle _ _ _
      _ ≤ fkIsingExpandingSquareMesh k + C :=
        add_le_add (by simpa [dist_comm] using hznear) hzC
      _ ≤ 4 + C := by simpa [add_comm] using add_le_add_right hmesh C
      _ = C + 4 := by ring
      _ ≤ B := le_max_right 4 (C + 4)



theorem fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageEnergy :
    FKIsingCaratheodoryApproximation.HasEventualCompactAverageEnergy
      fkIsingExpandingBoundarySquareCaratheodoryApproximation
      fkIsingExpandingBoundarySquareRadialSupport :=
  ⟨fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageNormSq,
    fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactWindowDiameter⟩



theorem fkIsingExpandingBoundarySquare_eventualMedialBounds
    (I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation) :
    ∀ K : Set Complex, IsCompact K →
      K ⊆ fkIsingExpandingBoundarySquareCaratheodoryApproximation.U →
      ∃ B : Real, ∀ᶠ k in atTop,
        ∀ e : fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k,
          (∃ z ∈ K,
            dist z
              (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding
                k e) ≤
              fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) →
          ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
            (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) e‖ ≤ B :=
  FKIsingCaratheodoryApproximation.eventualMedialBounds_of_holderInterpolation_and_averageEnergy
      fkIsingExpandingBoundarySquareCaratheodoryApproximation I
      fkIsingExpandingBoundarySquareRadialSupport
      fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageEnergy




theorem fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_primitiveIm
    (I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun k ↦
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
            (phi (psi k))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U →
      ∃ (P : Complex → Complex) (C : Real),
        DifferentiableOn Complex P
            fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
        Set.EqOn (deriv P) (fun z ↦ f z ^ 2)
            fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
        (∀ z ∈ fkIsingExpandingBoundarySquareCaratheodoryApproximation.U,
          (P z).im = (Phi z).im + C) ∧
        f fkIsingExpandingBoundarySquareCaratheodoryApproximation.root =
          target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) :
    TendstoLocallyUniformlyOn
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
      TendstoLocallyUniformlyOn
        (deriv ∘
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant)
        (deriv target) atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  exact
    FKIsingCaratheodoryApproximation.scalingLimit_of_holderAverageEnergy_and_primitiveIm
      fkIsingExpandingBoundarySquareCaratheodoryApproximation I
      fkIsingExpandingBoundarySquareRadialSupport target Phi
      fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic htarget
      htarget_ne hPhi hPhideriv E
      fkIsingExpandingBoundarySquareRadialSupport_hasEventualCompactAverageEnergy
      hidentifyPrimitive






theorem
    fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveIm
    (I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hidentifyDense : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun k ↦
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
            (phi (psi k))) f atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U →
      ∃ (S : Set Complex) (C : Real), Dense S ∧
        Set.EqOn
          (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im)
          (fun z ↦ (Phi z).im + C) S ∧
        f fkIsingExpandingBoundarySquareCaratheodoryApproximation.root =
          target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) :
    TendstoLocallyUniformlyOn
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
      TendstoLocallyUniformlyOn
        (deriv ∘
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant)
        (deriv target) atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  apply fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_primitiveIm
    I target Phi htarget htarget_ne hPhi hPhideriv E
  intro phi psi f hphi hpsi hlimit
  obtain ⟨S, C, hSdense, hsample, hanchor⟩ :=
    hidentifyDense phi psi f hphi hpsi hlimit
  have hfOn : DifferentiableOn Complex f Set.univ :=
    hlimit.differentiableOn
      (Filter.Eventually.of_forall (fun k ↦
        fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic
          (phi (psi k)))) isOpen_univ
  have hf : Differentiable Complex f := differentiableOn_univ.mp hfOn
  have hPhiFull : Differentiable Complex Phi := differentiableOn_univ.mp hPhi
  refine ⟨isingFermionicEntireSquarePrimitive f, C,
    (isingFermionicEntireSquarePrimitive_differentiable hf).differentiableOn,
    ?_, ?_, hanchor⟩
  · intro z _hz
    exact (isingFermionicEntireSquarePrimitive_hasDerivAt hf z).deriv
  · intro z _hz
    exact isingFermionicEntireSquarePrimitive_im_eq_of_dense
      hf hPhiFull.continuous S hSdense C hsample z

end

end StatMech.Universality
