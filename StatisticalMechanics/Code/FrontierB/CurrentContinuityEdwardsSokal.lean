/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierB.CurrentContinuityFKBridge
import Code.FrontierB.CurrentContinuityAdjacentInfluence
import Code.FrontierB.FreeMultipointEdwardsSokal
import Code.FrontierB.FreeBoxEvenLimit
import Code.IsingFK.HisingBoxClose
import Code.FK.DensityFiniteToInfinite
import Code.FK.FKUniqPerEdge

open Filter MeasureTheory Set
open scoped BigOperators

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Sharpness
open StatMech.IsingFK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in


theorem monoIndicator_pair_eq_half_one_add_esSpinProduct
    (sigma : V → Fin 2) (x y : V) (hxy : x ≠ y) :
    Potts.monoIndicator sigma s(x, y) =
      (1 + esSpinProduct ({x, y} : Finset V) sigma) / 2 := by
  rw [Potts.monoIndicator_mk, esSpinProduct, Finset.prod_pair hxy,
    isingSpin_mul]
  by_cases h : sigma x = sigma y <;> simp [h]



theorem esMonoExpectation_eq_half_one_add_isingExpectation
    (beta : Real) (x y : V) (hxy : x ≠ y) :
    (∑ sigma : V → Fin 2,
        esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma *
          Potts.monoIndicator sigma s(x, y)) =
      (1 + Ising.isingExpectation G beta 0
        (spinProd ({x, y} : Finset V))) / 2 := by
  let A : Finset V := {x, y}
  have hAeven : Even A.card := by simp [A, hxy]
  have hmulti :
      esMultiPoint G (1 - Real.exp (-2 * beta)) A =
        Ising.isingExpectation G beta 0 (spinProd A) := by
    rw [esMultiPoint_eq_allClustersEvenProb,
      isingExpectation_spinProd_eq_allClustersEvenProb G beta A hAeven]
  have hfirst :
      (∑ sigma : V → Fin 2,
        esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma) = 1 := by
    convert (esFirstMarginal_sum_eq_one G (q := 2) (2 * beta) 1) using 1
    all_goals ring_nf
  have hspin :
      (∑ sigma : V → Fin 2,
        esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma *
          esSpinProduct A sigma) =
        Ising.isingExpectation G beta 0 (spinProd A) := by
    rw [← esMultiPoint_eq_firstMarginal_sum G _ A, hmulti]
  calc
    (∑ sigma : V → Fin 2,
        esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma *
          Potts.monoIndicator sigma s(x, y)) =
        ∑ sigma : V → Fin 2,
          (esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma +
            esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma *
              esSpinProduct A sigma) / 2 := by
          apply Finset.sum_congr rfl
          intro sigma _
          rw [monoIndicator_pair_eq_half_one_add_esSpinProduct sigma x y hxy]
          simp only [A]
          ring
    _ = ((∑ sigma : V → Fin 2,
          esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma) +
        (∑ sigma : V → Fin 2,
          esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma *
            esSpinProduct A sigma)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = _ := by rw [hfirst, hspin]



theorem edgeMargProb_fkProb_eq_p_div_two_mul_one_add_isingExpectation
    (beta : Real) (x y : V) (hxy : x ≠ y)
    (hedge : s(x, y) ∈ G.edgeFinset) :
    edgeMargProb (fkProb G (1 - Real.exp (-2 * beta)) 2) s(x, y) =
      (1 - Real.exp (-2 * beta)) / 2 *
        (1 + Ising.isingExpectation G beta 0
          (spinProd ({x, y} : Finset V))) := by
  have h := edgeMargProb_fkProb_eq_p_mul_esMono G 2
    (1 - Real.exp (-2 * beta)) s(x, y) hedge
  rw [esMonoExpectation_eq_half_one_add_isingExpectation G beta x y hxy] at h
  convert h using 1
  all_goals ring



theorem esWeightWired_open_sum_eq
    (bdry : V → Prop) [DecidablePred bdry]
    (beta : Real) (sigma : V → Fin 2) (x y : V)
    (hedge : s(x, y) ∈ G.edgeFinset) :
    (∑ omega : ConfigSpace (Sym2 V),
        esWeightWired G bdry (0 : Fin 2) (1 - Real.exp (-2 * beta)) sigma omega *
          (if omega s(x, y) then 1 else 0)) =
      (1 - Real.exp (-2 * beta)) * Potts.monoIndicator sigma s(x, y) *
        ∑ omega : ConfigSpace (Sym2 V),
          esWeightWired G bdry (0 : Fin 2)
            (1 - Real.exp (-2 * beta)) sigma omega := by
  unfold esWeightWired
  by_cases hbdry : BoundaryFixed bdry (0 : Fin 2) sigma
  · simp only [if_pos hbdry]
    exact esWeight_open_sum_eq G 2 (1 - Real.exp (-2 * beta)) sigma s(x, y) hedge
  · simp [hbdry]



theorem edgeMargProb_wiredFkProb_eq_p_mul_esWiredMono
    (bdry : V → Prop) [DecidablePred bdry]
    (v0 : V) (hv0 : bdry v0) (beta : Real) (x y : V)
    (hedge : s(x, y) ∈ G.edgeFinset) :
    edgeMargProb
        (wiredFkProb G bdry (1 - Real.exp (-2 * beta)) 2) s(x, y) =
      (1 - Real.exp (-2 * beta)) *
        ∑ sigma : V → Fin 2,
          esWiredFirstMarginal G bdry 2 (0 : Fin 2)
              (1 - Real.exp (-2 * beta)) sigma *
            Potts.monoIndicator sigma s(x, y) := by
  have hq : ∀ omega : ConfigSpace (Sym2 V),
      1 ≤ numClustersBC G (boundaryCliqueGraph bdry) omega :=
    fun omega => one_le_numClustersBC G bdry v0 omega
  have hedgeLaw : wiredFkProb G bdry (1 - Real.exp (-2 * beta)) 2 =
      esWiredSecondMarginal G bdry 2 (0 : Fin 2)
        (1 - Real.exp (-2 * beta)) := by
    funext omega
    rw [wiredFkProb_eq_bcProb]
    exact (esWiredSecondMarginal_eq_bcProb G bdry (0 : Fin 2)
      (1 - Real.exp (-2 * beta)) omega v0 hv0 (by omega) hq).symm
  rw [hedgeLaw]
  unfold edgeMargProb esWiredSecondMarginal esWiredFirstMarginal
  calc
    (∑ omega : ConfigSpace (Sym2 V),
        (if omega s(x, y) then 1 else 0) *
          ((∑ sigma : V → Fin 2,
            esWeightWired G bdry (0 : Fin 2)
              (1 - Real.exp (-2 * beta)) sigma omega) /
          esZWired G bdry 2 (0 : Fin 2) (1 - Real.exp (-2 * beta)))) =
      (∑ omega : ConfigSpace (Sym2 V),
        (if omega s(x, y) then 1 else 0) *
          (∑ sigma : V → Fin 2,
            esWeightWired G bdry (0 : Fin 2)
              (1 - Real.exp (-2 * beta)) sigma omega)) /
        esZWired G bdry 2 (0 : Fin 2) (1 - Real.exp (-2 * beta)) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro omega _
          ring
    _ =
      (∑ sigma : V → Fin 2,
          (1 - Real.exp (-2 * beta)) * Potts.monoIndicator sigma s(x, y) *
            (∑ omega : ConfigSpace (Sym2 V),
              esWeightWired G bdry (0 : Fin 2)
                (1 - Real.exp (-2 * beta)) sigma omega)) /
        esZWired G bdry 2 (0 : Fin 2) (1 - Real.exp (-2 * beta)) := by
          congr 1
          calc
            (∑ omega : ConfigSpace (Sym2 V),
                (if omega s(x, y) then 1 else 0) *
                  ∑ sigma : V → Fin 2,
                    esWeightWired G bdry (0 : Fin 2)
                      (1 - Real.exp (-2 * beta)) sigma omega) =
              ∑ omega : ConfigSpace (Sym2 V),
                ∑ sigma : V → Fin 2,
                  (if omega s(x, y) then 1 else 0) *
                    esWeightWired G bdry (0 : Fin 2)
                      (1 - Real.exp (-2 * beta)) sigma omega := by
                apply Finset.sum_congr rfl
                intro omega _
                rw [Finset.mul_sum]
            _ = ∑ sigma : V → Fin 2,
                ∑ omega : ConfigSpace (Sym2 V),
                  (if omega s(x, y) then 1 else 0) *
                    esWeightWired G bdry (0 : Fin 2)
                      (1 - Real.exp (-2 * beta)) sigma omega :=
              Finset.sum_comm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro sigma _
              calc
                (∑ omega : ConfigSpace (Sym2 V),
                    (if omega s(x, y) then 1 else 0) *
                      esWeightWired G bdry (0 : Fin 2)
                        (1 - Real.exp (-2 * beta)) sigma omega) =
                  ∑ omega : ConfigSpace (Sym2 V),
                    esWeightWired G bdry (0 : Fin 2)
                        (1 - Real.exp (-2 * beta)) sigma omega *
                      (if omega s(x, y) then 1 else 0) := by
                    apply Finset.sum_congr rfl
                    intro omega _
                    ring
                _ = _ :=
                  esWeightWired_open_sum_eq G bdry beta sigma x y hedge
    _ = (1 - Real.exp (-2 * beta)) *
        ∑ sigma : V → Fin 2,
          ((∑ omega : ConfigSpace (Sym2 V),
              esWeightWired G bdry (0 : Fin 2)
                (1 - Real.exp (-2 * beta)) sigma omega) /
              esZWired G bdry 2 (0 : Fin 2) (1 - Real.exp (-2 * beta))) *
            Potts.monoIndicator sigma s(x, y) := by
          rw [Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro sigma _
          ring



theorem hbx_isingWiredPair_eq_plusIntegral
    (d n : Nat) (beta : Real) (x y : boxVerts d n) (hxy : x ≠ y) :
    ((∑ sigma : boxVerts d (n + 1) → Fin 2,
        isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) beta sigma *
          esSpinProduct ({boxSiteSucc x, boxSiteSucc y} :
            Finset (boxVerts d (n + 1))) sigma) /
      isingWiredZ (boxGraph d (n + 1)) (boxBoundary d (n + 1)) beta) =
      ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  let C : Real :=
    ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset \
      bondFinsetTouch d n).card : Real)
  let E : Real := Real.exp (beta * C)
  have hE0 : E ≠ 0 := (Real.exp_pos _).ne'
  have hspin (tau : ConfigSpace (boxVerts d n)) :
      esSpinProduct ({boxSiteSucc x, boxSiteSucc y} :
          Finset (boxVerts d (n + 1))) (latToBox d n tau) =
        spinProd ({x.1, y.1} : Finset (Site d))
          (glue (plusField d) tau) := by
    rw [esSpinProduct, Finset.prod_pair (boxSiteSucc_ne hxy),
      spinProd, Finset.prod_pair (fun h => hxy (Subtype.ext h)),
      isingSpin_latToBox, isingSpin_latToBox]
    rfl
  have hnum :
      (∑ sigma : boxVerts d (n + 1) → Fin 2,
          isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) beta sigma *
            esSpinProduct ({boxSiteSucc x, boxSiteSucc y} :
              Finset (boxVerts d (n + 1))) sigma) =
        E * ∑ tau : ConfigSpace (boxVerts d n),
          fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau *
            spinProd ({x.1, y.1} : Finset (Site d))
              (glue (plusField d) tau) := by
    rw [hbx_sum_reindex]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tau _
      rw [hbx_isingWiredWeight_latToBox, hspin]
      change Real.exp (beta * C) * _ * _ = E * (_ * _)
      rw [show E = Real.exp (beta * C) by rfl]
      ring
    · intro sigma hnot
      simp [isingWiredWeight, hnot]
  have hden :
      isingWiredZ (boxGraph d (n + 1)) (boxBoundary d (n + 1)) beta =
        E * fvZ (plusField d) n (bondFinsetTouch d n) beta 0 := by
    unfold isingWiredZ fvZ
    rw [hbx_sum_reindex]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tau _
      exact hbx_isingWiredWeight_latToBox d n beta tau
    · intro sigma hnot
      simp [isingWiredWeight, hnot]
  rw [hnum, hden, mul_div_mul_left _ _ hE0]
  change _ = ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
    ∂fvMeasure (plusField d) n (bondFinsetTouch d n) beta 0
  rw [integral_fvMeasure_eq_sum]
  unfold fvProb
  rw [Finset.sum_div]
  congr 1
  funext tau
  ring



theorem esWiredMonoExpectation_box_eq_half_one_add_plusIntegral
    (d n : Nat) (beta : Real) (x y : boxVerts d n) (hxy : x ≠ y) :
    (∑ sigma : boxVerts d (n + 1) → Fin 2,
        esWiredFirstMarginal (boxGraph d (n + 1)) (boxBoundary d (n + 1))
            2 (0 : Fin 2) (1 - Real.exp (-2 * beta)) sigma *
          Potts.monoIndicator sigma s(boxSiteSucc x, boxSiteSucc y)) =
      (1 + ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) / 2 := by
  let G' := boxGraph d (n + 1)
  let bdry := boxBoundary d (n + 1)
  let A : Finset (boxVerts d (n + 1)) := {boxSiteSucc x, boxSiteSucc y}
  have hfirst :
      (∑ sigma : boxVerts d (n + 1) → Fin 2,
        esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
          (1 - Real.exp (-2 * beta)) sigma) = 1 := by
    have hpmap : 1 - Real.exp (-2 * beta) =
        1 - Real.exp (-((2 * beta) * 1)) := by ring_nf
    rw [hpmap, Finset.sum_congr rfl (fun sigma _ =>
      esWiredFirstMarginal_eq_pottsProbWired G' bdry (0 : Fin 2)
        (2 * beta) 1 sigma)]
    simpa only [mul_one] using
      pottsProbWired_sum_eq_one G' bdry 2 (0 : Fin 2) (2 * beta) 1
  have hspin :
      (∑ sigma : boxVerts d (n + 1) → Fin 2,
        esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
            (1 - Real.exp (-2 * beta)) sigma * esSpinProduct A sigma) =
        ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
          ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
    have hpoint (sigma : boxVerts d (n + 1) → Fin 2) :
        esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
              (1 - Real.exp (-2 * beta)) sigma =
          isingWiredWeight G' bdry beta sigma / isingWiredZ G' bdry beta := by
      have hpmap : 1 - Real.exp (-2 * beta) =
          1 - Real.exp (-((2 * beta) * 1)) := by ring_nf
      rw [hpmap, esWiredFirstMarginal_eq_pottsProbWired G' bdry
        (0 : Fin 2) (2 * beta) 1 sigma]
      unfold pottsProbWired pottsZWired
      rw [pottsWeightWired_eq_isingWiredWeight]
      have hden :
          (∑ tau : boxVerts d (n + 1) → Fin 2,
            pottsWeightWired G' bdry (0 : Fin 2) (2 * beta) 1 tau) =
            Real.exp (beta * G'.edgeFinset.card) * isingWiredZ G' bdry beta := by
        unfold isingWiredZ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro tau _
        exact pottsWeightWired_eq_isingWiredWeight G' bdry beta tau
      rw [hden, mul_div_mul_left _ _ (Real.exp_pos _).ne']
    rw [Finset.sum_congr rfl (fun sigma _ => by rw [hpoint sigma])]
    calc
      (∑ sigma : boxVerts d (n + 1) → Fin 2,
          isingWiredWeight G' bdry beta sigma /
              isingWiredZ G' bdry beta * esSpinProduct A sigma) =
          (∑ sigma : boxVerts d (n + 1) → Fin 2,
            isingWiredWeight G' bdry beta sigma * esSpinProduct A sigma) /
              isingWiredZ G' bdry beta := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro sigma _
            ring
      _ = _ := hbx_isingWiredPair_eq_plusIntegral d n beta x y hxy
  calc
    (∑ sigma : boxVerts d (n + 1) → Fin 2,
        esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
            (1 - Real.exp (-2 * beta)) sigma *
          Potts.monoIndicator sigma s(boxSiteSucc x, boxSiteSucc y)) =
      ∑ sigma : boxVerts d (n + 1) → Fin 2,
        (esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
              (1 - Real.exp (-2 * beta)) sigma +
          esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
              (1 - Real.exp (-2 * beta)) sigma * esSpinProduct A sigma) / 2 := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [monoIndicator_pair_eq_half_one_add_esSpinProduct sigma
          (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)]
        simp only [A]
        ring
    _ = ((∑ sigma : boxVerts d (n + 1) → Fin 2,
          esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
            (1 - Real.exp (-2 * beta)) sigma) +
        (∑ sigma : boxVerts d (n + 1) → Fin 2,
          esWiredFirstMarginal G' bdry 2 (0 : Fin 2)
              (1 - Real.exp (-2 * beta)) sigma * esSpinProduct A sigma)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = _ := by rw [hfirst, hspin]



variable {d : Nat}



theorem freeEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityFreeTwoPoint
    (N : Nat) (beta : Real) (hbeta : 0 < beta)
    (x y : boxVerts d N) (hxy : (boxGraph d N).Adj x y) :
    freeEdgeDensity d 2 (edgeIncl d N s(x, y))
        (1 - Real.exp (-2 * beta)) =
      (1 - Real.exp (-2 * beta)) / 2 *
        (1 + currentContinuityFreeTwoPoint d beta x.1 y.1) := by
  let p : Real := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  have hne : x ≠ y := hxy.ne
  have hdens := dfi_free_density_eq_limit N s(x, y) hp hp1
  have hspin := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta.le ({x.1, y.1} : Finset (Site d))
  have hshift : Tendsto (fun k : Nat => N + k) atTop atTop := dfi_tendsto_add_left N
  have hspin' := hspin.comp hshift
  have heq : ∀ k : Nat,
      edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) s(x, y)) =
        p / 2 * (1 + ∫ omega,
          spinProd ({x.1, y.1} : Finset (Site d)) omega
            ∂(freeMeasure d (N + k) beta 0 :
              Measure (ConfigSpace (Site d)))) := by
    intro k
    let xi := boxVertInclLE d (Nat.le_add_right N k) x
    let yi := boxVertInclLE d (Nat.le_add_right N k) y
    have hxyi : (boxGraph d (N + k)).Adj xi yi := by
      simpa [boxGraph, xi, yi, boxVertInclLE] using hxy
    rw [fpe2_innerEdgeLE_mk]
    rw [edgeMargProb_fkProb_eq_p_div_two_mul_one_add_isingExpectation
      (boxGraph d (N + k)) beta xi yi hxyi.ne
      (by simpa using hxyi)]
    rw [show Ising.isingExpectation (boxGraph d (N + k)) beta 0
        (spinProd ({xi, yi} : Finset (boxVerts d (N + k)))) =
      ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
        ∂(freeMeasure d (N + k) beta 0 :
          Measure (ConfigSpace (Site d))) by
      change Ising.isingExpectation (Sharpness.sctBoxGraph d (N + k)) beta 0
          (spinProd ({xi, yi} : Finset (boxVerts d (N + k)))) = _
      have hsub : (↑({x.1, y.1} : Finset (Site d)) : Set (Site d)) ⊆
          box d (N + k) := by
        intro z hz
        have hz' : z ∈ ({x.1, y.1} : Finset (Site d)) := hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
        rcases hz' with rfl | rfl
        · exact box_mono d (Nat.le_add_right N k) x.2
        · exact box_mono d (Nat.le_add_right N k) y.2
      rw [integral_freeMeasure_spinProd
        d (N + k) beta 0 ({x.1, y.1} : Finset (Site d)) hsub]
      congr 2
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton, boxSpinSupport,
        Finset.mem_filter, Finset.mem_univ, true_and, xi, yi, boxVertInclLE]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)]
  have hright : Tendsto (fun k : Nat =>
      p / 2 * (1 + ∫ omega,
        spinProd ({x.1, y.1} : Finset (Site d)) omega
          ∂(freeMeasure d (N + k) beta 0 :
            Measure (ConfigSpace (Site d))))) atTop
      (nhds (p / 2 * (1 + currentContinuityFreeTwoPoint d beta x.1 y.1))) := by
    simpa only [currentContinuityFreeTwoPoint] using
      ((tendsto_const_nhds.add hspin').const_mul (p / 2))
  have hleft := hdens.congr (fun k => heq k)
  simpa only [p] using tendsto_nhds_unique hleft hright



theorem wiredEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityPlusTwoPoint
    (N : Nat) (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (x y : boxVerts d N) (hxy : (boxGraph d N).Adj x y) :
    wiredEdgeDensity d 2 (edgeIncl d N s(x, y))
        (1 - Real.exp (-2 * beta)) =
      (1 - Real.exp (-2 * beta)) / 2 *
        (1 + currentContinuityPlusTwoPoint d beta x.1 y.1) := by
  let p : Real := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  have hne : x ≠ y := hxy.ne
  have hdens0 := dfi_wired_density_eq_limit N s(x, y) hp hp1
  have hdens := hdens0.comp (tendsto_add_atTop_nat 1)
  have hdens' : Tendsto (fun k =>
      edgeMargProb
        (wiredFkProb (boxGraph d ((N + k) + 1))
          (boxBoundary d ((N + k) + 1)) p 2)
        (innerEdgeLE d (by omega : N ≤ (N + k) + 1) s(x, y))) atTop
      (nhds (wiredEdgeDensity d 2 (edgeIncl d N s(x, y)) p)) := by
    simpa only [Function.comp_apply, Nat.add_assoc] using hdens
  have hspin := integral_plusMeasure_spinProd_full_tendsto
    d beta hbeta.le ({x.1, y.1} : Finset (Site d))
  have hshift : Tendsto (fun k : Nat => N + k) atTop atTop := dfi_tendsto_add_left N
  have hspin' := hspin.comp hshift
  have heq : ∀ k : Nat,
      edgeMargProb
          (wiredFkProb (boxGraph d ((N + k) + 1))
            (boxBoundary d ((N + k) + 1)) p 2)
          (innerEdgeLE d (by omega : N ≤ (N + k) + 1) s(x, y)) =
        p / 2 * (1 + ∫ omega,
          spinProd ({x.1, y.1} : Finset (Site d)) omega
            ∂(plusMeasure d (N + k) beta 0 :
              Measure (ConfigSpace (Site d)))) := by
    intro k
    let xk : boxVerts d (N + k) :=
      boxVertInclLE d (Nat.le_add_right N k) x
    let yk : boxVerts d (N + k) :=
      boxVertInclLE d (Nat.le_add_right N k) y
    have hxyk : (boxGraph d (N + k)).Adj xk yk := by
      simpa [boxGraph, xk, yk, boxVertInclLE] using hxy
    have hedgesucc :
        s(boxSiteSucc xk, boxSiteSucc yk) ∈
          (boxGraph d ((N + k) + 1)).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      simpa [boxGraph, boxSiteSucc, xk, yk, boxVertInclLE] using hxy
    obtain ⟨v0, hv0⟩ := boxBoundary_nonempty d ((N + k) + 1) hd (by omega)
    have hinner :
        innerEdgeLE d (by omega : N ≤ (N + k) + 1) s(x, y) =
          s(boxSiteSucc xk, boxSiteSucc yk) := by
      rw [fpe2_innerEdgeLE_mk]
      rfl
    rw [hinner]
    rw [edgeMargProb_wiredFkProb_eq_p_mul_esWiredMono
      (boxGraph d ((N + k) + 1)) (boxBoundary d ((N + k) + 1))
      v0 hv0 beta
      (boxSiteSucc xk) (boxSiteSucc yk) hedgesucc,
      esWiredMonoExpectation_box_eq_half_one_add_plusIntegral
        d (N + k) beta xk yk hxyk.ne]
    simp only [xk, yk, boxVertInclLE]
    ring
  have hright : Tendsto (fun k : Nat =>
      p / 2 * (1 + ∫ omega,
        spinProd ({x.1, y.1} : Finset (Site d)) omega
          ∂(plusMeasure d (N + k) beta 0 :
            Measure (ConfigSpace (Site d))))) atTop
      (nhds (p / 2 * (1 + currentContinuityPlusTwoPoint d beta x.1 y.1))) := by
    simpa only [currentContinuityPlusTwoPoint] using
      ((tendsto_const_nhds.add hspin').const_mul (p / 2))
  have hleft := hdens'.congr (fun k => heq k)
  simpa only [p] using tendsto_nhds_unique hleft hright







theorem currentContinuity_allEdgeDensity_eq_of_adjacent_eq
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hadj : ∀ x y : Site d, (hypercubicLattice d).Adj x y →
      currentContinuityPlusTwoPoint d beta x y =
        currentContinuityFreeTwoPoint d beta x y) :
    ∀ (N : Nat) (e : Sym2 (boxVerts d N)),
      freeEdgeDensity d 2 (edgeIncl d N e)
          (1 - Real.exp (-2 * beta)) =
        wiredEdgeDensity d 2 (edgeIncl d N e)
          (1 - Real.exp (-2 * beta)) := by
  intro N e
  let p : Real := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  by_cases hedge : e ∈ (boxGraph d N).edgeFinset
  · induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : (boxGraph d N).Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
        have hlat : (hypercubicLattice d).Adj x.1 y.1 := by
          simpa only [boxGraph, SimpleGraph.comap_adj] using hxy
        rw [freeEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityFreeTwoPoint
            N beta hbeta x y hxy,
          wiredEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityPlusTwoPoint
            N beta hbeta hd x y hxy,
          hadj x.1 y.1 hlat]
  · rw [fpe2_free_density_nonEdge N e hedge hp hp1,
      fpe2_wired_density_nonEdge N e hedge hp hp1]



theorem currentContinuity_freeInfiniteVolume_eq_wiredInfiniteVolume_of_noPercolation
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hnoperco : (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
      (Percolation.percolationEvent d) = 0) :
    (freeInfiniteVolume d
        (p := 1 - Real.exp (-2 * beta)) (q := 2)
        (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
        (by linarith [Real.exp_pos (-2 * beta)])
        (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d)))) =
    (wiredInfiniteVolume d
        (p := 1 - Real.exp (-2 * beta)) (q := 2)
        (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
        (by linarith [Real.exp_pos (-2 * beta)])
        (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d)))) := by
  apply freeInfiniteVolume_eq_wiredInfiniteVolume_of_edgeDensity_eq
  intro N e
  exact currentContinuity_allEdgeDensity_eq_of_adjacent_eq beta hbeta hd
    (fun x y hxy => currentContinuity_adjacent_eq_of_no_percolation
      d beta hbeta hnoperco x y hxy) N e





theorem currentContinuity_FK_phase_eq_of_freeLROZero
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
          (Percolation.percolationEvent d) = 0 ∧
      (freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      (wiredInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  have hnoperco := currentContinuity_no_percolation_of_freeLROZero
    (d := d) beta hbeta
      (currentContinuityMixedTraceLaw_uniqueInfiniteCluster d hd beta hbeta)
      (currentContinuityMixedTraceLaw_percolationPrinciple d hd beta hbeta)
      hLRO
  exact ⟨hnoperco,
    currentContinuity_freeInfiniteVolume_eq_wiredInfiniteVolume_of_noPercolation
      beta hbeta hd hnoperco⟩

end StatMech.FrontierB
