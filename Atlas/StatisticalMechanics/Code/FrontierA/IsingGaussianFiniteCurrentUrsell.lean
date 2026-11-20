/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamWeightedFourCurrent
import Code.FrontierA.GrahamWeightedSurvivorSwitching
import Code.FrontierA.GrahamCorrections
import Code.Ising.CorrelationRatio










open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteCurrentFourthUrsell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  let Z := currentSum G beta J ∅
  (currentSum G beta J {i, j, k, l} * Z -
    currentSum G beta J {i, j} * currentSum G beta J {k, l} -
    currentSum G beta J {i, k} * currentSum G beta J {j, l} -
    currentSum G beta J {i, l} * currentSum G beta J {j, k}) / Z ^ 2


noncomputable def finiteIsingFourthUrsell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  expectationJ G beta J {i, j, k, l} -
    expectationJ G beta J {i, j} * expectationJ G beta J {k, l} -
    expectationJ G beta J {i, k} * expectationJ G beta J {j, l} -
    expectationJ G beta J {i, l} * expectationJ G beta J {j, k}


theorem finiteIsingFourthUrsell_eq_current
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    finiteIsingFourthUrsell G beta J i j k l =
      finiteCurrentFourthUrsell G beta J i j k l := by
  unfold finiteIsingFourthUrsell finiteCurrentFourthUrsell
  dsimp only
  simp_rw [current_representation]
  have hZ : currentSum G beta J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G beta J)
  field_simp [hZ]



noncomputable def finiteCurrentTreeDiagram
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑ y : V,
    expectationJ G beta J (grahamPairSupport i y) *
      expectationJ G beta J (grahamPairSupport j y) *
      expectationJ G beta J (grahamPairSupport k y) *
      expectationJ G beta J (grahamPairSupport l y)


noncomputable def finiteCurrentTreeDiagramMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑ y : V,
    currentSum G beta J (grahamPairSupport i y) *
      currentSum G beta J (grahamPairSupport j y) *
      currentSum G beta J (grahamPairSupport k y) *
      currentSum G beta J (grahamPairSupport l y)



theorem finiteCurrentFourthUrsell_eq_allThree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finiteCurrentFourthUrsell G beta J i j k l =
      -2 * gatedSourcePairSum G beta J {i, j, k, l} ∅
        (fun m => grahamAllThreeConnected G m i j k l) /
          currentSum G beta J ∅ ^ 2 := by
  unfold finiteCurrentFourthUrsell
  dsimp only
  rw [grahamCurrentSum_ursell4_eq_allThree G beta J
    hij hik hil hjk hjl hkl]



theorem finiteCurrentFourthUrsell_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finiteCurrentFourthUrsell G beta J i j k l <= 0 := by
  rw [finiteCurrentFourthUrsell_eq_allThree G beta J
    hij hik hil hjk hjl hkl]
  have hM := gatedSourcePairSum_nonneg G beta J hbeta hJ
    {i, j, k, l} ∅ (fun m => grahamAllThreeConnected G m i j k l)
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hM) (sq_nonneg _)


theorem finiteCurrentTreeDiagram_eq_mass_div
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) :
    finiteCurrentTreeDiagram G beta J i j k l =
      finiteCurrentTreeDiagramMass G beta J i j k l /
        currentSum G beta J ∅ ^ 4 := by
  unfold finiteCurrentTreeDiagram finiteCurrentTreeDiagramMass
  simp_rw [current_representation]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  ring



theorem finiteCurrent_treeDiagram_bound_iff_mass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    -finiteCurrentFourthUrsell G beta J i j k l <=
        2 * finiteCurrentTreeDiagram G beta J i j k l ↔
      gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun m => grahamAllThreeConnected G m i j k l) *
            currentSum G beta J ∅ ^ 2 <=
        finiteCurrentTreeDiagramMass G beta J i j k l := by
  rw [finiteCurrentFourthUrsell_eq_allThree G beta J
    hij hik hil hjk hjl hkl,
    finiteCurrentTreeDiagram_eq_mass_div]
  have hZ : currentSum G beta J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G beta J)
  have hZ2 : 0 < currentSum G beta J ∅ ^ 2 := sq_pos_of_ne_zero hZ
  have hZ4 : 0 < currentSum G beta J ∅ ^ 4 := by positivity
  constructor <;> intro h
  · have h' :
        2 * gatedSourcePairSum G beta J {i, j, k, l} ∅
              (fun m => grahamAllThreeConnected G m i j k l) /
              currentSum G beta J ∅ ^ 2 <=
          2 * finiteCurrentTreeDiagramMass G beta J i j k l /
              currentSum G beta J ∅ ^ 4 := by
      convert h using 1 <;> ring
    have hcross := (div_le_div_iff₀ hZ2 hZ4).mp h'
    nlinarith [sq_nonneg (currentSum G beta J ∅ ^ 2)]
  · have hcross :
        (2 * gatedSourcePairSum G beta J {i, j, k, l} ∅
            (fun m => grahamAllThreeConnected G m i j k l)) *
              currentSum G beta J ∅ ^ 4 <=
          (2 * finiteCurrentTreeDiagramMass G beta J i j k l) *
              currentSum G beta J ∅ ^ 2 := by
      nlinarith [sq_nonneg (currentSum G beta J ∅ ^ 2)]
    have h' := (div_le_div_iff₀ hZ2 hZ4).mpr hcross
    convert h' using 1 <;> ring



theorem finiteIsing_treeDiagram_bound_of_mass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hmass :
      gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun m => grahamAllThreeConnected G m i j k l) *
            currentSum G beta J ∅ ^ 2 <=
        finiteCurrentTreeDiagramMass G beta J i j k l) :
    0 <= -finiteIsingFourthUrsell G beta J i j k l ∧
      -finiteIsingFourthUrsell G beta J i j k l <=
        2 * finiteCurrentTreeDiagram G beta J i j k l := by
  rw [finiteIsingFourthUrsell_eq_current]
  exact ⟨neg_nonneg.mpr
      (finiteCurrentFourthUrsell_nonpos G beta J hbeta hJ
        hij hik hil hjk hjl hkl),
    (finiteCurrent_treeDiagram_bound_iff_mass G beta J
      hij hik hil hjk hjl hkl).2 hmass⟩



theorem gatedPairConnection_eq_twoPointMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (x₁ x₂ y : V) :
    gatedSourcePairSum G beta J (grahamPairSupport x₁ x₂) ∅
        (fun m => CurrentConnected G m x₁ y) =
      currentSum G beta J (grahamPairSupport x₁ y) *
        currentSum G beta J (grahamPairSupport y x₂) := by
  by_cases hy : y = x₁
  · subst y
    rw [show grahamPairSupport x₁ x₁ = ∅ by simp [grahamPairSupport]]
    calc
      gatedSourcePairSum G beta J (grahamPairSupport x₁ x₂) ∅
          (fun m => CurrentConnected G m x₁ x₁) =
          gatedSourcePairSum G beta J (grahamPairSupport x₁ x₂) ∅
            (fun _ => True) := by
              unfold gatedSourcePairSum
              apply tsum_congr
              rintro ⟨p, q⟩
              simp [CurrentConnected.refl]
      _ = sourcePairSum G beta J (grahamPairSupport x₁ x₂) ∅ :=
        gatedSourcePairSum_true G beta J _ _
      _ = currentSum G beta J (grahamPairSupport x₁ x₂) *
          currentSum G beta J ∅ := sourcePairSum_eq_mul G beta J _ _
      _ = currentSum G beta J ∅ *
          currentSum G beta J (grahamPairSupport x₁ x₂) := by ring
  · have hpair : ({x₁, y} : Finset V) = grahamPairSupport x₁ y := by
      ext z
      simp only [grahamPairSupport, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_symmDiff]
      by_cases hx : z = x₁ <;> by_cases hzy : z = y <;> simp_all [eq_comm]
    have hcomm12 : grahamPairSupport x₁ x₂ = grahamPairSupport x₂ x₁ := by
      unfold grahamPairSupport
      rw [symmDiff_comm]
    have hcomm2y : grahamPairSupport x₂ y = grahamPairSupport y x₂ := by
      unfold grahamPairSupport
      rw [symmDiff_comm]
    have hsource : symmDiff (grahamPairSupport x₁ x₂)
        ({x₁, y} : Finset V) = grahamPairSupport y x₂ := by
      rw [hpair, hcomm12, grahamPairSupport_chain, hcomm2y]
    have hswitch := gatedSourcePairSum_switching G beta J
      (grahamPairSupport x₁ x₂) (Ne.symm hy) (fun _ => True)
    rw [hsource, hpair] at hswitch
    calc
      gatedSourcePairSum G beta J (grahamPairSupport x₁ x₂) ∅
          (fun m => CurrentConnected G m x₁ y) =
          gatedSourcePairSum G beta J (grahamPairSupport y x₂)
            (grahamPairSupport x₁ y) (fun _ => True) := by
              simpa only [true_and] using hswitch.symm
      _ = sourcePairSum G beta J (grahamPairSupport y x₂)
          (grahamPairSupport x₁ y) :=
        gatedSourcePairSum_true G beta J _ _
      _ = _ := by rw [sourcePairSum_eq_mul]; ring

end StatMech.FrontierA
