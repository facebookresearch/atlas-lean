/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.IsingInfraredReduction
import Code.Lattice.BoxSurfaceVolume
import Code.Sharpness.EpsToZeroLattice
import Code.Sharpness.IsingSusceptibilityPlus

open Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

open Lattice Percolation Sharpness





theorem boxBoundary_card_le_surfacePower (d n : ℕ) (hn : 1 ≤ n) :
    ((boxSV_vbF d n).card : ℝ) ≤
      2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) := by
  have hcard : (boxSV_vbF d n).card = boxSV_boundaryCard d n := by
    rw [boxSV_vbF_eq_toFinset]
    rfl
  rw [hcard, boxSV_boundary_card d n hn]
  have hle : (2 * n - 1) ^ d ≤ (2 * n + 1) ^ d :=
    Nat.pow_le_pow_left (by omega) d
  rw [Nat.cast_sub hle]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow := boxSV_pow_sub_pow_le
    (2 * (n : ℝ) + 1) (2 * (n : ℝ) - 1)
    (by linarith) (by linarith) d
  have hminus : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  push_cast
  rw [hminus]
  calc
    (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d ≤
        ((2 * (n : ℝ) + 1) - (2 * (n : ℝ) - 1)) *
          (d * (2 * (n : ℝ) + 1) ^ (d - 1)) := hpow
    _ = 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) := by ring



theorem boxBoundaryEdges_card_le_surfacePower (d n : ℕ) (hn : 1 ≤ n) :
    ((boundaryEdges d (boxSV_boxF d n)).card : ℝ) ≤
      4 * d ^ 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by
  classical
  have hsubset :
      ((boxSV_boxF d n ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ
          (Finset.univ : Finset Bool)).filter
          (fun t => coordShift t.1 t.2.1 (stepSign t.2.2) ∉ boxSV_boxF d n)) ⊆
        boxSV_vbF d n ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ
          (Finset.univ : Finset Bool) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    rw [Finset.mem_product, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _, Finset.mem_univ _⟩
    rw [boxSV_vbF, Finset.mem_sdiff]
    refine ⟨ht.1.1, ?_⟩
    intro hinner
    have hadj : (hypercubicLattice d).Adj t.1
        (coordShift t.1 t.2.1 (stepSign t.2.2)) :=
      adj_coordShift t.1 t.2.1 t.2.2
    have hinnerSet : t.1 ∈ box d (n - 1) := by
      rw [← boxSV_coe_boxF]
      exact hinner
    have hout : coordShift t.1 t.2.1 (stepSign t.2.2) ∈ box d n :=
      sct_adj_mem_box_of_mem_box_pred hn hinnerSet hadj
    apply ht.2
    change coordShift t.1 t.2.1 (stepSign t.2.2) ∈
      (boxSV_boxF d n : Set (Site d))
    rw [boxSV_coe_boxF]
    exact hout
  have hcardNat :
      (boundaryEdges d (boxSV_boxF d n)).card ≤
        (boxSV_vbF d n).card * (2 * d) := by
    unfold boundaryEdges
    calc
      ((Finset.filter
          (fun t => coordShift t.1 t.2.1 (stepSign t.2.2) ∉ boxSV_boxF d n)
          (boxSV_boxF d n ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ
            (Finset.univ : Finset Bool))).image
          (fun t => (t.1, coordShift t.1 t.2.1 (stepSign t.2.2)))).card ≤
          (Finset.filter
            (fun t => coordShift t.1 t.2.1 (stepSign t.2.2) ∉ boxSV_boxF d n)
            (boxSV_boxF d n ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ
              (Finset.univ : Finset Bool))).card := Finset.card_image_le
      _ ≤ (boxSV_vbF d n ×ˢ (Finset.univ : Finset (Fin d)) ×ˢ
          (Finset.univ : Finset Bool)).card := Finset.card_le_card hsubset
      _ = (boxSV_vbF d n).card * (2 * d) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_univ,
          Finset.card_univ, Fintype.card_fin, Fintype.card_bool]
        ring
  have hcardReal :
      ((boundaryEdges d (boxSV_boxF d n)).card : ℝ) ≤
        (boxSV_vbF d n).card * (2 * d) := by exact_mod_cast hcardNat
  calc
    ((boundaryEdges d (boxSV_boxF d n)).card : ℝ) ≤
        (boxSV_vbF d n).card * (2 * d) := hcardReal
    _ ≤ (2 * d * (2 * (n : ℝ) + 1) ^ (d - 1)) * (2 * d) := by
      gcongr
      exact boxBoundary_card_le_surfacePower d n hn
    _ = 4 * d ^ 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by ring






theorem boundaryMass_forces_pointwise_powerLower
    {X : Type*}
    (boundary : Finset X) (weight corr : X → ℝ) (targetValue : ℝ)
    (surfaceConstant edgeBound comparisonConstant radius : ℝ)
    (exponent : ℕ)
    (hsurface : (boundary.card : ℝ) ≤ surfaceConstant * radius ^ exponent)
    (hedge : 0 < edgeBound) (hcomparison : 0 < comparisonConstant)
    (hsurfaceConstant : 0 < surfaceConstant) (hradius : 0 < radius)
    (htarget : 0 ≤ targetValue)
    (hweightBound : ∀ x ∈ boundary, weight x ≤ edgeBound)
    (hcorrNonneg : ∀ x ∈ boundary, 0 ≤ corr x)
    (hcompare : ∀ x ∈ boundary, corr x ≤ comparisonConstant * targetValue)
    (hmass : 1 ≤ ∑ x ∈ boundary, weight x * corr x) :
    1 / (surfaceConstant * edgeBound * comparisonConstant * radius ^ exponent) ≤
      targetValue := by
  have hsum :
      (∑ x ∈ boundary, weight x * corr x) ≤
        (boundary.card : ℝ) * (edgeBound * (comparisonConstant * targetValue)) := by
    calc
      (∑ x ∈ boundary, weight x * corr x) ≤
          ∑ _x ∈ boundary, edgeBound * (comparisonConstant * targetValue) := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        exact mul_le_mul (hweightBound x hx) (hcompare x hx)
          (hcorrNonneg x hx) hedge.le
      _ = (boundary.card : ℝ) *
          (edgeBound * (comparisonConstant * targetValue)) := by simp
  have hsurfaceTarget :
      (boundary.card : ℝ) * (edgeBound * (comparisonConstant * targetValue)) ≤
        (surfaceConstant * radius ^ exponent) *
          (edgeBound * (comparisonConstant * targetValue)) := by
    exact mul_le_mul_of_nonneg_right hsurface
      (mul_nonneg hedge.le (mul_nonneg hcomparison.le htarget))
  have hdenom :
      0 < surfaceConstant * edgeBound * comparisonConstant * radius ^ exponent := by
    positivity
  apply (div_le_iff₀ hdenom).2
  calc
    1 ≤ ∑ x ∈ boundary, weight x * corr x := hmass
    _ ≤ (boundary.card : ℝ) *
        (edgeBound * (comparisonConstant * targetValue)) := hsum
    _ ≤ (surfaceConstant * radius ^ exponent) *
        (edgeBound * (comparisonConstant * targetValue)) := hsurfaceTarget
    _ = targetValue *
        (surfaceConstant * edgeBound * comparisonConstant * radius ^ exponent) := by ring






theorem isingBoxSimonMass_forces_pointwise_powerLower
    (d n : ℕ) (beta targetValue comparisonConstant : ℝ)
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hbeta : 0 < beta)
    (hcomparison : 0 < comparisonConstant) (htarget : 0 ≤ targetValue)
    (hphi : 1 ≤ phiIsing d beta (boxSV_boxF d n))
    (hshellCompare : ∀ e ∈ boundaryEdges d (boxSV_boxF d n),
      corrOriginInner d beta (boxSV_boxF d n) e.1 ≤
        comparisonConstant * targetValue) :
    1 / (4 * d ^ 2 * Real.tanh beta * comparisonConstant *
      (2 * (n : ℝ) + 1) ^ (d - 1)) ≤ targetValue := by
  have htanh : 0 < Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hbeta) (Real.cosh_pos beta)
  have hsurfaceConstant : (0 : ℝ) < 4 * d ^ 2 := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    positivity
  have hradius : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hmass : 1 ≤
      ∑ e ∈ boundaryEdges d (boxSV_boxF d n),
        Real.tanh beta * corrOriginInner d beta (boxSV_boxF d n) e.1 := by
    simpa only [phiIsing, Finset.mul_sum] using hphi
  exact boundaryMass_forces_pointwise_powerLower
    (boundaryEdges d (boxSV_boxF d n))
    (fun _e => Real.tanh beta)
    (fun e => corrOriginInner d beta (boxSV_boxF d n) e.1)
    targetValue (4 * d ^ 2) (Real.tanh beta) comparisonConstant
    (2 * (n : ℝ) + 1) (d - 1)
    (boxBoundaryEdges_card_le_surfacePower d n hn) htanh hcomparison
    hsurfaceConstant hradius htarget
    (fun _e _he => le_rfl)
    (fun e _he => corrOriginInner_nonneg d hbeta.le (boxSV_boxF d n) e.1)
    hshellCompare hmass



theorem greenComparison_gives_pointwise_powerUpper
    (twoPoint greenValue infraredConstant greenConstant radius : ℝ)
    (exponent : ℕ)
    (hinfrared : 0 ≤ infraredConstant)
    (hcomparison : twoPoint ≤ infraredConstant * greenValue)
    (hgreen : greenValue ≤ greenConstant / radius ^ exponent) :
    twoPoint ≤ infraredConstant * greenConstant / radius ^ exponent := by
  calc
    twoPoint ≤ infraredConstant * greenValue := hcomparison
    _ ≤ infraredConstant * (greenConstant / radius ^ exponent) :=
      mul_le_mul_of_nonneg_left hgreen hinfrared
    _ = infraredConstant * greenConstant / radius ^ exponent := by ring




theorem criticalTwoPoint_powerBounds_of_reductions
    {X : Type*}
    (d : ℕ) (boundary : Finset X) (weight corr : X → ℝ)
    (twoPoint greenValue : ℝ)
    (surfaceConstant edgeBound comparisonConstant radius : ℝ)
    (infraredConstant greenConstant : ℝ)
    (hsurface : (boundary.card : ℝ) ≤
      surfaceConstant * radius ^ (d - 1))
    (hedge : 0 < edgeBound) (hcomparisonConstant : 0 < comparisonConstant)
    (hsurfaceConstant : 0 < surfaceConstant) (hradius : 0 < radius)
    (htwoPoint : 0 ≤ twoPoint)
    (hweightBound : ∀ x ∈ boundary, weight x ≤ edgeBound)
    (hcorrNonneg : ∀ x ∈ boundary, 0 ≤ corr x)
    (hshellCompare : ∀ x ∈ boundary,
      corr x ≤ comparisonConstant * twoPoint)
    (hmass : 1 ≤ ∑ x ∈ boundary, weight x * corr x)
    (hinfraredConstant : 0 ≤ infraredConstant)
    (hgreenComparison : twoPoint ≤ infraredConstant * greenValue)
    (hgreenDecay : greenValue ≤ greenConstant / radius ^ (d - 2)) :
    1 / (surfaceConstant * edgeBound * comparisonConstant * radius ^ (d - 1)) ≤
        twoPoint ∧
      twoPoint ≤ infraredConstant * greenConstant / radius ^ (d - 2) := by
  constructor
  · exact boundaryMass_forces_pointwise_powerLower boundary weight corr twoPoint
      surfaceConstant edgeBound comparisonConstant radius (d - 1) hsurface hedge
      hcomparisonConstant hsurfaceConstant hradius htwoPoint hweightBound
      hcorrNonneg hshellCompare hmass
  · exact greenComparison_gives_pointwise_powerUpper twoPoint greenValue
      infraredConstant greenConstant radius (d - 2) hinfraredConstant
      hgreenComparison hgreenDecay

end StatMech.FrontierA
