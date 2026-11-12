/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingLatticeGreenSpatialDecay









open Filter Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Lattice

private theorem intDifferenceBlock_abs_sum_le
    (f : Int -> Real) (N a : Nat) (ha : a < N) :
    (∑ b ∈ Finset.range N, |f ((b : Int) - (a : Int))|) <=
      (∑ t ∈ Finset.range N, |f (t : Int)|) +
        ∑ t ∈ Finset.range N, |f (-(t : Int))| := by
  classical
  let upper := (Finset.range N).filter fun b => a <= b
  let lower := (Finset.range N).filter fun b => b < a
  have hsplit : upper ∪ lower = Finset.range N := by
    ext b
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter,
      Finset.mem_range]
    omega
  have hdisjoint : Disjoint upper lower := by
    rw [Finset.disjoint_left]
    intro b hbUpper hbLower
    simp only [upper, Finset.mem_filter] at hbUpper
    simp only [lower, Finset.mem_filter] at hbLower
    omega
  have hupperInj : Set.InjOn (fun b : Nat => b - a) (upper : Set Nat) := by
    intro b hb c hc hbc
    simp only [upper, Finset.mem_coe, Finset.mem_filter] at hb hc
    calc
      b = b - a + a := (Nat.sub_add_cancel hb.2).symm
      _ = c - a + a := congrArg (fun z => z + a) hbc
      _ = c := Nat.sub_add_cancel hc.2
  have hlowerInj : Set.InjOn (fun b : Nat => a - b) (lower : Set Nat) := by
    intro b hb c hc hbc
    simp only [lower, Finset.mem_coe, Finset.mem_filter] at hb hc
    calc
      b = a - (a - b) := (Nat.sub_sub_self hb.2.le).symm
      _ = a - (a - c) := congrArg (fun z => a - z) hbc
      _ = c := Nat.sub_sub_self hc.2.le
  have hupperSubset : upper.image (fun b => b - a) <= Finset.range N := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    simp only [upper, Finset.mem_filter, Finset.mem_range] at hb
    rw [Finset.mem_range]
    omega
  have hlowerSubset : lower.image (fun b => a - b) <= Finset.range N := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    simp only [lower, Finset.mem_filter, Finset.mem_range] at hb
    rw [Finset.mem_range]
    omega
  have hupper :
      (∑ b ∈ upper, |f ((b : Int) - (a : Int))|) <=
        ∑ t ∈ Finset.range N, |f (t : Int)| := by
    calc
      (∑ b ∈ upper, |f ((b : Int) - (a : Int))|) =
          ∑ t ∈ upper.image (fun b => b - a), |f (t : Int)| := by
        rw [Finset.sum_image hupperInj]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [upper, Finset.mem_filter] at hb
        congr 2
        omega
      _ <= ∑ t ∈ Finset.range N, |f (t : Int)| :=
        Finset.sum_le_sum_of_subset_of_nonneg hupperSubset
          (fun _ _ _ => abs_nonneg _)
  have hlower :
      (∑ b ∈ lower, |f ((b : Int) - (a : Int))|) <=
        ∑ t ∈ Finset.range N, |f (-(t : Int))| := by
    calc
      (∑ b ∈ lower, |f ((b : Int) - (a : Int))|) =
          ∑ t ∈ lower.image (fun b => a - b), |f (-(t : Int))| := by
        rw [Finset.sum_image hlowerInj]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [lower, Finset.mem_filter] at hb
        congr 2
        omega
      _ <= ∑ t ∈ Finset.range N, |f (-(t : Int))| :=
        Finset.sum_le_sum_of_subset_of_nonneg hlowerSubset
          (fun _ _ _ => abs_nonneg _)
  have hdecomp :
      (∑ b ∈ Finset.range N, |f ((b : Int) - (a : Int))|) =
        (∑ b ∈ upper, |f ((b : Int) - (a : Int))|) +
          ∑ b ∈ lower, |f ((b : Int) - (a : Int))| := by
    rw [← hsplit, Finset.sum_union hdisjoint]
  rw [hdecomp]
  exact add_le_add hupper hlower

private theorem intDifferenceBlock_abs_le_cesaro
    (f : Int -> Real) (N : Nat) (hN : 1 <= N) :
    |(1 / (N : Real) ^ 2) *
        ∑ a ∈ Finset.range N,
          ∑ b ∈ Finset.range N, f ((b : Int) - (a : Int))| <=
      (N : Real)⁻¹ * (∑ t ∈ Finset.range N, |f (t : Int)|) +
        (N : Real)⁻¹ * ∑ t ∈ Finset.range N, |f (-(t : Int))| := by
  let S : Real :=
    (∑ t ∈ Finset.range N, |f (t : Int)|) +
      ∑ t ∈ Finset.range N, |f (-(t : Int))|
  have hS : 0 <= S := add_nonneg
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hinner (a : Nat) (ha : a ∈ Finset.range N) :
      |∑ b ∈ Finset.range N, f ((b : Int) - (a : Int))| <= S := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (intDifferenceBlock_abs_sum_le f N a (Finset.mem_range.mp ha))
  have hdouble :
      |∑ a ∈ Finset.range N,
          ∑ b ∈ Finset.range N, f ((b : Int) - (a : Int))| <=
        (N : Real) * S := by
    calc
      |∑ a ∈ Finset.range N,
          ∑ b ∈ Finset.range N, f ((b : Int) - (a : Int))| <=
          ∑ a ∈ Finset.range N,
            |∑ b ∈ Finset.range N, f ((b : Int) - (a : Int))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _a ∈ Finset.range N, S := Finset.sum_le_sum hinner
      _ = (N : Real) * S := by simp
  have hcoef : 0 <= 1 / (N : Real) ^ 2 := by positivity
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    (1 / (N : Real) ^ 2) *
        |∑ a ∈ Finset.range N,
          ∑ b ∈ Finset.range N, f ((b : Int) - (a : Int))| <=
        (1 / (N : Real) ^ 2) * ((N : Real) * S) :=
      mul_le_mul_of_nonneg_left hdouble hcoef
    _ = (N : Real)⁻¹ * (∑ t ∈ Finset.range N, |f (t : Int)|) +
        (N : Real)⁻¹ * ∑ t ∈ Finset.range N, |f (-(t : Int))| := by
      have hNR : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      dsimp [S]
      field_simp

private theorem isingLatticeGreen_axis_abs_tendsto_zero
    {d : Nat} (hd : 2 < d) (i : Fin d) :
    Tendsto (fun n : Nat =>
      |isingLatticeGreen d (Pi.single i (n : Int))|) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨R, hR⟩ :=
    isingLatticeGreen_eventually_small_outside_box hd epsilon hepsilon
  refine ⟨R + 1, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)]
  apply hR
  intro hx
  have hi := hx i
  simp [Pi.single] at hi
  omega

private theorem isingLatticeGreen_axis_neg_abs_tendsto_zero
    {d : Nat} (hd : 2 < d) (i : Fin d) :
    Tendsto (fun n : Nat =>
      |isingLatticeGreen d (Pi.single i (-(n : Int)))|) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨R, hR⟩ :=
    isingLatticeGreen_eventually_small_outside_box hd epsilon hepsilon
  refine ⟨R + 1, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)]
  apply hR
  intro hx
  have hi := hx i
  simp [Pi.single] at hi
  omega



theorem isingLatticeGreenAxisBlockAverage_tendsto_zero
    {d : Nat} (hd : 2 < d) (i : Fin d) :
    Tendsto (isingLatticeGreenAxisBlockAverage i) atTop (nhds 0) := by
  let f : Int -> Real := fun z => isingLatticeGreen d (Pi.single i z)
  have hpos : Tendsto (fun n : Nat => |f (n : Int)|) atTop (nhds 0) :=
    isingLatticeGreen_axis_abs_tendsto_zero hd i
  have hneg : Tendsto (fun n : Nat => |f (-(n : Int))|) atTop (nhds 0) :=
    isingLatticeGreen_axis_neg_abs_tendsto_zero hd i
  have hmajorant : Tendsto
      (fun N : Nat =>
        (N : Real)⁻¹ * (∑ t ∈ Finset.range N, |f (t : Int)|) +
          (N : Real)⁻¹ * ∑ t ∈ Finset.range N, |f (-(t : Int))|)
      atTop (nhds 0) := by
    simpa using hpos.cesaro.add hneg.cesaro
  have hmajorantSucc : Tendsto
      (fun r : Nat =>
        ((r + 1 : Nat) : Real)⁻¹ *
            (∑ t ∈ Finset.range (r + 1), |f (t : Int)|) +
          ((r + 1 : Nat) : Real)⁻¹ *
            ∑ t ∈ Finset.range (r + 1), |f (-(t : Int))|)
      atTop (nhds 0) := by
    exact (Filter.tendsto_add_atTop_iff_nat 1).2 hmajorant
  have habs : Tendsto
      (fun r => |isingLatticeGreenAxisBlockAverage i r|)
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun r => ?_) hmajorantSucc
    simpa only [isingLatticeGreenAxisBlockAverage, f, Nat.cast_add,
      Nat.cast_one] using
      intDifferenceBlock_abs_le_cesaro f (r + 1) (by omega)
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  simpa only [Function.comp_apply] using habs

end StatMech.FrontierA
