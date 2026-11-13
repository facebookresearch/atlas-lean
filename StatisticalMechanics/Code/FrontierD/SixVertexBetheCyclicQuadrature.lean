/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexWeightedQuadrature










namespace StatMech.FrontierD

noncomputable section

def sixVertexCyclicRootPartition {n : Nat}
    (p : Fin (n + 1) → Real) : Nat → Real
  | 0 => p (Fin.last n) - 2 * Real.pi
  | k + 1 => p ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩

@[simp] theorem sixVertexCyclicRootPartition_zero
    {n : Nat} (p : Fin (n + 1) → Real) :
    sixVertexCyclicRootPartition p 0 =
      p (Fin.last n) - 2 * Real.pi := rfl

theorem sixVertexCyclicRootPartition_succ
    {n k : Nat} (p : Fin (n + 1) → Real) (hk : k <= n) :
    sixVertexCyclicRootPartition p (k + 1) =
      p ⟨k, Nat.lt_succ_of_le hk⟩ := by
  change p ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩ = _
  congr 1
  apply Fin.ext
  simp [min_eq_left hk]

@[simp] theorem sixVertexCyclicRootPartition_end
    {n : Nat} (p : Fin (n + 1) → Real) :
    sixVertexCyclicRootPartition p (n + 1) = p (Fin.last n) := by
  rw [sixVertexCyclicRootPartition_succ p le_rfl]
  rfl

theorem sixVertexCyclicRootPartition_ordered
    {n : Nat} {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p) :
    ∀ k < n + 1, sixVertexCyclicRootPartition p k <=
      sixVertexCyclicRootPartition p (k + 1) := by
  intro k hk
  cases k with
  | zero =>
      rw [sixVertexCyclicRootPartition_zero,
        sixVertexCyclicRootPartition_succ p (Nat.zero_le n)]
      have hfirst := (hopen.2.2 (0 : Fin (n + 1))).1
      have hlast := (hopen.2.2 (Fin.last n)).2
      have hfirst' : -Real.pi <
          p ⟨0, Nat.zero_lt_succ n⟩ := by simpa using hfirst
      linarith [Real.pi_pos]
  | succ j =>
      have hj : j < n := by omega
      have hjle : j <= n := hj.le.trans (Nat.le_refl n)
      have hjsucc : j + 1 <= n := hj
      rw [sixVertexCyclicRootPartition_succ p hjle,
        sixVertexCyclicRootPartition_succ p hjsucc]
      exact (hopen.1 (by simp [Fin.lt_iff_val_lt_val])).le

theorem sixVertexCyclicRootPartition_mesh_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
    ∀ k < n + 1,
      sixVertexCyclicRootPartition p (k + 1) -
          sixVertexCyclicRootPartition p k <=
        1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
  intro k hk
  cases k with
  | zero =>
      rw [sixVertexCyclicRootPartition_zero,
        sixVertexCyclicRootPartition_succ p (Nat.zero_le n)]
      exact sixVertexBetheSolution_boundarySpacing_upper_tail
        hc htail hN hhalf hopen hsol
  | succ j =>
      have hj : j < n := by omega
      let jf : Fin n := ⟨j, hj⟩
      have hjle : j <= n := hj.le.trans (Nat.le_refl n)
      have hjsucc : j + 1 <= n := hj
      rw [sixVertexCyclicRootPartition_succ p hjle,
        sixVertexCyclicRootPartition_succ p hjsucc]
      simpa [jf] using sixVertexBetheSolution_adjacentSpacing_upper_tail
        hc htail hN hhalf.ge hopen hsol jf

theorem sixVertexCyclicRootPartition_densityMass
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
    ∀ k < n + 1,
      ∫ x in sixVertexCyclicRootPartition p k..
          sixVertexCyclicRootPartition p (k + 1),
          sixVertexFiniteRootDensity c N (n + 1) p x = 1 / N := by
  intro k hk
  cases k with
  | zero =>
      rw [sixVertexCyclicRootPartition_zero,
        sixVertexCyclicRootPartition_succ p (Nat.zero_le n)]
      have hboundary := intervalIntegral_sixVertexFiniteRootDensity_boundary
        hc hN hsol
      have hmass : ((N : Real) - 2 * (n + 1 : Real) + 1) / N =
          1 / (N : Real) := by
        have hhalfReal : (N : Real) = 2 * (n + 1 : Real) := by
          exact_mod_cast hhalf
        rw [hhalfReal]
        ring
      exact hboundary.trans hmass
  | succ j =>
      have hj : j < n := by omega
      let jf : Fin n := ⟨j, hj⟩
      have hjle : j <= n := hj.le.trans (Nat.le_refl n)
      have hjsucc : j + 1 <= n := hj
      rw [sixVertexCyclicRootPartition_succ p hjle,
        sixVertexCyclicRootPartition_succ p hjsucc]
      simpa [jf] using intervalIntegral_sixVertexFiniteRootDensity_adjacent
        hc hN hsol jf

theorem abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_of_mesh
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {mesh : Real}
    (hmesh : ∀ k < n + 1,
      sixVertexCyclicRootPartition p (k + 1) -
          sixVertexCyclicRootPartition p k ≤ mesh)
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f) :
    |∑ k ∈ Finset.range (n + 1),
          (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) -
        ∫ x in sixVertexCyclicRootPartition p 0..
            sixVertexCyclicRootPartition p (n + 1),
          f x * sixVertexFiniteRootDensity c N (n + 1) p x| ≤
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
        mesh * (2 * Real.pi) := by
  have hB : 0 ≤ sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hquad := abs_weightedLeftEndpointSum_sub_densityIntegral_le
    hf hlip (continuous_sixVertexFiniteRootDensity hc N (n + 1) p) hB
    (sixVertexCyclicRootPartition p) (fun _ => 1 / (N : Real)) (n + 1)
    (sixVertexCyclicRootPartition_ordered hopen) hmesh
    (fun x => abs_sixVertexFiniteRootDensity_le hc hN hcount p x)
    (sixVertexCyclicRootPartition_densityMass hc hN hhalf hsol)
  simpa using hquad


theorem abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f) :
    |∑ k ∈ Finset.range (n + 1),
          (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) -
        ∫ x in sixVertexCyclicRootPartition p 0..
            sixVertexCyclicRootPartition p (n + 1),
          f x * sixVertexFiniteRootDensity c N (n + 1) p x| <=
      (C : Real) * sixVertexFiniteRootDensityUniformBound c *
        (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
          (2 * Real.pi) := by
  have hnle : n + 1 <= N := by omega
  have hB : 0 <= sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hquad := abs_weightedLeftEndpointSum_sub_densityIntegral_le
    hf hlip (continuous_sixVertexFiniteRootDensity hc N (n + 1) p) hB
    (sixVertexCyclicRootPartition p) (fun _ => 1 / (N : Real)) (n + 1)
    (sixVertexCyclicRootPartition_ordered hopen)
    (sixVertexCyclicRootPartition_mesh_tail hc htail hN hhalf hopen hsol)
    (fun x => abs_sixVertexFiniteRootDensity_le hc hN hnle p x)
    (sixVertexCyclicRootPartition_densityMass hc hN hhalf hsol)
  simpa using hquad

end

end StatMech.FrontierD
