/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRootGapFirstOrder
import Code.FrontierD.SixVertexBetheTailLimit
import Code.FrontierD.SixVertexBetheFourierPhysicalDensity









namespace StatMech.FrontierD

noncomputable section

open Filter Topology

theorem tendsto_sixVertexHalfFilledFiniteRootDensity_at_fourierPhysical
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    Tendsto (fun k => sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x)
      atTop (nhds (sixVertexFourierPhysicalDensity c hc x)) := by
  let w := sixVertexRootDensityWeight c x
  have hw : 0 < w := sixVertexRootDensityWeight_pos hc x
  have hweighted := tendsto_sixVertexSelectedWeightedDensity_at hc htail hx
  have hdiv := hweighted.div_const w
  have htailEq := sixVertexTailRootDensity_eq_fourierPhysicalDensity hc htail x hx
  convert hdiv using 1
  · funext k
    rw [sixVertexSelectedFiniteRootDensity_eq_halfFilled]
    dsimp [w]
    exact (mul_div_cancel_left₀ _ hw.ne').symm
  · congr 1
    dsimp [w]
    rw [htailEq]
    exact (mul_div_cancel_left₀ _ hw.ne').symm



theorem sixVertexFourierPhysicalDensity_lipschitzOn
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x z : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hz : z ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexFourierPhysicalDensity c hc x -
        sixVertexFourierPhysicalDensity c hc z| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) * |x - z| := by
  have htx := tendsto_sixVertexHalfFilledFiniteRootDensity_at_fourierPhysical
    hc htail hx
  have htz := tendsto_sixVertexHalfFilledFiniteRootDensity_at_fourierPhysical
    hc htail hz
  have hlim := (htx.sub htz).abs
  let C := (sixVertexFiniteRootDensityLipschitzConstant c : Real) * |x - z|
  have hevent : ∀ᶠ k : Nat in atTop,
      |sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x -
        sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) z| ∈
        Set.Iic C := by
    filter_upwards [] with k
    have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
    have hn : (k + 1) + (k + 1) <= sixVertexFourWidth 0 k := by
      unfold sixVertexFourWidth
      omega
    have hlip := lipschitzWith_sixVertexFiniteRootDensity hc hN hn
      (sixVertexHalfFilledBetheRoots hc k)
    change |_ - _| <= C
    calc
      |_ - _| = dist
          (sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x)
          (sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) z) := by
            rw [Real.dist_eq]
      _ <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
          dist x z := hlip.dist_le_mul x z
      _ = C := by rw [Real.dist_eq]
  exact isClosed_Iic.mem_of_tendsto hlim hevent

theorem sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexTailFiniteDensityFloor c <=
      sixVertexFourierPhysicalDensity c hc x := by
  have hlim := tendsto_sixVertexHalfFilledFiniteRootDensity_at_fourierPhysical
    hc htail hx
  apply isClosed_Ici.mem_of_tendsto hlim
  filter_upwards [] with k
  exact sixVertexTailFiniteDensityFloor_le hc (sixVertexFourWidth_pos 0 k)
    (by unfold sixVertexFourWidth; omega)
    (sixVertexHalfFilledBetheRoots hc k) x


theorem sixVertexFourierPhysicalDensity_reciprocal_lipschitzOn
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {x z : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hz : z ∈ Set.Icc (-Real.pi) Real.pi) :
    |1 / sixVertexFourierPhysicalDensity c hc x -
        1 / sixVertexFourierPhysicalDensity c hc z| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          sixVertexTailFiniteDensityFloor c ^ 2 * |x - z| := by
  let rhoX := sixVertexFourierPhysicalDensity c hc x
  let rhoZ := sixVertexFourierPhysicalDensity c hc z
  let floor := sixVertexTailFiniteDensityFloor c
  let L := (sixVertexFiniteRootDensityLipschitzConstant c : Real)
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hxLower : floor <= rhoX :=
    sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail hx
  have hzLower : floor <= rhoZ :=
    sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail hz
  have hxPos : 0 < rhoX := hfloor.trans_le hxLower
  have hzPos : 0 < rhoZ := hfloor.trans_le hzLower
  have hlip := sixVertexFourierPhysicalDensity_lipschitzOn hc htail hx hz
  have hden : floor ^ 2 <= rhoX * rhoZ := by
    nlinarith [mul_le_mul hxLower hzLower hfloor.le hxPos.le]
  change |1 / rhoX - 1 / rhoZ| <= L / floor ^ 2 * |x - z|
  rw [show 1 / rhoX - 1 / rhoZ = (rhoZ - rhoX) / (rhoX * rhoZ) by
    field_simp [hxPos.ne', hzPos.ne']]
  rw [abs_div, abs_of_pos (mul_pos hxPos hzPos)]
  have hnum : |rhoZ - rhoX| <= L * |x - z| := by
    simpa [abs_sub_comm] using hlip
  calc
    |rhoZ - rhoX| / (rhoX * rhoZ) <=
        (L * |x - z|) / (rhoX * rhoZ) :=
      div_le_div_of_nonneg_right hnum (mul_pos hxPos hzPos).le
    _ <= (L * |x - z|) / floor ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hfloor) hden
    _ = L / floor ^ 2 * |x - z| := by ring

end

end StatMech.FrontierD
