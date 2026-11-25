/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.SpherePackingDensityFour
import MathlibExt.Geometry.LatticePointCubeSandwich

/-!
# A lower bound for sphere packing in four dimensions

The integer lattice together with its translate by $(1/2,1/2,1/2,1/2)$ supports a packing
of balls of radius $1/2$. Counting two balls per unit cube gives the lower bound
$\pi^2/16$ for the optimal packing density.
-/

open Filter MeasureTheory Metric Set
open LatticePointCubeSandwich

namespace MathlibExt.Geometry.SpherePackingDensityFourWanted

noncomputable section

/-- **Statement of the lower bound for sphere packing in dimension four.** The proposition that
the sphere packing density $\Delta_4$ of $\mathbb{R}^4$, the supremum of the upper densities of
all packings of congruent balls in $\mathbb{R}^4$, satisfies $\frac{\pi^2}{16} \le \Delta_4$.

Source: dLOV2014 Table 1, center-density lower bound `0.12500 = 1/8`,
converted exactly to `π²/16`; `0.616850` is only an approximation. -/
@[expose] public def lowerBound_dLOV2014 : Prop :=
  ENNReal.ofReal (Real.pi ^ 2 / 16) ≤ spherePackingDensity4

private abbrev CubeIndex := Fin 4 → ℤ

/-- The lower corner and the midpoint of the half-open unit cube indexed by `z`. -/
private def center (z : CubeIndex) (b : Fin 2) : Space :=
  WithLp.toLp 2 (fun i ↦ (z i : ℝ) + (b : ℝ) / 2)

private lemma center_separated {z w : CubeIndex} {b c : Fin 2} (h : (z, b) ≠ (w, c)) :
    1 ≤ dist (center z b) (center w c) := by
  by_cases hbc : b = c
  · subst c
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ w i := by
      by_contra! he
      exact h (by rw [funext he])
    refine le_trans ?_ (PiLp.dist_apply_le (center z b) (center w b) i)
    change 1 ≤ dist ((z i : ℝ) + b / 2) ((w i : ℝ) + b / 2)
    rw [dist_add_right, Real.dist_eq, ← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hi)
  · have hcoord (i : Fin 4) : 1 / 2 ≤ dist (center z b i) (center w c i) := by
      change 1 / 2 ≤ dist ((z i : ℝ) + b / 2) ((w i : ℝ) + c / 2)
      -- Twice a coordinate difference between the two cosets is an odd integer.
      let k : ℤ := 2 * z i + b.val - (2 * w i + c.val)
      have hk : k ≠ 0 := by
        have := Fin.val_ne_of_ne hbc
        have := b.isLt
        have := c.isLt
        dsimp [k]
        omega
      have hdiff : (z i : ℝ) + b / 2 - ((w i : ℝ) + c / 2) = (k : ℝ) / 2 := by
        dsimp [k]
        push_cast
        ring
      rw [Real.dist_eq, hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      exact_mod_cast Int.one_le_abs hk
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (hcoord i) 2)
    rw [← PiLp.dist_sq_eq_of_L2] at hs
    norm_num at hs
    nlinarith [dist_nonneg (x := center z b) (y := center w c)]

private lemma balls_disjoint {z w : CubeIndex} {b c : Fin 2} (h : (z, b) ≠ (w, c)) :
    Disjoint (ball (center z b) (1 / 2)) (ball (center w c) (1 / 2)) := by
  apply ball_disjoint_ball
  linarith [center_separated h]

private def latticePacking : Packing where
  radius := 1 / 2
  radius_pos := by norm_num
  centers := range (fun p : CubeIndex × Fin 2 ↦ center p.1 p.2)
  interior_disjoint := by
    rintro _ ⟨⟨z, b⟩, rfl⟩ _ ⟨⟨w, c⟩, rfl⟩ hne
    exact balls_disjoint (fun h ↦ hne (congrArg (fun p ↦ center p.1 p.2) h))

private lemma dist_center_le_two {z : CubeIndex} {x : Fin 4 → ℝ}
    (hx : x ∈ integerUnitCube z) (b : Fin 2) : dist (center z b) (WithLp.toLp 2 x) ≤ 2 := by
  have hcoord (i : Fin 4) : dist (center z b i) (x i) ≤ 1 := by
    obtain ⟨hlo, hhi⟩ := mem_integerUnitCube_iff.mp hx i
    change dist ((z i : ℝ) + b / 2) (x i) ≤ 1
    rw [Real.dist_eq, abs_le]
    have hb : (b : ℝ) ≤ 1 := by exact_mod_cast (show b.val ≤ 1 by omega)
    constructor <;> linarith [show 0 ≤ (b : ℝ) by positivity]
  rw [PiLp.dist_eq_of_L2, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  calc
    _ ≤ ∑ _ : Fin 4, (1 : ℝ) ^ 2 := Finset.sum_le_sum fun i _ ↦
      pow_le_pow_left₀ dist_nonneg (hcoord i) 2
    _ = _ := by norm_num

private lemma ball_volume_real (p : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball p r) = r ^ 4 * (Real.pi ^ 2 / 2) := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity :
    0 ≤ Real.pi ^ 2 / 2)]

/-- Each unit cube meeting the radius-`r` ball contributes two disjoint balls, both
contained in the observation ball of radius `r + 3`. -/
private lemma covered_volume (r : ℝ) (hr : 0 ≤ r) :
    (r ^ 4 * (Real.pi ^ 2 / 2)) * (Real.pi ^ 2 / 16) ≤
      volume.real (packingRegion latticePacking ∩ ball (0 : Space) (r + 3)) := by
  classical
  let S := WithLp.toLp 2 ⁻¹' ball (0 : Space) r
  have hS : Bornology.IsBounded S :=
    (PiLp.antilipschitzWith_toLp 2 (fun _ : Fin 4 ↦ ℝ)).isBounded_preimage isBounded_ball
  let I := outerCubeSet S 1
  let : Fintype I := (finite_outerCubeSet S hS zero_lt_one).fintype
  have hcount : r ^ 4 * (Real.pi ^ 2 / 2) ≤ Fintype.card I := by
    have h := (cube_measure_sandwich S hS zero_lt_one).2
    have hm : volume S = volume (ball (0 : Space) r) :=
      (PiLp.volume_preserving_toLp (Fin 4)).measure_preimage measurableSet_ball.nullMeasurableSet
    rw [← ball_volume_real 0 hr]
    simpa [Measure.real, hm, I, Nat.card_eq_fintype_card] using h
  let balls (j : I × Fin 2) := ball (center j.1.val j.2) (1 / 2)
  have hdisj : Pairwise (fun j k ↦ Disjoint (balls j) (balls k)) := by
    intro j k hjk
    exact balls_disjoint fun he ↦ hjk (Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (congrArg (Prod.snd (α := CubeIndex)) he))
  have hsub : (⋃ j, balls j) ⊆ packingRegion latticePacking ∩ ball (0 : Space) (r + 3) := by
    intro y hy
    obtain ⟨⟨⟨z, hz⟩, b⟩, hy⟩ := mem_iUnion.mp hy
    refine ⟨mem_iUnion₂.mpr ⟨center z b, ⟨(z, b), rfl⟩, ball_subset_closedBall hy⟩, ?_⟩
    obtain ⟨x, hx, hxS⟩ := mem_outerCubeSet_iff.mp hz
    have hxr : dist (WithLp.toLp 2 x) (0 : Space) < r := by
      simpa [S, mem_ball] using hxS
    change dist y (center z b) < 1 / 2 at hy
    exact (dist_triangle4 y (center z b) (WithLp.toLp 2 x) 0).trans_lt
      (by linarith [dist_center_le_two hx b])
  calc
    _ ≤ (Fintype.card I : ℝ) * (Real.pi ^ 2 / 16) := by gcongr
    _ = ∑ j : I × Fin 2, volume.real (balls j) := by
      have hv (j : I × Fin 2) : volume.real (balls j) = (1 / 2 : ℝ) ^ 4 * (Real.pi ^ 2 / 2) :=
        ball_volume_real _ (by norm_num)
      simp [hv, Fintype.card_prod]
      ring
    _ = volume.real (⋃ j, balls j) :=
      (measureReal_iUnion_fintype hdisj (fun _ ↦ measurableSet_ball)
        (fun _ ↦ measure_ball_ne_top)).symm
    _ ≤ _ := measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_ball_ne_top)

private lemma finite_density_bound (n : ℕ) :
    ENNReal.ofReal (((n : ℝ) / (n + 3)) ^ 4 * (Real.pi ^ 2 / 16)) ≤
      finiteRadiusDensity latticePacking 0 ⟨n + 3, by positivity⟩ := by
  let R : PositiveRadius := ⟨n + 3, by positivity⟩
  have hf := (finiteRadiusDensity_le_one latticePacking 0 R).trans_lt ENNReal.one_lt_top
  rw [ENNReal.ofReal_le_iff_le_toReal hf.ne, finiteRadiusDensity, ENNReal.toReal_div]
  change _ ≤ volume.real _ / volume.real (ball (0 : Space) (n + 3))
  rw [ball_volume_real _ (by positivity), le_div_iff₀ (by positivity)]
  convert covered_volume n (Nat.cast_nonneg n) using 1
  field_simp

/-- **Lower bound for sphere packing in dimension four.** The sphere packing density $\Delta_4$
of $\mathbb{R}^4$, the supremum of the upper densities of all packings of congruent balls in
$\mathbb{R}^4$, satisfies $\frac{\pi^2}{16} \le \Delta_4$.

Source: dLOV2014 Table 1. Known literature bound; no Lean proof supplied. -/
public theorem lowerBound_dLOV2014_wanted : lowerBound_dLOV2014 := by
  let radius (n : ℕ) : PositiveRadius := ⟨n + 3, by positivity⟩
  have hrad : Tendsto radius atTop atTop := by
    refine tendsto_atTop.2 fun R ↦ ?_
    filter_upwards [eventually_ge_atTop ⌈(R : ℝ)⌉₊] with n hn
    change (R : ℝ) ≤ (n : ℝ) + 3
    linarith [Nat.le_ceil (R : ℝ), (Nat.cast_le (α := ℝ)).mpr hn]
  let f (n : ℕ) := ENNReal.ofReal (((n : ℝ) / (n + 3)) ^ 4 * (Real.pi ^ 2 / 16))
  have hlim : Tendsto f atTop (nhds (ENNReal.ofReal (Real.pi ^ 2 / 16))) := by
    apply ENNReal.tendsto_ofReal
    simpa using ((tendsto_natCast_div_add_atTop (3 : ℝ)).pow 4).mul_const (Real.pi ^ 2 / 16)
  calc
    ENNReal.ofReal (Real.pi ^ 2 / 16) = limsup f atTop := hlim.limsup_eq.symm
    _ ≤ limsup (centeredRadiusDensity latticePacking ∘ radius) atTop :=
      limsup_le_limsup (.of_forall fun n ↦ (finite_density_bound n).trans
        (le_iSup (finiteRadiusDensity latticePacking · (radius n)) 0))
    _ ≤ upperDensity latticePacking := hrad.limsup_comp_le_limsup
    _ ≤ spherePackingDensity4 := le_iSup upperDensity latticePacking

end
end MathlibExt.Geometry.SpherePackingDensityFourWanted
