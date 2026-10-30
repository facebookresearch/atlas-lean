/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Lp.Compactness

@[expose] public section

namespace MathlibExt.Analysis.Normed.Lp.CompactnessTest

open MathlibExt.Analysis.Normed.Lp.Compactness
open Filter
open scoped ENNReal Topology

/-- Truncating the unit vector at coordinate `0` to one coordinate is the identity. -/
example : lpTrunc (2 : ℝ≥0∞) 1 (lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ))
    = lp.single (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ) := by
  ext j
  rw [lpTrunc_apply]
  by_cases hj : j < 1
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj]
    exact (lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 0 (5 : ℝ) (by omega : j ≠ 0)).symm

/-- Truncating the unit vector at coordinate `1` to one coordinate kills it. -/
example : lpTrunc (2 : ℝ≥0∞) 1 (lp.single (E := fun _ : ℕ => ℝ) 2 1 (5 : ℝ)) = 0 := by
  ext j
  simp only [lpTrunc_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases hj : j < 1
  · rw [ite_eq_left hj]
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    subst hj0
    exact lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 1 (5 : ℝ) (by norm_num : (0 : ℕ) ≠ 1)
  · rw [ite_eq_right hj]

/-- Truncation is a contraction on `ℓ² (ℕ, ℝ)`. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (x : lp (fun _ : ℕ => ℝ) 2) (N : ℕ) :
    ‖lpTrunc (2 : ℝ≥0∞) N x‖ ≤ ‖x‖ :=
  norm_lpTrunc_le N x

/-- The tail of a vector of `ℓ² (ℕ, ℝ)` is bounded by the vector itself. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (x : lp (fun _ : ℕ => ℝ) 2) (N : ℕ) :
    ‖x - lpTrunc (2 : ℝ≥0∞) N x‖ ≤ ‖x‖ :=
  norm_sub_lpTrunc_le N x

/-- The truncations of a vector of `ℓ² (ℕ, ℝ)` converge to the vector. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (x : lp (fun _ : ℕ => ℝ) 2) :
    Tendsto (fun N => lpTrunc (2 : ℝ≥0∞) N x) atTop (𝓝 x) :=
  tendsto_lpTrunc (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x

/-- A singleton in `ℓ² (ℕ, ℝ)` is relatively compact: its truncations stabilize. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    IsCompact (closure {lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)}) := by
  rw [isCompact_closure_iff_bounded_and_uniformTailVanishing hp, isBounded_iff_forall_norm_le]
  have htrunc : lpTrunc (2 : ℝ≥0∞) 1 (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ))
      = lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) := by
    ext j
    rw [lpTrunc_apply]
    by_cases hj : j < 1
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj]
      exact (lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) (by omega : j ≠ 0)).symm
  refine ⟨⟨1, fun x hx => ?_⟩, fun ε hε => ⟨1, fun x hx => ?_⟩⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [lp.norm_single (by positivity : (0 : ℝ≥0∞) < 2), norm_one]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [htrunc, sub_self, norm_zero]
    exact hε

/-- A singleton in `ℓ² (ℕ, ℝ)` is compact, via the compact form of the criterion. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    IsCompact {lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ)} := by
  rw [isCompact_iff_isComplete_and_bounded_and_uniformTailVanishing hp,
    isBounded_iff_forall_norm_le]
  have htrunc : lpTrunc (2 : ℝ≥0∞) 1 (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ))
      = lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) := by
    ext j
    rw [lpTrunc_apply]
    by_cases hj : j < 1
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj]
      exact (lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) (by omega : j ≠ 0)).symm
  refine ⟨isCompact_singleton.isComplete, ⟨1, fun x hx => ?_⟩,
    fun ε hε => ⟨1, fun x hx => ?_⟩⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [lp.norm_single (by positivity : (0 : ℝ≥0∞) < 2), norm_one]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [htrunc, sub_self, norm_zero]
    exact hε

/-- The unit vectors of `ℓ² (ℕ, ℝ)` are not relatively compact: the `N`-th
unit vector has tail norm `1` at truncation length `N`. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    ¬ TotallyBounded
      (Set.range (fun n : ℕ => lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ))) := by
  intro hTB
  rw [totallyBounded_iff_bounded_and_uniformTailVanishing hp] at hTB
  obtain ⟨-, htail⟩ := hTB
  obtain ⟨N, hN⟩ := htail (1 / 2) (by norm_num)
  have h := hN (lp.single (E := fun _ : ℕ => ℝ) 2 N (1 : ℝ)) ⟨N, rfl⟩
  have htrunc : lpTrunc (2 : ℝ≥0∞) N (lp.single (E := fun _ : ℕ => ℝ) 2 N (1 : ℝ)) = 0 := by
    ext j
    simp only [lpTrunc_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases hj : j < N
    · rw [ite_eq_left hj]
      exact lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 N (1 : ℝ) (by omega : j ≠ N)
    · rw [ite_eq_right hj]
  rw [htrunc, sub_zero, lp.norm_single (by positivity : (0 : ℝ≥0∞) < 2), norm_one] at h
  norm_num at h

/-- A weighted sequence tending to `0` together with its limit is relatively
compact in `ℓ² (ℕ, ℝ)`: every element is supported on coordinate `0`, so all
tails vanish at truncation length `1`. -/
example (hp : (2 : ℝ≥0∞) ≠ ⊤) [Fact (1 ≤ (2 : ℝ≥0∞))] :
    IsCompact (closure (Set.range
        (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ) • lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ))
      ∪ {0})) := by
  rw [isCompact_closure_iff_bounded_and_uniformTailVanishing hp, isBounded_iff_forall_norm_le]
  have htrunc : lpTrunc (2 : ℝ≥0∞) 1 (lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ))
      = lp.single (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) := by
    ext j
    rw [lpTrunc_apply]
    by_cases hj : j < 1
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj]
      exact (lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 0 (1 : ℝ) (by omega : j ≠ 0)).symm
  refine ⟨⟨1, fun x hx => ?_⟩, fun ε hε => ⟨1, fun x hx => ?_⟩⟩
  · rcases hx with ⟨n, rfl⟩ | hx
    · rw [norm_smul, lp.norm_single (by positivity : (0 : ℝ≥0∞) < 2), norm_one, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simp
  · rcases hx with ⟨n, rfl⟩ | hx
    · rw [lpTrunc_smul, htrunc, sub_self, norm_zero]
      exact hε
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [lpTrunc_zero, sub_self, norm_zero]
      exact hε

/-- The criterion fails for `p = ∞`: a vector all of whose coordinates are `1`
has tail norm `1` at every truncation length, so its singleton does not have
uniformly vanishing tails, although it is compact. -/
theorem not_uniformTailVanishing_of_forall_apply_eq_one
    (x : lp (fun _ : ℕ => ℝ) ⊤) (hx : ∀ i, x i = 1) :
    ¬ UniformTailVanishing (⊤ : ℝ≥0∞) {x} := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  have h1 := hN x (Set.mem_singleton x)
  have hnorm : ‖x - lpTrunc (⊤ : ℝ≥0∞) N x‖ = 1 := by
    rw [lp.norm_eq_ciSup]
    apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    · intro i
      rw [lp.coeFn_sub, Pi.sub_apply, lpTrunc_apply]
      by_cases hi : i < N
      · rw [ite_eq_left hi, hx i, sub_self, norm_zero]
        exact zero_le_one
      · rw [ite_eq_right hi, hx i, sub_zero, norm_one]
    · intro b hb
      refine ⟨N, ?_⟩
      rw [lp.coeFn_sub, Pi.sub_apply, lpTrunc_apply, hx N,
        ite_eq_right (lt_irrefl N), sub_zero, norm_one]
      exact hb
  rw [hnorm] at h1
  norm_num at h1

/-- The singleton containing the constant sequence `1` in `ℓ^∞` does not have
uniformly vanishing tails. -/
example : ¬ UniformTailVanishing (⊤ : ℝ≥0∞)
    {⟨fun _ : ℕ => (1 : ℝ), by
      apply memℓp_infty
      refine ⟨1, ?_⟩
      rintro y ⟨n, rfl⟩
      simp⟩} := by
  apply not_uniformTailVanishing_of_forall_apply_eq_one
  intro i
  rfl

/-- Finite-`p` truncation is the existing bundled Schauder projection. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (x : lp (fun _ : ℕ => ℝ) 2) (N : ℕ) :
    lpTrunc (2 : ℝ≥0∞) N x =
      (MathlibExt.Analysis.Normed.Lp.SchauderBasis.lpSchauderBasis
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).proj N x :=
  lpTrunc_eq_lpSchauderBasis_proj (by norm_num) N x

/-- Restriction preserves an in-range coordinate of a concrete unit vector. -/
example : lpRestrict 2 (lp.single (E := fun _ : ℕ => ℝ) 2 1 (5 : ℝ)) (1 : Fin 2) = 5 := by
  rw [lpRestrict_apply]
  simp

/-- Extension preserves an in-range coordinate and vanishes at the support boundary. -/
example (z : Fin 2 → ℝ) : lpExtend 2 z 1 = z 1 ∧ lpExtend 2 z 2 = 0 := by
  constructor
  · rw [lpExtend_apply, dite_eq_left (by decide : (1 : ℕ) < 2)]
    rfl
  · rw [lpExtend_apply, dite_eq_right (by decide : ¬ (2 : ℕ) < 2)]

/-- Lifting an extended finite vector preserves its coordinates and zero support boundary. -/
example (z : Fin 2 → ℝ) :
    lpLift (2 : ℝ≥0∞) 2 (lpExtend 2 z) 1 = z 1 ∧
      lpLift (2 : ℝ≥0∞) 2 (lpExtend 2 z) 2 = 0 := by
  constructor
  · rw [lpLift_apply, ite_eq_left (by decide : (1 : ℕ) < 2),
      lpExtend_apply, dite_eq_left (by decide : (1 : ℕ) < 2)]
    rfl
  · rw [lpLift_apply, ite_eq_right (by decide : ¬ (2 : ℕ) < 2)]

/-- The lift norm estimate applies directly to an extended finite coordinate vector. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (z : Fin 2 → ℝ) :
    ‖lpLift (2 : ℝ≥0∞) 2 (lpExtend 2 z)‖ ≤
      (2 : ℝ) ^ (1 / (2 : ℝ≥0∞).toReal) * ‖z‖ := by
  have hext : (fun i : Fin 2 => lpExtend 2 z i) = z := by
    funext i
    exact dite_eq_left i.2
  simpa only [hext, Nat.cast_ofNat] using
    norm_lpLift_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) 2 (lpExtend 2 z)

/-- Tail monotonicity includes the empty truncation `N = 0`, for every upper cut. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] (x : lp (fun _ : ℕ => ℝ) 2) (M : ℕ) :
    ‖x - lpTrunc (2 : ℝ≥0∞) M x‖ ≤ ‖x - lpTrunc (2 : ℝ≥0∞) 0 x‖ :=
  norm_sub_lpTrunc_mono (Nat.zero_le M) x

/-- A caller with the former norm-bound hypothesis uses the canonical boundedness interface. -/
example [Fact (1 ≤ (2 : ℝ≥0∞))] {K : Set (lp (fun _ : ℕ => ℝ) 2)}
    (hNorm : ∃ C, ∀ x ∈ K, ‖x‖ ≤ C) (hTail : UniformTailVanishing (2 : ℝ≥0∞) K) :
    TotallyBounded K :=
  (totallyBounded_iff_bounded_and_uniformTailVanishing
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mpr
      ⟨isBounded_iff_forall_norm_le.mpr hNorm, hTail⟩

end MathlibExt.Analysis.Normed.Lp.CompactnessTest
