/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import MathlibExt.Analysis.InnerProductSpace.MatchingPursuit
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Convergence of weak greedy matching pursuit -/

@[expose] public section

open scoped InnerProductSpace
open Filter Topology MathlibExt.Analysis.InnerProductSpace.MatchingPursuit

namespace MathlibExt.Analysis.InnerProductSpace.MatchingPursuitWanted

/-- A norm estimate in terms of the energy drop and the inner product of the displacement
with the second vector. -/
private theorem norm_sub_sq_le_energy_add {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (u v : H) :
    ‖u - v‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖v‖ ^ 2 + 2 * ‖⟪u - v, v⟫_𝕜‖ := by
  have h := (neg_le_abs (RCLike.re ⟪u - v, v⟫_𝕜)).trans (RCLike.abs_re_le_norm _)
  have hreal : -RCLike.re ⟪u - v, v⟫_𝕜 = ‖v‖ ^ 2 - RCLike.re ⟪u, v⟫_𝕜 := by
    rw [inner_sub_left, map_sub, inner_self_eq_norm_sq]
    ring
  rw [hreal] at h
  rw [norm_sub_sq (𝕜 := 𝕜) u v]
  linarith

/-- **Convergence of matching pursuit** (S. Mallat and Z. Zhang, *Matching pursuits with
time-frequency dictionaries*, IEEE Trans. Signal Process. 41 (1993), Theorem 1). Let `H` be a
Hilbert space, `D : Γ → H` a dictionary of unit vectors and `0 < α ≤ 1`. If the selected
indices `γₙ` satisfy the weak greedy rule
`α · sup_γ |⟨D γ, Rⁿ f⟩| ≤ |⟨D γₙ, Rⁿ f⟩|` (equation (11)) for every `n`, then the residues
`R^m f` converge to the orthogonal projection of `f` on the orthogonal complement of the span of
the dictionary (equation (18)). (The orthogonal complement of the span equals that of its
closure.) -/
theorem tendsto_residue_starProjection_orthogonal
    {𝕜 H Γ : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (D : Γ → H) (hD : ∀ γ, ‖D γ‖ = 1) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (γs : ℕ → Γ) (f : H)
    (hsel : ∀ n, α * ⨆ γ, ‖⟪D γ, residue (𝕜 := 𝕜) (D ∘ γs) f n⟫_𝕜‖ ≤
      ‖⟪D (γs n), residue (𝕜 := 𝕜) (D ∘ γs) f n⟫_𝕜‖) :
    Tendsto (fun m => residue (𝕜 := 𝕜) (D ∘ γs) f m) atTop
      (𝓝 ((Submodule.span 𝕜 (Set.range D))ᗮ.starProjection f)) := by
  let r := residue (𝕜 := 𝕜) (D ∘ γs) f
  let c (n : ℕ) := ‖⟪D (γs n), r n⟫_𝕜‖
  let e (n : ℕ) := ‖r n‖ ^ 2
  have hr (j : ℕ) : r (j + 1) = r j - ⟪D (γs j), r j⟫_𝕜 • D (γs j) :=
    residue_succ _ _ _
  have he (j : ℕ) : e j = (c j) ^ 2 + e (j + 1) :=
    norm_sq_residue_eq _ _ _ (hD (γs j))
  have hmono : Antitone e := antitone_nat_of_succ_le fun j => by
    rw [he j]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hbelow : BddBelow (Set.range e) := ⟨0, by rintro _ ⟨n, rfl⟩; exact sq_nonneg _⟩
  have he_lim : Tendsto e atTop (𝓝 (⨅ n, e n)) := tendsto_atTop_ciInf hmono hbelow
  have hgreedy (n : ℕ) (γ : Γ) : α * ‖⟪D γ, r n⟫_𝕜‖ ≤ c n := by
    have hb : BddAbove (Set.range fun a : Γ => ‖⟪D a, r n⟫_𝕜‖) := by
      refine ⟨‖r n‖, ?_⟩
      rintro _ ⟨a, rfl⟩
      simpa only [hD a, one_mul] using norm_inner_le_norm (𝕜 := 𝕜) (D a) (r n)
    exact (mul_le_mul_of_nonneg_left (le_ciSup hb γ) hα₀.le).trans (hsel n)
  have hvec {a b : ℕ} (hab : a ≤ b) :
      r a - r b = ∑ j ∈ Finset.Ico a b, ⟪D (γs j), r j⟫_𝕜 • D (γs j) := by
    calc
      r a - r b = -r b - -r a := by abel
      _ = ∑ j ∈ Finset.Ico a b, (-r (j + 1) - (-r j)) :=
        (Finset.sum_Ico_sub (fun j => -r j) hab).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hr j]
        abel
  have henergy {a b : ℕ} (hab : a ≤ b) : ∑ j ∈ Finset.Ico a b, (c j) ^ 2 = e a - e b := by
    calc
      _ = ∑ j ∈ Finset.Ico a b, (-e (j + 1) - (-e j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [he j]
        ring
      _ = -e b - -e a := Finset.sum_Ico_sub (fun j => -e j) hab
      _ = _ := by ring
  -- Use the smallest coefficient on the intervening indices so the mixed inner products
  -- are bounded by a sum of squares, not by a sum of absolute coefficients.
  have hcross {a b k : ℕ} (hab : a ≤ b) (hk : ∀ j ∈ Finset.Ico a b, c k ≤ c j) :
      ‖⟪r a - r b, r k⟫_𝕜‖ ≤ (e a - e b) / α := by
    rw [hvec hab, sum_inner]
    calc
      _ ≤ ∑ j ∈ Finset.Ico a b, ‖⟪⟪D (γs j), r j⟫_𝕜 • D (γs j), r k⟫_𝕜‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ico a b, (c j) ^ 2 / α := by
        apply Finset.sum_le_sum
        intro j hj
        rw [inner_smul_left, norm_mul, RCLike.norm_conj]
        have hbound : ‖⟪D (γs j), r k⟫_𝕜‖ ≤ c j / α :=
          (le_div_iff₀ hα₀).mpr (by rw [mul_comm]; exact (hgreedy k (γs j)).trans (hk j hj))
        change c j * _ ≤ _
        rw [pow_two, mul_div_assoc]
        have hc : 0 ≤ c j := norm_nonneg _
        exact mul_le_mul_of_nonneg_left hbound hc
      _ = (e a - e b) / α := by rw [← Finset.sum_div, henergy hab]
  let C := 3 / α
  have hC : 0 < C := by dsimp [C]; positivity
  have hinvOne : 1 ≤ α⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hα₀).mpr (by simpa only [one_mul] using hα₁)
  have hdist {a b : ℕ} (hab : a ≤ b) : ∃ k : ℕ,
      ‖r a - r k‖ ^ 2 ≤ C * (e a - e b) ∧ ‖r b - r k‖ ^ 2 ≤ C * (e a - e b) := by
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (Finset.Icc a b) c
      (Finset.nonempty_Icc.mpr hab)
    obtain ⟨hak, hkb⟩ := Finset.mem_Icc.mp hk
    have h₁ := hcross hak (k := k) <| fun j hj =>
      hmin j (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2.le.trans hkb⟩)
    have h₂ := hcross hkb (k := k) <| fun j hj =>
      hmin j (Finset.mem_Icc.mpr ⟨hak.trans (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2.le⟩)
    have hneg : ‖⟪r b - r k, r k⟫_𝕜‖ = ‖⟪r k - r b, r k⟫_𝕜‖ := by
      rw [show r b - r k = -(r k - r b) by abel, inner_neg_left, norm_neg]
    have h₃ : ‖r a - r k‖ ^ 2 ≤ e a - e k + 2 * ‖⟪r a - r k, r k⟫_𝕜‖ :=
      norm_sub_sq_le_energy_add (𝕜 := 𝕜) _ _
    have h₄ : ‖r b - r k‖ ^ 2 ≤ e b - e k + 2 * ‖⟪r k - r b, r k⟫_𝕜‖ := by
      rw [← hneg]
      exact norm_sub_sq_le_energy_add (𝕜 := 𝕜) _ _
    have hea := hmono hak
    have heb := hmono hkb
    have hinv : 0 ≤ α⁻¹ := inv_nonneg.mpr hα₀.le
    have hscale := mul_le_mul_of_nonneg_right hinvOne (sub_nonneg.mpr (hmono hab))
    simp only [div_eq_mul_inv] at h₁ h₂
    refine ⟨k, ?_, ?_⟩
    · dsimp [C]
      rw [div_eq_mul_inv]
      nlinarith [mul_nonneg (sub_nonneg.mpr heb) hinv]
    · dsimp [C]
      rw [div_eq_mul_inv]
      nlinarith [mul_nonneg (sub_nonneg.mpr hea) hinv]
  have hcauchy : CauchySeq r := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ := (ε / 2) ^ 2 / C
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp he_lim δ hδ)
    have horder (a b : ℕ) (ha : N ≤ a) (hab : a ≤ b) : dist (r a) (r b) < ε := by
      have htail : e a - e b < δ := by
        have hclose := hN a ha
        rw [Real.dist_eq] at hclose
        have hlow : (⨅ n, e n) ≤ e b := ciInf_le hbelow b
        exact ((sub_le_sub_left hlow _).trans (le_abs_self _)).trans_lt hclose
      have hbound : C * (e a - e b) < (ε / 2) ^ 2 := by
        rw [mul_comm]
        exact (lt_div_iff₀ hC).mp htail
      obtain ⟨k, ha', hb'⟩ := hdist hab
      have hk₁ : dist (r a) (r k) < ε / 2 := by
        rw [dist_eq_norm]
        exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp (ha'.trans_lt hbound)
      have hk₂ : dist (r b) (r k) < ε / 2 := by
        rw [dist_eq_norm]
        exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp (hb'.trans_lt hbound)
      calc
        dist (r a) (r b) ≤ dist (r a) (r k) + dist (r b) (r k) := dist_triangle_right _ _ _
        _ < ε := by linarith
    refine ⟨N, ?_⟩
    intro a ha b hb
    rcases le_total a b with hab | hba
    · exact horder a b ha hab
    · rw [dist_comm]
      exact horder b a hb hba
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hcoeff : Tendsto (fun n => (c n) ^ 2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => e (n + 1)) atTop (𝓝 (⨅ n, e n)) :=
      he_lim.comp (tendsto_add_atTop_nat 1)
    have hz : Tendsto (fun n => e n - e (n + 1)) atTop (𝓝 0) := by
      simpa only [sub_self] using he_lim.sub ht
    exact hz.congr fun n => by rw [he n, add_sub_cancel_right]
  have horth (a : Γ) : ⟪D a, v⟫_𝕜 = 0 := by
    have ht : Tendsto (fun n => (α * ‖⟪D a, r n⟫_𝕜‖) ^ 2) atTop
        (𝓝 ((α * ‖⟪D a, v⟫_𝕜‖) ^ 2)) :=
      (((tendsto_const_nhds (x := D a)).inner hv).norm.const_mul α).pow 2
    have hh : (α * ‖⟪D a, v⟫_𝕜‖) ^ 2 ≤ 0 :=
      le_of_tendsto_of_tendsto ht hcoeff <| Eventually.of_forall fun n =>
        (sq_le_sq₀ (mul_nonneg hα₀.le (norm_nonneg _)) (norm_nonneg _)).mpr (hgreedy n a)
    have hzero : α * ‖⟪D a, v⟫_𝕜‖ = 0 := by nlinarith
    exact norm_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hα₀.ne')
  let V := Submodule.span 𝕜 (Set.range D)
  have hv_mem : v ∈ Vᗮ := by
    have hspan : V ≤ (𝕜 ∙ v)ᗮ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (horth a)
    exact (V.mem_orthogonal v).mpr fun x hx =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hspan hx)
  have hproj (n : ℕ) : Vᗮ.starProjection (r n) = Vᗮ.starProjection f := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hd : D (γs n) ∈ V := Submodule.subset_span (Set.mem_range_self _)
      rw [hr n, map_sub, ih, map_smul, Submodule.starProjection_orthogonal_apply_eq_zero hd,
        smul_zero, sub_zero]
  have hp : Tendsto (fun n => Vᗮ.starProjection (r n)) atTop (𝓝 (Vᗮ.starProjection v)) :=
    Vᗮ.starProjection.continuous.continuousAt.tendsto.comp hv
  have hp' : Tendsto (fun n => Vᗮ.starProjection (r n)) atTop (𝓝 (Vᗮ.starProjection f)) :=
    tendsto_const_nhds.congr fun n => (hproj n).symm
  have hv_eq : v = Vᗮ.starProjection f :=
    (Submodule.starProjection_eq_self_iff.mpr hv_mem).symm.trans (tendsto_nhds_unique hp hp')
  rwa [hv_eq] at hv

end MathlibExt.Analysis.InnerProductSpace.MatchingPursuitWanted
