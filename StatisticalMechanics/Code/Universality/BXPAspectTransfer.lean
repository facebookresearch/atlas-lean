/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Lattice.JordanExteriorClosure
import Code.Universality.BXPAllAspect
import Code.Universality.BXPTransfer
import Code.Universality.CrossingReflection

open Set MeasureTheory SimpleGraph

namespace StatMech
namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip



theorem bat_swapConfig_involutive (ω : ConfigSpace (Sym2 (Site 2))) :
    crf_swapConfig (crf_swapConfig ω) = ω := by
  funext e
  rw [crf_swapConfig_apply, crf_swapConfig_apply]
  induction e using Sym2.inductionOn with
  | _ x y => simp [Sym2.map_mk]

theorem bat_horizontal_to_vertical_swap (a b c d : ℤ)
    (ω : ConfigSpace (Sym2 (Site 2)))
    (h : HorizontalCrossing ω a b c d) :
    VerticalCrossing (crf_swapConfig ω) c d a b := by
  apply crf_horizontal_to_vertical c d a b (crf_swapConfig ω)
  simpa only [bat_swapConfig_involutive] using h

theorem bat_translatedHorizontal_eq_physical (τ : Site 2) (a b : ℤ) :
    translatedHorizontalCrossingEvent τ a b =
      horizontalCrossingEvent (τ 0) (a + τ 0) (τ 1) (b + τ 1) := by
  rw [bxr_translatedHorizontalCrossingEvent_eq,
    ← cti_horizontalCrossingEvent_translate 0 a 0 b τ]
  simp only [zero_add]

theorem bat_translatedVertical_eq_physical (τ : Site 2) (a b : ℤ) :
    translatedVerticalCrossingEvent τ a b =
      verticalCrossingEvent (τ 0) (a + τ 0) (τ 1) (b + τ 1) := by
  rw [bxr_translatedVerticalCrossingEvent_eq,
    ← cti_verticalCrossingEvent_translate 0 a 0 b τ]
  simp only [zero_add]



theorem bat_verticalIntersection (ω : ConfigSpace (Sym2 (Site 2)))
    {a b c m m' d : ℤ} (hab : a ≤ b) (hcm : c ≤ m) (hmm' : m ≤ m')
    (hm'd : m' ≤ d) (hcm' : c < m') (hmd : m < d) :
    VerticalCrossing ω a b c m' → HorizontalCrossing ω a b m m' →
      VerticalCrossing ω a b m d → VerticalCrossing ω a b c d := by
  intro hV₁ hH hV₂
  have hsepL : vsFix_VSeparatesHFixed (crf_swapConfig ω) c m' m m' a b :=
    vsFix_arc_sides_imp (crf_swapConfig ω) c m' m m' a b
      (jec_vsFix_arc_sides (crf_swapConfig ω) hcm' hab)
  have hsepR : vsFix_VSeparatesHFixed (crf_swapConfig ω) m d m m' a b :=
    vsFix_arc_sides_imp (crf_swapConfig ω) m d m m' a b
      (jec_vsFix_arc_sides (crf_swapConfig ω) hmd hab)
  have hglue := vsFix_hvIntersection (crf_swapConfig ω)
    hcm hmm' hm'd hsepL hsepR
  apply crf_horizontal_to_vertical a b c d ω
  exact hglue (crf_vertical_to_horizontal a b c m' ω hV₁)
    (bat_horizontal_to_vertical_swap a b m m' ω hH)
    (crf_vertical_to_horizontal a b m d ω hV₂)


theorem bat_vertical_strip_glue
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a b c m m' d : ℤ}
    (hab : a ≤ b) (hcm : c ≤ m) (hmm' : m ≤ m') (hm'd : m' ≤ d)
    (hcm' : c < m') (hmd : m < d) :
    μ.real (verticalCrossingEvent a b c m')
        * μ.real (horizontalCrossingEvent a b m m')
        * μ.real (verticalCrossingEvent a b m d)
      ≤ μ.real (verticalCrossingEvent a b c d) := by
  set A := verticalCrossingEvent a b c m'
  set B := horizontalCrossingEvent a b m m'
  set C := verticalCrossingEvent a b m d
  have hA : IsIncreasing A := verticalCrossingEvent_isIncreasing a b c m'
  have hB : IsIncreasing B := horizontalCrossingEvent_isIncreasing a b m m'
  have hC : IsIncreasing C := verticalCrossingEvent_isIncreasing a b m d
  have hsub : A ∩ B ∩ C ⊆ verticalCrossingEvent a b c d := by
    rintro ω ⟨⟨h1, h2⟩, h3⟩
    exact bat_verticalIntersection ω hab hcm hmm' hm'd hcm' hmd h1 h2 h3
  have h1 := hpa A B hA hB
  have h2 := hpa (A ∩ B) C (hA.inter hB) hC
  calc
    μ.real A * μ.real B * μ.real C
        ≤ μ.real (A ∩ B) * μ.real C :=
          mul_le_mul_of_nonneg_right h1 measureReal_nonneg
    _ ≤ μ.real (A ∩ B ∩ C) := h2
    _ ≤ μ.real (verticalCrossingEvent a b c d) := measureReal_mono hsub



theorem bat_horizontal_lower_of_bxp {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
    {ρ : ℝ} {n0 n : ℕ} (τ : Site 2) (hn : n0 ≤ n) :
    boxCrossingInf μ ρ n0 ≤
      μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ)) := by
  unfold boxCrossingInf
  apply csInf_le (boxCrossingProbabilities_bddBelow μ ρ n0)
  exact ⟨n, τ, hn, Or.inl rfl⟩

theorem bat_vertical_lower_of_bxp {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
    {ρ : ℝ} {n0 n : ℕ} (τ : Site 2) (hn : n0 ≤ n) :
    boxCrossingInf μ ρ n0 ≤
      μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋) := by
  unfold boxCrossingInf
  apply csInf_le (boxCrossingProbabilities_bddBelow μ ρ n0)
  exact ⟨n, τ, hn, Or.inr rfl⟩



theorem bat_horizontal_physical_mono {τ : Site 2} {w w' h : ℤ}
    (hw : 0 < w) (hww' : w ≤ w') :
    horizontalCrossingEvent (τ 0) (w' + τ 0) (τ 1) (h + τ 1) ⊆
      horizontalCrossingEvent (τ 0) (w + τ 0) (τ 1) (h + τ 1) := by
  intro ω hω
  have hbase := cti_horizontalCrossing_translate_bwd 0 w' 0 h τ ω (by
    simpa only [zero_add, add_comm] using hω)
  have hnarrow := bxa_horizontalCrossing_mono_width hw hww' hbase
  have := cti_horizontalCrossing_translate_fwd 0 w 0 h τ ω hnarrow
  simpa only [zero_add, add_comm] using this

theorem bat_vertical_physical_mono {τ : Site 2} {w h h' : ℤ}
    (hh : 0 < h) (hh' : h ≤ h') :
    verticalCrossingEvent (τ 0) (w + τ 0) (τ 1) (h' + τ 1) ⊆
      verticalCrossingEvent (τ 0) (w + τ 0) (τ 1) (h + τ 1) := by
  intro ω hω
  have hbase := cti_verticalCrossing_translate_bwd 0 w 0 h' τ ω (by
    simpa only [zero_add, add_comm] using hω)
  have hnarrow := bxa_verticalCrossing_mono_height hh hh' hbase
  have := cti_verticalCrossing_translate_fwd 0 w 0 h τ ω hnarrow
  simpa only [zero_add, add_comm] using this



theorem bat_horizontal_chain
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (c : ℝ) (hc : 0 ≤ c)
    (n W : ℕ) (hn : 1 ≤ n) (hW : n < W) (τ : Site 2)
    (hH : ∀ σ : Site 2,
      c ≤ μ.real (translatedHorizontalCrossingEvent σ (W : ℤ) (n : ℤ)))
    (hV : ∀ σ : Site 2,
      c ≤ μ.real (translatedVerticalCrossingEvent σ (n : ℤ) (W : ℤ))) :
    ∀ k : ℕ, 1 ≤ k →
      c ^ (2 * k - 1) ≤ μ.real (horizontalCrossingEvent
        (τ 0) ((n + k * (W - n) : ℕ) + τ 0) (τ 1) ((n : ℤ) + τ 1)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      simpa [bat_translatedHorizontal_eq_physical, Nat.add_sub_of_le hW.le]
        using hH τ
  | succ k hk ih =>
      let L : ℤ := (n + k * (W - n) : ℕ)
      let s : ℤ := (W - n : ℕ)
      let σR : Site 2 := ![τ 0 + L - n, τ 1]
      let σB : Site 2 := ![τ 0 + L - n, τ 1]
      have hnW : (n : ℤ) < W := by exact_mod_cast hW
      have hnpos : (0 : ℤ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hspos : (0 : ℤ) < s := by
        dsimp [s]; exact_mod_cast Nat.sub_pos_of_lt hW
      have hLn : (n : ℤ) < L := by
        dsimp [L]
        push_cast
        rw [Nat.cast_sub hW.le]
        have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
        nlinarith
      have hband : c ≤ μ.real (verticalCrossingEvent
          (τ 0 + L - n) (τ 0 + L) (τ 1) ((n : ℤ) + τ 1)) := by
        have hv := hV σB
        rw [bat_translatedVertical_eq_physical] at hv
        have hm := measureReal_mono (μ := μ)
          (bat_vertical_physical_mono (τ := σB) (w := (n : ℤ))
            (h := (n : ℤ)) (h' := (W : ℤ)) hnpos hnW.le)
        have hsquare : c ≤ μ.real (verticalCrossingEvent
            (σB 0) ((n : ℤ) + σB 0) (σB 1) ((n : ℤ) + σB 1)) := hv.trans hm
        convert hsquare using 1 <;> simp [σB] <;> ring
      have hright : c ≤ μ.real (horizontalCrossingEvent
          (τ 0 + L - n) (τ 0 + L + s) (τ 1) ((n : ℤ) + τ 1)) := by
        have hr := hH σR
        rw [bat_translatedHorizontal_eq_physical] at hr
        convert hr using 1 <;> simp [σR, s, Nat.cast_sub hW.le] <;> ring
      have hglue := jec_rsw_strip_glue μ hpa
        (a := τ 0) (m := τ 0 + L - n) (m' := τ 0 + L)
        (b := τ 0 + L + s) (c := τ 1) (d := (n : ℤ) + τ 1)
        (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      have hleft : c ^ (2 * k - 1) ≤
          μ.real (horizontalCrossingEvent (τ 0) (τ 0 + L)
            (τ 1) ((n : ℤ) + τ 1)) := by
        simpa [L, add_comm] using ih
      have hprod : c ^ (2 * (k + 1) - 1) ≤
          μ.real (horizontalCrossingEvent (τ 0) (τ 0 + L) (τ 1) ((n : ℤ) + τ 1))
            * μ.real (verticalCrossingEvent (τ 0 + L - n) (τ 0 + L)
                (τ 1) ((n : ℤ) + τ 1))
            * μ.real (horizontalCrossingEvent (τ 0 + L - n) (τ 0 + L + s)
                (τ 1) ((n : ℤ) + τ 1)) := by
        have hexp : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
        rw [hexp, pow_add, pow_two]
        calc
          c ^ (2 * k - 1) * (c * c)
              ≤ μ.real (horizontalCrossingEvent (τ 0) (τ 0 + L)
                    (τ 1) ((n : ℤ) + τ 1)) * (c * c) := by
                gcongr
          _ ≤ μ.real (horizontalCrossingEvent (τ 0) (τ 0 + L)
                    (τ 1) ((n : ℤ) + τ 1)) *
                  (μ.real (verticalCrossingEvent (τ 0 + L - n) (τ 0 + L)
                    (τ 1) ((n : ℤ) + τ 1)) * c) := by
                gcongr
          _ ≤ μ.real (horizontalCrossingEvent (τ 0) (τ 0 + L)
                    (τ 1) ((n : ℤ) + τ 1)) *
                  (μ.real (verticalCrossingEvent (τ 0 + L - n) (τ 0 + L)
                    (τ 1) ((n : ℤ) + τ 1)) *
                    μ.real (horizontalCrossingEvent (τ 0 + L - n) (τ 0 + L + s)
                      (τ 1) ((n : ℤ) + τ 1))) := by
                gcongr
          _ = _ := by ring
      calc
        c ^ (2 * (k + 1) - 1) ≤ _ := hprod
        _ ≤ μ.real (horizontalCrossingEvent (τ 0) (τ 0 + L + s)
              (τ 1) ((n : ℤ) + τ 1)) := hglue
        _ = μ.real (horizontalCrossingEvent (τ 0)
              ((n + (k + 1) * (W - n) : ℕ) + τ 0)
              (τ 1) ((n : ℤ) + τ 1)) := by
                congr 2
                dsimp [L, s]
                push_cast
                rw [Nat.cast_sub hW.le]
                ring

theorem bat_vertical_chain
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (c : ℝ) (hc : 0 ≤ c)
    (n W : ℕ) (hn : 1 ≤ n) (hW : n < W) (τ : Site 2)
    (hH : ∀ σ : Site 2,
      c ≤ μ.real (translatedHorizontalCrossingEvent σ (W : ℤ) (n : ℤ)))
    (hV : ∀ σ : Site 2,
      c ≤ μ.real (translatedVerticalCrossingEvent σ (n : ℤ) (W : ℤ))) :
    ∀ k : ℕ, 1 ≤ k →
      c ^ (2 * k - 1) ≤ μ.real (verticalCrossingEvent
        (τ 0) ((n : ℤ) + τ 0) (τ 1)
        ((n + k * (W - n) : ℕ) + τ 1)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      simpa [bat_translatedVertical_eq_physical, Nat.add_sub_of_le hW.le]
        using hV τ
  | succ k hk ih =>
      let L : ℤ := (n + k * (W - n) : ℕ)
      let s : ℤ := (W - n : ℕ)
      let σT : Site 2 := ![τ 0, τ 1 + L - n]
      let σB : Site 2 := ![τ 0, τ 1 + L - n]
      have hnW : (n : ℤ) < W := by exact_mod_cast hW
      have hnpos : (0 : ℤ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hspos : (0 : ℤ) < s := by
        dsimp [s]; exact_mod_cast Nat.sub_pos_of_lt hW
      have hLn : (n : ℤ) < L := by
        dsimp [L]
        push_cast
        rw [Nat.cast_sub hW.le]
        have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
        nlinarith
      have hband : c ≤ μ.real (horizontalCrossingEvent
          (τ 0) ((n : ℤ) + τ 0) (τ 1 + L - n) (τ 1 + L)) := by
        have hh := hH σB
        rw [bat_translatedHorizontal_eq_physical] at hh
        have hm := measureReal_mono (μ := μ)
          (bat_horizontal_physical_mono (τ := σB) (w := (n : ℤ))
            (w' := (W : ℤ)) (h := (n : ℤ)) hnpos hnW.le)
        have hsquare : c ≤ μ.real (horizontalCrossingEvent
            (σB 0) ((n : ℤ) + σB 0) (σB 1) ((n : ℤ) + σB 1)) := hh.trans hm
        convert hsquare using 1 <;> simp [σB] <;> ring
      have htop : c ≤ μ.real (verticalCrossingEvent
          (τ 0) ((n : ℤ) + τ 0) (τ 1 + L - n) (τ 1 + L + s)) := by
        have hr := hV σT
        rw [bat_translatedVertical_eq_physical] at hr
        convert hr using 1 <;> simp [σT, s, Nat.cast_sub hW.le] <;> ring
      have hglue := bat_vertical_strip_glue μ hpa
        (a := τ 0) (b := (n : ℤ) + τ 0)
        (c := τ 1) (m := τ 1 + L - n) (m' := τ 1 + L)
        (d := τ 1 + L + s)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hbottom : c ^ (2 * k - 1) ≤
          μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
            (τ 1) (τ 1 + L)) := by
        simpa [L, add_comm] using ih
      have hprod : c ^ (2 * (k + 1) - 1) ≤
          μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
              (τ 1) (τ 1 + L))
            * μ.real (horizontalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                (τ 1 + L - n) (τ 1 + L))
            * μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                (τ 1 + L - n) (τ 1 + L + s)) := by
        have hexp : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
        rw [hexp, pow_add, pow_two]
        calc
          c ^ (2 * k - 1) * (c * c)
              ≤ μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                    (τ 1) (τ 1 + L)) * (c * c) := by
                gcongr
          _ ≤ μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                    (τ 1) (τ 1 + L)) *
                  (μ.real (horizontalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                    (τ 1 + L - n) (τ 1 + L)) * c) := by
                gcongr
          _ ≤ μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                    (τ 1) (τ 1 + L)) *
                  (μ.real (horizontalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                    (τ 1 + L - n) (τ 1 + L)) *
                    μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
                      (τ 1 + L - n) (τ 1 + L + s))) := by
                gcongr
          _ = _ := by ring
      calc
        c ^ (2 * (k + 1) - 1) ≤ _ := hprod
        _ ≤ μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
              (τ 1) (τ 1 + L + s)) := hglue
        _ = μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0)
              (τ 1) ((n + (k + 1) * (W - n) : ℕ) + τ 1)) := by
                congr 2
                dsimp [L, s]
                push_cast
                rw [Nat.cast_sub hW.le]
                ring




theorem boxCrossingProperty_aspect_independent
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {ρ : ℝ} (hρBXP : BoxCrossingProperty μ ρ) :
    ∀ ρ' : ℝ, 1 < ρ' → BoxCrossingProperty μ ρ' := by
  rintro ρ' hρ'
  rcases hρBXP with ⟨hρ, n0, hcpos⟩
  let δ : ℝ := (ρ - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨Nδ, hNδ⟩ := exists_nat_ge (1 / δ)
  let n1 : ℕ := max 1 (max n0 Nδ)
  have hn1 : 1 ≤ n1 := Nat.le_max_left _ _
  have hn01 : n0 ≤ n1 := le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hNδ1 : Nδ ≤ n1 := le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨k0, hk0⟩ := exists_nat_ge ((ρ' - 1) / δ)
  let k : ℕ := max 1 k0
  have hk : 1 ≤ k := Nat.le_max_left _ _
  have hk0k : k0 ≤ k := Nat.le_max_right _ _
  have hkratio : (ρ' - 1) / δ ≤ (k : ℝ) :=
    hk0.trans (by exact_mod_cast hk0k)
  have hkδ : ρ' - 1 ≤ (k : ℝ) * δ := by
    have := mul_le_mul_of_nonneg_right hkratio hδ.le
    field_simp [hδ.ne'] at this
    simpa [mul_comm] using this
  let c := boxCrossingInf μ ρ n0
  have hc : 0 < c := hcpos
  have hcpow : 0 < c ^ (2 * k - 1) := pow_pos hc _
  refine rba_bxp_of_uniform_seed μ ρ' hρ' n1 (c ^ (2 * k - 1)) hcpow ?_ ?_
  · intro n τ hn
    have hn0 : n0 ≤ n := hn01.trans hn
    have hnNat : 1 ≤ n := hn1.trans hn
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
    have hNδn : (Nδ : ℝ) ≤ n := by exact_mod_cast hNδ1.trans hn
    have hδn : 1 ≤ δ * (n : ℝ) := by
      have hdiv : 1 / δ ≤ (n : ℝ) := hNδ.trans hNδn
      have := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ δ from hδ.le)
      field_simp [hδ.ne'] at this
      simpa [mul_comm] using this
    let W : ℕ := ⌊ρ * (n : ℝ)⌋.toNat
    have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
    have hfloor0 : (0 : ℤ) ≤ ⌊ρ * (n : ℝ)⌋ := by
      rw [Int.le_floor]
      norm_num
      exact mul_nonneg hρpos.le (Nat.cast_nonneg n)
    have hWcast : (W : ℤ) = ⌊ρ * (n : ℝ)⌋ := by
      simp [W, Int.toNat_of_nonneg hfloor0]
    have hWlargeReal : (n : ℝ) + δ * n < (W : ℝ) := by
      have hlt := Int.lt_floor_add_one (ρ * (n : ℝ))
      rw [← hWcast] at hlt
      push_cast at hlt
      dsimp [δ] at hδn ⊢
      nlinarith [hδn]
    have hW : n < W := by
      exact_mod_cast lt_of_le_of_lt (by nlinarith [hδn] :
        (n : ℝ) ≤ (n : ℝ) + δ * n) hWlargeReal
    have hstep : δ * (n : ℝ) ≤ ((W - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hW.le]
      linarith
    have hsourceH : ∀ σ : Site 2,
        c ≤ μ.real (translatedHorizontalCrossingEvent σ (W : ℤ) (n : ℤ)) := by
      intro σ
      rw [hWcast]
      exact bat_horizontal_lower_of_bxp σ hn0
    have hsourceV : ∀ σ : Site 2,
        c ≤ μ.real (translatedVerticalCrossingEvent σ (n : ℤ) (W : ℤ)) := by
      intro σ
      rw [hWcast]
      exact bat_vertical_lower_of_bxp σ hn0
    have hchain := bat_horizontal_chain μ hpa c hc.le n W hnNat hW τ
      hsourceH hsourceV k hk
    let L : ℕ := n + k * (W - n)
    have htargetReal : ρ' * (n : ℝ) ≤ (L : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg k)
      have hkn : (ρ' - 1) * (n : ℝ) ≤ (k : ℝ) * (δ * n) := by
        have := mul_le_mul_of_nonneg_right hkδ (Nat.cast_nonneg n)
        nlinarith
      dsimp [L]
      push_cast
      nlinarith
    have htarget : ⌊ρ' * (n : ℝ)⌋ ≤ (L : ℤ) := by
      calc
        ⌊ρ' * (n : ℝ)⌋ ≤ ⌊(L : ℝ)⌋ := Int.floor_le_floor htargetReal
        _ = (L : ℤ) := Int.floor_natCast L
    have htargetPos : (0 : ℤ) < ⌊ρ' * (n : ℝ)⌋ :=
      bxa_zero_lt_floor hρ' hnNat
    have hmono := measureReal_mono (μ := μ)
      (bat_horizontal_physical_mono (τ := τ) (w := ⌊ρ' * (n : ℝ)⌋)
        (w' := (L : ℤ)) (h := (n : ℤ)) htargetPos htarget)
    have hfinal := hchain.trans hmono
    rw [bat_translatedHorizontal_eq_physical]
    simpa [L, add_comm] using hfinal
  · intro n τ hn
    have hn0 : n0 ≤ n := hn01.trans hn
    have hnNat : 1 ≤ n := hn1.trans hn
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
    have hNδn : (Nδ : ℝ) ≤ n := by exact_mod_cast hNδ1.trans hn
    have hδn : 1 ≤ δ * (n : ℝ) := by
      have hdiv : 1 / δ ≤ (n : ℝ) := hNδ.trans hNδn
      have := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ δ from hδ.le)
      field_simp [hδ.ne'] at this
      simpa [mul_comm] using this
    let W : ℕ := ⌊ρ * (n : ℝ)⌋.toNat
    have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
    have hfloor0 : (0 : ℤ) ≤ ⌊ρ * (n : ℝ)⌋ := by
      rw [Int.le_floor]
      norm_num
      exact mul_nonneg hρpos.le (Nat.cast_nonneg n)
    have hWcast : (W : ℤ) = ⌊ρ * (n : ℝ)⌋ := by
      simp [W, Int.toNat_of_nonneg hfloor0]
    have hWlargeReal : (n : ℝ) + δ * n < (W : ℝ) := by
      have hlt := Int.lt_floor_add_one (ρ * (n : ℝ))
      rw [← hWcast] at hlt
      push_cast at hlt
      dsimp [δ] at hδn ⊢
      nlinarith [hδn]
    have hW : n < W := by
      exact_mod_cast lt_of_le_of_lt (by nlinarith [hδn] :
        (n : ℝ) ≤ (n : ℝ) + δ * n) hWlargeReal
    have hstep : δ * (n : ℝ) ≤ ((W - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hW.le]
      linarith
    have hsourceH : ∀ σ : Site 2,
        c ≤ μ.real (translatedHorizontalCrossingEvent σ (W : ℤ) (n : ℤ)) := by
      intro σ
      rw [hWcast]
      exact bat_horizontal_lower_of_bxp σ hn0
    have hsourceV : ∀ σ : Site 2,
        c ≤ μ.real (translatedVerticalCrossingEvent σ (n : ℤ) (W : ℤ)) := by
      intro σ
      rw [hWcast]
      exact bat_vertical_lower_of_bxp σ hn0
    have hchain := bat_vertical_chain μ hpa c hc.le n W hnNat hW τ
      hsourceH hsourceV k hk
    let L : ℕ := n + k * (W - n)
    have htargetReal : ρ' * (n : ℝ) ≤ (L : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg k)
      have hkn : (ρ' - 1) * (n : ℝ) ≤ (k : ℝ) * (δ * n) := by
        have := mul_le_mul_of_nonneg_right hkδ (Nat.cast_nonneg n)
        nlinarith
      dsimp [L]
      push_cast
      nlinarith
    have htarget : ⌊ρ' * (n : ℝ)⌋ ≤ (L : ℤ) := by
      calc
        ⌊ρ' * (n : ℝ)⌋ ≤ ⌊(L : ℝ)⌋ := Int.floor_le_floor htargetReal
        _ = (L : ℤ) := Int.floor_natCast L
    have htargetPos : (0 : ℤ) < ⌊ρ' * (n : ℝ)⌋ :=
      bxa_zero_lt_floor hρ' hnNat
    have hmono := measureReal_mono (μ := μ)
      (bat_vertical_physical_mono (τ := τ) (w := (n : ℤ))
        (h := ⌊ρ' * (n : ℝ)⌋) (h' := (L : ℤ)) htargetPos htarget)
    have hfinal := hchain.trans hmono
    rw [bat_translatedVertical_eq_physical]
    simpa [L, add_comm] using hfinal

end Universality
end StatMech
