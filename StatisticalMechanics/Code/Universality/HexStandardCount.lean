/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Universality.HexLiteralConnEndgame
import Code.Universality.HexInfraHeading

namespace StatMech.Universality

open Filter HexWalk Topology
open scoped Real Topology

noncomputable section




def hexRootedVertices (h : ℤ) (ts : List ℤ) : List ℂ :=
  verticesAux (-halfStep h) h ts

@[simp] theorem hexRootedVertices_head (h : ℤ) (ts : List ℤ) :
    (hexRootedVertices h ts).headI = 0 := by
  cases ts <;> simp [hexRootedVertices, verticesAux]

@[simp] theorem verticesAux_headI (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (verticesAux m h ts).headI = m + halfStep h := by
  cases ts <;> rfl



theorem verticesAux_injective_of_legal :
    ∀ (s : List ℤ) (m : ℂ) (h : ℤ),
      (∀ u ∈ s, u = 1 ∨ u = -1) →
      ∀ t : List ℤ, (∀ u ∈ t, u = 1 ∨ u = -1) →
        verticesAux m h s = verticesAux m h t → s = t := by
  intro s
  induction s with
  | nil =>
      intro m h hs t ht heq
      have hlen := congrArg List.length heq
      have htlen := length_verticesAux m h t
      simp only [verticesAux_nil, List.length_singleton] at hlen
      rw [htlen] at hlen
      have : t.length = 0 := by omega
      exact (List.length_eq_zero_iff.mp this).symm
  | cons u us ih =>
      intro m h hs t ht heq
      cases t with
      | nil =>
          have hlen := congrArg List.length heq
          simp [length_verticesAux] at hlen
      | cons v vs =>
          have hu : u = 1 ∨ u = -1 := hs u (by simp)
          have hv : v = 1 ∨ v = -1 := ht v (by simp)
          have htails :
              verticesAux (m + halfStep h + halfStep (h + u)) (h + u) us =
                verticesAux (m + halfStep h + halfStep (h + v)) (h + v) vs := by
            change
              (m + halfStep h) ::
                  verticesAux (m + halfStep h + halfStep (h + u)) (h + u) us =
                (m + halfStep h) ::
                  verticesAux (m + halfStep h + halfStep (h + v)) (h + v) vs at heq
            exact (List.cons.inj heq).2
          have hheads := congrArg List.headI htails
          simp only [verticesAux_headI] at hheads
          have hstep : halfStep (h + u) = halfStep (h + v) := by
            linear_combination (1 / 2 : ℂ) * hheads
          have hmod : (6 : ℤ) ∣ (h + u - (h + v)) :=
            (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj hstep)
          have huv : u = v := by
            rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
            · rfl
            · rcases hmod with ⟨k, hk⟩
              omega
            · rcases hmod with ⟨k, hk⟩
              omega
            · rfl
          subst v
          have hus : ∀ z ∈ us, z = 1 ∨ z = -1 :=
            fun z hz => hs z (by simp [hz])
          have hvs : ∀ z ∈ vs, z = 1 ∨ z = -1 :=
            fun z hz => ht z (by simp [hz])
          exact congrArg (List.cons u)
            (ih (m + halfStep h + halfStep (h + u)) (h + u)
              hus vs hvs htails)


noncomputable def hexRootedOrientationFinset (h : ℤ) (n : ℕ) :
    Finset (List ℂ) :=
  (hlc_sawFinset (-halfStep h) h n).image (hexRootedVertices h)




noncomputable def hexStandardSAWFinset (n : ℕ) : Finset (List ℂ) :=
  hexRootedOrientationFinset 0 n ∪
    (hexRootedOrientationFinset 2 n ∪ hexRootedOrientationFinset 4 n)


noncomputable def hexStandardSAWCountNat (n : ℕ) : ℕ :=
  (hexStandardSAWFinset n).card


noncomputable def hexStandardSAWCount (n : ℕ) : ℝ :=
  (hexStandardSAWCountNat n : ℝ)

theorem hexRootedOrientation_card (h : ℤ) (n : ℕ) :
    (hexRootedOrientationFinset h n).card = hlc_sawCount (-halfStep h) h n := by
  classical
  calc
    (hexRootedOrientationFinset h n).card =
        (hlc_sawFinset (-halfStep h) h n).card := by
      apply Finset.card_image_iff.mpr
      intro s hs t ht heq
      have hs' := (hlc_mem_sawFinset (-halfStep h) h n s).mp hs
      have ht' := (hlc_mem_sawFinset (-halfStep h) h n t).mp ht
      exact verticesAux_injective_of_legal s (-halfStep h) h
        hs'.1.1 t ht'.1.1 heq
    _ = hlc_sawCount (-halfStep h) h n := hlc_card_sawFinset _ _ _

theorem hexRootedOrientation_card_eq_literal (h : ℤ) (n : ℕ) :
    (hexRootedOrientationFinset h n).card = hlc_sawCount 0 0 n := by
  rw [hexRootedOrientation_card, hlc_sawCount_rebase 0 (-halfStep h) 0 h n]



theorem hlc_sawCount_le_standard (n : ℕ) :
    hlc_sawCount 0 0 n ≤ hexStandardSAWCountNat n := by
  rw [hexStandardSAWCountNat, ← hexRootedOrientation_card_eq_literal 0 n]
  exact Finset.card_le_card (by
    intro s hs
    exact Finset.mem_union_left _ hs)



theorem hexStandardSAWCountNat_le_three_mul (n : ℕ) :
    hexStandardSAWCountNat n ≤ 3 * hlc_sawCount 0 0 n := by
  unfold hexStandardSAWCountNat hexStandardSAWFinset
  have houter := Finset.card_union_le (hexRootedOrientationFinset 0 n)
    (hexRootedOrientationFinset 2 n ∪ hexRootedOrientationFinset 4 n)
  have hinner := Finset.card_union_le (hexRootedOrientationFinset 2 n)
    (hexRootedOrientationFinset 4 n)
  have houter' :
      (hexRootedOrientationFinset 0 n ∪
        (hexRootedOrientationFinset 2 n ∪ hexRootedOrientationFinset 4 n)).card ≤
        hlc_sawCount 0 0 n +
          (hexRootedOrientationFinset 2 n ∪ hexRootedOrientationFinset 4 n).card := by
    simpa only [hexRootedOrientation_card_eq_literal] using houter
  have hinner' :
      (hexRootedOrientationFinset 2 n ∪ hexRootedOrientationFinset 4 n).card ≤
        hlc_sawCount 0 0 n + hlc_sawCount 0 0 n := by
    simpa only [hexRootedOrientation_card_eq_literal] using hinner
  omega

theorem hexLiteralSAWCount_le_standard (n : ℕ) :
    hexLiteralSAWCount n ≤ hexStandardSAWCount n := by
  unfold hexLiteralSAWCount hexStandardSAWCount hexStandardSAWCountNat
    hlc_sawCountR
  exact_mod_cast hlc_sawCount_le_standard n

theorem hexStandardSAWCount_le_three_mul (n : ℕ) :
    hexStandardSAWCount n ≤ 3 * hexLiteralSAWCount n := by
  unfold hexLiteralSAWCount hexStandardSAWCount hexStandardSAWCountNat
    hlc_sawCountR
  exact_mod_cast hexStandardSAWCountNat_le_three_mul n

theorem hexStandardSAWCount_one_le (n : ℕ) :
    1 ≤ hexStandardSAWCount n :=
  le_trans (hexLiteralSAWCount_one_le n) (hexLiteralSAWCount_le_standard n)



theorem hexStandard_connective_of_literal {mu : ℝ}
    (hmu : Tendsto
      (fun n => (hexLiteralSAWCount n) ^ ((n : ℝ)⁻¹))
      atTop (nhds mu)) :
    Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹))
      atTop (nhds mu) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hthree : Tendsto (fun n : ℕ => (3 : ℝ) ^ ((n : ℝ)⁻¹))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.rpow hinv (Or.inl (by norm_num : (3 : ℝ) ≠ 0)))
  have hupp : Tendsto
      (fun n : ℕ => (3 : ℝ) ^ ((n : ℝ)⁻¹) *
        (hexLiteralSAWCount n) ^ ((n : ℝ)⁻¹))
      atTop (nhds mu) := by
    simpa using hthree.mul hmu
  apply Filter.Tendsto.squeeze hmu hupp
  · intro n
    exact Real.rpow_le_rpow
      (le_trans (by norm_num) (hexLiteralSAWCount_one_le n))
      (hexLiteralSAWCount_le_standard n) (inv_nonneg.mpr (Nat.cast_nonneg n))
  · intro n
    calc
      (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹) ≤
          (3 * hexLiteralSAWCount n) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by
          unfold hexStandardSAWCount
          positivity) (hexStandardSAWCount_le_three_mul n)
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ = (3 : ℝ) ^ ((n : ℝ)⁻¹) *
          (hexLiteralSAWCount n) ^ ((n : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by norm_num)
          (le_trans (by norm_num) (hexLiteralSAWCount_one_le n))]



theorem hexStandard_connective_constant_of_series
    (hdiv : ¬ Summable (fun n => hexLiteralSAWCount n * hexChiE ^ n))
    (hconv : ∀ x, 0 ≤ x → x < hexChiE →
      Summable (fun n => hexLiteralSAWCount n * x ^ n)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹))
        atTop (nhds kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  obtain ⟨kappa, hkappa, hlim, hkappa_eq⟩ :=
    hexLiteral_connective_constant_of_series hdiv hconv
  exact ⟨kappa, hkappa, hexStandard_connective_of_literal hlim, hkappa_eq⟩

end

end StatMech.Universality
