/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.RevealedPreference.AfriatCertificate
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Revealed preference: GARP yields Afriat's inequalities

Finitely many demand observations satisfying GARP admit numbers `Uⁱ` and `λⁱ > 0` solving
Afriat's inequalities `Uⁱ ≤ Uʲ + λʲ pʲ·(xⁱ - xʲ)`. This is direction (2) ⇒ (3) of Afriat's
theorem; with `DemandData.garp_of_rationalizes` and
`DemandData.IsAfriatCertificate.afriatUtility_spec` it closes the cycle (1) ⇒ (2) ⇒ (3) ⇒ (4)
for strictly positive prices and nonempty sets of observations and goods. No sign condition on
prices is needed for this direction.

## Main results

* `DemandData.exists_isAfriatCertificate_of_garp`: Afriat's theorem, (2) ⇒ (3).

## References

* H. R. Varian, "The Nonparametric Approach to Demand Analysis", Econometrica 50 (1982),
  945-973: Afriat's theorem p. 946; Algorithm 3 and the proof of (2) ⇒ (3) in Appendix I.
* S. N. Afriat, "The Construction of Utility Functions from Expenditure Data", International
  Economic Review 8 (1967), 67-77.
-/

namespace MathlibExt.Economics.RevealedPreference

-- The statement keeps the contract's `[Fintype ι]`; `[Finite ι]` would suffice.
set_option linter.unusedFintypeInType false in
/-- Afriat's theorem, (2) ⇒ (3): finitely many observations satisfying GARP admit numbers `Uⁱ`
and `λⁱ > 0` solving Afriat's inequalities. No sign condition on prices is needed. -/
theorem DemandData.exists_isAfriatCertificate_of_garp {ι G : Type*} [Fintype ι] [Fintype G]
    {D : DemandData ι G} (h : D.GARP) : ∃ U lam : ι → ℝ, D.IsAfriatCertificate U lam := by
  classical
  have hR0_refl : ∀ i, D.DirectlyRevealedPreferred i i := fun i => le_refl _
  have hR_refl : ∀ i, D.RevealedPreferred i i :=
    fun i => Relation.TransGen.single (hR0_refl i)
  have hR_trans : ∀ {a b c : ι}, D.RevealedPreferred a b → D.RevealedPreferred b c →
      D.RevealedPreferred a c :=
    fun hab hbc => Relation.TransGen.trans hab hbc
  suffices hmain : ∀ (n : ℕ) (s : Finset ι), s.card ≤ n → ∃ U lam : ι → ℝ,
      (∀ i ∈ s, 0 < lam i) ∧
        ∀ i ∈ s, ∀ j ∈ s,
          U i ≤ U j + lam j * (D.price j ⬝ᵥ (D.bundle i - D.bundle j)) by
    obtain ⟨U, lam, hpos, hineq⟩ := hmain Finset.univ.card Finset.univ le_rfl
    exact ⟨U, lam, fun i => hpos i (Finset.mem_univ i),
      fun i j => hineq i (Finset.mem_univ i) j (Finset.mem_univ j)⟩
  intro n
  induction n with
  | zero =>
    intro s hs
    have hcard : s.card = 0 := Nat.le_zero.mp hs
    have hs_empty : s = ∅ := Finset.card_eq_zero.mp hcard
    refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
    · intro i hi
      rw [hs_empty] at hi
      exact absurd hi (Finset.notMem_empty i)
    · intro i hi
      rw [hs_empty] at hi
      exact absurd hi (Finset.notMem_empty i)
  | succ n ih =>
    intro s hs
    by_cases hs_nonempty : s.Nonempty
    · -- Maximal element via Mathlib's Finset.exists_maximalFor (Round 2 requirement).
      let : LE ι := ⟨D.RevealedPreferred⟩
      have : IsTrans ι (· ≤ ·) :=
        ⟨fun _ _ _ hab hbc => Relation.TransGen.trans hab hbc⟩
      obtain ⟨m, hm_mem, hm_max⟩ :=
        Finset.exists_maximalFor (id : ι → ι) s hs_nonempty
      -- E = R-successors of m within s; B = rest.
      let E : Finset ι := s.filter (fun i => D.RevealedPreferred m i)
      let B : Finset ι := s \ E
      have hmE : m ∈ E := Finset.mem_filter.mpr ⟨hm_mem, hR_refl m⟩
      have hE_sub : E ⊆ s := Finset.filter_subset _ _
      have hE_nonempty : E.Nonempty := ⟨m, hmE⟩
      have hEquiv : ∀ i ∈ E, D.RevealedPreferred i m := by
        intro i hi
        exact hm_max (hE_sub hi) (Finset.mem_filter.mp hi).2
      have hClosed : ∀ i ∈ E, ∀ j ∈ s, D.RevealedPreferred i j → j ∈ E := by
        intro i hi j hj hij
        exact Finset.mem_filter.mpr ⟨hj, hR_trans (Finset.mem_filter.mp hi).2 hij⟩
      have hB_ssub : B ⊂ s := Finset.sdiff_ssubset hE_sub hE_nonempty
      have hB_card : B.card < s.card := Finset.card_lt_card hB_ssub
      have hB_le : B.card ≤ n := by omega
      obtain ⟨U0, lam0, hpos0, hineq0⟩ := ih B hB_le
      -- Positivity of A i j for i ∈ E, j ∈ B.
      have hPos : ∀ i ∈ E, ∀ j ∈ B,
          0 < D.price i ⬝ᵥ (D.bundle j - D.bundle i) := by
        intro i hi j hj
        have hj_s : j ∈ s := (Finset.mem_sdiff.mp hj).1
        have hj_notE : j ∉ E := (Finset.mem_sdiff.mp hj).2
        have h_not_R0 : ¬ D.DirectlyRevealedPreferred i j := by
          intro hR0
          exact hj_notE (hClosed i hi j hj_s (Relation.TransGen.single hR0))
        have hlt : D.price i ⬝ᵥ D.bundle i < D.price i ⬝ᵥ D.bundle j :=
          lt_of_not_ge h_not_R0
        have h_eq : D.price i ⬝ᵥ (D.bundle j - D.bundle i)
            = D.price i ⬝ᵥ D.bundle j - D.price i ⬝ᵥ D.bundle i :=
          dotProduct_sub _ _ _
        rw [h_eq]
        linarith
      -- Nonnegativity of A j i for i, j ∈ E (via GARP).
      have hNonneg : ∀ i ∈ E, ∀ j ∈ E,
          0 ≤ D.price j ⬝ᵥ (D.bundle i - D.bundle j) := by
        intro i hi j hj
        have hRij : D.RevealedPreferred i j :=
          hR_trans (hEquiv i hi) (Finset.mem_filter.mp hj).2
        have h_not_P0 : ¬ D.StrictlyDirectlyRevealedPreferred j i := h i j hRij
        have hle : D.price j ⬝ᵥ D.bundle j ≤ D.price j ⬝ᵥ D.bundle i :=
          le_of_not_gt h_not_P0
        have h_eq : D.price j ⬝ᵥ (D.bundle i - D.bundle j)
            = D.price j ⬝ᵥ D.bundle i - D.price j ⬝ᵥ D.bundle j :=
          dotProduct_sub _ _ _
        rw [h_eq]
        linarith
      by_cases hB_nonempty : B.Nonempty
      · -- B nonempty: define Um via Finset.min', lam_m via Finset.max'.
        have hProd_nonempty : (E.product B).Nonempty :=
          Finset.nonempty_product.mpr ⟨hE_nonempty, hB_nonempty⟩
        let S_um : Finset ℝ := (E.product B).image (fun p : ι × ι =>
          min (U0 p.2 + lam0 p.2 * (D.price p.2 ⬝ᵥ (D.bundle p.1 - D.bundle p.2))) (U0 p.2))
        have hS_um_nonempty : S_um.Nonempty :=
          Finset.image_nonempty.mpr hProd_nonempty
        let Um : ℝ := S_um.min' hS_um_nonempty
        have hUm_le : ∀ i ∈ E, ∀ j ∈ B,
            Um ≤ min (U0 j + lam0 j * (D.price j ⬝ᵥ (D.bundle i - D.bundle j))) (U0 j) := by
          intro i hi j hj
          have hmem : (i, j) ∈ E.product B := Finset.mem_product.mpr ⟨hi, hj⟩
          have himg :
              min (U0 j + lam0 j * (D.price j ⬝ᵥ (D.bundle i - D.bundle j))) (U0 j) ∈ S_um := by
            exact Finset.mem_image.mpr ⟨(i, j), hmem, rfl⟩
          exact Finset.min'_le S_um _ himg
        let S_lam : Finset ℝ := (E.product B).image (fun p : ι × ι =>
          max ((U0 p.2 - Um) / (D.price p.1 ⬝ᵥ (D.bundle p.2 - D.bundle p.1))) 1)
        have hS_lam_nonempty : S_lam.Nonempty :=
          Finset.image_nonempty.mpr hProd_nonempty
        let lam_m : ℝ := S_lam.max' hS_lam_nonempty
        have hlam_ge : ∀ i ∈ E, ∀ j ∈ B,
            max ((U0 j - Um) / (D.price i ⬝ᵥ (D.bundle j - D.bundle i))) 1 ≤ lam_m := by
          intro i hi j hj
          have hmem : (i, j) ∈ E.product B := Finset.mem_product.mpr ⟨hi, hj⟩
          have himg : max ((U0 j - Um) / (D.price i ⬝ᵥ (D.bundle j - D.bundle i))) 1 ∈ S_lam := by
            exact Finset.mem_image.mpr ⟨(i, j), hmem, rfl⟩
          exact Finset.le_max' S_lam _ himg
        have hlam_one : (1 : ℝ) ≤ lam_m := by
          obtain ⟨i0, hi0⟩ := hE_nonempty
          obtain ⟨j0, hj0⟩ := hB_nonempty
          have hle := hlam_ge i0 hi0 j0 hj0
          exact le_trans (le_max_right _ _) hle
        have hlam_pos : 0 < lam_m := lt_of_lt_of_le zero_lt_one hlam_one
        let U : ι → ℝ := fun k => if k ∈ E then Um else U0 k
        let lam : ι → ℝ := fun k => if k ∈ E then lam_m else lam0 k
        have hmemB_of : ∀ k ∈ s, k ∉ E → k ∈ B := by
          intro k hk hnot
          exact Finset.mem_sdiff.mpr ⟨hk, hnot⟩
        refine ⟨U, lam, ?_, ?_⟩
        · intro k hk
          by_cases hkE : k ∈ E
          · simp only [lam, hkE, ite_true]
            exact hlam_pos
          · simp only [lam, hkE, ite_false]
            exact hpos0 k (hmemB_of k hk hkE)
        · intro a ha b hb
          by_cases haE : a ∈ E <;> by_cases hbE : b ∈ E
          · -- a, b ∈ E: equal values + GARP nonnegativity.
            have hUi : U a = Um := ite_eq_left haE
            have hUj : U b = Um := ite_eq_left hbE
            have hlamj : lam b = lam_m := ite_eq_left hbE
            rw [hUi, hUj, hlamj]
            have hnn := hNonneg a haE b hbE
            have hmul : 0 ≤ lam_m * (D.price b ⬝ᵥ (D.bundle a - D.bundle b)) :=
              mul_nonneg (le_of_lt hlam_pos) hnn
            linarith
          · -- a ∈ E, b ∈ B: Um definition.
            have hUi : U a = Um := ite_eq_left haE
            have hbB : b ∈ B := hmemB_of b hb hbE
            have hUj : U b = U0 b := ite_eq_right hbE
            have hlamj : lam b = lam0 b := ite_eq_right hbE
            rw [hUi, hUj, hlamj]
            have hle := hUm_le a haE b hbB
            exact le_trans hle (min_le_left _ _)
          · -- a ∈ B, b ∈ E: lam_m definition + positivity.
            have haB : a ∈ B := hmemB_of a ha haE
            have hUa : U a = U0 a := ite_eq_right haE
            have hUb : U b = Um := ite_eq_left hbE
            have hlam : lam b = lam_m := ite_eq_left hbE
            rw [hUa, hUb, hlam]
            have hpos_ab := hPos b hbE a haB
            have hge := hlam_ge b hbE a haB
            have hdiv : (U0 a - Um) / (D.price b ⬝ᵥ (D.bundle a - D.bundle b)) ≤ lam_m :=
              le_trans (le_max_left _ _) hge
            have hmul : U0 a - Um ≤ lam_m * (D.price b ⬝ᵥ (D.bundle a - D.bundle b)) :=
              (div_le_iff₀ hpos_ab).mp hdiv
            linarith
          · -- a, b ∈ B: induction hypothesis.
            have haB : a ∈ B := hmemB_of a ha haE
            have hbB : b ∈ B := hmemB_of b hb hbE
            have hUa : U a = U0 a := ite_eq_right haE
            have hUb : U b = U0 b := ite_eq_right hbE
            have hlam : lam b = lam0 b := ite_eq_right hbE
            rw [hUa, hUb, hlam]
            exact hineq0 a haB b hbB
      · -- B empty: all of s is in E; constant certificate works via GARP.
        have hB_empty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB_nonempty
        have h_all_E : ∀ k ∈ s, k ∈ E := by
          intro k hk
          by_contra hnot
          have hkB : k ∈ B := Finset.mem_sdiff.mpr ⟨hk, hnot⟩
          rw [hB_empty] at hkB
          exact absurd hkB (Finset.notMem_empty k)
        refine ⟨fun _ => 1, fun _ => 1, ?_, ?_⟩
        · intro k hk
          exact zero_lt_one
        · intro a ha b hb
          have hnn := hNonneg a (h_all_E a ha) b (h_all_E b hb)
          simp only
          linarith
    · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs_nonempty
      refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
      · intro i hi
        rw [hs_empty] at hi
        exact absurd hi (Finset.notMem_empty i)
      · intro i hi
        rw [hs_empty] at hi
        exact absurd hi (Finset.notMem_empty i)

end MathlibExt.Economics.RevealedPreference
