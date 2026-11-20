/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.BackboneSupportLexK4Realization

open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000

namespace StatMech.Sharpness

private noncomputable def shbCurrentTerm (x : ℝ) (k : ℕ) : ℝ :=
  x ^ k / k.factorial

private theorem shb_summable_currentTerm (x : ℝ) :
    Summable (shbCurrentTerm x) := by
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) x
  exact h.congr (fun k => by simp [shbCurrentTerm, div_eq_inv_mul, mul_comm])

private theorem shb_summable_currentTerm_filter (x : ℝ) (Q : ℕ → Prop)
    [DecidablePred Q] :
    Summable (fun k => if Q k then shbCurrentTerm x k else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (shb_summable_currentTerm x).norm
  split <;> simp

private theorem shb_tsum_even_filter (x : ℝ) :
    (∑' k : ℕ, if Even k then shbCurrentTerm x k else 0) =
      shbEvenCurrentSeries x := by
  unfold shbEvenCurrentSeries
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun k : ↑(Function.support (fun n : ℕ =>
      shbCurrentTerm x (2 * n))) => 2 * k.1)
  · intro a b hab
    apply Subtype.ext
    dsimp at hab ⊢
    omega
  · intro k hk
    simp only [Function.mem_support] at hk
    have he : Even k := by
      by_contra hne
      rw [if_neg hne] at hk
      exact hk rfl
    obtain ⟨n, rfl⟩ := he
    have hterm : shbCurrentTerm x (n + n) ≠ 0 := by simpa using hk
    exact ⟨⟨n, by simpa [two_mul] using hterm⟩, by simp [two_mul]⟩
  · intro k
    simp [shbCurrentTerm]

private theorem shb_tsum_odd_filter (x : ℝ) :
    (∑' k : ℕ, if Odd k then shbCurrentTerm x k else 0) =
      shbOddCurrentSeries x := by
  unfold shbOddCurrentSeries
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun k : ↑(Function.support (fun n : ℕ =>
      shbCurrentTerm x (2 * n + 1))) => 2 * k.1 + 1)
  · intro a b hab
    apply Subtype.ext
    dsimp at hab ⊢
    omega
  · intro k hk
    simp only [Function.mem_support] at hk
    have ho : Odd k := by
      by_contra hne
      rw [if_neg hne] at hk
      exact hk rfl
    obtain ⟨n, hn⟩ := ho
    refine ⟨⟨n, ?_⟩, hn.symm⟩
    simpa [hn] using hk
  · intro k
    simp [shbCurrentTerm]


private def shbParitySupportOn {E : Type*} [DecidableEq E]
    (S : Finset E) (m : ↑S → ℕ) : Finset E :=
  (S.attach.filter fun e => Odd (m e)).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] private theorem shb_mem_paritySupportOn
    {E : Type*} [DecidableEq E] (S : Finset E) (m : ↑S → ℕ)
    (e : ↑S) :
    e.1 ∈ shbParitySupportOn S m ↔ Odd (m e) := by
  simp [shbParitySupportOn]

private theorem shb_paritySupportOn_eq_iff
    {E : Type*} [DecidableEq E] (S A : Finset E) (hAS : A ⊆ S)
    (m : ↑S → ℕ) :
    shbParitySupportOn S m = A ↔
      ∀ e : ↑S, if e.1 ∈ A then Odd (m e) else Even (m e) := by
  constructor
  · intro h e
    by_cases he : e.1 ∈ A
    · simp only [if_pos he]
      rw [← h] at he
      simpa using he
    · simp only [if_neg he]
      rw [← Nat.not_odd_iff_even]
      intro ho
      apply he
      rw [← h]
      simpa using ho
  · intro h
    ext e
    by_cases heS : e ∈ S
    · let es : ↑S := ⟨e, heS⟩
      change (es.1 ∈ shbParitySupportOn S m ↔ e ∈ A)
      rw [shb_mem_paritySupportOn]
      by_cases heA : e ∈ A
      · have ho : Odd (m es) := by simpa [es, heA] using h es
        simp [heA, ho]
      · have hev : Even (m es) := by simpa [es, heA] using h es
        rw [← Nat.not_odd_iff_even] at hev
        simp [heA, hev]
    · have heA : e ∉ A := fun he => heS (hAS he)
      simp [shbParitySupportOn, heS, heA]

private theorem shb_fixedParity_tsum
    {E : Type*} [DecidableEq E] (S A : Finset E) (hAS : A ⊆ S)
    (x : ℝ) (hx : 0 ≤ x) :
    (∑' m : ↑S → ℕ,
      if shbParitySupportOn S m = A then
        ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
      ∏ e ∈ S,
        if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x := by
  let g : E → ℕ → ℝ := fun e k =>
    if (if e ∈ A then Odd k else Even k) then shbCurrentTerm x k else 0
  have hgsum : ∀ e, Summable (g e) := by
    intro e
    unfold g
    exact shb_summable_currentTerm_filter x _
  have hgnn : ∀ e k, 0 ≤ g e k := by
    intro e k
    by_cases h : if e ∈ A then Odd k else Even k
    · simp only [g, h, if_true]
      exact div_nonneg (pow_nonneg hx _) (by positivity)
    · simp [g, h]
  calc
    (∑' m : ↑S → ℕ,
        if shbParitySupportOn S m = A then
          ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
        ∑' m : ↑S → ℕ, ∏ e : ↑S, g e.1 (m e) := by
      apply tsum_congr
      intro m
      by_cases hs : shbParitySupportOn S m = A
      · rw [if_pos hs]
        have hall := (shb_paritySupportOn_eq_iff S A hAS m).mp hs
        apply Finset.prod_congr rfl
        intro e _
        simp only [g]
        rw [if_pos (hall e)]
      · rw [if_neg hs]
        have hall : ¬ ∀ e : ↑S,
            if e.1 ∈ A then Odd (m e) else Even (m e) :=
          fun h => hs ((shb_paritySupportOn_eq_iff S A hAS m).mpr h)
        push Not at hall
        obtain ⟨e, he⟩ := hall
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        simp only [g]
        rw [if_neg he]
    _ = ∏ e ∈ S, ∑' k : ℕ, g e k :=
      (prod_tsum_fubini g hgsum hgnn S).2.symm
    _ = ∏ e ∈ S,
          if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x := by
      apply Finset.prod_congr rfl
      intro e heS
      by_cases heA : e ∈ A
      · simp only [g, heA, if_true]
        exact shb_tsum_odd_filter x
      · simp only [g, heA, if_false]
        exact shb_tsum_even_filter x



theorem shb_current_tsum_eq_paritySeriesMassOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P]
    (x : ℝ) (hx : 0 ≤ x) :
    (∑' m : ↑S → ℕ,
      if P (shbParitySupportOn S m) then
        ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
      shbParitySeriesMassOn S P x := by
  unfold shbParitySeriesMassOn
  let F : Finset E → (↑S → ℕ) → ℝ := fun A m =>
    if P A then
      if shbParitySupportOn S m = A then
        ∏ e : ↑S, shbCurrentTerm x (m e) else 0
    else 0
  have hFsum : ∀ A ∈ S.powerset, Summable (F A) := by
    intro A hAS
    by_cases hPA : P A
    · simp only [F, hPA, if_true]
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
        (prod_tsum_fubini (fun _ k => shbCurrentTerm x k)
          (fun _ => shb_summable_currentTerm x)
          (fun _ k => div_nonneg (pow_nonneg hx _) (by positivity)) S).1
      · split
        · exact Finset.prod_nonneg (fun _ _ =>
            div_nonneg (pow_nonneg hx _) (by positivity))
        · exact le_rfl
      · split
        · exact le_rfl
        · exact Finset.prod_nonneg (fun _ _ =>
            div_nonneg (pow_nonneg hx _) (by positivity))
    · simp [F, hPA]
  calc
    (∑' m : ↑S → ℕ,
        if P (shbParitySupportOn S m) then
          ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
        ∑' m : ↑S → ℕ, ∑ A ∈ S.powerset, F A m := by
      apply tsum_congr
      intro m
      let A := shbParitySupportOn S m
      rw [Finset.sum_eq_single A]
      · simp [F, A]
      · intro B hB hBA
        by_cases hPB : P B
        · simp only [F, hPB, if_true]
          rw [if_neg]
          intro heq
          exact hBA heq.symm
        · simp [F, hPB]
      · intro hA
        exact absurd (Finset.mem_powerset.mpr (by
          intro e he
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
          exact a.2)) hA
    _ = ∑ A ∈ S.powerset, ∑' m : ↑S → ℕ, F A m :=
      Summable.tsum_finsetSum hFsum
    _ = ∑ A ∈ S.powerset,
          if P A then
            ∏ e ∈ S,
              if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
          else 0 := by
      apply Finset.sum_congr rfl
      intro A hAS
      by_cases hPA : P A
      · simp only [F, hPA, if_true]
        exact shb_fixedParity_tsum S A (Finset.mem_powerset.mp hAS) x hx
      · simp [F, hPA]





private noncomputable def shbK4CurrentEquiv (E : Finset shbK4Edge) :
    (↑E → ℕ) ≃ ((shbK4Graph E).edgeFinset → ℕ) :=
  Equiv.arrowCongr (shbK4GraphEdgeEquiv E) (Equiv.refl ℕ)

private theorem shbK4CurrentEquiv_apply
    (E : Finset shbK4Edge) (m : ↑E → ℕ) (k : ↑E) :
    shbK4CurrentEquiv E m (shbK4GraphEdgeEquiv E k) = m k := by
  simp [shbK4CurrentEquiv]

private theorem shbK4_oddSupport_reindex
    (E : Finset shbK4Edge) (m : ↑E → ℕ) :
    shbK4OddSupport E
        (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) =
      shbParitySupportOn E m := by
  ext k
  by_cases hk : k ∈ E
  · let ks : ↑E := ⟨k, hk⟩
    rw [shbK4Edge_mem_oddSupport]
    simp only [hk, true_and]
    have hsupport := shb_mem_paritySupportOn E m ks
    change (k ∈ shbParitySupportOn E m ↔ Odd (m ks)) at hsupport
    rw [hsupport]
    have hcode : (shbK4GraphEdgeEquiv E ks).1 = k.code := rfl
    rw [← hcode]
    unfold ofEdgeFun
    rw [dif_pos (shbK4GraphEdgeEquiv E ks).2,
      shbK4CurrentEquiv_apply]
  · simp [shbK4OddSupport, shbParitySupportOn, hk]

private theorem shbK4_weight_reindex
    (E : Finset shbK4Edge) (x : ℝ) (m : ↑E → ℕ) :
    weight (shbK4Graph E) x (fun _ ↦ 1)
        (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) =
      ∏ k : ↑E, shbCurrentTerm x (m k) := by
  rw [shbK4_weight_ofEdgeFun_one]
  apply Finset.prod_congr rfl
  intro k _
  rw [shbK4CurrentEquiv_apply]
  rfl



theorem shbK4_backboneNumSupport_eq_seriesMass
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (x : ℝ) (hx : 0 ≤ x) :
    shb_backboneNumSupport (shbK4Graph E) x (fun _ ↦ 1) 0 3
        (shbK4DirectPath E h03) =
      shbK4DirectFiberSeriesMass E x := by
  unfold shb_backboneNumSupport shbK4DirectFiberSeriesMass
  rw [← (shbK4CurrentEquiv E).tsum_eq]
  calc
    (∑' m : ↑E → ℕ,
      if sources (shbK4Graph E)
            (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) = {0, 3} ∧
          shb_backboneSelectSupport (shbK4Graph E)
              (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) 0 3 =
            some (shbK4DirectPath E h03) then
        weight (shbK4Graph E) x (fun _ ↦ 1)
          (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) else 0) =
      ∑' m : ↑E → ℕ,
        if shbK4SelectsDirect03 (shbParitySupportOn E m) then
          ∏ k : ↑E, shbCurrentTerm x (m k) else 0 := by
      apply tsum_congr
      intro m
      have hfiber :
          (sources (shbK4Graph E)
                (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) = {0, 3} ∧
            shb_backboneSelectSupport (shbK4Graph E)
                (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) 0 3 =
              some (shbK4DirectPath E h03)) ↔
            shbK4SelectsDirect03 (shbParitySupportOn E m) := by
        rw [shbK4_source_selector_fiber_iff, shbK4_oddSupport_reindex]
      by_cases hsel : shbK4SelectsDirect03 (shbParitySupportOn E m)
      · rw [if_pos (hfiber.mpr hsel), if_pos hsel, shbK4_weight_reindex]
      · rw [if_neg (fun h => hsel (hfiber.mp h)), if_neg hsel]
    _ = shbParitySeriesMassOn E shbK4SelectsDirect03 x :=
      shb_current_tsum_eq_paritySeriesMassOn E shbK4SelectsDirect03 x hx



theorem shbK4_currentSum_empty_eq_seriesMass
    (E : Finset shbK4Edge) (x : ℝ) (hx : 0 ≤ x) :
    currentSum (shbK4Graph E) x (fun _ ↦ 1) ∅ =
      shbK4VacuumSeriesMass E x := by
  unfold currentSum shbK4VacuumSeriesMass
  rw [← (shbK4CurrentEquiv E).tsum_eq]
  calc
    (∑' m : ↑E → ℕ,
      if sources (shbK4Graph E)
          (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) = ∅ then
        weight (shbK4Graph E) x (fun _ ↦ 1)
          (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) else 0) =
      ∑' m : ↑E → ℕ,
        if shbK4Boundary (shbParitySupportOn E m) = ∅ then
          ∏ k : ↑E, shbCurrentTerm x (m k) else 0 := by
      apply tsum_congr
      intro m
      rw [shbK4_sources_eq_boundary, shbK4_oddSupport_reindex,
        shbK4_weight_reindex]
    _ = shbParitySeriesMassOn E (fun A ↦ shbK4Boundary A = ∅) x :=
      shb_current_tsum_eq_paritySeriesMassOn E
        (fun A ↦ shbK4Boundary A = ∅) x hx



theorem shbK4_rhoSupport_eq_directRhoSeries
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (x : ℝ) (hx : 0 ≤ x) :
    shb_rhoSupport (shbK4Graph E) x (fun _ ↦ 1) 0 3
        (shbK4DirectPath E h03) =
      shbK4DirectRhoSeries E x := by
  unfold shb_rhoSupport shbK4DirectRhoSeries
  rw [shbK4_backboneNumSupport_eq_seriesMass E h03 x hx,
    shbK4_currentSum_empty_eq_seriesMass E x hx]




theorem shb_supportLex_literal_P3_counterexample :
    shb_rhoSupport (shbK4Graph shbK4H) (Real.artanh (2 / 3))
        (fun _ ↦ 1) 0 3 (shbK4DirectPath shbK4H (by decide)) <
      shb_rhoSupport (shbK4Graph shbK4G) (Real.artanh (2 / 3))
        (fun _ ↦ 1) 0 3
        (shb_pathMapLe (shbK4Graph_mono shbK4H_subset_shbK4G)
          (shbK4DirectPath shbK4H (by decide))) := by
  have hx : 0 ≤ Real.artanh (2 / 3) :=
    Real.artanh_nonneg (by norm_num)
  rw [shbK4DirectPath_mapLe,
    shbK4_rhoSupport_eq_directRhoSeries shbK4H (by decide) _ hx,
    shbK4_rhoSupport_eq_directRhoSeries shbK4G (by decide) _ hx]
  exact shb_supportLex_series_P3_counterexample

end StatMech.Sharpness
