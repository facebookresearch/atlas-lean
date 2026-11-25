/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Logic.Function.Basic

/-!
# BGW degree-reduction re-sharing: uniformity of the received-subshare matrix

When every dealer `i` re-shares a value `h i` with fresh independent Shamir
randomness, the coalition `I` receives one Shamir view per dealer. The joint
distribution over dealers of those views is `dealerViews`: the product
distribution, over all dealers, of the per-dealer coalition views.

When `I` is unauthorized (`I.card ≤ params.threshold`), every per-dealer view
is already secret-independent, so the whole received-subshare matrix is
independent of the re-shared values (`dealerViews_eq_of_unauthorized`), hence
of any secret determined by them. The agreement-restricted form
(`dealerViews_eq_of_agree_on`) follows as a corollary.

## Conditioning limitation

This file covers the received-subshare matrix *alone*. Full privacy of BGW
degree reduction would require the joint model of these subshares together
with the original shares already held by the coalition; that joint claim is
not made here.
-/

@[expose] public section

namespace CSLibExt.Crypto.Protocols.BGW

open Cslib.Crypto.Protocols.SecretSharing

/-- Joint subshare matrix over the dealers in `l`, starting from the base
matrix `g`: each dealer `i` in `l` draws an independent view from `view i`
and overwrites row `i`. -/
noncomputable def dealerViewsAux {F Party : Type*} [DecidableEq Party]
    {I : Finset Party} (view : Party → PMF (I → F)) :
    List Party → (Party → I → F) → PMF (Party → I → F)
  | [], g => PMF.pure g
  | i :: rest, g =>
      (view i).bind fun v => dealerViewsAux view rest (Function.update g i v)

/-- The joint distribution of the subshare matrix received by coalition `I`
when every dealer `i` re-shares `h i` with fresh independent randomness. -/
noncomputable def dealerViews {F Party : Type*} [Field F] [Fintype Party]
    [DecidableEq Party] (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params) (I : Finset Party)
    (h : Party → F) : PMF (Party → I → F) :=
  dealerViewsAux (fun i => viewDistOf sampler.gen (Shamir.share params) I (h i))
    Finset.univ.toList (fun _ _ => 0)

/-- Rows outside the dealer list keep their base value. -/
theorem dealerViewsAux_map_eq_pure_of_not_mem {F Party : Type*}
    [DecidableEq Party] {I : Finset Party} (view : Party → PMF (I → F))
    (l : List Party) (g : Party → I → F) (j : Party) :
    j ∉ l → (dealerViewsAux view l g).map (fun g' => g' j) = PMF.pure (g j) := by
  induction l generalizing g with
  | nil => intro _; simp only [dealerViewsAux, PMF.pure_map]
  | cons i rest ih =>
      intro hj
      simp only [List.mem_cons, not_or] at hj
      obtain ⟨hne, hmem⟩ := hj
      simp only [dealerViewsAux, PMF.map_bind]
      have hmap : ∀ v,
          ((dealerViewsAux view rest (Function.update g i v)).map fun g' => g' j) =
            PMF.pure (g j) := by
        intro v
        rw [ih _ hmem, Function.update_of_ne hne]
      simp only [hmap]
      exact PMF.bind_const (view i) (PMF.pure (g j))

/-- The marginal at a listed dealer is that dealer's own view. -/
theorem dealerViewsAux_map_mem {F Party : Type*} [DecidableEq Party]
    {I : Finset Party} (view : Party → PMF (I → F))
    (l : List Party) (g : Party → I → F) (j : Party) :
    l.Nodup → j ∈ l → (dealerViewsAux view l g).map (fun g' => g' j) = view j := by
  induction l generalizing g with
  | nil => intro _ h; simp at h
  | cons i rest ih =>
      intro hnodup hj
      rw [List.nodup_cons] at hnodup
      obtain ⟨hni, hnodup_rest⟩ := hnodup
      simp only [dealerViewsAux, PMF.map_bind]
      rcases List.mem_cons.mp hj with hji | hmem
      · rw [hji]
        have hmap : ∀ v,
            ((dealerViewsAux view rest (Function.update g i v)).map fun g' => g' i) =
              PMF.pure v := by
          intro v
          rw [dealerViewsAux_map_eq_pure_of_not_mem view rest _ i hni,
            Function.update_self]
        simp only [hmap]
        exact PMF.bind_pure (view i)
      · have hmap : ∀ v,
            ((dealerViewsAux view rest (Function.update g i v)).map fun g' => g' j) =
              view j := fun v => ih _ hnodup_rest hmem
        simp only [hmap]
        exact PMF.bind_const (view i) (view j)

/-- The joint law is determined by the per-dealer laws. -/
theorem dealerViewsAux_congr {F Party : Type*} [DecidableEq Party]
    {I : Finset Party} (f₁ f₂ : Party → PMF (I → F))
    (l : List Party) (g : Party → I → F) :
    (∀ i ∈ l, f₁ i = f₂ i) → dealerViewsAux f₁ l g = dealerViewsAux f₂ l g := by
  induction l generalizing g with
  | nil => intro _; simp only [dealerViewsAux]
  | cons i rest ih =>
      intro h
      have hi : f₁ i = f₂ i := h i (List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ k ∈ rest, f₁ k = f₂ k :=
        fun k hk => h k (List.mem_cons.mpr (Or.inr hk))
      simp only [dealerViewsAux]
      rw [hi]
      congr 1
      funext v
      exact ih _ hrest

/-- The `dealerViews` marginal at dealer `i` is dealer `i`'s own view. -/
theorem dealerViews_map_eval {F Party : Type*} [Field F] [Fintype Party]
    [DecidableEq Party] (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params) (I : Finset Party)
    (h : Party → F) (i : Party) :
    (dealerViews params sampler I h).map (fun g => g i) =
      viewDistOf sampler.gen (Shamir.share params) I (h i) := by
  simp only [dealerViews]
  exact dealerViewsAux_map_mem _ _ _ _ (Finset.nodup_toList Finset.univ)
    (Finset.mem_toList.mpr (Finset.mem_univ i))

/-- The joint law is determined by the per-dealer view distributions. -/
theorem dealerViews_eq_of_forall_eq {F Party : Type*} [Field F] [Fintype Party]
    [DecidableEq Party] (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params) (I : Finset Party)
    (h₁ h₂ : Party → F)
    (heq : ∀ i : Party, viewDistOf sampler.gen (Shamir.share params) I (h₁ i) =
      viewDistOf sampler.gen (Shamir.share params) I (h₂ i)) :
    dealerViews params sampler I h₁ = dealerViews params sampler I h₂ := by
  simp only [dealerViews]
  exact dealerViewsAux_congr _ _ _ _ (fun i _ => heq i)

/-- Strong uniformity: for an unauthorized coalition the received-subshare
matrix is independent of the re-shared values, with no agreement hypothesis.
This covers the received matrix alone, not the joint model with the
coalition's original shares. -/
theorem dealerViews_eq_of_unauthorized {F Party : Type*} [Field F]
    [Fintype Party] [DecidableEq Party] (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params) (I : Finset Party)
    (hcard : I.card ≤ params.threshold) (h₁ h₂ : Party → F) :
    dealerViews params sampler I h₁ = dealerViews params sampler I h₂ := by
  have hunauth : ¬ Shamir.authorized params I := by
    simp only [Shamir.authorized]
    intro hle
    exact lt_irrefl _ (lt_of_le_of_lt (le_trans hle hcard) (Nat.lt_succ_self _))
  exact dealerViews_eq_of_forall_eq params sampler I h₁ h₂
    (fun i => Shamir.view_indist_of_tailSampler params sampler I hunauth (h₁ i) (h₂ i))

/-- Agreement-restricted uniformity, from the stronger unauthorized form. -/
theorem dealerViews_eq_of_agree_on {F Party : Type*} [Field F]
    [Fintype Party] [DecidableEq Party] (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params) (I : Finset Party)
    (hcard : I.card ≤ params.threshold) (h₁ h₂ : Party → F)
    (_hagree : ∀ i ∈ I, h₁ i = h₂ i) :
    dealerViews params sampler I h₁ = dealerViews params sampler I h₂ :=
  dealerViews_eq_of_unauthorized params sampler I hcard h₁ h₂

/-- Per-dealer views on the empty coalition agree: there is nothing to see. -/
theorem viewDistOf_empty_eq {F Party : Type*} [Field F] [Fintype Party]
    (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params) (s₀ s₁ : F) :
    viewDistOf sampler.gen (Shamir.share params) ∅ s₀ =
      viewDistOf sampler.gen (Shamir.share params) ∅ s₁ := by
  simp only [viewDistOf]
  congr 1
  funext r
  funext i
  exact absurd i.2 (Finset.notMem_empty i.1)

/-- The empty coalition always sees the same (trivial) joint matrix. -/
theorem dealerViews_empty_eq {F Party : Type*} [Field F] [Fintype Party]
    [DecidableEq Party] (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params) (h₁ h₂ : Party → F) :
    dealerViews params sampler ∅ h₁ = dealerViews params sampler ∅ h₂ := by
  simp only [dealerViews]
  exact dealerViewsAux_congr _ _ _ _
    (fun i _ => viewDistOf_empty_eq params sampler (h₁ i) (h₂ i))

/-- Single-dealer sanity: one row is just one Shamir view. -/
theorem dealerViewsAux_singleton_eq {F Party : Type*} [Field F]
    [Fintype Party] [DecidableEq Party] {I : Finset Party}
    (params : Shamir.Params F Party)
    (sampler : Shamir.TailSampler params)
    (hunauth : ¬ Shamir.authorized params I) (h₁ h₂ : Party → F)
    (i : Party) (g : Party → I → F) :
    dealerViewsAux (fun j => viewDistOf sampler.gen (Shamir.share params) I (h₁ j))
        [i] g =
      dealerViewsAux (fun j => viewDistOf sampler.gen (Shamir.share params) I (h₂ j))
        [i] g := by
  simp only [dealerViewsAux]
  rw [Shamir.view_indist_of_tailSampler params sampler I hunauth (h₁ i) (h₂ i)]

end CSLibExt.Crypto.Protocols.BGW
