/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSet
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Limits between consecutive layers of a self-similar compact set

The block infima of the enumeration of one layer form the enumeration of the
next layer: `isSelfSimilarCompactSet_layer_enum_tendsto` shows that, for a
self-similar compact set, the values of a layer enumeration along a block
$\omega \alpha + n$ tend to the corresponding point of the next layer.
-/

namespace MetaMathlibExt

open Ordinal Filter Topology Set

namespace isSelfSimilarCompactSet_layer_enum_tendsto




/-- A nonempty well-founded subset of the reals has a greatest element. -/
private theorem exists_isMax {X : Set ℝ} (hX : X.WellFoundedOn (· > ·))
    (hne : X.Nonempty) : ∃ m ∈ X, ∀ w ∈ X, w ≤ m := by
  obtain ⟨m, hm⟩ := WellFoundedOn.exists_maximal hX hne
  refine ⟨m, hm.1, fun w hw => ?_⟩
  by_contra hlt
  exact (lt_irrefl m) (lt_of_lt_of_le (not_le.mp hlt) (hm.2 hw (not_le.mp hlt).le))

/-- An accumulation point of a well-founded set is approached from above. -/
private theorem exists_gt_of_mem_derivedSet {X : Set ℝ} (hX : X.WellFoundedOn (· > ·))
    {y : ℝ} (hy : y ∈ derivedSet X) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ X, y < z ∧ z < y + ε := by
  by_contra h
  have hcon : ∀ z ∈ X, y < z → y + ε ≤ z := by
    intro z hz hlt
    by_contra hle
    exact h ⟨z, hz, hlt, not_le.mp hle⟩
  rw [mem_derivedSet, accPt_iff_nhds] at hy
  have hbelow : ∀ z ∈ X, z < y → z ≤ y - ε := by
    intro z hz hzy
    by_contra hzlt
    have hzgt : y - ε < z := not_le.mp hzlt
    let S : Set ℝ := X ∩ Set.Ioo (y - ε) y
    have hS : S.WellFoundedOn (· > ·) := hX.subset Set.inter_subset_left
    have hne : S.Nonempty := ⟨z, hz, hzgt, hzy⟩
    obtain ⟨m, hmS, hmmax⟩ := exists_isMax hS hne
    obtain ⟨hmX, hmz, hmy⟩ := hmS
    obtain ⟨w, ⟨⟨hmw, hwyε⟩, hwX⟩, hwne⟩ :=
      hy (Set.Ioo m (y + ε)) (Ioo_mem_nhds hmy (lt_add_of_pos_right y hε))
    rcases lt_or_ge w y with hwy | hwy
    · exact absurd (hmmax w ⟨hwX, by linarith, hwy⟩) (not_le_of_gt hmw)
    · exact absurd (hcon w hwX (lt_of_le_of_ne' hwy hwne)) (not_le_of_gt hwyε)
  obtain ⟨w, ⟨⟨hwlo, hwhi⟩, hwX⟩, hwne⟩ :=
    hy (Set.Ioo (y - ε) (y + ε)) (Ioo_mem_nhds (by linarith) (lt_add_of_pos_right y hε))
  rcases lt_trichotomy w y with hwy | rfl | hwy
  · exact absurd (hbelow w hwX hwy) (not_le_of_gt hwlo)
  · exact hwne rfl
  · exact absurd (hcon w hwX hwy) (not_le_of_gt hwhi)





private theorem omega_le_omega_pow_omega : ω ≤ (ω ^ ω : Ordinal.{0}) := by
  calc
    ω = ω ^ (1 : Ordinal) := (opow_one _).symm
    _ ≤ ω ^ ω := opow_le_opow_right omega0_pos one_lt_omega0.le

private theorem zero_lt_omega_pow_omega : (0 : Ordinal.{0}) < ω ^ ω :=
  omega0_pos.trans_le omega_le_omega_pow_omega

private theorem derived_iterate_succ {K : Set ℝ} (v : ℕ) :
    derivedSet^[v + 1] K = derivedSet (derivedSet^[v] K) :=
  Function.iterate_succ_apply' derivedSet v K

private theorem X_closed {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    (hK : IsSelfSimilarCompactSet K μ ρ) : IsClosed (derivedSet^[u] K) := by
  induction u with
  | zero => simpa using hK.2.2.1.isClosed
  | succ v ih =>
    rw [derived_iterate_succ]
    exact isClosed_derivedSet _

private theorem X_subset_K {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    (hK : IsSelfSimilarCompactSet K μ ρ) : derivedSet^[u] K ⊆ K := by
  induction u with
  | zero => exact le_rfl
  | succ v ih =>
    rw [derived_iterate_succ]
    intro x hx
    exact ih ((X_closed (u := v) hK).closure_subset (derivedSet_subset_closure _ hx))

private theorem X_wf {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    (hK : IsSelfSimilarCompactSet K μ ρ) : (derivedSet^[u] K).WellFoundedOn (· > ·) :=
  hK.2.2.2.2.1.subset (X_subset_K hK)

private theorem s_mem_X {K : Set ℝ} {u : ℕ} {s : Ordinal.{0} → ℝ}
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {β : Ordinal.{0}}
    (hβ : β < ω ^ ω) : s β ∈ derivedSet^[u] K := by
  have hmem : s β ∈ selfSimilarLayer K u := by
    rw [← hsK]; exact ⟨β, hβ, rfl⟩
  exact hmem.1

private theorem s_not_mem_derived {K : Set ℝ} {u : ℕ} {s : Ordinal.{0} → ℝ}
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {β : Ordinal.{0}}
    (hβ : β < ω ^ ω) : s β ∉ derivedSet (derivedSet^[u] K) := by
  have hmem : s β ∈ selfSimilarLayer K u := by
    rw [← hsK]; exact ⟨β, hβ, rfl⟩
  have hmem2 : s β ∈ derivedSet^[u] K \ derivedSet^[u + 1] K := hmem
  rw [derived_iterate_succ] at hmem2
  exact hmem2.2

private theorem s_nonneg {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ} {s : Ordinal.{0} → ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ)
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {β : Ordinal.{0}}
    (hβ : β < ω ^ ω) : 0 ≤ s β :=
  hK.2.2.2.1 (X_subset_K hK (s_mem_X hsK hβ))

private theorem X_le_s0 {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ} {s : Ordinal.{0} → ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {w : ℝ}
    (hw : w ∈ derivedSet^[u] K) : w ≤ s 0 := by
  have hne : (derivedSet^[u] K).Nonempty :=
    ⟨s 0, s_mem_X hsK zero_lt_omega_pow_omega⟩
  obtain ⟨m, hmX, hmmax⟩ := exists_isMax (X_wf hK) hne
  have hm_eq : m = s 0 := by
    by_cases hlayer : m ∈ selfSimilarLayer K u
    · rw [← hsK] at hlayer
      obtain ⟨β, hβ, rfl⟩ := hlayer
      have h1 : s β ≤ s 0 :=
        hs.antitoneOn zero_lt_omega_pow_omega hβ zero_le
      have h0 : s 0 ≤ s β := hmmax _ (s_mem_X hsK zero_lt_omega_pow_omega)
      exact le_antisymm h1 h0
    · have hmder : m ∈ derivedSet (derivedSet^[u] K) := by
        by_contra hbad
        exact hlayer ⟨hmX, fun h => hbad (by rwa [derived_iterate_succ] at h)⟩
      obtain ⟨p, hpX, hmp, -⟩ :=
        exists_gt_of_mem_derivedSet (X_wf hK) hmder (ε := 1) one_pos
      exact absurd (hmmax p hpX) (not_le_of_gt hmp)
  rw [← hm_eq]
  exact hmmax w hw




/-- Every ordinal below `ω * (α + 1)` is at most `ω * α + n` for some `n`. -/
private theorem exists_le_block {α β : Ordinal.{0}} (hβ : β < ω * (α + 1)) :
    ∃ n : ℕ, β ≤ ω * α + n := by
  rw [mul_add_one] at hβ
  by_cases hle : β ≤ ω * α
  · exact ⟨0, by simpa using hle⟩
  · have hge : ω * α ≤ β := le_of_not_ge hle
    have hsub : β - ω * α < ω := (sub_lt_of_le hge).mpr hβ
    obtain ⟨n, hn⟩ := lt_omega0.mp hsub
    refine ⟨n, ?_⟩
    rw [← hn]
    exact le_of_eq (Ordinal.add_sub_cancel_of_le hge).symm

/-- Block indices stay below `ω ^ ω`. -/
private theorem block_lt {α : Ordinal.{0}} (hα : α < ω ^ ω) (n : ℕ) :
    ω * α + n < ω ^ ω := by
  have hmul : ω * (ω ^ ω : Ordinal.{0}) = ω ^ ω := by
    calc ω * ω ^ ω = ω ^ (1 : Ordinal.{0}) * ω ^ ω := by rw [opow_one]
      _ = ω ^ ((1 : Ordinal.{0}) + ω) := (opow_add _ _ _).symm
      _ = ω ^ ω := by rw [one_add_omega0]
  have h1 : ω * (α + 1) ≤ ω ^ ω := by
    rw [← hmul]
    exact mul_le_mul_right (Order.add_one_le_iff.mpr hα) ω
  have h2 : ω * α + (n : Ordinal) < ω * (α + 1) := by
    rw [mul_add_one, add_lt_add_iff_left]
    exact natCast_lt_omega0 n
  exact h2.trans_le h1

private theorem block_lt_of_lt {α β : Ordinal.{0}} (hα : α < ω ^ ω)
    (hβ : β < ω * (α + 1)) : β < ω ^ ω :=
  (exists_le_block hβ).elim fun n hn => hn.trans_lt (block_lt hα n)

/-- The infimum of one block of the enumeration. -/
private noncomputable def blockInf (s : Ordinal.{0} → ℝ) (α : Ordinal.{0}) : ℝ :=
  sInf (Set.range fun n : ℕ => s (ω * α + n))

private theorem block_tendsto {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ} {s : Ordinal.{0} → ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α : Ordinal.{0}}
    (hα : α < ω ^ ω) :
    Tendsto (fun n : ℕ => s (ω * α + n)) atTop (𝓝 (blockInf s α)) := by
  have hanti : Antitone (fun n : ℕ => s (ω * α + n)) := by
    intro m n hmn
    apply hs.antitoneOn (block_lt hα m) (block_lt hα n)
    rw [add_le_add_iff_left]
    exact_mod_cast hmn
  have hbdd : BddBelow (Set.range fun n : ℕ => s (ω * α + n)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact s_nonneg hK hsK (block_lt hα n)⟩
  exact tendsto_atTop_ciInf hanti hbdd

private theorem blockInf_le {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ} {s : Ordinal.{0} → ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ)
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α : Ordinal.{0}}
    (hα : α < ω ^ ω) (n : ℕ) : blockInf s α ≤ s (ω * α + n) :=
  csInf_le ⟨0, by
    rintro _ ⟨m, rfl⟩
    exact s_nonneg hK hsK (block_lt hα m)⟩ ⟨n, rfl⟩

private theorem le_blockInf {s : Ordinal.{0} → ℝ} {α : Ordinal.{0}}
    {c : ℝ} (hc : ∀ n : ℕ, c ≤ s (ω * α + n)) :
    c ≤ blockInf s α :=
  le_csInf (Set.range_nonempty _) (by
    rintro _ ⟨n, rfl⟩
    exact hc n)




private theorem blockInf_mem_derived {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α : Ordinal.{0}}
    (hα : α < ω ^ ω) :
    blockInf s α ∈ derivedSet (derivedSet^[u] K) := by
  have htend := block_tendsto hK hs hsK hα
  rw [mem_derivedSet, accPt_iff_nhds]
  intro U hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend hU)
  refine ⟨s (ω * α + N), ⟨hN N le_rfl, s_mem_X hsK (block_lt hα N)⟩, ?_⟩
  have hlt : s (ω * α + ((N + 1 : ℕ) : Ordinal.{0})) < s (ω * α + (N : Ordinal.{0})) :=
    hs (block_lt hα N) (block_lt hα (N + 1)) (by
      rw [add_lt_add_iff_left]
      exact_mod_cast Nat.lt_succ_self N)
  have hle : blockInf s α ≤ s (ω * α + ((N + 1 : ℕ) : Ordinal.{0})) :=
    blockInf_le hK hsK hα (N + 1)
  exact ne_of_gt (lt_of_le_of_lt hle hlt)

private theorem succ_block_lt {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    ω * (α + 1) < ω ^ ω := by
  have hlim : Order.IsSuccLimit (ω ^ ω : Ordinal.{0}) :=
    isSuccLimit_opow one_lt_omega0 isSuccLimit_omega0
  have h1 : α + 1 < ω ^ ω := by
    rw [← Order.succ_eq_add_one]
    exact hlim.succ_lt hα
  have hmul : ω * (ω ^ ω : Ordinal.{0}) = ω ^ ω := by
    calc ω * ω ^ ω = ω ^ (1 : Ordinal.{0}) * ω ^ ω := by rw [opow_one]
      _ = ω ^ ((1 : Ordinal.{0}) + ω) := (opow_add _ _ _).symm
      _ = ω ^ ω := by rw [one_add_omega0]
  rw [← hmul]
  exact mul_lt_mul_of_pos_left h1 omega0_pos

private theorem succ_block_lt_blockInf {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α : Ordinal.{0}}
    (hα : α < ω ^ ω) : s (ω * (α + 1)) < blockInf s α := by
  have hidx : ∀ n : ℕ, ω * α + n < ω * (α + 1) := fun n => by
    rw [mul_add_one, add_lt_add_iff_left]
    exact natCast_lt_omega0 n
  have hle : s (ω * (α + 1)) ≤ blockInf s α := by
    apply le_blockInf
    intro n
    exact hs.antitoneOn (block_lt hα n) (succ_block_lt hα) (hidx n).le
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    exact s_not_mem_derived hsK (succ_block_lt hα)
      (heq.symm ▸ blockInf_mem_derived hK hs hsK hα)
  · exact hlt

private theorem blockInf_eq_sInf_Iio {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α : Ordinal.{0}}
    (hα : α < ω ^ ω) :
    blockInf s α = sInf (s '' Set.Iio (ω * (α + 1))) := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨s (ω * α), ⟨ω * α, by
        have : ω * α < ω * (α + 1) := by
          rw [mul_add_one]
          exact lt_add_of_pos_right _ omega0_pos
        exact this, rfl⟩⟩
    · rintro _ ⟨β, hβ, rfl⟩
      obtain ⟨n, hn⟩ := exists_le_block hβ
      exact (blockInf_le hK hsK hα n).trans
        (hs.antitoneOn (block_lt_of_lt hα hβ) (block_lt hα n) hn)
  · apply le_blockInf
    intro n
    exact csInf_le ⟨0, by
      rintro _ ⟨β, hβ, rfl⟩
      exact s_nonneg hK hsK (block_lt_of_lt hα hβ)⟩
      ⟨ω * α + n, by
        rw [mul_add_one]
        exact (add_lt_add_iff_left _).mpr (natCast_lt_omega0 n), rfl⟩




private theorem sInf_image_gt_eq {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {z : ℝ} (hz : z ∈ derivedSet (derivedSet^[u] K)) :
    sInf (s '' {β : Ordinal.{0} | β < ω ^ ω ∧ z < s β}) = z := by
  have hzX : z ∈ derivedSet^[u] K :=
    (derivedSet_subset_closure _).trans (X_closed hK).closure_subset hz
  have hne : s 0 ≠ z := fun h =>
    s_not_mem_derived hsK zero_lt_omega_pow_omega (h.symm ▸ hz)
  have hzlt : z < s 0 := lt_of_le_of_ne (X_le_s0 hK hs hsK hzX) hne.symm
  set T : Set Ordinal.{0} := {β | β < ω ^ ω ∧ z < s β} with hT
  have hTne : (s '' T).Nonempty :=
    ⟨s 0, ⟨0, ⟨zero_lt_omega_pow_omega, hzlt⟩, rfl⟩⟩
  have hbdd : BddBelow (s '' T) := ⟨0, by
    rintro _ ⟨β, ⟨hβ, -⟩, rfl⟩
    exact s_nonneg hK hsK hβ⟩
  have hmge : z ≤ sInf (s '' T) := by
    apply le_csInf hTne
    rintro _ ⟨β, ⟨-, hlt⟩, rfl⟩
    exact hlt.le
  have hder_of_gap : ∀ w ∈ derivedSet^[u] K, z < w → w < sInf (s '' T) →
      w ∈ derivedSet (derivedSet^[u] K) := by
    intro w hwX hwz hwm
    by_contra hwbad
    have hwlayer : w ∈ selfSimilarLayer K u := ⟨hwX, fun h =>
      hwbad (by rwa [derived_iterate_succ] at h)⟩
    rw [← hsK] at hwlayer
    obtain ⟨β, hβ, rfl⟩ := hwlayer
    exact absurd (csInf_le hbdd ⟨β, ⟨hβ, hwz⟩, rfl⟩) (not_le_of_gt hwm)
  by_cases hEq : sInf (s '' T) = z
  · exact hEq
  · exfalso
    have hmgt : z < sInf (s '' T) := lt_of_le_of_ne hmge (fun h => hEq h.symm)
    have hgap : ∀ w ∈ derivedSet^[u] K, z < w → w < sInf (s '' T) → False := by
      intro w hwX hwz hwm
      have hwder := hder_of_gap w hwX hwz hwm
      have hS : (derivedSet^[u] K ∩ Set.Ioo z (sInf (s '' T))).WellFoundedOn (· > ·) :=
        (X_wf hK).subset Set.inter_subset_left
      obtain ⟨mw, hmwS, hmwmax⟩ := exists_isMax hS ⟨w, hwX, hwz, hwm⟩
      obtain ⟨hmwX, hmwz, hmwm⟩ := hmwS
      have mwder := hder_of_gap mw hmwX hmwz hmwm
      obtain ⟨p, hpX, hmwp, hpm⟩ := exists_gt_of_mem_derivedSet (X_wf hK) mwder
        (ε := sInf (s '' T) - mw) (by linarith)
      exact absurd (hmwmax p ⟨hpX, by linarith, by linarith⟩) (not_le_of_gt hmwp)
    obtain ⟨p, hpX, hzp, hpm⟩ := exists_gt_of_mem_derivedSet (X_wf hK) hz
      (ε := sInf (s '' T) - z) (by linarith)
    exact hgap p hpX hzp (by linarith)






/-- The supremum of the indices of layer points above a derived point is a
multiple of `ω`, and the point is the infimum of the block infima below it. -/
private theorem gamma_form {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {z : ℝ} (hz : z ∈ derivedSet (derivedSet^[u] K)) :
    ∃ q : Ordinal.{0}, q ≠ 0 ∧ q ≤ ω ^ ω ∧ sSup {β : Ordinal.{0} | β < ω ^ ω ∧ z < s β} = ω * q ∧
      z = sInf (blockInf s '' Set.Iio q) := by
  set T : Set Ordinal.{0} := {β | β < ω ^ ω ∧ z < s β} with hT
  set γ : Ordinal.{0} := sSup T with hγ
  have hzX : z ∈ derivedSet^[u] K :=
    (derivedSet_subset_closure _).trans (X_closed hK).closure_subset hz
  have hne : s 0 ≠ z := fun h =>
    s_not_mem_derived hsK zero_lt_omega_pow_omega (h.symm ▸ hz)
  have hzlt : z < s 0 := lt_of_le_of_ne (X_le_s0 hK hs hsK hzX) hne.symm
  have hTne : T.Nonempty := ⟨0, zero_lt_omega_pow_omega, hzlt⟩
  have hTbdd : BddAbove T := ⟨ω ^ ω, fun β hβ => hβ.1.le⟩
  have hdown : ∀ {β β' : Ordinal.{0}}, β < β' → β' ∈ T → β ∈ T := by
    intro β β' hlt hβ'
    refine ⟨lt_trans hlt hβ'.1, ?_⟩
    exact lt_trans hβ'.2 (hs (lt_trans hlt hβ'.1) hβ'.1 hlt)
  have hmin : ∀ δ : Ordinal.{0}, δ < ω ^ ω → sInf (s '' Set.Iic δ) = s δ := by
    intro δ hδ
    have hbdd : BddBelow (s '' Set.Iic δ) := ⟨0, by
      rintro _ ⟨β, hβ, rfl⟩
      exact s_nonneg hK hsK (lt_of_le_of_lt hβ hδ)⟩
    have hmem : s δ ∈ s '' Set.Iic δ :=
      Set.mem_image_of_mem s (Set.mem_Iic.mpr le_rfl)
    apply le_antisymm
    · exact csInf_le hbdd hmem
    · apply le_csInf ⟨s δ, hmem⟩
      rintro _ ⟨β, hβ, rfl⟩
      exact hs.antitoneOn (lt_of_le_of_lt hβ hδ) hδ hβ
  have hγle : γ ≤ ω ^ ω := csSup_le hTne (fun β hβ => hβ.1.le)
  have hγnotmem : γ ∉ T := by
    intro hγmem
    have hTIic : T = Set.Iic γ := by
      apply Set.Subset.antisymm
      · intro β hβ
        exact le_csSup hTbdd hβ
      · intro β hβ
        rcases eq_or_lt_of_le (Set.mem_Iic.mp hβ) with rfl | hlt
        · exact hγmem
        · exact hdown hlt hγmem
    have hz_eq : z = s γ := by
      have h1 : sInf (s '' T) = z := sInf_image_gt_eq hK hs hsK hz
      rw [hTIic] at h1
      rw [← h1]
      exact hmin γ hγmem.1
    exact s_not_mem_derived hsK hγmem.1 (hz_eq ▸ hz)
  have hTIio : T = Set.Iio γ := by
    apply Set.Subset.antisymm
    · intro β hβ
      exact lt_of_le_of_ne (le_csSup hTbdd hβ) (fun h => by
        have hβ' : sSup T ∈ T := h ▸ hβ
        exact hγnotmem hβ')
    · intro β hβ
      obtain ⟨β', hβ'T, hββ'⟩ := (lt_csSup_iff hTbdd hTne).mp hβ
      exact hdown hββ' hβ'T
  have hγpos : 0 < γ := by
    have h0 : (0 : Ordinal.{0}) ≤ γ := le_csSup hTbdd ⟨zero_lt_omega_pow_omega, hzlt⟩
    exact lt_of_le_of_ne h0 (fun h => hγnotmem (h ▸ ⟨zero_lt_omega_pow_omega, hzlt⟩))
  have hγsucc : ∀ δ : Ordinal.{0}, δ < γ → δ + 1 < γ := by
    intro δ hδ
    by_contra hle
    have hγeq : γ = δ + 1 := le_antisymm (le_of_not_gt hle)
      (by exact_mod_cast Order.add_one_le_iff.mpr hδ)
    have hδmem : δ ∈ T := by rw [hTIio]; exact hδ
    have hδlt : δ < ω ^ ω := by
      have h1 : δ < γ := by rw [hTIio] at hδmem; exact hδmem
      exact lt_of_lt_of_le h1 hγle
    have hTIic : T = Set.Iic δ := by
      rw [hTIio, hγeq]
      ext β
      constructor
      · intro h
        exact Set.mem_Iic.mpr (Order.le_of_lt_succ (by rwa [← Order.succ_eq_add_one] at h))
      · intro h
        rw [← Order.succ_eq_add_one]
        exact lt_of_le_of_lt (Set.mem_Iic.mp h) (Order.lt_succ δ)
    have hz_eq : z = s δ := by
      have h1 : sInf (s '' T) = z := sInf_image_gt_eq hK hs hsK hz
      rw [hTIic] at h1
      rw [← h1]
      exact hmin δ hδlt
    exact s_not_mem_derived hsK hδlt (hz_eq ▸ hz)
  have hpre : Order.IsSuccPrelimit γ :=
    Order.isSuccPrelimit_of_succ_lt fun δ hδ => by
      rw [Order.succ_eq_add_one]
      exact hγsucc δ hδ
  obtain ⟨q, hq⟩ := isSuccPrelimit_iff_omega0_dvd.mp hpre
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact lt_irrefl 0 (hq ▸ hγpos)
  have hmul : ω * (ω ^ ω : Ordinal.{0}) = ω ^ ω := by
    calc ω * ω ^ ω = ω ^ (1 : Ordinal.{0}) * ω ^ ω := by rw [opow_one]
      _ = ω ^ ((1 : Ordinal.{0}) + ω) := (opow_add _ _ _).symm
      _ = ω ^ ω := by rw [one_add_omega0]
  have hqle : q ≤ ω ^ ω := by
    by_contra hlt
    have h1 : ω * (ω ^ ω) < ω * q :=
      mul_lt_mul_of_pos_left (not_le.mp hlt) omega0_pos
    rw [hmul, ← hq] at h1
    exact lt_irrefl _ (h1.trans_le hγle)
  have hEqIio : sInf (s '' Set.Iio γ) = z := by
    have h1 : sInf (s '' T) = z := sInf_image_gt_eq hK hs hsK hz
    rwa [hTIio] at h1
  have hbddS : BddBelow (s '' Set.Iio γ) := ⟨0, by
    rintro _ ⟨β, hβ, rfl⟩
    exact s_nonneg hK hsK (lt_of_lt_of_le (Set.mem_Iio.mp hβ) hγle)⟩
  have hblock : sInf (s '' Set.Iio γ) = sInf (blockInf s '' Set.Iio q) := by
    apply le_antisymm
    · apply le_csInf
      · exact ⟨blockInf s 0, Set.mem_image_of_mem _ (Set.mem_Iio.mpr
          (pos_iff_ne_zero.mpr hq0))⟩
      · rintro _ ⟨α, hαq, rfl⟩
        have hαq' : α < q := Set.mem_Iio.mp hαq
        have hαlt : α < ω ^ ω := lt_of_lt_of_le hαq' hqle
        rw [blockInf_eq_sInf_Iio hK hs hsK hαlt]
        apply le_csInf
        · exact ⟨s (ω * α), Set.mem_image_of_mem _ (Set.mem_Iio.mpr (by
            rw [mul_add_one]
            exact lt_add_of_pos_right _ omega0_pos))⟩
        · rintro _ ⟨n, hn, rfl⟩
          apply csInf_le hbddS
          apply Set.mem_image_of_mem
          apply Set.mem_Iio.mpr
          have h2 : ω * (α + 1) ≤ γ := by
            rw [hq]
            exact mul_le_mul_right (Order.add_one_le_iff.mpr hαq') ω
          exact lt_of_lt_of_le (Set.mem_Iio.mp hn) h2
    · apply le_csInf
      · exact ⟨s 0, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hγpos)⟩
      · rintro _ ⟨β, hβγ, rfl⟩
        have hβγ' : β < γ := Set.mem_Iio.mp hβγ
        have hdiv : ∃ α : Ordinal.{0}, α < q ∧ β < ω * (α + 1) := by
          refine ⟨β / ω, ?_, ?_⟩
          · by_contra hc
            have h1 : ω * q ≤ ω * (β / ω) :=
              mul_le_mul_right (le_of_not_gt hc) ω
            have h2 : ω * (β / ω) ≤ β := mul_div_le β ω
            rw [hq] at hβγ'
            exact absurd (h1.trans h2) (not_le_of_gt hβγ')
          · have hmod : β % ω < ω := mod_lt β omega0_ne_zero
            have hlt : ω * (β / ω) + β % ω < ω * (β / ω) + ω := by
              rw [add_lt_add_iff_left]
              exact hmod
            rw [div_add_mod β ω] at hlt
            rw [mul_add_one]
            exact hlt
        obtain ⟨α, hαq, hβα⟩ := hdiv
        have hαlt : α < ω ^ ω := lt_of_lt_of_le hαq hqle
        have hbddBlock : BddBelow (blockInf s '' Set.Iio q) := ⟨0, by
          rintro _ ⟨α', hα', rfl⟩
          exact le_blockInf (fun n => s_nonneg hK hsK
            (block_lt (lt_of_lt_of_le (Set.mem_Iio.mp hα') hqle) n))⟩
        have hLle : blockInf s α ≤ s β := by
          rw [blockInf_eq_sInf_Iio hK hs hsK hαlt]
          exact csInf_le ⟨0, by
            rintro _ ⟨β', hβ', rfl⟩
            exact s_nonneg hK hsK (block_lt_of_lt hαlt (Set.mem_Iio.mp hβ'))⟩
            (Set.mem_image_of_mem _ (Set.mem_Iio.mpr hβα))
        exact (csInf_le hbddBlock (Set.mem_image_of_mem _ (Set.mem_Iio.mpr hαq))).trans hLle
  refine ⟨q, hq0, hqle, ?_, ?_⟩
  · exact hq
  · rw [← hEqIio, hblock]




private theorem blockInf_antitone {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α β : Ordinal.{0}}
    (hα : α < ω ^ ω) (hβ : β < ω ^ ω) (h : α ≤ β) :
    blockInf s β ≤ blockInf s α := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · apply le_trans (blockInf_le hK hsK hβ 0)
    apply le_blockInf
    intro n
    apply hs.antitoneOn (block_lt hα n) (block_lt hβ 0)
    have h1 : ω * α + (n : Ordinal.{0}) < ω * β := by
      have h2 : ω * α + (n : Ordinal.{0}) < ω * (α + 1) := by
        rw [mul_add_one, add_lt_add_iff_left]
        exact natCast_lt_omega0 n
      have h3 : ω * (α + 1) ≤ ω * β :=
        mul_le_mul_right (Order.add_one_le_iff.mpr hlt) ω
      exact h2.trans_le h3
    simpa using h1.le

private theorem blockInf_strictAnti {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α β : Ordinal.{0}}
    (hα : α < ω ^ ω) (hβ : β < ω ^ ω) (h : α < β) :
    blockInf s β < blockInf s α := by
  apply lt_of_le_of_lt _ (succ_block_lt_blockInf hK hs hsK hα)
  apply le_trans (blockInf_le hK hsK hβ 0)
  have hle : ω * (α + 1) ≤ ω * β + ((0 : ℕ) : Ordinal.{0}) := by
    have hle' : ω * (α + 1) ≤ ω * β :=
      mul_le_mul_right (Order.add_one_le_iff.mpr h) ω
    simpa using hle'
  exact hs.antitoneOn (succ_block_lt hα) (block_lt hβ 0) hle

private theorem sInf_block_Iic {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {δ : Ordinal.{0}}
    (hδ : δ < ω ^ ω) : sInf (blockInf s '' Set.Iic δ) = blockInf s δ := by
  apply le_antisymm
  · exact csInf_le ⟨0, by
      rintro _ ⟨α, hα, rfl⟩
      exact le_blockInf (fun n => s_nonneg hK hsK
        (block_lt (lt_of_le_of_lt (Set.mem_Iic.mp hα) hδ) n))⟩
      (Set.mem_image_of_mem _ (Set.mem_Iic.mpr le_rfl))
  · apply le_csInf ⟨blockInf s δ, Set.mem_image_of_mem _ (Set.mem_Iic.mpr le_rfl)⟩
    rintro _ ⟨α, hα, rfl⟩
    exact blockInf_antitone hK hs hsK (lt_of_le_of_lt (Set.mem_Iic.mp hα) hδ) hδ
      (Set.mem_Iic.mp hα)

private theorem mem_derivedSet_of_isSuccLimit {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {z : ℝ} {q : Ordinal.{0}} (hq : Order.IsSuccLimit q) (hqle : q ≤ ω ^ ω)
    (hz : z = sInf (blockInf s '' Set.Iio q)) :
    z ∈ derivedSet (derivedSet (derivedSet^[u] K)) := by
  rw [mem_derivedSet, accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hqpos : (0 : Ordinal.{0}) < q := by
    rcases eq_or_ne q 0 with rfl | hne
    · exact absurd hq not_isSuccLimit_zero
    · exact pos_iff_ne_zero.mpr hne
  have hne : (blockInf s '' Set.Iio q).Nonempty :=
    ⟨blockInf s 0, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hqpos)⟩
  obtain ⟨y, hymem, hylt⟩ := exists_lt_of_csInf_lt hne
    (by rw [← hz]; exact lt_add_of_pos_right _ hε)
  obtain ⟨α, hαmem, rfl⟩ := hymem
  have hαq : α < q := Set.mem_Iio.mp hαmem
  have hαlt : α < ω ^ ω := lt_of_lt_of_le hαq hqle
  have hbddBlock : BddBelow (blockInf s '' Set.Iio q) := ⟨0, by
    rintro _ ⟨α', hα', rfl⟩
    exact le_blockInf (fun n => s_nonneg hK hsK
      (block_lt (lt_of_lt_of_le (Set.mem_Iio.mp hα') hqle) n))⟩
  have hzle : z ≤ blockInf s α := by
    rw [hz]
    exact csInf_le hbddBlock (Set.mem_image_of_mem _ (Set.mem_Iio.mpr hαq))
  have hα' : α + 1 < q := hq.succ_lt hαq
  have hα'lt : α + 1 < ω ^ ω := lt_of_lt_of_le hα' hqle
  have hzlt : z < blockInf s α := by
    have h1 : blockInf s (α + 1) < blockInf s α :=
      blockInf_strictAnti hK hs hsK hαlt hα'lt (by
        rw [← Order.succ_eq_add_one]
        exact Order.lt_succ α)
    have h2 : z ≤ blockInf s (α + 1) := by
      rw [hz]
      exact csInf_le hbddBlock (Set.mem_image_of_mem _
        (Set.mem_Iio.mpr (by rw [← Order.succ_eq_add_one]; exact hα')))
    exact lt_of_le_of_lt h2 h1
  refine ⟨blockInf s α, ⟨?_, blockInf_mem_derived hK hs hsK hαlt⟩, ?_⟩
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · exact ne_of_gt hzlt




/-- Every point of the next layer is the infimum of one block. -/
private theorem exists_block_eq {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {z : ℝ} (hzB : z ∈ derivedSet (derivedSet^[u] K))
    (hzD : z ∉ derivedSet (derivedSet (derivedSet^[u] K))) :
    ∃ α : Ordinal.{0}, α < ω ^ ω ∧ z = blockInf s α := by
  obtain ⟨q, hq0, hqle, -, hz⟩ := gamma_form hK hs hsK hzB
  rcases zero_or_succ_or_isSuccLimit q with hq0' | ⟨δ, hδ⟩ | hqlim
  · exact absurd hq0' hq0
  · have hqeq : q = δ + 1 := by rw [← hδ]; exact (Order.succ_eq_add_one δ).symm
    have hδlt : δ < ω ^ ω := by
      have : δ < q := by rw [hqeq]; exact lt_add_of_pos_right _ one_pos
      exact lt_of_lt_of_le this hqle
    refine ⟨δ, hδlt, ?_⟩
    rw [hz, hqeq]
    have : Set.Iio (δ + 1) = Set.Iic δ := by
      ext β
      constructor
      · intro h
        exact Set.mem_Iic.mpr (Order.le_of_lt_succ (by rwa [← Order.succ_eq_add_one] at h))
      · intro h
        rw [← Order.succ_eq_add_one]
        exact lt_of_le_of_lt (Set.mem_Iic.mp h) (Order.lt_succ δ)
    rw [this]
    exact sInf_block_Iic hK hs hsK hδlt
  · exact absurd (mem_derivedSet_of_isSuccLimit hK hs hsK hqlim hqle hz) hzD

/-- No point of the next derived set lies strictly between a block infimum
and the first point of its block. -/
private theorem gap {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α : Ordinal.{0}}
    (hα : α < ω ^ ω) {z : ℝ} (hzB : z ∈ derivedSet (derivedSet^[u] K))
    (hlt : blockInf s α < z) (hgt : z < s (ω * α)) : False := by
  obtain ⟨q, hq0, hqle, -, hz⟩ := gamma_form hK hs hsK hzB
  have hqα : q ≤ α := by
    by_contra hltq
    have hαq : α < q := not_le.mp hltq
    have hbddBlock : BddBelow (blockInf s '' Set.Iio q) := ⟨0, by
      rintro _ ⟨α', hα', rfl⟩
      exact le_blockInf (fun n => s_nonneg hK hsK
        (block_lt (lt_of_lt_of_le (Set.mem_Iio.mp hα') hqle) n))⟩
    have : z ≤ blockInf s α := by
      rw [hz]
      exact csInf_le hbddBlock (Set.mem_image_of_mem _ (Set.mem_Iio.mpr hαq))
    exact absurd this (not_le_of_gt hlt)
  have hbddBlock : BddBelow (blockInf s '' Set.Iio q) := ⟨0, by
    rintro _ ⟨α', hα', rfl⟩
    exact le_blockInf (fun n => s_nonneg hK hsK
      (block_lt (lt_of_lt_of_le (Set.mem_Iio.mp hα') hqle) n))⟩
  have hge : s (ω * α) ≤ z := by
    rw [hz]
    apply le_csInf ⟨blockInf s 0, Set.mem_image_of_mem _ (Set.mem_Iio.mpr
      (pos_iff_ne_zero.mpr hq0))⟩
    rintro _ ⟨α', hα'mem, rfl⟩
    have hα'q : α' < q := Set.mem_Iio.mp hα'mem
    have hα'α : α' < α := lt_of_lt_of_le hα'q hqα
    apply le_blockInf
    intro n
    have e : ω * α + ((0 : ℕ) : Ordinal.{0}) = ω * α := by simp
    rw [← e]
    apply hs.antitoneOn (block_lt (lt_of_lt_of_le hα'q hqle) n) (block_lt hα 0)
    apply le_of_lt
    have h1 : ω * α' + (n : Ordinal.{0}) < ω * (α' + 1) := by
      rw [mul_add_one, add_lt_add_iff_left]
      exact natCast_lt_omega0 n
    have h2 : ω * (α' + 1) ≤ ω * α + ((0 : ℕ) : Ordinal.{0}) := by
      simpa using mul_le_mul_right (Order.add_one_le_iff.mpr hα'α) ω
    exact h1.trans_le h2
  exact absurd hge (not_le_of_gt hgt)

/-- A block infimum is isolated in the next derived set. -/
private theorem blockInf_not_mem_derivedSet {K : Set ℝ} {μ : ℕ} {ρ : ℝ} {u : ℕ}
    {s : Ordinal.{0} → ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
    (hs : StrictAntiOn s (Set.Iio (ω ^ ω)))
    (hsK : s '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) {α : Ordinal.{0}}
    (hα : α < ω ^ ω) :
    blockInf s α ∉ derivedSet (derivedSet (derivedSet^[u] K)) := by
  intro hder
  have hBwf : (derivedSet (derivedSet^[u] K)).WellFoundedOn (· > ·) :=
    (X_wf hK).subset ((derivedSet_subset_closure _).trans (X_closed hK).closure_subset)
  have hpos : 0 < s (ω * α) - blockInf s α := by
    have h1 : blockInf s α ≤ s (ω * α + ((1 : ℕ) : Ordinal.{0})) :=
      blockInf_le hK hsK hα 1
    have h2 : s (ω * α + ((1 : ℕ) : Ordinal.{0})) < s (ω * α + ((0 : ℕ) : Ordinal.{0})) := by
      apply hs (block_lt hα 0) (block_lt hα 1)
      rw [add_lt_add_iff_left]
      exact_mod_cast Nat.zero_lt_one
    have h3 : ω * α + ((0 : ℕ) : Ordinal.{0}) = ω * α := by simp
    rw [h3] at h2
    linarith
  obtain ⟨w, hwB, hlow, hhigh⟩ := exists_gt_of_mem_derivedSet hBwf hder
    (ε := s (ω * α) - blockInf s α) hpos
  exact gap hK hs hsK hα hwB (by linarith) (by linarith)





end isSelfSimilarCompactSet_layer_enum_tendsto

open isSelfSimilarCompactSet_layer_enum_tendsto in
/-- **Limits between consecutive layers of a self-similar compact set.** Let $K$ be a
self-similar compact set of module $\mu$ and ratio $\rho$, with layers
$T_u = K^{(u)} \setminus K^{(u+1)}$ for $u \ge 0$, where $K^{(u)}$ is the $u$-th derived set of
$K$. Suppose that for every $u$, $\alpha \mapsto T_u[\alpha]$ is a strictly decreasing map from
the ordinals $\alpha < \omega^\omega$ onto $T_u$. Then for every $u \ge 0$ and every ordinal
$\alpha < \omega^\omega$, $T_u[\omega \alpha + n] \to T_{u+1}[\alpha]$ as $n \to \infty$ through
the natural numbers (ordinal arithmetic in the index).

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 4. -/
public theorem isSelfSimilarCompactSet_layer_enum_tendsto {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {t : ℕ → Ordinal.{0} → ℝ}
    (ht : ∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω)))
    (htK : ∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    (u : ℕ) {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    Tendsto (fun n : ℕ => t u (ω * α + n)) atTop (𝓝 (t (u + 1) α)) := by
  have hmemB : ∀ y ∈ selfSimilarLayer K (u + 1),
      y ∈ derivedSet (derivedSet^[u] K) ∧
        y ∉ derivedSet (derivedSet (derivedSet^[u] K)) := by
    intro y hy
    have hy1 : y ∈ derivedSet^[u + 1] K := hy.1
    have hy2 : y ∉ derivedSet^[u + 1 + 1] K := hy.2
    rw [derived_iterate_succ] at hy1
    rw [derived_iterate_succ (u + 1)] at hy2
    rw [derived_iterate_succ] at hy2
    exact ⟨hy1, hy2⟩
  have hlayer_of : ∀ y : ℝ, y ∈ derivedSet (derivedSet^[u] K) →
      y ∉ derivedSet (derivedSet (derivedSet^[u] K)) →
      y ∈ selfSimilarLayer K (u + 1) := by
    intro y hy1 hy2
    have h1 : y ∈ derivedSet^[u + 1] K := by
      rw [derived_iterate_succ]
      exact hy1
    have h2 : y ∉ derivedSet^[u + 1 + 1] K := by
      rw [derived_iterate_succ (u + 1), derived_iterate_succ]
      exact hy2
    exact ⟨h1, h2⟩
  have hLmem : ∀ β : Ordinal.{0}, β < ω ^ ω →
      blockInf (t u) β ∈ selfSimilarLayer K (u + 1) := by
    intro β hβ
    exact hlayer_of _ (blockInf_mem_derived hK (ht u) (htK u) hβ)
      (blockInf_not_mem_derivedSet hK (ht u) (htK u) hβ)
  have hrange1 : blockInf (t u) '' Set.Iio (ω ^ ω) = selfSimilarLayer K (u + 1) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨β, hβ, rfl⟩
      exact hLmem β hβ
    · intro y hy
      obtain ⟨hy1, hy2⟩ := hmemB y hy
      obtain ⟨β, hβ, hβeq⟩ := exists_block_eq hK (ht u) (htK u) hy1 hy2
      exact ⟨β, hβ, hβeq.symm⟩
  have hEq : blockInf (t u) α = t (u + 1) α := by
    let A' : Set.Iio (ω ^ ω : Ordinal.{0}) → ℝᵒᵈ :=
      fun a => OrderDual.toDual (blockInf (t u) a)
    let B' : Set.Iio (ω ^ ω : Ordinal.{0}) → ℝᵒᵈ :=
      fun a => OrderDual.toDual (t (u + 1) a)
    have hA : StrictMono A' := fun a b hab =>
      blockInf_strictAnti hK (ht u) (htK u) a.2 b.2 hab
    have hB : StrictMono B' := fun a b hab => ht (u + 1) a.2 b.2 hab
    have hrange : Set.range A' = Set.range B' := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        have hmem : blockInf (t u) a ∈ selfSimilarLayer K (u + 1) := hLmem a a.2
        rw [← htK (u + 1)] at hmem
        obtain ⟨γ, hγ, hγeq⟩ := hmem
        exact ⟨⟨γ, hγ⟩, congrArg OrderDual.toDual hγeq⟩
      · rintro ⟨a, rfl⟩
        have hmem : t (u + 1) a ∈ selfSimilarLayer K (u + 1) := by
          rw [← htK (u + 1)]
          exact ⟨a, a.2, rfl⟩
        rw [← hrange1] at hmem
        obtain ⟨γ, hγ, hγeq⟩ := hmem
        exact ⟨⟨γ, hγ⟩, congrArg OrderDual.toDual hγeq⟩
    have hcongr := congrFun ((hA.range_inj_of_wellFoundedLT hB).mp hrange) ⟨α, hα⟩
    have h3 := congrArg OrderDual.ofDual hcongr
    change OrderDual.ofDual (OrderDual.toDual (blockInf (t u) α)) =
      OrderDual.ofDual (OrderDual.toDual (t (u + 1) α)) at h3
    simpa using h3
  rw [← hEq]
  exact block_tendsto hK (ht u) (htK u) hα
end MetaMathlibExt
