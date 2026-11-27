/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Basic

/-!
# Reservoir sampling of stream positions

Positions are numbered from zero. After filling the first `k` places, draw one fresh index
`j` uniformly from `0, …, m` when item `m` arrives. Replace the entry at position `j` by the
new entry if `j` is in the reservoir; otherwise keep everything. No final length is an input
to the update. `sample` stores the items as well as their positions.

For a fixed possible output `t`, swapping `j` and `m` recovers the unique possible input
for that draw. This input belongs to the old prefix precisely when `j ∉ t`. Thus every
valid output has the same number `m + 1 - k` of predecessors counted with their draws.

A. Chakrabarti, *Data Stream Algorithms*, lecture notes, 1 July 2025, §6.2, Algorithm 10,
p. 32, uses the one-position update. The joint law for general `k` is deduced here.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.ReservoirSampling

open Finset
open scoped ENNReal
open Cslib.Probability.PMF (uniformOfFinset uniformOfFinset_apply mem_support_uniformOfFinset_iff)

/-- The index drawn when item `m` arrives is uniform on the positions `{0, …, m}`,
including the new position `m`. -/
noncomputable def draw (m : ℕ) : PMF ℕ :=
  uniformOfFinset (range (m + 1)) nonempty_range_add_one

/-- A hit replaces the position that was drawn; a miss changes no position. -/
def replacePosition (m j : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image fun i => if i = j then m else i

theorem replacePosition_eq (m j : ℕ) (s : Finset ℕ) :
    replacePosition m j s = if j ∈ s then insert m (s.erase j) else s := by
  ext i
  by_cases hj : j ∈ s <;> simp [replacePosition, hj, mem_image] <;> grind

/-- The position process, started empty and driven by fresh draws after the first `k` arrivals. -/
noncomputable def positions (k : ℕ) : ℕ → PMF (Finset ℕ)
  | 0 => PMF.pure ∅
  | m + 1 => if m < k then (positions k m).map (insert m) else
      (positions k m).bind fun s => (draw m).map fun j => replacePosition m j s

/-- For any finite set `s` of positions below `m`, the probability that `draw m` lands in `s`
is `s.card / (m + 1)`. -/
theorem hit_probability {m : ℕ} {s : Finset ℕ} (hs : s ⊆ range m) :
    (draw m).toOuterMeasure (↑s : Set ℕ) = s.card / (m + 1 : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_apply_finset]
  calc
    _ = ∑ _i ∈ s, ((m + 1 : ℝ≥0∞)⁻¹) := by
      apply sum_congr rfl
      intro i hi
      have h : i ∈ range (m + 1) := range_mono (Nat.le_succ m) (hs hi)
      simp [draw, h]
    _ = _ := by simp [div_eq_mul_inv, nsmul_eq_mul]

/-- Conditional on a hit, the evicted position is uniform on the nonempty old reservoir. -/
theorem draw_given_hit {m : ℕ} {s : Finset ℕ} (hs : s ⊆ range m) (hne : s.Nonempty) :
    (draw m).filter (↑s) (by
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, hi, (mem_support_uniformOfFinset_iff _ _).2 (range_mono (Nat.le_succ m) (hs hi))⟩) =
      uniformOfFinset s hne := by
  classical
  ext i
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, hit_probability hs]
  by_cases hi : i ∈ s
  · have h : i ∈ range (m + 1) := range_mono (Nat.le_succ m) (hs hi)
    simp [draw, h, hi, div_eq_mul_inv, ENNReal.mul_inv, mul_left_comm,
      ENNReal.inv_mul_cancel (show (m : ℝ≥0∞) + 1 ≠ 0 by positivity) (by simp)]
  · simp [hi]

private theorem positions_fill {k m : ℕ} (h : m ≤ k) : positions k m = PMF.pure (range m) := by
  induction m with
  | zero => simp [positions]
  | succ m ih => simp [positions, show m < k by omega, ih (by omega), range_add_one, PMF.pure_map]

private def swapSet (m j : ℕ) := (Equiv.swap m j).finsetCongr

private theorem replace_eq_swap {m j : ℕ} {s : Finset ℕ} (hs : s ⊆ range m) :
    replacePosition m j s = swapSet m j s := by
  rw [swapSet, Equiv.finsetCongr_apply, map_eq_image]
  apply image_congr
  intro i hi
  have him := Nat.ne_of_lt (mem_range.mp (hs hi))
  by_cases hij : i = j <;> simp [Equiv.swap_apply_def, him, hij]

-- The inverse swap lands in the old family iff the candidate is valid and omits the draw.
private theorem inverse_valid {m j k : ℕ} (hj : j ∈ range (m + 1)) (t : Finset ℕ) :
    (swapSet m j).symm t ∈ (range m).powersetCard k ↔
      t ∈ (range (m + 1)).powersetCard k ∧ j ∉ t := by
  have hlt := mem_range.mp hj
  have hmem (i : ℕ) : i ∈ (swapSet m j).symm t ↔ Equiv.swap m j i ∈ t := by
    simp [swapSet, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, mem_map_equiv]
  simp only [mem_powersetCard, swapSet, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, card_map]
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨⟨fun i hi => ?_, hc⟩, fun h => notMem_range_self (hs ((hmem m).2 (by simpa using h)))⟩
    have hx := mem_range.mp (hs ((hmem (Equiv.swap m j i)).2 (by simpa using hi)))
    simp only [Equiv.swap_apply_def] at hx
    split_ifs at hx <;> simp only [mem_range] <;> omega
  · rintro ⟨⟨hs, hc⟩, hn⟩
    refine ⟨fun i hi => ?_, hc⟩
    have hx := (hmem i).1 hi
    have hl := mem_range.mp (hs hx)
    simp only [Equiv.swap_apply_def] at hx hl
    split_ifs at hx hl <;> simp only [mem_range] <;> first | omega | contradiction

private theorem uniform_map_replace {m k : ℕ} (h : ((range m).powersetCard k).Nonempty)
    (j : ℕ) (t : Finset ℕ) :
    ((uniformOfFinset _ h).map (replacePosition m j)) t =
      uniformOfFinset _ h ((swapSet m j).symm t) := by
  classical
  rw [PMF.map_apply, tsum_eq_single ((swapSet m j).symm t)]
  · by_cases ht : (swapSet m j).symm t ∈ (range m).powersetCard k
    · rw [replace_eq_swap (mem_powersetCard.mp ht).1, Equiv.apply_symm_apply, ite_eq_left rfl]
    · simp [uniformOfFinset_apply, ht]
  · intro s hs
    by_cases hv : s ∈ (range m).powersetCard k
    · rw [replace_eq_swap (mem_powersetCard.mp hv).1]
      exact ite_eq_right (fun he => hs (by simp [he]))
    · simp [uniformOfFinset_apply, hv]

private theorem step_weight {k m : ℕ} (h : k ≤ m) :
    ((m + 1 - k : ℕ) : ℝ≥0∞) * (((m + 1 : ℕ) : ℝ≥0∞)⁻¹ * (m.choose k : ℝ≥0∞)⁻¹) =
      ((m + 1).choose k : ℝ≥0∞)⁻¹ := by
  rw [mul_comm (((m + 1 : ℕ) : ℝ≥0∞)⁻¹), ← ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp)),
    ← Nat.cast_mul, Nat.choose_mul_succ_eq, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp)), mul_left_comm, ENNReal.mul_inv_cancel,
    mul_one]
  · exact_mod_cast (show m + 1 - k ≠ 0 by omega)
  · simp

private theorem uniform_step {m k : ℕ} (h : k ≤ m) (hne : ((range m).powersetCard k).Nonempty)
    (hne' : ((range (m + 1)).powersetCard k).Nonempty) :
    ((uniformOfFinset _ hne).bind fun s => (draw m).map fun j => replacePosition m j s) =
      uniformOfFinset _ hne' := by
  classical
  ext t
  rw [show ((uniformOfFinset _ hne).bind fun s => (draw m).map fun j => replacePosition m j s) =
      (draw m).bind (fun j => (uniformOfFinset _ hne).map (replacePosition m j)) from
        PMF.bind_comm _ _ _, PMF.bind_apply, tsum_eq_sum (s := range (m + 1))]
  · simp_rw [uniform_map_replace, uniformOfFinset_apply]
    by_cases ht : t ∈ (range (m + 1)).powersetCard k
    · rw [ite_eq_left ht]
      calc
        _ = ∑ j ∈ range (m + 1), if j ∉ t then
              ((↑(m + 1) : ℝ≥0∞)⁻¹ * (m.choose k : ℝ≥0∞)⁻¹) else 0 := by
          apply sum_congr rfl
          intro j hj
          simp [inverse_valid hj, ht, draw, hj, mul_ite, card_powersetCard]
        _ = _ := by
          rw [← sum_filter, show ((range (m + 1)).filter fun j => j ∉ t) = range (m + 1) \ t by
            ext; simp]
          simpa [nsmul_eq_mul, card_sdiff_of_subset (mem_powersetCard.mp ht).1,
            (mem_powersetCard.mp ht).2, card_powersetCard] using step_weight h
    · rw [ite_eq_right ht]
      exact sum_eq_zero fun j hj => by simp [inverse_valid hj, ht]
  · intro j hj
    simp [draw, hj]

/-- After any prefix of length `m ≥ k`, the whole reservoir is uniform on the `k`-subsets
of `{0, …, m-1}`. This includes the empty reservoir for `k = 0`. -/
theorem positions_uniform {k m : ℕ} (h : k ≤ m) :
    positions k m = uniformOfFinset ((range m).powersetCard k)
      (powersetCard_nonempty.mpr (by simpa using h)) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [positions_fill (le_refl k)]
    have he : (range k).powersetCard k = {range k} := by
      simpa using powersetCard_self (range k)
    ext s
    simp [PMF.pure_apply, uniformOfFinset_apply, he]
  | succ m hm ih =>
    rw [positions, ite_eq_right (by omega), ih]
    exact uniform_step hm _ _

/-- After a prefix of length `m ≥ k`, a position set can occur if and only if it consists of
exactly `k` positions below `m`. -/
theorem positions_support {k m : ℕ} (h : k ≤ m) (s : Finset ℕ) :
    s ∈ (positions k m).support ↔ s ⊆ range m ∧ s.card = k := by
  rw [positions_uniform h, mem_support_uniformOfFinset_iff, mem_powersetCard]

/-- The one retained position has mass `1/m` at each index below `m`. -/
theorem one_position {m i : ℕ} (hi : i < m) : positions 1 m {i} = (m : ℝ≥0∞)⁻¹ := by
  rw [positions_uniform (by omega), uniformOfFinset_apply]
  simp [mem_powersetCard, hi, card_powersetCard]

/-- Attach the actual input item to each sampled position. Tags distinguish equal values. -/
def tagged {α : Type*} (a : ℕ → α) (s : Finset ℕ) : Finset (ℕ × α) :=
  s.map ⟨fun i => (i, a i), fun _ _ he => congrArg Prod.fst he⟩

/-- Read one item `x`. Before filling the reservoir insert `(m,x)`; afterwards replace only
an entry whose position matches the fresh draw. This update never looks up an old item. -/
noncomputable def step {α : Type*} [DecidableEq α] (k m : ℕ) (x : α) (s : Finset (ℕ × α)) :
    PMF (Finset (ℕ × α)) :=
  if m < k then PMF.pure (insert (m, x) s) else
    (draw m).map fun j => s.image fun e => if e.1 = j then (m, x) else e

/-- The law of the stored entries, starting empty and reading one more item at each successor. -/
noncomputable def sample {α : Type*} [DecidableEq α] (k : ℕ) (a : ℕ → α) : ℕ → PMF (Finset (ℕ × α))
  | 0 => PMF.pure ∅
  | m + 1 => (sample k a m).bind (step k m (a m))

/-- The online law of the stored entries is the pushforward of the position process by tagging.
Thus their provenance has the same law for all streams, without assuming distinct items. -/
theorem sample_eq_tagged {α : Type*} [DecidableEq α] (k : ℕ) (a : ℕ → α) (m : ℕ) :
    sample k a m = (positions k m).map (tagged a) := by
  induction m with
  | zero => simp [sample, positions, PMF.pure_map, tagged]
  | succ m ih =>
    rw [sample, ih, PMF.bind_map, positions]
    by_cases hm : m < k
    · rw [ite_eq_left hm, PMF.map_comp]
      change (positions k m).bind _ = (positions k m).bind _
      congr 1
      funext s
      simp [step, hm, tagged, Function.comp_def, Finset.map_insert]
      rfl
    · simp only [hm, ite_false, PMF.map_bind, PMF.map_comp, Function.comp_def, step]
      congr 1
      funext s
      congr 1
      funext j
      simp only [tagged, replacePosition, map_eq_image, image_image]
      apply image_congr
      intro i _
      change (if i = j then (m, a m) else (i, a i)) =
        ((if i = j then m else i), a (if i = j then m else i))
      split <;> rfl

/-- Forgetting the payloads recovers the same position law for every input stream. -/
theorem sample_positions {α : Type*} [DecidableEq α] (k : ℕ) (a : ℕ → α) (m : ℕ) :
    (sample k a m).map (fun entries => entries.image Prod.fst) = positions k m := by
  rw [sample_eq_tagged, PMF.map_comp]
  have h (s : Finset ℕ) : (tagged a s).image Prod.fst = s := by
    simp only [tagged, map_eq_image, image_image]
    exact Finset.image_id
  have hf : (fun entries : Finset (ℕ × α) => entries.image Prod.fst) ∘ tagged a = id := funext h
  rw [hf, PMF.map_id]

/-- After a prefix of length `m ≥ k` of stream `a`, a stored state can occur if and only if it
consists of the pairs `(i, a i)` for the positions `i` in some `k`-element subset of the prefix.
Equal values at different positions give distinct pairs. -/
theorem sample_support {α : Type*} [DecidableEq α] {k m : ℕ} (h : k ≤ m) (a : ℕ → α)
    (entries : Finset (ℕ × α)) :
    entries ∈ (sample k a m).support ↔
      ∃ s : Finset ℕ, (s ⊆ range m ∧ s.card = k) ∧ tagged a s = entries := by
  rw [sample_eq_tagged, PMF.mem_support_map_iff]
  simp_rw [positions_support h]

end Cslib.Algorithms.Lean.ReservoirSampling
