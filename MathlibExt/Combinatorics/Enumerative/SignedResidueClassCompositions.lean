/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedMinimumPartCompositions
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.Choose.Sum

/-!
# Signed counts of residue-class compositions

When the minimum part is `r - s`, the allowed parts are the positive multiples of `r`.
Dividing the ordered list of parts by `r` preserves its length and reduces the signed count
to the unrestricted count at the quotient.

## References

* Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal of Integer Sequences
  **27** (2024), Article 24.6.5, pp. 1–10, Theorems 8 and 10 and Corollary 12.
  https://cs.uwaterloo.ca/journals/JIS/VOL27/Huang/huang9.html
-/

namespace MetaMathlibExt

private theorem map_div_mul_cancel {r : ℕ} {l : List ℕ} (h : ∀ a ∈ l, r ∣ a) :
    (l.map (· / r)).map (r * ·) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun a ha => Nat.mul_div_cancel' (h a ha)

private def scaleComposition {r q : ℕ} (hr : 0 < r) :
    Composition q ≃ {c : Composition (r * q) // ∀ a ∈ c.blocks, r ∣ a} where
  toFun c :=
    ⟨⟨c.blocks.map (r * ·), by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact Nat.mul_pos hr (c.blocks_pos hb), by
        simpa using List.sum_map_mul_left c.blocks id r⟩, by
      intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact dvd_mul_right r b⟩
  invFun c :=
    ⟨c.val.blocks.map (· / r), by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact Nat.div_pos (Nat.le_of_dvd (c.val.blocks_pos hb) (c.property b hb)) hr, by
      apply Nat.eq_of_mul_eq_mul_left hr
      have h := congrArg List.sum (map_div_mul_cancel c.property)
      rwa [List.map_map, Function.comp_def, List.sum_map_mul_left, c.val.blocks_sum] at h⟩
  left_inv c := Composition.ext (by
    change (c.blocks.map (r * ·)).map (· / r) = c.blocks
    rw [List.map_map]
    conv_rhs => rw [← List.map_id c.blocks]
    exact List.map_congr_left fun a _ => Nat.mul_div_cancel_left a hr)
  right_inv c := Subtype.ext (Composition.ext (map_div_mul_cancel c.property))

private theorem signedCount_multiples {r q : ℕ} (hr : 0 < r) :
    compositionOddMinusEven (r * q) (fun c => ∀ a ∈ c.blocks, r ∣ a) =
      compositionOddMinusEven q (fun c => ∀ a ∈ c.blocks, 1 ≤ a) := by
  classical
  let P (c : Composition (r * q)) := ∀ a ∈ c.blocks, r ∣ a
  let _ : DecidablePred P := fun _ => Classical.propDecidable _
  change compositionOddMinusEven (r * q) P = _
  simp only [compositionOddMinusEven]
  rw [← Finset.sum_filter (s := Finset.univ) P (fun c => (-1 : ℤ) ^ (c.length + 1)),
    Finset.sum_subtype _ (by simp : ∀ c, c ∈ Finset.univ.filter P ↔ P c)]
  calc
    _ = ∑ c : Composition q, (-1 : ℤ) ^ (c.length + 1) := by
      refine (Fintype.sum_equiv (scaleComposition hr) _ _ fun c => ?_).symm
      change (-1 : ℤ) ^ (c.length + 1) = (-1) ^ ((c.blocks.map (r * ·)).length + 1)
      rw [List.length_map, Composition.length]
    _ = _ := Finset.sum_congr rfl fun c _ =>
      (ite_eq_left (show ∀ a ∈ c.blocks, 1 ≤ a from fun _ ha => c.blocks_pos ha)).symm

private theorem signedCount_minOne {q : ℕ} (hq : 1 ≤ q) :
    compositionOddMinusEven q (fun c => ∀ a ∈ c.blocks, 1 ≤ a) = if q = 1 then 1 else 0 := by
  have hsum : compositionOddMinusEven q (fun c => ∀ a ∈ c.blocks, 1 ≤ a) =
      ∑ j ∈ Finset.range (q - 1 + 1), (-1 : ℤ) ^ j * ((q - 1).choose j : ℤ) := by
    simpa using compositionOddMinusEven_parts_ge 1 q (le_refl 1) hq
  rw [hsum]
  calc
    _ = ((-1 : ℤ) + 1) ^ (q - 1) := by
      simpa only [one_pow, mul_one] using (add_pow (-1 : ℤ) 1 (q - 1)).symm
    _ = _ := by
      by_cases h : q = 1
      · simp [h]
      · simp [h, zero_pow (show q - 1 ≠ 0 by omega)]

/-- **Signed count of residue-class compositions with parts at least $r - s$.** Let $r > s \ge 0$,
let $k = r - s$ and let $n \ge 1$. Among the compositions of $n + k - 1$ whose parts are all at
least $k$ and congruent to $k + s$ modulo $r$, the number with an odd number of parts minus the
number with an even number of parts is $1$ if $n = s + 1$ and $0$ otherwise.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Corollary 12
(`jis-2024-24.6.5-cor-12`). -/
public theorem compositionOddMinusEven_parts_ge_modEq_sub (n r s : ℕ) (hn : 1 ≤ n)
    (hsr : s < r) :
    compositionOddMinusEven (n + (r - s) - 1)
        (fun c => ∀ a ∈ c.blocks, r - s ≤ a ∧ a % r = (r - s + s) % r)
      = if n = s + 1 then 1 else 0 := by
  classical
  have hr : 0 < r := Nat.zero_lt_of_lt hsr
  have hparts (c : Composition (n + (r - s) - 1)) :
      (∀ a ∈ c.blocks, r - s ≤ a ∧ a % r = (r - s + s) % r) ↔
        ∀ a ∈ c.blocks, r ∣ a := by
    simp only [Nat.sub_add_cancel hsr.le, Nat.mod_self, Nat.dvd_iff_mod_eq_zero]
    refine ⟨fun h a ha => (h a ha).2, fun h a ha => ⟨?_, h a ha⟩⟩
    exact (Nat.sub_le r s).trans (Nat.le_of_dvd (c.blocks_pos ha)
      (Nat.dvd_of_mod_eq_zero (h a ha)))
  rw [show (fun c : Composition (n + (r - s) - 1) =>
      ∀ a ∈ c.blocks, r - s ≤ a ∧ a % r = (r - s + s) % r) =
      (fun c => ∀ a ∈ c.blocks, r ∣ a) from funext fun c => propext (hparts c)]
  have htotal : n + (r - s) - 1 = r ↔ n = s + 1 := by omega
  by_cases hdiv : r ∣ n + (r - s) - 1
  · obtain ⟨q, hq⟩ := hdiv
    have hqpos : 1 ≤ q := by
      by_contra! h
      have hzero : q = 0 := by omega
      rw [hzero, Nat.mul_zero] at hq
      omega
    have hqone : q = 1 ↔ n = s + 1 := by
      rw [← htotal, hq]
      exact ⟨fun h => by rw [h, Nat.mul_one], fun h =>
        Nat.eq_of_mul_eq_mul_left hr (h.trans (Nat.mul_one r).symm)⟩
    rw [hq, signedCount_multiples hr, signedCount_minOne hqpos, if_congr hqone rfl rfl]
  · have hne : n ≠ s + 1 := fun h => hdiv ((htotal.mpr h).symm ▸ dvd_rfl)
    rw [ite_eq_right hne, compositionOddMinusEven]
    refine Finset.sum_eq_zero fun c _ => ite_eq_right fun h => hdiv ?_
    simpa only [c.blocks_sum] using List.dvd_sum h

end MetaMathlibExt
