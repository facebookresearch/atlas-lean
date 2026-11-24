/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bollobás's set-pairs inequality

Let `(A i, B i)`, `i ∈ s`, be pairs of finite sets with `A i ∩ B i = ∅` and `A i ∩ B j ≠ ∅` for
`i ≠ j`. Bollobás (1965) proved that `∑ i, 1 / C(|A i| + |B i|, |A i|) ≤ 1`.

The proof here is the standard induction on a ground set `X` containing every set: for `x ∈ X`
keep the pairs with `x ∉ A i` and erase `x` from their `B i`; this is again a set-pair system on
`X \ {x}`, and summing the induction hypothesis over `x ∈ X` gives `|X|` times the claimed sum.

Main results:
* `sum_inv_choose_le_one`: the inequality.
* `card_le_choose`: the uniform case, `|s| ≤ C(a + b, a)` when `|A i| = a`, `|B i| = b`.
* `lym_of_sum_inv_choose_le_one`: taking `B i` to be the complement of `A i` recovers the
  Lubell–Yamamoto–Meshalkin inequality `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`
  of Mathlib.

Reference: B. Bollobás, "On generalized graphs", *Acta Math. Acad. Sci. Hungar.* 16 (1965)
447–452; statement as Theorem 1 of J. O'Neill and J. Verstraëte, "A generalization of the Bollobás
set pairs inequality", arXiv:1812.00537v2 (2020).
-/

@[expose] public section

open Finset

namespace MathlibExt.Combinatorics.SetFamily.BollobasSetPairs

variable {𝕜 α ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

-- The weight of a pair of sizes `a`, `b`: `C(a + b, a)⁻¹`.
private noncomputable def wt (𝕜 : Type*) [Field 𝕜] (a b : ℕ) : 𝕜 := (((a + b).choose a : ℕ) : 𝕜)⁻¹

private lemma choose_pos' (a b : ℕ) : (0 : 𝕜) < (((a + b).choose a : ℕ) : 𝕜) := by
  exact_mod_cast Nat.choose_pos (Nat.le_add_right a b)

-- `b · C(a + b - 1, a)⁻¹ = (a + b) · C(a + b, a)⁻¹` for `b = b' + 1`.
private lemma succ_mul_wt (a b' : ℕ) :
    ((b' + 1 : ℕ) : 𝕜) * wt 𝕜 a b' = ((a + (b' + 1) : ℕ) : 𝕜) * wt 𝕜 a (b' + 1) := by
  have h := Nat.choose_mul_succ_eq (a + b') a
  have h1 : a + b' + 1 - a = b' + 1 := by omega
  rw [h1, show a + b' + 1 = a + (b' + 1) by omega] at h
  have h' : (((a + b').choose a : ℕ) : 𝕜) * ((a + (b' + 1) : ℕ) : 𝕜) =
      (((a + (b' + 1)).choose a : ℕ) : 𝕜) * ((b' + 1 : ℕ) : 𝕜) := by
    exact_mod_cast h
  have p1 := choose_pos' (𝕜 := 𝕜) a b'
  have p2 := choose_pos' (𝕜 := 𝕜) a (b' + 1)
  unfold wt
  field_simp
  linarith [h']

-- The inner sum of the double counting: for `A, B ⊆ X` disjoint with `B` nonempty,
-- `∑_{x ∈ X \ A} C(|A| + |B \ {x}|, |A|)⁻¹ = |X| · C(|A| + |B|, |A|)⁻¹`.
private lemma sum_wt_erase [DecidableEq α] (X A B : Finset α) (hA : A ⊆ X) (hB : B ⊆ X)
    (hAB : Disjoint A B) (hBne : B.Nonempty) :
    ∑ x ∈ X \ A, wt 𝕜 #A #(B.erase x) = (#X : 𝕜) * wt 𝕜 #A #B := by
  obtain ⟨b', hb'⟩ : ∃ b', #B = b' + 1 := ⟨#B - 1, by have := hBne.card_pos; omega⟩
  have hterm : ∀ x ∈ X \ A,
      wt 𝕜 #A #(B.erase x) = if x ∈ B then wt 𝕜 #A b' else wt 𝕜 #A #B := by
    intro x _
    split_ifs with hx
    · rw [card_erase_of_mem hx, hb']; rfl
    · rw [erase_eq_of_notMem hx]
  rw [sum_congr rfl hterm, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hfil : (X \ A).filter (· ∈ B) = B := by
    ext x
    simp only [mem_filter, mem_sdiff]
    exact ⟨fun h => h.2, fun h => ⟨⟨hB h, fun ha => disjoint_left.1 hAB ha h⟩, h⟩⟩
  have hcount : #((X \ A).filter (· ∉ B)) + #B + #A = #X := by
    have h1 := card_filter_add_card_filter_not (s := X \ A) (fun x => x ∈ B)
    rw [hfil] at h1
    have h2 := card_sdiff_add_card_eq_card hA
    omega
  rw [hfil]
  have key := succ_mul_wt (𝕜 := 𝕜) #A b'
  rw [← hb'] at key
  rw [key, ← hcount]
  push_cast
  ring

-- The set-pairs inequality on a fixed ground set `X`, by induction on `|X|`.
private lemma sum_wt_le_one_aux (n : ℕ) :
    ∀ (X : Finset α), #X = n → ∀ (s : Finset ι) (A B : ι → Finset α),
      (∀ i ∈ s, A i ⊆ X) → (∀ i ∈ s, B i ⊆ X) →
      (∀ i ∈ s, Disjoint (A i) (B i)) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) →
      ∑ i ∈ s, wt 𝕜 #(A i) #(B i) ≤ 1 := by
  classical
  -- if some `B i` is empty, then `s ⊆ {i}`
  have trivial_case : ∀ (s : Finset ι) (A B : ι → Finset α),
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) →
      ∀ i ∈ s, B i = ∅ → ∑ i ∈ s, wt 𝕜 #(A i) #(B i) ≤ 1 := by
    intro s A B hcross i hi hBi
    have hs : s = {i} := by
      refine eq_singleton_iff_unique_mem.2 ⟨hi, fun j hj => ?_⟩
      by_contra hji
      exact hcross j hj i hi hji (by rw [hBi]; exact disjoint_empty_right _)
    rw [hs, sum_singleton, hBi, card_empty]
    simp [wt]
  induction n with
  | zero =>
    intro X hX s A B hA hB _ hcross
    rw [card_eq_zero] at hX
    subst hX
    rcases s.eq_empty_or_nonempty with hs | ⟨i, hi⟩
    · simp [hs]
    · exact trivial_case s A B hcross i hi (subset_empty.1 (hB i hi))
  | succ n ih =>
    intro X hX s A B hA hB hdisj hcross
    by_cases hemp : ∃ i ∈ s, B i = ∅
    · obtain ⟨i, hi, hBi⟩ := hemp
      exact trivial_case s A B hcross i hi hBi
    push Not at hemp
    -- induction hypothesis applied at every point `x ∈ X`
    have hx : ∀ x ∈ X, ∑ i ∈ s.filter (fun i => x ∉ A i),
        wt 𝕜 #(A i) #((B i).erase x) ≤ 1 := by
      intro x hxX
      refine ih (X.erase x) (by rw [card_erase_of_mem hxX, hX]; rfl)
        (s.filter (fun i => x ∉ A i)) A (fun i => (B i).erase x) ?_ ?_ ?_ ?_
      · intro i hi
        rw [mem_filter] at hi
        intro y hy
        exact mem_erase.2 ⟨fun h => hi.2 (h ▸ hy), hA i hi.1 hy⟩
      · intro i hi
        exact erase_subset_erase x (hB i (mem_filter.1 hi).1)
      · intro i hi
        exact (hdisj i (mem_filter.1 hi).1).mono_right (erase_subset _ _)
      · intro i hi j hj hij hd
        rw [mem_filter] at hi hj
        refine hcross i hi.1 j hj.1 hij ?_
        rw [disjoint_left] at hd ⊢
        intro y hyA hyB
        refine hd hyA (mem_erase.2 ⟨?_, hyB⟩)
        rintro rfl
        exact hi.2 hyA
    have hsum : ∑ x ∈ X, ∑ i ∈ s.filter (fun i => x ∉ A i),
        wt 𝕜 #(A i) #((B i).erase x) ≤ (#X : 𝕜) := by
      calc _ ≤ ∑ _x ∈ X, (1 : 𝕜) := sum_le_sum hx
        _ = (#X : 𝕜) := by simp
    have hswap : ∑ x ∈ X, ∑ i ∈ s.filter (fun i => x ∉ A i),
        wt 𝕜 #(A i) #((B i).erase x) =
          ∑ i ∈ s, ∑ x ∈ X \ A i, wt 𝕜 #(A i) #((B i).erase x) := by
      refine sum_comm' ?_
      intro x i
      simp only [mem_filter, mem_sdiff]
      tauto
    have hinner : ∑ i ∈ s, ∑ x ∈ X \ A i, wt 𝕜 #(A i) #((B i).erase x) =
        (#X : 𝕜) * ∑ i ∈ s, wt 𝕜 #(A i) #(B i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      exact sum_wt_erase X (A i) (B i) (hA i hi) (hB i hi) (hdisj i hi)
        (hemp i hi)
    rw [hswap, hinner] at hsum
    have hXpos : (0 : 𝕜) < (#X : 𝕜) := by rw [hX]; exact_mod_cast Nat.succ_pos n
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left hlt hXpos
    linarith

/-- **Bollobás's set-pairs inequality.** If `A i ∩ B i = ∅` for every `i ∈ s` and
`A i ∩ B j ≠ ∅` for all distinct `i, j ∈ s`, then
`∑_{i ∈ s} C(|A i| + |B i|, |A i|)⁻¹ ≤ 1` (B. Bollobás, "On generalized graphs", *Acta Math.
Acad. Sci. Hungar.* 16 (1965); stated as Theorem 1 of O'Neill–Verstraëte, arXiv:1812.00537v2). -/
theorem sum_inv_choose_le_one (s : Finset ι) (A B : ι → Finset α)
    (hdisj : ∀ i ∈ s, Disjoint (A i) (B i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : 𝕜)⁻¹ ≤ 1 := by
  classical
  have h := sum_wt_le_one_aux (𝕜 := 𝕜) _ (s.biUnion fun i => A i ∪ B i) rfl s A B
    (fun i hi => subset_union_left.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi))
    (fun i hi => subset_union_right.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi))
    hdisj hcross
  simpa [wt] using h

/-- **Uniform set-pairs inequality.** If moreover `|A i| = a` and `|B i| = b` for every `i ∈ s`,
then `|s| ≤ C(a + b, a)`; equality holds for the pairs `(A, X \ A)` with `A` ranging over the
`a`-subsets of an `(a + b)`-set `X` (O'Neill–Verstraëte, arXiv:1812.00537v2, discussion after
Theorem 1). -/
theorem card_le_choose (s : Finset ι) (A B : ι → Finset α) (a b : ℕ)
    (hA : ∀ i ∈ s, #(A i) = a) (hB : ∀ i ∈ s, #(B i) = b)
    (hdisj : ∀ i ∈ s, Disjoint (A i) (B i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    #s ≤ (a + b).choose a := by
  have h := sum_inv_choose_le_one (𝕜 := ℚ) s A B hdisj hcross
  rw [sum_congr rfl (fun i hi => by rw [hA i hi, hB i hi]), sum_const, nsmul_eq_mul] at h
  have hpos : (0 : ℚ) < ((a + b).choose a : ℚ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right a b)
  rw [mul_inv_le_iff₀ hpos, one_mul] at h
  exact_mod_cast h

/-- **The LYM inequality from the set-pairs inequality.** For an antichain `𝒜` of subsets of a
finite type `α`, the pairs `(S, Sᶜ)`, `S ∈ 𝒜`, form a set-pair system, and
`sum_inv_choose_le_one` gives `∑_{S ∈ 𝒜} C(|α|, |S|)⁻¹ ≤ 1`, the statement of Mathlib's
`Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose` (B. Bollobás, 1965; see the
discussion after Theorem 1 of O'Neill–Verstraëte, arXiv:1812.00537v2). -/
theorem lym_of_sum_inv_choose_le_one [Fintype α] {𝒜 : Finset (Finset α)}
    (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    ∑ S ∈ 𝒜, ((Fintype.card α).choose #S : 𝕜)⁻¹ ≤ 1 := by
  classical
  have h := sum_inv_choose_le_one (𝕜 := 𝕜) 𝒜 id (fun S => Sᶜ)
    (fun S _ => disjoint_compl_right)
    (fun S hS T hT hST hd => by
      have : S ⊆ T := by
        intro x hx
        by_contra hxT
        exact disjoint_left.1 hd hx (mem_compl.2 hxT)
      exact h𝒜 hS hT hST this)
  refine le_of_eq_of_le (sum_congr rfl fun S _ => ?_) h
  simp [card_compl, Nat.add_sub_cancel' (card_le_univ S)]

end MathlibExt.Combinatorics.SetFamily.BollobasSetPairs
