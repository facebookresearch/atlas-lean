/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords

/-!
# Reconstructing letter positions in a binary word

`letterPosition_reconstruction` recovers each pair of occurrence positions from the
previously occupied positions and the signed distance between the next two occurrences.
-/

namespace MetaMathlibExt

namespace letterPosition_reconstruction

private theorem sInf_unused {w : ℕ → Bool} (hw : BothLettersInfinite w) (n : ℕ) :
    sInf {m : ℕ | ∀ j, 1 ≤ j → j ≤ n →
      m ≠ letterPosition w true j ∧ m ≠ letterPosition w false j} =
        min (letterPosition w true (n + 1)) (letterPosition w false (n + 1)) := by
  let pos (a : Bool) := Nat.nth (fun i => w i = a)
  have inf (a : Bool) : {i | w i = a}.Infinite := by
    cases a
    · exact hw.2
    · exact hw.1
  have letter (a : Bool) (i : ℕ) : w (pos a i) = a := Nat.nth_mem_of_infinite (inf a) i
  -- An occurrence cannot coincide with an earlier occurrence of either letter.
  have fresh (a b : Bool) {j : ℕ} (hj : j < n) : pos a n ≠ pos b j := by
    intro h
    have hab := (letter a n).symm.trans ((congrArg w h).trans (letter b j))
    subst b
    exact (Nat.nth_strictMono (inf a) hj).ne' h
  simp only [letterPosition, Nat.add_sub_cancel]
  change sInf {m : ℕ | ∀ j, 1 ≤ j → j ≤ n →
    m ≠ pos true (j - 1) ∧ m ≠ pos false (j - 1)} = min (pos true n) (pos false n)
  apply IsLeast.csInf_eq
  constructor
  · intro j hj hjn
    rcases min_choice (pos true n) (pos false n) with h | h <;>
      rw [h] <;> exact ⟨fresh _ _ (by omega), fresh _ _ (by omega)⟩
  · intro m hm
    -- Write m as occurrence i of its own letter. If m is unused, then i ≥ n.
    obtain ⟨i, hi⟩ := Nat.subset_range_nth (p := fun j => w j = w m) (a := m) rfl
    change pos (w m) i = m at hi
    have hni : n ≤ i := by
      by_contra! hlt
      have prev := hm (i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at prev
      cases h : w m with
      | false => exact prev.2 (h ▸ hi).symm
      | true => exact prev.1 (h ▸ hi).symm
    have hle : pos (w m) n ≤ m := (Nat.nth_monotone (inf (w m)) hni).trans_eq hi
    cases h : w m with
    | false => exact (min_le_right _ _).trans (h ▸ hle)
    | true => exact (min_le_left _ _).trans (h ▸ hle)

end letterPosition_reconstruction

/-- **Reconstruction of a binary word from its relative position function.** Let $w$ be an
infinite binary word over $\{a, b\}$ in which both letters occur infinitely often, let $p_a(n)$
and $p_b(n)$ be the positions (counted from $0$) of the $n$-th $a$ and the $n$-th $b$ in $w$, and
let $r(n) = p_b(n) - p_a(n)$. If $r(1) > 0$ then $p_a(1) = 0$ and $p_b(1) = r(1)$; if $r(1) < 0$
then $p_a(1) = -r(1)$ and $p_b(1) = 0$. For every $n \ge 1$, let $k_{n+1}$ be the least natural
number different from all of $p_a(1), \dots, p_a(n), p_b(1), \dots, p_b(n)$. If $r(n+1) > 0$ then
$p_a(n+1) = k_{n+1}$ and $p_b(n+1) = k_{n+1} + r(n+1)$; if $r(n+1) < 0$ then
$p_a(n+1) = k_{n+1} - r(n+1)$ and $p_b(n+1) = k_{n+1}$.

The paper states this as an algorithm; here its output is stated as equalities with the true
positions. Since $r(1) \ne 0$, the paper's "otherwise" in the first step is the case $r(1) < 0$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 6
(`jis-2025-25.1.5-lem-6`). -/
public theorem letterPosition_reconstruction {w : ℕ → Bool} (hw : BothLettersInfinite w) :
    let pa := fun n => (letterPosition w true n : ℤ)
    let pb := fun n => (letterPosition w false n : ℤ)
    let r := relativePosition w
    (0 < r 1 → pa 1 = 0 ∧ pb 1 = r 1) ∧ (r 1 < 0 → pa 1 = -r 1 ∧ pb 1 = 0) ∧
      ∀ n, 1 ≤ n →
        let k : ℤ := ((sInf {m : ℕ | ∀ j, 1 ≤ j → j ≤ n →
          (m : ℤ) ≠ pa j ∧ (m : ℤ) ≠ pb j} : ℕ) : ℤ)
        (0 < r (n + 1) → pa (n + 1) = k ∧ pb (n + 1) = k + r (n + 1)) ∧
          (r (n + 1) < 0 → pa (n + 1) = k - r (n + 1) ∧ pb (n + 1) = k) := by
  simp only [relativePosition, ne_eq, Int.natCast_inj, letterPosition_reconstruction.sInf_unused hw]
  have first : letterPosition w true 1 = 0 ∨ letterPosition w false 1 = 0 := by
    cases h : w 0 with
    | false => exact Or.inr (letterPosition_one_of_head h)
    | true => exact Or.inl (letterPosition_one_of_head h)
  refine ⟨?_, ?_, fun n _ => ?_⟩ <;> omega

end MetaMathlibExt
