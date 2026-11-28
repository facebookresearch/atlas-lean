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
`exists_word_letterPosition_eq_iff` characterizes which sequences can occur as the positions of
one letter in a word that starts with `true` and in which both letters occur infinitely often
(`BothLettersInfinite`).
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

private theorem infinite_compl_range_iff {f : ℕ → ℕ} (hf : StrictMono f) :
    (Set.range f)ᶜ.Infinite ↔ {i | f i + 1 < f (i + 1)}.Infinite := by
  constructor
  · intro hcompl hfinite
    obtain ⟨N, hN⟩ := hfinite.bddAbove
    -- Once all adjacent gaps are one, the range contains an entire tail.
    have step (k : ℕ) : f (N + 1 + k + 1) = f (N + 1 + k) + 1 := by
      have hlt : f (N + 1 + k) < f (N + 1 + k + 1) := hf (Nat.lt_succ_self _)
      have hgap : ¬ f (N + 1 + k) + 1 < f (N + 1 + k + 1) := by
        intro h
        have hle : N + 1 + k ≤ N := hN h
        omega
      omega
    have tail (k : ℕ) : f (N + 1 + k) = f (N + 1) + k := by
      induction k with
      | zero => simp
      | succ k ih => rw [← Nat.add_assoc (N + 1) k 1, step, ih, Nat.add_assoc]
    apply hcompl ((Set.finite_Iio (f (N + 1))).subset ?_)
    intro m hm
    change m < f (N + 1)
    by_contra! h
    exact hm ⟨N + 1 + (m - f (N + 1)), by rw [tail]; omega⟩
  · intro hgap
    -- Each large gap supplies a distinct missing value, namely f i + 1.
    refine (hgap.image (hf.add_const 1).injective.injOn).mono ?_
    rintro _ ⟨i, hi, rfl⟩ ⟨j, hj⟩
    change f j = f i + 1 at hj
    change f i + 1 < f (i + 1) at hi
    rcases le_or_gt j i with hji | hij
    · have := hf.monotone hji
      omega
    · have hle : f (i + 1) ≤ f j := hf.monotone (Nat.succ_le_of_lt hij)
      omega

private theorem exists_word_letterPosition_eq_iff_aux (p : ℕ → ℕ) (α : Bool) :
    (∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → letterPosition w α n = p n) ↔
      (∀ n, 1 ≤ n → p n < p (n + 1)) ∧ (p 1 = 0 ↔ α = true) ∧
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite := by
  classical
  let f (i : ℕ) := p (i + 1)
  have gap : {i | f i + 1 < f (i + 1)}.Infinite ↔
      {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite := by
    have himage : (fun i : ℕ => i + 1) '' {i | f i + 1 < f (i + 1)} =
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n} := by
      ext n
      constructor
      · rintro ⟨i, hi, rfl⟩
        change p (i + 1) + 1 < p (i + 1 + 1) at hi
        change 1 ≤ i + 1 ∧ 1 < p (i + 1 + 1) - p (i + 1)
        exact ⟨by omega, by omega⟩
      · rintro ⟨hn, hg⟩
        refine ⟨n - 1, ?_, Nat.sub_add_cancel hn⟩
        change p (n - 1 + 1) + 1 < p (n - 1 + 1 + 1)
        rw [Nat.sub_add_cancel hn]
        omega
    rw [← himage, Set.infinite_image_iff (fun _ _ _ _ h => Nat.add_right_cancel h)]
  have zero_mem_range (hf : StrictMono f) : 0 ∈ Set.range f ↔ p 1 = 0 := by
    constructor
    · rintro ⟨i, hi⟩
      have hmin : p 1 ≤ f i := hf.monotone (Nat.zero_le i)
      omega
    · intro h
      exact ⟨0, h⟩
  have compl_occurrences (w : ℕ → Bool) : {i | w i = α}ᶜ = {i | w i = !α} := by
    ext i
    exact Bool.eq_not_iff.symm
  constructor
  · rintro ⟨w, hw, hhead, hpos⟩
    have hinf (b : Bool) : {i | w i = b}.Infinite := by
      cases b
      · exact hw.2
      · exact hw.1
    have hf : f = Nat.nth (fun i => w i = α) := by
      funext i
      simpa only [f, letterPosition, Nat.add_sub_cancel] using (hpos (i + 1) (by omega)).symm
    have hmono : StrictMono f := hf.symm ▸ Nat.nth_strictMono (hinf α)
    have hrange : Set.range f = {i | w i = α} := by
      rw [hf]
      exact Nat.range_nth_of_infinite (hinf α)
    refine ⟨fun n hn => ?_, ?_, gap.mp ((infinite_compl_range_iff hmono).mp ?_)⟩
    · have h : f (n - 1) < f (n - 1 + 1) := hmono (Nat.lt_succ_self _)
      simpa only [f, Nat.sub_add_cancel hn] using h
    · rw [← zero_mem_range hmono, hrange]
      change w 0 = α ↔ α = true
      rw [hhead, eq_comm]
    · rw [hrange, compl_occurrences]
      exact hinf (!α)
  · rintro ⟨hinc, hfirst, hgap⟩
    have hmono : StrictMono f := strictMono_nat_of_lt_succ fun i => hinc (i + 1) (by omega)
    have hrange : (Set.range f).Infinite := Set.infinite_range_of_injective hmono.injective
    have hcompl := (infinite_compl_range_iff hmono).mpr (gap.mpr hgap)
    let w (i : ℕ) := if i ∈ Set.range f then α else !α
    have hocc : {i | w i = α} = Set.range f := by
      ext i
      change (if i ∈ Set.range f then α else !α) = α ↔ i ∈ Set.range f
      by_cases hi : i ∈ Set.range f
      · rw [ite_eq_left hi]
        exact ⟨fun _ => hi, fun _ => rfl⟩
      · rw [ite_eq_right hi, iff_false_intro hi]
        cases α <;> decide
    have hother : {i | w i = !α} = (Set.range f)ᶜ := by
      rw [← compl_occurrences, hocc]
    have hw : BothLettersInfinite w := by
      cases α
      · exact ⟨hother.symm ▸ hcompl, hocc.symm ▸ hrange⟩
      · exact ⟨hocc.symm ▸ hrange, hother.symm ▸ hcompl⟩
    have hw₀ : w 0 = true := by
      have h₀ : w 0 = α ↔ α = true := by
        change 0 ∈ {i | w i = α} ↔ α = true
        rwa [hocc, zero_mem_range hmono]
      cases α
      · exact Bool.eq_true_of_not_eq_false fun hfalse => Bool.false_ne_true (h₀.mp hfalse)
      · exact h₀.mpr rfl
    have hall : (fun i => f i ∈ Set.range f) = (fun _ => True) :=
      funext fun i => propext (iff_true_intro ⟨i, rfl⟩)
    have henum (i : ℕ) : f i = Nat.nth (fun j => j ∈ Set.range f) i := by
      have h := Nat.nth_comp_of_strictMono (n := i) (p := fun j => j ∈ Set.range f)
        hmono (fun _ hj => hj) (fun hf => (hrange hf).elim)
      simpa only [hall, Nat.nth_true] using h
    refine ⟨w, hw, hw₀, fun n hn => ?_⟩
    change Nat.nth (fun i => i ∈ {i | w i = α}) (n - 1) = p n
    rw [hocc, ← henum]
    simp only [f, Nat.sub_add_cancel hn]

/-- **Characterization of the position functions.** Let $p$ be a function from the natural
numbers to the natural numbers. There is an infinite word $w$ over the letters $a$ and $b$ that
starts with $a$, in which both letters occur infinitely often, and whose position function for
$a$ satisfies $p_a(n) = p(n)$ for all $n \ge 1$, if and only if $p(n) < p(n+1)$ for all $n \ge 1$,
$p(1) = 0$, and $p(n+1) - p(n) > 1$ for infinitely many $n \ge 1$. Likewise, there is an infinite
word over $a$ and $b$ that starts with $a$, in which both letters occur infinitely often, and
whose position function for $b$ satisfies $p_b(n) = p(n)$ for all $n \ge 1$, if and only if
$p(n) < p(n+1)$ for all $n \ge 1$, $p(1) > 0$, and $p(n+1) - p(n) > 1$ for infinitely many
$n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 4
(`jis-2025-25.1.5-lem-4`). -/
public theorem exists_word_letterPosition_eq_iff (p : ℕ → ℕ) :
    ((∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → letterPosition w true n = p n) ↔
      (∀ n, 1 ≤ n → p n < p (n + 1)) ∧ p 1 = 0 ∧
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite) ∧
    ((∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → letterPosition w false n = p n) ↔
      (∀ n, 1 ≤ n → p n < p (n + 1)) ∧ 0 < p 1 ∧
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite) := by
  constructor
  · simpa using exists_word_letterPosition_eq_iff_aux p true
  · simpa [Nat.pos_iff_ne_zero] using exists_word_letterPosition_eq_iff_aux p false

end MetaMathlibExt
