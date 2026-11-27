/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.KeywordSubstitutionClasses

/-!
# Keyword symmetries of the substitution graph

Negating the keyword preserves the substitution graph. Reversing or seminegating
every word gives an isomorphism to the graph of the transformed keyword.
-/

namespace MetaMathlibExt
namespace keywordGraph_neg_rev_seminegation

-- An involution on words gives a graph isomorphism if it sends each applicable
-- substitution to a substitution for the transformed keyword.
private theorem iso_of_involution {m n : ℕ}
    (f : ∀ {k : ℕ}, (Fin k → Bool) → Fin k → Bool)
    (inv : ∀ {k : ℕ}, Function.Involutive (@f k))
    (step : ∀ (a : Fin (m + 1) → Bool) (i : ℕ) (u : Fin n → Bool),
      KeywordApplicable a i u →
        ∃ j, keywordSimpleMap (f a) j (f u) = f (keywordSimpleMap a i u))
    (a : Fin (m + 1) → Bool) :
    Nonempty (keywordGraph a n ≃g keywordGraph (f a) n) := by
  have maps (b : Fin (m + 1) → Bool) {u v : Fin n → Bool}
      (h : (keywordGraph b n).Adj u v) : (keywordGraph (f b) n).Adj (f u) (f v) := by
    have forward {x y : Fin n → Bool} (hne : x ≠ y) (i : ℕ) (hi : keywordSimpleMap b i x = y) :
        ∃ j, keywordSimpleMap (f b) j (f x) = f y := by
      have ha : KeywordApplicable b i x := by
        by_contra h
        exact hne ((keywordSimpleMap_of_not_applicable b i x h).symm.trans hi)
      rw [← hi]
      exact step b i x ha
    obtain ⟨hne, hstep⟩ := (keywordGraph_adj ..).mp h
    apply (keywordGraph_adj ..).mpr
    refine ⟨inv.injective.ne hne, ?_⟩
    rcases hstep with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl (forward hne i hi)
    · exact Or.inr (forward hne.symm i hi)
  refine ⟨{ toEquiv := inv.toPerm f, map_rel_iff' := ?_ }⟩
  intro u v
  change (keywordGraph (f a) n).Adj (f u) (f v) ↔ (keywordGraph a n).Adj u v
  exact ⟨fun h => by simpa only [inv a, inv u, inv v] using maps (f a) h, maps a⟩

private def reverseWord {k : ℕ} (u : Fin k → Bool) (j : Fin k) := u j.rev

private theorem reverse_step {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) (ha : KeywordApplicable a i u) :
    ∃ j, keywordSimpleMap (reverseWord a) j (reverseWord u) =
      reverseWord (keywordSimpleMap a i u) := by
  obtain ⟨hi, matchWindow⟩ := ha
  let j := n - (i + m + 1)
  have hj : j + m < n := by dsimp [j]; omega
  have bound {s : ℕ} (hs : s + m < n) (t : Fin (m + 1)) : s + t < n :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_of_lt_succ t.isLt) s) hs
  -- Offset t in the reflected window came from offset t.rev in the original window.
  have index (t : Fin (m + 1)) :
      (⟨j + t, bound hj t⟩ : Fin n).rev = ⟨i + t.rev, bound hi t.rev⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev, j]
    have := t.isLt
    omega
  have hb : KeywordApplicable (reverseWord a) j (reverseWord u) := by
    refine ⟨hj, ?_⟩
    rcases matchWindow with h | h
    · exact Or.inl fun t => by simpa only [reverseWord, index] using h t.rev
    · exact Or.inr fun t => by simpa only [reverseWord, index] using h t.rev
  refine ⟨j, ?_⟩
  funext k
  rw [keywordSimpleMap_apply_of_applicable _ _ _ hb]
  unfold reverseWord
  rw [keywordSimpleMap_apply_of_applicable _ _ _ ⟨hi, matchWindow⟩]
  have window : (j ≤ k.val ∧ k.val ≤ j + m) ↔ (i ≤ k.rev.val ∧ k.rev.val ≤ i + m) := by
    simp only [j, Fin.val_rev]
    have := k.isLt
    omega
  simp only [window]

private def flipAt (i : ℕ) (b : Bool) := if i % 2 = 0 then b else !b

private theorem flipAt_not (i : ℕ) (b : Bool) : flipAt i (!b) = !flipAt i b := by
  unfold flipAt
  split <;> rfl

private theorem flipAt_add (i t : ℕ) (b : Bool) :
    flipAt (i + t) b = flipAt i (flipAt t b) := by
  unfold flipAt
  split_ifs <;> first | rfl | exact (Bool.not_not _).symm | omega

private def semi {k : ℕ} (u : Fin k → Bool) (j : Fin k) := flipAt j.val (u j)

private theorem semi_step {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) (ha : KeywordApplicable a i u) :
    ∃ j, keywordSimpleMap (semi a) j (semi u) = semi (keywordSimpleMap a i u) := by
  have hb : KeywordApplicable (semi a) i (semi u) := by
    obtain ⟨hi, matchWindow⟩ := ha
    refine ⟨hi, ?_⟩
    -- An odd starting index exchanges a keyword match with a complement match.
    by_cases evenStart : i % 2 = 0
    · rcases matchWindow with h | h
      · exact Or.inl fun t => by
          simp only [semi, flipAt_add, h t]
          simp [flipAt, evenStart]
      · exact Or.inr fun t => by
          simp only [semi, flipAt_add, h t, flipAt_not]
          simp [flipAt, evenStart]
    · rcases matchWindow with h | h
      · exact Or.inr fun t => by
          simp only [semi, flipAt_add, h t]
          simp [flipAt, evenStart]
      · exact Or.inl fun t => by
          simp only [semi, flipAt_add, h t, flipAt_not]
          simp [flipAt, evenStart]
  refine ⟨i, ?_⟩
  funext k
  rw [keywordSimpleMap_apply_of_applicable _ _ _ hb]
  unfold semi
  rw [keywordSimpleMap_apply_of_applicable _ _ _ ha]
  split <;> simp [flipAt_not]

end keywordGraph_neg_rev_seminegation

open keywordGraph_neg_rev_seminegation in
/-- **Keyword symmetries of the substitution graph.** Let $a = a_0 a_1 \cdots a_m$ be a keyword of
length $m + 1$ and let $n \ge 0$. Write $\neg a$ for the letterwise negation of $a$,
$\rho(a) = a_m a_{m-1} \cdots a_0$ for its reversal, and $\bar a$ for its seminegation, which keeps
$a_t$ for even $t$ and negates $a_t$ for odd $t$. Then the substitution graphs satisfy
$\mathcal{G}_n^{(a)} = \mathcal{G}_n^{(\neg a)}$, and $\mathcal{G}_n^{(a)}$ is isomorphic both to
$\mathcal{G}_n^{(\rho(a))}$ and to $\mathcal{G}_n^{(\bar a)}$.

In the paper's numbering, which counts letters from $1$, the seminegation negates the letters in
even positions. The paper states this for $n \ge 1$; it also holds at $n = 0$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 15
(`jis-2025-25.6.6-prop-15`). -/
public theorem keywordGraph_neg_rev_seminegation {m : ℕ} (a : Fin (m + 1) → Bool)
    (n : ℕ) :
    keywordGraph a n = keywordGraph (fun t => !a t) n ∧
      Nonempty (keywordGraph a n ≃g keywordGraph (fun t => a t.rev) n) ∧
      Nonempty (keywordGraph a n ≃g
        keywordGraph (fun t => if t.val % 2 = 0 then a t else !a t) n) := by
  refine ⟨?_, iso_of_involution reverseWord ?_ reverse_step a,
    iso_of_involution semi ?_ semi_step a⟩
  · have app (i : ℕ) (u : Fin n → Bool) :
        KeywordApplicable (fun t => !a t) i u ↔ KeywordApplicable a i u := by
      simp only [KeywordApplicable, Bool.not_not, or_comm]
    have step (i : ℕ) (u : Fin n → Bool) :
        keywordSimpleMap (fun t => !a t) i u = keywordSimpleMap a i u := by
      by_cases h : KeywordApplicable a i u
      · simp only [keywordSimpleMap, (app i u).mpr h, h, ite_true]
      · simp only [keywordSimpleMap, (app i u).not.mpr h, h, ite_false]
    simp only [keywordGraph, step]
  · intro k u
    funext j
    simp [reverseWord]
  · intro k u
    funext j
    simp only [semi, flipAt]
    split <;> simp

end MetaMathlibExt
