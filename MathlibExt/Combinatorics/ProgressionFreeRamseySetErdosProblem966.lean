/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AP.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Progression-free sets that are Ramsey for shorter progressions (Erdős Problem 966)

We prove `progressionFreeRamseySet_holds`: for all `k, r ≥ 2` there is a set `A ⊆ ℕ` that
contains no arithmetic progression of `k + 1` distinct terms, yet every `r`-colouring of `A` has
a monochromatic arithmetic progression of `k` distinct terms.

## Proof outline

By the Hales–Jewett theorem (`Combinatorics.Line.exists_mono_in_high_dimension`) there is a
dimension `n` such that every `r`-colouring of the words of length `n` over the alphabet
`{0, …, k - 1}` has a monochromatic combinatorial line. Read each word as the base-`k ^ 2` digits
of a natural number (`Behrend.map`) and let `A` be the set of these numbers.

* A combinatorial line becomes the progression `a, a + d, …, a + (k - 1) d`, where `d ≠ 0` is the
  sum of the powers of `k ^ 2` over the moving coordinates. Colouring a word by the colour of its
  number therefore gives a monochromatic progression of `k` distinct terms in `A`.
* If `a, a + d, …, a + k d` lie in `A` with words `w₀, w₁, …, w_k`, then
  `(a + k d) + (k - 1) a = k (a + d)`. Every digit of both sides is at most `k (k - 1) < k ^ 2`,
  so there are no carries and `w_k i + (k - 1) w₀ i = k w₁ i` for every coordinate `i`, that is,
  `w_k i - w₀ i = k (w₁ i - w₀ i)`. As all digits are below `k`, this forces `w₁ i = w₀ i`, hence
  `d = 0`, and the progression has a single term instead of `k + 1`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ProgressionFreeRamseySetErdosProblem966Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #966, https://www.erdosproblems.com/966 (status PROVED
(LEAN)). UnsolvedMath record UM-30007103 (`EP-966`), dataset ulamai/UnsolvedMath v1.8.0.

Non-trivial progressions have distinct terms: MathlibExt's `Set.IsAPOfLength t l` requires `t` to
have exactly `l` elements, and `Set.IsAPOfLengthFree A l` says that `A` contains no such `t`. An
`r`-colouring of `A` is a function `ℕ → Fin r` (its values off `A` are irrelevant). Compared with
the formal-conjectures statement `ErdosProblems/966.lean` (equivalent; no code imported).
-/

/-- **Erdős Problem 966: progression-free sets that are Ramsey for shorter progressions.** This
is the statement that for all natural numbers $k \ge 2$ and $r \ge 2$ there is a set $A$ of
natural numbers that contains no arithmetic progression of $k + 1$ distinct terms and such that
for every colouring $c$ of the natural numbers with $r$ colours there are a subset
$t \subseteq A$ that is an arithmetic progression of $k$ distinct terms and a colour $i$ with
$c(x) = i$ for every $x \in t$.

Only the colours of elements of $A$ matter, so the colouring condition says that every
colouring of $A$ with $r$ colours has a monochromatic progression of $k$ distinct terms. -/
def progressionFreeRamseySet : Prop :=
  ∀ k r : ℕ, 2 ≤ k → 2 ≤ r → ∃ A : Set ℕ, A.IsAPOfLengthFree (k + 1) ∧
    ∀ c : ℕ → Fin r, ∃ t ⊆ A, t.IsAPOfLength k ∧ ∃ i : Fin r, ∀ x ∈ t, c x = i

/-- The natural number whose base-`k ^ 2` digits are the letters of a word `w` of length `n` over
the alphabet `{0, …, k - 1}`, least significant digit first. -/
private def wordValue {n k : ℕ} (w : Fin n → Fin k) : ℕ :=
  Behrend.map (k ^ 2) fun i => (w i : ℕ)

/-- The numbers with at most `n` digits in base `k ^ 2`, all of them below `k`, contain no
arithmetic progression of `k + 1` distinct terms. -/
private theorem isAPOfLengthFree_range_wordValue {n k : ℕ} (hk : 2 ≤ k) :
    (Set.range (wordValue : (Fin n → Fin k) → ℕ)).IsAPOfLengthFree (k + 1) := by
  rintro t hts ⟨a, d, hcard, rfl⟩
  exfalso
  have mem : ∀ j ≤ k, ∃ w : Fin n → Fin k, wordValue w = a + j * d := by
    intro j hj
    obtain ⟨w, hw⟩ := hts ⟨j, by exact_mod_cast Nat.lt_succ_of_le hj, rfl⟩
    exact ⟨w, by rw [hw, smul_eq_mul]⟩
  -- The progression has `k + 1 ≥ 3` distinct terms, so its difference is not zero.
  have hd : d ≠ 0 := by
    rintro rfl
    have hset : {x | ∃ m : ℕ, ∃ (_ : (m : ℕ∞) < k + 1), a + m • 0 = x} = {a} := by
      ext x
      simp only [smul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, _, hx⟩ => hx.symm, fun hx => ⟨0, by simp, hx.symm⟩⟩
    rw [hset, ENat.card_coe_set_eq, Set.encard_singleton] at hcard
    have hk1 : ((k + 1 : ℕ) : ℕ∞) = (1 : ℕ) := by exact_mod_cast hcard.symm
    have := Nat.cast_injective hk1
    omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w₀, h₀⟩ := mem 0 (Nat.zero_le _)
  obtain ⟨w₁, h₁⟩ := mem 1 (by omega)
  obtain ⟨w₂, h₂⟩ := mem (m + 1) le_rfl
  -- `(a + (m + 1) d) + m a = (m + 1) (a + d)` holds digit by digit, as there are no carries.
  have key : (fun i => (w₂ i : ℕ)) + m • (fun i => (w₀ i : ℕ)) =
      (m + 1) • fun i => (w₁ i : ℕ) := by
    refine Behrend.map_injOn (d := (m + 1) ^ 2) (fun i => ?_) (fun i => ?_) ?_
    · have h0 := (w₀ i).isLt
      have h2 := (w₂ i).isLt
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · have h1 := (w₁ i).isLt
      simp only [Pi.smul_apply, smul_eq_mul]
      nlinarith
    · change Behrend.map _ (_ + _) = Behrend.map _ _
      rw [map_add, map_nsmul, map_nsmul]
      change wordValue w₂ + m • wordValue w₀ = (m + 1) • wordValue w₁
      rw [h₀, h₁, h₂, smul_eq_mul, smul_eq_mul]
      ring
  -- All digits are below `m + 1`, so the digits of `a` and `a + d` agree.
  have hw : (fun i => (w₁ i : ℕ)) = fun i => (w₀ i : ℕ) := by
    funext i
    have hi := congr_fun key i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have h0 := (w₀ i).isLt
    have h1 := (w₁ i).isLt
    have h2 := (w₂ i).isLt
    rcases lt_trichotomy (w₁ i : ℕ) (w₀ i) with h | h | h
    · nlinarith [Nat.mul_le_mul_left (m + 1) (Nat.succ_le_of_lt h)]
    · exact h
    · nlinarith [Nat.mul_le_mul_left (m + 1) (Nat.succ_le_of_lt h)]
  have had : a + 1 * d = a + 0 * d := by
    rw [← h₀, ← h₁]
    simp only [wordValue, hw]
  exact hd (by simpa using had)

/-- Every `r`-colouring of the natural numbers has a monochromatic arithmetic progression of `k`
distinct terms among the numbers whose base-`k ^ 2` digits are the letters of the words of some
fixed length over `{0, …, k - 1}`. -/
private theorem exists_mono_isAPOfLength {k r : ℕ} (hk : 2 ≤ k) :
    ∃ n : ℕ, ∀ c : ℕ → Fin r, ∃ t ⊆ Set.range (wordValue : (Fin n → Fin k) → ℕ),
      t.IsAPOfLength k ∧ ∃ i : Fin r, ∀ x ∈ t, c x = i := by
  obtain ⟨ι, _, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun c => ?_⟩
  obtain ⟨l, i, hl⟩ := hι fun w => c (wordValue (w ∘ e.symm))
  -- The fixed letters of the line, and the indicator of its moving coordinates.
  let b : Fin (Fintype.card ι) → ℕ := fun j => (l.idxFun (e.symm j)).elim 0 fun y => (y : ℕ)
  let u : Fin (Fintype.card ι) → ℕ := fun j => (l.idxFun (e.symm j)).elim 1 fun _ => 0
  have hpt : ∀ x : Fin k,
      wordValue (l x ∘ e.symm) = Behrend.map (k ^ 2) b + (x : ℕ) * Behrend.map (k ^ 2) u := by
    intro x
    have hx : (fun j => ((l x ∘ e.symm) j : ℕ)) = b + (x : ℕ) • u := by
      funext j
      simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, b, u]
      cases h : l.idxFun (e.symm j) <;> simp [h]
    simp only [wordValue, hx, map_add, map_nsmul, smul_eq_mul]
  -- The line moves in at least one coordinate, so the common difference is not zero.
  have hu : Behrend.map (k ^ 2) u ≠ 0 := by
    obtain ⟨j₀, hj₀⟩ := l.proper
    intro h0
    have hu0 : u = 0 := by
      refine Behrend.map_injOn (d := k ^ 2) (fun j => ?_) (fun j => ?_) (by rw [h0, map_zero])
      · have hk2 : 1 < k ^ 2 := by nlinarith
        simp only [u]
        cases l.idxFun (e.symm j) <;> simp <;> omega
      · simp only [Pi.zero_apply]
        positivity
    have := congr_fun hu0 (e j₀)
    simp [u, hj₀] at this
  refine ⟨Set.range fun x : Fin k => wordValue (l x ∘ e.symm), ?_,
    ⟨Behrend.map (k ^ 2) b, Behrend.map (k ^ 2) u, ?_, ?_⟩, i, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · have hinj : Function.Injective fun x : Fin k => wordValue (l x ∘ e.symm) := by
      intro x y hxy
      simp only [hpt] at hxy
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hu) (Nat.add_left_cancel hxy))
    rw [ENat.card_coe_set_eq, hinj.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by exact_mod_cast x.isLt, by rw [smul_eq_mul]; exact (hpt x).symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, by exact_mod_cast hm⟩, by rw [smul_eq_mul]; exact hpt _⟩
  · rintro _ ⟨x, rfl⟩
    exact hl x

/--
**Erdős Problem 966 holds.** For all natural numbers $k \ge 2$ and $r \ge 2$ there is a set $A$
of natural numbers that contains no arithmetic progression of $k + 1$ distinct terms and such
that for every colouring $c$ of the natural numbers with $r$ colours there are a subset
$t \subseteq A$ that is an arithmetic progression of $k$ distinct terms and a colour $i$ with
$c(x) = i$ for every $x \in t$.

Source: T. F. Bloom, Erdős
Problems, Problem #966, https://www.erdosproblems.com/966 (status PROVED (LEAN)); resolution: formal
proof linked from erdosproblems.com/966 (found with Aristotle, posted in the comment thread); P.
Erdős, Problems and results in combinatorial number theory (1975), 295-310, reports that Spencer had
shown that such a sequence exists, erdosproblems.com/966 status 'proved (Lean)'; formal proof cited
by formal-conjectures ErdosProblems/966.lean,
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos966.lean.
-/
theorem progressionFreeRamseySet_holds : progressionFreeRamseySet := by
  intro k r hk _
  obtain ⟨n, hn⟩ := exists_mono_isAPOfLength (r := r) hk
  exact ⟨_, isAPOfLengthFree_range_wordValue (n := n) hk, hn⟩

end MathlibExt.Combinatorics.ProgressionFreeRamseySetErdosProblem966Wanted
