/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.List.TFAE
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Stream.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Topology.Instances.EReal.Lemmas
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse
public import MathlibExt.Combinatorics.Words.EquilibriousWord

/-!
# Relative position in binary words (Coons–Ramsey–Strungaru)

Statements from Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position
in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5
(arXiv:2410.12173, TeX source read for the definitions).

Conventions. An infinite binary word `w = ℓ₀ ℓ₁ ℓ₂ ⋯` is a function `ℕ → Bool`, with the
letter `a` encoded as `true` and `b` as `false`. The paper's `𝒲` (both letters occur
infinitely often) is `BothLettersInfinite`, and `a𝒲` adds `w 0 = true`. The paper's
functions on `ℕ = {1, 2, …}` are functions `ℕ → _` used only at `n ≥ 1`; the difference
sequence is `Δs(n) = s(n+1) - s(n)`. "Increasing" in the paper means non-decreasing.
The reflection `w̄` is `fun i => !w i`, the prefix operator `Pre_u(w) = u w` is Mathlib's
`u ++ₛ w`, the cloning substitution `φ_k(w)` is `fun i => w (i / k)`, and the counting function
`#_α(m)` counts the letters `α` among the first `m` letters `ℓ₀ ⋯ ℓ_{m-1}`.
The Fibonacci word `f = abaab⋯` is `fun i => !fibInf i` (`fibInf` encodes `a` as `false`), so
`f̄ = fibInf`, and `ϱ_F^n(a)` is `(fibWord n).map (!·)`. The Thue–Morse word `t = abba⋯` is
`fun i => !thueMorse i`. A one-sided fixed point of a substitution `ϱ` is a word `w` with
`IsSubstitutionImage ϱ w w`, and the substitution matrix of `ϱ` has entries
`M₁₁ = |ϱ(a)|_a`, `M₁₂ = |ϱ(b)|_a`, `M₂₁ = |ϱ(a)|_b`, `M₂₂ = |ϱ(b)|_b`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The paper's set `𝒲`: infinite binary words (`a = true`, `b = false`) in which both
letters occur infinitely often.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of `𝒲`). -/
public def BothLettersInfinite (w : ℕ → Bool) : Prop :=
  {i | w i = true}.Infinite ∧ {i | w i = false}.Infinite

/-- The position function `p_α(n)`: the (0-based) position of the `n`-th occurrence
(`n ≥ 1`) of the letter `α` in `w`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of position functions). -/
public noncomputable def letterPosition (w : ℕ → Bool) (α : Bool) (n : ℕ) : ℕ :=
  Nat.nth (fun i => w i = α) (n - 1)

/-- The relative position function `r(n) = p_b(n) - p_a(n)`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the relative position function). -/
public noncomputable def relativePosition (w : ℕ → Bool) (n : ℕ) : ℤ :=
  (letterPosition w false n : ℤ) - letterPosition w true n

/-- If `w` starts with `α`, then `p_α(1) = 0`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of position functions). -/
public theorem letterPosition_one_of_head {w : ℕ → Bool} {α : Bool} (h : w 0 = α) :
    letterPosition w α 1 = 0 := by
  simp [letterPosition, Nat.nth_zero_of_zero (p := fun i => w i = α) h]

/-- If `w` starts with `ab`, then `r(1) = 1`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the relative position function). -/
public theorem relativePosition_one_of_head_ab {w : ℕ → Bool} (h₀ : w 0 = true)
    (h₁ : w 1 = false) : relativePosition w 1 = 1 := by
  have hb : letterPosition w false 1 = 1 := by
    simp only [letterPosition, Nat.sub_self, Nat.nth_zero]
    refine le_antisymm (Nat.sInf_le h₁) (Nat.one_le_iff_ne_zero.2 fun h => ?_)
    rcases Nat.sInf_eq_zero.1 h with h | h
    · have h' : w 0 = false := h
      simp [h₀] at h'
    · exact (Set.eq_empty_iff_forall_notMem.1 h 1) h₁
  simp [relativePosition, hb, letterPosition_one_of_head h₀]

/-- **Lemma 4.** A function `p : ℕ → ℤ_{≥0}` is `p_a` of some `w ∈ a𝒲` iff it is strictly
increasing, `p(1) = 0` and `Δp > 1` infinitely often; it is `p_b` of some `w ∈ a𝒲` iff it is
strictly increasing, `p(1) > 0` and `Δp > 1` infinitely often.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 4
(`jis-2025-25.1.5-lem-4`). -/
public theorem_wanted exists_word_letterPosition_eq_iff (p : ℕ → ℕ) :
    ((∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → letterPosition w true n = p n) ↔
      (∀ n, 1 ≤ n → p n < p (n + 1)) ∧ p 1 = 0 ∧
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite) ∧
    ((∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → letterPosition w false n = p n) ↔
      (∀ n, 1 ≤ n → p n < p (n + 1)) ∧ 0 < p 1 ∧
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite)

/-- **Lemma 5.** Two words of `𝒲` coincide iff their relative position functions coincide.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 5
(`jis-2025-25.1.5-lem-5`). -/
public theorem_wanted eq_iff_relativePosition_eq {w w' : ℕ → Bool} (hw : BothLettersInfinite w)
    (hw' : BothLettersInfinite w') :
    w = w' ↔ ∀ n, 1 ≤ n → relativePosition w n = relativePosition w' n

/-- **Lemma 8.** Every non-decreasing `r : ℕ → ℕ` (positive values) is the relative position
function of some `w ∈ a𝒲`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 8
(`jis-2025-25.1.5-lem-8`). -/
public theorem_wanted exists_word_relativePosition_eq_of_monotone (r : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ r n) (hmono : ∀ n, 1 ≤ n → r n ≤ r (n + 1)) :
    ∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → relativePosition w n = r n

/-- **Corollary 9.** Every non-increasing `r : ℕ → ℤ` with `r(1) < 0` is the relative position
function of some `w ∈ b𝒲`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 9
(`jis-2025-25.1.5-cor-9`). -/
public theorem_wanted exists_word_relativePosition_eq_of_antitone (r : ℕ → ℤ) (h₁ : r 1 < 0)
    (hanti : ∀ n, 1 ≤ n → r (n + 1) ≤ r n) :
    ∃ w, BothLettersInfinite w ∧ w 0 = false ∧ ∀ n, 1 ≤ n → relativePosition w n = r n

/-- **Lemma 13.** For `w ∈ a𝒲` and `k ≥ 1`: `b^k` is a subword of `w` iff
`sup Δp_a > k` iff `Δp_b` takes the value one at least `k - 1` times in a row; and `a^k` is a
subword iff `Δp_a` takes the value one at least `k - 1` times in a row.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 13
(`jis-2025-25.1.5-lem-13`). -/
public theorem_wanted subword_run_iff_letterPosition_diff {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) {k : ℕ} (hk : 1 ≤ k) :
    ((∃ i, ∀ j < k, w (i + j) = false) ↔
        ∃ n, 1 ≤ n ∧ k < letterPosition w true (n + 1) - letterPosition w true n) ∧
      ((∃ i, ∀ j < k, w (i + j) = false) ↔
        ∃ n, 1 ≤ n ∧ ∀ j < k - 1,
          letterPosition w false (n + j + 1) - letterPosition w false (n + j) = 1) ∧
      ((∃ i, ∀ j < k, w (i + j) = true) ↔
        ∃ n, 1 ≤ n ∧ ∀ j < k - 1,
          letterPosition w true (n + j + 1) - letterPosition w true (n + j) = 1)

/-- **Lemma 14.** For `w ∈ a𝒲`: (a) if `r` is strictly increasing then `bb` is not a subword;
(b) if `bb` is not a subword then `r` is non-decreasing; (c) if `b^k` is a subword, then
`Δr(n+j) ≤ 0` for `1 ≤ j ≤ k-1` and some `n`; (d) if `a^k` is a subword, then
`Δr(n+j) ≥ 0` for `1 ≤ j ≤ k-1` and some `n`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 14
(`jis-2025-25.1.5-lem-14`). -/
public theorem_wanted relativePosition_monotonicity_runs {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    let r := relativePosition w
    ((∀ n, 1 ≤ n → r n < r (n + 1)) → ¬ ∃ i, w i = false ∧ w (i + 1) = false) ∧
      ((¬ ∃ i, w i = false ∧ w (i + 1) = false) → ∀ n, 1 ≤ n → r n ≤ r (n + 1)) ∧
      (∀ k, (∃ i, ∀ j < k, w (i + j) = false) →
        ∃ n, ∀ j, 1 ≤ j → j ≤ k - 1 → r (n + j + 1) - r (n + j) ≤ 0) ∧
      (∀ k, (∃ i, ∀ j < k, w (i + j) = true) →
        ∃ n, ∀ j, 1 ≤ j → j ≤ k - 1 → 0 ≤ r (n + j + 1) - r (n + j))

/-- **Lemma 15.** For `w ∈ a𝒲` not containing `b^k`, `|Δr - Δp_b| ≤ k`; in particular `Δr` is
bounded iff `Δp_b` is bounded.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 15
(`jis-2025-25.1.5-lem-15`). -/
public theorem_wanted abs_relativePosition_diff_sub_le {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) {k : ℕ}
    (hk : ¬ ∃ i, ∀ j < k, w (i + j) = false) :
    (∀ n, 1 ≤ n → |(relativePosition w (n + 1) - relativePosition w n) -
        ((letterPosition w false (n + 1) : ℤ) - letterPosition w false n)| ≤ k) ∧
      ((∃ C : ℤ, ∀ n, 1 ≤ n → |relativePosition w (n + 1) - relativePosition w n| ≤ C) ↔
        ∃ C : ℕ, ∀ n, 1 ≤ n → letterPosition w false (n + 1) - letterPosition w false n ≤ C)

/-- **Lemma 16.** For `w ∈ a𝒲`, the following are equivalent: `w` is periodic; `Δp_a` is
periodic; `Δp_a` and `Δp_b` are periodic. Moreover, if `w = u^ω` and `u` contains `k` letters
`a` and `j` letters `b`, then `Δp_a` is `k`-periodic and `Δp_b` is `j`-periodic.
(Periodic sequences on `ℕ = {1, 2, …}` are periodic at `n ≥ 1`; a periodic word is purely
periodic, `w = u^ω`.)

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 16
(`jis-2025-25.1.5-lem-16`). -/
public theorem_wanted periodic_iff_letterPosition_diff_periodic {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    let dpa := fun n => letterPosition w true (n + 1) - letterPosition w true n
    let dpb := fun n => letterPosition w false (n + 1) - letterPosition w false n
    let Per := fun f : ℕ → ℕ => ∃ q, 0 < q ∧ ∀ n, 1 ≤ n → f (n + q) = f n
    ((∃ q, 0 < q ∧ ∀ i, w (i + q) = w i) ↔ Per dpa) ∧ (Per dpa ↔ Per dpa ∧ Per dpb) ∧
      ∀ u : List Bool, 0 < u.length → (∀ i, w i = u.getD (i % u.length) false) →
        (∀ n, 1 ≤ n → dpa (n + u.count true) = dpa n) ∧
          ∀ n, 1 ≤ n → dpb (n + u.count false) = dpb n

/-- **Corollary 17.** If `w ∈ 𝒲` is periodic, so is `Δr`; if `w = u^ω` and `u` contains `k`
letters `a` and `j` letters `b`, then `lcm(k, j)` is a period of `Δr`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 17
(`jis-2025-25.1.5-cor-17`). -/
public theorem_wanted relativePosition_diff_periodic_of_periodic {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    let dr := fun n => relativePosition w (n + 1) - relativePosition w n
    ((∃ q, 0 < q ∧ ∀ i, w (i + q) = w i) → ∃ q, 0 < q ∧ ∀ n, 1 ≤ n → dr (n + q) = dr n) ∧
      ∀ u : List Bool, 0 < u.length → (∀ i, w i = u.getD (i % u.length) false) →
        ∀ n, 1 ≤ n → dr (n + Nat.lcm (u.count true) (u.count false)) = dr n

/-- **Lemma 25.** For `w ∈ a𝒲` all of whose single-letter runs have length at most `c`,
`p_a(n) ≤ (c+1)(n-1)`, `p_b(n) ≤ (c+1)n - 1` and `c(1-n) + 1 ≤ r(n) ≤ cn`.
The printed lower bound `(1-c)n + 1 ≤ r(n)` is false (for `w = (abb)^ω`, `c = 2`,
`r(4) = 5 - 9 = -4 < -3`); the bound `c(1-n) + 1` is the one derived in the paper's proof.
Stating the result for every bound `c` of the runs is equivalent to stating it for the
longest run.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 25
(`jis-2025-25.1.5-lem-25`). -/
public theorem_wanted letterPosition_le_of_run_le {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (h₀ : w 0 = true) {c : ℕ} (hc : ∀ i k, (∀ j < k, w (i + j) = w i) → k ≤ c) (n : ℕ)
    (hn : 1 ≤ n) :
    (letterPosition w true n : ℤ) ≤ (c + 1) * (n - 1) ∧
      (letterPosition w false n : ℤ) ≤ (c + 1) * n - 1 ∧
      (c : ℤ) * (1 - n) + 1 ≤ relativePosition w n ∧ relativePosition w n ≤ c * n

/-- **Corollary 27.** For `w ∈ 𝒲` all of whose single-letter runs have length at most `c`,
`p_a(n), p_b(n) ≤ (c+1)n - 1` and `-cn ≤ r(n) ≤ cn`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 27
(`jis-2025-25.1.5-cor-27`). -/
public theorem_wanted letterPosition_le_of_run_le' {w : ℕ → Bool} (hw : BothLettersInfinite w)
    {c : ℕ} (hc : ∀ i k, (∀ j < k, w (i + j) = w i) → k ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    (letterPosition w true n : ℤ) ≤ (c + 1) * n - 1 ∧
      (letterPosition w false n : ℤ) ≤ (c + 1) * n - 1 ∧
      -((c : ℤ) * n) ≤ relativePosition w n ∧ relativePosition w n ≤ c * n

/-- The deletion operator `D_α` on `𝒲`: delete the first occurrence of the letter `α`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the deletion operators `D_a`, `D_b`). -/
public noncomputable def deleteFirst (w : ℕ → Bool) (α : Bool) : ℕ → Bool :=
  fun i => if i < letterPosition w α 1 then w i else w (i + 1)

/-- The deletion operator `D = D_a ∘ D_b`: delete the first `b` and the first `a`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the deletion operator `D`). -/
public noncomputable def deletion (w : ℕ → Bool) : ℕ → Bool :=
  deleteFirst (deleteFirst w false) true

/-- If `w` starts with `α`, deleting the first `α` shifts `w` by one.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the deletion operators). -/
public theorem deleteFirst_of_head {w : ℕ → Bool} {α : Bool} (h : w 0 = α) :
    deleteFirst w α = fun i => w (i + 1) := by
  funext i
  simp [deleteFirst, letterPosition_one_of_head h]

/-- The counting function `#_α(m)`: the number of letters `α` among `ℓ₀, …, ℓ_{m-1}`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 3
(definition of the counting function). -/
public def letterCount (w : ℕ → Bool) (α : Bool) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun i => w i = α).card

/-- `#_α(0) = 0`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 3
(definition of the counting function). -/
public theorem letterCount_zero (w : ℕ → Bool) (α : Bool) : letterCount w α 0 = 0 := by
  simp [letterCount]

/-- `#_α(m+1) = #_α(m) + [ℓ_m = α]`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 3
(definition of the counting function). -/
public theorem letterCount_succ (w : ℕ → Bool) (α : Bool) (m : ℕ) :
    letterCount w α (m + 1) = letterCount w α m + if w m = α then 1 else 0 := by
  simp only [letterCount, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- **Lemma 6 (reconstruction algorithm).** For `w ∈ 𝒲` with relative position function `r`:
if `r(1) > 0` then `p_a(1) = 0`, `p_b(1) = r(1)`, otherwise `p_a(1) = -r(1)`, `p_b(1) = 0`; and
for `n ≥ 1`, with `k_{n+1}` the least position not among `p_a(1), …, p_a(n), p_b(1), …, p_b(n)`,
`r(n+1) > 0` gives `p_a(n+1) = k_{n+1}`, `p_b(n+1) = k_{n+1} + r(n+1)`, and `r(n+1) < 0` gives
`p_a(n+1) = k_{n+1} - r(n+1)`, `p_b(n+1) = k_{n+1}`. (The algorithm's output is stated as the
equality of the computed values with the true positions; `r(1) ≠ 0`, so "otherwise" is
`r(1) < 0`. Positions start at `0`, which always lies in `A_n ∪ B_n`, so taking the minimum over
`ℕ = {1, 2, …}` or over `ℤ_{≥0}` gives the same `k_{n+1}`.)

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 6
(`jis-2025-25.1.5-lem-6`). -/
public theorem_wanted letterPosition_reconstruction {w : ℕ → Bool} (hw : BothLettersInfinite w) :
    let pa := fun n => (letterPosition w true n : ℤ)
    let pb := fun n => (letterPosition w false n : ℤ)
    let r := relativePosition w
    (0 < r 1 → pa 1 = 0 ∧ pb 1 = r 1) ∧ (r 1 < 0 → pa 1 = -r 1 ∧ pb 1 = 0) ∧
      ∀ n, 1 ≤ n →
        let k : ℤ := ((sInf {m : ℕ | ∀ j, 1 ≤ j → j ≤ n →
          (m : ℤ) ≠ pa j ∧ (m : ℤ) ≠ pb j} : ℕ) : ℤ)
        (0 < r (n + 1) → pa (n + 1) = k ∧ pb (n + 1) = k + r (n + 1)) ∧
          (r (n + 1) < 0 → pa (n + 1) = k - r (n + 1) ∧ pb (n + 1) = k)

/-- **Proposition 11.** (a) The reflection `w ↦ w̄` maps `a𝒲` onto `b𝒲` and `b𝒲` onto `a𝒲`.
(b) For `w, w' ∈ 𝒲`, `w̄ = w'` iff `r_w = -r_{w'}`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 11
(`jis-2025-25.1.5-prop-11`). -/
public theorem_wanted reflection_image_and_relativePosition :
    ((fun w : ℕ → Bool => fun i => !w i) '' {w | BothLettersInfinite w ∧ w 0 = true} =
        {w | BothLettersInfinite w ∧ w 0 = false}) ∧
      ((fun w : ℕ → Bool => fun i => !w i) '' {w | BothLettersInfinite w ∧ w 0 = false} =
        {w | BothLettersInfinite w ∧ w 0 = true}) ∧
      ∀ w w' : ℕ → Bool, BothLettersInfinite w → BothLettersInfinite w' →
        ((fun i => !w i) = w' ↔ ∀ n, 1 ≤ n → relativePosition w n = -relativePosition w' n)

/-- **Lemma 19.** For `w ∈ 𝒲`, `Δp_b` is periodic iff `D_a^{p_b(1)}(w)` (the word `w` with its
initial run of `a`'s deleted) is periodic. (Same conventions as Lemma 16: periodic sequences on
`ℕ = {1, 2, …}` are periodic at `n ≥ 1`, and a periodic word is purely periodic.)

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 19
(`jis-2025-25.1.5-lem-19`). -/
public theorem_wanted letterPosition_diff_periodic_iff_deleteFirst_periodic {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    (∃ q, 0 < q ∧ ∀ n, 1 ≤ n → letterPosition w false (n + q + 1) - letterPosition w false (n + q) =
        letterPosition w false (n + 1) - letterPosition w false n) ↔
      ∃ q, 0 < q ∧ ∀ i,
        (fun v => deleteFirst v true)^[letterPosition w false 1] w (i + q) =
          (fun v => deleteFirst v true)^[letterPosition w false 1] w i

/-- **Lemma 21.** A finite word `u` of length `2k` is equilibrious (as many `a`'s as `b`'s) iff
`D^k ∘ Pre_u` is the identity on `𝒲`. (`IsEquilibriousWord` is stated on `List (Fin 2)`; the
letter `a = true` is sent to `0` and `b = false` to `1`.)

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 21
(`jis-2025-25.1.5-lem-21`). -/
public theorem_wanted isEquilibriousWord_iff_deletion_iterate_prepend (u : List Bool) {k : ℕ}
    (hu : u.length = 2 * k) :
    IsEquilibriousWord (u.map fun x => if x then 0 else 1) ↔
      ∀ w, BothLettersInfinite w → deletion^[k] (u ++ₛ w) = w

/-- **Lemma 22.** For an equilibrious word `u` of length `2k` and `w ∈ 𝒲`,
`p_{a, uw}(n+k) = p_{a,w}(n) + 2k`, `p_{b, uw}(n+k) = p_{b,w}(n) + 2k`, hence
`r_{uw}(n+k) = r_w(n)`, for all `n ≥ 1`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 22
(`jis-2025-25.1.5-lem-22`). -/
public theorem_wanted letterPosition_prepend_equilibrious (u : List Bool) {k : ℕ}
    (hu : u.length = 2 * k) (hequi : IsEquilibriousWord (u.map fun x => if x then 0 else 1))
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (n : ℕ) (hn : 1 ≤ n) :
    letterPosition (u ++ₛ w) true (n + k) = letterPosition w true n + 2 * k ∧
      letterPosition (u ++ₛ w) false (n + k) = letterPosition w false n + 2 * k ∧
      relativePosition (u ++ₛ w) (n + k) = relativePosition w n

/-- **Lemma 24.** For `w ∈ 𝒲` and the cloning substitution `φ_k(w) = fun i => w (i / k)`
(`a ↦ a^k`, `b ↦ b^k`), for all `m ≥ 0` and `1 ≤ j ≤ k`:
`p_{a,φ_k(w)}(mk+j) = k p_{a,w}(m+1) + j - 1`, `p_{b,φ_k(w)}(mk+j) = k p_{b,w}(m+1) + j - 1`,
`r_{φ_k(w)}(mk+j) = k r_w(m+1)`. The paper takes `k ≥ 2`; the identities hold for `k = 1`
(`φ_1` is the identity) and are vacuous for `k = 0`, so no bound on `k` is assumed.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 24
(`jis-2025-25.1.5-lem-24`). -/
public theorem_wanted letterPosition_clone {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (k m j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    letterPosition (fun i => w (i / k)) true (m * k + j) =
        k * letterPosition w true (m + 1) + j - 1 ∧
      letterPosition (fun i => w (i / k)) false (m * k + j) =
        k * letterPosition w false (m + 1) + j - 1 ∧
      relativePosition (fun i => w (i / k)) (m * k + j) = k * relativePosition w (m + 1)

open Filter Topology in
/-- **Lemma 28.** For `w ∈ 𝒲` and a letter `α`: (a) for `d ∈ (0, 1]`, `#_α(m)/m → d` iff
`p_α(n)/n → 1/d`; (b) `#_α(m)/m → 0` iff `p_α(n)/n → ∞`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 28
(`jis-2025-25.1.5-lem-28`). -/
public theorem_wanted tendsto_letterCount_div_iff_tendsto_letterPosition_div {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (α : Bool) :
    (∀ d : ℝ, 0 < d → d ≤ 1 →
      (Tendsto (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop (𝓝 d) ↔
        Tendsto (fun n : ℕ => (letterPosition w α n : ℝ) / n) atTop (𝓝 (1 / d)))) ∧
      (Tendsto (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop (𝓝 0) ↔
        Tendsto (fun n : ℕ => (letterPosition w α n : ℝ) / n) atTop atTop)

open Filter in
/-- **Corollary 29.** For `w ∈ 𝒲` and a letter `α`,
`limsup #_α(m)/m = limsup n/p_α(n)` and `liminf #_α(m)/m = liminf n/p_α(n)` (both sequences are
bounded, so the real `limsup`/`liminf` are the classical ones).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 29
(`jis-2025-25.1.5-cor-29`). -/
public theorem_wanted limsup_liminf_letterCount_div {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (α : Bool) :
    limsup (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop =
        limsup (fun n : ℕ => (n : ℝ) / letterPosition w α n) atTop ∧
      liminf (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop =
        liminf (fun n : ℕ => (n : ℝ) / letterPosition w α n) atTop

open Filter Topology in
/-- **Theorem 30.** For `w ∈ 𝒲` and `d ∈ (0, 1)` the following are equivalent:
`Freq(b) = d`; `Freq(a) = 1 - d`; `p_b(n)/n → 1/d`; `p_a(n)/n → 1/(1-d)`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 30
(`jis-2025-25.1.5-thm-30`). -/
public theorem_wanted letter_frequency_tfae {w : ℕ → Bool} (hw : BothLettersInfinite w) {d : ℝ}
    (hd₀ : 0 < d) (hd₁ : d < 1) :
    [Tendsto (fun m : ℕ => (letterCount w false m : ℝ) / m) atTop (𝓝 d),
      Tendsto (fun m : ℕ => (letterCount w true m : ℝ) / m) atTop (𝓝 (1 - d)),
      Tendsto (fun n : ℕ => (letterPosition w false n : ℝ) / n) atTop (𝓝 (1 / d)),
      Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 (1 / (1 - d)))].TFAE

open Filter Topology in
/-- **Corollary 31.** If `Freq(b) = d ∈ (0, 1)` then `r(n)/n → 1/d - 1/(1-d)`. (Such a word has
both letters infinitely often, so no separate `w ∈ 𝒲` hypothesis is needed.)

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 31
(`jis-2025-25.1.5-cor-31`). -/
public theorem_wanted tendsto_relativePosition_div_of_frequency {w : ℕ → Bool} {d : ℝ}
    (hd₀ : 0 < d) (hd₁ : d < 1)
    (hfreq : Tendsto (fun m : ℕ => (letterCount w false m : ℝ) / m) atTop (𝓝 d)) :
    Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (1 / d - 1 / (1 - d)))

open Filter Topology in
/-- **Proposition 33.** For `w ∈ 𝒲` with `r(n)/n → L` in the extended reals, `Freq(b)` exists
and equals `0` if `L = ∞`, `1` if `L = -∞`, `1/2` if `L = 0`, and
`(2 + L - √(4 + L²)) / (2L)` otherwise.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 33
(`jis-2025-25.1.5-prop-33`). -/
public theorem_wanted frequency_of_tendsto_relativePosition_div {w : ℕ → Bool}
    (hw : BothLettersInfinite w) {L : EReal}
    (hL : Tendsto (fun n : ℕ => (((relativePosition w n : ℝ) / n : ℝ) : EReal)) atTop (𝓝 L)) :
    let freqB := fun m : ℕ => (letterCount w false m : ℝ) / m
    (L = ⊤ → Tendsto freqB atTop (𝓝 0)) ∧ (L = ⊥ → Tendsto freqB atTop (𝓝 1)) ∧
      (L = 0 → Tendsto freqB atTop (𝓝 (1 / 2))) ∧
      ∀ x : ℝ, L = x → x ≠ 0 →
        Tendsto freqB atTop (𝓝 ((2 + x - Real.sqrt (4 + x ^ 2)) / (2 * x)))

open Filter Topology in
/-- **Theorem 34.** For `w ∈ 𝒲`, with `r(n)/n → r`, `p_b(n)/n → p`, `p_a(n)/n → q` read in the
extended reals: if one of the limits exists then all exist, `1/p + 1/q = 1`, and
`p = (2 + r + √(4 + r²))/2`, `q = (2 - r + √(4 + r²))/2`. At `r = ±∞` the formulas are read as
their limits (`r = ∞` gives `p = ∞`, `q = 1`; `r = -∞` gives `p = 1`, `q = ∞`), as in the paper's
remark that they hold for `r ∈ {0, ±∞}`. (`EReal` inverses have `⊤⁻¹ = 0`.)

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 34
(`jis-2025-25.1.5-thm-34`). -/
public theorem_wanted relativePosition_letterPosition_mean_values {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    let R := fun n : ℕ => (((relativePosition w n : ℝ) / n : ℝ) : EReal)
    let P := fun n : ℕ => (((letterPosition w false n : ℝ) / n : ℝ) : EReal)
    let Q := fun n : ℕ => (((letterPosition w true n : ℝ) / n : ℝ) : EReal)
    ((∃ x, Tendsto R atTop (𝓝 x)) ↔ ∃ y, Tendsto P atTop (𝓝 y)) ∧
      ((∃ x, Tendsto R atTop (𝓝 x)) ↔ ∃ z, Tendsto Q atTop (𝓝 z)) ∧
      (∀ y z, Tendsto P atTop (𝓝 y) → Tendsto Q atTop (𝓝 z) → y⁻¹ + z⁻¹ = 1) ∧
      (∀ x : ℝ, Tendsto R atTop (𝓝 x) →
        Tendsto P atTop (𝓝 (((2 + x + Real.sqrt (4 + x ^ 2)) / 2 : ℝ) : EReal)) ∧
          Tendsto Q atTop (𝓝 (((2 - x + Real.sqrt (4 + x ^ 2)) / 2 : ℝ) : EReal))) ∧
      (Tendsto R atTop (𝓝 ⊤) → Tendsto P atTop (𝓝 ⊤) ∧ Tendsto Q atTop (𝓝 1)) ∧
      (Tendsto R atTop (𝓝 ⊥) → Tendsto P atTop (𝓝 1) ∧ Tendsto Q atTop (𝓝 ⊤))

/-- `v = ϱ(w)` for a substitution `ϱ` (extended to words by concatenation): every prefix
`ϱ(ℓ₀ ⋯ ℓ_{m-1})` of the image is a prefix of `v`, and these prefixes are unboundedly long, so
that they determine all of `v` (without this, an erasing `ϱ` such as `fun _ => []` would relate
every pair of words). `IsSubstitutionImage ϱ w w` says that `w` is a fixed point of `ϱ`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 1
(binary substitutions as homomorphisms of words) and Section 3 (images `ϱ(w)`). -/
public def IsSubstitutionImage (ϱ : Bool → List Bool) (w v : ℕ → Bool) : Prop :=
  (∀ N, ∃ m, N ≤ ((List.ofFn fun j : Fin m => w j).flatMap ϱ).length) ∧
  ∀ m i, i < ((List.ofFn fun j : Fin m => w j).flatMap ϱ).length →
    v i = ((List.ofFn fun j : Fin m => w j).flatMap ϱ).getD i false

/-- Every word is its own image under the identity substitution.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 1
(binary substitutions as homomorphisms of words). -/
public theorem isSubstitutionImage_id (w : ℕ → Bool) :
    IsSubstitutionImage (fun x => [x]) w w := by
  refine ⟨fun N => ⟨N, by simp⟩, ?_⟩
  intro m i hi
  simp only [List.flatMap_singleton', List.length_ofFn] at hi ⊢
  simp [List.getD_eq_getElem?_getD, hi]

open Filter Topology in
/-- **Theorem 35.** Let `μ` be a binary substitution (`μ a`, `μ b` finite words, extended to
words by concatenation) such that `a` and `b` occur in `μ(ab)`, and let `v = μ(w)` for `w ∈ 𝒲`
with `Freq_a(w) = f`. Then `Freq_a(v)` and `Freq_b(v)` exist and
`[Freq_a(v), Freq_b(v)]ᵀ = M_μ [f, 1 - f]ᵀ / (|μ(a)| f + |μ(b)| (1 - f))`, where the incidence
matrix has `M₁₁ = |μ(a)|_a`, `M₁₂ = |μ(b)|_a`, `M₂₁ = |μ(a)|_b`, `M₂₂ = |μ(b)|_b`.
Added hypothesis: `μ` is non-erasing (`μ a`, `μ b` nonempty). The paper's substitutions are
arbitrary homomorphisms, and for erasing `μ` the formula fails: with `μ(a) = ε`, `μ(b) = ab`
and `w ∈ 𝒲` with `Freq_a(w) = 1` (for example `b` exactly at the perfect squares),
`μ(w) = (ab)^ω` has `Freq_a = 1/2` while the denominator `|μ(a)|·1 + |μ(b)|·0` is `0`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 35
(`jis-2025-25.1.5-thm-35`). -/
public theorem_wanted frequency_substitution_image (μ : Bool → List Bool)
    (hμa : μ true ≠ []) (hμb : μ false ≠ [])
    (hab : true ∈ μ true ++ μ false ∧ false ∈ μ true ++ μ false)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) {v : ℕ → Bool} (hv : IsSubstitutionImage μ w v)
    {f : ℝ} (hf : Tendsto (fun m : ℕ => (letterCount w true m : ℝ) / m) atTop (𝓝 f)) :
    let L := (μ true).length * f + (μ false).length * (1 - f)
    Tendsto (fun m : ℕ => (letterCount v true m : ℝ) / m) atTop
        (𝓝 (((μ true).count true * f + (μ false).count true * (1 - f)) / L)) ∧
      Tendsto (fun m : ℕ => (letterCount v false m : ℝ) / m) atTop
        (𝓝 (((μ true).count false * f + (μ false).count false * (1 - f)) / L))

open Polynomial in
/-- **Lemma 39.** For `M ∈ M₂(ℤ)`, `[τ 1]ᵀ` (`τ` the golden ratio) is a right eigenvector of `M`
iff `M = [[m+n, m], [m, n]]` for some integers `m, n`; in that case the eigenvalues of `M` are
`n + mτ` and `n + mτ'` (`τ' = (1 - √5)/2`), i.e. the characteristic polynomial factors as
`(X - (n + mτ))(X - (n + mτ'))`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 39
(`jis-2025-25.1.5-lem-39`). -/
public theorem_wanted golden_eigenvector_iff (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ((∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![Real.goldenRatio, 1] =
        c • ![Real.goldenRatio, 1]) ↔
        ∃ m n : ℤ, M = !![m + n, m; m, n]) ∧
      ∀ m n : ℤ, M = !![m + n, m; m, n] →
        (M.map (Int.cast : ℤ → ℝ)).charpoly =
          (X - C ((n : ℝ) + m * Real.goldenRatio)) * (X - C ((n : ℝ) + m * Real.goldenConj))

/-- **Theorem 63.** Let `j, m ≥ 1`, `τ_{j,m} = (j + √(j² + 4m))/2` and `M ∈ M₂(ℤ)`.
(a) If `j² + 4m` is not a perfect square, `[τ_{j,m} 1]ᵀ` is a right eigenvector of `M` iff
`M = [[t + sj, ms], [s, t]]` for some integers `s, t`. (b) If `j² + 4m = r²`, it is a right
eigenvector iff `M = [[s, t], [u, v]]` with `u(j+r)² + 2(v-s)(j+r) - 4t = 0`.
Corrected reading in (b): `r` is the nonnegative root, `r = √(j² + 4m)`, as the paper's proof
uses `τ_{j,m} = (j + r)/2`. For the negative root the printed statement fails: `j = 1`, `m = 2`,
`r = -3`, `M = [[0, 0], [1, 1]]` satisfies `u(j+r)² + 2(v-s)(j+r) - 4t = 4 - 4 - 0 = 0`, but
`τ_{1,2} = 2` and `M [2, 1]ᵀ = [0, 3]ᵀ` is not a multiple of `[2, 1]ᵀ`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 63
(`jis-2025-25.1.5-thm-63`). -/
public theorem_wanted pisa_eigenvector_iff (j m : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    let τ : ℝ := (j + Real.sqrt (j ^ 2 + 4 * m)) / 2
    let IsEig := ∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] = c • ![τ, 1]
    ((¬ IsSquare (j ^ 2 + 4 * m)) → (IsEig ↔ ∃ s t : ℤ, M = !![t + s * j, m * s; s, t])) ∧
      ∀ r : ℕ, j ^ 2 + 4 * m = r ^ 2 →
        (IsEig ↔ ∃ s t u v : ℤ,
          u * (j + r) ^ 2 + 2 * (v - s) * (j + r) - 4 * t = 0 ∧ M = !![s, t; u, v])

open Polynomial in
/-- **Lemma 66.** For `k ≥ 1`, `τ_k = (k + √(k² + 4))/2` and `M ∈ M₂(ℤ)`, `[τ_k 1]ᵀ` is a right
eigenvector of `M` iff `M = [[km + n, m], [m, n]]` for some integers `m, n`; then the eigenvalues
are `n + mτ_k` and `n + mτ_k'` with `τ_k' = (k - √(k² + 4))/2`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 66
(`jis-2025-25.1.5-lem-66`). -/
public theorem_wanted metallic_eigenvector_iff (k : ℕ) (hk : 1 ≤ k)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    let τ : ℝ := (k + Real.sqrt (k ^ 2 + 4)) / 2
    let τ' : ℝ := (k - Real.sqrt (k ^ 2 + 4)) / 2
    ((∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] = c • ![τ, 1]) ↔
        ∃ m n : ℤ, M = !![k * m + n, m; m, n]) ∧
      ∀ m n : ℤ, M = !![k * m + n, m; m, n] →
        (M.map (Int.cast : ℤ → ℝ)).charpoly = (X - C ((n : ℝ) + m * τ)) * (X - C ((n : ℝ) + m * τ'))

/-- **Theorem 38.** For the Fibonacci word `f`: (a) `Δp_a(n)` is the coding of `f` at `n - 1`
under `(a, b) ↦ (2, 1)`; (b) `Δp_b(n)` is its coding under `(a, b) ↦ (3, 2)`; (c) `r(n) = n` (so
`Δr = 1`). Corrected reading: the record prints the codings `(1, 2)` and `(2, 3)`, which are false
(`f = abaab⋯` has `p_a = 0, 2, 3, 5, …`, so `Δp_a(1) = 2` while `f` starts with `a`); the codings
`(2, 1)` and `(3, 2)` are the ones derived in the paper's proof. A sequence `x₁x₂⋯` is read as
the word with `x₁` at position `0`, as in the paper's conventions.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 38
(`jis-2025-25.1.5-thm-38`). -/
public theorem_wanted fibonacciWord_letterPosition_diff :
    let f := (fun i => !fibInf i)
    (∀ n, 1 ≤ n → letterPosition f true (n + 1) - letterPosition f true n =
        if f (n - 1) then 2 else 1) ∧
      (∀ n, 1 ≤ n → letterPosition f false (n + 1) - letterPosition f false n =
        if f (n - 1) then 3 else 2) ∧
      ∀ n, 1 ≤ n → relativePosition f n = n

/-- **Theorem 43.** For the Fibonacci word `f`, `r_{D(f)}(n) = n + 1` for all `n ≥ 1`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 43
(`jis-2025-25.1.5-thm-43`). -/
public theorem_wanted relativePosition_deletion_fibonacciWord (n : ℕ) (hn : 1 ≤ n) :
    relativePosition (deletion (fun i => !fibInf i)) n = n + 1

/-- **Theorem 44.** For every `k`, `r_{D^k(f)}(n) = n + k` for all sufficiently large `n`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 44
(`jis-2025-25.1.5-thm-44`). -/
public theorem_wanted relativePosition_deletion_iterate_fibonacciWord (k : ℕ) :
    ∃ N, ∀ n, N < n → relativePosition (deletion^[k] (fun i => !fibInf i)) n = n + k

/-- **Theorem 45 (the Fibonacci switch).** For `μ(a) = aab`, `μ(b) = ab`, the word obtained
from `f` by replacing each level-2 supertile `aba` by `aab` and keeping each `ab` is `μ(f)`
(the level-2 supertiles of `f` follow `f` itself), and `μ(f) = D(f)`. Stated as
`IsSubstitutionImage μ f (D f)`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 45
(`jis-2025-25.1.5-thm-45`). -/
public theorem_wanted fibonacci_switch :
    IsSubstitutionImage (fun x => if x then [true, true, false] else [true,
        false]) (fun i => !fibInf i)
      (deletion (fun i => !fibInf i))

/-- **Theorem 46.** For `w ∈ a𝒲`, both `Δp_a` and `Δp_b` are codings of `w` (`Δp_α(n)` a
function of `ℓ_{n-1}`) iff `w = f` or `w = (ab)^ω`; and they are both isomorphic to `w`
(injective codings) iff `w = f`. The second part drops the paper's word "aperiodic": `(ab)^ω` has
constant `Δp_a`, `Δp_b`, so it is never isomorphic to them, and the isomorphism claim holds for
every `w ∈ a𝒲`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 46
(`jis-2025-25.1.5-thm-46`). -/
public theorem_wanted letterPosition_diff_codings_iff_fibonacci {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    ((∃ σa σb : Bool → ℕ, ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = (fun i => !fibInf i) ∨ w = fun i => decide (i % 2 = 0)) ∧
      ((∃ σa σb : Bool → ℕ, Function.Injective σa ∧ Function.Injective σb ∧
        ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = (fun i => !fibInf i))

/-- **Corollary 48.** For `w ∈ b𝒲`, both `Δp_a` and `Δp_b` are codings of `w` iff `w = f̄` or
`w = (ba)^ω`; they are both isomorphic to `w` iff `w = f̄` ("aperiodic" dropped as in
Theorem 46).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 48
(`jis-2025-25.1.5-cor-48`). -/
public theorem_wanted letterPosition_diff_codings_iff_fibonacci_reflect {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = false) :
    ((∃ σa σb : Bool → ℕ, ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = fibInf ∨ w = fun i => decide (i % 2 = 1)) ∧
      ((∃ σa σb : Bool → ℕ, Function.Injective σa ∧ Function.Injective σb ∧
        ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = fibInf)

/-- **Corollary 49.** Up to isomorphism (the reflection), `f` is the only binary word of `𝒲`
isomorphic to the difference sequence of the position function of each letter: `Δp_a` and
`Δp_b` are both injective codings of `w ∈ 𝒲` iff `w = f` or `w = f̄` ("aperiodic" dropped as in
Theorem 46).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 49
(`jis-2025-25.1.5-cor-49`). -/
public theorem_wanted letterPosition_diff_isomorphic_iff_fibonacci {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    (∃ σa σb : Bool → ℕ, Function.Injective σa ∧ Function.Injective σb ∧
        ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
      w = (fun i => !fibInf i) ∨ w = fibInf

/-- **Proposition 51.** For the iccanobiF substitution `ϱ_F'` (`a ↦ ba`, `b ↦ a`) and `n ≥ 1`:
`ab ϱ_F^{2n}(a) = (ϱ_F')^{2n}(a) ba` and `ba ϱ_F^{2n-1}(a) = (ϱ_F')^{2n-1}(a) ab`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 51
(`jis-2025-25.1.5-prop-51`). -/
public theorem_wanted fibonacci_iccanobiF_conjugate_a (n : ℕ) (hn : 1 ≤ n) :
    [true, false] ++ (fibWord (2 * n)).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 *
        n] [true] ++ [false, true] ∧
      [false, true] ++ (fibWord (2 * n - 1)).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 * n -
            1] [true] ++ [true, false]

/-- **Proposition 52.** For `n ≥ 1`: `ab ϱ_F^{2n+1}(b) = (ϱ_F')^{2n+1}(b) ba` and
`ba ϱ_F^{2n}(b) = (ϱ_F')^{2n}(b) ab`. Here `ϱ_F^{k+1}(b) = ϱ_F^k(a)` is written
`(fibWord k).map (!·)`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 52
(`jis-2025-25.1.5-prop-52`). -/
public theorem_wanted fibonacci_iccanobiF_conjugate_b (n : ℕ) (hn : 1 ≤ n) :
    [true, false] ++ (fibWord (2 * n)).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 * n +
        1] [false] ++ [false, true] ∧
      [false, true] ++ (fibWord (2 * n - 1)).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 *
            n] [false] ++ [true, false]

/-- **Theorem 53.** The words `(ϱ_F')^{2n}(a)` are prefixes of `Pre_{ab}(f)` and
`(ϱ_F')^{2n}(b)` are prefixes of `Pre_{ba}(f)`, with lengths tending to infinity, so
`(ϱ_F')^{2n}(a) → Pre_{ab}(f) ∈ a𝒲` and `(ϱ_F')^{2n}(b) → Pre_{ba}(f) ∈ b𝒲`; moreover
`r_{Pre_{ab}(f)}(1) = 1`, `r_{Pre_{ba}(f)}(1) = -1` and both equal `n - 1` for `n > 1`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 53
(`jis-2025-25.1.5-thm-53`). -/
public theorem_wanted iccanobiF_fixed_points :
    let f := (fun i => !fibInf i)
    let it := fun (n : ℕ) (x : Bool) => (fun u : List Bool => u.flatMap fun x => if x then [false,
        true] else [true])^[2 * n] [x]
    (∀ n i, i < (it n true).length → (it n true).getD i false = ([true, false] ++ₛ f) i) ∧
      (∀ n i, i < (it n false).length → (it n false).getD i false = ([false, true] ++ₛ f) i) ∧
      (∀ N, ∃ n, N ≤ (it n true).length ∧ N ≤ (it n false).length) ∧
      relativePosition ([true, false] ++ₛ f) 1 = 1 ∧
      relativePosition ([false, true] ++ₛ f) 1 = -1 ∧
      ∀ n, 2 ≤ n → relativePosition ([true, false] ++ₛ f) n = n - 1 ∧
        relativePosition ([false, true] ++ₛ f) n = n - 1

/-- **Theorem 55.** For an equilibrious word `u` of length `2j` and `w_j = Pre_u(f)`,
`r_{w_j}(n) = n - j` for all `n > j`; if `u = (ab)^j`, then `r_{w_j}(1) = ⋯ = r_{w_j}(j) = 1`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 55
(`jis-2025-25.1.5-thm-55`). -/
public theorem_wanted relativePosition_prepend_equilibrious_fibonacci (u : List Bool) {j : ℕ}
    (hu : u.length = 2 * j) (hequi : IsEquilibriousWord (u.map fun x => if x then 0 else 1)) :
    (∀ n, j < n → relativePosition (u ++ₛ (fun i => !fibInf i)) n = n - j) ∧
      (u = (List.replicate j [true, false]).flatten →
        ∀ n, 1 ≤ n → n ≤ j → relativePosition (u ++ₛ (fun i => !fibInf i)) n = 1)

/-- **Theorem 57.** For `k, m ≥ 1`, `l ≥ 0` and `w` the one-sided fixed point of the extended Pisa
substitution `σ_{k,l,m}` (`a ↦ a^k b a^l`, `b ↦ a^m`):
`p_b(n) = m p_a(n) + (k+l+1-m) n + m - l - 1` and `r(n) = (m-1) p_a(n) + (k+l+1-m) n + m - l - 1`
for `n ≥ 1`; and `w` is the unique word of `𝒲` whose relative position function satisfies the
second identity.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 57
(`jis-2025-25.1.5-thm-57`). -/
public theorem_wanted pisa_letterPosition_identity (k l m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {w : ℕ → Bool} (hfix : IsSubstitutionImage (fun x : Bool => if x then List.replicate k true ++
        [false] ++ List.replicate l true else List.replicate m true) w w)
    (h₀ : w 0 = true) :
    (∀ n, 1 ≤ n → (letterPosition w false n : ℤ) =
        m * letterPosition w true n + (k + l + 1 - m : ℤ) * n + m - l - 1) ∧
      (∀ n, 1 ≤ n → relativePosition w n =
        (m - 1 : ℤ) * letterPosition w true n + (k + l + 1 - m : ℤ) * n + m - l - 1) ∧
      ∀ w' : ℕ → Bool, BothLettersInfinite w' →
        (∀ n, 1 ≤ n → relativePosition w' n =
          (m - 1 : ℤ) * letterPosition w' true n + (k + l + 1 - m : ℤ) * n + m - l - 1) →
        w' = w

/-- **Corollary 58.** For `k, m ≥ 1`, `l ≥ 0` and `w` the one-sided fixed point of `σ_{k,l,m}`,
`r(n) = ((m-1)/m) p_b(n) + ((k+l+1-m)/m) n + (m-l-1)/m` for `n ≥ 1`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 58
(`jis-2025-25.1.5-cor-58`). -/
public theorem_wanted pisa_relativePosition_of_letterPosition_b (k l m : ℕ) (hk : 1 ≤ k)
    (hm : 1 ≤ m) {w : ℕ → Bool}
        (hfix : IsSubstitutionImage (fun x : Bool => if x then List.replicate k true ++ [false] ++
        List.replicate l true else List.replicate m true) w w)
    (h₀ : w 0 = true) (n : ℕ) (hn : 1 ≤ n) :
    (relativePosition w n : ℚ) = (m - 1) / m * letterPosition w false n +
      (k + l + 1 - m) / m * n + (m - l - 1) / m

open Filter Topology in
/-- **Lemma 32.** Let `ϱ` be a primitive substitution (some power of its substitution matrix is
positive), `[u 1]ᵀ` a right Perron–Frobenius eigenvector of the substitution matrix (eigenvalue
`λ`), and `w ∈ 𝒲` a fixed point of `ϱ`. Then `Freq(a) = u/(u+1)`, `Freq(b) = 1/(u+1)`,
`p_a(n)/n → 1 + 1/u`, `p_b(n)/n → u + 1`, `r(n)/n → u - 1/u`, and all these limits lie in
`ℚ(λ)`. The Perron–Frobenius condition is stated as `u > 0` and `[u 1]ᵀ` an eigenvector: a
positive eigenvector of a primitive matrix belongs to the Perron–Frobenius eigenvalue.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 32
(`jis-2025-25.1.5-lem-32`). -/
public theorem_wanted primitive_fixed_point_mean_values (ϱ : Bool → List Bool) (hprim : ∃ p, ∀ i j,
    0 < ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
    (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {u c : ℝ} (hu : 0 < u)
        (heig : ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![u, 1] =
        c • ![u, 1])
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (hfix : IsSubstitutionImage ϱ w w) :
    Tendsto (fun n : ℕ => (letterCount w true n : ℝ) / n) atTop (𝓝 (u / (u + 1))) ∧
      Tendsto (fun n : ℕ => (letterCount w false n : ℝ) / n) atTop (𝓝 (1 / (u + 1))) ∧
      Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 (1 + 1 / u)) ∧
      Tendsto (fun n : ℕ => (letterPosition w false n : ℝ) / n) atTop (𝓝 (u + 1)) ∧
      Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (u - 1 / u)) ∧
      ∀ x ∈ ({u / (u + 1), 1 / (u + 1), 1 + 1 / u, u + 1, u - 1 / u} : Set ℝ),
        x ∈ IntermediateField.adjoin ℚ {c}

open Filter Topology in
/-- **Lemma 41.** For a primitive substitution `ϱ` and a fixed point `w ∈ 𝒲`, `r(n)/n → 1` iff
`[τ 1]ᵀ` (`τ` the golden ratio) is a right Perron–Frobenius eigenvector of the substitution
matrix (stated as an eigenvector: `[τ 1]ᵀ` is positive, so its eigenvalue is the
Perron–Frobenius one).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 41
(`jis-2025-25.1.5-lem-41`). -/
public theorem_wanted primitive_relativePosition_div_tendsto_one_iff (ϱ : Bool → List Bool)
    (hprim : ∃ p, ∀ i j, 0 < ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (hfix : IsSubstitutionImage ϱ w w) :
    Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 1) ↔
      ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
          (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec
          ![Real.goldenRatio, 1] = c • ![Real.goldenRatio, 1]

open Filter Topology in
/-- **Proposition 62.** Let `j, m ≥ 1`, `τ = τ_{j,m} = (j + √(j² + 4m))/2`, `ϱ` a primitive binary
substitution and `w` a fixed point of `ϱ`. The following are equivalent: (i) `Freq(a) =
(τ - m)/(j + 1 - m)`; (ii) `Freq(b) = (j + 1 - τ)/(j + 1 - m)`; (iii) `p_a(n)/n → 1 + (τ - j)/m`;
(iv) `p_b(n)/n → τ + 1`; (v) `r(n)/n → ((m-1)τ + j)/m`; (vi) `p_a(n)/n` has a limit `q` and
`r(n)/n → (m-1) q + (j + 1 - m)`; (vii) `[τ 1]ᵀ` is a right eigenvector of the substitution
matrix. Added hypothesis `m ≠ j + 1`: for `m = j + 1`, `τ_{j,j+1} = j + 1 = m`, so (i) and (ii)
read `0/0` and the printed equivalence is meaningless.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 62
(`jis-2025-25.1.5-prop-62`). -/
public theorem_wanted pisa_frequency_tfae (j m : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m) (hjm : m ≠ j + 1)
    (ϱ : Bool → List Bool) (hprim : ∃ p, ∀ i j, 0 <
        ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {w : ℕ → Bool} (hfix : IsSubstitutionImage ϱ w w) :
    let τ : ℝ := (j + Real.sqrt (j ^ 2 + 4 * m)) / 2
    [Tendsto (fun n : ℕ => (letterCount w true n : ℝ) / n) atTop (𝓝 ((τ - m) / (j + 1 - m))),
      Tendsto (fun n : ℕ => (letterCount w false n : ℝ) / n) atTop (𝓝 ((j + 1 - τ) / (j + 1 - m))),
      Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 (1 + (τ - j) / m)),
      Tendsto (fun n : ℕ => (letterPosition w false n : ℝ) / n) atTop (𝓝 (τ + 1)),
      Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (((m - 1) * τ + j) / m)),
      ∃ q : ℝ, Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 q) ∧
        Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 ((m - 1) * q + (j + 1 - m))),
      ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
          (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![τ,
          1] = c • ![τ, 1]].TFAE

/-- **Theorem 64.** (a) For `j ≥ 1`, `w = (a^j b^j)^ω` has `r(n) = j`. (b) For `0 ≤ j ≤ k - 1` and
`w` the one-sided fixed point of `σ_{k-j,j,1}`, `r(n) = kn - j`. (c) For `w` the one-sided fixed
point of `σ_{1,k-1,1}`, `r_{D(w)}(n) = kn + 1`. Domain restriction in (c): `k ≥ 1`; the paper
writes `k ≥ 0`, but `σ_{1,k-1,1}` needs `k - 1 ≥ 0`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 64
(`jis-2025-25.1.5-thm-64`). -/
public theorem_wanted linear_relativePosition_examples :
    (∀ j, 1 ≤ j → ∀ n, 1 ≤ n →
        relativePosition (fun i => decide (i % (2 * j) < j)) n = j) ∧
      (∀ k j : ℕ, j + 1 ≤ k → ∀ w : ℕ → Bool,
        IsSubstitutionImage (fun x : Bool => if x then List.replicate (k - j) true ++ [false] ++
            List.replicate j true else List.replicate 1 true) w w → w 0 = true →
        ∀ n, 1 ≤ n → relativePosition w n = k * n - j) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ w : ℕ → Bool,
        IsSubstitutionImage (fun x : Bool => if x then List.replicate 1 true ++ [false] ++
            List.replicate (k - 1) true else List.replicate 1 true) w w → w 0 = true →
        ∀ n, 1 ≤ n → relativePosition (deletion w) n = k * n + 1

/-- **Proposition 65**, corrected substitution. Let `k ≥ 1`, `j ∈ ℤ`, `j = qk - r` with
`0 ≤ r ≤ k - 1`, and let `w` be the one-sided fixed point of the Pisa substitution
`σ_{k-r,r,1}` (`a ↦ a^{k-r} b a^r`, `b ↦ a`). (a) If `q ≥ 0`, then `r_{D^q(w)}(n) = kn + j` for
all large `n`. (b) If `q < 0`, then for every equilibrious word `s` of length `-2q`,
`r_{sw}(n) = kn + j` for all large `n`.
Correction: the paper takes `w` to be the fixed point of `σ_{1,k-1,1}` for every `r`, which is
false unless `r = k - 1`: for `k = 2`, `j = 2` (`q = 1`, `r = 0`) that fixed point has
`r_{D(w)}(n) = 2n + 1` (Theorem 64(c)), not `2n + 2`. The substitution `σ_{k-r,r,1}` is the one
Theorem 64(b) provides (`r(n) = kn - r`), from which `D` (Section 2:
`r_{D(w)}(n) = r_w(n+1)` on `ab𝒲 ∪ ba𝒲`) and equilibrious prefixes (Lemma 22) shift the index by
`q`, giving every progression `kn + j` as the paper's
preceding sentence ("This can always be achieved") intends; for `r = k - 1` it is the paper's
`σ_{1,k-1,1}`. Domain restriction: `k ≥ 1` (the paper writes `k ≥ 0`, but `0 ≤ r ≤ k - 1` is then
empty). The instance `s = (ab)^{-q}` of (b) is omitted, being a special case.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 65
(`jis-2025-25.1.5-prop-65`). -/
public theorem_wanted relativePosition_eventually_eq_linear (k r : ℕ) (hk : 1 ≤ k) (hr : r < k)
    (q j : ℤ) (hj : j = q * k - r) (w : ℕ → Bool)
    (hw : IsSubstitutionImage (fun x : Bool => if x then List.replicate (k - r) true ++ [false] ++
        List.replicate r true else List.replicate 1 true) w w)
    (hw0 : w 0 = true) :
    (0 ≤ q → ∀ᶠ n in Filter.atTop, relativePosition (deletion^[q.toNat] w) n = k * n + j) ∧
      (q < 0 → ∀ u : List Bool, u.length = 2 * (-q).toNat →
        IsEquilibriousWord (u.map fun x => if x then 0 else 1) →
          ∀ᶠ n in Filter.atTop, relativePosition (u ++ₛ w) n = k * n + j)

open Filter Topology in
/-- **Theorem 67.** Let `ϱ` be a primitive binary substitution with substitution matrix `M` and
one-sided fixed point `w ∈ 𝒲`, `k ≥ 1` and `τ_k = (k + √(k² + 4))/2`. (a) `r(n)/n → k` iff
`[τ_k 1]ᵀ` is a right Perron–Frobenius eigenvector of `M` iff `M = [[km + n, m], [m, n]]` with
`m ≥ 1`, `n ≥ 0`. (b) `r(n)/n → -k` iff `[1 τ_k]ᵀ` is one iff `M = [[n, m], [m, km + n]]` with
`m ≥ 1`, `n ≥ 0`. (c) `r(n)/n → 0` iff `[1 1]ᵀ` is one iff the row sums `a + b`, `c + d` of
`M = [[a, b], [c, d]]` agree. The Perron–Frobenius conditions are stated as eigenvector
conditions (the vectors are positive, so the eigenvalue is the Perron–Frobenius one).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 67
(`jis-2025-25.1.5-thm-67`). -/
public theorem_wanted primitive_asymptotically_linear_classification (ϱ : Bool → List Bool)
    (hprim : ∃ p, ∀ i j, 0 < ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (hfix : IsSubstitutionImage ϱ w w)
    (k : ℕ) (hk : 1 ≤ k) :
    let τ : ℝ := (k + Real.sqrt (k ^ 2 + 4)) / 2
    [Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (k : ℝ)),
        ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![τ,
            1] = c • ![τ, 1],
        ∃ m n : ℕ, 1 ≤ m ∧ (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) = !![k * m + n, m; m, n]].TFAE ∧
      [Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (-(k : ℝ))),
        ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![1,
            τ] = c • ![1, τ],
        ∃ m n : ℕ, 1 ≤ m ∧ (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) = !![n, m; m, k * m + n]].TFAE ∧
      [Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 0),
        ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![1,
            1] = c • ![1, 1],
        (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 0 0 +
            (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 0 1 =
            (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 1 0 +
            (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 1 1].TFAE

/-- **Proposition 69.** If every dimer `X_n = ℓ_{2n} ℓ_{2n+1}` of `w` is `ab` or `ba`, then
`r(n) = 1` if `X_{n-1} = ab` and `r(n) = -1` if `X_{n-1} = ba`, for `n ≥ 1`. (The dimer condition
forces both letters to occur infinitely often, so no separate `w ∈ 𝒲` hypothesis is needed.)

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 69
(`jis-2025-25.1.5-prop-69`). -/
public theorem_wanted relativePosition_of_dimers {w : ℕ → Bool}
    (hdim : ∀ i, w (2 * i) ≠ w (2 * i + 1)) (n : ℕ) (hn : 1 ≤ n) :
    relativePosition w n = if w (2 * (n - 1)) then 1 else -1

/-- **Theorem 70.** The Thue–Morse word `t` is the only word `w ∈ a𝒲` with `w = r(1) r(2) ⋯` on
the letters `a = 1`, `b = -1`, i.e. with `r(n) = 1` if `ℓ_{n-1} = a` and `r(n) = -1` otherwise.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 70
(`jis-2025-25.1.5-thm-70`). -/
public theorem_wanted relativePosition_self_coding_iff_thueMorse {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    (∀ n, 1 ≤ n → relativePosition w n = if w (n - 1) then 1 else -1) ↔ w = (fun i => !thueMorse i)

/-- **Corollary 71.** The Thue–Morse word is the only word in `abba𝒲` isomorphic to
`r(1) r(2) ⋯` (`r(n)` an injective coding of `ℓ_{n-1}`).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 71
(`jis-2025-25.1.5-cor-71`). -/
public theorem_wanted relativePosition_isomorphic_iff_thueMorse {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) (h₁ : w 1 = false) (h₂ : w 2 = false)
    (h₃ : w 3 = true) :
    (∃ σ : Bool → ℤ, Function.Injective σ ∧ ∀ n, 1 ≤ n → relativePosition w n = σ (w (n - 1))) ↔
      w = (fun i => !thueMorse i)

/-- **Theorem 72.** For `k > 1`, `φ_k(t)` is the only word `w ∈ a𝒲` with `w = r(1) r(2) ⋯` on the
letters `a = k`, `b = -k`.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 72
(`jis-2025-25.1.5-thm-72`). -/
public theorem_wanted relativePosition_self_coding_iff_clone_thueMorse (k : ℕ) (hk : 1 < k)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    (∀ n, 1 ≤ n → relativePosition w n = if w (n - 1) then (k : ℤ) else -k) ↔
      w = fun i => !thueMorse (i / k)

end

end MetaMathlibExt
