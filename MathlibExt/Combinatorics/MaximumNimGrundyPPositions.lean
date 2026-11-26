/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MaximumNimJosephus
public import MathlibExt.GameTheory.SpragueGrundy

/-!
# P-positions of Maximum Nim

The move recursion for P-positions agrees with the recursion for having Grundy value zero.
The proof uses only that a move strictly decreases the pile size; the public theorem keeps the
rule-function hypotheses of its original statement.

## References

* Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
  INTEGERS 24 (2024), Article G5, pp. 1–16, Section 2 and Theorem 1
  (<https://math.colgate.edu/~integers/yg5/yg5.pdf>).
* Michael H. Albert, Richard J. Nowakowski, David Wolfe, *Lessons In Play: An Introduction to
  Combinatorial Game Theory*, 2nd ed., A K Peters/CRC Press, 2019. Takahashi, Manabe and Miyadera
  cite this book for the general Grundy-zero characterization of P-positions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The Maximum Nim game.** For a rule function $f : \mathbb{N} \to \mathbb{N}$, the Maximum Nim
game with rule $f$ is the impartial game whose positions are the pile sizes $x \in \mathbb{N}$, in
which the moves from $x$ go to $x - u$ for each $u$ with $1 \le u \le \min(f(x), x)$. The rank of
a position is the pile size itself, and the starting position is the empty pile $0$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public def maximumNimGame (f : ℕ → ℕ) : SpragueGrundy.ImpartialGame where
  Pos := ℕ
  eqDec := inferInstance
  moves := fun x => (Finset.Icc 1 (min (f x) x)).image (fun u => x - u)
  rank := id
  rank_lt := by
    intro x y h
    simp only [Finset.mem_image, Finset.mem_Icc] at h
    obtain ⟨u, ⟨h1, h2⟩, rfl⟩ := h
    simp only [id_eq]
    omega
  start := 0

/-- **P-positions of Maximum Nim.** Let $f : \mathbb{N} \to \mathbb{N}$ be a rule function and let
$x$ be a pile size. The position $x$ of the Maximum Nim game with rule $f$ is a P-position
if and only if, for every $u$ with $1 \le u \le \min(f(x), x)$, the position $x - u$ is not
a P-position.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public theorem maximumNimGame_isP_iff (f : ℕ → ℕ) (x : ℕ) :
    SpragueGrundy.IsP (maximumNimGame f) x ↔
      ∀ u, 1 ≤ u → u ≤ min (f x) x → ¬SpragueGrundy.IsP (maximumNimGame f) (x - u) := by
  refine (SpragueGrundy.isP_iff (maximumNimGame f) x).trans ?_
  change (∀ q : ℕ, q ∈ (Finset.Icc 1 (min (f x) x)).image (fun u => x - u) →
      ¬SpragueGrundy.IsP (maximumNimGame f) q) ↔ _
  constructor
  · intro h u h1 h2
    exact h (x - u) (Finset.mem_image.mpr ⟨u, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩)
  · intro h q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    exact h u (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hu).2

-- The original statement keeps the rule hypotheses, although neither recursion needs them.
set_option linter.unusedVariables false in
/-- **Grundy value zero characterizes P-positions in Maximum Nim.** Let $f : \mathbb{N} \to
\mathbb{N}$ satisfy $f(0) = 0$ and $f(m-1) \le f(m) \le f(m-1) + 1$ for every $m \ge 1$. Then for
every pile size $x \in \mathbb{N}$, the Grundy number of $x$ in Maximum Nim with rule function $f$
is $0$ if and only if $x$ is a P-position (a previous-player win under normal play) of that game.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Theorem 1 (`integers-2024-G5-thm-1`). -/
public theorem maximumNimGrundy_eq_zero_iff_isP (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hf : ∀ m, 1 ≤ m → f (m - 1) ≤ f m ∧ f m ≤ f (m - 1) + 1) (x : ℕ) :
    maximumNimGrundy f x = 0 ↔ SpragueGrundy.IsP (maximumNimGame f) x := by
  clear hf0 hf
  induction x using Nat.strong_induction_on
  rename_i x ih
  rw [maximumNimGrundy_eq f x, maximumNimMex_eq_iff, maximumNimGame_isP_iff]
  have hlt (u : ℕ) (hu : 1 ≤ u) (hux : u ≤ min (f x) x) : x - u < x := by omega
  constructor
  · intro h u hu hux hp
    exact h.1 (Finset.mem_image.mpr
      ⟨⟨u, Finset.mem_Icc.mpr ⟨hu, hux⟩⟩, Finset.mem_attach _ _, (ih _ (hlt u hu hux)).mpr hp⟩)
  · intro h
    refine ⟨?_, fun n hn => (Nat.not_lt_zero n hn).elim⟩
    intro hm
    obtain ⟨⟨u, hu⟩, -, heq⟩ := Finset.mem_image.mp hm
    obtain ⟨hu, hux⟩ := Finset.mem_Icc.mp hu
    exact h u hu hux ((ih _ (hlt u hu hux)).mp heq)

end

end MetaMathlibExt
