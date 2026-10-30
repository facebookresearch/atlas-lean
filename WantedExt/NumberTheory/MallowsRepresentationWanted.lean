/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity
public import MathlibExt.NumberTheory.ContinuedFractions.LagrangePeriodic

/-!
# The Mallows representation of the irrational numbers (wanted statements)

Statements from Takanori Hida, *The Mallows Representation of the Irrational Numbers*,
INTEGERS 25 (2025), Article A78.

Fractions are pairs `(n, m) : ℕ × ℕ` (numerator, denominator); a vertex of the Stern–Brocot
or Mallows tree is encoded by its path from the root (a list of letters) or by the gap
`(a, b)` of adjacent fractions in which its label is inserted. Sequences indexed by
`i ≥ 1` in the paper are indexed by `i ≥ 0` here (paper index `i` is Lean index `i - 1`).
The irrational numbers of `(0, 1)` form the set `{α | α ∈ Set.Ioo 0 1 ∧ Irrational α}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The letters `L`, `M`, `R` ("left", "middle", "right") of Mallows representations.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 4. -/
inductive MallowsLetter
  | L
  | M
  | R
  deriving DecidableEq

/-- The alphabet `{L, M, R}` is finite.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 4. -/
instance : Fintype MallowsLetter :=
  Fintype.ofList [.L, .M, .R] fun x => by cases x <;> simp

/-- The letters `L`, `R` of Stern–Brocot representations.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
inductive SternBrocotLetter
  | L
  | R
  deriving DecidableEq

/-- The four letters `O_L`, `E_R`, `O_R`, `E_L` of the intermediate set `I` linking the
Stern–Brocot and Mallows representations.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
inductive MallowsParityLetter
  | OL
  | ER
  | OR
  | EL
  deriving DecidableEq

/-- The real value `n / m` of a fraction encoded as the pair `(n, m)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2 (fractions `n / m` labelling the trees). -/
noncomputable def natPairToReal (p : ℕ × ℕ) : ℝ :=
  (p.1 : ℝ) / p.2

/-- Characteristic value: the pair `(1, 2)` encodes `1 / 2`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2. -/
theorem natPairToReal_one_two : natPairToReal (1, 2) = 1 / 2 := by
  norm_num [natPairToReal]

/-- The mediant `(n₁ + n₂) / (m₁ + m₂)` of the two fractions bounding a gap `(a, b)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 1 (mediant construction). -/
def gapMediant (I : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (I.1.1 + I.2.1, I.1.2 + I.2.2)

/-- Characteristic value: the mediant of `0 / 1` and `1 / 1` is `1 / 2`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 1. -/
theorem gapMediant_root : gapMediant ((0, 1), (1, 1)) = (1, 2) := rfl

/-- Mallows' insertion rule: between adjacent fractions `n₁ / m₁ < n₂ / m₂` insert
`⟨(n₁ + n₂)/(m₁ + m₂), (n₁ + 2n₂)/(m₁ + 2m₂)⟩` if `n₁` is even and
`⟨(2n₁ + n₂)/(2m₁ + m₂), (n₁ + n₂)/(m₁ + m₂)⟩` if `n₁` is odd.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3 (definition of `MT_{i+1}`). -/
def mallowsInsert (a b : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  if a.1 % 2 = 0 then ((a.1 + b.1, a.2 + b.2), (a.1 + 2 * b.1, a.2 + 2 * b.2))
  else ((2 * a.1 + b.1, 2 * a.2 + b.2), (a.1 + b.1, a.2 + b.2))

/-- Characteristic value: `MT_1 = ⟨1/2, 2/3⟩`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3. -/
theorem mallowsInsert_zero_one : mallowsInsert (0, 1) (1, 1) = ((1, 2), (2, 3)) := by
  decide

/-- Characteristic value (odd numerator branch): between `1/2` and `2/3` Mallows inserts
`4/7` and `3/5`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 1. -/
theorem mallowsInsert_half_twoThirds : mallowsInsert (1, 2) (2, 3) = ((4, 7), (3, 5)) := by
  decide

/-- One refinement step `{0/1, 1/1} ∪ MT_1 ∪ ⋯ ∪ MT_i ↦ {0/1, 1/1} ∪ MT_1 ∪ ⋯ ∪ MT_{i+1}` of an
increasing list of fractions: Mallows' insertion between each pair of adjacent fractions.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3. -/
def mallowsRefine : List (ℕ × ℕ) → List (ℕ × ℕ)
  | a :: b :: rest =>
      a :: (mallowsInsert a b).1 :: (mallowsInsert a b).2 :: mallowsRefine (b :: rest)
  | l => l

/-- The fractions Mallows inserts into an increasing list of fractions, in order.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3. -/
def mallowsInserted : List (ℕ × ℕ) → List (ℕ × ℕ)
  | a :: b :: rest => (mallowsInsert a b).1 :: (mallowsInsert a b).2 :: mallowsInserted (b :: rest)
  | _ => []

/-- The ordered set `MT_{i+1}` of the `2 ⋅ 3^i` fractions inserted at step `i + 1`
(Lean index `i`).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3. -/
def mallowsLevel (i : ℕ) : List (ℕ × ℕ) :=
  mallowsInserted (mallowsRefine^[i] [(0, 1), (1, 1)])

/-- Characteristic value: `MT_2 = ⟨1/3, 2/5, 4/7, 3/5, 3/4, 4/5⟩`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 1 and Figure 2. -/
theorem mallowsLevel_one :
    mallowsLevel 1 = [(1, 3), (2, 5), (4, 7), (3, 5), (3, 4), (4, 5)] := by
  decide

/-- The left, middle and right child gaps of a Mallows-tree vertex inserted in the gap
`(a, b)`: if `⟨p, q⟩` is the pair inserted in `(a, b)`, the children are the pairs inserted in
`(a, p)`, `(p, q)` and `(q, b)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 3. -/
def mallowsChild (I : (ℕ × ℕ) × (ℕ × ℕ)) : MallowsLetter → (ℕ × ℕ) × (ℕ × ℕ)
  | .L => (I.1, (mallowsInsert I.1 I.2).1)
  | .M => mallowsInsert I.1 I.2
  | .R => ((mallowsInsert I.1 I.2).2, I.2)

/-- The gap of the Mallows-tree vertex reached from the root by the path `w`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 3. -/
def mallowsNode (w : List MallowsLetter) : (ℕ × ℕ) × (ℕ × ℕ) :=
  w.foldl mallowsChild ((0, 1), (1, 1))

/-- The label (a pair of fractions) of the Mallows-tree vertex reached by the path `w`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 3 and Figure 3. -/
def mallowsLabel (w : List MallowsLetter) : (ℕ × ℕ) × (ℕ × ℕ) :=
  mallowsInsert (mallowsNode w).1 (mallowsNode w).2

/-- Characteristic values: the root is labelled `⟨1/2, 2/3⟩`, its middle child `⟨4/7, 3/5⟩`
and its right child `⟨3/4, 4/5⟩`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Figure 3. -/
theorem mallowsLabel_small :
    mallowsLabel [] = ((1, 2), (2, 3)) ∧ mallowsLabel [.M] = ((4, 7), (3, 5)) ∧
      mallowsLabel [.R] = ((3, 4), (4, 5)) := by
  decide

/-- The letter chosen at a Mallows vertex with gap `I` and label `⟨p, q⟩`: `L` if `α < p`,
`M` if `p < α < q`, and `R` otherwise.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 4. -/
noncomputable def mallowsChoose (α : ℝ) (I : (ℕ × ℕ) × (ℕ × ℕ)) : MallowsLetter :=
  if α < natPairToReal (mallowsInsert I.1 I.2).1 then .L
  else if α < natPairToReal (mallowsInsert I.1 I.2).2 then .M else .R

/-- The gap of the vertex `pf_{i+1}(α)` visited at step `i + 1` of the Mallows representation.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 4. -/
noncomputable def mallowsInterval (α : ℝ) : ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((0, 1), (1, 1))
  | i + 1 => mallowsChild (mallowsInterval α i) (mallowsChoose α (mallowsInterval α i))

/-- The Mallows representation `M(α) = ⟨M_1(α), M_2(α), …⟩`; `mallowsRep α i` is `M_{i+1}(α)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 4. -/
noncomputable def mallowsRep (α : ℝ) (i : ℕ) : MallowsLetter :=
  mallowsChoose α (mallowsInterval α i)

/-- Characteristic value: `M_1(α) = L` for `α < 1/2`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 4 and Figure 4. -/
theorem mallowsRep_zero_of_lt {α : ℝ} (h : α < 1 / 2) : mallowsRep α 0 = .L := by
  have h' : α < natPairToReal (mallowsInsert (0, 1) (1, 1)).1 := by
    rw [mallowsInsert_zero_one, natPairToReal_one_two]; exact h
  simp only [mallowsRep, mallowsInterval, mallowsChoose]
  exact ite_eq_left_of_eq_true _ _ (eq_true h')

/-- The child gap of a Stern–Brocot vertex with gap `(a, b)` (label `a ⊕ b`).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 1. -/
def sternBrocotChild (I : (ℕ × ℕ) × (ℕ × ℕ)) : SternBrocotLetter → (ℕ × ℕ) × (ℕ × ℕ)
  | .L => (I.1, gapMediant I)
  | .R => (gapMediant I, I.2)

/-- The label of the Stern–Brocot-tree vertex (of the left subtree, root `1/2`) reached from
the root by the path `w`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 1 and Figure 1. -/
def sternBrocotLabel (w : List SternBrocotLetter) : ℕ × ℕ :=
  gapMediant (w.foldl sternBrocotChild ((0, 1), (1, 1)))

/-- Characteristic values: the root is `1/2`; the path `L R` leads to `2/5`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Figure 1. -/
theorem sternBrocotLabel_small :
    sternBrocotLabel [] = (1, 2) ∧ sternBrocotLabel [.L, .R] = (2, 5) := by
  decide

/-- The letter chosen at a Stern–Brocot vertex with gap `I`: `L` if `α` is below its label.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
noncomputable def sternBrocotChoose (α : ℝ) (I : (ℕ × ℕ) × (ℕ × ℕ)) : SternBrocotLetter :=
  if α < natPairToReal (gapMediant I) then .L else .R

/-- The gap of the Stern–Brocot vertex `f_{j+1}(α)` visited at step `j + 1`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
noncomputable def sternBrocotInterval (α : ℝ) : ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((0, 1), (1, 1))
  | j + 1 => sternBrocotChild (sternBrocotInterval α j)
      (sternBrocotChoose α (sternBrocotInterval α j))

/-- The fraction `f_{j+1}(α)` of the Stern–Brocot path of `α`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
noncomputable def sternBrocotFrac (α : ℝ) (j : ℕ) : ℕ × ℕ :=
  gapMediant (sternBrocotInterval α j)

/-- Characteristic value: `f_1(α) = 1/2`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
theorem sternBrocotFrac_zero (α : ℝ) : sternBrocotFrac α 0 = (1, 2) := rfl

/-- The Stern–Brocot representation `SB(α)`; `sternBrocotRep α j` is `SB_{j+1}(α)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
noncomputable def sternBrocotRep (α : ℝ) (j : ℕ) : SternBrocotLetter :=
  sternBrocotChoose α (sternBrocotInterval α j)

/-- Characteristic value: `SB_1(α) = L` for `α < 1/2`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Definition 2. -/
theorem sternBrocotRep_zero_of_lt {α : ℝ} (h : α < 1 / 2) : sternBrocotRep α 0 = .L := by
  have h' : α < natPairToReal (gapMediant ((0, 1), (1, 1))) := by
    rw [gapMediant_root, natPairToReal_one_two]; exact h
  simp only [sternBrocotRep, sternBrocotInterval, sternBrocotChoose]
  exact ite_eq_left_of_eq_true _ _ (eq_true h')

/-- The map `φ_SBT` on a Stern–Brocot vertex with gap `I` (label `f`, children `l`, `r`):
`⟨l, f⟩` if the left child `l` has even numerator and `⟨f, r⟩` otherwise.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3 (definition of `φ_SBT`). -/
def sternBrocotPhi (I : (ℕ × ℕ) × (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if (gapMediant (I.1, gapMediant I)).1 % 2 = 0 then
    [gapMediant (I.1, gapMediant I), gapMediant I]
  else [gapMediant I, gapMediant (gapMediant I, I.2)]

/-- The map `ψ_SBT` on a Stern–Brocot vertex with gap `I`: the left child followed by the two
children of the right child if the left child has odd numerator, and otherwise the two
children of the left child followed by the right child (vertices encoded by their gaps).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3 (definition of `ψ_SBT`). -/
def sternBrocotPsi (I : (ℕ × ℕ) × (ℕ × ℕ)) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  if (gapMediant (I.1, gapMediant I)).1 % 2 = 1 then
    [(I.1, gapMediant I), (gapMediant I, gapMediant (gapMediant I, I.2)),
      (gapMediant (gapMediant I, I.2), I.2)]
  else
    [(I.1, gapMediant (I.1, gapMediant I)), (gapMediant (I.1, gapMediant I), gapMediant I),
      (gapMediant I, I.2)]

/-- Characteristic values at the root `1/2`: `φ_SBT(1/2) = ⟨1/2, 2/3⟩` and
`ψ_SBT(1/2) = ⟨1/3, 3/5, 3/4⟩` (gaps `(0/1, 1/2)`, `(1/2, 2/3)`, `(2/3, 1/1)`).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 2.3. -/
theorem sternBrocotPhi_psi_root :
    sternBrocotPhi ((0, 1), (1, 1)) = [(1, 2), (2, 3)] ∧
      sternBrocotPsi ((0, 1), (1, 1)) =
        [((0, 1), (1, 2)), ((1, 2), (2, 3)), ((2, 3), (1, 1))] := by
  decide

/-- The transition rule defining `Q_{j+1}` from `Q_j` and the letter `x_j`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3 (definition of `Q`, Figure 5). -/
def mallowsQStep : MallowsParityLetter → SternBrocotLetter → MallowsParityLetter
  | .OL, .L => .OL
  | .OL, .R => .ER
  | .ER, .L => .OR
  | .ER, .R => .OL
  | .OR, .L => .EL
  | .OR, .R => .OR
  | .EL, .L => .OR
  | .EL, .R => .OL

/-- The sequence `Q(x) = ⟨Q_1(x), Q_2(x), …⟩` with `Q_1 = O_L` and `Q_{j+1} = step(Q_j, x_j)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
def mallowsQ (x : ℕ → SternBrocotLetter) : ℕ → MallowsParityLetter
  | 0 => .OL
  | j + 1 => mallowsQStep (mallowsQ x j) (x j)

/-- Characteristic values: `Q_1 = O_L`, and on `⟨R, L, …⟩` the next values are `E_R`, `O_R`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
theorem mallowsQ_small (x : ℕ → SternBrocotLetter) (h0 : x 0 = .R) (h1 : x 1 = .L) :
    mallowsQ x 0 = .OL ∧ mallowsQ x 1 = .ER ∧ mallowsQ x 2 = .OR := by
  simp [mallowsQ, mallowsQStep, h0, h1]

/-- The set `I` of infinite sequences over `{O_L, E_R, O_R, E_L}` starting with `O_L` and
containing none of the factors `⟨O_L,O_R⟩, ⟨O_L,E_L⟩, ⟨E_R,E_L⟩, ⟨E_R,E_R⟩, ⟨O_R,O_L⟩,
⟨O_R,E_R⟩, ⟨E_L,E_L⟩, ⟨E_L,E_R⟩` and no tail `⟨O_L⟩^∞`, `⟨O_R⟩^∞`, `⟨O_L,E_R⟩^∞`,
`⟨O_R,E_L⟩^∞`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
def mallowsAdmissible : Set (ℕ → MallowsParityLetter) :=
  {x | x 0 = .OL ∧
    (∀ j, (x j, x (j + 1)) ∉ [(.OL, .OR), (.OL, .EL), (.ER, .EL), (.ER, .ER), (.OR, .OL),
      (.OR, .ER), (.EL, .EL), (.EL, .ER)]) ∧
    (¬ ∃ j₀, ∀ j, j₀ ≤ j → x j = .OL) ∧ (¬ ∃ j₀, ∀ j, j₀ ≤ j → x j = .OR) ∧
    (¬ ∃ j₀, ∀ t, x (j₀ + 2 * t) = .OL ∧ x (j₀ + 2 * t + 1) = .ER) ∧
    (¬ ∃ j₀, ∀ t, x (j₀ + 2 * t) = .OR ∧ x (j₀ + 2 * t + 1) = .EL)}

/-- Characteristic property: the constant sequence `⟨O_L⟩^∞` is not in `I`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
theorem const_OL_not_mem_mallowsAdmissible :
    (fun _ => MallowsParityLetter.OL) ∉ mallowsAdmissible :=
  fun h => h.2.2.1 ⟨0, fun _ _ => rfl⟩

/-- The enumeration `o(1) < o(2) < ⋯` of the positions `j` with `x_j ∈ {O_L, O_R}`;
`mallowsOddIndex x i` is `o(i+1) - 1`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
noncomputable def mallowsOddIndex (x : ℕ → MallowsParityLetter) : ℕ → ℕ :=
  Nat.nth fun j => x j = .OL ∨ x j = .OR

/-- Characteristic value: the first `O_L`/`O_R` position of a sequence starting with `O_L` is
`0`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3 (`o(1) = 1`). -/
theorem mallowsOddIndex_zero {x : ℕ → MallowsParityLetter} (h : x 0 = .OL) :
    mallowsOddIndex x 0 = 0 :=
  Nat.nth_zero_of_zero (Or.inl h)

/-- The letter `T_i`: when the next odd position is adjacent (`adj`), `L` for `O_L` and `R` for
`O_R`; otherwise `L` if both odd letters are `O_R`, `R` if both are `O_L`, and `M` if they
differ.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3 (definition of `T_i`). -/
def mallowsTLetter (adj : Bool) (a b : MallowsParityLetter) : MallowsLetter :=
  if adj then (if a = .OL then .L else .R)
  else if a = b then (if a = .OR then .L else .R) else .M

/-- The sequence `T(x) = ⟨T_1(x), T_2(x), …⟩` over `{L, M, R}`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 3. -/
noncomputable def mallowsT (x : ℕ → MallowsParityLetter) (i : ℕ) : MallowsLetter :=
  mallowsTLetter (decide (mallowsOddIndex x (i + 1) = mallowsOddIndex x i + 1))
    (x (mallowsOddIndex x i)) (x (mallowsOddIndex x (i + 1)))

/-- The finite version `Ṫ` of `T`, computed from the list of positions of `O_L`/`O_R`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 4.3 (definition of `Ṫ`). -/
def mallowsTFin (y : List MallowsParityLetter) : List MallowsLetter :=
  let os := (List.range y.length).filter fun j => y.getD j .ER = .OL ∨ y.getD j .ER = .OR
  (os.zip os.tail).map fun pq =>
    mallowsTLetter (decide (pq.2 = pq.1 + 1)) (y.getD pq.1 .ER) (y.getD pq.2 .ER)

/-- Characteristic values: `Ṫ⟨O_L, E_R, O_R⟩ = ⟨M⟩` and `Ṫ⟨O_L, O_L⟩ = ⟨L⟩`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 4.3. -/
theorem mallowsTFin_small :
    mallowsTFin [.OL, .ER, .OR] = [.M] ∧ mallowsTFin [.OL, .OL] = [.L] := by
  decide

/-- Positive Poisson stability of a point of the one-sided shift: there is `n₀` such that for
every length `ℓ` the block of length `ℓ` at `n₀` recurs at some shift `p ≥ 1`. This is the
source's shift-space criterion for "the positive orbit of `x` meets its ω-limit set"; the
recurring point is the orbit point `σ^{n₀} x`, not necessarily `x` itself (so `false, true, true, …`
qualifies).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 4.2. -/
def IsPositivelyPoissonStable {A : Type*} (x : ℕ → A) : Prop :=
  ∃ n₀ : ℕ, ∀ ℓ : ℕ, ∃ p : ℕ, 0 < p ∧ ∀ t < ℓ, x (n₀ + p + t) = x (n₀ + t)

/-- Characteristic property: constant sequences are positively Poisson stable.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Section 4.2. -/
theorem isPositivelyPoissonStable_const {A : Type*} (c : A) :
    IsPositivelyPoissonStable (fun _ : ℕ => c) :=
  ⟨0, fun _ => ⟨1, Nat.one_pos, fun _ _ => rfl⟩⟩

/-- Stern–Brocot tree (left subtree, root `1/2`): (i) every fraction of `(0, 1) ∩ ℚ` labels
exactly one vertex; (ii) on each level the left-to-right (lexicographic, `L < R`) order agrees
with the increasing order; (iii) the path to the vertex whose label has continued fraction
`[0; a_1, …, a_ℓ]` (`a_ℓ ≥ 2`, as produced by `GenContFract.of`) is
`L^{a_1 - 1} R^{a_2} L^{a_3} ⋯` with last block of length `a_ℓ - 1` (`L^{a_1 - 2}` if `ℓ = 1`).
Vertices are paths `w`; in (ii) two paths of the same length first differ by `L` versus `R`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 1 (`integers-2025-A78-prop-1`). -/
public theorem_wanted sternBrocotTree_label_unique_order_path :
    (∀ q : ℚ, 0 < q → q < 1 →
      ∃! w : List SternBrocotLetter, natPairToReal (sternBrocotLabel w) = q) ∧
    (∀ u v₁ v₂ : List SternBrocotLetter, v₁.length = v₂.length →
      natPairToReal (sternBrocotLabel (u ++ .L :: v₁)) <
        natPairToReal (sternBrocotLabel (u ++ .R :: v₂))) ∧
    ∀ (w : List SternBrocotLetter) (a : List ℕ),
      (∀ k (hk : k < a.length),
        (GenContFract.of (natPairToReal (sternBrocotLabel w))).partDens.get? k = some (a[k] : ℝ)) →
      (GenContFract.of (natPairToReal (sternBrocotLabel w))).partDens.get? a.length = none →
      w = (List.range a.length).flatMap fun k =>
        List.replicate (a.getD k 0 - (if k = 0 then 1 else 0) - (if k + 1 = a.length then 1 else 0))
          (if Even k then SternBrocotLetter.L else SternBrocotLetter.R)

/-- Stern–Brocot representation: (i) the fractions `f_j(α)` converge to `α`; (ii)
`SB(α) = L^{a_1 - 1} R^{a_2} L^{a_3} R^{a_4} ⋯` for `α = [0; a_1, a_2, …]`. In (ii) the digit
sequence is `a k = a_{k+1}`, and position `j` (paper `j + 1`) with
`a_1 + ⋯ + a_k ≤ j + 1 < a_1 + ⋯ + a_{k+1}` carries `L` for even `k`, `R` for odd `k`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 2 (`integers-2025-A78-prop-2`). -/
public theorem_wanted sternBrocotRep_tendsto_and_contFract (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) (a : ℕ → ℕ)
    (ha : ∀ k, (GenContFract.of α).partDens.get? k = some (a k : ℝ)) :
    Filter.Tendsto (fun j => natPairToReal (sternBrocotFrac α j)) Filter.atTop (nhds α) ∧
      ∀ j k, ∑ i ∈ Finset.range k, a i ≤ j + 1 → j + 1 < ∑ i ∈ Finset.range (k + 1), a i →
        sternBrocotRep α j = if Even k then .L else .R

/-- The Stern–Brocot representations of the irrationals of `(0, 1)` are exactly the
sequences over `{L, R}` that are not eventually constant.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Corollary 1 (`integers-2025-A78-cor-1`). -/
public theorem_wanted image_sternBrocotRep :
    (fun α => sternBrocotRep α) '' {α : ℝ | α ∈ Set.Ioo 0 1 ∧ Irrational α} =
      {x | (¬ ∃ j₀, ∀ j, j₀ ≤ j → x j = .L) ∧ ¬ ∃ j₀, ∀ j, j₀ ≤ j → x j = .R}

/-- Mallows tree: (i) every fraction of `(0, 1) ∩ ℚ` appears exactly once in some `MT_i`, i.e. as
exactly one side (`false` left, `true` right) of exactly one vertex label; (ii) on each `MT_i`
the left-to-right order agrees with the increasing order: each label `⟨p, q⟩` has `p < q`, and
if two paths of the same length first differ by `L < M`, `L < R` or `M < R`, the right element
of the first label is below the left element of the second.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 3 (`integers-2025-A78-prop-3`). -/
public theorem_wanted mallowsTree_label_unique_order :
    (∀ q : ℚ, 0 < q → q < 1 → ∃! p : List MallowsLetter × Bool,
      natPairToReal (if p.2 then (mallowsLabel p.1).2 else (mallowsLabel p.1).1) = q) ∧
    (∀ w : List MallowsLetter,
      natPairToReal (mallowsLabel w).1 < natPairToReal (mallowsLabel w).2) ∧
    ∀ (u v₁ v₂ : List MallowsLetter) (b c : MallowsLetter), v₁.length = v₂.length →
      (b, c) ∈ [(.L, .M), (.L, .R), (.M, .R)] →
      natPairToReal (mallowsLabel (u ++ b :: v₁)).2 < natPairToReal (mallowsLabel (u ++ c :: v₂)).1

/-- `MT_i = φ_SBT(ψ_SBT^{i-1}(⟨1/2⟩))` for every `i ≥ 1` (quoted from Hida, J. Comb. 14 (2023)).
Stern–Brocot vertices are encoded by their gaps, `ψ_SBT` and `φ_SBT` are extended to lists by
concatenation, and the root `1/2` is the gap `(0/1, 1/1)`; Lean index `i` is paper `i + 1`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 1 (`integers-2025-A78-thm-1`). -/
public theorem_wanted mallowsLevel_eq_phi_psi_iterate (i : ℕ) :
    mallowsLevel i =
      ((fun l : List ((ℕ × ℕ) × (ℕ × ℕ)) => l.flatMap sternBrocotPsi)^[i]
        [((0, 1), (1, 1))]).flatMap sternBrocotPhi

/-- The Mallows representations of the irrationals of `(0, 1)` are exactly the sequences over
`{L, M, R}` that are not eventually `L` and not eventually `R`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 4 (`integers-2025-A78-prop-4`). -/
public theorem_wanted image_mallowsRep :
    (fun α => mallowsRep α) '' {α : ℝ | α ∈ Set.Ioo 0 1 ∧ Irrational α} =
      {x | (¬ ∃ i₀, ∀ i, i₀ ≤ i → x i = .L) ∧ ¬ ∃ i₀, ∀ i, i₀ ≤ i → x i = .R}

/-- For every irrational `α ∈ (0, 1)`, `Q(SB(α))` belongs to `I`, and `Q` is a bijection from the
set of Stern–Brocot representations onto `I` (`Set.BijOn` includes the first claim).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 5 (`integers-2025-A78-prop-5`). -/
public theorem_wanted bijOn_mallowsQ :
    Set.BijOn mallowsQ
      ((fun α => sternBrocotRep α) '' {α : ℝ | α ∈ Set.Ioo 0 1 ∧ Irrational α}) mallowsAdmissible

/-- For irrational `α ∈ (0, 1)` and every `j`: (i) the numerator of `f_j(α)` is odd iff
`Q_j(SB(α)) ∈ {O_L, O_R}`; (ii) `f_j(α)` is the left (resp. right) element of the Mallows label
containing it iff `Q_j(SB(α)) ∈ {O_L, E_L}` (resp. `{O_R, E_R}`). Part (ii) is stated as: some
label contains `f_j(α)`, and every label having it as left (resp. right) element forces the
corresponding letters; with Proposition 3 this is the paper's equivalence.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 6 (`integers-2025-A78-prop-6`). -/
public theorem_wanted sternBrocotFrac_parity_side (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α)
    (j : ℕ) :
    (Odd (sternBrocotFrac α j).1 ↔
      mallowsQ (sternBrocotRep α) j = .OL ∨ mallowsQ (sternBrocotRep α) j = .OR) ∧
    (∃ w : List MallowsLetter,
      sternBrocotFrac α j = (mallowsLabel w).1 ∨ sternBrocotFrac α j = (mallowsLabel w).2) ∧
    ∀ w : List MallowsLetter,
      (sternBrocotFrac α j = (mallowsLabel w).1 →
        mallowsQ (sternBrocotRep α) j = .OL ∨ mallowsQ (sternBrocotRep α) j = .EL) ∧
      (sternBrocotFrac α j = (mallowsLabel w).2 →
        mallowsQ (sternBrocotRep α) j = .OR ∨ mallowsQ (sternBrocotRep α) j = .ER)

/-- For `x ∈ I`, consecutive positions of `O_L`/`O_R` are at distance one or two:
`o(i+1) > o(i) + 1` iff `o(i+1) = o(i) + 2`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 7 (`integers-2025-A78-prop-7`). -/
public theorem_wanted mallowsOddIndex_gap (x : ℕ → MallowsParityLetter)
    (hx : x ∈ mallowsAdmissible) (i : ℕ) :
    mallowsOddIndex x i + 1 < mallowsOddIndex x (i + 1) ↔
      mallowsOddIndex x (i + 1) = mallowsOddIndex x i + 2

/-- `T` maps `I` bijectively onto the set of Mallows representations (`Set.BijOn` includes
the membership claim).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 8 (`integers-2025-A78-prop-8`). -/
public theorem_wanted bijOn_mallowsT :
    Set.BijOn mallowsT mallowsAdmissible
      ((fun α => mallowsRep α) '' {α : ℝ | α ∈ Set.Ioo 0 1 ∧ Irrational α})

/-- For irrational `α ∈ (0, 1)` and `i ≥ 1`, `φ_SBT(f_{o(i)}(α)) = pf_i(α)`. The vertex
`f_{o(i)}(α)` is encoded by its gap, `pf_i(α)` is the label `⟨p, q⟩` inserted in the gap
`mallowsInterval α (i - 1)`, written as the list `[p, q]`, and `o` is computed on `Q(SB(α))`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Lemma 1 (`integers-2025-A78-lem-1`). -/
public theorem_wanted sternBrocotPhi_oddIndex (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α)
    (i : ℕ) :
    sternBrocotPhi (sternBrocotInterval α (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i)) =
      [(mallowsInsert (mallowsInterval α i).1 (mallowsInterval α i).2).1,
        (mallowsInsert (mallowsInterval α i).1 (mallowsInterval α i).2).2]

/-- Main link: `T(Q(SB(α))) = M(α)` for every irrational `α ∈ (0, 1)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 2 (`integers-2025-A78-thm-2`). -/
public theorem_wanted mallowsT_mallowsQ_sternBrocotRep (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    mallowsT (mallowsQ (sternBrocotRep α)) = mallowsRep α

/-- Block-matching lemma. (i) Equal length-`ℓ` blocks of `SB(α)` at `j₁`, `j₂` together with
`Q_{j₁} = Q_{j₂}` are equivalent to equal length-`(ℓ+1)` blocks of `Q(SB(α))`. (ii) Equal
length-`ℓ` blocks of `T(Q(SB(α)))` at `i₁`, `i₂` together with `Q_{o(i₁)} = Q_{o(i₂)}` are
equivalent to equality of the blocks of `Q(SB(α))` from `o(i₁)` to `o(i₁ + ℓ)` and from `o(i₂)`
of the same length; then `o(i₂ + k) - o(i₂) = o(i₁ + k) - o(i₁)` for `k ≤ ℓ`. Domain extension:
the paper assumes `ℓ ≥ 1`, `j₁ < j₂`, `i₁ < i₂`; the statement is trivial for `ℓ = 0`,
symmetric in the two positions, and trivial for equal positions.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Lemma 2 (`integers-2025-A78-lem-2`). -/
public theorem_wanted block_match_sternBrocot_mallowsQ (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α)
    (ℓ j₁ j₂ i₁ i₂ : ℕ) :
    (((∀ t < ℓ, sternBrocotRep α (j₁ + t) = sternBrocotRep α (j₂ + t)) ∧
        mallowsQ (sternBrocotRep α) j₁ = mallowsQ (sternBrocotRep α) j₂) ↔
      ∀ t ≤ ℓ, mallowsQ (sternBrocotRep α) (j₁ + t) = mallowsQ (sternBrocotRep α) (j₂ + t)) ∧
    (((∀ t < ℓ, mallowsT (mallowsQ (sternBrocotRep α)) (i₁ + t) =
          mallowsT (mallowsQ (sternBrocotRep α)) (i₂ + t)) ∧
        mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₁) =
          mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₂)) ↔
      ∀ t ≤ mallowsOddIndex (mallowsQ (sternBrocotRep α)) (i₁ + ℓ) -
          mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₁,
        mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₁ + t) =
          mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₂ + t)) ∧
    (((∀ t < ℓ, mallowsT (mallowsQ (sternBrocotRep α)) (i₁ + t) =
          mallowsT (mallowsQ (sternBrocotRep α)) (i₂ + t)) ∧
        mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₁) =
          mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₂)) →
      ∀ k ≤ ℓ, mallowsOddIndex (mallowsQ (sternBrocotRep α)) (i₂ + k) -
          mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₂ =
        mallowsOddIndex (mallowsQ (sternBrocotRep α)) (i₁ + k) -
          mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₁)

/-- Let `u` be a finite word over `{L, R}` such that the last letter of `Q̇^X(u)` (computed by
`List.scanl mallowsQStep X u`) is `O_L` or `O_R`. Then `T(Q(SB(α)))` from position `i₀` starts
with `Ṫ(Q̇^X(u))` and `Q_{o(i₀)}(SB(α)) = X` iff the block of `Q(SB(α))` from `o(i₀)` of length
`ℓ + 1` equals `Q̇^X(u)`. Domain extension: the paper assumes `X ∈ {O_L, O_R}` and `ℓ ≥ 1`; for
even `X` both sides are false (`Q_{o(i₀)}` is odd), and for `ℓ = 0` both sides say
`Q_{o(i₀)} = X`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Lemma 3 (`integers-2025-A78-lem-3`). -/
public theorem_wanted mallowsT_startsWith_iff (X : MallowsParityLetter) (u : List SternBrocotLetter)
    (hlast : (u.scanl mallowsQStep X).getLast? = some .OL ∨
      (u.scanl mallowsQStep X).getLast? = some .OR)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α) (i₀ : ℕ) :
    (List.ofFn (fun t : Fin (mallowsTFin (u.scanl mallowsQStep X)).length =>
          mallowsT (mallowsQ (sternBrocotRep α)) (i₀ + t)) =
        mallowsTFin (u.scanl mallowsQStep X) ∧
      mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₀) = X) ↔
    List.ofFn (fun t : Fin (u.length + 1) =>
        mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i₀ + t)) =
      u.scanl mallowsQStep X

/-- Write `⟨Q_{o(1)}, Q_{o(2)}, …⟩ = O_L^{e_1} O_R^{e_2} O_L^{e_3} ⋯` with positive `e_k`
(Equation (7)). Then `T_i(Q(SB(α))) = M` iff `i = e_1 + ⋯ + e_k` for some `k ≥ 1`. Here
`e k = e_{k+1}`, the run decomposition is the hypothesis `hrun`, and Lean position `i` is paper
`i + 1`. The paper's hypothesis that `O_L` and `O_R` both occur infinitely often is exactly what
makes such `e` exist, so it is replaced by `he` and `hrun`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Lemma 4 (`integers-2025-A78-lem-4`). -/
public theorem_wanted mallowsT_eq_M_iff_runEnd (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α)
    (e : ℕ → ℕ) (he : ∀ k, 0 < e k)
    (hrun : ∀ k i, ∑ t ∈ Finset.range k, e t ≤ i → i < ∑ t ∈ Finset.range (k + 1), e t →
      mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i) =
        if Even k then .OL else .OR)
    (i : ℕ) :
    mallowsT (mallowsQ (sternBrocotRep α)) i = .M ↔
      ∃ k, 1 ≤ k ∧ i + 1 = ∑ t ∈ Finset.range k, e t

/-- The Mallows representation of an irrational `α ∈ (0, 1)` is eventually periodic iff its
Stern–Brocot representation is.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 3 (`integers-2025-A78-thm-3`). -/
public theorem_wanted isEventuallyPeriodic_mallowsRep_iff_sternBrocotRep (α : ℝ)
    (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    IsEventuallyPeriodic (mallowsRep α) ↔ IsEventuallyPeriodic (sternBrocotRep α)

/-- The Mallows representation of an irrational `α ∈ (0, 1)` is eventually periodic iff `α` is
a quadratic irrational (degree-two algebraic over `ℚ`, `IsRealQuadraticIrrational`).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Corollary 2 (`integers-2025-A78-cor-2`). -/
public theorem_wanted isEventuallyPeriodic_mallowsRep_iff_quadratic (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    IsEventuallyPeriodic (mallowsRep α) ↔ IsRealQuadraticIrrational α

/-- The Mallows representation of an irrational `α ∈ (0, 1)` is positively Poisson stable iff
its Stern–Brocot representation is.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 4 (`integers-2025-A78-thm-4`). -/
public theorem_wanted isPositivelyPoissonStable_mallowsRep_iff_sternBrocotRep (α : ℝ)
    (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    IsPositivelyPoissonStable (mallowsRep α) ↔ IsPositivelyPoissonStable (sternBrocotRep α)

/-- The Mallows representation of an irrational `α = [0; a_1, a_2, …] ∈ (0, 1)` is positively
Poisson stable iff the digit sequence `⟨a_1, a_2, …⟩` is (as a point of the shift over
`ℤ_{>0}`); `a k = a_{k+1}`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Corollary 3 (`integers-2025-A78-cor-3`). -/
public theorem_wanted isPositivelyPoissonStable_mallowsRep_iff_contFract (α : ℝ)
    (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) (a : ℕ → ℕ)
    (ha : ∀ k, (GenContFract.of α).partDens.get? k = some (a k : ℝ)) :
    IsPositivelyPoissonStable (mallowsRep α) ↔ IsPositivelyPoissonStable a

/-- The Mallows representation of an irrational `α ∈ (0, 1)` is transitive (every finite word
over `{L, M, R}` occurs in it) iff its Stern–Brocot representation is (every finite word over
`{L, R}` occurs). The empty word occurs trivially.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 5 (`integers-2025-A78-thm-5`). -/
public theorem_wanted transitive_mallowsRep_iff_sternBrocotRep (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    (∀ w : List MallowsLetter, InfiniteWord.IsFactor w (mallowsRep α)) ↔
      ∀ w : List SternBrocotLetter, InfiniteWord.IsFactor w (sternBrocotRep α)

/-- The Mallows representation of an irrational `α = [0; a_1, a_2, …] ∈ (0, 1)` is transitive
iff every finite word over `ℤ_{>0}` occurs in `⟨a_1, a_2, …⟩`; `a k = a_{k+1}`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Corollary 4 (`integers-2025-A78-cor-4`). -/
public theorem_wanted transitive_mallowsRep_iff_contFract (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α)
    (a : ℕ → ℕ) (ha : ∀ k, (GenContFract.of α).partDens.get? k = some (a k : ℝ)) :
    (∀ w : List MallowsLetter, InfiniteWord.IsFactor w (mallowsRep α)) ↔
      ∀ w : List ℕ, (∀ c ∈ w, 0 < c) → InfiniteWord.IsFactor w a

/-- For `α = [0; a_1, a_2, …]` irrational in `(0, 1)`, `M(α)` contains no `M` iff `a_{2k}` is
even for all `k ≥ 1`; `a k = a_{k+1}`, so `a_{2k}` is `a (2k - 1)`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 9 (`integers-2025-A78-prop-9`). -/
public theorem_wanted mallowsRep_ne_M_iff (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α)
    (a : ℕ → ℕ)
    (ha : ∀ k, (GenContFract.of α).partDens.get? k = some (a k : ℝ)) :
    (∀ i, mallowsRep α i ≠ .M) ↔ ∀ k, Even (a (2 * k + 1))

/-- For `α = [0; a_1, a_2, …]` irrational in `(0, 1)`, `M(α)` contains no `R` iff
`⟨a_1, a_2, …⟩ = ⟨e'_1, 1, 2e'_2⟩ ⌢ w_1 ⌢ ⟨2e'_3⟩ ⌢ w_2 ⌢ ⟨2e'_4⟩ ⌢ ⋯` with positive `e'_k`
and each `w_k` equal to `⟨2⟩` or `⟨1, e''_k, 1⟩`. Here `a k = a_{k+1}`; the blocks
`w_k ⌢ ⟨2e'_{k+2}⟩` start at positions `s k` (`s 0 = 3`), and `2e'` is written as an even
digit (digits are positive).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 10 (`integers-2025-A78-prop-10`). -/
public theorem_wanted mallowsRep_ne_R_iff (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α)
    (a : ℕ → ℕ)
    (ha : ∀ k, (GenContFract.of α).partDens.get? k = some (a k : ℝ)) :
    (∀ i, mallowsRep α i ≠ .R) ↔
      a 1 = 1 ∧ Even (a 2) ∧ ∃ s : ℕ → ℕ, s 0 = 3 ∧ ∀ k,
        (a (s k) = 2 ∧ Even (a (s k + 1)) ∧ s (k + 1) = s k + 2) ∨
        (a (s k) = 1 ∧ a (s k + 2) = 1 ∧ Even (a (s k + 3)) ∧ s (k + 1) = s k + 4)

/-- For `α = [0; a_1, a_2, …]` irrational in `(0, 1)`, `M(α)` contains no `L` iff
`⟨a_1, a_2, …⟩ = ⟨1, 2e'_1 - 1⟩ ⌢ w_1 ⌢ ⟨2e'_2⟩ ⌢ w_2 ⌢ ⟨2e'_3⟩ ⌢ ⋯` with positive `e'_k` and
each `w_k` equal to `⟨2⟩` or `⟨1, e''_k, 1⟩`. Here `a k = a_{k+1}`; the blocks
`w_k ⌢ ⟨2e'_{k+1}⟩` start at positions `s k` (`s 0 = 2`); `2e'_1 - 1` is written as an odd digit
and `2e'` as an even digit.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 11 (`integers-2025-A78-prop-11`). -/
public theorem_wanted mallowsRep_ne_L_iff (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α)
    (a : ℕ → ℕ)
    (ha : ∀ k, (GenContFract.of α).partDens.get? k = some (a k : ℝ)) :
    (∀ i, mallowsRep α i ≠ .L) ↔
      a 0 = 1 ∧ Odd (a 1) ∧ ∃ s : ℕ → ℕ, s 0 = 2 ∧ ∀ k,
        (a (s k) = 2 ∧ Even (a (s k + 1)) ∧ s (k + 1) = s k + 2) ∨
        (a (s k) = 1 ∧ a (s k + 2) = 1 ∧ Even (a (s k + 3)) ∧ s (k + 1) = s k + 4)

/-- The parities of the numerators of `f_1(α), f_2(α), …` are not eventually constant.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 12 (`integers-2025-A78-prop-12`). -/
public theorem_wanted sternBrocotFrac_parity_not_eventually_const (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    ¬ ∃ c j₀, ∀ j, j₀ ≤ j → (sternBrocotFrac α j).1 % 2 = c

/-- The parities of the numerators of `f_j(α)` are eventually alternating iff `M` occurs
infinitely often in `M(α)` and, for some `k ≥ 1`, from the `2k`-th occurrence `m(2k)` of `M` on,
`M(α) = M R^{e'_1} M L^{e'_2} M R^{e'_3} M ⋯` (`e'_i ≥ 0`). With `m t` the `(t+1)`-st occurrence
of `M` (`Nat.nth`), this says: for all `t ≥ 2k - 1`, the letters strictly between `m t` and
`m (t+1)` are `R` for odd `t` and `L` for even `t`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 13 (`integers-2025-A78-prop-13`). -/
public theorem_wanted parity_eventually_alternating_iff (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    (∃ j₀, ∀ j, j₀ ≤ j → (sternBrocotFrac α (j + 1)).1 % 2 ≠ (sternBrocotFrac α j).1 % 2) ↔
      {i | mallowsRep α i = .M}.Infinite ∧ ∃ k, 1 ≤ k ∧ ∀ t, 2 * k - 1 ≤ t → ∀ i,
        Nat.nth (fun n => mallowsRep α n = .M) t < i →
        i < Nat.nth (fun n => mallowsRep α n = .M) (t + 1) →
        mallowsRep α i = if Odd t then .R else .L

/-- The parities of the numerators of `f_j(α)` are eventually periodic with period `3` iff
either `M(α)` eventually agrees with `⟨L, R⟩^∞`, or `M` occurs infinitely often, deleting all
`M`s leaves a sequence eventually agreeing with `⟨L, R⟩^∞`, and for some `k ≥ 1` and all
`k' ≥ k` the `2k'`-th (resp. `(2k'+1)`-st) occurrence of `M` is preceded by `R` (resp. `L`) and
followed by `L` (resp. `R`). The deleted sequence is enumerated by `Nat.nth` on the non-`M`
positions (required to be infinite); the `(t+1)`-st `M` is at `Nat.nth (· = M) t`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 14 (`integers-2025-A78-prop-14`). -/
public theorem_wanted parity_eventually_period_three_iff (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hirr : Irrational α) :
    (∃ j₀, ∀ j, j₀ ≤ j → (sternBrocotFrac α (j + 3)).1 % 2 = (sternBrocotFrac α j).1 % 2) ↔
      (∃ i₀, ∀ t, mallowsRep α (i₀ + 2 * t) = .L ∧ mallowsRep α (i₀ + 2 * t + 1) = .R) ∨
      ({i | mallowsRep α i = .M}.Infinite ∧ {i | mallowsRep α i ≠ .M}.Infinite ∧
        (∃ t₀, ∀ t,
          mallowsRep α (Nat.nth (fun n => mallowsRep α n ≠ .M) (t₀ + 2 * t)) = .L ∧
          mallowsRep α (Nat.nth (fun n => mallowsRep α n ≠ .M) (t₀ + 2 * t + 1)) = .R) ∧
        ∃ k, 1 ≤ k ∧ ∀ k', k ≤ k' →
          mallowsRep α (Nat.nth (fun n => mallowsRep α n = .M) (2 * k' - 1) - 1) = .R ∧
          mallowsRep α (Nat.nth (fun n => mallowsRep α n = .M) (2 * k' - 1) + 1) = .L ∧
          mallowsRep α (Nat.nth (fun n => mallowsRep α n = .M) (2 * k') - 1) = .L ∧
          mallowsRep α (Nat.nth (fun n => mallowsRep α n = .M) (2 * k') + 1) = .R)

/-- (i) Almost no irrational `α ∈ (0, 1)` has an eventually periodic Mallows representation;
(ii) almost every one has a positively Poisson stable Mallows representation; (iii) almost every
one has a transitive Mallows representation (Lebesgue measure on `(0, 1)`).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Proposition 15 (`integers-2025-A78-prop-15`). -/
public theorem_wanted mallowsRep_ae_properties :
    (∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)), Irrational α →
      ¬ IsEventuallyPeriodic (mallowsRep α)) ∧
    (∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)), Irrational α →
      IsPositivelyPoissonStable (mallowsRep α)) ∧
    ∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)), Irrational α →
      ∀ w : List MallowsLetter, InfiniteWord.IsFactor w (mallowsRep α)

/-- For almost every irrational `α ∈ (0, 1)` the factor complexity of `M(α)` is `ρ(n) = 3^n`
(stated for all `n`; `n = 0` gives `1`).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Corollary 5 (`integers-2025-A78-cor-5`). -/
public theorem_wanted mallowsRep_ae_factorComplexity :
    ∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)), Irrational α →
      ∀ n, wordFactorComplexity (mallowsRep α) n = 3 ^ n

/-- For almost every irrational `α ∈ (0, 1)` some finite word over `{L, M, R}` does not occur
relatively densely in `M(α)`: there is no `ℓ > 0` such that every length-`ℓ` window contains an
occurrence of it.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Corollary 6 (`integers-2025-A78-cor-6`). -/
public theorem_wanted mallowsRep_ae_not_relativelyDense :
    ∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)), Irrational α →
      ∃ w : List MallowsLetter, ¬ ∃ ℓ, 0 < ℓ ∧ ∀ i, ∃ j, i ≤ j ∧ j + w.length ≤ i + ℓ ∧
        InfiniteWord.factorList (mallowsRep α) w.length j = w

/-- Let `w` be a finite word over `{L, M, R}` containing `M` or both `L` and `R`. For almost every
irrational `α ∈ (0, 1)`, the frequency of occurrences of `w` in `M(α)` is `0`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 6 (`integers-2025-A78-thm-6`). -/
public theorem_wanted mallowsRep_ae_frequency_zero (w : List MallowsLetter)
    (hw : MallowsLetter.M ∈ w ∨ (MallowsLetter.L ∈ w ∧ MallowsLetter.R ∈ w)) :
    ∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)), Irrational α →
      Filter.Tendsto (fun n : ℕ => ((((Finset.range n).filter fun i =>
          InfiniteWord.factorList (mallowsRep α) w.length i = w).card : ℕ) : ℝ) / n)
        Filter.atTop (nhds 0)

/-- For almost every irrational `α ∈ (0, 1)`, the `ℓ`-th matching fraction
`lim_n |{i ≤ n : M_i(α) = M_{i+ℓ}(α)}| / n` of `M(α)` is `1` for all `ℓ ≥ 1`. Domain extension:
stated for all `ℓ`, the value at `ℓ = 0` being trivially `1`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 7 (`integers-2025-A78-thm-7`). -/
public theorem_wanted mallowsRep_ae_matchingFraction_one :
    ∀ᵐ α ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)), Irrational α → ∀ ℓ : ℕ,
      Filter.Tendsto (fun n : ℕ => ((((Finset.range n).filter fun i =>
          mallowsRep α i = mallowsRep α (i + ℓ)).card : ℕ) : ℝ) / n) Filter.atTop (nhds 1)

/-- Over words `w ∈ {L, M, R}^ℓ`, the Lebesgue measure of `{α ∈ (0,1) \ ℚ : M(α) starts with w}`
has maximum `1/(ℓ+1)` and minimum `4√2 / ((1+√2)^{2ℓ+2} - (1-√2)^{2ℓ+2})`. Domain extension:
stated for all `ℓ`, including `ℓ = 0` where both values are `1`.

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 8 (`integers-2025-A78-thm-8`). -/
public theorem_wanted mallowsRep_cylinder_measure_extrema (ℓ : ℕ) :
    IsGreatest (Set.range fun w : Fin ℓ → MallowsLetter =>
        MeasureTheory.volume.real
          {α : ℝ | α ∈ Set.Ioo 0 1 ∧ Irrational α ∧ ∀ t : Fin ℓ, mallowsRep α t = w t})
      (1 / (ℓ + 1)) ∧
    IsLeast (Set.range fun w : Fin ℓ → MallowsLetter =>
        MeasureTheory.volume.real
          {α : ℝ | α ∈ Set.Ioo 0 1 ∧ Irrational α ∧ ∀ t : Fin ℓ, mallowsRep α t = w t})
      (4 * √2 / ((1 + √2) ^ (2 * ℓ + 2) - (1 - √2) ^ (2 * ℓ + 2)))

/-- For every `i ≥ 1`, the Lebesgue measure of `{α ∈ (0,1) \ ℚ : M_i(α) = M}` is less than
`3 - 2√2` (Lean index `i` is paper `i + 1`).

Source: Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25
(2025), Article A78, Theorem 9 (`integers-2025-A78-thm-9`). -/
public theorem_wanted mallowsRep_eq_M_measure_lt (i : ℕ) :
    MeasureTheory.volume.real {α : ℝ | α ∈ Set.Ioo 0 1 ∧ Irrational α ∧ mallowsRep α i = .M} <
      3 - 2 * √2

end

end MetaMathlibExt
