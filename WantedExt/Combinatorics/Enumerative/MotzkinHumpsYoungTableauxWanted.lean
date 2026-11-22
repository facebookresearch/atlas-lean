/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
import Mathlib.Tactic

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- The vertical displacement of the encoded step `0 = D`, `1 = F`, or `2 = U`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def motzkinStep (s : Fin 3) : ℤ := (s.val : ℤ) - 1

/-- A length-`n` encoded path is a Motzkin prefix ending at height `h` exactly when
every partial sum is nonnegative and its total vertical displacement is `h`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinPrefix (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) : Prop :=
  (∀ m : ℕ, m ≤ n → 0 ≤ ∑ i : Fin n, if i.val < m then motzkinStep (p i) else 0) ∧
  ∑ i : Fin n, motzkinStep (p i) = h

/-- A pair of positions is a hump of height `k` when it consists of an up step and
a later down step, has only flat steps between them, and the up step reaches height `k`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinHump (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  i.val < j.val ∧ motzkinStep (p i) = 1 ∧ motzkinStep (p j) = -1 ∧
  (∀ r : Fin n, i.val < r.val → r.val < j.val → motzkinStep (p r) = 0) ∧
  (∑ r : Fin n, if r.val ≤ i.val then motzkinStep (p r) else 0) = (k : ℤ)

/-- The defining clauses of `IsMotzkinPrefix`: nonnegative partial sums and endpoint
height `h`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinPrefix_iff (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) :
    IsMotzkinPrefix n h p ↔
      (∀ m : ℕ, m ≤ n →
        0 ≤ ∑ i : Fin n, if i.val < m then motzkinStep (p i) else 0) ∧
      ∑ i : Fin n, motzkinStep (p i) = h := by
  rfl

/-- A bounded formulation of the prefix condition, quantifying over the `n + 1`
possible prefix lengths. It is used only to make finite cardinalities executable.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinPrefixFinite (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) : Prop :=
  (∀ m : Fin (n + 1),
    0 ≤ ∑ i : Fin n, if i.val < m.val then motzkinStep (p i) else 0) ∧
  ∑ i : Fin n, motzkinStep (p i) = h

/-- The bounded prefix condition is equivalent to the paper's condition over all
natural `m` subject to `m ≤ n`; this is the characteristic lemma for the executable
formulation.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinPrefixFinite_iff (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) :
    IsMotzkinPrefixFinite n h p ↔ IsMotzkinPrefix n h p := by
  constructor
  · intro hp
    refine ⟨?_, hp.2⟩
    intro m hm
    exact hp.1 ⟨m, Nat.lt_succ_iff.mpr hm⟩
  · intro hp
    refine ⟨?_, hp.2⟩
    intro m
    exact hp.1 m.val (Nat.lt_succ_iff.mp m.isLt)

/-- Motzkin-prefix membership is decidable via the equivalent bounded prefix condition.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsMotzkinPrefix (n : ℕ) (h : ℤ) (p : Fin n → Fin 3) :
    Decidable (IsMotzkinPrefix n h p) := by
  letI : Decidable (IsMotzkinPrefixFinite n h p) := by
    unfold IsMotzkinPrefixFinite
    infer_instance
  exact decidable_of_iff (IsMotzkinPrefixFinite n h p)
    (isMotzkinPrefixFinite_iff n h p)

/-- The defining clauses of a Motzkin hump: ordered up/down endpoints, flat interior,
and height `k` at the up endpoint.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinHump_iff (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) :
    IsMotzkinHump n k p i j ↔
      i.val < j.val ∧ motzkinStep (p i) = 1 ∧ motzkinStep (p j) = -1 ∧
      (∀ r : Fin n, i.val < r.val → r.val < j.val → motzkinStep (p r) = 0) ∧
      (∑ r : Fin n, if r.val ≤ i.val then motzkinStep (p r) else 0) = (k : ℤ) := by
  rfl

/-- Hump membership is decidable because all marked positions and intervening steps
range over finite types.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsMotzkinHump (n k : ℕ) (p : Fin n → Fin 3)
    (i j : Fin n) : Decidable (IsMotzkinHump n k p i j) := by
  unfold IsMotzkinHump
  infer_instance

/-- A hump is a peak exactly when its down step immediately follows its up step.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsMotzkinPeak (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  IsMotzkinHump n k p i j ∧ i.val + 1 = j.val

/-- The characteristic property of `IsMotzkinPeak`: it is a hump whose two marked
steps are adjacent.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isMotzkinPeak_iff (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) :
    IsMotzkinPeak n k p i j ↔ IsMotzkinHump n k p i j ∧ i.val + 1 = j.val := by
  rfl

/-- A Motzkin prefix belongs to `𝓜^{*U}_{n,h}` when its last non-flat step is up;
the existential formula is exactly the encoding specified in the paper task.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def LastNonflatStepUp (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, p i = 2 ∧ ∀ j, i < j → p j = 1

/-- The characteristic existential condition for a prefix whose last non-flat step is up.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem lastNonflatStepUp_iff (n : ℕ) (p : Fin n → Fin 3) :
    LastNonflatStepUp n p ↔ ∃ i, p i = 2 ∧ ∀ j, i < j → p j = 1 := by
  rfl

/-- A Motzkin prefix belongs to `𝓜^{D*}_{n,h}` when its first non-up step is down;
the existential condition excludes a path having no non-up step.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def FirstNonupStepDown (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, p i = 0 ∧ ∀ j, j < i → p j = 2

/-- The characteristic existential condition for a prefix whose first non-up step is down.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem firstNonupStepDown_iff (n : ℕ) (p : Fin n → Fin 3) :
    FirstNonupStepDown n p ↔ ∃ i, p i = 0 ∧ ∀ j, j < i → p j = 2 := by
  rfl

/-- An encoded path ends with an up step when its final position exists and contains `U`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def EndsWithUp (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∃ i, i.val + 1 = n ∧ p i = 2

/-- The characteristic existential condition for ending with an up step.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public theorem endsWithUp_iff (n : ℕ) (p : Fin n → Fin 3) :
    EndsWithUp n p ↔ ∃ i, i.val + 1 = n ∧ p i = 2 := by
  rfl

/-- `motzkinHumpCount n k` is `H_{n,k}`, the cardinality of paths of order `n` with
one distinguished hump of height `k`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def motzkinHumpCount (n k : ℕ) : ℕ :=
  Fintype.card {q : (Fin n → Fin 3) × Fin n × Fin n //
    IsMotzkinPrefix n 0 q.1 ∧ IsMotzkinHump n k q.1 q.2.1 q.2.2}

/-- A computationally shallow expansion of `H_{n,k}` that enumerates the path and
the two marked positions in nested indicator sums.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def motzkinHumpCountExpanded (n k : ℕ) : ℕ :=
  ∑ p : Fin n → Fin 3, ∑ i : Fin n, ∑ j : Fin n,
    if IsMotzkinPrefix n 0 p ∧ IsMotzkinHump n k p i j then 1 else 0

/-- The nested indicator expansion computes the defining distinguished-hump cardinality.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private theorem motzkinHumpCount_eq_expanded (n k : ℕ) :
    motzkinHumpCount n k = motzkinHumpCountExpanded n k := by
  classical
  rw [motzkinHumpCount, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rfl

/-- `motzkinSeries` is `M(x) = ∑ m_n x^n`, with integer coefficients the canonical Motzkin
numbers `motzkinNumber`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def motzkinSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (motzkinNumber n : ℤ))

/-- A finite-cell encoding of an SYT of order `n`: entries occupy distinct cells, and
every cell weakly northwest of entry `i` is occupied by an entry `j ≤ i`. This makes
each initial segment a Young diagram and encodes strict increase along rows and columns.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsStandardYoungTableau (n : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  Function.Injective T ∧
    ∀ i c, c.1 ≤ (T i).1 → c.2 ≤ (T i).2 → ∃ j, j ≤ i ∧ T j = c

/-- The defining clauses of the finite SYT encoding are injectivity and downward
closure witnessed within each initial segment.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isStandardYoungTableau_iff (n : ℕ) (T : Fin n → Fin n × Fin n) :
    IsStandardYoungTableau n T ↔
      Function.Injective T ∧
        ∀ i c, c.1 ≤ (T i).1 → c.2 ≤ (T i).2 → ∃ j, j ≤ i ∧ T j = c := by
  rfl

/-- Membership in the finite-cell SYT encoding is decidable by finite quantification.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsStandardYoungTableau (n : ℕ)
    (T : Fin n → Fin n × Fin n) : Decidable (IsStandardYoungTableau n T) := by
  unfold IsStandardYoungTableau Function.Injective
  infer_instance

/-- A tableau shape lies in the `(2,1)`-hook exactly when it has no occupied cell
whose zero-based row is at least two and whose zero-based column is at least one.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def IsInTwoOneHook (n : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  ∀ i, ¬(2 ≤ (T i).1.val ∧ 1 ≤ (T i).2.val)

/-- The characteristic forbidden-cell condition for membership in the `(2,1)`-hook.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem isInTwoOneHook_iff (n : ℕ) (T : Fin n → Fin n × Fin n) :
    IsInTwoOneHook n T ↔ ∀ i, ¬(2 ≤ (T i).1.val ∧ 1 ≤ (T i).2.val) := by
  rfl

/-- Membership in the `(2,1)`-hook is decidable by inspecting the finitely many entries.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableIsInTwoOneHook (n : ℕ) (T : Fin n → Fin n × Fin n) :
    Decidable (IsInTwoOneHook n T) := by
  unfold IsInTwoOneHook
  infer_instance

/-- The length of zero-based row `r` is the number of entries placed in that row.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def tableauRowLength (n : ℕ) (T : Fin n → Fin n × Fin n) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (T i).1.val = r).card

/-- A tableau has row-length difference `k` when `λ₁ = λ₂ + k`; this addition form
faithfully states `λ₁ - λ₂ = k` without truncated subtraction.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def HasFirstTwoRowDifference (n k : ℕ) (T : Fin n → Fin n × Fin n) : Prop :=
  tableauRowLength n T 0 = tableauRowLength n T 1 + k

/-- The characteristic row-cardinality equation for first-two-row difference `k`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public theorem hasFirstTwoRowDifference_iff (n k : ℕ) (T : Fin n → Fin n × Fin n) :
    HasFirstTwoRowDifference n k T ↔
      tableauRowLength n T 0 = tableauRowLength n T 1 + k := by
  rfl

/-- The first-two-row cardinality equation is decidable.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public instance instDecidableHasFirstTwoRowDifference (n k : ℕ)
    (T : Fin n → Fin n × Fin n) : Decidable (HasFirstTwoRowDifference n k T) := by
  unfold HasFirstTwoRowDifference
  infer_instance

/-- `sytHookCount n k` is `SYT_k(2,1;n)`: the cardinality of standard Young tableaux
of order `n` in the `(2,1)`-hook whose first two row lengths differ by `k`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
public def sytHookCount (n k : ℕ) : ℕ :=
  Fintype.card {T : Fin n → Fin n × Fin n //
    IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧ HasFirstTwoRowDifference n k T}

/-- A cell-valued map is equivalently the pair of its row and column coordinate maps.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def tableauCoordinateEquiv (n : ℕ) :
    (Fin n → Fin n × Fin n) ≃ (Fin n → Fin n) × (Fin n → Fin n) where
  toFun T := (fun i => (T i).1, fun i => (T i).2)
  invFun rc := fun i => (rc.1 i, rc.2 i)
  left_inv T := by
    funext i
    exact Prod.eta (T i)
  right_inv rc := by
    exact Prod.ext (by rfl) (by rfl)

/-- Restricting `tableauCoordinateEquiv` gives an equivalence between valid tableaux
and pairs of coordinate maps satisfying the same tableau predicate.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def sytHookSubtypeEquiv (n k : ℕ) :
    {T : Fin n → Fin n × Fin n //
      IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧ HasFirstTwoRowDifference n k T} ≃
    {rc : (Fin n → Fin n) × (Fin n → Fin n) //
      let T := fun i => (rc.1 i, rc.2 i)
      IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧
        HasFirstTwoRowDifference n k T} where
  toFun T := ⟨tableauCoordinateEquiv n T.val, by simpa [tableauCoordinateEquiv] using T.property⟩
  invFun rc := ⟨(tableauCoordinateEquiv n).symm rc.val, by
    simpa [tableauCoordinateEquiv] using rc.property⟩
  left_inv T := by
    apply Subtype.ext
    exact (tableauCoordinateEquiv n).left_inv T.val
  right_inv rc := by
    apply Subtype.ext
    exact (tableauCoordinateEquiv n).right_inv rc.val

/-- A computationally shallow expansion of `SYT_k(2,1;n)` that independently
enumerates the row and column coordinate maps.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private def sytHookCountExpanded (n k : ℕ) : ℕ :=
  ∑ rows : Fin n → Fin n, ∑ cols : Fin n → Fin n,
    let T := fun i => (rows i, cols i)
    if IsStandardYoungTableau n T ∧ IsInTwoOneHook n T ∧
        HasFirstTwoRowDifference n k T then 1 else 0

/-- The nested coordinate-map expansion computes the defining SYT cardinality.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
-/
private theorem sytHookCount_eq_expanded (n k : ℕ) :
    sytHookCount n k = sytHookCountExpanded n k := by
  classical
  rw [sytHookCount, Fintype.card_congr (sytHookSubtypeEquiv n k),
    Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The finite disjoint union `⋃_{1 ≤ k ≤ ⌊n/2⌋} 𝓗_{n,k}`, retaining the height
index and the distinguished up/down positions.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def MotzkinHumpFamily (n : ℕ) :=
  {q : ℕ × ((Fin n → Fin 3) × Fin n × Fin n) //
    1 ≤ q.1 ∧ q.1 ≤ n / 2 ∧ IsMotzkinPrefix n 0 q.2.1 ∧
      IsMotzkinHump n q.1 q.2.1 q.2.2.1 q.2.2.2}

/-- The finite disjoint union `⋃_{1 ≤ k ≤ ⌊n/2⌋} 𝓜^{*U}_{n,2k}`, retaining the
index `k`; its paths end at height `2k` and have last non-flat step `U`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public def MotzkinLastUpEvenFamily (n : ℕ) :=
  {q : ℕ × (Fin n → Fin 3) //
    1 ≤ q.1 ∧ q.1 ≤ n / 2 ∧ IsMotzkinPrefix n (2 * q.1) q.2 ∧
      LastNonflatStepUp n q.2}

/-- The finite disjoint union `⋃_{0 ≤ k ≤ n-2} 𝓜^{D*}_{n,k}`. The paper's lower
bound is automatic for `k : ℕ`, while `k ≤ n-2` is stated without truncation as
`k + 2 ≤ n`; each path ends at height `k` and has first non-up step `D`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
-/
public def MotzkinFirstDownFamily (n : ℕ) :=
  {q : ℕ × (Fin n → Fin 3) //
    q.1 + 2 ≤ n ∧ IsMotzkinPrefix n q.1 q.2 ∧ FirstNonupStepDown n q.2}

/-- The table value `SYT_1(2,1;3) = 2` for the faithful finite-cell encoding.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_three_one : sytHookCount 3 1 = 2 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- The table value `SYT_0(2,1;3) = 1` for the faithful finite-cell encoding.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_three_zero : sytHookCount 3 0 = 1 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- The table value `SYT_1(2,1;2) = 0` for the faithful finite-cell encoding.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Initial-values table.
-/
public theorem sytHookCount_two_one : sytHookCount 2 1 = 0 := by
  rw [sytHookCount_eq_expanded]
  decide

/-- The hump table value `H_{4,1} = 8` for the supplied distinguished-hump encoding.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Hump-count table.
-/
public theorem motzkinHumpCount_four_one : motzkinHumpCount 4 1 = 8 := by
  rw [motzkinHumpCount_eq_expanded]
  decide

/-- Theorem 2 gives the stated double-binomial closed formula for
`SYT_k(2,1;n)` when `0 ≤ k ≤ n-2`; the lower bound is automatic over `ℕ` and the
upper bound is written `k + 2 ≤ n`. All terms are compared in `ℚ`. The exceptional
paper term with `k = 0` and `2i = n-1` has nominal upper binomial argument `-1`;
natural subtraction truncates it to `0`, so its sole `j = 0` factor is
`Nat.choose 0 0 = 1`, as required.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Theorem 2 (`jis-2025-25.8.1-thm-2`).
-/
public theorem_wanted sytHookCount_closedForm (n k : ℕ) (hk : k + 2 ≤ n) :
    (sytHookCount n k : ℚ) =
      (-1 : ℚ) ^ (n + k) +
        ∑ i ∈ Finset.range ((n - k - 1) / 2 + 1),
          ∑ j ∈ Finset.range (n - k - 1 - 2 * i + 1),
            (if j % 2 = (n + k - 1) % 2 then (1 : ℚ) else 0) *
              ((2 * k + 2 : ℕ) : ℚ) / ((n + k + 1 - 2 * i - j : ℕ) : ℚ) *
              (Nat.choose (n - 2 * i - 2) j : ℚ) *
              (Nat.choose (n - 2 * i - j - 1) ((n + k - j - 1) / 2 - i) : ℚ)

/-- Lemma 3 supplies a bijection from height-indexed humps to even-height prefixes
whose last non-flat step is up. Equality of retained indices formalizes the paper's
membership equivalence at each `k`; moreover, a marked hump is a peak exactly when
its image actually ends with an up step.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public theorem_wanted motzkinHumpFamily_equiv_lastUpEvenFamily (n : ℕ) :
    ∃ e : MotzkinHumpFamily n ≃ MotzkinLastUpEvenFamily n,
      (∀ q, (e q).val.1 = q.val.1) ∧
        ∀ q, IsMotzkinPeak n q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 ↔
          EndsWithUp n (e q).val.2

/-- Corollary 5, in its generating-function (rather than equivalent Riordan-array)
form: for `k ≥ 1`, clearing the factor `1-X` gives the displayed identity in
`PowerSeries ℤ`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 5 (`jis-2025-25.8.1-cor-5`).
-/
public theorem_wanted motzkinHumpCount_generatingFunction (k : ℕ) (hk : 1 ≤ k) :
    (1 - (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n => if 2 * k ≤ n then (motzkinHumpCount n k : ℤ) else 0) =
      PowerSeries.X ^ (2 * k) * motzkinSeries ^ (2 * k)

/-- Lemma 6 is the bijection between prefixes indexed by `0 ≤ k ≤ n-2` whose first
non-up step is down and even-height prefixes indexed by `1 ≤ k ≤ ⌊n/2⌋` whose last
non-flat step is up. The automatic natural lower bound is omitted, and `k ≤ n-2`
is encoded as `k + 2 ≤ n` in the domain subtype.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
-/
public theorem_wanted motzkinFirstDownFamily_equiv_lastUpEvenFamily (n : ℕ) :
    Nonempty (MotzkinFirstDownFamily n ≃ MotzkinLastUpEvenFamily n)

/-- Lemma 7 states the generating function for
`T_{n,k} = SYT_k(2,1;n) + (-1)^{n+k+1}`. It is stated division-free in
`PowerSeries ℤ`, with the coefficient series explicitly truncated to `n ≥ k`.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 7 (`jis-2025-25.8.1-lem-7`).
-/
public theorem_wanted adjustedSytHookCount_generatingFunction (k : ℕ) :
    (1 + (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n =>
          if k ≤ n then (sytHookCount n k : ℤ) + (-1 : ℤ) ^ (n + k + 1) else 0) =
      (PowerSeries.X * motzkinSeries) ^ (k + 1)

/-- Corollary 9 gives the generating function for `SYT_k(2,1;n)` for every natural
`k`; it is stated division-free in `PowerSeries ℤ` and keeps the paper's `n ≥ k`
coefficient range explicitly.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 9 (`jis-2025-25.8.1-cor-9`).
-/
public theorem_wanted sytHookCount_generatingFunction (k : ℕ) :
    (1 + (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n => if k ≤ n then (sytHookCount n k : ℤ) else 0) =
      PowerSeries.X ^ k * (1 + PowerSeries.X * motzkinSeries ^ (k + 1))

/-- Corollary 10: for `1 ≤ k ≤ ⌊n/2⌋`, the sum of the two adjacent
`SYT_{2k-1}` counts equals the difference of the corresponding height-`k` hump
counts. Casts make the subtraction an identity in `ℤ`, avoiding natural truncation.
Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 10 (`jis-2025-25.8.1-cor-10`).
-/
public theorem_wanted sytHookCount_add_eq_humpCount_sub (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n / 2) :
    (sytHookCount (n + 1) (2 * k - 1) : ℤ) + (sytHookCount n (2 * k - 1) : ℤ) =
      (motzkinHumpCount (n + 1) k : ℤ) - (motzkinHumpCount n k : ℤ)

end

end MetaMathlibExt
