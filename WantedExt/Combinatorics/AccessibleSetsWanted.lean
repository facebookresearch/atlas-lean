/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Accessible and large sets (statements)

Statement-only targets from Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25
(2025), Article A64. Colorings are maps `ℕ+ → Fin r` (the paper's `ℕ` is the positive integers),
`D`-diffsequences are integer sequences with consecutive differences in `D`, and minimal systems
are compact metric spaces with a homeomorphism admitting no proper nonempty closed invariant set.
The colorings here are of `ℕ+`, unlike `MathlibExt.Combinatorics.PrimeTwoAccessibilityWanted`,
whose `IsRAccessible` colors all of `ℕ`.
-/

namespace MetaMathlibExt

@[expose] public section



/-- A finite sequence of positive integers is monochromatic when all of its
entries receive the same color.  The colors are `Fin r`, representing `[r]`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsMonochromatic {r k : ℕ} (c : ℕ+ → Fin r)
    (x : Fin k → ℕ+) : Prop :=
  ∀ i j, c (x i) = c (x j)

/-- `x` is a `k`-term arithmetic progression with a gap in `D`.  The witness
`a` is positive, `d ∈ D` is the gap, and the `i`th term is `a + i*d`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsDAP (D : Set ℕ) (k : ℕ) (x : Fin k → ℕ+) : Prop :=
  ∃ a : ℕ+, ∃ d ∈ D, ∀ i, (x i : ℕ) = a + (i : ℕ) * d

/-- Characterization of a `D`-arithmetic progression by its positive start,
gap in `D`, and term formula.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public theorem isDAP_iff (D : Set ℕ) (k : ℕ) (x : Fin k → ℕ+) :
    IsDAP D k x ↔ ∃ a : ℕ+, ∃ d ∈ D, ∀ i, (x i : ℕ) = a + (i : ℕ) * d :=
  Iff.rfl

/-- `D` is `r`-large when it contains only positive gaps, `r ≥ 1`, and every
`r`-coloring of the positive integers has a monochromatic `D`-AP of every
requested positive length.  The universal length quantifier formalizes
"arbitrarily long."
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsRLarge (r : ℕ) (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
    ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
      ∃ x : Fin k → ℕ+, IsMonochromatic c x ∧ IsDAP D k x

/-- Characterization of `r`-largeness, including positivity of `D`, the
condition `r ≥ 1`, and monochromatic `D`-APs of all positive lengths.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public theorem isRLarge_iff (r : ℕ) (D : Set ℕ) :
    IsRLarge r D ↔ D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
      ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
        ∃ x : Fin k → ℕ+, IsMonochromatic c x ∧ IsDAP D k x :=
  Iff.rfl

/-- A set is large when it is `r`-large for every positive number `r` of
colors; the explicit guard records the paper's positive-natural convention.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public def IsLarge (D : Set ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → IsRLarge r D

/-- Characterization of largeness as `r`-largeness for every `r ≥ 1`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-large). -/
public theorem isLarge_iff (D : Set ℕ) : IsLarge D ↔ ∀ r : ℕ, 1 ≤ r → IsRLarge r D :=
  Iff.rfl

/-- An integer-valued finite sequence is a `D`-diffsequence when every ordered
successive difference equals the coercion of some member of `D`.  This keeps
the paper's integer ambient space while `D` consists of natural gaps.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (D-diffsequence). -/
public def IsDDiffSequence (D : Set ℕ) {k : ℕ} (x : Fin k → ℤ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < k),
    ∃ d ∈ D, x ⟨i + 1, h⟩ - x ⟨i, by omega⟩ = (d : ℤ)

/-- Characterization of a `D`-diffsequence by its consecutive integer
differences.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (D-diffsequence). -/
public theorem isDDiffSequence_iff (D : Set ℕ) {k : ℕ} (x : Fin k → ℤ) :
    IsDDiffSequence D x ↔ ∀ (i : ℕ) (h : i + 1 < k),
      ∃ d ∈ D, x ⟨i + 1, h⟩ - x ⟨i, by omega⟩ = (d : ℤ) :=
  Iff.rfl

/-- `D` is `r`-accessible when it contains only positive gaps, `r ≥ 1`, and
every `r`-coloring of the positive integers has a monochromatic positive
`D`-diffsequence of every requested positive length.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public def IsRAccessible (r : ℕ) (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
    ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
      ∃ x : Fin k → ℕ+,
        IsMonochromatic c x ∧ IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ))

/-- Characterization of `r`-accessibility, with positivity and the universal
positive-length quantifier made explicit.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public theorem isRAccessible_iff (r : ℕ) (D : Set ℕ) :
    IsRAccessible r D ↔ D ⊆ Set.Ioi 0 ∧ 1 ≤ r ∧
      ∀ (c : ℕ+ → Fin r) (k : ℕ), 1 ≤ k →
        ∃ x : Fin k → ℕ+,
          IsMonochromatic c x ∧ IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ)) :=
  Iff.rfl

/-- Accessibility is antitone in the number of colors: an `s`-accessible set
is `r`-accessible whenever `1 ≤ r ≤ s`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public theorem IsRAccessible.mono (D : Set ℕ) {r s : ℕ} (h : IsRAccessible s D)
    (hr : 1 ≤ r) (hrs : r ≤ s) : IsRAccessible r D := by
  rcases h with ⟨hD, _, hs⟩
  refine ⟨hD, hr, ?_⟩
  intro c k hk
  obtain ⟨x, hx, hdiff⟩ := hs (fun n => Fin.castLE hrs (c n)) k hk
  refine ⟨x, ?_, hdiff⟩
  intro i j
  exact Fin.castLE_inj.mp (hx i j)

/-- A set is accessible when it is `r`-accessible for every positive number
`r` of colors.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public def IsAccessible (D : Set ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → IsRAccessible r D

/-- Characterization of accessibility as `r`-accessibility for all `r ≥ 1`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (r-accessible). -/
public theorem isAccessible_iff (D : Set ℕ) :
    IsAccessible D ↔ ∀ r : ℕ, 1 ≤ r → IsRAccessible r D :=
  Iff.rfl

/-- A sequence is lacunary when all terms are positive and some real ratio
`λ > 1` satisfies `m (n+1) ≥ λ*m n` for every zero-based index `n`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary sequence). -/
public def IsLacunary (m : ℕ → ℕ) : Prop :=
  (∀ n, 0 < m n) ∧ ∃ q : ℝ, 1 < q ∧
    ∀ n, (m (n + 1) : ℝ) ≥ q * (m n : ℝ)

/-- Characterization of a positive lacunary sequence and its ratio witness.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary sequence). -/
public theorem isLacunary_iff (m : ℕ → ℕ) :
    IsLacunary m ↔ (∀ n, 0 < m n) ∧ ∃ q : ℝ, 1 < q ∧
      ∀ n, (m (n + 1) : ℝ) ≥ q * (m n : ℝ) :=
  Iff.rfl

/-- A set is lacunary when it is exactly the range of a lacunary sequence.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary set). -/
public def IsLacunarySet (D : Set ℕ) : Prop :=
  ∃ m : ℕ → ℕ, IsLacunary m ∧ D = Set.range m

/-- Characterization of a lacunary set by a range representation.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Context (lacunary set). -/
public theorem isLacunarySet_iff (D : Set ℕ) :
    IsLacunarySet D ↔ ∃ m : ℕ → ℕ, IsLacunary m ∧ D = Set.range m :=
  Iff.rfl

/-- A compact metric homeomorphism is minimal exactly when it has no nonempty
proper closed invariant subset.  Compactness and metrizability are typeclass
parameters; invariance is the paper's literal equation `T '' K = K`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (topological dynamical system, minimal). -/
public def IsMinimalSystem {X : Type*} [MetricSpace X] [CompactSpace X]
    (T : X ≃ₜ X) : Prop :=
  ¬ ∃ K : Set X, IsClosed K ∧ K.Nonempty ∧ K ≠ Set.univ ∧ T '' K = K

/-- Characterization of minimality by absence of a nontrivial closed invariant
set, exactly as opposed to an orbit-density reformulation.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (topological dynamical system, minimal). -/
public theorem isMinimalSystem_iff {X : Type*} [MetricSpace X] [CompactSpace X]
    (T : X ≃ₜ X) :
    IsMinimalSystem T ↔
      ¬ ∃ K : Set X, IsClosed K ∧ K.Nonempty ∧ K ≠ Set.univ ∧ T '' K = K :=
  Iff.rfl

/-- `iteratePreimage T s U` formalizes `T⁻ˢ U`: it is the preimage of `U`
under the integer iterate `T^s` in the homeomorphism group.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def iteratePreimage {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)
    (s : ℤ) (U : Set X) : Set X :=
  (T ^ s) ⁻¹' U

/-- Characterization of the integer-iterate preimage notation.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem iteratePreimage_eq {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)
    (s : ℤ) (U : Set X) : iteratePreimage T s U = (T ^ s) ⁻¹' U :=
  rfl

/-- `D` is a set of `ℓ`-topological recurrence when every minimal compact
metric system and every nonempty open `U` admit `d ∈ D` for which the
intersection over `j = 0, …, ℓ` of `T⁻ʲᵈ U` is nonempty.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def IsLTopologicalRecurrence (ℓ : ℕ) (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧
    ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
      IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
        ∃ d ∈ D, (⋂ j : Fin (ℓ + 1),
          iteratePreimage T (((j : ℕ) : ℤ) * (d : ℤ)) U).Nonempty

/-- Characterization of `ℓ`-topological recurrence with the finite multiple
intersection encoded by `Fin (ℓ+1)`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem isLTopologicalRecurrence_iff (ℓ : ℕ) (D : Set ℕ) :
    IsLTopologicalRecurrence ℓ D ↔ D ⊆ Set.Ioi 0 ∧
      ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
          ∃ d ∈ D, (⋂ j : Fin (ℓ + 1),
            iteratePreimage T (((j : ℕ) : ℤ) * (d : ℤ)) U).Nonempty :=
  Iff.rfl

/-- Topological recurrence is the special case `ℓ = 1`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def IsTopologicalRecurrence (D : Set ℕ) : Prop :=
  IsLTopologicalRecurrence 1 D

/-- Characterization of topological recurrence as one-fold recurrence.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem isTopologicalRecurrence_iff (D : Set ℕ) :
    IsTopologicalRecurrence D ↔ IsLTopologicalRecurrence 1 D :=
  Iff.rfl

/-- Multiple topological recurrence means `ℓ`-topological recurrence for every
positive `ℓ`, matching the paper's `ℓ ≥ 1` convention.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public def IsMultipleTopologicalRecurrence (D : Set ℕ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → IsLTopologicalRecurrence ℓ D

/-- Characterization of multiple topological recurrence.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Definition (ℓ-topological recurrence). -/
public theorem isMultipleTopologicalRecurrence_iff (D : Set ℕ) :
    IsMultipleTopologicalRecurrence D ↔
      ∀ ℓ : ℕ, 1 ≤ ℓ → IsLTopologicalRecurrence ℓ D :=
  Iff.rfl

/-- A positive set is chromatically intersective when, in every finite
positive-integer coloring, two same-colored positive integers have the ordered
integer difference `a - b` equal to the coercion of a member of `D`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 13(iv). -/
public def IsChromaticallyIntersective (D : Set ℕ) : Prop :=
  D ⊆ Set.Ioi 0 ∧ ∀ (r : ℕ), 1 ≤ r → ∀ c : ℕ+ → Fin r,
    ∃ a b : ℕ+, c a = c b ∧
      ∃ d ∈ D, ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) = (d : ℤ)

/-- Characterization of chromatic intersectivity, preserving the ordered
difference rather than replacing it by an absolute difference.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 13(iv). -/
public theorem isChromaticallyIntersective_iff (D : Set ℕ) :
    IsChromaticallyIntersective D ↔
      D ⊆ Set.Ioi 0 ∧ ∀ (r : ℕ), 1 ≤ r → ∀ c : ℕ+ → Fin r,
        ∃ a b : ℕ+, c a = c b ∧
          ∃ d ∈ D, ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) = (d : ℤ) :=
  Iff.rfl

/-- The positive Fibonacci set is `{fib n | n ≥ 2}`; this removes zero and
ignores the duplicate value one exactly as a set should.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1. -/
public def positiveFibonacciSet : Set ℕ :=
  {d | ∃ n : ℕ, 2 ≤ n ∧ d = Nat.fib n}

/-- Characterization of membership in the positive Fibonacci set.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1. -/
public theorem mem_positiveFibonacciSet_iff (d : ℕ) :
    d ∈ positiveFibonacciSet ↔ ∃ n : ℕ, 2 ≤ n ∧ d = Nat.fib n :=
  Iff.rfl

/-- The even-Fibonacci set is `{fib (3*n+3) | n ≥ 0}`, whose first terms are
`2, 8, 34, …`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2. -/
public def evenFibonacciSet : Set ℕ :=
  {d | ∃ n : ℕ, d = Nat.fib (3 * n + 3)}

/-- Characterization of membership in the even-Fibonacci set.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2. -/
public theorem mem_evenFibonacciSet_iff (d : ℕ) :
    d ∈ evenFibonacciSet ↔ ∃ n : ℕ, d = Nat.fib (3 * n + 3) :=
  Iff.rfl

/-- A sufficiently fast-growing increasing enumeration of positive `D` is not
`r`-accessible.  The paper's `doa(D) ≤ r-1` is deliberately encoded as
`¬ IsRAccessible r D`; zero-based `n` represents the paper's index `n+1`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 1. -/
public theorem_wanted accessibility_degree_growth_bound (r : ℕ) (D : Set ℕ)
    (d : ℕ → ℕ) (hr : 2 ≤ r) (hmono : StrictMono d)
    (hD : D = Set.range d) (hd0 : 0 < d 0) (δ : ℝ) (hδ : 0 < δ)
    (N : ℕ) (hN : 0 < N)
    (hgrowth : ∀ n : ℕ, N ≤ n + 1 →
      (d (n + 1) : ℝ) ≥
        (2 + (((r - 1 : ℕ) : ℝ)⁻¹) + δ) * (d n : ℝ)) :
    ¬ IsRAccessible r D

/-- Growth by at least `3+δ` eventually obstructs 2-accessibility.  The
positive `N` and zero-based enumeration translate the paper's one-based tail.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Corollary 1. -/
public theorem_wanted not_two_accessible_of_growth (D : Set ℕ) (d : ℕ → ℕ)
    (hmono : StrictMono d) (hD : D = Set.range d) (hd0 : 0 < d 0)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (hgrowth : ∀ n : ℕ, N ≤ n + 1 →
      (d (n + 1) : ℝ) ≥ (3 + δ) * (d n : ℝ)) :
    ¬ IsRAccessible 2 D

/-- Every 2-large positive set contains a multiple of each positive integer.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 2. -/
public theorem_wanted two_large_contains_multiples (D : Set ℕ) (h : IsRLarge 2 D) :
    ∀ m : ℕ, 0 < m → ∃ d ∈ D, m ∣ d

/-- Removing a finite set from an `r`-large set preserves `r`-largeness.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 3. -/
public theorem_wanted rLarge_sdiff_finite (r : ℕ) (D F : Set ℕ)
    (hD : IsRLarge r D) (hF : F.Finite) :
    IsRLarge r (D \ F)

/-- If a union is large, at least one of its two summands is large.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 4. -/
public theorem_wanted large_union_partition (D D₁ D₂ : Set ℕ)
    (hD : D = D₁ ∪ D₂) (hlarge : IsLarge D) :
    IsLarge D₁ ∨ IsLarge D₂

/-- An increasing positive enumeration with every successive ratio at least
three does not form a 2-large set; the displayed condition is zero-based.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 5. -/
public theorem_wanted not_two_large_of_triple_growth (D : Set ℕ) (d : ℕ → ℕ)
    (hmono : StrictMono d) (hD : D = Set.range d) (hd0 : 0 < d 0)
    (hgrowth : ∀ n : ℕ, d (n + 1) ≥ 3 * d n) :
    ¬ IsRLarge 2 D

/-- A finite nonempty union of lacunary sets admits `α` and a positive `ε`
whose nearest-integer distances have infimum exactly `ε`.  `sInf` formalizes
the displayed infimum.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 6. -/
public theorem_wanted lacunary_union_avoids_integers (ℓ : ℕ) (hℓ : 0 < ℓ)
    (S : Fin ℓ → Set ℕ) (hS : ∀ i, IsLacunarySet (S i)) :
    ∃ α ε : ℝ, 0 < ε ∧
      sInf ((fun s : ℕ => |α * (s : ℝ) - round (α * (s : ℝ))|) '' (⋃ i, S i)) = ε

/-- A uniform positive nearest-integer distance produces a 2-coloring with no
monochromatic `D`-AP of length `ceil((2ε)⁻¹)+1`.  This is the cautious reading
of the malformed copied display, whose stray `r` belongs to `\rceil`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 7. -/
public theorem_wanted two_coloring_avoids_long_DAP (D : Set ℕ)
    (hD : D ⊆ Set.Ioi 0) (α ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ d ∈ D, ε ≤ |α * (d : ℝ) - round (α * (d : ℝ))|) :
    ∃ c : ℕ+ → Fin 2,
      ¬ ∃ x : Fin (Nat.ceil ((2 * ε)⁻¹) + 1) → ℕ+,
        IsMonochromatic c x ∧ IsDAP D (Nat.ceil ((2 * ε)⁻¹) + 1) x

/-- A finite union of lacunary positive sets is not 2-large.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 8. -/
public theorem_wanted finite_union_lacunary_not_two_large (n : ℕ) (hn : 0 < n)
    (D : Fin n → Set ℕ) (hD : ∀ i, IsLacunarySet (D i)) :
    ¬ IsRLarge 2 (⋃ i, D i)

/-- For an integer polynomial with positive leading coefficient and zero
constant term, its positive-natural values that are themselves positive form
a large set.  The set-builder encodes `ℕ ∩ {p(n) | n ∈ ℕ}`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 9. -/
public theorem_wanted polynomial_range_large (p : Polynomial ℤ)
    (hlead : 0 < p.leadingCoeff) (hzero : p.eval 0 = 0) :
    IsLarge {d : ℕ | 0 < d ∧ ∃ n : ℕ+, p.eval (n : ℤ) = (d : ℤ)}

/-- If every `(r-1)`-coloring of `D` contains arbitrarily long monochromatic
diffsequences with gaps in `D+c`, then `D+c` is `r`-accessible.  Elements
colored in the premise are positive members of `D`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 10. -/
public theorem_wanted accessible_of_colored_subset_diffsequences (c r : ℕ)
    (hr : 2 ≤ r) (D : Set ℕ) (hD : D ⊆ Set.Ioi 0)
    (hcolor : ∀ χ : ({n : ℕ+ // (n : ℕ) ∈ D} → Fin (r - 1)),
      ∀ k : ℕ, 1 ≤ k →
        ∃ x : Fin k → {n : ℕ+ // (n : ℕ) ∈ D},
          (∀ i j, χ (x i) = χ (x j)) ∧
          IsDDiffSequence {e : ℕ | ∃ d ∈ D, e = d + c}
            (fun i => (((x i : {n : ℕ+ // (n : ℕ) ∈ D}) : ℕ+) : ℕ))) :
    IsRAccessible r {e : ℕ | ∃ d ∈ D, e = d + c}

/-- If `D` contains `D`-diffsequences of every positive length, then it is
2-accessible.  Membership of every term formalizes that the sequence lies in
`D` itself.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Corollary 2. -/
public theorem_wanted two_accessible_of_internal_diffsequences (D : Set ℕ)
    (hD : D ⊆ Set.Ioi 0)
    (hseq : ∀ k : ℕ, 1 ≤ k → ∃ x : Fin k → ℕ+,
      (∀ i, (x i : ℕ) ∈ D) ∧
        IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ))) :
    IsRAccessible 2 D

/-- If `A` is `(r*d)`-accessible, then the positive integral quotient set
`{a/d | a ∈ A} ∩ ℕ` is `r`-accessible; divisibility is encoded by `a=n*d`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 11(i). -/
public theorem_wanted accessible_integral_quotients (A : Set ℕ) (d r : ℕ)
    (hd : 0 < d) (hA : IsRAccessible (r * d) A) :
    IsRAccessible r {n : ℕ | 0 < n ∧ ∃ a ∈ A, a = n * d}

/-- If `A` is `(r*d)`-accessible, then its subset of members congruent to zero
modulo `d` is `r`-accessible.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 11(ii). -/
public theorem_wanted accessible_divisible_subset (A : Set ℕ) (d r : ℕ)
    (hd : 0 < d) (hA : IsRAccessible (r * d) A) :
    IsRAccessible r {a : ℕ | a ∈ A ∧ a % d = 0}

/-- If every enumerated gap has fractional part in `[ε,(r-1)/r]`, an
`r`-coloring avoids monochromatic `D`-diffsequences of length
`ceil((r*ε)⁻¹)+1`.  This reads the copied terminal `rceil` as `\rceil`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 12. -/
public theorem_wanted coloring_avoids_diffsequence_of_fractional_bounds
    (r : ℕ) (hr : 1 ≤ r) (D : Set ℕ) (d : ℕ → ℕ)
    (hmono : StrictMono d) (hD : D = Set.range d) (hd0 : 0 < d 0)
    (α ε : ℝ) (hε : 0 < ε)
    (hfrac : ∀ n : ℕ, Int.fract (α * (d n : ℝ)) ∈
      Set.Icc ε (((r - 1 : ℕ) : ℝ) / (r : ℝ))) :
    ∃ c : ℕ+ → Fin r,
      ¬ ∃ x : Fin (Nat.ceil (((r : ℝ) * ε)⁻¹) + 1) → ℕ+,
        IsMonochromatic c x ∧
          IsDDiffSequence D (fun i => ((x i : ℕ) : ℤ))

/-- There is a 2-coloring of the positive integers with no monochromatic
6-term arithmetic progression whose gap is a positive Fibonacci number.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1 (coloring claim). -/
public theorem_wanted fibonacci_two_coloring_avoids_six_term_AP :
    ∃ c : ℕ+ → Fin 2,
      ¬ ∃ x : Fin 6 → ℕ+,
        IsMonochromatic c x ∧ IsDAP positiveFibonacciSet 6 x

/-- Consequently, the positive Fibonacci set is not 2-large.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1 (consequence). -/
public theorem_wanted fibonacci_not_two_large :
    ¬ IsRLarge 2 positiveFibonacciSet

/-- There is a 2-coloring of the positive integers with no monochromatic
4-term diffsequence whose gaps are even Fibonacci numbers.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2 (coloring claim). -/
public theorem_wanted even_fibonacci_two_coloring_avoids_four_term_diffsequence :
    ∃ c : ℕ+ → Fin 2,
      ¬ ∃ x : Fin 4 → ℕ+,
        IsMonochromatic c x ∧
          IsDDiffSequence evenFibonacciSet (fun i => ((x i : ℕ) : ℤ))

/-- Consequently, the even-Fibonacci set is not 2-accessible.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2 (consequence). -/
public theorem_wanted even_fibonacci_not_two_accessible :
    ¬ IsRAccessible 2 evenFibonacciSet

/-- For a translation-invariant collection `𝒜` of finite integer sets and
`r ≥ 1`, the partition property, the open-cover property for compact metric
systems, and the clopen-cover property for minimal systems are equivalent.
Translation invariance is expressed by `Finset.image (· + t) A ∈ 𝒜`; each
intersection uses integer homeomorphism iterates; the dynamical systems are on nonempty
compact metric spaces (on the empty space the cover clauses fail vacuously).
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Lemma 1. -/
public theorem_wanted furstenberg_weiss_correspondence
    (𝒜 : Set (Finset ℤ))
    (htrans : ∀ A ∈ 𝒜, ∀ t : ℤ, A.image (fun a => a + t) ∈ 𝒜)
    (r : ℕ) (hr : 1 ≤ r) :
    ((∀ c : ℤ → Fin r, ∃ i : Fin r, ∃ A ∈ 𝒜, ∀ a ∈ A, c a = i) ↔
      (∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X]
        (T : X ≃ₜ X)
        (U : Fin r → Set X),
        (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
          ∃ i : Fin r, ∃ A ∈ 𝒜,
            (⋂ a : A, iteratePreimage T (a : ℤ) (U i)).Nonempty)) ∧
    ((∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X]
        (T : X ≃ₜ X)
        (U : Fin r → Set X),
        (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
          ∃ i : Fin r, ∃ A ∈ 𝒜,
            (⋂ a : A, iteratePreimage T (a : ℤ) (U i)).Nonempty) ↔
      (∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X]
        (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Fin r → Set X,
        (∀ i, IsClopen (U i)) → (∀ x, ∃ i, x ∈ U i) →
          ∃ i : Fin r, ∃ A ∈ 𝒜,
            (⋂ a : A, iteratePreimage T (a : ℤ) (U i)).Nonempty))

/-- For a positive set `D`, topological recurrence, arbitrarily long integer
`D`-diffsequences returning every nonempty open set in every minimal system,
accessibility, and chromatic intersectivity are pairwise equivalent.  The
second clause uses integer sequence entries and integer homeomorphism powers;
the fourth retains the ordered difference `a-b`.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 13. -/
public theorem_wanted recurrence_accessibility_equivalences (D : Set ℕ)
    (hD : D ⊆ Set.Ioi 0) :
    (IsTopologicalRecurrence D ↔
      ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
          ∀ k : ℕ, 1 ≤ k → ∃ s : Fin k → ℤ,
            IsDDiffSequence D s ∧
              (U ∩ ⋂ i : Fin k, iteratePreimage T (s i) U).Nonempty) ∧
    ((∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
          ∀ k : ℕ, 1 ≤ k → ∃ s : Fin k → ℤ,
            IsDDiffSequence D s ∧
              (U ∩ ⋂ i : Fin k, iteratePreimage T (s i) U).Nonempty) ↔
      IsAccessible D) ∧
    (IsAccessible D ↔ IsChromaticallyIntersective D)

/-- If a union is a set of `k`-topological recurrence, then one of its two
summands is also a set of `k`-topological recurrence.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 14. -/
public theorem_wanted topological_recurrence_union_partition (k : ℕ)
    (D D₁ D₂ : Set ℕ) (hD : D = D₁ ∪ D₂)
    (hrec : IsLTopologicalRecurrence k D) :
    IsLTopologicalRecurrence k D₁ ∨ IsLTopologicalRecurrence k D₂

/-- If a union is accessible, then one of its two summands is accessible.
Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Corollary 3. -/
public theorem_wanted accessible_union_partition (D D₁ D₂ : Set ℕ)
    (hD : D = D₁ ∪ D₂) (hacc : IsAccessible D) :
    IsAccessible D₁ ∨ IsAccessible D₂

end

end MetaMathlibExt
