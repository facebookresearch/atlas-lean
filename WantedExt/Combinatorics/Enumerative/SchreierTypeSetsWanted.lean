/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On Schreier-type sets, partitions, and compositions

Statements from Kevin Beanland and Hùng Việt Chu, "On
Schreier-Type Sets, Partitions, and Compositions", *Journal of
Integer Sequences* 27 (2024), Article 24.4.4
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Beanland/bean4.html>).
The publisher TeX at
<https://cs.uwaterloo.ca/journals/JIS/VOL27/Beanland/bean4.tex>
is the source used for the definitions below.

A finite set `A` of positive integers is *Schreier* if it is empty
or `min A ≥ |A|`, and *`ℓ`-strong Schreier* if it is empty or
`min A ≥ ℓ|A| - ℓ + 1`; both are encoded here by the equivalent
conditions on all elements of `A`, which are vacuous for `A = ∅`.
A set is *sparse* if the differences between consecutive elements
(in increasing order) are non-decreasing, and *strongly sparse*
if they are strictly increasing; both are encoded by quantifying
over consecutive triples, which is vacuous for `|A| ≤ 2`, as in
the paper.

Partitions are Mathlib's `Nat.Partition`, with `P.parts` the
multiset of parts.  The paper's conventions `|E_{0,ℓ}| = 1` etc.
are automatic since `Nat.Partition 0` has the single empty
partition.  Compositions are Mathlib's `Composition u`, with
parts at least `v` imposed on `c.blocks` and exactly `s` parts
as `c.length = s`.

Parameter ranges follow the paper (whose `ℕ` is the positive
integers): Theorem 6 allows `ℓ ≥ 0` explicitly, Theorem 9 allows
`ℓ ≥ 0` but quantifies `m, n ∈ ℕ` (so `1 ≤ m` is a hypothesis
below), and the Section 4 setup chooses `n ≥ 1` and `ℓ ≥ 0`, so
`ℓ = 0` in Theorems 6 and 9 and in Lemma 11/Corollaries 12-13
is paper domain, not an extension.  Theorem 7 is quantified over
`1 ≤ n` and `1 ≤ ℓ`: the paper quantifies over `n, ℓ ∈ ℕ`, and
the identities fail at `ℓ = 0` (for example
`|A_{2,0}| = 2 ≠ 1 = |G_{1,0}|`).  Partition counts are defined
through Mathlib's `Nat.Partition.restricted` and
`Nat.Partition.distincts`; set-family counts are filtered
powersets; composition counts use Mathlib's `Composition u`
(positive block sizes), which agrees with the paper's `c(u, v)`
and `c(u, v, s)` at the values `v = ℓ + 1 ≥ 1` used in
Theorem 9.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

/-- A finite set of positive integers is *Schreier* if it is empty
or `min A ≥ |A|`; encoded as `|A| ≤ a` for every `a ∈ A`. -/
def IsSchreier (A : Finset ℕ) : Prop := ∀ a ∈ A, A.card ≤ a

instance (A : Finset ℕ) : Decidable (IsSchreier A) := by
  unfold IsSchreier; infer_instance

/-- A finite set of positive integers is *`ℓ`-strong Schreier* if
it is empty or `min A ≥ ℓ|A| - ℓ + 1`; encoded elementwise. -/
def IsStrongSchreier (l : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, l * A.card + 1 ≤ a + l

instance (l : ℕ) (A : Finset ℕ) : Decidable (IsStrongSchreier l A) := by
  unfold IsStrongSchreier; infer_instance

/-- A finite set is *sparse* if the differences between
consecutive elements in increasing order are non-decreasing. -/
def IsSparse (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c →
    (∀ x ∈ A, a < x → b ≤ x) → (∀ x ∈ A, b < x → c ≤ x) →
      b - a ≤ c - b

instance (A : Finset ℕ) : Decidable (IsSparse A) := by
  unfold IsSparse; infer_instance

/-- A finite set is *strongly sparse* if the differences between
consecutive elements in increasing order are strictly
increasing. -/
def IsStronglySparse (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c →
    (∀ x ∈ A, a < x → b ≤ x) → (∀ x ∈ A, b < x → c ≤ x) →
      b - a < c - b

instance (A : Finset ℕ) : Decidable (IsStronglySparse A) := by
  unfold IsStronglySparse; infer_instance

/-- `p(u, k)`, the number of partitions of `u` into exactly `k`
parts. -/
def partitionExactCount (u k : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Nat.Partition u =>
    P.parts.card = k)).card

/-- `p(u)`, the partition number of `u` (with `p(0) = 1`). -/
def partitionCount (u : ℕ) : ℕ := Fintype.card (Nat.Partition u)

/-- `|F_{n,m}|`: Schreier sparse sets `F ⊆ {1, …, n}` with
`n ∈ F` and `min F = m` (Section 2 of the paper). -/
def schreierSparseMinCount (n m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun F => IsSchreier F ∧
    IsSparse F ∧ n ∈ F ∧ m ∈ F ∧ ∀ a ∈ F, m ≤ a)).card

/-- `|F_n|`: Schreier sparse sets `F ⊆ {1, …, n}` with `n ∈ F`. -/
def schreierSparseCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun F => IsSchreier F ∧
    IsSparse F ∧ n ∈ F)).card

/-- `|A_{n,ℓ}|`: sparse `ℓ`-strong Schreier sets
`A ⊆ {1, …, n}` with `n ∈ A`. -/
def sparseStrongCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => n ∈ A ∧
    IsSparse A ∧ IsStrongSchreier l A)).card

/-- `|A^s_{n,ℓ}|`: strongly sparse `ℓ`-strong Schreier sets
`A ⊆ {1, …, n}` with `n ∈ A`. -/
def stronglySparseStrongCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => n ∈ A ∧
    IsStronglySparse A ∧ IsStrongSchreier l A)).card

/-- `|B_{n,ℓ}|`: `ℓ`-strong Schreier sets `B ⊆ {1, …, n}` with
`n ∈ B`. -/
def strongSchreierCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun B => n ∈ B ∧
    IsStrongSchreier l B)).card

/-- `|B_{n,ℓ,m}|`: as above with exactly `m` elements. -/
def strongSchreierCardCount (n l m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun B => n ∈ B ∧
    B.card = m ∧ IsStrongSchreier l B)).card

/-- `|E_{n,ℓ}|`: partitions of `n` into parts at least `ℓ`,
via Mathlib's `Nat.Partition.restricted`. -/
def partitionMinPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => l ≤ x)).card

/-- `|E^d_{n,ℓ}|`: partitions of `n` into distinct parts at
least `ℓ`, via `Nat.Partition.restricted` and
`Nat.Partition.distincts`. -/
def partitionDistinctMinPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => l ≤ x) ∩
    Nat.Partition.distincts n).card

/-- `|E_{n,ℓ,k}|`: partitions in `E_{n,ℓ}` with exactly `k`
parts. -/
def partitionMinPartExactCount (n l k : ℕ) : ℕ :=
  ((Nat.Partition.restricted n (fun x => l ≤ x)).filter
    (fun P => P.parts.card = k)).card

/-- `|E_{n,ℓ,k,q}|`: partitions in `E_{n,ℓ,k}` where the
difference between the largest and second largest parts is `q`,
encoded by removing the two largest parts `b + q ≥ b` from the
parts multiset. -/
noncomputable def partitionMinPartGapCount (n l k q : ℕ) : ℕ := by
  classical
  exact ((Nat.Partition.restricted n (fun x => l ≤ x)).filter
    (fun P => P.parts.card = k ∧
      ∃ b : ℕ, ∃ rest : Multiset ℕ,
        P.parts = (b + q) ::ₘ b ::ₘ rest ∧
          ∀ x ∈ rest, x ≤ b)).card

/-- `|G_{n,ℓ}|`: partitions of `n` with no parts in
`{2, …, ℓ}`, via `Nat.Partition.restricted`. -/
def partitionNoSmallPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => ¬ (2 ≤ x ∧ x ≤ l))).card

/-- `|H_{n,ℓ}|`: partitions of `n` with no parts in `{2, …, ℓ}`
and no even parts greater than `2ℓ`, via
`Nat.Partition.restricted`. -/
def partitionNoSmallNoEvenCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n
    (fun x => ¬ (2 ≤ x ∧ x ≤ l) ∧ (Even x → x ≤ 2 * l))).card

/-- `c(u, v, s)`: compositions of `u` into exactly `s` parts,
each at least `v`. -/
def compositionMinPartExactCount (u v s : ℕ) : ℕ :=
  Fintype.card {c : Composition u //
    (∀ x ∈ c.blocks, v ≤ x) ∧ c.length = s}

/-- `c(u, v)`: compositions of `u` into parts at least `v`. -/
def compositionMinPartCount (u v : ℕ) : ℕ :=
  Fintype.card {c : Composition u // ∀ x ∈ c.blocks, v ≤ x}

/-- Membership in the refined family `F_{n,ℓ}` of Section 4:
`A = {a_1, …, a_p, n+1}` with `p ≥ 2`, `A` sparse and
`ℓ`-strong Schreier, and `n + 1 + a_{p-1} = 2·a_p` for the two
largest elements `a_{p-1} < a_p` below `n + 1`. -/
def IsRefinedSchreier (n l : ℕ) (A : Finset ℕ) : Prop :=
  n + 1 ∈ A ∧ (∀ x ∈ A, x ≤ n + 1) ∧ 3 ≤ A.card ∧ IsSparse A ∧
    IsStrongSchreier l A ∧
      ∃ a ∈ A, ∃ b ∈ A, a < b ∧ b < n + 1 ∧
        (∀ x ∈ A, x ≤ b ∨ x = n + 1) ∧
          (∀ x ∈ A, x ≤ a ∨ x = b ∨ x = n + 1) ∧
            n + 1 + a = 2 * b

instance (n l : ℕ) (A : Finset ℕ) :
    Decidable (IsRefinedSchreier n l A) := by
  unfold IsRefinedSchreier; infer_instance

/-- `|F_{n,ℓ}|` for the refined family of Section 4 (every such
set is contained in `{0, …, n + 1}`). -/
def refinedSchreierCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (IsRefinedSchreier n l)).card

/-- `|F_{n,ℓ,k}|`: sets in `F_{n,ℓ}` with exactly `k`
elements. -/
def refinedSchreierCardCount (n l k : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (fun A => IsRefinedSchreier n l A ∧ A.card = k)).card

/-- `|F_{n,ℓ,k,q}|`: sets in `F_{n,ℓ,k}` whose smallest element
is `q`. -/
def refinedSchreierCardMinCount (n l k q : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (fun A => IsRefinedSchreier n l A ∧ A.card = k ∧
      q ∈ A ∧ ∀ x ∈ A, q ≤ x)).card

/-- **Proposition 2**: `|F_{n,m+1}| = p(n-1, m)` for `m ≤ n - 1`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Proposition 2. -/
theorem_wanted schreierSparseMinCount_eq (m n : ℕ) (hmn : m + 1 ≤ n) :
    schreierSparseMinCount n (m + 1) = partitionExactCount (n - 1) m

/-- **Corollary 3**: `|F_n| = p(n-1)` for `n ≥ 1`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 3. -/
theorem_wanted schreierSparseCount_eq (n : ℕ) (hn : 1 ≤ n) :
    schreierSparseCount n = partitionCount (n - 1)

/-- **Theorem 6, sparse case**:
`|A_{n,ℓ}| = Σ_{i=0}^{n-1} |E_{i,ℓ+1}|` for `n ≥ 1` and `ℓ ≥ 0`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 6. -/
theorem_wanted sparseStrongCount_eq_sum (n l : ℕ) (hn : 1 ≤ n) :
    sparseStrongCount n l =
      ∑ i ∈ Finset.range n, partitionMinPartCount i (l + 1)

/-- **Theorem 6, strongly sparse case**:
`|A^s_{n,ℓ}| = Σ_{i=0}^{n-1} |E^d_{i,ℓ+1}|` for `n ≥ 1` and
`ℓ ≥ 0`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 6. -/
theorem_wanted stronglySparseStrongCount_eq_sum (n l : ℕ)
    (hn : 1 ≤ n) :
    stronglySparseStrongCount n l =
      ∑ i ∈ Finset.range n, partitionDistinctMinPartCount i (l + 1)

/-- **Theorem 7, sparse case**: `|A_{n,ℓ}| = |G_{n-1,ℓ}|` for
positive `n` and `ℓ` (the paper's `ℕ` is the positive integers;
the identity fails at `ℓ = 0`).

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 7. -/
theorem_wanted sparseStrongCount_eq_noSmall (n l : ℕ) (hn : 1 ≤ n)
    (hl : 1 ≤ l) :
    sparseStrongCount n l = partitionNoSmallPartCount (n - 1) l

/-- **Theorem 7, strongly sparse case**:
`|A^s_{n,ℓ}| = |H_{n-1,ℓ}|` for positive `n` and `ℓ`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 7. -/
theorem_wanted stronglySparseStrongCount_eq_noSmallNoEven (n l : ℕ)
    (hn : 1 ≤ n) (hl : 1 ≤ l) :
    stronglySparseStrongCount n l =
      partitionNoSmallNoEvenCount (n - 1) l

/-- **Theorem 9, exact-cardinality case**:
`|B_{n,ℓ,m}| = c(n + ℓ, ℓ + 1, m)` for `n ≥ 1`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 9. -/
theorem_wanted strongSchreierCardCount_eq (m n l : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    strongSchreierCardCount n l m =
      compositionMinPartExactCount (n + l) (l + 1) m

/-- **Theorem 9, total case**: `|B_{n,ℓ}| = c(n + ℓ, ℓ + 1)` for
`n ≥ 1`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Theorem 9. -/
theorem_wanted strongSchreierCount_eq (n l : ℕ) (hn : 1 ≤ n) :
    strongSchreierCount n l = compositionMinPartCount (n + l) (l + 1)

/-- **Lemma 11**: `|F_{n,ℓ,k+1,ℓk+q}| = |E_{n,ℓ+1,k,q-1}|` for
`n ≥ ℓ + 1`, `k ≥ 2`, and `q ≥ 1`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Lemma 11. -/
theorem_wanted refinedSchreierCardMinCount_eq (n l k q : ℕ)
    (hn : l + 1 ≤ n) (hk : 2 ≤ k) (hq : 1 ≤ q) :
    refinedSchreierCardMinCount n l (k + 1) (l * k + q) =
      partitionMinPartGapCount n (l + 1) k (q - 1)

/-- **Corollary 12**: `|E_{n,ℓ+1,k}| = |F_{n,ℓ,k+1}|` for
`n ≥ ℓ + 1` and `k ≥ 2`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 12. -/
theorem_wanted partitionMinPartExactCount_eq_refined (n l k : ℕ)
    (hn : l + 1 ≤ n) (hk : 2 ≤ k) :
    partitionMinPartExactCount n (l + 1) k =
      refinedSchreierCardCount n l (k + 1)

/-- **Corollary 13**: `|E_{n,ℓ+1}| = |F_{n,ℓ}| + 1` for
`n ≥ ℓ + 1`.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 13. -/
theorem_wanted partitionMinPartCount_eq_refined_add_one (n l : ℕ)
    (hn : l + 1 ≤ n) :
    partitionMinPartCount n (l + 1) = refinedSchreierCount n l + 1

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted
