/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Extending Sidon sets to perfect difference sets (Erdős Problem 707)

Erdős Problem 707: let `A ⊂ ℕ` be a finite Sidon set. Is there some set `B` with `A ⊆ B` which is a
perfect difference set modulo `p² + p + 1` for some prime `p`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.Combinatorics.SidonPerfectDifferenceSetErdosProblem707Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #707, https://www.erdosproblems.com/707 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006987 (`EP-707`), dataset ulamai/UnsolvedMath v1.8.0.

Sidon is MathlibExt's `Set.IsSidon` (repeated summands included). `B ⊆ ℕ` is a perfect difference
set modulo `v` when every nonzero residue is `a - b (mod v)` for exactly one ordered pair `(a, b) ∈
B × B`; uniqueness forces the elements of `B` to be distinct modulo `v`. A second target is Erdős's
weaker form with modulus `m² + m + 1`, `m ≥ 1` (every finite perfect difference set with at least
two elements has such a modulus); `m = 0` (modulus `1`) is excluded since every set is vacuously a
perfect difference set modulo `1`. Compared with the formal-conjectures statement
`ErdosProblems/707.lean` (formal-conjectures uses any positive modulus in its main statement; no
code imported).
-/

/-- `B ⊆ ℕ` is a perfect difference set modulo `v`: every nonzero residue modulo `v` is
`a - b (mod v)` for exactly one ordered pair `(a, b)` of elements of `B`. -/
def IsPerfectDifferenceSetMod (B : Set ℕ) (v : ℕ) : Prop :=
  ∀ x : ZMod v, x ≠ 0 → ∃! ab : ℕ × ℕ, ab.1 ∈ B ∧ ab.2 ∈ B ∧ (ab.1 : ZMod v) - ab.2 = x

/-- Erdős Problem 707: every finite Sidon set `A ⊆ ℕ` is contained in a perfect difference set
modulo `p² + p + 1` for some prime `p`. -/
def sidonExtendsToPrimePerfectDifferenceSet : Prop :=
  ∀ A : Set ℕ, A.Finite → A.IsSidon →
    ∃ p : ℕ, p.Prime ∧ ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSetMod B (p ^ 2 + p + 1)

/-- The weaker form Erdős also asked: every finite Sidon set is contained in a perfect difference
set modulo `m² + m + 1` for some `m ≥ 1`. -/
def sidonExtendsToPerfectDifferenceSet : Prop :=
  ∀ A : Set ℕ, A.Finite → A.IsSidon →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSetMod B (m ^ 2 + m + 1)

/--
Resolved false: Alexeev and Mixon proved that the Sidon set `{1, 2, 4, 8}` cannot be extended to a
perfect difference set modulo `p² + p + 1` for any prime `p` (their proof is formalized in Lean);
erdosproblems.com/707 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#707, https://www.erdosproblems.com/707 (status DISPROVED (LEAN)); resolution: B. Alexeev and D. G.
Mixon, Forbidden Sidon subsets of perfect difference sets, featuring a human-assisted proof,
arXiv:2510.19804 (2025); M. Hall, Jr., Cyclic projective planes, Duke Math. J. 14 (1947), 1079-1090,
abstract of arXiv:2510.19804: {1, 2, 4, 8, 13} is a finite Sidon set contained in no finite perfect
difference set; erdosproblems.com/707: {1, 2, 4, 8} cannot be extended to a perfect difference set
modulo p² + p + 1 for any prime p, and Hall's {1, 3, 9, 10, 13} cannot be extended to any perfect
difference set, https://arxiv.org/abs/2510.19804.
-/
public theorem_wanted sidonExtendsToPrimePerfectDifferenceSet_refuted :
    ¬ sidonExtendsToPrimePerfectDifferenceSet

/--
Resolved false: Alexeev and Mixon proved that the Sidon set `{1, 2, 4, 8, 13}` is contained in no
perfect difference set, and Hall (1947) proved the same for `{1, 3, 9, 10, 13}`; so the weaker form
with modulus `m² + m + 1` also fails. Source: T. F. Bloom, Erdős Problems, Problem #707,
https://www.erdosproblems.com/707 (status DISPROVED (LEAN)); resolution: B. Alexeev and D. G. Mixon,
Forbidden Sidon subsets of perfect difference sets, featuring a human-assisted proof,
arXiv:2510.19804 (2025); M. Hall, Jr., Cyclic projective planes, Duke Math. J. 14 (1947), 1079-1090,
abstract of arXiv:2510.19804: {1, 2, 4, 8, 13} is a finite Sidon set contained in no finite perfect
difference set; erdosproblems.com/707: {1, 2, 4, 8} cannot be extended to a perfect difference set
modulo p² + p + 1 for any prime p, and Hall's {1, 3, 9, 10, 13} cannot be extended to any perfect
difference set, https://arxiv.org/abs/2510.19804.
-/
public theorem_wanted sidonExtendsToPerfectDifferenceSet_refuted :
    ¬ sidonExtendsToPerfectDifferenceSet

end MathlibExt.Combinatorics.SidonPerfectDifferenceSetErdosProblem707Wanted
