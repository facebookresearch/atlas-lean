/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The weak order on the symmetric group is Sperner (Cooper's problem list)

J. Cooper, Combinatorial Problems I Like, Matroids, Lattices, and Posets: is the weak order on `S_n`
(the "inversion" poset) Sperner?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Antichain

@[expose] public section

namespace MathlibExt.Combinatorics.WeakOrderSpernerAMR30Problem0039Wanted

/-!
Source: J. Cooper, Combinatorial Problems I Like (2020 snapshot), Matroids, Lattices, and Posets,
item 39, https://people.math.sc.edu/cooper/combprob.html. UnsolvedMath record UM-03100039
(`AMR-030-0039`), dataset ulamai/UnsolvedMath v1.8.0.

The weak order compares inversion sets, `σ ≤ τ` iff `Inv(σ) ⊆ Inv(τ)`, with inversions taken as
pairs of positions (the left weak order; the right weak order, by value pairs, is isomorphic via `σ
↦ σ⁻¹`, so the Sperner property is the same). It is graded by the number of inversions; Sperner
means that no antichain is larger than the largest rank level. The target is stated for every `n`.
-/

/-- The inversion set of `σ ∈ S_n`: the pairs of positions `i < j` with `σ j < σ i`. -/
def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ σ p.2 < σ p.1

/-- The weak order on `S_n` (the inversion poset): `σ ≤ τ` iff the inversion set of `σ` is
contained in that of `τ`. -/
def weakLE {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : Prop :=
  inversions σ ⊆ inversions τ

/-- The weak order on `S_n` is Sperner, for every `n`: no antichain is larger than the largest rank
level, the rank of `σ` being its number of inversions. -/
def weakOrderSperner : Prop :=
  ∀ (n : ℕ) (A : Finset (Equiv.Perm (Fin n))), IsAntichain weakLE (A : Set (Equiv.Perm (Fin n))) →
    ∃ k : ℕ, A.card ≤
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => (inversions σ).card = k).card

/--
Resolved true: Gaetz and Gao prove Stanley's conjecture that the weak order on `S_n` is strongly
Sperner (a Peck poset); in particular it is Sperner. Source: J. Cooper, Combinatorial Problems I
Like (2020 snapshot), Matroids, Lattices, and Posets, item 39,
https://people.math.sc.edu/cooper/combprob.html; resolution: C. Gaetz and Y. Gao, A combinatorial
sl₂-action and the Sperner property for the weak order, Proc. Amer. Math. Soc. 148 (2020);
arXiv:1811.05501, abstract: the sl₂-representation resolves Stanley's conjecture that the weak order
has the strong Sperner property (and is a Peck poset); strongly Sperner implies Sperner,
https://doi.org/10.1090/proc/14655.
-/
public theorem_wanted weakOrderSperner_holds : weakOrderSperner

end MathlibExt.Combinatorics.WeakOrderSpernerAMR30Problem0039Wanted
