/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import WantedExt.NumberTheory.GobelSequenceWanted

/-!
# Non-integrality of `(k, l)`-Göbel sequences (statements)

Statement-only targets from Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of
the (k, l)-Göbel Sequences*. The sequence `g_{k,l}` is the existing `gobelSequence k l`;
`x ∈ ℤ_(p)` is `0 ≤ padicValRat p x`, as in `GobelSequenceWanted`. The thresholds `N_{k,l}`
are not defined; claims about them are stated directly through `gobelSequence`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The residue walk `tilde g_l` starts at `l` at index one and, while its value is strictly
between zero and `p`, adds the product of the two Jacobi symbols from the paper. At an endpoint
it stays fixed. The paper only uses indices `1 ≤ n ≤ p`; this totalization assigns zero at index
zero and continues the same update rule beyond `p`. For an odd prime, `jacobiSym` is the
Legendre symbol. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the
(k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2
definition of `tilde g_l`. -/
public def gobelResidueWalk (p l : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => l
  | n + 2 =>
      let x := gobelResidueWalk p l (n + 1)
      if 0 < x ∧ x < p then
        Int.toNat ((x : ℤ) + jacobiSym (n + 1 : ℤ) p * jacobiSym (x : ℤ) p)
      else
        x

/-- The residue walk has the paper's initial value at index one, with no hypotheses needed.
Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of
`tilde g_l`. -/
public theorem gobelResidueWalk_one (p l : ℕ) : gobelResidueWalk p l 1 = l := by
  rfl

/-- At an interior value, the residue walk obeys the Jacobi-symbol recurrence. The hypotheses
`1 ≤ n` and the use of `Int.toNat` expose respectively the paper's index range and the
conversion of its integer-valued update back to `ℕ`; for odd primes in the paper the update is
nonnegative. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the
(k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2
definition of `tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_between (p l n : ℕ) (hn : 1 ≤ n)
    (hbetween : 0 < gobelResidueWalk p l n ∧ gobelResidueWalk p l n < p) :
    gobelResidueWalk p l (n + 1) =
      Int.toNat ((gobelResidueWalk p l n : ℤ) +
        jacobiSym (n : ℤ) p * jacobiSym (gobelResidueWalk p l n : ℤ) p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hbetween ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then
      Int.toNat ((gobelResidueWalk p l (m + 1) : ℤ) +
        jacobiSym (m + 1 : ℤ) p * jacobiSym (gobelResidueWalk p l (m + 1) : ℤ) p)
    else gobelResidueWalk p l (m + 1)) = _
  simp [hbetween]

/-- Once the residue walk is zero, its next value is zero. The added hypothesis `1 ≤ n` is
the paper's indexing convention. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Section 2 definition of `tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_eq_zero (p l n : ℕ) (hn : 1 ≤ n)
    (hzero : gobelResidueWalk p l n = 0) :
    gobelResidueWalk p l (n + 1) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hzero ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then _
    else gobelResidueWalk p l (m + 1)) = 0
  simp [hzero]

/-- Once the residue walk is `p`, its next value is `p`. The added hypothesis `1 ≤ n` is
the paper's indexing convention. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Section 2 definition of `tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_eq_prime (p l n : ℕ) (hn : 1 ≤ n)
    (hprime : gobelResidueWalk p l n = p) :
    gobelResidueWalk p l (n + 1) = p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hprime ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then _
    else gobelResidueWalk p l (m + 1)) = p
  simp [hprime]

/-- `IsZigzagBelow p a b` is exactly the paper's relation `A ⪯ B`: some `m ≤ p` has
`a(n) < b(n)` on `1 ≤ n ≤ m`, and the two functions agree on `m < n ≤ p`. The point-set
notation is represented by its integer-valued coordinate function; values outside `1..p` are
ignored. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition
of `⪯`. -/
public def IsZigzagBelow (p : ℕ) (a b : ℕ → ℤ) : Prop :=
  ∃ m ≤ p,
    (∀ n, 1 ≤ n → n ≤ m → a n < b n) ∧
    (∀ n, m < n → n ≤ p → a n = b n)

/-- These are precisely the four conditions defining the paper's sequence `a_{p,l}`: values
are `±1` on `1..p-1`, the value at one is one, and clauses (b), (c), and (d) are the three
displayed symmetries. Since a function `ℕ → ℤ` is used instead of a finite sequence, values
outside `1..p-1` are fixed to zero solely to make literal function uniqueness express the
paper's uniqueness. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of
the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8,
Proposition 17. -/
public def IsGobelASequence (p l : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ n, 1 ≤ n → n ≤ p - 1 → a n = 1 ∨ a n = -1) ∧
  (∀ n, n = 0 ∨ p ≤ n → a n = 0) ∧
  a 1 = 1 ∧
  (∀ n, 1 ≤ n → n ≤ (p - 1) / 2 → a n = a (p - n)) ∧
  (∀ n, 1 ≤ n → n ≤ l / 2 → a n = -a (l + 1 - n)) ∧
  (∀ n, 1 ≤ n → n ≤ p - l - 2 → a n = a (l + 1 + n))

/-- These are precisely the conditions defining the periodically extended paper sequence
`b_{l,s}`: every value is `±1`, the function has period `l+1`, its value at one is one,
clause (b) holds off the zero residue class, and clause (c) holds for every integer. Using an
actual function `ℤ → ℤ` makes the paper's periodic extension explicit; no choice-defined
sequence is introduced. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality
of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8,
Proposition 20. -/
public def IsGobelBSequence (l s : ℕ) (b : ℤ → ℤ) : Prop :=
  (∀ n, b n = 1 ∨ b n = -1) ∧
  (∀ n, b (n + (l + 1 : ℤ)) = b n) ∧
  b 1 = 1 ∧
  (∀ n, Int.emod n (l + 1 : ℤ) ≠ 0 → b n = -b ((l + 1 : ℤ) - n)) ∧
  (∀ n, b ((s : ℤ) - n) = b ((s : ℤ) + 1 + n))

/-- This predicate says that `lL` is the paper's
`max {l even | tilde g_l(p)=0} + 2`. The quantified candidates are exactly the even naturals
`0 ≤ l ≤ p-1`; nonemptiness is included by exhibiting the maximum. Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, proof of Theorem 1. -/
public def IsGobelLeftBoundary (p lL : ℕ) : Prop :=
  ∃ l0, Even l0 ∧ l0 < p ∧ gobelResidueWalk p l0 p = 0 ∧ lL = l0 + 2 ∧
    ∀ l, Even l → l < p → gobelResidueWalk p l p = 0 → l ≤ l0

/-- This predicate says that `lR` is the paper's
`min {l even | tilde g_l(p)=p}`. The quantified candidates are exactly the even naturals
`0 ≤ l ≤ p-1`; membership and minimality encode the minimum. Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, proof of Theorem 1. -/
public def IsGobelRightBoundary (p lR : ℕ) : Prop :=
  Even lR ∧ lR < p ∧ gobelResidueWalk p lR p = p ∧
    ∀ l, Even l → l < p → gobelResidueWalk p l p = p → lR ≤ l

/-- For an odd prime `p ≡ 3 (mod 4)`, every `0 ≤ l < p` gives localization membership
`g_{(p-1)/2,l}(p) ∈ ℤ_(p)`, encoded as nonnegative `padicValRat`. Naturals make the printed
lower bound `0 ≤ l` automatic; all other clauses are unchanged. Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Theorem 1(a). -/
public theorem_wanted gobelSequence_half_pred_mem_localization_of_three_mod_four
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 3) :
    ∀ l, l < p → 0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p)

/-- For an odd prime `p ≡ 1 (mod 4)`, every odd `0 ≤ l < p` gives localization membership.
Membership is encoded by nonnegative `padicValRat`, and the lower bound is automatic for
naturals. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 1(b), odd
case. -/
public theorem_wanted gobelSequence_half_pred_mem_localization_of_one_mod_four_of_odd
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    ∀ l, Odd l → l < p → 0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p)

/-- For `p ≥ 13` in the one-mod-four case, this is the paper's unique decomposition encoded
by its unique even boundary pair. The three intervals are represented by the equivalent
localization criterion `l < lL ∨ lR ≤ l` for every even `l < p`; the pair conditions encode
`2 ≤ lL < lR ≤ p-1`. Naturals make all printed nonnegativity clauses automatic. Source: Yuh
Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 1(b), unique decomposition. -/
public theorem_wanted gobelSequence_half_pred_unique_even_localization_decomposition
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (hp13 : 13 ≤ p) :
    ∃! bounds : ℕ × ℕ,
      Even bounds.1 ∧ Even bounds.2 ∧ 2 ≤ bounds.1 ∧ bounds.1 < bounds.2 ∧
      bounds.2 ≤ p - 1 ∧
      ∀ l, Even l → l < p →
        (0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p) ↔
          l < bounds.1 ∨ bounds.2 ≤ l)

/-- Let `p ≥ 13` be a prime with `p ≡ 1 (mod 4)` and `k` a positive odd multiple of
`(p-1)/2` (such `k` is automatically positive and even, so the paper's hypothesis "`k` positive
even" is implied and not repeated). Then there is an even
`2 ≤ l ≤ p-3` such that every positive `l' ≡ l (mod p)` has negative `p`-adic valuation
at index `p`. The final bounded witness is the formal counterpart of `N_{k,l'} ≤ p`, stated
directly because no threshold object is introduced. Congruence is natural-number remainder.
Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Corollary 2. -/
public theorem_wanted gobelSequence_nonintegral_congruence_class_of_odd_multiple
    (k p : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p)
    (hmod : p % 4 = 1)
    (hmultiple : ∃ q, 0 < q ∧ Odd q ∧ k = ((p - 1) / 2) * q) :
    ∃ l, Even l ∧ 2 ≤ l ∧ l ≤ p - 3 ∧
      ∀ l', 0 < l' → l' % p = l % p →
        padicValRat p (gobelSequence k l' p) < 0 ∧
        ∃ n, 1 ≤ n ∧ n ≤ p ∧ ¬∃ z : ℤ, gobelSequence k l' n = z

/-- No finite collection of the displayed prime-indexed sets covers their union: for every
finite set `S` of candidate primes there is a natural `k` lying in
`(p-1)/2 * (2ℕ+1)` for some prime `p ≥ 13`, `p ≡ 1 (mod 4)`, but in none of the sets
indexed by members of `S`, where `S` ranges over finite sets of such primes.
Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 3. -/
public theorem_wanted odd_multiple_prime_half_sets_not_finitely_coverable :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1) → ∃ k,
      (∃ p m, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1 ∧
        k = ((p - 1) / 2) * (2 * m + 1)) ∧
      ∀ p ∈ S, ¬∃ m, k = ((p - 1) / 2) * (2 * m + 1)

/-- For a fixed odd prime and `0 ≤ l ≤ p-1`, the congruence
`n g_{(p-1)/2,l}(n) ≡ tilde g_l(n) (mod p)` holds for `1 ≤ n ≤ p`, and localization
membership at `p` is equivalent to the endpoint being zero or `p`. Congruence in
`ℤ_(p)` is encoded by the difference being zero or having valuation at least one; the
explicit zero case is necessary because Mathlib sets `padicValRat p 0 = 0`. Source: Yuh
Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 6. -/
public theorem_wanted gobelSequence_half_pred_congruent_residue_walk
    (p l : ℕ) (hp : p.Prime) (hpodd : Odd p) (hl : l ≤ p - 1) :
    (∀ n, 1 ≤ n → n ≤ p →
      let d : ℚ := (n : ℚ) * gobelSequence ((p - 1) / 2) l n - gobelResidueWalk p l n
      d = 0 ∨ 1 ≤ padicValRat p d) ∧
    (0 ≤ padicValRat p (gobelSequence ((p - 1) / 2) l p) ↔
      gobelResidueWalk p l p = 0 ∨ gobelResidueWalk p l p = p)

/-- If the residue walk meets the diagonal at `m`, it remains on the diagonal through `p`.
The fixed-section hypotheses that `p` is an odd prime and `0 ≤ l ≤ p-1` are explicit;
natural-number indices make the lower bound on `l` automatic. Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Lemma 8. -/
public theorem_wanted gobelResidueWalk_eq_index_of_eq_index
    (p l m : ℕ) (hp : p.Prime) (hpodd : Odd p) (hl : l ≤ p - 1)
    (hm1 : 1 ≤ m) (hmp : m ≤ p) (hmeq : gobelResidueWalk p l m = m) :
    ∀ n, m ≤ n → n ≤ p → gobelResidueWalk p l n = n

/-- For every odd `1 ≤ l < p`, the diagonal is zigzag-below the residue walk. The paper's
point sets are represented by their integer coordinate functions, with all fixed-section
hypotheses on the odd prime `p` and the bound on `l` explicit. Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Proposition 9. -/
public theorem_wanted diagonal_isZigzagBelow_gobelResidueWalk_of_odd
    (p l : ℕ) (hp : p.Prime) (hpodd : Odd p) (hlodd : Odd l) (hlp : l < p) :
    IsZigzagBelow p (fun n => (n : ℤ)) (fun n => gobelResidueWalk p l n)

/-- When `p ≡ 3 (mod 4)`, every even residue walk is zigzag-below the reflected diagonal
`n ↦ p-n`. The paper's point sets are coordinate functions, and the fixed-section
hypotheses on the odd prime and `0 ≤ l < p` are explicit. Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Proposition 10. -/
public theorem_wanted gobelResidueWalk_isZigzagBelow_antidiagonal_of_three_mod_four
    (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 3)
    (hleven : Even l) (hlp : l < p) :
    IsZigzagBelow p (fun n => gobelResidueWalk p l n) (fun n => (p : ℤ) - n)

/-- When `p ≡ 1 (mod 4)`, consecutive even residue walks form the paper's chain
`G_0 ⪯ G_2 ⪯ ... ⪯ G_{p-1}`. The display is expanded into its equivalent adjacent-link
statement for every even `l` with `l+2 ≤ p-1`; the fixed-section odd-prime hypotheses are
explicit. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Proposition 11. -/
public theorem_wanted gobelResidueWalk_even_chain_of_one_mod_four
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    ∀ l, Even l → l + 2 ≤ p - 1 →
      IsZigzagBelow p (fun n => gobelResidueWalk p l n)
        (fun n => gobelResidueWalk p (l + 2) n)

/-- For `p ≡ 1 (mod 4)`, the left and right boundaries defined from the residue walk are
equal exactly when some even `0 ≤ l ≤ p-3` satisfies the two displayed Jacobi/Legendre-symbol
symmetries. The theorem quantifies any `lL,lR` satisfying the paper's max/min definitions;
`jacobiSym` is used consistently and equals the Legendre symbol for the odd prime. Naturals
make the lower bounds automatic. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Theorem 15. -/
public theorem_wanted gobel_boundaries_eq_iff_jacobi_symmetries
    (p lL lR : ℕ) (hp : p.Prime) (hmod : p % 4 = 1)
    (hleft : IsGobelLeftBoundary p lL) (hright : IsGobelRightBoundary p lR) :
    lL = lR ↔
      ∃ l, Even l ∧ l ≤ p - 3 ∧
        (∀ n, 1 ≤ n → n ≤ l / 2 →
          jacobiSym (n : ℤ) p = -jacobiSym (l + 1 - n : ℤ) p) ∧
        (∀ n, 1 ≤ n → n ≤ p - l - 2 →
          jacobiSym (n : ℤ) p = jacobiSym (l + 1 + n : ℤ) p)

/-- Lemma 16 (arithmetic billiards). Let `p ≡ 1 (mod 4)` be prime and `l` even with
`0 ≤ l ≤ p - 3`. For `l ≤ (p - 5)/2` let `R` be the rectangle with vertices `(0, l+1)`,
`(l+1, 0)`, `(p/2, p/2 - (l+1))`, `(p/2 - (l+1), p/2)`, and for `l ≥ (p - 1)/2` the rectangle
with vertices `(0, p-(l+1))`, `(p-(l+1), 0)`, `(p/2, (l+1) - p/2)`, `((l+1) - p/2, p/2)`; write
`(0, m)`, `(m, 0)` for its first two vertices and `L` for the lattice points on its boundary other
than these two. The path that starts at `(0, m)`, runs horizontally, and alternately turns
vertical and horizontal at each boundary hit (a sequence `P` of boundary lattice points, each
step moving to a different boundary point in the same row for even steps and the same column
for odd steps) exists; it visits each of the `p - 2` points of `L` exactly once at steps
`1, …, p - 2`, reaches `(m, 0)` at step `p - 1`, and is symmetric in the line `y = x`. In the
second case the paper says only "a similar statement holds"; it is read with the second
rectangle's vertices `(0, m)` and `(m, 0)` as start and end. Turning points are lattice points
because every edge lies on a line `x ± y = const` with integer constant.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 16
(`lem:billiards`). -/
public theorem_wanted arithmetic_billiards_rotated_rectangle (p l : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hl : Even l) (hlp : l + 3 ≤ p) :
    let m : ℕ := if 2 * l + 5 ≤ p then l + 1 else p - (l + 1)
    let c : ℝ := if 2 * l + 5 ≤ p then (p : ℝ) / 2 - (l + 1) else (l + 1 : ℝ) - p / 2
    let R : Set (ℝ × ℝ) :=
      convexHull ℝ {((0 : ℝ), (m : ℝ)), ((m : ℝ), (0 : ℝ)), ((p : ℝ) / 2, c), (c, (p : ℝ) / 2)}
    let L : Set (ℤ × ℤ) :=
      {z | ((z.1 : ℝ), (z.2 : ℝ)) ∈ frontier R} \ {((0 : ℤ), (m : ℤ)), ((m : ℤ), (0 : ℤ))}
    let IsPath : (ℕ → ℤ × ℤ) → Prop := fun P =>
      P 0 = (0, (m : ℤ)) ∧ ∀ i < p - 1,
        (((P (i + 1)).1 : ℝ), ((P (i + 1)).2 : ℝ)) ∈ frontier R ∧ P (i + 1) ≠ P i ∧
          if Even i then (P (i + 1)).2 = (P i).2 else (P (i + 1)).1 = (P i).1
    (∃ P, IsPath P) ∧ ∀ P, IsPath P →
      Set.BijOn P (Set.Icc 1 (p - 2)) L ∧ P (p - 1) = ((m : ℤ), 0) ∧
        ∀ i ≤ p - 1, P (p - 1 - i) = (P i).swap

/-- Under the paper's prime and parity hypotheses, there exists exactly one function satisfying
the four defining conditions of `a_{p,l}`. The zero extension built into
`IsGobelASequence` is the only deviation from the finite index set and makes `∃!` literal;
no choice-defined sequence is introduced. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note
on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026),
Article 26.3.8, Proposition 17. -/
public theorem_wanted existsUnique_gobelASequence
    (p l : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (hleven : Even l) (hl : l ≤ p - 3) :
    ∃! a : ℕ → ℤ, IsGobelASequence p l a

/-- If `l` is nonnegative even, `0 ≤ s ≤ l`, and `2s+1` is coprime to `l+1`, there is
exactly one periodically extended `±1` function satisfying clauses (a), (b), and (c).
Nonnegativity is automatic for naturals, periodicity is explicit on `ℤ`, and no
choice-defined sequence is introduced. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Proposition 20. -/
public theorem_wanted existsUnique_gobelBSequence
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hcoprime : Nat.Coprime (2 * s + 1) (l + 1)) :
    ∃! b : ℤ → ℤ, IsGobelBSequence l s b

/-- For any functions satisfying the defining conditions for `b_{l,s}` and `b_{l,l-s}`,
their values agree off the zero residue class modulo `l+1` and are negatives on that class.
This states the lemma for every admissible realization instead of naming choice-defined unique
sequences. All Proposition 20 hypotheses and the printed assumption `l ≥ 2` are explicit.
Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 22. -/
public theorem_wanted gobelBSequence_complement
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hl2 : 2 ≤ l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    (b₁ b₂ : ℤ → ℤ) (hb₁ : IsGobelBSequence l s b₁)
    (hb₂ : IsGobelBSequence l (l - s) b₂) :
    ∀ n, (Int.emod n (l + 1 : ℤ) ≠ 0 → b₁ n = b₂ n) ∧
      (Int.emod n (l + 1 : ℤ) = 0 → b₁ n = -b₂ n)

/-- Every function satisfying the defining conditions for `b_{l,s}` obeys all three
translations/reflection identities of the paper. Clauses (b) and (c) use
`t = l/2-s` inline, and divisibility is encoded by `Int.emod = 0`. This avoids introducing
the unique sequence by choice; all Proposition 20 hypotheses and `l ≥ 2` are explicit.
Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 23. -/
public theorem_wanted gobelBSequence_translation_identities
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hl2 : 2 ≤ l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    (b : ℤ → ℤ) (hb : IsGobelBSequence l s b) :
    (∀ n : ℤ, Int.emod n (l + 1 : ℤ) ≠ 0 →
      Int.emod (n + (2 * s + 1 : ℕ)) (l + 1 : ℤ) ≠ 0 →
      b n = -b (n + (2 * s + 1 : ℕ))) ∧
    (s < l / 2 →
      ∀ n : ℤ, Int.emod n (l + 1 : ℤ) ≠ 0 →
        Int.emod (n + (2 * (l / 2 - s) : ℕ)) (l + 1 : ℤ) ≠ 0 →
        b n = -b (n + (2 * (l / 2 - s) : ℕ))) ∧
    (s < l / 2 →
      ∀ n : ℤ, Int.emod (((l / 2 - s : ℕ) : ℤ) - n) (l + 1 : ℤ) ≠ 0 →
        Int.emod (((l / 2 - s : ℕ) : ℤ) + n) (l + 1 : ℤ) ≠ 0 →
        b (((l / 2 - s : ℕ) : ℤ) - n) = b (((l / 2 - s : ℕ) : ℤ) + n))

/-- For every function satisfying the defining conditions for `a_{p,l}`, some positive
`m` with `2m ≤ p-3` violates `a(2m)=a(2)a(m)`. This is equivalent to naming the unique
sequence by Proposition 17 but avoids choice. All printed bounds, parity, primality, and
congruence hypotheses are unchanged. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Theorem 25. -/
public theorem_wanted gobelASequence_not_multiplicative_at_even_index
    (p l : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hmod : p % 4 = 1)
    (hleven : Even l) (hl2 : 2 ≤ l) (hlp : l ≤ p - 3)
    (a : ℕ → ℤ) (ha : IsGobelASequence p l a) :
    ∃ m, 0 < m ∧ 2 * m ≤ p - 3 ∧ a (2 * m) ≠ a 2 * a m

/-- The first nonintegral term of `g_{2600725,2}` is exactly index `9011`: the value there
is not an integer and every positive earlier value is an integer. This direct formulation is
the paper's `N_{2600725}=9011` and avoids defining `N_k`. Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Theorem 26. -/
public theorem_wanted gobelSequence_first_nonintegral_2600725 :
    (¬∃ z : ℤ, gobelSequence 2600725 2 9011 = z) ∧
    ∀ n, 1 ≤ n → n < 9011 → ∃ z : ℤ, gobelSequence 2600725 2 n = z

/-- For every `2 ≤ k ≤ 10^7`, some positive index at most `9011` is nonintegral, directly
encoding `N_k ≤ 9011`. Together with the preceding exact equality this says the largest
threshold in the range is `9011`. The uncheckable claim that every value was explicitly
determined in an external repository is deliberately omitted as instructed. Source: Yuh
Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 26. -/
public theorem_wanted gobelSequence_nonintegral_index_le_9011
    (k : ℕ) (hk2 : 2 ≤ k) (hkmax : k ≤ 10 ^ 7) :
    ∃ n, 1 ≤ n ∧ n ≤ 9011 ∧ ¬∃ z : ℤ, gobelSequence k 2 n = z

/-- Among the `9999999` naturals `2 ≤ k ≤ 10^7`, exactly `8649270` have a prime first
nonintegral index. The subtype counted by `Nat.card` spells out primality, nonintegrality at
`q`, and integrality at every earlier positive index. Finiteness for every `k` in the range
is supplied by the preceding theorem-wanted; the paper's percentage and external table are
omitted. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Theorem 26. -/
public theorem_wanted card_gobelSequence_prime_first_nonintegral_index :
    Nat.card {k : ℕ // 2 ≤ k ∧ k ≤ 10 ^ 7 ∧
      ∃ q, q.Prime ∧ (¬∃ z : ℤ, gobelSequence k 2 q = z) ∧
        ∀ n, 1 ≤ n → n < q → ∃ z : ℤ, gobelSequence k 2 n = z} = 8649270

/-- For every `2 ≤ k ≤ 10^14`, a positive nonintegral term occurs by index `29363`.
This is the direct formulation of `N_k ≤ 29363`, avoiding a threshold definition while
preserving both printed bounds. Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Theorem 29. -/
public theorem_wanted gobelSequence_nonintegral_index_le_29363
    (k : ℕ) (hk2 : 2 ≤ k) (hkmax : k ≤ 10 ^ 14) :
    ∃ n, 1 ≤ n ∧ n ≤ 29363 ∧ ¬∃ z : ℤ, gobelSequence k 2 n = z

end

end MetaMathlibExt
