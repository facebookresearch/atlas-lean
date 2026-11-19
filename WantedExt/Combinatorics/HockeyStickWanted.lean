/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A generalized hockey stick theorem

Statement from Molly Lynch and Michael Weselcouch, "A
Generalized Hockey Stick Theorem", *Journal of Integer
Sequences* 28 (2025), Article 25.7.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Weselcouch/wesel8.html>).

Corollary 14 is the classical hockey stick identity,
already in Mathlib as `Nat.sum_range_add_choose`.
Corollary 15 (namespace `MathlibExt.Combinatorics.HockeyStickWanted`)
was verified numerically for `n < 8`, `k < 14`. The
generalized identity (Corollary 13) and the paper's
combinatorial framework (compositions with parts in
`[2, r + 1]`, labeled tableaux `Λ(α, r)`, lattice
sequences `𝓛(m, h)`, Propositions 1, 4, 11, Lemma 9,
Theorem 12) are stated in namespace `MetaMathlibExt`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.HockeyStickWanted

/-- **Corollary 15**:
`∑_{i=0}^k C(2i + n, i)
  = ∑_{i=0}^{⌊k/2⌋} (-1)^i C(2k + 1 + n - i, k - 2i)`.

Source: Molly Lynch and Michael Weselcouch, "A
Generalized Hockey Stick Theorem", Corollary 15. -/
theorem_wanted sum_choose_two_mul_add (n k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        (Nat.choose (2 * i + n) i : ℤ)) =
      ∑ i ∈ Finset.range (k / 2 + 1),
        (-1 : ℤ) ^ i *
          (Nat.choose (2 * k + 1 + n - i) (k - 2 * i) : ℤ)

end MathlibExt.Combinatorics.HockeyStickWanted

namespace MetaMathlibExt

/-- The sign `sgn(α) = (-1)^{|α| - ℓ(α)}` of a composition `α`, given as its list of parts.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.2. -/
def hockeyCompositionSign (α : List ℕ) : ℤ :=
  (-1) ^ (α.sum - α.length)

/-- `sgn((2)) = -1` and `sgn((3, 1)) = 1`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.2. -/
theorem hockeyCompositionSign_small :
    hockeyCompositionSign [2] = -1 ∧ hockeyCompositionSign [3, 1] = 1 := by
  decide

/-- For a composition `α = (a, t…)` with `a ≥ 2`, each of `α^→ = (a + 1, t…)`,
`α^↑ = (2, a, t…)` and `α^↙` (`(a - 1, t…)` if `a > 2`, `(t…)` if `a = 2`) has sign `-sgn(α)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Proposition 1 (`jis-2025-25.7.7-prop-1`). -/
theorem_wanted hockeyCompositionSign_ops (a : ℕ) (t : List ℕ) (ha : 2 ≤ a)
    (ht : ∀ b ∈ t, 0 < b) :
    hockeyCompositionSign ((a + 1) :: t) = -hockeyCompositionSign (a :: t) ∧
      hockeyCompositionSign (2 :: a :: t) = -hockeyCompositionSign (a :: t) ∧
      hockeyCompositionSign (if 2 < a then (a - 1) :: t else t) = -hockeyCompositionSign (a :: t)

/-- The set `𝒞(k, r)` of compositions of some `j ≤ k` with every part in `[2, r + 1]`, as lists
of parts.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.2 (definition of `c(k, r)` and `𝒞(k, r)`). -/
def hockeyCompositions (k r : ℕ) : Finset (List ℕ) :=
  (Finset.range (k + 1)).biUnion fun j =>
    (Finset.range (j + 1)).biUnion fun l =>
      ((Finset.Nat.antidiagonalTuple l j).filter fun x => ∀ i, 2 ≤ x i ∧ x i ≤ r + 1).image
        List.ofFn

/-- `𝒞(5, 3) = {∅, (2), (3), (4), (2, 2), (2, 3), (3, 2)}`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Example following Proposition 1. -/
theorem hockeyCompositions_five_three :
    hockeyCompositions 5 3 = {[], [2], [3], [4], [2, 2], [2, 3], [3, 2]} := by
  decide

/-- The labeled tableaux `Λ(α, r)` of shape `α`: in each row `i` the entries after the empty first
box are strictly increasing labels in `{0, …, r - 1}`, recorded as the set of the `α_i - 1` labels
of the row.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.3 (labeled tableaux). -/
def labeledTableaux (α : List ℕ) (r : ℕ) : Finset (Fin α.length → Finset (Fin r)) :=
  Fintype.piFinset fun i => (Finset.univ : Finset (Fin r)).powersetCard (α.get i - 1)

/-- `|Λ((2, 2), 2)| = 4` and `|Λ(∅, 3)| = 1`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.3 (labeled tableaux). -/
theorem card_labeledTableaux_small :
    (labeledTableaux [2, 2] 2).card = 4 ∧ (labeledTableaux [] 3).card = 1 := by
  decide

/-- `|Λ(α, r)| = ∏_j C(r, α_j - 1)` (equal to `1` for `α = ∅`).

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Proposition 4 (`jis-2025-25.7.7-prop-4`). -/
theorem_wanted card_labeledTableaux (α : List ℕ) (r : ℕ) :
    (labeledTableaux α r).card = (α.map fun a => r.choose (a - 1)).prod

/-- The lattice sequences `𝓛(m, h)` of width `m` and height `h`:
`0 = L_0 ≤ L_1 ≤ ⋯ ≤ L_{m+1} = h`, as maps `Fin (m + 2) → Fin (h + 1)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.4 (lattice sequences). -/
def latticeSequences (m h : ℕ) : Finset (Fin (m + 2) → Fin (h + 1)) :=
  Finset.univ.filter fun L =>
    L 0 = 0 ∧ (∀ i : Fin (m + 1), L i.castSucc ≤ L i.succ) ∧ L (Fin.last (m + 1)) = Fin.last h

/-- `|𝓛(1, 1)| = 2` and `|𝓛(2, 2)| = 6 = C(4, 2)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.4 (lattice sequences). -/
theorem card_latticeSequences_small :
    (latticeSequences 1 1).card = 2 ∧ (latticeSequences 2 2).card = 6 := by
  decide

/-- The entry `L_j` of a lattice sequence (`0` past the end).

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.4. -/
def latticeEntry {m h : ℕ} (L : Fin (m + 2) → Fin (h + 1)) (j : ℕ) : ℕ :=
  if hj : j < m + 2 then (L ⟨j, hj⟩ : ℕ) else 0

/-- `ω_η(L) = L_{η+1} - L_η`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.4. -/
def latticeOmega {m h : ℕ} (L : Fin (m + 2) → Fin (h + 1)) (η : ℕ) : ℕ :=
  latticeEntry L (η + 1) - latticeEntry L η

/-- `γ_η(L)`: the largest ascent `i ∈ {0, …, η - 1}` (`L_i < L_{i+1}`) of `L_{[0, η]}`, or `-1` if
there is none.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.4. -/
def latticeGamma {m h : ℕ} (L : Fin (m + 2) → Fin (h + 1)) (η : ℕ) : ℤ :=
  ((((Finset.range η).filter fun i => latticeEntry L i < latticeEntry L (i + 1)).image
    fun i : ℕ => (i : ℤ)).max).unbotD (-1)

/-- `μ_η(L) = η - 1 - γ_η(L)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.4. -/
def latticeMu {m h : ℕ} (L : Fin (m + 2) → Fin (h + 1)) (η : ℕ) : ℤ :=
  η - 1 - latticeGamma L η

/-- For `L = (0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4)` and `η = 9`: `ω = 2`, `γ = 4`, `μ = 4`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Example before Lemma 9. -/
theorem lattice_omega_gamma_mu_example :
    latticeOmega (m := 12) (h := 4) ![0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4] 9 = 2 ∧
      latticeGamma (m := 12) (h := 4) ![0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4] 9 = 4 ∧
      latticeMu (m := 12) (h := 4) ![0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4] 9 = 4 := by
  decide

/-- With `η = rk + n + 1`, the number of `L ∈ 𝓛(η, k)` with `μ_η(L) ≥ r ω_η(L)` and
`ω_η(L) = k - i` is `C((r + 1)i + n, i)`, for `i ≤ k`. The paper allows every `i ≥ 0`; for
`i > k` the set is empty (`r = k = n = 0`, `i = 1`: `0 ≠ C(1, 1) = 1`).

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Lemma 9 (`jis-2025-25.7.7-lem-9`). -/
theorem_wanted card_latticeSequences_mu_ge (r k n i : ℕ) (hi : i ≤ k) :
    ((latticeSequences (r * k + n + 1) k).filter fun L =>
        (r : ℤ) * latticeOmega L (r * k + n + 1) ≤ latticeMu L (r * k + n + 1) ∧
          latticeOmega L (r * k + n + 1) = k - i).card =
      ((r + 1) * i + n).choose i

/-- For `α ∈ 𝒞(k, r)`, the number of labeled lattice sequences `(λ, L)` of type `(k, n, r)` with
`sh(λ) = α` (`λ ∈ Λ(α, r)`, `L ∈ 𝓛(rk + n + 1 + ℓ(α), k - |α|)`) is
`(∏_j C(r, α_j - 1)) · C((r + 1)k + n + 1 - |α| + ℓ(α), k - |α|)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Proposition 11 (`jis-2025-25.7.7-prop-11`). -/
theorem_wanted card_labeledLatticeSequences (k n r : ℕ) (α : List ℕ)
    (hα : α ∈ hockeyCompositions k r) :
    (labeledTableaux α r ×ˢ latticeSequences (r * k + n + 1 + α.length) (k - α.sum)).card =
      (α.map fun a => r.choose (a - 1)).prod *
        ((r + 1) * k + n + 1 - α.sum + α.length).choose (k - α.sum)

/-- The total weight `∑ sgn(λ)` over the labeled lattice sequences `(λ, L)` of type `(k, n, r)`
is `∑_{i=0}^k C((r + 1)i + n, i)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Theorem 12 (`jis-2025-25.7.7-thm-12`). -/
theorem_wanted sum_sign_labeledLatticeSequences (k n r : ℕ) :
    ∑ α ∈ hockeyCompositions k r,
        ∑ _p ∈ labeledTableaux α r ×ˢ latticeSequences (r * k + n + 1 + α.length) (k - α.sum),
          hockeyCompositionSign α =
      ∑ i ∈ Finset.range (k + 1), (((r + 1) * i + n).choose i : ℤ)

/-- The generalized hockey stick identity
`∑_{i=0}^k C((r + 1)i + n, i) = ∑_{α ∈ 𝒞(k, r)} sgn(α) (∏_j C(r, α_j - 1))
C((r + 1)k + n + 1 - |α| + ℓ(α), k - |α|)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Corollary 13 (`jis-2025-25.7.7-cor-13`). -/
theorem_wanted sum_choose_succ_mul_add (k n r : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (((r + 1) * i + n).choose i : ℤ) =
      ∑ α ∈ hockeyCompositions k r, hockeyCompositionSign α *
        ((α.map fun a => r.choose (a - 1)).prod *
          ((r + 1) * k + n + 1 - α.sum + α.length).choose (k - α.sum) : ℕ)

end MetaMathlibExt
