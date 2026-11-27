/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Cardinality of labeled tableaux

A tableau is specified by an independent choice of labels for each row.

## References

* Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of Integer
  Sequences 28 (2025), Article 25.7.7, §2.3 and Proposition 4 (p. 6).
* Richard P. Stanley, *Enumerative Combinatorics: Volume 1*, 2nd ed., Cambridge University Press,
  2011, §1.2, cited by Lynch and Weselcouch for background on compositions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The labeled tableaux `Λ(α, r)` of shape `α`: in each row `i` the entries after the empty first
box are strictly increasing labels in `{0, …, r - 1}`, recorded as the set of the `α_i - 1` labels
of the row.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.3 (labeled tableaux). -/
def labeledTableaux (α : List ℕ) (r : ℕ) : Finset (Fin α.length → Finset (Fin r)) :=
  Fintype.piFinset fun i => (Finset.univ : Finset (Fin r)).powersetCard (α.get i - 1)

/-- `|Λ(α, r)| = ∏_j C(r, α_j - 1)` (equal to `1` for `α = ∅`).

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Proposition 4 (`jis-2025-25.7.7-prop-4`). -/
theorem card_labeledTableaux (α : List ℕ) (r : ℕ) :
    (labeledTableaux α r).card = (α.map fun a => r.choose (a - 1)).prod := by
  rw [labeledTableaux, Fintype.card_piFinset]
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← Fin.prod_ofFn]
  exact congrArg List.prod (List.ofFn_getElem_eq_map α (fun a => r.choose (a - 1)))

end

end MetaMathlibExt
