/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.RNA.PartitionFunction

/-!
# Zuker's minimum free energy algorithm under a loop energy model (wanted)

In the nearest-neighbor (loop) energy model the free energy of an RNA secondary structure is
not a sum over base pairs but a sum over the **loops** of the structure (Tinoco et al. 1971;
Zuker and Stiegler 1981; Zuker and Sankoff 1984). The pairs of a structure `P` that are not
enclosed by any other pair are its exterior branches; for a pair `(i, j) ∈ P`, its branches
(`branches P (i, j)`) are the pairs of `P` strictly inside `(i, j)` that are not enclosed by
another pair strictly inside `(i, j)`. The loop closed by `(i, j)` is

* a **hairpin** if it has no branch,
* a **stack, bulge or interior loop** if it has exactly one branch `(k, l)` (a stack when
  `k = i + 1` and `l = j - 1`),
* a **multiloop** if it has at least two branches.

A `LoopEnergy` assigns an energy to each kind of loop: `hairpin i j`, `interior i j k l`
(stacks, bulges and interior loops alike), and the affine multiloop energy
`a + b · (number of branches) + c · (number of unpaired bases in the loop)`. The exterior loop
has energy `0` (dangling-end and terminal-mismatch terms are not modeled). The energy of a
structure is the sum of the energies of the loops closed by its pairs (`freeEnergy`).
Numerical parameters (the Turner rules of the Nearest Neighbor Database) are data, not
theorems.

`zukerVW` is the Zuker recursion for an interval `[i, i + len)`: the minimum energy `V` of a
structure on the interval closed by the pair `(i, i + len - 1)`, and the minimum energy `WM` of
a multiloop fragment with at least one branch; `zukerExterior` adds the exterior loop on a
prefix. Values live in `WithTop ℝ` (`⊤` when no structure is possible).

## Main statements (wanted)

* `existsUnique_closing_pair`: every pair of a structure is either an exterior branch or a
  branch of exactly one pair, so the loops of a structure (one per pair, plus the exterior
  loop) decompose it uniquely.
* `zukerMFE_eq_inf`: Zuker's recursion computes the minimum free energy over all secondary
  structures with minimum hairpin `m`.

## References

* M. Zuker and P. Stiegler, *Optimal computer folding of large RNA sequences using
  thermodynamics and auxiliary information*, Nucleic Acids Res. 9 (1981), 133–148.
* M. Zuker and D. Sankoff, *RNA secondary structures and their prediction*, Bull. Math. Biol.
  46 (1984), 591–621.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.RNA.Zuker

open Cslib.Bioinformatics.RNA.Nussinov Cslib.Bioinformatics.RNA.PartitionFunction

/-- A loop (nearest-neighbor) energy model: energies of hairpin loops closed by `(i, j)`, of
stacks, bulges and interior loops closed by `(i, j)` with inner pair `(k, l)`, and the affine
multiloop parameters `a` (per multiloop), `b` (per branch) and `c` (per unpaired base). The
exterior loop has energy `0`. Units: free energy, e.g. kcal/mol. -/
structure LoopEnergy where
  /-- Energy of the hairpin loop closed by the pair `(i, j)`. -/
  hairpin : ℕ → ℕ → ℝ
  /-- Energy of the stack, bulge or interior loop closed by `(i, j)` with inner pair `(k, l)`. -/
  interior : ℕ → ℕ → ℕ → ℕ → ℝ
  /-- Multiloop initiation energy `a`. -/
  multiA : ℝ
  /-- Multiloop energy per branch `b`. -/
  multiB : ℝ
  /-- Multiloop energy per unpaired base `c`. -/
  multiC : ℝ

/-- `q` lies strictly inside the pair `p`: `p.1 < q.1` and `q.2 < p.2`. -/
def Encloses (p q : ℕ × ℕ) : Prop :=
  p.1 < q.1 ∧ q.2 < p.2

/-- `Encloses` is decidable. -/
instance (p q : ℕ × ℕ) : Decidable (Encloses p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The branches of the loop closed by `p` in `P`: the pairs of `P` strictly inside `p` that
are not strictly inside another pair of `P` strictly inside `p`. -/
def branches (P : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  P.filter fun q => Encloses p q ∧ ∀ r ∈ P, Encloses p r → ¬ Encloses r q

/-- The exterior branches of `P`: the pairs not strictly inside any pair of `P`. -/
def exteriorBranches (P : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  P.filter fun q => ∀ r ∈ P, ¬ Encloses r q

/-- The energy of the loop closed by `p = (i, j)` in `P`: a hairpin with no branch, a stack,
bulge or interior loop with one branch `(k, l)`, and the affine multiloop energy
`a + b · r + c · u` with `r ≥ 2` branches and `u = (j - i - 1) - ∑ (l - k + 1)` unpaired
bases. -/
noncomputable def loopEnergy (E : LoopEnergy) (P : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : ℝ :=
  let br := branches P p
  if br.card = 0 then E.hairpin p.1 p.2
  else if h : br.card = 1 then
    let q := (Finset.card_eq_one.mp h).choose
    E.interior p.1 p.2 q.1 q.2
  else
    E.multiA + E.multiB * br.card +
      E.multiC * ((p.2 - p.1 - 1 - ∑ q ∈ br, (q.2 - q.1 + 1) : ℕ) : ℝ)

/-- The free energy of a structure in the loop model: the sum of the energies of the loops
closed by its pairs (the exterior loop contributes `0`). -/
noncomputable def freeEnergy (E : LoopEnergy) (P : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ P, loopEnergy E P p

variable {B : Type*} (pair : B → B → Prop) [DecidableRel pair] (m : ℕ) (s : List B)

/-- **Zuker's recursion** on the interval `[i, i + len)`, with `j = i + len - 1`, returning
`(V, WM)`:
* `V = ⊤` unless `(i, j)` can close a loop (`i + m < j`, `CanPair pair s i j`); otherwise `V` is
  the least of the hairpin energy `hairpin i j`, the interior-loop energies
  `interior i j k l + V(k, l)` over `i < k < l < j`, and the multiloop energies
  `a + WM(i + 1, u) + WM(u + 1, j - 1)` over `i < u < j - 1`;
* `WM` (a multiloop fragment with at least one branch, charging `b` per branch and `c` per
  unpaired base) is the least of `V + b`, `WM(i + 1, j) + c` (base `i` unpaired),
  `WM(i, j - 1) + c` (base `j` unpaired) and `WM(i, u) + WM(u + 1, j)` over `i ≤ u < j`.
Intervals are written by start and length. -/
noncomputable def zukerVW (E : LoopEnergy) : ℕ → ℕ → WithTop ℝ × WithTop ℝ
  | i, len =>
    let j := i + len - 1
    let V : WithTop ℝ :=
      if i + m < j ∧ CanPair pair s i j then
        min (E.hairpin i j : WithTop ℝ)
          (min
            (Finset.univ.inf fun a : Fin len => Finset.univ.inf fun b : Fin len =>
              if 1 ≤ a.val ∧ a.val + b.val < len ∧ 1 ≤ b.val then
                (E.interior i j (i + a.val) (i + a.val + b.val - 1) : WithTop ℝ) +
                  (zukerVW E (i + a.val) b.val).1
              else ⊤)
            (Finset.univ.inf fun a : Fin len =>
              if 1 ≤ a.val ∧ a.val + 2 < len then
                (E.multiA : WithTop ℝ) + (zukerVW E (i + 1) a.val).2 +
                  (zukerVW E (i + a.val + 1) (len - a.val - 2)).2
              else ⊤))
      else ⊤
    let WM : WithTop ℝ :=
      if len = 0 then ⊤
      else
        min (V + (E.multiB : WithTop ℝ))
          (min ((zukerVW E (i + 1) (len - 1)).2 + (E.multiC : WithTop ℝ))
            (min ((zukerVW E i (len - 1)).2 + (E.multiC : WithTop ℝ))
              (Finset.univ.inf fun a : Fin len =>
                if 1 ≤ a.val then (zukerVW E i a.val).2 + (zukerVW E (i + a.val) (len - a.val)).2
                else ⊤)))
    (V, WM)
  termination_by _ len => len
  decreasing_by all_goals omega

/-- The exterior-loop recursion on the prefix `[0, len)`: `W(0) = 0` and
`W(len + 1) = min (W(len), min_{i ≤ len} W(i) + V(i, len + 1 - i))` (the last base is unpaired,
or closes an exterior branch `(i, len)`). -/
noncomputable def zukerExterior (E : LoopEnergy) : ℕ → WithTop ℝ
  | 0 => 0
  | len + 1 =>
    min (zukerExterior E len)
      (Finset.univ.inf fun i : Fin (len + 1) =>
        zukerExterior E i.val + (zukerVW pair m s E i.val (len + 1 - i.val)).1)
  termination_by len => len
  decreasing_by all_goals omega

/-- Zuker's minimum free energy of `s`: the exterior recursion on the whole sequence. -/
noncomputable def zukerMFE (E : LoopEnergy) : WithTop ℝ :=
  zukerExterior pair m s E s.length

/-- **Unique loop decomposition**: in a secondary structure every pair is either an exterior
branch or a branch of exactly one pair of the structure (and not both), so the loops (one per
pair, plus the exterior loop) partition the structure. -/
theorem_wanted existsUnique_closing_pair (P : Finset (ℕ × ℕ)) (hP : IsStructure pair m s P)
    (q : ℕ × ℕ) (hq : q ∈ P) :
    (q ∈ exteriorBranches P ∧ ∀ p ∈ P, q ∉ branches P p) ∨
      (q ∉ exteriorBranches P ∧ ∃! p, p ∈ P ∧ q ∈ branches P p)

/-- **Zuker's algorithm** (Zuker and Stiegler 1981; Zuker and Sankoff 1984): with the affine
multiloop energy, the Zuker recursion computes the minimum free energy over all secondary
structures on `s` with minimum hairpin `m`, for any real loop energies. -/
theorem_wanted zukerMFE_eq_inf (E : LoopEnergy) :
    zukerMFE pair m s E =
      (structures pair m s).inf fun P => ((freeEnergy E P : ℝ) : WithTop ℝ)

end Cslib.Bioinformatics.RNA.Zuker
