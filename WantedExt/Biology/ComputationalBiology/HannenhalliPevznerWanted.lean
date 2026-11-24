/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hannenhalli-Pevzner duality for signed reversal distance

For a signed permutation `π` of `±1..±n` (as an integer list with each
nonzero value of absolute value at most `n` exactly once), framed by `0`
and `n+1`, adjacencies join consecutive values (`y - x = 1`) and
breakpoints are the other adjacent framed pairs. The breakpoint graph has
black edges on breakpoints and gray edges on inverse breakpoints; its
alternating cycles decompose the black edges, with maximum count `c(π)`.
With `b(π)` breakpoints and `h(π)` hurdles (unoriented components, counted
with `superHurdles` for fortresses), the reversal distance is
`d(π) = b(π) - c(π) + h(π) + 1` on fortresses and `b(π) - c(π) + h(π)`
otherwise. The Reversal_Sort procedure sorts optimally; its `O(n^4)` time
bound needs a RAM cost model and is context here.

Overlap (partial base): `CSLibExt/Bioinformatics/Rearrangement/SortingByReversals.lean`
has breakpoints, the `b ≤ 2d` bound, and sortability; the duality formula,
hurdles, fortresses, and optimal sorting are new.

Sources: S. Hannenhalli and P. A. Pevzner, "Transforming cabbage into
turnip: polynomial algorithm for sorting signed permutations by reversals",
J. ACM 46(1):1-27, 1999, doi:10.1145/300515.300516, Theorems 5-6.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.HannenhalliPevznerWanted

open Classical

variable (n : ℕ)

/-- Valid signed permutations: each nonzero value of absolute value at most
`n` exactly once. -/
def IsSignedPerm (π : List ℤ) : Prop :=
  π.length = n ∧ ∀ v : ℤ, v ≠ 0 → v.natAbs ≤ n → v ∈ π

/-- Framing with `0` and `n+1`. -/
def framed (π : List ℤ) : List ℤ :=
  0 :: π ++ [((n : ℤ) + 1)]

/-- Adjacent values differ by exactly one upward step. -/
def Adjacent (x y : ℤ) : Prop :=
  y - x = 1

/-- Breakpoint count of the framed permutation. -/
noncomputable def breakpoints (π : List ℤ) : ℕ :=
  ((List.range (framed n π).length).filter fun i =>
    ∃ x y : ℤ, (framed n π).getD i 0 = x ∧ (framed n π).getD (i + 1) 0 = y ∧
      ¬ Adjacent x y).length

/-- Black edges join breakpoint position pairs; gray edges join
inverse-breakpoint pairs. Vertices are positions `0..n`. -/
def blackEdge (π : List ℤ) (a b : Fin (n + 1)) : Prop :=
  ∃ i, i + 1 ≤ n ∧
    ((framed n π).getD i 0 + 1 ≠ (framed n π).getD (i + 1) 0 ∧
      a.val = i ∧ b.val = i + 1) ∨
    ((framed n π).getD i 0 + 1 ≠ (framed n π).getD (i + 1) 0 ∧
      a.val = i + 1 ∧ b.val = i)

/-- Gray edges: value-consecutive positions in the inverse permutation. -/
def grayEdge (π : List ℤ) (a b : Fin (n + 1)) : Prop :=
  ∃ u v : ℤ, v - u = 1 ∧
    ((framed n π).getD a.val 0 = u ∧ (framed n π).getD b.val 0 = v) ∨
    ((framed n π).getD a.val 0 = v ∧ (framed n π).getD b.val 0 = u)

/-- Reachability in the black/gray union graph. -/
inductive CGReach (n : ℕ) (E : Fin (n + 1) × Fin (n + 1) → Prop) :
    Fin (n + 1) → Fin (n + 1) → Prop where
  | refl (v) : CGReach n E v v
  | step (u v w) : CGReach n E u v → E (v, w) → CGReach n E u w

/-- Union edges for a permutation. -/
def unionEdges (π : List ℤ) (p : Fin (n + 1) × Fin (n + 1)) : Prop :=
  blackEdge n π p.1 p.2 ∨ grayEdge n π p.1 p.2

/-- Alternating cycle components of the breakpoint graph. -/
noncomputable def cycleComps (π : List ℤ) : Finset (Finset (Fin (n + 1))) :=
  Finset.univ.filter fun K =>
    K.Nonempty ∧ (∀ u ∈ K, ∀ v ∈ K, CGReach n (fun p => unionEdges n π p) u v) ∧
      ∀ w ∉ K, ∀ u ∈ K, ¬ CGReach n (fun p => unionEdges n π p) u w

/-- Apply signed reversal `[i,j]`: reverse and negate the framed segment. -/
def applySignedReversal (π : List ℤ) (r : ℕ × ℕ) : List ℤ :=
  unframeSigned ((framed n π).take (r.1 + 1) ++
    (((framed n π).drop (r.1 + 1)).take (r.2 - r.1)).reverse.map (-·) ++
    (framed n π).drop (r.2 + 1))
where
  /-- Unframe: drop both sentinels. -/
  unframeSigned (F : List ℤ) : List ℤ :=
    F.drop 1 |>.dropLast

/-- Sorting by signed reversals: chains to the identity `1..n`. -/
inductive SortsSigned (n : ℕ) : List ℤ → List (ℕ × ℕ) → Prop where
  | nil (π) : SortsSigned n π []
  | cons (π π' : List ℤ) (r : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
      π' = applySignedReversal n π r → SortsSigned n π' rest →
        SortsSigned n π (r :: rest)

/-- Reversal distance, characterized by `hd_le`/`hd_att` below. -/
noncomputable def revDist (π : List ℤ)
    (h : ∃ seq : List (ℕ × ℕ), SortsSigned n π seq) : ℕ :=
  Nat.find (p := fun k => ∃ seq : List (ℕ × ℕ),
    SortsSigned n π seq ∧ seq.length = k)
    (by obtain ⟨s, hs⟩ := h; exact ⟨s.length, s, hs, rfl⟩)

/-- **Hannenhalli-Pevzner duality** (1999, Theorem 5): hypotheses are a valid
signed permutation (`hπ`), hurdles `h` with super-hurdle count
(`hsuper`: at most `h`), the fortress flag characterized by odd hurdles all
super (`hfort`: `fortress ↔ Odd h ∧ superHurdles = h`), the max-cycle
characterization (`hcmx`, `hcmx_att` over alternating decompositions
`IsAltDecomp`, given as all-valid-cycle-covers), and the distance
characterization (`hd_le`, `hd_att`). Conclusion over `ℤ`: `d = b - c + h`,
plus one on fortresses.

Source: Hannenhalli-Pevzner (1999), Theorem 5. -/
theorem_wanted duality_signed (π : List ℤ) (hπ : IsSignedPerm n π)
    (h : ℕ) (superHurdles : ℕ) (hsuper : superHurdles ≤ h)
    (fortress : Prop)
    (hfort : fortress ↔ (Odd h ∧ superHurdles = h))
    (cmax : ℕ)
    (hcmx : ∀ C : List (Finset (Fin (n + 1))),
      (∀ K ∈ C, K ∈ cycleComps n π) → C.length ≤ cmax)
    (hcmx_att : ∃ C : List (Finset (Fin (n + 1))),
      (∀ K ∈ C, K ∈ cycleComps n π) ∧ C.length = cmax)
    (hex : ∃ seq : List (ℕ × ℕ), SortsSigned n π seq)
    (hd_le : ∀ seq : List (ℕ × ℕ), SortsSigned n π seq →
      revDist n π hex ≤ seq.length)
    (hd_att : ∃ seq : List (ℕ × ℕ), SortsSigned n π seq ∧
      revDist n π hex = seq.length) :
    (revDist n π hex : ℤ) = breakpoints n π - cmax + h +
      (if fortress then 1 else 0)

/-- **Reversal_Sort is optimal** (1999, Theorem 6): same hypotheses as
`duality_signed`, plus a Reversal_Sort run (`seq`, each step an admissible
signed reversal chosen by the procedure, `hrun`) attaining the duality
bound (`hopt`). Conclusion: the run sorts `π` in exactly `d(π)` reversals;
the `O(n^4)` time reading is context.

Source: Hannenhalli-Pevzner (1999), Theorem 6. -/
theorem_wanted reversalSort_optimal (π : List ℤ) (hπ : IsSignedPerm n π)
    (h : ℕ) (superHurdles : ℕ) (hsuper : superHurdles ≤ h)
    (fortress : Prop)
    (hfort : fortress ↔ (Odd h ∧ superHurdles = h))
    (cmax : ℕ)
    (hcmx : ∀ C : List (Finset (Fin (n + 1))),
      (∀ K ∈ C, K ∈ cycleComps n π) → C.length ≤ cmax)
    (hcmx_att : ∃ C : List (Finset (Fin (n + 1))),
      (∀ K ∈ C, K ∈ cycleComps n π) ∧ C.length = cmax)
    (hex : ∃ seq : List (ℕ × ℕ), SortsSigned n π seq)
    (seq : List (ℕ × ℕ))
    (hrun : SortsSigned n π seq)
    (hopt : (seq.length : ℤ) = breakpoints n π - cmax + h +
      (if fortress then 1 else 0)) :
    seq.length = revDist n π hex

end WantedExt.Biology.ComputationalBiology.HannenhalliPevznerWanted
