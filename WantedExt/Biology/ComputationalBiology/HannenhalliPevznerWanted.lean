/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hannenhalli–Pevzner duality theorem for signed reversal distance

A signed permutation `π = (π_1, …, π_n)` contains each of `1, …, n` exactly once, each with a
sign. A reversal `ρ(i, j)` reverses the block `π_i … π_j` and changes the sign of each of its
elements; the reversal distance `d(π)` is the least number of reversals that turn `π` into the
identity `(+1, …, +n)`. Frame `π` by `π_0 = 0` and `π_{n+1} = n + 1`; a breakpoint is a position
`0 ≤ t ≤ n` with `π_{t+1} - π_t ≠ 1`, and `b(π)` is their number.

The unsigned image of `π` replaces `+x` by `2x - 1, 2x` and `-x` by `2x, 2x - 1`, between the
framing values `0` and `2n + 1`; it is a sequence `u_0, …, u_{2n+1}`. The breakpoint graph has a
black edge between the positions `2t` and `2t + 1` and a gray edge between the positions of the
values `2t` and `2t + 1`, for `0 ≤ t ≤ n`; it decomposes uniquely into alternating cycles. A
cycle with one black edge is an adjacency; `c(π)` counts the other cycles.

The gray edge `t` spans the interval between the positions of `2t` and `2t + 1`. It is trivial if
these positions are `2s, 2s + 1` (it is part of an adjacency), and oriented if the two positions
have the same parity (equivalently, the elements `t` and `t + 1` of `π` have opposite signs).
Two nontrivial gray edges overlap if their intervals intersect without either containing the
other; the components of the overlap graph are the components of `π`, and a component is
unoriented if none of its gray edges is oriented. Place the positions `0, …, 2n + 1` on a circle.
An unoriented component `U` separates two components if the points of `U` lie on both arcs
between them. A hurdle is an unoriented component that separates no two other unoriented
components; a superhurdle is a hurdle whose removal turns an unoriented component that is not a
hurdle into a hurdle; `h(π)` is the number of hurdles, and `π` is a fortress if it has an odd
number of hurdles, all of them superhurdles.

**Theorem 5** (Hannenhalli–Pevzner 1999). `d(π) = b(π) - c(π) + h(π) + 1` if `π` is a fortress,
and `d(π) = b(π) - c(π) + h(π)` otherwise.

Signed permutations, signed reversals, the breakpoint count `b(π)`, the unsigned image and the
reversal distance are the canonical `SValid`, `srevBlock`, `sbreaks`, `dbl` and `sdist` of
`CSLibExt.Bioinformatics.Rearrangement.SortingByReversals` (lists over `ℤ`, zero-based positions),
where `sbreaks_eq_ubreaks_dbl_of_valid` relates `b(π)` to the breakpoints of the unsigned image.
Theorem 6 (the algorithm Reversal_Sort sorts optimally in `O(n^4)` time) is not stated.

Sources: S. Hannenhalli and P. A. Pevzner, "Transforming cabbage into turnip: polynomial
algorithm for sorting signed permutations by reversals", J. ACM 46(1):1-27, 1999,
doi:10.1145/300515.300516, Theorem 5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Rearrangement.SortingByReversals
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Relation

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.HannenhalliPevznerWanted

open Cslib.Bioinformatics.Rearrangement.SortingByReversals

/-- The unsigned image `[0, u_1, …, u_{2n}, 2n + 1]` as natural numbers: the doubling `dbl π`
(`+x` becomes `2x - 1, 2x` and `-x` becomes `2x, 2x - 1`) framed by `0` and `2n + 1`. -/
def image (n : ℕ) (π : List ℤ) : List ℕ :=
  (0 :: dbl π ++ [((2 * n + 1 : ℕ) : ℤ)]).map Int.toNat

/-- The position of the value `v` in the unsigned image. -/
def pos (n : ℕ) (π : List ℤ) (v : ℕ) : ℕ :=
  (image n π).idxOf v

/-- One step along the alternating cycles: from position `x`, cross the black edge to the
position `x xor 1`, then the gray edge from its value `u` to the value `u xor 1`, and return the
position of that value. -/
def cycleStep (n : ℕ) (π : List ℤ) (x : ℕ) : ℕ :=
  pos n π ((image n π).getD (x ^^^ 1) 0 ^^^ 1)

open Classical in
/-- The positions in the orbit of `x` under `cycleStep`: one endpoint of each black edge of the
alternating cycle through `x`, traversed in one direction. -/
noncomputable def orbit (n : ℕ) (π : List ℤ) (x : ℕ) : Finset ℕ :=
  (Finset.range (2 * n + 2)).filter fun y => ∃ k, (cycleStep n π)^[k] x = y

open Classical in
/-- The number `c(π)` of alternating cycles that are not adjacencies. Each such cycle with `L ≥ 2`
black edges gives two orbits of `cycleStep` with `L` positions (one per direction), so `c(π)` is
half the number of orbits with at least two positions, each orbit counted at its least
position. -/
noncomputable def cycles (n : ℕ) (π : List ℤ) : ℕ :=
  ((Finset.range (2 * n + 2)).filter fun x =>
    (∀ y ∈ orbit n π x, x ≤ y) ∧ 2 ≤ (orbit n π x).card).card / 2

/-- The left end of the interval of gray edge `t`. -/
def left (n : ℕ) (π : List ℤ) (t : Fin (n + 1)) : ℕ :=
  min (pos n π (2 * t)) (pos n π (2 * t + 1))

/-- The right end of the interval of gray edge `t`. -/
def right (n : ℕ) (π : List ℤ) (t : Fin (n + 1)) : ℕ :=
  max (pos n π (2 * t)) (pos n π (2 * t + 1))

/-- Gray edge `t` is nontrivial: its endpoints are not the two ends `2s, 2s + 1` of a black
edge. -/
def IsNontrivial (n : ℕ) (π : List ℤ) (t : Fin (n + 1)) : Prop :=
  ¬ (right n π t = left n π t + 1 ∧ Even (left n π t))

/-- Gray edge `t` is oriented: its endpoints have positions of the same parity. -/
def IsOriented (n : ℕ) (π : List ℤ) (t : Fin (n + 1)) : Prop :=
  pos n π (2 * t) % 2 = pos n π (2 * t + 1) % 2

/-- Two nontrivial gray edges overlap: their intervals intersect and neither contains the
other. -/
def Overlap (n : ℕ) (π : List ℤ) (s t : Fin (n + 1)) : Prop :=
  IsNontrivial n π s ∧ IsNontrivial n π t ∧
    ((left n π s < left n π t ∧ left n π t < right n π s ∧ right n π s < right n π t) ∨
      (left n π t < left n π s ∧ left n π s < right n π t ∧ right n π t < right n π s))

open Classical in
/-- The component of gray edge `t`: the gray edges reachable from `t` in the overlap graph. -/
noncomputable def component (n : ℕ) (π : List ℤ) (t : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun s => Relation.ReflTransGen (Overlap n π) t s

open Classical in
/-- The unoriented components: components of nontrivial gray edges none of whose gray edges is
oriented. -/
noncomputable def unorientedComponents (n : ℕ) (π : List ℤ) : Finset (Finset (Fin (n + 1))) :=
  (Finset.univ.filter fun t => IsNontrivial n π t ∧
    ∀ s ∈ component n π t, ¬ IsOriented n π s).image (component n π)

/-- The positions of the endpoints of the gray edges of a component. -/
def points (n : ℕ) (π : List ℤ) (K : Finset (Fin (n + 1))) : Finset ℕ :=
  K.biUnion fun s => {left n π s, right n π s}

/-- On the circle of positions, `U` separates `V` from `W`: for some points `x` of `V` and `y`
of `W`, both arcs between `x` and `y` contain a point of `U`. -/
def Separates (n : ℕ) (π : List ℤ) (U V W : Finset (Fin (n + 1))) : Prop :=
  ∃ x ∈ points n π V, ∃ y ∈ points n π W,
    (∃ u ∈ points n π U, min x y < u ∧ u < max x y) ∧
      ∃ u ∈ points n π U, u < min x y ∨ max x y < u

/-- `U` is a hurdle among the unoriented components `𝒰`: `U ∈ 𝒰` and `U` separates no two other
components of `𝒰`. -/
def IsHurdle (n : ℕ) (π : List ℤ) (𝒰 : Finset (Finset (Fin (n + 1))))
    (U : Finset (Fin (n + 1))) : Prop :=
  U ∈ 𝒰 ∧ ¬ ∃ V ∈ 𝒰, ∃ W ∈ 𝒰, V ≠ U ∧ W ≠ U ∧ Separates n π U V W

open Classical in
/-- The number `h(π)` of hurdles. -/
noncomputable def hurdles (n : ℕ) (π : List ℤ) : ℕ :=
  ((unorientedComponents n π).filter (IsHurdle n π (unorientedComponents n π))).card

/-- `U` is a superhurdle: a hurdle such that, after removing `U`, some unoriented component that
was not a hurdle becomes a hurdle. -/
def IsSuperhurdle (n : ℕ) (π : List ℤ) (U : Finset (Fin (n + 1))) : Prop :=
  IsHurdle n π (unorientedComponents n π) U ∧
    ∃ V ∈ unorientedComponents n π, ¬ IsHurdle n π (unorientedComponents n π) V ∧
      IsHurdle n π ((unorientedComponents n π).erase U) V

/-- `π` is a fortress: it has an odd number of hurdles, and every hurdle is a superhurdle. -/
def IsFortress (n : ℕ) (π : List ℤ) : Prop :=
  Odd (hurdles n π) ∧
    ∀ U, IsHurdle n π (unorientedComponents n π) U → IsSuperhurdle n π U

open Classical in
/-- **Hannenhalli–Pevzner duality** (1999, Theorem 5). For every signed permutation `π` of
`1, …, n` (`SValid n π`), the reversal distance `sdist n π` equals `b(π) - c(π) + h(π) + 1` if `π`
is a fortress and `b(π) - c(π) + h(π)` otherwise, where `b(π) = sbreaks n π`.

Source: S. Hannenhalli and P. A. Pevzner, J. ACM 46 (1999) 1-27, Theorem 5.

Source: R. Shamir and I. Pe'er, *Algorithms for Molecular Biology*, lecture 11 scribe notes,
Tel Aviv University, 1998, Theorem 11.12,
<https://www.cs.tau.ac.il/~rshamir/algmb/98/scribe/html/lec11/node13.html>. -/
theorem_wanted sdist_eq (n : ℕ) {π : List ℤ} (hπ : SValid n π) :
    (sdist n π hπ : ℤ) = (sbreaks n π : ℤ) - cycles n π + hurdles n π +
      (if IsFortress n π then 1 else 0)

end WantedExt.Biology.ComputationalBiology.HannenhalliPevznerWanted
