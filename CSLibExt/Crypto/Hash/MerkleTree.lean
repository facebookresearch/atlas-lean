/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Function.Iterate

/-!
# Merkle trees: roots, authentication paths, and verification

Fix an abstract two-to-one hash `h : A → A → A`. A list of leaves is hashed level by level:
`level h` hashes adjacent pairs `[a, b, c, d, e] ↦ [h a b, h c d, e]`, and `root h l` repeats this
until one node remains. A tree with `n` leaves has height `Nat.clog 2 n` (`⌈log₂ n⌉`): after that
many levels at most one node is left (`length_iterate_level_clog_le_one`).

**Odd-leaf rule.** An unpaired last node is *promoted* to the next level unchanged (it is neither
duplicated nor hashed with itself). Bitcoin duplicates the last node, which makes `[a, b, c]` and
`[a, b, c, c]` share a root for every `a, b, c` and every hash; promotion avoids that unconditional
structural duplication. It does not rule out leaf lists of different lengths sharing a root in
general, even for an injective hash: leaves and internal nodes are not domain-separated (see
below), so a leaf can equal the internal node above other leaves. For example `Nat.pair 0 0 = 0`,
so `[1, 2, 0]` and `[1, 2, 0, 0]` have the same root under `Nat.pair` with no collision.

* `authPath h l i`: the authentication path of leaf `i`, the sibling at each level from the
  leaves upward; promoted levels contribute no sibling.
* `verify h n i x p r`: the verifier, given the number of leaves `n`, the position `i`, the
  claimed leaf `x`, a path `p`, and a root `r`, recomputes a root from `x` and `p` (using the bits
  of `i` and `n` to place each sibling) and compares it with `r` (`verify_eq_true_iff`). It runs
  for `Nat.clog 2 n` rounds, so its work is logarithmic in `n`, and paths have at most that many
  entries (`length_authPath_le`; exactly that many when `n` is a power of two,
  `length_authPath_of_length_eq_two_pow`).
* `verify_authPath` (**completeness**): the honest path of a leaf verifies against the root.
* `verify_sound` (**existential soundness**): if a path for `x` at position `i` verifies against the
  root of `l`, then `l[i] = x`, or `h` has some collision (`HasCollision h`). This compatibility
  theorem does not identify which collision caused the forgery. The computational strengthening
  `verify_sound_findCollision` in `MerkleTree.Collision` returns a concrete collision found by
  comparing the forged and actual leaf-to-root paths.
* `verify_sound_of_injective`: for an injective `h` the collision branch is impossible, so a
  verifying path proves that leaf `i` is `x`.

The compatibility theorem `verify_sound` records only existential correctness. The separate
`MerkleTree.Collision` module gives the computational version: `findCollision` walks the forged and
actual paths, and `verify_sound_findCollision` proves that a forgery makes it return unequal hash
inputs with equal outputs.

The root does not by itself commit to the number of leaves (there is no domain separation between
leaves and internal nodes, as in the `[1, 2, 0]` example above), so the verifier takes `n` as an
input, as in Katz and Lindell's construction for a fixed number of leaves. Soundness is relative
to that `n`: it speaks about the leaves of an `l` with `l.length = n`, not about every leaf list
with the same root.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.6.2 (Merkle trees). The textbook fixes the number of leaves to a power of two; here
  the number of leaves is arbitrary, with the promotion rule above.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleTree

variable {A : Type*} (h : A → A → A)

/-! ### Levels and the root -/

/-- One level up the tree: hash adjacent pairs, promoting an unpaired last node unchanged. -/
def level : List A → List A
  | a :: b :: rest => h a b :: level rest
  | [a] => [a]
  | [] => []

/-- A level has half as many nodes as the one below it, rounded up. -/
theorem length_level : ∀ l : List A, (level h l).length = (l.length + 1) / 2
  | _ :: _ :: rest => by
    simp only [level, List.length_cons, length_level rest]
    omega
  | [_] => by simp [level]
  | [] => by simp [level]

/-- Node `j` of the next level is the hash of nodes `2j` and `2j + 1` when both exist. -/
theorem getElem?_level_pair : ∀ {l : List A} {j : ℕ} {a b : A},
    l[2 * j]? = some a → l[2 * j + 1]? = some b → (level h l)[j]? = some (h a b)
  | _ :: _ :: _, 0, _, _, ha, hb => by simp_all [level]
  | _ :: _ :: rest, j + 1, _, _, ha, hb => by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega] at ha
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by omega] at hb
    simp only [List.getElem?_cons_succ] at ha hb
    simp only [level, List.getElem?_cons_succ]
    exact getElem?_level_pair ha hb
  | [_], _, _, _, _, hb => by simp at hb
  | [], _, _, _, ha, _ => by simp at ha

/-- When node `2j + 1` does not exist, node `j` of the next level is node `2j` (promoted, or
absent). -/
theorem getElem?_level_last : ∀ {l : List A} {j : ℕ},
    l.length ≤ 2 * j + 1 → (level h l)[j]? = l[2 * j]?
  | _ :: _ :: _, 0, hl => by simp at hl
  | _ :: _ :: rest, j + 1, hl => by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    simp only [level, List.getElem?_cons_succ]
    exact getElem?_level_last (by simp at hl; omega)
  | [_], j, _ => by
    simp only [level, List.getElem?_singleton]
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj, show ¬ 2 * j = 0 by omega]
  | [], _, _ => by simp [level]

/-- After `k` levels a list of at most `2 ^ k` nodes has at most one node left. -/
theorem length_iterate_level_le_one : ∀ (k : ℕ) {l : List A}, l.length ≤ 2 ^ k →
    ((level h)^[k] l).length ≤ 1
  | 0, _, hl => by simpa using hl
  | k + 1, l, hl => by
    rw [Function.iterate_succ_apply]
    apply length_iterate_level_le_one k
    rw [length_level]
    rw [Nat.pow_succ] at hl
    omega

/-- A tree with `n` leaves has height `Nat.clog 2 n`: after that many levels at most one node is
left. -/
theorem length_iterate_level_clog_le_one (l : List A) :
    ((level h)^[Nat.clog 2 l.length] l).length ≤ 1 :=
  length_iterate_level_le_one h _ (Nat.le_pow_clog (by decide) _)

/-- The Merkle root: iterate `level` for the height `Nat.clog 2 l.length` of the tree (after which
at most one node is left, `length_iterate_level_clog_le_one`) and take the remaining node; `none`
for an empty list of leaves. -/
def root (l : List A) : Option A := ((level h)^[Nat.clog 2 l.length] l).head?

/-! ### Authentication paths and verification -/

/-- The siblings met on the way up from position `i`, for `k` levels. At each level the sibling of
an even position `i` is `i + 1` and that of an odd position is `i - 1`; a promoted node has no
sibling and contributes nothing. -/
def authPathAux : ℕ → List A → ℕ → List A
  | 0, _, _ => []
  | k + 1, l, i =>
    (if i % 2 = 0 then l[i + 1]? else l[i - 1]?).toList ++ authPathAux k (level h l) (i / 2)

/-- The **authentication path** (inclusion proof) of leaf `i` of `l`, one level per unit of the
height `Nat.clog 2 l.length`. -/
def authPath (l : List A) (i : ℕ) : List A := authPathAux h (Nat.clog 2 l.length) l i

/-- Each level contributes at most one sibling. -/
theorem length_authPathAux_le : ∀ (k : ℕ) (l : List A) (i : ℕ), (authPathAux h k l i).length ≤ k
  | 0, _, _ => by simp [authPathAux]
  | k + 1, l, i => by
    have hk := length_authPathAux_le k (level h l) (i / 2)
    have hs : ∀ o : Option A, o.toList.length ≤ 1 := by intro o; cases o <;> simp
    have := hs (if i % 2 = 0 then l[i + 1]? else l[i - 1]?)
    simp only [authPathAux, List.length_append]
    omega

/-- **Logarithmic path length**: the authentication path of any leaf of an `n`-leaf tree has at
most `⌈log₂ n⌉` entries. -/
theorem length_authPath_le (l : List A) (i : ℕ) :
    (authPath h l i).length ≤ Nat.clog 2 l.length :=
  length_authPathAux_le h _ l i

/-- In a full tree of `2 ^ k` nodes every level has a sibling, so the path has exactly `k`
entries. -/
theorem length_authPathAux_of_length_eq_two_pow : ∀ (k : ℕ) {l : List A} {i : ℕ},
    l.length = 2 ^ k → i < 2 ^ k → (authPathAux h k l i).length = k
  | 0, _, _, _, _ => by simp [authPathAux]
  | k + 1, l, i, hl, hi => by
    rw [Nat.pow_succ] at hl hi
    have hlev : (level h l).length = 2 ^ k := by rw [length_level]; omega
    have hk := length_authPathAux_of_length_eq_two_pow k hlev (i := i / 2) (by omega)
    have hs : (if i % 2 = 0 then l[i + 1]? else l[i - 1]?).toList.length = 1 := by
      split
      · rw [List.getElem?_eq_getElem (by omega)]; rfl
      · rw [List.getElem?_eq_getElem (by omega)]; rfl
    simp only [authPathAux, List.length_append]
    omega

/-- **Exact path length for a balanced tree** (Katz and Lindell, Section 5.6.2, where the number
of leaves is a power of two): with `2 ^ k` leaves every path has exactly `k = log₂ (2 ^ k)`
entries. -/
theorem length_authPath_of_length_eq_two_pow {l : List A} {i k : ℕ} (hl : l.length = 2 ^ k)
    (hi : i < 2 ^ k) : (authPath h l i).length = k := by
  rw [authPath, hl, Nat.clog_pow 2 k (by decide)]
  exact length_authPathAux_of_length_eq_two_pow h k hl hi

/-- Recompute a root from the current node `cur` at position `i` of a level with `n` nodes and the
remaining path `p`, for `k` levels. An odd position hashes the next path entry on the left; an
even position with a right neighbour hashes it on the right; an even last position is promoted
and consumes nothing. The path must be used up exactly. -/
def recompute : ℕ → ℕ → ℕ → A → List A → Option A
  | 0, _, _, cur, [] => some cur
  | 0, _, _, _, _ :: _ => none
  | k + 1, n, i, cur, p =>
    if i % 2 = 1 then
      match p with
      | s :: p => recompute k ((n + 1) / 2) (i / 2) (h s cur) p
      | [] => none
    else if i + 1 < n then
      match p with
      | s :: p => recompute k ((n + 1) / 2) (i / 2) (h cur s) p
      | [] => none
    else recompute k ((n + 1) / 2) (i / 2) cur p

/-- The **Merkle verifier**: accept the claim "leaf `i` of an `n`-leaf tree with root `r` is `x`"
with path `p` when `i < n` and recomputing from `x` and `p` for the height `Nat.clog 2 n` of the
tree gives `r`. `recompute` recurses once per level, so verification takes `⌈log₂ n⌉` rounds,
whatever the path. -/
def verify [DecidableEq A] (n i : ℕ) (x : A) (p : List A) (r : A) : Bool :=
  decide (i < n ∧ recompute h (Nat.clog 2 n) n i x p = some r)

/-- The verifier accepts exactly when it recomputes the claimed root from the leaf and path. -/
theorem verify_eq_true_iff [DecidableEq A] {n i : ℕ} {x : A} {p : List A} {r : A} :
    verify h n i x p r = true ↔ i < n ∧ recompute h (Nat.clog 2 n) n i x p = some r := by
  simp [verify]

/-- `h` has a collision: two distinct input pairs with the same hash. -/
def HasCollision : Prop := ∃ a b c d : A, (a, b) ≠ (c, d) ∧ h a b = h c d

/-- A hash with injective uncurrying has no collision. -/
theorem not_hasCollision_of_injective (hinj : Function.Injective (Function.uncurry h)) :
    ¬ HasCollision h := by
  rintro ⟨a, b, c, d, hne, heq⟩
  exact hne (hinj heq)

private theorem div_two_pow_succ (i k : ℕ) : i / 2 ^ (k + 1) = i / 2 / 2 ^ k := by
  rw [Nat.pow_succ', Nat.div_div_eq_div_mul]

/-- Inductive form of completeness: following the honest path for `k` levels recomputes node
`i / 2 ^ k` of the `k`-th level. -/
theorem recompute_authPathAux : ∀ (k : ℕ) {l : List A} {i : ℕ} {x : A}, l[i]? = some x →
    recompute h k l.length i x (authPathAux h k l i) = ((level h)^[k] l)[i / 2 ^ k]?
  | 0, _, _, _, hx => by simp [authPathAux, recompute, hx]
  | k + 1, l, i, x, hx => by
    have hi : i < l.length := (List.getElem?_eq_some_iff.1 hx).1
    rw [Function.iterate_succ_apply, div_two_pow_succ]
    simp only [authPathAux, recompute]
    rw [← length_level h l]
    by_cases hodd : i % 2 = 1
    · have hprev : l[i - 1]? = some l[i - 1] := List.getElem?_eq_getElem (by omega)
      have hlev := getElem?_level_pair h (j := i / 2)
        (by rw [show 2 * (i / 2) = i - 1 by omega]; exact hprev)
        (by rw [show 2 * (i / 2) + 1 = i by omega]; exact hx)
      simp only [↓reduceIte, hprev, hodd]
      exact recompute_authPathAux k hlev
    · by_cases hnext : i + 1 < l.length
      · have hn : l[i + 1]? = some l[i + 1] := List.getElem?_eq_getElem hnext
        have hlev := getElem?_level_pair h (j := i / 2)
          (by rw [show 2 * (i / 2) = i by omega]; exact hx)
          (by rw [show 2 * (i / 2) + 1 = i + 1 by omega]; exact hn)
        simp only [show i % 2 = 0 by omega, ↓reduceIte, hnext, hn, Option.toList_some]
        exact recompute_authPathAux k hlev
      · have hn : l[i + 1]? = none := List.getElem?_eq_none (by omega)
        have hlev : (level h l)[i / 2]? = some x := by
          rw [getElem?_level_last h (by omega), show 2 * (i / 2) = i by omega, hx]
        simp only [show i % 2 = 0 by omega, ↓reduceIte, hnext, hn, Option.toList_none,
          List.nil_append]
        exact recompute_authPathAux k hlev

/-- After `k = Nat.clog 2 l.length` levels the root sits at position `i / 2 ^ k = 0`. -/
private theorem root_eq_getElem? {l : List A} {i : ℕ} (hi : i < l.length) :
    root h l = ((level h)^[Nat.clog 2 l.length] l)[i / 2 ^ Nat.clog 2 l.length]? := by
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_pow_clog (by decide) _)), root,
    List.head?_eq_getElem?]

/-- **Completeness** of Merkle inclusion proofs: the authentication path of leaf `i` verifies
against the root. -/
theorem verify_authPath [DecidableEq A] {l : List A} {i : ℕ} {x r : A} (hx : l[i]? = some x)
    (hr : root h l = some r) : verify h l.length i x (authPath h l i) r = true := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 hx).1
  rw [verify_eq_true_iff, authPath, recompute_authPathAux h _ hx, ← root_eq_getElem? h hi]
  exact ⟨hi, hr⟩

/-- Inductive form of soundness: if recomputing for `k` levels from `x` at position `i` gives node
`i / 2 ^ k` of the `k`-th level, then leaf `i` is `x` or `h` has a collision. -/
theorem recompute_sound : ∀ (k : ℕ) {l : List A} {i : ℕ} {x r : A} {p : List A},
    i < l.length → recompute h k l.length i x p = some r →
    ((level h)^[k] l)[i / 2 ^ k]? = some r → l[i]? = some x ∨ HasCollision h
  | 0, l, i, x, r, p, _, hrec, hroot => by
    rcases p with _ | ⟨_, _⟩
    · simp only [recompute, Option.some.injEq] at hrec
      subst hrec
      exact Or.inl (by simpa using hroot)
    · simp [recompute] at hrec
  | k + 1, l, i, x, r, p, hi, hrec, hroot => by
    have hi' : i / 2 < (level h l).length := by rw [length_level]; omega
    have hcur : l[i]? = some l[i] := List.getElem?_eq_getElem hi
    rw [Function.iterate_succ_apply, div_two_pow_succ] at hroot
    simp only [recompute] at hrec
    rw [← length_level h l] at hrec
    by_cases hodd : i % 2 = 1
    · have hprev : l[i - 1]? = some l[i - 1] := List.getElem?_eq_getElem (by omega)
      have hlev := getElem?_level_pair h (j := i / 2)
        (by rw [show 2 * (i / 2) = i - 1 by omega]; exact hprev)
        (by rw [show 2 * (i / 2) + 1 = i by omega]; exact hcur)
      simp only [hodd, ↓reduceIte] at hrec
      rcases p with _ | ⟨s, p⟩
      · simp at hrec
      · rcases recompute_sound k hi' hrec hroot with hl | hc
        · rw [hlev, Option.some.injEq] at hl
          by_cases heq : (l[i - 1], l[i]) = (s, x)
          · exact Or.inl (by rw [hcur, (Prod.mk.inj heq).2])
          · exact Or.inr ⟨_, _, _, _, heq, hl⟩
        · exact Or.inr hc
    · simp only [hodd, ↓reduceIte] at hrec
      by_cases hnext : i + 1 < l.length
      · have hn : l[i + 1]? = some l[i + 1] := List.getElem?_eq_getElem hnext
        have hlev := getElem?_level_pair h (j := i / 2)
          (by rw [show 2 * (i / 2) = i by omega]; exact hcur)
          (by rw [show 2 * (i / 2) + 1 = i + 1 by omega]; exact hn)
        simp only [hnext, ↓reduceIte] at hrec
        rcases p with _ | ⟨s, p⟩
        · simp at hrec
        · rcases recompute_sound k hi' hrec hroot with hl | hc
          · rw [hlev, Option.some.injEq] at hl
            by_cases heq : (l[i], l[i + 1]) = (x, s)
            · exact Or.inl (by rw [hcur, (Prod.mk.inj heq).1])
            · exact Or.inr ⟨_, _, _, _, heq, hl⟩
          · exact Or.inr hc
      · simp only [hnext, ↓reduceIte] at hrec
        rcases recompute_sound k hi' hrec hroot with hl | hc
        · rw [getElem?_level_last h (by omega), show 2 * (i / 2) = i by omega] at hl
          exact Or.inl hl
        · exact Or.inr hc

/-- **Existential soundness** of Merkle inclusion proofs: if a path for `x` at position `i` verifies
against the root of `l`, then leaf `i` of `l` is `x`, or `h` has some collision.

This theorem is retained for compatibility and does not tie the existential collision to the given
proof. For the computational strengthening that extracts a collision from the forged and actual
paths, use `verify_sound_findCollision` from `MerkleTree.Collision`. -/
theorem verify_sound [DecidableEq A] {l : List A} {i : ℕ} {x r : A} {p : List A}
    (hr : root h l = some r) (hv : verify h l.length i x p r = true) :
    l[i]? = some x ∨ HasCollision h := by
  obtain ⟨hi, hrec⟩ := (verify_eq_true_iff h).1 hv
  exact recompute_sound h _ hi hrec (by rw [← root_eq_getElem? h hi, hr])

/-- **Soundness for an injective hash**: a verifying inclusion proof for `x` at position `i`
implies that leaf `i` is `x`. -/
theorem verify_sound_of_injective [DecidableEq A]
    (hinj : Function.Injective (Function.uncurry h)) {l : List A} {i : ℕ} {x r : A}
    {p : List A} (hr : root h l = some r) (hv : verify h l.length i x p r = true) :
    l[i]? = some x :=
  (verify_sound h hr hv).resolve_right (not_hasCollision_of_injective h hinj)

end Cslib.Crypto.MerkleTree
