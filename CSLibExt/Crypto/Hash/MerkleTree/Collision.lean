/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.MerkleTree
public import CSLibExt.Crypto.Hash.MerkleDamgard

/-!
# Computational collision extraction for Merkle inclusion proofs

`findCollision h l i x p` compares the forged computation from `x` and `p` with the
computation from the actual leaf `l[i]` and its authentication path. It walks both leaf-to-root
paths in lockstep and returns the first unequal pair of hash inputs that produce equal outputs.

`verify_sound_findCollision` ties verification to this computation: a claim that verifies against
the root of `l` either names the actual leaf or makes `findCollision` return a concrete collision
found on those two paths. `IsCollision` is only an abbreviation of the existing
Merkle–Damgård compression-collision predicate, using the uncurried hash; its decision instance
is reused as well.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleTree

variable {A : Type*} (h : A → A → A)

/-- Compatibility name for the existing compression-collision predicate, specialized to `h`. -/
abbrev IsCollision (c : (A × A) × (A × A)) : Prop :=
  MerkleDamgard.IsCollision (Function.uncurry h) c

/-- Internal lockstep traversal used by `findCollision`. -/
def findCollisionAux [DecidableEq A] :
    ℕ → ℕ → ℕ → A → List A → A → List A → Option ((A × A) × (A × A))
  | 0, _, _, _, _, _, _ => none
  | k + 1, n, i, x, p, y, q =>
    if i % 2 = 1 then
      match p, q with
      | sx :: px, sy :: py =>
          if (sx, x) = (sy, y) then
            findCollisionAux k ((n + 1) / 2) (i / 2) (h sx x) px (h sy y) py
          else if h sx x = h sy y then some ((sx, x), (sy, y))
          else findCollisionAux k ((n + 1) / 2) (i / 2) (h sx x) px (h sy y) py
      | _, _ => none
    else if i + 1 < n then
      match p, q with
      | sx :: px, sy :: py =>
          if (x, sx) = (y, sy) then
            findCollisionAux k ((n + 1) / 2) (i / 2) (h x sx) px (h y sy) py
          else if h x sx = h y sy then some ((x, sx), (y, sy))
          else findCollisionAux k ((n + 1) / 2) (i / 2) (h x sx) px (h y sy) py
      | _, _ => none
    else findCollisionAux k ((n + 1) / 2) (i / 2) x p y q

/-- Inspect the forged and actual leaf-to-root paths for a concrete collision. The function returns
`none` when `i` is not a leaf position or when the two traversals expose no collision. -/
def findCollision [DecidableEq A] (l : List A) (i : ℕ) (x : A) (p : List A) :
    Option ((A × A) × (A × A)) :=
  match l[i]? with
  | none => none
  | some y =>
      findCollisionAux h (Nat.clog 2 l.length) l.length i x p y (authPath h l i)

private theorem findCollisionAux_complete [DecidableEq A] :
    ∀ (k n i : ℕ) (x : A) (p : List A) (y : A) (q : List A) (r : A),
      x ≠ y → recompute h k n i x p = some r → recompute h k n i y q = some r →
        ∃ c, findCollisionAux h k n i x p y q = some c ∧ IsCollision h c
  | 0, _, _, x, p, y, q, _, hxy, hx, hy => by
      rcases p with _ | ⟨_, _⟩
      · rcases q with _ | ⟨_, _⟩
        · simp only [recompute, Option.some.injEq] at hx hy
          exact (hxy (hx.trans hy.symm)).elim
        · simp [recompute] at hy
      · simp [recompute] at hx
  | k + 1, n, i, x, p, y, q, r, hxy, hx, hy => by
      simp only [recompute] at hx hy
      by_cases hodd : i % 2 = 1
      · simp only [hodd, ↓reduceIte] at hx hy
        rcases p with _ | ⟨sx, px⟩
        · simp at hx
        rcases q with _ | ⟨sy, py⟩
        · simp at hy
        have hpair : (sx, x) ≠ (sy, y) := fun heq => hxy (Prod.mk.inj heq).2
        by_cases hout : h sx x = h sy y
        · refine ⟨((sx, x), (sy, y)), ?_, hpair, hout⟩
          simp [findCollisionAux, hodd, hpair, hout]
        · obtain ⟨c, hc, hcoll⟩ :=
            findCollisionAux_complete k ((n + 1) / 2) (i / 2) (h sx x) px (h sy y) py r
              hout hx hy
          refine ⟨c, ?_, hcoll⟩
          simp [findCollisionAux, hodd, hpair, hout, hc]
      · simp only [hodd, ↓reduceIte] at hx hy
        by_cases hnext : i + 1 < n
        · simp only [hnext, ↓reduceIte] at hx hy
          rcases p with _ | ⟨sx, px⟩
          · simp at hx
          rcases q with _ | ⟨sy, py⟩
          · simp at hy
          have hpair : (x, sx) ≠ (y, sy) := fun heq => hxy (Prod.mk.inj heq).1
          by_cases hout : h x sx = h y sy
          · refine ⟨((x, sx), (y, sy)), ?_, hpair, hout⟩
            simp [findCollisionAux, hodd, hnext, hpair, hout]
          · obtain ⟨c, hc, hcoll⟩ :=
              findCollisionAux_complete k ((n + 1) / 2) (i / 2) (h x sx) px (h y sy) py r
                hout hx hy
            refine ⟨c, ?_, hcoll⟩
            simp [findCollisionAux, hodd, hnext, hpair, hout, hc]
        · simp only [hnext, ↓reduceIte] at hx hy
          obtain ⟨c, hc, hcoll⟩ :=
            findCollisionAux_complete k ((n + 1) / 2) (i / 2) x p y q r hxy hx hy
          exact ⟨c, by simp [findCollisionAux, hodd, hnext, hc], hcoll⟩

/-- **Constructive soundness** of Merkle inclusion proofs: if a path for `x` at position `i`
verifies against the root of `l`, then `x` is the actual leaf or `findCollision` returns unequal
hash-input pairs from the forged and actual paths on which `h` agrees. -/
theorem verify_sound_findCollision [DecidableEq A] {l : List A} {i : ℕ} {x r : A}
    {p : List A} (hr : root h l = some r) (hv : verify h l.length i x p r = true) :
    l[i]? = some x ∨ ∃ c, findCollision h l i x p = some c ∧ IsCollision h c := by
  obtain ⟨hi, hrec⟩ := (verify_eq_true_iff h).1 hv
  have hy : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  by_cases hleaf : l[i]? = some x
  · exact Or.inl hleaf
  · right
    have hxy : x ≠ l[i] := by
      intro heq
      apply hleaf
      simpa only [heq] using hy
    have hhonest :
        recompute h (Nat.clog 2 l.length) l.length i l[i] (authPath h l i) = some r :=
      ((verify_eq_true_iff h).1 (verify_authPath h hy hr)).2
    rw [findCollision, hy]
    exact findCollisionAux_complete h _ _ _ _ _ _ _ _ hxy hrec hhonest

end Cslib.Crypto.MerkleTree
