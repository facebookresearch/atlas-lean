/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF

/-!
# The Merkle–Damgård transform: a hash collision yields a compression collision

A compression function `h : S × B → S` (chaining value and message block) and an initial value
`iv : S` define the Merkle–Damgård hash of a list of blocks `M = [x₁, …, x_L]` with length
strengthening: `z₀ = iv`, `zᵢ = h (zᵢ₋₁, xᵢ)`, and `hash M = h (z_L, ⟨L⟩)`, where `⟨L⟩ = lenBlock L`
encodes the number of blocks as one more block.

* `findCollision h iv lenBlock M M'` is an explicit procedure that compares the last compression
  inputs and then walks back through the two chains (`search`).
* `findCollision_spec` (a block-level form of Katz and Lindell, Theorem 5.4): if `M ≠ M'`,
  `hash M = hash M'`, and the length encoding separates the two lengths, then `findCollision`
  returns two distinct inputs on which `h` agrees.
* `hashCollisionGame_le` (**collision resistance is preserved**, as an advantage inequality): for
  any collision finder `A` for the hash with random coins in a finite type `R`, using messages of
  fewer than `maxLen` blocks on which `lenBlock` is injective, the compression-function collision
  finder `findCollision ∘ A` succeeds with at least the same probability.

**Relation to the textbook.** Katz and Lindell's Construction 5.3 zero-pads an arbitrary bit
string of length `L < 2 ^ n` into blocks and appends `L` itself as the final block. Here messages
are already lists of blocks and the final block encodes the number of blocks; the hypothesis that
`lenBlock` separates the lengths in question replaces the bound `L < 2 ^ n`. The collision-finding
argument is the textbook one.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.2.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleDamgard

variable {S B : Type*} (h : S × B → S) (iv : S)

/-- The chaining value after processing a list of blocks given **last block first**:
`chainRev [] = iv` and `chainRev (x :: xs) = h (chainRev xs, x)`. -/
def chainRev : List B → S
  | [] => iv
  | x :: xs => h (chainRev xs, x)

/-- The chaining value `z_L` after processing the blocks of `M` in order. -/
def chain (M : List B) : S := chainRev h iv M.reverse

theorem chain_eq_foldl (M : List B) : chain h iv M = M.foldl (fun z x => h (z, x)) iv := by
  rw [chain, ← List.foldr_reverse]
  induction M.reverse with
  | nil => rfl
  | cons x xs ih => simp [chainRev, ih]

variable (lenBlock : ℕ → B)

/-- The Merkle–Damgård hash with length strengthening: `h (z_L, lenBlock L)`. -/
def hash (M : List B) : S := h (chain h iv M, lenBlock M.length)

variable [DecidableEq S] [DecidableEq B]

/-- Walk back through two chains given last block first, returning the first pair of distinct
compression inputs. -/
def search : List B → List B → Option ((S × B) × (S × B))
  | x :: xs, y :: ys =>
    if (chainRev h iv xs, x) = (chainRev h iv ys, y) then search xs ys
    else some ((chainRev h iv xs, x), (chainRev h iv ys, y))
  | _, _ => none

/-- A pair of compression inputs that collide. -/
def IsCollision (p : (S × B) × (S × B)) : Prop := p.1 ≠ p.2 ∧ h p.1 = h p.2

instance (p : (S × B) × (S × B)) : Decidable (IsCollision h p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem search_spec : ∀ {xs ys : List B}, xs.length = ys.length → xs ≠ ys →
    chainRev h iv xs = chainRev h iv ys →
    ∃ p, search h iv xs ys = some p ∧ IsCollision h p
  | [], [], _, hne, _ => absurd rfl hne
  | x :: xs, y :: ys, hlen, hne, heq => by
    rw [search]
    split_ifs with hin
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hin
      subst h2
      exact search_spec (by simpa using hlen) (fun h => hne (h ▸ rfl)) h1
    · exact ⟨_, rfl, hin, heq⟩

/-- Find a compression collision behind a hash collision: compare the final compression inputs,
and if they agree, walk back through the two chains. -/
def findCollision (M M' : List B) : Option ((S × B) × (S × B)) :=
  if (chain h iv M, lenBlock M.length) = (chain h iv M', lenBlock M'.length) then
    search h iv M.reverse M'.reverse
  else some ((chain h iv M, lenBlock M.length), (chain h iv M', lenBlock M'.length))

/-- **Merkle–Damgård** (block-level form of Katz and Lindell, Theorem 5.4): from distinct
messages with equal hashes whose lengths the length block separates, `findCollision` extracts a
collision of `h`. -/
theorem findCollision_spec {M M' : List B} (hne : M ≠ M')
    (heq : hash h iv lenBlock M = hash h iv lenBlock M')
    (hlen : lenBlock M.length = lenBlock M'.length → M.length = M'.length) :
    ∃ p, findCollision h iv lenBlock M M' = some p ∧ IsCollision h p := by
  rw [findCollision]
  split_ifs with hin
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hin
    exact search_spec h iv (by simpa using hlen h2) (fun h => hne (List.reverse_injective h)) h1
  · exact ⟨_, rfl, hin, heq⟩

/-! ### The collision-finding games -/

variable {R : Type*} [Fintype R] [Nonempty R] (maxLen : ℕ)

/-- Collision finding for the hash: the adversary's coins are uniform, and it wins with two
distinct messages of fewer than `maxLen` blocks with the same hash. -/
noncomputable def hashCollisionGame (A : R → List B × List B) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype R).map fun r =>
    decide ((A r).1 ≠ (A r).2 ∧ (A r).1.length < maxLen ∧ (A r).2.length < maxLen ∧
      hash h iv lenBlock (A r).1 = hash h iv lenBlock (A r).2)

/-- Collision finding for the compression function: the adversary wins when it outputs a
collision of `h`. -/
noncomputable def compressionCollisionGame (A : R → Option ((S × B) × (S × B))) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype R).map fun r =>
    match A r with
    | some p => decide (IsCollision h p)
    | none => false

/-- The compression-collision finder built from a hash-collision finder. -/
def reduction (A : R → List B × List B) : R → Option ((S × B) × (S × B)) :=
  fun r => findCollision h iv lenBlock (A r).1 (A r).2

omit [DecidableEq S] [DecidableEq B] in
private theorem map_uniform_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] {f g : Ω → Bool}
    (hfg : ∀ ω, f ω = true → g ω = true) :
    (Cslib.Probability.PMF.uniformOfFintype Ω).map f true ≤
      (Cslib.Probability.PMF.uniformOfFintype Ω).map g true := by
  rw [PMF.map_apply, PMF.map_apply]
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases hf : f ω = true
  · simp [hf, hfg ω hf]
  · simp only [eq_comm (a := true), hf]
    exact zero_le

/-- **The Merkle–Damgård transform preserves collision resistance**: if `lenBlock` is injective
on lengths below `maxLen`, the reduction finds a compression collision with at least the
probability that `A` finds a hash collision. -/
theorem hashCollisionGame_le (hinj : ∀ L L', L < maxLen → L' < maxLen → lenBlock L = lenBlock L' →
    L = L') (A : R → List B × List B) :
    hashCollisionGame h iv lenBlock maxLen A true ≤
      compressionCollisionGame h (reduction h iv lenBlock A) true := by
  refine map_uniform_le fun r hr => ?_
  simp only [decide_eq_true_eq] at hr
  obtain ⟨hne, h1, h2, heq⟩ := hr
  obtain ⟨p, hp, hcoll⟩ := findCollision_spec h iv lenBlock hne heq (hinj _ _ h1 h2)
  simp only [reduction, hp, decide_eq_true_eq]
  exact hcoll

end Cslib.Crypto.MerkleDamgard
