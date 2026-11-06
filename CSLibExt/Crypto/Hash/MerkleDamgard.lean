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

/-- **Chaining value of a reversed block list.** Let $h : S \times B \to S$ be a compression
function and $iv \in S$ an initial value. The chaining value of a list of blocks given last block
first is defined recursively: the empty list has chaining value $iv$, and a list with first entry
$x$ followed by a list $xs$ has chaining value $h(c, x)$, where $c$ is the chaining value of
$xs$. -/
def chainRev : List B → S
  | [] => iv
  | x :: xs => h (chainRev xs, x)

/-- **Merkle–Damgård chaining value.** Let $h : S \times B \to S$ be a compression function and
$iv \in S$ an initial value. The chaining value of a list of blocks $M = (x_1, \dots, x_L)$ is
$z_L$, where $z_0 = iv$ and $z_i = h(z_{i-1}, x_i)$ for $1 \le i \le L$. -/
def chain (M : List B) : S := chainRev h iv M.reverse

theorem chain_eq_foldl (M : List B) : chain h iv M = M.foldl (fun z x => h (z, x)) iv := by
  rw [chain, ← List.foldr_reverse]
  induction M.reverse with
  | nil => rfl
  | cons x xs ih => simp [chainRev, ih]

variable (lenBlock : ℕ → B)

/-- **Merkle–Damgård hash with length strengthening.** Let $h : S \times B \to S$ be a compression
function, $iv \in S$ an initial value and $\ell : \mathbb{N} \to B$ a length encoding. The hash of
a list of blocks $M = (x_1, \dots, x_L)$ is $h(z_L, \ell(L))$, where $z_0 = iv$ and
$z_i = h(z_{i-1}, x_i)$ for $1 \le i \le L$. -/
def hash (M : List B) : S := h (chain h iv M, lenBlock M.length)

variable [DecidableEq S] [DecidableEq B]

/-- **Backward search for a compression collision.** Let $h : S \times B \to S$ be a compression
function with initial value $iv$, and for a list of blocks written last block first let $z(xs)$
be its chaining value: $z([\,]) = iv$ and $z(x :: xs) = h(z(xs), x)$. Given two such lists, the
search compares their leading compression inputs: on $x :: xs$ and $y :: ys$, if
$(z(xs), x) = (z(ys), y)$ it continues with $xs$ and $ys$, and otherwise it returns the pair
$((z(xs), x), (z(ys), y))$. When either list is empty it returns no pair. -/
def search : List B → List B → Option ((S × B) × (S × B))
  | x :: xs, y :: ys =>
    if (chainRev h iv xs, x) = (chainRev h iv ys, y) then search xs ys
    else some ((chainRev h iv xs, x), (chainRev h iv ys, y))
  | _, _ => none

/-- **Collision of a compression function.** Let $h : S \times B \to S$ be a compression function.
A pair $(p_1, p_2)$ of compression inputs in $S \times B$ is a collision of $h$ when $p_1 \ne p_2$
and $h(p_1) = h(p_2)$. -/
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

/-- **Extracting a compression collision from a Merkle–Damgård collision.** Let
$h : S \times B \to S$ be a compression function, $iv \in S$ an initial value and
$\ell : \mathbb{N} \to B$ a length encoding. Let $M = (x_1, \dots, x_L)$ and
$M' = (x'_1, \dots, x'_{L'})$ be lists of blocks with chaining values $z_0 = z'_0 = iv$,
$z_i = h(z_{i-1}, x_i)$ and $z'_j = h(z'_{j-1}, x'_j)$. The procedure compares the final
compression inputs $(z_L, \ell(L))$ and $(z'_{L'}, \ell(L'))$ and returns this pair if they
differ. Otherwise, for $k = 1, 2, \dots, \min(L, L')$ in turn, it compares
$(z_{L-k}, x_{L-k+1})$ with $(z'_{L'-k}, x'_{L'-k+1})$ and returns the first such pair that
differs; if there is none, it returns no output. -/
def findCollision (M M' : List B) : Option ((S × B) × (S × B)) :=
  if (chain h iv M, lenBlock M.length) = (chain h iv M', lenBlock M'.length) then
    search h iv M.reverse M'.reverse
  else some ((chain h iv M, lenBlock M.length), (chain h iv M', lenBlock M'.length))

/-- **A Merkle–Damgård hash collision yields a compression collision.** Let
$h : S \times B \to S$ be a compression function, $iv \in S$ an initial value and
$\ell : \mathbb{N} \to B$ a length encoding, and let $H$ be the Merkle–Damgård hash with length
strengthening they define. Write $|M|$ for the number of blocks of a list of blocks $M$. If $M$
and $M'$ are distinct lists of blocks with $H(M) = H(M')$, and $\ell(|M|) = \ell(|M'|)$ implies
$|M| = |M'|$, then the collision-finding procedure applied to $M$ and $M'$ returns a pair
$(p_1, p_2)$ of compression inputs with $p_1 \ne p_2$ and $h(p_1) = h(p_2)$.

This is a block-level form of Katz and Lindell, Theorem 5.4. -/
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

/-- **Hash collision game for Merkle–Damgård.** Let $H$ be the Merkle–Damgård hash with length
strengthening defined by a compression function $h : S \times B \to S$, an initial value
$iv \in S$ and a length encoding $\ell : \mathbb{N} \to B$, and let $N$ be a natural number. An
adversary $A$ maps random coins $r$ from a finite nonempty type $R$ to a pair of lists of blocks.
The game is the distribution of the Boolean outcome when $r$ is drawn uniformly from $R$: the
adversary wins (outcome true) exactly when $A(r) = (M, M')$ with $M \ne M'$, both $M$ and $M'$
have fewer than $N$ blocks, and $H(M) = H(M')$. -/
noncomputable def hashCollisionGame (A : R → List B × List B) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype R).map fun r =>
    decide ((A r).1 ≠ (A r).2 ∧ (A r).1.length < maxLen ∧ (A r).2.length < maxLen ∧
      hash h iv lenBlock (A r).1 = hash h iv lenBlock (A r).2)

/-- **Compression-function collision game.** Let $h : S \times B \to S$ be a compression function
and let $A$ be an adversary that maps random coins $r$ from a finite nonempty type $R$ either to a
pair $(p_1, p_2)$ of compression inputs in $S \times B$ or to no output. The game is the
distribution of the Boolean outcome when $r$ is drawn uniformly from $R$: the adversary wins
(outcome true) exactly when $A(r)$ is a pair $(p_1, p_2)$ with $p_1 \ne p_2$ and
$h(p_1) = h(p_2)$, and loses when $A(r)$ is no output. -/
noncomputable def compressionCollisionGame (A : R → Option ((S × B) × (S × B))) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype R).map fun r =>
    match A r with
    | some p => decide (IsCollision h p)
    | none => false

/-- **Merkle–Damgård collision reduction.** Let $h : S \times B \to S$ be a compression function,
$iv \in S$ an initial value, $\ell : \mathbb{N} \to B$ a length encoding and $A$ an adversary that
maps random coins $r$ from a finite nonempty type $R$ to a pair $(M, M')$ of lists of blocks. The
reduction is the adversary that, on coins $r$, outputs the result of the Merkle–Damgård
collision-finding procedure applied to the pair $(M, M') = A(r)$: a pair of compression inputs,
or no output. -/
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

/-- **The Merkle–Damgård transform preserves collision resistance.** Let $h : S \times B \to S$
be a compression function, $iv \in S$ an initial value, $\ell : \mathbb{N} \to B$ a length
encoding and $N$ a natural number such that $\ell$ is injective on $\{0, 1, \dots, N - 1\}$. Then
for every adversary $A$ that maps random coins from a finite nonempty type $R$ to a pair of lists
of blocks, the probability that the reduction built from $A$ wins the compression-function
collision game for $h$ is at least the probability that $A$ wins the hash collision game for the
Merkle–Damgård hash defined by $h$, $iv$ and $\ell$ with messages of fewer than $N$ blocks. -/
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
