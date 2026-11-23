/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinPruning
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Lattice

/-!
# Joint maximum-likelihood ancestral reconstruction (Pupko's algorithm)

On a rooted binary phylogeny `t : Tree L S R` (the tree of `FelsensteinPruning`, with transition
weights `P a b` on every child edge and leaf weights `obs l s`), a *joint reconstruction* of one
site is a root state `s` together with a labeling `z : Labeling t` of all non-root nodes. Its
likelihood is `π s * weight obs t s z`, the root weight times the product over all edges of the
transition weights times the leaf weights. Joint maximum-likelihood ancestral reconstruction
asks for a pair `(s, z)` of maximal likelihood.

Pupko, Pe'er, Shamir and Graur (2000) solve this by dynamic programming: replace the sums of
Felsenstein's pruning recursion by maxima (`maxPrune`), remember at every edge and every state
of the parent a child state attaining the maximum (`traceback`), pick a root state maximizing
`π s * maxPrune obs t s` (`jointRoot`), and read the labeling top-down.

The weights live in a linearly ordered commutative semiring `R` (`ℝ`, `ℚ`, `ℕ`, `ℝ≥0`); the
optimality statements assume every transition weight, every leaf weight and the root weights are
nonnegative (`NonnegWeights`), as for probabilities. Without nonnegativity the max-product
recursion does not compute the maximum (a product of two negative maxima need not be maximal);
`weight_traceback` (the traced labeling has weight `maxPrune`) holds without it.

## Main results

* `weight_le_maxPrune`, `weight_traceback`, `maxPrune_eq_sup'`: the max-product recursion
  computes the maximal weight of a labeling given the root state, and the traceback attains it.
* `pupko_isJointML`: **Pupko's reconstruction is a joint maximum-likelihood reconstruction**.
* `jointLik_pupko`: its likelihood is `max_s π s * maxPrune obs t s`.

## Cost model

Tabulating `maxPrune` per subtree (as `pruneTab` does for sums) takes `O(|S|²)` comparisons and
multiplications per internal node, linear in the number of taxa; the traceback is one more
top-down pass. `maxPrune` itself is the specification and is not tabulated here.

## References

* T. Pupko, I. Pe'er, R. Shamir and D. Graur, *A fast algorithm for joint reconstruction of
  ancestral amino acid sequences*, Mol. Biol. Evol. 17 (2000), 890–896.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 16.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Phylogenetics.AncestralReconstruction

open Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning Tree Finset

universe u v w

variable {L : Type u} {S : Type v} {R : Type w}

/-- All transition weights in the tree are nonnegative. -/
def NonnegWeights [Zero R] [LE R] : Tree L S R → Prop
  | leaf _ => True
  | node P l Q r => (∀ a b, 0 ≤ P a b) ∧ (∀ a b, 0 ≤ Q a b) ∧ NonnegWeights l ∧ NonnegWeights r

section Argmax

variable [LinearOrder R] [Finite S] [Nonempty S]

/-- A state maximizing `f` (ties broken by choice). -/
noncomputable def argmaxState (f : S → R) : S :=
  (Finite.exists_max f).choose

/-- `argmaxState f` maximizes `f`. -/
theorem le_argmaxState (f : S → R) (a : S) : f a ≤ f (argmaxState f) :=
  (Finite.exists_max f).choose_spec a

/-- The value at `argmaxState f` is the maximum `univ.sup'` of `f`. -/
theorem sup'_eq_argmaxState [Fintype S] (f : S → R) :
    univ.sup' univ_nonempty f = f (argmaxState f) :=
  le_antisymm (sup'_le _ _ fun a _ => le_argmaxState f a) (le_sup' f (mem_univ _))

end Argmax

variable [CommSemiring R] [LinearOrder R] [IsOrderedRing R] [Fintype S] [Nonempty S]

variable (obs : L → S → R)

/-- The max-product (Viterbi) form of Felsenstein's pruning recursion: the largest weight of a
labeling of the subtree `t` given state `s` at its root. -/
def maxPrune : Tree L S R → S → R
  | leaf l, s => obs l s
  | node P l Q r, s =>
    (univ.sup' univ_nonempty fun a => P s a * maxPrune l a) *
      (univ.sup' univ_nonempty fun b => Q s b * maxPrune r b)

/-- Pupko's traceback: given the state `s` of the root of `t`, label each child with a state
maximizing the transition weight times the child's `maxPrune`, and recurse. -/
noncomputable def traceback : (t : Tree L S R) → S → Labeling t
  | leaf _, _ => PUnit.unit
  | node P l Q r, s =>
    let a := argmaxState fun a => P s a * maxPrune obs l a
    let b := argmaxState fun b => Q s b * maxPrune obs r b
    ((a, traceback l a), (b, traceback r b))

/-- With nonnegative weights, `maxPrune` is nonnegative. -/
theorem maxPrune_nonneg (hobs : ∀ l s, 0 ≤ obs l s) :
    ∀ (t : Tree L S R), NonnegWeights t → ∀ s, 0 ≤ maxPrune obs t s := by
  intro t
  induction t with
  | leaf l => intro _ s; exact hobs l s
  | node P l Q r ihl ihr =>
    intro ht s
    obtain ⟨hP, hQ, hl, hr⟩ := ht
    have a0 : S := Classical.arbitrary S
    exact mul_nonneg
      (le_trans (mul_nonneg (hP s a0) (ihl hl a0)) (le_sup' (fun a => P s a * maxPrune obs l a)
        (mem_univ a0)))
      (le_trans (mul_nonneg (hQ s a0) (ihr hr a0)) (le_sup' (fun b => Q s b * maxPrune obs r b)
        (mem_univ a0)))

omit [IsOrderedRing R] in
/-- **The traced labeling attains `maxPrune`.** No sign condition is needed. -/
theorem weight_traceback :
    ∀ (t : Tree L S R) (s : S), weight obs t s (traceback obs t s) = maxPrune obs t s
  | leaf _, _ => rfl
  | node P l Q r, s => by
    simp only [weight, traceback, maxPrune, weight_traceback l, weight_traceback r]
    rw [sup'_eq_argmaxState (fun a => P s a * maxPrune obs l a),
      sup'_eq_argmaxState (fun b => Q s b * maxPrune obs r b)]

omit [Fintype S] [Nonempty S] in
/-- With nonnegative weights, every labeling has nonnegative weight. -/
theorem weight_nonneg (hobs : ∀ l s, 0 ≤ obs l s) :
    ∀ (t : Tree L S R), NonnegWeights t → ∀ (s : S) (z : Labeling t), 0 ≤ weight obs t s z
  | leaf l, _, s, _ => hobs l s
  | node P l Q r, ht, s, z => by
    obtain ⟨hP, hQ, hl, hr⟩ := ht
    exact mul_nonneg (mul_nonneg (hP _ _) (weight_nonneg hobs l hl _ _))
      (mul_nonneg (hQ _ _) (weight_nonneg hobs r hr _ _))

/-- **`maxPrune` bounds the weight of every labeling** (nonnegative weights). -/
theorem weight_le_maxPrune (hobs : ∀ l s, 0 ≤ obs l s) :
    ∀ (t : Tree L S R), NonnegWeights t → ∀ (s : S) (z : Labeling t),
      weight obs t s z ≤ maxPrune obs t s
  | leaf _, _, _, _ => le_rfl
  | node P l Q r, ht, s, z => by
    obtain ⟨hP, hQ, hl, hr⟩ := ht
    simp only [weight, maxPrune]
    exact mul_le_mul
      ((mul_le_mul_of_nonneg_left (weight_le_maxPrune hobs l hl _ _) (hP _ _)).trans
        (le_sup' (fun a => P s a * maxPrune obs l a) (mem_univ _)))
      ((mul_le_mul_of_nonneg_left (weight_le_maxPrune hobs r hr _ _) (hQ _ _)).trans
        (le_sup' (fun b => Q s b * maxPrune obs r b) (mem_univ _)))
      (mul_nonneg (hQ _ _) (weight_nonneg obs hobs r hr _ _))
      (le_trans (mul_nonneg (hP _ _) (maxPrune_nonneg obs hobs l hl _))
        (le_sup' (fun a => P s a * maxPrune obs l a) (mem_univ z.1.1)))

/-- **The max-product recursion computes the maximal labeling weight**: `maxPrune obs t s` is the
maximum over all labelings `z` of the non-root nodes of `weight obs t s z`. -/
theorem maxPrune_eq_sup' (hobs : ∀ l s, 0 ≤ obs l s) (t : Tree L S R) (ht : NonnegWeights t)
    (s : S) :
    maxPrune obs t s = univ.sup' ⟨traceback obs t s, mem_univ _⟩ (weight obs t s) := by
  refine le_antisymm ?_ (sup'_le _ _ fun z _ => weight_le_maxPrune obs hobs t ht s z)
  rw [← weight_traceback obs t s]
  exact le_sup' (weight obs t s) (mem_univ _)

/-- The root state of Pupko's reconstruction: it maximizes `π s * maxPrune obs t s`. -/
noncomputable def jointRoot (t : Tree L S R) (π : S → R) : S :=
  argmaxState fun s => π s * maxPrune obs t s

/-- **Pupko's joint reconstruction**: the root state `jointRoot` and the traced labeling. -/
noncomputable def pupko (t : Tree L S R) (π : S → R) : S × Labeling t :=
  (jointRoot obs t π, traceback obs t (jointRoot obs t π))

omit [IsOrderedRing R] in
/-- The likelihood of Pupko's reconstruction is `max_s π s * maxPrune obs t s`. -/
theorem jointLik_pupko (t : Tree L S R) (π : S → R) :
    π (pupko obs t π).1 * weight obs t (pupko obs t π).1 (pupko obs t π).2 =
      univ.sup' univ_nonempty fun s => π s * maxPrune obs t s := by
  simp only [pupko, jointRoot, weight_traceback]
  exact (sup'_eq_argmaxState fun s => π s * maxPrune obs t s).symm

/-- **Pupko et al. (2000): joint maximum likelihood.** With nonnegative root, transition and leaf
weights, no root state `s` and labeling `z` of the non-root nodes has larger joint likelihood
`π s * weight obs t s z` than Pupko's reconstruction. -/
theorem pupko_isJointML (hobs : ∀ l s, 0 ≤ obs l s) (t : Tree L S R) (ht : NonnegWeights t)
    (π : S → R) (hπ : ∀ s, 0 ≤ π s) (s : S) (z : Labeling t) :
    π s * weight obs t s z ≤
      π (pupko obs t π).1 * weight obs t (pupko obs t π).1 (pupko obs t π).2 := by
  rw [jointLik_pupko]
  exact (mul_le_mul_of_nonneg_left (weight_le_maxPrune obs hobs t ht s z) (hπ s)).trans
    (le_sup' (fun s => π s * maxPrune obs t s) (mem_univ s))

end Cslib.Bioinformatics.Phylogenetics.AncestralReconstruction
