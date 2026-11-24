/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Free
public import MathlibExt.Combinatorics.SemigroupLargeness
import Mathlib.Data.Fintype.Pi

/-!
# Hales–Jewett configurations in J-sets

Every J-set of nonempty words contains all substitutions of a variable word over any
given finite level of an increasing alphabet.
-/

namespace MetaMathlibExt

/-- **J-sets contain Hales–Jewett configurations.** Let $A_0 \subseteq A_1 \subseteq \cdots$ be
finite sets whose union $A$ is nonempty, and let $S_0$ be the semigroup of nonempty finite words
over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable word over $A$ is a nonempty
finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which
every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$
is obtained from $w$ by replacing each $v_i$ by $a_i$. If $D \subseteq S_0$ is a $J$-set, then
for all $m, n \in \mathbb{N}$ there is an $n$-variable word $w$ over $A$ with $w(\vec a) \in D$
for every $\vec a \in A_m^n$.

The alphabet must be nonempty: over the empty alphabet every subset of $S_0 = \emptyset$ is
vacuously a $J$-set, and there is no $0$-variable word.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Lemma 3.4. -/
public theorem exists_variableWord_subst_mem_of_isMulJSet {α : Type*} [Nonempty α]
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (m n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D := by
  classical
  obtain ⟨c⟩ := ‹Nonempty α›
  obtain ⟨k, hk⟩ := hcover c
  -- Enlarge the level to include c, so the family of substitutions is nonempty.
  let tuples := Fintype.piFinset fun _ : Fin n => A (max m k)
  have htuples : tuples.Nonempty :=
    ⟨fun _ => c, Fintype.mem_piFinset.mpr fun _ => hA (le_max_right _ _) hk⟩
  let block : FreeSemigroup (α ⊕ Fin n) := ⟨Sum.inl c, List.ofFn Sum.inr⟩
  let subst (a : Fin n → α) := FreeSemigroup.map (Sum.elim id a)
  let seq (a : Fin n → α) (_ : ℕ) := subst a block
  obtain ⟨r, b, t, _, hb⟩ := hD (tuples.image seq) (htuples.image seq)
  -- Interleave the constant coefficient words with copies of the unsubstituted block.
  let embed : FreeSemigroup α →ₙ* FreeSemigroup (α ⊕ Fin n) := FreeSemigroup.map Sum.inl
  let parts := List.ofFn fun j : Fin r => embed (b j.succ.castSucc) * block
  refine ⟨parts.foldl (· * ·) (embed (b 0) * block) * embed (b (Fin.last (r + 1))), ?_, ?_⟩
  · intro i
    have letters_mul (u v : FreeSemigroup (α ⊕ Fin n)) :
        (u * v).head :: (u * v).tail = (u.head :: u.tail) ++ (v.head :: v.tail) := rfl
    rw [letters_mul]
    apply List.mem_append_left
    apply parts.foldlRecOn (motive := fun w => Sum.inr i ∈ w.head :: w.tail) (· * ·)
    · rw [letters_mul]
      exact List.mem_append_right _ (.tail _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    · intro w hw v _
      rw [letters_mul]
      exact List.mem_append_left _ hw
  · intro a ha
    have hfix (u : FreeSemigroup α) : subst a (embed u) = u := by
      induction u with simp [subst, embed, *]
    have hfold (xs : List (FreeSemigroup (α ⊕ Fin n))) (u) :
        subst a (xs.foldl (· * ·) u) = (xs.map (subst a)).foldl (· * ·) (subst a u) := by
      rw [List.foldl_map]
      exact (List.foldl_hom (subst a) fun x y => (map_mul (subst a) x y).symm).symm
    have ha' : a ∈ tuples := Fintype.mem_piFinset.mpr fun i => hA (le_max_left _ _) (ha i)
    change subst a _ ∈ D
    simpa only [map_mul, hfold, parts, List.map_ofFn, Function.comp_def, hfix, seq] using
      hb (seq a) (Finset.mem_image_of_mem seq ha')

end MetaMathlibExt
