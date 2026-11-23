/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

/-!
# Weighted zero-sum free sequences and the weighted Davenport constant

For a weight set `A ⊆ ℕ` and an additive commutative monoid `G`, a finite sequence over `G` is
`A`-weighted zero-sum free when no non-empty set of its terms has a vanishing `A`-weighted
sum. The weighted Davenport constant `D_A(G)` is the least length forcing such a zero sum,
valued in `ℕ∞` (`⊤` when no length forces one).
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Weighted zero-sum free sequences.** Let $G$ be an additive commutative monoid and $A$ a
finite set of natural numbers. A finite sequence $s = (s_1, \dots, s_n)$ over $G$ is
$A$-weighted zero-sum free when, for every non-empty set $I \subseteq \{1, \dots, n\}$ of
positions and every choice of weights $a_i \in A$ for $i \in I$, the weighted sum
$\sum_{i \in I} a_i s_i$ is non-zero, where $a_i s_i$ is the sum of $a_i$ copies of $s_i$.
Terms are indexed by position, so repeated terms count separately.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (weighted zero-sum subsequences, as used in Lemmas 2 and 3). -/
def IsWeightedZeroSumFree {G : Type*} [AddCommMonoid G] (A : Finset ℕ) (s : List G) :
    Prop :=
  ∀ I : Finset (Fin s.length), I.Nonempty → ∀ a : Fin s.length → ℕ,
    (∀ i ∈ I, a i ∈ A) → ∑ i ∈ I, a i • s.get i ≠ 0

/-- **Weighted Davenport constant.** Let $G$ be an additive commutative monoid and $A$ a finite
set of natural numbers. The $A$-weighted Davenport constant $D_A(G) \in \mathbb{N} \cup \{\infty\}$
is the least length $\ell \in \mathbb{N}$ such that no sequence over $G$ of length $\ell$ is
$A$-weighted zero-sum free, that is, such that every sequence over $G$ of length $\ell$ has a
non-empty $A$-weighted zero-sum subsequence; it is $\infty$ when no such length exists.

For example $D_A(G) = \infty$ when $A = \emptyset$, or when $A = \{1\}$ and $G = \mathbb{Z}$. For
a finite group $G$ and a non-empty weight set $A$ it is finite. The ordinary Davenport constant of
$G$ is $D_{\{1\}}(G)$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (definition of `D_A(G)`). -/
noncomputable def weightedDavenport (A : Finset ℕ) (G : Type*) [AddCommMonoid G] : ℕ∞ :=
  ⨅ ℓ ∈ {ℓ : ℕ | ∀ s : List G, s.length = ℓ → ¬ IsWeightedZeroSumFree A s}, (ℓ : ℕ∞)

/-- **The weighted Davenport constant as a least length.** Let $G$ be an additive commutative
monoid, $A$ a finite set of natural numbers and $D_A(G)$ the $A$-weighted Davenport constant
of $G$. If there is a length $\ell \in \mathbb{N}$ such that no sequence over $G$ of length
$\ell$ is $A$-weighted zero-sum free, then $D_A(G)$ is finite and equals the least such length.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (definition of `D_A(G)`). -/
theorem weightedDavenport_eq_natCast_sInf (A : Finset ℕ) (G : Type*) [AddCommMonoid G]
    (h : {ℓ : ℕ | ∀ s : List G, s.length = ℓ → ¬ IsWeightedZeroSumFree A s}.Nonempty) :
    weightedDavenport A G =
      ((sInf {ℓ : ℕ | ∀ s : List G, s.length = ℓ → ¬ IsWeightedZeroSumFree A s} : ℕ) : ℕ∞) :=
  (ENat.natCast_sInf h).symm

/-- **Prefixes of weighted zero-sum free sequences.** Let $G$ be an additive commutative monoid
and $A$ a finite set of natural numbers. If a sequence $s$ over $G$ is $A$-weighted zero-sum
free, then for every $\ell \in \mathbb{N}$ the prefix of $s$ formed by its first $\ell$ terms
(all of $s$ when $\ell$ is at least its length) is $A$-weighted zero-sum free.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (definition of `D_A(G)`). -/
theorem IsWeightedZeroSumFree.take {G : Type*} [AddCommMonoid G] {A : Finset ℕ}
    {s : List G} (hs : IsWeightedZeroSumFree A s) (ℓ : ℕ) :
    IsWeightedZeroSumFree A (s.take ℓ) := by
  intro I hI a ha hsum
  have hlen : ∀ i : Fin (s.take ℓ).length, (i : ℕ) < s.length := fun i =>
    lt_of_lt_of_le i.2 (by simp)
  let e : Fin (s.take ℓ).length ↪ Fin s.length :=
    ⟨fun i => ⟨i, hlen i⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  let w : Fin s.length → ℕ := fun j =>
    if h : (j : ℕ) < (s.take ℓ).length then a ⟨j, h⟩ else 0
  have hw : ∀ i, w (e i) = a i := fun i => by
    show (if h : (i : ℕ) < (s.take ℓ).length then a ⟨i, h⟩ else 0) = a i
    rw [dite_eq_left i.2]
  have hget : ∀ i, s.get (e i) = (s.take ℓ).get i := fun i => by
    show s[(i : ℕ)] = (s.take ℓ)[(i : ℕ)]
    rw [List.getElem_take]
  refine hs (I.map e) (hI.map) w ?_ ?_
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    rw [hw]
    exact ha i hi
  · rw [Finset.sum_map]
    simp only [hw, hget]
    exact hsum

/-- **Upper bound for the weighted Davenport constant.** Let $G$ be an additive commutative
monoid, $A$ a finite set of natural numbers, $D_A(G)$ the $A$-weighted Davenport constant of
$G$ and $\ell$ a natural number. If no sequence over $G$ of length $\ell$ is $A$-weighted
zero-sum free, that is, every sequence over $G$ of length $\ell$ has a non-empty $A$-weighted
zero-sum subsequence, then $D_A(G) \le \ell$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (definition of `D_A(G)`). -/
theorem weightedDavenport_le {G : Type*} [AddCommMonoid G] {A : Finset ℕ} {ℓ : ℕ}
    (h : ∀ s : List G, s.length = ℓ → ¬ IsWeightedZeroSumFree A s) :
    weightedDavenport A G ≤ ℓ :=
  biInf_le (fun ℓ : ℕ => (ℓ : ℕ∞)) h

/-- **Lower bound for the weighted Davenport constant.** Let $G$ be an additive commutative
monoid, $A$ a finite set of natural numbers and $D_A(G)$ the $A$-weighted Davenport constant
of $G$. If a sequence over $G$ of length $L$ is $A$-weighted zero-sum free, then $L < D_A(G)$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (definition of `D_A(G)`). -/
theorem lt_weightedDavenport {G : Type*} [AddCommMonoid G] {A : Finset ℕ} {s : List G}
    (hs : IsWeightedZeroSumFree A s) : (s.length : ℕ∞) < weightedDavenport A G := by
  have hgt : ∀ ℓ ∈ {ℓ : ℕ | ∀ t : List G, t.length = ℓ → ¬ IsWeightedZeroSumFree A t},
      s.length < ℓ := by
    intro ℓ hℓ
    by_contra hle
    exact hℓ (s.take ℓ) (by simp; omega) (hs.take ℓ)
  by_cases hne : {ℓ : ℕ | ∀ t : List G, t.length = ℓ → ¬ IsWeightedZeroSumFree A t}.Nonempty
  · rw [weightedDavenport_eq_natCast_sInf A G hne]
    exact_mod_cast hgt _ (Nat.sInf_mem hne)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [weightedDavenport, hne]
    simp

/-- **When the weighted Davenport constant is infinite.** Let $G$ be an additive commutative
monoid, $A$ a finite set of natural numbers and $D_A(G)$ the $A$-weighted Davenport constant
of $G$. Then $D_A(G) = \infty$ if and only if for every $\ell \in \mathbb{N}$ there is an
$A$-weighted zero-sum free sequence over $G$ of length $\ell$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (definition of `D_A(G)`). -/
theorem weightedDavenport_eq_top_iff {G : Type*} [AddCommMonoid G] {A : Finset ℕ} :
    weightedDavenport A G = ⊤ ↔
      ∀ ℓ : ℕ, ∃ s : List G, s.length = ℓ ∧ IsWeightedZeroSumFree A s := by
  rw [weightedDavenport]
  simp only [iInf_eq_top, ENat.natCast_ne_top, imp_false]
  refine forall_congr' fun ℓ => ?_
  simp only [Set.mem_ofPred_eq, not_forall, not_not, exists_prop]

/-- **Weighted Davenport constant of the trivial group.** For every non-empty finite set $A$ of
natural numbers, the $A$-weighted Davenport constant of the trivial group $\mathbb{Z}/1\mathbb{Z}$
is $D_A(\mathbb{Z}/1\mathbb{Z}) = 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (characteristic value of `D_A`). -/
theorem weightedDavenport_zmod_one (A : Finset ℕ) (hA : A.Nonempty) :
    weightedDavenport A (ZMod 1) = 1 := by
  have hset :
      {ℓ | ∀ s : List (ZMod 1), s.length = ℓ → ¬ IsWeightedZeroSumFree A s} =
        Set.Ici 1 := by
    ext ℓ
    constructor
    · intro h
      by_contra hℓ
      change ¬1 ≤ ℓ at hℓ
      have hzero : ℓ = 0 := by omega
      have := h [] (by simp [hzero])
      apply this
      intro I hI
      obtain ⟨i, _⟩ := hI
      exact Fin.elim0 i
    · intro hℓ s hs hfree
      change 1 ≤ ℓ at hℓ
      have hspos : 0 < s.length := by omega
      obtain ⟨a, ha⟩ := hA
      let i : Fin s.length := ⟨0, hspos⟩
      have hz := hfree {i} (by simp) (fun _ => a) (by simpa using ha)
      exact hz (Subsingleton.elim _ _)
  rw [weightedDavenport_eq_natCast_sInf _ _ (by rw [hset]; exact Set.nonempty_Ici), hset]
  simp

/-- **Davenport constant of the group of order two.** The ordinary Davenport constant of
$\mathbb{Z}/2\mathbb{Z}$, that is, its $\{1\}$-weighted Davenport constant, is
$D_{\{1\}}(\mathbb{Z}/2\mathbb{Z}) = 2$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum Constants*, INTEGERS 26 (2026), Article A89, Section 2 (characteristic value of `D_A`). -/
theorem weightedDavenport_singleton_one_zmod_two :
    weightedDavenport {1} (ZMod 2) = 2 := by
  have hone : IsWeightedZeroSumFree {1} [(1 : ZMod 2)] := by
    intro I hI a ha
    have hzeroMem : (0 : Fin 1) ∈ I := by
      obtain ⟨i, hi⟩ := hI
      fin_cases i
      exact hi
    have hI' : I = {(0 : Fin 1)} := by
      ext i
      fin_cases i
      simp [hzeroMem]
    subst I
    have ha' : a 0 = 1 := by
      simpa using ha 0 (by simp)
    simp [ha']
  have hset :
      {ℓ | ∀ s : List (ZMod 2), s.length = ℓ → ¬ IsWeightedZeroSumFree {1} s} =
        Set.Ici 2 := by
    ext ℓ
    constructor
    · intro h
      by_contra hℓ
      change ¬2 ≤ ℓ at hℓ
      by_cases hzero : ℓ = 0
      · have hempty := h [] (by simp [hzero])
        apply hempty
        intro I hI
        obtain ⟨i, _⟩ := hI
        exact Fin.elim0 i
      · have honeLength : ℓ = 1 := by omega
        exact h [(1 : ZMod 2)] (by simp [honeLength]) hone
    · intro hℓ s hs hfree
      change 2 ≤ ℓ at hℓ
      have hslen : 2 ≤ s.length := by omega
      let i₀ : Fin s.length := ⟨0, by omega⟩
      let i₁ : Fin s.length := ⟨1, by omega⟩
      have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      rcases hcases (s.get i₀) with h₀ | h₀
      · have hz := hfree {i₀} (by simp) (fun _ => 1) (by simp)
        apply hz
        simpa only [Finset.sum_singleton, one_nsmul] using h₀
      · rcases hcases (s.get i₁) with h₁ | h₁
        · have hz := hfree {i₁} (by simp) (fun _ => 1) (by simp)
          apply hz
          simpa only [Finset.sum_singleton, one_nsmul] using h₁
        · have hne : i₀ ≠ i₁ := by
            intro heq
            simpa [i₀, i₁] using congrArg Fin.val heq
          have hz := hfree {i₀, i₁} (by simp) (fun _ => 1) (by simp)
          apply hz
          rw [Finset.sum_pair hne]
          simpa only [one_nsmul] using
            (calc
              s.get i₀ + s.get i₁ = 1 + 1 := congrArg₂ (· + ·) h₀ h₁
              _ = 0 := by decide)
  rw [weightedDavenport_eq_natCast_sInf _ _ (by rw [hset]; exact Set.nonempty_Ici), hset]
  simp

end MetaMathlibExt
