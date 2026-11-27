/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Complex.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Free independence in a noncommutative probability space

A *noncommutative probability space* is a unital complex algebra `A` with a linear functional
`φ : A → ℂ` such that `φ 1 = 1` (Anderson, Guionnet and Zeitouni (manuscript numbering), Definition
5.2.1). A family of
unital subalgebras `(A_j)` is *freely independent* if `φ (a₁ ⋯ aₙ) = 0` whenever each `aᵢ` lies in
some `A_{k(i)}`, is centred (`φ aᵢ = 0`), and consecutive indices differ, `k(i) ≠ k(i + 1)`
(Definition 5.3.1). Repetitions of indices are allowed as long as they are not consecutive, so this
is a genuinely noncommutative notion. Elements are free when the unital subalgebras they generate
are free.

Freeness is defined for a noncommutative probability space, so `IsFreelyIndependent` and
`AreFree` take a proof of `φ 1 = 1`. Without it the definition would be vacuous for `φ = 0`,
for which every family of subalgebras would be free.

## Main definitions

* `MathlibExt.Probability.FreeProbability.IsFreelyIndependent φ hφ B`: the family of
  subalgebras `B` is freely independent with respect to `φ`, where `hφ : φ 1 = 1`.
* `MathlibExt.Probability.FreeProbability.AreFree φ hφ a`: the family of elements `a` is free.

## Main results

* `IsFreelyIndependent.of_subsingleton`: a family with at most one member is free.
* `isFreelyIndependent_of_eq_bot`: a family in which every member but one is the algebra of
  scalars is free (scalars are free from everything).
* `IsFreelyIndependent.map_mul`: elements of two different free subalgebras satisfy
  `φ (a b) = φ a φ b`.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
  pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Definition
  5.2.1 and
  Definition 5.3.1.
-/

@[expose] public section

namespace MathlibExt.Probability.FreeProbability

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **Free independence** (Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*
(manuscript numbering),
Definition 5.3.1). Let `φ` be a linear functional with `φ 1 = 1`, so that `(A, φ)` is a
noncommutative probability space (Definition 5.2.1). A family `B : ι → Subalgebra ℂ A` of unital
subalgebras is freely independent with respect to `φ` if, for every `n ≥ 1`, indices
`k : Fin n → ι` with consecutive indices distinct (`k i ≠ k (i + 1)`) and elements `aᵢ ∈ B (k i)`
with `φ aᵢ = 0`, one has `φ (a₀ a₁ ⋯ a_{n-1}) = 0`. The words are indexed by `Fin (n + 1)` so
that they are nonempty. For `φ = 0`, which is excluded, every family would be free. -/
def IsFreelyIndependent (φ : A →ₗ[ℂ] ℂ) (_hφ : φ 1 = 1) {ι : Type*} (B : ι → Subalgebra ℂ A) :
    Prop :=
  ∀ (n : ℕ) (k : Fin (n + 1) → ι) (a : Fin (n + 1) → A),
    (∀ i : Fin n, k i.castSucc ≠ k i.succ) → (∀ i, a i ∈ B (k i)) → (∀ i, φ (a i) = 0) →
      φ (List.ofFn a).prod = 0

/-- **Free random variables.** In a noncommutative probability space (`φ 1 = 1`), a family of
elements `a : ι → A` is free with respect to `φ` if the unital subalgebras `ℂ⟨a i⟩` that they
generate are freely independent (Anderson, Guionnet and Zeitouni, *An Introduction to Random
Matrices* (manuscript numbering), Definition 5.3.1, last paragraph). -/
def AreFree (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) {ι : Type*} (a : ι → A) : Prop :=
  IsFreelyIndependent φ hφ fun i => Algebra.adjoin ℂ {a i}

/-- **A family with at most one member is free.** A word of length at least two would need two
distinct consecutive indices. -/
theorem IsFreelyIndependent.of_subsingleton (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) {ι : Type*}
    [Subsingleton ι] (B : ι → Subalgebra ℂ A) : IsFreelyIndependent φ hφ B := by
  intro n k a hk _ hφ
  rcases n with _ | n
  · simpa using hφ 0
  · exact absurd (Subsingleton.elim _ _) (hk 0)

/- A centred scalar is zero when `φ 1 = 1`. -/
theorem eq_zero_of_mem_bot {φ : A →ₗ[ℂ] ℂ} (hφ : φ 1 = 1) {x : A} (hx : x ∈ (⊥ : Subalgebra ℂ A))
    (h0 : φ x = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ, smul_eq_mul, mul_one] at h0
  rw [h0, map_zero]

/-- **Scalars are free from everything.** If every member of the family other than `B i₀` is the
algebra of scalars `⊥`, the family is freely independent: in a word of length at least two one of
the first two letters is a centred scalar, hence zero since `φ 1 = 1`. -/
theorem isFreelyIndependent_of_eq_bot {φ : A →ₗ[ℂ] ℂ} (hφ : φ 1 = 1) {ι : Type*}
    (B : ι → Subalgebra ℂ A) (i₀ : ι) (hB : ∀ i, i ≠ i₀ → B i = ⊥) :
    IsFreelyIndependent φ hφ B := by
  intro n k a hk ha hφa
  rcases n with _ | n
  · simpa using hφa 0
  · have hzero : ∃ t, a t = 0 := by
      by_cases h0 : k 0 = i₀
      · refine ⟨1, eq_zero_of_mem_bot hφ ?_ (hφa 1)⟩
        have h1 : k 1 ≠ i₀ := fun h => hk 0 (by simpa [h0] using h.symm)
        simpa [hB _ h1] using ha 1
      · exact ⟨0, eq_zero_of_mem_bot hφ (by simpa [hB _ h0] using ha 0) (hφa 0)⟩
    obtain ⟨t, ht⟩ := hzero
    rw [List.prod_eq_zero (List.mem_ofFn.2 ⟨t, ht⟩), map_zero]

/-- **Free variables are uncorrelated**: if `a ∈ B i` and `b ∈ B j` with `i ≠ j` in a freely
independent family, then `φ (a b) = φ a · φ b`. Apply the definition to the centred
elements `a - φ a` and `b - φ b` (Anderson, Guionnet and Zeitouni, *An Introduction to Random
Matrices*, Definition 5.3.1; the computation of mixed moments in Remark 5.3.2(ii)). -/
theorem IsFreelyIndependent.map_mul {φ : A →ₗ[ℂ] ℂ} (hφ : φ 1 = 1) {ι : Type*}
    {B : ι → Subalgebra ℂ A} (h : IsFreelyIndependent φ hφ B) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) : φ (a * b) = φ a * φ b := by
  set a' := a - φ a • (1 : A)
  set b' := b - φ b • (1 : A)
  have ha' : a' ∈ B i := sub_mem ha (Subalgebra.smul_mem _ (one_mem _) _)
  have hb' : b' ∈ B j := sub_mem hb (Subalgebra.smul_mem _ (one_mem _) _)
  have hca : φ a' = 0 := by simp [a', hφ]
  have hcb : φ b' = 0 := by simp [b', hφ]
  have h0 := h 1 ![i, j] ![a', b'] (fun k => by fin_cases k; simpa using hij)
    (fun k => by fin_cases k <;> simpa) (fun k => by fin_cases k <;> simpa)
  have hprod : (List.ofFn ![a', b']).prod = a' * b' := by simp
  rw [hprod] at h0
  have hexp : a' * b' = a * b - φ b • a - φ a • b + (φ a * φ b) • (1 : A) := by
    simp only [a', b', sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [smul_sub, smul_smul, mul_comm (φ b) (φ a)]
    abel
  rw [hexp] at h0
  simp only [map_add, map_sub, map_smul, hφ, smul_eq_mul, mul_one] at h0
  linear_combination h0

end MathlibExt.Probability.FreeProbability
