/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Group.WordMetric

/-!
# Changing the finite generating set of a word metric

If `P` and `Q` are generating families of a group `G` and `Q` is finite, every `Q`-word of length
`n` can be rewritten as a `P`-word of length at most `K n`, where `K` is the largest `P`-length of
a generator in `Q`. Hence two finite generating families give word lengths, and therefore word
metrics, that are bi-Lipschitz equivalent (Gromov, *Groups of polynomial growth and expanding
maps*, Publ. Math. IHÉS 53 (1981), p. 53, "Elementary properties of the norm"; *Asymptotic
invariants of infinite groups*, 1993, §0.2.C, Example).

## Main results

* `Group.Generators.wordLength_wordProd_le_mul`: a `Q`-word of length `n` has `P`-length at most
  `K n`.
* `Group.Generators.exists_wordLength_le_mul`: for finite `Q`, `|g|_P ≤ K |g|_Q`.
* `Group.Generators.exists_wordLength_bilipschitz`: for finite `P` and `Q`, the two word lengths
  are bi-Lipschitz equivalent.
* `Group.Generators.exists_wordLength_le_mul_of_monoidHom`: a homomorphism between groups with
  generating families, the source one finite, is Lipschitz for the word lengths.
-/

@[expose] public section

namespace Group.Generators

variable {G H ι κ : Type*} [Group G] [Group H]

/-- **Rewriting a word in another generating family.** If every generator `Q.val k` has
`P`-length at most `K`, then the element represented by a `Q`-word `l` has `P`-length at most
`K * l.length`. -/
theorem wordLength_wordProd_le_mul (P : Generators G ι) (Q : Generators G κ) (K : ℕ)
    (hK : ∀ k, P.wordLength (Q.val k) ≤ K) (l : List (κ × Bool)) :
    P.wordLength (Q.wordProd l) ≤ K * l.length := by
  induction l with
  | nil => simp [wordProd_nil]
  | cons a l ih =>
    obtain ⟨k, b⟩ := a
    rw [wordProd_cons, List.length_cons]
    calc P.wordLength (cond b (Q.val k) (Q.val k)⁻¹ * Q.wordProd l)
        ≤ P.wordLength (cond b (Q.val k) (Q.val k)⁻¹) + P.wordLength (Q.wordProd l) :=
          P.wordLength_mul_le _ _
      _ ≤ K + K * l.length := by
          gcongr
          cases b <;> simp [hK]
      _ = K * (l.length + 1) := by ring

/-- **Word lengths of two generating families are comparable.** If `Q` is a finite generating
family, there is `K : ℕ` with `|g|_P ≤ K |g|_Q` for every `g : G` (Gromov, *Groups of polynomial
growth and expanding maps*, Publ. Math. IHÉS 53 (1981), p. 53). -/
theorem exists_wordLength_le_mul [Finite κ] (P : Generators G ι) (Q : Generators G κ) :
    ∃ K : ℕ, ∀ g : G, P.wordLength g ≤ K * Q.wordLength g := by
  have := Fintype.ofFinite κ
  refine ⟨Finset.univ.sup fun k => P.wordLength (Q.val k), fun g => ?_⟩
  obtain ⟨l, hl, rfl⟩ := Q.exists_isGeodesic g
  rw [show Q.wordLength (Q.wordProd l) = l.length from hl]
  exact wordLength_wordProd_le_mul P Q _ (fun k => Finset.le_sup (f := fun k =>
    P.wordLength (Q.val k)) (Finset.mem_univ k)) l

/-- **Change of finite generating set is bi-Lipschitz.** For two finite generating families `P`
and `Q` of `G` there is `K ≥ 1` with `|g|_P ≤ K |g|_Q` and `|g|_Q ≤ K |g|_P` for every `g`; since
the word metric is `d(g, h) = |g⁻¹ h|`, the identity of `G` is a `K`-bi-Lipschitz map between the
two word metrics (Gromov, *Groups of polynomial growth and expanding maps*, Publ. Math. IHÉS 53
(1981), p. 53: `C⁻¹ ‖γ‖_old ≤ ‖γ‖_new ≤ C ‖γ‖_old`). -/
theorem exists_wordLength_bilipschitz [Finite ι] [Finite κ] (P : Generators G ι)
    (Q : Generators G κ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ g : G, P.wordLength g ≤ K * Q.wordLength g ∧
      Q.wordLength g ≤ K * P.wordLength g := by
  obtain ⟨K₁, h₁⟩ := exists_wordLength_le_mul P Q
  obtain ⟨K₂, h₂⟩ := exists_wordLength_le_mul Q P
  refine ⟨max 1 (max K₁ K₂), le_max_left _ _, fun g => ⟨?_, ?_⟩⟩
  · exact (h₁ g).trans (Nat.mul_le_mul_right _ ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (h₂ g).trans (Nat.mul_le_mul_right _ ((le_max_right _ _).trans (le_max_right _ _)))

/-- **Images of words under a homomorphism.** If `φ : G →* H` sends every generator `Q.val k` to
an element of `P`-length at most `K`, then `φ` of the element represented by a `Q`-word `l` has
`P`-length at most `K * l.length`. -/
theorem wordLength_map_wordProd_le_mul (P : Generators H ι) (Q : Generators G κ) (φ : G →* H)
    (K : ℕ) (hK : ∀ k, P.wordLength (φ (Q.val k)) ≤ K) (l : List (κ × Bool)) :
    P.wordLength (φ (Q.wordProd l)) ≤ K * l.length := by
  induction l with
  | nil => simp [wordProd_nil]
  | cons a l ih =>
    obtain ⟨k, b⟩ := a
    rw [wordProd_cons, map_mul, List.length_cons]
    calc P.wordLength (φ (cond b (Q.val k) (Q.val k)⁻¹) * φ (Q.wordProd l))
        ≤ P.wordLength (φ (cond b (Q.val k) (Q.val k)⁻¹)) + P.wordLength (φ (Q.wordProd l)) :=
          P.wordLength_mul_le _ _
      _ ≤ K + K * l.length := by
          gcongr
          cases b <;> simp [hK]
      _ = K * (l.length + 1) := by ring

/-- **Homomorphisms are Lipschitz for word lengths.** If `φ : G →* H`, `Q` is a finite generating
family of `G` and `P` any generating family of `H`, there is `K : ℕ` with
`|φ g|_P ≤ K |g|_Q` for every `g : G` (Gromov, *Asymptotic invariants of infinite groups*, 1993,
§0.2.C: "every homomorphism between finitely generated groups is Lipschitz"). -/
theorem exists_wordLength_le_mul_of_monoidHom [Finite κ] (P : Generators H ι)
    (Q : Generators G κ) (φ : G →* H) :
    ∃ K : ℕ, ∀ g : G, P.wordLength (φ g) ≤ K * Q.wordLength g := by
  have := Fintype.ofFinite κ
  refine ⟨Finset.univ.sup fun k => P.wordLength (φ (Q.val k)), fun g => ?_⟩
  obtain ⟨l, hl, rfl⟩ := Q.exists_isGeodesic g
  rw [show Q.wordLength (Q.wordProd l) = l.length from hl]
  exact wordLength_map_wordProd_le_mul P Q φ _ (fun k => Finset.le_sup (f := fun k =>
    P.wordLength (φ (Q.val k))) (Finset.mem_univ k)) l

end Group.Generators
