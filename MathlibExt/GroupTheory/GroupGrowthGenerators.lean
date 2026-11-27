/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.GroupGrowth
public import MathlibExt.GroupTheory.WordMetricComparison
public import Mathlib.Data.Set.Finite.List
public import MathlibExt.GroupTheory.IntWordMetric

/-!
# Polynomial growth does not depend on the finite generating set, and is a quasi-isometry invariant

Gromov, *Groups of polynomial growth and expanding maps*, Publ. Math. IHÉS 53 (1981), p. 54:
"One can easily see that this definition does not depend on the particular choice of the
generators and so this notion is correctly defined for the finitely generated groups." The proof is
the bi-Lipschitz comparison of word lengths (`MathlibExt.GroupTheory.WordMetricComparison`): a ball
of radius `n` for one finite generating family lies in the ball of radius `K n` for another.

## Main results

* `Group.Generators.growth_le_growth_mul`: `γ_P(n) ≤ γ_Q(K n)` for a finite family `P`.
* `Group.Generators.HasPolynomialGrowth.of_generators`: polynomial growth transfers from any
  generating family `Q` to every finite generating family `P`.
* `Group.Generators.hasPolynomialGrowth_iff`: for two finite generating families, polynomial
  growth for one is equivalent to polynomial growth for the other.
* `Group.Generators.HasPolynomialGrowth.of_quasiIsometricEmbedding`: if a finitely generated group
  `G` admits a quasi-isometric embedding (for the word metrics) into a group `H` of polynomial
  growth, then `G` has polynomial growth. In particular polynomial growth is invariant under
  quasi-isometry of finitely generated groups (Gromov, *Infinite groups as geometric objects*,
  Proc. ICM Warszawa 1983, §2.B: "the polynomial growth property ... is q.i. invariant").
* `Group.Generators.hasPolynomialGrowth_intGenerators`: the infinite cyclic group has polynomial
  growth (its balls have `2n + 1` elements).
-/

@[expose] public section

namespace Group.Generators

variable {G ι κ : Type*} [Group G]

/-- **Word balls of a finite generating family are finite.** If `P` is a finite generating family,
each ball `{g | |g|_P ≤ n}` is finite: it is the image of the finite set of words of length at
most `n`. -/
theorem finite_wordLength_le [Finite ι] (P : Generators G ι) (n : ℕ) :
    Finite {g : G // P.wordLength g ≤ n} := by
  have hS : {l : List (ι × Bool) | l.length ≤ n}.Finite := List.finite_length_le (ι × Bool) n
  have hsub : {g : G | P.wordLength g ≤ n} ⊆ P.wordProd '' {l | l.length ≤ n} := by
    intro g hg
    obtain ⟨l, hl, rfl⟩ := (P.wordLength_le_iff (g := g)).mp hg
    exact ⟨l, hl, rfl⟩
  exact ((hS.image _).subset hsub).to_subtype

/-- **Growth functions of two generating families dominate each other.** If `P` is a finite
generating family and the balls of `Q` are finite, there is `K : ℕ` with `γ_P(n) ≤ γ_Q(K n)` for
every `n`. -/
theorem growth_le_growth_mul [Finite ι] (P : Generators G ι) (Q : Generators G κ)
    (hQ : ∀ n, Finite {g : G // Q.wordLength g ≤ n}) :
    ∃ K : ℕ, ∀ n, P.growth n ≤ Q.growth (K * n) := by
  obtain ⟨K, hK⟩ := exists_wordLength_le_mul Q P
  refine ⟨K, fun n => ?_⟩
  have := hQ (K * n)
  exact Nat.card_le_card_of_injective
    (fun g => ⟨g.1, (hK g.1).trans (Nat.mul_le_mul_left K g.2)⟩)
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

/-- **Polynomial growth transfers between generating families.** If some generating family `Q` of
`G` has polynomial growth, then every finite generating family `P` has polynomial growth (Gromov,
*Groups of polynomial growth and expanding maps*, Publ. Math. IHÉS 53 (1981), p. 54). -/
theorem HasPolynomialGrowth.of_generators [Finite ι] (P : Generators G ι) {Q : Generators G κ}
    (hQ : Q.HasPolynomialGrowth) : P.HasPolynomialGrowth := by
  obtain ⟨hfin, C, d, hCd⟩ := hQ
  obtain ⟨K, hK⟩ := exists_wordLength_le_mul Q P
  have hinj : ∀ n, Function.Injective (fun g : {g : G // P.wordLength g ≤ n} =>
      (⟨g.1, (hK g.1).trans (Nat.mul_le_mul_left K g.2)⟩ : {g : G // Q.wordLength g ≤ K * n})) :=
    fun n a b h => Subtype.ext (by simpa using congrArg Subtype.val h)
  refine ⟨fun n => Finite.of_injective _ (hinj n), C * (K + 1) ^ d, d, fun n => ?_⟩
  have := hfin (K * n)
  have h1 : P.growth n ≤ Q.growth (K * n) := Nat.card_le_card_of_injective _ (hinj n)
  have h2 : K * n + 1 ≤ (K + 1) * (n + 1) := by nlinarith
  calc P.growth n ≤ Q.growth (K * n) := h1
    _ ≤ C * (K * n + 1) ^ d := hCd _
    _ ≤ C * ((K + 1) * (n + 1)) ^ d := by gcongr
    _ = C * (K + 1) ^ d * (n + 1) ^ d := by rw [mul_pow]; ring

/-- **Polynomial growth is independent of the finite generating set.** For two finite generating
families `P` and `Q` of `G`, `P` has polynomial growth if and only if `Q` does (Gromov, *Groups of
polynomial growth and expanding maps*, Publ. Math. IHÉS 53 (1981), p. 54). -/
theorem hasPolynomialGrowth_iff [Finite ι] [Finite κ] (P : Generators G ι)
    (Q : Generators G κ) : P.HasPolynomialGrowth ↔ Q.HasPolynomialGrowth :=
  ⟨fun h => HasPolynomialGrowth.of_generators Q h, fun h => HasPolynomialGrowth.of_generators P h⟩

/-- **Polynomial growth is a quasi-isometry invariant.** Let `P` and `Q` be finite generating
families of groups `G` and `H`, and let `f : G → H` be a quasi-isometric embedding for the
(left-invariant) word metrics: `|g⁻¹ g'|_P ≤ L |f(g)⁻¹ f(g')|_Q + C` and
`|f(g)⁻¹ f(g')|_Q ≤ L |g⁻¹ g'|_P + C` for all `g g'`. If `Q` has polynomial growth, so does `P`.
The map `f` need not be a homomorphism, injective or coarsely surjective. In particular
polynomial growth is invariant under quasi-isometry of finitely generated groups (Gromov,
*Infinite groups as geometric objects*, Proc. ICM Warszawa 1983, §2.B). -/
theorem HasPolynomialGrowth.of_quasiIsometricEmbedding {H κ' : Type*} [Group H] [Finite ι]
    (P : Generators G ι) (Q : Generators H κ') (f : G → H) {L C : ℝ}
    (hlow : ∀ g g' : G, (P.wordLength (g⁻¹ * g') : ℝ) ≤ L * Q.wordLength ((f g)⁻¹ * f g') + C)
    (hup : ∀ g g' : G, (Q.wordLength ((f g)⁻¹ * f g') : ℝ) ≤ L * P.wordLength (g⁻¹ * g') + C)
    (hQ : Q.HasPolynomialGrowth) : P.HasPolynomialGrowth := by
  classical
  obtain ⟨hfin, A, d, hAd⟩ := hQ
  set L' : ℕ := ⌈L⌉₊
  set C' : ℕ := ⌈C⌉₊
  -- a representative of each fibre of `f`
  let r : H → G := Function.invFun f
  have hr : ∀ g, f (r (f g)) = f g := fun g => Function.invFun_eq ⟨g, rfl⟩
  have hfib : ∀ g, P.wordLength ((r (f g))⁻¹ * g) ≤ C' := by
    intro g
    have h := hlow (r (f g)) g
    rw [hr, inv_mul_cancel, wordLength_one, Nat.cast_zero, mul_zero, zero_add] at h
    exact_mod_cast h.trans (Nat.le_ceil C)
  have hball : ∀ (n : ℕ) (g : G), P.wordLength g ≤ n →
      Q.wordLength ((f 1)⁻¹ * f g) ≤ L' * n + C' := by
    intro n g hg
    have h := hup 1 g
    rw [inv_one, one_mul] at h
    have hL : L ≤ L' := Nat.le_ceil L
    have hC : C ≤ C' := Nat.le_ceil C
    have hL0 : (0 : ℝ) ≤ L' := Nat.cast_nonneg _
    have hg' : (P.wordLength g : ℝ) ≤ n := by exact_mod_cast hg
    have : (Q.wordLength ((f 1)⁻¹ * f g) : ℝ) ≤ L' * n + C' := by
      have h1 : L * P.wordLength g ≤ L' * n := by
        rcases le_total 0 L with hL0' | hL0'
        · exact (mul_le_mul_of_nonneg_left hg' hL0').trans
            (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg n))
        · exact (mul_nonpos_of_nonpos_of_nonneg hL0' (Nat.cast_nonneg _)).trans
            (mul_nonneg hL0 (Nat.cast_nonneg n))
      linarith
    exact_mod_cast this
  have hinj : ∀ n : ℕ, Function.Injective (fun g : {g : G // P.wordLength g ≤ n} =>
      ((⟨(f 1)⁻¹ * f g.1, hball n g.1 g.2⟩ : {h : H // Q.wordLength h ≤ L' * n + C'}),
        (⟨(r (f g.1))⁻¹ * g.1, hfib g.1⟩ : {g : G // P.wordLength g ≤ C'}))) := by
    intro n a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have hf : f a.1 = f b.1 := mul_left_cancel h1
    rw [hf] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have := finite_wordLength_le P C'
  refine ⟨finite_wordLength_le P, A * P.growth C' * (L' + C' + 1) ^ d, d, fun n => ?_⟩
  have := hfin (L' * n + C')
  have h1 : P.growth n ≤ Q.growth (L' * n + C') * P.growth C' := by
    have := Nat.card_le_card_of_injective _ (hinj n)
    rwa [Nat.card_prod] at this
  have h2 : L' * n + C' + 1 ≤ (L' + C' + 1) * (n + 1) := by nlinarith
  calc P.growth n ≤ Q.growth (L' * n + C') * P.growth C' := h1
    _ ≤ A * (L' * n + C' + 1) ^ d * P.growth C' := Nat.mul_le_mul_right _ (hAd _)
    _ ≤ A * ((L' + C' + 1) * (n + 1)) ^ d * P.growth C' := by gcongr
    _ = A * P.growth C' * (L' + C' + 1) ^ d * (n + 1) ^ d := by rw [mul_pow]; ring

/-- **The infinite cyclic group has polynomial growth.** The ball of radius `n` of
`Multiplicative ℤ` for the generator `ofAdd 1` is finite with at most `2 (n + 1)` elements (it has
exactly `2n + 1`), so `intGenerators` has polynomial growth of degree `1`. -/
theorem hasPolynomialGrowth_intGenerators : intGenerators.HasPolynomialGrowth := by
  have hinj : ∀ n : ℕ, Function.Injective
      (fun g : {g : Multiplicative ℤ // intGenerators.wordLength g ≤ n} =>
        (⟨(Multiplicative.toAdd g.1 + n).toNat, by
          have h := g.2
          rw [← ofAdd_toAdd g.1, wordLength_intGenerators] at h
          omega⟩ : Fin (2 * n + 1))) := by
    intro n a b hab
    have ha := a.2
    have hb := b.2
    rw [← ofAdd_toAdd a.1, wordLength_intGenerators] at ha
    rw [← ofAdd_toAdd b.1, wordLength_intGenerators] at hb
    simp only [Fin.mk.injEq] at hab
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    omega
  refine ⟨fun n => Finite.of_injective _ (hinj n), 2, 1, fun n => ?_⟩
  calc intGenerators.growth n ≤ Nat.card (Fin (2 * n + 1)) :=
        Nat.card_le_card_of_injective _ (hinj n)
    _ ≤ 2 * (n + 1) ^ 1 := by rw [Nat.card_fin, pow_one]; omega

end Group.Generators
