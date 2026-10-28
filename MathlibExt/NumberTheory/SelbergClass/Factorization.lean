/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Primitive
import MathlibExt.NumberTheory.SelbergClass.Degree
import MathlibExt.NumberTheory.SelbergClass.DegreeBound
import MathlibExt.NumberTheory.SelbergClass.DegreeZero

/-!
# Factorization into primitive functions in the Selberg class

The degree of a functional equation is additive on products, is `0` only for the trivial
function `1` (Conrey–Ghosh), and is otherwise at least `1` (Selberg). Hence a nontrivial member
of `𝒮` cannot be split into nontrivial factors indefinitely, and induction on the degree shows
that it is a finite product of primitive functions.

## Main statements

* `SelbergClass.one_le_degree_of_ne_one`: a member `a ≠ 1` of `𝒮` has degree at least `1`.
* `SelbergClass.exists_multiset_prod_eq`: every `a ∈ 𝒮` with `a ≠ 1` is a finite product of
  primitive members of `𝒮`.
-/

open ArithmeticFunction

@[expose] public section

namespace SelbergClass

/-- The degree of a functional equation is nonnegative. -/
theorem FunctionalEquation.degree_nonneg {F : ℂ → ℂ} (D : FunctionalEquation F) :
    0 ≤ D.degree := by
  unfold FunctionalEquation.degree
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (D.α_pos i).le)
  linarith

/-- A member `a ≠ 1` of the Selberg class has degree at least `1`, for every functional
equation of its continuation. -/
theorem one_le_degree_of_ne_one {b : ArithmeticFunction ℂ} (hb : b ∈ selbergClass) (hb1 : b ≠ 1)
    {F : ℂ → ℂ} (hF : IsLSeriesContinuation b F) (D : FunctionalEquation F) :
    1 ≤ D.degree := by
  refine one_le_degree_of_pos b hb F hF D ?_
  rcases D.degree_nonneg.lt_or_eq with h | h
  · exact h
  · exact absurd (eq_one_of_degree_eq_zero hb hF D h.symm) hb1

/-- **Factorization into primitives.** Every `a ∈ 𝒮` with `a ≠ 1` is a finite product (for
Dirichlet convolution, i.e. the product of `L`-functions) of primitive members of `𝒮`. -/
theorem exists_multiset_prod_eq {a : ArithmeticFunction ℂ} (ha : a ∈ selbergClass)
    (ha1 : a ≠ 1) :
    ∃ l : Multiset (ArithmeticFunction ℂ), (∀ g ∈ l, IsSelbergPrimitive g) ∧ l.prod = a := by
  have key : ∀ n : ℕ, ∀ a ∈ selbergClass, a ≠ 1 → ∀ (F : ℂ → ℂ), IsLSeriesContinuation a F →
      ∀ D : FunctionalEquation F, D.degree < n →
      ∃ l : Multiset (ArithmeticFunction ℂ), (∀ g ∈ l, IsSelbergPrimitive g) ∧ l.prod = a := by
    intro n
    induction n with
    | zero =>
      intro a _ _ F _ D hD
      exact absurd hD (by simpa using D.degree_nonneg)
    | succ n ih =>
      intro a ha ha1 F hF D hD
      by_cases hp : IsSelbergPrimitive a
      · exact ⟨{a}, by simpa using hp, by simp⟩
      · have : ∃ b ∈ selbergClass, ∃ c ∈ selbergClass, a = b * c ∧ b ≠ 1 ∧ c ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hp ⟨ha, ha1, fun b hb c hc h => by
            by_contra hbc
            push Not at hbc
            exact hbc.2 (hcon b hb c hc h hbc.1)⟩
        obtain ⟨b, hb, c, hc, rfl, hb1, hc1⟩ := this
        obtain ⟨_, ⟨Fb, hFb, _, ⟨Db⟩⟩, _⟩ := id hb
        obtain ⟨_, ⟨Fc, hFc, _, ⟨Dc⟩⟩, _⟩ := id hc
        have hsum := FunctionalEquation.degree_eq_add_of_mul b c hb hc Fb Fc F hFb hFc hF Db Dc D
        have h1 := one_le_degree_of_ne_one hb hb1 hFb Db
        have h2 := one_le_degree_of_ne_one hc hc1 hFc Dc
        push_cast at hD
        obtain ⟨lb, hlb, hpb⟩ := ih b hb hb1 Fb hFb Db (by linarith)
        obtain ⟨lc, hlc, hpc⟩ := ih c hc hc1 Fc hFc Dc (by linarith)
        refine ⟨lb + lc, fun g hg => ?_, by simp [hpb, hpc]⟩
        rcases Multiset.mem_add.mp hg with h | h
        · exact hlb g h
        · exact hlc g h
  obtain ⟨_, ⟨F, hF, _, ⟨D⟩⟩, _⟩ := id ha
  obtain ⟨n, hn⟩ := exists_nat_gt D.degree
  exact key n a ha ha1 F hF D hn

end SelbergClass
