/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Induction
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The word-length filtration of a universal enveloping algebra

Let R be a commutative ring and L an R-Lie algebra. For a finite list
x₁,…,xₙ in L, let w(x₁,…,xₙ) = ι(x₁) ⋯ ι(xₙ) in U_R(L),
with the empty word equal to 1. The stage F_p is the R-span of words
of length at most p.

The filtration is increasing, has F_0 = R·1 and contains every scalar
in every stage. It is multiplicative: F_p F_q ⊆ F_(p+q), and exhaustive:
every element of U_R(L) lies in some F_p.
The defining commutator satisfies
ι(x)ι(y)−ι(y)ι(x) = ι([x,y]) ∈ F_1.
These properties apply to arbitrary R-Lie algebras and retain the
independent scalar and Lie-carrier worlds.
-/

@[expose] public section

universe u v

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

attribute [local instance] LieRing.ofAssociativeRing

/-- For a commutative ring R, an R-Lie algebra L and a list
x₁,…,xₙ in L, its enveloping word is
ι(x₁) ⋯ ι(xₙ) ∈ U_R(L), in the given order.
The empty word has value 1, and concatenation multiplies word values. -/
def word (xs : List L) : UniversalEnvelopingAlgebra R L :=
  (xs.map (ι R)).prod

@[simp]
theorem word_nil : word R L [] = 1 := rfl

@[simp]
theorem word_cons (x : L) (xs : List L) :
    word R L (x :: xs) = ι R x * word R L xs := rfl

@[simp]
theorem word_append (xs ys : List L) :
    word R L (xs ++ ys) = word R L xs * word R L ys := by
  simp only [word, List.map_append, List.prod_append]

/-- For a commutative ring R and an R-Lie algebra L, F_p is
the R-submodule of U_R(L) spanned by all products
ι(x₁) ⋯ ι(xₙ) with n ≤ p. The index p is a nonnegative integer. -/
def degreeFiltration (p : ℕ) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  Submodule.span R {a | ∃ xs : List L, xs.length ≤ p ∧ word R L xs = a}

theorem word_mem_degreeFiltration (xs : List L) (p : ℕ) (hp : xs.length ≤ p) :
    word R L xs ∈ degreeFiltration R L p :=
  Submodule.subset_span ⟨xs, hp, rfl⟩

theorem degreeFiltration_mono : Monotone (degreeFiltration R L) := by
  intro p q hpq
  apply Submodule.span_mono
  rintro a ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans hpq, rfl⟩

theorem one_mem_degreeFiltration (p : ℕ) :
    (1 : UniversalEnvelopingAlgebra R L) ∈ degreeFiltration R L p := by
  simpa only [word_nil] using
    word_mem_degreeFiltration R L [] p (Nat.zero_le p)

theorem ι_mem_degreeFiltration (x : L) :
    ι R x ∈ degreeFiltration R L 1 := by
  simpa only [word_cons, word_nil, mul_one] using
    word_mem_degreeFiltration R L [x] 1 (le_refl 1)

/-- For a commutative ring R and an R-Lie algebra L, the
word-length filtration satisfies F_0 = R·1 inside U_R(L).
Its only generating word at length zero is the empty word. -/
theorem degreeFiltration_zero :
    degreeFiltration R L 0 = R ∙ (1 : UniversalEnvelopingAlgebra R L) := by
  have hs : {a : UniversalEnvelopingAlgebra R L |
      ∃ xs : List L, xs.length ≤ 0 ∧ word R L xs = a} = {1} := by
    ext a
    constructor
    · rintro ⟨xs, hxs, rfl⟩
      have hnil : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hxs)
      subst xs
      rfl
    · intro ha
      have ha' : a = 1 := Set.mem_singleton_iff.mp ha
      subst a
      exact ⟨[], le_rfl, rfl⟩
  rw [degreeFiltration, hs]

theorem algebraMap_mem_degreeFiltration (p : ℕ) (r : R) :
    algebraMap R (UniversalEnvelopingAlgebra R L) r ∈ degreeFiltration R L p := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (degreeFiltration R L p).smul_mem r (one_mem_degreeFiltration R L p)

/-- For a commutative ring R and an R-Lie algebra L, if
a ∈ F_p and b ∈ F_q in the word-length filtration of U_R(L),
then ab ∈ F_(p+q). Multiplication retains the order of the
two generator words before concatenating them. -/
theorem mul_mem_degreeFiltration {p q : ℕ}
    {a b : UniversalEnvelopingAlgebra R L}
    (ha : a ∈ degreeFiltration R L p) (hb : b ∈ degreeFiltration R L q) :
    a * b ∈ degreeFiltration R L (p + q) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨xs, hxs, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨ys, hys, rfl⟩ := hb
          rw [← word_append]
          exact word_mem_degreeFiltration R L (xs ++ ys) (p + q)
            (by simpa only [List.length_append] using Nat.add_le_add hxs hys)
      | zero =>
          rw [mul_zero]
          exact (degreeFiltration R L (p + q)).zero_mem
      | add b c hb hc ihb ihc =>
          rw [mul_add]
          exact (degreeFiltration R L (p + q)).add_mem ihb ihc
      | smul r b hb ih =>
          rw [mul_smul_comm]
          exact (degreeFiltration R L (p + q)).smul_mem r ih
  | zero =>
      rw [zero_mul]
      exact (degreeFiltration R L (p + q)).zero_mem
  | add a c ha hc iha ihc =>
      rw [add_mul]
      exact (degreeFiltration R L (p + q)).add_mem iha ihc
  | smul r a ha ih =>
      rw [smul_mul_assoc]
      exact (degreeFiltration R L (p + q)).smul_mem r ih

/-- For a commutative ring R, an R-Lie algebra L and
a ∈ U_R(L), there exists p ≥ 0 with a ∈ F_p, the R-span of
generator words of length at most p. Thus the increasing
word-length filtration is exhaustive. -/
theorem degreeFiltration_exhaustive (a : UniversalEnvelopingAlgebra R L) :
    ∃ p : ℕ, a ∈ degreeFiltration R L p := by
  induction a using UniversalEnvelopingAlgebra.induction R L with
  | algebraMap r =>
      exact ⟨0, algebraMap_mem_degreeFiltration R L 0 r⟩
  | ι x =>
      exact ⟨1, ι_mem_degreeFiltration R L x⟩
  | mul a b ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p + q, mul_mem_degreeFiltration R L hp hq⟩
  | add a b ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨max p q, (degreeFiltration R L (max p q)).add_mem
        (degreeFiltration_mono R L (le_max_left p q) hp)
        (degreeFiltration_mono R L (le_max_right p q) hq)⟩

/-- For a commutative ring R, an R-Lie algebra L and x,y ∈ L,
the identity ι(x)ι(y)−ι(y)ι(x) = ι([x,y]) holds in U_R(L).
In particular this commutator belongs to the first stage F_1
of the word-length filtration. -/
theorem ι_mul_sub_mul_ι (x y : L) :
    ι R x * ι R y - ι R y * ι R x = ι R ⁅x, y⁆ := by
  simpa only [LieRing.of_associative_ring_bracket] using
    ((ι R (L := L)).map_lie x y).symm

theorem ι_commutator_mem_degreeFiltration (x y : L) :
    ι R x * ι R y - ι R y * ι R x ∈ degreeFiltration R L 1 := by
  rw [ι_mul_sub_mul_ι]
  exact ι_mem_degreeFiltration R L ⁅x, y⁆

end UniversalEnvelopingAlgebra
