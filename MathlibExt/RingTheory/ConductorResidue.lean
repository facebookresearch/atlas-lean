/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Residue rings at primes avoiding a denominator-clearing ideal

Let `O → B` be a commutative-ring algebra, `q` a maximal ideal of `B`, and `c` an
ideal of `B` not contained in `q`. Suppose elements of `c` clear arbitrary elements
of `B` back into the image of `O`:

  `hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b`.

Then the canonical map induces an isomorphism
`O ⧸ q.comap (algebraMap O B) ≃+* B ⧸ q`, with consequences for `Nat.card` and
`Submodule.cardQuot`.

This is the prime-local slice of ATLAS `NumberTheoryI` Proposition 6.32, stated for
an arbitrary commutative-ring algebra rather than for orders in a number field. It
generalizes the monogenic case `Ideal.quotAdjoinEquivQuotMap`, where the
denominator-clearing ideal is the conductor of a single adjoined element.
-/

@[expose] public section

noncomputable section

namespace Ideal

variable {O B : Type*} [CommRing O] [CommRing B] [Algebra O B]
variable (q : Ideal B) [q.IsMaximal] (c : Ideal B)

/-- **Residue-ring isomorphism away from a denominator-clearing ideal.** Let $B$ be an algebra
over $O$, where $O$ and $B$ are commutative rings, with structure map $\varphi : O \to B$. Let
$\mathfrak q$ be a maximal ideal of $B$ and let $\mathfrak c$ be an ideal of $B$ with
$\mathfrak c \not\subseteq \mathfrak q$ such that for every $x \in \mathfrak c$ and every $b \in B$
there is $o \in O$ with $\varphi(o) = xb$. This is the ring isomorphism
$O / \varphi^{-1}(\mathfrak q) \to B / \mathfrak q$ induced by $\varphi$, which sends the class of
$o \in O$ to the class of $\varphi(o)$. -/
def quotient_coprime_residue_equiv (hc : ¬ c ≤ q)
    (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
    O ⧸ q.comap (algebraMap O B) ≃+* B ⧸ q := by
  refine RingEquiv.ofBijective (Ideal.quotientMap q (algebraMap O B) le_rfl)
    ⟨Ideal.quotientMap_injective, ?_⟩
  obtain ⟨s, hs_mem, hs_notin⟩ := SetLike.not_le_iff_exists.mp hc
  obtain ⟨a₀, q₀, hq₀, ha₀⟩ := (inferInstance : q.IsMaximal).exists_inv hs_notin
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨o, ho⟩ := hclear s hs_mem (b * a₀)
  refine ⟨Ideal.Quotient.mk _ o, ?_⟩
  simp only [Ideal.quotientMap_mk]
  rw [Ideal.Quotient.eq]
  have h1 : s * a₀ = 1 - q₀ := by linear_combination ha₀
  have hkey : algebraMap O B o - b = -(b * q₀) := by
    calc algebraMap O B o - b = s * (b * a₀) - b := by rw [ho]
      _ = b * (s * a₀) - b := by ring
      _ = b * (1 - q₀) - b := by rw [h1]
      _ = -(b * q₀) := by ring
  rw [hkey]
  exact q.neg_mem (q.mul_mem_left b hq₀)

/-- **The residue-ring isomorphism on residue classes.** Let $B$ be an algebra over $O$, where
$O$ and $B$ are commutative rings, with structure map $\varphi : O \to B$. Let $\mathfrak q$ be a
maximal ideal of $B$ and let $\mathfrak c$ be an ideal of $B$ with
$\mathfrak c \not\subseteq \mathfrak q$ such that for every $x \in \mathfrak c$ and every $b \in B$
there is $o \in O$ with $\varphi(o) = xb$. Then for every $o \in O$, the residue-ring isomorphism
$O / \varphi^{-1}(\mathfrak q) \cong B / \mathfrak q$ sends the class of $o$ to the class of
$\varphi(o)$. -/
@[simp]
theorem quotient_coprime_residue_equiv_apply_mk (hc : ¬ c ≤ q)
    (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) (o : O) :
    quotient_coprime_residue_equiv q c hc hclear (Ideal.Quotient.mk _ o) =
      Ideal.Quotient.mk _ (algebraMap O B o) :=
  rfl

/-- **Equal cardinality of residue rings away from a denominator-clearing ideal.** Let $B$ be an
algebra over $O$, where $O$ and $B$ are commutative rings, with structure map
$\varphi : O \to B$. Let $\mathfrak q$ be a maximal ideal of $B$ and let $\mathfrak c$ be an
ideal of $B$ with $\mathfrak c \not\subseteq \mathfrak q$ such that for every $x \in \mathfrak c$
and every $b \in B$ there is $o \in O$ with $\varphi(o) = xb$. Then
$O / \varphi^{-1}(\mathfrak q)$ and $B / \mathfrak q$ have the same cardinality, where the
cardinality of an infinite set is taken to be $0$. -/
theorem nat_card_quotient_coprime_residue_eq (hc : ¬ c ≤ q)
    (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
    Nat.card (O ⧸ q.comap (algebraMap O B)) = Nat.card (B ⧸ q) :=
  Nat.card_congr (quotient_coprime_residue_equiv q c hc hclear).toEquiv

/-- **Equal ideal indices away from a denominator-clearing ideal.** Let $B$ be an algebra over
$O$, where $O$ and $B$ are commutative rings, with structure map $\varphi : O \to B$. Let
$\mathfrak q$ be a maximal ideal of $B$ and let $\mathfrak c$ be an ideal of $B$ with
$\mathfrak c \not\subseteq \mathfrak q$ such that for every $x \in \mathfrak c$ and every $b \in B$
there is $o \in O$ with $\varphi(o) = xb$. Then the index of $\varphi^{-1}(\mathfrak q)$ in $O$
equals the index of $\mathfrak q$ in $B$, where the index of an ideal is the number of elements of
the quotient, taken to be $0$ when the quotient is infinite. -/
theorem cardQuot_coprime_residue_eq (hc : ¬ c ≤ q)
    (hclear : ∀ x ∈ c, ∀ b : B, ∃ o : O, algebraMap O B o = x * b) :
    Submodule.cardQuot (q.comap (algebraMap O B) : Submodule O O) =
      Submodule.cardQuot (q : Submodule B B) := by
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (quotient_coprime_residue_equiv q c hc hclear).toEquiv

end Ideal
