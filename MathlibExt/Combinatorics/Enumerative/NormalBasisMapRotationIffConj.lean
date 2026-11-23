/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import MathlibExt.Combinatorics.Enumerative.TupleRotationOrbit
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Rotation orbits of normal basis coordinates and conjugate elements

Let `K` be a finite field extension of a finite field `F` with `q` elements, let `n = [K : F]`,
and let `β ∈ K` be such that `β, β ^ q, …, β ^ (q ^ (n - 1))` are linearly independent over `F`.
The map `Φ : F^n → K`, `Φ a = ∑ i, a i • β ^ (q ^ i)`, sends two tuples to elements with the same
minimal polynomial over `F` exactly when the tuples lie in the same rotation orbit
(`tupleRotationOrbit`). This is Corollary 9.5 of the arXiv text of Darij Grinberg and Peter Mao,
*Necklaces over a Group with Identity Product* (arXiv:2405.08937v4), published in the Journal of
Integer Sequences 29 (2026), Article 26.4.6.

The proof follows theirs. The Frobenius automorphism `x ↦ x ^ q` of `K` over `F` shifts the
coordinates of `Φ` by one step, because `β ^ (q ^ n) = β`; so the `m`-th power of the Frobenius
sends `Φ (a ∘ finRotate n ^ m)` to `Φ a`. The powers of the Frobenius are all the automorphisms of
`K` over `F` (`FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`), two elements of the
normal extension `K` have the same minimal polynomial exactly when an automorphism sends one to the
other (`isConjRoot_iff_exists_algEquiv`), and `Φ` is injective because the family is linearly
independent. The statement does not assume that `K` is finite: when `n > 0`, `K` is a
finite-dimensional vector space over the finite field `F`, hence finite, and when `n = 0` the only
tuple is the empty one and both sides of the equivalence hold.

## Main statements

* `MetaMathlibExt.normalBasisMap_rotation_iff_conj`: `b` lies in the rotation orbit of `a` if
  and only if `Φ a` and `Φ b` have the same minimal polynomial over `F`.
-/

namespace MetaMathlibExt

section FiniteField

variable (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K]

namespace normalBasisMap_rotation_iff_conj

/-- The Frobenius `x ↦ x ^ q` sends the image of a tuple rotated one step back to the image of the
tuple. -/
private theorem frobenius_comp_finRotate [Finite K] (n : ℕ) (hn : Module.finrank F K = n)
    (β : K) (a : Fin n → F) :
    FiniteField.frobeniusAlgEquivOfAlgebraic F K
        (∑ i, (a ∘ ⇑(finRotate n)) i • β ^ (Fintype.card F ^ (i : ℕ))) =
      ∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ)) := by
  have := Fintype.ofFinite K
  have hβ : β ^ (Fintype.card F ^ n) = β := by
    rw [← hn, ← Module.card_eq_pow_finrank, FiniteField.pow_card]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (hn ▸ Module.finrank_pos.ne')
  rw [map_sum, ← Equiv.sum_comp (finRotate (m + 1))
    (fun i => a i • β ^ (Fintype.card F ^ (i : ℕ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, Function.comp_apply, ← pow_mul,
    ← pow_succ, coe_finRotate]
  split_ifs with h
  · subst h
    simp [hβ]
  · rfl

/-- The `m`-th power of the Frobenius sends the image of a tuple rotated `m` steps back to the
image of the tuple. -/
private theorem frobenius_pow_comp_finRotate_pow [Finite K] (n : ℕ)
    (hn : Module.finrank F K = n) (β : K) (a : Fin n → F) (m : ℕ) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ m)
        (∑ i, (a ∘ ⇑(finRotate n ^ m)) i • β ^ (Fintype.card F ^ (i : ℕ))) =
      ∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, AlgEquiv.mul_apply, Equiv.Perm.coe_mul, ← Function.comp_assoc,
      frobenius_comp_finRotate F K n hn β, ih]

/-- The coordinate map of a linearly independent family is injective. -/
private theorem normalBasisMap_injective (n : ℕ) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ)))) :
    Function.Injective (fun a : Fin n → F => ∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) := by
  intro a b hab
  have h := Fintype.linearIndependent_iff.mp hβ (a - b) (by
    simpa [sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using hab)
  funext i
  exact sub_eq_zero.mp (h i)

end normalBasisMap_rotation_iff_conj

open normalBasisMap_rotation_iff_conj

/-- **Rotation orbits correspond to conjugate elements.** Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then for all
$a, b \in F^n$, the tuple $b$ lies in the rotation orbit of $a$ if and only if $\Phi(a)$ and
$\Phi(b)$ have the same minimal polynomial over $F$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 29
(`jis-2026-26.4.6-cor-29`). -/
public theorem normalBasisMap_rotation_iff_conj (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ))))
    (a b : Fin n → F) :
    b ∈ tupleRotationOrbit a ↔
      minpoly F (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) =
        minpoly F (∑ i, b i • β ^ (Fintype.card F ^ (i : ℕ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · obtain rfl := Subsingleton.elim a b
    exact iff_of_true (self_mem_tupleRotationOrbit a) rfl
  have : Module.Finite F K := Module.finite_of_finrank_pos (hn ▸ hpos)
  have : Finite K := Module.finite_of_finite F
  constructor
  · rintro ⟨m, rfl⟩
    rw [← frobenius_pow_comp_finRotate_pow F K n hn β a m, minpoly.algEquiv_eq]
  · intro h
    obtain ⟨σ, hσ⟩ := (isConjRoot_iff_exists_algEquiv (K := F)).mp h
    obtain ⟨m, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).2 σ
    refine ⟨m, normalBasisMap_injective F K n β hβ <|
      (FiniteField.frobeniusAlgEquivOfAlgebraic F K ^ (m : ℕ)).injective ?_⟩
    rw [frobenius_pow_comp_finRotate_pow F K n hn β a m]
    exact hσ

end FiniteField

end MetaMathlibExt
