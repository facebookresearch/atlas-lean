/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 351, Logic 352

/-!
# Equal mod finite; $P(\omega)\slash \textrm{fin}$ automorphism

## References

* Jech (for `EqModFinite`, `IsPowModFiniteAutomorphism`)
-/

namespace MetaMathlibExt

-- Logic 351: Equal mod finite

/-- **Equality modulo finite sets.** Subsets $A$ and $B$ of $\mathbb{N}$ are *equal modulo finite*,
written $A =^{\ast} B$, if their symmetric difference $A \mathbin{\triangle} B$ is finite. -/
def EqModFinite (A B : Set ℕ) : Prop := (symmDiff A B).Finite

-- Logic 352: $P(\omega)\slash \textrm{fin}$ automorphism

/-- **Automorphisms of P(ω)/fin on representatives.** For subsets $A$, $B$ of $\mathbb{N}$, write
$A =^{\ast} B$ when their symmetric difference is finite. A map $\Phi$ from subsets of
$\mathbb{N}$ to subsets of $\mathbb{N}$ presents an automorphism of $P(\omega)/\mathrm{fin}$ if for
all subsets $A$, $B$ of $\mathbb{N}$: it respects $=^{\ast}$ ($A =^{\ast} B$ implies
$\Phi(A) =^{\ast} \Phi(B)$), it preserves meets ($\Phi(A \cap B) =^{\ast} \Phi(A) \cap \Phi(B)$)
and complements ($\Phi(\mathbb{N} \setminus A) =^{\ast} \mathbb{N} \setminus \Phi(A)$), it is
one-to-one modulo finite ($\Phi(A) =^{\ast} \Phi(B)$ implies $A =^{\ast} B$), and it is onto
modulo finite (for every $B$ there is $A$ with $\Phi(A) =^{\ast} B$).
-/
structure IsPowModFiniteAutomorphism (Φ : Set ℕ → Set ℕ) : Prop where
  respects : ∀ A B : Set ℕ, EqModFinite A B → EqModFinite (Φ A) (Φ B)
  inter : ∀ A B : Set ℕ, EqModFinite (Φ (A ∩ B)) (Φ A ∩ Φ B)
  compl : ∀ A : Set ℕ, EqModFinite (Φ Aᶜ) (Φ A)ᶜ
  injective : ∀ A B : Set ℕ, EqModFinite (Φ A) (Φ B) → EqModFinite A B
  surjective : ∀ B : Set ℕ, ∃ A : Set ℕ, EqModFinite (Φ A) B

end MetaMathlibExt

end
