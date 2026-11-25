/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_MazurAdmissible_GaloisModule.lean`,
`Theorems/Thm_MazurAdmissible_natCard_eq_pow_filtLength.lean`
and
`P2M/Sol/S_MazurAdmissible_natCard_eq_pow_filtLength.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Mazur-admissible Galois modules

This file states Mazur's admissible filtrations of a Galois module (Mazur, *Modular curves and
the Eisenstein ideal*, Chapter I, §1 (f)) as the upstream formalization credited above states
them in `Definitions/Def_MazurAdmissible_GaloisModule.lean`, and proves that such a filtration
determines the order of the module.

Throughout, the absolute Galois group of `ℚ` is `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`
with its Krull topology, and `M` is an additive commutative group with an action
`Φ : OpenAction M` of it whose kernel is open, so that the action factors through the Galois
group of a finite extension of `ℚ`.

* `AdmissibleChain p Φ` is a chain of subgroups `⊥ = M₀ ≤ M₁ ≤ ⋯ ≤ Mₙ = ⊤` of `M` in which each
  quotient `Mᵢ₊₁ / Mᵢ` has `p` elements, with a tag for each step saying whether the Galois group
  acts on that quotient trivially (`IsTrivialStep`) or through the mod-`p` cyclotomic character
  (`IsCyclotomicStep`). For a prime `p` either condition makes `Mᵢ₊₁` stable under the action,
  so the chain is a filtration of `M` by Galois submodules whose successive quotients are
  isomorphic to the Galois modules `ℤ/p` or `μ_p`.
* `IsMazurAdmissible p Φ` says that such a chain exists. For a prime `p` this is Mazur's
  condition that the Galois module `M` has an admissible filtration.
* `filtLength c` is the length `n` of a chain `c`, and `filtAlpha c` is the number of its steps
  tagged trivial. They are the Galois-module counterparts of Mazur's invariants `ℓ` (the length)
  and `α` (the number of quotients `ℤ/p` in an admissible filtration).

## Main results

* `AdmissibleChain.natCard_eq_pow_filtLength`: if `M` has an admissible chain `c` for a prime
  `q`, then `Nat.card M = q ^ filtLength c`. So `M` is finite, and all admissible chains of `M`
  for `q` have the same length.

## Scope

Mazur defines admissibility for group schemes. For a prime `p` different from his fixed prime
level `N`, an admissible `p`-group is a commutative group scheme over `Spec ℤ`, finite and flat
over `ℤ[1/N]` and killed by a power of `p`, with a filtration over `ℤ[1/N]` by finite flat
subgroup schemes whose successive quotients are the group schemes `ℤ/p` or `μ_p`. He notes that
such a filtration exists exactly when the Galois module of its points has an admissible
filtration. `IsMazurAdmissible` is this Galois-module condition only. It involves no group
scheme, so a module satisfying it need not be the Galois module of an admissible group; it may,
for instance, be ramified at a prime other than `p` and `N`. The definitions also allow any
natural number `p`; the description above is for prime `p`. Mazur defines `α` on the group
scheme and notes that for odd `p` it is determined by the Galois module, but not for `p = 2`.
Here, for `p = 2`, a step is trivial exactly when it is cyclotomic, so `filtAlpha` depends on the
tags.

## References

* B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977), 33–186;
  Chapter I, §1 (f), *Admissible p-groups*.
-/

@[expose] public section

namespace MazurAdmissible

/-- An open action of the absolute Galois group of `ℚ` on an additive
commutative group `M`, given by a monoid homomorphism into `AddAut M`
whose kernel is open for the Krull topology. Mathlib makes `AddAut M` an
additive group, so the homomorphism takes values in
`Multiplicative (AddAut M)`, as `DistribMulAction.toAddAut` does. -/
structure OpenAction (M : Type*) [AddCommGroup M] where
  /-- The action, as a monoid homomorphism into the additive automorphism group. -/
  φ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Multiplicative (AddAut M)
  /-- The kernel of the action is open. -/
  hker : IsOpen (φ.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

variable {M : Type*} [AddCommGroup M]

namespace OpenAction

variable (Φ : OpenAction M)

/-- The identity acts trivially. -/
theorem map_one : (Φ.φ 1).toAdd = 0 := by
  rw [_root_.map_one, toAdd_one]

/-- The action respects multiplication in the Galois group. -/
theorem map_mul (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (Φ.φ (σ * τ)).toAdd = (Φ.φ σ).toAdd + (Φ.φ τ).toAdd := by
  rw [_root_.map_mul, toAdd_mul]

/-- The set of Galois elements that act as the identity is open. -/
theorem isOpen_setOf_toAdd_eq_zero : IsOpen {σ | (Φ.φ σ).toAdd = 0} := by
  simpa only [MonoidHom.coe_ker, Set.preimage, Set.mem_singleton_iff, toAdd_eq_zero]
    using Φ.hker

end OpenAction

/-- A step `A ≤ B` is trivial for `Φ` if every Galois element fixes `B`
pointwise modulo `A`. -/
def IsTrivialStep (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ B, (Φ.φ σ).toAdd x - x ∈ A

/-- A step `A ≤ B` is cyclotomic of level `p` for `Φ` if a Galois element
sending a primitive `p`-th root of unity `ζ` to `ζ ^ a` acts on `B` as
multiplication by `a` modulo `A`. -/
def IsCyclotomicStep (p : ℕ) (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p → ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ x ∈ B, (Φ.φ σ).toAdd x - a • x ∈ A

/-- An admissible chain of length `n` in `M`: a chain of subgroups from
`⊥` to `⊤` in which each successive quotient has cardinality `p` and
each step is either trivial or cyclotomic for `Φ`. -/
structure AdmissibleChain (p : ℕ) (Φ : OpenAction M) where
  /-- The length of the chain. -/
  n : ℕ
  /-- The subgroups in the chain, indexed by `Fin (n + 1)`. -/
  step : Fin (n + 1) → AddSubgroup M
  /-- The chain starts at the trivial subgroup. -/
  hbot : step 0 = ⊥
  /-- The chain ends at the whole group. -/
  htop : step (Fin.last n) = ⊤
  /-- The chain is monotone. -/
  hmono : ∀ i : Fin n, step i.castSucc ≤ step i.succ
  /-- Whether each step is trivial (`true`) or cyclotomic (`false`). -/
  tag : Fin n → Bool
  /-- Each successive quotient has cardinality `p`. -/
  hcard : ∀ i : Fin n,
    Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = p
  /-- Each step is trivial or cyclotomic according to its tag. -/
  hact : ∀ i : Fin n,
    if tag i then IsTrivialStep Φ (step i.castSucc) (step i.succ)
      else IsCyclotomicStep p Φ (step i.castSucc) (step i.succ)

variable {p : ℕ} {Φ : OpenAction M}

/-- The length of an admissible chain. -/
def filtLength (c : AdmissibleChain p Φ) : ℕ :=
  c.n

/-- The number of steps of an admissible chain tagged trivial (`tag i = true`), the steps on
whose quotient the Galois group acts trivially. It is the Galois-module counterpart of Mazur's
invariant `α`, the number of quotients `ℤ/p` in an admissible filtration. It counts the tags of
the chain `c`: for `p = 2` a step is trivial exactly when it is cyclotomic, so there the tags,
and with them `filtAlpha c`, are a free choice. -/
def filtAlpha (c : AdmissibleChain p Φ) : ℕ :=
  (Finset.univ.filter fun i => c.tag i = true).card

@[simp]
theorem filtLength_eq (c : AdmissibleChain p Φ) : filtLength c = c.n :=
  rfl

namespace AdmissibleChain

/-- The ambient group of an admissible chain for a prime `p` has
cardinality `p` raised to the length of the chain. Each step multiplies
the cardinality by `p`, since the successive quotient has cardinality
`p`. -/
public theorem natCard_eq_pow_filtLength {q : ℕ} (_hq : q.Prime)
    {Φ : OpenAction M} (c : AdmissibleChain q Φ) :
    Nat.card M = q ^ filtLength c := by
  have h : ∀ i : Fin (c.n + 1), Nat.card (c.step i) = q ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [c.hbot]; simp
    | succ i ih =>
      have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        ((c.step i.castSucc).addSubgroupOf (c.step i.succ))
      rw [c.hcard i,
        Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (c.hmono i)).toEquiv,
        ih] at hmul
      rw [hmul, Fin.val_succ, pow_succ, mul_comm, Fin.val_castSucc]
  have htop := h (Fin.last c.n)
  rw [c.htop, AddSubgroup.card_top, Fin.val_last] at htop
  exact htop

end AdmissibleChain

/-- `M` is Mazur admissible at `p` for `Φ` if it admits an admissible chain. For a prime `p`
this says that the Galois module `M` has an admissible filtration in Mazur's sense: a filtration
by Galois submodules whose successive quotients are isomorphic to the Galois modules `ℤ/p`
(trivial action) or `μ_p` (action through the mod-`p` cyclotomic character). It is a condition
on the Galois module only, not Mazur's notion of an admissible group scheme. -/
def IsMazurAdmissible (p : ℕ) (Φ : OpenAction M) : Prop :=
  Nonempty (AdmissibleChain p Φ)

end MazurAdmissible
