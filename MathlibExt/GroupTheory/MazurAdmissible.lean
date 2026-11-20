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

@[expose] public section

namespace MazurAdmissible

/-- An open action of the absolute Galois group of `ℚ` on an additive
commutative group `M`, given by a monoid homomorphism into `AddAut M`
whose kernel is open for the Krull topology. -/
structure OpenAction (M : Type*) [AddCommGroup M] where
  /-- The action, as a function into the additive automorphism group. -/
  φ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → AddAut M
  /-- The identity acts trivially. -/
  map_one : φ 1 = 0
  /-- The action respects multiplication in the Galois group. -/
  map_mul : ∀ σ τ, φ (σ * τ) = φ σ + φ τ
  /-- The kernel of the action is open. -/
  hker : IsOpen {σ | φ σ = 0}

variable {M : Type*} [AddCommGroup M]

/-- A step `A ≤ B` is trivial for `Φ` if every Galois element fixes `B`
pointwise modulo `A`. -/
def IsTrivialStep (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ B, Φ.φ σ x - x ∈ A

/-- A step `A ≤ B` is cyclotomic of level `p` for `Φ` if a Galois element
sending a primitive `p`-th root of unity `ζ` to `ζ ^ a` acts on `B` as
multiplication by `a` modulo `A`. -/
def IsCyclotomicStep (p : ℕ) (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p → ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ x ∈ B, Φ.φ σ x - a • x ∈ A

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

/-- The number of trivial steps in an admissible chain. -/
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

/-- `M` is Mazur admissible at `p` for `Φ` if it admits an admissible
chain. -/
def IsMazurAdmissible (p : ℕ) (Φ : OpenAction M) : Prop :=
  Nonempty (AdmissibleChain p Φ)

end MazurAdmissible
