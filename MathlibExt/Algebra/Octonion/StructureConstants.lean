/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
transport the eight-square sign rule to `BitVec 3` and expose its finite
structure constants and contraction identities.
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Eight-square structure constants

This file gives the signed multiplication table underlying the Degen--Graves
eight-square identity. Basis indices use `BitVec 3`; bits 0, 1, and 2 are the
source's first, second, and third coordinates. It does not define an octonion
ring or a composition algebra structure.

The sign formula and crossing argument are adapted from the `Eight.phi`,
`Eight.sigma`, `Eight.psi`, `Eight.signs`, and block-contraction declarations in
Anthropic's `formal-math` repository at commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

namespace Octonion

open Finset

private abbrev SourceBlock := Bool × Bool × Bool

private def sourceBlock (p : BitVec 3) : SourceBlock :=
  (p.getLsbD 0, p.getLsbD 1, p.getLsbD 2)

private def sourceXor (p q : SourceBlock) : SourceBlock :=
  (p.1 ^^ q.1, p.2.1 ^^ q.2.1, p.2.2 ^^ q.2.2)

private def sourcePhi (p q : SourceBlock) : Nat :=
  p.1.toNat * q.1.toNat + p.1.toNat * q.2.1.toNat +
    p.1.toNat * q.2.2.toNat + p.2.1.toNat * q.2.1.toNat +
    p.2.1.toNat * q.2.2.toNat + p.2.2.toNat * q.2.2.toNat +
    q.1.toNat * p.2.1.toNat * p.2.2.toNat +
    p.1.toNat * q.2.1.toNat * p.2.2.toNat +
    p.1.toNat * p.2.1.toNat * q.2.2.toNat

private def sourceSigma (p q : SourceBlock) : Int :=
  (-1) ^ sourcePhi p q

private def sourcePsi (k p q : SourceBlock) : Int :=
  if sourceXor p q = k then sourceSigma p q else 0

private theorem sourceBlock_xor (p q : BitVec 3) :
    sourceBlock (p ^^^ q) = sourceXor (sourceBlock p) (sourceBlock q) := by
  simp only [sourceBlock, sourceXor, BitVec.getLsbD_xor]

private theorem sourceBlock_injective : Function.Injective sourceBlock := by
  intro p q h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · exact congrArg (fun x => x.1) h
  · exact congrArg (fun x => x.2.1) h
  · exact congrArg (fun x => x.2.2) h

private theorem sourceXor_eq_iff (p q k : BitVec 3) :
    sourceXor (sourceBlock p) (sourceBlock q) = sourceBlock k ↔ p ^^^ q = k := by
  rw [← sourceBlock_xor]
  exact sourceBlock_injective.eq_iff

/-- The sign of the product of basis elements indexed by `p` and `q`.

The output basis index is `p ^^^ q`. Bits are read least-significant first, so
bits 0, 1, and 2 correspond to the source coordinates 1, 2, and 3. -/
def basisSign (p q : BitVec 3) : Int :=
  let p₁ := (p.getLsbD 0).toNat
  let p₂ := (p.getLsbD 1).toNat
  let p₃ := (p.getLsbD 2).toNat
  let q₁ := (q.getLsbD 0).toNat
  let q₂ := (q.getLsbD 1).toNat
  let q₃ := (q.getLsbD 2).toNat
  (-1) ^ (p₁ * q₁ + p₁ * q₂ + p₁ * q₃ + p₂ * q₂ + p₂ * q₃ + p₃ * q₃ +
    q₁ * p₂ * p₃ + p₁ * q₂ * p₃ + p₁ * p₂ * q₃)

/-- The signed structure constant for the basis product indexed by `p` and `q`. -/
def structureConstant (p q k : BitVec 3) : Int :=
  if p ^^^ q = k then basisSign p q else 0

private theorem basisSign_eq_sourceSigma (p q : BitVec 3) :
    basisSign p q = sourceSigma (sourceBlock p) (sourceBlock q) := rfl

private theorem structureConstant_eq_sourcePsi (p q k : BitVec 3) :
    structureConstant p q k =
      sourcePsi (sourceBlock k) (sourceBlock p) (sourceBlock q) := by
  unfold structureConstant sourcePsi
  rw [basisSign_eq_sourceSigma]
  have hx := sourceXor_eq_iff p q k
  by_cases h : p ^^^ q = k
  · simp only [h, hx.mpr h, ite_true]
  · have hs : sourceXor (sourceBlock p) (sourceBlock q) ≠ sourceBlock k :=
      fun h' => h (hx.mp h')
    simp only [h, hs, ite_false]

/-- Every basis multiplication sign squares to one. -/
@[simp] theorem basisSign_mul_self (p q : BitVec 3) :
    basisSign p q * basisSign p q = 1 := by
  revert p q
  decide

/-- The cancellation rule of signs for two distinct decompositions of one xor index. -/
theorem basisSign_mul_add_swap {p q p' q' : BitVec 3}
    (hxor : p ^^^ q = p' ^^^ q') (hne : q ≠ q') :
    basisSign p q * basisSign p' q' +
      basisSign p q' * basisSign p' q = 0 := by
  revert p q p' q'
  decide

/-- Contracting two structure constants leaves their common xor component. -/
theorem sum_structureConstant_mul (p q p' q' : BitVec 3) :
    (∑ k : BitVec 3, structureConstant p q k * structureConstant p' q' k) =
      (if p ^^^ q = p' ^^^ q' then basisSign p q * basisSign p' q' else 0) := by
  revert p q p' q'
  decide

/-- The two contractions in the eight-square crossing decomposition. -/
theorem crossing_identity (x y u v : BitVec 3) :
    (∑ k : BitVec 3, structureConstant x y k * structureConstant v u k) +
      (∑ k : BitVec 3, structureConstant x u k * structureConstant v y k) =
        2 * (if x = v ∧ y = u then 1 else 0) := by
  revert x y u v
  decide

/-- A structure constant has absolute value at most one. -/
theorem abs_structureConstant_le_one (p q k : BitVec 3) :
    abs (structureConstant p q k) ≤ 1 := by
  revert p q k
  decide

/-- A contraction of two structure constants has absolute value at most one. -/
theorem abs_sum_structureConstant_mul_le_one (p q p' q' : BitVec 3) :
    abs (∑ k : BitVec 3, structureConstant p q k * structureConstant p' q' k) ≤ 1 := by
  revert p q p' q'
  decide

end Octonion
