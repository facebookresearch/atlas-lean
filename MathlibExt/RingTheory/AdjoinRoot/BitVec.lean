/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
identify fixed-width bitvectors with binary polynomial residue classes.
-/
module

public import MathlibExt.Algebra.Polynomial.BitVec
public import Mathlib.RingTheory.AdjoinRoot

/-! # Fixed-width binary residue classes

This file identifies a width-`s` bitvector with its polynomial residue modulo the monic binary
polynomial `X ^ s + g`.

The construction is adapted from `bitsW`, `decW_surj`, and `decW_inj` in
`eth/proof/variables/VariableBound/Field/Quot.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace BitVec

private theorem degree_toPolynomial_lt {s : Nat} (w : BitVec s) :
    w.toPolynomial.degree < (s : WithBot Nat) := by
  simpa [toPolynomial] using Polynomial.degree_ofCoeffList_lt
    (w.toBoolListLE.map fun b => if b then (1 : ZMod 2) else 0)

/-- Fixed-width binary words are in bijection with residues modulo their associated monic
polynomial. This is an ordinary equivalence because builtin bitvector addition has carries. -/
noncomputable def adjoinRootEquiv {s : Nat} (g : BitVec s) :
    BitVec s ≃ AdjoinRoot g.monicModulus where
  toFun w := AdjoinRoot.mk g.monicModulus w.toPolynomial
  invFun z := (AdjoinRoot.modByMonicHom g.monicModulus_monic z).toBitVec s
  left_inv w := by
    change (AdjoinRoot.modByMonicHom g.monicModulus_monic
      (AdjoinRoot.mk g.monicModulus w.toPolynomial)).toBitVec s = w
    rw [AdjoinRoot.modByMonicHom_mk,
      (Polynomial.modByMonic_eq_self_iff g.monicModulus_monic).mpr,
      BitVec.toBitVec_toPolynomial]
    rw [Polynomial.degree_eq_natDegree g.monicModulus_monic.ne_zero,
      g.monicModulus_natDegree]
    exact degree_toPolynomial_lt w
  right_inv z := by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    change AdjoinRoot.mk g.monicModulus
      ((AdjoinRoot.modByMonicHom g.monicModulus_monic
        (AdjoinRoot.mk g.monicModulus p)).toBitVec s).toPolynomial =
        AdjoinRoot.mk g.monicModulus p
    rw [AdjoinRoot.modByMonicHom_mk,
      Polynomial.toPolynomial_toBitVec s _ (by
        calc
          _ < g.monicModulus.degree :=
            Polynomial.degree_modByMonic_lt _ g.monicModulus_monic
          _ = (s : WithBot Nat) := by
            rw [Polynomial.degree_eq_natDegree g.monicModulus_monic.ne_zero,
              g.monicModulus_natDegree])]
    simpa using AdjoinRoot.mk_leftInverse g.monicModulus_monic
      (AdjoinRoot.mk g.monicModulus p)

/-- The forward equivalence is the canonical quotient constructor applied to the polynomial
encoding. -/
@[simp] theorem adjoinRootEquiv_apply {s : Nat} (g w : BitVec s) :
    g.adjoinRootEquiv w = AdjoinRoot.mk g.monicModulus w.toPolynomial :=
  rfl

/-- The inverse equivalence extracts the canonical remainder's lowest `s` binary
coefficients. -/
@[simp] theorem adjoinRootEquiv_symm_apply {s : Nat} (g : BitVec s)
    (z : AdjoinRoot g.monicModulus) :
    g.adjoinRootEquiv.symm z =
      (AdjoinRoot.modByMonicHom g.monicModulus_monic z).toBitVec s :=
  rfl

/-- The canonical remainder coordinates of an encoded word are exactly its low-first bits. -/
theorem adjoinRootEquiv_coeff {s : Nat} (g w : BitVec s) (i : Fin s) :
    (AdjoinRoot.modByMonicHom g.monicModulus_monic
      (g.adjoinRootEquiv w)).coeff i.val = if w.getLsbD i.val then 1 else 0 := by
  rw [adjoinRootEquiv_apply, AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff g.monicModulus_monic).mpr,
    coeff_toPolynomial]
  rw [Polynomial.degree_eq_natDegree g.monicModulus_monic.ne_zero,
    g.monicModulus_natDegree]
  exact degree_toPolynomial_lt w

/-- Bitwise xor corresponds to quotient addition; builtin bitvector addition does not. -/
theorem adjoinRootEquiv_xor {s : Nat} (g x y : BitVec s) :
    g.adjoinRootEquiv (x ^^^ y) = g.adjoinRootEquiv x + g.adjoinRootEquiv y := by
  rw [adjoinRootEquiv_apply, adjoinRootEquiv_apply, adjoinRootEquiv_apply,
    toPolynomial_xor, map_add]

/-- The defining quotient equation reduces `root ^ s` to the encoded lower coefficients. -/
theorem adjoinRoot_root_pow {s : Nat} (g : BitVec s) :
    AdjoinRoot.root g.monicModulus ^ s = g.adjoinRootEquiv g := by
  have hmod : AdjoinRoot.root g.monicModulus ^ s + g.adjoinRootEquiv g = 0 := by
    rw [adjoinRootEquiv_apply]
    have h : AdjoinRoot.mk g.monicModulus
        (Polynomial.X ^ s + g.toPolynomial) = 0 := by
      rw [← monicModulus]
      exact AdjoinRoot.mk_self
    simpa only [map_add, map_pow, AdjoinRoot.mk_X] using h
  have hzero : (0#s).toPolynomial = 0 := by
    ext i
    simp [coeff_toPolynomial]
  have htwo : g.adjoinRootEquiv g + g.adjoinRootEquiv g = 0 := by
    rw [← adjoinRootEquiv_xor, BitVec.xor_self, adjoinRootEquiv_apply,
      hzero, map_zero]
  calc
    AdjoinRoot.root g.monicModulus ^ s =
        AdjoinRoot.root g.monicModulus ^ s +
          (g.adjoinRootEquiv g + g.adjoinRootEquiv g) := by rw [htwo, add_zero]
    _ = g.adjoinRootEquiv g := by rw [← add_assoc, hmod, zero_add]

end BitVec
