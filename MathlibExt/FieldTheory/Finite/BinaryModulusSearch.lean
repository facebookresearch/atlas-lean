/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
search exhaustively for the first irreducible binary polynomial modulus.
-/
module

public import MathlibExt.Data.BitVec.BinaryPolynomialArithmetic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.List.GetD

/-! # Exhaustive search for binary polynomial moduli

This file implements the exhaustive inverse test and first-modulus search from the ETH
formalization. The candidates are the lower coefficient words in ascending natural-number order.

The construction is adapted from `Field/Defs.lean`, `Field/Quot.lean`, and `Field/Search.lean` in
`anthropics/formal-math` at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

namespace Polynomial

/-- Over `ZMod 2`, there is a monic irreducible polynomial of every positive degree. -/
theorem exists_monic_irreducible_zmod_two (s : Nat) (hs : 0 < s) :
    ∃ f : Polynomial (ZMod 2), f.Monic ∧ Irreducible f ∧ f.natDegree = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top
    (ZMod 2) (GaloisField 2 s)
  have hint : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).mp hα,
    GaloisField.finrank 2 (by omega)]

end Polynomial

namespace BitVec

/-- Test exhaustively whether every nonzero word has a multiplicative inverse modulo
`g.monicModulus`. -/
def passesInverseTest {s : Nat} (g : BitVec s) : Bool :=
  let words := (List.range (2 ^ s)).map (BitVec.ofNat s)
  words.all fun x =>
    decide (x = 0#s) ||
      words.any fun y => decide (g.mulMod x y = 1#s)

private def binaryWords (s : Nat) : List (BitVec s) :=
  (List.range (2 ^ s)).map (BitVec.ofNat s)

private theorem mem_binaryWords {s : Nat} (w : BitVec s) : w ∈ binaryWords s := by
  rw [binaryWords, List.mem_map]
  refine ⟨w.toNat, List.mem_range.mpr w.isLt, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

private theorem passesInverseTest_eq_true {s : Nat} (g : BitVec s) :
    g.passesInverseTest = true ↔
      ∀ x : BitVec s, x = 0#s ∨ ∃ y : BitVec s, g.mulMod x y = 1#s := by
  change (binaryWords s).all _ = true ↔ _
  simp only [List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true]
  constructor
  · intro h x
    rcases h x (mem_binaryWords x) with hx | ⟨y, _, hy⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, hy⟩
  · intro h x _
    rcases h x with hx | ⟨y, hy⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, mem_binaryWords y, hy⟩

private theorem adjoinRootEquiv_zero {s : Nat} (g : BitVec s) :
    g.adjoinRootEquiv (0#s) = 0 := by
  rw [BitVec.adjoinRootEquiv_apply, toPolynomial_zero, map_zero]

private theorem adjoinRootEquiv_one {s : Nat} (g : BitVec s) (hs : 0 < s) :
    g.adjoinRootEquiv (1#s) = 1 := by
  rw [BitVec.adjoinRootEquiv_apply, toPolynomial_one hs, map_one]

/-- At positive width, the exhaustive inverse test succeeds exactly for irreducible monic
moduli. -/
theorem passesInverseTest_iff_irreducible {s : Nat} (g : BitVec s) (hs : 0 < s) :
    g.passesInverseTest = true ↔ Irreducible g.monicModulus := by
  rw [passesInverseTest_eq_true, ← AdjoinRoot.isField_iff_irreducible]
  constructor
  · intro h
    have hzeroone : (0#s) ≠ 1#s := by
      rw [BitVec.toNat_ne]
      simp [BitVec.toNat_one hs]
    refine IsField.mk
      ⟨g.adjoinRootEquiv (0#s), g.adjoinRootEquiv (1#s),
        fun h01 => hzeroone (g.adjoinRootEquiv.injective h01)⟩ mul_comm ?_
    intro z hz
    let x := g.adjoinRootEquiv.symm z
    have hx : x ≠ 0#s := by
      intro hx
      apply hz
      calc
        z = g.adjoinRootEquiv x := (g.adjoinRootEquiv.apply_symm_apply z).symm
        _ = g.adjoinRootEquiv (0#s) := congrArg g.adjoinRootEquiv hx
        _ = 0 := adjoinRootEquiv_zero g
    rcases h x with hx0 | ⟨y, hy⟩
    · exact absurd hx0 hx
    · refine ⟨g.adjoinRootEquiv y, ?_⟩
      calc
        z * g.adjoinRootEquiv y =
            g.adjoinRootEquiv x * g.adjoinRootEquiv y := by
              rw [g.adjoinRootEquiv.apply_symm_apply]
        _ = g.adjoinRootEquiv (g.mulMod x y) := by
          rw [BitVec.adjoinRootEquiv_apply g y]
          exact (BitVec.adjoinRootEquiv_mulMod g x y).symm
        _ = 1 := by rw [hy, adjoinRootEquiv_one g hs]
  · intro hfield
    have hirr : Irreducible g.monicModulus :=
      AdjoinRoot.isField_iff_irreducible.mp hfield
    have : Fact (Irreducible g.monicModulus) := ⟨hirr⟩
    intro x
    by_cases hx : x = 0#s
    · exact Or.inl hx
    · right
      have hne : g.adjoinRootEquiv x ≠ 0 := by
        intro hzero
        apply hx
        apply g.adjoinRootEquiv.injective
        rw [hzero, adjoinRootEquiv_zero]
      let y := g.adjoinRootEquiv.symm (g.adjoinRootEquiv x)⁻¹
      refine ⟨y, g.adjoinRootEquiv.injective ?_⟩
      calc
        g.adjoinRootEquiv (g.mulMod x y) =
            g.adjoinRootEquiv x *
              AdjoinRoot.mk g.monicModulus y.toPolynomial :=
          BitVec.adjoinRootEquiv_mulMod g x y
        _ = g.adjoinRootEquiv x * (g.adjoinRootEquiv x)⁻¹ := by
          rw [← BitVec.adjoinRootEquiv_apply, show y =
            g.adjoinRootEquiv.symm (g.adjoinRootEquiv x)⁻¹ from rfl,
            g.adjoinRootEquiv.apply_symm_apply]
        _ = 1 := mul_inv_cancel₀ hne
        _ = g.adjoinRootEquiv (1#s) := (adjoinRootEquiv_one g hs).symm

/-- Search the lower coefficient words in ascending order for the first word passing the
exhaustive inverse test. Width zero is deliberately reported as failure. -/
def findIrreducibleModulus (s : Nat) : Option (BitVec s) :=
  if 0 < s then
    ((List.range (2 ^ s)).map (BitVec.ofNat s)).find? passesInverseTest
  else
    none

/-- At every positive width, exhaustive search returns an irreducible binary modulus. -/
theorem findIrreducibleModulus_spec (s : Nat) (hs : 0 < s) :
    ∃ g : BitVec s, findIrreducibleModulus s = some g ∧
      Irreducible g.monicModulus := by
  obtain ⟨f, hf, hirr, hd⟩ := Polynomial.exists_monic_irreducible_zmod_two s hs
  let g := f.toBitVec s
  have hgmod : g.monicModulus = f := monicModulus_toBitVec f hf hd
  have hgirr : Irreducible g.monicModulus := hgmod.symm ▸ hirr
  have hgpass : g.passesInverseTest = true :=
    (passesInverseTest_iff_irreducible g hs).2 hgirr
  cases hfind : (binaryWords s).find? passesInverseTest with
  | none =>
      exact absurd hgpass
        (List.find?_eq_none.mp hfind g (mem_binaryWords g))
  | some g₀ =>
      refine ⟨g₀, ?_, (passesInverseTest_iff_irreducible g₀ hs).1
        (List.find?_some hfind)⟩
      simpa [findIrreducibleModulus, hs, binaryWords] using hfind

/-- The returned modulus is no larger than any lower coefficient word whose monic modulus is
irreducible. -/
theorem findIrreducibleModulus_minimal {s : Nat} (g : BitVec s)
    (h : findIrreducibleModulus s = some g) :
    ∀ g' : BitVec s, Irreducible g'.monicModulus → g.toNat ≤ g'.toNat := by
  have hs : 0 < s := by
    by_contra hs
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    simp [findIrreducibleModulus] at h
  have hfind : (binaryWords s).find? passesInverseTest = some g := by
    simpa [findIrreducibleModulus, hs, binaryWords] using h
  rcases List.find?_eq_some_iff_getElem.mp hfind with
    ⟨_, i, hi, hig, hbefore⟩
  have hipow : i < 2 ^ s := by simpa [binaryWords] using hi
  have hitonat : i = g.toNat := by
    have hnat := congrArg BitVec.toNat hig
    simpa [binaryWords, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hipow] using hnat
  intro g' hg'
  have hg'pass : g'.passesInverseTest = true :=
    (passesInverseTest_iff_irreducible g' hs).2 hg'
  by_contra hle
  have hlt : g'.toNat < i := by omega
  have hjpow : g'.toNat < 2 ^ s := g'.isLt
  have hjlen : g'.toNat < (binaryWords s).length := by
    simpa [binaryWords] using hjpow
  have hword : (binaryWords s)[g'.toNat] = g' := by
    apply BitVec.eq_of_toNat_eq
    simp [binaryWords]
  have hfailure := hbefore g'.toNat hlt
  simp [hword, hg'pass] at hfailure

end BitVec
