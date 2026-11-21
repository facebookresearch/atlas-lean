/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.AdjoinRoot.BitVec

@[expose] public section

open Polynomial

namespace ETHAdjoinRootBitVecReference

/-- The source Boolean-to-ring constructor, local to the compatibility test. -/
private def sourceBit (R : Type) [CommRing R] (b : Bool) : R := if b then 1 else 0

/-- The exact source low-first Horner decoder. -/
private def sourceDecR {R : Type} [CommRing R] (r : R) : List Bool → R
  | [] => 0
  | b :: w => sourceBit R b + r * sourceDecR r w

/-- The exact source polynomial constructor. -/
private noncomputable def sourcePolyW (w : List Bool) : Polynomial (ZMod 2) :=
  sourceDecR X w

/-- The exact source modulus constructor. -/
private noncomputable def sourceModP (g : List Bool) : Polynomial (ZMod 2) :=
  X ^ g.length + sourcePolyW g

/-- The exact source quotient decoder. -/
private noncomputable def sourceDecW (g w : List Bool) : AdjoinRoot (sourceModP g) :=
  sourceDecR (AdjoinRoot.root (sourceModP g)) w

private theorem sourceMapDecR {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) (w : List Bool) :
    φ (sourceDecR r w) = sourceDecR (φ r) w := by
  induction w with
  | nil => simp [sourceDecR]
  | cons b w ih =>
      cases b <;> simp [sourceDecR, sourceBit, ih]

private theorem coeffSourcePolyW (w : List Bool) (i : Nat) :
    (sourcePolyW w).coeff i = sourceBit (ZMod 2) (w.getD i false) := by
  induction w generalizing i with
  | nil => simp [sourcePolyW, sourceDecR, sourceBit]
  | cons b w ih =>
      have h : sourcePolyW (b :: w) =
          C (sourceBit (ZMod 2) b) + X * sourcePolyW w := by
        unfold sourcePolyW
        rw [sourceDecR]
        cases b <;> simp [sourceBit]
      rw [h, coeff_add]
      cases i with
      | zero => cases b <;> simp [sourceBit]
      | succ i => simp [coeff_X_mul, ih, coeff_C_succ]

private theorem toPolynomial_eq_source {s : Nat} (w : BitVec s) :
    w.toPolynomial = sourcePolyW w.toBoolListLE := by
  ext i
  rw [BitVec.coeff_toPolynomial, coeffSourcePolyW, BitVec.getD_toBoolListLE]
  rfl

private theorem monicModulus_eq_source {s : Nat} (g : BitVec s) :
    g.monicModulus = sourceModP g.toBoolListLE := by
  rw [BitVec.monicModulus, sourceModP, BitVec.length_toBoolListLE,
    toPolynomial_eq_source]

private theorem sourceMkPolyW (g w : List Bool) :
    AdjoinRoot.mk (sourceModP g) (sourcePolyW w) = sourceDecW g w := by
  rw [sourcePolyW, sourceMapDecR, AdjoinRoot.mk_X, sourceDecW]

private noncomputable def transportAdjoinRoot {p q : Polynomial (ZMod 2)} (h : p = q) :
    AdjoinRoot q → AdjoinRoot p :=
  fun z => Eq.mp (congrArg AdjoinRoot h.symm) z

@[simp] private theorem transportAdjoinRoot_mk {p q x : Polynomial (ZMod 2)}
    (h : p = q) : transportAdjoinRoot h (AdjoinRoot.mk q x) = AdjoinRoot.mk p x := by
  subst q
  rfl

/-- The source decoder transported to the canonical BitVec modulus. -/
private noncomputable def sourceDecWCanonical {s : Nat} (g w : BitVec s) :
    AdjoinRoot g.monicModulus :=
  transportAdjoinRoot (monicModulus_eq_source g)
    (sourceDecW g.toBoolListLE w.toBoolListLE)

/-- The canonical quotient codec agrees with the exact source decoder for every fixed-width
word; the explicit transport compares the same quotient type. -/
private theorem adjoinRootEquiv_eq_source {s : Nat} (g w : BitVec s) :
    g.adjoinRootEquiv w = sourceDecWCanonical g w := by
  rw [BitVec.adjoinRootEquiv_apply]
  unfold sourceDecWCanonical
  rw [← sourceMkPolyW, transportAdjoinRoot_mk, toPolynomial_eq_source]

/-- The source `mk_polyW` equation itself, before transport. -/
example (g w : List Bool) :
    AdjoinRoot.mk (sourceModP g) (sourcePolyW w) = sourceDecW g w :=
  sourceMkPolyW g w

example {s : Nat} (g w : BitVec s) :
    g.adjoinRootEquiv w = sourceDecWCanonical g w :=
  adjoinRootEquiv_eq_source g w

example {s : Nat} (g w : BitVec s) :
    g.adjoinRootEquiv w = AdjoinRoot.mk g.monicModulus w.toPolynomial :=
  BitVec.adjoinRootEquiv_apply g w

end ETHAdjoinRootBitVecReference

/-- Both inverse equations hold for arbitrary words and quotient elements. -/
example {s : Nat} (g w : BitVec s) :
    g.adjoinRootEquiv.symm (g.adjoinRootEquiv w) = w :=
  g.adjoinRootEquiv.symm_apply_apply w

example {s : Nat} (g : BitVec s) (z : AdjoinRoot g.monicModulus) :
    g.adjoinRootEquiv (g.adjoinRootEquiv.symm z) = z :=
  g.adjoinRootEquiv.apply_symm_apply z

example {s : Nat} (g : BitVec s) (z : AdjoinRoot g.monicModulus) :
    g.adjoinRootEquiv.symm z =
      (AdjoinRoot.modByMonicHom g.monicModulus_monic z).toBitVec s :=
  BitVec.adjoinRootEquiv_symm_apply g z

/-- The public coefficient theorem is the coordinate theorem for Mathlib's actual canonical
power basis `1, root, ..., root^(s-1)`. -/
example {s : Nat} (g w : BitVec s) (i : Fin s) :
    (AdjoinRoot.powerBasisAux' g.monicModulus_monic).repr (g.adjoinRootEquiv w)
        ((finCongr g.monicModulus_natDegree).symm i) =
      if w.getLsbD i.val then 1 else 0 := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simpa using BitVec.adjoinRootEquiv_coeff g w i

private theorem zeroToPolynomial (s : Nat) : (0#s).toPolynomial = 0 := by
  ext i
  simp [BitVec.coeff_toPolynomial]

private theorem one3ToPolynomial : (1#3).toPolynomial = 1 := by
  ext i
  rw [BitVec.coeff_toPolynomial, Polynomial.coeff_one]
  by_cases h0 : i = 0
  · subst i
    decide
  by_cases hi : 3 ≤ i
  · rw [BitVec.getLsbD_of_ge _ _ hi]
    simp [h0]
  have hi' : i = 1 ∨ i = 2 := by omega
  rcases hi' with h | h <;> subst i <;> decide

private theorem two3ToPolynomial : (2#3).toPolynomial = X := by
  ext i
  rw [BitVec.coeff_toPolynomial, Polynomial.coeff_X]
  by_cases h0 : i = 0
  · subst i
    decide
  by_cases h1 : i = 1
  · subst i
    decide
  by_cases h2 : i = 2
  · subst i
    decide
  have hi : 3 ≤ i := by omega
  have h1' : 1 ≠ i := Ne.symm h1
  rw [BitVec.getLsbD_of_ge _ _ hi]
  simp [h1']

private theorem four3ToPolynomial : (4#3).toPolynomial = X ^ 2 := by
  ext i
  rw [BitVec.coeff_toPolynomial, coeff_X_pow]
  by_cases h0 : i = 0
  · subst i
    decide
  by_cases h1 : i = 1
  · subst i
    decide
  by_cases h2 : i = 2
  · subst i
    decide
  have hi : 3 ≤ i := by omega
  rw [BitVec.getLsbD_of_ge _ _ hi]
  simp [h2]

private theorem three3ToPolynomial : (3#3).toPolynomial = X + 1 := by
  rw [show (3#3) = (2#3 ^^^ 1#3) by decide, BitVec.toPolynomial_xor,
    two3ToPolynomial, one3ToPolynomial]

/-- The populated modulus is `X^3 + X + 1`, and its defining root equation reduces to `X + 1`. -/
example : (3#3).monicModulus = X ^ 3 + X + 1 := by
  rw [BitVec.monicModulus, three3ToPolynomial, add_assoc]

example : AdjoinRoot.root (3#3).monicModulus ^ 3 = (3#3).adjoinRootEquiv (3#3) :=
  BitVec.adjoinRoot_root_pow (3#3)

/-- The canonical power-basis coordinate at index zero of `X` is zero. -/
example :
    (AdjoinRoot.powerBasisAux' (3#3).monicModulus_monic).repr
        ((3#3).adjoinRootEquiv (2#3))
        ((finCongr (3#3).monicModulus_natDegree).symm ⟨0, by decide⟩) = 0 := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simpa using BitVec.adjoinRootEquiv_coeff (3#3) (2#3) ⟨0, by decide⟩

example :
    (AdjoinRoot.powerBasisAux' (3#3).monicModulus_monic).repr
        ((3#3).adjoinRootEquiv (2#3))
        ((finCongr (3#3).monicModulus_natDegree).symm ⟨1, by decide⟩) = 1 := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simpa using BitVec.adjoinRootEquiv_coeff (3#3) (2#3) ⟨1, by decide⟩

example :
    (AdjoinRoot.powerBasisAux' (3#3).monicModulus_monic).repr
        ((3#3).adjoinRootEquiv (2#3))
        ((finCongr (3#3).monicModulus_natDegree).symm ⟨2, by decide⟩) = 0 := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simpa using BitVec.adjoinRootEquiv_coeff (3#3) (2#3) ⟨2, by decide⟩

example :
    (AdjoinRoot.powerBasisAux' (3#3).monicModulus_monic).repr
        ((3#3).adjoinRootEquiv (4#3))
        ((finCongr (3#3).monicModulus_natDegree).symm ⟨0, by decide⟩) = 0 := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simpa using BitVec.adjoinRootEquiv_coeff (3#3) (4#3) ⟨0, by decide⟩

example :
    (AdjoinRoot.powerBasisAux' (3#3).monicModulus_monic).repr
        ((3#3).adjoinRootEquiv (4#3))
        ((finCongr (3#3).monicModulus_natDegree).symm ⟨1, by decide⟩) = 0 := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simpa using BitVec.adjoinRootEquiv_coeff (3#3) (4#3) ⟨1, by decide⟩

example :
    (AdjoinRoot.powerBasisAux' (3#3).monicModulus_monic).repr
        ((3#3).adjoinRootEquiv (4#3))
        ((finCongr (3#3).monicModulus_natDegree).symm ⟨2, by decide⟩) = 1 := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simpa using BitVec.adjoinRootEquiv_coeff (3#3) (4#3) ⟨2, by decide⟩

/-- Width zero gives the quotient by `1`; both the source and target are singletons. -/
example : (0#0).monicModulus = 1 := by
  rw [BitVec.monicModulus, zeroToPolynomial]
  simp

example (z : AdjoinRoot (0#0).monicModulus) : z = 0 := by
  apply (0#0).adjoinRootEquiv.symm.injective
  exact Subsingleton.elim _ _

example : (1 : AdjoinRoot (0#0).monicModulus) = 0 := by
  apply (0#0).adjoinRootEquiv.symm.injective
  exact Subsingleton.elim _ _

example (z : AdjoinRoot (0#0).monicModulus) : (0#0).adjoinRootEquiv.symm z = 0#0 :=
  Subsingleton.elim _ _

example : (0#0).adjoinRootEquiv (0#0) = 0 := by
  apply (0#0).adjoinRootEquiv.symm.injective
  exact Subsingleton.elim _ _

/-- Carried addition and xor map to `X` and `0`, respectively, for the same degree-three
modulus. -/
example :
    (3#3).adjoinRootEquiv ((1#3) + (1#3)) =
      AdjoinRoot.mk (3#3).monicModulus X := by
  rw [show (1#3) + (1#3) = 2#3 by decide,
    BitVec.adjoinRootEquiv_apply, two3ToPolynomial]

example : (3#3).adjoinRootEquiv ((1#3) ^^^ (1#3)) = 0 := by
  rw [show (1#3) ^^^ (1#3) = 0#3 by decide,
    BitVec.adjoinRootEquiv_apply, zeroToPolynomial, map_zero]

example :
    (3#3).adjoinRootEquiv ((1#3) + (1#3)) ≠
      (3#3).adjoinRootEquiv ((1#3) ^^^ (1#3)) := by
  intro h
  have hne : (1#3) + (1#3) ≠ (1#3) ^^^ (1#3) := by decide
  exact hne ((3#3).adjoinRootEquiv.injective h)

/-- The reducible modulus `X^2` has a nonzero nilpotent root, so the codec has no hidden field
or irreducibility hypothesis. -/
example : (0#2).monicModulus = X ^ 2 := by
  rw [BitVec.monicModulus, zeroToPolynomial]
  simp

example : AdjoinRoot.root (0#2).monicModulus ^ 2 = 0 := by
  calc
    AdjoinRoot.root (0#2).monicModulus ^ 2 =
        (0#2).adjoinRootEquiv (0#2) := BitVec.adjoinRoot_root_pow (0#2)
    _ = 0 := by
      rw [BitVec.adjoinRootEquiv_apply, zeroToPolynomial, map_zero]

example : AdjoinRoot.root (0#2).monicModulus ≠ 0 := by
  rw [show (0#2).monicModulus = X ^ 2 by
    rw [BitVec.monicModulus, zeroToPolynomial]
    simp]
  rw [← AdjoinRoot.mk_X]
  apply AdjoinRoot.mk_ne_zero_of_degree_lt (Polynomial.monic_X_pow 2)
  · exact Polynomial.X_ne_zero
  · simp

/-- Xor compatibility is universal and deliberately says nothing about carried addition. -/
example {s : Nat} (g x y : BitVec s) :
    g.adjoinRootEquiv (x ^^^ y) = g.adjoinRootEquiv x + g.adjoinRootEquiv y :=
  BitVec.adjoinRootEquiv_xor g x y

example {s : Nat} (g w : BitVec s) (i : Fin s) :
    (AdjoinRoot.modByMonicHom g.monicModulus_monic
      (g.adjoinRootEquiv w)).coeff i.val = if w.getLsbD i.val then 1 else 0 :=
  BitVec.adjoinRootEquiv_coeff g w i

#print axioms BitVec.adjoinRootEquiv
#print axioms BitVec.adjoinRootEquiv_apply
#print axioms BitVec.adjoinRootEquiv_symm_apply
#print axioms BitVec.adjoinRootEquiv_coeff
#print axioms BitVec.adjoinRootEquiv_xor
#print axioms BitVec.adjoinRoot_root_pow
