/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Data.BitVec.BinaryPolynomialArithmetic
public meta import MathlibExt.Data.BitVec.BinaryPolynomialArithmetic

@[expose] public section

namespace ETHBinaryArithmeticReference

private def sourceXor (x y : List Bool) : List Bool :=
  (x.zip y).map fun p => xor p.1 p.2

private def sourceZero (g : List Bool) : List Bool := g.map fun _ => false

private def sourceOne (g : List Bool) : List Bool := true :: g.tail.map fun _ => false

private def sourceMulX (g w : List Bool) : List Bool :=
  if w.getLast?.getD false then
    sourceXor ((false :: w).take w.length) g
  else
    (false :: w).take w.length

private def sourceMulW (g x y : List Bool) : List Bool :=
  y.foldr
    (fun b c => if b then sourceXor x (sourceMulX g c) else sourceMulX g c)
    (sourceZero g)

private def sourcePowW (g u : List Bool) (e : Nat) : List Bool :=
  (List.range e).foldl (fun c _ => sourceMulW g c u) (sourceOne g)

private def sourceBit (R : Type*) [CommRing R] (b : Bool) : R :=
  if b then 1 else 0

private def sourceDecR {R : Type*} [CommRing R] (r : R) : List Bool → R
  | [] => 0
  | b :: w => sourceBit R b + r * sourceDecR r w

private noncomputable def sourcePolyW (w : List Bool) : Polynomial (ZMod 2) :=
  sourceDecR Polynomial.X w

private theorem coeff_sourcePolyW (w : List Bool) (i : Nat) :
    (sourcePolyW w).coeff i = sourceBit (ZMod 2) (w.getD i false) := by
  induction w generalizing i with
  | nil => simp [sourcePolyW, sourceDecR, sourceBit]
  | cons b w ih =>
      have h : sourcePolyW (b :: w) =
          Polynomial.C (sourceBit (ZMod 2) b) + Polynomial.X * sourcePolyW w := by
        unfold sourcePolyW
        rw [sourceDecR]
        cases b <;> simp [sourceBit]
      rw [h, Polynomial.coeff_add]
      cases i with
      | zero => cases b <;> simp [sourceBit]
      | succ i => simp [Polynomial.coeff_X_mul, ih, Polynomial.coeff_C_succ]

private theorem toPolynomial_eq_source {s : Nat} (w : BitVec s) :
    w.toPolynomial = sourcePolyW w.toBoolListLE := by
  ext i
  rw [BitVec.coeff_toPolynomial, coeff_sourcePolyW, BitVec.getD_toBoolListLE]
  rfl

private theorem eval₂_sourcePolyW {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (w : List Bool) :
    Polynomial.eval₂ φ r (sourcePolyW w) = sourceDecR r w := by
  induction w with
  | nil => simp [sourcePolyW, sourceDecR]
  | cons b w ih =>
      have h : sourcePolyW (b :: w) =
          Polynomial.C (sourceBit (ZMod 2) b) + Polynomial.X * sourcePolyW w := by
        unfold sourcePolyW
        rw [sourceDecR]
        cases b <;> simp [sourceBit]
      rw [h, sourceDecR, Polynomial.eval₂_add, Polynomial.eval₂_C,
        Polynomial.eval₂_mul, Polynomial.eval₂_X, ih]
      cases b <;> simp [sourceBit]

private theorem sourceDecR_toBoolListLE {s : Nat} {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (r : R) (w : BitVec s) :
    sourceDecR r w.toBoolListLE = w.toPolynomial.eval₂ φ r := by
  rw [toPolynomial_eq_source, eval₂_sourcePolyW]

private def sourceAddHomOfTwoEqZero {R : Type*} [CommRing R]
    (h2 : (2 : R) = 0) : ZMod 2 →+ R :=
  ZMod.lift 2 ⟨Int.castAddHom R, by simpa using h2⟩

private def sourceHomOfTwoEqZero {R : Type*} [CommRing R]
    (h2 : (2 : R) = 0) : ZMod 2 →+* R :=
  { sourceAddHomOfTwoEqZero h2 with
    map_one' := by
      change sourceAddHomOfTwoEqZero h2 ((1 : ℤ) : ZMod 2) = 1
      rw [sourceAddHomOfTwoEqZero, ZMod.lift_coe]
      simp
    map_mul' := by
      intro x y
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
      obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
      change sourceAddHomOfTwoEqZero h2 ((a : ZMod 2) * (b : ZMod 2)) =
        sourceAddHomOfTwoEqZero h2 (a : ZMod 2) *
          sourceAddHomOfTwoEqZero h2 (b : ZMod 2)
      rw [← Int.cast_mul, sourceAddHomOfTwoEqZero, ZMod.lift_coe,
        ZMod.lift_coe, ZMod.lift_coe]
      simp }

private theorem two_eq_zero_of_hom {R : Type*} [CommRing R] (φ : ZMod 2 →+* R) :
    (2 : R) = 0 := by
  have h := congrArg φ (show (2 : ZMod 2) = 0 by decide)
  simpa only [map_ofNat, map_zero] using h

private theorem toBoolListLE_xor {s : Nat} (x y : BitVec s) :
    (x ^^^ y).toBoolListLE = sourceXor x.toBoolListLE y.toBoolListLE := by
  unfold sourceXor
  apply List.ext_get (by simp)
  intro i hi h'i
  change (x ^^^ y).toBoolListLE[i] =
    ((x.toBoolListLE.zip y.toBoolListLE).map fun p => xor p.1 p.2)[i]
  rw [BitVec.getElem_toBoolListLE, List.getElem_map, List.getElem_zip,
    BitVec.getElem_toBoolListLE, BitVec.getElem_toBoolListLE,
    BitVec.getLsbD_xor]

private theorem toBoolListLE_shiftLeft {s : Nat} (w : BitVec s) :
    (w.shiftLeft 1).toBoolListLE = (false :: w.toBoolListLE).take s := by
  apply List.ext_get (by simp)
  intro i hi h'i
  change (w.shiftLeft 1).toBoolListLE[i] =
    ((false :: w.toBoolListLE).take s)[i]
  rw [BitVec.getElem_toBoolListLE, List.getElem_take]
  cases i with
  | zero => simp [BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft]
  | succ i =>
      rw [List.getElem_cons_succ, BitVec.getElem_toBoolListLE]
      have his : i + 1 < s := by simpa using hi
      simp [BitVec.shiftLeft_eq, his]
      rw [BitVec.getLsbD_eq_getElem (by omega)]

private theorem getLast?_toBoolListLE {s : Nat} (w : BitVec s) :
    w.toBoolListLE.getLast?.getD false = w.getMsbD 0 := by
  cases s with
  | zero => simp [BitVec.toBoolListLE]
  | succ s =>
      rw [List.getLast?_eq_getElem?, BitVec.length_toBoolListLE]
      simp [BitVec.getMsbD_eq_getLsbD, BitVec.getElem_toBoolListLE]

private theorem mulXMod_eq_source {s : Nat} (g w : BitVec s) :
    (g.mulXMod w).toBoolListLE = sourceMulX g.toBoolListLE w.toBoolListLE := by
  rw [BitVec.mulXMod, sourceMulX, getLast?_toBoolListLE]
  split
  · rw [toBoolListLE_xor, toBoolListLE_shiftLeft, BitVec.length_toBoolListLE]
  · rw [toBoolListLE_shiftLeft, BitVec.length_toBoolListLE]

private theorem zero_eq_source {s : Nat} (g : BitVec s) :
    (0#s).toBoolListLE = sourceZero g.toBoolListLE := by
  unfold sourceZero
  apply List.ext_get (by simp)
  intro i hi h'i
  change (0#s).toBoolListLE[i] = (g.toBoolListLE.map fun _ => false)[i]
  rw [BitVec.getElem_toBoolListLE, List.getElem_map, BitVec.getLsbD_zero]

private theorem mulMod_eq_source {s t : Nat} (g x : BitVec s) (y : BitVec t) :
    (g.mulMod x y).toBoolListLE =
      sourceMulW g.toBoolListLE x.toBoolListLE y.toBoolListLE := by
  unfold BitVec.mulMod sourceMulW
  induction y.toBoolListLE with
  | nil => exact zero_eq_source g
  | cons b bits ih =>
      simp only [List.foldr]
      cases b
      · rw [ite_eq_right (by simp), ite_eq_right (by simp), mulXMod_eq_source, ih]
      · rw [ite_eq_left (by simp), ite_eq_left (by simp), toBoolListLE_xor,
          mulXMod_eq_source, ih]

private theorem one_eq_source {s : Nat} (g : BitVec s) (hs : 0 < s) :
    (1#s).toBoolListLE = sourceOne g.toBoolListLE := by
  unfold sourceOne
  apply List.ext_get (by simp; omega)
  intro i hi h'i
  change (1#s).toBoolListLE[i] =
    (true :: g.toBoolListLE.tail.map fun _ => false)[i]
  rw [BitVec.getElem_toBoolListLE, BitVec.getLsbD_one]
  cases i <;> simp [hs]

private theorem powMod_zero_imported {s t : Nat} (g : BitVec s) (u : BitVec t) :
    g.powMod u 0 = 1#s := by
  rw [BitVec.powMod, ← Nat.fold_eq_foldTR, Nat.fold_zero]

private theorem powMod_succ_imported {s t : Nat} (g : BitVec s) (u : BitVec t)
    (e : Nat) :
    g.powMod u (e + 1) = g.mulMod (g.powMod u e) u := by
  unfold BitVec.powMod
  rw [← Nat.fold_eq_foldTR, Nat.fold_succ, Nat.fold_eq_foldTR]

private theorem powMod_eq_source {s t : Nat} (g : BitVec s) (u : BitVec t)
    (e : Nat) (hs : 0 < s) :
    (g.powMod u e).toBoolListLE =
      sourcePowW g.toBoolListLE u.toBoolListLE e := by
  induction e with
  | zero => simpa [powMod_zero_imported, sourcePowW] using one_eq_source g hs
  | succ e ih =>
      have htarget := powMod_succ_imported g u e
      have hsource :
          sourcePowW g.toBoolListLE u.toBoolListLE (e + 1) =
            sourceMulW g.toBoolListLE
              (sourcePowW g.toBoolListLE u.toBoolListLE e) u.toBoolListLE := by
        simp [sourcePowW, List.range_succ]
      rw [htarget, hsource, mulMod_eq_source, ih]

private theorem sourceDecR_mulX {s : Nat} {R : Type*} [CommRing R]
    (h2 : (2 : R) = 0) (r : R) (g w : BitVec s)
    (hr : r ^ s = sourceDecR r g.toBoolListLE) :
    sourceDecR r (sourceMulX g.toBoolListLE w.toBoolListLE) =
      r * sourceDecR r w.toBoolListLE := by
  let φ := sourceHomOfTwoEqZero h2
  rw [← mulXMod_eq_source, sourceDecR_toBoolListLE,
    sourceDecR_toBoolListLE]
  exact BitVec.eval₂_mulXMod φ r g w
    (hr.trans (sourceDecR_toBoolListLE φ r g))

private theorem sourceDecR_mulW {s t : Nat} {R : Type*} [CommRing R]
    (h2 : (2 : R) = 0) (r : R) (g x : BitVec s) (y : BitVec t)
    (hr : r ^ s = sourceDecR r g.toBoolListLE) :
    sourceDecR r (sourceMulW g.toBoolListLE x.toBoolListLE y.toBoolListLE) =
      sourceDecR r x.toBoolListLE * sourceDecR r y.toBoolListLE := by
  let φ := sourceHomOfTwoEqZero h2
  rw [← mulMod_eq_source, sourceDecR_toBoolListLE,
    sourceDecR_toBoolListLE, sourceDecR_toBoolListLE]
  exact BitVec.eval₂_mulMod φ r g x y (hr.trans (sourceDecR_toBoolListLE φ r g))

private theorem sourceDecR_powW {s t : Nat} {R : Type*} [CommRing R]
    (h2 : (2 : R) = 0) (r : R) (g : BitVec s) (u : BitVec t)
    (e : Nat) (hs : 0 < s) (hr : r ^ s = sourceDecR r g.toBoolListLE) :
    sourceDecR r (sourcePowW g.toBoolListLE u.toBoolListLE e) =
      sourceDecR r u.toBoolListLE ^ e := by
  let φ := sourceHomOfTwoEqZero h2
  rw [← powMod_eq_source g u e hs, sourceDecR_toBoolListLE,
    sourceDecR_toBoolListLE]
  exact BitVec.eval₂_powMod φ r g u e hs
    (hr.trans (sourceDecR_toBoolListLE φ r g))

private noncomputable def sourceDecWCanonical {s : Nat} (g : BitVec s)
    (w : List Bool) : AdjoinRoot g.monicModulus :=
  sourceDecR (AdjoinRoot.root g.monicModulus) w

private theorem sourceDecW_mulW {s t : Nat} (g x : BitVec s) (y : BitVec t) :
    sourceDecWCanonical g
        (sourceMulW g.toBoolListLE x.toBoolListLE y.toBoolListLE) =
      sourceDecWCanonical g x.toBoolListLE * sourceDecWCanonical g y.toBoolListLE := by
  apply sourceDecR_mulW
    (two_eq_zero_of_hom (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus)))
  rw [sourceDecR_toBoolListLE, ← Polynomial.aeval_def,
    AdjoinRoot.aeval_eq, ← BitVec.adjoinRootEquiv_apply,
    BitVec.adjoinRoot_root_pow]

private theorem sourceDecW_powW {s t : Nat} (g : BitVec s) (u : BitVec t)
    (e : Nat) (hs : 0 < s) :
    sourceDecWCanonical g (sourcePowW g.toBoolListLE u.toBoolListLE e) =
      sourceDecWCanonical g u.toBoolListLE ^ e := by
  apply sourceDecR_powW
    (two_eq_zero_of_hom (algebraMap (ZMod 2) (AdjoinRoot g.monicModulus)))
      _ _ _ _ hs
  rw [sourceDecR_toBoolListLE, ← Polynomial.aeval_def,
    AdjoinRoot.aeval_eq, ← BitVec.adjoinRootEquiv_apply,
    BitVec.adjoinRoot_root_pow]

/-- The source multiplication schema applies to an ordinary positive-width
characteristic-two target without an explicitly supplied homomorphism. -/
example :
    sourceDecR (1 : ZMod 2)
        (sourceMulW (1#1).toBoolListLE (1#1).toBoolListLE (1#1).toBoolListLE) =
      sourceDecR 1 (1#1).toBoolListLE * sourceDecR 1 (1#1).toBoolListLE := by
  exact sourceDecR_mulW (R := ZMod 2) (by decide) 1 (1#1) (1#1) (1#1) (by decide)

/-- The same source schema includes the characteristic-one trivial endpoint. -/
example :
    sourceDecR (0 : ZMod 1)
        (sourceMulW (0#0).toBoolListLE (0#0).toBoolListLE (0#0).toBoolListLE) =
      sourceDecR 0 (0#0).toBoolListLE * sourceDecR 0 (0#0).toBoolListLE := by
  exact sourceDecR_mulW (R := ZMod 1) (by decide) 0 (0#0) (0#0) (0#0)
    (Subsingleton.elim _ _)

/-- At width zero the source list retains its `true` identity bit. -/
example : sourcePowW [] [] 0 = [true] := rfl

/-- The fixed-width operation instead returns the unique zero-width word. -/
example : (0#0).powMod (0#0) 0 = 0#0 := by
  rw [powMod_zero_imported]
  exact Subsingleton.elim _ _

example : ((0#0).powMod (0#0) 0).toBoolListLE ≠ sourcePowW [] [] 0 := by
  rw [powMod_zero_imported]
  decide

/-- The distinct representatives still denote the same element of the zero quotient. -/
example :
    sourceDecWCanonical (0#0) (sourcePowW [] [] 0) =
      (0#0).adjoinRootEquiv ((0#0).powMod (0#0) 0) := by
  apply (0#0).adjoinRootEquiv.symm.injective
  exact Subsingleton.elim _ _

end ETHBinaryArithmeticReference

private theorem modByMonic_mulMod {s t : Nat} (g x : BitVec s) (y : BitVec t) :
    (x.toPolynomial * y.toPolynomial).modByMonic g.monicModulus =
      (g.mulMod x y).toPolynomial := by
  have h := congrArg (AdjoinRoot.modByMonicHom g.monicModulus_monic)
    (BitVec.adjoinRootEquiv_mulMod g x y)
  simp only [BitVec.adjoinRootEquiv_apply,
    AdjoinRoot.modByMonicHom_mk] at h
  rw [(Polynomial.modByMonic_eq_self_iff g.monicModulus_monic).mpr] at h
  · exact h.symm
  · rw [Polynomial.degree_eq_natDegree g.monicModulus_monic.ne_zero,
      g.monicModulus_natDegree]
    simpa [BitVec.toPolynomial] using Polynomial.degree_ofCoeffList_lt
      ((g.mulMod x y).toBoolListLE.map fun b => if b then (1 : ZMod 2) else 0)

private theorem modByMonic_powMod {s t : Nat} (g : BitVec s) (u : BitVec t)
    (e : Nat) :
    (u.toPolynomial ^ e).modByMonic g.monicModulus =
      (g.powMod u e).toPolynomial := by
  have h := congrArg (AdjoinRoot.modByMonicHom g.monicModulus_monic)
    (BitVec.adjoinRootEquiv_powMod g u e)
  simp only [BitVec.adjoinRootEquiv_apply,
    AdjoinRoot.modByMonicHom_mk] at h
  rw [(Polynomial.modByMonic_eq_self_iff g.monicModulus_monic).mpr] at h
  · exact h.symm
  · rw [Polynomial.degree_eq_natDegree g.monicModulus_monic.ne_zero,
      g.monicModulus_natDegree]
    simpa [BitVec.toPolynomial] using Polynomial.degree_ofCoeffList_lt
      ((g.powMod u e).toBoolListLE.map fun b => if b then (1 : ZMod 2) else 0)

example : (3#3).mulXMod (2#3) = 4#3 := by decide

example : (3#3).mulXMod (4#3) = 3#3 := by decide

example : (3#3).mulMod (2#3) (4#3) = 3#3 := by decide

example : (3#3).mulMod (3#3) (4#3) = 7#3 := by decide

example : (3#3).mulMod (3#3) (3#3) = 5#3 := by decide

private theorem powMod_two_seven : (3#3).powMod (2#3) 7 = 1#3 := by
  simp only [ETHBinaryArithmeticReference.powMod_succ_imported,
    ETHBinaryArithmeticReference.powMod_zero_imported]
  decide

example : (3#3).powMod (2#3) 7 = 1#3 := powMod_two_seven

example : (3#3).mulMod (1#3) (16#5) = 6#3 := by decide

private theorem powMod_sixteen_one : (3#3).powMod (16#5) 1 = 6#3 := by
  rw [ETHBinaryArithmeticReference.powMod_succ_imported,
    ETHBinaryArithmeticReference.powMod_zero_imported]
  decide

example : (3#3).powMod (16#5) 1 = 6#3 := powMod_sixteen_one

example : (3#3).powMod (0#3) 0 = 1#3 :=
  ETHBinaryArithmeticReference.powMod_zero_imported _ _

example : (3#3).powMod (0#3) 1 = 0#3 := by
  rw [ETHBinaryArithmeticReference.powMod_succ_imported,
    ETHBinaryArithmeticReference.powMod_zero_imported]
  decide

example : (1#3).mulMod (3#3) (7#3) = 0#3 := by decide

example : (0#0).mulXMod (0#0) = 0#0 := by decide

example : (0#0).mulMod (0#0) (0#0) = 0#0 := by decide

example {s : Nat} (x : BitVec s) : x ^^^ x = 0#s := by rw [BitVec.xor_self]

private def assertEval {n : Nat} (actual expected : BitVec n) : IO (BitVec n) :=
  if actual == expected then
    pure actual
  else
    throw <| IO.userError "binary arithmetic evaluation mismatch"

#eval assertEval ((3#3).mulXMod (2#3)) (4#3)
#eval assertEval ((3#3).mulXMod (4#3)) (3#3)
#eval assertEval ((3#3).mulMod (2#3) (4#3)) (3#3)
#eval assertEval ((3#3).mulMod (3#3) (4#3)) (7#3)
#eval assertEval ((3#3).mulMod (3#3) (3#3)) (5#3)
#eval assertEval ((3#3).powMod (2#3) 7) (1#3)
#eval assertEval ((3#3).mulMod (1#3) (16#5)) (6#3)
#eval assertEval ((3#3).powMod (16#5) 1) (6#3)
#eval assertEval ((1#3).mulMod (3#3) (7#3)) (0#3)

example :
    ((2#3).toPolynomial * (4#3).toPolynomial).modByMonic
        (3#3).monicModulus = (3#3).toPolynomial := by
  rw [modByMonic_mulMod]
  congr 1

example :
    ((3#3).toPolynomial * (4#3).toPolynomial).modByMonic
        (3#3).monicModulus = (7#3).toPolynomial := by
  rw [modByMonic_mulMod]
  congr 1

example :
    ((3#3).toPolynomial ^ 2).modByMonic
        (3#3).monicModulus = (5#3).toPolynomial := by
  rw [modByMonic_powMod]
  congr 1
  simp only [ETHBinaryArithmeticReference.powMod_succ_imported,
    ETHBinaryArithmeticReference.powMod_zero_imported]
  decide

example :
    ((2#3).toPolynomial ^ 7).modByMonic
        (3#3).monicModulus = (1#3).toPolynomial := by
  rw [modByMonic_powMod, powMod_two_seven]

example :
    (3#3).adjoinRootEquiv (2#3) *
        AdjoinRoot.mk (3#3).monicModulus (4#3).toPolynomial =
      (3#3).adjoinRootEquiv (3#3) := by
  calc
    _ = (3#3).adjoinRootEquiv ((3#3).mulMod (2#3) (4#3)) :=
      (BitVec.adjoinRootEquiv_mulMod (3#3) (2#3) (4#3)).symm
    _ = _ := congrArg ((3#3).adjoinRootEquiv) (by decide)

example :
    (3#3).adjoinRootEquiv (3#3) *
        AdjoinRoot.mk (3#3).monicModulus (4#3).toPolynomial =
      (3#3).adjoinRootEquiv (7#3) := by
  calc
    _ = (3#3).adjoinRootEquiv ((3#3).mulMod (3#3) (4#3)) :=
      (BitVec.adjoinRootEquiv_mulMod (3#3) (3#3) (4#3)).symm
    _ = _ := congrArg ((3#3).adjoinRootEquiv) (by decide)

example :
    (AdjoinRoot.mk (3#3).monicModulus (3#3).toPolynomial) ^ 2 =
      (3#3).adjoinRootEquiv (5#3) := by
  calc
    _ = (3#3).adjoinRootEquiv ((3#3).powMod (3#3) 2) :=
      (BitVec.adjoinRootEquiv_powMod (3#3) (3#3) 2).symm
    _ = _ := congrArg ((3#3).adjoinRootEquiv) (by
      simp only [ETHBinaryArithmeticReference.powMod_succ_imported,
        ETHBinaryArithmeticReference.powMod_zero_imported]
      decide)

example :
    (AdjoinRoot.mk (3#3).monicModulus (2#3).toPolynomial) ^ 7 =
      (1 : AdjoinRoot (3#3).monicModulus) := by
  calc
    _ = (3#3).adjoinRootEquiv ((3#3).powMod (2#3) 7) :=
      (BitVec.adjoinRootEquiv_powMod (3#3) (2#3) 7).symm
    _ = (3#3).adjoinRootEquiv (1#3) :=
      congrArg ((3#3).adjoinRootEquiv) powMod_two_seven
    _ = 1 := by
      have hone : (1#3).toPolynomial = 1 := by
        ext i
        rw [BitVec.coeff_toPolynomial, BitVec.getLsbD_one,
          Polynomial.coeff_one]
        simp
      rw [BitVec.adjoinRootEquiv_apply]
      simp [hone]

#print axioms BitVec.mulXMod
#print axioms BitVec.mulMod
#print axioms BitVec.powMod
#print axioms BitVec.eval₂_mulXMod
#print axioms BitVec.eval₂_mulMod
#print axioms BitVec.eval₂_powMod
#print axioms BitVec.adjoinRootEquiv_mulXMod
#print axioms BitVec.adjoinRootEquiv_mulMod
#print axioms BitVec.adjoinRootEquiv_powMod
