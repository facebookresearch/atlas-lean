/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.FieldTheory.Finite.BinaryModulusSearch
public meta import MathlibExt.FieldTheory.Finite.BinaryModulusSearch

@[expose] public section

namespace ETHBinaryModulusSearchReference

private def sourceToWord : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, y => decide (y % 2 = 1) :: sourceToWord n (y / 2)

private def sourceWords (s : Nat) : List (List Bool) :=
  (List.range (2 ^ s)).map (sourceToWord s)

private def sourceXor (x y : List Bool) : List Bool :=
  (x.zip y).map fun p => xor p.1 p.2

private def sourceZero (g : List Bool) : List Bool := g.map fun _ => false

private def sourceOne (g : List Bool) : List Bool :=
  true :: g.tail.map fun _ => false

private def sourceMulX (g w : List Bool) : List Bool :=
  if w.getLast?.getD false then
    sourceXor ((false :: w).take w.length) g
  else
    (false :: w).take w.length

private def sourceMulW (g x y : List Bool) : List Bool :=
  y.foldr
    (fun b c => if b then sourceXor x (sourceMulX g c) else sourceMulX g c)
    (sourceZero g)

private def sourceIrrW (g : List Bool) : Bool :=
  (sourceWords g.length).all fun x =>
    decide (x = sourceZero g) ||
      (sourceWords g.length).any fun y =>
        decide (sourceMulW g x y = sourceOne g)

private def sourceModW (s : Nat) : List Bool :=
  ((sourceWords s).find? sourceIrrW).getD []

private theorem toBoolListLE_ofNat_succ (s y : Nat) :
    (BitVec.ofNat (s + 1) y).toBoolListLE =
      decide (y % 2 = 1) :: (BitVec.ofNat s (y / 2)).toBoolListLE := by
  unfold BitVec.toBoolListLE
  rw [List.ofFn_succ]
  congr 1
  · rw [BitVec.getLsbD_ofNat]
    change (decide (0 < s + 1) && y.testBit 0) = decide (y % 2 = 1)
    rw [Nat.testBit_zero]
    simp
  · apply congrArg List.ofFn
    funext i
    rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
    change (decide (i.val + 1 < s + 1) && y.testBit (i.val + 1)) =
      (decide (i.val < s) && (y / 2).testBit i.val)
    rw [Nat.testBit_succ]
    simp [i.isLt]

private theorem sourceToWord_eq_toBoolListLE (s y : Nat) :
    sourceToWord s y = (BitVec.ofNat s y).toBoolListLE := by
  induction s generalizing y with
  | zero => rfl
  | succ s ih => rw [sourceToWord, toBoolListLE_ofNat_succ, ih]

private theorem sourceWords_eq (s : Nat) :
    sourceWords s =
      ((List.range (2 ^ s)).map (BitVec.ofNat s)).map BitVec.toBoolListLE := by
  simp [sourceWords, List.map_map, sourceToWord_eq_toBoolListLE]

private theorem toBoolListLE_injective {s : Nat} {x y : BitVec s}
    (h : x.toBoolListLE = y.toBoolListLE) : x = y := by
  apply (BitVec.equivBoolListLE s).injective
  exact Subtype.ext h

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
    (g.mulXMod w).toBoolListLE =
      sourceMulX g.toBoolListLE w.toBoolListLE := by
  rw [BitVec.mulXMod, sourceMulX, getLast?_toBoolListLE]
  split
  · rw [toBoolListLE_xor, toBoolListLE_shiftLeft,
      BitVec.length_toBoolListLE]
  · rw [toBoolListLE_shiftLeft, BitVec.length_toBoolListLE]

private theorem zero_eq_source {s : Nat} (g : BitVec s) :
    (0#s).toBoolListLE = sourceZero g.toBoolListLE := by
  unfold sourceZero
  apply List.ext_get (by simp)
  intro i hi h'i
  change (0#s).toBoolListLE[i] = (g.toBoolListLE.map fun _ => false)[i]
  rw [BitVec.getElem_toBoolListLE, List.getElem_map, BitVec.getLsbD_zero]

private theorem one_eq_source {s : Nat} (g : BitVec s) (hs : 0 < s) :
    (1#s).toBoolListLE = sourceOne g.toBoolListLE := by
  unfold sourceOne
  apply List.ext_get (by simp; omega)
  intro i hi h'i
  change (1#s).toBoolListLE[i] =
    (true :: g.toBoolListLE.tail.map fun _ => false)[i]
  rw [BitVec.getElem_toBoolListLE, BitVec.getLsbD_one]
  cases i <;> simp [hs]

private theorem mulMod_eq_source {s t : Nat} (g x : BitVec s) (y : BitVec t) :
    (g.mulMod x y).toBoolListLE =
      sourceMulW g.toBoolListLE x.toBoolListLE y.toBoolListLE := by
  unfold BitVec.mulMod sourceMulW
  induction y.toBoolListLE with
  | nil => exact zero_eq_source g
  | cons b bits ih =>
      simp only [List.foldr]
      cases b
      · rw [ite_eq_right (by simp), ite_eq_right (by simp),
          mulXMod_eq_source, ih]
      · rw [ite_eq_left (by simp), ite_eq_left (by simp),
          toBoolListLE_xor, mulXMod_eq_source, ih]

private theorem eq_zero_iff_source {s : Nat} (g x : BitVec s) :
    x = 0#s ↔ x.toBoolListLE = sourceZero g.toBoolListLE := by
  rw [← zero_eq_source g]
  exact ⟨fun h => congrArg BitVec.toBoolListLE h,
    toBoolListLE_injective⟩

private theorem mulMod_eq_one_iff_source {s : Nat} (g x y : BitVec s)
    (hs : 0 < s) :
    g.mulMod x y = 1#s ↔
      sourceMulW g.toBoolListLE x.toBoolListLE y.toBoolListLE =
        sourceOne g.toBoolListLE := by
  rw [← mulMod_eq_source, ← one_eq_source g hs]
  exact ⟨fun h => congrArg BitVec.toBoolListLE h,
    toBoolListLE_injective⟩

private theorem passesInverseTest_eq_source {s : Nat} (g : BitVec s) :
    g.passesInverseTest = sourceIrrW g.toBoolListLE := by
  by_cases hs : 0 < s
  · unfold BitVec.passesInverseTest sourceIrrW
    rw [BitVec.length_toBoolListLE, sourceWords_eq]
    simp only [List.all_map, List.any_map]
    apply congrArg (List.all (List.range (2 ^ s)))
    funext n
    let x := BitVec.ofNat s n
    change (decide (x = 0#s) ||
        (List.range (2 ^ s)).any fun m =>
          decide (g.mulMod x (BitVec.ofNat s m) = 1#s)) =
      (decide (x.toBoolListLE = sourceZero g.toBoolListLE) ||
        (List.range (2 ^ s)).any fun m =>
          decide (sourceMulW g.toBoolListLE x.toBoolListLE
            (BitVec.ofNat s m).toBoolListLE = sourceOne g.toBoolListLE))
    have hzero : decide (x = 0#s) =
        decide (x.toBoolListLE = sourceZero g.toBoolListLE) :=
      decide_eq_decide.mpr (eq_zero_iff_source g x)
    rw [hzero]
    congr 1
    apply congrArg (List.any (List.range (2 ^ s)))
    funext m
    let y := BitVec.ofNat s m
    change decide (g.mulMod x y = 1#s) =
      decide (sourceMulW g.toBoolListLE x.toBoolListLE y.toBoolListLE =
        sourceOne g.toBoolListLE)
    exact decide_eq_decide.mpr (mulMod_eq_one_iff_source g x y hs)
  · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    have hg : g = 0#0 := Subsingleton.elim _ _
    subst g
    decide

private def targetWords (s : Nat) : List (BitVec s) :=
  (List.range (2 ^ s)).map (BitVec.ofNat s)

private theorem sourceFind_eq (s : Nat) :
    (sourceWords s).find? sourceIrrW =
      ((targetWords s).find? BitVec.passesInverseTest).map
        BitVec.toBoolListLE := by
  unfold targetWords
  rw [sourceWords_eq, List.find?_map]
  congr 2
  funext g
  exact (passesInverseTest_eq_source g).symm

private theorem findIrreducibleModulus_eq_source_some (s : Nat) (hs : 0 < s) :
    (BitVec.findIrreducibleModulus s).map BitVec.toBoolListLE =
      some (sourceModW s) := by
  obtain ⟨g, hg, _⟩ := BitVec.findIrreducibleModulus_spec s hs
  have hgraw : (targetWords s).find? BitVec.passesInverseTest = some g := by
    simpa [BitVec.findIrreducibleModulus, hs, targetWords] using hg
  rw [hg, Option.map_some]
  congr 1
  unfold sourceModW
  rw [sourceFind_eq, hgraw]
  rfl

private theorem findIrreducibleModulus_default_eq_source (s : Nat) :
    ((BitVec.findIrreducibleModulus s).map BitVec.toBoolListLE).getD [] =
      sourceModW s := by
  by_cases hs : 0 < s
  · rw [findIrreducibleModulus_eq_source_some s hs]
    rfl
  · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    decide

example (s : Nat) :
    sourceWords s =
      ((List.range (2 ^ s)).map (BitVec.ofNat s)).map BitVec.toBoolListLE :=
  sourceWords_eq s

example {s : Nat} (g : BitVec s) :
    g.passesInverseTest = sourceIrrW g.toBoolListLE :=
  passesInverseTest_eq_source g

example (s : Nat) (hs : 0 < s) :
    (BitVec.findIrreducibleModulus s).map BitVec.toBoolListLE =
      some (sourceModW s) :=
  findIrreducibleModulus_eq_source_some s hs

example (s : Nat) :
    ((BitVec.findIrreducibleModulus s).map BitVec.toBoolListLE).getD [] =
      sourceModW s :=
  findIrreducibleModulus_default_eq_source s

example : sourceModW 0 = [] := by decide

end ETHBinaryModulusSearchReference

example : BitVec.findIrreducibleModulus 0 = none := by decide

example : (0#0).passesInverseTest = true := by decide

private theorem zero0ToPolynomial : (0#0).toPolynomial = 0 := by
  ext i
  simp [BitVec.coeff_toPolynomial]

example : (0#0).monicModulus = 1 := by
  rw [BitVec.monicModulus, zero0ToPolynomial]
  simp

example : ¬Irreducible (0#0).monicModulus := by
  rw [show (0#0).monicModulus = 1 by
    rw [BitVec.monicModulus, zero0ToPolynomial]
    simp]
  exact not_irreducible_one

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

private theorem two3ToPolynomial : (2#3).toPolynomial = Polynomial.X := by
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

private theorem three3ToPolynomial :
    (3#3).toPolynomial = Polynomial.X + 1 := by
  rw [show (3#3) = (2#3 ^^^ 1#3) by decide,
    BitVec.toPolynomial_xor, two3ToPolynomial, one3ToPolynomial]

example : (3#3).toBoolListLE = [true, true, false] := by decide

example :
    (3#3).monicModulus =
      Polynomial.X ^ 3 + Polynomial.X + 1 := by
  rw [BitVec.monicModulus, three3ToPolynomial, add_assoc]

example : BitVec.findIrreducibleModulus 1 = some (0#1) := by decide

example : BitVec.findIrreducibleModulus 2 = some (3#2) := by decide

example : BitVec.findIrreducibleModulus 3 = some (3#3) := by decide

example : BitVec.findIrreducibleModulus 4 = some (3#4) := by decide

example : (0#1).passesInverseTest = true := by decide

example : (1#1).passesInverseTest = true := by decide

example : (0#3).passesInverseTest = false := by decide

example : (1#3).passesInverseTest = false := by decide

example : (2#3).passesInverseTest = false := by decide

example : (3#3).passesInverseTest = true := by decide

private theorem three3Irreducible : Irreducible (3#3).monicModulus :=
  (BitVec.passesInverseTest_iff_irreducible (3#3) (by decide)).1 (by decide)

example : Irreducible (3#3).monicModulus := three3Irreducible

example (h : Irreducible (3#3).monicModulus) :
    (3#3).passesInverseTest = true :=
  (BitVec.passesInverseTest_iff_irreducible (3#3) (by decide)).2 h

example : ¬Irreducible (1#3).monicModulus := by
  intro h
  have := (BitVec.passesInverseTest_iff_irreducible (1#3) (by decide)).2 h
  exact (by decide : (1#3).passesInverseTest ≠ true) this

example : ∃ g : BitVec 3,
    BitVec.findIrreducibleModulus 3 = some g ∧ Irreducible g.monicModulus :=
  BitVec.findIrreducibleModulus_spec 3 (by decide)

example {g : BitVec 3} (h : Irreducible g.monicModulus) :
    (3#3).toNat ≤ g.toNat :=
  BitVec.findIrreducibleModulus_minimal (3#3) (by decide) g h

example : ∃ f : Polynomial (ZMod 2),
    f.Monic ∧ Irreducible f ∧ f.natDegree = 3 :=
  Polynomial.exists_monic_irreducible_zmod_two 3 (by decide)

example : ¬∃ f : Polynomial (ZMod 2),
    f.Monic ∧ Irreducible f ∧ f.natDegree = 0 := by
  rintro ⟨f, hf, hi, hd⟩
  rw [Polynomial.eq_one_of_monic_natDegree_zero hf hd] at hi
  exact not_irreducible_one hi

example : ∃ y : BitVec 3, (3#3).mulMod (2#3) y = 1#3 :=
  ⟨5#3, by decide⟩

private theorem adjoinRootEquivOne3 :
    (3#3).adjoinRootEquiv (1#3) = 1 := by
  rw [BitVec.adjoinRootEquiv_apply]
  have : (1#3).toPolynomial = 1 := by
    ext i
    rw [BitVec.coeff_toPolynomial, BitVec.getLsbD_one, Polynomial.coeff_one]
    simp
  rw [this, map_one]

example : ∃ z : AdjoinRoot (3#3).monicModulus,
    (3#3).adjoinRootEquiv (2#3) * z = 1 := by
  refine ⟨(3#3).adjoinRootEquiv (5#3), ?_⟩
  calc
    (3#3).adjoinRootEquiv (2#3) * (3#3).adjoinRootEquiv (5#3) =
        (3#3).adjoinRootEquiv ((3#3).mulMod (2#3) (5#3)) := by
      rw [BitVec.adjoinRootEquiv_apply (3#3) (5#3)]
      exact (BitVec.adjoinRootEquiv_mulMod (3#3) (2#3) (5#3)).symm
    _ = (3#3).adjoinRootEquiv (1#3) :=
      congrArg ((3#3).adjoinRootEquiv) (by decide)
    _ = 1 := adjoinRootEquivOne3

example : (3#3).adjoinRootEquiv (2#3) ≠ 0 := by
  intro h
  have hzero : (3#3).adjoinRootEquiv (0#3) = 0 := by
    rw [BitVec.adjoinRootEquiv_apply]
    have : (0#3).toPolynomial = 0 := by
      ext i
      simp [BitVec.coeff_toPolynomial]
    rw [this, map_zero]
  have heq : (3#3).adjoinRootEquiv (2#3) =
      (3#3).adjoinRootEquiv (0#3) := h.trans hzero.symm
  have : (2#3) = 0#3 := (3#3).adjoinRootEquiv.injective heq
  exact (by decide : (2#3) ≠ 0#3) this

#eval BitVec.findIrreducibleModulus 0
#eval BitVec.findIrreducibleModulus 1
#eval BitVec.findIrreducibleModulus 2
#eval BitVec.findIrreducibleModulus 3
#eval BitVec.findIrreducibleModulus 4

#print axioms Polynomial.exists_monic_irreducible_zmod_two
#print axioms BitVec.passesInverseTest
#print axioms BitVec.passesInverseTest_iff_irreducible
#print axioms BitVec.findIrreducibleModulus
#print axioms BitVec.findIrreducibleModulus_spec
#print axioms BitVec.findIrreducibleModulus_minimal
