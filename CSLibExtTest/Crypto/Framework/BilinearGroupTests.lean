/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Framework.BilinearGroup

/-!
# Tests for the bilinear-group interface

Toy-model numerics at `q = 7` (by `decide`), a kernel-triviality spot check,
the toy BDH insecurity witness, DDH-game distinction in `G1` and `G2` on the
DDH exponent relation, an SXDH advantage bound, a randomized two-coin
distinguisher with computed advantage, and axiom audits for the toy
construction and the headline theorems.
-/

namespace Cslib.Crypto.Framework

/-- The toy model at `q = 7`. -/
def toy7 : BilinearGroupData := BilinearGroupData.toyModel 7 (by decide)

/-- Decidable equality on the toy target group (definitionally `ZMod 7`-based). -/
instance toy7GTDecEq : DecidableEq toy7.GT :=
  inferInstanceAs (DecidableEq (Multiplicative (ZMod 7)))

/-- Pairing numerics at `q = 7`: `e 2 3 = gT ^ 6`. -/
example : toy7.e (Multiplicative.ofAdd (2 : ZMod 7)) (Multiplicative.ofAdd (3 : ZMod 7))
    = toy7.gT ^ 6 := by decide

/-- Nondegeneracy spot at `q = 7`: `e 2 3 ≠ 1`. -/
example : toy7.e (Multiplicative.ofAdd (2 : ZMod 7)) (Multiplicative.ofAdd (3 : ZMod 7))
    ≠ 1 := by decide

/-- Kernel triviality at `q = 7`. -/
example (a : Multiplicative (ZMod 7)) (h : ∀ b, toy7.e a b = 1) : a = 1 :=
  BilinearGroupData.eq_one_of_forall_e_eq_one_left toy7 a h

/-- The toy BDH insecurity witness at `q = 7`: a decoding adversary wins with
probability one, exhibiting the insecurity of every instance against
unrestricted adversaries that decode with `exp.symm`. -/
example : toy7.bdhAdvantage (BilinearGroupData.toyBdhAdversary 7) = 1 :=
  BilinearGroupData.toy_bdhAdvantage_eq_one 7 _

/-- A DDH-relation distinguisher in `G1`: outputs `true` iff the exponents
satisfy `a * b = c`. -/
noncomputable def ddh1Test : toy7.G1 → toy7.G1 → toy7.G1 → PMF Bool :=
  fun (x y z : Multiplicative (ZMod toy7.q)) =>
    if x.toAdd * y.toAdd = z.toAdd then PMF.pure true else PMF.pure false

/-- A DDH-relation distinguisher in `G2`. -/
noncomputable def ddh2Test : toy7.G2 → toy7.G2 → toy7.G2 → PMF Bool :=
  fun (x y z : Multiplicative (ZMod toy7.q)) =>
    if x.toAdd * y.toAdd = z.toAdd then PMF.pure true else PMF.pure false

/-- Every real `G1` triple satisfies the DDH relation. -/
theorem ddh1Test_real (a b : ZMod toy7.q) :
    ddh1Test (toy7.exp1 (Multiplicative.ofAdd a)) (toy7.exp1 (Multiplicative.ofAdd b))
      (toy7.exp1 (Multiplicative.ofAdd (a * b))) = PMF.pure true := by
  have h : ddh1Test (Multiplicative.ofAdd a : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd b : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd (a * b) : Multiplicative (ZMod toy7.q)) = PMF.pure true := by
    simp [ddh1Test]
  exact h

/-- Every real `G2` triple satisfies the DDH relation. -/
theorem ddh2Test_real (a b : ZMod toy7.q) :
    ddh2Test (toy7.exp2 (Multiplicative.ofAdd a)) (toy7.exp2 (Multiplicative.ofAdd b))
      (toy7.exp2 (Multiplicative.ofAdd (a * b))) = PMF.pure true := by
  have h : ddh2Test (Multiplicative.ofAdd a : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd b : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd (a * b) : Multiplicative (ZMod toy7.q)) = PMF.pure true := by
    simp [ddh2Test]
  exact h

/-- The concrete triple `(2, 3, 4)` at `q = 7` violates the DDH relation. -/
theorem ddh1Test_concrete :
    ddh1Test (toy7.exp1 (Multiplicative.ofAdd (2 : ZMod toy7.q)))
      (toy7.exp1 (Multiplicative.ofAdd (3 : ZMod toy7.q)))
      (toy7.exp1 (Multiplicative.ofAdd (4 : ZMod toy7.q))) = PMF.pure false := by
  have h : ddh1Test
      (Multiplicative.ofAdd (2 : ZMod toy7.q) : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd (3 : ZMod toy7.q) : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd (4 : ZMod toy7.q) : Multiplicative (ZMod toy7.q)) =
      PMF.pure false := by
    have h23 : (Multiplicative.ofAdd (2 : ZMod toy7.q)).toAdd *
        (Multiplicative.ofAdd (3 : ZMod toy7.q)).toAdd ≠
        (Multiplicative.ofAdd (4 : ZMod toy7.q)).toAdd := by decide
    unfold ddh1Test
    rw [ite_eq_right h23]
  exact h

/-- The concrete triple `(2, 3, 4)` at `q = 7` violates the DDH relation. -/
theorem ddh2Test_concrete :
    ddh2Test (toy7.exp2 (Multiplicative.ofAdd (2 : ZMod toy7.q)))
      (toy7.exp2 (Multiplicative.ofAdd (3 : ZMod toy7.q)))
      (toy7.exp2 (Multiplicative.ofAdd (4 : ZMod toy7.q))) = PMF.pure false := by
  have h : ddh2Test
      (Multiplicative.ofAdd (2 : ZMod toy7.q) : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd (3 : ZMod toy7.q) : Multiplicative (ZMod toy7.q))
      (Multiplicative.ofAdd (4 : ZMod toy7.q) : Multiplicative (ZMod toy7.q)) =
      PMF.pure false := by
    have h23 : (Multiplicative.ofAdd (2 : ZMod toy7.q)).toAdd *
        (Multiplicative.ofAdd (3 : ZMod toy7.q)).toAdd ≠
        (Multiplicative.ofAdd (4 : ZMod toy7.q)).toAdd := by decide
    unfold ddh2Test
    rw [ite_eq_right h23]
  exact h

/-- The real `G1` DDH game at `q = 7` always outputs `true`. -/
theorem ddh1RealGame_toy7 : toy7.ddh1RealGame ddh1Test = PMF.pure true := by
  unfold BilinearGroupData.ddh1RealGame
  simp only [ddh1Test_real, PMF.bind_const]

/-- The real `G2` DDH game at `q = 7` always outputs `true`. -/
theorem ddh2RealGame_toy7 : toy7.ddh2RealGame ddh2Test = PMF.pure true := by
  unfold BilinearGroupData.ddh2RealGame
  simp only [ddh2Test_real, PMF.bind_const]

/-- Every exponent lies in the support of the uniform sampler. -/
theorem mem_support_uniformOfFintype_zmod7 (a : ZMod toy7.q) :
    a ∈ (Cslib.Probability.PMF.uniformOfFintype (ZMod toy7.q)).support := by
  show a ∈ (Cslib.Probability.PMF.uniformOfFinset Finset.univ _).support
  rw [Cslib.Probability.PMF.mem_support_uniformOfFinset_iff]
  exact Finset.mem_univ a

/-- The random `G1` DDH game at `q = 7` can output `false`, witnessed by the
concrete triple `(2, 3, 4)`. -/
theorem ddh1RandomGame_false_mem :
    false ∈ (toy7.ddh1RandomGame ddh1Test).support := by
  unfold BilinearGroupData.ddh1RandomGame
  simp only [PMF.mem_support_bind_iff]
  refine ⟨2, mem_support_uniformOfFintype_zmod7 2, 3,
    mem_support_uniformOfFintype_zmod7 3, 4, mem_support_uniformOfFintype_zmod7 4, ?_⟩
  rw [ddh1Test_concrete]
  simp

/-- The random `G2` DDH game at `q = 7` can output `false`, witnessed by the
concrete triple `(2, 3, 4)`. -/
theorem ddh2RandomGame_false_mem :
    false ∈ (toy7.ddh2RandomGame ddh2Test).support := by
  unfold BilinearGroupData.ddh2RandomGame
  simp only [PMF.mem_support_bind_iff]
  refine ⟨2, mem_support_uniformOfFintype_zmod7 2, 3,
    mem_support_uniformOfFintype_zmod7 3, 4, mem_support_uniformOfFintype_zmod7 4, ?_⟩
  rw [ddh2Test_concrete]
  simp

/-- The `G1` DDH games at `q = 7` are distinguished. -/
theorem ddh1Games_differ :
    toy7.ddh1RealGame ddh1Test ≠ toy7.ddh1RandomGame ddh1Test := by
  intro h
  have hmem := ddh1RandomGame_false_mem
  rw [← h, ddh1RealGame_toy7] at hmem
  simp at hmem

/-- The `G2` DDH games at `q = 7` are distinguished. -/
theorem ddh2Games_differ :
    toy7.ddh2RealGame ddh2Test ≠ toy7.ddh2RandomGame ddh2Test := by
  intro h
  have hmem := ddh2RandomGame_false_mem
  rw [← h, ddh2RealGame_toy7] at hmem
  simp at hmem

/-- The `G1` DDH advantage at `q = 7` is positive. -/
theorem ddh1Advantage_pos : 0 < toy7.ddh1Advantage ddh1Test := by
  have hne : (toy7.ddh1RandomGame ddh1Test) false ≠ 0 :=
    (PMF.mem_support_iff _ _).mp ddh1RandomGame_false_mem
  have hpos : 0 < ((toy7.ddh1RandomGame ddh1Test) false).toReal :=
    ENNReal.toReal_pos hne (PMF.apply_ne_top _ _)
  have hfalse := toReal_apply_false (toy7.ddh1RandomGame ddh1Test)
  have hrw : winProb (toy7.ddh1RealGame ddh1Test) = 1 := by simp [ddh1RealGame_toy7]
  have hlt : winProb (toy7.ddh1RandomGame ddh1Test) < 1 := by linarith
  rw [BilinearGroupData.ddh1Advantage, advantage, hrw,
    abs_of_pos (by linarith : (0 : ℝ) < 1 - winProb (toy7.ddh1RandomGame ddh1Test))]
  linarith

/-- The `G2` DDH advantage at `q = 7` is positive. -/
theorem ddh2Advantage_pos : 0 < toy7.ddh2Advantage ddh2Test := by
  have hne : (toy7.ddh2RandomGame ddh2Test) false ≠ 0 :=
    (PMF.mem_support_iff _ _).mp ddh2RandomGame_false_mem
  have hpos : 0 < ((toy7.ddh2RandomGame ddh2Test) false).toReal :=
    ENNReal.toReal_pos hne (PMF.apply_ne_top _ _)
  have hfalse := toReal_apply_false (toy7.ddh2RandomGame ddh2Test)
  have hrw : winProb (toy7.ddh2RealGame ddh2Test) = 1 := by simp [ddh2RealGame_toy7]
  have hlt : winProb (toy7.ddh2RandomGame ddh2Test) < 1 := by linarith
  rw [BilinearGroupData.ddh2Advantage, advantage, hrw,
    abs_of_pos (by linarith : (0 : ℝ) < 1 - winProb (toy7.ddh2RandomGame ddh2Test))]
  linarith

/-- The SXDH advantage bound holds at `q = 7` for the DDH-relation
distinguishers (trivial bound `1`). -/
theorem sxdhAdvBound_toy7 : toy7.sxdhAdvBound ddh1Test ddh2Test 1 :=
  ⟨advantage_le_one _ _, advantage_le_one _ _⟩

/-- A genuinely randomized distinguisher: flips two fair coins through
`PMF.bind` and outputs their conjunction. -/
noncomputable def ddh1TwoCoins : toy7.G1 → toy7.G1 → toy7.G1 → PMF Bool :=
  fun _ _ _ => fairCoin.bind fun b₁ => fairCoin.bind fun b₂ => PMF.pure (b₁ && b₂)

/-- The real `G1` DDH game against the two-coin distinguisher is just the
two-coin distribution. -/
theorem ddh1RealGame_twoCoins :
    toy7.ddh1RealGame ddh1TwoCoins =
      fairCoin.bind fun b₁ => fairCoin.bind fun b₂ => PMF.pure (b₁ && b₂) := by
  unfold BilinearGroupData.ddh1RealGame ddh1TwoCoins
  simp only [PMF.bind_const]

/-- The two-coin distinguisher has zero `G1` DDH advantage: both games equal
the same coin distribution. -/
theorem ddh1Advantage_twoCoins : toy7.ddh1Advantage ddh1TwoCoins = 0 := by
  have h : toy7.ddh1RealGame ddh1TwoCoins = toy7.ddh1RandomGame ddh1TwoCoins := by
    unfold BilinearGroupData.ddh1RealGame BilinearGroupData.ddh1RandomGame ddh1TwoCoins
    simp only [PMF.bind_const]
  rw [BilinearGroupData.ddh1Advantage, h, advantage_self]

/-- The two-coin game wins with probability `1 / 4`. -/
theorem winProb_twoCoins : winProb (toy7.ddh1RealGame ddh1TwoCoins) = 1 / 4 := by
  have hcoin : ((2 : ENNReal)⁻¹).toReal = 1 / 2 := by simp
  have o1 : (PMF.pure (true && true) : PMF Bool) true = 1 := by simp [PMF.pure_apply]
  have o2 : (PMF.pure (true && false) : PMF Bool) true = 0 := by simp [PMF.pure_apply]
  have o3 : (PMF.pure (false && true) : PMF Bool) true = 0 := by simp [PMF.pure_apply]
  have o4 : (PMF.pure (false && false) : PMF Bool) true = 0 := by simp [PMF.pure_apply]
  rw [ddh1RealGame_twoCoins]
  simp only [winProb, PMF.bind_apply, tsum_fintype, Fintype.sum_bool, fairCoin,
    Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
    o1, o2, o3, o4, mul_one, mul_zero, add_zero, ENNReal.toReal_mul, hcoin]
  ring

#print axioms BilinearGroupData.toyModel
#print axioms toy7
#print axioms BilinearGroupData.toy_bdhAdvantage_eq_one
#print axioms ddh1RealGame_toy7
#print axioms ddh1RandomGame_false_mem
#print axioms ddh1Games_differ
#print axioms ddh1Advantage_pos
#print axioms ddh2RealGame_toy7
#print axioms ddh2RandomGame_false_mem
#print axioms ddh2Games_differ
#print axioms ddh2Advantage_pos
#print axioms sxdhAdvBound_toy7
#print axioms ddh1Advantage_twoCoins
#print axioms winProb_twoCoins

end Cslib.Crypto.Framework
