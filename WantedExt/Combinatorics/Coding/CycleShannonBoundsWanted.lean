/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Combinatorics.Coding.CycleCode

/-!
# Known cycle-capacity construction and rate requests

These are private unproved requests, not proofs or conjectures about newly open results.
The actual modular code and capacity model comes from `CycleGraphCode`. The paper-specific
integer profiles below perform only the displayed arithmetic; they do not supply independent
sets or prove that a profile comes from a valid tuple.

Source: Optimization Problems, constant 9a, pinned at
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; Gao arXiv:2607.27869;
Buys--Polak--Zuiddam arXiv:2607.29681; Tandon arXiv:2608.30273.
Approximate decimal displays are not asserted as equalities or rational bounds.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- Source: Polak--Schrijver, arXiv:1808.07438, the fifth-power 367-word construction. -/
theorem_wanted polakSchrijverLowerBound :
  ∃ A : Finset (Fin 5 → ZMod 7), IsCycleCode 7 A ∧ A.card = 367

/-- Source: Shannon (1956), the fractional-clique-cover upper bound. -/
theorem_wanted shannon1956UpperBound :
  shannonCapacityCycle 7 ≤ (7 : ENNReal) / 2

/-- The exact odd-cycle theta expression; its approximate source display is not an equality.
Source: Lovász (1979), as printed in BPZ, arXiv:2607.29681. -/
noncomputable def lovaszThetaCycleSeven : ENNReal :=
  ENNReal.ofReal (7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)))

/-- Source: Lovász (1979); the closed form is also printed in the retained BPZ primary. -/
theorem_wanted lovasz1979UpperBound :
  shannonCapacityCycle 7 ≤ lovaszThetaCycleSeven

/-- Source: Baumert--McEliece--Rodemich--Rumsey--Stanley--Taylor (1971), exact rate row. -/
theorem_wanted bmrrst1971LowerBound :
  ENNReal.rpow 343 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- Source: Vesel--Žerovnik (2002), exact rate row; no unprinted code is supplied. -/
theorem_wanted veselZerovnik2002LowerBound :
  ENNReal.rpow 108 ((4 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- Source: Mathew--Östergård (2017), exact rate row; no unprinted code is supplied. -/
theorem_wanted mathewOstergard2017LowerBound :
  ENNReal.rpow 350 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- Source: Polak--Schrijver, arXiv:1808.07438, exact fifth-root rate. -/
theorem_wanted polakSchrijverRateLowerBound :
  ENNReal.rpow 367 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- Source: Itty--Rosin--Carstensen--Reichman, arXiv:2607.21517, exact tenth-root rate. -/
theorem_wanted ittyRosinCarstensenReichman2026LowerBound :
  ENNReal.rpow 134753 ((10 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- Source: Itty--Rosin--Carstensen--Reichman, arXiv:2607.21517, tenth-power construction. -/
theorem_wanted ittyRosinCarstensenReichman2026Construction :
  ∃ A : Finset (Fin 10 → ZMod 7), IsCycleCode 7 A ∧ A.card = 134753

/-- The four integer coordinates propagated by the BPZ valid-tuple product.
Source: BPZ, arXiv:2607.29681, valid-tuple profiles. -/
structure BPZProfile where
  code : ℤ
  pairs : ℤ
  auxiliary : ℤ
  neutral : ℤ
  deriving DecidableEq, Repr

/-- Exact BPZ profile multiplication, without an independent-set certificate.
Source: BPZ, arXiv:2607.29681, the profile product. -/
def BPZProfile.star (p₁ p₂ : BPZProfile) : BPZProfile where
  code :=
    (p₁.code - p₁.pairs) * (p₂.code - p₂.pairs) +
      p₁.auxiliary * p₂.pairs + p₁.pairs * p₂.auxiliary
  pairs := p₁.neutral * p₂.pairs + p₁.pairs * p₂.neutral
  auxiliary := p₁.auxiliary * p₂.auxiliary
  neutral :=
    p₁.neutral * p₂.neutral +
      (p₁.auxiliary - p₁.neutral) * (p₂.auxiliary - p₂.neutral)

/-- Repeated exact BPZ profile squaring.
Source: BPZ, arXiv:2607.29681, iterated profile products. -/
def bpzProfileSquareIter : ℕ → BPZProfile → BPZProfile
  | 0, p => p
  | k + 1, p => bpzProfileSquareIter k (p.star p)

set_option linter.style.longLine false in
/-- Gao's exact printed dimension-200 cardinality.
Source: Gao, arXiv:2607.27869, the printed M40 value. -/
def gao2026M40 : ℕ :=
  4085567963379990282748597333793399773399910167372462112610203714626938509773125898252337545387866277249

/-- Source: Gao, arXiv:2607.27869, exact dimension-200 construction. -/
theorem_wanted gao2026Construction :
  ∃ A : Finset (Fin 200 → ZMod 7), IsCycleCode 7 A ∧ A.card = gao2026M40

/-- Source: Gao, arXiv:2607.27869, exact dimension-200 root rate. -/
theorem_wanted gao2026LowerBound :
  ENNReal.rpow (gao2026M40 : ENNReal) ((200 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- BPZ's one-block five-dimensional seven-cycle profile.
Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi1 : BPZProfile := ⟨367, 8, 367, 322⟩
/-- BPZ's two-block seven-cycle profile.
Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi2 : BPZProfile := bpzC7Pi1.star bpzC7Pi1
/-- BPZ's three-block seven-cycle profile.
Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi3 : BPZProfile := bpzC7Pi1.star bpzC7Pi2
/-- BPZ's five-block seven-cycle profile.
Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi5 : BPZProfile := bpzC7Pi2.star bpzC7Pi3
/-- BPZ's ten-block seven-cycle profile.
Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi10 : BPZProfile := bpzC7Pi5.star bpzC7Pi5
/-- BPZ's twenty-block seven-cycle profile.
Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi20 : BPZProfile := bpzC7Pi10.star bpzC7Pi10
/-- BPZ's final forty-block seven-cycle profile.
Source: BPZ, arXiv:2607.29681, seven-cycle construction. -/
def bpzC7Pi40 : BPZProfile := bpzC7Pi20.star bpzC7Pi20

set_option linter.style.longLine false in
/-- Kernel-checked first coordinate of the exact BPZ seven-cycle recursion.
Source: BPZ, arXiv:2607.29681, forty-block seven-cycle recursion. -/
theorem bpzC7Pi40_code :
    bpzC7Pi40.code =
      4089635995108338053456272492117641008738901835089431264388780413340766441486608118807897325023935704961 := by
  rfl

/-- Source: BPZ, arXiv:2607.29681, the exact forty-block dimension-200 construction. -/
theorem_wanted bpz2026CycleSevenConstruction :
  ∃ A : Finset (Fin 200 → ZMod 7), IsCycleCode 7 A ∧ A.card = bpzC7Pi40.code.toNat

/-- Source: BPZ, arXiv:2607.29681, the exact dimension-200 root rate. -/
theorem_wanted bpz2026CycleSevenLowerBound :
  ENNReal.rpow (bpzC7Pi40.code.toNat : ENNReal) ((200 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

set_option linter.style.longLine false in
/-- Tandon's exact printed dimension-500 cardinality.
Source: Tandon, arXiv:2608.30273, the printed Mstar value. -/
def tandon2026Mstar : ℕ :=
  33964672918117456943408517573718333225317390754651100605971152590324909277046876400440353958428359262989621520394737276681196655776758386330470832773308559159990317076102131413374061066595834823529274560988950698158729501949866486079791784996498585401881281

/-- Source: Tandon, arXiv:2608.30273, exact dimension-500 construction. -/
theorem_wanted tandon2026Construction :
  ∃ A : Finset (Fin 500 → ZMod 7), IsCycleCode 7 A ∧ A.card = tandon2026Mstar

/-- Source: Tandon, arXiv:2608.30273, exact dimension-500 root rate. -/
theorem_wanted tandon2026LowerBound :
  ENNReal.rpow (tandon2026Mstar : ENNReal) ((500 : ℝ)⁻¹) ≤ shannonCapacityCycle 7

/-- BPZ's one-block three-dimensional eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi1 : BPZProfile := ⟨148, 3, 148, 142⟩
/-- BPZ's two-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi2 : BPZProfile := bpzC11Pi1.star bpzC11Pi1
/-- BPZ's three-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi3 : BPZProfile := bpzC11Pi1.star bpzC11Pi2
/-- BPZ's four-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi4 : BPZProfile := bpzC11Pi2.star bpzC11Pi2
/-- BPZ's seven-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi7 : BPZProfile := bpzC11Pi3.star bpzC11Pi4
/-- BPZ's eight-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi8 : BPZProfile := bpzC11Pi4.star bpzC11Pi4
/-- BPZ's fourteen-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi14 : BPZProfile := bpzC11Pi7.star bpzC11Pi7
/-- BPZ's fifteen-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi15 : BPZProfile := bpzC11Pi7.star bpzC11Pi8
/-- BPZ's twenty-nine-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi29 : BPZProfile := bpzC11Pi14.star bpzC11Pi15
/-- BPZ's final fifty-eight-block eleven-cycle profile.
Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi58 : BPZProfile := bpzC11Pi29.star bpzC11Pi29

/-- BPZ's one-block six-dimensional thirteen-cycle profile.
Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi1 : BPZProfile := ⟨62530, 1014, 62530, 60502⟩
/-- BPZ's two-block thirteen-cycle profile.
Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi2 : BPZProfile := bpzC13Pi1.star bpzC13Pi1
/-- BPZ's three-block thirteen-cycle profile.
Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi3 : BPZProfile := bpzC13Pi1.star bpzC13Pi2
/-- BPZ's four-block thirteen-cycle profile.
Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi4 : BPZProfile := bpzC13Pi2.star bpzC13Pi2
/-- BPZ's five-block thirteen-cycle profile.
Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi5 : BPZProfile := bpzC13Pi2.star bpzC13Pi3
/-- BPZ's nine-block thirteen-cycle profile.
Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi9 : BPZProfile := bpzC13Pi4.star bpzC13Pi5
/-- BPZ's final seventy-two-block thirteen-cycle profile.
Source: BPZ, arXiv:2607.29681, thirteen-cycle construction. -/
def bpzC13Pi72 : BPZProfile := bpzProfileSquareIter 3 bpzC13Pi9

/-- BPZ's one-block four-dimensional fifteen-cycle profile.
Source: BPZ, arXiv:2607.29681, fifteen-cycle construction. -/
def bpzC15Pi1 : BPZProfile := ⟨2842, 3, 2842, 2833⟩
/-- BPZ's final fifteen-cycle profile after ten squarings.
Source: BPZ, arXiv:2607.29681, fifteen-cycle construction. -/
def bpzC15Pi1024 : BPZProfile := bpzProfileSquareIter 10 bpzC15Pi1

/-- BPZ's one-block four-dimensional nineteen-cycle profile.
Source: BPZ, arXiv:2607.29681, nineteen-cycle construction. -/
def bpzC19Pi1 : BPZProfile := ⟨7666, 2, 7666, 7661⟩
/-- BPZ's final nineteen-cycle profile after twelve squarings.
Source: BPZ, arXiv:2607.29681, nineteen-cycle construction. -/
def bpzC19Pi4096 : BPZProfile := bpzProfileSquareIter 12 bpzC19Pi1

/-- BPZ's one-block four-dimensional twenty-one-cycle profile.
Source: BPZ, arXiv:2607.29681, twenty-one-cycle construction. -/
def bpzC21Pi1 : BPZProfile := ⟨11441, 10, 11441, 11398⟩
/-- BPZ's final twenty-one-cycle profile after ten squarings.
Source: BPZ, arXiv:2607.29681, twenty-one-cycle construction. -/
def bpzC21Pi1024 : BPZProfile := bpzProfileSquareIter 10 bpzC21Pi1

/-- BPZ's one-block four-dimensional twenty-three-cycle profile.
Source: BPZ, arXiv:2607.29681, twenty-three-cycle construction. -/
def bpzC23Pi1 : BPZProfile := ⟨16466, 30, 16466, 16323⟩
/-- BPZ's final twenty-three-cycle profile after nine squarings.
Source: BPZ, arXiv:2607.29681, twenty-three-cycle construction. -/
def bpzC23Pi512 : BPZProfile := bpzProfileSquareIter 9 bpzC23Pi1

/-- Source: BPZ, arXiv:2607.29681, eleven-cycle construction in dimension 174. -/
theorem_wanted bpz2026CycleElevenConstruction :
  ∃ A : Finset (Fin 174 → ZMod 11), IsCycleCode 11 A ∧ A.card = bpzC11Pi58.code.toNat

/-- Source: BPZ, arXiv:2607.29681, thirteen-cycle construction in dimension 432. -/
theorem_wanted bpz2026CycleThirteenConstruction :
  ∃ A : Finset (Fin 432 → ZMod 13), IsCycleCode 13 A ∧ A.card = bpzC13Pi72.code.toNat

/-- Source: BPZ, arXiv:2607.29681, fifteen-cycle construction in dimension 4096. -/
theorem_wanted bpz2026CycleFifteenConstruction :
  ∃ A : Finset (Fin 4096 → ZMod 15), IsCycleCode 15 A ∧ A.card = bpzC15Pi1024.code.toNat

/-- Source: BPZ, arXiv:2607.29681, nineteen-cycle construction in dimension 16384. -/
theorem_wanted bpz2026CycleNineteenConstruction :
  ∃ A : Finset (Fin 16384 → ZMod 19), IsCycleCode 19 A ∧ A.card = bpzC19Pi4096.code.toNat

/-- Source: BPZ, arXiv:2607.29681, twenty-one-cycle construction in dimension 4096. -/
theorem_wanted bpz2026CycleTwentyOneConstruction :
  ∃ A : Finset (Fin 4096 → ZMod 21), IsCycleCode 21 A ∧ A.card = bpzC21Pi1024.code.toNat

/-- Source: BPZ, arXiv:2607.29681, twenty-three-cycle construction in dimension 2048. -/
theorem_wanted bpz2026CycleTwentyThreeConstruction :
  ∃ A : Finset (Fin 2048 → ZMod 23), IsCycleCode 23 A ∧ A.card = bpzC23Pi512.code.toNat

/-- Source: BPZ, arXiv:2607.29681, exact eleven-cycle root rate. -/
theorem_wanted bpz2026CycleElevenLowerBound :
  ENNReal.rpow (bpzC11Pi58.code.toNat : ENNReal) ((174 : ℝ)⁻¹) ≤ shannonCapacityCycle 11

/-- Source: BPZ, arXiv:2607.29681, exact thirteen-cycle root rate. -/
theorem_wanted bpz2026CycleThirteenLowerBound :
  ENNReal.rpow (bpzC13Pi72.code.toNat : ENNReal) ((432 : ℝ)⁻¹) ≤ shannonCapacityCycle 13

/-- Source: BPZ, arXiv:2607.29681, exact fifteen-cycle root rate. -/
theorem_wanted bpz2026CycleFifteenLowerBound :
  ENNReal.rpow (bpzC15Pi1024.code.toNat : ENNReal) ((4096 : ℝ)⁻¹) ≤ shannonCapacityCycle 15

/-- Source: BPZ, arXiv:2607.29681, exact nineteen-cycle root rate. -/
theorem_wanted bpz2026CycleNineteenLowerBound :
  ENNReal.rpow (bpzC19Pi4096.code.toNat : ENNReal) ((16384 : ℝ)⁻¹) ≤ shannonCapacityCycle 19

/-- Source: BPZ, arXiv:2607.29681, exact twenty-one-cycle root rate. -/
theorem_wanted bpz2026CycleTwentyOneLowerBound :
  ENNReal.rpow (bpzC21Pi1024.code.toNat : ENNReal) ((4096 : ℝ)⁻¹) ≤ shannonCapacityCycle 21

/-- Source: BPZ, arXiv:2607.29681, exact twenty-three-cycle root rate. -/
theorem_wanted bpz2026CycleTwentyThreeLowerBound :
  ENNReal.rpow (bpzC23Pi512.code.toNat : ENNReal) ((2048 : ℝ)⁻¹) ≤ shannonCapacityCycle 23

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
