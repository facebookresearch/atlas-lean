/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskTree
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionPackedNat
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic

/-! Kernel-efficient evaluators for the octad binary forest certificates, written with the
primitive natural-number operations accelerated by Lean's kernel, together with proofs that they
agree with the reference evaluators. Only the reference evaluators enter the forest statements. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A bit test using only primitive operations. -/
def generatedAxisGlobalTwelveOctadFastBit (m n : ℕ) : Bool :=
  Nat.beq (Nat.land 1 (Nat.shiftRight m n)) 1

/-- The primitive bit test is the ordinary bit test. -/
theorem generatedAxisGlobalTwelveOctadFastBit_eq (m n : ℕ) :
    generatedAxisGlobalTwelveOctadFastBit m n = m.testBit n := by
  have h1 : Nat.land 1 (Nat.shiftRight m n) = (m >>> n) % 2 := Nat.one_and_eq_mod_two _
  have h2 : m.testBit n = (1 &&& (m >>> n) != 0) := rfl
  rw [generatedAxisGlobalTwelveOctadFastBit, h1, h2, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m >>> n) with h | h <;> rw [h] <;> rfl

/-- Column-XOR evaluation by the list recursor and primitive operations. -/
def generatedAxisGlobalTwelveOctadFastRows (rows : List (ℕ × ℕ)) (b : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun p _ acc => cond (generatedAxisGlobalTwelveOctadFastBit b p.1) (Nat.xor p.2 acc) acc) rows

/-- The fast column-XOR evaluator is the reference evaluator. -/
theorem generatedAxisGlobalTwelveOctadFastRows_eq (rows : List (ℕ × ℕ)) (b : ℕ) :
    generatedAxisGlobalTwelveOctadFastRows rows b = generatedAxisGlobalMaskRowsAction rows b := by
  induction rows with
  | nil => rfl
  | cons p rows ih =>
      rcases p with ⟨i, c⟩
      change cond (generatedAxisGlobalTwelveOctadFastBit b i)
          (Nat.xor c (generatedAxisGlobalTwelveOctadFastRows rows b))
          (generatedAxisGlobalTwelveOctadFastRows rows b) = _
      rw [generatedAxisGlobalTwelveOctadFastBit_eq, ih]
      simp only [generatedAxisGlobalMaskRowsAction]
      cases b.testBit i <;> rfl

/-- Parities of all twelve-bit masks, one bit per mask. -/
def generatedAxisGlobalTwelveOctadParityTable : ℕ :=
  generatedAxisGlobalPackedNat%[
    "43076240682773474866209781176446303895211632923266",
    "72683452035016566979907475895852677523809774830926",
    "12093359287707331958523049115438554099597118701065",
    "02811152268655745823936942503137071892389625559840",
    "71516729832284987877447591461925080246935500987793",
    "64218178901904949478413814501382336475533680075066",
    "43686221477321281427424620485213741062231841419105",
    "44191747735380670515611760277420951046115344572699",
    "79341104744462222794708013847602227839468474242829",
    "30911974606466871029171729517965594834469459608318",
    "54814226072689753469729406682167083593796715188263",
    "17460379482275074383057915585869126297498686669293",
    "49581053324331039784695472695136034645771254288780",
    "88465820359996190296996250373000040671427348366378",
    "60485485399398240765395365016234110316005344683393",
    "99205033480489628971491880288247343374226663186821",
    "13719951400326862908643132959179752236079678730762",
    "31122980219269452823000863328210901828433081969464",
    "66150460744506552493381418500204580502929213576875",
    "33705896912014762047137607986134752620425117132499",
    "18092112212569908004931734015101549789455916591296",
    "24912620348300529210184763248439236190958771598348",
    "17660300113191106175133224559131812771965245176880",
    "61548439494181853220249582114142996432906093435682",
    "956233714326210876384175117134230"]

/-- The parity of the low twelve bits of a mask, by the reference fold. -/
def generatedAxisGlobalTwelveOctadLowParity (m : ℕ) : Bool :=
  (List.ofFn (fun i : Fin 12 => m.testBit i.val)).foldl Bool.xor false

/-- Singularity of a mask, as a function of the coordinatewise product of its two halves. -/
theorem generatedAxisGlobalTwelveOctadSingular_low (b : ℕ) :
    generatedAxisGlobalMaskSingular b =
      !generatedAxisGlobalTwelveOctadLowParity (Nat.land (Nat.land b (Nat.shiftRight b 12)) 4095) := by
  unfold generatedAxisGlobalMaskSingular generatedAxisGlobalTwelveOctadLowParity
  congr 2
  apply List.ofFn_inj.mpr
  funext i
  have h4095 : (4095 : ℕ).testBit i.val = true := by
    have := i.isLt
    interval_cases (i.val) <;> decide
  change (b.testBit i.val && b.testBit (i.val + 12)) =
    ((b &&& (b >>> 12)) &&& 4095).testBit i.val
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, h4095, Bool.and_true,
    Nat.add_comm 12]

/-- Singularity by one primitive table lookup. -/
def generatedAxisGlobalTwelveOctadFastSingular (b : ℕ) : Bool :=
  Nat.beq (Nat.land 1 (Nat.shiftRight generatedAxisGlobalTwelveOctadParityTable
    (Nat.land (Nat.land b (Nat.shiftRight b 12)) 4095))) 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check the parity table against the reference fold on all 4096 low masks.
/-- The parity table agrees with the reference parity on every twelve-bit mask. -/
theorem generatedAxisGlobalTwelveOctadParityTable_certificate : ∀ m : Fin 4096,
    Nat.beq (Nat.land 1 (Nat.shiftRight generatedAxisGlobalTwelveOctadParityTable m.val)) 0 =
      !generatedAxisGlobalTwelveOctadLowParity m.val := by
  decide +kernel

/-- The fast singularity test is the reference singularity test. -/
theorem generatedAxisGlobalTwelveOctadFastSingular_eq (b : ℕ) :
    generatedAxisGlobalTwelveOctadFastSingular b = generatedAxisGlobalMaskSingular b := by
  rw [generatedAxisGlobalTwelveOctadSingular_low]
  have hm : Nat.land (Nat.land b (Nat.shiftRight b 12)) 4095 < 4096 := by
    change (b &&& (b >>> 12)) &&& 4095 < 4096
    exact lt_of_le_of_lt (Nat.and_le_right) (by norm_num)
  exact generatedAxisGlobalTwelveOctadParityTable_certificate ⟨_, hm⟩

/-- Leaf selection in a balanced data tree by primitive operations. -/
def generatedAxisGlobalTwelveOctadFastTree (tr : GeneratedAxisGlobalMaskTree) (b : ℕ) :
    ℕ → ℕ :=
  GeneratedAxisGlobalMaskTree.rec (motive := fun _ => ℕ → ℕ) (fun v _ => v)
    (fun _ _ fl fr d =>
      cond (generatedAxisGlobalTwelveOctadFastBit b (Nat.sub d 1)) (fr (Nat.sub d 1))
        (fl (Nat.sub d 1))) tr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
