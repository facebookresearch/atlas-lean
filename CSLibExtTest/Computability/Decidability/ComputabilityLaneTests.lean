/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.ArithmeticalHierarchy
public import CSLibExt.Computability.Decidability.Blum
public import CSLibExt.Computability.Decidability.ChurchTuring
public import CSLibExt.Computability.Decidability.CounterMachines
public import CSLibExt.Computability.Decidability.Degrees
public import CSLibExt.Computability.Decidability.Myhill
public import CSLibExt.Computability.Decidability.RAMMachines
public import CSLibExt.Computability.Decidability.SpecialSets

@[expose] public section

/-!
# Tests for the TCS computability lane

Concrete computations for the executable definitions added in this lane:
counter/RAM instruction steps and halting, the oracle-code decoder on valid
and invalid code numbers, fuel-indexed oracle evaluation, and the eventual
Blum-class API.
-/

set_option autoImplicit false

open Cslib.Decidability

namespace CSLibExtTest.Computability.Decidability.ComputabilityLane

/-- A URM-computable total function is computed by a multi-stack Turing machine. -/
example {f : ℕ → ℕ} (h : Cslib.URM.Computable 1 fun inputs ↦ Part.some (f (inputs 0))) :
    Nonempty (Turing.TM2Computable Computability.encodeNat Computability.encodeNat f) :=
  urmComputable_to_tm2 h

/-- A URM-decidable predicate is decidable by a multi-stack Turing machine. -/
example {P : ℕ → Prop} (h : Cslib.URM.Decidable P) : TM2Decidable P :=
  urmDecidable_to_tm2Decidable h

/-- A URM-recognizable predicate is recognizable by a multi-stack Turing machine. -/
example {P : ℕ → Prop} (h : Cslib.URM.Recognizable P) : TM2Recognizable P :=
  urmRecognizable_to_tm2Recognizable h

/-- A recursive isomorphism gives a 1-equivalence. -/
example {P Q : ℕ → Prop} (h : RecursiveIsomorphic P Q) : OneOneEquiv P Q :=
  recursiveIsomorphic_to_oneOneEquiv h

/-- `Σ₁ = RE`. -/
example {P : ℕ → Prop} : IsSigma 1 P ↔ REPred P :=
  sigma_one_eq_re

/-- `Σₙ ⊆ Πₙ₊₁`. -/
example {n : ℕ} {P : ℕ → Prop} (h : IsSigma n P) : IsPi (n + 1) P :=
  sigma_subset_pi_succ h

/-- `Σₙ ∪ Πₙ ⊆ Δₙ₊₁`. -/
example {n : ℕ} {P : ℕ → Prop} (h : IsSigma n P ∨ IsPi n P) : IsDelta (n + 1) P :=
  sigma_pi_subset_delta_succ h

/-- A productive set is not RE. -/
example {P : ℕ → Prop} (h : Productive P) : ¬ REPred P :=
  productive_not_re h

/-- An immune set is not RE. -/
example {P : ℕ → Prop} (h : Immune P) : ¬ REPred P :=
  immune_not_re h

/-- A simple set is not computable. -/
example {P : ℕ → Prop} (h : Simple P) : ¬ ComputablePred P :=
  simple_not_computable h

/-- A creative set is not computable. -/
example {P : ℕ → Prop} (h : Creative P) : ¬ ComputablePred P :=
  creative_not_computable h

/-- Turing reducibility is reflexive. -/
example (P : ℕ → Prop) : TuringReduciblePred P P :=
  turingReduciblePred_refl P

/-- Turing reducibility is transitive. -/
example {P Q R : ℕ → Prop} (hPQ : TuringReduciblePred P Q)
    (hQR : TuringReduciblePred Q R) : TuringReduciblePred P R :=
  turingReduciblePred_trans hPQ hQR

/-- The enumeration of oracle codes is surjective. -/
example : Function.Surjective oracleCodeOfNat :=
  oracleCodeOfNat_surjective

/-- The effective enumeration inverts the Gödel numbering. -/
example (c : OracleCode) : oracleCodeOfNat (encodeOracleCode c) = c :=
  oracleCodeOfNat_encode c

/-- Blum classes are monotone in the bound. -/
example {Φ : BlumMeasure} {t t' : ℕ → ℕ} {f : ℕ →. ℕ}
    (h : ∀ᶠ n in Filter.atTop, t n ≤ t' n) (hf : BlumClass Φ t f) :
    BlumClass Φ t' f :=
  BlumClass.mono h hf

/-- Blum-class membership unfolds to an eventual bound. -/
example {Φ : BlumMeasure} {t : ℕ → ℕ} {f : ℕ →. ℕ} :
    BlumClass Φ t f ↔
      ∃ c : Nat.Partrec.Code, c.eval = f ∧
        ∃ N, ∀ n, N ≤ n → ∃ m, m ≤ t n ∧ Φ.cost c n = Part.some m :=
  blumClass_iff Φ t f

/-- Counter `inc`: register `0` goes `5 ↦ 6`, program counter advances. -/
example : (counterStep [CounterInstr.inc 0] (counterInit [5])).regs 0 = 6 := rfl

/-- Counter `inc`: the program counter advances to `1`. -/
example : (counterStep [CounterInstr.inc 0] (counterInit [5])).pc = 1 := rfl

/-- Counter `dec` saturates at `0`. -/
example : (counterStep [CounterInstr.dec 0] (counterInit [0])).regs 0 = 0 := rfl

/-- Counter `dec` on a positive register decrements. -/
example : (counterStep [CounterInstr.dec 0] (counterInit [3])).regs 0 = 2 := rfl

/-- Counter `jz` jumps when the tested register is zero. -/
example : (counterStep [CounterInstr.jz 0 3] (counterInit [0])).pc = 3 := rfl

/-- Counter `jz` falls through when the tested register is nonzero. -/
example : (counterStep [CounterInstr.jz 0 3] (counterInit [5])).pc = 1 := rfl

/-- Counter step is sticky past the end of the program (immediate halting). -/
example : counterStep [CounterInstr.inc 0] ⟨5, fun _ => 0⟩ = ⟨5, fun _ => 0⟩ := rfl

/-- Counter execution: one `inc` step from `[5]` halts with output `6`. -/
example : 6 ∈ counterEval [CounterInstr.inc 0] [5] :=
  mem_counterEval_of_halted (t := 1) (by rfl) (by rfl)

/-- RAM `imm` resolves to the literal. -/
example : ramResolve ⟨0, 0, fun _ => 0⟩ (RAMAddr.imm 7) = 7 := rfl

/-- RAM `dir` resolves to the register contents. -/
example : ramResolve ⟨0, 0, fun i => if i = 1 then 20 else 0⟩ (RAMAddr.dir 1) = 20 := rfl

/-- RAM `ind` resolves through two register dereferences. -/
example : ramResolve ⟨0, 0, fun i => if i = 0 then 1 else if i = 1 then 42 else 0⟩
    (RAMAddr.ind 0) = 42 := rfl

/-- RAM `load` of an immediate sets the accumulator and advances. -/
example : (ramStep [RAMInstr.load (RAMAddr.imm 5)] (ramInit [0])).acc = 5 := rfl

/-- RAM direct `store` writes the accumulator to the named register. -/
example : (ramStep [RAMInstr.store (RAMDest.dir 2)] ⟨0, 7, fun _ => 0⟩).regs 2 = 7 := rfl

/-- RAM indirect `store` writes the accumulator to the register whose index
is the contents of the named register. -/
example : (ramStep [RAMInstr.store (RAMDest.ind 0)]
    ⟨0, 7, fun i => if i = 0 then 2 else 0⟩).regs 2 = 7 := rfl

/-- RAM `add` of a direct operand adds to the accumulator. -/
example : (ramStep [RAMInstr.add (RAMAddr.dir 1)] ⟨0, 3, fun i => if i = 1 then 4 else 0⟩).acc
    = 7 := rfl

/-- RAM `sub` saturates at `0`. -/
example : (ramStep [RAMInstr.sub (RAMAddr.dir 1)] ⟨0, 3, fun i => if i = 1 then 9 else 0⟩).acc
    = 0 := rfl

/-- RAM `jz` jumps when the accumulator is zero. -/
example : (ramStep [RAMInstr.jz 9] ⟨0, 0, fun _ => 0⟩).pc = 9 := rfl

/-- RAM `jz` falls through when the accumulator is nonzero. -/
example : (ramStep [RAMInstr.jz 9] ⟨0, 3, fun _ => 0⟩).pc = 1 := rfl

/-- RAM `halt` jumps to the end of the program. -/
example : (ramStep [RAMInstr.halt] ⟨0, 7, fun _ => 0⟩).pc = 1 := rfl

/-- RAM step is sticky past the end of the program (immediate halting). -/
example : ramStep [RAMInstr.load (RAMAddr.imm 5)] ⟨3, 0, fun _ => 0⟩ =
    ⟨3, 0, fun _ => 0⟩ := rfl

/-- RAM execution: `load 5; halt` halts with accumulator `5`. -/
example : 5 ∈ ramEval [RAMInstr.load (RAMAddr.imm 5), RAMInstr.halt] [] :=
  mem_ramEval_of_halted (t := 2) (by rfl) (by rfl)

/-- Decoder round trip on a leaf code. -/
example : decodeOracleCode (encodeOracleCode OracleCode.zero) = some OracleCode.zero :=
  decodeOracleCode_encode _

/-- Decoder round trip on a composite code. -/
example : decodeOracleCode (encodeOracleCode (OracleCode.pair OracleCode.zero OracleCode.succ))
    = some (OracleCode.pair OracleCode.zero OracleCode.succ) :=
  decodeOracleCode_encode _

/-- Decoder on code number `0` gives `zero`. -/
example : decodeOracleCode 0 = some OracleCode.zero := rfl

/-- Decoder on code number `2 = pair 1 0` gives `succ`. -/
example : decodeOracleCode (Nat.pair 1 0) = some OracleCode.succ := by
  simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair]

/-- Decoder on code number `1` gives `none` (`1 = pair 0 1`, leaf tag with
nonzero payload). -/
example : decodeOracleCode 1 = none := rfl

/-- Decoder on code number `9 = pair 0 3` gives `none` (leaf tag with nonzero
payload). -/
example : decodeOracleCode (Nat.pair 0 3) = none := by
  simp [decodeOracleCode, decodeOracleCodeFuel, Nat.unpair_pair]

/-- Fuel-indexed oracle evaluation: fuel `0` never answers. -/
example : oracleEvaln (fun _ => none) 0 OracleCode.zero 0 = none := by
  simp [oracleEvaln]

/-- Fuel-indexed oracle evaluation: `zero` needs its input within fuel. -/
example : oracleEvaln (fun _ => none) 1 OracleCode.zero 0 = some 0 := by
  simp [oracleEvaln]

/-- Fuel-indexed oracle evaluation: input past the fuel guard fails. -/
example : oracleEvaln (fun _ => none) 1 OracleCode.zero 5 = none := by
  simp [oracleEvaln]

/-- Fuel-indexed oracle evaluation: the `oracle` instruction queries the oracle. -/
example : oracleEvaln (fun _ => some 42) 1 OracleCode.oracle 0 = some 42 := by
  simp [oracleEvaln]

/-- Fuel-indexed oracle evaluation: `pair` combines sub-evaluations. -/
example : oracleEvaln (fun _ => none) 1 (OracleCode.pair OracleCode.zero OracleCode.succ) 0
    = some (Nat.pair 0 1) := by
  simp [oracleEvaln]

/-- Unbounded oracle evaluation with a nowhere-defined oracle is `none`. -/
example : oracleEval (fun _ => none) OracleCode.oracle 0 = Part.none := by
  apply Part.eq_none_iff.2
  intro y hy
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hy
  cases k <;> simp [oracleEvaln] at hk

end CSLibExtTest.Computability.Decidability.ComputabilityLane
