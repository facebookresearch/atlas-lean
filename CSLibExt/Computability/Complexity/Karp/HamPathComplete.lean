/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete
public import CSLibExt.Computability.Complexity.Karp.HamPathCorrect
public import CSLibExt.Computability.Complexity.Karp.HamPathVerify
public import CSLibExt.Computability.Complexity.Karp.HamPathEmit

/-!
# HAMPATH is NP-complete

SAT ≤ HAMPATH (Sipser, Theorem 7.46; spec `Karp.HamPath`) is polynomial-time: the SAT tokenizer
followed by the emitter `EmitHam` (`TokThen.isPolyTime_out`; `isPolyTime_reduceHam`). With
`satDec_eq_hamPathDec_reduceHam` and NP-hardness of `satDec`, HAMPATH is NP-hard; the verifier
component `HamVerify` in the verifier host puts it in NP (`hamPathDec_mem_NP`), so it is
NP-complete (`hamPathDec_npComplete`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL MetaMathlibExt.ComplexityTheory

/-- `HamVerify` as a host component. -/
abbrev hamVerifyComp : Host.Comp where
  K := HamVerify.K
  Γ := fun _ => SatVerifier.Sym
  finΓ := fun _ => SatVerifier.Sym.instFintype
  L := HamVerify.Lab
  prog := HamVerify.prog
  ks := [.X, .W, .S, .T, .N, .C, .A, .B, .E, .Z, .R, .Q]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

theorem isPolyTime_hamCheck :
    IsPolyTime fun q : List Bool × List Bool => HamVerify.hamCheck q.1 q.2 :=
  Host.isPolyTime_verifier (c := hamVerifyComp) (cX := HamVerify.K.X) (cW := HamVerify.K.W)
    (gX := SatVerifier.Sym.bit) (gW := SatVerifier.Sym.bit) (start := HamVerify.start)
    (yes := HamVerify.Lab.yes) (no := HamVerify.Lab.no) HamVerify.hamCheck
    (Polynomial.C 100 * (Polynomial.X + 1) ^ 4) (fun h => by cases h) (fun h => by cases h) rfl
    rfl fun x w => by
      obtain ⟨v', S', r⟩ := HamVerify.run x w false (Function.update (Function.update
        (fun _ => []) HamVerify.K.X (x.map SatVerifier.Sym.bit)) HamVerify.K.W
        (w.map SatVerifier.Sym.bit)) (by simp) (by simp) (fun k hX hW => by simp [hX, hW])
      exact ⟨v', S', r.mono (le_of_eq (by simp))⟩

/-- **HAMPATH is in NP**. -/
theorem hamPathDec_mem_NP : hamPathDec ∈ NP :=
  ⟨(Polynomial.X + 1) ^ 2, fun q => HamVerify.hamCheck q.1 q.2, isPolyTime_hamCheck,
    fun x => by simpa using HamVerify.hamPathDec_iff x⟩

instance EmitHam.instFintypeΓ (k : EmitHam.K) : Fintype (EmitHam.Γ k) := by
  cases k <;> infer_instance

/-- The HAMPATH emitter as an `Emitter`. -/
abbrev emitHam : Emitter where
  K := EmitHam.K
  Γ := EmitHam.Γ
  L := EmitHam.Lab
  prog := EmitHam.prog
  start := EmitHam.start
  done := .done
  start_ne_done := by decide
  prog_done := rfl
  cT := .T
  cO := .O
  cT_ne_cO := by decide
  iT := Equiv.refl _
  eO := Equiv.refl _
  g := toHam
  noOut := noHam
  B n := 2000 * (n + 1) ^ 5
  B_mono a b h := by dsimp only; gcongr
  run φ v St hT hO h0 := by
    obtain ⟨v', S', r, h⟩ := EmitHam.run φ [] v St (by simpa using hT) hO h0
    exact ⟨v', S', r, by simpa using h⟩

theorem out_emitHam (x : List Bool) : TokThen.out emitHam x = reduceHam x := by
  unfold TokThen.out reduceHam
  cases decodeCNF x <;> rfl

/-- **SAT ≤ HAMPATH is polynomial-time**. -/
theorem isPolyTime_reduceHam : IsPolyTime reduceHam := by
  have h := TokThen.isPolyTime_out emitHam
    [.T, .O, .F, .V, .W, .Q, .G, .X, .Y, .C, .M, .P, .N, .R, .L, .J, .D, .Z]
    (by decide) (fun k => by cases k <;> decide)
    (Polynomial.C 2000 * (Polynomial.X + 1) ^ 5 + Polynomial.C 2 * Polynomial.X +
      Polynomial.C 3) (fun n => by simp [emitHam]; omega)
  rwa [show TokThen.out emitHam = reduceHam from funext out_emitHam] at h

theorem satDec_polyManyOneRed_hamPathDec : PolyManyOneRed satDec hamPathDec :=
  ⟨reduceHam, isPolyTime_reduceHam, satDec_eq_hamPathDec_reduceHam⟩

/-- **HAMPATH is NP-hard**. -/
theorem hamPathDec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L hamPathDec :=
  npHard_of_polyManyOneRed Cslib.Complexity.CookLevin.Hardness.satDec_npHard
    satDec_polyManyOneRed_hamPathDec

/-- **HAMPATH is NP-complete** (Sipser, Theorem 7.46). -/
theorem hamPathDec_npComplete :
    hamPathDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L hamPathDec :=
  ⟨hamPathDec_mem_NP, hamPathDec_npHard⟩

end Cslib.Complexity.Karp
