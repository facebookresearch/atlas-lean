/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CliqueComplete
public import CSLibExt.Computability.Complexity.Karp.SubsetSumCorrect
public import CSLibExt.Computability.Complexity.Karp.SubsetSumVerify
public import CSLibExt.Computability.Complexity.Karp.SubsetSumEmit

/-!
# SUBSET-SUM is NP-complete

VERTEX-COVER ≤ SUBSET-SUM (spec `Karp.SubsetSum`, from the exact-size VERTEX-COVER of
`Karp.Clique`) is polynomial-time: the component `EmitSS` in the reduction host
(`isPolyTime_reduceSS`). With `vertexCoverDec_eq_subsetSumDec_reduceSS` and NP-hardness of
VERTEX-COVER (`Karp.CliqueComplete`), SUBSET-SUM is NP-hard; the verifier component `SSVerify` in
the verifier host puts it in NP (`subsetSumDec_mem_NP`), so it is NP-complete
(`subsetSumDec_npComplete`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin MetaMathlibExt.ComplexityTheory

/-- `SSVerify` as a host component. -/
abbrev ssVerifyComp : Host.Comp where
  K := SSVerify.K
  Γ := fun _ => SatVerifier.Sym
  finΓ := fun _ => SatVerifier.Sym.instFintype
  L := SSVerify.Lab
  prog := SSVerify.prog
  ks := [.X, .W, .T, .A, .B, .P, .Q]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

theorem isPolyTime_ssCheck :
    IsPolyTime fun q : List Bool × List Bool => SSVerify.ssCheck q.1 q.2 :=
  Host.isPolyTime_verifier (c := ssVerifyComp) (cX := SSVerify.K.X) (cW := SSVerify.K.W)
    (gX := SatVerifier.Sym.bit) (gW := SatVerifier.Sym.bit) (start := SSVerify.start)
    (yes := SSVerify.Lab.yes) (no := SSVerify.Lab.no) SSVerify.ssCheck
    (Polynomial.C 16 * (Polynomial.X + 1) ^ 3) (fun h => by cases h) (fun h => by cases h) rfl rfl
    fun x w => by
      obtain ⟨v', S', r⟩ := SSVerify.run x w false (Function.update (Function.update
        (fun _ => []) SSVerify.K.X (x.map SatVerifier.Sym.bit)) SSVerify.K.W
        (w.map SatVerifier.Sym.bit)) (by simp) (by simp) (fun k hX hW => by simp [hX, hW])
      exact ⟨v', S', r.mono (le_of_eq (by simp))⟩

/-- **SUBSET-SUM is in NP**. -/
theorem subsetSumDec_mem_NP : subsetSumDec ∈ NP :=
  ⟨Polynomial.X, fun q => SSVerify.ssCheck q.1 q.2, isPolyTime_ssCheck,
    fun x => by simpa using SSVerify.subsetSumDec_iff x⟩

instance EmitSS.instFintypeΓ (k : EmitSS.K) : Fintype (EmitSS.Γ k) := by
  cases k <;> infer_instance

/-- `EmitSS` as a host component. -/
abbrev emitSSComp : Host.Comp where
  K := EmitSS.K
  Γ := EmitSS.Γ
  L := EmitSS.Lab
  prog := EmitSS.prog
  ks := [.X, .O, .A, .H, .N, .M, .C, .S1, .S2, .Y, .Z, .T, .L, .R, .Rt]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **VERTEX-COVER ≤ SUBSET-SUM is polynomial-time**. -/
theorem isPolyTime_reduceSS : IsPolyTime reduceSS :=
  Host.isPolyTime_reduction (c := emitSSComp) (cX := EmitSS.K.X) (cO := EmitSS.K.O)
    (gX := SatVerifier.Sym.bit) (start := EmitSS.start) (done := EmitSS.Lab.done)
    (Equiv.refl Bool) reduceSS (Polynomial.C 40 * (Polynomial.X + 1) ^ 4) rfl fun x => by
      obtain ⟨v', S', r, h⟩ := EmitSS.run x false (Function.update (fun _ => []) EmitSS.K.X
        (x.map SatVerifier.Sym.bit)) (by simp) (fun k hk => by simp [hk])
      refine ⟨v', S', r.mono (le_of_eq ?_), ?_⟩
      · simp
      · rw [h]; simp [Equiv.refl_symm]

theorem vertexCoverDec_polyManyOneRed_subsetSumDec : PolyManyOneRed vertexCoverDec subsetSumDec :=
  ⟨reduceSS, isPolyTime_reduceSS, vertexCoverDec_eq_subsetSumDec_reduceSS⟩

/-- **SUBSET-SUM is NP-hard**. -/
theorem subsetSumDec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L subsetSumDec :=
  npHard_of_polyManyOneRed vertexCoverDec_npHard vertexCoverDec_polyManyOneRed_subsetSumDec

/-- **SUBSET-SUM is NP-complete**. -/
theorem subsetSumDec_npComplete :
    subsetSumDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L subsetSumDec :=
  ⟨subsetSumDec_mem_NP, subsetSumDec_npHard⟩

end Cslib.Complexity.Karp
