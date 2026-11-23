/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete
public import CSLibExt.Computability.Complexity.Karp.ColorCorrect
public import CSLibExt.Computability.Complexity.Karp.ColorVerify
public import CSLibExt.Computability.Complexity.Karp.ColorEmit

/-!
# 3-COLOR is NP-complete

SAT ≤ 3-COLOR (spec `Karp.Color`) is polynomial-time: the SAT tokenizer followed by the emitter
`EmitColor` (`TokThen.isPolyTime_out`; `isPolyTime_reduceCol`). With `satDec_eq_col3Dec_reduceCol`
and NP-hardness of `satDec`, 3-COLOR is NP-hard; the verifier component `ColVerify` in the
verifier host puts it in NP (`col3Dec_mem_NP`), so it is NP-complete (`col3Dec_npComplete`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL MetaMathlibExt.ComplexityTheory

/-- **The 3-COLOR verifier as a host component.** The component machine whose stacks are the
seven stacks $X, W, N, P, T, U, V$ of the 3-COLOR verifier machine, listed in that order and each
over the token alphabet of the SAT verifier, and whose labels and program are those of the
3-COLOR verifier machine. -/
abbrev colVerifyComp : Host.Comp where
  K := ColVerify.K
  Γ := fun _ => SatVerifier.Sym
  finΓ := fun _ => SatVerifier.Sym.instFintype
  L := ColVerify.Lab
  prog := ColVerify.prog
  ks := [.X, .W, .N, .P, .T, .U, .V]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

theorem isPolyTime_colCheck :
    IsPolyTime fun q : List Bool × List Bool => ColVerify.colCheck q.1 q.2 :=
  Host.isPolyTime_verifier (c := colVerifyComp) (cX := ColVerify.K.X) (cW := ColVerify.K.W)
    (gX := SatVerifier.Sym.bit) (gW := SatVerifier.Sym.bit) (start := ColVerify.start)
    (yes := ColVerify.Lab.yes) (no := ColVerify.Lab.no) ColVerify.colCheck
    (Polynomial.C 8 * (Polynomial.X + 1) ^ 3) (fun h => by cases h) (fun h => by cases h) rfl rfl
    fun x w => by
      obtain ⟨v', S', r⟩ := ColVerify.run x w false (Function.update (Function.update
        (fun _ => []) ColVerify.K.X (x.map SatVerifier.Sym.bit)) ColVerify.K.W
        (w.map SatVerifier.Sym.bit)) (by simp) (by simp) (fun k hX hW => by simp [hX, hW])
      exact ⟨v', S', r.mono (le_of_eq (by simp))⟩

/-- **3-COLOR is in NP**. -/
theorem col3Dec_mem_NP : col3Dec ∈ NP :=
  ⟨Polynomial.C 2 * Polynomial.X, fun q => ColVerify.colCheck q.1 q.2, isPolyTime_colCheck,
    fun x => by simpa using ColVerify.col3Dec_iff x⟩

instance EmitColor.instFintypeΓ (k : EmitColor.K) : Fintype (EmitColor.Γ k) := by
  cases k <;> infer_instance

/-- **The 3-COLOR emitter.** The emitter whose stacks, alphabets, labels, program and start label
are those of the 3-COLOR emitter machine, which exits at the machine's final label, reads the
tokens of a CNF formula from stack $T$ and writes its output bits on stack $O$ (both symbol maps
being the identity), and has step bound $B(n) = 500 (n + 1)^4$ for $n$ tokens. Its output for a
CNF formula $\varphi$ is the encoded 3-COLOR instance of $\varphi$, and for an undecodable input
the encoding of the complete graph $K_4$. -/
abbrev emitColor : Emitter where
  K := EmitColor.K
  Γ := EmitColor.Γ
  L := EmitColor.Lab
  prog := EmitColor.prog
  start := EmitColor.start
  done := .done
  start_ne_done := by decide
  prog_done := rfl
  cT := .T
  cO := .O
  cT_ne_cO := by decide
  iT := Equiv.refl _
  eO := Equiv.refl _
  g := toCol
  noOut := noCol
  B n := 500 * (n + 1) ^ 4
  B_mono a b h := by dsimp only; gcongr
  run φ v St hT hO h0 := by
    obtain ⟨v', S', r, h⟩ := EmitColor.run φ [] v St (by simpa using hT) hO h0
    exact ⟨v', S', r, by simpa using h⟩

theorem out_emitColor (x : List Bool) : TokThen.out emitColor x = reduceCol x := by
  unfold TokThen.out reduceCol
  cases decodeCNF x <;> rfl

/-- **The SAT-to-3-COLOR reduction is polynomial-time.** The map on bit strings that sends a
string decoding to a CNF formula $\varphi$ to the encoding of the 3-COLOR instance of $\varphi$,
and every other string to the encoding of the complete graph $K_4$, is computable in polynomial
time. -/
theorem isPolyTime_reduceCol : IsPolyTime reduceCol := by
  have h := TokThen.isPolyTime_out emitColor [.T, .O, .N, .R, .D, .E, .A, .P, .F, .U, .X, .B, .W]
    (by decide) (fun k => by cases k <;> decide)
    (Polynomial.C 500 * (Polynomial.X + 1) ^ 4 + Polynomial.C 2 * Polynomial.X + Polynomial.C 3)
    (fun n => by simp [emitColor]; omega)
  rwa [show TokThen.out emitColor = reduceCol from funext out_emitColor] at h

theorem satDec_polyManyOneRed_col3Dec : PolyManyOneRed satDec col3Dec :=
  ⟨reduceCol, isPolyTime_reduceCol, satDec_eq_col3Dec_reduceCol⟩

/-- **3-COLOR is NP-hard.** Every decision problem in NP reduces to 3-COLOR by a polynomial-time
many-one reduction. -/
theorem col3Dec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L col3Dec :=
  npHard_of_polyManyOneRed Cslib.Complexity.CookLevin.Hardness.satDec_npHard
    satDec_polyManyOneRed_col3Dec

/-- **3-COLOR is NP-complete.** 3-COLOR is in NP, and every decision problem in NP reduces to
3-COLOR by a polynomial-time many-one reduction. -/
theorem col3Dec_npComplete :
    col3Dec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L col3Dec :=
  ⟨col3Dec_mem_NP, col3Dec_npHard⟩

end Cslib.Complexity.Karp
