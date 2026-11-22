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

/-- **The SUBSET-SUM verifier machine as a host component.** The multi-stack Turing machine
that checks SUBSET-SUM certificates, packaged as a host component: it has seven stacks, each
holding symbols of the SAT verifier alphabet, its labels and its program are those of the
machine, and the list of its stacks names each of the seven stacks exactly once. -/
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

/-- **SUBSET-SUM is in NP.** SUBSET-SUM is the decision problem on bit strings that accepts $x$
exactly when $x$ encodes a target $t$ followed by natural numbers $a_1, \dots, a_n$ (each written
in binary and delimited) such that some, possibly empty, sublist of $a_1, \dots, a_n$ sums to
$t$. This decision problem belongs to NP: there are a polynomial $p$ with natural-number
coefficients and a polynomial-time computable verifier $R$ such that SUBSET-SUM accepts $x$
exactly when $R(x, w)$ holds for some bit string $w$ with $|w| \le p(|x|)$. -/
theorem subsetSumDec_mem_NP : subsetSumDec ∈ NP :=
  ⟨Polynomial.X, fun q => SSVerify.ssCheck q.1 q.2, isPolyTime_ssCheck,
    fun x => by simpa using SSVerify.subsetSumDec_iff x⟩

instance EmitSS.instFintypeΓ (k : EmitSS.K) : Fintype (EmitSS.Γ k) := by
  cases k <;> infer_instance

/-- **The VERTEX-COVER to SUBSET-SUM machine as a host component.** The multi-stack Turing
machine that computes the VERTEX-COVER to SUBSET-SUM reduction on bit strings, packaged as a
host component: its fifteen stacks (the output stack holds booleans, every other stack holds
symbols of the SAT verifier alphabet), its labels and its program are those of the machine, and
the list of its stacks names each of the fifteen stacks exactly once. -/
abbrev emitSSComp : Host.Comp where
  K := EmitSS.K
  Γ := EmitSS.Γ
  L := EmitSS.Lab
  prog := EmitSS.prog
  ks := [.X, .O, .A, .H, .N, .M, .C, .S1, .S2, .Y, .Z, .T, .L, .R, .Rt]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **The VERTEX-COVER to SUBSET-SUM reduction is polynomial-time.** The reduction map on bit
strings, which sends the encoding of a VERTEX-COVER instance $(k, G)$ to the encoding of the
SUBSET-SUM instance built from it (one base-4 number for each vertex and for each pair of
vertices of $G$, and a target) and every other bit string to the instance with no numbers and
target $1$, is computable in polynomial time. -/
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

/-- **SUBSET-SUM is NP-hard.** Let SUBSET-SUM be the decision problem on bit strings that
accepts exactly the strings encoding a target $t$ followed by natural numbers $a_1, \dots, a_n$
(each written in binary and delimited) such that some, possibly empty, sublist of
$a_1, \dots, a_n$ sums to $t$. Every decision problem $L$ in NP reduces to SUBSET-SUM by a
polynomial-time many-one reduction: there is a polynomial-time computable map $f$ on bit strings
such that, for every bit string $x$, $L$ accepts $x$ exactly when SUBSET-SUM accepts $f(x)$. -/
theorem subsetSumDec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L subsetSumDec :=
  npHard_of_polyManyOneRed vertexCoverDec_npHard vertexCoverDec_polyManyOneRed_subsetSumDec

/-- **SUBSET-SUM is NP-complete.** Let SUBSET-SUM be the decision problem on bit strings that
accepts exactly the strings encoding a target $t$ followed by natural numbers $a_1, \dots, a_n$
(each written in binary and delimited) such that some, possibly empty, sublist of
$a_1, \dots, a_n$ sums to $t$. Then SUBSET-SUM belongs to NP, and every decision problem $L$ in
NP reduces to SUBSET-SUM by a polynomial-time many-one reduction: there is a polynomial-time
computable map $f$ on bit strings such that, for every bit string $x$, $L$ accepts $x$ exactly
when SUBSET-SUM accepts $f(x)$. -/
theorem subsetSumDec_npComplete :
    subsetSumDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L subsetSumDec :=
  ⟨subsetSumDec_mem_NP, subsetSumDec_npHard⟩

end Cslib.Complexity.Karp
