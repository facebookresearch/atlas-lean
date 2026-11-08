/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete
public import CSLibExt.Computability.Complexity.Karp.CliqueCorrect
public import CSLibExt.Computability.Complexity.Karp.KGMap
public import CSLibExt.Computability.Complexity.Karp.CliqueEmit
public import CSLibExt.Computability.Complexity.Karp.CliqueVerify

/-!
# CLIQUE, INDEPENDENT-SET and (exact-size) VERTEX-COVER are NP-complete

The languages are those of `Karp.Clique`: graphs with a clique, an independent set, or a vertex
cover of exactly `k` vertices. For VERTEX-COVER this is the exact-size variant (Sipser's
convention), which differs from the at-most-`k` language only when `k > n`.

Karp's reductions SAT ≤ CLIQUE ≤ INDEPENDENT-SET ≤ VERTEX-COVER (spec `Karp.Clique`) are
polynomial-time:

* `reduceClique` by the SAT tokenizer followed by the emitter `EmitClique`
  (`TokThen.isPolyTime_out`; `isPolyTime_reduceClique`);
* `flipKG` and `isToVc` by the component `KGMap` in the reduction host
  (`isPolyTime_flipKG`, `isPolyTime_isToVc`).

With the correctness theorems of `Karp.CliqueCorrect` and NP-hardness of `satDec`, the three
languages are NP-hard. The verifier component `KGVerify` in the verifier host puts them in NP
(`cliqueDec_mem_NP`, `indSetDec_mem_NP`, `vertexCoverDec_mem_NP`), so all three are
NP-complete (`cliqueDec_npComplete`, `indSetDec_npComplete`, `vertexCoverDec_npComplete`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL MetaMathlibExt.ComplexityTheory

instance KGMap.instFintypeΓ (k : KGMap.K) : Fintype (KGMap.Γ k) := by
  cases k <;> infer_instance

/-- `KGMap` in mode `m` as a host component. -/
abbrev kgMapComp (m : KGMap.Mode) : Host.Comp where
  K := KGMap.K
  Γ := KGMap.Γ
  L := KGMap.Lab
  prog := KGMap.prog m
  ks := [.X, .O, .A, .B, .D, .Y]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

theorem isPolyTime_kgMap (m : KGMap.Mode) : IsPolyTime m.f :=
  Host.isPolyTime_reduction (c := kgMapComp m) (cX := KGMap.K.X) (cO := KGMap.K.O)
    (gX := SatVerifier.Sym.bit) (start := KGMap.start) (done := KGMap.Lab.done) (Equiv.refl Bool)
    m.f (Polynomial.C 3 * (Polynomial.X + 1)) rfl fun x => by
      obtain ⟨v', S', r, h⟩ := KGMap.run m x false (Function.update (fun _ => []) KGMap.K.X
        (x.map SatVerifier.Sym.bit)) (by simp) (fun k hk => by simp [hk])
      refine ⟨v', S', r.mono (le_of_eq ?_), ?_⟩
      · simp [Polynomial.eval_mul, Polynomial.eval_add]
      · rw [h]; simp [Equiv.refl_symm]

/-- **CLIQUE ≤ INDEPENDENT-SET is polynomial-time**. -/
theorem isPolyTime_flipKG : IsPolyTime flipKG := isPolyTime_kgMap .flip

/-- **INDEPENDENT-SET ≤ VERTEX-COVER is polynomial-time**. -/
theorem isPolyTime_isToVc : IsPolyTime isToVc := isPolyTime_kgMap .vc

theorem cliqueDec_polyManyOneRed_indSetDec : PolyManyOneRed cliqueDec indSetDec :=
  ⟨flipKG, isPolyTime_flipKG, cliqueDec_eq_indSetDec_flipKG⟩

theorem indSetDec_polyManyOneRed_vertexCoverDec : PolyManyOneRed indSetDec vertexCoverDec :=
  ⟨isToVc, isPolyTime_isToVc, indSetDec_eq_vertexCoverDec_isToVc⟩

instance EmitClique.instFintypeΓ (k : EmitClique.K) : Fintype (EmitClique.Γ k) := by
  cases k <;> infer_instance

/-- The CLIQUE emitter as an `Emitter`. -/
abbrev emitClique : Emitter where
  K := EmitClique.K
  Γ := EmitClique.Γ
  L := EmitClique.Lab
  prog := EmitClique.prog
  start := EmitClique.start
  done := .done
  start_ne_done := by decide
  prog_done := rfl
  cT := .T
  cO := .O
  cT_ne_cO := by decide
  iT := Equiv.refl _
  eO := Equiv.refl _
  g := toClique
  noOut := noKG
  B n := 8 * (n + 1) ^ 3
  B_mono a b h := by dsimp only; gcongr
  run φ v St hT hO h0 := by
    obtain ⟨v', S', r, h⟩ := EmitClique.run φ [] v St (by simpa using hT) hO h0
    exact ⟨v', S', r, by simpa using h⟩

theorem out_emitClique (x : List Bool) : TokThen.out emitClique x = reduceClique x := by
  unfold TokThen.out reduceClique
  cases decodeCNF x <;> rfl

/-- **SAT ≤ CLIQUE is polynomial-time**. -/
theorem isPolyTime_reduceClique : IsPolyTime reduceClique := by
  have h := TokThen.isPolyTime_out emitClique [.T, .O, .A, .B, .D, .E, .X, .C, .N] (by decide)
    (fun k => by cases k <;> decide)
    (Polynomial.C 8 * (Polynomial.X + 1) ^ 3 + Polynomial.C 2 * Polynomial.X + Polynomial.C 3)
    (fun n => by simp [emitClique]; omega)
  rwa [show TokThen.out emitClique = reduceClique from funext out_emitClique] at h

theorem satDec_polyManyOneRed_cliqueDec : PolyManyOneRed satDec cliqueDec :=
  ⟨reduceClique, isPolyTime_reduceClique, satDec_eq_cliqueDec_reduceClique⟩

/-- **CLIQUE is NP-hard**. -/
theorem cliqueDec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L cliqueDec :=
  npHard_of_polyManyOneRed Cslib.Complexity.CookLevin.Hardness.satDec_npHard
    satDec_polyManyOneRed_cliqueDec

/-- **INDEPENDENT-SET is NP-hard**. -/
theorem indSetDec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L indSetDec :=
  npHard_of_polyManyOneRed cliqueDec_npHard cliqueDec_polyManyOneRed_indSetDec

/-- **VERTEX-COVER (exact size `k`) is NP-hard**. -/
theorem vertexCoverDec_npHard :
    ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L vertexCoverDec :=
  npHard_of_polyManyOneRed indSetDec_npHard indSetDec_polyManyOneRed_vertexCoverDec

/-- `KGVerify` in mode `m` as a host component. -/
abbrev kgVerifyComp (m : KGVerify.Mode) : Host.Comp where
  K := KGVerify.K
  Γ := fun _ => SatVerifier.Sym
  finΓ := fun _ => SatVerifier.Sym.instFintype
  L := KGVerify.Lab
  prog := KGVerify.prog m
  ks := [.X, .W, .C, .N, .V, .T]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

theorem isPolyTime_kgCheck (m : KGVerify.Mode) :
    IsPolyTime fun q : List Bool × List Bool => KGVerify.kgCheck m q.1 q.2 :=
  Host.isPolyTime_verifier (c := kgVerifyComp m) (cX := KGVerify.K.X) (cW := KGVerify.K.W)
    (gX := SatVerifier.Sym.bit) (gW := SatVerifier.Sym.bit) (start := KGVerify.start)
    (yes := KGVerify.Lab.yes) (no := KGVerify.Lab.no) (KGVerify.kgCheck m)
    (Polynomial.C 8 * (Polynomial.X + 1) ^ 3) (fun h => by cases h) (fun h => by cases h) rfl rfl
    fun x w => by
      obtain ⟨v', S', r⟩ := KGVerify.run m x w false (Function.update (Function.update
        (fun _ => []) KGVerify.K.X (x.map SatVerifier.Sym.bit)) KGVerify.K.W
        (w.map SatVerifier.Sym.bit)) (by simp) (by simp) (fun k hX hW => by simp [hX, hW])
      exact ⟨v', S', r.mono (le_of_eq (by simp))⟩

/-- An `NP` membership from a verifier with witnesses no longer than the input. -/
theorem mem_NP_of_kgCheck {L : DecisionProblem} (m : KGVerify.Mode)
    (h : ∀ x, L x = true ↔ ∃ w, w.length ≤ x.length ∧ KGVerify.kgCheck m x w = true) : L ∈ NP :=
  ⟨Polynomial.X, fun q => KGVerify.kgCheck m q.1 q.2, isPolyTime_kgCheck m,
    fun x => by simpa using h x⟩

/-- **CLIQUE is in NP**. -/
theorem cliqueDec_mem_NP : cliqueDec ∈ NP := mem_NP_of_kgCheck .clique KGVerify.cliqueDec_iff

/-- **INDEPENDENT-SET is in NP**. -/
theorem indSetDec_mem_NP : indSetDec ∈ NP := mem_NP_of_kgCheck .indep KGVerify.indSetDec_iff

/-- **VERTEX-COVER (exact size `k`) is in NP**. -/
theorem vertexCoverDec_mem_NP : vertexCoverDec ∈ NP :=
  mem_NP_of_kgCheck .cover KGVerify.vertexCoverDec_iff

/-- **CLIQUE is NP-complete**. -/
theorem cliqueDec_npComplete :
    cliqueDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L cliqueDec :=
  ⟨cliqueDec_mem_NP, cliqueDec_npHard⟩

/-- **INDEPENDENT-SET is NP-complete**. -/
theorem indSetDec_npComplete :
    indSetDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L indSetDec :=
  ⟨indSetDec_mem_NP, indSetDec_npHard⟩

/-- **VERTEX-COVER (exact size `k`) is NP-complete**. -/
theorem vertexCoverDec_npComplete :
    vertexCoverDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L vertexCoverDec :=
  ⟨vertexCoverDec_mem_NP, vertexCoverDec_npHard⟩

end Cslib.Complexity.Karp
