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

/-- **The CLIQUE-to-INDEPENDENT-SET and INDEPENDENT-SET-to-VERTEX-COVER map as a host
component.** For a mode $m$, standing for the reduction from CLIQUE to INDEPENDENT-SET or the one
from INDEPENDENT-SET to VERTEX-COVER, this is the host component whose stacks (listed as
$X, O, A, B, D, Y$), stack alphabets, labels and program are those of the Turing machine that
computes the reduction of mode $m$. -/
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

/-- **CLIQUE ≤ INDEPENDENT-SET is polynomial-time.** The map on bit strings that sends
$1^k 0 1^n 0 b$, for natural numbers $k$ and $n$ and a bit string $b$, to $1^k 0 1^n 0 \bar b$,
where $\bar b$ is $b$ with every bit complemented, and sends every string not of this form to the
string $100$, is computable in polynomial time. -/
theorem isPolyTime_flipKG : IsPolyTime flipKG := isPolyTime_kgMap .flip

/-- **INDEPENDENT-SET ≤ VERTEX-COVER is polynomial-time.** The map on bit strings that sends
$1^k 0 1^n 0 b$, for natural numbers $k \le n$ and a bit string $b$, to $1^{n-k} 0 1^n 0 b$, and
sends every other string (including $1^k 0 1^n 0 b$ with $k > n$) to the string $100$, is
computable in polynomial time. -/
theorem isPolyTime_isToVc : IsPolyTime isToVc := isPolyTime_kgMap .vc

theorem cliqueDec_polyManyOneRed_indSetDec : PolyManyOneRed cliqueDec indSetDec :=
  ⟨flipKG, isPolyTime_flipKG, cliqueDec_eq_indSetDec_flipKG⟩

theorem indSetDec_polyManyOneRed_vertexCoverDec : PolyManyOneRed indSetDec vertexCoverDec :=
  ⟨isToVc, isPolyTime_isToVc, indSetDec_eq_vertexCoverDec_isToVc⟩

instance EmitClique.instFintypeΓ (k : EmitClique.K) : Fintype (EmitClique.Γ k) := by
  cases k <;> infer_instance

/-- **The CLIQUE emitter.** The emitter given by the CLIQUE emitter machine, run from its start
label to its exit label, with token stack $T$ and output stack $O$. Its output on a CNF formula
$\varphi$ is Karp's CLIQUE instance of $\varphi$, its output on undecodable input is the string
$100$, and its step bound on $m$ tokens is $8(m + 1)^3$. Let $\varphi$ be a CNF formula with $m$
tokens. Started with the tokens of $\varphi$ on $T$, last token on top, and all other stacks
empty, the machine reaches its exit label within $8(m + 1)^3$ steps, with Karp's CLIQUE instance
of $\varphi$ on $O$, first bit on top. -/
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

/-- **SAT ≤ CLIQUE is polynomial-time.** Let $f$ be the map on bit strings that sends the
binary code of a CNF formula $\varphi$ to the encoding of Karp's CLIQUE instance $(k, G)$ of
$\varphi$, and sends every string that is not the code of a CNF formula to the string $100$.
Here $G$ has one vertex per literal occurrence in $\varphi$, two occurrences are adjacent when
they lie in different clauses and are not complementary, and $k$ is the number of clauses of
$\varphi$. Then $f$ is computable in polynomial time. -/
theorem isPolyTime_reduceClique : IsPolyTime reduceClique := by
  have h := TokThen.isPolyTime_out emitClique [.T, .O, .A, .B, .D, .E, .X, .C, .N] (by decide)
    (fun k => by cases k <;> decide)
    (Polynomial.C 8 * (Polynomial.X + 1) ^ 3 + Polynomial.C 2 * Polynomial.X + Polynomial.C 3)
    (fun n => by simp [emitClique]; omega)
  rwa [show TokThen.out emitClique = reduceClique from funext out_emitClique] at h

theorem satDec_polyManyOneRed_cliqueDec : PolyManyOneRed satDec cliqueDec :=
  ⟨reduceClique, isPolyTime_reduceClique, satDec_eq_cliqueDec_reduceClique⟩

/-- **CLIQUE is NP-hard.** Every decision problem $L$ in NP has a polynomial-time many-one
reduction to CLIQUE: a polynomial-time computable map $f$ on bit strings such that, for every
bit string $x$, $L$ accepts $x$ exactly when CLIQUE accepts $f(x)$. -/
theorem cliqueDec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L cliqueDec :=
  npHard_of_polyManyOneRed Cslib.Complexity.CookLevin.Hardness.satDec_npHard
    satDec_polyManyOneRed_cliqueDec

/-- **INDEPENDENT-SET is NP-hard.** Every decision problem $L$ in NP has a polynomial-time
many-one reduction to INDEPENDENT-SET: a polynomial-time computable map $f$ on bit strings such
that, for every bit string $x$, $L$ accepts $x$ exactly when INDEPENDENT-SET accepts $f(x)$. -/
theorem indSetDec_npHard : ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L indSetDec :=
  npHard_of_polyManyOneRed cliqueDec_npHard cliqueDec_polyManyOneRed_indSetDec

/-- **VERTEX-COVER (exact size `k`) is NP-hard.** Every decision problem in NP reduces by a
polynomial-time many-one reduction to the decision problem VERTEX-COVER, which accepts exactly
the valid encodings of a number $k$ and a graph $G$ such that $G$ has a vertex cover of exactly
$k$ vertices. -/
theorem vertexCoverDec_npHard :
    ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L vertexCoverDec :=
  npHard_of_polyManyOneRed indSetDec_npHard indSetDec_polyManyOneRed_vertexCoverDec

/-- **The CLIQUE, INDEPENDENT-SET and VERTEX-COVER verifier as a host component.** For a mode $m$
(clique, independent set or vertex cover), this is the host component whose stacks are
$X, W, C, N, V, T$, each over the symbol alphabet of the SAT verifier, and whose labels and
program are those of the verifier machine of mode $m$. -/
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

/-- **NP membership from the CLIQUE, INDEPENDENT-SET and VERTEX-COVER verifier.** Let $L$ be a
decision problem, let $m$ be a mode (clique, independent set or vertex cover), and let $V_m$ be
the verifier of mode $m$. If for every bit string $x$, $L$ accepts $x$ exactly when there is a
bit string $w$ with $|w| \le |x|$ such that $V_m$ accepts $(x, w)$, then $L$ is in NP. -/
theorem mem_NP_of_kgCheck {L : DecisionProblem} (m : KGVerify.Mode)
    (h : ∀ x, L x = true ↔ ∃ w, w.length ≤ x.length ∧ KGVerify.kgCheck m x w = true) : L ∈ NP :=
  ⟨Polynomial.X, fun q => KGVerify.kgCheck m q.1 q.2, isPolyTime_kgCheck m,
    fun x => by simpa using h x⟩

/-- **CLIQUE is in NP**. -/
theorem cliqueDec_mem_NP : cliqueDec ∈ NP := mem_NP_of_kgCheck .clique KGVerify.cliqueDec_iff

/-- **INDEPENDENT-SET is in NP**. -/
theorem indSetDec_mem_NP : indSetDec ∈ NP := mem_NP_of_kgCheck .indep KGVerify.indSetDec_iff

/-- **VERTEX-COVER (exact size `k`) is in NP.** The decision problem VERTEX-COVER, which accepts
exactly the valid encodings of a number $k$ and a graph $G$ such that $G$ has a vertex cover of
exactly $k$ vertices, is in NP. -/
theorem vertexCoverDec_mem_NP : vertexCoverDec ∈ NP :=
  mem_NP_of_kgCheck .cover KGVerify.vertexCoverDec_iff

/-- **CLIQUE is NP-complete.** CLIQUE lies in NP, and every decision problem in NP has a
polynomial-time many-one reduction to CLIQUE. -/
theorem cliqueDec_npComplete :
    cliqueDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L cliqueDec :=
  ⟨cliqueDec_mem_NP, cliqueDec_npHard⟩

/-- **INDEPENDENT-SET is NP-complete.** INDEPENDENT-SET lies in NP, and every decision problem
in NP has a polynomial-time many-one reduction to INDEPENDENT-SET. -/
theorem indSetDec_npComplete :
    indSetDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L indSetDec :=
  ⟨indSetDec_mem_NP, indSetDec_npHard⟩

/-- **VERTEX-COVER (exact size `k`) is NP-complete.** The decision problem VERTEX-COVER, which
accepts exactly the valid encodings of a number $k$ and a graph $G$ such that $G$ has a vertex
cover of exactly $k$ vertices, is in NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction. -/
theorem vertexCoverDec_npComplete :
    vertexCoverDec ∈ NP ∧ ∀ L : DecisionProblem, L ∈ NP → PolyManyOneRed L vertexCoverDec :=
  ⟨vertexCoverDec_mem_NP, vertexCoverDec_npHard⟩

end Cslib.Complexity.Karp
