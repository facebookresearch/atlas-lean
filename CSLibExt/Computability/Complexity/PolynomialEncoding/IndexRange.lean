/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat
public import MathlibExt.Computability.BinaryNatEncoding
import Mathlib.Tactic.Linarith
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy

/-!
# Emitting consecutive binary indices

Given a word of length $n$, write the canonical encoding of the list $[0,\ldots,n-1]$.
The machine repeatedly removes one input symbol, copies the remaining length to the
unary-to-binary emitter, and prepends the resulting frame to the output.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.IndexRange

open Turing Function MetaMathlibExt TM2Program TM2Embedding BitstringEncoding
open ComplexityTheory Karp SatVerifier

private abbrev Lab := UnaryNat.Lab ⊕ Fin 4

private def label (l : UnaryNat.Lab) : Lab :=
  if l = .done then .inr 0 else .inl l

private def prog : Lab → TM2.Stmt EmitSS.Γ Lab Bool
  | .inl l => mapS UnaryNat.embedding label (UnaryNat.prog true l)
  | .inr 0 => .pop .N (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .inr 1) (.goto fun _ => .inr 3)
  | .inr 1 => moveB .N .S1 EmitSS.valOf Sym.val (.inr 1) (.inr 2)
  | .inr 2 => splitB .S1 .N .A EmitSS.valOf Sym.val (fun _ => EmitSS.U)
      (.inr 2) (.inl (.emit .hv))
  | .inr _ => .halt

private theorem lift_run {n : ℕ} {v w : Bool} {S T : ∀ k, List (EmitSS.Γ k)}
    (h : RunLe (UnaryNat.prog true) n ⟨some (.emit .hv), v, S⟩ ⟨some .done, w, T⟩) :
    RunLe prog n ⟨some (.inl (.emit .hv)), v, S⟩ ⟨some (.inr 0), w, T⟩ := by
  have hem : Embeds UnaryNat.embedding label (UnaryNat.prog true) prog := by
    intro l
    by_cases hl : l = .done
    · exact Or.inr (by subst l; rfl)
    · exact Or.inl (by simp [label, hl, prog])
  have ha : Agree UnaryNat.embedding S S := by
    intro k
    change S k = (S k).map id
    simp
  obtain ⟨U, hu, he, _⟩ := runLe_embed label hem h ha
  have e : U = T := by
    funext k
    have hk : U k = (T k).map id := he k
    simpa using hk
  subst U
  exact hu

private def time (n : ℕ) := 720 * (n+1)^2

private theorem run (x : List Bool) (out : List Bool) (v : Bool)
    (S : ∀ k, List (EmitSS.Γ k)) (hin : S .N = x.map Sym.val)
    (ha : S .A = []) (hh : S .H = []) (ht : S .T = [])
    (hs : S .S1 = []) (ho : S .O = out) :
    ∃ w U, RunLe prog (time x.length) ⟨some (.inr 0), v, S⟩ ⟨some (.inr 3), w, U⟩ ∧
      U .O = bitEncode (List.range x.length) ++ out := by
  induction x generalizing out v S with
  | nil =>
    let U := update S EmitSS.K.N []
    have first : Run prog 1 ⟨some (.inr 0), v, S⟩ ⟨some (.inr 3), false, U⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, U, hin]
    exact ⟨false, U, first.le (by decide), ho⟩
  | cons b x ih =>
    let S₀ := update S EmitSS.K.N (x.map Sym.val)
    have first : Run prog 1 ⟨some (.inr 0), v, S⟩ ⟨some (.inr 1), true, S₀⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, S₀, hin]
    obtain ⟨S₁, second, hN, hs1, hA, hrest⟩ := copyB_run
      (M := prog) (first := .inr 1) (second := .inr 2) (next := .inl (.emit .hv))
      (a := EmitSS.K.N) (t := EmitSS.K.S1) (b := EmitSS.K.A)
      (da := EmitSS.valOf) (dt := EmitSS.valOf) (ga := Sym.val) (gt := Sym.val)
      (gb := fun _ => EmitSS.U) rfl rfl (by decide) (by decide) (by decide)
      (fun _ => rfl) (fun _ => rfl) x [] true S₀ (by simp [S₀]) rfl
      (by simp [S₀, hs, EndsBitBlock])
    obtain ⟨S₂, third, hO₂, hA₂, hH₂, hT₂, hframe⟩ :=
      UnaryNat.run_framed x.length out false S₁ (by simpa [S₀, ha, cnt] using hA)
        (by simpa [S₀, hh] using hrest .H (by decide) (by decide) (by decide))
        (by simpa [S₀, ht] using hrest .T (by decide) (by decide) (by decide))
        (by simpa [S₀, ho] using hrest .O (by decide) (by decide) (by decide))
    obtain ⟨w, U, fourth, result⟩ := ih _ false S₂
      (by rw [hframe .N (by decide) (by decide) (by decide) (by decide), hN]; simp [S₀])
      hA₂ hH₂ hT₂
      (by rw [hframe .S1 (by decide) (by decide) (by decide) (by decide), hs1]; simpa [S₀] using hs)
      hO₂
    refine ⟨w, U, (((first.trans second).le le_rfl).trans (lift_run third) |>.trans fourth).mono ?_,
      ?_⟩
    · simp only [time, List.length_cons]
      nlinarith only [Nat.zero_le x.length]
    · have enc (l : List ℕ) (n : ℕ) :
          bitEncode (l ++ [n]) = bitEncode l ++ delimit (bitEncode n) := by
        change (((l ++ [n]).map bitEncode).map delimit).flatten =
          ((l.map bitEncode).map delimit).flatten ++ delimit (bitEncode n)
        simp
      simpa [List.range_succ, enc, List.append_assoc] using result

/-- The encoded consecutive indices below the input length can be produced in
polynomial time, including the total cost of emitting all the binary indices. -/
theorem isPolyTime_encodeRange :
    IsPolyTime (fun x : List Bool => bitEncode (List.range x.length)) := by
  let c : Host.Comp := { UnaryNat.component true with
    L := Lab, finL := inferInstance, decL := inferInstance, prog := prog }
  apply Host.isPolyTime_reduction (c := c) (cX := EmitSS.K.N) (cO := EmitSS.K.O)
    (gX := Sym.val) (start := .inr 0) (done := .inr 3) (Equiv.refl Bool) _
    (Polynomial.C 720 * (Polynomial.X + 1)^2) rfl
  intro x
  let S := update (fun k : EmitSS.K => ([] : List (EmitSS.Γ k))) .N (x.map Sym.val)
  obtain ⟨w, U, hr, ho⟩ := run x [] false S
    (by simp [S]) (by simp [S]) (by simp [S]) (by simp [S]) (by simp [S]) (by simp [S])
  refine ⟨w, U, by simpa [time] using hr, ?_⟩
  change U EmitSS.K.O = List.map id _
  simpa using ho

end Cslib.Complexity.PolynomialEncoding.IndexRange
