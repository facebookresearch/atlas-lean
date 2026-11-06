/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Karp.SubsetSumEmit
public import CSLibExt.Computability.Complexity.FramedCNF.Block
public import CSLibExt.Computability.Complexity.Host

/-!
# Reusable unary-count to canonical binary Nat conversion

Reuse the existing SUBSET-SUM emitter's actual halving and target-writing
phases, then charge explicit cleanup of their scratch stacks. The framed
variant preserves a previous output suffix; the raw variant removes just
the new frame with the shared block reader. No second arithmetic kernel or
new Nat representation is introduced.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.UnaryNat

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program
open MetaMathlibExt.TM2Embedding MetaMathlibExt.BitstringEncoding
open Karp SatVerifier

/-- **Control labels of the unary-to-binary converter.**
Existing emitter labels and the cleanup/unframing continuation. -/
inductive Lab | emit (l : EmitSS.Lab) | clean | read | back | done
  deriving DecidableEq

/-- **Label enumeration of the unary-to-binary converter.**
The finite label enumeration uses the existing emitter enumeration
and two Boolean choices, without a noncomputable list conversion. -/
def labEquiv : Lab ≃ EmitSS.Lab ⊕ Bool ⊕ Bool where
  toFun
    | .emit l => .inl l
    | .clean => .inr (.inl false)
    | .read => .inr (.inl true)
    | .back => .inr (.inr false)
    | .done => .inr (.inr true)
  invFun
    | .inl l => .emit l
    | .inr (.inl false) => .clean
    | .inr (.inl true) => .read
    | .inr (.inr false) => .back
    | .inr (.inr true) => .done
  left_inv l := by cases l <;> rfl
  right_inv l := by
    rcases l with l | b | b
    · rfl
    all_goals cases b <;> rfl

instance : Fintype Lab := Fintype.ofEquiv _ labEquiv.symm

/-- **Emitter stack embedding in the unary-to-binary converter.**
The component retains the existing emitter's heterogeneous alphabets. -/
def embedding : SEmb EmitSS.Γ EmitSS.Γ :=
  ⟨id, injective_id, fun _ => Equiv.refl _⟩

/-- **Label map from the emitter halt to scratch cleanup.**
The actual emitter halt is followed by charged scratch cleanup. -/
def emitLabel (l : EmitSS.Lab) : Lab :=
  if l = .done then .clean else .emit l

/-- **Program of the unary-to-binary converter.**
`framed = true` keeps the new frame; otherwise only that frame is
removed, preserving any earlier output below it. -/
def prog (framed : Bool) : Lab → TM2.Stmt EmitSS.Γ Lab Bool
  | .emit l => mapS embedding emitLabel (EmitSS.prog l)
  | .clean => cleanS [.A, .H, .T] .clean (if framed then .done else .read)
  | .read => FramedCNF.Block.read .O .X some Sym.bit .read .back .done
  | .back => moveB .X .O Sym.bit? id .back .done
  | .done => .halt

private theorem emitter_frame (n : Nat) (out : List Bool) (v : Bool)
    (S : ∀ k, List (EmitSS.Γ k)) (hA : S .A = cnt EmitSS.U n)
    (hH : S .H = []) (hT : S .T = []) (hO : S .O = out) :
    ∃ v' U, RunLe EmitSS.prog (7 * n + 3)
      ⟨some .hv, v, S⟩ ⟨some .done, v', U⟩ ∧
      U .O = delimit (Computability.encodeNat n) ++ out ∧
      ∀ k, k ≠ .A → k ≠ .H → k ≠ .T → k ≠ .O → U k = S k := by
  obtain ⟨v₁, S₁, hr₁, ht, hf⟩ := EmitSS.hv_run n v S hA hH
  have ho : S₁ .O = out := (hf _ (by decide) (by decide) (by decide)).trans hO
  let B := update S₁ EmitSS.K.O (false :: out)
  have hr₂ : Run EmitSS.prog 1 ⟨some .tem0, v₁, S₁⟩
      ⟨some .tsk, v₁, B⟩ := by
    simpa [B, ho] using emit_run (M := EmitSS.prog)
      (self := EmitSS.Lab.tem0) rfl v₁ S₁
  obtain ⟨v₂, S₂, hr₃, ho₂, hf₂⟩ := EmitSS.tsk_run
    (Computability.encodeNat n).reverse v₁ B out
    (by simp [B, ht, hT, List.map_reverse]) (by simp [B])
  refine ⟨v₂, S₂, (hr₁.trans ((hr₂.trans hr₃).le le_rfl)).mono ?_, ?_, ?_⟩
  · have hn := EmitSS.encodeNat_length_le n
    simp only [List.length_reverse]
    omega
  · have he := EmitSS.encodeNat_bitsVal_rev (Computability.encodeNat n)
    rw [TM2Recursive.bitsVal_encodeNat] at he
    simpa [← he] using ho₂
  · intro k hka hkh hkt hko
    rw [hf₂ k hkt hko]
    change update S₁ EmitSS.K.O (false :: out) k = S k
    rw [update_of_ne hko, hf k hka hkh hkt]

private def emitterTM : FinTM2 where
  K := EmitSS.K
  k₀ := .A
  k₁ := .O
  Γ := EmitSS.Γ
  Λ := EmitSS.Lab
  main := .hv
  σ := Bool
  initialState := false
  m := EmitSS.prog

private theorem emitter_push_bound :
    TM2Composition.pushBound emitterTM ≤ 100 := by
  decide +kernel

private theorem emitter_scratch_bound {n : Nat} {v w : Bool}
    {S U : ∀ k, List (EmitSS.Γ k)} (hA : S .A = cnt EmitSS.U n)
    (hH : S .H = []) (hT : S .T = [])
    (hr : RunLe EmitSS.prog (7 * n + 3)
      ⟨some .hv, v, S⟩ ⟨some .done, w, U⟩) :
    ∀ k, k ∈ [EmitSS.K.A, .H, .T] → (U k).length ≤ 701 * n + 300 := by
  obtain ⟨t, ht, hr⟩ := hr
  intro k hk
  have hs : (S k).length ≤ n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simp [hA, cnt]
    · simp [hH]
    · simp [hT]
  have hu : (U k).length ≤ (S k).length +
      TM2Composition.pushBound emitterTM * t :=
    TM2Composition.length_iter emitterTM k t _ _ hr
  have hp := Nat.mul_le_mul_right t emitter_push_bound
  omega

private theorem embeds (framed : Bool) :
    Embeds embedding emitLabel EmitSS.prog (prog framed) := by
  intro l
  by_cases h : l = .done
  · right
    subst l
    rfl
  · left
    simp [emitLabel, h, prog]

private theorem lift_emitter (framed : Bool) {t : Nat} {v w : Bool}
    {S U : ∀ k, List (EmitSS.Γ k)}
    (hr : RunLe EmitSS.prog t ⟨some .hv, v, S⟩ ⟨some .done, w, U⟩) :
    RunLe (prog framed) t
      ⟨some (.emit .hv), v, S⟩ ⟨some .clean, w, U⟩ := by
  have ha : Agree embedding S S := by
    intro k
    change S k = (S k).map id
    simp
  obtain ⟨V, hv, he, _⟩ := runLe_embed emitLabel (embeds framed) hr ha
  have hVU : V = U := by
    funext k
    have hk : V k = (U k).map id := he k
    simpa using hk
  subst V
  simpa [emitLabel] using hv

private theorem clean_frame_run (framed : Bool) (n : Nat)
    (out : List Bool) (v : Bool) (S : ∀ k, List (EmitSS.Γ k))
    (hA : S .A = cnt EmitSS.U n) (hH : S .H = []) (hT : S .T = [])
    (hO : S .O = out) :
    ∃ U, RunLe (prog framed) (708 * n + 304)
      ⟨some (.emit .hv), v, S⟩
      ⟨some (if framed then .done else .read), false, U⟩ ∧
      U .O = delimit (Computability.encodeNat n) ++ out ∧
      U .A = [] ∧ U .H = [] ∧ U .T = [] ∧
      ∀ k, k ≠ .A → k ≠ .H → k ≠ .T → k ≠ .O → U k = S k := by
  obtain ⟨w, U, hr, ho, hf⟩ := emitter_frame n out v S hA hH hT hO
  have hs := emitter_scratch_bound hA hH hT hr
  have hc := clean_run (M := prog framed) (ks := [EmitSS.K.A, .H, .T])
    (self := Lab.clean) (next := if framed then Lab.done else Lab.read)
    rfl (by decide) (701 * n + 300) w U hs
  refine ⟨_, ((lift_emitter framed hr).trans hc).mono (by omega),
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa using ho
  · simp
  · simp
  · simp
  · intro k hka hkh hkt hko
    simpa [hka, hkh, hkt] using hf k hka hkh hkt hko

private theorem unframe_run (p out : List Bool) (v : Bool)
    (S : ∀ k, List (EmitSS.Γ k)) (hO : S .O = delimit p ++ out)
    (hX : S .X = []) :
    ∃ w U, Run (prog false) (2 * p.length + 2)
      ⟨some .read, v, S⟩ ⟨some .done, w, U⟩ ∧
      U .O = p ++ out ∧ U .X = [] ∧
      ∀ k, k ≠ .X → k ≠ .O → U k = S k := by
  obtain ⟨S₁, hr₁, ho₁, hx₁, hf₁⟩ := FramedCNF.Block.run_delimit
    (M := prog false) (a := EmitSS.K.O) (b := .X) (d := some)
    (g := Sym.bit) (self := Lab.read) (good := Lab.back) (bad := Lab.done)
    rfl (by decide) id (fun _ => rfl) p out v S (by simpa using hO)
  obtain ⟨w, U, hr₂, hx₂, ho₂, hf₂⟩ := moveB_run
    (M := prog false) (a := EmitSS.K.X) (b := .O) (d := Sym.bit?)
    (g := id) (self := Lab.back) (next := Lab.done) rfl (by decide)
    p.reverse (p.map Sym.bit).reverse [] false S₁
    (by simpa [hX] using hx₁)
    (by simp [IsBitBlock, List.map_reverse, List.map_map,
      Function.comp_def, Sym.bit?]) rfl
  refine ⟨w, U, (hr₁.trans hr₂).of_eq (by simp; omega), ?_, hx₂, ?_⟩
  · simpa [ho₁] using ho₂
  · intro k hkx hko
    rw [hf₂ k hkx hko, hf₁ k hko hkx]

/-- **Converter turns a unary count into a canonical binary frame.**
Emit one canonical Nat frame above any earlier output and restore
all conversion scratch. The old counter is consumed; unrelated stacks,
including `X`, are preserved. Cleanup is part of the charged run. -/
theorem run_framed (n : Nat) (out : List Bool) (v : Bool)
    (S : ∀ k, List (EmitSS.Γ k)) (hA : S .A = cnt EmitSS.U n)
    (hH : S .H = []) (hT : S .T = []) (hO : S .O = out) :
    ∃ U, RunLe (prog true) (708 * n + 304)
      ⟨some (.emit .hv), v, S⟩ ⟨some .done, false, U⟩ ∧
      U .O = delimit (Computability.encodeNat n) ++ out ∧
      U .A = [] ∧ U .H = [] ∧ U .T = [] ∧
      ∀ k, k ≠ .A → k ≠ .H → k ≠ .T → k ≠ .O → U k = S k := by
  exact clean_frame_run true n out v S hA hH hT hO

/-- **Converter turns a unary count into a raw canonical binary payload.**
Convert a unary count to the canonical unframed Nat payload,
preserving an earlier output suffix and clearing every used work stack. -/
theorem run_raw (n : Nat) (out : List Bool) (v : Bool)
    (S : ∀ k, List (EmitSS.Γ k)) (hA : S .A = cnt EmitSS.U n)
    (hH : S .H = []) (hT : S .T = []) (hO : S .O = out)
    (hX : S .X = []) :
    ∃ w U, RunLe (prog false) (710 * n + 306)
      ⟨some (.emit .hv), v, S⟩ ⟨some .done, w, U⟩ ∧
      U .O = Computability.encodeNat n ++ out ∧
      U .A = [] ∧ U .H = [] ∧ U .T = [] ∧ U .X = [] ∧
      ∀ k, k ≠ .A → k ≠ .H → k ≠ .T → k ≠ .O → k ≠ .X →
        U k = S k := by
  obtain ⟨U, hr, ho, ha, hh, ht, hf⟩ :=
    clean_frame_run false n out v S hA hH hT hO
  have hx : U .X = [] :=
    (hf _ (by decide) (by decide) (by decide) (by decide)).trans hX
  obtain ⟨w, V, hv, hvo, hvx, hframe⟩ :=
    unframe_run (Computability.encodeNat n) out false U ho hx
  refine ⟨w, V, (hr.trans (hv.le le_rfl)).mono ?_, hvo,
    ?_, ?_, ?_, hvx, ?_⟩
  · have hn := EmitSS.encodeNat_length_le n
    omega
  · exact (hframe _ (by decide) (by decide)).trans ha
  · exact (hframe _ (by decide) (by decide)).trans hh
  · exact (hframe _ (by decide) (by decide)).trans ht
  · intro k hka hkh hkt hko hkx
    exact (hframe k hkx hko).trans (hf k hka hkh hkt hko)

/-- **Unary-to-binary converter as a host component.**
The adapter is a finite component of the existing Host. Its input
counter has `n` physical symbols; the bound is linear in that length,
not in the bit length of an arbitrary binary-encoded numeric input. -/
abbrev component (framed : Bool) : Host.Comp where
  K := EmitSS.K
  Γ := EmitSS.Γ
  finΓ k := by cases k <;> infer_instance
  L := Lab
  prog := prog framed
  ks := [.X, .O, .A, .H, .N, .M, .C, .S1, .S2, .Y, .Z, .T, .L, .R, .Rt]
  ks_nodup := by decide
  mem_ks k := by cases k <;> simp

end Cslib.Complexity.PolynomialEncoding.UnaryNat
