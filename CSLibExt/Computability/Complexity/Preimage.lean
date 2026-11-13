/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Computability.TuringMachine.Composition
public import CSLibExt.Computability.CookLevin
import CSLibExt.Computability.Complexity.EncodingConverters
import CSLibExt.Computability.Complexity.SatVerifierTM
import MathlibExt.Computability.TuringMachine.ExactStackEmbedding

/-!
# Polynomial preimages of canonical NP languages

The verifier for a preimage computes the reduction on its first input and
preserves the certificate. Every conversion uses the canonical encodings.
Output size is bounded by the machine's pushes, not assumed separately.
-/

@[expose] public section

namespace Cslib.Complexity.Preimage

open Turing Function MetaMathlibExt TM2Program TM2Composition
open ComplexityTheory BitstringEncoding DenseSAT

/-- A polynomial-time machine has polynomially bounded encoded output. -/
theorem output_length_le {α β A B : Type} {ea : α → List A}
    {eb : β → List B} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (midPoly h).eval (ea a).length := by
  obtain ⟨⟨s, hs⟩, ht⟩ := h.outputsFun a
  change (flip bind h.tm.step)^[s]
      (some (initList h.tm ((ea a).map h.inputAlphabet.symm))) =
    some (haltList h.tm ((eb (f a)).map h.outputAlphabet.symm)) at hs
  have hl := length_iter h.tm h.tm.k₁ s _ _ hs
  rw [haltList_stk_self, List.length_map] at hl
  have hi := initList_stk_length_le h.tm
    ((ea a).map h.inputAlphabet.symm) h.tm.k₁
  simp only [List.length_map] at hi
  have hm := Nat.mul_le_mul_left (pushBound h.tm) ht
  simpa only [midPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C] using
      hl.trans ((Nat.add_le_add_right hi _).trans
        (Nat.add_le_add_left hm _))

/-- Canonical polynomial-time maps can also be run on unframed bit lists. -/
theorem raw_computable {f : List Bool → List Bool} (hf : IsPolyTime f) :
    Nonempty (TM2ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) f) := by
  obtain ⟨h⟩ := hf
  obtain ⟨h₁⟩ := tm2ComputableInPolyTime_comp (f := id) (g := f)
    EncodeBits.computable h
  exact tm2ComputableInPolyTime_comp (f := f) (g := id)
    h₁ DecodeBits.computable

namespace MapFirst

private abbrev side : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Verifier.G
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

variable (M : FinTM2)

private abbrev K := CK M side
private abbrev Γ := CΓ M side
private abbrev Lab := CΛ M side ⊕ Bool
private abbrev State := Cσ M side

private noncomputable def identEmb : TM2Embedding.SEmb (Γ M) (Γ M) where
  e := id
  inj := Function.injective_id
  ι _ := Equiv.refl _

private def leftBit : Option Verifier.G → Bool
  | some (.inl _) => true
  | _ => false

private def getBit : Option Verifier.G → Bool
  | some (.inl b) => b
  | _ => false

private noncomputable def st (S : ∀ k, List (M.Γ k)) (i t : List Verifier.G) :
    ∀ k, List (Γ M k) := mkStk M side S (fun _ => i) t

private noncomputable def prog
    (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) :
    Lab M → TM2.Stmt (Γ M) (Lab M) (State M)
  | .inl l => TM2Embedding.mapS (identEmb M) Sum.inl
      (TM2Composition.prog M side (Sum.inl ∘ eo) l)
  | .inr false =>
      .peek (.inr (.inl ())) (fun s o => (s.1, (), o)) <|
      .branch (fun s => leftBit s.2.2)
        (.pop (.inr (.inl ())) (fun s _ => s) <|
          .push (tmp M side) (fun s => .inl (getBit s.2.2)) <|
          .goto fun _ => .inr false)
        (.goto fun _ => .inr true)
  | .inr true =>
      .pop (tmp M side) (fun s o => (s.1, (), o)) <|
      .branch (fun s => s.2.2.isSome)
        (.push (.inl M.k₀) (fun s => ei.symm (getBit s.2.2)) <|
          .goto fun _ => .inr true)
        (.goto fun _ => .inl (.inl M.main))

variable {M}

variable (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)

private theorem read_run (x : List Bool) (w t : List Verifier.G)
    (S : ∀ k, List (M.Γ k)) (v : M.σ) (o : Option Verifier.G) :
    Run (prog M ei eo) (x.length + 1)
      ⟨some (.inr false), (v, (), o),
        st M S (x.map Sum.inl ++ .inr none :: w) t⟩
      ⟨some (.inr true), (v, (), some (.inr none)),
        st M S (.inr none :: w) ((x.map Sum.inl).reverse ++ t)⟩ := by
  induction x generalizing t o with
  | nil =>
    apply Run.single
    simp [prog, TM2.stepAux, st, mkStk, leftBit]
  | cons b x ih =>
    have hr := ih (.inl b :: t) (some (.inl b))
    simp only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append] at hr ⊢
    apply Run.head _ hr
    simp [TM2.step, prog, TM2.stepAux, leftBit, getBit, st, mkStk,
      funext_iff]

private theorem restore_run (x : List Bool) (w : List Verifier.G)
    (S : ∀ k, List (M.Γ k)) (v : M.σ) (o : Option Verifier.G) :
    Run (prog M ei eo) (x.length + 1)
      ⟨some (.inr true), (v, (), o), st M S w (x.map Sum.inl)⟩
      ⟨some (.inl (.inl M.main)), (v, (), none),
        st M (update S M.k₀ (x.reverse.map ei.symm ++ S M.k₀)) w []⟩ := by
  induction x generalizing S o with
  | nil =>
    apply Run.single
    simp [prog, TM2.stepAux, st, mkStk]
  | cons b x ih =>
    have hr := ih (update S M.k₀ (ei.symm b :: S M.k₀))
      (some (.inl b))
    simp only [List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
      update_self, update_idem] at hr ⊢
    apply Run.head _ hr
    simp [TM2.step, prog, TM2.stepAux, getBit, st, mkStk, funext_iff]

private noncomputable def context (c : M.Cfg) (w : List Verifier.G) :
    TM2.Cfg (CΓ M side) (CΛ M side) (Cσ M side) :=
  ⟨some (lab₁ (M₂ := side) c.l), (c.var, (), none), st M c.stk w []⟩

private theorem step_context (w : List Verifier.G) {c d : M.Cfg}
    (h : M.step c = some d) :
    TM2.step (TM2Composition.prog M side (Sum.inl ∘ eo))
      (context c w) = some (context d w) := by
  rcases c with ⟨l | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · change some (TM2.stepAux (M.m l) v S) = some d at h
    have hd := Option.some.inj h
    subst d
    simp only [context, lab₁, TM2.step, TM2Composition.prog, st]
    rw [stepAux_lift₁]
    rfl

private theorem run_context {s : ℕ} {x : List (M.Γ M.k₀)}
    {y : List (M.Γ M.k₁)} (w : List Verifier.G)
    (hr : Run M.m s (initList M x) (haltList M y)) :
    Run (TM2Composition.prog M side (Sum.inl ∘ eo))
      (s + (2 * y.length + 1) + (2 * y.length + 1) + 1)
      (context (initList M x) w)
      ⟨none, (M.initialState, (), none),
        st M (fun _ => []) (y.map (Sum.inl ∘ eo) ++ w) []⟩ := by
  have r₁ := iter_sim (fun c => context c w)
    (fun _ _ h => step_context eo w h) s _ _ hr
  have r₂ := copy₁ (M₁ := M) (M₂ := side) (Sum.inl ∘ eo) y
    M.initialState () none (haltList M y).stk (fun _ => w) []
    (haltList_stk_self M y)
  rw [update_haltList_stk, List.append_nil] at r₂
  have r₃ := copy₂ (M₁ := M) (M₂ := side) (Sum.inl ∘ eo)
    (y.map (Sum.inl ∘ eo)).reverse M.initialState () none
    (fun _ => []) (fun _ => w)
  simp only [List.reverse_reverse, List.length_reverse,
    List.length_map] at r₃
  have r₄ : Run (TM2Composition.prog M side (Sum.inl ∘ eo)) 1
      ⟨some (.inr (.inl ())), (M.initialState, (), none),
        st M (fun _ => []) (y.map (Sum.inl ∘ eo) ++ w) []⟩
      ⟨none, (M.initialState, (), none),
        st M (fun _ => []) (y.map (Sum.inl ∘ eo) ++ w) []⟩ :=
    Run.single rfl
  exact Run.trans (Run.trans (Run.trans r₁ r₂) r₃) r₄

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
  FinTM2.Γk₀Fin

private noncomputable def tm : FinTM2 where
  K := K M
  k₀ := .inr (.inl ())
  k₁ := .inr (.inl ())
  Γ := Γ M
  Λ := Lab M
  main := .inr false
  σ := State M
  initialState := (M.initialState, (), none)
  m := prog M ei eo

private theorem init_tm (l : List Verifier.G) :
    initList (tm ei eo) l =
      ⟨some (.inr false), (M.initialState, (), none),
        st M (fun _ => []) l []⟩ := by
  simp only [initList, tm]
  congr 1
  funext k
  rcases k with k | ⟨⟩ | ⟨⟩ <;> simp [st, mkStk]
  rfl

private theorem halt_tm (l : List Verifier.G) :
    haltList (tm ei eo) l =
      ⟨none, (M.initialState, (), none), st M (fun _ => []) l []⟩ := by
  simp only [haltList, tm]
  congr 1
  funext k
  rcases k with k | ⟨⟩ | ⟨⟩ <;> simp [st, mkStk]
  rfl

private theorem lift_run {s : ℕ}
    {c d : TM2.Cfg (CΓ M side) (CΛ M side) (Cσ M side)}
    (hr : Run (TM2Composition.prog M side (Sum.inl ∘ eo)) s c d) :
    Run (prog M ei eo) s
      ⟨c.l.map Sum.inl, c.var, c.stk⟩
      ⟨d.l.map Sum.inl, d.var, d.stk⟩ := by
  apply TM2Embedding.run_embed_exact_of_agree_frame
    (identEmb M) Sum.inl (fun _ => rfl) hr
  · intro k
    exact (List.map_id _).symm
  · intro k
    exact (List.map_id _).symm
  · intro k hk
    exact (hk k rfl).elim

private theorem phase0 (x w : List Bool) :
    Run (prog M ei eo) (2 * x.length + 2)
      (initList (tm ei eo) (Verifier.pairEncode (x, w)))
      ⟨some (.inl (.inl M.main)), (M.initialState, (), none),
        st M (initList M (x.map ei.symm)).stk
          (.inr none :: w.map (fun b => .inr (some b))) []⟩ := by
  have r₁ := read_run ei eo x (w.map fun b => .inr (some b)) []
    (fun _ => []) M.initialState none
  have r₂ := restore_run ei eo x.reverse
    (.inr none :: w.map (fun b => .inr (some b)))
    (fun _ => []) M.initialState (some (.inr none))
  simp only [List.reverse_reverse, List.length_reverse,
    List.map_reverse, List.append_nil] at r₁ r₂
  rw [← update_nil_eq_initList]
  rw [init_tm]
  exact (r₁.trans r₂).of_eq (by omega)

private theorem whole_run (x y w : List Bool) {s : ℕ}
    (hr : Run M.m s (initList M (x.map ei.symm))
      (haltList M (y.map eo.symm))) :
    Run (prog M ei eo) (2 * x.length + s + 4 * y.length + 5)
      (initList (tm ei eo) (Verifier.pairEncode (x, w)))
      (haltList (tm ei eo) (Verifier.pairEncode (y, w))) := by
  have r := lift_run ei eo
    (run_context eo (.inr none :: w.map (fun b => .inr (some b))) hr)
  simp only [List.length_map, List.map_map, Function.comp_def,
    Equiv.apply_symm_apply] at r
  have ht := (phase0 ei eo x w).trans r
  rw [halt_tm]
  exact ht.of_eq (by omega)

/-- Run a bit-list machine on the first component, leaving the second
component unchanged on a disjoint stack. -/
private noncomputable def computable {f : List Bool → List Bool}
    (h : TM2ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) f) :
    TM2ComputableInPolyTime Verifier.pairEncode Verifier.pairEncode
      (fun p => (f p.1, p.2)) where
  tm := tm h.inputAlphabet h.outputAlphabet
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + h.time +
    Polynomial.C 4 * midPoly h + Polynomial.C 5
  outputsFun p := by
    obtain ⟨x, w⟩ := p
    obtain ⟨⟨s, hs⟩, ht⟩ := h.outputsFun x
    refine ⟨⟨2 * x.length + s + 4 * (f x).length + 5, ?_⟩, ?_⟩
    · change Run (prog h.tm h.inputAlphabet h.outputAlphabet) _
        (initList (tm h.inputAlphabet h.outputAlphabet)
          ((Verifier.pairEncode (x, w)).map id))
        (haltList (tm h.inputAlphabet h.outputAlphabet)
          ((Verifier.pairEncode (f x, w)).map id))
      erw [List.map_id, List.map_id]
      exact whole_run h.inputAlphabet h.outputAlphabet x (f x) w hs
    · change s ≤ h.time.eval x.length at ht
      have hx : x.length ≤ (Verifier.pairEncode (x, w)).length := by
        simp [Verifier.pairEncode]
      have htime := eval_mono h.time hx
      have hout := (output_length_le h x).trans (eval_mono (midPoly h) hx)
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega

end MapFirst

end Cslib.Complexity.Preimage

namespace MetaMathlibExt.ComplexityTheory

open Cslib.Complexity Cslib.Complexity.Preimage

/-- Mapping the first component of an encoded pair is polynomial-time;
the second component is preserved, not recomputed or guessed. -/
theorem IsPolyTime.map_fst {f : List Bool → List Bool}
    (hf : IsPolyTime f) :
    IsPolyTime (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  obtain ⟨h⟩ := raw_computable hf
  obtain ⟨h₁⟩ := tm2ComputableInPolyTime_comp
    DenseSAT.Converter.computable (MapFirst.computable h)
  exact tm2ComputableInPolyTime_comp h₁ DenseSAT.ToCanonical.computable

/-- Encoded output length is polynomial in the unframed input length. -/
theorem IsPolyTime.length_bound {f : List Bool → List Bool}
    (hf : IsPolyTime f) :
    ∃ q : Polynomial ℕ, ∀ x, (f x).length ≤ q.eval x.length := by
  obtain ⟨h⟩ := raw_computable hf
  exact ⟨TM2Composition.midPoly h, output_length_le h⟩

open Cslib.CookLevin Cslib.Logic.PL

private theorem satVerifier_sound {x w : List Bool}
    (h : (satVerifier (x, w)).ret = true) : satDec x = true := by
  cases hd : decodeCNF x with
  | none => simp [satVerifier_none hd] at h
  | some φ =>
    rw [satVerifier_some hd, checkCNF_ret] at h
    have hs : CNFSat φ := cnfSat_iff_exists_satisfies.2 ⟨_, h⟩
    rw [(decodeCNF_eq_some_iff x φ).1 hd]
    exact (DenseSAT.ToBinary.satDec_encodeCNF φ).2 hs

/-- Pulling SAT back along a polynomial map preserves NP membership.
SAT verifier soundness holds even for certificates above its length bound. -/
theorem satDec_comp_mem_NP {f : List Bool → List Bool}
    (hf : IsPolyTime f) : satDec ∘ f ∈ NP := by
  obtain ⟨q, hq⟩ := hf.length_bound
  refine ⟨q, fun p => (satVerifier (f p.1, p.2)).ret,
    hf.map_fst.comp SatVerifier.Machine.isPolyTime_satVerifier, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨w, hw, ha⟩ := (satVerifier_verifies (f x)).1 hx
    rw [Polynomial.eval_X] at hw
    exact ⟨w, hw.trans (hq x), ha⟩
  · rintro ⟨w, -, ha⟩
    exact satVerifier_sound ha

/-- Canonical NP is closed under polynomial-time preimages.
Cook–Levin supplies a verifier sound for arbitrarily long certificates,
so enlarging the transformed witness bound introduces no false positives. -/
theorem comp_mem_NP {L : DecisionProblem} {f : List Bool → List Bool}
    (hL : L ∈ NP) (hf : IsPolyTime f) : L ∘ f ∈ NP := by
  obtain ⟨g, hg, he⟩ :=
    SatVerifier.Machine.cook_levin_SAT_np_complete.2 L hL
  have hEq : L ∘ f = satDec ∘ (g ∘ f) := funext fun x => he (f x)
  rw [hEq]
  exact satDec_comp_mem_NP (hf.comp hg)

/-- NP membership transfers backwards along a polynomial many-one reduction. -/
theorem mem_NP_of_polyManyOneRed {L K : DecisionProblem}
    (hK : K ∈ NP) (hr : PolyManyOneRed L K) : L ∈ NP := by
  obtain ⟨f, hf, he⟩ := hr
  have hEq : L = K ∘ f := funext he
  rw [hEq]
  exact comp_mem_NP hK hf

/-- Canonical coNP is closed under polynomial-time preimages. -/
theorem comp_mem_coNP {L : DecisionProblem} {f : List Bool → List Bool}
    (hL : L ∈ coNP) (hf : IsPolyTime f) : L ∘ f ∈ coNP :=
  comp_mem_NP (L := Lᶜ) (f := f) hL hf

end MetaMathlibExt.ComplexityTheory

namespace Cslib.CookLevin

/-- The same reduction function reduces the complements. -/
theorem PolyManyOneRed.compl
    {L K : MetaMathlibExt.ComplexityTheory.DecisionProblem}
    (h : PolyManyOneRed L K) : PolyManyOneRed Lᶜ Kᶜ := by
  obtain ⟨f, hf, he⟩ := h
  exact ⟨f, hf, fun x => congrArg Bool.not (he x)⟩

end Cslib.CookLevin
