/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.FramedCNF.Block
import CSLibExt.Computability.Complexity.Host
import CSLibExt.Computability.Complexity.PairEncodingConverter
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import Mathlib.Algebra.BigOperators.Ring.Finset
import MathlibExt.Computability.TuringMachine.Cleanup
import MathlibExt.Computability.TuringMachine.Composition

/-!
# Adleman's theorem: BPP is contained in P/poly

A finite counting argument supplies a list of random strings whose majority vote is correct
on every input of a fixed length. A polynomial-time verifier reads the framed advice and
runs the original verifier on each of its strings.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.Adleman

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

section Counting

open Finset

/-- Count the successful trials in a tuple. -/
private noncomputable def successes {ι α : Type} [Fintype ι] (good : α → Bool)
    (r : ι → α) : ℕ := ((univ : Finset ι).filter fun i => good (r i)).card

private theorem prod_trialWeight {ι : Type} [Fintype ι] (b : ι → Bool) :
    (∏ i, if b i then 1 else (2 : ℕ)) = 2 ^ ((univ : Finset ι).filter fun i => ¬ b i).card := by
  rw [← Finset.prod_const]
  rw [Finset.prod_filter]
  exact Finset.prod_congr rfl fun i _ => by cases b i <;> rfl

/-- A weighted count bounds the number of tuples with at least half failed trials. -/
private theorem badTuples_lt {α : Type} [Fintype α] [Nonempty α]
    (good : α → Bool)
    (hgood : 3 * ((univ : Finset α).filter fun a => ¬ good a).card ≤ Fintype.card α)
    (n : ℕ) :
    (2 ^ n) * ((univ : Finset (Fin (2 * (6 * (n + 1))) → α)).filter
      fun r => successes good r ≤ 6 * (n + 1)).card <
      Fintype.card (Fin (2 * (6 * (n + 1))) → α) := by
  classical
  let k := 6 * (n + 1)
  let d := Fintype.card α
  let wt (a : α) : ℕ := if good a then 1 else 2
  let bad : Finset (Fin (2 * k) → α) := univ.filter fun r => successes good r ≤ k
  let errors : Finset α := univ.filter fun a => ¬ good a
  have hsum : ∑ a, wt a = d + errors.card := by
    have heq : ∀ a, wt a = 1 + if ¬ good a then 1 else 0 := by
      intro a
      cases h : good a <;> simp [wt, h]
    simp only [heq, sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, mul_one]
    rw [← sum_filter]
    simp [d, errors]
  have hwt : ∀ r ∈ bad, 2 ^ k ≤ ∏ i, wt (r i) := by
    intro r hr
    have hr' : successes good r ≤ k := (mem_filter.mp hr).2
    have hc : successes good r + ((univ : Finset (Fin (2 * k))).filter
        fun i => ¬ good (r i)).card = 2 * k := by
      unfold successes
      simpa using card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * k))))
        (fun i => (good (r i) : Prop))
    rw [prod_trialWeight (fun i => good (r i))]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hb : bad.card * 2 ^ k ≤ (d + errors.card) ^ (2 * k) := calc
    _ = ∑ _r ∈ bad, 2 ^ k := by simp
    _ ≤ ∑ r ∈ bad, ∏ i, wt (r i) := sum_le_sum hwt
    _ ≤ ∑ r : Fin (2 * k) → α, ∏ i, wt (r i) :=
      sum_le_sum_of_subset (subset_univ _)
    _ = _ := by simpa [hsum] using (Fintype.prod_sum (fun _ : Fin (2 * k) => wt)).symm
  have hscale : 9 * (d + errors.card)^2 ≤ 16 * d^2 := by
    have he : 3 * errors.card ≤ d := hgood
    have hs : 3 * (d + errors.card) ≤ 4 * d := by omega
    have := Nat.pow_le_pow_left hs 2
    nlinarith only [this]
  have hpow : (9 : ℕ)^k * (d + errors.card)^(2 * k) ≤
      16^k * (d^2)^k := by
    simpa only [mul_pow, pow_mul] using Nat.pow_le_pow_left hscale k
  have hnum : (2 : ℕ)^n * 16^k < 9^k * 2^k := by
    rw [← mul_pow, show k = 6 * (n + 1) from rfl, pow_mul 16, pow_mul (9 * 2)]
    calc
      _ < 2^(n + 1) * (16^6)^(n + 1) := by
        exact Nat.mul_lt_mul_of_pos_right
          (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (Nat.lt_succ_self n)) (by positivity)
      _ = (2 * 16^6)^(n + 1) := (mul_pow ..).symm
      _ ≤ ((9 * 2)^6)^(n + 1) := Nat.pow_le_pow_left (by decide) _
  have hd : 0 < d := Fintype.card_pos
  have hlt : (2 ^ n) * bad.card < d ^ (2 * k) := by
    have h₁ := Nat.mul_le_mul_left (2 ^ n * 9 ^ k) hb
    have h₂ := Nat.mul_le_mul_left (2 ^ n) hpow
    have h₃ := Nat.mul_lt_mul_of_pos_right hnum (pow_pos (pow_pos hd 2) k)
    rw [← pow_mul] at h₃
    apply (Nat.mul_lt_mul_right (a := 9 ^ k * 2 ^ k) (by positivity)).mp
    calc
      _ = (2 ^ n * 9 ^ k) * (bad.card * 2 ^ k) := by ac_rfl
      _ ≤ (2 ^ n * 9 ^ k) * (d + errors.card) ^ (2 * k) := h₁
      _ = 2 ^ n * (9 ^ k * (d + errors.card) ^ (2 * k)) := by ac_rfl
      _ ≤ 2 ^ n * (16 ^ k * (d ^ 2) ^ k) := h₂
      _ = (2 ^ n * 16 ^ k) * d ^ (2 * k) := by rw [pow_mul d, mul_assoc]
      _ < (9 ^ k * 2 ^ k) * d ^ (2 * k) := h₃
      _ = _ := by ac_rfl
  simpa only [Fintype.card_pi_const, k, d, bad] using hlt

/-- Across all bit strings of a given length, one tuple has a strict majority of good trials
for every input. -/
private theorem exists_good_tuple {α : Type} [Fintype α] [Nonempty α]
    (n : ℕ) (good : (Fin n → Bool) → α → Bool)
    (hgood : ∀ x, 3 * ((univ : Finset α).filter fun a => ¬ good x a).card ≤ Fintype.card α) :
    ∃ r : Fin (2 * (6 * (n + 1))) → α, ∀ x, 6 * (n + 1) < successes (good x) r := by
  classical
  let bad (x : Fin n → Bool) : Finset (Fin (2 * (6 * (n + 1))) → α) :=
    univ.filter fun r => successes (good x) r ≤ 6 * (n + 1)
  have hbad (x) : 2 ^ n * (bad x).card < Fintype.card (Fin (2 * (6 * (n + 1))) → α) :=
    badTuples_lt (good x) (hgood x) n
  obtain ⟨x₀, -, hx₀⟩ := exists_max_image (univ : Finset (Fin n → Bool))
    (fun x => (bad x).card) univ_nonempty
  have hunion : #(univ.biUnion bad) < Fintype.card (Fin (2 * (6 * (n + 1))) → α) := calc
    _ ≤ ∑ x, (bad x).card := card_biUnion_le
    _ ≤ ∑ _x : Fin n → Bool, (bad x₀).card := sum_le_sum hx₀
    _ = 2 ^ n * (bad x₀).card := by simp
    _ < _ := hbad x₀
  obtain ⟨r, -, hr⟩ := exists_mem_notMem_of_card_lt_card (by simpa using hunion :
    #(univ.biUnion bad) < #(univ : Finset (Fin (2 * (6 * (n + 1))) → α)))
  refine ⟨r, fun x => lt_of_not_ge fun hx => hr ?_⟩
  exact mem_biUnion.mpr ⟨x, mem_univ x, mem_filter.mpr ⟨mem_univ r, hx⟩⟩

end Counting

section Machine

open Turing Function Polynomial MetaMathlibExt.BitstringEncoding
open MetaMathlibExt.TM2Program MetaMathlibExt.TM2Composition
open Cslib.Complexity.FramedCNF Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.DenseSAT.Converter (encSnd bitEncode_list)

private inductive Stack
  | input | prefix | spare | coins | yes | no | out
  deriving DecidableEq

private instance stackFintype : Fintype Stack :=
  Fintype.ofList [.input, .prefix, .spare, .coins, .yes, .no, .out] (by intro k; cases k <;> simp)

private inductive Label
  | start | decode | restore | next | read | coins | prefix | spare | call | compare
  | clean (ans : Bool) | emit (ans : Bool)
  deriving DecidableEq

private instance labelFintype : Fintype Label := Fintype.ofList
  [.start, .decode, .restore, .next, .read, .coins, .prefix, .spare, .call, .compare,
    .clean false, .clean true, .emit false, .emit true] (by
    intro l
    cases l with
    | clean b | emit b => cases b <;> simp
    | _ => simp)

private def workStacks : List Stack := [.input, .prefix, .spare, .coins, .yes, .no, .out]

/-- The controller splits the canonical input and runs the advice decoder. The three glue
labels take over when a complete coin string is available. -/
private def controller : Label → TM2.Stmt (fun _ : Stack => Bool) Label Bool
  | .start => Block.read .input .prefix some id .start .decode (.clean false)
  | .decode => .pop .input (fun _ o => o.isSome) <| .branch id
      (.pop .input (fun _ o => o.getD false) <| .pop .input (fun s _ => s) <|
        .push .spare id <| .goto fun _ => .decode)
      (.goto fun _ => .restore)
  | .restore => moveB .spare .input some id .restore .next
  | .next => .peek .input (fun _ o => o.isSome) <| .goto fun s => if s then .read else .compare
  | .read => Block.read .input .coins some id .read .coins (.clean false)
  | .coins | .prefix | .call => .halt
  | .spare => moveB .spare .prefix some id .spare .call
  | .compare => .pop .no (fun _ o => o.isSome) <| .branch id
      (.pop .yes (fun _ o => o.isSome) <| .goto fun s => if s then .compare else .clean false)
      (.peek .yes (fun _ o => o.isSome) <| .goto fun s => .clean s)
  | .clean b => cleanS workStacks (.clean b) (.emit b)
  | .emit b => .push .out (fun _ => b) <| .load (fun _ => false) .halt

private abbrev ctrl : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .out
  Γ := fun _ => Bool
  Λ := Label
  main := .start
  σ := Bool
  initialState := false
  m := controller

private def layout (input pref spare coins : List Bool) (yes no : ℕ) : Stack → List Bool
  | .input => input
  | .prefix => pref
  | .spare => spare
  | .coins => coins
  | .yes => cnt true yes
  | .no => cnt true no
  | .out => []

private theorem decode_run (w pref spare : List Bool) (v : Bool) :
    Run controller (w.length + 1) ⟨some .decode, v, layout (encSnd w) pref spare [] 0 0⟩
      ⟨some .restore, false, layout [] pref (w.reverse ++ spare) [] 0 0⟩ := by
  induction w generalizing spare v with
  | nil =>
    apply Run.single
    simp [controller, layout, encSnd]
  | cons b w ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    refine Run.head ?_ (ih (b :: spare) b)
    simp only [TM2.step, Option.some.injEq]
    apply congrArg (TM2.Cfg.mk (some Label.decode) b)
    funext k
    cases k <;> rfl

private theorem start_run (x w : List Bool) :
    ∃ v, RunLe controller ((encSnd x).length + 2 * w.length + 3)
      ⟨some .start, false, layout (delimit (encSnd x) ++ encSnd w) [] [] [] 0 0⟩
      ⟨some .next, v, layout w (encSnd x).reverse [] [] 0 0⟩ := by
  obtain ⟨S, hr, hi, hp, hs⟩ := Block.run_delimit (M := controller)
    (a := Stack.input) (b := Stack.prefix) (d := some) (g := id)
    (self := Label.start) (good := Label.decode) (bad := Label.clean false)
    rfl (by decide) id (fun _ => rfl) (encSnd x) (encSnd w) false
    (layout (delimit (encSnd x) ++ encSnd w) [] [] [] 0 0) (by simp [layout])
  have hS : S = layout (encSnd w) (encSnd x).reverse [] [] 0 0 := by
    funext k
    cases k <;> first | exact hi | simpa [layout] using hp | exact hs _ (by decide) (by decide)
  rw [hS] at hr
  have hd := decode_run w (encSnd x).reverse [] false
  rw [List.append_nil] at hd
  obtain ⟨v, T, hm, hs', hi', hrest⟩ := moveB_run (M := controller)
    (a := Stack.spare) (b := Stack.input) (d := some) (g := id)
    (self := Label.restore) (next := Label.next) rfl (by decide)
    w.reverse w.reverse [] false (layout [] (encSnd x).reverse w.reverse [] 0 0)
    (by simp [layout]) rfl rfl
  have hT : T = layout w (encSnd x).reverse [] [] 0 0 := by
    funext k
    cases k <;> first | simpa [layout] using hi' | exact hs' | exact hrest _ (by decide) (by decide)
  rw [hT] at hm
  exact ⟨v, ((hr.trans hd).trans hm).le (by simp; omega)⟩

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

private noncomputable abbrev sideStack {M : FinTM2} (k : Stack) : CK M ctrl := .inr (.inl k)

private noncomputable abbrev sideLabel {M : FinTM2} (l : Label) : CΛ M ctrl := .inr (.inl l)

private noncomputable def keepBit {M : FinTM2} (s : Cσ M ctrl) (o : Option Bool) : Cσ M ctrl :=
  (s.1, false, o)

private noncomputable def clearBit {M : FinTM2} (s : Cσ M ctrl) : Cσ M ctrl := (s.1, false, none)

private noncomputable def prepareCoins (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) :
    TM2.Stmt (CΓ M ctrl) (CΛ M ctrl) (Cσ M ctrl) :=
  .pop (sideStack .coins) keepBit <| .branch (·.2.2.isSome)
    (.push (.inl M.k₀) (fun _ => ei.symm false) <|
      .push (.inl M.k₀) (fun s => ei.symm (s.2.2.getD false)) <|
      .push (.inl M.k₀) (fun _ => ei.symm true) <|
      .load clearBit (.goto fun _ => sideLabel .coins))
    (.push (.inl M.k₀) (fun _ => ei.symm false) <| .goto fun _ => sideLabel .prefix)

private noncomputable def preparePrefix (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) :
    TM2.Stmt (CΓ M ctrl) (CΛ M ctrl) (Cσ M ctrl) :=
  .pop (sideStack .prefix) keepBit <| .branch (·.2.2.isSome)
    (.push (sideStack .spare) (fun s => s.2.2.getD false) <|
      .push (.inl M.k₀) (fun s => ei.symm (s.2.2.getD false)) <|
      .push (.inl M.k₀) (fun _ => ei.symm true) <|
      .load clearBit (.goto fun _ => sideLabel .prefix))
    (.goto fun _ => sideLabel .spare)

private noncomputable def recordVote (M : FinTM2) (eo : M.Γ M.k₁ ≃ Bool) :
    TM2.Stmt (CΓ M ctrl) (CΛ M ctrl) (Cσ M ctrl) :=
  .pop (.inl M.k₁) (fun s o => (s.1, (o.map eo).getD false, none)) <|
    .branch (·.2.1)
      (.push (sideStack .yes) (fun _ => true) (.goto fun _ => sideLabel .next))
      (.push (sideStack .no) (fun _ => true) (.goto fun _ => sideLabel .next))

/-- The verifier runs on its own stacks. The controller preserves the input prefix, prepares
one canonical verifier input per frame, and records each returned bit. -/
private noncomputable def program (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) :
    CΛ M ctrl → TM2.Stmt (CΓ M ctrl) (CΛ M ctrl) (Cσ M ctrl)
  | .inl l => lift₁ M ctrl (M.m l)
  | .inr (.inl .coins) => prepareCoins M ei
  | .inr (.inl .prefix) => preparePrefix M ei
  | .inr (.inl .call) => .goto fun _ => .inl M.main
  | .inr (.inl l) => lift₂ M ctrl (controller l)
  | .inr (.inr (.inl none)) => recordVote M eo
  | .inr (.inr _) => .halt

private theorem program_coins (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) :
    program M ei eo (sideLabel .coins) = prepareCoins M ei := rfl

private theorem program_prefix (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) :
    program M ei eo (sideLabel .prefix) = preparePrefix M ei := rfl

private theorem program_return (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) :
    program M ei eo (pop1 M ctrl) = recordVote M eo := rfl

private noncomputable abbrev machine (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) :
    FinTM2 where
  K := CK M ctrl
  k₀ := sideStack .input
  k₁ := sideStack .out
  Γ := CΓ M ctrl
  Λ := CΛ M ctrl
  main := sideLabel .start
  σ := Cσ M ctrl
  initialState := (M.initialState, false, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program M ei eo

private noncomputable def withController (M : FinTM2) (V : ∀ k, List (M.Γ k)) (c : ctrl.Cfg) :
    TM2.Cfg (CΓ M ctrl) (CΛ M ctrl) (Cσ M ctrl) :=
  ⟨c.l.map sideLabel, (M.initialState, c.var, none), mkStk M ctrl V c.stk []⟩

private noncomputable def withVerifier (M : FinTM2) (S : Stack → List Bool) (v : Bool) (c : M.Cfg) :
    TM2.Cfg (CΓ M ctrl) (CΛ M ctrl) (Cσ M ctrl) :=
  ⟨some (lab₁ c.l), (c.var, v, none), mkStk M ctrl c.stk S []⟩

private theorem verifier_run {M : FinTM2} {ei : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}
    (S : Stack → List Bool) (v : Bool) {n : ℕ} {c d : M.Cfg} (h : Run M.m n c d) :
    Run (program M ei eo) n (withVerifier M S v c) (withVerifier M S v d) := by
  refine iter_sim (withVerifier M S v) (fun c d hs => ?_) n c d h
  rcases c with ⟨_ | l, u, T⟩
  · simp [TM2.step] at hs
  · change some (TM2.stepAux (M.m l) u T) = some d at hs
    rw [← Option.some.inj hs]
    exact congrArg some (stepAux_lift₁ (M₁ := M) (M₂ := ctrl) (M.m l) u T v none S [])

private theorem active_of_run {n : ℕ} {c d : ctrl.Cfg} (h : Run controller n c d)
    (hd : d.l.isSome = true) : c.l.isSome = true := by
  cases n with
  | zero => rwa [Option.some.inj h]
  | succ n =>
    rcases c with ⟨_ | l, v, S⟩
    · unfold Run at h
      rw [iterate_succ_apply] at h
      change (flip bind (TM2.step controller))^[n] none = some d at h
      rw [iter_none] at h
      cases h
    · rfl

private theorem controller_run {M : FinTM2} {ei : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}
    (V : ∀ k, List (M.Γ k)) {n : ℕ} {c d : ctrl.Cfg} (h : Run controller n c d)
    (hd : d.l.isSome = true) :
    Run (program M ei eo) n (withController M V c) (withController M V d) := by
  induction n generalizing c with
  | zero =>
    have hc : c = d := Option.some.inj h
    subst c
    exact Run.zero _
  | succ n ih =>
    have hc := active_of_run h hd
    rcases c with ⟨_ | l, v, S⟩
    · cases hc
    · have hs : Run controller n (TM2.stepAux (controller l) v S) d := by
        unfold Run at h
        rw [iterate_succ_apply] at h
        exact h
      refine Run.head ?_ (ih hs)
      have hactive := active_of_run hs hd
      have hstep (l : Label)
          (he : program M ei eo (sideLabel l) = lift₂ M ctrl (controller l)) :
          TM2.step (program M ei eo) (withController M V ⟨some l, v, S⟩) =
            some (withController M V (TM2.stepAux (controller l) v S)) := by
        change some (TM2.stepAux (program M ei eo (sideLabel l)) _ _) = _
        rw [he]
        exact congrArg some
          (stepAux_lift₂ (M₁ := M) (M₂ := ctrl) (controller l) v S M.initialState none V [])
      cases l <;> first
        | exact hstep _ rfl
        | simp only [controller, TM2.stepAux, Option.isSome_none,
            Bool.false_eq_true] at hactive

private theorem controller_runLe {M : FinTM2} {ei : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}
    (V : ∀ k, List (M.Γ k)) {n : ℕ} {c d : ctrl.Cfg} (h : RunLe controller n c d)
    (hd : d.l.isSome = true) :
    RunLe (program M ei eo) n (withController M V c) (withController M V d) := by
  obtain ⟨m, hm, hr⟩ := h
  exact (controller_run V hr hd).le hm

private abbrev inputStack (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (bits : List Bool) :=
  update (fun _ => []) M.k₀ (bits.map ei.symm)

private noncomputable abbrev atLabel (M : FinTM2) (l : Label) (V : ∀ k, List (M.Γ k))
    (S : Stack → List Bool) (v : Bool := false) :=
  withController M V ⟨some l, v, S⟩

private theorem coins_run (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
    (r u w pref : List Bool) (a b : ℕ) (v : Bool) :
    Run (program M ei eo) (r.length + 1)
      (atLabel M .coins (inputStack M ei u) (layout w pref [] r a b) v)
      (atLabel M .prefix (inputStack M ei (false :: encSnd r.reverse ++ u))
        (layout w pref [] [] a b)) := by
  have hl (old new : List Bool) :
      update (layout w pref [] old a b) .coins new = layout w pref [] new a b := by
    funext k
    cases k <;> rfl
  induction r generalizing u v with
  | nil =>
    apply Run.single
    simp [TM2.stepAux, program_coins, prepareCoins, keepBit, atLabel, withController, encSnd,
      layout, update_mkStk_inl (M₁ := M) (M₂ := ctrl), update_mkStk_inr (M₁ := M) (M₂ := ctrl),
      update_idem, mkStk, inputStack, hl]
  | cons bit r ih =>
    have h := ih (true :: bit :: false :: u) false
    simp only [List.reverse_cons, encSnd, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append] at h ⊢
    refine Run.head ?_ h
    simp [TM2.step, program_coins, prepareCoins, atLabel, withController, keepBit, clearBit,
      layout, update_mkStk_inr (M₁ := M) (M₂ := ctrl), update_mkStk_inl (M₁ := M) (M₂ := ctrl),
      update_idem, mkStk, inputStack, hl]

private theorem prefix_run (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
    (pref u w spare : List Bool) (a b : ℕ) :
    Run (program M ei eo) (pref.length + 1)
      (atLabel M .prefix (inputStack M ei u) (layout w pref spare [] a b))
      (atLabel M .spare (inputStack M ei (pref.reverse.flatMap (fun bit => [true, bit]) ++ u))
        (layout w [] (pref.reverse ++ spare) [] a b)) := by
  have hp (old new spare : List Bool) :
      update (layout w old spare [] a b) .prefix new = layout w new spare [] a b := by
    funext k
    cases k <;> rfl
  have hs (pref old new : List Bool) :
      update (layout w pref old [] a b) .spare new = layout w pref new [] a b := by
    funext k
    cases k <;> rfl
  induction pref generalizing u spare with
  | nil =>
    apply Run.single
    simp [TM2.stepAux, program_prefix, preparePrefix, keepBit, atLabel, withController,
      layout, update_mkStk_inr (M₁ := M) (M₂ := ctrl), mkStk, hp]
  | cons bit pref ih =>
    have h := ih (true :: bit :: u) (bit :: spare)
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append] at h ⊢
    refine Run.head ?_ h
    simp [TM2.step, program_prefix, preparePrefix, atLabel, withController, keepBit, clearBit,
      layout, update_mkStk_inr (M₁ := M) (M₂ := ctrl), update_mkStk_inl (M₁ := M) (M₂ := ctrl),
      update_idem, mkStk, inputStack, hp, hs]

private theorem encodePair (x w : List Bool) :
    bitEncode (x, w) = delimit (encSnd x) ++ encSnd w := by
  change delimit (bitEncode x) ++ bitEncode w = _
  rw [bitEncode_list, bitEncode_list]

private theorem encodePair_length (x w : List Bool) :
    (bitEncode (x, w)).length = 2 * (encSnd x).length + 1 + 3 * w.length := by
  have h (w : List Bool) : (encSnd w).length = 3 * w.length := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      change ([true, b, false] ++ encSnd w).length = 3 * (w.length + 1)
      simp only [List.length_append, List.length_cons, List.length_nil, ih]
      omega
  simp [encodePair, h w]

private theorem call_run {R : List Bool × List Bool → Bool}
    (h : TM2ComputableInPolyTime bitEncode bitEncode R) (x r w : List Bool) (a b : ℕ)
    (v : Bool) :
    RunLe (program h.tm h.inputAlphabet h.outputAlphabet)
      (r.length + 2 * (encSnd x).length + (h.time.eval (bitEncode (x, r)).length) + 5)
      (atLabel h.tm .coins (fun _ => []) (layout w (encSnd x).reverse [] r.reverse a b) v)
      (atLabel h.tm .next (fun _ => [])
        (layout w (encSnd x).reverse [] [] (a + (R (x, r)).toNat) (b + (!R (x, r)).toNat))
        (R (x, r))) := by
  let M := h.tm
  let ei := h.inputAlphabet
  let eo := h.outputAlphabet
  let q := bitEncode (x, r)
  let S := layout w (encSnd x).reverse [] [] a b
  have hz : inputStack M ei [] = (fun _ => []) := update_eq_self _ _
  have hr := coins_run M ei eo r.reverse [] w (encSnd x).reverse a b v
  rw [hz, List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have hp := prefix_run M ei eo (encSnd x).reverse (false :: encSnd r) w [] a b
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at hp
  have hq : (encSnd x).flatMap (fun bit => [true, bit]) ++ false :: encSnd r = q := by
    dsimp [q]
    rw [encodePair, Cslib.Complexity.DenseSAT.Converter.delimit_eq, List.append_assoc]
    rfl
  rw [hq] at hp
  obtain ⟨v', T, hm, hs, hf, hk⟩ := moveB_run (M := controller)
    (a := Stack.spare) (b := Stack.prefix) (d := some) (g := id)
    (self := Label.spare) (next := Label.call) rfl (by decide)
    (encSnd x) (encSnd x) [] false (layout w [] (encSnd x) [] a b)
    (by simp [layout]) rfl rfl
  have hT : T = S := by
    funext k
    cases k <;> first | exact hs | simpa [S, layout] using hf | exact hk _ (by decide) (by decide)
  rw [hT] at hm
  have hm' := controller_run (ei := ei) (eo := eo) (inputStack M ei q) hm rfl
  have hcall : Run (program M ei eo) 1 (atLabel M .call (inputStack M ei q) S v')
      (withVerifier M S v' (initList M (q.map ei.symm))) := by
    rw [Cslib.Complexity.Host.initList_eq]
    exact Run.single rfl
  obtain ⟨⟨t, ht⟩, ht'⟩ := h.outputsFun (x, r)
  change Run M.m t (initList M (q.map ei.symm)) (haltList M [eo.symm (R (x, r))]) at ht
  have hv := verifier_run (ei := ei) (eo := eo) S v' ht
  have hret : Run (program M ei eo) 1
      (withVerifier M S v' (haltList M [eo.symm (R (x, r))]))
      (atLabel M .next (fun _ => [])
        (layout w (encSnd x).reverse [] [] (a + (R (x, r)).toNat) (b + (!R (x, r)).toNat))
        (R (x, r))) := by
    have hyes : update S .yes (true :: cnt true a) =
        layout w (encSnd x).reverse [] [] (a + 1) b := by
      funext k
      cases k <;> rfl
    have hno : update S .no (true :: cnt true b) =
        layout w (encSnd x).reverse [] [] a (b + 1) := by
      funext k
      cases k <;> rfl
    apply Run.single
    rw [Cslib.Complexity.Host.haltList_eq]
    cases R (x, r) <;>
      simp [S, atLabel, withController, lab₁, program_return, recordVote, TM2.stepAux, mkStk,
        update_mkStk_inl (M₁ := M) (M₂ := ctrl), update_mkStk_inr (M₁ := M) (M₂ := ctrl),
        update_idem, layout, hyes, hno]
  change t ≤ h.time.eval (bitEncode (x, r)).length at ht'
  exact (((((hr.trans hp).trans hm').trans hcall).trans hv).trans hret).le (by omega)

private theorem compare_run (pref : List Bool) (a b : ℕ) (v : Bool) :
    ∃ v' S, RunLe controller (a + b + 1)
      ⟨some .compare, v, layout [] pref [] [] a b⟩
      ⟨some (.clean (decide (b < a))), v', S⟩ := by
  induction a generalizing b v with
  | zero =>
    cases b <;> exact ⟨_, _, (Run.single rfl).le (by omega)⟩
  | succ a ih =>
    cases b with
    | zero => exact ⟨_, _, (Run.single rfl).le (by omega)⟩
    | succ b =>
      obtain ⟨v', S, h⟩ := ih b true
      have h₁ : Run controller 1 ⟨some .compare, v, layout [] pref [] [] (a + 1) (b + 1)⟩
          ⟨some .compare, true, layout [] pref [] [] a b⟩ := by
        apply Run.single
        apply congrArg (TM2.Cfg.mk (some Label.compare) true)
        funext k
        cases k <;> rfl
      have hn : 1 + (a + b + 1) ≤ (a + 1) + (b + 1) + 1 := by omega
      exact ⟨v', S, by simpa only [Nat.succ_lt_succ_iff] using ((h₁.le le_rfl).trans h).mono hn⟩

private def vote (R : List Bool × List Bool → Bool) (x w : List Bool) (a b : ℕ) : Bool :=
  ((undelimitBlocks w).map fun rows =>
    let votes := rows.map fun r => R (x, r)
    decide (b + votes.count false < a + votes.count true)).getD false

private theorem vote_delimit (R : List Bool × List Bool → Bool) (x r w : List Bool) (a b : ℕ) :
    vote R x (delimit r ++ w) a b =
      vote R x w (a + (R (x, r)).toNat) (b + (!R (x, r)).toNat) := by
  rw [vote, blocks_delimit]
  cases hw : undelimitBlocks w <;> cases hb : R (x, r) <;>
    simp [vote, hw, hb, Bool.toNat, Nat.add_assoc, Nat.add_comm]

/-- Scan the remaining advice. The size bound is the original encoded input length. -/
private theorem scan_run {R : List Bool × List Bool → Bool}
    (h : TM2ComputableInPolyTime bitEncode bitEncode R) (x w : List Bool) (a b B : ℕ) (v : Bool)
    (hB : (bitEncode (x, w)).length ≤ B) :
    ∃ v' S, RunLe (program h.tm h.inputAlphabet h.outputAlphabet)
      ((w.length + 1) * (h.time.eval B + 4 * B + 10) + a + b)
      (atLabel h.tm .next (fun _ => []) (layout w (encSnd x).reverse [] [] a b) v)
      (atLabel h.tm (.clean (vote R x w a b)) (fun _ => []) S v') := by
  let V : ∀ k, List (h.tm.Γ k) := fun _ => []
  let P := program h.tm h.inputAlphabet h.outputAlphabet
  let pref := (encSnd x).reverse
  let cost := h.time.eval B + 4 * B + 10
  by_cases he : w = []
  · subst w
    obtain ⟨v', S, hc⟩ := compare_run pref a b false
    have hn : Run controller 1 ⟨some .next, v, layout [] pref [] [] a b⟩
        ⟨some .compare, false, layout [] pref [] [] a b⟩ := Run.single rfl
    have hr : RunLe P (1 + (a + b + 1))
        (atLabel h.tm .next V (layout [] pref [] [] a b) v)
        (atLabel h.tm (.clean (decide (b < a))) V S v') :=
      controller_runLe V ((hn.le le_rfl).trans hc) rfl
    refine ⟨v', S, ?_⟩
    simpa [vote, undelimitBlocks, undelimitBlocksAux] using hr.mono
      (show 1 + (a + b + 1) ≤ ([] : List Bool).length.succ * cost + a + b by
        simp [cost]; omega)
  · have hv : w.head?.isSome = true := by cases w <;> simp_all
    have hn : Run controller 1 ⟨some .next, v, layout w pref [] [] a b⟩
        ⟨some .read, true, layout w pref [] [] a b⟩ :=
      Run.single (by simp [controller, layout, hv])
    cases hw : undelimit w with
    | none =>
      obtain ⟨v', S, hr⟩ := Block.run_none (M := controller) (a := Stack.input)
        (b := Stack.coins) (d := some) (g := id) (self := Label.read) (good := Label.coins)
        (bad := Label.clean false) rfl (by decide) id (fun _ => rfl) w true
        (layout w pref [] [] a b) (by simp [layout]) hw
      have hnone : undelimitBlocks w = none := by
        cases w with
        | nil => contradiction
        | cons w ws => simp [undelimitBlocks, undelimitBlocksAux, hw]
      have hread := controller_runLe (ei := h.inputAlphabet) (eo := h.outputAlphabet)
        V ((hn.le le_rfl).trans hr) rfl
      have hle : 1 + (w.length + 1) ≤ (w.length + 1) * cost + a + b := by
        have hl := Nat.mul_le_mul_left (w.length + 1) (show 2 ≤ cost by dsimp [cost]; omega)
        omega
      refine ⟨v', S, ?_⟩
      simpa only [vote, hnone, Option.map_none, Option.getD_none] using hread.mono hle
    | some p =>
      obtain ⟨r, rest⟩ := p
      have hf := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hw
      have hl : w.length = 2 * r.length + 1 + rest.length := by
        simp [hf, length_delimit]
      have hp : (bitEncode (x, r)).length ≤ B := by
        rw [encodePair_length] at hB ⊢
        omega
      have ht : (bitEncode (x, rest)).length ≤ B := by
        rw [encodePair_length] at hB ⊢
        omega
      rw [hf] at hn
      obtain ⟨T, hr, hi, hc, hk⟩ := Block.run_delimit (M := controller) (a := Stack.input)
        (b := Stack.coins) (d := some) (g := id) (self := Label.read) (good := Label.coins)
        (bad := Label.clean false) rfl (by decide) id (fun _ => rfl) r rest true
        (layout (delimit r ++ rest) pref [] [] a b) (by simp [layout])
      have hT : T = layout rest pref [] r.reverse a b := by
        funext k
        cases k <;> first | exact hi | simpa [layout] using hc | exact hk _ (by decide) (by decide)
      rw [hT] at hr
      have hread := controller_run (ei := h.inputAlphabet) (eo := h.outputAlphabet)
        V (hn.trans hr) rfl
      have hcall := call_run h x r rest a b false
      let a' := a + (R (x, r)).toNat
      let b' := b + (!R (x, r)).toNat
      obtain ⟨v', S, hrest⟩ := scan_run h x rest a' b' B (R (x, r)) ht
      rw [hf, vote_delimit]
      refine ⟨v', S, ((hread.le le_rfl |>.trans hcall).trans hrest).mono ?_⟩
      have hvotes : a' + b' = a + b + 1 := by
        cases hb : R (x, r) <;> simp [a', b', hb, Bool.toNat] <;> omega
      have htime := eval_mono h.time hp
      have hsize : 2 * r.length + 2 * (encSnd x).length ≤ 4 * B := by
        rw [encodePair_length] at hB
        omega
      have hmul := Nat.mul_le_mul_right cost (show rest.length + 2 ≤ w.length + 1 by omega)
      rw [show rest.length + 2 = rest.length + 1 + 1 by omega, Nat.add_mul, Nat.one_mul, hl] at hmul
      dsimp only [cost] at hmul
      simp only [List.length_append, length_delimit]
      omega
termination_by w.length
decreasing_by omega

/-- Evaluate the strict majority of the verifier's answers on delimiter-framed coin strings.
Empty advice, a tie, or a truncated frame gives `false`. -/
@[expose] public def majorityVerifier (R : List Bool × List Bool → Bool)
    (q : List Bool × List Bool) : Bool :=
  ((undelimitBlocks q.2).map fun rows =>
    let votes := rows.map fun r => R (q.1, r)
    decide (votes.count false < votes.count true)).getD false

private theorem majorityVerifier_eq_vote (R : List Bool × List Bool → Bool) (x w : List Bool) :
    majorityVerifier R (x, w) = vote R x w 0 0 := by simp [majorityVerifier, vote]

private theorem machine_init (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
    (u : List Bool) : initList (machine M ei eo) u =
      atLabel M .start (fun _ => []) (layout u [] [] [] 0 0) := by
  erw [Cslib.Complexity.Host.initList_eq]
  change _ = withController M _ _
  apply congrArg (TM2.Cfg.mk (some (sideLabel .start)) (M.initialState, false, none))
  funext k
  rcases k with k | k | ⟨⟩
  · rfl
  · cases k <;> rfl
  · rfl

private theorem machine_emit (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
    (b : Bool) : Run (program M ei eo) 1
      (atLabel M (.emit b) (fun _ => []) (fun _ => [])) (haltList (machine M ei eo) [b]) := by
  apply Run.single
  rw [Cslib.Complexity.Host.haltList_eq]
  apply congrArg (TM2.Cfg.mk none (M.initialState, false, none))
  funext k
  rcases k with k | k | ⟨⟩
  · rfl
  · cases k <;> rfl
  · rfl

/-- A polynomial-time verifier can be run once per framed coin string and its votes counted
in polynomial time in the combined encoded input length. -/
public theorem isPolyTime_majorityVerifier {R : List Bool × List Bool → Bool}
    (hR : IsPolyTime R) : IsPolyTime (majorityVerifier R) := by
  obtain ⟨h⟩ : Nonempty (TM2ComputableInPolyTime bitEncode bitEncode R) := hR
  let M := h.tm
  let ei := h.inputAlphabet
  let eo := h.outputAlphabet
  let tm := machine M ei eo
  let mid : Polynomial ℕ := Polynomial.X + C 3 +
    (Polynomial.X + 1) * (h.time + C 4 * Polynomial.X + C 10)
  let total : Polynomial ℕ := C (pushBound tm + 1) * mid + Polynomial.X + C 2
  refine ⟨{
    tm := tm
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := total
    outputsFun := ?_ }⟩
  rintro ⟨x, w⟩
  let q := bitEncode (x, w)
  let N := q.length
  let ans := vote R x w 0 0
  suffices hrun : RunLe tm.m (total.eval N) (initList tm q) (haltList tm [ans]) by
    change TM2OutputsInTime tm (q.map id)
      (some ([majorityVerifier R (x, w)].map id)) (total.eval N)
    rw [List.map_id, List.map_id, majorityVerifier_eq_vote]
    exact ⟨⟨hrun.choose, hrun.choose_spec.2⟩, hrun.choose_spec.1⟩
  obtain ⟨v, hstart⟩ := start_run x w
  have hstart' : RunLe tm.m ((encSnd x).length + 2 * w.length + 3) (initList tm q)
      (atLabel M .next (fun _ => []) (layout w (encSnd x).reverse [] [] 0 0) v) := by
    have hi : initList tm q = atLabel M .start (fun _ => []) (layout q [] [] [] 0 0) :=
      machine_init M ei eo q
    rw [hi, show q = _ from encodePair x w]
    exact controller_runLe (fun _ => []) hstart rfl
  obtain ⟨v', S, hscan⟩ := scan_run h x w 0 0 N v le_rfl
  have hlen : N = 2 * (encSnd x).length + 1 + 3 * w.length := encodePair_length x w
  have hmul := Nat.mul_le_mul_right (h.time.eval N + 4 * N + 10)
    (show w.length + 1 ≤ N + 1 by omega)
  have hpre := ((hstart'.trans hscan).mono (show _ ≤ mid.eval N by
    simp only [mid, eval_add, eval_X, eval_C, eval_mul, eval_one]
    omega))
  obtain ⟨t, ht, hr⟩ := hpre
  let B := N + pushBound tm * mid.eval N
  have hB (k : Stack) : (S k).length ≤ B := by
    have hg := length_iter tm (sideStack k) t _ _ hr
    have hi := initList_stk_length_le tm q (sideStack k)
    change (S k).length ≤ ((initList tm q).stk (sideStack k)).length + pushBound tm * t at hg
    exact hg.trans (Nat.add_le_add hi (Nat.mul_le_mul_left _ ht))
  have hc := clean_run (M := controller) (self := Label.clean ans) (next := Label.emit ans)
    (ks := workStacks) rfl (by decide) B v' S (fun k _ => hB k)
  have hnil : (fun k => if k ∈ workStacks then [] else S k) = fun _ => [] := by
    funext k
    cases k <;> simp [workStacks]
  rw [hnil] at hc
  have hc' := controller_runLe (ei := ei) (eo := eo) (fun _ => []) hc rfl
  have hf := machine_emit M ei eo ans
  have hall := ((hr.le ht).trans hc').trans (hf.le le_rfl)
  have hfinal : mid.eval N + (B + 1) + 1 ≤ total.eval N := by
    simp only [total, B, eval_add, eval_mul, eval_C, eval_X]
    ring_nf
    rfl
  exact hall.mono hfinal

end Machine

section Inclusion

open Finset Polynomial MetaMathlibExt.BitstringEncoding

private theorem ncard_filter {α : Type} [Fintype α] (b : α → Bool) :
    Set.ncard {a | b a = true} = ((univ : Finset α).filter fun a => b a).card := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext a
  simp

private theorem error_count {L : DecisionProblem} {p : Polynomial ℕ}
    {R : List Bool × List Bool → Bool}
    (hR : ∀ x,
      (L x = true → 2 * 2 ^ p.eval x.length ≤
        3 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true}) ∧
      (L x = false → 3 * Set.ncard {r : Fin (p.eval x.length) → Bool |
        R (x, List.ofFn r) = true} ≤ 2 ^ p.eval x.length))
    (n : ℕ) (x : Fin n → Bool) :
    3 * ((univ : Finset (Fin (p.eval n) → Bool)).filter
      fun r => !(R (List.ofFn x, List.ofFn r) == L (List.ofFn x))).card ≤
      Fintype.card (Fin (p.eval n) → Bool) := by
  generalize hx : List.ofFn x = y
  have hn : y.length = n := by rw [← hx, List.length_ofFn]
  clear hx x
  subst n
  let f (r : Fin (p.eval y.length) → Bool) := R (y, List.ofFn r)
  have hf := hR y
  simp only [ncard_filter] at hf
  rw [Fintype.card_pi_const, Fintype.card_bool]
  cases hl : L y with
  | false =>
    have he : (univ.filter fun r => (!(f r == false) : Bool) = true) =
        univ.filter (fun r => (f r : Prop)) := by
      apply filter_congr
      intro r _
      cases f r <;> simp
    change 3 * (univ.filter fun r => (!(f r == false) : Bool) = true).card ≤ 2 ^ p.eval y.length
    rw [he]
    exact hf.2 hl
  | true =>
    have ha := hf.1 hl
    have htot := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (p.eval y.length) → Bool))) (fun r => (f r : Prop))
    simp only [card_univ, Fintype.card_pi_const, Fintype.card_bool] at htot
    have he : (univ.filter fun r => (!(f r == true) : Bool) = true) =
        univ.filter (fun r => ¬(f r : Prop)) := by
      apply filter_congr
      intro r _
      cases f r <;> simp
    change 3 * (univ.filter fun r => (!(f r == true) : Bool) = true).card ≤ 2 ^ p.eval y.length
    rw [he]
    change 2 * 2 ^ p.eval y.length ≤ 3 * (univ.filter fun r => (f r : Prop)).card at ha
    omega

/-- **Adleman's theorem: BPP is contained in P/poly.** Every decision problem in BPP lies in
P/poly.

Adleman proved that every language in R (now usually written RP) has polynomial-size circuits.
Bennett and Gill remark that the second part of their Corollary to Theorem 5, that every language
in BPP is in P^A with probability 1 for a random oracle A, generalizes Adleman's result to BPP.

Source: L. Adleman, "Two theorems on
random polynomial time", Proceedings of the Nineteenth Annual Symposium on Foundations of
Computer Science (FOCS 1978), 75-83; C. H. Bennett and J. Gill, "Relative to a random oracle A,
P^A ≠ NP^A ≠ co-NP^A with probability 1", SIAM J. Comput. 10 (1981), no. 1, 96-113, Remark
after the Corollary to Theorem 5 (p. 105). -/
public theorem adleman :
    BPP ⊆ PPoly := by
  classical
  intro L hL
  obtain ⟨p, R, hR, hc⟩ := hL
  have hc' : ∀ n, ∃ r : Fin (2 * (6 * (n + 1))) → (Fin (p.eval n) → Bool),
      ∀ x : Fin n → Bool, 6 * (n + 1) <
        successes (fun a => R (List.ofFn x, List.ofFn a) == L (List.ofFn x)) r := by
    intro n
    exact exists_good_tuple n
      (fun x a => R (List.ofFn x, List.ofFn a) == L (List.ofFn x)) (error_count hc n)
  choose r hr using hc'
  let rows (n : ℕ) := List.ofFn (fun i => List.ofFn (r n i))
  let advice (n : ℕ) := ((rows n).map delimit).flatten
  refine ⟨C 12 * (X + 1) * (C 2 * p + 1), advice, ?_, majorityVerifier R,
    isPolyTime_majorityVerifier hR, ?_⟩
  · intro n
    dsimp [advice, rows]
    rw [List.length_flatten, List.map_map, ← List.ofFn_comp']
    simp only [Function.comp_apply, length_delimit, List.length_ofFn, List.ofFn_const,
      List.sum_replicate, Nat.nsmul_eq_mul, eval_mul, eval_C, eval_add, eval_X, eval_one]
    ring_nf
    rfl
  · intro x
    have hvote := hr x.length x.get
    rw [List.ofFn_get] at hvote
    let f (i : Fin (2 * (6 * (x.length + 1)))) := R (x, List.ofFn (r x.length i))
    have hmajor : 6 * (x.length + 1) < (List.ofFn f).count (L x) := by
      simpa only [successes, beq_iff_eq, List.count_ofFn, f] using hvote
    have htot : (List.ofFn f).count false + (List.ofFn f).count true =
        2 * (6 * (x.length + 1)) := by
      have h (xs : List Bool) : xs.count false + xs.count true = xs.length := by
        induction xs with
        | nil => rfl
        | cons b xs ih => cases b <;> simp <;> omega
      simpa only [List.length_ofFn] using h (List.ofFn f)
    have hf : ((rows x.length).map fun a => R (x, a)) = List.ofFn f :=
      (List.ofFn_comp' (fun i => List.ofFn (r x.length i)) (fun a => R (x, a))).symm
    rw [majorityVerifier, show undelimitBlocks (advice x.length) = some (rows x.length) from
      undelimitBlocks_flatten_delimit _]
    simp only [Option.map_some, Option.getD_some, decide_eq_true_eq, hf]
    cases h : L x with
    | false =>
      rw [h] at hmajor
      simp only [Bool.false_eq_true, false_iff]
      omega
    | true =>
      rw [h] at hmajor
      simp only [true_iff]
      omega

end Inclusion

end MetaMathlibExt.Complexity.KeyTheorems.Adleman
