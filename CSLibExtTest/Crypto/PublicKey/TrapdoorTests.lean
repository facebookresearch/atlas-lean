/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.PublicKey.Trapdoor
import CSLibExt.Crypto.Framework.Negligible
import Mathlib.Analysis.SpecificLimits.Normed
import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
import CSLibExt.Computability.Complexity.PairProjection
import CSLibExt.Computability.Complexity.BoolClosure

namespace Cslib.Crypto.PublicKey.Trapdoor.Tests

open Cslib.Probability.PMF (uniformOfFinset)

private abbrev Bits := List Bool

-- The two possible pairs select different finite spaces. The public and secret labels for
-- the two-point transposition differ; they must not be supplied interchangeably.
private def pairs : Finset (Bits × Bits) := {([], []), ([true], [false])}

private def space (pk : Bits) : Finset Bits := if pk = [true] then {[], [true]} else {[]}

private def transpose (x : Bits) : Bits := if x = [] then [true] else []

private noncomputable def toy : Family where
  setup _ := PMF.pure []
  keys _ _ := uniformOfFinset pairs (by simp [pairs])
  domain v := space v.2.2
  codomain v := space v.2.2
  eval v := if v.1.2.2 = [true] then transpose v.2 else v.2
  invert v := if v.1.2.2 = [false] then transpose v.2 else v.2

example (n : ℕ+) : toy.Generated n [] [true] [false] ∧ toy.Generated n [] [] [] ∧
    ¬ toy.Generated n [] [true] [] := by
  simp [Family.Generated, toy, pairs]

example : (toy.domain (index 1 [] [])).card = 1 ∧ (toy.domain (index 1 [] [true])).card = 2 := by
  decide

private theorem correct_swap (n : ℕ+) : toy.CorrectAt n [] [true] [false] := by
  simp [Family.CorrectAt, toy, index, space, transpose, Set.MapsTo, Set.LeftInvOn]

example (n : ℕ+) : Set.RightInvOn (fun y => toy.invert (index n [] [false], y))
    (fun x => toy.eval (index n [] [true], x)) (toy.domain (index n [] [true])) :=
  ((correct_swap n).bijOn_and_rightInvOn rfl).2

example (n : ℕ+) : ¬ toy.CorrectAt n [] [true] [] := by
  intro h
  have bad := h.2.2 (x := []) (by simp [toy, index, space])
  simp [toy, index, transpose] at bad

-- With just one input and two possible outputs, the extra output can be sent to an
-- arbitrary domain point by the secret map. Correctness does not make this a permutation.
private noncomputable def wider : Family := { toy with
  domain := fun _ => {[]}
  codomain := fun _ => {[], [true]}
  eval := fun _ => []
  invert := fun _ => [] }

example (n : ℕ+) : wider.CorrectAt n [] [] [] ∧
    ¬ Set.SurjOn (fun x => wider.eval (index n [] [], x))
      (wider.domain (index n [] [])) (wider.codomain (index n [] [])) := by
  constructor
  · simp [Family.CorrectAt, wider, Set.MapsTo, Set.LeftInvOn]
  · intro h
    obtain ⟨_, _, he⟩ := h (show [true] ∈ wider.codomain (index n [] []) by simp [wider])
    contradiction

-- A law on the empty set cannot silently stand for a uniform challenge.
example (S : Family) (n : ℕ+) (pp pk sk : Bits) (hg : S.Generated n pp pk sk)
    (he : S.domain (index n pp pk) = ∅) : ¬ S.IsBoundedCoinFunctionScheme := by
  intro h
  simpa [he] using h.domain_nonempty n pp pk sk hg

-- Even a nonempty three-element domain is incompatible with exact sampling from a fixed
-- number of fair bits, independently of which polynomial coin budget is proposed.
example (S : Family) (n : ℕ+) (pp pk sk : Bits) (hg : S.Generated n pp pk sk)
    (hc : (S.domain (index n pp pk)).card = 3) : ¬ S.IsBoundedCoinFunctionScheme := by
  intro h
  obtain ⟨q, hq⟩ := h.card_domain_dvd
  have hthree := hq n pp pk sk hg
  rw [hc] at hthree
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

open MetaMathlibExt MetaMathlibExt.BitstringEncoding MetaMathlibExt.ComplexityTheory
open Cslib.Complexity Cslib.Complexity.PolynomialEncoding _root_.Turing MetaMathlibExt.TM2Program

-- Read one canonically delimited field. The input stack then holds precisely the encoding
-- of the second field. The host accounts for moving and cleaning the other stacks.
private theorem snd_poly {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.snd : α × β → β) := by
  let c := PairSplit.component
  let p : Polynomial ℕ := Polynomial.X + 1
  let tm := Host.rtm c .input .input id .read .good
  refine ⟨{ tm := tm, inputAlphabet := Equiv.refl Bool, outputAlphabet := Equiv.refl Bool,
            time := Host.rtime c .input .input id .read .good p,
            outputsFun := ?_ }⟩
  rintro ⟨a, b⟩
  let x := bitEncode (a, b)
  have hs : Function.update (fun _ : PairSplit.K => ([] : Bits)) .input (x.map id) =
      PairSplit.st x [] [] := by funext k; cases k <;> simp [PairSplit.st]
  have h := Host.rprog_run_at (c := c) (cX := .input) (cO := .input) (gX := id)
    (start := .read) (done := .good) (Equiv.refl Bool) (bitEncode b) p rfl x (by
      obtain ⟨v, hr⟩ := PairSplit.run_delimit (bitEncode a) (bitEncode b) [] false
      refine ⟨v, PairSplit.st (bitEncode b) (bitEncode a ++ []) [], ?_, ?_⟩
      swap
      · change bitEncode b = (bitEncode b).map id
        simp
      rw [hs]
      apply hr.le
      change 2 * (bitEncode a).length + 2 ≤ p.eval (delimit (bitEncode a) ++ bitEncode b).length
      simp [p, length_delimit])
  let t := h.choose
  refine ⟨⟨t, ?_⟩, h.choose_spec.1⟩
  change Run tm.m t (initList tm (x.map id)) (haltList tm ((bitEncode b).map id))
  erw [List.map_id, List.map_id, Host.initList_eq, Host.haltList_eq]
  have hh : Run (Host.rprog c .input .input id .read .good) t _ _ := h.choose_spec.2
  rw [show (⇑(Equiv.refl Bool).symm) = id from rfl, List.map_id] at hh
  exact hh

-- Inspect two input symbols. The one-bit words are accepted, longer ones rejected, and the
-- flag selects whether to accept the empty word. The host accounts for input and output handling.
private def sizeTest (allowEmpty : Bool) : Host.Comp where
  K := Bool
  Γ := fun _ => Bool
  L := Bool
  prog l := if l then .halt else
    .pop false (fun _ a => allowEmpty || a.isSome) (.peek false (fun v a => v && a.isNone)
      (.push true id (.goto fun _ => true)))
  ks := [false, true]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

private theorem singleton_poly : IsPolyTime (fun x : Bits => decide (x.length = 1)) := by
  apply Host.isPolyTime_decider (c := sizeTest false) (cX := false) (cO := true) (gX := id)
    (start := false) (done := true) (Equiv.refl Bool) _ 1 rfl
  intro x
  cases x with
  | nil => exact ⟨_, _, (Run.single rfl).le (by simp), rfl⟩
  | cons b xs => cases xs with
    | nil => exact ⟨_, _, (Run.single rfl).le (by simp), rfl⟩
    | cons c xs => exact ⟨_, _, (Run.single rfl).le (by simp), rfl⟩

private theorem short_poly : IsPolyTime (fun x : Bits => decide (x.length ≤ 1)) := by
  apply Host.isPolyTime_decider (c := sizeTest true) (cX := false) (cO := true) (gX := id)
    (start := false) (done := true) (Equiv.refl Bool) _ 1 rfl
  intro x
  cases x with
  | nil => exact ⟨_, _, (Run.single rfl).le (by simp), rfl⟩
  | cons b xs => cases xs with
    | nil => exact ⟨_, _, (Run.single rfl).le (by simp), rfl⟩
    | cons c xs => exact ⟨_, _, (Run.single rfl).le (by simp), rfl⟩

private abbrev letters : Finset Bits := {[false], [true]}
private noncomputable def binaryFamily : Family where
  setup _ := PMF.pure []
  keys _ pp := PMF.pure (pp, [])
  domain _ := letters
  codomain _ := letters
  eval := Prod.snd
  invert := Prod.snd

private theorem length_one_iff (z : Bits) : z.length = 1 ↔ z ∈ letters := by
  cases z with
  | nil => simp [letters]
  | cons b z => cases b <;> cases z <;> simp [letters]

open Cslib.Probability.PMF (uniformOfFintype uniformOfFinset)

private theorem uniform_letter : (uniformOfFintype (Fin 1 → Bool)).map List.ofFn =
    uniformOfFinset letters (by simp [letters]) := by
  classical
  ext z
  rw [PMF.map_apply, tsum_fintype, Cslib.Probability.PMF.uniformOfFinset_apply]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _
    (fun b => if z = [b] then ((2 : ENNReal)⁻¹) else 0) (by intro r; simp [List.ofFn_succ])]
  cases z with
  | nil => simp [letters]
  | cons b z => cases b <;> cases z <;> simp [letters]

-- A full two-letter permutation scheme: the sampler reads one bit, both maps are the identity,
-- and the two generators read zero bits. No hardness property is imposed on this fixture.
private theorem binary_permutation : binaryFamily.IsBoundedCoinPermutationScheme := by
  constructor
  · constructor
    · constructor
      · let mem := fun t : (Bits × Bits × Bits) × Bits => decide (t.2.length = 1)
        have hm : IsPolyTime mem := snd_poly.comp singleton_poly
        exact ⟨mem, mem, hm, hm, fun _ _ _ _ _ z => by simp [mem, binaryFamily, length_one_iff]⟩
      · exact snd_poly
      · exact snd_poly
      · refine ⟨1, fun n pp pk sk hg => ?_⟩
        obtain ⟨rfl, rfl, rfl⟩ : pp = [] ∧ pk = pp ∧ sk = [] := by
          simpa [Family.Generated, binaryFamily] using hg
        simp [binaryFamily, letters]
      · intro n pp pk sk _
        exact ⟨fun _ h => h, fun _ h => h, fun _ _ => rfl⟩
    · refine ⟨0, Prod.snd, snd_poly, fun n => ?_⟩
      simp [binaryFamily, PMF.map_comp, Function.comp_def, List.ofFn_zero,
        PMF.map_const, Function.const_def]
    · refine ⟨0, Prod.snd, snd_poly, fun n pp _ => ?_⟩
      simp [binaryFamily, PMF.map_comp, Function.comp_def, List.ofFn_zero,
        PMF.map_const, Function.const_def]
    · refine ⟨1, Prod.snd, snd_poly, fun n pp pk sk _ => ⟨by simp [binaryFamily, letters], ?_⟩⟩
      rw [PMF.map_comp]
      change (uniformOfFintype (Fin ((1 : Polynomial ℕ).eval n.val) → Bool)).map List.ofFn = _
      rw [Polynomial.eval_one]
      exact uniform_letter
  · exact fun _ _ _ _ _ => rfl

open Cslib.Crypto.Framework FairSampler
open scoped ENNReal

-- A genuine local transition table with no work tapes. Each pair 00, 01, 10 emits one
-- of [], [false], [true] and halts. 11 returns to the initial configuration.
private def act (q : Option (Option Bool)) (o : Option Bool) : Action 0 Bool (Option Bool) :=
  ⟨0, Fin.elim0, o, q⟩
private def ternary : FairSampler where
  tapes := 0
  State := Option Bool
  start := none
  table q _ _ b := match q, b with
    | none, a => act (some (some a)) none
    | some false, false => act none none
    | some false, true => act none (some false)
    | some true, false => act none (some true)
    | some true, true => act (some none) none

private def start (x : Bits) : Cfg ternary.tapes Bool ternary.State x := Cfg.init ternary.start x
private def stop (x y : Bits) : Cfg ternary.tapes Bool ternary.State x :=
  {start x with state := none, output := y}

private theorem table2 (x : Bits) :
    ternary.two (start x) false false = stop x [] ∧
    ternary.two (start x) false true = stop x [false] ∧
    ternary.two (start x) true false = stop x [true] ∧
    ternary.two (start x) true true = start x := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Cfg.ext_zero_tapes <;>
    simp [two, step, start, stop, ternary, act, Action.apply]

private theorem live_stop (x y : Bits) (n : ℕ) : live ternary n (stop x y) = 0 := by
  cases n <;> simp [live, stop, Cfg.Halted]

private theorem live_ternary (x : Bits) (n : ℕ) : live ternary n (start x) = (4 : ℝ≥0∞)⁻¹ ^ n := by
  induction n with
  | zero => simp [live, start, Cfg.Halted]
  | succ n ih =>
    obtain ⟨h0,h1,h2,h3⟩ := table2 x
    have hstart : ¬ (start x).Halted := by intro h; cases h
    rw [live, ite_eq_right_of_eq_false _ _ (eq_false hstart), avg, h0, h1, h2, h3,
      live_stop, live_stop, live_stop, ih, pow_succ']
    simp

private def codes : Finset Bits := {[], [false], [true]}

private theorem hit_ternary (x y : Bits) (n : ℕ) :
    hit ternary y (n+1) (start x) = if y ∈ codes then (4 : ℝ≥0∞)⁻¹ ^ (n+1) else 0 := by
  have hstart : ¬ (start x).Halted := by intro h; cases h
  have hz (z : Bits) : hit ternary y 0 (stop x z) = if z = y then 1 else 0 := by
    simp [hit, stop, Cfg.Halted]
  have hn (z : Bits) (j : ℕ) : hit ternary y (j+1) (stop x z) = 0 := by
    simp [hit, stop, Cfg.Halted]
  have hzero : hit ternary y 0 (start x) = 0 := by simp [hit, start, Cfg.Halted]
  obtain ⟨h0,h1,h2,h3⟩ := table2 x
  induction n with
  | zero =>
    rw [hit, ite_eq_right_of_eq_false _ _ (eq_false hstart), avg, h0,h1,h2,h3, hzero, hz, hz, hz]
    cases y with
    | nil => simp [codes]
    | cons b ys => cases b <;> cases ys <;> simp [codes]
  | succ n ih =>
    rw [hit, ite_eq_right_of_eq_false _ _ (eq_false hstart), avg, h0,h1,h2,h3, hn, hn, hn, ih]
    split <;> simp [pow_succ']

private theorem mass_ternary (x y : Bits) :
    mass ternary x y = if y ∈ codes then (3 : ℝ≥0∞)⁻¹ else 0 := by
  change (∑' n, hit ternary y n (start x)) = _
  have ht := tsum_eq_zero_add' (f := fun n : ℕ => hit ternary y n (start x))
    CompleteLattice.summable
  rw [ht]
  have hzero : hit ternary y 0 (start x) = 0 := by simp [hit, start, Cfg.Halted]
  simp_rw [hzero, hit_ternary, zero_add]
  by_cases h : y ∈ codes
  · simp only [h, ite_true, ENNReal.tsum_geometric_add_one]
    have hle : (4 : NNReal)⁻¹ < 1 := by rw [inv_lt_one₀ (by norm_num)]; norm_num
    have hh : (1 : NNReal) - 4⁻¹ ≠ 0 := ne_of_gt (tsub_pos_of_lt hle)
    have hnum : (4 : NNReal)⁻¹ * (1 - 4⁻¹)⁻¹ = 3⁻¹ := by
      apply NNReal.eq
      push_cast [NNReal.coe_sub hle.le]
      norm_num
    have hcast := congrArg (fun r : NNReal => (r : ENNReal)) hnum
    simpa only [ENNReal.coe_mul, ENNReal.coe_inv hh, ENNReal.coe_sub, ENNReal.coe_one,
      ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0),
      ENNReal.coe_ofNat] using hcast
  · simp [h]


private theorem ternary_realizes (x : Bits) : ternary.mass x =
    ⇑(uniformOfFinset codes (by simp [codes])) := by
  funext y
  rw [mass_ternary]
  simp [Cslib.Probability.PMF.uniformOfFinset_apply, codes]

private noncomputable def ternaryAlgorithm : TailAlgorithm where
  machine := ternary
  bound := 1
  efficient := {
    halts := fun n aux _ => (ternary_realizes (input n aux)) ▸
      (uniformOfFinset codes (by simp [codes])).2
    tail := by
      refine ⟨Polynomial.X, fun n => (4 : ℝ)⁻¹ ^ n, fun _ => by positivity, ?_, ?_⟩
      · apply Cslib.Crypto.Framework.NegligibleAdv.of_superpolynomialDecay
        intro j
        exact tendsto_pow_const_mul_const_pow_of_abs_lt_one j (by norm_num)
      · intro n aux _
        change live ternary (Polynomial.X.eval n.val) (start (input n aux)) ≤ _
        rw [Polynomial.eval_X, live_ternary, ENNReal.ofReal_pow (by norm_num : 0 ≤ (4 : ℝ)⁻¹)]
        simp }

-- Setup outputs no symbol. Key generation outputs the single symbol in the canonical encoding
-- of the empty public/secret pair. Both are local one-transition machines, on every input.
private def emitter (o : Option Bool) : FairSampler where
  tapes := 0
  State := Unit
  start := ()
  table _ _ _ _ := ⟨0, Fin.elim0, o, none⟩

private def initial (o : Option Bool) (x : Bits) :=
  Cfg.init (k := (emitter o).tapes) (emitter o).start x

private def terminal (o : Option Bool) (x : Bits) :
    Cfg (emitter o).tapes Bool (emitter o).State x :=
  {initial o x with state := none, output := o.toList}

private theorem emitter_two (o : Option Bool) (x : Bits) (a b : Bool) :
    (emitter o).two (initial o x) a b = terminal o x := by
  apply Cfg.ext_zero_tapes <;> simp [emitter, initial, terminal, two, step, Action.apply]

private theorem emitter_mass (o : Option Bool) (x : Bits) :
    (emitter o).mass x = ⇑(PMF.pure o.toList) := by
  funext y
  change (∑' n, (emitter o).hit y n (initial o x)) = _
  have h₀ : ¬ (initial o x).Halted := by intro h; cases h
  rw [tsum_eq_single 1]
  · rw [hit, ite_eq_right_of_eq_false _ _ (eq_false h₀)]
    simp only [emitter_two, avg_const]
    simp [hit, terminal, Cfg.Halted, PMF.pure_apply, eq_comm]
  · intro n hn
    cases n with
    | zero => simp [hit, initial, Cfg.Halted]
    | succ n => cases n with
      | zero => contradiction
      | succ n =>
        rw [hit, ite_eq_right_of_eq_false _ _ (eq_false h₀)]
        simp [emitter_two, hit, terminal, Cfg.Halted]

private noncomputable def constantAlgorithm (o : Option Bool) (b : Polynomial ℕ := 0) :
    TailAlgorithm where
  machine := emitter o
  bound := b
  efficient := {
    halts := fun n aux _ => (emitter_mass o (input n aux)) ▸ (PMF.pure o.toList).2
    tail := by
      refine ⟨1, fun _ => 0, fun _ => le_rfl, Cslib.Crypto.Framework.negligibleAdv_zero, ?_⟩
      intro n aux _
      change (emitter o).live (Polynomial.eval n.val 1) (initial o (input n aux)) ≤ _
      rw [Polynomial.eval_one]
      change live _ (0 + 1) (initial o (input n aux)) ≤ _
      have hc : ¬ (initial o (input n aux)).Halted := by intro h; cases h
      rw [live, ite_eq_right_of_eq_false _ _ (eq_false hc)]
      simp only [emitter_two, avg_const]
      simp [live, terminal, Cfg.Halted] }

private noncomputable def threeLetters : Family where
  setup _ := PMF.pure []
  keys _ _ := PMF.pure ([], [])
  domain _ := codes
  codomain _ := codes
  eval := Prod.snd
  invert := Prod.snd

private theorem mem_codes (z : Bits) : z.length ≤ 1 ↔ z ∈ codes := by
  cases z with
  | nil => simp [codes]
  | cons b zs => cases b <;> cases zs <;> simp [codes]

-- All clauses of the broad definition hold; this very same family cannot satisfy the strict one.
private theorem three_permutation :
    threeLetters.IsPermutationScheme ∧ ¬ threeLetters.IsBoundedCoinPermutationScheme := by
  have keys {n pp pk sk} (hg : threeLetters.Generated n pp pk sk) :
      pp = [] ∧ pk = [] ∧ sk = [] := by simpa [Family.Generated, threeLetters] using hg
  constructor
  · refine ⟨?_, fun _ _ _ _ _ => rfl⟩
    constructor
    · constructor
      · let mem := fun t : (Bits × Bits × Bits) × Bits => decide (t.2.length ≤ 1)
        have hm : IsPolyTime mem := snd_poly.comp short_poly
        exact ⟨mem, mem, hm, hm, fun _ _ _ _ _ z => by simp [mem, threeLetters, mem_codes]⟩
      · exact snd_poly
      · exact snd_poly
      · refine ⟨1, fun n pp pk sk hg => ?_⟩
        obtain ⟨rfl, rfl, rfl⟩ := keys hg
        simp [threeLetters, codes]
      · exact fun _ _ _ _ _ => ⟨fun _ h => h, fun _ h => h, fun _ _ => rfl⟩
    · exact ⟨constantAlgorithm none, fun _ => ⟨by simp, emitter_mass _ _⟩⟩
    · refine ⟨constantAlgorithm (some false), fun n pp hp => ?_⟩
      obtain rfl : pp = [] := by simpa [threeLetters] using hp
      refine ⟨by simp, ?_⟩
      rw [show threeLetters.keys n [] = PMF.pure (([] : Bits), ([] : Bits)) from rfl, PMF.pure_map]
      change (emitter (some false)).mass (input n []) = ⇑(PMF.pure ([false] : Bits))
      exact emitter_mass (some false) _
    · refine ⟨ternaryAlgorithm, fun n pp pk sk hg => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := keys hg
      refine ⟨by simp [threeLetters, codes], ?_, ternary_realizes _⟩
      change (bitEncode (([] : Bits), ([] : Bits))).length ≤ (1 : Polynomial ℕ).eval n.val
      rw [Polynomial.eval_one]
      decide
  · intro h
    have hg : threeLetters.Generated 1 [] [] [] := by simp [Family.Generated, threeLetters]
    obtain ⟨q, hq⟩ := h.1.card_domain_dvd
    have hh : 3 ∣ 2 ^ q.eval 1 := by simpa [threeLetters, codes] using hq 1 [] [] [] hg
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hh)

open Cslib.Crypto.Framework

-- Negligibility is on natural numbers with a dummy value at zero. It cannot hold when a
-- positive lower bound holds at every *positive* security parameter.
private theorem not_negligible_of_positive_bound {f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hl : ∀ n : ℕ+, δ ≤ f n.val) : ¬ NegligibleAdv f := by
  intro h
  apply not_negligibleAdv_const hδ
  apply NegligibleAdv.of_eventually_le
  intro c
  obtain ⟨N, hN⟩ := h.eventually_le c
  exact ⟨max 1 N, fun n hn => (hl ⟨n, by omega⟩).trans (hN n (by omega))⟩

-- In the identity permutation on the two letters, the public image is the sampled letter.
-- Merely reading the image from the public tuple succeeds, with no coins at all.
private abbrev readImage (t : (Bits × Bits × Bits) × Bits × Bits) : Bits := t.2.1

private theorem binary_readImage (n : ℕ+) (m : ℕ) :
    binaryFamily.boundedCoinOneWayGame binary_permutation.1.domain_nonempty readImage n m =
      PMF.pure true := by
  simpa [Family.boundedCoinOneWayGame, binaryFamily, readImage, PMF.map_const, Function.const_def]
    using PMF.bind_const (uniformOfFinset letters (by simp [letters])) (PMF.pure true)

example : ¬ binaryFamily.IsBoundedCoinOneWay binary_permutation.1 := by
  intro h
  have hA : IsPolyTime readImage := snd_poly.comp Cslib.Complexity.isPolyTime_fst
  apply not_negligible_of_positive_bound (δ := 1) zero_lt_one _ (h 0 readImage hA)
  intro n
  erw [dite_eq_left n.property, binary_readImage n]
  simp [winProb]

-- For the three equally likely words, a constant output matches on precisely one word.
-- The constant machine takes one transition (one checkpoint suffices). Its envelope of five
-- auxiliary bits covers the canonical encoding of the two empty parameters and any public image.
private noncomputable abbrev blankObserver := constantAlgorithm none 5

private theorem blank_fits : threeLetters.TranscriptFits blankObserver := by
  intro n pp pk sk hg y hy
  obtain ⟨rfl, rfl, rfl⟩ : pp = [] ∧ pk = [] ∧ sk = [] := by
    simpa [Family.Generated, threeLetters] using hg
  obtain h | h | h : y = [] ∨ y = [false] ∨ y = [true] := by
    simpa [threeLetters, codes] using hy
  all_goals
    subst y
    change (bitEncode _).length ≤ (5 : Polynomial ℕ).eval n.val
    rw [Polynomial.eval_ofNat]
    decide

private theorem blank_law (s : Bits) (hh : HasSum (blankObserver.machine.mass s) 1) :
    blankObserver.machine.law s hh = PMF.pure [] :=
  DFunLike.ext _ _ (congrFun (emitter_mass none s))

private theorem three_blank_winProb (n : ℕ+) :
    winProb (threeLetters.transcriptGame three_permutation.1.1 blankObserver blank_fits n) =
      (1 : ℝ) / 3 := by
  classical
  simp only [Family.transcriptGame, threeLetters, PMF.pure_bindOnSupport, blank_law,
    PMF.pure_map, PMF.bindOnSupport_eq_bind]
  change winProb ((uniformOfFinset codes _).map (fun x => decide (([] : Bits) = x))) = _
  rw [winProb, PMF.map_apply, tsum_eq_single ([] : Bits)]
  · simp [codes, one_div]
  · intro z hz
    simp [Ne.symm hz]

example : ¬ threeLetters.IsTranscriptOneWay three_permutation.1.1 := by
  intro h
  apply not_negligible_of_positive_bound (δ := 1 / 3) (by norm_num) _ (h blankObserver blank_fits)
  intro n
  erw [dite_eq_left n.property]
  exact (three_blank_winProb n).ge

-- For the key-dependent fixture, pass (key, word) to a two-input operation. In the canonical
-- encoding of ((unary, pp, key), word) the first two inner fields each have two framing layers.
-- Skipping these fields leaves exactly the encoding of (key, word), with no re-encoding.
private def skipField (self next : Fin 3) : TM2.Stmt (fun _ : Unit => Bool) (Fin 3) Bool :=
  .pop () (fun v _ => v) <| .pop () (fun _ o => o.getD false) <| .branch id
    (.pop () (fun _ _ => false) <| .pop () (fun v _ => v) (.goto fun _ => self))
    (.goto fun _ => next)

private def keepKeyTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Bool
  initialState := false
  m l := if l = 0 then skipField 0 1 else if l = 1 then skipField 1 2 else .halt

private def skipCfg (l : Option (Fin 3)) (w : Bits) : keepKeyTM.Cfg := ⟨l, false, fun _ => w⟩

private theorem skipField_run (self next : Fin 3) (h : keepKeyTM.m self = skipField self next)
    (u rest val : Bits) : Run keepKeyTM.m (u.length + 1)
      (skipCfg (some self) (delimit (delimit u ++ rest) ++ val))
      (skipCfg (some next) (delimit rest ++ val)) := by
  induction u with
  | nil =>
    apply Run.single
    rw [h]
    apply congrArg (TM2.Cfg.mk (some next) false)
    funext k
    cases k
    rfl
  | cons b u ih =>
    apply Run.head _ ih
    simp only [TM2.step, skipCfg, h, Option.some.injEq]
    apply congrArg (TM2.Cfg.mk (some self) false)
    funext k
    cases k
    rfl

private abbrev keepKey (v : (Bits × Bits × Bits) × Bits) : Bits × Bits := (v.1.2.2, v.2)

private theorem keepKey_poly : IsPolyTime keepKey := by
  refine ⟨{ tm := keepKeyTM, inputAlphabet := Equiv.refl Bool, outputAlphabet := Equiv.refl Bool,
            time := Polynomial.X + 3, outputsFun := ?_ }⟩
  rintro ⟨⟨s, p, k⟩, z⟩
  let u := bitEncode s
  let v := bitEncode p
  let r := bitEncode k
  let w := bitEncode z
  refine ⟨⟨u.length + 1 + (v.length + 1) + 1, ?_⟩, ?_⟩
  · have h0 := skipField_run 0 1 rfl u (delimit v ++ r) w
    have h1 := skipField_run 1 2 rfl v r w
    have h2 : Run keepKeyTM.m 1 (skipCfg (some 2) (delimit r ++ w))
        (skipCfg none (delimit r ++ w)) := Run.single rfl
    change Run keepKeyTM.m _
      (initList keepKeyTM ((delimit (delimit u ++ (delimit v ++ r)) ++ w).map id))
      (haltList keepKeyTM ((delimit r ++ w).map id))
    erw [List.map_id, List.map_id]
    exact (h0.trans h1).trans h2
  · change _ ≤ (Polynomial.X + 3 : Polynomial ℕ).eval
      (delimit (delimit u ++ (delimit v ++ r)) ++ w).length
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
      List.length_append, length_delimit]
    omega

private abbrev gate (op : Bool → Bool → Bool) (v : (Bits × Bits × Bits) × Bits) : Bits :=
  [op (v.2.headD false) (v.1.2.2.headD false)]

private theorem gate_poly (op : Bool → Bool → Bool) : IsPolyTime (gate op) :=
  (keepKey_poly.comp (isPolyTime_heads op)).comp isPolyTime_singleton

-- The two raw input stacks contain the key and the candidate word. Accept exactly one bit,
-- allowing true only when the public key's bit is true.
private abbrev allowed (p : Bits × Bits) :=
  decide (p.2.length = 1) && (!p.2.headD false || p.1.headD false)

private abbrev allowedComp : Host.Comp where
  K := Bool
  Γ _ := Bool
  L := Fin 3
  prog l := if l = 0 then
    .peek false (fun _ k => k.getD false) <|
    .pop true (fun k b => b.isSome && (!b.getD false || k)) <|
      .peek true (fun s b => s && b.isNone) (.goto fun s => if s then 1 else 2)
    else .halt
  ks := [false, true]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

private theorem allowed_poly : IsPolyTime allowed := by
  apply Host.isPolyTime_verifier (c := allowedComp) (cX := false) (cW := true)
    (gX := id) (gW := id) (start := 0) (yes := 1) (no := 2)
    (fun k z => allowed (k, z)) 1 (by decide : (false : Bool) ≠ true)
    (by decide : (1 : Fin 3) ≠ 2) rfl rfl
  intro k z
  cases k with
  | nil => cases z with
    | nil => exact ⟨_, _, (Run.single rfl).le (by simp)⟩
    | cons b z => cases b <;> cases z <;> exact ⟨_, _, (Run.single rfl).le (by simp)⟩
  | cons a k => cases a <;> cases z with
    | nil => exact ⟨_, _, (Run.single rfl).le (by simp)⟩
    | cons b z => cases b <;> cases z <;> exact ⟨_, _, (Run.single rfl).le (by simp)⟩

private abbrev fibre (pk : Bits) : Finset Bits := if pk.headD false then letters else {[false]}

private noncomputable def keyedLetters : Family where
  setup _ := PMF.pure []
  keys _ _ := (uniformOfFinset letters (by simp [letters])).map fun b => (b, b)
  domain ctx := fibre ctx.2.2
  codomain ctx := fibre ctx.2.2
  eval := gate Bool.xor
  invert := gate Bool.xor

private theorem matching (n : ℕ+) (pp pk sk : Bits) : keyedLetters.Generated n pp pk sk ↔
    pp = [] ∧ (pk = [false] ∨ pk = [true]) ∧ sk = pk := by
  simp [Family.Generated, keyedLetters, letters]
  grind

private theorem allowed_iff (k z : Bits) : allowed (k, z) = true ↔ z ∈ fibre k := by
  cases hk : (k.head?).getD false <;> cases z with
    | nil => simp [allowed, fibre, hk, letters]
    | cons b z => cases b <;> cases z <;> simp [allowed, fibre, hk, letters]

private theorem keyed_uniform (ctx : Bits × Bits × Bits) : ∃ h : (fibre ctx.2.2).Nonempty,
    ((uniformOfFintype (Fin 1 → Bool)).map List.ofFn).map (fun r => gate Bool.and (ctx,r)) =
      uniformOfFinset (fibre ctx.2.2) h := by
  classical
  cases hk : (ctx.2.2.head?).getD false with
  | false =>
    refine ⟨by simp [fibre, hk], ?_⟩
    simp only [gate, List.headD_eq_head?_getD, hk, Bool.and_false]
    erw [PMF.map_const]
    ext y
    simp [fibre, hk, Cslib.Probability.PMF.uniformOfFinset_apply, PMF.pure_apply]
  | true =>
    refine ⟨by simp [fibre, hk, letters], ?_⟩
    have he : (fun r : Fin 1 → Bool => gate Bool.and (ctx,List.ofFn r)) = List.ofFn := by
      funext r
      simp [gate, hk, List.ofFn_succ]
    rw [PMF.map_comp]
    change (uniformOfFintype _).map (fun r : Fin 1 → Bool => gate Bool.and (ctx,List.ofFn r)) = _
    rw [he]
    simpa [fibre, hk] using uniform_letter

private theorem keyed_permutation : keyedLetters.IsBoundedCoinPermutationScheme := by
  refine ⟨?_, fun _ _ _ _ _ => rfl⟩
  constructor
  · constructor
    · have hm := keepKey_poly.comp allowed_poly
      exact ⟨_, _, hm, hm, fun n pp pk sk _ z => ⟨allowed_iff pk z, allowed_iff pk z⟩⟩
    · exact gate_poly _
    · exact gate_poly _
    · refine ⟨1, fun n pp pk sk hg => ?_⟩
      obtain ⟨rfl, hpk, rfl⟩ := (matching ..).mp hg
      rcases hpk with rfl | rfl <;> simp [keyedLetters, fibre, letters, index]
    · intro n pp pk sk hg
      obtain ⟨rfl, hpk, rfl⟩ := (matching ..).mp hg
      rcases hpk with rfl | rfl <;>
        simp [Family.CorrectAt, keyedLetters, fibre, letters, index, gate, Set.MapsTo,
          Set.LeftInvOn]
  · refine ⟨0, Prod.snd, snd_poly, fun n => ?_⟩
    simp [keyedLetters, PMF.map_comp, Function.comp_def, List.ofFn_zero, PMF.map_const,
      Function.const_def]
  · let g := fun t : Bits × Bits × Bits => (t.2.2, t.2.2)
    have hproj : IsPolyTime (fun t : Bits × Bits × Bits => t.2.2) := snd_poly.comp snd_poly
    refine ⟨1, g, hproj.comp isPolyTime_dup, fun n pp _ => ?_⟩
    change ((uniformOfFintype (Fin ((1 : Polynomial ℕ).eval n.val) → Bool)).map List.ofFn).map _ = _
    rw [Polynomial.eval_one, uniform_letter]
    rfl
  · refine ⟨1, gate Bool.and, gate_poly _, fun n pp pk sk _ => ?_⟩
    obtain ⟨hne, hs⟩ := keyed_uniform (index n pp pk)
    refine ⟨hne, ?_⟩
    change ((uniformOfFintype (Fin ((1 : Polynomial ℕ).eval n.val) → Bool)).map List.ofFn).map _ = _
    rw [Polynomial.eval_one]
    exact hs

example (n : ℕ+) : keyedLetters.IsBoundedCoinPermutationScheme ∧
    keyedLetters.Generated n [] [false] [false] ∧ keyedLetters.Generated n [] [true] [true] ∧
    (keyedLetters.domain (index n [] [false])).card = 1 ∧
    (keyedLetters.domain (index n [] [true])).card = 2 ∧
    keyedLetters.eval (index n [] [false], [false]) = [false] ∧
    keyedLetters.eval (index n [] [true], [false]) = [true] := by
  exact ⟨keyed_permutation, (matching ..).2 (by simp), (matching ..).2 (by simp),
    by change (fibre [false]).card = 1; decide, by change (fibre [true]).card = 2; decide, rfl, rfl⟩

-- Conditional laws of the *same* honest one-coin sampler at the two supported public keys.
example (n : ℕ+) :
    let draw := fun pk => ((uniformOfFintype (Fin 1 → Bool)).map List.ofFn).map
      (fun r => gate Bool.and (index n [] pk, r))
    draw [false] [true] = 0 ∧ draw [true] [true] = (2 : ℝ≥0∞)⁻¹ := by
  dsimp only
  obtain ⟨_, hf⟩ := keyed_uniform (index n [] [false])
  obtain ⟨_, ht⟩ := keyed_uniform (index n [] [true])
  rw [hf, ht]
  simp [fibre, letters, Cslib.Probability.PMF.uniformOfFinset_apply]

end Cslib.Crypto.PublicKey.Trapdoor.Tests
