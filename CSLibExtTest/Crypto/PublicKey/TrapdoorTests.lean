/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Crypto.PublicKey.Trapdoor
import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit

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
    (he : S.domain (index n pp pk) = ∅) : ¬ S.IsFunctionScheme := by
  intro h
  simpa [he] using h.domain_nonempty n pp pk sk hg

-- Even a nonempty three-element domain is incompatible with exact sampling from a fixed
-- number of fair bits, independently of which polynomial coin budget is proposed.
example (S : Family) (n : ℕ+) (pp pk sk : Bits) (hg : S.Generated n pp pk sk)
    (hc : (S.domain (index n pp pk)).card = 3) : ¬ S.IsFunctionScheme := by
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

-- Inspect two input symbols. The result bit is true just when the first is present and the
-- second absent. Host.isPolyTime_decider supplies the time for input and output handling.
private def sizeTest : Host.Comp where
  K := Bool
  Γ := fun _ => Bool
  L := Bool
  prog l := if l then .halt else
    .pop false (fun _ a => a.isSome) (.peek false (fun v a => v && a.isNone)
      (.push true id (.goto fun _ => true)))
  ks := [false, true]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

private theorem singleton_poly : IsPolyTime (fun x : Bits => decide (x.length = 1)) := by
  apply Host.isPolyTime_decider (c := sizeTest) (cX := false) (cO := true) (gX := id)
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
example : binaryFamily.IsBoundedCoinPermutationScheme := by
  constructor
  · constructor
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
    · let mem := fun t : (Bits × Bits × Bits) × Bits => decide (t.2.length = 1)
      have hm : IsPolyTime mem := snd_poly.comp singleton_poly
      exact ⟨mem, mem, hm, hm, fun _ _ _ _ _ z => by simp [mem, binaryFamily, length_one_iff]⟩
    · exact snd_poly
    · exact snd_poly
    · refine ⟨1, fun n pp pk sk hg => ?_⟩
      simp [Family.Generated, binaryFamily] at hg
      obtain ⟨rfl, rfl, rfl⟩ := hg
      simp [binaryFamily, letters]
    · intro n pp pk sk _
      exact ⟨fun _ h => h, fun _ h => h, fun _ _ => rfl⟩
  · exact fun _ _ _ _ _ => rfl

end Cslib.Crypto.PublicKey.Trapdoor.Tests
