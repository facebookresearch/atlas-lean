/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Crypto.PublicKey.Trapdoor

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

end Cslib.Crypto.PublicKey.Trapdoor.Tests
