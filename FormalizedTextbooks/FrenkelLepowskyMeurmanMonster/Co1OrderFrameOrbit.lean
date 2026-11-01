/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Counting the genuine monomial orbit of a coordinate-frame vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderNormEightOrbit

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The forty-eight signed coordinate-frame vectors, represented by their actual coordinates. -/
def leechSignedFrame (t : Fin 24 × ZMod 2) : LeechNormEight := by
  refine ⟨⟨if t.2 = 0 then leechCoordinateFrameVector t.1 else
    -leechCoordinateFrameVector t.1, ?_⟩, ?_⟩
  · split_ifs
    · exact leechCoordinateFrameVector_mem t.1
    · exact leechIntegral.neg_mem (leechCoordinateFrameVector_mem t.1)
  · split_ifs
    · exact leechCoordinateFrameVector_square t.1
    · simpa only [leechSquareSum, Pi.neg_apply, neg_sq] using
        leechCoordinateFrameVector_square t.1

private theorem monomial_frame_action (d : golayCode) (p : golayAutomorphismSubgroup) :
    (golaySignIsometry d * golayPermutationIsometry p) • leechNormEightAxis =
      leechSignedFrame (p.val 0, d.val (p.val 0)) := by
  apply Subtype.ext
  apply Subtype.ext
  change (leechIntegralAction (golaySignIsometry d * golayPermutationIsometry p)
    (leechCoordinateFrameLattice 0)).val = _
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  funext i
  have hp : p.val.symm i = 0 ↔ i = p.val 0 := by
    constructor
    · intro h
      have hh := congrArg p.val h
      rw [p.val.apply_symm_apply] at hh
      exact hh
    · intro h
      rw [h, p.val.symm_apply_apply]
  by_cases hi : i = p.val 0
  · subst i
    simp [golayIntegerSign, golayIntegerPermute, leechCoordinateFrameLattice,
      leechCoordinateFrameVector, leechSignedFrame, ite_apply]
  · have hn := mt hp.mp hi
    simp [golayIntegerSign, golayIntegerPermute, leechCoordinateFrameLattice,
      leechCoordinateFrameVector, leechSignedFrame, ite_apply, hi, hn]

private theorem golayPermutation_zero_transitive (i : Fin 24) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = i := by
  let a : Fin 4 → Fin 24 := fun j => Fin.castAdd 20 j
  let b : Fin 4 → Fin 24 := fun j => Equiv.swap (0 : Fin 24) i (a j)
  have ha : Function.Injective a := by
    intro j k h
    exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h)
  have hb : Function.Injective b := (Equiv.swap (0 : Fin 24) i).injective.comp ha
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive a b ha hb
  refine ⟨p, ?_⟩
  simpa [a, b] using hp 0

/-- Every signed coordinate-frame vector occurs in the actual monomial orbit. -/
theorem leechSignedFrame_mem_monomial_orbit (t : Fin 24 × ZMod 2) :
    leechSignedFrame t ∈ MulAction.orbit golayMonomialSubgroup leechNormEightAxis := by
  obtain ⟨p, hp⟩ := golayPermutation_zero_transitive t.1
  let f : Fin 4 → Fin 24 := fun j => Equiv.swap (0 : Fin 24) t.1 (Fin.castAdd 20 j)
  have hf : Function.Injective f := by
    intro j k h
    have hh := (Equiv.swap (0 : Fin 24) t.1).injective h
    exact Fin.ext (congrArg (fun x : Fin 24 => x.val) hh)
  obtain ⟨d, hd⟩ := golayCode_four_coordinate_surjective f hf (fun _ => t.2)
  have hdi : d.val t.1 = t.2 := by
    have hh := congrFun hd 0
    simpa [f] using hh
  let e : golayMonomialSubgroup :=
    ⟨golaySignIsometry d * golayPermutationIsometry p, ⟨d, p, rfl⟩⟩
  refine ⟨e, ?_⟩
  change e.val • leechNormEightAxis = leechSignedFrame t
  rw [monomial_frame_action, hp, hdi]

/-- The actual monomial orbit consists exactly of the signed coordinate-frame vectors. -/
theorem leech_monomial_orbit_eq_signedFrame :
    MulAction.orbit golayMonomialSubgroup leechNormEightAxis = Set.range leechSignedFrame := by
  ext u
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, p, he⟩ := e.property
    refine ⟨(p.val 0, d.val (p.val 0)), ?_⟩
    change leechSignedFrame _ = e.val • leechNormEightAxis
    rw [he, monomial_frame_action]
  · rintro ⟨t, rfl⟩
    exact leechSignedFrame_mem_monomial_orbit t

/-- Distinct coordinate/sign labels give distinct actual frame vectors. -/
theorem leechSignedFrame_injective : Function.Injective leechSignedFrame := by
  rintro ⟨i, b⟩ ⟨j, d⟩ h
  have hv := congrArg (fun u : LeechNormEight => u.val.val) h
  have hij : i = j := by
    by_contra hij
    have hi := congrFun hv i
    by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
      norm_num [leechSignedFrame, leechCoordinateFrameVector, hb, hd, hij,
        ite_apply] at hi
  subst j
  have hi := congrFun hv i
  have ht : ∀ b d : ZMod 2, (if b = 0 then 8 else -8 : ℤ) =
      (if d = 0 then 8 else -8 : ℤ) → b = d := by decide
  have hbd : b = d := ht b d (by
    simpa [leechSignedFrame, leechCoordinateFrameVector, ite_apply] using hi)
  subst d
  rfl

/-- The genuine monomial orbit has exactly forty-eight elements. -/
theorem leech_monomial_frame_orbit_card :
    Nat.card (MulAction.orbit golayMonomialSubgroup leechNormEightAxis) = 48 := by
  rw [leech_monomial_orbit_eq_signedFrame]
  rw [← Nat.card_congr (Equiv.ofInjective leechSignedFrame leechSignedFrame_injective)]
  norm_num [Nat.card_prod]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
