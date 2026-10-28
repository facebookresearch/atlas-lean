/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Geometric coordinate-frame preservation implies a signed permutation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomialRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem frame_pairing (i j : Fin 24) (a b : ℝ) :
    stdPairingFun (a • (Pi.single i 1 : Fin 24 → ℝ))
      (b • (Pi.single j 1 : Fin 24 → ℝ)) = if i = j then a * b else 0 := by
  by_cases h : i = j
  · subst j
    simp [stdPairingFun, Pi.single_apply, ite_mul, mul_ite]
  · simp [stdPairingFun, Pi.single_apply, h, Ne.symm h, ite_mul, mul_ite]

/-- An actual isometry that permutes the signed coordinate axes is geometrically monomial. -/
theorem leechFrame_signed_permutation (e : leechIsomSubgroup)
    (h : ∀ i : Fin 24, ∃ j : Fin 24, ∃ b : ZMod 2,
      e.val (Pi.single i 1) = qSign b • (Pi.single j 1 : Fin 24 → ℝ)) :
    ∃ p : Equiv.Perm (Fin 24), ∃ d : Fin 24 → ZMod 2,
      e.val = golayRealSign d * golayRealPermute p := by
  classical
  choose p b hp using h
  have hpi : Function.Injective p := by
    intro i j hij
    by_contra hne
    have hh := e.property.1 (Pi.single i 1) (Pi.single j 1)
    rw [hp i, hp j, frame_pairing] at hh
    have hunit (i : Fin 24) : (Pi.single i 1 : Fin 24 → ℝ) =
        (1 : ℝ) • Pi.single i 1 := by simp
    rw [hunit i, hunit j, frame_pairing] at hh
    have h0 : (if i = j then (1 : ℝ) * 1 else 0) = 0 := by simp [hne]
    rw [h0] at hh
    have hz : qSign (b i) * qSign (b j) = 0 := by
      simpa only [hij, ite_true] using hh
    have hi : qSign (b i) ≠ 0 := by
      intro hz
      have hs := qSign_sq (b i)
      rw [hz, zero_mul] at hs
      norm_num at hs
    have hj : qSign (b j) ≠ 0 := by
      intro hz
      have hs := qSign_sq (b j)
      rw [hz, zero_mul] at hs
      norm_num at hs
    exact (mul_ne_zero hi hj) hz
  let p' : Equiv.Perm (Fin 24) := Equiv.ofBijective p
    ⟨hpi, Finite.surjective_of_injective hpi⟩
  let d : Fin 24 → ZMod 2 := fun j => b (p'.symm j)
  refine ⟨p', d, ?_⟩
  apply LinearEquiv.ext
  intro x
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin 24 → ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, hp i]
  congr 1
  ext j
  change qSign (b i) * (Pi.single (p i) 1 : Fin 24 → ℝ) j =
    qSign (d j) * (Pi.single i 1 : Fin 24 → ℝ) (p'.symm j)
  have hi : p'.symm j = i ↔ j = p i := by
    constructor
    · intro he
      have hh := congrArg p' he
      rw [Equiv.apply_symm_apply] at hh
      change j = p i at hh
      exact hh
    · intro he
      rw [he]
      exact p'.symm_apply_apply i
  by_cases hj : j = p i
  · subst j
    have hs : p'.symm (p i) = i := p'.symm_apply_apply i
    simp [hs, d]
  · have hn := mt hi.mp hj
    simp [hj, hn]

/-- The actual coordinate-frame stabilizer is contained in the counted monomial subgroup. -/
theorem leechFrame_mem_monomial (e : leechIsomSubgroup)
    (h : ∀ i : Fin 24, ∃ j : Fin 24, ∃ b : ZMod 2,
      e.val (Pi.single i 1) = qSign b • (Pi.single j 1 : Fin 24 → ℝ)) :
    e ∈ golayMonomialSubgroup := by
  obtain ⟨p, d, he⟩ := leechFrame_signed_permutation e h
  exact leechMonomial_mem e p d he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
