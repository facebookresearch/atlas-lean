/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightFrameFiber

/-! Every nonempty lattice-class fiber in the actual E8 section has sixteen vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual reduction fiber in the specified coordinate section. -/
def GeneratedOctadNormEightReductionFiber (c : Fin 24 → ZMod 2) (b : LeechModTwo) :=
  {x : GeneratedOctadNormEight c // leechReduction x.val = b}

/-- A genuine section-preserving isometry acts bijectively on its norm-eight vectors. -/
def generatedStandardOctadNormEightEquiv (e : leechIsomSubgroup)
    (he : generatedStandardOctadPreserves e) :
    GeneratedOctadNormEight golayStandardOctad ≃
      GeneratedOctadNormEight golayStandardOctad where
  toFun x := ⟨leechIntegralAction e x.val, by
    rw [generatedOctadSupported_standard]
    exact (he x.val).mpr ((generatedOctadSupported_standard _).mp x.property.1),
    by rw [leechIntegralAction_squareSum]; exact x.property.2⟩
  invFun x := ⟨leechIntegralAction e⁻¹ x.val, by
    rw [generatedOctadSupported_standard]
    exact (generatedStandardOctadPreserves_inv e he x.val).mpr
      ((generatedOctadSupported_standard _).mp x.property.1),
    by rw [leechIntegralAction_squareSum]; exact x.property.2⟩
  left_inv x := by
    apply Subtype.ext
    change leechIntegralAction e⁻¹ (leechIntegralAction e x.val) = x.val
    rw [map_inv]
    exact (leechIntegralAction e).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    change leechIntegralAction e (leechIntegralAction e⁻¹ x.val) = x.val
    rw [map_inv]
    exact (leechIntegralAction e).apply_symm_apply x.val

/-- Internal transitivity transports any actual nonempty reduction fiber
to the distinguished coordinate-frame fiber. -/
def generatedStandardOctadReductionFiberEquiv
    (u : GeneratedOctadNormEight golayStandardOctad) :
    GeneratedOctadNormEightReductionFiber golayStandardOctad (leechReduction u.val) ≃
      GeneratedOctadNormEightFrameFiber golayStandardOctad := by
  let h := generatedStandardOctad_normEight_transitive u.val u.property.2
    ((generatedOctadSupported_standard _).mp u.property.1)
  let e := Classical.choose h
  have he := (Classical.choose_spec h).2.1
  have haxis := (Classical.choose_spec h).2.2
  have heaxis : leechIntegralAction e u.val = leechCoordinateFrameLattice 0 :=
    Subtype.ext haxis
  let E := generatedStandardOctadNormEightEquiv e he
  let A := leechQuotientAut (leechIntegralAction e)
  have ha (x : GeneratedOctadNormEight golayStandardOctad) :
      leechReduction (E x).val = A (leechReduction x.val) := rfl
  have hau : A (leechReduction u.val) = leechReduction (leechCoordinateFrameLattice 0) := by
    rw [leechQuotientAut_reduce, heaxis]
  have hiff (x : GeneratedOctadNormEight golayStandardOctad) :
      leechReduction (E x).val = leechReduction (leechCoordinateFrameLattice 0) ↔
        leechReduction x.val = leechReduction u.val := by
    rw [ha, ← hau]
    exact A.injective.eq_iff
  exact {
    toFun := fun x => ⟨E x.val, (hiff x.val).mpr x.property⟩
    invFun := fun y => ⟨E.symm y.val, (hiff (E.symm y.val)).mp (by
      rw [E.apply_symm_apply]
      exact y.property)⟩
    left_inv := fun x => Subtype.ext (E.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (E.apply_symm_apply y.val)
  }

/-- Each actual nonempty lattice-class fiber inside the E8 section has sixteen vectors. -/
theorem generatedStandardOctad_reductionFiber_card
    (u : GeneratedOctadNormEight golayStandardOctad) :
    Nat.card (GeneratedOctadNormEightReductionFiber golayStandardOctad
      (leechReduction u.val)) = 16 := by
  rw [Nat.card_congr (generatedStandardOctadReductionFiberEquiv u)]
  exact generatedStandardOctad_frameFiber_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
