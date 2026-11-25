/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoInverse
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteStageKernelClosure
public import MathlibExt.KTheory.Ring.K2.MilnorComparisonNaturality

/-!
# Matsumoto's theorem for fields

For a field `F`, `milnorComparison F` and `matsumotoReverse F` are mutually
inverse. They give the additive equivalence `matsumotoAddEquiv_unconditional F`
between `MilnorK F 2` and `Additive (K2 F)`.

The comparison commutes with field homomorphisms whose source and target
lie in the same universe.

## Main results

* `milnorComparison_comp_matsumotoReverse_eq_id_unconditional`: the
  algebraic K₂ inverse identity.
* `matsumotoAddEquiv_unconditional`: Matsumoto's additive equivalence.
* `matsumotoAddEquiv_mapRingHom`: naturality of its forward map.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter III, Theorem 6.1 (Matsumoto's theorem), PDF page 239 / printed
  page 231, https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.pdf.
-/

@[expose] public section

namespace AlgebraicKTheory.K2

open scoped IsMulCommutative

universe u

/-- The composite `milnorComparison F ∘ matsumotoReverse F` is the identity
on `Additive (K2 F)`. -/
theorem milnorComparison_comp_matsumotoReverse_eq_id_unconditional
    (F : Type u) [Field F] :
    (milnorComparison F).toAddMonoidHom.comp (matsumotoReverse F) =
      AddMonoidHom.id (Additive (K2 F)) :=
  milnorComparison_comp_matsumotoReverse_eq_id (F := F)
    StableSteinberg.ker_toStableE_eq_torusCocycleSubgroup
    (MatsumotoStableExtensionDiagram.matsumotoReverse_steinbergSymbol (F := F))

/-- Matsumoto's additive equivalence `MilnorK F 2 ≃+ Additive (K2 F)`. -/
noncomputable def matsumotoAddEquiv_unconditional (F : Type u) [Field F] :
    MilnorK F 2 ≃+ Additive (K2 F) :=
  matsumotoAddEquiv (F := F)
    (MatsumotoStableExtensionDiagram.matsumotoReverse_steinbergSymbol (F := F))
    StableSteinberg.ker_toStableE_eq_torusCocycleSubgroup

/-- The Matsumoto comparison commutes with a field homomorphism between
fields in the same universe. -/
theorem matsumotoAddEquiv_mapRingHom
    {F K : Type u} [Field F] [Field K] (f : F →+* K) :
    (K2.mapRingHom f).toAdditive.comp
        (matsumotoAddEquiv_unconditional F).toAddMonoidHom =
      (matsumotoAddEquiv_unconditional K).toAddMonoidHom.comp
        (MilnorK.mapAddHom f 2) := by
  apply AddMonoidHom.ext
  intro x
  have hF : ∀ y, (matsumotoAddEquiv_unconditional (F := F)).toAddMonoidHom y =
      milnorComparison F y := fun y => rfl
  have hK : ∀ y, (matsumotoAddEquiv_unconditional (F := K)).toAddMonoidHom y =
      milnorComparison K y := fun y => rfl
  simp only [AddMonoidHom.comp_apply, hF, hK, MilnorK.mapAddHom_apply]
  exact mapRingHom_milnorComparison f x

end AlgebraicKTheory.K2

end
