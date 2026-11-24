/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.Algebra.Homology.SpectralObject.MonoidAction

/-!
# Ordinary clients of the interval forget comparison

Apply the canonical forget-map characteristic at arbitrary intervals and derive
its monoid-algebra generator formula from the existing spectral action law.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComposableArrows

universe v u w t

namespace CategoryTheory.Abelian.SpectralObject.IntervalForgetCharacteristicTests

variable {ι : Type t} [Category.{v} ι] {M : Type w} [Monoid M]
  (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E)

/-- The ordinary public characteristic retains every interval and universe. -/
theorem hom_apply (n : ℤ) (I : ComposableArrows ι 1)
    (x : E.monoidModuleInterval ρ n I) :
    (E.monoidModuleIntervalForgetIso ρ n I).hom x =
      (E.intervalRepresentation ρ n I).asModuleEquiv x :=
  E.monoidModuleIntervalForgetIso_hom_apply ρ n I x

/-- A generator's forgotten value is the original spectral endomorphism. -/
theorem generator_apply (n : ℤ) (I : ComposableArrows ι 1)
    (a : M) (x : E.monoidModuleInterval ρ n I) :
    (E.monoidModuleIntervalForgetIso ρ n I).hom
        (MonoidAlgebra.single a (1 : ℤ) • x) = ((ρ a).asHom.hom n).app I x := by
  rw [E.monoidModuleIntervalForgetIso_hom_apply ρ]
  exact E.monoidModuleInterval_generator_apply ρ n I a x

end CategoryTheory.Abelian.SpectralObject.IntervalForgetCharacteristicTests

end
