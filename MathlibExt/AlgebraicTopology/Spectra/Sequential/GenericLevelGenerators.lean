/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Functor
public import MathlibExt.AlgebraicTopology.ModelCategory.TensorPowerGeneratorMaps

/-!
# Original sequential tensor-power generator classes

The genuine index has the original tensor-power Hom object forwards and
the actual initial object backwards. The empty power uses unitors, and
every positive coefficient uses cofibrancy of T. Cof(unit) is unnecessary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace HomotopicalAlgebra.GenericSequentialLevel

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V] [HasInitial V]

/-- The entire coefficient arrow into the selected initial tensor coefficient is an isomorphism. -/
theorem initialCoefficient_isIso {X Y : V} (f : X ⟶ Y) : IsIso (f ▷ (⊥_ V)) :=
  isIso_of_isInitial (MonoidalCategory.tensorInitialLeft X) (MonoidalCategory.tensorInitialLeft Y) _

variable [ModelCategory V] [SymmetricCategory V] [IsClosedSymmetricMonoidalModelCategory V]

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- Every full original sequential coefficient preserves base cofibrations at every pair of degrees. -/
theorem indexHom_cofibration (T : V) [IsCofibrant T]
    (a b : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T)
    {X Y : V} (f : X ⟶ Y) (hf : cofibrations V f) :
    cofibrations V (f ▷ (a ⟶[V] b)) := by
  by_cases h : a.degree ≤ b.degree
  · change cofibrations V (f ▷ CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom T a b)
    rw [CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le T a b h]
    exact TensorPowerGeneratorMaps.right_cofibration T _ f hf
  · change cofibrations V (f ▷ CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom T a b)
    rw [CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_gt T a b (Nat.lt_of_not_ge h)]
    let _ : IsIso (f ▷ (⊥_ V)) := initialCoefficient_isIso f
    exact (cofibration_iff _).mp inferInstance

/-- Every full original sequential coefficient preserves base trivial cofibrations at every pair of degrees. -/
theorem indexHom_trivialCofibration (T : V) [IsCofibrant T]
    (a b : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T)
    {X Y : V} (f : X ⟶ Y) (hf : trivialCofibrations V f) :
    trivialCofibrations V (f ▷ (a ⟶[V] b)) := by
  by_cases h : a.degree ≤ b.degree
  · change trivialCofibrations V (f ▷ CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom T a b)
    rw [CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le T a b h]
    exact TensorPowerGeneratorMaps.right_trivialCofibration T _ f hf
  · change trivialCofibrations V (f ▷ CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom T a b)
    rw [CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_gt T a b (Nat.lt_of_not_ge h)]
    let _ : IsIso (f ▷ (⊥_ V)) := initialCoefficient_isIso f
    exact ⟨(cofibration_iff _).mp inferInstance, (weakEquivalence_iff _).mp inferInstance⟩

/-- The actual original free/evaluation map retains its full coefficient and is a base cofibration. -/
theorem evaluatedFree_cofibration (T : V) [IsCofibrant T] (n m : ℕ)
    {X Y : V} (f : X ⟶ Y) (hf : cofibrations V f) :
    cofibrations V ((CategoryTheory.Spectra.Sequential.evaluation T m).map
      ((CategoryTheory.Spectra.Sequential.freeAt T n).map f)) := by
  change cofibrations V (CategoryTheory.Spectra.Sequential.levelMap
    ((CategoryTheory.Spectra.Sequential.freeAt T n).map f) m)
  rw [CategoryTheory.Spectra.Sequential.freeAt_map_levelMap]
  exact indexHom_cofibration T _ _ f hf

/-- The actual original free/evaluation map retains its full coefficient and is a base trivial cofibration. -/
theorem evaluatedFree_trivialCofibration (T : V) [IsCofibrant T] (n m : ℕ)
    {X Y : V} (f : X ⟶ Y) (hf : trivialCofibrations V f) :
    trivialCofibrations V ((CategoryTheory.Spectra.Sequential.evaluation T m).map
      ((CategoryTheory.Spectra.Sequential.freeAt T n).map f)) := by
  change trivialCofibrations V (CategoryTheory.Spectra.Sequential.levelMap
    ((CategoryTheory.Spectra.Sequential.freeAt T n).map f) m)
  rw [CategoryTheory.Spectra.Sequential.freeAt_map_levelMap]
  exact indexHom_trivialCofibration T _ _ f hf

end HomotopicalAlgebra.GenericSequentialLevel
