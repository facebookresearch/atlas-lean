/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module
public import MathlibExt.CategoryTheory.Preadditive.KilledBy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Actual cycles and homology inherit torsion from the corresponding term -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v a
open CategoryTheory CategoryTheory.Preadditive
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type a} {c : ComplexShape ι}

/-- The entire actual complex is killed by `m` if every actual term is killed by `m`. -/
theorem isKilledBy_of_terms (K : HomologicalComplex C c) (m : ℕ)
    (hK : ∀ i, IsKilledBy (K.X i) m) : IsKilledBy K m := by
  change m • (𝟙 K : K ⟶ K) = 0
  ext i
  exact hK i

/-- The actual cycle object is a subobject of the corresponding actual term. -/
theorem cycles_isKilledBy (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    {m : ℕ} (hK : IsKilledBy (K.X i) m) : IsKilledBy (K.cycles i) m :=
  hK.of_mono (K.iCycles i)

/-- The actual homology object is a quotient of the actual cycle object. -/
theorem homology_isKilledBy (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    {m : ℕ} (hK : IsKilledBy (K.X i) m) : IsKilledBy (K.homology i) m :=
  (K.cycles_isKilledBy i hK).of_epi (K.homologyπ i)

end HomologicalComplex
