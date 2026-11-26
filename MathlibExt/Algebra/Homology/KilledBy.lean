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

/-!
# Annihilation of complex objects and their homology

In a preadditive category, an object is killed by m when m times its identity morphism is
zero. If every term of a complex is killed by m, so is the complex object.

At a degree where homology exists, annihilation of the term passes to its cycles by the cycle
monomorphism and to its homology by the cycle-to-homology epimorphism. The complex shape and
category universes are arbitrary.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v a
open CategoryTheory CategoryTheory.Preadditive
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type a} {c : ComplexShape ι}

/-- Termwise annihilation kills the complex identity.

If every K_i is killed by the natural number m, then m times the identity of K is zero. -/
theorem isKilledBy_of_terms (K : HomologicalComplex C c) (m : ℕ)
    (hK : ∀ i, IsKilledBy (K.X i) m) : IsKilledBy K m := by
  change m • (𝟙 K : K ⟶ K) = 0
  ext i
  exact hK i

/-- Annihilation passes from a complex term to its cycles.

If K_i is killed by m and degree-i homology exists, then the cycle object Z_i(K) is killed by
m. -/
theorem cycles_isKilledBy (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    {m : ℕ} (hK : IsKilledBy (K.X i) m) : IsKilledBy (K.cycles i) m :=
  hK.of_mono (K.iCycles i)

/-- Annihilation passes from a complex term to its homology.

If K_i is killed by m and degree-i homology exists, then H_i(K) is killed by m. -/
theorem homology_isKilledBy (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    {m : ℕ} (hK : IsKilledBy (K.X i) m) : IsKilledBy (K.homology i) m :=
  (K.cycles_isKilledBy i hK).of_epi (K.homologyπ i)

end HomologicalComplex
