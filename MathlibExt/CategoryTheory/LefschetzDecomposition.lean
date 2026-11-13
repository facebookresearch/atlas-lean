/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

@[expose] public section

/-!
# Cohomology objects and Lefschetz morphisms

For a triangulated category with a t-structure, `cohomologyFunctor t j`
first shifts by `j`, then takes the degree-zero slice. Its objects belong
to the heart of `t`.

`lefschetzPower` composes an actual degree-two morphism using Mathlib's
shift identifications. `lefschetzMorphism` applies the degree-zero slice
to that iterate shifted by `-i`, producing `H⁻ⁱ(K) ⟶ Hⁱ(K)`.
`HasHardLefschetz` states that these induced morphisms are isomorphisms.

## References

* P. Deligne, *Théorème de Lefschetz et critères de dégénérescence de suites
  spectrales*, Publ. Math. IHÉS 35 (1968), 107–126, Theorem 1.5.
  https://doi.org/10.1007/BF02698925
* M. A. A. de Cataldo and L. Migliorini, *Hodge-theoretic aspects of the
  Decomposition Theorem*, §2.2.
  https://www.math.stonybrook.edu/~mde/papers/20.pdf
-/

namespace MathlibExt.CategoryTheory.LefschetzDecomposition

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Triangulated

universe v u

noncomputable section

section Iterates

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] {K : C}

/-- The actual `i`th iterate of a degree-two morphism, with the canonical
shift identifications used in every composition. -/
def lefschetzPower (η : K ⟶ K⟦(2 : ℤ)⟧) :
    (i : ℕ) → K ⟶ K⟦2 * (i : ℤ)⟧
  | 0 => ShiftedHom.mk₀ _ (by simp) (𝟙 K)
  | i + 1 => ShiftedHom.comp (lefschetzPower η i) η (by omega)

end Iterates

section Cohomology

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (j : ℤ), (shiftFunctor C j).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The `j`th cohomology functor, viewed in the ambient triangulated
category: shift by `j`, then take the degree-zero t-structure slice. -/
def cohomologyFunctor (t : TStructure C) (j : ℤ) : C ⥤ C :=
  shiftFunctor C j ⋙ t.truncGELE 0 0

/-- The cohomology objects belong to the heart of the supplied t-structure. -/
theorem cohomologyFunctor_obj_mem_heart (t : TStructure C) (j : ℤ) (K : C) :
    t.heart ((cohomologyFunctor t j).obj K) := by
  rw [TStructure.mem_heart_iff]
  constructor <;> dsimp [cohomologyFunctor] <;> infer_instance

/-- The hard Lefschetz morphism `H⁻ⁱ(K) ⟶ Hⁱ(K)` induced by `ηⁱ`.
The inner map is `ηⁱ` shifted by `-i`, followed by the canonical
identification `K⟦2i⟧⟦-i⟧ ≅ K⟦i⟧`; taking its degree-zero slice gives
the displayed map. -/
def lefschetzMorphism (t : TStructure C) {K : C}
    (η : K ⟶ K⟦(2 : ℤ)⟧) (i : ℕ) :
    (cohomologyFunctor t (-(i : ℤ))).obj K ⟶
      (cohomologyFunctor t (i : ℤ)).obj K :=
  (t.truncGELE 0 0).map
    ((lefschetzPower η i)⟦-(i : ℤ)⟧' ≫
      (shiftFunctorAdd' C (2 * (i : ℤ)) (-(i : ℤ))
        (i : ℤ) (by omega)).inv.app K)

/-- Hard Lefschetz for the given morphism, centered in degree zero. -/
def HasHardLefschetz (t : TStructure C) {K : C}
    (η : K ⟶ K⟦(2 : ℤ)⟧) : Prop :=
  ∀ i : ℕ, IsIso (lefschetzMorphism t η i)

end Cohomology

end

end MathlibExt.CategoryTheory.LefschetzDecomposition
