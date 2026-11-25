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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Coordinates

/-!
# Orthogonality of native tensor degree components

The existing native sum-tensor descriptor projects onto a selected degree
pair. Its composite with an inclusion from a different pair is zero.
The same statement holds after the original equality transport between
the two displayed sum degrees. Both module worlds are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category HomologicalComplex
open scoped TensorProduct

universe u v w

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]
  (P : CochainComplex (ModuleCat.{v} R) ℤ) (Q : CochainComplex (ModuleCat.{w} R) ℤ)

/-- Equality transport on the actual native sum degree carries its original inclusion to the same pair. -/
theorem nativeComponentInclusion_cast (i j m n : ℤ) (hm : i + j = m) (h : m = n) :
    HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        i j m hm ≫ ((complexAt R P Q).XIsoOfEq h).hom =
      HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        i j n (hm.trans h) := by
  subst n
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  let J : ModuleCat.tensorObjAt R (P.X i) (Q.X j) ⟶ (complexAt R P Q).X m :=
    HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ) i j m hm
  change J ≫ 𝟙 ((complexAt R P Q).X m) = J
  exact Category.comp_id J

/-- The original projection also kills a different pair transported from its original sum degree. -/
theorem componentInclusionAt_other_projectionAt (p q i j : ℤ)
    (h : i + j = p + q) (hne : i ≠ p ∨ j ≠ q) :
    (componentInclusionAt R P Q i j ≫ ((complexAt R P Q).XIsoOfEq h).hom) ≫
        tensorCellProjection R P Q p q (p + q) = 0 := by
  have hcast : componentInclusionAt R P Q i j ≫ ((complexAt R P Q).XIsoOfEq h).hom =
      HomologicalComplex.ιMapBifunctor P Q (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        i j (p + q) h :=
    nativeComponentInclusion_cast R P Q i j (i + j) (p + q) rfl h
  exact (congrArg (fun f => f ≫ tensorCellProjection R P Q p q (p + q)) hcast).trans
    (tensorCellProjection_ι_eq_zero R P Q p q (p + q) i j h hne)

end CochainComplex.ModuleTensor
