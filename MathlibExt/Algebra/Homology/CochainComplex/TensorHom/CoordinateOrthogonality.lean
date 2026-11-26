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
# Tensor-cell orthogonality after a total-degree transport

Let R be a commutative ring and P,Q integer cochain complexes in independent module universes.
Transport along an equality of displayed total degrees sends a cell inclusion to the inclusion
of the same factor degrees.

An inclusion from a different factor pair, transported to the same sum degree, is still killed
by the projection onto the selected pair.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category HomologicalComplex
open scoped TensorProduct

universe u v w

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]
  (P : CochainComplex (ModuleCat.{v} R) ℤ) (Q : CochainComplex (ModuleCat.{w} R) ℤ)

/-- Let R be a commutative ring, P,Q integer R-module cochain complexes in independent carrier
universes, and i+j=m with m=n. The inclusion P^i⊗Q^j → (P⊗Q)^m followed by the term
isomorphism for m=n equals the canonical inclusion into (P⊗Q)^n. The factor indices remain
i,j. -/
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

/-- For integer R-module cochain complexes P,Q over a commutative ring R, suppose i+j=p+q and i≠p
or j≠q. Include the cell (i,j) into total degree i+j, transport to degree p+q, and project
onto (p,q). This composite is zero. The two module carrier universes may be independent. -/
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
