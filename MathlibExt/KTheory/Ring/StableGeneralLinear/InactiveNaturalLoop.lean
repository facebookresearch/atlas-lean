/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.InactivePermutationFactor
public import MathlibExt.CategoryTheory.NerveProductLoop
public import MathlibExt.CategoryTheory.NerveIhomComposition

/-!
# Whole natural loops of the computed inactive BGL factor

The original active restriction has already been identified with the
original finite-to-stable classifying functor. The original inactive
factor gives a whole natural loop of that restriction. Its complete
simplicial cylinder is the actual paired active simplex and normalized
inactive edge, followed by the original commuting-family functor.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R] {n N : ℕ}

/-- The actual restriction of the whole computed active/inactive functor
at its ORIGINAL inactive object; it equals the original finite inclusion. -/
public abbrev initialInactiveActiveFunctor (h : n ≤ N) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤ ClassifyingCategory R :=
  Prod.sectL (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
      (SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ) ⋙
    initialInactiveClassifyingFamilyFunctor R h

/-- The whole normalized inactive natural loop of the original active
restriction, before realization or any based retuning. -/
public abbrev initialInactiveClassifyingLoop (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    initialInactiveActiveFunctor R h ⟶ initialInactiveActiveFunctor R h :=
  Functor.whiskerRight
    (CategoryTheory.productConstantLoop
      (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
      (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)
      (SingleObj.star _) (MulOpposite.op g⁻¹))
    (initialInactiveClassifyingFamilyFunctor R h)

/-- The original normalized inactive stable matrix is the component at
EVERY original active object, with the opposite/inverse order retained. -/
public theorem initialInactiveClassifyingLoop_app (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N))
    (c : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (initialInactiveClassifyingLoop R h g).app c =
      MulOpposite.op (inactiveStableMatrixHom R N (initialActiveIndices n N) g.val)⁻¹ := by
  rw [Functor.whiskerRight_app, CategoryTheory.productConstantLoop_app,
    initialInactiveClassifyingFamilyFunctor_map]
  change MulOpposite.op (StableGL.of (1 : Matrix.GeneralLinearGroup (Fin n) R) *
    inactiveStableMatrixHom R N (initialActiveIndices n N) (g.val)⁻¹) = _
  rw [StableGL.of_one, one_mul, map_inv]

/-- The ENTIRE simplicial natural loop is the original whole product
family restricted along the SAME normalized inactive edge. No vertex-only
or fundamental-group-only equation is substituted. -/
public theorem initialInactiveClassifyingLoop_nerveHomotopyMap (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    NatTrans.nerveHomotopyMap (initialInactiveClassifyingLoop R h g) =
      Limits.prod.lift
        (CartesianMonoidalCategory.fst
          (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
          (Δ[1] : SSet.{u}))
        (CartesianMonoidalCategory.snd
          (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
          (Δ[1] : SSet.{u}) ≫
            SSet.yonedaEquiv.symm
              (nerve.edgeMk
                (x := SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)
                (y := SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)
                (MulOpposite.op g⁻¹)).edge) ≫
        (nerveProdIso
          (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
          (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)).inv ≫
          nerveMap (initialInactiveClassifyingFamilyFunctor R h) :=
  CategoryTheory.nerveHomotopyMap_productConstantLoop_postcomp
    (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)
    (SingleObj.star _) (MulOpposite.op g⁻¹) (initialInactiveClassifyingFamilyFunctor R h)

/-- Transporting the computed active restriction to its PROVED original
finite-inclusion equality retains the literal original functor. -/
public def finiteInactiveClassifyingLoop (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    (finiteToStableCategoryMap R n).toFunctor ⟶ (finiteToStableCategoryMap R n).toFunctor :=
  eqToHom (initialInactiveClassifyingFamily_activeFunctor R h).symm ≫
    initialInactiveClassifyingLoop R h g ≫
      eqToHom (initialInactiveClassifyingFamily_activeFunctor R h)

/-- The exact equality transports in the original one-object category
leave EVERY original normalized inactive component unchanged. -/
public theorem finiteInactiveClassifyingLoop_app (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N))
    (c : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteInactiveClassifyingLoop R h g).app c =
      MulOpposite.op (inactiveStableMatrixHom R N (initialActiveIndices n N) g.val)⁻¹ := by
  have htransport
      {F F' : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤ ClassifyingCategory R}
      (e : F = F') (α : F ⟶ F) :
      (eqToHom e.symm ≫ α ≫ eqToHom e).app c = α.app c := by
    cases e
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (eqToHom (initialInactiveClassifyingFamily_activeFunctor R h).symm ≫
      initialInactiveClassifyingLoop R h g ≫
        eqToHom (initialInactiveClassifyingFamily_activeFunctor R h)).app c = _
  exact (htransport (initialInactiveClassifyingFamily_activeFunctor R h)
    (initialInactiveClassifyingLoop R h g)).trans
      (initialInactiveClassifyingLoop_app R h g c)

/-- The ACTUAL original finite-inclusion natural loop has the complete
same original paired-simplex cylinder after the computed functor transport. -/
public theorem finiteInactiveClassifyingLoop_nerveHomotopyMap (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    NatTrans.nerveHomotopyMap (finiteInactiveClassifyingLoop R h g) =
      NatTrans.nerveHomotopyMap (initialInactiveClassifyingLoop R h g) :=
  NatTrans.nerveHomotopyMap_eqToHomEndpoints (initialInactiveClassifyingFamily_activeFunctor R h)
    (initialInactiveClassifyingFamily_activeFunctor R h)
    (initialInactiveClassifyingLoop R h g)

end AlgebraicKTheory.StableGL

end
