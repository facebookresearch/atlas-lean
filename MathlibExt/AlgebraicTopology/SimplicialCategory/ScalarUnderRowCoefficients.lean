/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderNerveProjection
import MathlibExt.CategoryTheory.Comma.UnderProjectionChains

/-!
# Full original scalar-under rows and their initial Hom coefficients

Fix only the nerve arity. Every scalar degree retains the complete
original base chain and its entire original initial Hom simplex.
Native whole-word reconstruction and recovery give both inverse maps,
with the original forgetful projection and all scalar operators retained.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- The SAME full base-nerve row at the supplied original nerve arity. -/
abbrev baseRow (n : ℕ) : SSet.{u} := simplicialRow (baseNerveDiagram C) (op ⦋n⦌)

/-- The SAME full original scalar-under row at the supplied nerve arity. -/
abbrev underRow (z : C) (n : ℕ) : SSet.{u} := simplicialRow (nerveDiagram C z) (op ⦋n⦌)

/-- The actual entire original row projection. -/
def rowProjection (z : C) (n : ℕ) : underRow C z n ⟶ baseRow C n :=
  (simplicialTransposeFunctor.map (nerveProjection C z)).app (op ⦋n⦌)

/-- The original whole row coefficient is its complete base word and
SAME entire initial Hom simplex in every scalar degree. -/
def rowCoefficients (z : C) (n : ℕ) : SSet.{u} where
  obj q := Σ w : (baseRow C n).obj q, (z ⟶[SSet.{u}] (w.obj 0).obj).obj q
  map {q r} f := ↾fun a => ⟨(baseRow C n).map f a.1,
    (z ⟶[SSet.{u}] (a.1.obj 0).obj).map f a.2⟩
  map_id q := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Sigma.ext
    · exact (baseRow C n).map_id_apply q a.1
    · exact heq_of_eq ((z ⟶[SSet.{u}] (a.1.obj 0).obj).map_id_apply q a.2)
  map_comp {q r t} f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Sigma.ext
    · exact (baseRow C n).map_comp_apply f g a.1
    · exact heq_of_eq ((z ⟶[SSet.{u}] (a.1.obj 0).obj).map_comp_apply f g a.2)

/-- Forget only the initial Hom coefficient, preserving the SAME full base word. -/
def rowCoefficientsProjection (z : C) (n : ℕ) : rowCoefficients C z n ⟶ baseRow C n where
  app _ := ↾_root_.Sigma.fst
  naturality _ _ _ := rfl

/-- Reconstruct the SAME complete original under-word by native initial-arrow extension. -/
def rowCoefficientsToUnder (z : C) (n : ℕ) : rowCoefficients C z n ⟶ underRow C z n where
  app q := ↾fun a => Under.chainFromInitialArrow a.1 (X := sourceObject C z q) a.2
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (Under.chainFromInitialArrow_post a.1 a.2 (scalarOperator (C := C) f)).symm

/-- Recover the SAME full original base word and its actual original first arrow. -/
def underToRowCoefficients (z : C) (n : ℕ) : underRow C z n ⟶ rowCoefficients C z n where
  app q := ↾fun U => ⟨U ⋙ forget C z q, (U.obj 0).hom⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro U
    apply Sigma.ext
    · rfl
    · rfl

/-- Both whole original operations recover every full original word and coefficient. -/
theorem rowCoefficientsToUnder_underTo (z : C) (n : ℕ) :
    rowCoefficientsToUnder C z n ≫ underToRowCoefficients C z n = 𝟙 (rowCoefficients C z n) := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  apply Sigma.ext
  · exact Under.chainFromInitialArrow_forget a.1 a.2
  · exact heq_of_eq (Under.chainFromInitialArrow_zero a.1 a.2)

/-- Both whole original operations recover the SAME complete native under-word. -/
theorem underToRowCoefficients_toUnder (z : C) (n : ℕ) :
    underToRowCoefficients C z n ≫ rowCoefficientsToUnder C z n = 𝟙 (underRow C z n) := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro U
  have h := Under.projectionChain U (U ⋙ forget C z q) rfl
  change U = Under.chainFromInitialArrow (U ⋙ forget C z q)
    ((U.obj 0).hom ≫ eqToHom rfl) at h
  rw [eqToHom_refl, Category.comp_id] at h
  exact h.symm

/-- The SAME complete original scalar-under row is genuinely isomorphic
to its original whole base words paired with their full initial Homs. -/
def rowCoefficientsIso (z : C) (n : ℕ) : rowCoefficients C z n ≅ underRow C z n where
  hom := rowCoefficientsToUnder C z n
  inv := underToRowCoefficients C z n
  hom_inv_id := rowCoefficientsToUnder_underTo C z n
  inv_hom_id := underToRowCoefficients_toUnder C z n

/-- The whole original reconstruction preserves the SAME complete base-word projection. -/
@[reassoc]
theorem rowCoefficientsIso_hom_projection (z : C) (n : ℕ) :
    (rowCoefficientsIso C z n).hom ≫ rowProjection C z n = rowCoefficientsProjection C z n := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  exact Under.chainFromInitialArrow_forget a.1 a.2

/-- Every complete original scalar coefficient reads back as the SAME native whole word. -/
theorem rowCoefficientsToUnder_app (z : C) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (a : (rowCoefficients C z n).obj q) :
    (rowCoefficientsToUnder C z n).app q a =
      Under.chainFromInitialArrow a.1 (X := sourceObject C z q) a.2 := rfl

/-- The inverse reads back the SAME whole original base word and original first Hom. -/
theorem underToRowCoefficients_app (z : C) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (U : (underRow C z n).obj q) :
    (underToRowCoefficients C z n).app q U = ⟨U ⋙ forget C z q, (U.obj 0).hom⟩ := rfl

end SSet.ScalarUnderCategory
