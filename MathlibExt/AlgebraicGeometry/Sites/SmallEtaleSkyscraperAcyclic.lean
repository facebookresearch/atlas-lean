/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleSkyscraperSections
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Precomposition
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exactness and derived sections of geometric skyscrapers

Skyscraper coefficient maps are objectwise products of the additive-group
map. Exact products give epimorphism preservation on the sheaf category,
and the exact point adjunction preserves injectives.

Mapping a coefficient injective resolution and applying the global-sections
comparison gives vanishing of positive right-derived global sections.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}

/-- Each original skyscraper component map is surjective for an epi coefficient map. -/
theorem smallEtaleSkyscraperMap_component_surjective (x : Spec (.of Ω) ⟶ X)
    {M N : AddCommGrpCat.{max u w}} (f : M ⟶ N) [Epi f] (U : X.Etale) :
    Function.Surjective
      (((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.map f).hom.app
        (op U)) := by
  let p := smallEtaleGeometricPointCommon.{u, w} x
  let I : Type (max u w) := p.fiber.obj U
  let t : Discrete.functor (fun _ : I => M) ⟶ Discrete.functor (fun _ : I => N) :=
    Discrete.natTrans (fun _ => f)
  let : ∀ j : Discrete I, Epi (t.app j) := by
    intro j
    change Epi f
    infer_instance
  let : Epi t := NatTrans.epi_of_epi_app t
  have ht : Epi ((lim (J := Discrete I) (C := AddCommGrpCat.{max u w})).map t) := by
    infer_instance
  exact (AddCommGrpCat.epi_iff_surjective _).mp ht

/-- The actual point skyscraper preserves epimorphisms by its objectwise group products. -/
instance smallEtaleSkyscraperPreservesEpimorphisms (x : Spec (.of Ω) ⟶ X) :
    ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w})).PreservesEpimorphisms where
  preserves {M N} f hf := by
    let b := (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.map f
    let : ∀ U : X.Etaleᵒᵖ, Epi (b.hom.app U) := fun U =>
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (smallEtaleSkyscraperMap_component_surjective.{u, w} x f U.unop)
    let : Epi b.hom := NatTrans.epi_of_epi_app b.hom
    exact (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).epi_of_epi_map
      (show Epi b.hom from inferInstance)

/-- The same actual skyscraper right adjoint is additive. -/
instance smallEtaleSkyscraperAdditive (x : Spec (.of Ω) ⟶ X) :
    ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Epimorphism preservation and the actual preserved kernels make the skyscraper exact. -/
instance smallEtaleSkyscraperPreservesHomology (x : Spec (.of Ω) ⟶ X) :
    ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w})).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Every coefficient short exact sequence maps to the same actual skyscraper sequence. -/
theorem smallEtaleSkyscraper_shortExact (x : Spec (.of Ω) ⟶ X)
    (S : ShortComplex AddCommGrpCat.{max u w}) (hS : S.ShortExact) :
    (S.map ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w}))).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact hS.map _

/-- Exactness of the original point stalk makes its actual skyscraper preserve injectives. -/
instance smallEtaleSkyscraperPreservesInjectives (x : Spec (.of Ω) ⟶ X) :
    ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w})).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))

private theorem identityDerivedSuccIsZero.{v} (M : AddCommGrpCat.{v}) (n : ℕ) :
    IsZero (((𝟭 AddCommGrpCat.{v}).rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (𝟭 AddCommGrpCat.{v}) (n + 1))
  have h := I.cocomplex_exactAt_succ n
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h

/-- Every positive right-derived global-sections object of the actual skyscraper is zero. -/
theorem smallEtaleSkyscraperDerivedSections_succ_isZero (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w}) (n : ℕ) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived
      (n + 1)).obj
        ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M)) := by
  let R := (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
    (A := AddCommGrpCat.{max u w})
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let I := injectiveResolution M
  let e := (Functor.rightDerivedPrecompIsoWithResolution R Γ (n + 1) I).symm ≪≫
    ((NatIso.rightDerived (smallEtaleSkyscraperSectionsIso.{u, w} x) (n + 1)).app M)
  exact IsZero.of_iso (identityDerivedSuccIsZero M n) e

end AlgebraicGeometry.Scheme.DerivedSections
