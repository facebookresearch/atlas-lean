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
# Exact geometric skyscrapers and their derived global sections

Let Ω be a separably closed field of universe u, X a scheme of that universe, and x : Spec(Ω)
→ X a geometric point. For additive-group coefficients M in universe max(u,w), its small-étale
skyscraper sheaf has value ∏_{z∈Fiber_x(U)} M at U → X.

This coefficient-to-sheaf functor is additive, preserves epimorphisms and homology, and
preserves injective objects through the stalk–skyscraper adjunction. Since its global sections
identify with M, its positive right-derived global sections vanish for every coefficient M.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}

/-- Let Ω be a separably closed field, x : Spec(Ω) → X a geometric point, and f : M → N an
epimorphism of additive groups in universe max(u,w). For every object U of X's small étale
category, the component of the skyscraper sheaf map x_*f at U is surjective. Its value is the
product of f over the geometric fiber Fiber_x(U). -/
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

/-- For a separably closed field Ω, a scheme X of universe u, and x : Spec(Ω) → X, the small-étale
skyscraper functor from AddCommGrpCat.{max(u,w)} to sheaves on X preserves epimorphisms. An
epic coefficient map induces a surjection on each product-valued skyscraper component. -/
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

/-- Let Ω be a separably closed field and x : Spec(Ω) → X a geometric point. The skyscraper sheaf
functor on AddCommGrpCat.{max(u,w)} is additive: its induced maps preserve sums of coefficient
morphisms. It is the right adjoint in the stalk–skyscraper adjunction. -/
instance smallEtaleSkyscraperAdditive (x : Spec (.of Ω) ⟶ X) :
    ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- For a geometric point x : Spec(Ω) → X with Ω separably closed, the additive-group small-étale
skyscraper functor preserves homology. It preserves kernels as a right adjoint and
epimorphisms through its product-valued components, giving the exactness needed for homology
preservation. -/
instance smallEtaleSkyscraperPreservesHomology (x : Spec (.of Ω) ⟶ X) :
    ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w})).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Let Ω be a separably closed field, x : Spec(Ω) → X a geometric point, and S₁ → S₂ → S₃ a short
exact sequence in AddCommGrpCat.{max(u,w)}. Applying the small-étale skyscraper functor gives
a short exact sequence of additive-group sheaves on X. -/
theorem smallEtaleSkyscraper_shortExact (x : Spec (.of Ω) ⟶ X)
    (S : ShortComplex AddCommGrpCat.{max u w}) (hS : S.ShortExact) :
    (S.map ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w}))).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact hS.map _

/-- For a geometric point x : Spec(Ω) → X with Ω a separably closed field, the small-étale
skyscraper functor on additive groups preserves injective objects. Its left adjoint, the
geometric stalk functor, preserves monomorphisms, so the adjunction sends injective
coefficients to injective sheaves. -/
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

/-- Let Ω be a separably closed field of universe u, X a scheme of that universe, x : Spec(Ω) → X,
M ∈ AddCommGrpCat.{max(u,w)}, and n ∈ ℕ. Then (R^{n+1}Γ)(x_*M) is a zero object for the small
étale topology. This holds for every coefficient M; exactness and injective preservation of
x_* and the comparison Γ(x_*M)≅M compute the derived functor. -/
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
