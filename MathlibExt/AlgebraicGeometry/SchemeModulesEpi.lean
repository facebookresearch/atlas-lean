/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.Basic

@[expose] public section

universe u v v' u'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem epi_toSheaf_map_of_epi {M N : SheafOfModules.{v} R} (φ : M ⟶ N) [Epi φ] :
    Epi ((toSheaf R).map φ) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
  let G := SheafOfModules.forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let S := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  let ψ := G.map φ
  haveI hcounit : IsIso adj.counit :=
    inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).counit)
  let εM : S.obj (G.obj M) ≅ M :=
    @asIso _ _ _ _ (adj.counit.app M) (NatIso.isIso_app_of_isIso adj.counit M)
  let εN : S.obj (G.obj N) ≅ N :=
    @asIso _ _ _ _ (adj.counit.app N) (NatIso.isIso_app_of_isIso adj.counit N)
  have hnat : S.map ψ ≫ εN.hom = εM.hom ≫ φ := adj.counit.naturality φ
  haveI : Epi (S.map ψ) := by
    have hthis : S.map ψ = (εM.hom ≫ φ) ≫ εN.inv := (Iso.eq_comp_inv εN).2 hnat
    rw [hthis]; infer_instance
  have h0 : S.map (cokernel.π ψ) = 0 := by
    apply zero_of_epi_comp (S.map ψ)
    rw [← S.map_comp, cokernel.condition]
    exact S.map_zero _ _
  let T := PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v}
  have hT : ∀ {P Q : PresheafOfModules.{v} R.obj} (f : P ⟶ Q),
      T.map f = (toSheaf R).map (S.map f) := fun f => rfl
  have h0' : T.map (cokernel.π ψ) = 0 := by
    rw [hT, h0]
    exact Functor.map_zero _ _ _
  have hc := isColimitOfHasCokernelOfPreservesColimit T ψ
  haveI hTψ : Epi (T.map ψ) := by
    refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc g hg
    rw [← hd]
    change T.map (cokernel.π ψ) ≫ d = 0
    rw [h0', zero_comp]
  have h2 : T.map ψ ≫ ((toSheaf R).mapIso εN).hom =
      ((toSheaf R).mapIso εM).hom ≫ (toSheaf R).map φ := by
    change (toSheaf R).map (S.map ψ) ≫ (toSheaf R).map εN.hom =
      (toSheaf R).map εM.hom ≫ (toSheaf R).map φ
    rw [← Functor.map_comp, ← Functor.map_comp, hnat]
  have hthis : (toSheaf R).map φ =
      ((toSheaf R).mapIso εM).inv ≫ T.map ψ ≫ ((toSheaf R).mapIso εN).hom :=
    (Iso.eq_inv_comp _).2 h2.symm
  rw [hthis]
  haveI : IsIso ((toSheaf R).mapIso εM).inv := ((toSheaf R).mapIso εM).isIso_inv
  haveI : IsIso ((toSheaf R).mapIso εN).hom := ((toSheaf R).mapIso εN).isIso_hom
  haveI h1 : Epi (T.map ψ ≫ ((toSheaf R).mapIso εN).hom) :=
    epi_comp' hTψ (@IsIso.epi_of_iso _ _ _ _ ((toSheaf R).mapIso εN).hom
      ((toSheaf R).mapIso εN).isIso_hom)
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ ((toSheaf R).mapIso εM).inv
    ((toSheaf R).mapIso εM).isIso_inv) h1

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An epimorphism of module sheaves on a scheme is locally surjective on
sections: every section of the target, at every point of its open set, lifts
to the source after shrinking the open set around that point, and conversely
this local lifting property implies that the morphism is an epimorphism. -/
public theorem Hom.epi_iff_locallySurjective {M N : X.Modules} (φ : M ⟶ N) :
    Epi φ ↔ ∀ (U : X.Opens) (s : Γ(N, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ N.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V) := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  haveI : ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization AddCommGrpCat.{u} :=
    ⟨⟨ConcreteCategory.functorialSurjectiveInjectiveFactorizationData _⟩⟩
  have key : Epi φ ↔ Sheaf.IsLocallySurjective (F.map φ) := by
    constructor
    · intro hφ
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ :=
        ⟨fun g h w => (cancel_epi φ).1 w⟩
      haveI : Epi (F.map φ) :=
        @SheafOfModules.epi_toSheaf_map_of_epi _ _ _ X.ringCatSheaf _ _ M N φ hepi
      exact (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u})
        (φ := F.map φ)).2 inferInstance
    · intro h
      haveI : Epi (F.map φ) := (Sheaf.isLocallySurjective_iff_epi'
        (A := AddCommGrpCat.{u}) (φ := F.map φ)).1 h
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ :=
        F.epi_of_epi_map inferInstance
      exact ⟨fun g h w => (@cancel_epi _ _ _ _ _ φ hepi _ _).1 w⟩
  rw [key]
  constructor
  · intro h U s x hx
    obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (F.map φ).hom (U := op U) s x hx
    exact ⟨V, i.le, hxV, t, ht⟩
  · intro h
    refine ⟨fun {U} s x hx => ?_⟩
    obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
    exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩

end AlgebraicGeometry.Scheme.Modules
