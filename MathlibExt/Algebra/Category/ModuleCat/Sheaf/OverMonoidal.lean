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

public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# Monoidal restriction along arrows between slice sites

Let `C : Type u` have morphism universe `u`, `J` be a Grothendieck topology, and `ℛ : Sheaf J
CommRingCat.{u}`. Write `ℛ_ring` for the underlying ring sheaf of `ℛ`. For `h : V → U`, presheaf restriction precomposes with `Over.map h : Over V
→ Over U`. With weak additive sheafification and the locally-bijective and underlying-ring
comparisons on the relevant slices, it commutes naturally with module sheafification.

Assume also monoidality of `W` on the base and slice sites. The sheaf functor
`F_h=SheafOfModules.overMap ℛ_ring h` is monoidal. Its unit map agrees with the
structure-module comparison, and its tensor isomorphism has direction `F_h(M ⊗ N) ≅ F_h(M) ⊗
F_h(N)`. The comparison between successive and direct restriction preserves units and tensors.

Generic category lemmas express descent of monoidality along an essentially surjective
monoidal functor, composition of adjunction-unit mates, and compatibility of module-unit maps.
-/

@[expose] public section
noncomputable section

open CategoryTheory MonoidalCategory
open PresheafOfModulesOfCommRing
open scoped _root_.AddCommGrpCat

universe u u₁ u₂ u₃ v v₁ v₂ v₃

namespace SheafOfModules.OverMonoidal

section

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [J.WEqualsLocallyBijective Ab.{u}] [HasWeakSheafify J Ab.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Let `(C,J)` be a site at common universe `u`, `R : Sheaf J CommRingCat.{u}`, and assume weak
additive sheafification, the locally-bijective comparison, and the underlying-ring sheaf
comparison. For `M : SheafOfModules(sheafComposeRing R)`, the counit isomorphism has direction
`sheafificationBase R (forgetRestrictBase R M) ≅ M`. -/
private def counitIso (M : SheafOfModules (sheafComposeRing R)) :
    (sheafificationBase R).obj ((forgetRestrictBase R).obj M) ≅ M :=
  asIso ((sheafificationAdjBase R).counit.app M)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- Let `(C,J)` be a site at common universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`.
The functor `overMapPresheaf ℛ h` sends module presheaves over `(ℛ.over U).obj` to those over
`(ℛ.over V).obj`, using the underlying ring presheaves. It precomposes with `(Over.map h).op`,
so an object `Y→V` is evaluated at the composite `Y→V→U`. -/
private def overMapPresheaf :
    PresheafOfModulesOfCommRing (ℛ.over U).obj ⥤
      PresheafOfModulesOfCommRing (ℛ.over V).obj :=
  PresheafOfModules.pushforward₀OfCommRingCat (Over.map h) (ℛ.over U).obj

/-- Let `(C,J)` be a site at common universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`,
with underlying-ring sheaf comparisons on the base and both slices. Put `P_h=overMapPresheaf`,
`F_h=overMap ℛ_ring h`, and `U_U,U_V` for the forgetful module-presheaf functors. For a module
sheaf `M` over `U`, `forgetOverMapIso ℛ h M` identifies `P_h(U_U M)` with `U_V(F_h M)`. -/
private def forgetOverMapIso (M : SheafOfModules ((sheafComposeRing ℛ).over U)) :
    (overMapPresheaf ℛ h).obj ((forgetRestrictBase (ℛ.over U)).obj M) ≅
      (forgetRestrictBase (ℛ.over V)).obj
        ((SheafOfModules.overMap (sheafComposeRing ℛ) h).obj M) := Iso.refl _

omit [(J.W (A := Ab.{u})).IsMonoidal]
  [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}]
  [((J.over U).W (A := Ab.{u})).IsMonoidal]
  [((J.over V).W (A := Ab.{u})).IsMonoidal]
  [HasWeakSheafify (J.over V) Ab.{u}]
  [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Let `(C,J)` be a site at universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`. Assume
weak additive sheafification on `J.over U`, locally-bijective characterizations of `W` on both
slices, and underlying-ring comparisons on the base and source slice. For a module presheaf
`A` over `U`, the underlying additive map of `overMapPresheaf ℛ h (η_U,A)` belongs to `(J.over
V).W`, where `η_U` is the source sheafification unit. -/
private theorem overMapPresheaf_unit_memW
    (A : PresheafOfModulesOfCommRing (ℛ.over U).obj) :
    (J.over V).W.inverseImage
        (PresheafOfModules.toPresheaf ((sheafComposeRing ℛ).over V).obj)
      ((overMapPresheaf ℛ h).map ((sheafificationAdjBase (ℛ.over U)).unit.app A)) := by
  let J := J
  let a : (Over U)ᵒᵖ ⥤ Ab.{u} := (PresheafOfModules.toPresheaf _).obj A
  have heq : (PresheafOfModules.toPresheaf ((sheafComposeRing ℛ).over V).obj).map
      ((overMapPresheaf ℛ h).map ((sheafificationAdjBase (ℛ.over U)).unit.app A)) =
      (Over.map h).op.whiskerLeft (_root_.CategoryTheory.toSheafify (J.over U) a) := rfl
  have hi : Presheaf.IsLocallyInjective (J.over V)
      ((Over.map h).op.whiskerLeft (_root_.CategoryTheory.toSheafify (J.over U) a)) :=
    Presheaf.isLocallyInjective_whisker (J.over V) (J.over U) (Over.map h) _
  have hs : Presheaf.IsLocallySurjective (J.over V)
      ((Over.map h).op.whiskerLeft (_root_.CategoryTheory.toSheafify (J.over U) a)) :=
    Presheaf.isLocallySurjective_whisker (J.over V) (J.over U) (Over.map h) _
  change (J.over V).W ((PresheafOfModules.toPresheaf _).map _)
  rw [heq]
  exact (GrothendieckTopology.W_iff_isLocallyBijective _ _).mpr ⟨hi, hs⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [((J.over U).W (A := Ab.{u})).IsMonoidal]
  [((J.over V).W (A := Ab.{u})).IsMonoidal] in
/-- Let `(C,J)` be a site at universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`, with
weak additive sheafification, the locally-bijective comparison, and underlying-ring
comparisons on both slices. For a module presheaf `A` over `U`, the map `L_V(P_h(η_U,A))` is
an isomorphism, where `P_h=overMapPresheaf ℛ h`, `L_V=sheafificationBase (ℛ.over V)`, and
`η_U` is the source sheafification unit. -/
private theorem isIso_overMapPresheaf_sheafify_unit
    (A : PresheafOfModulesOfCommRing (ℛ.over U).obj) :
    IsIso ((sheafificationBase (ℛ.over V)).map
      ((overMapPresheaf ℛ h).map ((sheafificationAdjBase (ℛ.over U)).unit.app A))) := by
  have : Presheaf.IsLocallyInjective (J.over V)
      (Sheaf.commRingCatForget₂Id (ℛ.over V)) := by
    change Presheaf.IsLocallyInjective _ (𝟙 ((ℛ.over V).obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  have : Presheaf.IsLocallySurjective (J.over V)
      (Sheaf.commRingCatForget₂Id (ℛ.over V)) := by
    change Presheaf.IsLocallySurjective _ (𝟙 ((ℛ.over V).obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  exact Localization.inverts (sheafificationBase (ℛ.over V))
    ((J.over V).W.inverseImage
      (PresheafOfModules.toPresheaf ((ℛ.over V).obj ⋙ forget₂ CommRingCat RingCat))) _
    (overMapPresheaf_unit_memW ℛ h A)

/-- Let `(C,J)` be a site at universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`, with
weak additive sheafification and the locally-bijective and underlying-ring comparisons on both
slices. Write `P_h` for presheaf restriction, `F_h` for sheaf restriction, and `L_U,U_V` for
source sheafification and target forgetting. For a module presheaf `A`, the map `α_h(A) : P_h
A → U_V(F_h(L_U A))` is `P_h(η_U,A)` followed by `forgetOverMapIso` at `L_U A`. -/
private def overMapSheafificationAdjoint
    (A : PresheafOfModulesOfCommRing (ℛ.over U).obj) :
    (overMapPresheaf ℛ h).obj A ⟶
      (forgetRestrictBase (ℛ.over V)).obj
        ((SheafOfModules.overMap (sheafComposeRing ℛ) h).obj
          ((sheafificationBase (ℛ.over U)).obj A)) :=
  (overMapPresheaf ℛ h).map ((sheafificationAdjBase (ℛ.over U)).unit.app A) ≫
    (forgetOverMapIso ℛ h ((sheafificationBase (ℛ.over U)).obj A)).hom

/-- Let `(C,J)` be a site at universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`, with
weak additive sheafification and the locally-bijective and underlying-ring comparisons on both
slices and the base ring comparison. For `P_h=overMapPresheaf`, `F_h=overMap`, and `L_U,L_V`
the two sheafifiers, `overMapSheafificationHom ℛ h A : L_V(P_h A) → F_h(L_U A)` is the mate of
`overMapSheafificationAdjoint ℛ h A` under `L_V ⊣ U_V`. -/
private def overMapSheafificationHom
    (A : PresheafOfModulesOfCommRing (ℛ.over U).obj) :
    (sheafificationBase (ℛ.over V)).obj ((overMapPresheaf ℛ h).obj A) ⟶
      (SheafOfModules.overMap (sheafComposeRing ℛ) h).obj
        ((sheafificationBase (ℛ.over U)).obj A) :=
  ((sheafificationAdjBase (ℛ.over V)).homEquiv _ _).symm
    (overMapSheafificationAdjoint ℛ h A)

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [((J.over U).W (A := Ab.{u})).IsMonoidal]
  [((J.over V).W (A := Ab.{u})).IsMonoidal] in
/-- Let `(C,J)` be a site at universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`. Assume
weak additive sheafification, locally-bijective comparisons, and underlying-ring sheaf
comparisons on both slices, together with the base ring comparison. For every module presheaf
`A` over `U`, the comparison `L_V(P_h A) → F_h(L_U A)` given by `overMapSheafificationHom ℛ h
A` is an isomorphism. -/
private theorem isIso_overMapSheafificationHom
    (A : PresheafOfModulesOfCommRing (ℛ.over U).obj) :
    IsIso (overMapSheafificationHom ℛ h A) := by
  let B := (SheafOfModules.overMap (sheafComposeRing ℛ) h).obj
    ((sheafificationBase (ℛ.over U)).obj A)
  have hc : IsIso ((sheafificationAdjBase (ℛ.over V)).counit.app B) :=
    (counitIso (ℛ.over V) B).isIso_hom
  have hp : IsIso ((sheafificationBase (ℛ.over V)).map
      (overMapSheafificationAdjoint ℛ h A)) := by
    change IsIso ((sheafificationBase (ℛ.over V)).map
      ((overMapPresheaf ℛ h).map ((sheafificationAdjBase (ℛ.over U)).unit.app A) ≫
        (forgetOverMapIso ℛ h ((sheafificationBase (ℛ.over U)).obj A)).hom))
    rw [Functor.map_comp]
    have hu := isIso_overMapPresheaf_sheafify_unit ℛ h A
    exact IsIso.comp_isIso' hu (Functor.map_isIso _ _)
  have heq : overMapSheafificationHom ℛ h A =
      (sheafificationBase (ℛ.over V)).map (overMapSheafificationAdjoint ℛ h A) ≫
        (sheafificationAdjBase (ℛ.over V)).counit.app B :=
    (sheafificationAdjBase (ℛ.over V)).homEquiv_counit _ _ _
  rw [heq]
  exact IsIso.comp_isIso' hp hc

omit [(J.W (A := Ab.{u})).IsMonoidal]
  [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}]
  [((J.over U).W (A := Ab.{u})).IsMonoidal]
  [((J.over V).W (A := Ab.{u})).IsMonoidal]
  [(J.over V).WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify (J.over V) Ab.{u}] in
/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, and assume weak
additive sheafification, locally-bijective comparisons, and underlying-ring sheaf comparisons
on both slices and the base ring comparison. For `P_h` the presheaf restriction, `F_h` the
sheaf restriction, `L_U` source sheafification, `U_V` target forgetting, and `a : A → B`, the
adjoints `α` satisfy `P_h(a) ≫ α_h(B) = α_h(A) ≫ U_V(F_h(L_U(a)))`. -/
private theorem overMapSheafificationAdjoint_naturality
    {A B : PresheafOfModulesOfCommRing (ℛ.over U).obj} (a : A ⟶ B) :
    (overMapPresheaf ℛ h).map a ≫ overMapSheafificationAdjoint ℛ h B =
      overMapSheafificationAdjoint ℛ h A ≫
        (forgetRestrictBase (ℛ.over V)).map
          ((SheafOfModules.overMap (sheafComposeRing ℛ) h).map
            ((sheafificationBase (ℛ.over U)).map a)) := by
  let P := overMapPresheaf ℛ h
  let L := sheafificationBase (ℛ.over U)
  let F := forgetRestrictBase (ℛ.over U)
  let adj := sheafificationAdjBase (ℛ.over U)
  have hu : a ≫ adj.unit.app B = adj.unit.app A ≫ F.map (L.map a) := by
    exact adj.unit.naturality a
  change P.map a ≫ P.map (adj.unit.app B) ≫ 𝟙 _ =
    (P.map (adj.unit.app A) ≫ 𝟙 _) ≫ P.map (F.map (L.map a))
  simp only [Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp, hu]

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [((J.over U).W (A := Ab.{u})).IsMonoidal]
  [((J.over V).W (A := Ab.{u})).IsMonoidal] in
/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, locally-bijective comparisons, and underlying-ring comparisons on both slices
and the base ring comparison. For a presheaf-module map `a : A → B`, `L_V(P_h(a)) ≫ σ_h(B) =
σ_h(A) ≫ F_h(L_U(a))`, where `σ_h=overMapSheafificationHom ℛ h`, `P_h` is presheaf
restriction, and `F_h` is sheaf restriction. -/
private theorem overMapSheafificationHom_naturality
    {A B : PresheafOfModulesOfCommRing (ℛ.over U).obj} (a : A ⟶ B) :
    (sheafificationBase (ℛ.over V)).map ((overMapPresheaf ℛ h).map a) ≫
        overMapSheafificationHom ℛ h B =
      overMapSheafificationHom ℛ h A ≫
        (SheafOfModules.overMap (sheafComposeRing ℛ) h).map
          ((sheafificationBase (ℛ.over U)).map a) := by
  let P := overMapPresheaf ℛ h
  let LU := sheafificationBase (ℛ.over U)
  let LV := sheafificationBase (ℛ.over V)
  let F := forgetRestrictBase (ℛ.over V)
  let S := SheafOfModules.overMap (sheafComposeRing ℛ) h
  let adj : LV ⊣ F := sheafificationAdjBase (ℛ.over V)
  let αA : LV.obj (P.obj A) ⟶ S.obj (LU.obj A) := overMapSheafificationHom ℛ h A
  let αB : LV.obj (P.obj B) ⟶ S.obj (LU.obj B) := overMapSheafificationHom ℛ h B
  change LV.map (P.map a) ≫ αB = αA ≫ S.map (LU.map a)
  have hA : adj.homEquiv _ _ αA = overMapSheafificationAdjoint ℛ h A :=
    (adj.homEquiv _ _).apply_symm_apply _
  have hB : adj.homEquiv _ _ αB = overMapSheafificationAdjoint ℛ h B :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv (P.obj A) (S.obj (LU.obj B))).injective
  calc
    _ = P.map a ≫ adj.homEquiv _ _ αB :=
      adj.homEquiv_naturality_left (P.map a) αB
    _ = P.map a ≫ overMapSheafificationAdjoint ℛ h B :=
      congrArg (fun t => P.map a ≫ t) hB
    _ = overMapSheafificationAdjoint ℛ h A ≫ F.map (S.map (LU.map a)) :=
      overMapSheafificationAdjoint_naturality ℛ h a
    _ = _ := (congrArg (fun t => t ≫ F.map (S.map (LU.map a))) hA.symm).trans
      (adj.homEquiv_naturality_right αA (S.map (LU.map a))).symm

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, locally-bijective comparisons, and underlying-ring comparisons on both slices
and the base ring comparison. There is a natural isomorphism `P_h ⋙ L_V ≅ L_U ⋙ F_h`, where
`P_h=overMapPresheaf ℛ h`, `F_h=overMap ℛ_ring h`, and `L_U,L_V` are the slice module
sheafifiers. Its forward component is `overMapSheafificationHom ℛ h A`. -/
private def overMapSheafificationIso :
    overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V) ≅
      sheafificationBase (ℛ.over U) ⋙ SheafOfModules.overMap (sheafComposeRing ℛ) h :=
  NatIso.ofComponents
    (fun A => by
      letI : IsIso (overMapSheafificationHom ℛ h A) := isIso_overMapSheafificationHom ℛ h A
      exact asIso (overMapSheafificationHom ℛ h A))
    (fun a => by
      exact overMapSheafificationHom_naturality ℛ h a)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- For a site `(C,J)` at universe `u`, a commutative ring sheaf `ℛ`, and `h : V → U`,
`overMapPresheaf ℛ h` is monoidal by precomposition with `(Over.map h).op`. Tensor products
and structure-module presheaves are preserved through their pointwise comparison maps. -/
private instance overMapPresheafMonoidal : (overMapPresheaf ℛ h).Monoidal :=
  inferInstanceAs ((PresheafOfModules.pushforward₀OfCommRingCat
    (Over.map h) (ℛ.over U).obj).Monoidal)

attribute [-instance] overMapPresheafMonoidal
attribute [local instance] overMapPresheafMonoidal

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, and assume the base
underlying-ring comparison. On both slice sites assume weak additive sheafification,
locally-bijective comparison, monoidal `W`, and underlying-ring comparison. The functor
`F_h=SheafOfModules.overMap ℛ_ring h : SheafOfModules(ℛ_ring.over U) →
SheafOfModules(ℛ_ring.over V)` is monoidal, by the presheaf restriction/sheafification natural
comparison. -/
private instance overMapMonoidal :
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    (SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal := by
  letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
    SheafOfModules.monoidalCategory (ℛ.over U)
  letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
    SheafOfModules.monoidalCategory (ℛ.over V)
  have : Presheaf.IsLocallyInjective (J.over U)
      (Sheaf.commRingCatForget₂Id (ℛ.over U)) := by
    change Presheaf.IsLocallyInjective _ (𝟙 ((ℛ.over U).obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  have : Presheaf.IsLocallySurjective (J.over U)
      (Sheaf.commRingCatForget₂Id (ℛ.over U)) := by
    change Presheaf.IsLocallySurjective _ (𝟙 ((ℛ.over U).obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  letI : (overMapPresheaf ℛ h).Monoidal := overMapPresheafMonoidal ℛ h
  letI : (sheafificationBase (ℛ.over U)).Monoidal :=
    SheafOfModules.sheafificationCommIdMonoidal (ℛ.over U)
  letI : (sheafificationBase (ℛ.over V)).Monoidal :=
    SheafOfModules.sheafificationCommIdMonoidal (ℛ.over V)
  letI : (overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V)).Monoidal :=
    Functor.Monoidal.instComp (overMapPresheaf ℛ h) (sheafificationBase (ℛ.over V))
  letI : Localization.Lifting (sheafificationBase (ℛ.over U))
      ((J.over U).W.inverseImage
        (PresheafOfModules.toPresheaf ((ℛ.over U).obj ⋙ forget₂ CommRingCat RingCat)))
      (overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V))
      (SheafOfModules.overMap (sheafComposeRing ℛ) h) := ⟨(overMapSheafificationIso ℛ h).symm⟩
  exact @Localization.Monoidal.functorMonoidalOfComp
    (PresheafOfModulesOfCommRing (ℛ.over U).obj)
    (SheafOfModules ((sheafComposeRing ℛ).over U))
    (SheafOfModules ((sheafComposeRing ℛ).over V))
    _ _ _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
    (SheafOfModules.monoidalCategory (ℛ.over U))
    (SheafOfModules.monoidalCategory (ℛ.over V))
    (sheafificationBase (ℛ.over U))
    ((J.over U).W.inverseImage
      (PresheafOfModules.toPresheaf ((ℛ.over U).obj ⋙ forget₂ CommRingCat RingCat)))
    (PresheafOfModules.instIsLocalizationSheafOfModulesSheafificationInverseImageFunctorOppositeAbWToPresheaf
      (Sheaf.commRingCatForget₂Id (ℛ.over U)))
    (SheafOfModules.sheafificationCommIdMonoidal (ℛ.over U))
    (SheafOfModules.overMap (sheafComposeRing ℛ) h)
    (overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V))
    (@Functor.Monoidal.instComp
      (PresheafOfModulesOfCommRing (ℛ.over U).obj) _
      (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
      (PresheafOfModulesOfCommRing (ℛ.over V).obj) _
      (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over V).obj))
      (SheafOfModules ((sheafComposeRing ℛ).over V)) _
      (SheafOfModules.monoidalCategory (ℛ.over V))
      (overMapPresheaf ℛ h) (sheafificationBase (ℛ.over V))
      (overMapPresheafMonoidal ℛ h)
      (SheafOfModules.sheafificationCommIdMonoidal (ℛ.over V))) _
    ⟨(overMapSheafificationIso ℛ h).symm⟩

attribute [-instance] overMapMonoidal
attribute [local instance] overMapMonoidal

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Functor.LaxMonoidal

/-- Let `C,D,E` be monoidal categories with independently quantified object and morphism
universes. Let `L : C → D` be monoidal and essentially surjective, `F,G : D → E` lax monoidal,
and `τ : F → G` a natural transformation. If its precomposition `Functor.whiskerLeft L τ` is
monoidal, then `τ` is monoidal. -/
private theorem isMonoidal_of_whiskerLeft
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (L : C ⥤ D) [L.Monoidal] [L.EssSurj]
    {F G : D ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G)
    [NatTrans.IsMonoidal (Functor.whiskerLeft L τ)] : NatTrans.IsMonoidal τ := by
  have hu := NatTrans.IsMonoidal.unit (τ := Functor.whiskerLeft L τ)
  have ht := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerLeft L τ)
  constructor
  · apply (cancel_mono (G.map (Functor.Monoidal.εIso L).hom)).mp
    simpa only [Functor.LaxMonoidal.comp_ε, Functor.whiskerLeft_app,
      Functor.Monoidal.εIso_hom, Category.assoc, τ.naturality] using hu
  · intro A B
    have hbase (a b : C) :
        μ F (L.obj a) (L.obj b) ≫ τ.app (L.obj a ⊗ L.obj b) =
          (τ.app (L.obj a) ⊗ₘ τ.app (L.obj b)) ≫ μ G (L.obj a) (L.obj b) := by
      apply (cancel_mono (G.map (Functor.Monoidal.μIso L a b).hom)).mp
      have h := ht a b
      simpa only [Functor.LaxMonoidal.comp_μ, Functor.whiskerLeft_app,
        Functor.Monoidal.μIso_hom, Category.assoc, τ.naturality] using h
    let eA := L.objObjPreimageIso A
    let eB := L.objObjPreimageIso B
    apply (cancel_epi (F.map eA.hom ⊗ₘ F.map eB.hom)).mp
    rw [← Category.assoc, μ_natural]
    rw [Category.assoc, τ.naturality, ← Category.assoc, hbase]
    rw [Category.assoc, ← μ_natural]
    rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
      τ.naturality, τ.naturality]

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

/-- Let `C_i,D_i` for `i=0,1,2` be categories of common object universe `u` and morphism universe `v`, with adjunctions `L_i ⊣ G_i` and units `ι_i`. For `ij=01,12,02`, give functors `P_ij : C_i → C_j`, `R_ij : D_i → D_j`, and isomorphisms `α_ij : G_i⋙P_ij ≅ R_ij⋙G_j`, `c_ij : P_ij⋙L_j ≅ L_i⋙R_ij`. Give `η : P_01⋙P_12 ≅ P_02` and `γ : R_01⋙R_12 ≅ R_02`. Assume each `c_ij(A)` is the mate of `P_ij(ι_i,A) ≫ α_ij(L_i A)` and, for every `Y∈D_0`,
`α_12(R_01 Y) ≫ G_2(γ_Y) = P_12(α_01(Y)⁻¹) ≫ η_{G_0Y} ≫ α_02(Y)`.
Then for every `A∈C_0`,
`c_12(P_01 A) ≫ R_12(c_01(A)) ≫ γ_{L_0A} = L_2(η_A) ≫ c_02(A)`. -/
private theorem unitMates_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
    [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
    {L₀ : C₀ ⥤ D₀} {G₀ : D₀ ⥤ C₀}
    {L₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂}
    (adj₀ : L₀ ⊣ G₀) (adj₁ : L₁ ⊣ G₁) (adj₂ : L₂ ⊣ G₂)
    {P₀₁ : C₀ ⥤ C₁} {P₁₂ : C₁ ⥤ C₂} {P₀₂ : C₀ ⥤ C₂}
    {R₀₁ : D₀ ⥤ D₁} {R₁₂ : D₁ ⥤ D₂} {R₀₂ : D₀ ⥤ D₂}
    (α₀₁ : G₀ ⋙ P₀₁ ≅ R₀₁ ⋙ G₁)
    (α₁₂ : G₁ ⋙ P₁₂ ≅ R₁₂ ⋙ G₂)
    (α₀₂ : G₀ ⋙ P₀₂ ≅ R₀₂ ⋙ G₂)
    (η : P₀₁ ⋙ P₁₂ ≅ P₀₂) (γ : R₀₁ ⋙ R₁₂ ≅ R₀₂)
    (c₀₁ : P₀₁ ⋙ L₁ ≅ L₀ ⋙ R₀₁)
    (c₁₂ : P₁₂ ⋙ L₂ ≅ L₁ ⋙ R₁₂)
    (c₀₂ : P₀₂ ⋙ L₂ ≅ L₀ ⋙ R₀₂)
    (hm₀₁ : ∀ A, adj₁.homEquiv _ _ (c₀₁.hom.app A) =
      P₀₁.map (adj₀.unit.app A) ≫ α₀₁.hom.app (L₀.obj A))
    (hm₁₂ : ∀ A, adj₂.homEquiv _ _ (c₁₂.hom.app A) =
      P₁₂.map (adj₁.unit.app A) ≫ α₁₂.hom.app (L₁.obj A))
    (hm₀₂ : ∀ A, adj₂.homEquiv _ _ (c₀₂.hom.app A) =
      P₀₂.map (adj₀.unit.app A) ≫ α₀₂.hom.app (L₀.obj A))
    (hα : ∀ Y, α₁₂.hom.app (R₀₁.obj Y) ≫ G₂.map (γ.hom.app Y) =
      P₁₂.map (α₀₁.inv.app Y) ≫ η.hom.app (G₀.obj Y) ≫ α₀₂.hom.app Y)
    (A : C₀) :
    c₁₂.hom.app (P₀₁.obj A) ≫ R₁₂.map (c₀₁.hom.app A) ≫ γ.hom.app (L₀.obj A) =
      L₂.map (η.hom.app A) ≫ c₀₂.hom.app A := by
  have hc : adj₁.unit.app (P₀₁.obj A) ≫ G₁.map (c₀₁.hom.app A) =
      P₀₁.map (adj₀.unit.app A) ≫ α₀₁.hom.app (L₀.obj A) :=
    (adj₁.homEquiv_unit _ _ (c₀₁.hom.app A)).symm.trans (hm₀₁ A)
  have hn : α₁₂.hom.app (L₁.obj (P₀₁.obj A)) ≫ G₂.map (R₁₂.map (c₀₁.hom.app A)) =
      P₁₂.map (G₁.map (c₀₁.hom.app A)) ≫ α₁₂.hom.app (R₀₁.obj (L₀.obj A)) :=
    (α₁₂.hom.naturality (c₀₁.hom.app A)).symm
  have hη : P₁₂.map (P₀₁.map (adj₀.unit.app A)) ≫ η.hom.app (G₀.obj (L₀.obj A)) =
      η.hom.app A ≫ P₀₂.map (adj₀.unit.app A) := η.hom.naturality (adj₀.unit.app A)
  apply (adj₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Functor.map_comp, hm₁₂]
  simp only [Category.assoc]
  rw [← Category.assoc (α₁₂.hom.app (L₁.obj (P₀₁.obj A)))
    (G₂.map (R₁₂.map (c₀₁.hom.app A))) (G₂.map (γ.hom.app (L₀.obj A))), hn, Category.assoc]
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp]
  rw [hα]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, Category.comp_id]
  rw [← Category.assoc (P₁₂.map (P₀₁.map (adj₀.unit.app A)))
    (η.hom.app (G₀.obj (L₀.obj A))) (α₀₂.hom.app (L₀.obj A)), hη, Category.assoc]
  rw [Adjunction.homEquiv_naturality_left]
  exact congrArg (fun t => η.hom.app A ≫ t) (hm₀₂ A).symm

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- Let `(C,J)` be a site at universe `u`, `ℛ` a commutative ring sheaf, and `h : V → U`. Write
`q_U,q_V` for base-to-slice module-presheaf restriction and `P_h=overMapPresheaf ℛ h`. The
natural isomorphism `q_U ⋙ P_h ≅ q_V` identifies both functors on an object `Y→V` with
evaluation at `Y`; its components preserve the section values and ring actions. -/
private def presheafOverFunctorMap :
    restrictPresheaf ℛ U ⋙ overMapPresheaf ℛ h ≅ restrictPresheaf ℛ V :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun a => by ext K : 1; rfl)

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, with underlying-ring comparisons
on the base and slice over `W`. Write `U_0,U_W` for the module-presheaf forgetful functors,
`q_W` for presheaf restriction, and `F_W` for sheaf restriction. The natural isomorphism `U_0
⋙ q_W ≅ F_W ⋙ U_W` has component `forgetRestrictIso ℛ W A` at each module sheaf `A`. -/
private def forgetOverFunctorNatIso (W : C) :
    forgetRestrictBase ℛ ⋙ restrictPresheaf ℛ W ≅
      restrictSheaf ℛ W ⋙ forgetRestrictBase (ℛ.over W) :=
  NatIso.ofComponents (fun A => forgetRestrictIso ℛ W A) (fun _ => rfl)

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with underlying-ring
comparisons on the base and both slices. For `P_h=overMapPresheaf`, `F_h=overMap`, and
`U_U,U_V` the two forgetful functors, there is a natural isomorphism `U_U ⋙ P_h ≅ F_h ⋙ U_V`,
whose component is `forgetOverMapIso ℛ h A`. -/
private def forgetOverMapNatIso :
    forgetRestrictBase (ℛ.over U) ⋙ overMapPresheaf ℛ h ≅
      SheafOfModules.overMap (sheafComposeRing ℛ) h ⋙ forgetRestrictBase (ℛ.over V) :=
  NatIso.ofComponents (fun A => forgetOverMapIso ℛ h A) (fun _ => rfl)

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, locally-bijective comparisons, and underlying-ring comparisons on the base and
both slices. For `L=sheafificationBase ℛ`, `F_U,F_V` the base-to-slice restrictions, and
`F_h=overMap ℛ_ring h`, the natural isomorphism `(L ⋙ F_U) ⋙ F_h ≅ L ⋙ F_V` is obtained from
the sheafification comparisons and the identity of the two presheaf restriction composites. -/
private def sheafificationOverFunctorMapIso :
    (sheafificationBase ℛ ⋙ restrictSheaf ℛ U) ⋙
        SheafOfModules.overMap (sheafComposeRing ℛ) h ≅
      sheafificationBase ℛ ⋙ restrictSheaf ℛ V := by
  let P := restrictPresheaf ℛ U
  let Q := overMapPresheaf ℛ h
  let LU := sheafificationBase (ℛ.over U)
  let LV := sheafificationBase (ℛ.over V)
  let S := SheafOfModules.overMap (sheafComposeRing ℛ) h
  exact Functor.isoWhiskerRight (commIso ℛ U).symm S ≪≫
    Functor.associator P LU S ≪≫
    Functor.isoWhiskerLeft P (overMapSheafificationIso ℛ h).symm ≪≫
    (Functor.associator P Q LV).symm ≪≫
    Functor.isoWhiskerRight (presheafOverFunctorMap ℛ h) LV ≪≫ commIso ℛ V

omit [(J.W (A := Ab.{u})).IsMonoidal]
  [((J.over U).W (A := Ab.{u})).IsMonoidal] [((J.over V).W (A := Ab.{u})).IsMonoidal] in
/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, locally-bijective comparisons, and underlying-ring comparisons on the base and
slices. Put `L=sheafificationBase ℛ` and `γ_h=SheafOfModules.overFunctorMap ℛ_ring h : F_U ⋙
F_h ≅ F_V`. Then `(sheafificationOverFunctorMapIso ℛ h).hom = (Functor.associator L F_U
F_h).hom ≫ Functor.whiskerLeft L γ_h.hom`. -/
private theorem sheafificationOverFunctorMapIso_hom :
    (sheafificationOverFunctorMapIso ℛ h).hom =
      (Functor.associator (sheafificationBase ℛ) (restrictSheaf ℛ U)
        (SheafOfModules.overMap (sheafComposeRing ℛ) h)).hom ≫
        Functor.whiskerLeft (sheafificationBase ℛ)
          (SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h).hom := by
  let Rc : Sheaf J CommRingCat.{u} := ℛ
  let R := sheafComposeRing Rc
  let LX := sheafificationBase Rc
  let LU := sheafificationBase (Rc.over U)
  let LV := sheafificationBase (Rc.over V)
  let FX := forgetRestrictBase Rc
  let FU := forgetRestrictBase (Rc.over U)
  let FV := forgetRestrictBase (Rc.over V)
  let ax : LX ⊣ FX := sheafificationAdjBase Rc
  let au : LU ⊣ FU := sheafificationAdjBase (Rc.over U)
  let av : LV ⊣ FV := sheafificationAdjBase (Rc.over V)
  let P := restrictPresheaf Rc U
  let Q : PresheafOfModulesOfCommRing (Rc.over U).obj ⥤
      PresheafOfModulesOfCommRing (Rc.over V).obj := overMapPresheaf ℛ h
  let P' := restrictPresheaf Rc V
  let O : SheafOfModules (sheafComposeRing Rc) ⥤
      SheafOfModules (sheafComposeRing (Rc.over U)) := restrictSheaf Rc U
  let S : SheafOfModules (sheafComposeRing (Rc.over U)) ⥤
      SheafOfModules (sheafComposeRing (Rc.over V)) := SheafOfModules.overMap R h
  let O' : SheafOfModules (sheafComposeRing Rc) ⥤
      SheafOfModules (sheafComposeRing (Rc.over V)) := restrictSheaf Rc V
  let c := commIso Rc U
  let d : Q ⋙ LV ≅ LU ⋙ S := overMapSheafificationIso ℛ h
  let e := commIso Rc V
  let η : P ⋙ Q ≅ P' := presheafOverFunctorMap ℛ h
  let γ : O ⋙ S ≅ O' := SheafOfModules.overFunctorMap R h
  let α₁ : FX ⋙ P ≅ O ⋙ FU := forgetOverFunctorNatIso ℛ U
  let α₂ : FU ⋙ Q ≅ S ⋙ FV := forgetOverMapNatIso ℛ h
  let α₃ : FX ⋙ P' ≅ O' ⋙ FV := forgetOverFunctorNatIso ℛ V
  have hm₁ (A) : au.homEquiv _ _ (c.hom.app A) =
      P.map (ax.unit.app A) ≫ α₁.hom.app (LX.obj A) :=
    (au.homEquiv _ _).apply_symm_apply _
  have hm₂ (A) : av.homEquiv _ _ (d.hom.app A) =
      Q.map (au.unit.app A) ≫ α₂.hom.app (LU.obj A) :=
    (av.homEquiv _ _).apply_symm_apply _
  have hm₃ (A) : av.homEquiv _ _ (e.hom.app A) =
      P'.map (ax.unit.app A) ≫ α₃.hom.app (LX.obj A) :=
    (av.homEquiv _ _).apply_symm_apply _
  have hf (A) : α₂.hom.app (O.obj A) ≫ FV.map (γ.hom.app A) =
      Q.map (α₁.inv.app A) ≫ η.hom.app (FX.obj A) ≫ α₃.hom.app A := by
    ext K x
    rfl
  apply NatTrans.ext
  funext A
  have hc := unitMates_comp ax au av α₁ α₂ α₃ η γ c d e hm₁ hm₂ hm₃ hf A
  change (Functor.isoWhiskerRight c.symm S ≪≫ Functor.associator P LU S ≪≫
      Functor.isoWhiskerLeft P d.symm ≪≫ (Functor.associator P Q LV).symm ≪≫
      Functor.isoWhiskerRight η LV ≪≫ e).hom.app A =
    (Functor.associator LX O S).hom.app A ≫ γ.hom.app (LX.obj A)
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.id_comp]
  let cu : LU.obj (P.obj A) ≅ O.obj (LX.obj A) := c.app A
  let dh : LV.obj (Q.obj (P.obj A)) ≅ S.obj (LU.obj (P.obj A)) := d.app (P.obj A)
  let eh : LV.obj (P'.obj A) ⟶ O'.obj (LX.obj A) := e.hom.app A
  let pa : Q.obj (P.obj A) ⟶ P'.obj A := η.hom.app A
  let ga : S.obj (O.obj (LX.obj A)) ⟶ O'.obj (LX.obj A) := γ.hom.app (LX.obj A)
  change S.map cu.inv ≫ dh.inv ≫ LV.map pa ≫ eh = ga
  have hx : dh.hom ≫ S.map cu.hom ≫ ga = LV.map pa ≫ eh := hc
  rw [← hx]
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [S.map_id (O.obj (LX.obj A)), Category.id_comp]

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- For a site `(C,J)` at universe `u`, a commutative ring sheaf `ℛ`, and `h : V → U`, the
composite `restrictPresheaf ℛ U ⋙ overMapPresheaf ℛ h` is monoidal. It uses the composite of
the pointwise monoidal structures of the two presheaf-precomposition functors. -/
private instance presheafOverFunctorMapCompMonoidal :
    (restrictPresheaf ℛ U ⋙ overMapPresheaf ℛ h).Monoidal :=
  @Functor.Monoidal.instComp
    (PresheafOfModulesOfCommRing ℛ.obj) _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := ℛ.obj))
    (PresheafOfModulesOfCommRing (ℛ.over U).obj) _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
    (PresheafOfModulesOfCommRing (ℛ.over V).obj) _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over V).obj))
    (restrictPresheaf ℛ U) (overMapPresheaf ℛ h)
    (pfMonoidal ℛ U) (overMapPresheafMonoidal ℛ h)

attribute [-instance] presheafOverFunctorMapCompMonoidal
attribute [local instance] presheafOverFunctorMapCompMonoidal

omit [(J.W (A := Ab.{u})).IsMonoidal]
  [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [((J.over U).W (A := Ab.{u})).IsMonoidal]
  [(J.over U).WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify (J.over U) Ab.{u}]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
  [((J.over V).W (A := Ab.{u})).IsMonoidal]
  [(J.over V).WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify (J.over V) Ab.{u}]
  [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- For a site `(C,J)` at universe `u`, a commutative ring sheaf `ℛ`, and `h : V → U`, the natural
comparison `restrictPresheaf ℛ U ⋙ overMapPresheaf ℛ h ≅ restrictPresheaf ℛ V` is monoidal.
Its forward natural transformation preserves the tensor and unit comparison maps of the two
restriction functors. -/
private theorem presheafOverFunctorMap_isMonoidal :
    letI : (overMapPresheaf ℛ h).Monoidal := overMapPresheafMonoidal ℛ h
    letI : (restrictPresheaf ℛ U ⋙ overMapPresheaf ℛ h).Monoidal :=
      presheafOverFunctorMapCompMonoidal ℛ h
    letI : (restrictPresheaf ℛ V).Monoidal := pfMonoidal ℛ V
    (presheafOverFunctorMap ℛ h).hom.IsMonoidal := by
  let : (overMapPresheaf ℛ h).Monoidal := overMapPresheafMonoidal ℛ h
  let : (restrictPresheaf ℛ U ⋙ overMapPresheaf ℛ h).Monoidal :=
    presheafOverFunctorMapCompMonoidal ℛ h
  let : (restrictPresheaf ℛ V).Monoidal := pfMonoidal ℛ V
  constructor
  · ext K : 1
    rfl
  · intro A B
    ext K : 1
    exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (Z : C)
    [((J.over Z).W (A := Ab.{u})).IsMonoidal] [(J.over Z).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over Z) Ab.{u}]
    [(J.over Z).HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`Z`. The natural isomorphism `commIso R Z : restrictPresheaf R Z ⋙ sheafificationOver R Z ≅
sheafificationBase R ⋙ restrictSheaf R Z` has a monoidal forward transformation, preserving
tensor and unit comparison maps. -/
private theorem canonicalRestrictionCommIso_isMonoidal : (commIso R Z).hom.IsMonoidal := by
  let L := sheafificationBase R
  let G := restrictPresheaf R Z ⋙ sheafificationOver R Z
  let F := restrictSheaf R Z
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat RingCat))
  let : Presheaf.IsLocallyInjective J (Sheaf.commRingCatForget₂Id R) := by
    change Presheaf.IsLocallyInjective _ (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : Presheaf.IsLocallySurjective J (Sheaf.commRingCatForget₂Id R) := by
    change Presheaf.IsLocallySurjective _ (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : Localization.Lifting L W G F := ⟨(commIso R Z).symm⟩
  let : (commIso R Z).symm.hom.IsMonoidal := Localization.Monoidal.lifting_isMonoidal L W F G
  exact inferInstanceAs ((commIso R Z).symm.inv.IsMonoidal)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, with the base underlying-ring
comparison. For `W∈C`, assume weak additive sheafification, monoidal `W`-equivalences,
locally-bijective comparison, and the underlying-ring comparison on `J.over W`. The category
`SheafOfModules((sheafComposeRing ℛ).over W)` has the monoidal structure obtained by
sheafifying the pointwise module-presheaf tensor product on that slice. -/
private instance overModuleMonoidal (W : C)
    [((J.over W).W (A := Ab.{u})).IsMonoidal] [(J.over W).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over W) Ab.{u}]
    [(J.over W).HasSheafCompose (forget₂ CommRingCat RingCat)] :
    MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over W)) :=
  SheafOfModules.monoidalCategory (ℛ.over W)

attribute [-instance] overModuleMonoidal
attribute [local instance] overModuleMonoidal

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u` and `W∈C`. Assume weak additive
sheafification, monoidality of `(J.over W).W`, and the locally-bijective and underlying-ring
comparisons on that slice. Then `sheafificationBase (ℛ.over W)` is monoidal, from module
presheaves over the restricted commutative ring presheaf to module sheaves over its underlying
ring sheaf. -/
private instance overSheafificationMonoidal (W : C)
    [((J.over W).W (A := Ab.{u})).IsMonoidal] [(J.over W).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over W) Ab.{u}]
    [(J.over W).HasSheafCompose (forget₂ CommRingCat RingCat)] :
    (sheafificationBase (ℛ.over W)).Monoidal :=
  SheafOfModules.sheafificationCommIdMonoidal (ℛ.over W)

attribute [-instance] overSheafificationMonoidal
attribute [local instance] overSheafificationMonoidal

attribute [local instance] overMapPresheafMonoidal overMapMonoidal

variable {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, and assume the base
underlying-ring comparison. On both slices assume weak additive sheafification, monoidal `W`,
and locally-bijective and underlying-ring comparisons. The composite `L_U ⋙ F_h` is monoidal,
where `L_U=sheafificationBase (ℛ.over U)` and `F_h=overMap ℛ_ring h`. -/
private instance overMapAfterSheafificationMonoidal :
    (sheafificationBase (ℛ.over U) ⋙ SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal :=
  @Functor.Monoidal.instComp
    (PresheafOfModulesOfCommRing (ℛ.over U).obj) _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
    (SheafOfModules ((sheafComposeRing ℛ).over U)) _ (SheafOfModules.monoidalCategory (ℛ.over U))
    (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
    (sheafificationBase (ℛ.over U)) (SheafOfModules.overMap (sheafComposeRing ℛ) h)
    (SheafOfModules.sheafificationCommIdMonoidal (ℛ.over U)) (overMapMonoidal ℛ h)

attribute [-instance] overMapAfterSheafificationMonoidal
attribute [local instance] overMapAfterSheafificationMonoidal

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u` and `h : V → U`. With weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
target slice, `overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V)` is monoidal. Its structure
is the composite of pointwise presheaf restriction and target monoidal sheafification. -/
private instance sheafificationAfterOverMapMonoidal :
    (overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V)).Monoidal :=
  @Functor.Monoidal.instComp
    (PresheafOfModulesOfCommRing (ℛ.over U).obj) _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
    (PresheafOfModulesOfCommRing (ℛ.over V).obj) _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over V).obj))
    (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
    (overMapPresheaf ℛ h) (sheafificationBase (ℛ.over V))
    (overMapPresheafMonoidal ℛ h) (SheafOfModules.sheafificationCommIdMonoidal (ℛ.over V))

attribute [-instance] sheafificationAfterOverMapMonoidal
attribute [local instance] sheafificationAfterOverMapMonoidal

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] in
/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, and assume the base
ring comparison and weak additive sheafification, monoidal `W`, and locally-bijective and
underlying-ring comparisons on both slices. The forward transformation of
`overMapSheafificationIso ℛ h : P_h ⋙ L_V ≅ L_U ⋙ F_h` is monoidal, respecting unit and tensor
comparisons of the two composite functors. -/
private theorem overMapSheafificationIso_isMonoidal :
    @NatTrans.IsMonoidal (PresheafOfModulesOfCommRing (ℛ.over U).obj) _
      (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
      (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
      (overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V))
      (sheafificationBase (ℛ.over U) ⋙ SheafOfModules.overMap (sheafComposeRing ℛ) h)
      (overMapSheafificationIso ℛ h).hom
      (sheafificationAfterOverMapMonoidal ℛ h).toLaxMonoidal
      (overMapAfterSheafificationMonoidal ℛ h).toLaxMonoidal := by
  let : MonoidalCategory (SheafOfModules (sheafComposeRing (ℛ.over U))) :=
    SheafOfModules.monoidalCategory (ℛ.over U)
  let : MonoidalCategory (SheafOfModules (sheafComposeRing (ℛ.over V))) :=
    SheafOfModules.monoidalCategory (ℛ.over V)
  let : (sheafificationBase (ℛ.over U) ⋙ SheafOfModules.overMap (sheafComposeRing ℛ) h).LaxMonoidal :=
    (overMapAfterSheafificationMonoidal ℛ h).toLaxMonoidal
  let : (overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V)).LaxMonoidal :=
    (sheafificationAfterOverMapMonoidal ℛ h).toLaxMonoidal
  let : (sheafificationBase (ℛ.over U) ⋙ SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal :=
    overMapAfterSheafificationMonoidal ℛ h
  let : (overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V)).Monoidal :=
    sheafificationAfterOverMapMonoidal ℛ h
  let L := sheafificationBase (ℛ.over U)
  let G : PresheafOfModulesOfCommRing (ℛ.over U).obj ⥤
      SheafOfModules ((sheafComposeRing ℛ).over V) := overMapPresheaf ℛ h ⋙ sheafificationBase (ℛ.over V)
  let F : SheafOfModules ((sheafComposeRing ℛ).over U) ⥤
      SheafOfModules ((sheafComposeRing ℛ).over V) := SheafOfModules.overMap (sheafComposeRing ℛ) h
  let : G.Monoidal := sheafificationAfterOverMapMonoidal ℛ h
  let W := (J.over U).W.inverseImage
    (PresheafOfModules.toPresheaf ((ℛ.over U).obj ⋙ forget₂ CommRingCat RingCat))
  let : Presheaf.IsLocallyInjective (J.over U)
      (Sheaf.commRingCatForget₂Id (ℛ.over U)) := by
    change Presheaf.IsLocallyInjective _ (𝟙 ((ℛ.over U).obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : Presheaf.IsLocallySurjective (J.over U)
      (Sheaf.commRingCatForget₂Id (ℛ.over U)) := by
    change Presheaf.IsLocallySurjective _ (𝟙 ((ℛ.over U).obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : Localization.Lifting L W G F := ⟨(overMapSheafificationIso ℛ h).symm⟩
  exact @Iso.instIsMonoidalInvFunctor
    (PresheafOfModulesOfCommRing (ℛ.over U).obj) _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
    (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
    (L ⋙ F) G (overMapAfterSheafificationMonoidal ℛ h).toLaxMonoidal
    (sheafificationAfterOverMapMonoidal ℛ h).toLaxMonoidal (overMapSheafificationIso ℛ h).symm
    (@Localization.Monoidal.lifting_isMonoidal
      (PresheafOfModulesOfCommRing (ℛ.over U).obj)
      (SheafOfModules ((sheafComposeRing ℛ).over U)) (SheafOfModules ((sheafComposeRing ℛ).over V)) _ _ _
      (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
      (SheafOfModules.monoidalCategory (ℛ.over U)) (SheafOfModules.monoidalCategory (ℛ.over V))
      L W
      (PresheafOfModules.instIsLocalizationSheafOfModulesSheafificationInverseImageFunctorOppositeAbWToPresheaf
        (Sheaf.commRingCatForget₂Id (ℛ.over U)))
      (SheafOfModules.sheafificationCommIdMonoidal (ℛ.over U)) F G
      (sheafificationAfterOverMapMonoidal ℛ h) _ ⟨(overMapSheafificationIso ℛ h).symm⟩)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

/-- Let `C,C₁,C₂,D,D₁,D₂` be monoidal categories of common object universe `u` and morphism universe `v`. Give monoidal functors `L,L₁,L₂`, `P,Q,P'`, `O,S,O'` with types `L:C→D`, `L_i:C_i→D_i`, `P:C→C₁`, `Q:C₁→C₂`, `P':C→C₂`, `O:D→D₁`, `S:D₁→D₂`, `O':D→D₂`, and assume `L` essentially surjective. Give monoidal natural isomorphisms `c:P⋙L₁≅L⋙O`, `d:Q⋙L₂≅L₁⋙S`, `e:P'⋙L₂≅L⋙O'`, `η:P⋙Q≅P'`, and an isomorphism `γ:O⋙S≅O'`. Form
`Φ = isoWhiskerRight c.symm S ≪≫ assoc(P,L₁,S) ≪≫ isoWhiskerLeft P d.symm ≪≫ assoc(P,Q,L₂).symm ≪≫ isoWhiskerRight η L₂ ≪≫ e`.
If `Φ.hom = assoc(L,O,S).hom ≫ Functor.whiskerLeft L γ.hom`, then `γ.hom` is monoidal. -/
private theorem restrictionComparison_isMonoidal
    {C C₁ C₂ D D₁ D₂ : Type u}
    [Category.{v} C] [Category.{v} C₁] [Category.{v} C₂]
    [Category.{v} D] [Category.{v} D₁] [Category.{v} D₂]
    [MonoidalCategory C] [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory D] [MonoidalCategory D₁] [MonoidalCategory D₂]
    {L : C ⥤ D} {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    {P : C ⥤ C₁} {Q : C₁ ⥤ C₂} {P' : C ⥤ C₂}
    {O : D ⥤ D₁} {S : D₁ ⥤ D₂} {O' : D ⥤ D₂}
    [L.Monoidal] [L₁.Monoidal] [L₂.Monoidal] [L.EssSurj]
    [P.Monoidal] [Q.Monoidal] [P'.Monoidal] [O.Monoidal] [S.Monoidal] [O'.Monoidal]
    (c : P ⋙ L₁ ≅ L ⋙ O) (d : Q ⋙ L₂ ≅ L₁ ⋙ S) (e : P' ⋙ L₂ ≅ L ⋙ O')
    (η : P ⋙ Q ≅ P') (γ : O ⋙ S ≅ O')
    [c.hom.IsMonoidal] [d.hom.IsMonoidal] [e.hom.IsMonoidal] [η.hom.IsMonoidal]
    (h : (Functor.isoWhiskerRight c.symm S ≪≫ Functor.associator P L₁ S ≪≫
        Functor.isoWhiskerLeft P d.symm ≪≫ (Functor.associator P Q L₂).symm ≪≫
        Functor.isoWhiskerRight η L₂ ≪≫ e).hom =
      (Functor.associator L O S).hom ≫ Functor.whiskerLeft L γ.hom) : γ.hom.IsMonoidal := by
  let σ := Functor.isoWhiskerRight c.symm S ≪≫ Functor.associator P L₁ S ≪≫
    Functor.isoWhiskerLeft P d.symm ≪≫ (Functor.associator P Q L₂).symm ≪≫
    Functor.isoWhiskerRight η L₂ ≪≫ e
  let : σ.hom.IsMonoidal := by
    simp only [σ, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom]
    infer_instance
  have ht : Functor.whiskerLeft L γ.hom = (Functor.associator L O S).inv ≫ σ.hom := by
    rw [h, Iso.inv_hom_id_assoc]
  let : (Functor.whiskerLeft L γ.hom).IsMonoidal := by
    rw [ht]
    infer_instance
  exact isMonoidal_of_whiskerLeft L γ.hom

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Let `(C,J)` be a site at universe `u` and `ℛ : Sheaf J CommRingCat.{u}`. Assume weak additive
sheafification, monoidal `J.W`, and the locally-bijective and underlying-ring sheaf
comparisons. Then `SheafOfModules(sheafComposeRing ℛ)` has the monoidal structure induced by
localization of module presheaves. -/
private instance baseModuleMonoidal : MonoidalCategory (SheafOfModules (sheafComposeRing ℛ)) :=
  SheafOfModules.monoidalCategory ℛ

attribute [-instance] baseModuleMonoidal
attribute [local instance] baseModuleMonoidal

attribute [local instance] overModuleMonoidal overMapMonoidal overMapPresheafMonoidal
attribute [local instance] overSheafificationMonoidal overMapAfterSheafificationMonoidal
attribute [local instance] sheafificationAfterOverMapMonoidal presheafOverFunctorMapCompMonoidal

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, and assume weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and slice over `W`. The functor `SheafOfModules.overFunctor ℛ_ring W` is monoidal,
identifying restriction of a tensor product with the tensor product of restrictions and
preserving the tensor unit. -/
private instance actualOverFunctorMonoidal (W : C)
    [((J.over W).W (A := Ab.{u})).IsMonoidal] [(J.over W).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over W) Ab.{u}]
    [(J.over W).HasSheafCompose (forget₂ CommRingCat RingCat)] :
    (SheafOfModules.overFunctor (sheafComposeRing ℛ) W).Monoidal := ofMonoidal ℛ W

attribute [-instance] actualOverFunctorMonoidal
attribute [local instance] actualOverFunctorMonoidal

variable {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and both slices. The composite `overFunctor ℛ_ring U ⋙ overMap ℛ_ring h` is monoidal,
using the monoidal structures of the base-to-slice and slice-to-slice restrictions. -/
private instance actualOverFunctorMapCompMonoidal :
    (SheafOfModules.overFunctor (sheafComposeRing ℛ) U ⋙ SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal :=
  @Functor.Monoidal.instComp (SheafOfModules (sheafComposeRing ℛ)) _ (SheafOfModules.monoidalCategory ℛ)
    (SheafOfModules ((sheafComposeRing ℛ).over U)) _ (SheafOfModules.monoidalCategory (ℛ.over U))
    (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
    (SheafOfModules.overFunctor (sheafComposeRing ℛ) U) (SheafOfModules.overMap (sheafComposeRing ℛ) h)
    (actualOverFunctorMonoidal ℛ U) (overMapMonoidal ℛ h)

attribute [-instance] actualOverFunctorMapCompMonoidal
attribute [local instance] actualOverFunctorMapCompMonoidal

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and both slices. The forward transformation of `overFunctorMap ℛ_ring h : F_U ⋙ F_h ≅
F_V` is monoidal for the restriction structures constructed from sheafification. -/
private theorem actualOverFunctorMap_isMonoidal :
    @NatTrans.IsMonoidal (SheafOfModules (sheafComposeRing ℛ)) _ (SheafOfModules.monoidalCategory ℛ)
      (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
      (SheafOfModules.overFunctor (sheafComposeRing ℛ) U ⋙ SheafOfModules.overMap (sheafComposeRing ℛ) h)
      (SheafOfModules.overFunctor (sheafComposeRing ℛ) V)
      (SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h).hom
      (actualOverFunctorMapCompMonoidal ℛ h).toLaxMonoidal
      (actualOverFunctorMonoidal ℛ V).toLaxMonoidal := by
  let L := sheafificationBase ℛ
  let L₁ := sheafificationBase (ℛ.over U)
  let L₂ := sheafificationBase (ℛ.over V)
  let P := restrictPresheaf ℛ U
  let Q := overMapPresheaf ℛ h
  let P' := restrictPresheaf ℛ V
  let O := restrictSheaf ℛ U
  let S := SheafOfModules.overMap (sheafComposeRing ℛ) h
  let O' := restrictSheaf ℛ V
  let c := commIso ℛ U
  let d := overMapSheafificationIso ℛ h
  let e := commIso ℛ V
  let η := presheafOverFunctorMap ℛ h
  let γ := SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h
  let : Presheaf.IsLocallyInjective J
      (Sheaf.commRingCatForget₂Id ℛ) := by
    change Presheaf.IsLocallyInjective _ (𝟙 (ℛ.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : Presheaf.IsLocallySurjective J
      (Sheaf.commRingCatForget₂Id ℛ) := by
    change Presheaf.IsLocallySurjective _ (𝟙 (ℛ.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : L.Monoidal := SheafOfModules.sheafificationCommIdMonoidal ℛ
  let : L₁.Monoidal := overSheafificationMonoidal ℛ U
  let : L₂.Monoidal := overSheafificationMonoidal ℛ V
  let : P.Monoidal := pfMonoidal ℛ U
  let : Q.Monoidal := overMapPresheafMonoidal ℛ h
  let : P'.Monoidal := pfMonoidal ℛ V
  let : O.Monoidal := actualOverFunctorMonoidal ℛ U
  let : S.Monoidal := overMapMonoidal ℛ h
  let : O'.Monoidal := actualOverFunctorMonoidal ℛ V
  let hess : L.EssSurj :=
    ⟨fun A => ⟨(forgetRestrictBase ℛ).obj A, ⟨counitIso ℛ A⟩⟩⟩
  exact @restrictionComparison_isMonoidal
    (PresheafOfModulesOfCommRing ℛ.obj)
    (PresheafOfModulesOfCommRing (ℛ.over U).obj)
    (PresheafOfModulesOfCommRing (ℛ.over V).obj)
    (SheafOfModules (sheafComposeRing ℛ)) (SheafOfModules ((sheafComposeRing ℛ).over U))
    (SheafOfModules ((sheafComposeRing ℛ).over V)) _ _ _ _ _ _
    (PresheafOfModulesOfCommRing.monoidalCategory (R := ℛ.obj))
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over U).obj))
    (PresheafOfModulesOfCommRing.monoidalCategory (R := (ℛ.over V).obj))
    (SheafOfModules.monoidalCategory ℛ)
    (SheafOfModules.monoidalCategory (ℛ.over U)) (SheafOfModules.monoidalCategory (ℛ.over V))
    L L₁ L₂ P Q P' O S O'
    (SheafOfModules.sheafificationCommIdMonoidal ℛ) (overSheafificationMonoidal ℛ U)
    (overSheafificationMonoidal ℛ V) hess (pfMonoidal ℛ U) (overMapPresheafMonoidal ℛ h)
    (pfMonoidal ℛ V) (actualOverFunctorMonoidal ℛ U) (overMapMonoidal ℛ h)
    (actualOverFunctorMonoidal ℛ V) c d e η γ
    (canonicalRestrictionCommIso_isMonoidal ℛ U) (overMapSheafificationIso_isMonoidal ℛ h)
    (canonicalRestrictionCommIso_isMonoidal ℛ V) (presheafOverFunctorMap_isMonoidal ℛ h)
    (sheafificationOverFunctorMapIso_hom ℛ h)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (Z : C)
    [((J.over Z).W (A := Ab.{u})).IsMonoidal] [(J.over Z).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over Z) Ab.{u}]
    [(J.over Z).HasSheafCompose (forget₂ CommRingCat RingCat)]

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over Z).W (A := Ab.{u})).IsMonoidal] in
/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
locally-bijective comparisons, and underlying-ring comparisons on the base and slice over `Z`.
Write `L_R,L_Z` for sheafification, `U_R,U_Z` for forgetting, `q_Z,F_Z` for presheaf/sheaf
restriction, `e` for `commIso`, and `i_A : q_Z(U_R A) ≅ U_Z(F_Z A)` for `forgetRestrictIso`.
For each module sheaf `A`, `e_{U_R A}.hom ≫ F_Z(c_A) = L_Z(i_A.hom) ≫ c^Z_{F_Z A}`, where
`c,c^Z` are the two counits. -/
private theorem restriction_commIso_counit (A : SheafOfModules (sheafComposeRing R)) :
    (commIso R Z).hom.app ((forgetRestrictBase R).obj A) ≫
        (restrictSheaf R Z).map ((sheafificationAdjBase R).counit.app A) =
      (sheafificationOver R Z).map (forgetRestrictIso R Z A).hom ≫
        (sheafificationAdjOver R Z).counit.app ((restrictSheaf R Z).obj A) := by
  let L := sheafificationBase R
  let F := forgetRestrictBase R
  let LZ := sheafificationOver R Z
  let FZ := forgetRestrictOver R Z
  let O := restrictSheaf R Z
  let P := restrictPresheaf R Z
  let ax : L ⊣ F := sheafificationAdjBase R
  let az : LZ ⊣ FZ := sheafificationAdjOver R Z
  let c : LZ.obj (P.obj (F.obj A)) ⟶ O.obj (L.obj (F.obj A)) :=
    (commIso R Z).hom.app (F.obj A)
  let a : L.obj (F.obj A) ⟶ A := ax.counit.app A
  let ρ := forgetRestrictIso R Z A
  let ρ' := forgetRestrictIso R Z (L.obj (F.obj A))
  let b : LZ.obj (P.obj (F.obj A)) ⟶ O.obj A := LZ.map ρ.hom ≫ az.counit.app (O.obj A)
  change c ≫ O.map a = b
  have hc : az.homEquiv _ _ c = P.map (ax.unit.app (F.obj A)) ≫ ρ'.hom :=
    (az.homEquiv _ _).apply_symm_apply _
  have hf : ρ'.hom ≫ FZ.map (O.map a) = P.map (F.map a) ≫ ρ.hom :=
    forgetRestrictIso_naturality R Z a
  have hb₀ : az.homEquiv (FZ.obj (O.obj A)) (O.obj A) (az.counit.app (O.obj A)) =
      𝟙 (FZ.obj (O.obj A)) :=
    (az.homEquiv_unit _ _ _).trans (az.right_triangle_components (O.obj A))
  have hb : az.homEquiv _ _ b = ρ.hom := by
    rw [Adjunction.homEquiv_naturality_left, hb₀, Category.comp_id]
  apply (az.homEquiv _ _).injective
  calc
    _ = (az.homEquiv _ _ c) ≫ FZ.map (O.map a) := az.homEquiv_naturality_right c (O.map a)
    _ = P.map (ax.unit.app (F.obj A)) ≫ P.map (F.map a) ≫ ρ.hom := by
      rw [hc, Category.assoc, hf]
    _ = P.map (𝟙 (F.obj A)) ≫ ρ.hom := by
      rw [← Functor.map_comp_assoc]
      exact congrArg (fun t => P.map t ≫ ρ.hom) (ax.right_triangle_components A)
    _ = ρ.hom := by rw [P.map_id, Category.id_comp]
    _ = _ := hb.symm

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For the localized
monoidal structure on `L_R=sheafificationBase R`, the lax unit map `ε L_R : 𝟙_Sheaf →
L_R(𝟙_Presheaf)` is the identity, because the tensor unit is chosen as that sheafified unit. -/
private theorem sheafificationBase_ε_eq_id :
    Functor.LaxMonoidal.ε (sheafificationBase R) = 𝟙 _ := rfl

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For the localized
monoidal structure on `L_R=sheafificationBase R`, the oplax unit map `η L_R : L_R(𝟙_Presheaf)
→ 𝟙_Sheaf` is the identity on the chosen tensor unit. -/
private theorem sheafificationBase_η_eq_id :
    Functor.OplaxMonoidal.η (sheafificationBase R) = 𝟙 _ := rfl

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [((J.over Z).W (A := Ab.{u})).IsMonoidal] [(J.over Z).WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify (J.over Z) Ab.{u}]
  [(J.over Z).HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- For a site `(C,J)` at universe `u`, a commutative ring sheaf `R`, and `Z∈C`, the lax-monoidal
unit map of `q_Z=restrictPresheaf R Z` is the identity. The slice's structure-module presheaf
is the precomposition of the base structure-module presheaf. -/
private theorem restrictPresheaf_ε_eq_id :
    Functor.LaxMonoidal.ε (restrictPresheaf R Z) = 𝟙 _ := rfl

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`Z`. The lax unit map of `F_Z=restrictSheaf R Z` equals `(commIso R Z).hom.app 𝟙_Presheaf`,
from the slice tensor unit to the restriction of the base tensor unit. -/
private theorem restrictSheaf_ε_eq_commIso :
    Functor.LaxMonoidal.ε (restrictSheaf R Z) =
      (commIso R Z).hom.app (𝟙_ (PresheafOfModulesOfCommRing R.obj)) := by
  let L := sheafificationBase R
  let G := restrictPresheaf R Z ⋙ sheafificationOver R Z
  let F := restrictSheaf R Z
  let W := J.W.inverseImage (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat RingCat))
  let : Presheaf.IsLocallyInjective J (Sheaf.commRingCatForget₂Id R) := by
    change Presheaf.IsLocallyInjective _ (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : Presheaf.IsLocallySurjective J (Sheaf.commRingCatForget₂Id R) := by
    change Presheaf.IsLocallySurjective _ (𝟙 (R.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  let : Localization.Lifting L W G F := ⟨(commIso R Z).symm⟩
  let B₀ : PresheafOfModulesOfCommRing R.obj := 𝟙_ _
  let B₁ : PresheafOfModulesOfCommRing (R.over Z).obj := (restrictPresheaf R Z).obj B₀
  let T₀ : SheafOfModules (sheafComposeRing R) := L.obj B₀
  let T₁ : SheafOfModules (overSheafComposeRing R Z) := (sheafificationOver R Z).obj B₁
  let c : T₁ ⟶ F.obj T₀ := (commIso R Z).hom.app B₀
  have hG : Functor.LaxMonoidal.ε G = 𝟙 T₁ := by
    change (𝟙 T₁) ≫ (sheafificationOver R Z).map (𝟙 B₁) = 𝟙 T₁
    rw [(sheafificationOver R Z).map_id B₁, Category.id_comp]
  have hmap : F.map (Functor.OplaxMonoidal.η L) = 𝟙 (F.obj T₀) := by
    change F.map (𝟙 T₀) = 𝟙 (F.obj T₀)
    exact F.map_id _
  have h := Localization.Monoidal.functorMonoidalOfComp_ε L W F G
  change Functor.LaxMonoidal.ε F = Functor.LaxMonoidal.ε G ≫ c ≫
    F.map (Functor.OplaxMonoidal.η L) at h
  change Functor.LaxMonoidal.ε F = c
  exact h.trans (by
    rw [hG, hmap]
    exact (Category.id_comp (c ≫ 𝟙 (F.obj T₀))).trans (Category.comp_id c))

/-- Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`Z`. For `F_Z=restrictSheaf R Z`, the tensor-unit/structure-module isomorphisms satisfy `ε F_Z
≫ F_Z((tensorUnitIso R).hom) = (tensorUnitIso (R.over Z)).hom`. -/
private theorem restrictSheaf_moduleUnit_ε :
    Functor.LaxMonoidal.ε (restrictSheaf R Z) ≫
        (restrictSheaf R Z).map (SheafOfModules.tensorUnitIso R).hom =
      (SheafOfModules.tensorUnitIso (R.over Z)).hom := by
  let A : SheafOfModules (sheafComposeRing R) := SheafOfModules.unit (sheafComposeRing R)
  let O := restrictSheaf R Z
  let P := restrictPresheaf R Z
  let F := forgetRestrictBase R
  let LZ := sheafificationOver R Z
  let ax := sheafificationAdjBase R
  let az := sheafificationAdjOver R Z
  rw [restrictSheaf_ε_eq_commIso]
  change (commIso R Z).hom.app (F.obj A) ≫ O.map (ax.counit.app A) = az.counit.app (O.obj A)
  have h := restriction_commIso_counit R Z A
  exact h.trans (by
    change LZ.map (𝟙 (P.obj (F.obj A))) ≫ az.counit.app (O.obj A) = az.counit.app (O.obj A)
    rw [LZ.map_id]
    exact Category.id_comp _)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

/-- Let `C,D,E` be monoidal categories of common object universe `u` and morphism universe `v`,
with monoidal functors `O:C→D`, `S:D→E`, `O':C→E`, and a monoidal natural isomorphism
`γ:O⋙S≅O'`. For `A∈C`, give morphisms `e_b:𝟙_C→A`, `e_u:𝟙_D→O(A)`, `e_v:𝟙_E→O'(A)` satisfying
`ε O ≫ O(e_b)=e_u` and `ε O' ≫ O'(e_b)=e_v`. Then `ε S ≫ S(e_u) ≫ γ_A.hom = e_v`. -/
private theorem monoidalUnitComparison_comp
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    {O : C ⥤ D} {S : D ⥤ E} {O' : C ⥤ E}
    [O.Monoidal] [S.Monoidal] [O'.Monoidal]
    (γ : O ⋙ S ≅ O') [γ.hom.IsMonoidal] (A : C)
    (eb : 𝟙_ C ⟶ A) (eu : 𝟙_ D ⟶ O.obj A) (ev : 𝟙_ E ⟶ O'.obj A)
    (hu : Functor.LaxMonoidal.ε O ≫ O.map eb = eu)
    (hv : Functor.LaxMonoidal.ε O' ≫ O'.map eb = ev) :
    Functor.LaxMonoidal.ε S ≫ S.map eu ≫ γ.hom.app A = ev := by
  have hn : S.map (O.map eb) ≫ γ.hom.app A = γ.hom.app (𝟙_ C) ≫ O'.map eb :=
    γ.hom.naturality eb
  have hunit : Functor.LaxMonoidal.ε S ≫ S.map (Functor.LaxMonoidal.ε O) ≫
      γ.hom.app (𝟙_ C) = Functor.LaxMonoidal.ε O' := by
    simpa only [Functor.LaxMonoidal.comp_ε, Category.assoc] using NatTrans.IsMonoidal.unit (τ := γ.hom)
  rw [← hu, Functor.map_comp, Category.assoc, hn]
  simpa only [Category.assoc] using (congrArg (fun t => t ≫ O'.map eb) hunit).trans hv

end

section

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.AddCommGrpCat

open SheafOfModules.RestrictSheafification

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and both slices. Put `F_h=overMap ℛ_ring h`, `t_U=tensorUnitIso (ℛ.over U)`,
`t_V=tensorUnitIso (ℛ.over V)`, and `u_h=overMapUnitIso h`. Then `ε F_h ≫ F_h(t_U.hom) ≫
u_h.hom = t_V.hom`, as maps from the slice tensor unit to its structure module. -/
private theorem actualOverMap_moduleUnit_ε :
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    letI : (SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal := overMapMonoidal ℛ h
    Functor.LaxMonoidal.ε (SheafOfModules.overMap (sheafComposeRing ℛ) h) ≫
        (SheafOfModules.overMap (sheafComposeRing ℛ) h).map (SheafOfModules.tensorUnitIso (ℛ.over U)).hom ≫
        (SheafOfModules.overMapUnitIso (R := (sheafComposeRing ℛ)) h).hom =
      (SheafOfModules.tensorUnitIso (ℛ.over V)).hom := by
  let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
    SheafOfModules.monoidalCategory (ℛ.over U)
  let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
    SheafOfModules.monoidalCategory (ℛ.over V)
  let : (SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal := overMapMonoidal ℛ h
  let Rc : Sheaf J CommRingCat.{u} := ℛ
  let R := sheafComposeRing Rc
  let CX := SheafOfModules (sheafComposeRing Rc)
  let CU := SheafOfModules (sheafComposeRing (Rc.over U))
  let CV := SheafOfModules (sheafComposeRing (Rc.over V))
  let O : CX ⥤ CU := restrictSheaf Rc U
  let S : CU ⥤ CV := SheafOfModules.overMap R h
  let O' : CX ⥤ CV := restrictSheaf Rc V
  let : O.Monoidal := ofMonoidal Rc U
  let : S.Monoidal := overMapMonoidal ℛ h
  let : O'.Monoidal := ofMonoidal Rc V
  let γ : O ⋙ S ≅ O' := SheafOfModules.overFunctorMap R h
  let A : CX := SheafOfModules.unit R
  let eb : (𝟙_ CX) ⟶ A := (SheafOfModules.tensorUnitIso Rc).hom
  let eu : 𝟙_ CU ⟶ O.obj A := (SheafOfModules.tensorUnitIso (Rc.over U)).hom
  let ev : 𝟙_ CV ⟶ O'.obj A := (SheafOfModules.tensorUnitIso (Rc.over V)).hom
  let u : S.obj (O.obj A) ⟶ O'.obj A := (SheafOfModules.overMapUnitIso (R := (sheafComposeRing ℛ)) h).hom
  have hu : Functor.LaxMonoidal.ε O ≫ O.map eb = eu := restrictSheaf_moduleUnit_ε Rc U
  have hv : Functor.LaxMonoidal.ε O' ≫ O'.map eb = ev := restrictSheaf_moduleUnit_ε Rc V
  have ha : γ.hom.app A = u := rfl
  change Functor.LaxMonoidal.ε S ≫ S.map eu ≫ u = ev
  have hc := @monoidalUnitComparison_comp CX CU CV _ _ _
    (SheafOfModules.monoidalCategory Rc) (SheafOfModules.monoidalCategory (Rc.over U))
    (SheafOfModules.monoidalCategory (Rc.over V)) O S O'
    (ofMonoidal Rc U) (overMapMonoidal ℛ h) (ofMonoidal Rc V) γ
    (actualOverFunctorMap_isMonoidal ℛ h) A eb eu ev hu hv
  exact (congrArg (fun t => Functor.LaxMonoidal.ε S ≫ S.map eu ≫ t) ha).symm.trans hc

end

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- Let `C,D` be monoidal categories of common object universe `u` and morphism universe `v`, `F,G
: C → D` monoidal functors, and `e : F ≅ G` with monoidal forward transformation. For `A,B∈C`,
the inverse tensor comparisons satisfy `δ_F(A,B) ≫ (e_A.hom ⊗ e_B.hom) = e_{A⊗B}.hom ≫
δ_G(A,B)`, where `δ` is the oplax map inverse to the monoidal tensor isomorphism. -/
private theorem monoidalNatIso_δ
    {C D : Type u} [Category.{v} C] [Category.{v} D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ≅ G) [e.hom.IsMonoidal] (A B : C) :
    δ F A B ≫ (e.hom.app A ⊗ₘ e.hom.app B) = e.hom.app (A ⊗ B) ≫ δ G A B := by
  apply (cancel_mono (μ G A B)).mp
  simp only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  rw [← NatTrans.IsMonoidal.tensor, Functor.Monoidal.δ_μ_assoc]


section OverTensorRestriction

open CategoryTheory MonoidalCategory
open SheafOfModules.RestrictSheafification


variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (ℛ : Sheaf J CommRingCat.{u})
    [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {U V : C}
    [((J.over U).W (A := Ab.{u})).IsMonoidal] [(J.over U).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over U) Ab.{u}]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
    [((J.over V).W (A := Ab.{u})).IsMonoidal] [(J.over V).WEqualsLocallyBijective Ab.{u}]
    [HasWeakSheafify (J.over V) Ab.{u}]
    [(J.over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
    (h : V ⟶ U)

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, and assume the base
underlying-ring comparison. On both slices assume weak additive sheafification, monoidal `W`,
and locally-bijective and underlying-ring comparisons. Then `overMapMonoidalStructure ℛ h`
equips `F_h=overMap ℛ_ring h` with a monoidal structure between the standard monoidal
module-sheaf categories on `U` and `V`. -/
@[no_expose, instance_reducible] def overMapMonoidalStructure :
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    (SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal := by
  letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
    SheafOfModules.monoidalCategory (ℛ.over U)
  letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
    SheafOfModules.monoidalCategory (ℛ.over V)
  exact overMapMonoidal ℛ h

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and both slices. With `F_h` equipped by `overMapMonoidalStructure ℛ h`, the forward
transformation of `overFunctorMap ℛ_ring h : F_U ⋙ F_h ≅ F_V` is monoidal, preserving the
tensor and unit comparisons of direct and successive restriction. -/
theorem overMapMonoidalStructure_restriction :
    letI : MonoidalCategory (SheafOfModules (sheafComposeRing ℛ)) := SheafOfModules.monoidalCategory ℛ
    letI : MonoidalCategory (SheafOfModules (sheafComposeRing ℛ)) :=
      SheafOfModules.monoidalCategory ℛ
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    letI : (SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal := overMapMonoidalStructure ℛ h
    letI : (SheafOfModules.overFunctor (sheafComposeRing ℛ) U).Monoidal := ofMonoidal ℛ U
    letI : (SheafOfModules.overFunctor (sheafComposeRing ℛ) V).Monoidal := ofMonoidal ℛ V
    letI : (SheafOfModules.overFunctor (sheafComposeRing ℛ) U ⋙
        SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal :=
      @Functor.Monoidal.instComp
        (SheafOfModules (sheafComposeRing ℛ)) _ (SheafOfModules.monoidalCategory ℛ)
        (SheafOfModules ((sheafComposeRing ℛ).over U)) _ (SheafOfModules.monoidalCategory (ℛ.over U))
        (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
        (SheafOfModules.overFunctor (sheafComposeRing ℛ) U) (SheafOfModules.overMap (sheafComposeRing ℛ) h)
        (ofMonoidal ℛ U) (overMapMonoidalStructure ℛ h)
    (SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h).hom.IsMonoidal :=
  actualOverFunctorMap_isMonoidal ℛ h

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and both slices. For `F_h` with `overMapMonoidalStructure ℛ h`, let `t_U,t_V` be the
tensor-unit/structure-module isomorphisms and `u_h=overMapUnitIso h`. Then `ε F_h ≫
F_h(t_U.hom) ≫ u_h.hom = t_V.hom`. -/
theorem overMapMonoidalStructure_moduleUnit :
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    letI : (SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal := overMapMonoidalStructure ℛ h
    Functor.LaxMonoidal.ε (SheafOfModules.overMap (sheafComposeRing ℛ) h) ≫
        (SheafOfModules.overMap (sheafComposeRing ℛ) h).map (SheafOfModules.tensorUnitIso (ℛ.over U)).hom ≫
        (SheafOfModules.overMapUnitIso (R := (sheafComposeRing ℛ)) h).hom =
      (SheafOfModules.tensorUnitIso (ℛ.over V)).hom :=
  actualOverMap_moduleUnit_ε ℛ h

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, and assume the base
ring comparison and weak additive sheafification, monoidal `W`, and locally-bijective and
underlying-ring comparisons on both slices. For `M,N` over `ℛ_ring.over U`, `overMapTensorIso
ℛ h M N : F_h(M ⊗ N) ≅ F_h(M) ⊗ F_h(N)` is the inverse structural tensor isomorphism of
`F_h=overMap ℛ_ring h`. -/
def overMapTensorIso (M N : SheafOfModules ((sheafComposeRing ℛ).over U)) :
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    (SheafOfModules.overMap (sheafComposeRing ℛ) h).obj (M ⊗ N) ≅
      (SheafOfModules.overMap (sheafComposeRing ℛ) h).obj M ⊗
        (SheafOfModules.overMap (sheafComposeRing ℛ) h).obj N := by
  letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
    SheafOfModules.monoidalCategory (ℛ.over U)
  letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
    SheafOfModules.monoidalCategory (ℛ.over V)
  letI : (SheafOfModules.overMap (sheafComposeRing ℛ) h).Monoidal := overMapMonoidalStructure ℛ h
  exact (Functor.Monoidal.μIso (SheafOfModules.overMap (sheafComposeRing ℛ) h) M N).symm

/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and both slices. For ambient module sheaves `M,N`, write `F_U,F_V` for base restrictions,
`F_h` for restriction along `h`, `γ_A : F_h(F_U A) ≅ F_V A` for `overFunctorMap`, and
`δ_U,δ_V,δ_h` for the tensor comparisons. Then `γ_{M⊗N}.hom ≫ δ_V(M,N).hom = F_h(δ_U(M,N).hom)
≫ δ_h(F_U M,F_U N).hom ≫ (γ_M.hom ⊗ γ_N.hom)`. -/
theorem overMapTensorIso_restriction (M N : (SheafOfModules (sheafComposeRing ℛ))) :
    let : MonoidalCategory (SheafOfModules (sheafComposeRing ℛ)) := SheafOfModules.monoidalCategory ℛ
  let : MonoidalCategory (SheafOfModules (sheafComposeRing ℛ)) :=
    SheafOfModules.monoidalCategory ℛ
    let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    ((SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h).app (M ⊗ N)).hom ≫
        (ofTensorIso ℛ V M N).hom =
      (SheafOfModules.overMap (sheafComposeRing ℛ) h).map (ofTensorIso ℛ U M N).hom ≫
        (overMapTensorIso ℛ h (M.over U) (N.over U)).hom ≫
        (((SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h).app M).hom ⊗ₘ
          ((SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h).app N).hom) := by
  let : MonoidalCategory (SheafOfModules (sheafComposeRing ℛ)) := SheafOfModules.monoidalCategory ℛ
  let : MonoidalCategory (SheafOfModules (sheafComposeRing ℛ)) :=
    SheafOfModules.monoidalCategory ℛ
  let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
    SheafOfModules.monoidalCategory (ℛ.over U)
  let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
    SheafOfModules.monoidalCategory (ℛ.over V)
  let F := SheafOfModules.overFunctor (sheafComposeRing ℛ) U
  let G := SheafOfModules.overMap (sheafComposeRing ℛ) h
  let H := SheafOfModules.overFunctor (sheafComposeRing ℛ) V
  let : F.Monoidal := ofMonoidal ℛ U
  let : G.Monoidal := overMapMonoidalStructure ℛ h
  let : H.Monoidal := ofMonoidal ℛ V
  let sMono : (F ⋙ G).Monoidal :=
    @Functor.Monoidal.instComp
        (SheafOfModules (sheafComposeRing ℛ)) _ (SheafOfModules.monoidalCategory ℛ)
        (SheafOfModules ((sheafComposeRing ℛ).over U)) _ (SheafOfModules.monoidalCategory (ℛ.over U))
        (SheafOfModules ((sheafComposeRing ℛ).over V)) _ (SheafOfModules.monoidalCategory (ℛ.over V))
        (SheafOfModules.overFunctor (sheafComposeRing ℛ) U) (SheafOfModules.overMap (sheafComposeRing ℛ) h)
        (ofMonoidal ℛ U) (overMapMonoidalStructure ℛ h)
  let e := SheafOfModules.overFunctorMap (sheafComposeRing ℛ) h
  let : e.hom.IsMonoidal := overMapMonoidalStructure_restriction ℛ h
  have hc := (@monoidalNatIso_δ
    (SheafOfModules (sheafComposeRing ℛ)) (SheafOfModules ((sheafComposeRing ℛ).over V))
    _ _ (SheafOfModules.monoidalCategory ℛ)
    (SheafOfModules.monoidalCategory (ℛ.over V))
    (F ⋙ G) H sMono (ofMonoidal ℛ V) e
    (overMapMonoidalStructure_restriction ℛ h) M N).symm
  change e.hom.app (M ⊗ N) ≫ Functor.OplaxMonoidal.δ H M N =
    G.map (Functor.OplaxMonoidal.δ F M N) ≫
      Functor.OplaxMonoidal.δ G (F.obj M) (F.obj N) ≫ (e.hom.app M ⊗ₘ e.hom.app N)
  calc
    _ = Functor.OplaxMonoidal.δ (F ⋙ G) M N ≫ (e.hom.app M ⊗ₘ e.hom.app N) := hc
    _ = _ := by rw [Functor.OplaxMonoidal.comp_δ F G M N, Category.assoc]

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] in
/-- Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with the base
underlying-ring comparison and weak additive sheafification, monoidal `W`, and
locally-bijective and underlying-ring comparisons on both slices. For module sheaves
`M,N,M',N'` over `U`, maps `a : M → M'`, `b : N → N'`, and `F_h=overMap ℛ_ring h`, `F_h(a ⊗ b)
≫ δ_h(M',N').hom = δ_h(M,N).hom ≫ (F_h(a) ⊗ F_h(b))`, where `δ_h=overMapTensorIso ℛ h`. -/
theorem overMapTensorIso_naturality
    (M N M' N' : SheafOfModules ((sheafComposeRing ℛ).over U)) (a : M ⟶ M') (b : N ⟶ N') :
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
      SheafOfModules.monoidalCategory (ℛ.over U)
    letI : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
      SheafOfModules.monoidalCategory (ℛ.over V)
    (SheafOfModules.overMap (sheafComposeRing ℛ) h).map (a ⊗ₘ b) ≫ (overMapTensorIso ℛ h M' N').hom =
      (overMapTensorIso ℛ h M N).hom ≫
        ((SheafOfModules.overMap (sheafComposeRing ℛ) h).map a ⊗ₘ
          (SheafOfModules.overMap (sheafComposeRing ℛ) h).map b) := by
  let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over U)) :=
    SheafOfModules.monoidalCategory (ℛ.over U)
  let : MonoidalCategory (SheafOfModules ((sheafComposeRing ℛ).over V)) :=
    SheafOfModules.monoidalCategory (ℛ.over V)
  let G := SheafOfModules.overMap (sheafComposeRing ℛ) h
  let : G.Monoidal := overMapMonoidalStructure ℛ h
  change G.map (a ⊗ₘ b) ≫ Functor.OplaxMonoidal.δ G M' N' =
    Functor.OplaxMonoidal.δ G M N ≫ (G.map a ⊗ₘ G.map b)
  exact (Functor.OplaxMonoidal.δ_natural G a b).symm

end OverTensorRestriction

end SheafOfModules.OverMonoidal
