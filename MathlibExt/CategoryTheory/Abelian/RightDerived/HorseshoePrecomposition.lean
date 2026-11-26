/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ConnectingNaturality
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Precomposition

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasInjectiveResolutions D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. Let `D` be abelian and `E : C → D` additive and preserving
injectives and homology. If `E(S)` is short exact, mapping the three
resolutions, cochain lifts and row splittings gives compatible
horseshoe data for `E(S)`. -/
def HorseshoeData.mapExact {S : ShortComplex C} {hS : S.ShortExact}
    (H : HorseshoeData S hS) (E : C ⥤ D) [E.Additive]
    [E.PreservesInjectiveObjects] [E.PreservesHomology]
    (hES : (S.map E).ShortExact) : HorseshoeData (S.map E) hES where
  res₁ := E.mapInjectiveResolution H.res₁
  res₂ := E.mapInjectiveResolution H.res₂
  res₃ := E.mapInjectiveResolution H.res₃
  φf := (E.mapInjectiveResolutionHom
    (InjectiveResolution.Hom.mk (f := S.f) H.φf
      (H.lift_f.trans (congrArg (· ≫ H.res₂.ι.f 0)
        (CochainComplex.single₀_map_f_zero S.f).symm)))).hom
  φg := (E.mapInjectiveResolutionHom
    (InjectiveResolution.Hom.mk (f := S.g) H.φg
      (H.lift_g.trans (congrArg (· ≫ H.res₃.ι.f 0)
        (CochainComplex.single₀_map_f_zero S.g).symm)))).hom
  w := by
    change (E.mapHomologicalComplex (ComplexShape.up ℕ)).map H.φf ≫
      (E.mapHomologicalComplex (ComplexShape.up ℕ)).map H.φg = 0
    rw [← Functor.map_comp, H.w, Functor.map_zero]
  lift_f := by
    simpa only [CochainComplex.single₀_map_f_zero, ShortComplex.map_X₁, ShortComplex.map_X₂,
      ShortComplex.map_f, ShortComplex.map_g] using (E.mapInjectiveResolutionHom
    (InjectiveResolution.Hom.mk (f := S.f) H.φf
      (H.lift_f.trans (congrArg (· ≫ H.res₂.ι.f 0)
        (CochainComplex.single₀_map_f_zero S.f).symm)))).ι_f_zero_comp_hom_f_zero
  lift_g := by
    simpa only [CochainComplex.single₀_map_f_zero, ShortComplex.map_X₁, ShortComplex.map_X₂,
      ShortComplex.map_f, ShortComplex.map_g] using (E.mapInjectiveResolutionHom
    (InjectiveResolution.Hom.mk (f := S.g) H.φg
      (H.lift_g.trans (congrArg (· ≫ H.res₃.ι.f 0)
        (CochainComplex.single₀_map_f_zero S.g).symm)))).ι_f_zero_comp_hom_f_zero
  split n := by
    change ((H.diagram.map (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).map E).Splitting
    exact (H.split n).map E


end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u''} [Category.{v''} A] [Abelian A]
variable (E : C ⥤ D) [E.Additive] [E.PreservesInjectiveObjects] [E.PreservesHomology]
variable (B : D ⥤ A) [B.Additive]

/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. Let `D,A` be abelian, `E : C → D` additive and preserving
injectives and homology, and `B : D → A` additive, with `E(S)` short
exact. The complex-composition isomorphism identifies the horseshoe
mapped by `E ⋙ B` with the mapped horseshoe for `E(S)` followed by `B`. -/
def HorseshoeData.precompMappedIso {S : ShortComplex C} {hS : S.ShortExact}
    (H : HorseshoeData S hS) (hES : (S.map E).ShortExact) :
    H.mapped (E ⋙ B) ≅ (H.mapExact E hES).mapped B :=
  H.diagram.mapNatIso
    (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ B)) (ComplexShape.up ℕ)).symm

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`. Let `C,D` admit injective resolutions, `D,A` be abelian,
`E : C → D` additive and preserving injectives and homology,
`B : D → A` additive, and `E(S)` short exact. The right-derived
precomposition comparisons commute with the boundaries of `H` and
its mapped data in degrees `n,n+1`. -/
theorem HorseshoeData.delta_precomp {S : ShortComplex C} {hS : S.ShortExact}
    (H : HorseshoeData S hS) (hES : (S.map E).ShortExact) (n : ℕ) :
    H.delta (E ⋙ B) n (n + 1) rfl ≫
        (Functor.rightDerivedPrecompIso E B (n + 1)).hom.app S.X₁ =
      (Functor.rightDerivedPrecompIso E B n).hom.app S.X₃ ≫
        (H.mapExact E hES).delta B n (n + 1) rfl := by
  let h := H.precompMappedIso E B hES
  have hd := HomologicalComplex.HomologySequence.δ_naturality h.hom
    (H.mapped_shortExact (E ⋙ B)) ((H.mapExact E hES).mapped_shortExact B)
    n (n + 1) rfl
  have hp₁ := Functor.rightDerivedPrecompIso_hom_app_eq E B (n + 1) H.res₁
  have hp₃ := Functor.rightDerivedPrecompIso_hom_app_eq E B n H.res₃
  rw [hp₁, hp₃]
  dsimp only [Functor.rightDerivedPrecompIsoWithResolution, Iso.trans_hom, Iso.symm_hom,
    HorseshoeData.delta]
  change (H.mapped_shortExact (E ⋙ B)).δ n (n + 1) rfl ≫
      (Functor.rightDerivedPrecompHomologyIso E B (n + 1) H.res₁).hom =
    (Functor.rightDerivedPrecompHomologyIso E B n H.res₃).hom ≫
      ((H.mapExact E hES).mapped_shortExact B).δ n (n + 1) rfl at hd
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((H.mapped_shortExact (E ⋙ B)).δ n (n + 1) rfl), hd]
  dsimp only [HorseshoeData.mapExact]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end CategoryTheory.Functor.RightDerived

end
