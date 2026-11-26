/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.HorseshoeBoundaryChoice
public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeSplitCoordinates

/-!
# Augmentation and connecting naturality of projective-preserving source change

For additive homology- and projective-preserving `U : C → D` between
abelian categories with projective resolutions, and additive
`L : D → E` into an abelian category, the comparison
`L_n(U ⋙ L) ≅ U ⋙ L_nL` preserves degree-zero augmentations and
left-derived connecting maps. Mapping projective resolutions and
horseshoe endpoint coordinates supplies the corresponding diagrams.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]

namespace ProjectiveResolution

/-- Let `C,D` be abelian, `U : C → D` additive and preserving
projectives and homology, and `P` a projective resolution of `X`.
The degree-zero augmentation of the mapped resolution `U(P)` is
`U(π_P,₀)`. -/
theorem mapProjectiveResolution_π_f_zero
    (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
    {X : C} (P : ProjectiveResolution X) :
    (U.mapProjectiveResolution P).π.f 0 = U.map (P.π.f 0) := by
  change U.map (P.π.f 0) ≫
      ((HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.down ℕ) 0).hom.app X).f 0 = _
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  change U.map (P.π.f 0) ≫ U.map (𝟙 X) ≫ 𝟙 (U.obj X) = U.map (P.π.f 0)
  erw [Functor.map_id, Category.comp_id, Category.comp_id]

/-- Let `C,D,E` be abelian, `U : C → D` additive and preserving
projectives and homology, `L : D → E` additive, and `P` a projective
resolution of `X`. The complex-composition identification carries
the opcycles augmentation of `L(U(P))` to that of `(U ⋙ L)(P)`. -/
theorem mapCompositionOpcycles_comp_fromLeftDerivedZero'
    (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
    (L : D ⥤ E) [L.Additive] {X : C} (P : ProjectiveResolution X) :
    HomologicalComplex.opcyclesMap
        ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
          (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).inv.app P.complex) 0 ≫
      (U.mapProjectiveResolution P).fromLeftDerivedZero' L =
        P.fromLeftDerivedZero' (U ⋙ L) := by
  let Q := U.mapProjectiveResolution P
  let K := ((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let K' := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let φ : K ⟶ K' := (Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).inv.app P.complex
  change HomologicalComplex.opcyclesMap φ 0 ≫ Q.fromLeftDerivedZero' L = _
  apply (cancel_epi (HomologicalComplex.pOpcycles K 0)).1
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  change (𝟙 _) ≫ L.map (Q.π.f 0) = L.map (U.map (P.π.f 0))
  rw [Category.id_comp, mapProjectiveResolution_π_f_zero U P]
  rfl

end ProjectiveResolution

namespace Functor

variable [HasProjectiveResolutions C] [HasProjectiveResolutions D]

/-- Let `C,D,E` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
and `L : D → E` additive. The forward degree-zero precomposition comparison followed
by the augmentation `U ⋙ L₀L → U ⋙ L` equals the augmentation
of `L₀(U ⋙ L)`. -/
@[reassoc]
theorem leftDerivedPrecompIso_hom_fromLeftDerivedZero
    (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
    (L : D ⥤ E) [L.Additive] :
    (leftDerivedPrecompIso U L 0).hom ≫ whiskerLeft U L.fromLeftDerivedZero =
      (U ⋙ L).fromLeftDerivedZero := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let Q := U.mapProjectiveResolution P
  let K := ((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let K' := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let φ : K ⟶ K' := (Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).inv.app P.complex
  have hAug : HomologicalComplex.opcyclesMap φ 0 ≫ Q.fromLeftDerivedZero' L =
      P.fromLeftDerivedZero' (U ⋙ L) :=
    ProjectiveResolution.mapCompositionOpcycles_comp_fromLeftDerivedZero' U L P
  let a := P.isoLeftDerivedObj (U ⋙ L) 0
  let c := Q.isoLeftDerivedObj L 0
  let i := (ChainComplex.isoHomologyι₀ K).hom
  let i' := (ChainComplex.isoHomologyι₀ K').hom
  have hCore : HomologicalComplex.homologyMap φ 0 ≫ i' ≫ Q.fromLeftDerivedZero' L =
      i ≫ P.fromLeftDerivedZero' (U ⋙ L) := by
    change HomologicalComplex.homologyMap φ 0 ≫ K'.homologyι 0 ≫
      Q.fromLeftDerivedZero' L = K.homologyι 0 ≫ P.fromLeftDerivedZero' (U ⋙ L)
    rw [HomologicalComplex.homologyι_naturality_assoc, hAug]
  have hτ : (leftDerivedPrecompIso U L 0).hom.app X =
      a.hom ≫ HomologicalComplex.homologyMap φ 0 ≫ c.inv :=
    leftDerivedPrecompIso_hom_app U L 0 P
  have hAugQ : L.fromLeftDerivedZero.app (U.obj X) = c.hom ≫ i' ≫ Q.fromLeftDerivedZero' L :=
    Q.fromLeftDerivedZero_eq L
  have hAugP : (U ⋙ L).fromLeftDerivedZero.app X = a.hom ≫ i ≫
      P.fromLeftDerivedZero' (U ⋙ L) := P.fromLeftDerivedZero_eq (U ⋙ L)
  have cancelTriple {W X Y Z V : E} (f : W ⟶ X) (g : X ⟶ Y)
      (e : Z ≅ Y) (h : Y ⟶ V) :
      (f ≫ g ≫ e.inv) ≫ (e.hom ≫ h) = f ≫ (g ≫ h) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [NatTrans.comp_app, whiskerLeft_app]
  calc
    (leftDerivedPrecompIso U L 0).hom.app X ≫ L.fromLeftDerivedZero.app (U.obj X) =
        (a.hom ≫ HomologicalComplex.homologyMap φ 0 ≫ c.inv) ≫
          (c.hom ≫ i' ≫ Q.fromLeftDerivedZero' L) :=
      congrArg₂ (fun f g => f ≫ g) hτ hAugQ
    _ = a.hom ≫ (HomologicalComplex.homologyMap φ 0 ≫ i' ≫ Q.fromLeftDerivedZero' L) :=
      cancelTriple a.hom (HomologicalComplex.homologyMap φ 0) c
        (i' ≫ Q.fromLeftDerivedZero' L)
    _ = a.hom ≫ (i ≫ P.fromLeftDerivedZero' (U ⋙ L)) :=
      congrArg (fun f => a.hom ≫ f) hCore
    _ = (U ⋙ L).fromLeftDerivedZero.app X := hAugP.symm

/-- Let `C,D,E` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
and `L : D → E` additive. The inverse degree-zero precomposition comparison followed
by the augmentation of `L₀(U ⋙ L)` equals
`U ⋙ L₀L → U ⋙ L`. -/
@[reassoc]
theorem leftDerivedPrecompIso_inv_fromLeftDerivedZero
    (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
    (L : D ⥤ E) [L.Additive] :
    (leftDerivedPrecompIso U L 0).inv ≫ (U ⋙ L).fromLeftDerivedZero =
      whiskerLeft U L.fromLeftDerivedZero := by
  have h := leftDerivedPrecompIso_hom_fromLeftDerivedZero U L
  calc
    (leftDerivedPrecompIso U L 0).inv ≫ (U ⋙ L).fromLeftDerivedZero =
        (leftDerivedPrecompIso U L 0).inv ≫
          ((leftDerivedPrecompIso U L 0).hom ≫ whiskerLeft U L.fromLeftDerivedZero) :=
      congrArg (fun f => (leftDerivedPrecompIso U L 0).inv ≫ f) h.symm
    _ = _ := (leftDerivedPrecompIso U L 0).inv_hom_id_assoc _

end Functor
end CategoryTheory

namespace CategoryTheory.ProjectiveResolution.HorseshoeData

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {S : ShortComplex C} {hS : S.ShortExact}
  {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be short
exact, `P₁,P₃` endpoint projective resolutions, and `H` horseshoe data
with middle resolution `P₂`. Its inclusion `P₁ → P₂`, together with its augmentation
square, is a map of projective resolutions lifting `S.f`. -/
def inclusionResolutionHom (H : HorseshoeData hS P₁ P₃) :
    ProjectiveResolution.Hom P₁ H.middle S.f where
  hom := H.i
  hom_f_zero_comp_π_f_zero := by
    simpa only [HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom H.i_augmentation 0

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be short
exact, `P₁,P₃` endpoint projective resolutions, and `H` horseshoe data
with middle resolution `P₂`. Its projection `P₂ → P₃`, together with its augmentation
square, is a map of projective resolutions lifting `S.g`. -/
def projectionResolutionHom (H : HorseshoeData hS P₁ P₃) :
    ProjectiveResolution.Hom H.middle P₃ S.g where
  hom := H.p
  hom_f_zero_comp_π_f_zero := by
    simpa only [HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom H.p_augmentation 0

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be short
exact, `P₁,P₃` endpoint projective resolutions, and `H` horseshoe data
with middle resolution `P₂`. An endpoint coordinate specification gives a splitting
of the resolution row `P₁,n → P₂,n → P₃,n` in every degree `n`. -/
def degreeSplitting (H : HorseshoeData hS P₁ P₃) (sH : H.Spec) (n : ℕ) :
    (ShortComplex.mk (H.i.f n) (H.p.f n)
      (HomologicalComplex.congr_hom H.zero n)).Splitting := by
  let e : ShortComplex.mk
        (biprod.inl : P₁.complex.X n ⟶ P₁.complex.X n ⊞ P₃.complex.X n)
        biprod.snd biprod.inl_snd ≅
      ShortComplex.mk (H.i.f n) (H.p.f n) (HomologicalComplex.congr_hom H.zero n) :=
    ShortComplex.isoMk (Iso.refl _) (sH.middleXIso n).symm (Iso.refl _)
      (by
        simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
        exact (Iso.eq_comp_inv (sH.middleXIso n)).mpr (sH.i_f n))
      (by
        simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using sH.p_f n)
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct
    (P₁.complex.X n) (P₃.complex.X n)).ofIso e

section Map

variable (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects]
  [U.PreservesHomology]

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be short
exact, `P₁,P₃` endpoint projective resolutions, and `H` horseshoe data
with middle resolution `P₂`. For abelian `D` and additive homology- and projective-preserving
`U : C → D`, mapping resolutions and the row splittings gives
horseshoe data for the short exact sequence `U(S)`. -/
def map (H : HorseshoeData hS P₁ P₃) (sH : H.Spec) :
    HorseshoeData (S := S.map U) (by
        let : PreservesFiniteLimits U := Functor.preservesFiniteLimits_of_preservesHomology U
        let : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesHomology U
        exact hS.map_of_exact U)
      (U.mapProjectiveResolution P₁) (U.mapProjectiveResolution P₃) where
  middle := U.mapProjectiveResolution H.middle
  i := (U.mapProjectiveResolutionHom (inclusionResolutionHom H)).hom
  p := (U.mapProjectiveResolutionHom (projectionResolutionHom H)).hom
  zero := by
    change (U.mapHomologicalComplex (ComplexShape.down ℕ)).map H.i ≫
        (U.mapHomologicalComplex (ComplexShape.down ℕ)).map H.p = 0
    rw [← Functor.map_comp, H.zero, Functor.map_zero]
  shortExact := H.mapped_shortExact sH U
  i_augmentation := (U.mapProjectiveResolutionHom (inclusionResolutionHom H)).hom_comp_π
  p_augmentation := (U.mapProjectiveResolutionHom (projectionResolutionHom H)).hom_comp_π

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be short
exact, `P₁,P₃` endpoint projective resolutions, and `H` horseshoe data
with middle resolution `P₂`. For abelian `D` and additive homology- and projective-preserving
`U : C → D`, the mapped row splittings give the endpoint coordinate
specification of the mapped horseshoe data. -/
def mapSpec (H : HorseshoeData hS P₁ P₃) (sH : H.Spec) :
    (map U H sH).Spec :=
  (map U H sH).specOfSplittings (fun n => by
    change ((ShortComplex.mk (H.i.f n) (H.p.f n)
      (HomologicalComplex.congr_hom H.zero n)).map U).Splitting
    exact (H.degreeSplitting sH n).map U)

end Map
end CategoryTheory.ProjectiveResolution.HorseshoeData

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasProjectiveResolutions D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]

/-- Let `C,D,E` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
and `L : D → E` additive. For short exact `S`, the forward comparisons in degrees
`n+1,n` satisfy `e_(n+1),X₃ ≫ δ_L,n(U(S)) = δ_(U⋙L),n ≫ e_n,X₁`. -/
@[reassoc]
theorem leftDerivedPrecompIso_hom_LDdelta
    (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
    (L : D ⥤ E) [L.Additive] (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    (leftDerivedPrecompIso U L (n + 1)).hom.app S.X₃ ≫
        LeftDerivedDelta.LDdelta L n (S.map U) (by
        let : PreservesFiniteLimits U := Functor.preservesFiniteLimits_of_preservesHomology U
        let : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesHomology U
        exact hS.map_of_exact U) =
      LeftDerivedDelta.LDdelta (U ⋙ L) n S hS ≫
        (leftDerivedPrecompIso U L n).hom.app S.X₁ := by
  let P₁ := projectiveResolution S.X₁
  let P₃ := projectiveResolution S.X₃
  let H := ProjectiveResolution.horseshoe hS P₁ P₃
  let sH := ProjectiveResolution.horseshoe_spec hS P₁ P₃
  let HU := ProjectiveResolution.HorseshoeData.map U H sH
  let sHU := ProjectiveResolution.HorseshoeData.mapSpec U H sH
  let hSU := by
    letI : PreservesFiniteLimits U := Functor.preservesFiniteLimits_of_preservesHomology U
    letI : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesHomology U
    exact hS.map_of_exact U
  let hLow := H.mapped_shortExact sH (U ⋙ L)
  let hHigh := HU.mapped_shortExact sHU L
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)
  let φ : H.mapped (U ⋙ L) ⟶ HU.mapped L :=
    (ShortComplex.mk H.i H.p H.zero).mapNatTrans χ.inv
  let a₃ := P₃.isoLeftDerivedObj (U ⋙ L) (n + 1)
  let a₁ := P₁.isoLeftDerivedObj (U ⋙ L) n
  let c₃ := (U.mapProjectiveResolution P₃).isoLeftDerivedObj L (n + 1)
  let c₁ := (U.mapProjectiveResolution P₁).isoLeftDerivedObj L n
  let b₃ := HomologicalComplex.homologyMap (χ.inv.app P₃.complex) (n + 1)
  let b₁ := HomologicalComplex.homologyMap (χ.inv.app P₁.complex) n
  let dLow := hLow.δ (n + 1) n (ComplexShape.down_mk _ _ rfl)
  let dHigh := hHigh.δ (n + 1) n (ComplexShape.down_mk _ _ rfl)
  have hMiddle : dLow ≫ b₁ = b₃ ≫ dHigh :=
    HomologicalComplex.HomologySequence.δ_naturality φ hLow hHigh
      (n + 1) n (ComplexShape.down_mk _ _ rfl)
  have hNativeLow : LeftDerivedDelta.LDdelta (U ⋙ L) n S hS =
      a₃.hom ≫ dLow ≫ a₁.inv :=
    (H.delta_eq_native sH (U ⋙ L) n).symm
  have hNativeHigh : LeftDerivedDelta.LDdelta L n (S.map U) hSU =
      c₃.hom ≫ dHigh ≫ c₁.inv :=
    (HU.delta_eq_native sHU L n).symm
  have hτ₃ : (leftDerivedPrecompIso U L (n + 1)).hom.app S.X₃ =
      a₃.hom ≫ b₃ ≫ c₃.inv :=
    leftDerivedPrecompIso_hom_app U L (n + 1) P₃
  have hτ₁ : (leftDerivedPrecompIso U L n).hom.app S.X₁ =
      a₁.hom ≫ b₁ ≫ c₁.inv :=
    leftDerivedPrecompIso_hom_app U L n P₁
  have cancelTriple {W X Y Z V : E} (f : W ⟶ X) (g : X ⟶ Y)
      (e : Z ≅ Y) (h : Y ⟶ V) :
      (f ≫ g ≫ e.inv) ≫ (e.hom ≫ h) = f ≫ (g ≫ h) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hτ₃, hτ₁, hNativeLow, hNativeHigh]
  calc
    (a₃.hom ≫ b₃ ≫ c₃.inv) ≫ (c₃.hom ≫ dHigh ≫ c₁.inv) =
        a₃.hom ≫ (b₃ ≫ dHigh ≫ c₁.inv) :=
      cancelTriple a₃.hom b₃ c₃ (dHigh ≫ c₁.inv)
    _ = a₃.hom ≫ (dLow ≫ b₁ ≫ c₁.inv) :=
      congrArg (fun f => a₃.hom ≫ f)
        ((Category.assoc b₃ dHigh c₁.inv).symm.trans
          ((congrArg (fun f => f ≫ c₁.inv) hMiddle.symm).trans
            (Category.assoc dLow b₁ c₁.inv)))
    _ = (a₃.hom ≫ dLow ≫ a₁.inv) ≫ (a₁.hom ≫ b₁ ≫ c₁.inv) :=
      (cancelTriple a₃.hom dLow a₁ (b₁ ≫ c₁.inv)).symm

/-- Let `C,D,E` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
and `L : D → E` additive. For short exact `S`, the inverse comparisons satisfy
`e_(n+1),X₃⁻¹ ≫ δ_(U⋙L),n = δ_L,n(U(S)) ≫ e_n,X₁⁻¹`. -/
@[reassoc]
theorem leftDerivedPrecompIso_inv_LDdelta
    (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
    (L : D ⥤ E) [L.Additive] (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    (leftDerivedPrecompIso U L (n + 1)).inv.app S.X₃ ≫
        LeftDerivedDelta.LDdelta (U ⋙ L) n S hS =
      LeftDerivedDelta.LDdelta L n (S.map U) (by
        let : PreservesFiniteLimits U := Functor.preservesFiniteLimits_of_preservesHomology U
        let : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesHomology U
        exact hS.map_of_exact U) ≫
        (leftDerivedPrecompIso U L n).inv.app S.X₁ := by
  have h := leftDerivedPrecompIso_hom_LDdelta U L n S hS
  have hc := congrArg (fun f =>
    (leftDerivedPrecompIso U L (n + 1)).inv.app S.X₃ ≫ f ≫
      (leftDerivedPrecompIso U L n).inv.app S.X₁) h
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id] using hc.symm

end CategoryTheory.Functor
