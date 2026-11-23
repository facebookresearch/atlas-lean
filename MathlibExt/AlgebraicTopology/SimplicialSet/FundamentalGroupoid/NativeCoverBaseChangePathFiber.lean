/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathHomotopyFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPSimplicialHomotopyEquiv
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathHomotopyFiberIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyFiberRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Selected native covering fibers and the fixed original Top fiber

The verified native map and the original singular-fiber comparison give a
comparison for every selected native lift. Its original source coordinate
and entire path are retained, with the original topological fiber unchanged.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet.KanComplex

/-- The actual covering pullback projects to the same original ending-path fiber. -/
noncomputable def nativeCoverBaseChangePathFiberMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    SSet.pathHomotopyFiber (pullback.snd f (nativeCoverProjection Y a)) v ⟶
      SSet.pathHomotopyFiber f y :=
  SSet.pathHomotopyFiberMap (pullback.fst f (nativeCoverProjection Y a))
    (nativeCoverProjection Y a)
    (pullback.condition (f := f) (g := nativeCoverProjection Y a)).symm hv

/-- The actual map retains the original source coordinate through the literal first projection. -/
theorem nativeCoverBaseChangePathFiberMap_toTotal
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    nativeCoverBaseChangePathFiberMap f a v hv ≫ SSet.pathHomotopyFiberToTotal f y =
      SSet.pathHomotopyFiberToTotal
          (pullback.snd f (nativeCoverProjection Y a)) v ≫
        pullback.fst f (nativeCoverProjection Y a) :=
  SSet.pathHomotopyFiberMap_toTotal _ _ _ _

/-- Its full ending path is projected by the actual cover map, with the same orientation. -/
theorem nativeCoverBaseChangePathFiberMap_path
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    nativeCoverBaseChangePathFiberMap f a v hv ≫ SSet.pathHomotopyFiberPath f y =
      SSet.pathHomotopyFiberPath
          (pullback.snd f (nativeCoverProjection Y a)) v ≫
        (ihom (Δ[1] : SSet.{u})).map (nativeCoverProjection Y a) :=
  SSet.pathHomotopyFiberMap_path _ _ _ _

private theorem endInclusion_anodyne :
    SSet.anodyneExtensions
      (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have hface :
      SSet.stdSimplex.face ({0}ᶜ : Finset (Fin 2)) =
        SSet.horn (1 : ℕ) (1 : Fin 2) := by
    have hfin : ({0}ᶜ : Finset (Fin 2)) = {1} := by decide
    rw [hfin]
    ext m x
    simp [SSet.horn_eq_iSup, hfin]
  let e :
      Arrow.mk (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≅
        Arrow.mk (SSet.horn (1 : ℕ) (1 : Fin 2)).ι :=
    Arrow.isoMk
      (SSet.stdSimplex.faceSingletonComplIso (0 : Fin 2) ≪≫
        SSet.Subcomplex.eqToIso hface)
      (Iso.refl _) (by
        change (SSet.stdSimplex.faceSingletonComplIso (0 : Fin 2) ≪≫
            SSet.Subcomplex.eqToIso hface).hom ≫ (SSet.horn 1 (1 : Fin 2)).ι =
          SSet.stdSimplex.δ (0 : Fin 2) ≫ (Iso.refl _).hom
        simp only [Iso.trans_hom, Category.assoc, SSet.Subcomplex.eqToIso_hom,
          SSet.Subcomplex.homOfLE_ι, SSet.stdSimplex.faceSingletonComplIso_hom_ι,
          Iso.refl_hom, Category.comp_id])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left e p]
  exact SSet.anodyneExtensions.horn_ι (1 : Fin 2) p hp

private theorem endTensorEndpoint (A : SSet.{u}) :
    (λ_ A).inv ≫ (SSet.Δ0IsoUnit.inv ▷ A) ≫
        (SSet.stdSimplex.δ (0 : Fin 2) ▷ A) =
      SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.braiding_hom_fst,
      SSet.stdSimplex.δ_zero_eq_const, SSet.comp_const]
    exact (SSet.ι₁_snd A).symm
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      CartesianMonoidalCategory.leftUnitor_inv_snd,
      CartesianMonoidalCategory.braiding_hom_snd, SSet.ι₁_fst]

private theorem endRestriction_eq_eval
    {A B : SSet.{u}} (γ : A ⟶ SSet.pathSpace B) :
    γ ≫ (MonoidalClosed.pre
          (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app B ≫
        (SSet.ihomZeroIso B).hom =
      γ ≫ SSet.eval₁ := by
  have hcurried :
      γ ≫ (MonoidalClosed.pre
          (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app B ≫
          (SSet.ihomZeroIso B).hom =
        ((λ_ A).inv ≫ (SSet.Δ0IsoUnit.inv ▷ A) ≫
          (SSet.stdSimplex.δ (0 : Fin 2) ▷ A)) ≫ MonoidalClosed.uncurry γ := by
    rw [SSet.ihomZeroIso_hom, ← MonoidalClosed.curry_uncurry γ,
      MonoidalClosed.curry_pre_app_assoc, MonoidalClosed.curry_pre_app_assoc,
      SSet.curry_unitIsoSelf];
        simp only [MonoidalClosed.uncurry_curry, Category.assoc]
  calc
    _ = ((λ_ A).inv ≫ (SSet.Δ0IsoUnit.inv ▷ A) ≫
        (SSet.stdSimplex.δ (0 : Fin 2) ▷ A)) ≫ MonoidalClosed.uncurry γ := hcurried
    _ = γ ≫ SSet.eval₁ := by
      rw [endTensorEndpoint]
      simpa only [Category.assoc] using
        (SSet.comp_eval₁_eq_ι₁_braiding_uncurry γ).symm

private theorem zeroHom_naturality {P Y : SSet.{u}} (p : P ⟶ Y) :
    (ihom (Δ[0] : SSet.{u})).map p ≫ (SSet.ihomZeroIso Y).hom =
      (SSet.ihomZeroIso P).hom ≫ p := by
  have hpre := (MonoidalClosed.pre SSet.Δ0IsoUnit.inv).naturality p
  let A : SSet.{u} := (ihom (𝟙_ SSet.{u})).obj P
  have hcurryP : MonoidalClosed.curry (MonoidalClosed.uncurry (𝟙 A)) = 𝟙 A :=
    MonoidalClosed.curry_uncurry (𝟙 A)
  have huncurryP : MonoidalClosed.uncurry (𝟙 A) =
      (ihom.ev (𝟙_ SSet.{u})).app P := by
    change MonoidalClosed.uncurry (𝟙 ((ihom (𝟙_ SSet.{u})).obj P)) = _
    exact MonoidalClosed.uncurry_id_eq_ev (𝟙_ SSet.{u}) P
  have hbasicP :
      MonoidalClosed.curry (MonoidalClosed.uncurry (𝟙 A)) ≫
          (MonoidalClosed.unitIsoSelf (X := P)).hom =
        (λ_ A).inv ≫ MonoidalClosed.uncurry (𝟙 A) :=
    SSet.curry_unitIsoSelf (MonoidalClosed.uncurry (𝟙 A))
  have hunitP : (MonoidalClosed.unitIsoSelf (X := P)).hom =
      (λ_ A).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app P := by
    calc
      _ = (𝟙 A) ≫ (MonoidalClosed.unitIsoSelf (X := P)).hom := (Category.id_comp _).symm
      _ = MonoidalClosed.curry (MonoidalClosed.uncurry (𝟙 A)) ≫
          (MonoidalClosed.unitIsoSelf (X := P)).hom :=
        congrArg (fun h : A ⟶ A => h ≫ (MonoidalClosed.unitIsoSelf (X := P)).hom) hcurryP.symm
      _ = (λ_ A).inv ≫ MonoidalClosed.uncurry (𝟙 A) := hbasicP
      _ = _ := congrArg (fun h : (𝟙_ SSet.{u}) ⊗ A ⟶ P => (λ_ A).inv ≫ h) huncurryP
  have hcurryY :
      MonoidalClosed.curry (MonoidalClosed.uncurry ((ihom (𝟙_ SSet.{u})).map p)) =
        (ihom (𝟙_ SSet.{u})).map p :=
    MonoidalClosed.curry_uncurry ((ihom (𝟙_ SSet.{u})).map p)
  have huncurryY : MonoidalClosed.uncurry ((ihom (𝟙_ SSet.{u})).map p) =
      (ihom.ev (𝟙_ SSet.{u})).app P ≫ p :=
    MonoidalClosed.uncurry_ihom_map (A := (𝟙_ SSet.{u})) p
  have hbasicY :
      MonoidalClosed.curry (MonoidalClosed.uncurry ((ihom (𝟙_ SSet.{u})).map p)) ≫
          (MonoidalClosed.unitIsoSelf (X := Y)).hom =
        (λ_ A).inv ≫ MonoidalClosed.uncurry ((ihom (𝟙_ SSet.{u})).map p) :=
    SSet.curry_unitIsoSelf (MonoidalClosed.uncurry ((ihom (𝟙_ SSet.{u})).map p))
  have hunitY :
      (ihom (𝟙_ SSet.{u})).map p ≫ (MonoidalClosed.unitIsoSelf (X := Y)).hom =
        (λ_ A).inv ≫ ((ihom.ev (𝟙_ SSet.{u})).app P ≫ p) := by
    calc
      _ = MonoidalClosed.curry (MonoidalClosed.uncurry ((ihom (𝟙_ SSet.{u})).map p)) ≫
          (MonoidalClosed.unitIsoSelf (X := Y)).hom :=
        congrArg (fun h : A ⟶ (ihom (𝟙_ SSet.{u})).obj Y =>
          h ≫ (MonoidalClosed.unitIsoSelf (X := Y)).hom) hcurryY.symm
      _ = (λ_ A).inv ≫ MonoidalClosed.uncurry ((ihom (𝟙_ SSet.{u})).map p) := hbasicY
      _ = _ := congrArg (fun h : (𝟙_ SSet.{u}) ⊗ A ⟶ Y => (λ_ A).inv ≫ h) huncurryY
  have hunit :
      (ihom (𝟙_ SSet.{u})).map p ≫ (MonoidalClosed.unitIsoSelf (X := Y)).hom =
        (MonoidalClosed.unitIsoSelf (X := P)).hom ≫ p := by
    calc
      _ = (λ_ A).inv ≫ ((ihom.ev (𝟙_ SSet.{u})).app P ≫ p) := hunitY
      _ = ((λ_ A).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app P) ≫ p :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun h : A ⟶ P => h ≫ p) hunitP.symm
  rw [SSet.ihomZeroIso_hom, SSet.ihomZeroIso_hom]
  calc
    _ = ((MonoidalClosed.pre SSet.Δ0IsoUnit.inv).app P ≫
        (ihom (𝟙_ SSet.{u})).map p) ≫
        (MonoidalClosed.unitIsoSelf (X := Y)).hom := by
      rw [← Category.assoc, hpre]
    _ = _ := by rw [Category.assoc, hunit, ← Category.assoc]

private noncomputable def pathFiberLift
    {Z X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌)
    (x : Z ⟶ X) (γ : Z ⟶ SSet.pathSpace B)
    (hzero : γ ≫ SSet.eval₀ = x ≫ f)
    (hone : γ ≫ SSet.eval₁ = SSet.const (X := Z) b) :
    Z ⟶ SSet.pathHomotopyFiber f b :=
  pullback.lift (Limits.prod.lift x (SSet.stdSimplex.isTerminalObj₀.from Z)) γ (by
    change Limits.prod.lift x (SSet.stdSimplex.isTerminalObj₀.from Z) ≫
        Limits.prod.map f (SSet.const (X := (Δ[0] : SSet.{u})) b) =
      γ ≫ SSet.evalPair ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd B).hom.app B
    apply Limits.prod.hom_ext
    · simpa only [Category.assoc, Limits.prod.map_fst, Limits.prod.lift_fst_assoc,
        SSet.tensorLeftIsoProd_hom_fst, SSet.evalPair_fst] using hzero.symm
    · simpa only [Category.assoc, Limits.prod.map_snd, Limits.prod.lift_snd_assoc,
        SSet.tensorLeftIsoProd_hom_snd, SSet.evalPair_snd, SSet.comp_const] using hone.symm)

private theorem pathFiberLift_toTotal
    {Z X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌)
    (x : Z ⟶ X) (γ : Z ⟶ SSet.pathSpace B)
    (hzero : γ ≫ SSet.eval₀ = x ≫ f)
    (hone : γ ≫ SSet.eval₁ = SSet.const (X := Z) b) :
    pathFiberLift f b x γ hzero hone ≫ SSet.pathHomotopyFiberToTotal f b = x := by
  dsimp only [pathFiberLift, SSet.pathHomotopyFiberToTotal,
    SSet.pathHomotopyPullbackLeft]
  rw [← Category.assoc, pullback.lift_fst, Limits.prod.lift_fst]

private theorem pathFiberLift_path
    {Z X B : SSet.{u}} (f : X ⟶ B) (b : B _⦋0⦌)
    (x : Z ⟶ X) (γ : Z ⟶ SSet.pathSpace B)
    (hzero : γ ≫ SSet.eval₀ = x ≫ f)
    (hone : γ ≫ SSet.eval₁ = SSet.const (X := Z) b) :
    pathFiberLift f b x γ hzero hone ≫ SSet.pathHomotopyFiberPath f b = γ := by
  dsimp only [pathFiberLift, SSet.pathHomotopyFiberPath,
    SSet.pathHomotopyPullbackPath]
  exact pullback.lift_snd _ _ _

/-- Boundary lifts of the actual fiber map use ending prisms and the original cover fibration. -/
theorem nativeCoverBaseChangePathFiberMap_mem_I_rlp
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    SSet.modelCategoryQuillen.I.rlp (nativeCoverBaseChangePathFiberMap f a v hv) := by
  let Xorig : SSet.{u} := X
  let Yorig : SSet.{u} := Y
  let P : SSet.{u} := nativeCover Y a
  let p : P ⟶ Yorig := nativeCoverProjection Y a
  let Q : SSet.{u} := pullback f p
  let q : Q ⟶ P := pullback.snd f p
  let S : SSet.{u} := SSet.pathHomotopyFiber q v
  let T : SSet.{u} := SSet.pathHomotopyFiber f y
  let C : S ⟶ T := nativeCoverBaseChangePathFiberMap f a v hv
  let HP : SSet.{u} := (MonoidalClosed.internalHom.obj (Opposite.op (Δ[1] : SSet.{u}))).obj P
  let HY : SSet.{u} := (MonoidalClosed.internalHom.obj (Opposite.op (Δ[1] : SSet.{u}))).obj Yorig
  let H0P : SSet.{u} := (MonoidalClosed.internalHom.obj (Opposite.op (Δ[0] : SSet.{u}))).obj P
  let H0Y : SSet.{u} :=
    (MonoidalClosed.internalHom.obj (Opposite.op (Δ[0] : SSet.{u}))).obj Yorig
  let ΓS : S ⟶ HP := SSet.pathHomotopyFiberPath q v
  let ΓT : T ⟶ HY := SSet.pathHomotopyFiberPath f y
  let m1 : HP ⟶ HY :=
    (MonoidalClosed.internalHom.obj (Opposite.op (Δ[1] : SSet.{u}))).map p
  let m0 : H0P ⟶ H0Y :=
    (MonoidalClosed.internalHom.obj (Opposite.op (Δ[0] : SSet.{u}))).map p
  let zP : H0P ≅ P := SSet.ihomZeroIso P
  let zY : H0Y ≅ Yorig := SSet.ihomZeroIso Yorig
  have hCtotal : C ≫ SSet.pathHomotopyFiberToTotal f y =
      SSet.pathHomotopyFiberToTotal q v ≫ pullback.fst f p :=
    nativeCoverBaseChangePathFiberMap_toTotal f a v hv
  have hCpath : C ≫ ΓT = ΓS ≫ m1 := nativeCoverBaseChangePathFiberMap_path f a v hv
  have hSzero : ΓS ≫ SSet.eval₀ = SSet.pathHomotopyFiberToTotal q v ≫ q :=
    SSet.pathHomotopyFiberPath_evalZero q v
  have hmzero : m1 ≫ SSet.eval₀ = SSet.eval₀ ≫ p := SSet.pathSpace_map_eval₀ p
  have hzeroNat : m0 ≫ zY.hom = zP.hom ≫ p := zeroHom_naturality p
  have hpv : p.app (Opposite.op ⦋0⦌) v = y := hv
  have hconst : SSet.const (X := T) v ≫ p = SSet.const (X := T) y :=
    (SSet.const_comp v p).trans
      (congrArg (fun t : Yorig _⦋0⦌ => SSet.const (X := T) t) hpv)
  have hp : HomotopicalAlgebra.Fibration p := by
    let _ : Groupoid.{u} (CategoryTheory.Under (SSet.FundamentalGroupoid.mk a)) :=
      Groupoid.ofIsGroupoid
    let _ : HomotopicalAlgebra.Fibration (nativeCoverNerveProjection Y a) := by
      dsimp only [nativeCoverNerveProjection]
      exact CategoryTheory.nerve.fibration_nerveMap_of_isIsofibration
        (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk a))
    dsimp only [p, nativeCoverProjection]
    exact SSet.fibration_pullback_fst
  let j : (Δ[0] : SSet.{u}) ⟶ Δ[1] := SSet.stdSimplex.δ (0 : Fin 2)
  let R := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j p
  have hR : SSet.modelCategoryQuillen.I.rlp R.π := by
    intro A B i hi
    obtain ⟨n⟩ := hi
    let d := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
      j (SSet.boundary n).ι
    rw [← MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff d R]
    have han := SSet.anodyneExtensions_pushoutObjObjι' d endInclusion_anodyne
    exact han _ ((HomotopicalAlgebra.fibration_iff p).mp hp)
  have hπfst : R.π ≫ R.fst = (MonoidalClosed.pre j).app P := R.π_fst
  have hπsnd : R.π ≫ R.snd = m1 := R.π_snd
  have htarget : (SSet.const (X := T) v ≫ zP.inv) ≫ m0 =
      ΓT ≫ (MonoidalClosed.pre j).app Yorig := by
    apply (cancel_mono zY.hom).mp
    calc
      _ = SSet.const (X := T) v ≫ (zP.inv ≫ (m0 ≫ zY.hom)) := by
        simp only [Category.assoc]
      _ = SSet.const (X := T) v ≫ (zP.inv ≫ (zP.hom ≫ p)) :=
        congrArg (fun h : H0P ⟶ Yorig => SSet.const (X := T) v ≫ zP.inv ≫ h) hzeroNat
      _ = SSet.const (X := T) v ≫ p := by
        rw [zP.inv_hom_id_assoc]
      _ = SSet.const (X := T) y := hconst
      _ = ΓT ≫ SSet.eval₁ := (SSet.pathHomotopyFiberPath_evalOne f y).symm
      _ = (ΓT ≫ (MonoidalClosed.pre j).app Yorig) ≫ zY.hom := by
        have heval : ΓT ≫ (MonoidalClosed.pre j).app Yorig ≫ zY.hom =
            ΓT ≫ SSet.eval₁ := by
          change ΓT ≫ (MonoidalClosed.pre
              (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app Yorig ≫
            (SSet.ihomZeroIso Yorig).hom = _
          exact endRestriction_eq_eval ΓT
        exact heval.symm.trans
          (Category.assoc ΓT ((MonoidalClosed.pre j).app Yorig) zY.hom).symm
  let Arel : T ⟶ R.pt := R.isPullback.lift
    (SSet.const (X := T) v ≫ zP.inv) ΓT htarget
  have hAfst : Arel ≫ R.fst = SSet.const (X := T) v ≫ zP.inv :=
    R.isPullback.lift_fst _ _ _
  have hAsnd : Arel ≫ R.snd = ΓT := R.isPullback.lift_snd _ _ _
  have hAend : (Arel ≫ R.fst) ≫ zP.hom = SSet.const (X := T) v := by
    calc
      _ = (SSet.const (X := T) v ≫ zP.inv) ≫ zP.hom :=
        congrArg (fun h : T ⟶ H0P => h ≫ zP.hom) hAfst
      _ = _ := by rw [Category.assoc, zP.inv_hom_id, Category.comp_id]
  have hsq : ΓS ≫ R.π = C ≫ Arel := by
    apply R.hom_ext
    · apply (cancel_mono zP.hom).mp
      calc
        _ = ΓS ≫ ((R.π ≫ R.fst) ≫ zP.hom) := by simp only [Category.assoc]
        _ = ΓS ≫ ((MonoidalClosed.pre j).app P ≫ zP.hom) :=
          congrArg (fun h : HP ⟶ H0P => ΓS ≫ h ≫ zP.hom) hπfst
        _ = ΓS ≫ SSet.eval₁ := endRestriction_eq_eval ΓS
        _ = SSet.const (X := S) v := SSet.pathHomotopyFiberPath_evalOne q v
        _ = C ≫ SSet.const (X := T) v := (SSet.comp_const C v).symm
        _ = C ≫ ((Arel ≫ R.fst) ≫ zP.hom) :=
          congrArg (fun h : T ⟶ P => C ≫ h) hAend.symm
        _ = _ := by simp only [Category.assoc]
    · calc
        _ = ΓS ≫ (R.π ≫ R.snd) := Category.assoc _ _ _
        _ = ΓS ≫ m1 := congrArg (fun h : HP ⟶ HY => ΓS ≫ h) hπsnd
        _ = C ≫ ΓT := hCpath.symm
        _ = C ≫ (Arel ≫ R.snd) := congrArg (fun h : T ⟶ HY => C ≫ h) hAsnd.symm
        _ = _ := (Category.assoc _ _ _).symm
  intro A B i hi
  obtain ⟨n⟩ := hi
  refine ⟨fun {α β} sq => ?_⟩
  have hLP : HasLiftingProperty (SSet.boundary n).ι R.π := hR _ ⟨n⟩
  have sqR : CommSq (α ≫ ΓS) (SSet.boundary n).ι R.π (β ≫ Arel) := by
    refine ⟨?_⟩
    calc
      (α ≫ ΓS) ≫ R.π = α ≫ (ΓS ≫ R.π) := Category.assoc _ _ _
      _ = α ≫ (C ≫ Arel) := congrArg (fun h : S ⟶ R.pt => α ≫ h) hsq
      _ = (α ≫ C) ≫ Arel := (Category.assoc _ _ _).symm
      _ = ((SSet.boundary n).ι ≫ β) ≫ Arel :=
        congrArg (fun h : (SSet.boundary n : SSet.{u}) ⟶ T => h ≫ Arel) sq.w
      _ = (SSet.boundary n).ι ≫ (β ≫ Arel) := Category.assoc _ _ _
  let _ : sqR.HasLift := hLP.sq_hasLift sqR
  let γ : (Δ[n] : SSet.{u}) ⟶ HP := sqR.lift
  have hγleft : (SSet.boundary n).ι ≫ γ = α ≫ ΓS := sqR.fac_left
  have hγright : γ ≫ R.π = β ≫ Arel := sqR.fac_right
  have hγY : γ ≫ m1 = β ≫ ΓT := by
    have h := congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ R.pt => h ≫ R.snd) hγright
    have hleft : (γ ≫ R.π) ≫ R.snd = γ ≫ m1 :=
      (Category.assoc _ _ _).trans (congrArg (fun g : HP ⟶ HY => γ ≫ g) hπsnd)
    have hright : (β ≫ Arel) ≫ R.snd = β ≫ ΓT :=
      (Category.assoc _ _ _).trans (congrArg (fun g : T ⟶ HY => β ≫ g) hAsnd)
    exact hleft.symm.trans (h.trans hright)
  have hγone : γ ≫ SSet.eval₁ = SSet.const (X := (Δ[n] : SSet.{u})) v := by
    have h := congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ R.pt => h ≫ R.fst) hγright
    have hleft : (γ ≫ R.π) ≫ R.fst = γ ≫ (MonoidalClosed.pre j).app P :=
      (Category.assoc _ _ _).trans (congrArg (fun g : HP ⟶ H0P => γ ≫ g) hπfst)
    have hright : (β ≫ Arel) ≫ R.fst = β ≫ (SSet.const (X := T) v ≫ zP.inv) :=
      (Category.assoc _ _ _).trans (congrArg (fun g : T ⟶ H0P => β ≫ g) hAfst)
    have he := hleft.symm.trans (h.trans hright)
    have hep := congrArg (fun g : (Δ[n] : SSet.{u}) ⟶ H0P => g ≫ zP.hom) he
    calc
      _ = (γ ≫ (MonoidalClosed.pre j).app P) ≫ zP.hom := by
        have heval : γ ≫ (MonoidalClosed.pre j).app P ≫ zP.hom = γ ≫ SSet.eval₁ := by
          change γ ≫ (MonoidalClosed.pre
              (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app P ≫
            (SSet.ihomZeroIso P).hom = _
          exact endRestriction_eq_eval γ
        exact heval.symm.trans
          (Category.assoc γ ((MonoidalClosed.pre j).app P) zP.hom).symm
      _ = (β ≫ (SSet.const (X := T) v ≫ zP.inv)) ≫ zP.hom := hep
      _ = β ≫ SSet.const (X := T) v := by
        rw [Category.assoc, Category.assoc, zP.inv_hom_id, Category.comp_id]
      _ = _ := SSet.comp_const β v
  let x : (Δ[n] : SSet.{u}) ⟶ Xorig := β ≫ SSet.pathHomotopyFiberToTotal f y
  have hQ : x ≫ f = (γ ≫ SSet.eval₀) ≫ p := by
    calc
      _ = β ≫ (SSet.pathHomotopyFiberToTotal f y ≫ f) := Category.assoc _ _ _
      _ = β ≫ (ΓT ≫ SSet.eval₀) :=
        congrArg (fun h : T ⟶ Yorig => β ≫ h) (SSet.pathHomotopyFiberPath_evalZero f y).symm
      _ = (β ≫ ΓT) ≫ SSet.eval₀ := (Category.assoc _ _ _).symm
      _ = (γ ≫ m1) ≫ SSet.eval₀ :=
        congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ HY => h ≫ SSet.eval₀) hγY.symm
      _ = γ ≫ (m1 ≫ SSet.eval₀) := Category.assoc _ _ _
      _ = γ ≫ (SSet.eval₀ ≫ p) := congrArg (fun h : HP ⟶ Yorig => γ ≫ h) hmzero
      _ = _ := (Category.assoc _ _ _).symm
  let xQ : (Δ[n] : SSet.{u}) ⟶ Q := pullback.lift x (γ ≫ SSet.eval₀) hQ
  have hxQfst : xQ ≫ pullback.fst f p = x := pullback.lift_fst _ _ _
  have hxQsnd : xQ ≫ q = γ ≫ SSet.eval₀ := pullback.lift_snd _ _ _
  let φ : (Δ[n] : SSet.{u}) ⟶ S :=
    pathFiberLift q v xQ γ hxQsnd.symm hγone
  have hφtotal : φ ≫ SSet.pathHomotopyFiberToTotal q v = xQ :=
    pathFiberLift_toTotal _ _ _ _ _ _
  have hφpath : φ ≫ ΓS = γ := pathFiberLift_path _ _ _ _ _ _
  have hφC : φ ≫ C = β := by
    apply SSet.pathHomotopyFiber_hom_ext
    · calc
        _ = φ ≫ (C ≫ SSet.pathHomotopyFiberToTotal f y) := Category.assoc _ _ _
        _ = φ ≫ (SSet.pathHomotopyFiberToTotal q v ≫ pullback.fst f p) :=
          congrArg (fun h : S ⟶ Xorig => φ ≫ h) hCtotal
        _ = (φ ≫ SSet.pathHomotopyFiberToTotal q v) ≫ pullback.fst f p :=
          (Category.assoc _ _ _).symm
        _ = xQ ≫ pullback.fst f p :=
          congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ Q => h ≫ pullback.fst f p) hφtotal
        _ = β ≫ SSet.pathHomotopyFiberToTotal f y := hxQfst
    · calc
        _ = φ ≫ (C ≫ ΓT) := Category.assoc _ _ _
        _ = φ ≫ (ΓS ≫ m1) :=
          congrArg (fun h : S ⟶ HY => φ ≫ h) hCpath
        _ = (φ ≫ ΓS) ≫ m1 := (Category.assoc _ _ _).symm
        _ = γ ≫ m1 :=
          congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ HP =>
            h ≫ m1) hφpath
        _ = β ≫ ΓT := hγY
  have hφboundary : (SSet.boundary n).ι ≫ φ = α := by
    apply SSet.pathHomotopyFiber_hom_ext
    · apply pullback.hom_ext
      · calc
          _ = ((SSet.boundary n).ι ≫ φ) ≫
              (SSet.pathHomotopyFiberToTotal q v ≫ pullback.fst f p) := Category.assoc _ _ _
          _ = ((SSet.boundary n).ι ≫ φ) ≫
              (C ≫ SSet.pathHomotopyFiberToTotal f y) :=
            congrArg (fun h : S ⟶ Xorig => ((SSet.boundary n).ι ≫ φ) ≫ h) hCtotal.symm
          _ = (((SSet.boundary n).ι ≫ φ) ≫ C) ≫
              SSet.pathHomotopyFiberToTotal f y := (Category.assoc _ _ _).symm
          _ = ((SSet.boundary n).ι ≫ (φ ≫ C)) ≫
              SSet.pathHomotopyFiberToTotal f y :=
            congrArg (fun h : (SSet.boundary n : SSet.{u}) ⟶ T =>
              h ≫ SSet.pathHomotopyFiberToTotal f y) (Category.assoc _ _ _)
          _ = ((SSet.boundary n).ι ≫ β) ≫ SSet.pathHomotopyFiberToTotal f y :=
            congrArg (fun h : (SSet.boundary n : SSet.{u}) ⟶ T =>
              h ≫ SSet.pathHomotopyFiberToTotal f y)
                (congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ T => (SSet.boundary n).ι ≫ h) hφC)
          _ = (α ≫ C) ≫ SSet.pathHomotopyFiberToTotal f y :=
            congrArg (fun h : (SSet.boundary n : SSet.{u}) ⟶ T =>
              h ≫ SSet.pathHomotopyFiberToTotal f y) sq.w.symm
          _ = α ≫ (C ≫ SSet.pathHomotopyFiberToTotal f y) := Category.assoc _ _ _
          _ = α ≫ (SSet.pathHomotopyFiberToTotal q v ≫ pullback.fst f p) :=
            congrArg (fun h : S ⟶ Xorig => α ≫ h) hCtotal
          _ = _ := (Category.assoc _ _ _).symm
      · calc
          _ = ((SSet.boundary n).ι ≫ φ) ≫
              (SSet.pathHomotopyFiberToTotal q v ≫ q) := Category.assoc _ _ _
          _ = ((SSet.boundary n).ι ≫ φ) ≫ (ΓS ≫ SSet.eval₀) :=
            congrArg (fun h : S ⟶ P => ((SSet.boundary n).ι ≫ φ) ≫ h) hSzero.symm
          _ = (((SSet.boundary n).ι ≫ φ) ≫ ΓS) ≫ SSet.eval₀ :=
            (Category.assoc _ _ _).symm
          _ = ((SSet.boundary n).ι ≫ (φ ≫ ΓS)) ≫ SSet.eval₀ :=
            congrArg (fun h : (SSet.boundary n : SSet.{u}) ⟶ HP =>
              h ≫ SSet.eval₀) (Category.assoc _ _ _)
          _ = ((SSet.boundary n).ι ≫ γ) ≫ SSet.eval₀ :=
            congrArg (fun h : (SSet.boundary n : SSet.{u}) ⟶ HP =>
              h ≫ SSet.eval₀)
                (congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ HP =>
                  (SSet.boundary n).ι ≫ h) hφpath)
          _ = (α ≫ ΓS) ≫ SSet.eval₀ :=
            congrArg (fun h : (SSet.boundary n : SSet.{u}) ⟶ HP =>
              h ≫ SSet.eval₀) hγleft
          _ = α ≫ (ΓS ≫ SSet.eval₀) := Category.assoc _ _ _
          _ = α ≫ (SSet.pathHomotopyFiberToTotal q v ≫ q) :=
            congrArg (fun h : S ⟶ P => α ≫ h) hSzero
          _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = (SSet.boundary n).ι ≫ (φ ≫ ΓS) := Category.assoc _ _ _
        _ = (SSet.boundary n).ι ≫ γ :=
          congrArg (fun h : (Δ[n] : SSet.{u}) ⟶ HP =>
            (SSet.boundary n).ι ≫ h) hφpath
        _ = α ≫ ΓS := hγleft
  apply CommSq.HasLift.mk'
  exact { l := φ, fac_left := hφboundary, fac_right := hφC }

end SSet.KanComplex

namespace SSet.KanComplex

private theorem actualFiberMap_rlp_monomorphisms
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (nativeCoverBaseChangePathFiberMap f a v hv) := by
  rw [SSet.rlp_monomorphisms]
  exact nativeCoverBaseChangePathFiberMap_mem_I_rlp f a v hv

/-- The actual map is a fibration and a weak equivalence for the canonical realization property. -/
theorem nativeCoverBaseChangePathFiberMap_mem_trivialFibrations
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    (HomotopicalAlgebra.fibrations SSet.{u} ⊓ SSet.realizationWeakEquivalences)
      (nativeCoverBaseChangePathFiberMap f a v hv) := by
  let C := nativeCoverBaseChangePathFiberMap f a v hv
  have hI : SSet.modelCategoryQuillen.I.rlp C :=
    nativeCoverBaseChangePathFiberMap_mem_I_rlp f a v hv
  have hMono : (MorphismProperty.monomorphisms SSet.{u}).rlp C :=
    actualFiberMap_rlp_monomorphisms f a v hv
  have hJ : SSet.modelCategoryQuillen.J.rlp C :=
    (MorphismProperty.antitone_rlp SSet.modelCategoryQuillen.J_le_monomorphisms) _ hMono
  have hFib : HomotopicalAlgebra.Fibration C :=
    (SSet.modelCategoryQuillen.fibration_iff C).mpr hJ
  exact ⟨(HomotopicalAlgebra.fibration_iff C).mp hFib,
    SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences C hI⟩

/-- The same original map lies in the actual canonical realization weak-equivalence property. -/
theorem nativeCoverBaseChangePathFiberMap_mem_realizationWeakEquivalences
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    SSet.realizationWeakEquivalences (nativeCoverBaseChangePathFiberMap f a v hv) :=
  (nativeCoverBaseChangePathFiberMap_mem_trivialFibrations f a v hv).2

private theorem exists_actualFiberSection
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    ∃ s : SSet.pathHomotopyFiber f y ⟶
        SSet.pathHomotopyFiber (pullback.snd f (nativeCoverProjection Y a)) v,
      s ≫ nativeCoverBaseChangePathFiberMap f a v hv =
        𝟙 (SSet.pathHomotopyFiber f y) := by
  let p := nativeCoverProjection Y a
  let S := SSet.pathHomotopyFiber (pullback.snd f p) v
  let T := SSet.pathHomotopyFiber f y
  let C : S ⟶ T := nativeCoverBaseChangePathFiberMap f a v hv
  let A : T.Subcomplex := ⊥
  let top : (A : SSet.{u}) ⟶ S := SSet.Subcomplex.isInitialBot.to S
  let sq : CommSq top A.ι C (𝟙 T) := ⟨SSet.Subcomplex.isInitialBot.hom_ext _ _⟩
  let _ : HasLiftingProperty A.ι C :=
    actualFiberMap_rlp_monomorphisms f a v hv _ (by infer_instance)
  exact ⟨sq.lift, sq.fac_right⟩

/-- Lifting the actual empty-subcomplex inclusion constructs a section on the original fibers. -/
noncomputable def nativeCoverBaseChangePathFiberSection
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    SSet.pathHomotopyFiber f y ⟶
      SSet.pathHomotopyFiber (pullback.snd f (nativeCoverProjection Y a)) v :=
  Classical.choose
    (show ∃ s : SSet.pathHomotopyFiber f y ⟶
        SSet.pathHomotopyFiber (pullback.snd f (nativeCoverProjection Y a)) v,
      s ≫ nativeCoverBaseChangePathFiberMap f a v hv = 𝟙 (SSet.pathHomotopyFiber f y)
      from by exact exists_actualFiberSection f a v hv)

/-- The constructed section projects to the identity of the same original path fiber. -/
theorem nativeCoverBaseChangePathFiberSection_comp
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    nativeCoverBaseChangePathFiberSection f a v hv ≫
        nativeCoverBaseChangePathFiberMap f a v hv =
      𝟙 (SSet.pathHomotopyFiber f y) :=
  Classical.choose_spec (exists_actualFiberSection f a v hv)

/-- Its actual pullback source projects to the original source coordinate. -/
theorem nativeCoverBaseChangePathFiberSection_toTotal
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    nativeCoverBaseChangePathFiberSection f a v hv ≫
        SSet.pathHomotopyFiberToTotal (pullback.snd f (nativeCoverProjection Y a)) v ≫
          pullback.fst f (nativeCoverProjection Y a) =
      SSet.pathHomotopyFiberToTotal f y := by
  let p := nativeCoverProjection Y a
  let S := SSet.pathHomotopyFiber (pullback.snd f p) v
  let T := SSet.pathHomotopyFiber f y
  let C : S ⟶ T := nativeCoverBaseChangePathFiberMap f a v hv
  let s : T ⟶ S := nativeCoverBaseChangePathFiberSection f a v hv
  have hs : s ≫ C = 𝟙 T := nativeCoverBaseChangePathFiberSection_comp f a v hv
  have hC : C ≫ SSet.pathHomotopyFiberToTotal f y =
      SSet.pathHomotopyFiberToTotal (pullback.snd f p) v ≫ pullback.fst f p :=
    nativeCoverBaseChangePathFiberMap_toTotal f a v hv
  calc
    _ = s ≫ (C ≫ SSet.pathHomotopyFiberToTotal f y) :=
      congrArg (fun h : S ⟶ X => s ≫ h) hC.symm
    _ = (s ≫ C) ≫ SSet.pathHomotopyFiberToTotal f y := (Category.assoc _ _ _).symm
    _ = (𝟙 T) ≫ SSet.pathHomotopyFiberToTotal f y :=
      congrArg (fun h : T ⟶ T => h ≫ SSet.pathHomotopyFiberToTotal f y) hs
    _ = _ := Category.id_comp _

private theorem rightBoundary_hom_ext
    {A B : SSet.{u}} {f g : A ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ B}
    (hzero : (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ f =
      (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ g)
    (hone : (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ f =
      (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ g) : f = g := by
  apply (cancel_epi (β_ A (SSet.boundary 1 : SSet.{u})).inv).mp
  apply BinaryCofan.IsColimit.hom_ext (SSet.boundaryOneTensorCofanIsColimit A)
  · change (SSet.boundary.ι (1 : Fin 2) ▷ A) ≫
        (β_ A (SSet.boundary 1 : SSet.{u})).inv ≫ f =
      (SSet.boundary.ι (1 : Fin 2) ▷ A) ≫
        (β_ A (SSet.boundary 1 : SSet.{u})).inv ≫ g
    simpa only [Category.assoc, BraidedCategory.braiding_inv_naturality_left_assoc] using
      congrArg (fun h : A ⊗ (Δ[0] : SSet.{u}) ⟶ B =>
        (β_ A (Δ[0] : SSet.{u})).inv ≫ h) hzero
  · change (SSet.boundary.ι (0 : Fin 2) ▷ A) ≫
        (β_ A (SSet.boundary 1 : SSet.{u})).inv ≫ f =
      (SSet.boundary.ι (0 : Fin 2) ▷ A) ≫
        (β_ A (SSet.boundary 1 : SSet.{u})).inv ≫ g
    simpa only [Category.assoc, BraidedCategory.braiding_inv_naturality_left_assoc] using
      congrArg (fun h : A ⊗ (Δ[0] : SSet.{u}) ⟶ B =>
        (β_ A (Δ[0] : SSet.{u})).inv ≫ h) hone

private noncomputable def rightBoundaryDesc
    {A B : SSet.{u}} (fzero fone : A ⟶ B) :
    A ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ B :=
  (β_ A (SSet.boundary 1 : SSet.{u})).hom ≫
    BinaryCofan.IsColimit.desc (SSet.boundaryOneTensorCofanIsColimit A)
      (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fzero)
      (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fone)

private theorem rightBoundaryDesc_zero
    {A B : SSet.{u}} (fzero fone : A ⟶ B) :
    (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ rightBoundaryDesc fzero fone =
      CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ fzero := by
  let d := BinaryCofan.IsColimit.desc (SSet.boundaryOneTensorCofanIsColimit A)
    (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fzero)
    (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fone)
  have hd : (SSet.boundary.ι (1 : Fin 2) ▷ A) ≫ d =
      CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fzero :=
    BinaryCofan.IsColimit.inl_desc (SSet.boundaryOneTensorCofanIsColimit A) _ _
  change (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫
      (β_ A (SSet.boundary 1 : SSet.{u})).hom ≫ d = _
  calc
    _ = (β_ A (Δ[0] : SSet.{u})).hom ≫
        ((SSet.boundary.ι (1 : Fin 2) ▷ A) ≫ d) := by
      rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc]
    _ = (β_ A (Δ[0] : SSet.{u})).hom ≫
        (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fzero) :=
      congrArg (fun h : (Δ[0] : SSet.{u}) ⊗ A ⟶ B =>
        (β_ A (Δ[0] : SSet.{u})).hom ≫ h) hd
    _ = _ := by rw [← Category.assoc, CartesianMonoidalCategory.braiding_hom_snd]

private theorem rightBoundaryDesc_one
    {A B : SSet.{u}} (fzero fone : A ⟶ B) :
    (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ rightBoundaryDesc fzero fone =
      CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ fone := by
  let d := BinaryCofan.IsColimit.desc (SSet.boundaryOneTensorCofanIsColimit A)
    (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fzero)
    (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fone)
  have hd : (SSet.boundary.ι (0 : Fin 2) ▷ A) ≫ d =
      CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fone :=
    BinaryCofan.IsColimit.inr_desc (SSet.boundaryOneTensorCofanIsColimit A) _ _
  change (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫
      (β_ A (SSet.boundary 1 : SSet.{u})).hom ≫ d = _
  calc
    _ = (β_ A (Δ[0] : SSet.{u})).hom ≫
        ((SSet.boundary.ι (0 : Fin 2) ▷ A) ≫ d) := by
      rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc]
    _ = (β_ A (Δ[0] : SSet.{u})).hom ≫
        (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) A ≫ fone) :=
      congrArg (fun h : (Δ[0] : SSet.{u}) ⊗ A ⟶ B =>
        (β_ A (Δ[0] : SSet.{u})).hom ≫ h) hd
    _ = _ := by rw [← Category.assoc, CartesianMonoidalCategory.braiding_hom_snd]

private noncomputable def vertexPair (A : SSet.{u}) : A ⟶ A ⊗ (Δ[0] : SSet.{u}) :=
  CartesianMonoidalCategory.lift (𝟙 A) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))

private theorem vertexPair_fst (A : SSet.{u}) :
    vertexPair A ≫ CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) = 𝟙 A := by
  simp only [vertexPair, CartesianMonoidalCategory.lift_fst]

private theorem vertexPair_delta_one (A : SSet.{u}) :
    vertexPair A ≫ (A ◁ SSet.stdSimplex.δ (1 : Fin 2)) = SSet.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst, vertexPair_fst]
    exact (SSet.ι₀_fst A).symm
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd,
      SSet.stdSimplex.δ_one_eq_const, SSet.comp_const]
    exact (SSet.ι₀_snd A).symm

private theorem vertexPair_delta_zero (A : SSet.{u}) :
    vertexPair A ≫ (A ◁ SSet.stdSimplex.δ (0 : Fin 2)) = SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst, vertexPair_fst]
    exact (SSet.ι₁_fst A).symm
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd,
      SSet.stdSimplex.δ_zero_eq_const, SSet.comp_const]
    exact (SSet.ι₁_snd A).symm

private theorem rightBoundaryDesc_precomp
    {A B Z : SSet.{u}} (g : A ⟶ B) (fzero fone : B ⟶ Z) :
    (g ▷ (SSet.boundary 1 : SSet.{u})) ≫ rightBoundaryDesc fzero fone =
      rightBoundaryDesc (g ≫ fzero) (g ≫ fone) := by
  apply rightBoundary_hom_ext
  · calc
      _ = (g ▷ (Δ[0] : SSet.{u})) ≫
          ((B ◁ SSet.boundary.ι (1 : Fin 2)) ≫ rightBoundaryDesc fzero fone) := by
        rw [← Category.assoc, whisker_exchange, Category.assoc]
      _ = (g ▷ (Δ[0] : SSet.{u})) ≫
          (CartesianMonoidalCategory.fst B (Δ[0] : SSet.{u}) ≫ fzero) :=
        congrArg (fun h : B ⊗ (Δ[0] : SSet.{u}) ⟶ Z =>
          (g ▷ (Δ[0] : SSet.{u})) ≫ h) (rightBoundaryDesc_zero fzero fone)
      _ = CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ (g ≫ fzero) := by
        rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst, Category.assoc]
      _ = _ := (rightBoundaryDesc_zero (g ≫ fzero) (g ≫ fone)).symm
  · calc
      _ = (g ▷ (Δ[0] : SSet.{u})) ≫
          ((B ◁ SSet.boundary.ι (0 : Fin 2)) ≫ rightBoundaryDesc fzero fone) := by
        rw [← Category.assoc, whisker_exchange, Category.assoc]
      _ = (g ▷ (Δ[0] : SSet.{u})) ≫
          (CartesianMonoidalCategory.fst B (Δ[0] : SSet.{u}) ≫ fone) :=
        congrArg (fun h : B ⊗ (Δ[0] : SSet.{u}) ⟶ Z =>
          (g ▷ (Δ[0] : SSet.{u})) ≫ h) (rightBoundaryDesc_one fzero fone)
      _ = CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ (g ≫ fone) := by
        rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst, Category.assoc]
      _ = _ := (rightBoundaryDesc_one (g ≫ fzero) (g ≫ fone)).symm

private theorem rightBoundaryDesc_postcomp
    {A B Z : SSet.{u}} (fzero fone : A ⟶ B) (g : B ⟶ Z) :
    rightBoundaryDesc fzero fone ≫ g =
      rightBoundaryDesc (fzero ≫ g) (fone ≫ g) := by
  apply rightBoundary_hom_ext
  · calc
      _ = ((A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ rightBoundaryDesc fzero fone) ≫ g :=
        (Category.assoc _ _ _).symm
      _ = (CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ fzero) ≫ g :=
        congrArg (fun h : A ⊗ (Δ[0] : SSet.{u}) ⟶ B => h ≫ g)
          (rightBoundaryDesc_zero fzero fone)
      _ = CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ (fzero ≫ g) :=
        Category.assoc _ _ _
      _ = _ := (rightBoundaryDesc_zero (fzero ≫ g) (fone ≫ g)).symm
  · calc
      _ = ((A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ rightBoundaryDesc fzero fone) ≫ g :=
        (Category.assoc _ _ _).symm
      _ = (CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ fone) ≫ g :=
        congrArg (fun h : A ⊗ (Δ[0] : SSet.{u}) ⟶ B => h ≫ g)
          (rightBoundaryDesc_one fzero fone)
      _ = CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ (fone ≫ g) :=
        Category.assoc _ _ _
      _ = _ := (rightBoundaryDesc_one (fzero ≫ g) (fone ≫ g)).symm

private theorem rightBoundaryDesc_refl {A B : SSet.{u}} (f : A ⟶ B) :
    rightBoundaryDesc f f =
      CartesianMonoidalCategory.fst A (SSet.boundary 1 : SSet.{u}) ≫ f := by
  apply rightBoundary_hom_ext
  · calc
      _ = CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ f :=
        rightBoundaryDesc_zero f f
      _ = _ := by rw [← Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]
  · calc
      _ = CartesianMonoidalCategory.fst A (Δ[0] : SSet.{u}) ≫ f :=
        rightBoundaryDesc_one f f
      _ = _ := by rw [← Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]

/-- The section retains the entire original ending path after the actual cover projection. -/
theorem nativeCoverBaseChangePathFiberSection_path
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    nativeCoverBaseChangePathFiberSection f a v hv ≫
        SSet.pathHomotopyFiberPath (pullback.snd f (nativeCoverProjection Y a)) v ≫
          (ihom (Δ[1] : SSet.{u})).map (nativeCoverProjection Y a) =
      SSet.pathHomotopyFiberPath f y := by
  let p := nativeCoverProjection Y a
  let S := SSet.pathHomotopyFiber (pullback.snd f p) v
  let T := SSet.pathHomotopyFiber f y
  let C : S ⟶ T := nativeCoverBaseChangePathFiberMap f a v hv
  let s : T ⟶ S := nativeCoverBaseChangePathFiberSection f a v hv
  have hs : s ≫ C = 𝟙 T := nativeCoverBaseChangePathFiberSection_comp f a v hv
  have hC : C ≫ SSet.pathHomotopyFiberPath f y =
      SSet.pathHomotopyFiberPath (pullback.snd f p) v ≫
        (ihom (Δ[1] : SSet.{u})).map p :=
    nativeCoverBaseChangePathFiberMap_path f a v hv
  calc
    _ = s ≫ (C ≫ SSet.pathHomotopyFiberPath f y) :=
      congrArg (fun h : S ⟶ SSet.pathSpace Y => s ≫ h) hC.symm
    _ = (s ≫ C) ≫ SSet.pathHomotopyFiberPath f y := (Category.assoc _ _ _).symm
    _ = (𝟙 T) ≫ SSet.pathHomotopyFiberPath f y :=
      congrArg (fun h : T ⟶ T => h ≫ SSet.pathHomotopyFiberPath f y) hs
    _ = _ := Category.id_comp _

private theorem exists_actualFiberDeformation
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    ∃ d : SSet.StrongDeformationRetract (nativeCoverBaseChangePathFiberSection f a v hv),
      d.r = nativeCoverBaseChangePathFiberMap f a v hv ∧
        d.homotopy.h ≫ nativeCoverBaseChangePathFiberMap f a v hv =
          CartesianMonoidalCategory.fst
              (SSet.pathHomotopyFiber (pullback.snd f (nativeCoverProjection Y a)) v)
              (Δ[1] : SSet.{u}) ≫
            nativeCoverBaseChangePathFiberMap f a v hv := by
  let p := nativeCoverProjection Y a
  let S := SSet.pathHomotopyFiber (pullback.snd f p) v
  let T := SSet.pathHomotopyFiber f y
  let C : S ⟶ T := nativeCoverBaseChangePathFiberMap f a v hv
  let s : T ⟶ S := nativeCoverBaseChangePathFiberSection f a v hv
  have hs : s ≫ C = 𝟙 T := nativeCoverBaseChangePathFiberSection_comp f a v hv
  let R : S.Subcomplex := SSet.Subcomplex.range s
  have hRange : R.ι ≫ (C ≫ s) = R.ι := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨x, hx⟩
    change x ∈ Set.range (s.app n) at hx
    obtain ⟨t, rfl⟩ := hx
    have ht := ConcreteCategory.congr_hom (congr_app hs n) t
    change C.app n (s.app n t) = t at ht
    change s.app n (C.app n (s.app n t)) = s.app n t
    exact congrArg (s.app n) ht
  have hCsC : (C ≫ s) ≫ C = C := by
    calc
      _ = C ≫ (s ≫ C) := Category.assoc _ _ _
      _ = C ≫ 𝟙 T := congrArg (fun h : T ⟶ T => C ≫ h) hs
      _ = _ := Category.comp_id _
  let D : (S ⊗ (Δ[1] : SSet.{u})).Subcomplex :=
    R.unionProd (SSet.boundary 1)
  let dB : S ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ S :=
    rightBoundaryDesc (𝟙 S) (C ≫ s)
  let dR : (R : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ S :=
    CartesianMonoidalCategory.fst (R : SSet.{u}) (Δ[1] : SSet.{u}) ≫ R.ι
  have hcompat :
      (R.ι ▷ (SSet.boundary 1 : SSet.{u})) ≫ dB =
        ((R : SSet.{u}) ◁ (SSet.boundary 1).ι) ≫ dR := by
    calc
      _ = rightBoundaryDesc R.ι R.ι := by
        rw [rightBoundaryDesc_precomp, Category.comp_id, hRange]
      _ = CartesianMonoidalCategory.fst (R : SSet.{u})
          (SSet.boundary 1 : SSet.{u}) ≫ R.ι := rightBoundaryDesc_refl R.ι
      _ = _ := by rw [← Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]
  let hPush := SSet.Subcomplex.unionProd.isPushout R (SSet.boundary 1)
  let U : (D : SSet.{u}) ⟶ S := hPush.desc dB dR hcompat
  have hUB :
      SSet.Subcomplex.unionProd.ι₁ R (SSet.boundary 1) ≫ U = dB :=
    hPush.inl_desc _ _ _
  have hUR :
      SSet.Subcomplex.unionProd.ι₂ R (SSet.boundary 1) ≫ U = dR :=
    hPush.inr_desc _ _ _
  have hU : U ≫ C = D.ι ≫
      (CartesianMonoidalCategory.fst S (Δ[1] : SSet.{u}) ≫ C) := by
    apply hPush.hom_ext
    · calc
        _ = (SSet.Subcomplex.unionProd.ι₁ R (SSet.boundary 1) ≫ U) ≫ C :=
          (Category.assoc _ _ _).symm
        _ = dB ≫ C :=
          congrArg (fun h : S ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ S => h ≫ C) hUB
        _ = rightBoundaryDesc C C := by
          rw [rightBoundaryDesc_postcomp, Category.id_comp, hCsC]
        _ = CartesianMonoidalCategory.fst S (SSet.boundary 1 : SSet.{u}) ≫ C :=
          rightBoundaryDesc_refl C
        _ = _ := by
          rw [← Category.assoc, SSet.Subcomplex.unionProd.ι₁_ι,
            ← Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]
    · calc
        _ = (SSet.Subcomplex.unionProd.ι₂ R (SSet.boundary 1) ≫ U) ≫ C :=
          (Category.assoc _ _ _).symm
        _ = dR ≫ C :=
          congrArg (fun h : (R : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ S => h ≫ C) hUR
        _ = _ := by
          rw [← Category.assoc, SSet.Subcomplex.unionProd.ι₂_ι,
            ← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
  let _ : HasLiftingProperty D.ι C :=
    actualFiberMap_rlp_monomorphisms f a v hv _ (by infer_instance)
  let sq : CommSq U D.ι C
      (CartesianMonoidalCategory.fst S (Δ[1] : SSet.{u}) ≫ C) := ⟨hU⟩
  let H : S ⊗ (Δ[1] : SSet.{u}) ⟶ S := sq.lift
  have hDH : D.ι ≫ H = U := sq.fac_left
  have hHC : H ≫ C = CartesianMonoidalCategory.fst S (Δ[1] : SSet.{u}) ≫ C :=
    sq.fac_right
  have hHB : (S ◁ (SSet.boundary 1).ι) ≫ H = dB := by
    calc
      _ = (SSet.Subcomplex.unionProd.ι₁ R (SSet.boundary 1) ≫ D.ι) ≫ H :=
        congrArg (fun h : S ⊗ (SSet.boundary 1 : SSet.{u}) ⟶
          S ⊗ (Δ[1] : SSet.{u}) => h ≫ H)
            (SSet.Subcomplex.unionProd.ι₁_ι R (SSet.boundary 1)).symm
      _ = SSet.Subcomplex.unionProd.ι₁ R (SSet.boundary 1) ≫ (D.ι ≫ H) :=
        Category.assoc _ _ _
      _ = SSet.Subcomplex.unionProd.ι₁ R (SSet.boundary 1) ≫ U :=
        congrArg (fun h : (D : SSet.{u}) ⟶ S =>
          SSet.Subcomplex.unionProd.ι₁ R (SSet.boundary 1) ≫ h) hDH
      _ = dB := hUB
  have hHR : (R.ι ▷ (Δ[1] : SSet.{u})) ≫ H =
      CartesianMonoidalCategory.fst (R : SSet.{u}) (Δ[1] : SSet.{u}) ≫ R.ι := by
    calc
      _ = (SSet.Subcomplex.unionProd.ι₂ R (SSet.boundary 1) ≫ D.ι) ≫ H :=
        congrArg (fun h : (R : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
          S ⊗ (Δ[1] : SSet.{u}) => h ≫ H)
            (SSet.Subcomplex.unionProd.ι₂_ι R (SSet.boundary 1)).symm
      _ = SSet.Subcomplex.unionProd.ι₂ R (SSet.boundary 1) ≫ (D.ι ≫ H) :=
        Category.assoc _ _ _
      _ = SSet.Subcomplex.unionProd.ι₂ R (SSet.boundary 1) ≫ U :=
        congrArg (fun h : (D : SSet.{u}) ⟶ S =>
          SSet.Subcomplex.unionProd.ι₂ R (SSet.boundary 1) ≫ h) hDH
      _ = _ := hUR
  have hface (j : Fin 2) :
      (S ◁ SSet.boundary.ι j) ≫ (S ◁ (SSet.boundary 1).ι) =
        S ◁ SSet.stdSimplex.δ j := by
    rw [← MonoidalCategory.whiskerLeft_comp, SSet.boundary.ι_ι]
  have hzero : SSet.ι₀ ≫ H = 𝟙 S := by
    calc
      _ = (vertexPair S ≫ (S ◁ SSet.stdSimplex.δ (1 : Fin 2))) ≫ H :=
        congrArg (fun h : S ⟶ S ⊗ (Δ[1] : SSet.{u}) => h ≫ H)
          (vertexPair_delta_one S).symm
      _ = vertexPair S ≫ (S ◁ SSet.boundary.ι (1 : Fin 2)) ≫
          ((S ◁ (SSet.boundary 1).ι) ≫ H) := by
        rw [← hface]; simp only [Category.assoc]
      _ = vertexPair S ≫ (S ◁ SSet.boundary.ι (1 : Fin 2)) ≫ dB :=
        congrArg (fun h : S ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ S =>
          vertexPair S ≫ (S ◁ SSet.boundary.ι (1 : Fin 2)) ≫ h) hHB
      _ = vertexPair S ≫ (CartesianMonoidalCategory.fst S (Δ[0] : SSet.{u}) ≫ 𝟙 S) :=
        congrArg (fun h : S ⊗ (Δ[0] : SSet.{u}) ⟶ S => vertexPair S ≫ h)
          (rightBoundaryDesc_zero (𝟙 S) (C ≫ s))
      _ = _ := by rw [← Category.assoc, vertexPair_fst, Category.id_comp]
  have hone : SSet.ι₁ ≫ H = C ≫ s := by
    calc
      _ = (vertexPair S ≫ (S ◁ SSet.stdSimplex.δ (0 : Fin 2))) ≫ H :=
        congrArg (fun h : S ⟶ S ⊗ (Δ[1] : SSet.{u}) => h ≫ H)
          (vertexPair_delta_zero S).symm
      _ = vertexPair S ≫ (S ◁ SSet.boundary.ι (0 : Fin 2)) ≫
          ((S ◁ (SSet.boundary 1).ι) ≫ H) := by
        rw [← hface]; simp only [Category.assoc]
      _ = vertexPair S ≫ (S ◁ SSet.boundary.ι (0 : Fin 2)) ≫ dB :=
        congrArg (fun h : S ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ S =>
          vertexPair S ≫ (S ◁ SSet.boundary.ι (0 : Fin 2)) ≫ h) hHB
      _ = vertexPair S ≫
          (CartesianMonoidalCategory.fst S (Δ[0] : SSet.{u}) ≫ (C ≫ s)) :=
        congrArg (fun h : S ⊗ (Δ[0] : SSet.{u}) ⟶ S => vertexPair S ≫ h)
          (rightBoundaryDesc_one (𝟙 S) (C ≫ s))
      _ = _ := by rw [← Category.assoc, vertexPair_fst, Category.id_comp]
  let Hrel : SSet.HomotopyRel (𝟙 S) (C ≫ s) R :=
    { h := H
      h₀ := hzero
      h₁ := hone
      stationary := by
        intro n x hx t
        have h := ConcreteCategory.congr_hom (congr_app hHR n) ⟨⟨x, hx⟩, t⟩
        change H.app n ⟨x, t⟩ = x at h ⊢
        exact h }
  let d : SSet.StrongDeformationRetract s :=
    { r := C
      retract := hs
      homotopy := Hrel }
  exact ⟨d, rfl, hHC⟩

/-- The section is a strong deformation retract with the actual original map as retraction. -/
noncomputable def nativeCoverBaseChangePathFiberSectionDeformationRetract
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    SSet.StrongDeformationRetract (nativeCoverBaseChangePathFiberSection f a v hv) :=
  Classical.choose
    (show ∃ d : SSet.StrongDeformationRetract
        (nativeCoverBaseChangePathFiberSection f a v hv),
      d.r = nativeCoverBaseChangePathFiberMap f a v hv ∧
        d.homotopy.h ≫ nativeCoverBaseChangePathFiberMap f a v hv =
          CartesianMonoidalCategory.fst
              (SSet.pathHomotopyFiber (pullback.snd f (nativeCoverProjection Y a)) v)
              (Δ[1] : SSet.{u}) ≫
            nativeCoverBaseChangePathFiberMap f a v hv
      from by exact exists_actualFiberDeformation f a v hv)

/-- The constructed deformation retraction is the same original covering fiber map. -/
theorem nativeCoverBaseChangePathFiberSectionDeformationRetract_r
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    (nativeCoverBaseChangePathFiberSectionDeformationRetract f a v hv).r =
      nativeCoverBaseChangePathFiberMap f a v hv :=
  (Classical.choose_spec (exists_actualFiberDeformation f a v hv)).1

/-- Every time of the relative homotopy projects to the same original coordinate and full path. -/
theorem nativeCoverBaseChangePathFiberSectionDeformationRetract_over
    {X Y : SSet.{u}} (f : X ⟶ Y) (a : Y _⦋0⦌) {y : Y _⦋0⦌}
    (v : (nativeCover Y a) _⦋0⦌)
    (hv : (nativeCoverProjection Y a).app (Opposite.op ⦋0⦌) v = y) :
    (nativeCoverBaseChangePathFiberSectionDeformationRetract f a v hv).homotopy.h ≫
        nativeCoverBaseChangePathFiberMap f a v hv =
      CartesianMonoidalCategory.fst
          (SSet.pathHomotopyFiber (pullback.snd f (nativeCoverProjection Y a)) v)
          (Δ[1] : SSet.{u}) ≫
        nativeCoverBaseChangePathFiberMap f a v hv :=
  (Classical.choose_spec (exists_actualFiberDeformation f a v hv)).2

end SSet.KanComplex

namespace SSet

private noncomputable def originalTopPathSingularIso (Y : TopCat.{u}) :
    TopCat.toSSet.obj (TopCat.pathObject Y) ≅
      SSet.pathSpace (TopCat.toSSet.obj Y) :=
  TopCat.toSSet.mapIso
      (TopCat.isoOfHomeo
        (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Y))) ≪≫
    SSet.singularPathIso Y

/-- The actual singular inverse followed by the counit lands in the same original fiber. -/
noncomputable def originalSingularPathFiberRealizationComparison
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    SSet.toTop.obj
        (SSet.pathHomotopyFiber (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)) ⟶
      TopCat.homotopyFiber f y :=
  SSet.toTop.map (SSet.singularPathHomotopyFiberIso f y).inv ≫
    sSetTopAdj.counit.app (TopCat.homotopyFiber f y)

/-- The comparison keeps the original source projection through the actual counit on X. -/
theorem originalSingularPathFiberRealizationComparison_toTotal
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    originalSingularPathFiberRealizationComparison f y ≫
        TopCat.homotopyFiberToTotal f y =
      SSet.toTop.map
          (SSet.pathHomotopyFiberToTotal (TopCat.toSSet.map f)
            (TopCat.toSSetObj₀Equiv.symm y)) ≫
        sSetTopAdj.counit.app X := by
  let F : TopCat.{u} := TopCat.homotopyFiber f y
  let N : SSet.{u} :=
    SSet.pathHomotopyFiber (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)
  let e : TopCat.toSSet.obj F ≅ N := SSet.singularPathHomotopyFiberIso f y
  let pF : F ⟶ X := TopCat.homotopyFiberToTotal f y
  let pN : N ⟶ TopCat.toSSet.obj X :=
    SSet.pathHomotopyFiberToTotal (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)
  have hforward : e.hom ≫ pN = TopCat.toSSet.map pF :=
    SSet.singularPathHomotopyFiberIso_hom_toTotal f y
  have hinverse : e.inv ≫ TopCat.toSSet.map pF = pN := by
    calc
      _ = e.inv ≫ (e.hom ≫ pN) :=
        congrArg (fun h : TopCat.toSSet.obj F ⟶ TopCat.toSSet.obj X => e.inv ≫ h)
          hforward.symm
      _ = (e.inv ≫ e.hom) ≫ pN := (Category.assoc _ _ _).symm
      _ = _ := by rw [Iso.inv_hom_id, Category.id_comp]
  have hcounit :
      SSet.toTop.map (TopCat.toSSet.map pF) ≫ sSetTopAdj.counit.app X =
        sSetTopAdj.counit.app F ≫ pF := by
    simpa only [Functor.comp_map, Functor.id_map] using sSetTopAdj.counit.naturality pF
  change (SSet.toTop.map e.inv ≫ sSetTopAdj.counit.app F) ≫ pF =
    SSet.toTop.map pN ≫ sSetTopAdj.counit.app X
  calc
    _ = SSet.toTop.map e.inv ≫ (sSetTopAdj.counit.app F ≫ pF) :=
      Category.assoc _ _ _
    _ = SSet.toTop.map e.inv ≫
        (SSet.toTop.map (TopCat.toSSet.map pF) ≫ sSetTopAdj.counit.app X) :=
      congrArg (fun h : SSet.toTop.obj (TopCat.toSSet.obj F) ⟶ X =>
        SSet.toTop.map e.inv ≫ h) hcounit.symm
    _ = (SSet.toTop.map e.inv ≫ SSet.toTop.map (TopCat.toSSet.map pF)) ≫
        sSetTopAdj.counit.app X := (Category.assoc _ _ _).symm
    _ = SSet.toTop.map (e.inv ≫ TopCat.toSSet.map pF) ≫ sSetTopAdj.counit.app X :=
      congrArg (fun h : SSet.toTop.obj N ⟶ SSet.toTop.obj (TopCat.toSSet.obj X) =>
        h ≫ sSetTopAdj.counit.app X)
          (SSet.toTop.map_comp e.inv (TopCat.toSSet.map pF)).symm
    _ = _ := congrArg (fun h : N ⟶ TopCat.toSSet.obj X =>
      SSet.toTop.map h ≫ sSetTopAdj.counit.app X) hinverse

/-- Its entire path is the original path through the actual interval and singular path bridges. -/
theorem originalSingularPathFiberRealizationComparison_path
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    originalSingularPathFiberRealizationComparison f y ≫ TopCat.homotopyFiberPath f y =
      SSet.toTop.map
          (SSet.pathHomotopyFiberPath (TopCat.toSSet.map f)
            (TopCat.toSSetObj₀Equiv.symm y)) ≫
        SSet.toTop.map
          (TopCat.toSSet.mapIso
              (TopCat.isoOfHomeo
                (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Y))) ≪≫
            SSet.singularPathIso Y).inv ≫
          sSetTopAdj.counit.app (TopCat.pathObject Y) := by
  let F : TopCat.{u} := TopCat.homotopyFiber f y
  let N : SSet.{u} :=
    SSet.pathHomotopyFiber (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)
  let e : TopCat.toSSet.obj F ≅ N := SSet.singularPathHomotopyFiberIso f y
  let P : TopCat.{u} := TopCat.pathObject Y
  let Q : SSet.{u} := SSet.pathSpace (TopCat.toSSet.obj Y)
  let b : TopCat.toSSet.obj P ≅ Q := originalTopPathSingularIso Y
  let pF : F ⟶ P := TopCat.homotopyFiberPath f y
  let pN : N ⟶ Q :=
    SSet.pathHomotopyFiberPath (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm y)
  have hforward : e.hom ≫ pN = TopCat.toSSet.map pF ≫ b.hom := by
    let c := TopCat.toSSet.map
      (TopCat.isoOfHomeo (X := P) (Y := TopCat.of (ContinuousMap unitInterval Y))
        (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Y))).hom
    let d := (SSet.singularPathIso Y).hom
    have h0 : e.hom ≫ pN = (TopCat.toSSet.map pF ≫ c) ≫ d :=
      SSet.singularPathHomotopyFiberIso_hom_path f y
    change e.hom ≫ pN = TopCat.toSSet.map pF ≫ (c ≫ d)
    exact h0.trans (Category.assoc _ _ _)
  have hinverse : e.inv ≫ TopCat.toSSet.map pF = pN ≫ b.inv := by
    have h := congrArg (fun k : TopCat.toSSet.obj F ⟶ Q => e.inv ≫ k ≫ b.inv) hforward
    have hnormalized : pN ≫ b.inv = e.inv ≫ TopCat.toSSet.map pF := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using h
    exact hnormalized.symm
  have hcounit :
      SSet.toTop.map (TopCat.toSSet.map pF) ≫ sSetTopAdj.counit.app P =
        sSetTopAdj.counit.app F ≫ pF := by
    simpa only [Functor.comp_map, Functor.id_map] using sSetTopAdj.counit.naturality pF
  change (SSet.toTop.map e.inv ≫ sSetTopAdj.counit.app F) ≫ pF =
    SSet.toTop.map pN ≫ SSet.toTop.map b.inv ≫ sSetTopAdj.counit.app P
  calc
    _ = SSet.toTop.map e.inv ≫ (sSetTopAdj.counit.app F ≫ pF) :=
      Category.assoc _ _ _
    _ = SSet.toTop.map e.inv ≫
        (SSet.toTop.map (TopCat.toSSet.map pF) ≫ sSetTopAdj.counit.app P) :=
      congrArg (fun h : SSet.toTop.obj (TopCat.toSSet.obj F) ⟶ P =>
        SSet.toTop.map e.inv ≫ h) hcounit.symm
    _ = (SSet.toTop.map e.inv ≫ SSet.toTop.map (TopCat.toSSet.map pF)) ≫
        sSetTopAdj.counit.app P := (Category.assoc _ _ _).symm
    _ = SSet.toTop.map (e.inv ≫ TopCat.toSSet.map pF) ≫ sSetTopAdj.counit.app P :=
      congrArg (fun h : SSet.toTop.obj N ⟶ SSet.toTop.obj (TopCat.toSSet.obj P) =>
        h ≫ sSetTopAdj.counit.app P)
          (SSet.toTop.map_comp e.inv (TopCat.toSSet.map pF)).symm
    _ = SSet.toTop.map (pN ≫ b.inv) ≫ sSetTopAdj.counit.app P :=
      congrArg (fun h : N ⟶ TopCat.toSSet.obj P =>
        SSet.toTop.map h ≫ sSetTopAdj.counit.app P) hinverse
    _ = (SSet.toTop.map pN ≫ SSet.toTop.map b.inv) ≫ sSetTopAdj.counit.app P :=
      congrArg (fun h : SSet.toTop.obj N ⟶ SSet.toTop.obj (TopCat.toSSet.obj P) =>
        h ≫ sSetTopAdj.counit.app P) (SSet.toTop.map_comp pN b.inv)
    _ = _ := Category.assoc _ _ _

/-- The actual comparison is weak for every original map and basepoint, with the fiber unchanged. -/
theorem originalSingularPathFiberRealizationComparison_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    TopCat.weakHomotopyEquivalences (originalSingularPathFiberRealizationComparison f y) := by
  let F : TopCat.{u} := TopCat.homotopyFiber f y
  let e := SSet.singularPathHomotopyFiberIso f y
  have hi : TopCat.weakHomotopyEquivalences (SSet.toTop.map e.inv) :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hc : TopCat.weakHomotopyEquivalences (sSetTopAdj.counit.app F) :=
    SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences F
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hi hc

end SSet

namespace SSet.KanComplex

/-- Every selected native lift gives the actual comparison with the fixed original fiber. -/
noncomputable def nativeCoverOriginalTopPathFiberComparison
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    SSet.toTop.obj
        (SSet.pathHomotopyFiber
          (pullback.snd (TopCat.toSSet.map f)
            (nativeCoverProjection (TopCat.toSSet.obj Y) a)) v) ⟶
      TopCat.homotopyFiber f y :=
  SSet.toTop.map
      (nativeCoverBaseChangePathFiberMap (TopCat.toSSet.map f) a v hv) ≫
    SSet.originalSingularPathFiberRealizationComparison f y

/-- Its original source coordinate is the realized native first projection and counit on X. -/
theorem nativeCoverOriginalTopPathFiberComparison_toTotal
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    nativeCoverOriginalTopPathFiberComparison f y a v hv ≫
        TopCat.homotopyFiberToTotal f y =
      SSet.toTop.map
          (SSet.pathHomotopyFiberToTotal
              (pullback.snd (TopCat.toSSet.map f)
                (nativeCoverProjection (TopCat.toSSet.obj Y) a)) v ≫
            pullback.fst (TopCat.toSSet.map f)
              (nativeCoverProjection (TopCat.toSSet.obj Y) a)) ≫
        sSetTopAdj.counit.app X := by
  let sf : TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj Y := TopCat.toSSet.map f
  let ys : (TopCat.toSSet.obj Y) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  let p := nativeCoverProjection (TopCat.toSSet.obj Y) a
  let q := pullback.snd sf p
  let r := pullback.fst sf p
  let A : SSet.{u} := SSet.pathHomotopyFiber q v
  let N : SSet.{u} := SSet.pathHomotopyFiber sf ys
  let C : A ⟶ N := nativeCoverBaseChangePathFiberMap sf a v hv
  let κ : SSet.toTop.obj N ⟶ TopCat.homotopyFiber f y :=
    SSet.originalSingularPathFiberRealizationComparison f y
  let tA : A ⟶ pullback sf p := SSet.pathHomotopyFiberToTotal q v
  let tN : N ⟶ TopCat.toSSet.obj X := SSet.pathHomotopyFiberToTotal sf ys
  have hC : C ≫ tN = tA ≫ r :=
    nativeCoverBaseChangePathFiberMap_toTotal sf a v hv
  have hκ : κ ≫ TopCat.homotopyFiberToTotal f y =
      SSet.toTop.map tN ≫ sSetTopAdj.counit.app X :=
    SSet.originalSingularPathFiberRealizationComparison_toTotal f y
  change (SSet.toTop.map C ≫ κ) ≫ TopCat.homotopyFiberToTotal f y =
    SSet.toTop.map (tA ≫ r) ≫ sSetTopAdj.counit.app X
  calc
    _ = SSet.toTop.map C ≫ (κ ≫ TopCat.homotopyFiberToTotal f y) :=
      Category.assoc _ _ _
    _ = SSet.toTop.map C ≫
        (SSet.toTop.map tN ≫ sSetTopAdj.counit.app X) :=
      congrArg (fun h : SSet.toTop.obj N ⟶ X => SSet.toTop.map C ≫ h) hκ
    _ = (SSet.toTop.map C ≫ SSet.toTop.map tN) ≫ sSetTopAdj.counit.app X :=
      (Category.assoc _ _ _).symm
    _ = SSet.toTop.map (C ≫ tN) ≫ sSetTopAdj.counit.app X :=
      congrArg (fun h : SSet.toTop.obj A ⟶
          SSet.toTop.obj (TopCat.toSSet.obj X) => h ≫ sSetTopAdj.counit.app X)
        (SSet.toTop.map_comp C tN).symm
    _ = _ := congrArg (fun h : A ⟶ TopCat.toSSet.obj X =>
      SSet.toTop.map h ≫ sSetTopAdj.counit.app X) hC

/-- Its full path is projected by the cover and the actual interval/singular/counit bridges. -/
theorem nativeCoverOriginalTopPathFiberComparison_path
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    nativeCoverOriginalTopPathFiberComparison f y a v hv ≫
        TopCat.homotopyFiberPath f y =
      SSet.toTop.map
          (SSet.pathHomotopyFiberPath
              (pullback.snd (TopCat.toSSet.map f)
                (nativeCoverProjection (TopCat.toSSet.obj Y) a)) v ≫
            (ihom (Δ[1] : SSet.{u})).map
              (nativeCoverProjection (TopCat.toSSet.obj Y) a)) ≫
        SSet.toTop.map
            (TopCat.toSSet.mapIso
                (TopCat.isoOfHomeo
                  (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Y))) ≪≫
              SSet.singularPathIso Y).inv ≫
          sSetTopAdj.counit.app (TopCat.pathObject Y) := by
  let sf : TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj Y := TopCat.toSSet.map f
  let ys : (TopCat.toSSet.obj Y) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  let P : SSet.{u} := nativeCover (TopCat.toSSet.obj Y) a
  let p : P ⟶ TopCat.toSSet.obj Y :=
    nativeCoverProjection (TopCat.toSSet.obj Y) a
  let q := pullback.snd sf p
  let A : SSet.{u} := SSet.pathHomotopyFiber q v
  let N : SSet.{u} := SSet.pathHomotopyFiber sf ys
  let C : A ⟶ N := nativeCoverBaseChangePathFiberMap sf a v hv
  let κ : SSet.toTop.obj N ⟶ TopCat.homotopyFiber f y :=
    SSet.originalSingularPathFiberRealizationComparison f y
  let HP : SSet.{u} := SSet.pathSpace P
  let HY : SSet.{u} := SSet.pathSpace (TopCat.toSSet.obj Y)
  let pA : A ⟶ HP := SSet.pathHomotopyFiberPath q v
  let pN : N ⟶ HY := SSet.pathHomotopyFiberPath sf ys
  let m : HP ⟶ HY := (ihom (Δ[1] : SSet.{u})).map p
  let T : TopCat.{u} := TopCat.pathObject Y
  let b : TopCat.toSSet.obj T ≅ HY :=
    TopCat.toSSet.mapIso
        (TopCat.isoOfHomeo (X := T) (Y := TopCat.of (ContinuousMap unitInterval Y))
          (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Y))) ≪≫
      SSet.singularPathIso Y
  let k : SSet.toTop.obj HY ⟶ T :=
    SSet.toTop.map b.inv ≫ sSetTopAdj.counit.app T
  have hC : C ≫ pN = pA ≫ m :=
    nativeCoverBaseChangePathFiberMap_path sf a v hv
  have hκ : κ ≫ TopCat.homotopyFiberPath f y = SSet.toTop.map pN ≫ k :=
    SSet.originalSingularPathFiberRealizationComparison_path f y
  change (SSet.toTop.map C ≫ κ) ≫ TopCat.homotopyFiberPath f y =
    SSet.toTop.map (pA ≫ m) ≫ k
  calc
    _ = SSet.toTop.map C ≫ (κ ≫ TopCat.homotopyFiberPath f y) :=
      Category.assoc _ _ _
    _ = SSet.toTop.map C ≫ (SSet.toTop.map pN ≫ k) :=
      congrArg (fun h : SSet.toTop.obj N ⟶ T => SSet.toTop.map C ≫ h) hκ
    _ = (SSet.toTop.map C ≫ SSet.toTop.map pN) ≫ k :=
      (Category.assoc _ _ _).symm
    _ = SSet.toTop.map (C ≫ pN) ≫ k :=
      congrArg (fun h : SSet.toTop.obj A ⟶ SSet.toTop.obj HY => h ≫ k)
        (SSet.toTop.map_comp C pN).symm
    _ = _ := congrArg (fun h : A ⟶ HY => SSet.toTop.map h ≫ k) hC

/-- The same actual comparison is weak for every original map and selected native lift. -/
theorem nativeCoverOriginalTopPathFiberComparison_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    TopCat.weakHomotopyEquivalences
      (nativeCoverOriginalTopPathFiberComparison f y a v hv) := by
  let C := nativeCoverBaseChangePathFiberMap (TopCat.toSSet.map f) a v hv
  let κ := SSet.originalSingularPathFiberRealizationComparison f y
  have hC : SSet.realizationWeakEquivalences C :=
    nativeCoverBaseChangePathFiberMap_mem_realizationWeakEquivalences
      (TopCat.toSSet.map f) a v hv
  have hRC : TopCat.weakHomotopyEquivalences (SSet.toTop.map C) :=
    (TopCat.mem_weakHomotopyEquivalences_iff (SSet.toTop.map C)).mpr
      ((SSet.mem_realizationWeakEquivalences_iff C).mp hC)
  have hκ : TopCat.weakHomotopyEquivalences κ :=
    SSet.originalSingularPathFiberRealizationComparison_mem_weakHomotopyEquivalences f y
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map C ≫ κ)
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hRC hκ

end SSet.KanComplex

open HomotopicalAlgebra CategoryTheory.MorphismProperty

namespace SSet

/-- The actual realization unit sends a vertex to its represented singular realized vertex. -/
theorem unit_vertex_realization (P : SSet.{u}) (v : P _⦋0⦌) :
    (sSetTopAdj.unit.app P).app (Opposite.op ⦋0⦌) v =
      TopCat.toSSetObj₀Equiv.symm (SSet.realizedVertex v) := by
  let e : (Δ[0] : SSet.{u}) ⟶ P := (SSet.yonedaEquiv (X := P) (n := ⦋0⦌)).symm v
  have hn : e ≫ sSetTopAdj.unit.app P =
      sSetTopAdj.unit.app (Δ[0] : SSet.{u}) ≫
        TopCat.toSSet.map (SSet.toTop.map e) := by
    simpa only [Functor.id_map, Functor.comp_map] using sSetTopAdj.unit.naturality e
  have ha : sSetTopAdj.homEquiv (Δ[0] : SSet.{u}) (SSet.toTop.obj P)
      (SSet.toTop.map e) = e ≫ sSetTopAdj.unit.app P := by
    rw [Adjunction.homEquiv_unit]
    exact hn.symm
  have hz : e ≫ sSetTopAdj.unit.app P =
      SSet.const (TopCat.toSSetObj₀Equiv.symm (SSet.toTop.map e default)) :=
    ha.symm.trans (sSetTopAdj_homEquiv_stdSimplex_zero (SSet.toTop.map e))
  have hv := congrArg (SSet.yonedaEquiv (X := TopCat.toSSet.obj (SSet.toTop.obj P))
    (n := ⦋0⦌)) hz
  simpa only [SSet.yonedaEquiv_comp, e, Equiv.apply_symm_apply,
    SSet.yonedaEquiv_const, SSet.realizedVertex] using hv

/-- The actual lifted-interval and singular path comparisons give the canonical path Iso. -/
noncomputable def topPathSingularIso (Y : TopCat.{u}) :
    TopCat.toSSet.obj (TopCat.pathObject Y) ≅
      SSet.pathSpace (TopCat.toSSet.obj Y) :=
  TopCat.toSSet.mapIso
      (TopCat.isoOfHomeo (X := TopCat.pathObject Y)
        (Y := TopCat.of (ContinuousMap unitInterval Y))
        (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Y))) ≪≫
    SSet.singularPathIso Y

/-- The entire singular path comparison is natural for actual Top maps. -/
theorem topPathSingularIso_naturality
    {Y Z : TopCat.{u}} (h : Y ⟶ Z) :
    TopCat.toSSet.map (TopCat.pathObjectMap h) ≫ (topPathSingularIso Z).hom =
      (topPathSingularIso Y).hom ≫
        (ihom (Δ[1] : SSet.{u})).map (TopCat.toSSet.map h) := by
  let OY : TopCat.{u} := TopCat.of (ContinuousMap unitInterval Y)
  let OZ : TopCat.{u} := TopCat.of (ContinuousMap unitInterval Z)
  let dY : TopCat.pathObject Y ≅ OY :=
    TopCat.isoOfHomeo (X := TopCat.pathObject Y) (Y := OY)
      (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Y))
  let dZ : TopCat.pathObject Z ≅ OZ :=
    TopCat.isoOfHomeo (X := TopCat.pathObject Z) (Y := OZ)
      (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl Z))
  let z : OY ⟶ OZ := TopCat.intervalContinuousMapPostcomp h.hom
  let bY : TopCat.toSSet.obj OY ⟶ SSet.pathSpace (TopCat.toSSet.obj Y) :=
    (SSet.singularPathIso Y).hom
  let bZ : TopCat.toSSet.obj OZ ⟶ SSet.pathSpace (TopCat.toSSet.obj Z) :=
    (SSet.singularPathIso Z).hom
  let m : SSet.pathSpace (TopCat.toSSet.obj Y) ⟶
      SSet.pathSpace (TopCat.toSSet.obj Z) :=
    (ihom (Δ[1] : SSet.{u})).map (TopCat.toSSet.map h)
  let ψ := TopCat.toSSet.map (TopCat.pathObjectMap h)
  have hd : TopCat.pathObjectMap h ≫ dZ.hom = dY.hom ≫ z := by
    apply TopCat.hom_ext
    ext γ t
    rfl
  have hs : ψ ≫ TopCat.toSSet.map dZ.hom =
      TopCat.toSSet.map dY.hom ≫ TopCat.toSSet.map z :=
    (TopCat.toSSet.map_comp (TopCat.pathObjectMap h) dZ.hom).symm.trans
      ((congrArg TopCat.toSSet.map hd).trans (TopCat.toSSet.map_comp dY.hom z))
  have hb : TopCat.toSSet.map z ≫ bZ = bY ≫ m :=
    SSet.singularPathComparison_naturality h.hom
  change ψ ≫ (TopCat.toSSet.map dZ.hom ≫ bZ) =
    (TopCat.toSSet.map dY.hom ≫ bY) ≫ m
  calc
    _ = (ψ ≫ TopCat.toSSet.map dZ.hom) ≫ bZ := (Category.assoc _ _ _).symm
    _ = (TopCat.toSSet.map dY.hom ≫ TopCat.toSSet.map z) ≫ bZ :=
      congrArg (fun k : TopCat.toSSet.obj (TopCat.pathObject Y) ⟶
        TopCat.toSSet.obj OZ => k ≫ bZ) hs
    _ = TopCat.toSSet.map dY.hom ≫ (TopCat.toSSet.map z ≫ bZ) :=
      Category.assoc _ _ _
    _ = TopCat.toSSet.map dY.hom ≫ (bY ≫ m) :=
      congrArg (fun k : TopCat.toSSet.obj OY ⟶ SSet.pathSpace (TopCat.toSSet.obj Z) =>
        TopCat.toSSet.map dY.hom ≫ k) hb
    _ = _ := (Category.assoc _ _ _).symm

/-- Its inverse retains the same complete path naturality square. -/
theorem topPathSingularIso_inv_naturality
    {Y Z : TopCat.{u}} (h : Y ⟶ Z) :
    (topPathSingularIso Y).inv ≫ TopCat.toSSet.map (TopCat.pathObjectMap h) =
      (ihom (Δ[1] : SSet.{u})).map (TopCat.toSSet.map h) ≫
        (topPathSingularIso Z).inv := by
  let bY := topPathSingularIso Y
  let bZ := topPathSingularIso Z
  let ψ := TopCat.toSSet.map (TopCat.pathObjectMap h)
  let m := (ihom (Δ[1] : SSet.{u})).map (TopCat.toSSet.map h)
  have hn : ψ ≫ bZ.hom = bY.hom ≫ m := topPathSingularIso_naturality h
  have he := congrArg (fun k : TopCat.toSSet.obj (TopCat.pathObject Y) ⟶
      SSet.pathSpace (TopCat.toSSet.obj Z) => bY.inv ≫ k ≫ bZ.inv) hn
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using he

/-- The actual adjunction units define the original endpoint path-fiber map. -/
noncomputable def unitPathHomotopyFiberMap
    {Q P : SSet.{u}} (q : Q ⟶ P) (v : P _⦋0⦌) :
    SSet.pathHomotopyFiber q v ⟶
      SSet.pathHomotopyFiber (TopCat.toSSet.map (SSet.toTop.map q))
        (TopCat.toSSetObj₀Equiv.symm (SSet.realizedVertex v)) :=
  SSet.pathHomotopyFiberMap (sSetTopAdj.unit.app Q) (sSetTopAdj.unit.app P)
    (by simpa only [Functor.id_map, Functor.comp_map] using sSetTopAdj.unit.naturality q)
    (unit_vertex_realization P v)

/-- Realize the unit fiber map and apply the counit at the same compact-open realized fiber. -/
noncomputable def unitRealizationPathFiberComparison
    {Q P : SSet.{u}} (q : Q ⟶ P) (v : P _⦋0⦌) :
    SSet.toTop.obj (SSet.pathHomotopyFiber q v) ⟶
      TopCat.homotopyFiber (SSet.toTop.map q) (SSet.realizedVertex v) :=
  SSet.toTop.map (unitPathHomotopyFiberMap q v) ≫
    SSet.originalSingularPathFiberRealizationComparison
      (SSet.toTop.map q) (SSet.realizedVertex v)

/-- The original total coordinate is retained by the actual left adjunction triangle. -/
theorem unitRealizationPathFiberComparison_toTotal
    {Q P : SSet.{u}} (q : Q ⟶ P) (v : P _⦋0⦌) :
    unitRealizationPathFiberComparison q v ≫
        TopCat.homotopyFiberToTotal (SSet.toTop.map q) (SSet.realizedVertex v) =
      SSet.toTop.map (SSet.pathHomotopyFiberToTotal q v) := by
  let rq : SSet.toTop.obj Q ⟶ SSet.toTop.obj P := SSet.toTop.map q
  let rv : SSet.toTop.obj P := SSet.realizedVertex v
  let q' : TopCat.toSSet.obj (SSet.toTop.obj Q) ⟶
      TopCat.toSSet.obj (SSet.toTop.obj P) := TopCat.toSSet.map rq
  let v' : (TopCat.toSSet.obj (SSet.toTop.obj P)) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm rv
  let A : SSet.{u} := SSet.pathHomotopyFiber q v
  let N : SSet.{u} := SSet.pathHomotopyFiber q' v'
  let V : A ⟶ N := unitPathHomotopyFiberMap q v
  let κ : SSet.toTop.obj N ⟶ TopCat.homotopyFiber rq rv :=
    SSet.originalSingularPathFiberRealizationComparison rq rv
  let tA : A ⟶ Q := SSet.pathHomotopyFiberToTotal q v
  let tN : N ⟶ TopCat.toSSet.obj (SSet.toTop.obj Q) :=
    SSet.pathHomotopyFiberToTotal q' v'
  have hq : q ≫ sSetTopAdj.unit.app P = sSetTopAdj.unit.app Q ≫ q' := by
    simpa only [Functor.id_map, Functor.comp_map] using sSetTopAdj.unit.naturality q
  have hc : (sSetTopAdj.unit.app P).app (Opposite.op ⦋0⦌) v = v' :=
    unit_vertex_realization P v
  have hV : V ≫ tN = tA ≫ sSetTopAdj.unit.app Q := by
    change SSet.pathHomotopyFiberMap (sSetTopAdj.unit.app Q) (sSetTopAdj.unit.app P)
      hq hc ≫ tN = tA ≫ sSetTopAdj.unit.app Q
    exact SSet.pathHomotopyFiberMap_toTotal _ _ _ _
  have hκ : κ ≫ TopCat.homotopyFiberToTotal rq rv =
      SSet.toTop.map tN ≫ sSetTopAdj.counit.app (SSet.toTop.obj Q) :=
    SSet.originalSingularPathFiberRealizationComparison_toTotal rq rv
  have ht : SSet.toTop.map (sSetTopAdj.unit.app Q) ≫
      sSetTopAdj.counit.app (SSet.toTop.obj Q) = 𝟙 (SSet.toTop.obj Q) :=
    sSetTopAdj.left_triangle_components Q
  change (SSet.toTop.map V ≫ κ) ≫ TopCat.homotopyFiberToTotal rq rv = SSet.toTop.map tA
  calc
    _ = SSet.toTop.map V ≫ (κ ≫ TopCat.homotopyFiberToTotal rq rv) :=
      Category.assoc _ _ _
    _ = SSet.toTop.map V ≫
        (SSet.toTop.map tN ≫ sSetTopAdj.counit.app (SSet.toTop.obj Q)) :=
      congrArg (fun k : SSet.toTop.obj N ⟶ SSet.toTop.obj Q => SSet.toTop.map V ≫ k) hκ
    _ = (SSet.toTop.map V ≫ SSet.toTop.map tN) ≫
        sSetTopAdj.counit.app (SSet.toTop.obj Q) := (Category.assoc _ _ _).symm
    _ = SSet.toTop.map (V ≫ tN) ≫ sSetTopAdj.counit.app (SSet.toTop.obj Q) :=
      congrArg (fun k : SSet.toTop.obj A ⟶
          SSet.toTop.obj (TopCat.toSSet.obj (SSet.toTop.obj Q)) =>
        k ≫ sSetTopAdj.counit.app (SSet.toTop.obj Q)) (SSet.toTop.map_comp V tN).symm
    _ = SSet.toTop.map (tA ≫ sSetTopAdj.unit.app Q) ≫
        sSetTopAdj.counit.app (SSet.toTop.obj Q) :=
      congrArg (fun k : A ⟶ TopCat.toSSet.obj (SSet.toTop.obj Q) =>
        SSet.toTop.map k ≫ sSetTopAdj.counit.app (SSet.toTop.obj Q)) hV
    _ = (SSet.toTop.map tA ≫ SSet.toTop.map (sSetTopAdj.unit.app Q)) ≫
        sSetTopAdj.counit.app (SSet.toTop.obj Q) :=
      congrArg (fun k : SSet.toTop.obj A ⟶
          SSet.toTop.obj (TopCat.toSSet.obj (SSet.toTop.obj Q)) =>
        k ≫ sSetTopAdj.counit.app (SSet.toTop.obj Q))
          (SSet.toTop.map_comp tA (sSetTopAdj.unit.app Q))
    _ = SSet.toTop.map tA ≫
        (SSet.toTop.map (sSetTopAdj.unit.app Q) ≫
          sSetTopAdj.counit.app (SSet.toTop.obj Q)) := Category.assoc _ _ _
    _ = SSet.toTop.map tA ≫ 𝟙 (SSet.toTop.obj Q) :=
      congrArg (fun k : SSet.toTop.obj Q ⟶ SSet.toTop.obj Q => SSet.toTop.map tA ≫ k) ht
    _ = _ := Category.comp_id _

/-- The entire path uses the actual unit and the canonical interval/singular path Iso. -/
theorem unitRealizationPathFiberComparison_path
    {Q P : SSet.{u}} (q : Q ⟶ P) (v : P _⦋0⦌) :
    unitRealizationPathFiberComparison q v ≫
        TopCat.homotopyFiberPath (SSet.toTop.map q) (SSet.realizedVertex v) =
      SSet.toTop.map
          (SSet.pathHomotopyFiberPath q v ≫
            (ihom (Δ[1] : SSet.{u})).map (sSetTopAdj.unit.app P)) ≫
        SSet.toTop.map (topPathSingularIso (SSet.toTop.obj P)).inv ≫
          sSetTopAdj.counit.app (TopCat.pathObject (SSet.toTop.obj P)) := by
  let rq : SSet.toTop.obj Q ⟶ SSet.toTop.obj P := SSet.toTop.map q
  let rv : SSet.toTop.obj P := SSet.realizedVertex v
  let q' := TopCat.toSSet.map rq
  let v' := TopCat.toSSetObj₀Equiv.symm rv
  let A : SSet.{u} := SSet.pathHomotopyFiber q v
  let N : SSet.{u} := SSet.pathHomotopyFiber q' v'
  let V : A ⟶ N := unitPathHomotopyFiberMap q v
  let κ : SSet.toTop.obj N ⟶ TopCat.homotopyFiber rq rv :=
    SSet.originalSingularPathFiberRealizationComparison rq rv
  let H : SSet.{u} := SSet.pathSpace (TopCat.toSSet.obj (SSet.toTop.obj P))
  let pA : A ⟶ SSet.pathSpace P := SSet.pathHomotopyFiberPath q v
  let pN : N ⟶ H := SSet.pathHomotopyFiberPath q' v'
  let m : SSet.pathSpace P ⟶ H := (ihom (Δ[1] : SSet.{u})).map (sSetTopAdj.unit.app P)
  let T : TopCat.{u} := TopCat.pathObject (SSet.toTop.obj P)
  let b : TopCat.toSSet.obj T ≅ H := topPathSingularIso (SSet.toTop.obj P)
  let k : SSet.toTop.obj H ⟶ T := SSet.toTop.map b.inv ≫ sSetTopAdj.counit.app T
  have hq : q ≫ sSetTopAdj.unit.app P = sSetTopAdj.unit.app Q ≫ q' := by
    simpa only [Functor.id_map, Functor.comp_map] using sSetTopAdj.unit.naturality q
  have hc : (sSetTopAdj.unit.app P).app (Opposite.op ⦋0⦌) v = v' :=
    unit_vertex_realization P v
  have hV : V ≫ pN = pA ≫ m := by
    change SSet.pathHomotopyFiberMap (sSetTopAdj.unit.app Q) (sSetTopAdj.unit.app P)
      hq hc ≫ pN = pA ≫ m
    exact SSet.pathHomotopyFiberMap_path _ _ _ _
  have hκ : κ ≫ TopCat.homotopyFiberPath rq rv = SSet.toTop.map pN ≫ k :=
    SSet.originalSingularPathFiberRealizationComparison_path rq rv
  change (SSet.toTop.map V ≫ κ) ≫ TopCat.homotopyFiberPath rq rv =
    SSet.toTop.map (pA ≫ m) ≫ k
  calc
    _ = SSet.toTop.map V ≫ (κ ≫ TopCat.homotopyFiberPath rq rv) := Category.assoc _ _ _
    _ = SSet.toTop.map V ≫ (SSet.toTop.map pN ≫ k) :=
      congrArg (fun j : SSet.toTop.obj N ⟶ T => SSet.toTop.map V ≫ j) hκ
    _ = (SSet.toTop.map V ≫ SSet.toTop.map pN) ≫ k := (Category.assoc _ _ _).symm
    _ = SSet.toTop.map (V ≫ pN) ≫ k :=
      congrArg (fun j : SSet.toTop.obj A ⟶ SSet.toTop.obj H => j ≫ k)
        (SSet.toTop.map_comp V pN).symm
    _ = _ := congrArg (fun j : A ⟶ H => SSet.toTop.map j ≫ k) hV

/-- The actual unit-based comparison is weak when its original target base is Kan. -/
theorem unitRealizationPathFiberComparison_mem_weakHomotopyEquivalences
    {Q P : SSet.{u}} [SSet.KanComplex P] (q : Q ⟶ P) (v : P _⦋0⦌) :
    TopCat.weakHomotopyEquivalences (unitRealizationPathFiberComparison q v) := by
  let _ : IsRightProper SSet.{u} := SSet.modelCategoryQuillen.instIsRightProper
  have hAn : SSet.anodyneExtensions.{u} = trivialCofibrations SSet.{u} := by
    rw [SSet.anodyneExtensions_eq_llp_rlp, ← SSet.modelCategoryQuillen.fibrations_eq]
    exact fibrations_llp _
  let _ : HasFunctorialFactorization (trivialCofibrations SSet.{u})
      (fibrations SSet.{u}) := by
    rw [← hAn]
    infer_instance
  let _ : SSet.KanComplex (TopCat.toSSet.obj (SSet.toTop.obj P)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex ((𝟭 SSet.{u}).obj P) := by
    simpa only [Functor.id_obj] using (inferInstance : SSet.KanComplex P)
  let _ : SSet.KanComplex ((SSet.toTop ⋙ TopCat.toSSet).obj P) := by
    change SSet.KanComplex (TopCat.toSSet.obj (SSet.toTop.obj P))
    infer_instance
  have hq : q ≫ sSetTopAdj.unit.app P =
      sSetTopAdj.unit.app Q ≫ TopCat.toSSet.map (SSet.toTop.map q) := by
    simpa only [Functor.id_map, Functor.comp_map] using sSetTopAdj.unit.naturality q
  have hc : (sSetTopAdj.unit.app P).app (Opposite.op ⦋0⦌) v =
      TopCat.toSSetObj₀Equiv.symm (SSet.realizedVertex v) := unit_vertex_realization P v
  have hV : SSet.realizationWeakEquivalences (unitPathHomotopyFiberMap q v) := by
    change SSet.realizationWeakEquivalences
      (SSet.pathHomotopyFiberMap (sSetTopAdj.unit.app Q) (sSetTopAdj.unit.app P) hq hc)
    exact SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences _ _ _ _
      (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences Q)
      (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences P)
  have hRV : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (unitPathHomotopyFiberMap q v)) :=
    (TopCat.mem_weakHomotopyEquivalences_iff _).mpr
      ((SSet.mem_realizationWeakEquivalences_iff _).mp hV)
  have hκ : TopCat.weakHomotopyEquivalences
      (SSet.originalSingularPathFiberRealizationComparison
        (SSet.toTop.map q) (SSet.realizedVertex v)) :=
    SSet.originalSingularPathFiberRealizationComparison_mem_weakHomotopyEquivalences _ _
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hRV hκ


end SSet

namespace SSet.KanComplex

/-- Every selected realized native point projects to the same original Top point. -/
theorem nativeCoverRealizedPoint_projection
    {Y : TopCat.{u}} (y : Y) (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    (SSet.toTop.map (nativeCoverProjection (TopCat.toSSet.obj Y) a) ≫
      sSetTopAdj.counit.app Y) (SSet.realizedVertex v) = y := by
  let p := nativeCoverProjection (TopCat.toSSet.obj Y) a
  change sSetTopAdj.counit.app Y (SSet.toTop.map p (SSet.realizedVertex v)) = y
  calc
    _ = sSetTopAdj.counit.app Y (SSet.realizedVertex (p.app (Opposite.op ⦋0⦌) v)) :=
      congrArg (fun z : SSet.toTop.obj (TopCat.toSSet.obj Y) =>
        sSetTopAdj.counit.app Y z) (SSet.realizedVertex_naturality p v).symm
    _ = sSetTopAdj.counit.app Y (SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm y)) :=
      congrArg (fun z : (TopCat.toSSet.obj Y) _⦋0⦌ =>
        sSetTopAdj.counit.app Y (SSet.realizedVertex z)) hv
    _ = TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm y) :=
      TopCat.counit_realizedVertex _
    _ = y := TopCat.toSSetObj₀Equiv.apply_symm_apply y

/-- The realized literal native pullback retains the original Top map square. -/
theorem nativeCoverRealizedPullback_square
    {X Y : TopCat.{u}} (f : X ⟶ Y) (a : (TopCat.toSSet.obj Y) _⦋0⦌) :
    SSet.toTop.map
          (pullback.snd (TopCat.toSSet.map f)
            (nativeCoverProjection (TopCat.toSSet.obj Y) a)) ≫
        (SSet.toTop.map (nativeCoverProjection (TopCat.toSSet.obj Y) a) ≫
          sSetTopAdj.counit.app Y) =
      (SSet.toTop.map
          (pullback.fst (TopCat.toSSet.map f)
            (nativeCoverProjection (TopCat.toSSet.obj Y) a)) ≫
        sSetTopAdj.counit.app X) ≫ f := by
  let sf := TopCat.toSSet.map f
  let p := nativeCoverProjection (TopCat.toSSet.obj Y) a
  let q := pullback.snd sf p
  let r := pullback.fst sf p
  have hs : q ≫ p = r ≫ sf := (pullback.condition (f := sf) (g := p)).symm
  have hn : SSet.toTop.map sf ≫ sSetTopAdj.counit.app Y =
      sSetTopAdj.counit.app X ≫ f := by
    simpa only [Functor.comp_map, Functor.id_map] using sSetTopAdj.counit.naturality f
  change SSet.toTop.map q ≫ (SSet.toTop.map p ≫ sSetTopAdj.counit.app Y) =
    (SSet.toTop.map r ≫ sSetTopAdj.counit.app X) ≫ f
  calc
    _ = (SSet.toTop.map q ≫ SSet.toTop.map p) ≫ sSetTopAdj.counit.app Y :=
      (Category.assoc _ _ _).symm
    _ = SSet.toTop.map (q ≫ p) ≫ sSetTopAdj.counit.app Y :=
      congrArg (fun k : SSet.toTop.obj (pullback sf p) ⟶
          SSet.toTop.obj (TopCat.toSSet.obj Y) => k ≫ sSetTopAdj.counit.app Y)
        (SSet.toTop.map_comp q p).symm
    _ = SSet.toTop.map (r ≫ sf) ≫ sSetTopAdj.counit.app Y :=
      congrArg (fun k : pullback sf p ⟶ TopCat.toSSet.obj Y =>
        SSet.toTop.map k ≫ sSetTopAdj.counit.app Y) hs
    _ = (SSet.toTop.map r ≫ SSet.toTop.map sf) ≫ sSetTopAdj.counit.app Y :=
      congrArg (fun k : SSet.toTop.obj (pullback sf p) ⟶
          SSet.toTop.obj (TopCat.toSSet.obj Y) => k ≫ sSetTopAdj.counit.app Y)
        (SSet.toTop.map_comp r sf)
    _ = SSet.toTop.map r ≫ (SSet.toTop.map sf ≫ sSetTopAdj.counit.app Y) :=
      Category.assoc _ _ _
    _ = SSet.toTop.map r ≫ (sSetTopAdj.counit.app X ≫ f) :=
      congrArg (fun k : SSet.toTop.obj (TopCat.toSSet.obj X) ⟶ Y =>
        SSet.toTop.map r ≫ k) hn
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual Top homotopy-pullback map lands in the same original fixed-point fiber. -/
noncomputable def nativeCoverRealizedPathFiberMap
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    TopCat.homotopyFiber
        (SSet.toTop.map
          (pullback.snd (TopCat.toSSet.map f)
            (nativeCoverProjection (TopCat.toSSet.obj Y) a)))
        (SSet.realizedVertex v) ⟶
      TopCat.homotopyFiber f y := by
  let sf := TopCat.toSSet.map f
  let p := nativeCoverProjection (TopCat.toSSet.obj Y) a
  let q := pullback.snd sf p
  let r := pullback.fst sf p
  let l : SSet.toTop.obj (pullback sf p) ⟶ X :=
    SSet.toTop.map r ≫ sSetTopAdj.counit.app X
  let h : SSet.toTop.obj (nativeCover (TopCat.toSSet.obj Y) a) ⟶ Y :=
    SSet.toTop.map p ≫ sSetTopAdj.counit.app Y
  have hc : SSet.toTop.map q ≫ h = l ≫ f := nativeCoverRealizedPullback_square f a
  have hp : h (SSet.realizedVertex v) = y := nativeCoverRealizedPoint_projection y a v hv
  exact TopCat.homotopyPullbackMap
    (f := SSet.toTop.map q) (g := (TopCat.const (SSet.realizedVertex v) :
      TopCat.of PUnit ⟶ SSet.toTop.obj (nativeCover (TopCat.toSSet.obj Y) a)))
    (f' := f) (g' := (TopCat.const y : TopCat.of PUnit ⟶ Y))
    l (𝟙 (TopCat.of PUnit)) h hc (by
      apply TopCat.hom_ext
      ext z
      change h (SSet.realizedVertex v) = y
      exact hp)

/-- Its original source projection is the realized native first projection and counit. -/
theorem nativeCoverRealizedPathFiberMap_toTotal
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    nativeCoverRealizedPathFiberMap f y a v hv ≫ TopCat.homotopyFiberToTotal f y =
      TopCat.homotopyFiberToTotal
          (SSet.toTop.map
            (pullback.snd (TopCat.toSSet.map f)
              (nativeCoverProjection (TopCat.toSSet.obj Y) a)))
          (SSet.realizedVertex v) ≫
        (SSet.toTop.map
            (pullback.fst (TopCat.toSSet.map f)
              (nativeCoverProjection (TopCat.toSSet.obj Y) a)) ≫
          sSetTopAdj.counit.app X) := by
  dsimp only [nativeCoverRealizedPathFiberMap]
  exact TopCat.homotopyPullbackMap_left _ _ _ _ _

/-- Its full defining path is postcomposed by the actual realized native projection. -/
theorem nativeCoverRealizedPathFiberMap_path
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    nativeCoverRealizedPathFiberMap f y a v hv ≫ TopCat.homotopyFiberPath f y =
      TopCat.homotopyFiberPath
          (SSet.toTop.map
            (pullback.snd (TopCat.toSSet.map f)
              (nativeCoverProjection (TopCat.toSSet.obj Y) a)))
          (SSet.realizedVertex v) ≫
        TopCat.pathObjectMap
          (SSet.toTop.map (nativeCoverProjection (TopCat.toSSet.obj Y) a) ≫
            sSetTopAdj.counit.app Y) := by
  dsimp only [nativeCoverRealizedPathFiberMap]
  exact TopCat.homotopyPullbackMap_path _ _ _ _ _

/-- The actual original comparison factors through the literal compact-open realized fiber. -/
theorem nativeCoverOriginalTopPathFiberComparison_factor
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    nativeCoverOriginalTopPathFiberComparison f y a v hv =
      SSet.unitRealizationPathFiberComparison
          (pullback.snd (TopCat.toSSet.map f)
            (nativeCoverProjection (TopCat.toSSet.obj Y) a)) v ≫
        nativeCoverRealizedPathFiberMap f y a v hv := by
  let sf := TopCat.toSSet.map f
  let P : SSet.{u} := nativeCover (TopCat.toSSet.obj Y) a
  let p : P ⟶ TopCat.toSSet.obj Y := nativeCoverProjection (TopCat.toSSet.obj Y) a
  let q := pullback.snd sf p
  let r := pullback.fst sf p
  let A : SSet.{u} := SSet.pathHomotopyFiber q v
  let F : TopCat.{u} := TopCat.homotopyFiber (SSet.toTop.map q) (SSet.realizedVertex v)
  let K : SSet.toTop.obj A ⟶ TopCat.homotopyFiber f y :=
    nativeCoverOriginalTopPathFiberComparison f y a v hv
  let R' : SSet.toTop.obj A ⟶ F := SSet.unitRealizationPathFiberComparison q v
  let α : F ⟶ TopCat.homotopyFiber f y := nativeCoverRealizedPathFiberMap f y a v hv
  let l : SSet.toTop.obj (pullback sf p) ⟶ X :=
    SSet.toTop.map r ≫ sSetTopAdj.counit.app X
  let h : SSet.toTop.obj P ⟶ Y := SSet.toTop.map p ≫ sSetTopAdj.counit.app Y
  let tA : A ⟶ pullback sf p := SSet.pathHomotopyFiberToTotal q v
  let tF : F ⟶ SSet.toTop.obj (pullback sf p) :=
    TopCat.homotopyFiberToTotal (SSet.toTop.map q) (SSet.realizedVertex v)
  have hRt : R' ≫ tF = SSet.toTop.map tA :=
    SSet.unitRealizationPathFiberComparison_toTotal q v
  have hαt : α ≫ TopCat.homotopyFiberToTotal f y = tF ≫ l :=
    nativeCoverRealizedPathFiberMap_toTotal f y a v hv
  have hKt : K ≫ TopCat.homotopyFiberToTotal f y =
      SSet.toTop.map (tA ≫ r) ≫ sSetTopAdj.counit.app X :=
    nativeCoverOriginalTopPathFiberComparison_toTotal f y a v hv
  have htotal : K ≫ TopCat.homotopyFiberToTotal f y =
      (R' ≫ α) ≫ TopCat.homotopyFiberToTotal f y := by
    have he : (R' ≫ α) ≫ TopCat.homotopyFiberToTotal f y =
        SSet.toTop.map (tA ≫ r) ≫ sSetTopAdj.counit.app X := by
      calc
        _ = R' ≫ (α ≫ TopCat.homotopyFiberToTotal f y) := Category.assoc _ _ _
        _ = R' ≫ (tF ≫ l) :=
          congrArg (fun k : F ⟶ X => R' ≫ k) hαt
        _ = (R' ≫ tF) ≫ l := (Category.assoc _ _ _).symm
        _ = SSet.toTop.map tA ≫ l :=
          congrArg (fun k : SSet.toTop.obj A ⟶ SSet.toTop.obj (pullback sf p) => k ≫ l) hRt
        _ = (SSet.toTop.map tA ≫ SSet.toTop.map r) ≫ sSetTopAdj.counit.app X :=
          (Category.assoc _ _ _).symm
        _ = _ := congrArg (fun k : SSet.toTop.obj A ⟶
            SSet.toTop.obj (TopCat.toSSet.obj X) => k ≫ sSetTopAdj.counit.app X)
          (SSet.toTop.map_comp tA r).symm
    exact hKt.trans he.symm
  let HP : SSet.{u} := SSet.pathSpace P
  let H0 : SSet.{u} := SSet.pathSpace (TopCat.toSSet.obj (SSet.toTop.obj P))
  let HY : SSet.{u} := SSet.pathSpace (TopCat.toSSet.obj Y)
  let TP : TopCat.{u} := TopCat.pathObject (SSet.toTop.obj P)
  let TY : TopCat.{u} := TopCat.pathObject Y
  let BP : TopCat.toSSet.obj TP ≅ H0 := SSet.topPathSingularIso (SSet.toTop.obj P)
  let BY : TopCat.toSSet.obj TY ≅ HY := SSet.topPathSingularIso Y
  let kP : SSet.toTop.obj H0 ⟶ TP := SSet.toTop.map BP.inv ≫ sSetTopAdj.counit.app TP
  let kY : SSet.toTop.obj HY ⟶ TY := SSet.toTop.map BY.inv ≫ sSetTopAdj.counit.app TY
  let η : P ⟶ TopCat.toSSet.obj (SSet.toTop.obj P) := sSetTopAdj.unit.app P
  let mη : HP ⟶ H0 := (ihom (Δ[1] : SSet.{u})).map η
  let mh : H0 ⟶ HY := (ihom (Δ[1] : SSet.{u})).map (TopCat.toSSet.map h)
  let mp : HP ⟶ HY := (ihom (Δ[1] : SSet.{u})).map p
  let pA : A ⟶ HP := SSet.pathHomotopyFiberPath q v
  let pF : F ⟶ TP := TopCat.homotopyFiberPath (SSet.toTop.map q) (SSet.realizedVertex v)
  have hn : p ≫ sSetTopAdj.unit.app (TopCat.toSSet.obj Y) =
      η ≫ TopCat.toSSet.map (SSet.toTop.map p) := by
    simpa only [Functor.id_map, Functor.comp_map] using sSetTopAdj.unit.naturality p
  have ht : sSetTopAdj.unit.app (TopCat.toSSet.obj Y) ≫
      TopCat.toSSet.map (sSetTopAdj.counit.app Y) = 𝟙 (TopCat.toSSet.obj Y) :=
    sSetTopAdj.right_triangle_components Y
  have hh : TopCat.toSSet.map h = TopCat.toSSet.map (SSet.toTop.map p) ≫
      TopCat.toSSet.map (sSetTopAdj.counit.app Y) := TopCat.toSSet.map_comp _ _
  have hη : η ≫ TopCat.toSSet.map h = p := by
    calc
      _ = η ≫ (TopCat.toSSet.map (SSet.toTop.map p) ≫
          TopCat.toSSet.map (sSetTopAdj.counit.app Y)) :=
        congrArg (fun k : TopCat.toSSet.obj (SSet.toTop.obj P) ⟶
          TopCat.toSSet.obj Y => η ≫ k) hh
      _ = (η ≫ TopCat.toSSet.map (SSet.toTop.map p)) ≫
          TopCat.toSSet.map (sSetTopAdj.counit.app Y) := (Category.assoc _ _ _).symm
      _ = (p ≫ sSetTopAdj.unit.app (TopCat.toSSet.obj Y)) ≫
          TopCat.toSSet.map (sSetTopAdj.counit.app Y) :=
        congrArg (fun k : P ⟶ TopCat.toSSet.obj (SSet.toTop.obj (TopCat.toSSet.obj Y)) =>
          k ≫ TopCat.toSSet.map (sSetTopAdj.counit.app Y)) hn.symm
      _ = p ≫ (sSetTopAdj.unit.app (TopCat.toSSet.obj Y) ≫
          TopCat.toSSet.map (sSetTopAdj.counit.app Y)) := Category.assoc _ _ _
      _ = p ≫ 𝟙 (TopCat.toSSet.obj Y) :=
        congrArg (fun k : TopCat.toSSet.obj Y ⟶ TopCat.toSSet.obj Y => p ≫ k) ht
      _ = p := Category.comp_id _
  have hm : mη ≫ mh = mp :=
    ((ihom (Δ[1] : SSet.{u})).map_comp η (TopCat.toSSet.map h)).symm.trans
      (congrArg (fun k : P ⟶ TopCat.toSSet.obj Y =>
        (ihom (Δ[1] : SSet.{u})).map k) hη)
  have hB : BP.inv ≫ TopCat.toSSet.map (TopCat.pathObjectMap h) = mh ≫ BY.inv :=
    SSet.topPathSingularIso_inv_naturality h
  have hε : sSetTopAdj.counit.app TP ≫ TopCat.pathObjectMap h =
      SSet.toTop.map (TopCat.toSSet.map (TopCat.pathObjectMap h)) ≫
        sSetTopAdj.counit.app TY := by
    simpa only [Functor.comp_map, Functor.id_map] using
      (sSetTopAdj.counit.naturality (TopCat.pathObjectMap h)).symm
  have htail : kP ≫ TopCat.pathObjectMap h = SSet.toTop.map mh ≫ kY := by
    change (SSet.toTop.map BP.inv ≫ sSetTopAdj.counit.app TP) ≫
      TopCat.pathObjectMap h = SSet.toTop.map mh ≫
        (SSet.toTop.map BY.inv ≫ sSetTopAdj.counit.app TY)
    calc
      _ = SSet.toTop.map BP.inv ≫ (sSetTopAdj.counit.app TP ≫ TopCat.pathObjectMap h) :=
        Category.assoc _ _ _
      _ = SSet.toTop.map BP.inv ≫
          (SSet.toTop.map (TopCat.toSSet.map (TopCat.pathObjectMap h)) ≫
            sSetTopAdj.counit.app TY) :=
        congrArg (fun k : SSet.toTop.obj (TopCat.toSSet.obj TP) ⟶ TY =>
          SSet.toTop.map BP.inv ≫ k) hε
      _ = (SSet.toTop.map BP.inv ≫
          SSet.toTop.map (TopCat.toSSet.map (TopCat.pathObjectMap h))) ≫
            sSetTopAdj.counit.app TY := (Category.assoc _ _ _).symm
      _ = SSet.toTop.map (BP.inv ≫ TopCat.toSSet.map (TopCat.pathObjectMap h)) ≫
          sSetTopAdj.counit.app TY :=
        congrArg (fun k : SSet.toTop.obj H0 ⟶ SSet.toTop.obj (TopCat.toSSet.obj TY) =>
          k ≫ sSetTopAdj.counit.app TY)
            (SSet.toTop.map_comp BP.inv (TopCat.toSSet.map (TopCat.pathObjectMap h))).symm
      _ = SSet.toTop.map (mh ≫ BY.inv) ≫ sSetTopAdj.counit.app TY :=
        congrArg (fun k : H0 ⟶ TopCat.toSSet.obj TY =>
          SSet.toTop.map k ≫ sSetTopAdj.counit.app TY) hB
      _ = (SSet.toTop.map mh ≫ SSet.toTop.map BY.inv) ≫ sSetTopAdj.counit.app TY :=
        congrArg (fun k : SSet.toTop.obj H0 ⟶ SSet.toTop.obj (TopCat.toSSet.obj TY) =>
          k ≫ sSetTopAdj.counit.app TY) (SSet.toTop.map_comp mh BY.inv)
      _ = _ := Category.assoc _ _ _
  have hRp : R' ≫ pF = SSet.toTop.map (pA ≫ mη) ≫ kP :=
    SSet.unitRealizationPathFiberComparison_path q v
  have hαp : α ≫ TopCat.homotopyFiberPath f y = pF ≫ TopCat.pathObjectMap h :=
    nativeCoverRealizedPathFiberMap_path f y a v hv
  have hKp : K ≫ TopCat.homotopyFiberPath f y = SSet.toTop.map (pA ≫ mp) ≫ kY :=
    nativeCoverOriginalTopPathFiberComparison_path f y a v hv
  have hpath : K ≫ TopCat.homotopyFiberPath f y =
      (R' ≫ α) ≫ TopCat.homotopyFiberPath f y := by
    have he : (R' ≫ α) ≫ TopCat.homotopyFiberPath f y =
        SSet.toTop.map (pA ≫ mp) ≫ kY := by
      calc
        _ = R' ≫ (α ≫ TopCat.homotopyFiberPath f y) := Category.assoc _ _ _
        _ = R' ≫ (pF ≫ TopCat.pathObjectMap h) :=
          congrArg (fun k : F ⟶ TY => R' ≫ k) hαp
        _ = (R' ≫ pF) ≫ TopCat.pathObjectMap h := (Category.assoc _ _ _).symm
        _ = (SSet.toTop.map (pA ≫ mη) ≫ kP) ≫ TopCat.pathObjectMap h :=
          congrArg (fun k : SSet.toTop.obj A ⟶ TP => k ≫ TopCat.pathObjectMap h) hRp
        _ = SSet.toTop.map (pA ≫ mη) ≫ (kP ≫ TopCat.pathObjectMap h) :=
          Category.assoc _ _ _
        _ = SSet.toTop.map (pA ≫ mη) ≫ (SSet.toTop.map mh ≫ kY) :=
          congrArg (fun k : SSet.toTop.obj H0 ⟶ TY => SSet.toTop.map (pA ≫ mη) ≫ k) htail
        _ = (SSet.toTop.map (pA ≫ mη) ≫ SSet.toTop.map mh) ≫ kY :=
          (Category.assoc _ _ _).symm
        _ = SSet.toTop.map ((pA ≫ mη) ≫ mh) ≫ kY :=
          congrArg (fun k : SSet.toTop.obj A ⟶ SSet.toTop.obj HY => k ≫ kY)
            (SSet.toTop.map_comp (pA ≫ mη) mh).symm
        _ = SSet.toTop.map (pA ≫ (mη ≫ mh)) ≫ kY :=
          congrArg (fun k : A ⟶ HY => SSet.toTop.map k ≫ kY) (Category.assoc _ _ _)
        _ = _ := congrArg (fun k : HP ⟶ HY => SSet.toTop.map (pA ≫ k) ≫ kY) hm
    exact hKp.trans he.symm
  change K = R' ≫ α
  apply TopCat.homotopyPullback_hom_ext
  · exact htotal
  · apply TopCat.hom_ext
    ext z
  · exact hpath

/-- The actual fixed-original-fiber map is weak for every original map and selected lift. -/
theorem nativeCoverRealizedPathFiberMap_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y)
    (a : (TopCat.toSSet.obj Y) _⦋0⦌)
    (v : (nativeCover (TopCat.toSSet.obj Y) a) _⦋0⦌)
    (hv : (nativeCoverProjection (TopCat.toSSet.obj Y) a).app
      (Opposite.op ⦋0⦌) v = TopCat.toSSetObj₀Equiv.symm y) :
    TopCat.weakHomotopyEquivalences (nativeCoverRealizedPathFiberMap f y a v hv) := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  let _ : SSet.KanComplex (nativeCover (TopCat.toSSet.obj Y) a) :=
    nativeCover_kanComplex (TopCat.toSSet.obj Y) a
  let q := pullback.snd (TopCat.toSSet.map f)
    (nativeCoverProjection (TopCat.toSSet.obj Y) a)
  have hR : TopCat.weakHomotopyEquivalences (SSet.unitRealizationPathFiberComparison q v) :=
    SSet.unitRealizationPathFiberComparison_mem_weakHomotopyEquivalences q v
  have hK : TopCat.weakHomotopyEquivalences
      (nativeCoverOriginalTopPathFiberComparison f y a v hv) :=
    nativeCoverOriginalTopPathFiberComparison_mem_weakHomotopyEquivalences f y a v hv
  have hRK : TopCat.weakHomotopyEquivalences
      (SSet.unitRealizationPathFiberComparison q v ≫
        nativeCoverRealizedPathFiberMap f y a v hv) := by
    rw [← nativeCoverOriginalTopPathFiberComparison_factor f y a v hv]
    exact hK
  exact TopCat.weakHomotopyEquivalences.of_precomp _ _ hR hRK

end SSet.KanComplex
