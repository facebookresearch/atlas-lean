/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorPreserving
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom

/-!
# Functorial lift of strong finite-tensor-preserving functors to colored operad objects

Given categories `V, W` with `FiniteTensor` structures and a strong
finite-tensor-preserving functor `F : V ⥤ W` with comparison
`map F ⋙ tensor_W ≅ tensor_V ⋙ F`, we construct a functor
`ColoredOperadObj Color V ⥤ ColoredOperadObj Color W`.

The mapped collection is `O.toCollection ⋙ F`. The unit source comparison uses
the canonical empty-family iso, and the substitution source comparison uses a
factors iso together with `p.comparisonIso`. Unit and associativity laws are
inherited through comparison lemmas using `singleton_compat` and
`flatten_compat` with canonical nested-family isos and cancellation of the
empty-family comparison.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredOperadObj

open CategoryTheory

universe uColor v₁ v₂ u₁ u₂

variable {Color : Type uColor} {V : Type u₁} {W : Type u₂}
  [Category.{v₁} V] [Category.{v₂} W]
  [FiniteTensor V] [FiniteTensor W]

namespace MapData

variable (F : V ⥤ W)

/-- Canonical iso from empty family in `W` to `map F` of empty family in `V`.

Index equivalence is `Equiv.refl Empty`, components are eliminators. -/
def emptyFamilyIso :
    (FiniteFamily.empty : FiniteFamily W) ≅
      (FiniteFamily.map F).obj (FiniteFamily.empty : FiniteFamily V) :=
  (FiniteFamily.mapEmptyIso F).symm

variable {F}

/-- Iso at a double family coming from `p.comparisonIso`. -/
noncomputable def comparisonIsoApp (p : FiniteTensor.Preserving F)
    (X : FiniteFamily V) :
    (FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W)).obj X ≅
      (FiniteTensor.tensor (V := V) ⋙ F).obj X :=
  p.comparisonIso.app X

/-- Unit source iso `tensor_W empty_W ≅ F (tensor_V empty_V)` built from
`emptyFamilyIso` and `p.comparisonIso`. Hom direction sends `W`-tensor of
`F`-images to `F` of `V`-tensor, as required. Constructed as trans of
`mapIso emptyFamilyIso` and `comparisonIsoApp` to avoid manual coherence. -/
noncomputable def unitSourceIso (p : FiniteTensor.Preserving F) :
    (FiniteTensor.tensor (V := W)).obj (FiniteFamily.empty : FiniteFamily W) ≅
      F.obj ((FiniteTensor.tensor (V := V)).obj
        (FiniteFamily.empty : FiniteFamily V)) :=
  (FiniteTensor.tensor (V := W)).mapIso (emptyFamilyIso F) ≪≫
    comparisonIsoApp p (FiniteFamily.empty : FiniteFamily V)

/-- Factors iso comparing `map F` of substitution factors with factors of
`O ⋙ F`. Uses identity equivalence and identity components. -/
def factorsIso (F : V ⥤ W) (O : ColoredSymmetricCollection Color V)
    (X : ColoredSubstitutionData Color) :
    (FiniteFamily.map F).obj ((substitutionFactors O).obj X) ≅
      (substitutionFactors (O ⋙ F)).obj X := by
  exact
    { hom :=
        { equiv := Equiv.refl (Option X.inner.index)
          hom := fun o =>
            match o with
            | none => 𝟙 (F.obj (O.obj X.outerProfile))
            | some i => 𝟙 (F.obj (O.obj (X.inner.obj i))) }
      inv :=
        { equiv := Equiv.refl (Option X.inner.index)
          hom := fun o =>
            match o with
            | none => 𝟙 (F.obj (O.obj X.outerProfile))
            | some i => 𝟙 (F.obj (O.obj (X.inner.obj i))) }
      hom_inv_id := by
        apply FiniteFamily.Hom_ext
        · rfl
        · intro o
          cases o with
          | none =>
            exact heq_of_eq (by
              change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
              simp)
          | some _ =>
            exact heq_of_eq (by
              change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
              simp)
      inv_hom_id := by
        apply FiniteFamily.Hom_ext
        · rfl
        · intro o
          cases o with
          | none =>
            exact heq_of_eq (by
              change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
              simp)
          | some _ =>
            exact heq_of_eq (by
              change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
              simp) }

omit [FiniteTensor V] [FiniteTensor W] in
/-- Naturality of `factorsIso` over `f : X ⟶ Y` in `ColoredSubstitutionData Color`. -/
theorem factorsIso_naturality {F : V ⥤ W} {O : ColoredSymmetricCollection Color V}
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y) :
    (FiniteFamily.map F).map ((substitutionFactors O).map f) ≫
        (factorsIso F O Y).hom =
      (factorsIso F O X).hom ≫ (substitutionFactors (O ⋙ F)).map f := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (by
        change F.map (O.map (ColoredSubstitutionData.outerProfileMap f)) ≫ 𝟙 _ =
          𝟙 _ ≫ F.map (O.map (ColoredSubstitutionData.outerProfileMap f))
        simp)
    | some i =>
      exact heq_of_eq (by
        change F.map (O.map (f.innerHom.hom i)) ≫ 𝟙 _ =
          𝟙 _ ≫ F.map (O.map (f.innerHom.hom i))
        simp)

omit [FiniteTensor V] [FiniteTensor W] in
/-- Inverse naturality derived from `factorsIso_naturality`. -/
theorem factorsIso_inv_naturality {F : V ⥤ W} {O : ColoredSymmetricCollection Color V}
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y) :
    (factorsIso F O X).inv ≫ (FiniteFamily.map F).map ((substitutionFactors O).map f) =
      (substitutionFactors (O ⋙ F)).map f ≫ (factorsIso F O Y).inv := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (by
        change 𝟙 _ ≫ F.map (O.map (ColoredSubstitutionData.outerProfileMap f)) =
          F.map (O.map (ColoredSubstitutionData.outerProfileMap f)) ≫ 𝟙 _
        simp)
    | some i =>
      exact heq_of_eq (by
        change 𝟙 _ ≫ F.map (O.map (f.innerHom.hom i)) =
          F.map (O.map (f.innerHom.hom i)) ≫ 𝟙 _
        simp)

/--
Comparison naturality:
`tensor_W.map (map F.map f) ≫ comparison.hom =
  comparison.hom ≫ F.map (tensor_V.map f)`.
-/
private theorem comparison_naturality {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    {X Y : FiniteFamily V} (f : X ⟶ Y) :
    (FiniteTensor.tensor (V := W)).map ((FiniteFamily.map F).map f) ≫
        p.comparisonIso.hom.app Y =
      p.comparisonIso.hom.app X ≫ F.map ((FiniteTensor.tensor (V := V)).map f) := by
  have h := p.comparisonIso.hom.naturality f
  -- `naturality` is `(map F ⋙ tensor_W).map f ≫ hom.app Y = hom.app X ≫ (tensor_V ⋙ F).map f`
  -- Unfold the two functor map compositions
  have h1 : (FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W)).map f =
      (FiniteTensor.tensor (V := W)).map ((FiniteFamily.map F).map f) := rfl
  have h2 : (FiniteTensor.tensor (V := V) ⋙ F).map f =
      F.map ((FiniteTensor.tensor (V := V)).map f) := rfl
  rw [h1, h2] at h
  exact h

private theorem comparisonIso_hom_app_singleton {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (X : V) :
    p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) =
      (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
        F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) := by
  have hCompat := p.singleton_compat_hom_app X
  have hSingletonMap :
      (FiniteFamily.singletonMapIso F).hom.app X = 𝟙 _ := by
    with_unfolding_all rfl
  have hLeftMap :
      (Functor.isoWhiskerRight (FiniteFamily.singletonMapIso F)
            (FiniteTensor.tensor (V := W))).hom.app X = 𝟙 _ := by
    change (FiniteTensor.tensor (V := W)).map
        ((FiniteFamily.singletonMapIso F).hom.app X) = 𝟙 _
    rw [hSingletonMap]
    exact (FiniteTensor.tensor (V := W)).map_id _
  have hLeft :
      (Functor.isoWhiskerRight (FiniteFamily.singletonMapIso F)
            (FiniteTensor.tensor (V := W)) ≪≫
          Functor.isoWhiskerLeft F
            (FiniteTensor.singletonIso (V := W)) ≪≫
          Functor.rightUnitor F).hom.app X =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, hLeftMap,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app]
    calc
      𝟙 _ ≫ (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫ 𝟙 _ =
          𝟙 _ ≫ (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) := by
        simp only [Category.comp_id]
      _ = (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) := by
        simp only [Category.id_comp]
  have hRightLeft :
      (Functor.isoWhiskerLeft (FiniteFamily.singleton (C := V))
          p.comparisonIso).hom.app X =
        p.comparisonIso.hom.app
          ((FiniteFamily.singleton (C := V)).obj X) := by
    with_unfolding_all rfl
  have hRightMid :
      (Functor.isoWhiskerRight
            (FiniteTensor.singletonIso (V := V)) F).hom.app X =
        F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) := by
    with_unfolding_all rfl
  have hRight :
      (Functor.isoWhiskerLeft (FiniteFamily.singleton (C := V))
            p.comparisonIso ≪≫
          Functor.isoWhiskerRight
            (FiniteTensor.singletonIso (V := V)) F ≪≫
          Functor.leftUnitor F).hom.app X =
        p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) := by
    simp only [Iso.trans_hom, NatTrans.comp_app, hRightLeft, hRightMid,
      Functor.leftUnitor_hom_app]
    simp
  have hEq :
      p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) := by
    have h := hCompat
    rw [hLeft, hRight] at h
    exact h.symm
  have hHomInv :
      (FiniteTensor.singletonIso (V := V)).hom.app X ≫
        (FiniteTensor.singletonIso (V := V)).inv.app X = 𝟙 _ := by
    have h := (FiniteTensor.singletonIso (V := V)).hom_inv_id
    have hApp := congrArg (fun t : NatTrans _ _ => t.app X) h
    simp only [NatTrans.comp_app] at hApp
    exact hApp
  have hMapHomInv :
      F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) ≫
        F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) = 𝟙 _ := by
    rw [← F.map_comp, hHomInv, F.map_id _]
  have hMapHomInvTyped :
      F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) ≫
        F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) =
        𝟙 ((FiniteTensor.tensor (V := V) ⋙ F).obj
          ((FiniteFamily.singleton (C := V)).obj X)) := by
    exact hMapHomInv
  let c := F.map ((FiniteTensor.singletonIso (V := V)).inv.app X)
  have hPost :
      (p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X)) ≫
        c =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫ c :=
    congrArg (fun k => k ≫ c) hEq
  have hMid :
      (p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X)) ≫
        c =
        p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) := by
    rw [Category.assoc, hMapHomInvTyped,
      Category.comp_id (p.comparisonIso.hom.app
        ((FiniteFamily.singleton (C := V)).obj X))]
  exact hMid.symm.trans hPost

/-- The singleton comparison followed by the mapped singleton counit is the singleton counit.

This is the cancellation consequence of `comparisonIso_hom_app_singleton` used by unit and
associativity component proofs. -/
private theorem comparisonIso_hom_app_singleton_comp {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (X : V) :
    p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
        F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) =
      (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) := by
  have hComp := comparisonIso_hom_app_singleton p X
  have hInvHomV :
      (FiniteTensor.singletonIso (V := V)).inv.app X ≫
        (FiniteTensor.singletonIso (V := V)).hom.app X =
        𝟙 X := by
    have h := (FiniteTensor.singletonIso (V := V)).inv_hom_id
    have hApp := congrArg (fun t : NatTrans _ _ => t.app X) h
    simp only [NatTrans.comp_app] at hApp
    exact hApp
  have h1 :
      p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) =
        ((FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).inv.app X)) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) :=
    congrArg
      (fun k => k ≫ F.map ((FiniteTensor.singletonIso (V := V)).hom.app X))
      hComp
  have h2 :
      ((FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).inv.app X)) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          (F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) ≫
            F.map ((FiniteTensor.singletonIso (V := V)).hom.app X)) := by
    rw [Category.assoc]
  have h3 :
      (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          (F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) ≫
            F.map ((FiniteTensor.singletonIso (V := V)).hom.app X)) =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).inv.app X ≫
            (FiniteTensor.singletonIso (V := V)).hom.app X) := by
    rw [← F.map_comp]
  have h4 :
      (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).inv.app X ≫
            (FiniteTensor.singletonIso (V := V)).hom.app X) =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          𝟙 (F.obj X) := by
    rw [hInvHomV, F.map_id]
  exact h1.trans <| h2.trans <| h3.trans <| h4.trans (Category.comp_id _)

/-- Source comparison isomorphism between the tensor of mapped substitution factors and the image
of the original substitution source. -/
noncomputable def sourceComparisonIso {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredSymmetricCollection Color V) (X : ColoredSubstitutionData Color) :
    (FiniteTensor.tensor (V := W)).obj ((substitutionFactors (O ⋙ F)).obj X) ≅
      F.obj ((FiniteTensor.tensor (V := V)).obj ((substitutionFactors O).obj X)) :=
  (FiniteTensor.tensor (V := W)).mapIso (factorsIso F O X).symm ≪≫
    comparisonIsoApp p ((substitutionFactors O).obj X)

/-- Source comparison hom: `tensor_W (factors (O⋙F) X) ⟶ F (tensor_V (factors O X))`. -/
noncomputable def sourceComparisonHom {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredSymmetricCollection Color V) (X : ColoredSubstitutionData Color) :
    (FiniteTensor.tensor (V := W)).obj ((substitutionFactors (O ⋙ F)).obj X) ⟶
      F.obj ((FiniteTensor.tensor (V := V)).obj ((substitutionFactors O).obj X)) :=
  (sourceComparisonIso p O X).hom

/-- Naturality of `sourceComparisonHom` over `f : X ⟶ Y`.

States that
`substitutionSource (O ⋙ F).map f ≫ sourceComparisonHom Y`
equals
`sourceComparisonHom X ≫ F.map (substitutionSource O.map f)`.

Derived from `factorsIso_inv_naturality`, functoriality of
`FiniteTensor.tensor W`, `comparison_naturality`, and reassociation. -/
theorem sourceComparisonHom_naturality {F : V ⥤ W}
    {O : ColoredSymmetricCollection Color V} (p : FiniteTensor.Preserving F)
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y) :
    (substitutionSource (O ⋙ F)).map f ≫ sourceComparisonHom p O Y =
      sourceComparisonHom p O X ≫
        F.map ((substitutionSource O).map f) := by
  let tW := FiniteTensor.tensor (V := W)
  let tV := FiniteTensor.tensor (V := V)
  let mf := (substitutionFactors O).map f
  let mfF := (substitutionFactors (O ⋙ F)).map f
  let invY := (factorsIso F O Y).inv
  let invX := (factorsIso F O X).inv
  let compY : tW.obj ((FiniteFamily.map F).obj ((substitutionFactors O).obj Y)) ⟶
      F.obj (tV.obj ((substitutionFactors O).obj Y)) :=
    (comparisonIsoApp p ((substitutionFactors O).obj Y)).hom
  let compX : tW.obj ((FiniteFamily.map F).obj ((substitutionFactors O).obj X)) ⟶
      F.obj (tV.obj ((substitutionFactors O).obj X)) :=
    (comparisonIsoApp p ((substitutionFactors O).obj X)).hom
  have h1 :
      (substitutionSource (O ⋙ F)).map f ≫ sourceComparisonHom p O Y =
        tW.map mfF ≫ (tW.map invY ≫ compY) := rfl
  have h2 : tW.map mfF ≫ (tW.map invY ≫ compY) =
      (tW.map mfF ≫ tW.map invY) ≫ compY :=
    (Category.assoc _ _ _).symm
  have h_eq_a : tW.map mfF ≫ tW.map invY = tW.map (mfF ≫ invY) :=
    (tW.map_comp _ _).symm
  have h3 : (tW.map mfF ≫ tW.map invY) ≫ compY =
      tW.map (mfF ≫ invY) ≫ compY :=
    congrArg (· ≫ compY) h_eq_a
  have h_eq_b : mfF ≫ invY = invX ≫ (FiniteFamily.map F).map mf := by
    have h := factorsIso_inv_naturality (F := F) (O := O) f
    exact h.symm
  have h_eq_b_map :
      tW.map (mfF ≫ invY) = tW.map (invX ≫ (FiniteFamily.map F).map mf) :=
    congrArg tW.map h_eq_b
  have h4 : tW.map (mfF ≫ invY) ≫ compY =
      tW.map (invX ≫ (FiniteFamily.map F).map mf) ≫ compY :=
    congrArg (· ≫ compY) h_eq_b_map
  have h_eq_c :
      tW.map (invX ≫ (FiniteFamily.map F).map mf) =
        tW.map invX ≫ tW.map ((FiniteFamily.map F).map mf) :=
    tW.map_comp _ _
  have h5 :
      tW.map (invX ≫ (FiniteFamily.map F).map mf) ≫ compY =
        (tW.map invX ≫ tW.map ((FiniteFamily.map F).map mf)) ≫ compY :=
    congrArg (· ≫ compY) h_eq_c
  have h6 :
      (tW.map invX ≫ tW.map ((FiniteFamily.map F).map mf)) ≫ compY =
        tW.map invX ≫ (tW.map ((FiniteFamily.map F).map mf) ≫ compY) :=
    Category.assoc _ _ _
  have h_eq_d :
      tW.map ((FiniteFamily.map F).map mf) ≫ compY =
        compX ≫ F.map (tV.map mf) := by
    have h1d :
        tW.map ((FiniteFamily.map F).map mf) ≫ compY =
          tW.map ((FiniteFamily.map F).map mf) ≫
            p.comparisonIso.hom.app ((substitutionFactors O).obj Y) := rfl
    have h2d :
        tW.map ((FiniteFamily.map F).map mf) ≫
            p.comparisonIso.hom.app ((substitutionFactors O).obj Y) =
          p.comparisonIso.hom.app ((substitutionFactors O).obj X) ≫
            F.map (tV.map mf) :=
      comparison_naturality p mf
    have h3d :
        p.comparisonIso.hom.app ((substitutionFactors O).obj X) ≫
            F.map (tV.map mf) =
          compX ≫ F.map (tV.map mf) := rfl
    exact (h1d.trans h2d).trans h3d
  have h7 :
      tW.map invX ≫ (tW.map ((FiniteFamily.map F).map mf) ≫ compY) =
        tW.map invX ≫ (compX ≫ F.map (tV.map mf)) :=
    congrArg (tW.map invX ≫ ·) h_eq_d
  have h8 :
      tW.map invX ≫ (compX ≫ F.map (tV.map mf)) =
        (tW.map invX ≫ compX) ≫ F.map (tV.map mf) :=
    (Category.assoc _ _ _).symm
  have h9 :
      (tW.map invX ≫ compX) ≫ F.map (tV.map mf) =
        sourceComparisonHom p O X ≫ F.map ((substitutionSource O).map f) := rfl
  exact ((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans
    h7).trans h8).trans h9)
/-- Mapped unit for `O.toCollection ⋙ F`, pointwise in the color. -/
noncomputable def mappedUnit {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    ColoredOperadUnit (O.toCollection ⋙ F) :=
  fun c ↦ (unitSourceIso p).hom ≫ F.map (O.unit c)

/-- Mapped substitution as an `ColoredOperadSubstitution (O.toCollection ⋙ F)`,
with `app X = sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X)`.

Naturality follows from `sourceComparisonHom_naturality`,
`F.map_comp`, `O.subst.naturality`, and the definitional form of
`substitutionTarget` for a postcomposed collection. -/
noncomputable def mappedSubstitution {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    ColoredOperadSubstitution (O.toCollection ⋙ F) where
  app X := sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X)
  naturality := by
    intro X Y f
    let tV := FiniteTensor.tensor (V := V)
    let mf := (substitutionFactors O.toCollection).map f
    have hS : (substitutionSource O.toCollection).map f = tV.map mf := rfl
    have hTF :
        (substitutionTarget (O.toCollection ⋙ F)).map f =
          F.map ((substitutionTarget O.toCollection).map f) := rfl
    have h1 :
        (substitutionSource (O.toCollection ⋙ F)).map f ≫
            (sourceComparisonHom p O.toCollection Y ≫ F.map (O.subst.app Y)) =
          ((substitutionSource (O.toCollection ⋙ F)).map f ≫
              sourceComparisonHom p O.toCollection Y) ≫
                F.map (O.subst.app Y) :=
      (Category.assoc _ _ _).symm
    have h_src_nat :
        (substitutionSource (O.toCollection ⋙ F)).map f ≫
            sourceComparisonHom p O.toCollection Y =
          sourceComparisonHom p O.toCollection X ≫
            F.map ((substitutionSource O.toCollection).map f) :=
      sourceComparisonHom_naturality p f
    have h_src_eq :
        sourceComparisonHom p O.toCollection X ≫
            F.map ((substitutionSource O.toCollection).map f) =
          sourceComparisonHom p O.toCollection X ≫ F.map (tV.map mf) := rfl
    have h_eq1 :
        (substitutionSource (O.toCollection ⋙ F)).map f ≫
            sourceComparisonHom p O.toCollection Y =
          sourceComparisonHom p O.toCollection X ≫ F.map (tV.map mf) :=
      h_src_nat.trans h_src_eq
    have h2 :
        ((substitutionSource (O.toCollection ⋙ F)).map f ≫
            sourceComparisonHom p O.toCollection Y) ≫
              F.map (O.subst.app Y) =
          (sourceComparisonHom p O.toCollection X ≫
              F.map (tV.map mf)) ≫
              F.map (O.subst.app Y) :=
      congrArg (· ≫ F.map (O.subst.app Y)) h_eq1
    have h3 :
        (sourceComparisonHom p O.toCollection X ≫ F.map (tV.map mf)) ≫
            F.map (O.subst.app Y) =
          sourceComparisonHom p O.toCollection X ≫
              (F.map (tV.map mf) ≫ F.map (O.subst.app Y)) :=
      Category.assoc _ _ _
    have h_eq2 :
        F.map (tV.map mf) ≫ F.map (O.subst.app Y) =
          F.map (tV.map mf ≫ O.subst.app Y) :=
      (F.map_comp _ _).symm
    have h4 :
        sourceComparisonHom p O.toCollection X ≫
            (F.map (tV.map mf) ≫ F.map (O.subst.app Y)) =
          sourceComparisonHom p O.toCollection X ≫
              F.map (tV.map mf ≫ O.subst.app Y) :=
      congrArg (sourceComparisonHom p O.toCollection X ≫ ·) h_eq2
    have h_eq3 : tV.map mf ≫ O.subst.app Y =
        (substitutionSource O.toCollection).map f ≫ O.subst.app Y :=
      congrArg (· ≫ O.subst.app Y) hS.symm
    have h_eq4 :
        (substitutionSource O.toCollection).map f ≫ O.subst.app Y =
          O.subst.app X ≫ (substitutionTarget O.toCollection).map f :=
      O.subst.naturality f
    have h_eq5 : tV.map mf ≫ O.subst.app Y =
        O.subst.app X ≫ (substitutionTarget O.toCollection).map f :=
      h_eq3.trans h_eq4
    have h_eq5F :
        F.map (tV.map mf ≫ O.subst.app Y) =
          F.map (O.subst.app X ≫ (substitutionTarget O.toCollection).map f) :=
      congrArg F.map h_eq5
    have h5 :
        sourceComparisonHom p O.toCollection X ≫
            F.map (tV.map mf ≫ O.subst.app Y) =
          sourceComparisonHom p O.toCollection X ≫
              F.map (O.subst.app X ≫
                (substitutionTarget O.toCollection).map f) :=
      congrArg (sourceComparisonHom p O.toCollection X ≫ ·) h_eq5F
    have h_eq6 :
        F.map (O.subst.app X ≫ (substitutionTarget O.toCollection).map f) =
          F.map (O.subst.app X) ≫
            F.map ((substitutionTarget O.toCollection).map f) :=
      F.map_comp _ _
    have h6 :
        sourceComparisonHom p O.toCollection X ≫
            F.map (O.subst.app X ≫
              (substitutionTarget O.toCollection).map f) =
          sourceComparisonHom p O.toCollection X ≫
              (F.map (O.subst.app X) ≫
                F.map ((substitutionTarget O.toCollection).map f)) :=
      congrArg (sourceComparisonHom p O.toCollection X ≫ ·) h_eq6
    have h7 :
        sourceComparisonHom p O.toCollection X ≫
            (F.map (O.subst.app X) ≫
              F.map ((substitutionTarget O.toCollection).map f)) =
          (sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X)) ≫
              F.map ((substitutionTarget O.toCollection).map f) :=
      (Category.assoc _ _ _).symm
    have h8 :
        (sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X)) ≫
              F.map ((substitutionTarget O.toCollection).map f) =
          (sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X)) ≫
              (substitutionTarget (O.toCollection ⋙ F)).map f :=
      congrArg
        ((sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X)) ≫ ·)
        hTF.symm
    exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans
      h7).trans h8

/-- Application of mapped substitution uses the canonical source comparison. -/
@[simp]
theorem mappedSubstitution_app {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V)
    (X : ColoredSubstitutionData Color) :
    (mappedSubstitution p O).app X =
      sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X) :=
  rfl

/-- Auxiliary mapped unit for an arbitrary collection unit `η`. -/
private noncomputable def mappedUnitAux {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O : ColoredSymmetricCollection Color V}
    (η : ColoredOperadUnit O) : ColoredOperadUnit (O ⋙ F) :=
  fun c ↦ (unitSourceIso p).hom ≫ F.map (η c)

/-- Comparison family for right insertion:
`rightTensorFamily (F.obj c) I ⟶ mapF (rightTensorFamily c I)`.
At `none` it is `comparison at singleton`, at `some` it is
`unitSourceIso.hom`. -/
private noncomputable def rightCompFamily {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (c : V) (I : FintypeCat) :
    _root_.CategoryTheory.Operad.UnitInsertion.rightTensorFamily (F.obj c) I ⟶
      (FiniteFamily.map F).obj
        (_root_.CategoryTheory.Operad.UnitInsertion.rightTensorFamily c I) where
  equiv := Equiv.refl (Option (I : Type))
  hom := fun o =>
    match o with
    | none =>
      p.comparisonIso.hom.app
        ((FiniteFamily.singleton (C := V)).obj c)
    | some _ => (unitSourceIso p).hom

/-- Comparison family for left insertion. -/
private noncomputable def leftCompFamily {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (c : V) :
    _root_.CategoryTheory.Operad.UnitInsertion.leftTensorFamily (F.obj c) ⟶
      (FiniteFamily.map F).obj (_root_.CategoryTheory.Operad.UnitInsertion.leftTensorFamily c) where
  equiv := Equiv.refl (Option PUnit)
  hom := fun o =>
    match o with
    | none => (unitSourceIso p).hom
    | some _ =>
      p.comparisonIso.hom.app
        ((FiniteFamily.singleton (C := V)).obj c)

/-- `F.map (singletonIso.inv) = singletonIso.inv_W ≫ comparison at singleton`. -/
private theorem map_singletonIso_inv {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (X : V) :
    F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) =
      (FiniteTensor.singletonIso (V := W)).inv.app (F.obj X) ≫
        p.comparisonIso.hom.app
          ((FiniteFamily.singleton (C := V)).obj X) := by
  have hComp := comparisonIso_hom_app_singleton p X
  have hInvHom : (FiniteTensor.singletonIso (V := W)).inv.app (F.obj X) ≫
      (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) =
        𝟙 (F.obj X) := by
    have h := (FiniteTensor.singletonIso (V := W)).inv_hom_id
    have hApp := congrArg (fun t : NatTrans _ _ => t.app (F.obj X)) h
    simp only [NatTrans.comp_app] at hApp
    exact hApp
  calc
    F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) =
        𝟙 (F.obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) :=
      (Category.id_comp _).symm
    _ = ((FiniteTensor.singletonIso (V := W)).inv.app (F.obj X) ≫
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X)) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).inv.app X) := by
      rw [← hInvHom]
    _ = (FiniteTensor.singletonIso (V := W)).inv.app (F.obj X) ≫
        ((FiniteTensor.singletonIso (V := W)).hom.app (F.obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).inv.app X)) := by
      rw [Category.assoc]
    _ = (FiniteTensor.singletonIso (V := W)).inv.app (F.obj X) ≫
        p.comparisonIso.hom.app
          ((FiniteFamily.singleton (C := V)).obj X) := by
      rw [← hComp]

/-- Right factor hom after postcomposition with `factorsIso.inv`
equals `rightCompFamily ≫ mapF (rightFactorHom)`. -/
private theorem rightFactorHomComp {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O : ColoredSymmetricCollection Color V}
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    (UnitInsertion.rightFactorHom (O ⋙ F) (mappedUnitAux p η) P ≫
      (factorsIso F O (ColoredSubstitutionData.rightUnit P)).inv) =
      (rightCompFamily p (O.obj P) P.inputs ≫
        (FiniteFamily.map F).map
          (UnitInsertion.rightFactorHom O η P)) := by
  have hEq := comparisonIso_hom_app_singleton_comp p (O.obj P)
  let lhs := UnitInsertion.rightFactorHom (O ⋙ F) (mappedUnitAux p η) P ≫
    (factorsIso F O (ColoredSubstitutionData.rightUnit P)).inv
  let rhs := rightCompFamily p (O.obj P) P.inputs ≫
    (FiniteFamily.map F).map (UnitInsertion.rightFactorHom O η P)
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      let a := (FiniteTensor.singletonIso (V := W)).hom.app (F.obj (O.obj P))
      let b := p.comparisonIso.hom.app
        ((FiniteFamily.singleton (C := V)).obj (O.obj P)) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj P))
      have hMapW : (O ⋙ F).map (ColoredSubstitutionData.rightUnitOuterHom P) =
          𝟙 _ := by
        rw [ColoredSubstitutionData.rightUnitOuterHom_eq_id]
        exact (O ⋙ F).map_id P
      have hMapV : O.map (ColoredSubstitutionData.rightUnitOuterHom P) = 𝟙 _ := by
        rw [ColoredSubstitutionData.rightUnitOuterHom_eq_id]
        exact O.map_id P
      have hLeft : HEq (lhs.hom none) a := by
        have h0 : HEq (lhs.hom none)
            ((a ≫ (O ⋙ F).map
              (ColoredSubstitutionData.rightUnitOuterHom P)) ≫ 𝟙 _) := by
          with_unfolding_all exact heq_of_eq rfl
        have h1 : HEq
            ((a ≫ (O ⋙ F).map
              (ColoredSubstitutionData.rightUnitOuterHom P)) ≫ 𝟙 _)
            ((a ≫ 𝟙 _) ≫ 𝟙 _) :=
          heq_of_eq (congrArg (fun t => (a ≫ t) ≫ 𝟙 _) hMapW)
        have h2 : HEq ((a ≫ 𝟙 _) ≫ 𝟙 _) a :=
          heq_of_eq (by simp)
        exact h0.trans (h1.trans h2)
      have hRight : HEq b (rhs.hom none) := by
        have h0 : HEq (rhs.hom none)
            (p.comparisonIso.hom.app
                ((FiniteFamily.singleton (C := V)).obj (O.obj P)) ≫
              F.map ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj P) ≫
                O.map (ColoredSubstitutionData.rightUnitOuterHom P))) := by
          with_unfolding_all exact heq_of_eq rfl
        have h1 : HEq
            (p.comparisonIso.hom.app
                ((FiniteFamily.singleton (C := V)).obj (O.obj P)) ≫
              F.map ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj P) ≫
                O.map (ColoredSubstitutionData.rightUnitOuterHom P)))
            (p.comparisonIso.hom.app
                ((FiniteFamily.singleton (C := V)).obj (O.obj P)) ≫
              F.map ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj P) ≫
                𝟙 _)) :=
          heq_of_eq (congrArg
            (fun t => p.comparisonIso.hom.app
              ((FiniteFamily.singleton (C := V)).obj (O.obj P)) ≫
                F.map ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj P) ≫ t))
            hMapV)
        have h2 : HEq
            (p.comparisonIso.hom.app
                ((FiniteFamily.singleton (C := V)).obj (O.obj P)) ≫
              F.map ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj P) ≫ 𝟙 _))
            b := heq_of_eq (by simp [b])
        exact ((h0.trans h1).trans h2).symm
      exact hLeft.trans ((heq_of_eq hEq.symm).trans hRight)
    | some i =>
      let a := (unitSourceIso p).hom ≫ F.map (η (P.inputColor i))
      have hLeft : HEq (lhs.hom (some i)) a := by
        with_unfolding_all
          exact heq_of_eq
            ((show lhs.hom (some i) = a ≫ 𝟙 _ from rfl).trans
              (Category.comp_id _))
      have hRight : HEq a (rhs.hom (some i)) := by
        with_unfolding_all exact heq_of_eq rfl
      exact hLeft.trans hRight

/-- Left factor hom comparison. -/
private theorem leftFactorHomComp {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O : ColoredSymmetricCollection Color V}
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    (UnitInsertion.leftFactorHom (O ⋙ F) (mappedUnitAux p η) P ≫
      (factorsIso F O (ColoredSubstitutionData.leftUnit P)).inv) =
      (leftCompFamily p (O.obj P) ≫
        (FiniteFamily.map F).map
          (UnitInsertion.leftFactorHom O η P)) := by
  have hEq := comparisonIso_hom_app_singleton_comp p (O.obj P)
  let lhs := UnitInsertion.leftFactorHom (O ⋙ F) (mappedUnitAux p η) P ≫
    (factorsIso F O (ColoredSubstitutionData.leftUnit P)).inv
  let rhs := leftCompFamily p (O.obj P) ≫
    (FiniteFamily.map F).map (UnitInsertion.leftFactorHom O η P)
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      let a := (unitSourceIso p).hom ≫ F.map (η P.outputColor)
      have hMapW : (O ⋙ F).map (ColoredSubstitutionData.leftUnitOuterHom P) =
          𝟙 _ := by
        rw [ColoredSubstitutionData.leftUnitOuterHom_eq_id]
        exact (O ⋙ F).map_id _
      have hMapV : O.map (ColoredSubstitutionData.leftUnitOuterHom P) = 𝟙 _ := by
        rw [ColoredSubstitutionData.leftUnitOuterHom_eq_id]
        exact O.map_id _
      have hLeft : HEq (lhs.hom none) a := by
        have h0 : HEq (lhs.hom none)
            ((a ≫ (O ⋙ F).map
              (ColoredSubstitutionData.leftUnitOuterHom P)) ≫ 𝟙 _) := by
          with_unfolding_all exact heq_of_eq rfl
        have h1 : HEq
            ((a ≫ (O ⋙ F).map
              (ColoredSubstitutionData.leftUnitOuterHom P)) ≫ 𝟙 _)
            ((a ≫ 𝟙 _) ≫ 𝟙 _) :=
          heq_of_eq (congrArg (fun t => (a ≫ t) ≫ 𝟙 _) hMapW)
        have h2 : HEq ((a ≫ 𝟙 _) ≫ 𝟙 _) a :=
          heq_of_eq (by simp)
        exact h0.trans (h1.trans h2)
      have hRight : HEq a (rhs.hom none) := by
        have h0 : HEq (rhs.hom none)
            ((unitSourceIso p).hom ≫
              F.map (η P.outputColor ≫
                O.map (ColoredSubstitutionData.leftUnitOuterHom P))) := by
          with_unfolding_all exact heq_of_eq rfl
        have h1 : HEq
            ((unitSourceIso p).hom ≫
              F.map (η P.outputColor ≫
                O.map (ColoredSubstitutionData.leftUnitOuterHom P)))
            ((unitSourceIso p).hom ≫ F.map (η P.outputColor ≫ 𝟙 _)) :=
          heq_of_eq (congrArg
            (fun t => (unitSourceIso p).hom ≫ F.map (η P.outputColor ≫ t))
            hMapV)
        have h2 : HEq
            ((unitSourceIso p).hom ≫ F.map (η P.outputColor ≫ 𝟙 _)) a :=
          heq_of_eq (by
            with_unfolding_all
              exact congrArg ((unitSourceIso p).hom ≫ ·)
                (congrArg F.map (Category.comp_id (η P.outputColor))))
        exact ((h0.trans h1).trans h2).symm
      exact hLeft.trans hRight
    | some i =>
      let a := (FiniteTensor.singletonIso (V := W)).hom.app (F.obj (O.obj P))
      let b := p.comparisonIso.hom.app
        ((FiniteFamily.singleton (C := V)).obj (O.obj P)) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj P))
      have hLeft : HEq (lhs.hom (some i)) a := by
        with_unfolding_all
          exact heq_of_eq
            ((show lhs.hom (some i) = a ≫ 𝟙 _ from rfl).trans
              (Category.comp_id _))
      have hRight : HEq b (rhs.hom (some i)) := by
        with_unfolding_all exact heq_of_eq rfl
      exact hLeft.trans ((heq_of_eq hEq.symm).trans hRight)

private def rightNestedHom (F : V ⥤ W) (c : V) (I : FintypeCat) :
    _root_.CategoryTheory.Operad.UnitInsertion.rightNestedFamily (F.obj c) I ⟶
      (FiniteFamily.map (FiniteFamily.map F)).obj
        (_root_.CategoryTheory.Operad.UnitInsertion.rightNestedFamily c I) where
  equiv := Equiv.refl (Option (I : Type))
  hom := fun o =>
    match o with
    | none => (FiniteFamily.singletonMapIso F).inv.app c
    | some _ => (emptyFamilyIso F).hom

private def leftNestedHom (F : V ⥤ W) (c : V) :
    _root_.CategoryTheory.Operad.UnitInsertion.leftNestedFamily (F.obj c) ⟶
      (FiniteFamily.map (FiniteFamily.map F)).obj
        (_root_.CategoryTheory.Operad.UnitInsertion.leftNestedFamily c) where
  equiv := Equiv.refl (Option PUnit)
  hom := fun o =>
    match o with
    | none => (emptyFamilyIso F).hom
    | some _ => (FiniteFamily.singletonMapIso F).inv.app c

private def rightFlattenObjMapIso (F : V ⥤ W) (c : V)
    (I : FintypeCat) :
    (FiniteFamily.map F).obj (_root_.CategoryTheory.Operad.UnitInsertion.rightFlattenObj c I) ≅
      _root_.CategoryTheory.Operad.UnitInsertion.rightFlattenObj (F.obj c) I where
  hom :=
    { equiv :=
        { toFun := fun p =>
            match p with
            | ⟨none, _⟩ => ⟨none, PUnit.unit⟩
            | ⟨some _, b⟩ => Empty.elim b
          invFun := fun q =>
            match q with
            | ⟨none, _⟩ => ⟨none, PUnit.unit⟩
            | ⟨some _, b⟩ => Empty.elim b
          left_inv := by
            intro p
            match p with
            | ⟨none, u⟩ =>
              cases u
              rfl
            | ⟨some _, b⟩ =>
              cases b
          right_inv := by
            intro q
            match q with
            | ⟨none, u⟩ =>
              cases u
              rfl
            | ⟨some _, b⟩ =>
              cases b }
      hom := fun p =>
        match p with
        | ⟨none, _⟩ => 𝟙 (F.obj c)
        | ⟨some _, b⟩ => Empty.elim b }
  inv :=
    { equiv :=
        { toFun := fun q =>
            match q with
            | ⟨none, _⟩ => ⟨none, PUnit.unit⟩
            | ⟨some _, b⟩ => Empty.elim b
          invFun := fun p =>
            match p with
            | ⟨none, _⟩ => ⟨none, PUnit.unit⟩
            | ⟨some _, b⟩ => Empty.elim b
          left_inv := by
            intro q
            match q with
            | ⟨none, u⟩ =>
              cases u
              rfl
            | ⟨some _, b⟩ =>
              cases b
          right_inv := by
            intro p
            match p with
            | ⟨none, u⟩ =>
              cases u
              rfl
            | ⟨some _, b⟩ =>
              cases b }
      hom := fun p =>
        match p with
        | ⟨none, _⟩ => 𝟙 (F.obj c)
        | ⟨some _, b⟩ => Empty.elim b }
  hom_inv_id := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro p
      match p with
      | ⟨none, u⟩ =>
        cases u
        rfl
      | ⟨some _, b⟩ =>
        cases b
    · intro p
      match p with
      | ⟨none, _⟩ =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)
      | ⟨some _, b⟩ =>
        cases b
  inv_hom_id := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro p
      match p with
      | ⟨none, u⟩ =>
        cases u
        rfl
      | ⟨some _, b⟩ =>
        cases b
    · intro p
      match p with
      | ⟨none, _⟩ =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)
      | ⟨some _, b⟩ =>
        cases b

private def leftFlattenObjMapIso (F : V ⥤ W) (c : V) :
    (FiniteFamily.map F).obj (_root_.CategoryTheory.Operad.UnitInsertion.leftFlattenObj c) ≅
      _root_.CategoryTheory.Operad.UnitInsertion.leftFlattenObj (F.obj c) where
  hom :=
    { equiv :=
        { toFun := fun p =>
            match p with
            | ⟨none, b⟩ => Empty.elim b
            | ⟨some _, _⟩ => ⟨some PUnit.unit, PUnit.unit⟩
          invFun := fun q =>
            match q with
            | ⟨none, b⟩ => Empty.elim b
            | ⟨some _, _⟩ => ⟨some PUnit.unit, PUnit.unit⟩
          left_inv := by
            intro p
            match p with
            | ⟨none, b⟩ =>
              cases b
            | ⟨some x, y⟩ =>
              cases x
              cases y
              rfl
          right_inv := by
            intro q
            match q with
            | ⟨none, b⟩ =>
              cases b
            | ⟨some x, y⟩ =>
              cases x
              cases y
              rfl }
      hom := fun p =>
        match p with
        | ⟨none, b⟩ => Empty.elim b
        | ⟨some _, _⟩ => 𝟙 (F.obj c) }
  inv :=
    { equiv :=
        { toFun := fun q =>
            match q with
            | ⟨none, b⟩ => Empty.elim b
            | ⟨some _, _⟩ => ⟨some PUnit.unit, PUnit.unit⟩
          invFun := fun p =>
            match p with
            | ⟨none, b⟩ => Empty.elim b
            | ⟨some _, _⟩ => ⟨some PUnit.unit, PUnit.unit⟩
          left_inv := by
            intro q
            match q with
            | ⟨none, b⟩ =>
              cases b
            | ⟨some x, y⟩ =>
              cases x
              cases y
              rfl
          right_inv := by
            intro p
            match p with
            | ⟨none, b⟩ =>
              cases b
            | ⟨some x, y⟩ =>
              cases x
              cases y
              rfl }
      hom := fun p =>
        match p with
        | ⟨none, b⟩ => Empty.elim b
        | ⟨some _, _⟩ => 𝟙 (F.obj c) }
  hom_inv_id := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro p
      match p with
      | ⟨none, b⟩ =>
        cases b
      | ⟨some x, y⟩ =>
        cases x
        cases y
        rfl
    · intro p
      match p with
      | ⟨none, b⟩ =>
        cases b
      | ⟨some _, _⟩ =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)
  inv_hom_id := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro p
      match p with
      | ⟨none, b⟩ =>
        cases b
      | ⟨some x, y⟩ =>
        cases x
        cases y
        rfl
    · intro p
      match p with
      | ⟨none, b⟩ =>
        cases b
      | ⟨some _, _⟩ =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)

omit [FiniteTensor V] [FiniteTensor W] in
private theorem rightSingletonToFlatten_map_comp_iso {F : V ⥤ W}
    (c : V) (I : FintypeCat) :
  (FiniteFamily.map F).map
      (_root_.CategoryTheory.Operad.UnitInsertion.rightSingletonToFlatten c I) ≫
      (rightFlattenObjMapIso F c I).hom =
    _root_.CategoryTheory.Operad.UnitInsertion.rightSingletonToFlatten (F.obj c) I := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro x
    cases x with
    | unit => rfl
  · intro x
    cases x with
    | unit =>
      have h : F.map (𝟙 c) ≫ 𝟙 (F.obj c) = 𝟙 (F.obj c) := by
        calc
          F.map (𝟙 c) ≫ 𝟙 (F.obj c) = 𝟙 (F.obj c) ≫ 𝟙 (F.obj c) := by
            rw [F.map_id c]
          _ = 𝟙 (F.obj c) := Category.comp_id _
      with_unfolding_all exact heq_of_eq h

omit [FiniteTensor V] [FiniteTensor W] in
private theorem leftSingletonToFlatten_map_comp_iso {F : V ⥤ W}
    (c : V) :
  (FiniteFamily.map F).map (_root_.CategoryTheory.Operad.UnitInsertion.leftSingletonToFlatten c) ≫
      (leftFlattenObjMapIso F c).hom =
    _root_.CategoryTheory.Operad.UnitInsertion.leftSingletonToFlatten (F.obj c) := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro x
    cases x with
    | unit => rfl
  · intro x
    cases x with
    | unit =>
      have h : F.map (𝟙 c) ≫ 𝟙 (F.obj c) = 𝟙 (F.obj c) := by
        calc
          F.map (𝟙 c) ≫ 𝟙 (F.obj c) = 𝟙 (F.obj c) ≫ 𝟙 (F.obj c) := by
            rw [F.map_id c]
          _ = 𝟙 (F.obj c) := Category.comp_id _
      with_unfolding_all exact heq_of_eq h

omit [FiniteTensor V] [FiniteTensor W] in
private theorem rightFlatten_map_nestedHom {F : V ⥤ W}
    (c : V) (I : FintypeCat) :
  (FiniteFamily.flatten (C := W)).map (rightNestedHom F c I) =
    (rightFlattenObjMapIso F c I).inv := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro p
    match p with
    | ⟨none, u⟩ =>
      cases u
      rfl
    | ⟨some _, b⟩ =>
      cases b
  · intro p
    match p with
    | ⟨none, u⟩ =>
      cases u
      exact heq_of_eq (by rfl)
    | ⟨some _, b⟩ =>
      cases b

omit [FiniteTensor V] [FiniteTensor W] in
private theorem leftFlatten_map_nestedHom {F : V ⥤ W}
    (c : V) :
  (FiniteFamily.flatten (C := W)).map (leftNestedHom F c) =
    (leftFlattenObjMapIso F c).inv := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro p
    match p with
    | ⟨none, b⟩ =>
      cases b
    | ⟨some x, y⟩ =>
      cases x
      cases y
      rfl
  · intro p
    match p with
    | ⟨none, b⟩ =>
      cases b
    | ⟨some x, y⟩ =>
      cases x
      cases y
      exact heq_of_eq (by rfl)

private theorem rightCompFamily_eq {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (c : V) (I : FintypeCat) :
  (FiniteFamily.map (FiniteTensor.tensor (V := W))).map (rightNestedHom F c I) ≫
      (FiniteFamily.mapIso p.comparisonIso).hom.app
        (_root_.CategoryTheory.Operad.UnitInsertion.rightNestedFamily c I) =
    rightCompFamily p c I := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      have hInv : (FiniteFamily.singletonMapIso F).inv.app c = 𝟙 _ := by
        with_unfolding_all rfl
      have hMap : (FiniteTensor.tensor (V := W)).map
          ((FiniteFamily.singletonMapIso F).inv.app c) = 𝟙 _ := by
        rw [hInv]
        exact (FiniteTensor.tensor (V := W)).map_id _
      exact heq_of_eq (by
        change (FiniteTensor.tensor (V := W)).map
            ((FiniteFamily.singletonMapIso F).inv.app c) ≫
            p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj c) =
          p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj c)
        rw [hMap]
        exact Category.id_comp _)
    | some _ =>
      exact heq_of_eq (by
        with_unfolding_all
          rfl)

private theorem leftCompFamily_eq {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (c : V) :
  (FiniteFamily.map (FiniteTensor.tensor (V := W))).map (leftNestedHom F c) ≫
      (FiniteFamily.mapIso p.comparisonIso).hom.app
        (_root_.CategoryTheory.Operad.UnitInsertion.leftNestedFamily c) =
    leftCompFamily p c := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (by
        with_unfolding_all
          rfl)
    | some _ =>
      have hInv : (FiniteFamily.singletonMapIso F).inv.app c = 𝟙 _ := by
        with_unfolding_all rfl
      have hMap : (FiniteTensor.tensor (V := W)).map
          ((FiniteFamily.singletonMapIso F).inv.app c) = 𝟙 _ := by
        rw [hInv]
        exact (FiniteTensor.tensor (V := W)).map_id _
      exact heq_of_eq (by
        change (FiniteTensor.tensor (V := W)).map
            ((FiniteFamily.singletonMapIso F).inv.app c) ≫
            p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj c) =
          p.comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj c)
        rw [hMap]
        exact Category.id_comp _)

private theorem flatten_compat_reduced_hom_app {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (X : FiniteFamily (FiniteFamily V)) :
    (FiniteTensor.flattenIso (V := W)).hom.app
        ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
      (FiniteTensor.tensor (V := W)).map
        ((FiniteFamily.mapIso p.comparisonIso).hom.app X) ≫
      p.comparisonIso.hom.app
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) =
    p.comparisonIso.hom.app ((FiniteFamily.flatten (C := V)).obj X) ≫
      F.map ((FiniteTensor.flattenIso (V := V)).hom.app X) := by
  have hFlat := p.flatten_compat_hom_app X
  have hLeft : (Functor.isoWhiskerLeft (FiniteFamily.flatten (C := V))
        p.comparisonIso ≪≫
      Functor.isoWhiskerRight (FiniteTensor.flattenIso (V := V)) F).hom.app X =
      p.comparisonIso.hom.app ((FiniteFamily.flatten (C := V)).obj X) ≫
        F.map ((FiniteTensor.flattenIso (V := V)).hom.app X) := by
    simp only [Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  have hLead : (Functor.isoWhiskerRight (FiniteFamily.flattenMapIso F)
      (FiniteTensor.tensor (V := W))).hom.app X =
      𝟙 (((FiniteFamily.map (FiniteFamily.map F) ⋙
            FiniteFamily.flatten (C := W)) ⋙
          FiniteTensor.tensor (V := W)).obj X) := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := W)).map_id _
  have hBridge1 : (Functor.isoWhiskerRight
      (FiniteFamily.mapCompIso (FiniteFamily.map F)
        (FiniteTensor.tensor (V := W))).symm
      (FiniteTensor.tensor (V := W))).hom.app X =
      𝟙 ((FiniteFamily.map
            (FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W)) ⋙
          FiniteTensor.tensor (V := W)).obj X) := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := W)).map_id _
  have hBridge2 : (Functor.isoWhiskerRight
      (FiniteFamily.mapCompIso (FiniteTensor.tensor (V := V)) F)
      (FiniteTensor.tensor (V := W))).hom.app X =
      𝟙 ((FiniteFamily.map (FiniteTensor.tensor (V := V)) ⋙
          FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W)).obj X) := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := W)).map_id _
  have hB : (Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map F))
      (FiniteTensor.flattenIso (V := W))).hom.app X =
      (FiniteTensor.flattenIso (V := W)).hom.app
        ((FiniteFamily.map (FiniteFamily.map F)).obj X) := by
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  have hD : (Functor.isoWhiskerRight (FiniteFamily.mapIso p.comparisonIso)
      (FiniteTensor.tensor (V := W))).hom.app X =
      (FiniteTensor.tensor (V := W)).map
        ((FiniteFamily.mapIso p.comparisonIso).hom.app X) := by
    simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  have hF2 : (Functor.isoWhiskerLeft
      (FiniteFamily.map (FiniteTensor.tensor (V := V)))
      p.comparisonIso).hom.app X =
      p.comparisonIso.hom.app
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) := by
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  have hRight : (Functor.isoWhiskerRight (FiniteFamily.flattenMapIso F)
        (FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map F))
        (FiniteTensor.flattenIso (V := W)) ≪≫
      Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso (FiniteFamily.map F)
          (FiniteTensor.tensor (V := W))).symm
        (FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerRight (FiniteFamily.mapIso p.comparisonIso)
        (FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerRight
        (FiniteFamily.mapCompIso
          (FiniteTensor.tensor (V := V)) F)
        (FiniteTensor.tensor (V := W)) ≪≫
      Functor.isoWhiskerLeft
        (FiniteFamily.map
          (FiniteTensor.tensor (V := V)))
        p.comparisonIso).hom.app X =
      (FiniteTensor.flattenIso (V := W)).hom.app
        ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
      (FiniteTensor.tensor (V := W)).map
        ((FiniteFamily.mapIso p.comparisonIso).hom.app X) ≫
      p.comparisonIso.hom.app
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) := by
    simp only [Iso.trans_hom, NatTrans.comp_app]
    erw [hLead, hB, hBridge1, hD, hBridge2, hF2]
    with_unfolding_all
      erw [← Category.assoc]
      erw [← Category.assoc]
      erw [← Category.assoc]
      erw [← Category.assoc]
      change ((((𝟙 (((FiniteFamily.map (FiniteFamily.map F) ⋙
                FiniteFamily.flatten (C := W)) ⋙
              FiniteTensor.tensor (V := W)).obj X) ≫
              (FiniteTensor.flattenIso (V := W)).hom.app
                ((FiniteFamily.map (FiniteFamily.map F)).obj X)) ≫
              𝟙 ((FiniteFamily.map (FiniteTensor.tensor (V := W)) ⋙
                  FiniteTensor.tensor (V := W)).obj
                ((FiniteFamily.map (FiniteFamily.map F)).obj X))) ≫
              (FiniteTensor.tensor (V := W)).map
                ((FiniteFamily.mapIso p.comparisonIso).hom.app X)) ≫
              𝟙 ((FiniteTensor.tensor (V := W)).obj
                  ((FiniteFamily.map (FiniteTensor.tensor (V := V) ⋙ F)).obj X))) ≫
              p.comparisonIso.hom.app
                ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) =
              (FiniteTensor.flattenIso (V := W)).hom.app
                ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
              (FiniteTensor.tensor (V := W)).map
                ((FiniteFamily.mapIso p.comparisonIso).hom.app X) ≫
              p.comparisonIso.hom.app
                ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X)
      simp only [Category.id_comp, Category.comp_id]
      exact Category.assoc
        ((FiniteTensor.flattenIso (V := W)).hom.app
          ((FiniteFamily.map (FiniteFamily.map F)).obj X))
        ((FiniteTensor.tensor (V := W)).map
          ((FiniteFamily.mapIso p.comparisonIso).hom.app X))
        (p.comparisonIso.hom.app
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X))
  with_unfolding_all
    exact hRight.symm.trans (hFlat.symm.trans hLeft)

/-- Expand the generic right-unit insertion constructor into its four coherence maps. -/
private theorem rightInsertFromFactor_eq_expanded
    (c : V) (I : FintypeCat) {X : FiniteFamily V}
    (f : _root_.CategoryTheory.Operad.UnitInsertion.rightTensorFamily c I ⟶ X) :
    _root_.CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor c I f =
      (FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (_root_.CategoryTheory.Operad.UnitInsertion.rightSingletonToFlatten c I) ≫
          (FiniteTensor.flattenIso (V := V)).hom.app
            (_root_.CategoryTheory.Operad.UnitInsertion.rightNestedFamily c I) ≫
            (FiniteTensor.tensor (V := V)).map f := by
  let N := _root_.CategoryTheory.Operad.UnitInsertion.rightNestedFamily c I
  let R := (FiniteFamily.flatten (C := V)).obj N
  let T := (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj N
  let a : c ⟶
      (FiniteTensor.tensor (V := V)).obj
        ((FiniteFamily.singleton (C := V)).obj c) :=
    (FiniteTensor.singletonIso (V := V)).inv.app c
  let b : (FiniteTensor.tensor (V := V)).obj
        ((FiniteFamily.singleton (C := V)).obj c) ⟶
      (FiniteTensor.tensor (V := V)).obj R := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := V)).map
        (_root_.CategoryTheory.Operad.UnitInsertion.rightSingletonToFlatten c I)
  let h : (FiniteTensor.tensor (V := V)).obj R ⟶
      (FiniteTensor.tensor (V := V)).obj T :=
    (FiniteTensor.flattenIso (V := V)).hom.app N
  let m : (FiniteTensor.tensor (V := V)).obj T ⟶
      (FiniteTensor.tensor (V := V)).obj X := by
    with_unfolding_all exact (FiniteTensor.tensor (V := V)).map f
  unfold _root_.CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor
  unfold _root_.CategoryTheory.Operad.UnitInsertion.rightInsertPrefix
  symm
  with_unfolding_all change a ≫ b ≫ h ≫ m = (a ≫ b ≫ h) ≫ m
  calc
    a ≫ b ≫ h ≫ m = a ≫ ((b ≫ h) ≫ m) := by
      rw [Category.assoc]
    _ = (a ≫ (b ≫ h)) ≫ m :=
      (Category.assoc a (b ≫ h) m).symm

/-- Expand the generic left-unit insertion constructor into its four coherence maps. -/
private theorem leftInsertFromFactor_eq_expanded
    (c : V) {X : FiniteFamily V}
    (f : _root_.CategoryTheory.Operad.UnitInsertion.leftTensorFamily c ⟶ X) :
    _root_.CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor c f =
      (FiniteTensor.singletonIso (V := V)).inv.app c ≫
        (FiniteTensor.tensor (V := V)).map
          (_root_.CategoryTheory.Operad.UnitInsertion.leftSingletonToFlatten c) ≫
          (FiniteTensor.flattenIso (V := V)).hom.app
            (_root_.CategoryTheory.Operad.UnitInsertion.leftNestedFamily c) ≫
            (FiniteTensor.tensor (V := V)).map f := by
  let N := _root_.CategoryTheory.Operad.UnitInsertion.leftNestedFamily c
  let R := (FiniteFamily.flatten (C := V)).obj N
  let T := (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj N
  let a : c ⟶
      (FiniteTensor.tensor (V := V)).obj
        ((FiniteFamily.singleton (C := V)).obj c) :=
    (FiniteTensor.singletonIso (V := V)).inv.app c
  let b : (FiniteTensor.tensor (V := V)).obj
        ((FiniteFamily.singleton (C := V)).obj c) ⟶
      (FiniteTensor.tensor (V := V)).obj R := by
    with_unfolding_all
      exact (FiniteTensor.tensor (V := V)).map
        (_root_.CategoryTheory.Operad.UnitInsertion.leftSingletonToFlatten c)
  let h : (FiniteTensor.tensor (V := V)).obj R ⟶
      (FiniteTensor.tensor (V := V)).obj T :=
    (FiniteTensor.flattenIso (V := V)).hom.app N
  let m : (FiniteTensor.tensor (V := V)).obj T ⟶
      (FiniteTensor.tensor (V := V)).obj X := by
    with_unfolding_all exact (FiniteTensor.tensor (V := V)).map f
  unfold _root_.CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor
  unfold _root_.CategoryTheory.Operad.UnitInsertion.leftInsertPrefix
  symm
  with_unfolding_all change a ≫ b ≫ h ≫ m = (a ≫ b ≫ h) ≫ m
  calc
    a ≫ b ≫ h ≫ m = a ≫ ((b ≫ h) ≫ m) := by
      rw [Category.assoc]
    _ = (a ≫ (b ≫ h)) ≫ m :=
      (Category.assoc a (b ≫ h) m).symm

private theorem rightUnitInsert_comp_sourceComparison {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O : ColoredSymmetricCollection Color V}
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    rightUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
        sourceComparisonHom p O (ColoredSubstitutionData.rightUnit P) =
      F.map (rightUnitInsert O η P) := by
  let c := O.obj P
  let tW : FiniteFamily W ⥤ W := FiniteTensor.tensor (V := W)
  let tV : FiniteFamily V ⥤ V := FiniteTensor.tensor (V := V)
  let nW : FiniteFamily (FiniteFamily W) :=
    _root_.CategoryTheory.Operad.UnitInsertion.rightNestedFamily (F.obj c) P.inputs
  let nV : FiniteFamily (FiniteFamily V) :=
    _root_.CategoryTheory.Operad.UnitInsertion.rightNestedFamily c P.inputs
  let sW :
      (FiniteFamily.singleton (C := W)).obj (F.obj c) ⟶
        (FiniteFamily.flatten (C := W)).obj nW :=
    by
      with_unfolding_all
        exact _root_.CategoryTheory.Operad.UnitInsertion.rightSingletonToFlatten
          (F.obj c) P.inputs
  let sV :
      (FiniteFamily.singleton (C := V)).obj c ⟶
        (FiniteFamily.flatten (C := V)).obj nV :=
    by
      with_unfolding_all
        exact _root_.CategoryTheory.Operad.UnitInsertion.rightSingletonToFlatten
          c P.inputs
  let fW :
      (FiniteFamily.map tW).obj nW ⟶
        (substitutionFactors (O ⋙ F)).obj (ColoredSubstitutionData.rightUnit P) :=
    by with_unfolding_all exact UnitInsertion.rightFactorHom (O ⋙ F) (mappedUnitAux p η) P
  let fV :
      (FiniteFamily.map tV).obj nV ⟶
        (substitutionFactors O).obj (ColoredSubstitutionData.rightUnit P) :=
    by with_unfolding_all exact UnitInsertion.rightFactorHom O η P
  let mf :
      (FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV) ⟶
        (FiniteFamily.map F).obj
          ((substitutionFactors O).obj (ColoredSubstitutionData.rightUnit P)) :=
    (FiniteFamily.map F).map fV
  let compFamily :
      (FiniteFamily.map tW).obj nW ⟶
        (FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV) :=
    by with_unfolding_all exact rightCompFamily p c P.inputs
  let nestedHom : nW ⟶ (FiniteFamily.map (FiniteFamily.map F)).obj nV :=
    by with_unfolding_all exact rightNestedHom F c P.inputs
  let map_tW_nested :
      (FiniteFamily.map tW).obj nW ⟶
        (FiniteFamily.map (FiniteFamily.map F ⋙ tW)).obj nV :=
    by with_unfolding_all exact (FiniteFamily.map tW).map nestedHom
  let mapIso :
      (FiniteFamily.map (FiniteFamily.map F ⋙ tW)).obj nV ⟶
        (FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV) :=
    by with_unfolding_all exact (FiniteFamily.mapIso p.comparisonIso).hom.app nV
  let invW :
      F.obj c ⟶
        tW.obj ((FiniteFamily.singleton (C := W)).obj (F.obj c)) :=
    by with_unfolding_all exact (FiniteTensor.singletonIso (V := W)).inv.app (F.obj c)
  let invV : c ⟶ tV.obj ((FiniteFamily.singleton (C := V)).obj c) :=
    by with_unfolding_all exact (FiniteTensor.singletonIso (V := V)).inv.app c
  let flattenW_nW :
      tW.obj ((FiniteFamily.flatten (C := W)).obj nW) ⟶
        tW.obj ((FiniteFamily.map tW).obj nW) :=
    by with_unfolding_all exact (FiniteTensor.flattenIso (V := W)).hom.app nW
  let flattenW_map :
      tW.obj ((FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV)) ⟶
        tW.obj ((FiniteFamily.map tW).obj
          ((FiniteFamily.map (FiniteFamily.map F)).obj nV)) :=
    by
      with_unfolding_all
        exact ((FiniteTensor.flattenIso (V := W)).hom.app
          ((FiniteFamily.map (FiniteFamily.map F)).obj nV))
  let flattenV_nV :
      tV.obj ((FiniteFamily.flatten (C := V)).obj nV) ⟶
        tV.obj ((FiniteFamily.map tV).obj nV) :=
    by with_unfolding_all exact (FiniteTensor.flattenIso (V := V)).hom.app nV
  let invFactors :
      (substitutionFactors (O ⋙ F)).obj (ColoredSubstitutionData.rightUnit P) ⟶
        (FiniteFamily.map F).obj
          ((substitutionFactors O).obj (ColoredSubstitutionData.rightUnit P)) :=
    by with_unfolding_all exact (factorsIso F O (ColoredSubstitutionData.rightUnit P)).inv
  let compTarget :
      tW.obj ((FiniteFamily.map F).obj
          ((substitutionFactors O).obj (ColoredSubstitutionData.rightUnit P))) ⟶
        F.obj (tV.obj ((substitutionFactors O).obj (ColoredSubstitutionData.rightUnit P))) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((substitutionFactors O).obj (ColoredSubstitutionData.rightUnit P))).hom
  let compRightTensor :
      tW.obj ((FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV)) ⟶
        F.obj (tV.obj ((FiniteFamily.map tV).obj nV)) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((FiniteFamily.map tV).obj nV)).hom
  let compFlatten :
      tW.obj ((FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV)) ⟶
        F.obj (tV.obj ((FiniteFamily.flatten (C := V)).obj nV)) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((FiniteFamily.flatten (C := V)).obj nV)).hom
  let compSingleton :
      tW.obj ((FiniteFamily.singleton (C := W)).obj (F.obj c)) ⟶
        F.obj (tV.obj ((FiniteFamily.singleton (C := V)).obj c)) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((FiniteFamily.singleton (C := V)).obj c)).hom
  let mapF_sV :
      (FiniteFamily.singleton (C := W)).obj (F.obj c) ⟶
        (FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV) :=
    by with_unfolding_all exact (FiniteFamily.map F).map sV
  let tW_mapF_sV :
      tW.obj ((FiniteFamily.singleton (C := W)).obj (F.obj c)) ⟶
        tW.obj ((FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV)) :=
    tW.map mapF_sV
  let flattenMapNested :
      (FiniteFamily.flatten (C := W)).obj nW ⟶
        (FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV) :=
    (FiniteFamily.flatten (C := W)).map nestedHom
  let rightFlattenIso :
      (FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV) ≅
        (FiniteFamily.flatten (C := W)).obj nW :=
    by with_unfolding_all exact rightFlattenObjMapIso F c P.inputs
  have hLHS_def :
      rightUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
        sourceComparisonHom p O (ColoredSubstitutionData.rightUnit P) =
      invW ≫ tW.map sW ≫ flattenW_nW ≫
        tW.map fW ≫ tW.map invFactors ≫ compTarget := by
    let expandedInsert : (O ⋙ F).obj P ⟶
        (substitutionSource (O ⋙ F)).obj
          (ColoredSubstitutionData.rightUnit P) := by
      with_unfolding_all
        exact invW ≫ (tW.map sW ≫ (flattenW_nW ≫ tW.map fW))
    let expandedSource :
        (substitutionSource (O ⋙ F)).obj
            (ColoredSubstitutionData.rightUnit P) ⟶
          F.obj ((substitutionSource O).obj
            (ColoredSubstitutionData.rightUnit P)) := by
      with_unfolding_all exact tW.map invFactors ≫ compTarget
    have hInsert :
        rightUnitInsert (O ⋙ F) (mappedUnitAux p η) P =
          expandedInsert := by
      unfold rightUnitInsert
      with_unfolding_all
        exact rightInsertFromFactor_eq_expanded
          (V := W) (F.obj c) P.inputs fW
    have hSource :
        sourceComparisonHom p O (ColoredSubstitutionData.rightUnit P) =
          expandedSource := by
      with_unfolding_all rfl
    have hExpanded :
        expandedInsert ≫ expandedSource =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map fW ≫ tW.map invFactors ≫ compTarget := by
      have h0 := Category.assoc invW
        (tW.map sW ≫ (flattenW_nW ≫ tW.map fW))
        (tW.map invFactors ≫ compTarget)
      have h1 := congrArg (invW ≫ ·)
        (Category.assoc (tW.map sW)
          (flattenW_nW ≫ tW.map fW)
          (tW.map invFactors ≫ compTarget))
      have h2 := congrArg (fun k => invW ≫ (tW.map sW ≫ k))
        (Category.assoc flattenW_nW (tW.map fW)
          (tW.map invFactors ≫ compTarget))
      with_unfolding_all
        exact h0.trans (h1.trans h2)
    have h0 := congrArg
      (· ≫ sourceComparisonHom p O (ColoredSubstitutionData.rightUnit P))
      hInsert
    have h1 := congrArg (expandedInsert ≫ ·) hSource
    exact h0.trans (h1.trans hExpanded)
  have hMapComp_fW :
      tW.map fW ≫ tW.map invFactors =
        tW.map (fW ≫ invFactors) := by
    with_unfolding_all
      exact (tW.map_comp fW invFactors).symm
  have hFactor : fW ≫ invFactors = compFamily ≫ mf := by
    with_unfolding_all
      exact rightFactorHomComp p η P
  have hMapFactor :
      tW.map (fW ≫ invFactors) = tW.map (compFamily ≫ mf) :=
    congrArg tW.map hFactor
  have hMapFactor_split :
      tW.map (compFamily ≫ mf) =
        tW.map compFamily ≫ tW.map mf := by
    with_unfolding_all
      exact tW.map_comp compFamily mf
  have hFactorMapped :
      tW.map fW ≫ tW.map invFactors =
        tW.map compFamily ≫ tW.map mf := by
    with_unfolding_all
      exact hMapComp_fW.trans (hMapFactor.trans hMapFactor_split)
  have hCompFamily : compFamily = map_tW_nested ≫ mapIso := by
    with_unfolding_all
      exact (rightCompFamily_eq p c P.inputs).symm
  have hMapCompFamily :
      tW.map compFamily = tW.map map_tW_nested ≫ tW.map mapIso := by
    with_unfolding_all
      exact (congrArg tW.map hCompFamily).trans
        (tW.map_comp map_tW_nested mapIso)
  have hFlatNat_aux :=
    (FiniteTensor.flattenIso (V := W)).hom.naturality nestedHom
  have hFlatNat :
      flattenW_nW ≫ tW.map map_tW_nested =
        tW.map flattenMapNested ≫ flattenW_map := by
    with_unfolding_all
      exact hFlatNat_aux.symm
  have hFlattenMap : flattenMapNested = rightFlattenIso.inv := by
    with_unfolding_all
      exact rightFlatten_map_nestedHom c P.inputs
  have hSingleIso : mapF_sV ≫ rightFlattenIso.hom = sW := by
    with_unfolding_all
      exact rightSingletonToFlatten_map_comp_iso c P.inputs
  have hHomInv :
      rightFlattenIso.hom ≫ rightFlattenIso.inv = 𝟙 _ :=
    rightFlattenIso.hom_inv_id
  have hMapSingle : sW ≫ rightFlattenIso.inv = mapF_sV := by
    with_unfolding_all
      exact ((congrArg (· ≫ rightFlattenIso.inv) hSingleIso.symm).trans
        (Category.assoc mapF_sV
          rightFlattenIso.hom rightFlattenIso.inv)).trans
        ((congrArg (mapF_sV ≫ ·) hHomInv).trans
          (Category.comp_id mapF_sV))
  have hEq_sW_flat : sW ≫ flattenMapNested = mapF_sV := by
    with_unfolding_all
      exact (congrArg (sW ≫ ·) hFlattenMap).trans hMapSingle
  have hTMap_sW_flat :
      tW.map sW ≫ tW.map flattenMapNested = tW_mapF_sV := by
    with_unfolding_all
      exact (tW.map_comp sW flattenMapNested).symm.trans
        (congrArg tW.map hEq_sW_flat)
  have hCompNat_fV :
      tW.map mf ≫ compTarget =
        compRightTensor ≫ F.map (tV.map fV) := by
    with_unfolding_all
      exact comparison_naturality p fV
  have hFlatCompat :
      flattenW_map ≫ tW.map mapIso ≫ compRightTensor =
        compFlatten ≫ F.map flattenV_nV := by
    with_unfolding_all
      exact flatten_compat_reduced_hom_app p nV
  have hCompNat_sV :
      tW_mapF_sV ≫ compFlatten =
        compSingleton ≫ F.map (tV.map sV) := by
    with_unfolding_all
      exact comparison_naturality p sV
  have hSingletonInv : F.map invV = invW ≫ compSingleton := by
    with_unfolding_all
      exact map_singletonIso_inv p c
  have hDef :
      rightUnitInsert O η P =
        invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV := by
    unfold rightUnitInsert
    with_unfolding_all
      exact rightInsertFromFactor_eq_expanded c P.inputs fV
  have hRHS_def :
      F.map (rightUnitInsert O η P) =
        F.map invV ≫ F.map (tV.map sV) ≫
          F.map flattenV_nV ≫ F.map (tV.map fV) := by
    have hMapDef :
        F.map (rightUnitInsert O η P) =
          F.map (invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV) :=
      congrArg F.map hDef
    have h1 :
        F.map (invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV) =
          F.map invV ≫
            F.map (tV.map sV ≫ flattenV_nV ≫ tV.map fV) := by
      with_unfolding_all
        exact F.map_comp invV (tV.map sV ≫ flattenV_nV ≫ tV.map fV)
    have h2 :
        F.map (tV.map sV ≫ flattenV_nV ≫ tV.map fV) =
          F.map (tV.map sV) ≫ F.map (flattenV_nV ≫ tV.map fV) := by
      with_unfolding_all
        exact F.map_comp (tV.map sV) (flattenV_nV ≫ tV.map fV)
    have h3 :
        F.map (flattenV_nV ≫ tV.map fV) =
          F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        exact F.map_comp flattenV_nV (tV.map fV)
    have h12 :
        F.map (invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV) =
          F.map invV ≫ F.map (tV.map sV) ≫
            F.map (flattenV_nV ≫ tV.map fV) := by
      with_unfolding_all
        exact h1.trans (congrArg (F.map invV ≫ ·) h2)
    have h123 :
        F.map invV ≫ F.map (tV.map sV) ≫
            F.map (flattenV_nV ≫ tV.map fV) =
          F.map invV ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        exact congrArg (F.map invV ≫ F.map (tV.map sV) ≫ ·) h3
    exact hMapDef.trans (h12.trans h123)
  have hChain :
      rightUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
        sourceComparisonHom p O (ColoredSubstitutionData.rightUnit P) =
      F.map invV ≫ F.map (tV.map sV) ≫
        F.map flattenV_nV ≫ F.map (tV.map fV) := by
    have h0 :
        rightUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
          sourceComparisonHom p O (ColoredSubstitutionData.rightUnit P) =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map fW ≫ tW.map invFactors ≫ compTarget :=
      hLHS_def
    have hE1 :
        invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map fW ≫ tW.map invFactors ≫ compTarget =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            (tW.map compFamily ≫ tW.map mf) ≫ compTarget := by
      with_unfolding_all
        have hB :
            invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map fW ≫ tW.map invFactors =
              invW ≫ tW.map sW ≫ flattenW_nW ≫
                (tW.map fW ≫ tW.map invFactors) := by
          rfl
        calc
          invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map fW ≫ tW.map invFactors ≫ compTarget
            = (invW ≫ tW.map sW ≫ flattenW_nW ≫
                  tW.map fW ≫ tW.map invFactors) ≫ compTarget := by
              simp only [Category.assoc]
          _ = (invW ≫ tW.map sW ≫ flattenW_nW ≫
                  (tW.map fW ≫ tW.map invFactors)) ≫ compTarget := by
              rw [← hB]
          _ = (invW ≫ tW.map sW ≫ flattenW_nW ≫
                  (tW.map compFamily ≫ tW.map mf)) ≫ compTarget := by
              rw [hFactorMapped]
          _ = invW ≫ tW.map sW ≫ flattenW_nW ≫
                (tW.map compFamily ≫ tW.map mf) ≫ compTarget := by
              simp only [Category.assoc]
    have hE1' :
        invW ≫ tW.map sW ≫ flattenW_nW ≫
            (tW.map compFamily ≫ tW.map mf) ≫ compTarget =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map map_tW_nested ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget := by
      with_unfolding_all
        calc
          invW ≫ tW.map sW ≫ flattenW_nW ≫
                (tW.map compFamily ≫ tW.map mf) ≫ compTarget
            = invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map compFamily ≫ tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
          _ = invW ≫ tW.map sW ≫ flattenW_nW ≫
                  (tW.map map_tW_nested ≫ tW.map mapIso) ≫
                tW.map mf ≫ compTarget := by
                rw [hMapCompFamily]
          _ = invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map map_tW_nested ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
    have hE2 :
        invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map map_tW_nested ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget =
          invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
            flattenW_map ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget := by
      with_unfolding_all
        calc
          invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map map_tW_nested ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget
            = invW ≫ tW.map sW ≫
                  (flattenW_nW ≫ tW.map map_tW_nested) ≫
                tW.map mapIso ≫ tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
          _ = invW ≫ tW.map sW ≫
                  (tW.map flattenMapNested ≫ flattenW_map) ≫
                tW.map mapIso ≫ tW.map mf ≫ compTarget := by
                exact congrArg
                  (fun y => invW ≫ tW.map sW ≫ y ≫
                    tW.map mapIso ≫ tW.map mf ≫ compTarget)
                  hFlatNat
          _ = invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
                flattenW_map ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
    have hE3 :
        invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
            flattenW_map ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget =
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ tW.map mf ≫ compTarget := by
      with_unfolding_all
        calc
          invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
                flattenW_map ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget
            = invW ≫ (tW.map sW ≫ tW.map flattenMapNested) ≫
                flattenW_map ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
          _ = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫ tW.map mf ≫ compTarget := by
                exact congrArg
                  (fun y => invW ≫ y ≫ flattenW_map ≫
                    tW.map mapIso ≫ tW.map mf ≫ compTarget)
                  hTMap_sW_flat
    have hE4 :
        invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ tW.map mf ≫ compTarget =
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ compRightTensor ≫
              F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
              tW.map mapIso ≫ tW.map mf ≫ compTarget
            = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫ (tW.map mf ≫ compTarget) := by
                rfl
          _ = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫
                  (compRightTensor ≫ F.map (tV.map fV)) := by
                rw [hCompNat_fV]
          _ = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫ compRightTensor ≫
                  F.map (tV.map fV) := by
                rfl
    have hE5 :
        invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ compRightTensor ≫ F.map (tV.map fV) =
          invW ≫ tW_mapF_sV ≫ compFlatten ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
              tW.map mapIso ≫ compRightTensor ≫ F.map (tV.map fV)
            = invW ≫ tW_mapF_sV ≫
                  (flattenW_map ≫ tW.map mapIso ≫ compRightTensor) ≫
                F.map (tV.map fV) := by
                simp only [Category.assoc]
          _ = invW ≫ tW_mapF_sV ≫
                  (compFlatten ≫ F.map flattenV_nV) ≫
                F.map (tV.map fV) := by
                exact congrArg
                  (fun y => invW ≫ tW_mapF_sV ≫ y ≫ F.map (tV.map fV))
                  hFlatCompat
          _ = invW ≫ tW_mapF_sV ≫ compFlatten ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                aesop_cat
    have hE6 :
        invW ≫ tW_mapF_sV ≫ compFlatten ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) =
          invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ tW_mapF_sV ≫ compFlatten ≫
              F.map flattenV_nV ≫ F.map (tV.map fV)
            = invW ≫ (tW_mapF_sV ≫ compFlatten) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                simp only [Category.assoc]
          _ = invW ≫ (compSingleton ≫ F.map (tV.map sV)) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                exact congrArg
                  (fun y => invW ≫ y ≫
                    F.map flattenV_nV ≫ F.map (tV.map fV))
                  hCompNat_sV
          _ = invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                simp only [Category.assoc]
    have hE7 :
        invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) =
          F.map invV ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
              F.map flattenV_nV ≫ F.map (tV.map fV)
            = (invW ≫ compSingleton) ≫ F.map (tV.map sV) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                simp only [Category.assoc]
          _ = F.map invV ≫ F.map (tV.map sV) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                rw [← hSingletonInv]
    exact h0.trans
      (hE1.trans
        (hE1'.trans
          (hE2.trans (hE3.trans (hE4.trans (hE5.trans (hE6.trans hE7)))))))
  exact hChain.trans hRHS_def.symm


private theorem leftUnitInsert_comp_sourceComparison {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O : ColoredSymmetricCollection Color V}
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    leftUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
        sourceComparisonHom p O (ColoredSubstitutionData.leftUnit P) =
      F.map (leftUnitInsert O η P) := by
  let c := O.obj P
  let tW : FiniteFamily W ⥤ W := FiniteTensor.tensor (V := W)
  let tV : FiniteFamily V ⥤ V := FiniteTensor.tensor (V := V)
  let nW : FiniteFamily (FiniteFamily W) :=
    _root_.CategoryTheory.Operad.UnitInsertion.leftNestedFamily (F.obj c)
  let nV : FiniteFamily (FiniteFamily V) :=
    _root_.CategoryTheory.Operad.UnitInsertion.leftNestedFamily c
  let sW :
      (FiniteFamily.singleton (C := W)).obj (F.obj c) ⟶
        (FiniteFamily.flatten (C := W)).obj nW :=
    by
      with_unfolding_all
        exact _root_.CategoryTheory.Operad.UnitInsertion.leftSingletonToFlatten (F.obj c)
  let sV :
      (FiniteFamily.singleton (C := V)).obj c ⟶
        (FiniteFamily.flatten (C := V)).obj nV :=
    by with_unfolding_all exact _root_.CategoryTheory.Operad.UnitInsertion.leftSingletonToFlatten c
  let fW :
      (FiniteFamily.map tW).obj nW ⟶
        (substitutionFactors (O ⋙ F)).obj (ColoredSubstitutionData.leftUnit P) :=
    by with_unfolding_all exact UnitInsertion.leftFactorHom (O ⋙ F) (mappedUnitAux p η) P
  let fV :
      (FiniteFamily.map tV).obj nV ⟶
        (substitutionFactors O).obj (ColoredSubstitutionData.leftUnit P) :=
    by with_unfolding_all exact UnitInsertion.leftFactorHom O η P
  let mf :
      (FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV) ⟶
        (FiniteFamily.map F).obj
          ((substitutionFactors O).obj (ColoredSubstitutionData.leftUnit P)) :=
    (FiniteFamily.map F).map fV
  let compFamily :
      (FiniteFamily.map tW).obj nW ⟶
        (FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV) :=
    by with_unfolding_all exact leftCompFamily p c
  let nestedHom : nW ⟶ (FiniteFamily.map (FiniteFamily.map F)).obj nV :=
    by with_unfolding_all exact leftNestedHom F c
  let map_tW_nested :
      (FiniteFamily.map tW).obj nW ⟶
        (FiniteFamily.map (FiniteFamily.map F ⋙ tW)).obj nV :=
    by with_unfolding_all exact (FiniteFamily.map tW).map nestedHom
  let mapIso :
      (FiniteFamily.map (FiniteFamily.map F ⋙ tW)).obj nV ⟶
        (FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV) :=
    by with_unfolding_all exact (FiniteFamily.mapIso p.comparisonIso).hom.app nV
  let invW :
      F.obj c ⟶
        tW.obj ((FiniteFamily.singleton (C := W)).obj (F.obj c)) :=
    by with_unfolding_all exact (FiniteTensor.singletonIso (V := W)).inv.app (F.obj c)
  let invV : c ⟶ tV.obj ((FiniteFamily.singleton (C := V)).obj c) :=
    by with_unfolding_all exact (FiniteTensor.singletonIso (V := V)).inv.app c
  let flattenW_nW :
      tW.obj ((FiniteFamily.flatten (C := W)).obj nW) ⟶
        tW.obj ((FiniteFamily.map tW).obj nW) :=
    by with_unfolding_all exact (FiniteTensor.flattenIso (V := W)).hom.app nW
  let flattenW_map :
      tW.obj ((FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV)) ⟶
        tW.obj ((FiniteFamily.map tW).obj
          ((FiniteFamily.map (FiniteFamily.map F)).obj nV)) :=
    by
      with_unfolding_all
        exact ((FiniteTensor.flattenIso (V := W)).hom.app
          ((FiniteFamily.map (FiniteFamily.map F)).obj nV))
  let flattenV_nV :
      tV.obj ((FiniteFamily.flatten (C := V)).obj nV) ⟶
        tV.obj ((FiniteFamily.map tV).obj nV) :=
    by with_unfolding_all exact (FiniteTensor.flattenIso (V := V)).hom.app nV
  let invFactors :
      (substitutionFactors (O ⋙ F)).obj (ColoredSubstitutionData.leftUnit P) ⟶
        (FiniteFamily.map F).obj
          ((substitutionFactors O).obj (ColoredSubstitutionData.leftUnit P)) :=
    by with_unfolding_all exact (factorsIso F O (ColoredSubstitutionData.leftUnit P)).inv
  let compTarget :
      tW.obj ((FiniteFamily.map F).obj
          ((substitutionFactors O).obj (ColoredSubstitutionData.leftUnit P))) ⟶
        F.obj (tV.obj ((substitutionFactors O).obj (ColoredSubstitutionData.leftUnit P))) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((substitutionFactors O).obj (ColoredSubstitutionData.leftUnit P))).hom
  let compRightTensor :
      tW.obj ((FiniteFamily.map F).obj ((FiniteFamily.map tV).obj nV)) ⟶
        F.obj (tV.obj ((FiniteFamily.map tV).obj nV)) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((FiniteFamily.map tV).obj nV)).hom
  let compFlatten :
      tW.obj ((FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV)) ⟶
        F.obj (tV.obj ((FiniteFamily.flatten (C := V)).obj nV)) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((FiniteFamily.flatten (C := V)).obj nV)).hom
  let compSingleton :
      tW.obj ((FiniteFamily.singleton (C := W)).obj (F.obj c)) ⟶
        F.obj (tV.obj ((FiniteFamily.singleton (C := V)).obj c)) :=
    by with_unfolding_all exact (comparisonIsoApp p
      ((FiniteFamily.singleton (C := V)).obj c)).hom
  let mapF_sV :
      (FiniteFamily.singleton (C := W)).obj (F.obj c) ⟶
        (FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV) :=
    by with_unfolding_all exact (FiniteFamily.map F).map sV
  let tW_mapF_sV :
      tW.obj ((FiniteFamily.singleton (C := W)).obj (F.obj c)) ⟶
        tW.obj ((FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV)) :=
    tW.map mapF_sV
  let flattenMapNested :
      (FiniteFamily.flatten (C := W)).obj nW ⟶
        (FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV) :=
    (FiniteFamily.flatten (C := W)).map nestedHom
  let leftFlattenIso :
      (FiniteFamily.map F).obj
          ((FiniteFamily.flatten (C := V)).obj nV) ≅
        (FiniteFamily.flatten (C := W)).obj nW :=
    by with_unfolding_all exact leftFlattenObjMapIso F c
  have hLHS_def :
      leftUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
        sourceComparisonHom p O (ColoredSubstitutionData.leftUnit P) =
      invW ≫ tW.map sW ≫ flattenW_nW ≫
        tW.map fW ≫ tW.map invFactors ≫ compTarget := by
    let expandedInsert : (O ⋙ F).obj P ⟶
        (substitutionSource (O ⋙ F)).obj
          (ColoredSubstitutionData.leftUnit P) := by
      with_unfolding_all
        exact invW ≫ (tW.map sW ≫ (flattenW_nW ≫ tW.map fW))
    let expandedSource :
        (substitutionSource (O ⋙ F)).obj
            (ColoredSubstitutionData.leftUnit P) ⟶
          F.obj ((substitutionSource O).obj
            (ColoredSubstitutionData.leftUnit P)) := by
      with_unfolding_all exact tW.map invFactors ≫ compTarget
    have hInsert :
        leftUnitInsert (O ⋙ F) (mappedUnitAux p η) P =
          expandedInsert := by
      unfold leftUnitInsert
      with_unfolding_all
        exact leftInsertFromFactor_eq_expanded (V := W) (F.obj c) fW
    have hSource :
        sourceComparisonHom p O (ColoredSubstitutionData.leftUnit P) =
          expandedSource := by
      with_unfolding_all rfl
    have hExpanded :
        expandedInsert ≫ expandedSource =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map fW ≫ tW.map invFactors ≫ compTarget := by
      have h0 := Category.assoc invW
        (tW.map sW ≫ (flattenW_nW ≫ tW.map fW))
        (tW.map invFactors ≫ compTarget)
      have h1 := congrArg (invW ≫ ·)
        (Category.assoc (tW.map sW)
          (flattenW_nW ≫ tW.map fW)
          (tW.map invFactors ≫ compTarget))
      have h2 := congrArg (fun k => invW ≫ (tW.map sW ≫ k))
        (Category.assoc flattenW_nW (tW.map fW)
          (tW.map invFactors ≫ compTarget))
      with_unfolding_all
        exact h0.trans (h1.trans h2)
    have h0 := congrArg
      (· ≫ sourceComparisonHom p O (ColoredSubstitutionData.leftUnit P))
      hInsert
    have h1 := congrArg (expandedInsert ≫ ·) hSource
    exact h0.trans (h1.trans hExpanded)
  have hMapComp_fW :
      tW.map fW ≫ tW.map invFactors =
        tW.map (fW ≫ invFactors) := by
    with_unfolding_all
      exact (tW.map_comp fW invFactors).symm
  have hFactor : fW ≫ invFactors = compFamily ≫ mf := by
    with_unfolding_all
      exact leftFactorHomComp p η P
  have hMapFactor :
      tW.map (fW ≫ invFactors) = tW.map (compFamily ≫ mf) :=
    congrArg tW.map hFactor
  have hMapFactor_split :
      tW.map (compFamily ≫ mf) =
        tW.map compFamily ≫ tW.map mf := by
    with_unfolding_all
      exact tW.map_comp compFamily mf
  have hFactorMapped :
      tW.map fW ≫ tW.map invFactors =
        tW.map compFamily ≫ tW.map mf := by
    with_unfolding_all
      exact hMapComp_fW.trans (hMapFactor.trans hMapFactor_split)
  have hCompFamily : compFamily = map_tW_nested ≫ mapIso := by
    with_unfolding_all
      exact (leftCompFamily_eq p c).symm
  have hMapCompFamily :
      tW.map compFamily = tW.map map_tW_nested ≫ tW.map mapIso := by
    with_unfolding_all
      exact (congrArg tW.map hCompFamily).trans
        (tW.map_comp map_tW_nested mapIso)
  have hFlatNat_aux :=
    (FiniteTensor.flattenIso (V := W)).hom.naturality nestedHom
  have hFlatNat :
      flattenW_nW ≫ tW.map map_tW_nested =
        tW.map flattenMapNested ≫ flattenW_map := by
    with_unfolding_all
      exact hFlatNat_aux.symm
  have hFlattenMap : flattenMapNested = leftFlattenIso.inv := by
    with_unfolding_all
      exact leftFlatten_map_nestedHom c
  have hSingleIso : mapF_sV ≫ leftFlattenIso.hom = sW := by
    with_unfolding_all
      exact leftSingletonToFlatten_map_comp_iso c
  have hHomInv :
      leftFlattenIso.hom ≫ leftFlattenIso.inv = 𝟙 _ :=
    leftFlattenIso.hom_inv_id
  have hMapSingle : sW ≫ leftFlattenIso.inv = mapF_sV := by
    with_unfolding_all
      exact ((congrArg (· ≫ leftFlattenIso.inv) hSingleIso.symm).trans
        (Category.assoc mapF_sV
          leftFlattenIso.hom leftFlattenIso.inv)).trans
        ((congrArg (mapF_sV ≫ ·) hHomInv).trans
          (Category.comp_id mapF_sV))
  have hEq_sW_flat : sW ≫ flattenMapNested = mapF_sV := by
    with_unfolding_all
      exact (congrArg (sW ≫ ·) hFlattenMap).trans hMapSingle
  have hTMap_sW_flat :
      tW.map sW ≫ tW.map flattenMapNested = tW_mapF_sV := by
    with_unfolding_all
      exact (tW.map_comp sW flattenMapNested).symm.trans
        (congrArg tW.map hEq_sW_flat)
  have hCompNat_fV :
      tW.map mf ≫ compTarget =
        compRightTensor ≫ F.map (tV.map fV) := by
    with_unfolding_all
      exact comparison_naturality p fV
  have hFlatCompat :
      flattenW_map ≫ tW.map mapIso ≫ compRightTensor =
        compFlatten ≫ F.map flattenV_nV := by
    with_unfolding_all
      exact flatten_compat_reduced_hom_app p nV
  have hCompNat_sV :
      tW_mapF_sV ≫ compFlatten =
        compSingleton ≫ F.map (tV.map sV) := by
    with_unfolding_all
      exact comparison_naturality p sV
  have hSingletonInv : F.map invV = invW ≫ compSingleton := by
    with_unfolding_all
      exact map_singletonIso_inv p c
  have hDef :
      leftUnitInsert O η P =
        invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV := by
    unfold leftUnitInsert
    with_unfolding_all
      exact leftInsertFromFactor_eq_expanded c fV
  have hRHS_def :
      F.map (leftUnitInsert O η P) =
        F.map invV ≫ F.map (tV.map sV) ≫
          F.map flattenV_nV ≫ F.map (tV.map fV) := by
    have hMapDef :
        F.map (leftUnitInsert O η P) =
          F.map (invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV) :=
      congrArg F.map hDef
    have h1 :
        F.map (invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV) =
          F.map invV ≫
            F.map (tV.map sV ≫ flattenV_nV ≫ tV.map fV) := by
      with_unfolding_all
        exact F.map_comp invV (tV.map sV ≫ flattenV_nV ≫ tV.map fV)
    have h2 :
        F.map (tV.map sV ≫ flattenV_nV ≫ tV.map fV) =
          F.map (tV.map sV) ≫ F.map (flattenV_nV ≫ tV.map fV) := by
      with_unfolding_all
        exact F.map_comp (tV.map sV) (flattenV_nV ≫ tV.map fV)
    have h3 :
        F.map (flattenV_nV ≫ tV.map fV) =
          F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        exact F.map_comp flattenV_nV (tV.map fV)
    have h12 :
        F.map (invV ≫ tV.map sV ≫ flattenV_nV ≫ tV.map fV) =
          F.map invV ≫ F.map (tV.map sV) ≫
            F.map (flattenV_nV ≫ tV.map fV) := by
      with_unfolding_all
        exact h1.trans (congrArg (F.map invV ≫ ·) h2)
    have h123 :
        F.map invV ≫ F.map (tV.map sV) ≫
            F.map (flattenV_nV ≫ tV.map fV) =
          F.map invV ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        exact congrArg (F.map invV ≫ F.map (tV.map sV) ≫ ·) h3
    exact hMapDef.trans (h12.trans h123)
  have hChain :
      leftUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
        sourceComparisonHom p O (ColoredSubstitutionData.leftUnit P) =
      F.map invV ≫ F.map (tV.map sV) ≫
        F.map flattenV_nV ≫ F.map (tV.map fV) := by
    have h0 :
        leftUnitInsert (O ⋙ F) (mappedUnitAux p η) P ≫
          sourceComparisonHom p O (ColoredSubstitutionData.leftUnit P) =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map fW ≫ tW.map invFactors ≫ compTarget :=
      hLHS_def
    have hE1 :
        invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map fW ≫ tW.map invFactors ≫ compTarget =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            (tW.map compFamily ≫ tW.map mf) ≫ compTarget := by
      with_unfolding_all
        have hB :
            invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map fW ≫ tW.map invFactors =
              invW ≫ tW.map sW ≫ flattenW_nW ≫
                (tW.map fW ≫ tW.map invFactors) := by
          rfl
        calc
          invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map fW ≫ tW.map invFactors ≫ compTarget
            = (invW ≫ tW.map sW ≫ flattenW_nW ≫
                  tW.map fW ≫ tW.map invFactors) ≫ compTarget := by
              simp only [Category.assoc]
          _ = (invW ≫ tW.map sW ≫ flattenW_nW ≫
                  (tW.map fW ≫ tW.map invFactors)) ≫ compTarget := by
              rw [← hB]
          _ = (invW ≫ tW.map sW ≫ flattenW_nW ≫
                  (tW.map compFamily ≫ tW.map mf)) ≫ compTarget := by
              rw [hFactorMapped]
          _ = invW ≫ tW.map sW ≫ flattenW_nW ≫
                (tW.map compFamily ≫ tW.map mf) ≫ compTarget := by
              simp only [Category.assoc]
    have hE1' :
        invW ≫ tW.map sW ≫ flattenW_nW ≫
            (tW.map compFamily ≫ tW.map mf) ≫ compTarget =
          invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map map_tW_nested ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget := by
      with_unfolding_all
        calc
          invW ≫ tW.map sW ≫ flattenW_nW ≫
                (tW.map compFamily ≫ tW.map mf) ≫ compTarget
            = invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map compFamily ≫ tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
          _ = invW ≫ tW.map sW ≫ flattenW_nW ≫
                  (tW.map map_tW_nested ≫ tW.map mapIso) ≫
                tW.map mf ≫ compTarget := by
                rw [hMapCompFamily]
          _ = invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map map_tW_nested ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
    have hE2 :
        invW ≫ tW.map sW ≫ flattenW_nW ≫
            tW.map map_tW_nested ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget =
          invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
            flattenW_map ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget := by
      with_unfolding_all
        calc
          invW ≫ tW.map sW ≫ flattenW_nW ≫
                tW.map map_tW_nested ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget
            = invW ≫ tW.map sW ≫
                  (flattenW_nW ≫ tW.map map_tW_nested) ≫
                tW.map mapIso ≫ tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
          _ = invW ≫ tW.map sW ≫
                  (tW.map flattenMapNested ≫ flattenW_map) ≫
                tW.map mapIso ≫ tW.map mf ≫ compTarget := by
                exact congrArg
                  (fun y => invW ≫ tW.map sW ≫ y ≫
                    tW.map mapIso ≫ tW.map mf ≫ compTarget)
                  hFlatNat
          _ = invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
                flattenW_map ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
    have hE3 :
        invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
            flattenW_map ≫ tW.map mapIso ≫
              tW.map mf ≫ compTarget =
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ tW.map mf ≫ compTarget := by
      with_unfolding_all
        calc
          invW ≫ tW.map sW ≫ tW.map flattenMapNested ≫
                flattenW_map ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget
            = invW ≫ (tW.map sW ≫ tW.map flattenMapNested) ≫
                flattenW_map ≫ tW.map mapIso ≫
                  tW.map mf ≫ compTarget := by
                simp only [Category.assoc]
          _ = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫ tW.map mf ≫ compTarget := by
                exact congrArg
                  (fun y => invW ≫ y ≫ flattenW_map ≫
                    tW.map mapIso ≫ tW.map mf ≫ compTarget)
                  hTMap_sW_flat
    have hE4 :
        invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ tW.map mf ≫ compTarget =
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ compRightTensor ≫
              F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
              tW.map mapIso ≫ tW.map mf ≫ compTarget
            = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫ (tW.map mf ≫ compTarget) := by
                rfl
          _ = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫
                  (compRightTensor ≫ F.map (tV.map fV)) := by
                rw [hCompNat_fV]
          _ = invW ≫ tW_mapF_sV ≫ flattenW_map ≫
                tW.map mapIso ≫ compRightTensor ≫
                  F.map (tV.map fV) := by
                rfl
    have hE5 :
        invW ≫ tW_mapF_sV ≫ flattenW_map ≫
            tW.map mapIso ≫ compRightTensor ≫ F.map (tV.map fV) =
          invW ≫ tW_mapF_sV ≫ compFlatten ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ tW_mapF_sV ≫ flattenW_map ≫
              tW.map mapIso ≫ compRightTensor ≫ F.map (tV.map fV)
            = invW ≫ tW_mapF_sV ≫
                  (flattenW_map ≫ tW.map mapIso ≫ compRightTensor) ≫
                F.map (tV.map fV) := by
                simp only [Category.assoc]
          _ = invW ≫ tW_mapF_sV ≫
                  (compFlatten ≫ F.map flattenV_nV) ≫
                F.map (tV.map fV) := by
                exact congrArg
                  (fun y => invW ≫ tW_mapF_sV ≫ y ≫ F.map (tV.map fV))
                  hFlatCompat
          _ = invW ≫ tW_mapF_sV ≫ compFlatten ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                aesop_cat
    have hE6 :
        invW ≫ tW_mapF_sV ≫ compFlatten ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) =
          invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ tW_mapF_sV ≫ compFlatten ≫
              F.map flattenV_nV ≫ F.map (tV.map fV)
            = invW ≫ (tW_mapF_sV ≫ compFlatten) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                simp only [Category.assoc]
          _ = invW ≫ (compSingleton ≫ F.map (tV.map sV)) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                exact congrArg
                  (fun y => invW ≫ y ≫
                    F.map flattenV_nV ≫ F.map (tV.map fV))
                  hCompNat_sV
          _ = invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                simp only [Category.assoc]
    have hE7 :
        invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) =
          F.map invV ≫ F.map (tV.map sV) ≫
            F.map flattenV_nV ≫ F.map (tV.map fV) := by
      with_unfolding_all
        calc
          invW ≫ compSingleton ≫ F.map (tV.map sV) ≫
              F.map flattenV_nV ≫ F.map (tV.map fV)
            = (invW ≫ compSingleton) ≫ F.map (tV.map sV) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                simp only [Category.assoc]
          _ = F.map invV ≫ F.map (tV.map sV) ≫
                F.map flattenV_nV ≫ F.map (tV.map fV) := by
                rw [← hSingletonInv]
    exact h0.trans
      (hE1.trans
        (hE1'.trans
          (hE2.trans (hE3.trans (hE4.trans (hE5.trans (hE6.trans hE7)))))))
  exact hChain.trans hRHS_def.symm

private theorem mappedRightUnit {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    IsRightUnit (O.toCollection ⋙ F) (mappedUnit p O)
      (mappedSubstitution p O) := by
  unfold IsRightUnit
  intro P
  let insertW : (O.toCollection ⋙ F).obj P ⟶
      (substitutionSource (O.toCollection ⋙ F)).obj (ColoredSubstitutionData.rightUnit P) := by
    with_unfolding_all
      exact rightUnitInsert (O.toCollection ⋙ F) (mappedUnit p O) P
  let sourceComp : (substitutionSource (O.toCollection ⋙ F)).obj
      (ColoredSubstitutionData.rightUnit P) ⟶
      F.obj ((substitutionSource O.toCollection).obj (ColoredSubstitutionData.rightUnit P)) := by
    with_unfolding_all
      exact sourceComparisonHom p O.toCollection (ColoredSubstitutionData.rightUnit P)
  let insertV : O.toCollection.obj P ⟶
      (substitutionSource O.toCollection).obj (ColoredSubstitutionData.rightUnit P) := by
    with_unfolding_all exact rightUnitInsert O.toCollection O.unit P
  let substV : (substitutionSource O.toCollection).obj (ColoredSubstitutionData.rightUnit P) ⟶
      (substitutionTarget O.toCollection).obj (ColoredSubstitutionData.rightUnit P) := by
    with_unfolding_all exact O.subst.app (ColoredSubstitutionData.rightUnit P)
  let relabelV : (substitutionTarget O.toCollection).obj (ColoredSubstitutionData.rightUnit P) ⟶
      O.toCollection.obj P := by
    with_unfolding_all exact O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P)
  let relabelW : (substitutionTarget (O.toCollection ⋙ F)).obj
      (ColoredSubstitutionData.rightUnit P) ⟶
      (O.toCollection ⋙ F).obj P := by
    with_unfolding_all
      exact (O.toCollection ⋙ F).map
        (ColoredSubstitutionData.rightUnitTotalHom P)
  have hComp : insertW ≫ sourceComp = F.map insertV := by
    with_unfolding_all exact rightUnitInsert_comp_sourceComparison p O.unit P
  have hRel : relabelW = F.map relabelV := by
    with_unfolding_all rfl
  have hInit : rightUnitInsert (O.toCollection ⋙ F) (mappedUnit p O) P ≫
      (mappedSubstitution p O).app (ColoredSubstitutionData.rightUnit P) ≫
        (O.toCollection ⋙ F).map
          (ColoredSubstitutionData.rightUnitTotalHom P) =
      (insertW ≫ (sourceComp ≫ F.map substV)) ≫ relabelW := by
    with_unfolding_all
      exact (Category.assoc insertW
        (sourceComp ≫ F.map substV) relabelW).symm
  have hAssoc : insertW ≫ (sourceComp ≫ F.map substV) =
      (insertW ≫ sourceComp) ≫ F.map substV := by
    with_unfolding_all exact
      (Category.assoc insertW sourceComp (F.map substV)).symm
  have hAssocW : (insertW ≫ (sourceComp ≫ F.map substV)) ≫ relabelW =
      ((insertW ≫ sourceComp) ≫ F.map substV) ≫ relabelW := by
    with_unfolding_all exact congrArg (· ≫ relabelW) hAssoc
  have hRelW : ((insertW ≫ sourceComp) ≫ F.map substV) ≫ relabelW =
      ((insertW ≫ sourceComp) ≫ F.map substV) ≫ F.map relabelV := by
    with_unfolding_all
      exact congrArg
        (((insertW ≫ sourceComp) ≫ F.map substV) ≫ ·) hRel
  have hGoal : rightUnitInsert (O.toCollection ⋙ F) (mappedUnit p O) P ≫
      (mappedSubstitution p O).app (ColoredSubstitutionData.rightUnit P) ≫
        (O.toCollection ⋙ F).map
          (ColoredSubstitutionData.rightUnitTotalHom P) =
      ((insertW ≫ sourceComp) ≫ F.map substV) ≫ F.map relabelV :=
    hInit.trans (hAssocW.trans hRelW)
  have hPost : (insertW ≫ sourceComp) ≫ F.map substV =
      F.map insertV ≫ F.map substV := by
    with_unfolding_all exact congrArg (· ≫ F.map substV) hComp
  have hPostRel : ((insertW ≫ sourceComp) ≫ F.map substV) ≫
      F.map relabelV = (F.map insertV ≫ F.map substV) ≫ F.map relabelV := by
    with_unfolding_all exact congrArg (· ≫ F.map relabelV) hPost
  have hMap1 : F.map insertV ≫ F.map substV =
      F.map (insertV ≫ substV) := by
    with_unfolding_all exact (F.map_comp insertV substV).symm
  have hMap1W : (F.map insertV ≫ F.map substV) ≫ F.map relabelV =
      F.map (insertV ≫ substV) ≫ F.map relabelV := by
    with_unfolding_all exact congrArg (· ≫ F.map relabelV) hMap1
  have hMap2 : F.map (insertV ≫ substV) ≫ F.map relabelV =
      F.map ((insertV ≫ substV) ≫ relabelV) := by
    with_unfolding_all exact
      (F.map_comp (insertV ≫ substV) relabelV).symm
  have hUnit : (insertV ≫ substV) ≫ relabelV =
      𝟙 (O.toCollection.obj P) := by
    with_unfolding_all
      exact (Category.assoc insertV substV relabelV).trans (O.right_unit P)
  have hMapUnit : F.map ((insertV ≫ substV) ≫ relabelV) =
      F.map (𝟙 (O.toCollection.obj P)) := by
    with_unfolding_all exact congrArg F.map hUnit
  have hId : F.map (𝟙 (O.toCollection.obj P)) =
      𝟙 (F.obj (O.toCollection.obj P)) :=
    F.map_id (O.toCollection.obj P)
  exact hGoal.trans
    (hPostRel.trans (hMap1W.trans (hMap2.trans (hMapUnit.trans hId))))

private theorem mappedLeftUnit {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    IsLeftUnit (O.toCollection ⋙ F) (mappedUnit p O)
      (mappedSubstitution p O) := by
  unfold IsLeftUnit
  intro P
  let insertW : (O.toCollection ⋙ F).obj P ⟶
      (substitutionSource (O.toCollection ⋙ F)).obj (ColoredSubstitutionData.leftUnit P) := by
    with_unfolding_all
      exact leftUnitInsert (O.toCollection ⋙ F) (mappedUnit p O) P
  let sourceComp : (substitutionSource (O.toCollection ⋙ F)).obj
      (ColoredSubstitutionData.leftUnit P) ⟶
      F.obj ((substitutionSource O.toCollection).obj (ColoredSubstitutionData.leftUnit P)) := by
    with_unfolding_all
      exact sourceComparisonHom p O.toCollection (ColoredSubstitutionData.leftUnit P)
  let insertV : O.toCollection.obj P ⟶
      (substitutionSource O.toCollection).obj (ColoredSubstitutionData.leftUnit P) := by
    with_unfolding_all exact leftUnitInsert O.toCollection O.unit P
  let substV : (substitutionSource O.toCollection).obj (ColoredSubstitutionData.leftUnit P) ⟶
      (substitutionTarget O.toCollection).obj (ColoredSubstitutionData.leftUnit P) := by
    with_unfolding_all exact O.subst.app (ColoredSubstitutionData.leftUnit P)
  let relabelV : (substitutionTarget O.toCollection).obj (ColoredSubstitutionData.leftUnit P) ⟶
      O.toCollection.obj P := by
    with_unfolding_all exact O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P)
  let relabelW : (substitutionTarget (O.toCollection ⋙ F)).obj
      (ColoredSubstitutionData.leftUnit P) ⟶
      (O.toCollection ⋙ F).obj P := by
    with_unfolding_all
      exact (O.toCollection ⋙ F).map
        (ColoredSubstitutionData.leftUnitTotalHom P)
  have hComp : insertW ≫ sourceComp = F.map insertV := by
    with_unfolding_all exact leftUnitInsert_comp_sourceComparison p O.unit P
  have hRel : relabelW = F.map relabelV := by
    with_unfolding_all rfl
  have hInit : leftUnitInsert (O.toCollection ⋙ F) (mappedUnit p O) P ≫
      (mappedSubstitution p O).app (ColoredSubstitutionData.leftUnit P) ≫
        (O.toCollection ⋙ F).map
          (ColoredSubstitutionData.leftUnitTotalHom P) =
      (insertW ≫ (sourceComp ≫ F.map substV)) ≫ relabelW := by
    with_unfolding_all
      exact (Category.assoc insertW
        (sourceComp ≫ F.map substV) relabelW).symm
  have hAssoc : insertW ≫ (sourceComp ≫ F.map substV) =
      (insertW ≫ sourceComp) ≫ F.map substV := by
    with_unfolding_all exact
      (Category.assoc insertW sourceComp (F.map substV)).symm
  have hAssocW : (insertW ≫ (sourceComp ≫ F.map substV)) ≫ relabelW =
      ((insertW ≫ sourceComp) ≫ F.map substV) ≫ relabelW := by
    with_unfolding_all exact congrArg (· ≫ relabelW) hAssoc
  have hRelW : ((insertW ≫ sourceComp) ≫ F.map substV) ≫ relabelW =
      ((insertW ≫ sourceComp) ≫ F.map substV) ≫ F.map relabelV := by
    with_unfolding_all
      exact congrArg
        (((insertW ≫ sourceComp) ≫ F.map substV) ≫ ·) hRel
  have hGoal : leftUnitInsert (O.toCollection ⋙ F) (mappedUnit p O) P ≫
      (mappedSubstitution p O).app (ColoredSubstitutionData.leftUnit P) ≫
        (O.toCollection ⋙ F).map
          (ColoredSubstitutionData.leftUnitTotalHom P) =
      ((insertW ≫ sourceComp) ≫ F.map substV) ≫ F.map relabelV :=
    hInit.trans (hAssocW.trans hRelW)
  have hPost : (insertW ≫ sourceComp) ≫ F.map substV =
      F.map insertV ≫ F.map substV := by
    with_unfolding_all exact congrArg (· ≫ F.map substV) hComp
  have hPostRel : ((insertW ≫ sourceComp) ≫ F.map substV) ≫
      F.map relabelV = (F.map insertV ≫ F.map substV) ≫ F.map relabelV := by
    with_unfolding_all exact congrArg (· ≫ F.map relabelV) hPost
  have hMap1 : F.map insertV ≫ F.map substV =
      F.map (insertV ≫ substV) := by
    with_unfolding_all exact (F.map_comp insertV substV).symm
  have hMap1W : (F.map insertV ≫ F.map substV) ≫ F.map relabelV =
      F.map (insertV ≫ substV) ≫ F.map relabelV := by
    with_unfolding_all exact congrArg (· ≫ F.map relabelV) hMap1
  have hMap2 : F.map (insertV ≫ substV) ≫ F.map relabelV =
      F.map ((insertV ≫ substV) ≫ relabelV) := by
    with_unfolding_all exact
      (F.map_comp (insertV ≫ substV) relabelV).symm
  have hUnit : (insertV ≫ substV) ≫ relabelV =
      𝟙 (O.toCollection.obj P) := by
    with_unfolding_all
      exact (Category.assoc insertV substV relabelV).trans (O.left_unit P)
  have hMapUnit : F.map ((insertV ≫ substV) ≫ relabelV) =
      F.map (𝟙 (O.toCollection.obj P)) := by
    with_unfolding_all exact congrArg F.map hUnit
  have hId : F.map (𝟙 (O.toCollection.obj P)) =
      𝟙 (F.obj (O.toCollection.obj P)) :=
    F.map_id (O.toCollection.obj P)
  exact hGoal.trans
    (hPostRel.trans (hMap1W.trans (hMap2.trans (hMapUnit.trans hId))))

private def groupingACompIso (F : V ⥤ W) (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteFamily.map F)).obj
        (AssocInsertion.groupingA O d) ≅
      AssocInsertion.groupingA (O ⋙ F) d where
  hom :=
    { equiv := Equiv.refl _
      hom := fun o =>
        match o with
        | none =>
          𝟙 ((FiniteFamily.singleton (C := W)).obj
            (F.obj (O.obj d.middleData.outerProfile)))
        | some i => (factorsIso F O (d.localData i)).hom }
  inv :=
    { equiv := Equiv.refl _
      hom := fun o =>
        match o with
        | none =>
          𝟙 ((FiniteFamily.singleton (C := W)).obj
            (F.obj (O.obj d.middleData.outerProfile)))
        | some i => (factorsIso F O (d.localData i)).inv }
  hom_inv_id := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)
      | some i =>
        exact heq_of_eq
          (factorsIso F O (d.localData i)).hom_inv_id
  inv_hom_id := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)
      | some i =>
        exact heq_of_eq
          (factorsIso F O (d.localData i)).inv_hom_id

private def groupingBCompIso (F : V ⥤ W) (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteFamily.map F)).obj
        (AssocInsertion.groupingB O d) ≅
      AssocInsertion.groupingB (O ⋙ F) d where
  hom :=
    { equiv := Equiv.refl _
      hom := fun o =>
        match o with
        | none => (factorsIso F O d.middleData).hom
        | some p =>
          𝟙 ((FiniteFamily.singleton (C := W)).obj
            (F.obj (O.obj (d.innerData.inner.obj p)))) }
  inv :=
    { equiv := Equiv.refl _
      hom := fun o =>
        match o with
        | none => (factorsIso F O d.middleData).inv
        | some p =>
          𝟙 ((FiniteFamily.singleton (C := W)).obj
            (F.obj (O.obj (d.innerData.inner.obj p)))) }
  hom_inv_id := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
        exact heq_of_eq
          (factorsIso F O d.middleData).hom_inv_id
      | some _ =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)
  inv_hom_id := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
        exact heq_of_eq
          (factorsIso F O d.middleData).inv_hom_id
      | some _ =>
        exact heq_of_eq (by
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ = 𝟙 _
          simp)

private def flattenedGroupingACompIso (F : V ⥤ W)
    (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    (FiniteFamily.map F).obj (AssocInsertion.flattenedGroupingA O d) ≅
      AssocInsertion.flattenedGroupingA (O ⋙ F) d := by
  with_unfolding_all
    exact (FiniteFamily.flatten (C := W)).mapIso
      (groupingACompIso F O d)

private def flattenedGroupingBCompIso (F : V ⥤ W)
    (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    (FiniteFamily.map F).obj (AssocInsertion.flattenedGroupingB O d) ≅
      AssocInsertion.flattenedGroupingB (O ⋙ F) d := by
  with_unfolding_all
    exact (FiniteFamily.flatten (C := W)).mapIso
      (groupingBCompIso F O d)

omit [FiniteTensor V] [FiniteTensor W] in
private theorem flattenAToFlattenBHom_naturality (F : V ⥤ W)
    (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    (flattenedGroupingACompIso F O d).hom ≫
        AssocInsertion.flattenAToFlattenBHom (O ⋙ F) d =
      (FiniteFamily.map F).map
          (AssocInsertion.flattenAToFlattenBHom O d) ≫
        (flattenedGroupingBCompIso F O d).hom := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro x
    rcases x with ⟨o, b⟩
    cases o with
    | none =>
      cases b
      rfl
    | some i =>
      cases b with
      | none => rfl
      | some _ => rfl
  · intro x
    rcases x with ⟨o, b⟩
    cases o with
    | none =>
      cases b
      exact heq_of_eq (by
        with_unfolding_all
          dsimp only [flattenedGroupingACompIso,
            flattenedGroupingBCompIso, groupingACompIso,
            groupingBCompIso, factorsIso,
            AssocInsertion.flattenAToFlattenBHom]
        with_unfolding_all
          dsimp
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ =
            F.map (𝟙 _) ≫ 𝟙 _
          simp only [F.map_id, Category.comp_id])
    | some i =>
      cases b with
      | none =>
        exact heq_of_eq (by
          with_unfolding_all
            dsimp only [flattenedGroupingACompIso,
              flattenedGroupingBCompIso, groupingACompIso,
              groupingBCompIso, factorsIso,
              AssocInsertion.flattenAToFlattenBHom]
          with_unfolding_all
            dsimp
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ =
            F.map (𝟙 _) ≫ 𝟙 _
          simp only [F.map_id, Category.comp_id])
      | some _ =>
        exact heq_of_eq (by
          with_unfolding_all
            dsimp only [flattenedGroupingACompIso,
              flattenedGroupingBCompIso, groupingACompIso,
              groupingBCompIso, factorsIso,
              AssocInsertion.flattenAToFlattenBHom]
          with_unfolding_all
            dsimp
          change (𝟙 _ : _ ⟶ _) ≫ 𝟙 _ =
            F.map (𝟙 _) ≫ 𝟙 _
          simp only [F.map_id, Category.comp_id])

omit [FiniteTensor V] [FiniteTensor W] in
private theorem flattenAToFlattenBHom_comp_flattenedGroupingBCompIso_inv
    (F : V ⥤ W) (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    AssocInsertion.flattenAToFlattenBHom (O ⋙ F) d ≫
        (flattenedGroupingBCompIso F O d).inv =
      (flattenedGroupingACompIso F O d).inv ≫
        (FiniteFamily.map F).map
          (AssocInsertion.flattenAToFlattenBHom O d) := by
  let isoA := flattenedGroupingACompIso F O d
  let isoB := flattenedGroupingBCompIso F O d
  let fF : AssocInsertion.flattenedGroupingA (O ⋙ F) d ⟶
      AssocInsertion.flattenedGroupingB (O ⋙ F) d :=
    AssocInsertion.flattenAToFlattenBHom (O ⋙ F) d
  let fO : (FiniteFamily.map F).obj
      (AssocInsertion.flattenedGroupingA O d) ⟶
      (FiniteFamily.map F).obj
        (AssocInsertion.flattenedGroupingB O d) :=
    (FiniteFamily.map F).map
      (AssocInsertion.flattenAToFlattenBHom O d)
  have hNat : isoA.hom ≫ fF = fO ≫ isoB.hom :=
    flattenAToFlattenBHom_naturality F O d
  have hA : isoA.inv ≫ isoA.hom = 𝟙 _ := isoA.inv_hom_id
  have hB : isoB.hom ≫ isoB.inv = 𝟙 _ := isoB.hom_inv_id
  calc
    fF ≫ isoB.inv
        = (𝟙 _ ≫ fF) ≫ isoB.inv := by
          rw [Category.id_comp]
    _ = ((isoA.inv ≫ isoA.hom) ≫ fF) ≫ isoB.inv := by
          rw [hA]
    _ = (isoA.inv ≫ (isoA.hom ≫ fF)) ≫ isoB.inv := by
          exact congrArg (· ≫ isoB.inv)
            (Category.assoc isoA.inv isoA.hom fF)
    _ = (isoA.inv ≫ (fO ≫ isoB.hom)) ≫ isoB.inv := by
          rw [hNat]
    _ = isoA.inv ≫ (fO ≫ isoB.hom) ≫ isoB.inv := by
          rw [Category.assoc]
    _ = isoA.inv ≫ fO ≫ isoB.hom ≫ isoB.inv := by
          exact congrArg (isoA.inv ≫ ·)
            (Category.assoc fO isoB.hom isoB.inv)
    _ = isoA.inv ≫ fO ≫ (isoB.hom ≫ isoB.inv) := by
          rfl
    _ = isoA.inv ≫ fO ≫ 𝟙 _ := by
          rw [hB]
    _ = isoA.inv ≫ fO := by
          rw [Category.comp_id]

private noncomputable def groupingACompFamily {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := W))).obj
        (AssocInsertion.groupingA (O ⋙ F) d) ⟶
      (FiniteFamily.map F).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
          (AssocInsertion.groupingA O d)) where
  equiv := Equiv.refl _
  hom := fun o =>
    match o with
    | none =>
      (comparisonIsoApp p ((FiniteFamily.singleton (C := V)).obj
        (O.obj d.middleData.outerProfile))).hom
    | some i => sourceComparisonHom p O (d.localData i)

private noncomputable def groupingBCompFamily {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := W))).obj
        (AssocInsertion.groupingB (O ⋙ F) d) ⟶
      (FiniteFamily.map F).obj
        ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
          (AssocInsertion.groupingB O d)) where
  equiv := Equiv.refl _
  hom := fun o =>
    match o with
    | none => sourceComparisonHom p O d.middleData
    | some q =>
      (comparisonIsoApp p ((FiniteFamily.singleton (C := V)).obj
        (O.obj (d.innerData.inner.obj q)))).hom

private theorem groupingAToFactorsHom_comp_factorsIso_inv
    {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (d : ColoredAssocData Color) :
    AssocInsertion.groupingAToFactorsHom
          (O.toCollection ⋙ F) (mappedSubstitution p O) d ≫
        (factorsIso F O.toCollection d.outerAfterInnerData).inv =
      groupingACompFamily p O.toCollection d ≫
        (FiniteFamily.map F).map
          (AssocInsertion.groupingAToFactorsHom
            O.toCollection O.subst d) := by
  let Xouter := O.toCollection.obj d.middleData.outerProfile
  have hEq := comparisonIso_hom_app_singleton_comp p Xouter
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      have hId :
          (FiniteTensor.singletonIso (V := W)).hom.app (F.obj Xouter) ≫
              𝟙 (F.obj Xouter) =
            p.comparisonIso.hom.app
                ((FiniteFamily.singleton (C := V)).obj Xouter) ≫
              F.map ((FiniteTensor.singletonIso (V := V)).hom.app Xouter) :=
        (Category.comp_id _).trans hEq.symm
      exact heq_of_eq (by
        with_unfolding_all
          dsimp only [groupingACompFamily,
            AssocInsertion.groupingAToFactorsHom, mappedSubstitution,
            factorsIso, comparisonIsoApp]
        with_unfolding_all
          dsimp
          exact hId)
    | some i =>
      exact heq_of_eq (by
        with_unfolding_all
          dsimp only [groupingACompFamily,
            AssocInsertion.groupingAToFactorsHom, mappedSubstitution,
            sourceComparisonHom, factorsIso]
        with_unfolding_all
          dsimp
          exact Category.comp_id _)

private theorem groupingBToFactorsHom_comp_factorsIso_inv
    {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (d : ColoredAssocData Color) :
    AssocInsertion.groupingBToFactorsHom
          (O.toCollection ⋙ F) (mappedSubstitution p O) d ≫
        (factorsIso F O.toCollection d.innerData).inv =
      groupingBCompFamily p O.toCollection d ≫
        (FiniteFamily.map F).map
          (AssocInsertion.groupingBToFactorsHom
            O.toCollection O.subst d) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (by
        with_unfolding_all
          dsimp only [groupingBCompFamily,
            AssocInsertion.groupingBToFactorsHom, mappedSubstitution,
            sourceComparisonHom, factorsIso]
        with_unfolding_all
          dsimp
          exact Category.comp_id _)
    | some q =>
      let Xq := O.toCollection.obj (d.innerData.inner.obj q)
      have hEq := comparisonIso_hom_app_singleton_comp p Xq
      have hId :
          (FiniteTensor.singletonIso (V := W)).hom.app (F.obj Xq) ≫
              𝟙 (F.obj Xq) =
            p.comparisonIso.hom.app
                ((FiniteFamily.singleton (C := V)).obj Xq) ≫
              F.map ((FiniteTensor.singletonIso (V := V)).hom.app Xq) :=
        (Category.comp_id _).trans hEq.symm
      exact heq_of_eq (by
        with_unfolding_all
          dsimp only [groupingBCompFamily,
            AssocInsertion.groupingBToFactorsHom, mappedSubstitution,
            factorsIso, comparisonIsoApp]
        with_unfolding_all
          dsimp
          exact hId)

private theorem groupingACompFamily_eq {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := W))).map
          (groupingACompIso F O d).inv ≫
        (FiniteFamily.mapIso p.comparisonIso).hom.app
          (AssocInsertion.groupingA O d) =
      groupingACompFamily p O d := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      have hMap : (FiniteTensor.tensor (V := W)).map
          (𝟙 ((FiniteFamily.singleton (C := W)).obj
            (F.obj (O.obj d.middleData.outerProfile)))) = 𝟙 _ := by
        exact (FiniteTensor.tensor (V := W)).map_id _
      exact heq_of_eq (by
        change (FiniteTensor.tensor (V := W)).map
            (𝟙 ((FiniteFamily.singleton (C := W)).obj
              (F.obj (O.obj d.middleData.outerProfile)))) ≫
            p.comparisonIso.hom.app
              ((FiniteFamily.singleton (C := V)).obj
                (O.obj d.middleData.outerProfile)) =
          p.comparisonIso.hom.app
            ((FiniteFamily.singleton (C := V)).obj
              (O.obj d.middleData.outerProfile))
        rw [hMap]
        exact Category.id_comp _)
    | some i =>
      exact heq_of_eq (by
        with_unfolding_all
          rfl)

private theorem groupingBCompFamily_eq {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := W))).map
          (groupingBCompIso F O d).inv ≫
        (FiniteFamily.mapIso p.comparisonIso).hom.app
          (AssocInsertion.groupingB O d) =
      groupingBCompFamily p O d := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (by
        with_unfolding_all
          rfl)
    | some q =>
      have hMap : (FiniteTensor.tensor (V := W)).map
          (𝟙 ((FiniteFamily.singleton (C := W)).obj
            (F.obj (O.obj (d.innerData.inner.obj q))))) = 𝟙 _ := by
        exact (FiniteTensor.tensor (V := W)).map_id _
      exact heq_of_eq (by
        change (FiniteTensor.tensor (V := W)).map
            (𝟙 ((FiniteFamily.singleton (C := W)).obj
              (F.obj (O.obj (d.innerData.inner.obj q))))) ≫
            p.comparisonIso.hom.app
              ((FiniteFamily.singleton (C := V)).obj
                (O.obj (d.innerData.inner.obj q))) =
          p.comparisonIso.hom.app
            ((FiniteFamily.singleton (C := V)).obj
              (O.obj (d.innerData.inner.obj q)))
        rw [hMap]
        exact Category.id_comp _)

private theorem groupingBCompIso_hom_comp_groupingBToFactorsHom
    {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := W))).map
          (groupingBCompIso F O.toCollection d).hom ≫
        AssocInsertion.groupingBToFactorsHom
          (O.toCollection ⋙ F) (mappedSubstitution p O) d =
      (FiniteFamily.mapIso p.comparisonIso).hom.app
          (AssocInsertion.groupingB O.toCollection d) ≫
        (FiniteFamily.map F).map
          (AssocInsertion.groupingBToFactorsHom
            O.toCollection O.subst d) ≫
        (factorsIso F O.toCollection d.innerData).hom := by
  let tWMap : FiniteFamily (FiniteFamily W) ⥤ FiniteFamily W :=
    FiniteFamily.map (FiniteTensor.tensor (V := W))
  let groupingIso :
      (FiniteFamily.map (FiniteFamily.map F)).obj
        (AssocInsertion.groupingB O.toCollection d) ≅
        AssocInsertion.groupingB (O.toCollection ⋙ F) d :=
    groupingBCompIso F O.toCollection d
  let factorsIsoInner :
      (FiniteFamily.map F).obj
        ((substitutionFactors O.toCollection).obj d.innerData) ≅
        (substitutionFactors (O.toCollection ⋙ F)).obj d.innerData :=
    factorsIso F O.toCollection d.innerData
  let compIsoHomApp :=
    (FiniteFamily.mapIso p.comparisonIso).hom.app
      (AssocInsertion.groupingB O.toCollection d)
  let groupingCompFam := groupingBCompFamily p O.toCollection d
  let factorHomW :=
    AssocInsertion.groupingBToFactorsHom
      (O.toCollection ⋙ F) (mappedSubstitution p O) d
  let factorHomV :=
    AssocInsertion.groupingBToFactorsHom O.toCollection O.subst d
  let mapF : FiniteFamily V ⥤ FiniteFamily W := FiniteFamily.map F
  let mapF_factorHomV := mapF.map factorHomV
  let desiredRHS := compIsoHomApp ≫ mapF_factorHomV ≫ factorsIsoInner.hom
  have hCompFamEq :
      tWMap.map groupingIso.inv ≫ compIsoHomApp = groupingCompFam :=
    groupingBCompFamily_eq p O.toCollection d
  have hFactorInvEq :
      factorHomW ≫ factorsIsoInner.inv =
        groupingCompFam ≫ mapF_factorHomV :=
    groupingBToFactorsHom_comp_factorsIso_inv p O d
  have hGroupWith :
      groupingCompFam ≫ mapF_factorHomV =
        (tWMap.map groupingIso.inv ≫ compIsoHomApp) ≫ mapF_factorHomV := by
    exact congrArg (fun k => k ≫ mapF_factorHomV) hCompFamEq.symm
  have hAssoc1 :
      (tWMap.map groupingIso.inv ≫ compIsoHomApp) ≫ mapF_factorHomV =
        tWMap.map groupingIso.inv ≫ (compIsoHomApp ≫ mapF_factorHomV) :=
    Category.assoc _ _ _
  have hGroupEq :
      groupingCompFam ≫ mapF_factorHomV =
        tWMap.map groupingIso.inv ≫ (compIsoHomApp ≫ mapF_factorHomV) :=
    Eq.trans hGroupWith hAssoc1
  have hFactorEq :
      factorHomW ≫ factorsIsoInner.inv =
        tWMap.map groupingIso.inv ≫ (compIsoHomApp ≫ mapF_factorHomV) :=
    Eq.trans hFactorInvEq hGroupEq
  have hPost :
      (factorHomW ≫ factorsIsoInner.inv) ≫ factorsIsoInner.hom =
        (tWMap.map groupingIso.inv ≫ (compIsoHomApp ≫ mapF_factorHomV)) ≫
          factorsIsoInner.hom :=
    congrArg (fun k => k ≫ factorsIsoInner.hom) hFactorEq
  have hLeftAssoc :
      (factorHomW ≫ factorsIsoInner.inv) ≫ factorsIsoInner.hom =
        factorHomW ≫ (factorsIsoInner.inv ≫ factorsIsoInner.hom) :=
    Category.assoc _ _ _
  have hLeftInvHom : factorsIsoInner.inv ≫ factorsIsoInner.hom = 𝟙 _ :=
    factorsIsoInner.inv_hom_id
  have hLeftStep :
      factorHomW ≫ (factorsIsoInner.inv ≫ factorsIsoInner.hom) =
        factorHomW ≫ 𝟙 _ :=
    congrArg (fun k => factorHomW ≫ k) hLeftInvHom
  have hLeftCompId : factorHomW ≫ 𝟙 _ = factorHomW :=
    Category.comp_id _
  have hLeft :
      (factorHomW ≫ factorsIsoInner.inv) ≫ factorsIsoInner.hom = factorHomW :=
    Eq.trans hLeftAssoc (Eq.trans hLeftStep hLeftCompId)
  have hRightAssoc :
      (tWMap.map groupingIso.inv ≫ (compIsoHomApp ≫ mapF_factorHomV)) ≫
          factorsIsoInner.hom =
        tWMap.map groupingIso.inv ≫
          ((compIsoHomApp ≫ mapF_factorHomV) ≫ factorsIsoInner.hom) :=
    Category.assoc _ _ _
  have hRightInner :
      (compIsoHomApp ≫ mapF_factorHomV) ≫ factorsIsoInner.hom =
        desiredRHS :=
    Category.assoc compIsoHomApp mapF_factorHomV factorsIsoInner.hom
  have hRight :
      (tWMap.map groupingIso.inv ≫
          (compIsoHomApp ≫ mapF_factorHomV)) ≫ factorsIsoInner.hom =
        tWMap.map groupingIso.inv ≫ desiredRHS :=
    hRightAssoc.trans
      (congrArg (tWMap.map groupingIso.inv ≫ ·) hRightInner)
  have hFactorHomEq :
      factorHomW = tWMap.map groupingIso.inv ≫ desiredRHS :=
    Eq.trans hLeft.symm (Eq.trans hPost hRight)
  have hPre :
      tWMap.map groupingIso.hom ≫ factorHomW =
        tWMap.map groupingIso.hom ≫
          (tWMap.map groupingIso.inv ≫ desiredRHS) :=
    congrArg (fun k => tWMap.map groupingIso.hom ≫ k) hFactorHomEq
  have hPreAssoc :
      tWMap.map groupingIso.hom ≫
          (tWMap.map groupingIso.inv ≫ desiredRHS) =
        (tWMap.map groupingIso.hom ≫ tWMap.map groupingIso.inv) ≫
          desiredRHS :=
    (Category.assoc _ _ _).symm
  have hMapComp :
      tWMap.map groupingIso.hom ≫ tWMap.map groupingIso.inv =
        tWMap.map (groupingIso.hom ≫ groupingIso.inv) :=
    (tWMap.map_comp groupingIso.hom groupingIso.inv).symm
  have hHomInv : groupingIso.hom ≫ groupingIso.inv = 𝟙 _ :=
    groupingIso.hom_inv_id
  have hMapHomInv :
      tWMap.map (groupingIso.hom ≫ groupingIso.inv) =
        tWMap.map (𝟙 _) :=
    congrArg tWMap.map hHomInv
  have hMapId :
      tWMap.map (𝟙 ((FiniteFamily.map (FiniteFamily.map F)).obj
        (AssocInsertion.groupingB O.toCollection d))) = 𝟙 _ :=
    tWMap.map_id _
  have hHomInvMap :
      tWMap.map groupingIso.hom ≫ tWMap.map groupingIso.inv = 𝟙 _ :=
    Eq.trans hMapComp (Eq.trans hMapHomInv hMapId)
  have hIdComp : 𝟙 _ ≫ desiredRHS = desiredRHS := Category.id_comp _
  have hFinalAssoc :
      (tWMap.map groupingIso.hom ≫ tWMap.map groupingIso.inv) ≫
          desiredRHS =
        𝟙 _ ≫ desiredRHS :=
    congrArg (fun k => k ≫ desiredRHS) hHomInvMap
  have hGoal :
      tWMap.map groupingIso.hom ≫ factorHomW = desiredRHS :=
    Eq.trans hPre (Eq.trans hPreAssoc (Eq.trans hFinalAssoc hIdComp))
  exact hGoal

private noncomputable def associativityCommonSourceComparisonHom
    {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredSymmetricCollection Color V) (d : ColoredAssocData Color) :
    associativityCommonSource (O ⋙ F) d ⟶
      F.obj (associativityCommonSource O d) :=
  (FiniteTensor.tensor (V := W)).map
      (flattenedGroupingACompIso F O d).inv ≫
    (comparisonIsoApp p
      (AssocInsertion.flattenedGroupingA O d)).hom

private theorem associativityRouteA_comparison
    {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (d : ColoredAssocData Color) :
    associativityRouteA
        (O.toCollection ⋙ F) (mappedSubstitution p O) d =
      associativityCommonSourceComparisonHom p O.toCollection d ≫
        F.map (associativityRouteA O.toCollection O.subst d) := by
  let tW : FiniteFamily W ⥤ W := FiniteTensor.tensor (V := W)
  let tV : FiniteFamily V ⥤ V := FiniteTensor.tensor (V := V)
  let groupingA_V : FiniteFamily (FiniteFamily V) :=
    AssocInsertion.groupingA O.toCollection d
  let groupingA_W : FiniteFamily (FiniteFamily W) :=
    AssocInsertion.groupingA (O.toCollection ⋙ F) d
  let flattenedA_V : FiniteFamily V :=
    AssocInsertion.flattenedGroupingA O.toCollection d
  let flattenedA_W : FiniteFamily W :=
    AssocInsertion.flattenedGroupingA (O.toCollection ⋙ F) d
  let outerData := d.outerAfterInnerData
  let groupingIso : (FiniteFamily.map (FiniteFamily.map F)).obj
      groupingA_V ≅ groupingA_W :=
    groupingACompIso F O.toCollection d
  let flattenedIso : (FiniteFamily.map F).obj flattenedA_V ≅ flattenedA_W :=
    flattenedGroupingACompIso F O.toCollection d
  let factorHom_V : (FiniteFamily.map tV).obj groupingA_V ⟶
      (substitutionFactors O.toCollection).obj outerData :=
    by with_unfolding_all exact
      AssocInsertion.groupingAToFactorsHom O.toCollection O.subst d
  let factorHom_W : (FiniteFamily.map tW).obj groupingA_W ⟶
      (substitutionFactors (O.toCollection ⋙ F)).obj outerData :=
    by
      with_unfolding_all
        exact AssocInsertion.groupingAToFactorsHom (O.toCollection ⋙ F)
          (mappedSubstitution p O) d
  let invFactors : (substitutionFactors (O.toCollection ⋙ F)).obj outerData ⟶
      (FiniteFamily.map F).obj
        ((substitutionFactors O.toCollection).obj outerData) :=
    by with_unfolding_all exact
      (factorsIso F O.toCollection outerData).inv
  let compFlattened : tW.obj ((FiniteFamily.map F).obj flattenedA_V) ⟶
      F.obj (tV.obj flattenedA_V) :=
    by with_unfolding_all exact
      (comparisonIsoApp p flattenedA_V).hom
  let compOuter : tW.obj
      ((FiniteFamily.map F).obj
        ((substitutionFactors O.toCollection).obj outerData)) ⟶
          F.obj (tV.obj
            ((substitutionFactors O.toCollection).obj outerData)) :=
    by with_unfolding_all exact
      (comparisonIsoApp p
        ((substitutionFactors O.toCollection).obj outerData)).hom
  let compMapTensor : tW.obj
      ((FiniteFamily.map F).obj ((FiniteFamily.map tV).obj groupingA_V)) ⟶
        F.obj (tV.obj ((FiniteFamily.map tV).obj groupingA_V)) :=
    by with_unfolding_all exact
      (comparisonIsoApp p ((FiniteFamily.map tV).obj groupingA_V)).hom
  let mapIsoHom : (FiniteFamily.map (FiniteFamily.map F ⋙ tW)).obj
      groupingA_V ⟶
        (FiniteFamily.map (tV ⋙ F)).obj groupingA_V :=
    by with_unfolding_all exact
      (FiniteFamily.mapIso p.comparisonIso).hom.app groupingA_V
  let flattenIso_W : tW.obj
      ((FiniteFamily.flatten (C := W)).obj groupingA_W) ⟶
        tW.obj ((FiniteFamily.map tW).obj groupingA_W) :=
    by with_unfolding_all exact
      (FiniteTensor.flattenIso (V := W)).hom.app groupingA_W
  let flattenIso_W_Y : tW.obj
      ((FiniteFamily.flatten (C := W)).obj
        ((FiniteFamily.map (FiniteFamily.map F)).obj groupingA_V)) ⟶
          tW.obj
            ((FiniteFamily.map tW).obj
              ((FiniteFamily.map (FiniteFamily.map F)).obj groupingA_V)) :=
    by
      with_unfolding_all
        exact (FiniteTensor.flattenIso (V := W)).hom.app ((FiniteFamily.map
          (FiniteFamily.map F)).obj groupingA_V)
  let flattenIso_V : tV.obj
      ((FiniteFamily.flatten (C := V)).obj groupingA_V) ⟶
        tV.obj ((FiniteFamily.map tV).obj groupingA_V) :=
    by with_unfolding_all exact
      (FiniteTensor.flattenIso (V := V)).hom.app groupingA_V
  let map_tW_groupingIsoInv : (FiniteFamily.map tW).obj groupingA_W ⟶
      (FiniteFamily.map (FiniteFamily.map F ⋙ tW)).obj groupingA_V :=
    by with_unfolding_all exact
      (FiniteFamily.map tW).map groupingIso.inv
  let tW_mapFlattenedIsoInv : tW.obj flattenedA_W ⟶
      tW.obj ((FiniteFamily.map F).obj flattenedA_V) :=
    by with_unfolding_all exact tW.map flattenedIso.inv
  let mapF_factorHom_V : (FiniteFamily.map F).obj
      ((FiniteFamily.map tV).obj groupingA_V) ⟶
        (FiniteFamily.map F).obj
          ((substitutionFactors O.toCollection).obj outerData) :=
    (FiniteFamily.map F).map factorHom_V
  let groupingACompFam : (FiniteFamily.map tW).obj groupingA_W ⟶
      (FiniteFamily.map F).obj ((FiniteFamily.map tV).obj groupingA_V) :=
    groupingACompFamily p O.toCollection d
  have hLHS_def : associativityRouteA
      (O.toCollection ⋙ F) (mappedSubstitution p O) d =
        flattenIso_W ≫ tW.map factorHom_W ≫ tW.map invFactors ≫
          compOuter ≫ F.map (O.subst.app outerData) := by
    with_unfolding_all
      change (FiniteTensor.flattenIso (V := W)).hom.app groupingA_W ≫
        (tW.map factorHom_W ≫
          ((tW.map invFactors ≫ compOuter) ≫
            F.map (O.subst.app outerData))) =
        flattenIso_W ≫ tW.map factorHom_W ≫ tW.map invFactors ≫
          compOuter ≫ F.map (O.subst.app outerData)
    aesop_cat
  have hFlatNat_aux :=
    (FiniteTensor.flattenIso (V := W)).hom.naturality groupingIso.inv
  have hFlatNat : flattenIso_W ≫ tW.map map_tW_groupingIsoInv =
      tW_mapFlattenedIsoInv ≫ flattenIso_W_Y := by
    with_unfolding_all
      exact hFlatNat_aux.symm
  have hGCeq : map_tW_groupingIsoInv ≫ mapIsoHom = groupingACompFam := by
    with_unfolding_all
      exact groupingACompFamily_eq p O.toCollection d
  have hFactorComp : factorHom_W ≫ invFactors =
      groupingACompFam ≫ mapF_factorHom_V := by
    with_unfolding_all
      exact groupingAToFactorsHom_comp_factorsIso_inv p O d
  have hMapComp_factors : tW.map factorHom_W ≫ tW.map invFactors =
      tW.map (factorHom_W ≫ invFactors) := by
    with_unfolding_all
      exact (tW.map_comp factorHom_W invFactors).symm
  have hMapFactor : tW.map (factorHom_W ≫ invFactors) =
      tW.map (groupingACompFam ≫ mapF_factorHom_V) :=
    congrArg tW.map hFactorComp
  have hMapFactorSplit : tW.map (groupingACompFam ≫ mapF_factorHom_V) =
      tW.map groupingACompFam ≫ tW.map mapF_factorHom_V := by
    with_unfolding_all
      exact tW.map_comp groupingACompFam mapF_factorHom_V
  have hMapGC : tW.map groupingACompFam =
      tW.map map_tW_groupingIsoInv ≫ tW.map mapIsoHom := by
    have h : groupingACompFam = map_tW_groupingIsoInv ≫ mapIsoHom :=
      hGCeq.symm
    have h1 : tW.map groupingACompFam =
        tW.map (map_tW_groupingIsoInv ≫ mapIsoHom) :=
      congrArg tW.map h
    have h2 : tW.map (map_tW_groupingIsoInv ≫ mapIsoHom) =
        tW.map map_tW_groupingIsoInv ≫ tW.map mapIsoHom := by
      with_unfolding_all
        exact tW.map_comp map_tW_groupingIsoInv mapIsoHom
    exact h1.trans h2
  have hFlatCompat : flattenIso_W_Y ≫ tW.map mapIsoHom ≫ compMapTensor =
      compFlattened ≫ F.map flattenIso_V := by
    with_unfolding_all
      exact flatten_compat_reduced_hom_app p groupingA_V
  have hCompNat : tW.map mapF_factorHom_V ≫ compOuter =
      compMapTensor ≫ F.map (tV.map factorHom_V) := by
    with_unfolding_all
      exact comparison_naturality p factorHom_V
  have hRouteA_V_def : associativityRouteA O.toCollection O.subst d =
      flattenIso_V ≫ tV.map factorHom_V ≫ O.subst.app outerData := by
    with_unfolding_all rfl
  have hFMapRoute : F.map (associativityRouteA O.toCollection O.subst d) =
      F.map flattenIso_V ≫ F.map (tV.map factorHom_V) ≫
        F.map (O.subst.app outerData) := by
    have h1 : F.map (associativityRouteA O.toCollection O.subst d) =
        F.map (flattenIso_V ≫ tV.map factorHom_V ≫
          O.subst.app outerData) :=
      congrArg F.map hRouteA_V_def
    have h2 : F.map (flattenIso_V ≫ tV.map factorHom_V ≫
        O.subst.app outerData) =
        F.map (flattenIso_V ≫ tV.map factorHom_V) ≫
          F.map (O.subst.app outerData) :=
      (congrArg F.map (Category.assoc flattenIso_V
        (tV.map factorHom_V) (O.subst.app outerData)).symm).trans
        (F.map_comp (flattenIso_V ≫ tV.map factorHom_V)
          (O.subst.app outerData))
    have h3 : F.map (flattenIso_V ≫ tV.map factorHom_V) =
        F.map flattenIso_V ≫ F.map (tV.map factorHom_V) :=
      F.map_comp flattenIso_V (tV.map factorHom_V)
    have h4 : F.map (flattenIso_V ≫ tV.map factorHom_V) ≫
        F.map (O.subst.app outerData) =
        (F.map flattenIso_V ≫ F.map (tV.map factorHom_V)) ≫
          F.map (O.subst.app outerData) :=
      congrArg (· ≫ F.map (O.subst.app outerData)) h3
    have h5 : (F.map flattenIso_V ≫ F.map (tV.map factorHom_V)) ≫
        F.map (O.subst.app outerData) =
        F.map flattenIso_V ≫ F.map (tV.map factorHom_V) ≫
          F.map (O.subst.app outerData) := by
      simp only [Category.assoc]
    exact h1.trans (h2.trans (h4.trans h5))
  have hCommonSrc : associativityCommonSourceComparisonHom
      p O.toCollection d = tW_mapFlattenedIsoInv ≫ compFlattened := by
    with_unfolding_all rfl
  have hE1 : flattenIso_W ≫ tW.map factorHom_W ≫ tW.map invFactors ≫
      compOuter ≫ F.map (O.subst.app outerData) =
        flattenIso_W ≫ tW.map (factorHom_W ≫ invFactors) ≫
          compOuter ≫ F.map (O.subst.app outerData) := by
    with_unfolding_all
      have hB : flattenIso_W ≫ tW.map factorHom_W ≫ tW.map invFactors =
          flattenIso_W ≫ (tW.map factorHom_W ≫ tW.map invFactors) := by
        rfl
      calc
        flattenIso_W ≫ tW.map factorHom_W ≫ tW.map invFactors ≫
            compOuter ≫ F.map (O.subst.app outerData)
          = (flattenIso_W ≫ tW.map factorHom_W ≫ tW.map invFactors) ≫
              compOuter ≫ F.map (O.subst.app outerData) := by
            simp only [Category.assoc]
        _ = (flattenIso_W ≫ (tW.map factorHom_W ≫ tW.map invFactors)) ≫
              compOuter ≫ F.map (O.subst.app outerData) := by
            rw [← hB]
        _ = (flattenIso_W ≫ tW.map (factorHom_W ≫ invFactors)) ≫
              compOuter ≫ F.map (O.subst.app outerData) := by
            rw [← hMapComp_factors]
        _ = flattenIso_W ≫ tW.map (factorHom_W ≫ invFactors) ≫
              compOuter ≫ F.map (O.subst.app outerData) := by
            simp only [Category.assoc]
  have hE2 : flattenIso_W ≫ tW.map (factorHom_W ≫ invFactors) ≫
      compOuter ≫ F.map (O.subst.app outerData) =
        flattenIso_W ≫ tW.map (groupingACompFam ≫ mapF_factorHom_V) ≫
          compOuter ≫ F.map (O.subst.app outerData) := by
    exact congrArg
      (fun k => flattenIso_W ≫ k ≫ compOuter ≫
        F.map (O.subst.app outerData))
      hMapFactor
  have hE3 : flattenIso_W ≫ tW.map (groupingACompFam ≫ mapF_factorHom_V) ≫
      compOuter ≫ F.map (O.subst.app outerData) =
        flattenIso_W ≫ (tW.map groupingACompFam ≫
          tW.map mapF_factorHom_V) ≫ compOuter ≫
            F.map (O.subst.app outerData) := by
    with_unfolding_all
      calc
        flattenIso_W ≫ tW.map (groupingACompFam ≫ mapF_factorHom_V) ≫
            compOuter ≫ F.map (O.subst.app outerData)
          = flattenIso_W ≫ (tW.map groupingACompFam ≫
              tW.map mapF_factorHom_V) ≫ compOuter ≫
                F.map (O.subst.app outerData) := by
            rw [← hMapFactorSplit]
        _ = flattenIso_W ≫ (tW.map groupingACompFam ≫
              tW.map mapF_factorHom_V) ≫ compOuter ≫
                F.map (O.subst.app outerData) := by
            rfl
  have hE4 : flattenIso_W ≫ (tW.map groupingACompFam ≫
      tW.map mapF_factorHom_V) ≫ compOuter ≫
        F.map (O.subst.app outerData) =
      flattenIso_W ≫ tW.map groupingACompFam ≫ tW.map mapF_factorHom_V ≫
        compOuter ≫ F.map (O.subst.app outerData) := by
    simp only [Category.assoc]
  have hE5 : flattenIso_W ≫ tW.map groupingACompFam ≫
      tW.map mapF_factorHom_V ≫ compOuter ≫
        F.map (O.subst.app outerData) =
      flattenIso_W ≫ (tW.map map_tW_groupingIsoInv ≫
        tW.map mapIsoHom) ≫ tW.map mapF_factorHom_V ≫ compOuter ≫
          F.map (O.subst.app outerData) := by
    exact congrArg
      (fun k => flattenIso_W ≫ k ≫ tW.map mapF_factorHom_V ≫
        compOuter ≫ F.map (O.subst.app outerData))
      hMapGC
  have hE6 : flattenIso_W ≫ (tW.map map_tW_groupingIsoInv ≫
      tW.map mapIsoHom) ≫ tW.map mapF_factorHom_V ≫ compOuter ≫
        F.map (O.subst.app outerData) =
      (flattenIso_W ≫ tW.map map_tW_groupingIsoInv) ≫ tW.map mapIsoHom ≫
        tW.map mapF_factorHom_V ≫ compOuter ≫
          F.map (O.subst.app outerData) := by
    simp only [Category.assoc]
  have hE7 : (flattenIso_W ≫ tW.map map_tW_groupingIsoInv) ≫
      tW.map mapIsoHom ≫ tW.map mapF_factorHom_V ≫ compOuter ≫
        F.map (O.subst.app outerData) =
      (tW_mapFlattenedIsoInv ≫ flattenIso_W_Y) ≫ tW.map mapIsoHom ≫
        tW.map mapF_factorHom_V ≫ compOuter ≫
          F.map (O.subst.app outerData) := by
    exact congrArg
      (fun k => k ≫ tW.map mapIsoHom ≫ tW.map mapF_factorHom_V ≫
        compOuter ≫ F.map (O.subst.app outerData))
      hFlatNat
  have hE8 : (tW_mapFlattenedIsoInv ≫ flattenIso_W_Y) ≫ tW.map mapIsoHom ≫
      tW.map mapF_factorHom_V ≫ compOuter ≫
        F.map (O.subst.app outerData) =
      tW_mapFlattenedIsoInv ≫ flattenIso_W_Y ≫ tW.map mapIsoHom ≫
        tW.map mapF_factorHom_V ≫ compOuter ≫
          F.map (O.subst.app outerData) := by
    with_unfolding_all
      exact Category.assoc tW_mapFlattenedIsoInv flattenIso_W_Y
        (tW.map mapIsoHom ≫ tW.map mapF_factorHom_V ≫
          compOuter ≫ F.map (O.subst.app outerData))
  have hE9 : tW_mapFlattenedIsoInv ≫ flattenIso_W_Y ≫ tW.map mapIsoHom ≫
      tW.map mapF_factorHom_V ≫ compOuter ≫
        F.map (O.subst.app outerData) =
      tW_mapFlattenedIsoInv ≫ (flattenIso_W_Y ≫ tW.map mapIsoHom ≫
        compMapTensor) ≫ F.map (tV.map factorHom_V) ≫
          F.map (O.subst.app outerData) := by
    with_unfolding_all
      have hMid := congrArg
        (fun k => tW_mapFlattenedIsoInv ≫ flattenIso_W_Y ≫
          tW.map mapIsoHom ≫ k ≫ F.map (O.subst.app outerData))
        hCompNat
      have hPre :
          tW_mapFlattenedIsoInv ≫ flattenIso_W_Y ≫ tW.map mapIsoHom ≫
              tW.map mapF_factorHom_V ≫ compOuter ≫
                F.map (O.subst.app outerData) =
            tW_mapFlattenedIsoInv ≫ flattenIso_W_Y ≫ tW.map mapIsoHom ≫
              (tW.map mapF_factorHom_V ≫ compOuter) ≫
                F.map (O.subst.app outerData) := by
        aesop_cat
      have hPost :
          tW_mapFlattenedIsoInv ≫ flattenIso_W_Y ≫ tW.map mapIsoHom ≫
              (compMapTensor ≫ F.map (tV.map factorHom_V)) ≫
                F.map (O.subst.app outerData) =
            tW_mapFlattenedIsoInv ≫
              (flattenIso_W_Y ≫ tW.map mapIsoHom ≫ compMapTensor) ≫
                F.map (tV.map factorHom_V) ≫
                  F.map (O.subst.app outerData) := by
        have hLeft := congrArg
          (fun k => tW_mapFlattenedIsoInv ≫ flattenIso_W_Y ≫
            tW.map mapIsoHom ≫ k)
          (Category.assoc compMapTensor (F.map (tV.map factorHom_V))
            (F.map (O.subst.app outerData)))
        have hInner1 := Category.assoc flattenIso_W_Y
          (tW.map mapIsoHom ≫ compMapTensor)
          (F.map (tV.map factorHom_V) ≫
            F.map (O.subst.app outerData))
        have hInner2 := congrArg (flattenIso_W_Y ≫ ·)
          (Category.assoc (tW.map mapIsoHom) compMapTensor
            (F.map (tV.map factorHom_V) ≫
              F.map (O.subst.app outerData)))
        have hRight := congrArg (tW_mapFlattenedIsoInv ≫ ·)
          (hInner1.trans hInner2)
        exact hLeft.trans hRight.symm
      exact hPre.trans (hMid.trans hPost)
  have hE10 : tW_mapFlattenedIsoInv ≫ (flattenIso_W_Y ≫ tW.map mapIsoHom ≫
      compMapTensor) ≫ F.map (tV.map factorHom_V) ≫
        F.map (O.subst.app outerData) =
      tW_mapFlattenedIsoInv ≫ compFlattened ≫ F.map flattenIso_V ≫
        F.map (tV.map factorHom_V) ≫
          F.map (O.subst.app outerData) := by
    with_unfolding_all
      have hMid := congrArg
        (fun k => tW_mapFlattenedIsoInv ≫ k ≫
          F.map (tV.map factorHom_V) ≫
            F.map (O.subst.app outerData))
        hFlatCompat
      have hPost := congrArg (tW_mapFlattenedIsoInv ≫ ·)
        (Category.assoc compFlattened (F.map flattenIso_V)
          (F.map (tV.map factorHom_V) ≫
            F.map (O.subst.app outerData)))
      exact hMid.trans hPost
  have hE11 : tW_mapFlattenedIsoInv ≫ compFlattened ≫ F.map flattenIso_V ≫
      F.map (tV.map factorHom_V) ≫ F.map (O.subst.app outerData) =
      (tW_mapFlattenedIsoInv ≫ compFlattened) ≫
        (F.map flattenIso_V ≫ F.map (tV.map factorHom_V) ≫
          F.map (O.subst.app outerData)) := by
    simp only [Category.assoc]
  have hE12 : (tW_mapFlattenedIsoInv ≫ compFlattened) ≫
      (F.map flattenIso_V ≫ F.map (tV.map factorHom_V) ≫
        F.map (O.subst.app outerData)) =
      associativityCommonSourceComparisonHom p O.toCollection d ≫
        F.map (associativityRouteA O.toCollection O.subst d) := by
    have h1 := congrArg
      (· ≫ (F.map flattenIso_V ≫ F.map (tV.map factorHom_V) ≫
        F.map (O.subst.app outerData)))
      hCommonSrc.symm
    have h2 := congrArg
      (associativityCommonSourceComparisonHom p O.toCollection d ≫ ·)
      hFMapRoute.symm
    exact h1.trans h2
  exact hLHS_def.trans
    (hE1.trans
      (hE2.trans
        (hE3.trans
          (hE4.trans
            (hE5.trans
              (hE6.trans
                (hE7.trans
                  (hE8.trans (hE9.trans (hE10.trans (hE11.trans hE12)))))))))))

private theorem associativityRouteB_comparison
    {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (d : ColoredAssocData Color) :
    associativityRouteB
        (O.toCollection ⋙ F) (mappedSubstitution p O) d =
      associativityCommonSourceComparisonHom p O.toCollection d ≫
        F.map (associativityRouteB O.toCollection O.subst d) := by
  let tW : FiniteFamily W ⥤ W := FiniteTensor.tensor (V := W)
  let tV : FiniteFamily V ⥤ V := FiniteTensor.tensor (V := V)
  let groupingB_V : FiniteFamily (FiniteFamily V) :=
    AssocInsertion.groupingB O.toCollection d
  let groupingB_W : FiniteFamily (FiniteFamily W) :=
    AssocInsertion.groupingB (O.toCollection ⋙ F) d
  let flattenedA_V : FiniteFamily V :=
    AssocInsertion.flattenedGroupingA O.toCollection d
  let flattenedA_W : FiniteFamily W :=
    AssocInsertion.flattenedGroupingA (O.toCollection ⋙ F) d
  let flattenedB_V : FiniteFamily V :=
    AssocInsertion.flattenedGroupingB O.toCollection d
  let flattenedB_W : FiniteFamily W :=
    AssocInsertion.flattenedGroupingB (O.toCollection ⋙ F) d
  let groupingIsoB : (FiniteFamily.map (FiniteFamily.map F)).obj groupingB_V ≅ groupingB_W :=
    groupingBCompIso F O.toCollection d
  let flattenedIsoA : (FiniteFamily.map F).obj flattenedA_V ≅ flattenedA_W :=
    flattenedGroupingACompIso F O.toCollection d
  let flattenedIsoB : (FiniteFamily.map F).obj flattenedB_V ≅ flattenedB_W :=
    flattenedGroupingBCompIso F O.toCollection d
  let flattenAToB_V : flattenedA_V ⟶ flattenedB_V :=
    AssocInsertion.flattenAToFlattenBHom O.toCollection d
  let flattenAToB_W : flattenedA_W ⟶ flattenedB_W :=
    AssocInsertion.flattenAToFlattenBHom (O.toCollection ⋙ F) d
  let factorHomB_V : (FiniteFamily.map tV).obj groupingB_V ⟶
      (substitutionFactors O.toCollection).obj d.innerData := by
    with_unfolding_all
      exact AssocInsertion.groupingBToFactorsHom O.toCollection O.subst d
  let factorHomB_W : (FiniteFamily.map tW).obj groupingB_W ⟶
      (substitutionFactors (O.toCollection ⋙ F)).obj d.innerData := by
    with_unfolding_all
      exact AssocInsertion.groupingBToFactorsHom (O.toCollection ⋙ F)
        (mappedSubstitution p O) d
  let flattenIsoB_W : tW.obj flattenedB_W ⟶
      tW.obj ((FiniteFamily.map tW).obj groupingB_W) := by
    with_unfolding_all
      exact (FiniteTensor.flattenIso (V := W)).hom.app groupingB_W
  let flattenIsoB_V : tV.obj flattenedB_V ⟶
      tV.obj ((FiniteFamily.map tV).obj groupingB_V) := by
    with_unfolding_all
      exact (FiniteTensor.flattenIso (V := V)).hom.app groupingB_V
  let flattenIsoW_YB : tW.obj
      ((FiniteFamily.flatten (C := W)).obj
        ((FiniteFamily.map (FiniteFamily.map F)).obj groupingB_V)) ⟶
      tW.obj ((FiniteFamily.map tW).obj
        ((FiniteFamily.map (FiniteFamily.map F)).obj groupingB_V)) := by
    with_unfolding_all
      exact (FiniteTensor.flattenIso (V := W)).hom.app
        ((FiniteFamily.map (FiniteFamily.map F)).obj groupingB_V)
  let tW_mapFlattenedAInv : tW.obj flattenedA_W ⟶
      tW.obj ((FiniteFamily.map F).obj flattenedA_V) := by
    with_unfolding_all
      exact tW.map flattenedIsoA.inv
  let tW_mapFlattenedBHom : tW.obj ((FiniteFamily.map F).obj flattenedB_V) ⟶
      tW.obj flattenedB_W := by
    with_unfolding_all
      exact tW.map flattenedIsoB.hom
  let tW_mapFlattenedBInv : tW.obj flattenedB_W ⟶
      tW.obj ((FiniteFamily.map F).obj flattenedB_V) := by
    with_unfolding_all
      exact tW.map flattenedIsoB.inv
  let map_tW_groupingIsoBHom : (FiniteFamily.map tW).obj
      ((FiniteFamily.map (FiniteFamily.map F)).obj groupingB_V) ⟶
      (FiniteFamily.map tW).obj groupingB_W := by
    with_unfolding_all
      exact (FiniteFamily.map tW).map groupingIsoB.hom
  let tW_map_map_tW_groupingIsoBHom : tW.obj
      ((FiniteFamily.map tW).obj
        ((FiniteFamily.map (FiniteFamily.map F)).obj groupingB_V)) ⟶
      tW.obj ((FiniteFamily.map tW).obj groupingB_W) := by
    with_unfolding_all
      exact tW.map map_tW_groupingIsoBHom
  let mapF_flattenAToB_V : (FiniteFamily.map F).obj flattenedA_V ⟶
      (FiniteFamily.map F).obj flattenedB_V := by
    with_unfolding_all
      exact (FiniteFamily.map F).map flattenAToB_V
  let tW_map_mapF_flattenAToB_V : tW.obj ((FiniteFamily.map F).obj flattenedA_V) ⟶
      tW.obj ((FiniteFamily.map F).obj flattenedB_V) := by
    with_unfolding_all
      exact tW.map mapF_flattenAToB_V
  let compIsoHomB : (FiniteFamily.map (FiniteFamily.map F ⋙ tW)).obj groupingB_V ⟶
      (FiniteFamily.map (tV ⋙ F)).obj groupingB_V := by
    with_unfolding_all
      exact (FiniteFamily.mapIso p.comparisonIso).hom.app groupingB_V
  let compApp_flattenedA_V : tW.obj ((FiniteFamily.map F).obj flattenedA_V) ⟶
      F.obj (tV.obj flattenedA_V) := by
    with_unfolding_all
      exact (comparisonIsoApp p flattenedA_V).hom
  let compApp_flattenedB_V : tW.obj ((FiniteFamily.map F).obj flattenedB_V) ⟶
      F.obj (tV.obj flattenedB_V) := by
    with_unfolding_all
      exact (comparisonIsoApp p flattenedB_V).hom
  let compApp_mapTV_B : tW.obj
      ((FiniteFamily.map F).obj ((FiniteFamily.map tV).obj groupingB_V)) ⟶
      F.obj (tV.obj ((FiniteFamily.map tV).obj groupingB_V)) := by
    with_unfolding_all
      exact (comparisonIsoApp p ((FiniteFamily.map tV).obj groupingB_V)).hom
  let compApp_innerFactors : tW.obj
      ((FiniteFamily.map F).obj
        ((substitutionFactors O.toCollection).obj d.innerData)) ⟶
      F.obj (tV.obj ((substitutionFactors O.toCollection).obj d.innerData)) := by
    with_unfolding_all
      exact (comparisonIsoApp p
        ((substitutionFactors O.toCollection).obj d.innerData)).hom
  let invFactorsInner :
      (substitutionFactors (O.toCollection ⋙ F)).obj d.innerData ⟶
        (FiniteFamily.map F).obj
          ((substitutionFactors O.toCollection).obj d.innerData) := by
    with_unfolding_all
      exact (factorsIso F O.toCollection d.innerData).inv
  let homFactorsInner :
      (FiniteFamily.map F).obj
          ((substitutionFactors O.toCollection).obj d.innerData) ⟶
        (substitutionFactors (O.toCollection ⋙ F)).obj d.innerData := by
    with_unfolding_all
      exact (factorsIso F O.toCollection d.innerData).hom
  let substVInner : tV.obj ((substitutionFactors O.toCollection).obj d.innerData) ⟶
      O.toCollection.obj d.innerData.totalProfile := by
    with_unfolding_all
      exact O.subst.app d.innerData
  let relabelV :
      O.toCollection.obj d.innerData.totalProfile ⟶
        O.toCollection.obj d.outerAfterInnerData.totalProfile := by
    with_unfolding_all
      exact O.toCollection.map d.totalHom
  let relabelW :
      (O.toCollection ⋙ F).obj d.innerData.totalProfile ⟶
        (O.toCollection ⋙ F).obj d.outerAfterInnerData.totalProfile := by
    with_unfolding_all
      exact (O.toCollection ⋙ F).map d.totalHom
  have hCommonSrc : associativityCommonSourceComparisonHom p O.toCollection d =
      tW_mapFlattenedAInv ≫ compApp_flattenedA_V := by
    with_unfolding_all rfl
  have hLHS_def : associativityRouteB
      (O.toCollection ⋙ F) (mappedSubstitution p O) d =
      tW.map flattenAToB_W ≫ flattenIsoB_W ≫ tW.map factorHomB_W ≫
        (tW.map invFactorsInner ≫ compApp_innerFactors ≫
          F.map substVInner) ≫ relabelW := by
    with_unfolding_all
      change (FiniteTensor.tensor (V := W)).map flattenAToB_W ≫
          (FiniteTensor.flattenIso (V := W)).hom.app groupingB_W ≫
            (FiniteTensor.tensor (V := W)).map factorHomB_W ≫
              (((FiniteTensor.tensor (V := W)).map invFactorsInner ≫
                compApp_innerFactors) ≫ F.map substVInner) ≫ relabelW =
          tW.map flattenAToB_W ≫ flattenIsoB_W ≫ tW.map factorHomB_W ≫
            (tW.map invFactorsInner ≫ compApp_innerFactors ≫
              F.map substVInner) ≫ relabelW
      aesop_cat
  have hFlattenAToB_comp : flattenAToB_W ≫ flattenedIsoB.inv =
      flattenedIsoA.inv ≫ (FiniteFamily.map F).map flattenAToB_V :=
    flattenAToFlattenBHom_comp_flattenedGroupingBCompIso_inv F O.toCollection d
  have hTMap_FlattenAToB_comp : tW.map flattenAToB_W ≫ tW_mapFlattenedBInv =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V := by
    have hMapComp : tW.map (flattenAToB_W ≫ flattenedIsoB.inv) =
        tW.map flattenAToB_W ≫ tW_mapFlattenedBInv := by
      with_unfolding_all exact tW.map_comp flattenAToB_W flattenedIsoB.inv
    have hMapComp2 : tW.map (flattenedIsoA.inv ≫ (FiniteFamily.map F).map flattenAToB_V) =
        tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V := by
      with_unfolding_all
        exact tW.map_comp flattenedIsoA.inv ((FiniteFamily.map F).map flattenAToB_V)
    have hEq : tW.map (flattenAToB_W ≫ flattenedIsoB.inv) =
        tW.map (flattenedIsoA.inv ≫ (FiniteFamily.map F).map flattenAToB_V) :=
      congrArg tW.map hFlattenAToB_comp
    exact hMapComp.symm.trans (hEq.trans hMapComp2)
  have hFlattenB_hom_inv : tW_mapFlattenedBInv ≫ tW_mapFlattenedBHom = 𝟙 _ := by
    have hIso : flattenedIsoB.inv ≫ flattenedIsoB.hom = 𝟙 _ := flattenedIsoB.inv_hom_id
    have hMap : tW.map (flattenedIsoB.inv ≫ flattenedIsoB.hom) =
        tW_mapFlattenedBInv ≫ tW_mapFlattenedBHom := by
      with_unfolding_all exact tW.map_comp flattenedIsoB.inv flattenedIsoB.hom
    have hId : tW.map (𝟙 flattenedB_W) = 𝟙 _ :=
      tW.map_id _
    exact hMap.symm.trans ((congrArg tW.map hIso).trans hId)
  have hTMap_flattenAToB_W : tW.map flattenAToB_W =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom := by
    calc
      tW.map flattenAToB_W
        = (tW.map flattenAToB_W ≫ tW_mapFlattenedBInv) ≫ tW_mapFlattenedBHom := by
          rw [Category.assoc, hFlattenB_hom_inv, Category.comp_id]
      _ = (tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V) ≫ tW_mapFlattenedBHom := by
          rw [hTMap_FlattenAToB_comp]
      _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom := by
          simp only [Category.assoc]
  have hFlatNat_aux :=
    (FiniteTensor.flattenIso (V := W)).hom.naturality groupingIsoB.hom
  have hFlatNat : tW_mapFlattenedBHom ≫ flattenIsoB_W =
      flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom := by
    with_unfolding_all exact hFlatNat_aux
  have hGroupingB_comp := groupingBCompIso_hom_comp_groupingBToFactorsHom p O d
  have hFactorB : map_tW_groupingIsoBHom ≫ factorHomB_W =
      compIsoHomB ≫ (FiniteFamily.map F).map factorHomB_V ≫ homFactorsInner := by
    with_unfolding_all exact hGroupingB_comp
  have hTMap_factorB : tW_map_map_tW_groupingIsoBHom ≫ tW.map factorHomB_W =
      tW.map compIsoHomB ≫
        tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
          tW.map homFactorsInner := by
    have h1 : tW.map (map_tW_groupingIsoBHom ≫ factorHomB_W) =
        tW_map_map_tW_groupingIsoBHom ≫ tW.map factorHomB_W := by
      with_unfolding_all exact tW.map_comp map_tW_groupingIsoBHom factorHomB_W
    have h2 : tW.map (compIsoHomB ≫ (FiniteFamily.map F).map factorHomB_V ≫ homFactorsInner) =
        tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
          tW.map homFactorsInner := by
      with_unfolding_all
        calc
          tW.map (compIsoHomB ≫ (FiniteFamily.map F).map factorHomB_V ≫ homFactorsInner)
            = tW.map (compIsoHomB ≫
                ((FiniteFamily.map F).map factorHomB_V ≫ homFactorsInner)) := by
              rfl
          _ = tW.map compIsoHomB ≫
              tW.map ((FiniteFamily.map F).map factorHomB_V ≫ homFactorsInner) := by
              exact tW.map_comp compIsoHomB _
          _ = tW.map compIsoHomB ≫
              (tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
                tW.map homFactorsInner) := by
              exact congrArg (tW.map compIsoHomB ≫ ·)
                (tW.map_comp ((FiniteFamily.map F).map factorHomB_V) homFactorsInner)
          _ = tW.map compIsoHomB ≫
              tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
                tW.map homFactorsInner := by
              rfl
    exact h1.symm.trans ((congrArg tW.map hFactorB).trans h2)
  have hHomInv_inner : homFactorsInner ≫ invFactorsInner =
      𝟙 ((FiniteFamily.map F).obj ((substitutionFactors O.toCollection).obj d.innerData)) :=
    (factorsIso F O.toCollection d.innerData).hom_inv_id
  have hTMap_homInv_inner : tW.map homFactorsInner ≫ tW.map invFactorsInner = 𝟙 _ := by
    have hMap : tW.map (homFactorsInner ≫ invFactorsInner) =
        tW.map homFactorsInner ≫ tW.map invFactorsInner := by
      with_unfolding_all exact tW.map_comp homFactorsInner invFactorsInner
    have hId : tW.map (𝟙 ((FiniteFamily.map F).obj
        ((substitutionFactors O.toCollection).obj d.innerData))) = 𝟙 _ :=
      tW.map_id _
    exact hMap.symm.trans ((congrArg tW.map hHomInv_inner).trans hId)
  have hCompNat_factorB : tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors =
      compApp_mapTV_B ≫ F.map (tV.map factorHomB_V) :=
    comparison_naturality p factorHomB_V
  have hFlatCompat := flatten_compat_reduced_hom_app p groupingB_V
  have hFlatCompat_eq : flattenIsoW_YB ≫ tW.map compIsoHomB ≫ compApp_mapTV_B =
      compApp_flattenedB_V ≫ F.map flattenIsoB_V := by
    with_unfolding_all exact hFlatCompat
  have hCompNat_flattenAToB : tW_map_mapF_flattenAToB_V ≫ compApp_flattenedB_V =
      compApp_flattenedA_V ≫ F.map (tV.map flattenAToB_V) :=
    comparison_naturality p flattenAToB_V
  have hRelabel : relabelW = F.map relabelV := by
    with_unfolding_all rfl
  have hRouteB_V_def : associativityRouteB O.toCollection O.subst d =
      tV.map flattenAToB_V ≫ flattenIsoB_V ≫ tV.map factorHomB_V ≫ substVInner ≫ relabelV := by
    with_unfolding_all rfl
  have hFMapRouteB_V : F.map (associativityRouteB O.toCollection O.subst d) =
      F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ F.map relabelV := by
    have h1 : F.map (associativityRouteB O.toCollection O.subst d) =
        F.map (tV.map flattenAToB_V ≫ flattenIsoB_V ≫
          tV.map factorHomB_V ≫ substVInner ≫ relabelV) :=
      congrArg F.map hRouteB_V_def
    calc
      F.map (tV.map flattenAToB_V ≫ flattenIsoB_V ≫
          tV.map factorHomB_V ≫ substVInner ≫ relabelV)
        = F.map (tV.map flattenAToB_V) ≫
          F.map (flattenIsoB_V ≫ tV.map factorHomB_V ≫ substVInner ≫ relabelV) := by
          with_unfolding_all exact F.map_comp (tV.map flattenAToB_V) _
      _ = F.map (tV.map flattenAToB_V) ≫
          (F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V ≫ substVInner ≫ relabelV)) := by
          exact congrArg (F.map (tV.map flattenAToB_V) ≫ ·)
            (F.map_comp flattenIsoB_V _)
      _ = F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          F.map (tV.map factorHomB_V ≫ substVInner ≫ relabelV) := by
          rfl
      _ = F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          (F.map (tV.map factorHomB_V) ≫ F.map (substVInner ≫ relabelV)) := by
          exact congrArg (F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫ ·)
            (F.map_comp (tV.map factorHomB_V) _)
      _ = F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          F.map (tV.map factorHomB_V) ≫ F.map (substVInner ≫ relabelV) := by
          rfl
      _ = F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          F.map (tV.map factorHomB_V) ≫
            (F.map substVInner ≫ F.map relabelV) := by
          exact congrArg
              (F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
                F.map (tV.map factorHomB_V) ≫ ·)
              (F.map_comp substVInner relabelV)
      _ = F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ F.map relabelV := by
          rfl
  have hE1 : tW.map flattenAToB_W ≫ flattenIsoB_W ≫ tW.map factorHomB_W ≫
      (tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner) ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom ≫
        flattenIsoB_W ≫ tW.map factorHomB_W ≫ tW.map invFactorsInner ≫
          compApp_innerFactors ≫ F.map substVInner ≫ relabelW := by
    calc
      tW.map flattenAToB_W ≫ flattenIsoB_W ≫ tW.map factorHomB_W ≫
            (tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner) ≫ relabelW
        = (tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom) ≫
            flattenIsoB_W ≫ tW.map factorHomB_W ≫
              (tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner) ≫
                relabelW := by
          exact congrArg (· ≫ flattenIsoB_W ≫ tW.map factorHomB_W ≫
            (tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner) ≫
              relabelW)
            hTMap_flattenAToB_W
      _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom ≫
            flattenIsoB_W ≫ tW.map factorHomB_W ≫ tW.map invFactorsInner ≫
              compApp_innerFactors ≫ F.map substVInner ≫ relabelW := by
          simp only [Category.assoc]
  have hE2 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom ≫
      flattenIsoB_W ≫ tW.map factorHomB_W ≫ tW.map invFactorsInner ≫
        compApp_innerFactors ≫ F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
        (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W ≫
          tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫ relabelW := by
    with_unfolding_all
      have hPair : tW_mapFlattenedBHom ≫ flattenIsoB_W ≫ tW.map factorHomB_W ≫
          tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
            relabelW =
          (tW_mapFlattenedBHom ≫ flattenIsoB_W) ≫ tW.map factorHomB_W ≫
            tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
              relabelW := by
        exact (Category.assoc tW_mapFlattenedBHom flattenIsoB_W
          (tW.map factorHomB_W ≫ tW.map invFactorsInner ≫ compApp_innerFactors ≫
            F.map substVInner ≫ relabelW)).symm
      have hPre : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
          tW_mapFlattenedBHom ≫ flattenIsoB_W ≫ tW.map factorHomB_W ≫
            tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
              relabelW =
          tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
            (tW_mapFlattenedBHom ≫ flattenIsoB_W) ≫ tW.map factorHomB_W ≫
              tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                relabelW := by
        have hInner : tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom ≫
            flattenIsoB_W ≫ tW.map factorHomB_W ≫ tW.map invFactorsInner ≫
              compApp_innerFactors ≫ F.map substVInner ≫ relabelW =
            tW_map_mapF_flattenAToB_V ≫ (tW_mapFlattenedBHom ≫ flattenIsoB_W) ≫
              tW.map factorHomB_W ≫ tW.map invFactorsInner ≫ compApp_innerFactors ≫
                F.map substVInner ≫ relabelW := by
          exact congrArg (tW_map_mapF_flattenAToB_V ≫ ·) hPair
        exact congrArg (tW_mapFlattenedAInv ≫ ·) hInner
      calc
        tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ tW_mapFlattenedBHom ≫
            flattenIsoB_W ≫ tW.map factorHomB_W ≫ tW.map invFactorsInner ≫
              compApp_innerFactors ≫ F.map substVInner ≫ relabelW
          = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
              (tW_mapFlattenedBHom ≫ flattenIsoB_W) ≫ tW.map factorHomB_W ≫
                tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                  relabelW := hPre
        _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
              (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W ≫
                tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                  relabelW := by
          rw [hFlatNat]
          rfl
  have hE3 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
      (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W ≫
        tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
        (tW_map_map_tW_groupingIsoBHom ≫ tW.map factorHomB_W) ≫
          tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫ relabelW := by
    with_unfolding_all
      have hAssoc : (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫
          tW.map factorHomB_W =
          flattenIsoW_YB ≫ (tW_map_map_tW_groupingIsoBHom ≫ tW.map factorHomB_W) :=
        Category.assoc flattenIsoW_YB tW_map_map_tW_groupingIsoBHom
          (tW.map factorHomB_W)
      have hPair : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
          (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W ≫
            tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
              relabelW =
          tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
            ((flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W) ≫
              tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                relabelW := by
        calc
          tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
              (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W ≫
                tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                  relabelW
            = (tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
                (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W) ≫
                  tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                    relabelW := by
              simp only [Category.assoc]
          _ = (tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
                ((flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫
                  tW.map factorHomB_W)) ≫
                  tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                    relabelW := by
              simp only [Category.assoc]
          _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
                ((flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫
                  tW.map factorHomB_W) ≫
                  tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                    relabelW := by
              simp only [Category.assoc]
      calc
        tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
            (flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W ≫
              tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                relabelW
          = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
              ((flattenIsoW_YB ≫ tW_map_map_tW_groupingIsoBHom) ≫ tW.map factorHomB_W) ≫
                tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                  relabelW := hPair
        _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
              (flattenIsoW_YB ≫ (tW_map_map_tW_groupingIsoBHom ≫ tW.map factorHomB_W)) ≫
                tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                  relabelW := by
            exact congrArg
              (fun k => tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ k ≫
                tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                  relabelW)
              hAssoc
        _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
              (tW_map_map_tW_groupingIsoBHom ≫ tW.map factorHomB_W) ≫
                tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫
                  relabelW := by
            have hGen : ∀ {C : Type u₂} [Category C] {X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : C}
                (a1 : X0 ⟶ X1) (a2 : X1 ⟶ X2) (b1 : X2 ⟶ X3) (b2 : X3 ⟶ X4)
                (b3 : X4 ⟶ X5) (c1 : X5 ⟶ X6) (c2 : X6 ⟶ X7) (d1 : X7 ⟶ X8)
                (d2 : X8 ⟶ X9),
                a1 ≫ a2 ≫ (b1 ≫ b2 ≫ b3) ≫ c1 ≫ c2 ≫ d1 ≫ d2 =
                a1 ≫ a2 ≫ b1 ≫ (b2 ≫ b3) ≫ c1 ≫ c2 ≫ d1 ≫ d2 := by
              intros
              simp only [Category.assoc]
            with_unfolding_all
              exact hGen tW_mapFlattenedAInv tW_map_mapF_flattenAToB_V flattenIsoW_YB
                tW_map_map_tW_groupingIsoBHom (tW.map factorHomB_W)
                (tW.map invFactorsInner) compApp_innerFactors (F.map substVInner)
                relabelW
  have hE4 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
      (tW_map_map_tW_groupingIsoBHom ≫ tW.map factorHomB_W) ≫
        tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
        (tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
          tW.map homFactorsInner) ≫ tW.map invFactorsInner ≫ compApp_innerFactors ≫
            F.map substVInner ≫ relabelW := by
    exact congrArg
      (tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫ · ≫
        tW.map invFactorsInner ≫ compApp_innerFactors ≫ F.map substVInner ≫ relabelW)
      hTMap_factorB
  have hE5 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
      (tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
        tW.map homFactorsInner) ≫ tW.map invFactorsInner ≫ compApp_innerFactors ≫
          F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
        tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
          (tW.map homFactorsInner ≫ tW.map invFactorsInner) ≫ compApp_innerFactors ≫
            F.map substVInner ≫ relabelW := by
    simp only [Category.assoc]
  have hE6 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
      tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
        (tW.map homFactorsInner ≫ tW.map invFactorsInner) ≫ compApp_innerFactors ≫
          F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
        tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
          compApp_innerFactors ≫ F.map substVInner ≫ relabelW := by
    have hCancel : tW.map homFactorsInner ≫ tW.map invFactorsInner = 𝟙 _ := hTMap_homInv_inner
    calc
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
            tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
              (tW.map homFactorsInner ≫ tW.map invFactorsInner) ≫ compApp_innerFactors ≫
                F.map substVInner ≫ relabelW
        = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
            tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
              𝟙 _ ≫ compApp_innerFactors ≫ F.map substVInner ≫ relabelW := by
          rw [hCancel]
      _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
            tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
              compApp_innerFactors ≫ F.map substVInner ≫ relabelW := by
          simp only [Category.id_comp]
  have hE7 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
      tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
        compApp_innerFactors ≫ F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
        tW.map compIsoHomB ≫ (compApp_mapTV_B ≫ F.map (tV.map factorHomB_V)) ≫
          F.map substVInner ≫ relabelW := by
    with_unfolding_all
      have hPair : tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
          compApp_innerFactors ≫ F.map substVInner ≫ relabelW =
          (tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors) ≫
            F.map substVInner ≫ relabelW := by
        exact (Category.assoc (tW.map ((FiniteFamily.map F).map factorHomB_V))
          compApp_innerFactors (F.map substVInner ≫ relabelW)).symm
      have hPre : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
          tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
            compApp_innerFactors ≫ F.map substVInner ≫ relabelW =
          tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
            tW.map compIsoHomB ≫
              (tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors) ≫
                F.map substVInner ≫ relabelW := by
        have hInner : tW.map compIsoHomB ≫
            tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors ≫
              F.map substVInner ≫ relabelW =
            tW.map compIsoHomB ≫
              (tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors) ≫
                F.map substVInner ≫ relabelW := by
          exact congrArg (tW.map compIsoHomB ≫ ·) hPair
        have hMid : flattenIsoW_YB ≫ tW.map compIsoHomB ≫
            tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors ≫
              F.map substVInner ≫ relabelW =
            flattenIsoW_YB ≫ tW.map compIsoHomB ≫
              (tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors) ≫
                F.map substVInner ≫ relabelW := by
          exact congrArg (flattenIsoW_YB ≫ ·) hInner
        have hOuter : tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
            tW.map compIsoHomB ≫
              tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors ≫
                F.map substVInner ≫ relabelW =
            tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫ tW.map compIsoHomB ≫
              (tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors) ≫
                F.map substVInner ≫ relabelW := by
          exact congrArg (tW_map_mapF_flattenAToB_V ≫ ·) hMid
        exact congrArg (tW_mapFlattenedAInv ≫ ·) hOuter
      calc
        tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
            tW.map compIsoHomB ≫ tW.map ((FiniteFamily.map F).map factorHomB_V) ≫
              compApp_innerFactors ≫ F.map substVInner ≫ relabelW
          = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
              tW.map compIsoHomB ≫
                (tW.map ((FiniteFamily.map F).map factorHomB_V) ≫ compApp_innerFactors) ≫
                  F.map substVInner ≫ relabelW := hPre
        _ = tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
              tW.map compIsoHomB ≫
                (compApp_mapTV_B ≫ F.map (tV.map factorHomB_V)) ≫ F.map substVInner ≫
                  relabelW := by
          exact congrArg
            (fun k => tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
              flattenIsoW_YB ≫ tW.map compIsoHomB ≫ k ≫ F.map substVInner ≫ relabelW)
            hCompNat_factorB
  have hE8 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ flattenIsoW_YB ≫
      tW.map compIsoHomB ≫ (compApp_mapTV_B ≫ F.map (tV.map factorHomB_V)) ≫
        F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
        (flattenIsoW_YB ≫ tW.map compIsoHomB ≫ compApp_mapTV_B) ≫
          F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW := by
    have hGen : ∀ {C : Type u₂} [Category C] {X0 X1 X2 X3 X4 X5 X6 X7 X8 : C}
        (a1 : X0 ⟶ X1) (a2 : X1 ⟶ X2) (b1 : X2 ⟶ X3) (b2 : X3 ⟶ X4)
        (c1 : X4 ⟶ X5) (c2 : X5 ⟶ X6) (d1 : X6 ⟶ X7) (d2 : X7 ⟶ X8),
        a1 ≫ a2 ≫ b1 ≫ b2 ≫ (c1 ≫ c2) ≫ d1 ≫ d2 =
        a1 ≫ a2 ≫ (b1 ≫ b2 ≫ c1) ≫ c2 ≫ d1 ≫ d2 := by
      intros
      simp only [Category.assoc]
    with_unfolding_all
      exact hGen tW_mapFlattenedAInv tW_map_mapF_flattenAToB_V flattenIsoW_YB
        (tW.map compIsoHomB) compApp_mapTV_B (F.map (tV.map factorHomB_V))
        (F.map substVInner) relabelW
  have hE9 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
      (flattenIsoW_YB ≫ tW.map compIsoHomB ≫ compApp_mapTV_B) ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
        (compApp_flattenedB_V ≫ F.map flattenIsoB_V) ≫
          F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW := by
    exact congrArg
      (tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫ · ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW)
      hFlatCompat_eq
  have hE10 : tW_mapFlattenedAInv ≫ tW_map_mapF_flattenAToB_V ≫
      (compApp_flattenedB_V ≫ F.map flattenIsoB_V) ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ (tW_map_mapF_flattenAToB_V ≫ compApp_flattenedB_V) ≫
        F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW := by
    simp only [Category.assoc]
  have hE11 : tW_mapFlattenedAInv ≫ (tW_map_mapF_flattenAToB_V ≫ compApp_flattenedB_V) ≫
      F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW =
      tW_mapFlattenedAInv ≫ (compApp_flattenedA_V ≫ F.map (tV.map flattenAToB_V)) ≫
        F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW := by
    exact congrArg
      (tW_mapFlattenedAInv ≫ · ≫ F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V) ≫
        F.map substVInner ≫ relabelW)
      hCompNat_flattenAToB
  have hE12 : tW_mapFlattenedAInv ≫ (compApp_flattenedA_V ≫ F.map (tV.map flattenAToB_V)) ≫
      F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW =
      (tW_mapFlattenedAInv ≫ compApp_flattenedA_V) ≫ F.map (tV.map flattenAToB_V) ≫
        F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW := by
    simp only [Category.assoc]
  have hE13 : (tW_mapFlattenedAInv ≫ compApp_flattenedA_V) ≫ F.map (tV.map flattenAToB_V) ≫
      F.map flattenIsoB_V ≫ F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW =
      associativityCommonSourceComparisonHom p O.toCollection d ≫
        F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW := by
    exact congrArg (· ≫ F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
      F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW) hCommonSrc.symm
  have hE14 : associativityCommonSourceComparisonHom p O.toCollection d ≫
      F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ relabelW =
      associativityCommonSourceComparisonHom p O.toCollection d ≫
        (F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          F.map (tV.map factorHomB_V) ≫ F.map substVInner) ≫ relabelW := by
    simp only [Category.assoc]
  have hE15 : associativityCommonSourceComparisonHom p O.toCollection d ≫
      (F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner) ≫ relabelW =
      associativityCommonSourceComparisonHom p O.toCollection d ≫
        (F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
          F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ F.map relabelV) := by
    with_unfolding_all
      rw [hRelabel]
      aesop_cat
  have hE16 : associativityCommonSourceComparisonHom p O.toCollection d ≫
      (F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ F.map relabelV) =
      associativityCommonSourceComparisonHom p O.toCollection d ≫
        F.map (associativityRouteB O.toCollection O.subst d) := by
    have hChain : F.map (tV.map flattenAToB_V) ≫ F.map flattenIsoB_V ≫
        F.map (tV.map factorHomB_V) ≫ F.map substVInner ≫ F.map relabelV =
        F.map (associativityRouteB O.toCollection O.subst d) := by
      exact hFMapRouteB_V.symm
    exact congrArg
      (associativityCommonSourceComparisonHom p O.toCollection d ≫ ·)
      hChain
  exact hLHS_def.trans <| hE1.trans <| hE2.trans <| hE3.trans <| hE4.trans <|
    hE5.trans <| hE6.trans <| hE7.trans <| hE8.trans <| hE9.trans <|
      hE10.trans <| hE11.trans <| hE12.trans <| hE13.trans <|
        hE14.trans <| hE15.trans hE16

private theorem mappedAssociative {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    IsAssociative (O.toCollection ⋙ F) (mappedSubstitution p O) := by
  intro d
  calc
    associativityRouteA (O.toCollection ⋙ F) (mappedSubstitution p O) d
        = associativityCommonSourceComparisonHom p O.toCollection d ≫
            F.map (associativityRouteA O.toCollection O.subst d) :=
          associativityRouteA_comparison p O d
    _ = associativityCommonSourceComparisonHom p O.toCollection d ≫
            F.map (associativityRouteB O.toCollection O.subst d) := by
          rw [O.assoc d]
    _ = associativityRouteB (O.toCollection ⋙ F) (mappedSubstitution p O) d :=
          (associativityRouteB_comparison p O d).symm

omit [FiniteTensor V] [FiniteTensor W] in
private theorem factorHom_whiskerRight_comp_factorsIso_inv
    {F : V ⥤ W} {O P : ColoredSymmetricCollection Color V}
    (f : O ⟶ P) (X : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.factorHom (Functor.whiskerRight f F) X ≫
        (factorsIso F P X).inv =
      (factorsIso F O X).inv ≫
        (FiniteFamily.map F).map (ColoredOperadObj.HomData.factorHom f X) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o <;> with_unfolding_all
      exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The substitution-source comparison is natural also in the collection
morphism, not only in the substitution datum. Its direction is from the
tensor of image factors to the image of the original tensor. -/
theorem sourceComparisonHom_collection_naturality
    (p : FiniteTensor.Preserving F)
    {C D : ColoredSymmetricCollection Color V} (α : C ⟶ D)
    (d : ColoredSubstitutionData Color) :
    HomData.sourceHom (Functor.whiskerRight α F) d ≫
        sourceComparisonHom p D d =
      sourceComparisonHom p C d ≫ F.map (HomData.sourceHom α d) := by
  let tV := FiniteTensor.tensor (V := V)
  let tW := FiniteTensor.tensor (V := W)
  let factorV := ColoredOperadObj.HomData.factorHom α d
  let factorW := ColoredOperadObj.HomData.factorHom (Functor.whiskerRight α F) d
  let invO := (factorsIso F C d).inv
  let invP := (factorsIso F D d).inv
  let compO := (comparisonIsoApp p ((substitutionFactors C).obj d)).hom
  let compP := (comparisonIsoApp p ((substitutionFactors D).obj d)).hom
  change tW.map factorW ≫ (tW.map invP ≫ compP) =
    (tW.map invO ≫ compO) ≫ F.map (tV.map factorV)
  have h1 : tW.map factorW ≫ (tW.map invP ≫ compP) =
      (tW.map factorW ≫ tW.map invP) ≫ compP :=
    (Category.assoc _ _ _).symm
  have h2 : tW.map factorW ≫ tW.map invP = tW.map (factorW ≫ invP) :=
    (tW.map_comp _ _).symm
  have h3 : (tW.map factorW ≫ tW.map invP) ≫ compP =
      tW.map (factorW ≫ invP) ≫ compP :=
    congrArg (· ≫ compP) h2
  have h4 : factorW ≫ invP = invO ≫ (FiniteFamily.map F).map factorV :=
    factorHom_whiskerRight_comp_factorsIso_inv α d
  have h5 : tW.map (factorW ≫ invP) = tW.map (invO ≫ (FiniteFamily.map F).map factorV) :=
    congrArg tW.map h4
  have h6 : tW.map (factorW ≫ invP) ≫ compP =
      tW.map (invO ≫ (FiniteFamily.map F).map factorV) ≫ compP :=
    congrArg (· ≫ compP) h5
  have h7 : tW.map (invO ≫ (FiniteFamily.map F).map factorV) =
      tW.map invO ≫ tW.map ((FiniteFamily.map F).map factorV) :=
    tW.map_comp _ _
  have h8 : tW.map (invO ≫ (FiniteFamily.map F).map factorV) ≫ compP =
      (tW.map invO ≫ tW.map ((FiniteFamily.map F).map factorV)) ≫ compP :=
    congrArg (· ≫ compP) h7
  have h9 : (tW.map invO ≫ tW.map ((FiniteFamily.map F).map factorV)) ≫ compP =
      tW.map invO ≫ (tW.map ((FiniteFamily.map F).map factorV) ≫ compP) :=
    Category.assoc _ _ _
  have h10 : tW.map ((FiniteFamily.map F).map factorV) ≫ compP =
      compO ≫ F.map (tV.map factorV) :=
    comparison_naturality p factorV
  have h11 : tW.map invO ≫ (tW.map ((FiniteFamily.map F).map factorV) ≫ compP) =
      tW.map invO ≫ (compO ≫ F.map (tV.map factorV)) :=
    congrArg (tW.map invO ≫ ·) h10
  have h12 : tW.map invO ≫ (compO ≫ F.map (tV.map factorV)) =
      (tW.map invO ≫ compO) ≫ F.map (tV.map factorV) :=
    (Category.assoc _ _ _).symm
  exact h1.trans (h3.trans (h6.trans (h8.trans (h9.trans (h11.trans h12)))))

private theorem mappedUnit_map {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O P : ColoredOperadObj Color V} (f : O ⟶ P)
    (c : Color) :
    mappedUnit p O c ≫
        (Functor.whiskerRight f.toCollectionHom F).app
          (ColoredSubstitutionData.unitProfile c) =
      mappedUnit p P c := by
  let sourceV := (FiniteTensor.tensor (V := V)).obj
    (FiniteFamily.empty : FiniteFamily V)
  let sourceW := (FiniteTensor.tensor (V := W)).obj
    (FiniteFamily.empty : FiniteFamily W)
  let comparison : sourceW ⟶ F.obj sourceV := (unitSourceIso p).hom
  let unitO : sourceV ⟶ O.toCollection.obj
      (ColoredSubstitutionData.unitProfile c) := by
    with_unfolding_all exact O.unit c
  let unitP : sourceV ⟶ P.toCollection.obj
      (ColoredSubstitutionData.unitProfile c) := by
    with_unfolding_all exact P.unit c
  let mapComponent := f.toCollectionHom.app
    (ColoredSubstitutionData.unitProfile c)
  have hUnit : unitO ≫ mapComponent = unitP := by
    with_unfolding_all exact f.map_unit c
  have hMappedO : mappedUnit p O c = comparison ≫ F.map unitO := by
    with_unfolding_all rfl
  have hMappedP : mappedUnit p P c = comparison ≫ F.map unitP := by
    with_unfolding_all rfl
  have hWhisker :
      (Functor.whiskerRight f.toCollectionHom F).app
          (ColoredSubstitutionData.unitProfile c) =
        F.map mapComponent := by
    with_unfolding_all rfl
  have hStart :
      mappedUnit p O c ≫
          (Functor.whiskerRight f.toCollectionHom F).app
            (ColoredSubstitutionData.unitProfile c) =
        (comparison ≫ F.map unitO) ≫ F.map mapComponent := by
    rw [hMappedO, hWhisker]
    exact rfl
  have hAssoc :
      (comparison ≫ F.map unitO) ≫ F.map mapComponent =
        comparison ≫ (F.map unitO ≫ F.map mapComponent) :=
    Category.assoc _ _ _
  have hMap :
      F.map unitO ≫ F.map mapComponent =
        F.map (unitO ≫ mapComponent) :=
    (F.map_comp unitO mapComponent).symm
  have hMapWhiskered :
      comparison ≫ (F.map unitO ≫ F.map mapComponent) =
        comparison ≫ F.map (unitO ≫ mapComponent) :=
    congrArg (comparison ≫ ·) hMap
  have hUnitWhiskered :
      comparison ≫ F.map (unitO ≫ mapComponent) =
        comparison ≫ F.map unitP :=
    congrArg (fun k => comparison ≫ F.map k) hUnit
  exact hStart.trans <| hAssoc.trans <| hMapWhiskered.trans <|
    hUnitWhiskered.trans hMappedP.symm

private theorem mappedSubstitution_map {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O P : ColoredOperadObj Color V} (f : O ⟶ P)
    (X : ColoredSubstitutionData Color) :
    (mappedSubstitution p O).app X ≫
        (Functor.whiskerRight f.toCollectionHom F).app
          X.totalProfile =
      ColoredOperadObj.HomData.sourceHom
          (Functor.whiskerRight f.toCollectionHom F) X ≫
        (mappedSubstitution p P).app X := by
  let srcO := sourceComparisonHom p O.toCollection X
  let srcP := sourceComparisonHom p P.toCollection X
  let sourceV := ColoredOperadObj.HomData.sourceHom f.toCollectionHom X
  let sourceW := ColoredOperadObj.HomData.sourceHom
    (Functor.whiskerRight f.toCollectionHom F) X
  let targetV := f.toCollectionHom.app X.totalProfile
  change
    (srcO ≫ F.map (O.subst.app X)) ≫ F.map targetV =
      sourceW ≫ (srcP ≫ F.map (P.subst.app X))
  have h1 :
      (srcO ≫ F.map (O.subst.app X)) ≫ F.map targetV =
        srcO ≫ (F.map (O.subst.app X) ≫ F.map targetV) :=
    Category.assoc _ _ _
  have hMapO :
      F.map (O.subst.app X) ≫ F.map targetV =
        F.map (O.subst.app X ≫ targetV) :=
    (F.map_comp _ _).symm
  have h2 :
      srcO ≫ (F.map (O.subst.app X) ≫ F.map targetV) =
        srcO ≫ F.map (O.subst.app X ≫ targetV) :=
    congrArg (srcO ≫ ·) hMapO
  have hSubst :
      O.subst.app X ≫ targetV = sourceV ≫ P.subst.app X := by
    exact f.map_subst X
  have hSubstF :
      F.map (O.subst.app X ≫ targetV) =
        F.map (sourceV ≫ P.subst.app X) :=
    congrArg F.map hSubst
  have h3 :
      srcO ≫ F.map (O.subst.app X ≫ targetV) =
        srcO ≫ F.map (sourceV ≫ P.subst.app X) :=
    congrArg (srcO ≫ ·) hSubstF
  have hMapP :
      F.map (sourceV ≫ P.subst.app X) =
        F.map sourceV ≫ F.map (P.subst.app X) :=
    F.map_comp _ _
  have h4 :
      srcO ≫ F.map (sourceV ≫ P.subst.app X) =
        srcO ≫ (F.map sourceV ≫ F.map (P.subst.app X)) :=
    congrArg (srcO ≫ ·) hMapP
  have h5 :
      srcO ≫ (F.map sourceV ≫ F.map (P.subst.app X)) =
        (srcO ≫ F.map sourceV) ≫ F.map (P.subst.app X) :=
    (Category.assoc _ _ _).symm
  have hSource :
      srcO ≫ F.map sourceV = sourceW ≫ srcP := by
    exact (sourceComparisonHom_collection_naturality
      p f.toCollectionHom X).symm
  have h6 :
      (srcO ≫ F.map sourceV) ≫ F.map (P.subst.app X) =
        (sourceW ≫ srcP) ≫ F.map (P.subst.app X) :=
    congrArg (· ≫ F.map (P.subst.app X)) hSource
  have h7 :
      (sourceW ≫ srcP) ≫ F.map (P.subst.app X) =
        sourceW ≫ (srcP ≫ F.map (P.subst.app X)) :=
    Category.assoc _ _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

end MapData

/-- A strong finite-tensor-preserving functor induces a functor on operad objects. -/
noncomputable def mapFunctor {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) : ColoredOperadObj Color V ⥤ ColoredOperadObj Color W where
  obj O :=
    { toCollection := O.toCollection ⋙ F
      unit := MapData.mappedUnit p O
      subst := MapData.mappedSubstitution p O
      right_unit := by exact MapData.mappedRightUnit p O
      left_unit := by exact MapData.mappedLeftUnit p O
      assoc := by exact MapData.mappedAssociative p O }
  map {O P} f :=
    { toCollectionHom := Functor.whiskerRight f.toCollectionHom F
      map_unit := by exact MapData.mappedUnit_map p f
      map_subst := by
        intro X
        exact MapData.mappedSubstitution_map p f X }
  map_id O := by
    apply ColoredOperadObj.Hom.ext
    change Functor.whiskerRight (𝟙 O.toCollection) F =
      𝟙 (O.toCollection ⋙ F)
    exact Functor.whiskerRight_id' F
  map_comp f g := by
    apply ColoredOperadObj.Hom.ext
    change Functor.whiskerRight (f.toCollectionHom ≫ g.toCollectionHom) F =
      Functor.whiskerRight f.toCollectionHom F ≫
        Functor.whiskerRight g.toCollectionHom F
    exact Functor.whiskerRight_comp f.toCollectionHom g.toCollectionHom F

/-- The underlying collection of `(mapFunctor p).obj O` is `O.toCollection ⋙ F`. -/
@[simp]
theorem mapFunctor_obj_toCollection {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    ((mapFunctor p).obj O).toCollection = O.toCollection ⋙ F :=
  rfl

/-- Objectwise formula for the underlying mapped collection. -/
@[simp]
theorem mapFunctor_obj_toCollection_obj {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V)
    (P : ColoredProfile Color) :
    ((mapFunctor p).obj O).toCollection.obj P =
      F.obj (O.toCollection.obj P) :=
  rfl

/-- The unit of `(mapFunctor p).obj O` is the mapped unit `MapData.mappedUnit p O`. -/
@[simp]
theorem mapFunctor_obj_unit {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    ((mapFunctor p).obj O).unit = MapData.mappedUnit p O :=
  rfl

/-- Component formula for a mapped color-indexed unit. -/
@[simp]
theorem mapFunctor_obj_unit_apply {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V)
    (c : Color) :
    ((mapFunctor p).obj O).unit c =
      (MapData.unitSourceIso p).hom ≫ F.map (O.unit c) :=
  rfl

/-- The substitution of `(mapFunctor p).obj O` is the mapped substitution
`MapData.mappedSubstitution p O`. -/
@[simp]
theorem mapFunctor_obj_subst {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V) :
    ((mapFunctor p).obj O).subst = MapData.mappedSubstitution p O :=
  rfl

/-- Component formula for mapped simultaneous substitution. -/
theorem mapFunctor_obj_subst_app {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (O : ColoredOperadObj Color V)
    (X : ColoredSubstitutionData Color) :
    ((mapFunctor p).obj O).subst.app X =
      MapData.sourceComparisonHom p O.toCollection X ≫
        F.map (O.subst.app X) :=
  rfl

/-- The underlying collection morphism of `(mapFunctor p).map f` is
`Functor.whiskerRight f.toCollectionHom F`. -/
@[simp]
theorem mapFunctor_map_toCollectionHom {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O P : ColoredOperadObj Color V} (f : O ⟶ P) :
    ((mapFunctor p).map f).toCollectionHom =
      Functor.whiskerRight f.toCollectionHom F :=
  rfl

/-- Component formula for a mapped operad morphism. -/
@[simp]
theorem mapFunctor_map_toCollectionHom_app {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) {O P : ColoredOperadObj Color V}
    (f : O ⟶ P) (X : ColoredProfile Color) :
    ((mapFunctor p).map f).toCollectionHom.app X =
      F.map (f.toCollectionHom.app X) :=
  rfl

end CategoryTheory.Operad.ColoredOperadObj
