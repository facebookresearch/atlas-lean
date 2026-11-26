/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Square

/-!
# Composition and cube coherence of left-derived square maps

Two underlying comparison squares between additive functors compose
using their source and target functor identifications. If the source
and target changes preserve homology and the source categories admit
projective resolutions, their canonical derived square maps compose
to the derived map of that underlying composite. Equality of two
underlying pasted cube faces likewise gives equality of the derived
pasted faces, without projective-preservation hypotheses on the
source changes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uD' vD' uE vE uE' vE' uE'' vE''

namespace CategoryTheory.Functor


variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {D' : Type uD'} [Category.{vD'} D'] [Abelian D']
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {E' : Type uE'} [Category.{vE'} E'] [Abelian E']
  {E'' : Type uE''} [Category.{vE''} E''] [Abelian E'']
  (U : D ⥤ C) [U.Additive] (U' : D' ⥤ D) [U'.Additive]
  (U₀ : D' ⥤ C) [U₀.Additive] (eU : U' ⋙ U ≅ U₀)
  (V : E' ⥤ E) [V.Additive] (V' : E'' ⥤ E') [V'.Additive]
  (V₀ : E'' ⥤ E) [V₀.Additive] (eV : V' ⋙ V ≅ V₀)
  (F : C ⥤ E) [F.Additive] (G : D ⥤ E') [G.Additive]
  (H : D' ⥤ E'') [H.Additive]
  (α : U ⋙ F ⟶ G ⋙ V) (β : U' ⋙ G ⟶ H ⋙ V')

/-- Let `C,D,D′,E,E′,E″` be abelian. Let `U : D → C`, `U′ : D′ → D`, `U₀ : D′ → C`,
`V : E′ → E`, `V′ : E″ → E′`, `V₀ : E″ → E` be additive, with `e_U : U′ ⋙ U ≅ U₀`, `e_V : V′ ⋙ V ≅ V₀`.
Let `F : C → E`, `G : D → E′`, `H : D′ → E″` be additive, with
`α : U ⋙ F → G ⋙ V`, `β : U′ ⋙ G → H ⋙ V′`. Their composite square is the natural transformation
`U₀ ⋙ F → H ⋙ V₀`, obtained by inverse source identification,
`α`, the mapped `β`, and the forward target identification. -/
def composeLeftDerivedSquare : U₀ ⋙ F ⟶ H ⋙ V₀ :=
  whiskerRight eU.inv F ≫ (Functor.associator U' U F).hom ≫ whiskerLeft U' α ≫
    (Functor.associator U' G V).inv ≫ whiskerRight β V ≫
    (Functor.associator H V' V).hom ≫ whiskerLeft H eV.hom

omit [Abelian C] [Abelian D] [Abelian D'] [Abelian E] [Abelian E'] [Abelian E'']
  [U.Additive] [U'.Additive] [U₀.Additive] [V.Additive] [V'.Additive] [V₀.Additive]
    [F.Additive] [G.Additive] [H.Additive] in
/-- Let `C,D,D′,E,E′,E″` be abelian. Let `U : D → C`, `U′ : D′ → D`, `U₀ : D′ → C`,
`V : E′ → E`, `V′ : E″ → E′`, `V₀ : E″ → E` be additive, with `e_U : U′ ⋙ U ≅ U₀`, `e_V : V′ ⋙ V ≅ V₀`.
Let `F : C → E`, `G : D → E′`, `H : D′ → E″` be additive, with
`α : U ⋙ F → G ⋙ V`, `β : U′ ⋙ G → H ⋙ V′`. At `Z : D′`, the composite square has component
`F(e_U,Z⁻¹) ≫ α_(U′Z) ≫ V(β_Z) ≫ e_V,H(Z)`. -/
theorem composeLeftDerivedSquare_app (Z : D') :
    (composeLeftDerivedSquare U U' U₀ eU V V' V₀ eV F G H α β).app Z =
      F.map (eU.inv.app Z) ≫ α.app (U'.obj Z) ≫ V.map (β.app Z) ≫ eV.hom.app (H.obj Z) := by
  change F.map (eU.inv.app Z) ≫ (𝟙 _) ≫ α.app (U'.obj Z) ≫ (𝟙 _) ≫
    V.map (β.app Z) ≫ (𝟙 _) ≫ eV.hom.app (H.obj Z) = _
  simp only [Category.id_comp]

omit [Abelian C] [Abelian D] [Abelian D'] [Abelian E] [Abelian E'] [Abelian E'']
  [U.Additive] [U'.Additive] [U₀.Additive] [V.Additive] [V'.Additive] [V₀.Additive]
    [F.Additive] [G.Additive] [H.Additive] in
/-- Let `C,D,D′,E,E′,E″` be abelian. Let `U : D → C`, `U′ : D′ → D`, `U₀ : D′ → C`,
`V : E′ → E`, `V′ : E″ → E′`, `V₀ : E″ → E` be additive, with `e_U : U′ ⋙ U ≅ U₀`, `e_V : V′ ⋙ V ≅ V₀`.
Let `F : C → E`, `G : D → E′`, `H : D′ → E″` be additive, with
`α : U ⋙ F → G ⋙ V`, `β : U′ ⋙ G → H ⋙ V′`. The paste `α_(U′Z) ≫ V(β_Z) ≫ e_V,H(Z)` equals
`F(e_U,Z)` followed by the composite square component at `Z`. -/
theorem composeLeftDerivedSquare_forward (Z : D') :
    α.app (U'.obj Z) ≫ V.map (β.app Z) ≫ eV.hom.app (H.obj Z) =
      F.map (eU.hom.app Z) ≫
        (composeLeftDerivedSquare U U' U₀ eU V V' V₀ eV F G H α β).app Z := by
  rw [composeLeftDerivedSquare_app]
  rw [← Category.assoc (F.map (eU.hom.app Z)), ← F.map_comp]
  have hId : eU.hom.app Z ≫ eU.inv.app Z = 𝟙 _ := Iso.hom_inv_id_app eU Z
  exact ((congrArg (fun z => F.map z ≫ α.app (U'.obj Z) ≫
    V.map (β.app Z) ≫ eV.hom.app (H.obj Z)) hId).trans
    ((congrArg (fun z => z ≫ α.app (U'.obj Z) ≫ V.map (β.app Z) ≫
      eV.hom.app (H.obj Z)) (F.map_id _)).trans (Category.id_comp _))).symm

section Derived

variable [HasProjectiveResolutions C] [HasProjectiveResolutions D] [HasProjectiveResolutions D']
  [U.PreservesHomology] [U'.PreservesHomology] [U₀.PreservesHomology]
  [V.PreservesHomology] [V'.PreservesHomology] [V₀.PreservesHomology]

/-- Let `C,D,D′,E,E′,E″` be abelian, with projective resolutions
in `C,D,D′`. Let `U : D → C`, `U′ : D′ → D`, `U₀ : D′ → C`,
`V : E′ → E`, `V′ : E″ → E′`, `V₀ : E″ → E` be additive and
preserve homology, with `e_U : U′ ⋙ U ≅ U₀`, `e_V : V′ ⋙ V ≅ V₀`.
Let `F : C → E`, `G : D → E′`, `H : D′ → E″` be additive, with
`α : U ⋙ F → G ⋙ V`, `β : U′ ⋙ G → H ⋙ V′`. For input maps `f : X → U(Y)`, `f′ : Y → U′(Z)`, the
derived square for `α` followed by the mapped derived square for `β`
and `e_V` equals the derived square of their composite after
`L_nF(f ≫ U(f′) ≫ e_U,Z)`. -/
theorem leftDerivedSquareHom_comp_with_input
    {X : C} {Y : D} {Z : D'} (f : X ⟶ U.obj Y) (f' : Y ⟶ U'.obj Z) (n : ℕ) :
    ((F.leftDerived n).map f ≫ (leftDerivedSquareHom U V F G α n).app Y) ≫
        V.map ((G.leftDerived n).map f' ≫ (leftDerivedSquareHom U' V' G H β n).app Z) ≫
        eV.hom.app ((H.leftDerived n).obj Z) =
      (F.leftDerived n).map (f ≫ U.map f' ≫ eU.hom.app Z) ≫
        (leftDerivedSquareHom U₀ V₀ F H
          (composeLeftDerivedSquare U U' U₀ eU V V' V₀ eV F G H α β) n).app Z := by
  let P := projectiveResolution X
  let Q := projectiveResolution Y
  let T := projectiveResolution Z
  let ρQ := mapChainAugmentation U Q.π
  let ρT := mapChainAugmentation U' T.π
  let ρ₀ := mapChainAugmentation U₀ T.π
  let : QuasiIso ρQ := mapChainAugmentation_quasiIso U Q.π
  let : QuasiIso ρT := mapChainAugmentation_quasiIso U' T.π
  let : QuasiIso ρ₀ := mapChainAugmentation_quasiIso U₀ T.π
  let a := (P.comparisonToAugmentedExact
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ f).val
  let b := (Q.comparisonToAugmentedExact
    ((U'.mapHomologicalComplex (ComplexShape.down ℕ)).obj T.complex) ρT f').val
  let c : P.complex ⟶ (U₀.mapHomologicalComplex (ComplexShape.down ℕ)).obj T.complex :=
    a ≫ (U.mapHomologicalComplex (ComplexShape.down ℕ)).map b ≫
      (Functor.mapHomologicalComplexCompIso (F := U') (G := U) eU
        (ComplexShape.down ℕ)).hom.app T.complex
  have ha : a ≫ ρQ = P.π ≫ (ChainComplex.single₀ C).map f :=
    (P.comparisonToAugmentedExact
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ f).property
  have hb : b ≫ ρT = Q.π ≫ (ChainComplex.single₀ D).map f' :=
    (Q.comparisonToAugmentedExact
      ((U'.mapHomologicalComplex (ComplexShape.down ℕ)).obj T.complex) ρT f').property
  have ha₀ : a.f 0 ≫ U.map (Q.π.f 0) = P.π.f 0 ≫ f := by
    have h₀ : @Eq (P.complex.X 0 ⟶ U.obj Y)
        ((a ≫ ρQ).f 0) ((P.π ≫ (ChainComplex.single₀ C).map f).f 0) :=
      HomologicalComplex.congr_hom ha 0
    have hL : @Eq (P.complex.X 0 ⟶ U.obj Y)
        ((a ≫ ρQ).f 0) (a.f 0 ≫ U.map (Q.π.f 0)) :=
      (HomologicalComplex.comp_f a ρQ 0).trans
        (congrArg (fun z => a.f 0 ≫ z) (mapChainAugmentation_f_zero U Q.π))
    have hR : @Eq (P.complex.X 0 ⟶ U.obj Y)
        ((P.π ≫ (ChainComplex.single₀ C).map f).f 0) (P.π.f 0 ≫ f) :=
      (HomologicalComplex.comp_f P.π ((ChainComplex.single₀ C).map f) 0).trans
        (congrArg (fun z => P.π.f 0 ≫ z) (ChainComplex.single₀_map_f_zero f))
    exact hL.symm.trans (h₀.trans hR)
  have hb₀ : b.f 0 ≫ U'.map (T.π.f 0) = Q.π.f 0 ≫ f' := by
    have h₀ : @Eq (Q.complex.X 0 ⟶ U'.obj Z)
        ((b ≫ ρT).f 0) ((Q.π ≫ (ChainComplex.single₀ D).map f').f 0) :=
      HomologicalComplex.congr_hom hb 0
    have hL : @Eq (Q.complex.X 0 ⟶ U'.obj Z)
        ((b ≫ ρT).f 0) (b.f 0 ≫ U'.map (T.π.f 0)) :=
      (HomologicalComplex.comp_f b ρT 0).trans
        (congrArg (fun z => b.f 0 ≫ z) (mapChainAugmentation_f_zero U' T.π))
    have hR : @Eq (Q.complex.X 0 ⟶ U'.obj Z)
        ((Q.π ≫ (ChainComplex.single₀ D).map f').f 0) (Q.π.f 0 ≫ f') :=
      (HomologicalComplex.comp_f Q.π ((ChainComplex.single₀ D).map f') 0).trans
        (congrArg (fun z => Q.π.f 0 ≫ z) (ChainComplex.single₀_map_f_zero f'))
    exact hL.symm.trans (h₀.trans hR)
  let p₀ : P.complex.X 0 ⟶ X := P.π.f 0
  let q₀ : Q.complex.X 0 ⟶ Y := Q.π.f 0
  let t₀ : T.complex.X 0 ⟶ Z := T.π.f 0
  let a₀ : P.complex.X 0 ⟶ U.obj (Q.complex.X 0) := a.f 0
  let b₀ : Q.complex.X 0 ⟶ U'.obj (T.complex.X 0) := b.f 0
  have ha₀' : a₀ ≫ U.map q₀ = p₀ ≫ f := ha₀
  have hb₀' : b₀ ≫ U'.map t₀ = q₀ ≫ f' := hb₀
  have hN : @Eq (U.obj (U'.obj (T.complex.X 0)) ⟶ U₀.obj Z)
      (eU.hom.app (T.complex.X 0) ≫ U₀.map t₀)
      (U.map (U'.map t₀) ≫ eU.hom.app Z) :=
    (eU.hom.naturality t₀).symm
  have hc₀ : @Eq (P.complex.X 0 ⟶ U₀.obj Z)
      (c.f 0 ≫ U₀.map (T.π.f 0)) (P.π.f 0 ≫ (f ≫ U.map f' ≫ eU.hom.app Z)) := by
    dsimp only [c]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex_app_f, Category.assoc]
    change a₀ ≫ U.map b₀ ≫ eU.hom.app (T.complex.X 0) ≫ U₀.map t₀ =
      p₀ ≫ f ≫ U.map f' ≫ eU.hom.app Z
    calc
      _ = a₀ ≫ U.map b₀ ≫ U.map (U'.map t₀) ≫ eU.hom.app Z :=
        congrArg (fun z => a₀ ≫ U.map b₀ ≫ z) hN
      _ = a₀ ≫ U.map (b₀ ≫ U'.map t₀) ≫ eU.hom.app Z :=
        congrArg (fun z => a₀ ≫ z)
          ((Category.assoc (U.map b₀) (U.map (U'.map t₀)) (eU.hom.app Z)).symm.trans
            (congrArg (fun z => z ≫ eU.hom.app Z) (U.map_comp b₀ (U'.map t₀)).symm))
      _ = a₀ ≫ U.map (q₀ ≫ f') ≫ eU.hom.app Z :=
        congrArg (fun z => a₀ ≫ U.map z ≫ eU.hom.app Z) hb₀'
      _ = (a₀ ≫ U.map q₀) ≫ U.map f' ≫ eU.hom.app Z :=
        (congrArg (fun z => a₀ ≫ z ≫ eU.hom.app Z) (U.map_comp q₀ f')).trans
          ((congrArg (fun z => a₀ ≫ z)
            (Category.assoc (U.map q₀) (U.map f') (eU.hom.app Z))).trans
            (Category.assoc a₀ (U.map q₀) (U.map f' ≫ eU.hom.app Z)).symm)
      _ = (p₀ ≫ f) ≫ U.map f' ≫ eU.hom.app Z :=
        congrArg (fun z => z ≫ U.map f' ≫ eU.hom.app Z) ha₀'
      _ = _ := Category.assoc p₀ f (U.map f' ≫ eU.hom.app Z)
  have hc : c ≫ ρ₀ = P.π ≫ (ChainComplex.single₀ C).map (f ≫ U.map f' ≫ eU.hom.app Z) := by
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | zero =>
      have hL : @Eq (P.complex.X 0 ⟶ U₀.obj Z)
          ((c ≫ ρ₀).f 0) (c.f 0 ≫ U₀.map (T.π.f 0)) :=
        (HomologicalComplex.comp_f c ρ₀ 0).trans
          (congrArg (fun z => c.f 0 ≫ z) (mapChainAugmentation_f_zero U₀ T.π))
      have hR : @Eq (P.complex.X 0 ⟶ U₀.obj Z)
          ((P.π ≫ (ChainComplex.single₀ C).map (f ≫ U.map f' ≫ eU.hom.app Z)).f 0)
          (P.π.f 0 ≫ (f ≫ U.map f' ≫ eU.hom.app Z)) :=
        (HomologicalComplex.comp_f P.π
          ((ChainComplex.single₀ C).map (f ≫ U.map f' ≫ eU.hom.app Z)) 0).trans
          (congrArg (fun z => P.π.f 0 ≫ z)
            (ChainComplex.single₀_map_f_zero (f ≫ U.map f' ≫ eU.hom.app Z)))
      exact hL.trans (hc₀.trans hR.symm)
    | succ i =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (U₀.obj Z)
        (i + 1) (by omega)).eq_of_tgt _ _
  let d := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map a ≫
    (mapSquareHomologicalComplex U V F G α).app Q.complex
  let d' := (G.mapHomologicalComplex (ComplexShape.down ℕ)).map b ≫
    (mapSquareHomologicalComplex U' V' G H β).app T.complex
  let α₀ := composeLeftDerivedSquare U U' U₀ eU V V' V₀ eV F G H α β
  let d₀ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map c ≫
    (mapSquareHomologicalComplex U₀ V₀ F H α₀).app T.complex
  have hd : d ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map d' ≫
      (Functor.mapHomologicalComplexCompIso (F := V') (G := V) eV
        (ComplexShape.down ℕ)).hom.app
          ((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj T.complex) = d₀ := by
    apply HomologicalComplex.hom_ext
    intro i
    dsimp only [d, d', d₀, c]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mapSquareHomologicalComplex_f, Functor.mapHomologicalComplexCompIso,
      NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f]
    change (F.map (a.f i) ≫ α.app (Q.complex.X i)) ≫
      V.map (G.map (b.f i) ≫ β.app (T.complex.X i)) ≫
      eV.hom.app (H.obj (T.complex.X i)) =
      F.map (a.f i ≫ U.map (b.f i) ≫ eU.hom.app (T.complex.X i)) ≫ α₀.app (T.complex.X i)
    simp only [Functor.map_comp, Category.assoc]
    have hα : α.app (Q.complex.X i) ≫ V.map (G.map (b.f i)) =
        F.map (U.map (b.f i)) ≫ α.app (U'.obj (T.complex.X i)) := by
      simpa only [Functor.comp_map, Functor.mapHomologicalComplex_obj_X] using
        (α.naturality (b.f i)).symm
    rw [← Category.assoc (α.app (Q.complex.X i)), hα]
    simp only [Category.assoc]
    rw [composeLeftDerivedSquare_forward U U' U₀ eU V V' V₀ eV F G H α β]
  rw [leftDerivedSquareHom_eq_with_source_lift U V F G α n f P Q a ha,
    leftDerivedSquareHom_eq_with_source_lift U' V' G H β n f' Q T b hb,
    leftDerivedSquareHom_eq_with_source_lift U₀ V₀ F H α₀ n
      (f ≫ U.map f' ≫ eU.hom.app Z) P T c hc]
  have hComp := HomologicalComplex.comparisonHom_comp V V' V₀ eV n
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
    ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
    ((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj T.complex) d d'
    (P.isoLeftDerivedObj F n) (Q.isoLeftDerivedObj G n) (T.isoLeftDerivedObj H n)
  rw [hd] at hComp
  exact hComp

end Derived

end CategoryTheory.Functor

universe uC₀ vC₀ uC₁ vC₁ uD₀ vD₀ uD₁ vD₁ uE₀ vE₀ uE₁ vE₁ uE'₀ vE'₀ uE'₁ vE'₁

namespace CategoryTheory.Functor

section Cube

variable {C₀ : Type uC₀} [Category.{vC₀} C₀] [Abelian C₀] [HasProjectiveResolutions C₀]
  {C₁ : Type uC₁} [Category.{vC₁} C₁] [Abelian C₁] [HasProjectiveResolutions C₁]
  {D₀ : Type uD₀} [Category.{vD₀} D₀] [Abelian D₀] [HasProjectiveResolutions D₀]
  {D₁ : Type uD₁} [Category.{vD₁} D₁] [Abelian D₁] [HasProjectiveResolutions D₁]
  {E₀ : Type uE₀} [Category.{vE₀} E₀] [Abelian E₀]
  {E₁ : Type uE₁} [Category.{vE₁} E₁] [Abelian E₁]
  {E'₀ : Type uE'₀} [Category.{vE'₀} E'₀] [Abelian E'₀]
  {E'₁ : Type uE'₁} [Category.{vE'₁} E'₁] [Abelian E'₁]
  (I : C₀ ⥤ C₁) [I.Additive] [I.PreservesHomology]
  (J : D₀ ⥤ D₁) [J.Additive] [J.PreservesHomology]
  (K : E₀ ⥤ E₁) [K.Additive] [K.PreservesHomology]
  (L : E'₀ ⥤ E'₁) [L.Additive] [L.PreservesHomology]
  (U₀ : D₀ ⥤ C₀) [U₀.Additive] [U₀.PreservesHomology]
  (U₁ : D₁ ⥤ C₁) [U₁.Additive] [U₁.PreservesHomology]
  (V₀ : E'₀ ⥤ E₀) [V₀.Additive] [V₀.PreservesHomology]
  (V₁ : E'₁ ⥤ E₁) [V₁.Additive] [V₁.PreservesHomology]
  (eU : U₀ ⋙ I ≅ J ⋙ U₁) (eV : V₀ ⋙ K ≅ L ⋙ V₁)
  (F₀ : C₀ ⥤ E₀) [F₀.Additive] (F₁ : C₁ ⥤ E₁) [F₁.Additive]
  (G₀ : D₀ ⥤ E'₀) [G₀.Additive] (G₁ : D₁ ⥤ E'₁) [G₁.Additive]
  (eF : I ⋙ F₁ ≅ F₀ ⋙ K) (eG : J ⋙ G₁ ≅ G₀ ⋙ L)
  (α₀ : U₀ ⋙ F₀ ⟶ G₀ ⋙ V₀) (α₁ : U₁ ⋙ F₁ ⟶ G₁ ⋙ V₁)

/-- Let `C_i,D_i,E_i,E′_i` for `i=0,1` be abelian, with projective
resolutions in `C_i,D_i`. Let `I : C₀ → C₁`, `J : D₀ → D₁`,
`K : E₀ → E₁`, `L : E′₀ → E′₁`, `U_i : D_i → C_i`, and
`V_i : E′_i → E_i` be additive and preserve homology. Let
`F_i : C_i → E_i`, `G_i : D_i → E′_i` be additive, with isomorphisms
`U₀ ⋙ I ≅ J ⋙ U₁`, `V₀ ⋙ K ≅ L ⋙ V₁`,
`I ⋙ F₁ ≅ F₀ ⋙ K`, `J ⋙ G₁ ≅ G₀ ⋙ L`, and square maps
`α_i : U_i ⋙ F_i → G_i ⋙ V_i`. If the two pasted underlying faces
agree, their derived routes from `L_nF₁(I(U₀(Y)))` to
`K(V₀(L_nG₀(Y)))` agree for every `n` and `Y : D₀`. -/
theorem leftDerivedSquareHom_cube_inverse
    (hCube :
      composeLeftDerivedSquare I U₀ (U₀ ⋙ I) (Iso.refl _) K V₀ (V₀ ⋙ K) (Iso.refl _)
          F₁ F₀ G₀ eF.hom α₀ =
        composeLeftDerivedSquare U₁ J (U₀ ⋙ I) eU.symm V₁ L (V₀ ⋙ K) eV.symm
          F₁ G₁ G₀ α₁ eG.hom)
    (n : ℕ) (Y : D₀) :
    (F₁.leftDerived n).map (eU.hom.app Y) ≫
        (leftDerivedSquareHom U₁ V₁ F₁ G₁ α₁ n).app (J.obj Y) ≫
        V₁.map ((leftDerivedSquareHom J L G₁ G₀ eG.hom n).app Y) ≫
        eV.inv.app ((G₀.leftDerived n).obj Y) =
      (leftDerivedSquareHom I K F₁ F₀ eF.hom n).app (U₀.obj Y) ≫
        K.map ((leftDerivedSquareHom U₀ V₀ F₀ G₀ α₀ n).app Y) := by
  let : (U₀ ⋙ I).PreservesHomology := by
    let : PreservesFiniteLimits U₀ := preservesFiniteLimits_of_preservesHomology U₀
    let : PreservesFiniteColimits U₀ := preservesFiniteColimits_of_preservesHomology U₀
    let : PreservesFiniteLimits I := preservesFiniteLimits_of_preservesHomology I
    let : PreservesFiniteColimits I := preservesFiniteColimits_of_preservesHomology I
    exact preservesHomologyOfExact (U₀ ⋙ I)
  let : (V₀ ⋙ K).PreservesHomology := by
    let : PreservesFiniteLimits V₀ := preservesFiniteLimits_of_preservesHomology V₀
    let : PreservesFiniteColimits V₀ := preservesFiniteColimits_of_preservesHomology V₀
    let : PreservesFiniteLimits K := preservesFiniteLimits_of_preservesHomology K
    let : PreservesFiniteColimits K := preservesFiniteColimits_of_preservesHomology K
    exact preservesHomologyOfExact (V₀ ⋙ K)
  have hLeft := leftDerivedSquareHom_comp_with_input
    I U₀ (U₀ ⋙ I) (Iso.refl _) K V₀ (V₀ ⋙ K) (Iso.refl _)
    F₁ F₀ G₀ eF.hom α₀ (𝟙 (I.obj (U₀.obj Y))) (𝟙 (U₀.obj Y)) n
  have hRight := leftDerivedSquareHom_comp_with_input
    U₁ J (U₀ ⋙ I) eU.symm V₁ L (V₀ ⋙ K) eV.symm
    F₁ G₁ G₀ α₁ eG.hom (eU.hom.app Y) (𝟙 (J.obj Y)) n
  simp only [Functor.map_id, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Iso.symm_hom,
    Iso.hom_inv_id_app, Category.assoc] at hLeft hRight
  rw [hCube] at hLeft
  let Cmp := (leftDerivedSquareHom (U₀ ⋙ I) (V₀ ⋙ K) F₁ G₀
    (composeLeftDerivedSquare U₁ J (U₀ ⋙ I) eU.symm V₁ L (V₀ ⋙ K) eV.symm
      F₁ G₁ G₀ α₁ eG.hom) n).app Y
  let A := (leftDerivedSquareHom I K F₁ F₀ eF.hom n).app (U₀.obj Y)
  let B := K.map ((leftDerivedSquareHom U₀ V₀ F₀ G₀ α₀ n).app Y)
  have hTail : A ≫ B ≫ 𝟙 _ = A ≫ B := congrArg (fun z => A ≫ z) (Category.comp_id B)
  have hFront : (F₁.leftDerived n).map (𝟙 ((U₀ ⋙ I).obj Y)) ≫ Cmp = Cmp :=
    (congrArg (fun z => z ≫ Cmp)
      ((F₁.leftDerived n).map_id ((U₀ ⋙ I).obj Y))).trans (Category.id_comp Cmp)
  have hClean : A ≫ B = Cmp := hTail.symm.trans (hLeft.trans hFront)
  exact hRight.trans hClean.symm

end Cube

end CategoryTheory.Functor
