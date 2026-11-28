/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Order.WithBotTop
public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralObject
public import MathlibExt.Algebra.Homology.MappingConeCokernelConnecting

/-!
# Complete horizontal filtration and its mapping-cone spectral object

Let C be a preadditive category with a zero object and finite coproducts, and K a bicomplex of
shape (down ℕ,down ℕ). Its total complex T has an increasing horizontal filtration G_a for a∈ℕ.
Extend the index to ℤ∪{⊥,⊤} by G_⊥=0, G_a=0 for finite a<0, G_a the horizontal stage for finite
a≥0, and G_⊤=T. Each G_i→T is monic, and the transition G_i→G_j for i≤j commutes with these
inclusions. For finite a≥0, the inclusion is an isomorphism on terms in degrees n≤a.

Place chain degree n in cochain degree -n and extend by zero to obtain a complete cochain
filtration F. The relative object for i≤j is Cone(F_i→F_j) in the homotopy category. Cone
composition triangles supply a triangulated spectral object. When C is abelian, cochain homology
gives the abelian spectral object, with connecting maps
H^n(Cone(F_j→F_k))→H^{n+1}(Cone(F_i→F_j)) for n+1=n′. Object and morphism universes remain
arbitrary.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows Pretriangulated

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Let C be preadditive with a zero object and finite coproducts, and K a bicomplex of shape (down
ℕ,down ℕ). The zero chain complex with its unique map 0→Tot K is a monic subcomplex of Tot K.
This object over Tot K is the bottom stage and every negative finite stage of the complete
horizontal filtration. -/
noncomputable def horizontalCompleteFilteredTotalZeroMonoOver :
    MonoOver (K.total (ComplexShape.down ℕ)) :=
  MonoOver.mk
    (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
      K.total (ComplexShape.down ℕ))
    (hf := { right_cancellation := fun g h _ =>
      HomologicalComplex.isZero_zero.eq_of_tgt g h })

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts, this is the monic subcomplex G_i→Tot K at i∈ℤ∪{⊥,⊤}. It is 0→Tot K for i=⊥ or finite
i<0, the horizontal filtration subcomplex G_a→Tot K for finite i=a≥0, and the identity Tot K→Tot
K for i=⊤. -/
noncomputable def horizontalCompleteFilteredTotalMonoOver (i : EInt) :
    MonoOver (K.total (ComplexShape.down ℕ)) :=
  WithBotTop.rec
    (horizontalCompleteFilteredTotalZeroMonoOver K)
    (fun a => if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K)
    (MonoOver.mk (𝟙 (K.total (ComplexShape.down ℕ)))) i

/-- Let C be preadditive with a zero object and finite coproducts, and K a bicomplex of shape (down
ℕ,down ℕ). At i∈ℤ∪{⊥,⊤}, G_i is the underlying chain complex of the complete horizontal
subcomplex of Tot K. Bottom and negative finite cuts give the zero complex; a finite a≥0 gives
the ath horizontal stage; the top cut gives Tot K. -/
abbrev horizontalCompleteFilteredTotalComplex (i : EInt) :
    ChainComplex C ℕ :=
  (horizontalCompleteFilteredTotalMonoOver K i).obj.left

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts and i∈ℤ∪{⊥,⊤}, this is the monic chain map ι_i:G_i→Tot K of the complete horizontal
filtration. It is zero at bottom and negative finite cuts, the horizontal-stage inclusion at
finite a≥0, and the identity at top. -/
abbrev horizontalCompleteFilteredTotalToTotal (i : EInt) :
    horizontalCompleteFilteredTotalComplex K i ⟶
      K.total (ComplexShape.down ℕ) :=
  (horizontalCompleteFilteredTotalMonoOver K i).arrow

/-- Let K be a bicomplex of shape (down ℕ,down ℕ) in a preadditive category with a zero object and
finite coproducts. For i≤j in ℤ∪{⊥,⊤}, this is the morphism from the monic subcomplex G_i→Tot K
to G_j→Tot K. Its underlying chain map t_{i,j}:G_i→G_j satisfies t_{i,j}≫ι_j=ι_i. Between
nonnegative finite cuts it is the horizontal-stage transition, from a zero stage it is zero, and
into top it is the inclusion. -/
noncomputable def horizontalCompleteFilteredTotalMonoOverMap
    {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalMonoOver K i ⟶
      horizontalCompleteFilteredTotalMonoOver K j := by
  induction i using WithBotTop.rec with
  | bot =>
      change horizontalCompleteFilteredTotalZeroMonoOver K ⟶ _
      refine MonoOver.homMk 0 ?_
      simp [horizontalCompleteFilteredTotalZeroMonoOver]
  | coe a =>
      induction j using WithBotTop.rec with
      | bot => simp at h
      | coe b =>
          have hab : a ≤ b := by simpa using h
          by_cases ha : 0 ≤ a
          · have hb : 0 ≤ b := ha.trans hab
            change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                (if 0 ≤ b then
                  (horizontalTotalFiltration K).toMonoOver.obj b.toNat
                else horizontalCompleteFilteredTotalZeroMonoOver K)
            rw [ite_eq_left ha, ite_eq_left hb]
            exact MonoOver.homMk
              (horizontalFilteredTotalComplexMap K
                (Int.toNat_le_toNat hab))
              (horizontalFilteredTotalComplexMap_toTotal K
                (Int.toNat_le_toNat hab))
          · change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                (if 0 ≤ b then
                  (horizontalTotalFiltration K).toMonoOver.obj b.toNat
                else horizontalCompleteFilteredTotalZeroMonoOver K)
            rw [ite_eq_right ha]
            refine MonoOver.homMk 0 ?_
            simp [horizontalCompleteFilteredTotalZeroMonoOver]
      | top =>
          by_cases ha : 0 ≤ a
          · change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                MonoOver.mk (𝟙 (K.total (ComplexShape.down ℕ)))
            rw [ite_eq_left ha]
            refine MonoOver.homMk
              (horizontalFilteredTotalComplexToTotal K a.toNat) ?_
            change horizontalFilteredTotalComplexToTotal K a.toNat ≫
                𝟙 _ = horizontalFilteredTotalComplexToTotal K a.toNat
            simp
          · change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                MonoOver.mk (𝟙 (K.total (ComplexShape.down ℕ)))
            rw [ite_eq_right ha]
            refine MonoOver.homMk 0 ?_
            simp [horizontalCompleteFilteredTotalZeroMonoOver]
  | top =>
      have hj : j = ⊤ := top_le_iff.mp h
      subst j
      exact 𝟙 _

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts and i≤j in ℤ∪{⊥,⊤}, this is the chain map t_{i,j}:G_i→G_j underlying the morphism of
complete horizontal subcomplexes. The map commutes with the total inclusions, t_{i,j}≫ι_j=ι_i,
and agrees with the finite horizontal transition when both cuts are nonnegative integers. -/
noncomputable def horizontalCompleteFilteredTotalMap
    {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex K j :=
  (horizontalCompleteFilteredTotalMonoOverMap K h).hom.left

@[reassoc]
theorem horizontalCompleteFilteredTotalMap_toTotal
    {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalMap K h ≫
        horizontalCompleteFilteredTotalToTotal K j =
      horizontalCompleteFilteredTotalToTotal K i :=
  MonoOver.w (horizontalCompleteFilteredTotalMonoOverMap K h)

/-- Let C be preadditive with a zero object and finite coproducts and K a bicomplex of shape (down
ℕ,down ℕ). The monic subcomplexes G_i→Tot K and their canonical transitions for i≤j define an
increasing filtration of Tot K indexed by ℤ∪{⊥,⊤}. The bottom and every negative finite stage
are zero, the nonnegative finite stages are the horizontal filtration stages, and the top stage
is Tot K. -/
noncomputable def horizontalCompleteTotalFiltration :
    CategoryTheory.Filtration (K.total (ComplexShape.down ℕ)) EInt where
  toMonoOver :=
    { obj := horizontalCompleteFilteredTotalMonoOver K
      map := fun {i j} f =>
        horizontalCompleteFilteredTotalMonoOverMap K (leOfHom f)
      map_id := by
        intro i
        apply Subsingleton.elim
      map_comp := by
        intro i j k f g
        apply Subsingleton.elim }

@[simp]
theorem horizontalCompleteFilteredTotalComplex_bot :
    horizontalCompleteFilteredTotalComplex K ⊥ =
      (HomologicalComplex.zero : ChainComplex C ℕ) :=
  rfl

@[simp]
theorem horizontalCompleteFilteredTotalComplex_top :
    horizontalCompleteFilteredTotalComplex K ⊤ =
      K.total (ComplexShape.down ℕ) :=
  rfl

theorem horizontalCompleteFilteredTotalComplex_coe_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) =
      horizontalFilteredTotalComplex K a.toNat := by
  change (if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K).obj.left = _
  rw [ite_eq_left ha]
  exact horizontalTotalFiltration_diagram_obj K a.toNat

theorem horizontalCompleteFilteredTotalComplex_coe_of_neg
    (a : ℤ) (ha : a < 0) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) =
      (HomologicalComplex.zero : ChainComplex C ℕ) := by
  have hna : ¬0 ≤ a := by omega
  change (if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K).obj.left = _
  rw [ite_eq_right hna]
  rfl

@[simp]
theorem horizontalCompleteFilteredTotalToTotal_top :
    horizontalCompleteFilteredTotalToTotal K ⊤ = 𝟙 _ :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltration_diagram_obj (i : EInt) :
    (horizontalCompleteTotalFiltration K).diagram.obj i =
      horizontalCompleteFilteredTotalComplex K i :=
  rfl

/-- The underlying chain complex of an extended-integer horizontal filtration subobject is its
complete horizontal stage. -/
@[simp]
theorem horizontalCompleteTotalFiltration_toMonoOver_obj_left (i : EInt) :
    ((horizontalCompleteTotalFiltration K).toMonoOver.obj i).obj.left =
      horizontalCompleteFilteredTotalComplex K i := by
  change (horizontalCompleteTotalFiltration K).diagram.obj i = _
  exact horizontalCompleteTotalFiltration_diagram_obj K i

theorem horizontalCompleteTotalFiltration_diagram_map
    {i j : EInt} (h : i ≤ j) :
    (horizontalCompleteTotalFiltration K).diagram.map (homOfLE h) =
      horizontalCompleteFilteredTotalMap K h :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltration_ι_app (i : EInt) :
    (horizontalCompleteTotalFiltration K).ι.app i =
      horizontalCompleteFilteredTotalToTotal K i :=
  rfl

/-- For a bicomplex K of shape (down ℕ,down ℕ) in a preadditive category with a zero object and
finite coproducts, let a∈ℤ satisfy a≥0 and n∈ℕ satisfy n≤a. The complete horizontal stage at a
has a canonical isomorphism (G_a)_n≅(Tot K)_n. The horizontal truncation retains every component
on the total-degree n antidiagonal because each of its horizontal indices is at most n≤a. -/
noncomputable def horizontalCompleteFilteredTotalEvalIsoOfLE
    (a : ℤ) (ha : 0 ≤ a) (n : ℕ) (h : n ≤ a.toNat) :
    (horizontalCompleteFilteredTotalComplex K (a : EInt)).X n ≅
      (K.total (ComplexShape.down ℕ)).X n :=
  (HomologicalComplex.eval C (ComplexShape.down ℕ) n).mapIso
      (eqToIso (horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha)) ≪≫
    horizontalFilteredTotalIsoOfLE K a.toNat n h

/-- Let K be a first-quadrant bicomplex in a preadditive category with a zero object and finite
coproducts. Reindex each complete horizontal chain stage G_i by placing its term of degree n∈ℕ
in cochain degree -n and setting positive cochain degrees to zero. This gives a functor
F:ℤ∪{⊥,⊤}→CochainComplex(C,ℤ), with transitions induced by G_i→G_j for i≤j. -/
noncomputable def horizontalCompleteFiltrationCochainDiagram :
    EInt ⥤ CochainComplex C ℤ :=
  (horizontalCompleteTotalFiltration K).diagram ⋙
    ComplexShape.embeddingDownNat.extendFunctor C

/-- Let C be preadditive with a zero object and finite coproducts, F:ℤ∪{⊥,⊤}→CochainComplex(C,ℤ),
and f:X→Y, g:Y→Z composable index arrows. This triangle has objects Cone(Ff), Cone(F(f≫g)) and
Cone(Fg). Its first two arrows are the cone maps induced by (id_{FX},Fg) and (Ff,id_{FZ}). Its
third arrow is Cone(Fg)→FY[1] from the cone triangle of Fg, followed by the shifted inclusion
FY[1]→Cone(Ff)[1]. Functoriality identifies F(f≫g) with Ff≫Fg. -/
noncomputable def functorMappingConeCompTriangle
    (F : EInt ⥤ CochainComplex C ℤ)
    {X Y Z : EInt} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Triangle (CochainComplex C ℤ) :=
  Triangle.mk
    (CochainComplex.mappingCone.map (F.map f) (F.map (f ≫ g)) (𝟙 _)
      (F.map g) (by simp [F.map_comp]))
    (CochainComplex.mappingCone.map (F.map (f ≫ g)) (F.map g) (F.map f)
      (𝟙 _) (by simp [F.map_comp]))
    ((CochainComplex.mappingCone.triangle (F.map g)).mor₃ ≫
      (CochainComplex.mappingCone.inr (F.map f))⟦1⟧')

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts, let F be its complete horizontal cochain filtration. The arrow i→j is sent to
Cone(F_i→F_j). A commutative square between i→j and i′→j′ is sent to the cone map induced by
F_i→F_{i′} and F_j→F_{j′}. These assignments define a functor from arrows of ℤ∪{⊥,⊤} to
integer-indexed cochain complexes. -/
noncomputable def horizontalCompleteFiltrationMappingConeFunctor :
    ComposableArrows EInt 1 ⥤ CochainComplex C ℤ where
  obj D := CochainComplex.mappingCone
    ((horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1))
  map {X Y} φ :=
    CochainComplex.mappingCone.map
      ((horizontalCompleteFiltrationCochainDiagram K).map (X.map' 0 1))
      ((horizontalCompleteFiltrationCochainDiagram K).map (Y.map' 0 1))
      ((horizontalCompleteFiltrationCochainDiagram K).map (φ.app 0))
      ((horizontalCompleteFiltrationCochainDiagram K).map (φ.app 1)) (by
        rw [← (horizontalCompleteFiltrationCochainDiagram K).map_comp,
          ← (horizontalCompleteFiltrationCochainDiagram K).map_comp]
        apply (horizontalCompleteFiltrationCochainDiagram K).congr_map
        have hφ := naturality' φ 0 1
        change X.map' 0 1 ≫ φ.app 1 = φ.app 0 ≫ Y.map' 0 1 at hφ
        exact hφ)
  map_id D := by
    dsimp
    simpa using CochainComplex.mappingCone.map_id
      ((horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1))
  map_comp φ ψ := by
    dsimp
    rw [← CochainComplex.mappingCone.map_comp]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- Let K be a bicomplex of shape (down ℕ,down ℕ) in a preadditive category with a zero object and
finite coproducts, and F its complete horizontal cochain filtration. This triangulated spectral
object in the cochain homotopy category, indexed by ℤ∪{⊥,⊤}, assigns i→j the relative cone
Cone(F_i→F_j). For i≤j≤k, the connecting arrow Cone(F_j→F_k)→Cone(F_i→F_j)[1] is the third
morphism of the cone composition triangle
Cone(F_i→F_j)→Cone(F_i→F_k)→Cone(F_j→F_k)→Cone(F_i→F_j)[1]. -/
noncomputable def horizontalCompleteFiltrationTriangulatedSpectralObject :
    CategoryTheory.Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) EInt where
  ω₁ :=
    horizontalCompleteFiltrationMappingConeFunctor K ⋙
      HomotopyCategory.quotient C (ComplexShape.up ℤ)
  δ'.app D := ((HomotopyCategory.quotient C
    (ComplexShape.up ℤ)).mapTriangle.obj
      (functorMappingConeCompTriangle
        (horizontalCompleteFiltrationCochainDiagram K)
        (D.map' 0 1) (D.map' 1 2))).mor₃
  δ'.naturality D₁ D₂ φ := by
    obtain ⟨_, _, _, f₁, g₁, rfl⟩ := ComposableArrows.mk₂_surjective D₁
    obtain ⟨_, _, _, f₂, g₂, rfl⟩ := ComposableArrows.mk₂_surjective D₂
    let F := horizontalCompleteFiltrationCochainDiagram K
    let φ' : mk₂ (F.map f₁) (F.map g₁) ⟶ mk₂ (F.map f₂) (F.map g₂) :=
      homMk₂ (F.map (φ.app 0)) (F.map (φ.app 1)) (F.map (φ.app 2))
        (by
          change F.map f₁ ≫ F.map (φ.app 1) = F.map (φ.app 0) ≫ F.map f₂
          rw [← F.map_comp, ← F.map_comp]
          apply F.congr_map
          have hφ := naturality' φ 0 1
          change f₁ ≫ φ.app 1 = φ.app 0 ≫ f₂ at hφ
          exact hφ)
        (by
          change F.map g₁ ≫ F.map (φ.app 2) = F.map (φ.app 1) ≫ F.map g₂
          rw [← F.map_comp, ← F.map_comp]
          apply F.congr_map
          have hφ := naturality' φ 1 2
          change g₁ ≫ φ.app 2 = φ.app 1 ≫ g₂ at hφ
          exact hφ)
    have eq := CochainComplex.mappingConeCompTriangle_mor₃_naturality
      (F.map f₁) (F.map g₁) (F.map f₂) (F.map g₂) φ'
    dsimp [F, φ', ComposableArrows.Precomp.map,
      horizontalCompleteFiltrationMappingConeFunctor,
      functorMappingConeCompTriangle] at eq ⊢
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp [eq]
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    let F := horizontalCompleteFiltrationCochainDiagram K
    let hfg := F.map_comp f g
    let e₂ :
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone (F.map (f ≫ g))) ≅
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone (F.map f ≫ F.map g)) :=
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso
        (CochainComplex.mappingCone.isoOfHomEq (C := C) hfg)
    refine isomorphic_distinguished _
      (HomotopyCategory.mappingConeCompTriangleh_distinguished
        (F.map f) (F.map g)) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e₂ (Iso.refl _) ?_ ?_ ?_
    · have hc := CochainComplex.mappingCone.map_comp_isoOfHomEq
        (F.map f) (𝟙 _) (F.map g) hfg
        (by simp [hfg]) (by simp)
      have hQ := (HomotopyCategory.quotient C
        (ComplexShape.up ℤ)).congr_map hc
      simpa [F, e₂, horizontalCompleteFiltrationMappingConeFunctor,
        functorMappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangleh,
        ComposableArrows.Precomp.map, ← Functor.map_comp] using hQ
    · have hc := (CochainComplex.mappingCone.isoOfHomEq_hom_comp_map
        (F.map g) (F.map f) (𝟙 _) hfg
        (by simp [hfg]) (by simp)).symm
      have hQ := (HomotopyCategory.quotient C
        (ComplexShape.up ℤ)).congr_map hc
      simpa [F, e₂, horizontalCompleteFiltrationMappingConeFunctor,
        functorMappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangleh,
        ComposableArrows.Precomp.map, ← Functor.map_comp] using hQ
    · simp [F, horizontalCompleteFiltrationMappingConeFunctor,
        functorMappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangleh,
        ComposableArrows.Precomp.map]

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). Apply the degree-zero
homological functor on the cochain homotopy category to the complete-filtration triangulated
spectral object. The resulting abelian spectral object is indexed by ℤ∪{⊥,⊤}; its degree-n value
on i→j is the cochain homology H^n(Cone(F_i→F_j)), where chain degree r of the complete stage is
placed in cochain degree -r. -/
noncomputable def horizontalCompleteFiltrationSpectralObject :
    CategoryTheory.Abelian.SpectralObject C EInt :=
  (horizontalCompleteFiltrationTriangulatedSpectralObject K).mapHomologicalFunctor
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)

/-- For a first-quadrant bicomplex K in an abelian category, let F be its complete horizontal
cochain filtration. For index arrows f:i→j and g:j→k and integers n,n′ with n+1=n′, the spectral
connecting map δ:H^n(Cone(Fg))→H^{n′}(Cone(Ff)) equals the connecting homology map of the
standard cone composition triangle Cone(Ff)→Cone(Ff≫Fg)→Cone(Fg)→Cone(Ff)[1]. The equality
identifies the specified connecting arrows with the same cochain degree increase and
cone-triangle sign convention. -/
theorem horizontalCompleteFiltrationSpectralObject_δ
    {i j k : EInt} (f : i ⟶ j) (g : j ⟶ k)
    (n n' : ℤ) (h : n + 1 = n') :
    (horizontalCompleteFiltrationSpectralObject K).δ f g n n' h =
      (HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) 0).homologySequenceδ
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
            (CochainComplex.mappingConeCompTriangle
              ((horizontalCompleteFiltrationCochainDiagram K).map f)
              ((horizontalCompleteFiltrationCochainDiagram K).map g)))
          n n' h := by
  rfl

end HomologicalComplex₂

end
