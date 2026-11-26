/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorFlip
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso
public import MathlibExt.Algebra.Homology.TotalComplexSingleDownNat
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Resolution augmentations of a biadditive bifunctor

Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive in both
variables. For nonnegative chain complexes, the bicomplex has term
`F(P_p,Q_q)` and total degree `n` given by the antidiagonal `p+q=n`.
A resolution augmentation `Q → B[0]` gives a total map to `F(P,B)`;
a resolution augmentation `P → A[0]` gives one to `F(A,Q)` using
the signed flip. The surviving degree-zero summands have the original
augmentation maps, and all positive augmented-factor summands vanish.
Homology preservation of the partial functors on projective factors
makes the corresponding total augmentation a quasi-isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftDerivedBalance

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X : C₁, (F.obj X).Additive]

local notation "c" => ComplexShape.down ℕ

omit [F.Additive] [Abelian C₁] in
/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. The flipped bifunctor `C₂ → C₁ → D` is additive in its
outer variable, by the second-variable additivity of `F`. -/
theorem flippedAdditive : F.flip.Additive where
  map_add := by
    intro Y Y' f g
    apply NatTrans.ext
    funext X
    exact (F.obj X).map_add

omit [∀ X : C₁, (F.obj X).Additive] [Abelian C₂] in
/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For every `Y : C₂`, the flipped partial functor
`F(-,Y) : C₁ → D` is additive. -/
theorem flippedObjAdditive (Y : C₂) : (F.flip.obj Y).Additive where
  map_add := by
    intro X X' f g
    exact congrArg (fun t : F.obj X ⟶ F.obj X' => t.app Y) (F.map_add (f := f) (g := g))

attribute [local instance] flippedAdditive flippedObjAdditive

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain complex `P` in `C₁` and `B : C₂`, the bicomplex
`F(P,B[0])` is naturally identified with the one-sided chain complex
`F(P,B)` concentrated at inner degree zero. -/
def singleRightBicomplexIso (P : ChainComplex C₁ ℕ) (B : C₂) :
    (((F.mapBifunctorHomologicalComplex c c).obj P).obj ((ChainComplex.single₀ C₂).obj B)) ≅
      ((ChainComplex.single₀ D).mapHomologicalComplex c).obj
        (((F.flip.obj B).mapHomologicalComplex c).obj P) := by
  let e (p : ℕ) :=
    (HomologicalComplex.singleMapHomologicalComplex (F.obj (P.X p)) c 0).app B
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro p p' hpp'
  change (e p).hom ≫ (ChainComplex.single₀ D).map ((F.map (P.d p p')).app B) =
    ((NatTrans.mapHomologicalComplex (F.map (P.d p p')) c).app
      ((ChainComplex.single₀ C₂).obj B)) ≫ (e p').hom
  have h := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj
    (F.map (P.d p p')) c 0 B
  have hc :
      ((NatTrans.mapHomologicalComplex (F.map (P.d p p')) c).app
        ((ChainComplex.single₀ C₂).obj B)) ≫ (e p').hom =
        (e p).hom ≫ (ChainComplex.single₀ D).map ((F.map (P.d p p')).app B) := by
    calc
      _ = ((e p).hom ≫ (ChainComplex.single₀ D).map ((F.map (P.d p p')).app B) ≫
          (e p').inv) ≫ (e p').hom :=
        congrArg
          (fun a : ((F.obj (P.X p)).mapHomologicalComplex c).obj
              ((ChainComplex.single₀ C₂).obj B) ⟶
            ((F.obj (P.X p')).mapHomologicalComplex c).obj
              ((ChainComplex.single₀ C₂).obj B) => a ≫ (e p').hom) h
      _ = _ := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hc.symm

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain complex `P` in `C₁` and `B : C₂`, totalizing
`F(P,B[0])` gives the natural complex isomorphism
`Tot(F(P,B[0])) ≅ F(P,B)`. -/
def singleRightTotalIso (P : ChainComplex C₁ ℕ) (B : C₂) :
    HomologicalComplex.mapBifunctor P ((ChainComplex.single₀ C₂).obj B) F c ≅
      ((F.flip.obj B).mapHomologicalComplex c).obj P :=
  (HomologicalComplex₂.totalFunctor D c c c).mapIso (singleRightBicomplexIso F P B) ≪≫
    HomologicalComplex₂.single₀MapTotalIso (((F.flip.obj B).mapHomologicalComplex c).obj P)

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For `P : ChainComplex C₁ ℕ` and `B : C₂`, the `(p,0)`
summand of `Tot(F(P,B[0]))` maps to `F(P_p,B)` by the canonical
single-complex coordinate identification in degree `p`. -/
theorem ι_singleRightTotalIso_hom (P : ChainComplex C₁ ℕ) (B : C₂) (p : ℕ) :
    HomologicalComplex.ιMapBifunctor P ((ChainComplex.single₀ C₂).obj B) F c p 0 p
        (Nat.add_zero p) ≫ (singleRightTotalIso F P B).hom.f p =
      (((HomologicalComplex.singleMapHomologicalComplex (F.obj (P.X p)) c 0).app B).hom).f 0 ≫
        (HomologicalComplex.singleObjXSelf c 0 ((F.obj (P.X p)).obj B)).hom := by
  let K : HomologicalComplex₂ D c c :=
    ((F.mapBifunctorHomologicalComplex c c).obj P).obj ((ChainComplex.single₀ C₂).obj B)
  let L : ChainComplex D ℕ := ((F.flip.obj B).mapHomologicalComplex c).obj P
  let S : HomologicalComplex₂ D c c := ((ChainComplex.single₀ D).mapHomologicalComplex c).obj L
  let E : K ≅ S := singleRightBicomplexIso F P B
  let M : K.total c ⟶ S.total c := HomologicalComplex₂.total.map E.hom c
  let J : S.total c ≅ L := HomologicalComplex₂.single₀MapTotalIso L
  let T : K.total c ≅ L := singleRightTotalIso F P B
  have hT : T.hom = M ≫ J.hom := rfl
  have hTComponent : T.hom.f p = M.f p ≫ J.hom.f p :=
    (congrArg (fun f : K.total c ⟶ L => f.f p) hT).trans
      (HomologicalComplex.comp_f M J.hom p)
  let X : D := (K.X p).X 0
  let Y : D := L.X p
  let ι : X ⟶ (K.total c).X p := K.ιTotal c p 0 p (by change p + 0 = p; omega)
  let ι' : Y ⟶ (S.total c).X p := S.ιTotal c p 0 p (by change p + 0 = p; omega)
  let e : X ⟶ Y := (E.hom.f p).f 0
  have hMap : ι ≫ M.f p = e ≫ ι' :=
    HomologicalComplex₂.ιTotal_map (K := K) (L := S) (φ := E.hom) (c₁₂ := c)
      (i₁ := p) (i₂ := 0) (i₁₂ := p) (h := by change p + 0 = p; omega)
  have hSingle : ι' ≫ J.hom.f p = 𝟙 Y :=
    HomologicalComplex₂.ιTotal_comp_single₀MapTotalIso_hom L p
  have hResult : ι ≫ T.hom.f p = e :=
    (congrArg (fun f : (K.total c).X p ⟶ Y => ι ≫ f) hTComponent).trans
      (((Category.assoc ι (M.f p) (J.hom.f p)).symm).trans
        ((congrArg (fun f : X ⟶ (S.total c).X p => f ≫ J.hom.f p) hMap).trans
          ((Category.assoc e ι' (J.hom.f p)).trans
            ((congrArg (fun f : Y ⟶ Y => e ≫ f) hSingle).trans (Category.comp_id e)))))
  let e₀ : X ⟶ Y :=
    (((HomologicalComplex.singleMapHomologicalComplex (F.obj (P.X p)) c 0).app B).hom).f 0
  have hComponent : e = e₀ := rfl
  let j : Y ⟶ Y := (HomologicalComplex.singleObjXSelf c 0 ((F.obj (P.X p)).obj B)).hom
  have hIdentity : j = 𝟙 Y := rfl
  have hRight : e₀ ≫ j = e :=
    (congrArg (fun f : Y ⟶ Y => e₀ ≫ f) hIdentity).trans
      ((Category.comp_id e₀).trans hComponent.symm)
  change ι ≫ T.hom.f p = e₀ ≫ j
  exact hResult.trans hRight.symm

/-- In an abelian category `D`, a map `f : L → L′` of nonnegative
chain complexes commutes with the canonical identifications of the
totals of their inner-degree-zero bicomplexes with `L` and `L′`. -/
theorem single₀MapTotalIso_hom_naturality
    {L L' : ChainComplex D ℕ} (f : L ⟶ L') :
    HomologicalComplex₂.total.map
        (((ChainComplex.single₀ D).mapHomologicalComplex c).map f) c ≫
        (HomologicalComplex₂.single₀MapTotalIso L').hom =
      (HomologicalComplex₂.single₀MapTotalIso L).hom ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  cases q with
  | zero =>
    change p + 0 = n at hpq
    have hp : p = n := by omega
    subst p
    let K : HomologicalComplex₂ D c c := ((ChainComplex.single₀ D).mapHomologicalComplex c).obj L
    let K' : HomologicalComplex₂ D c c := ((ChainComplex.single₀ D).mapHomologicalComplex c).obj L'
    let ψ : K ⟶ K' := ((ChainComplex.single₀ D).mapHomologicalComplex c).map f
    let X : D := L.X n
    let Y : D := L'.X n
    let ι : X ⟶ (K.total c).X n := K.ιTotal c n 0 n (by change n + 0 = n; omega)
    let ι' : Y ⟶ (K'.total c).X n := K'.ιTotal c n 0 n (by change n + 0 = n; omega)
    let m : (K.total c).X n ⟶ (K'.total c).X n := (HomologicalComplex₂.total.map ψ c).f n
    let j : (K.total c).X n ⟶ X := (HomologicalComplex₂.single₀MapTotalIso L).hom.f n
    let j' : (K'.total c).X n ⟶ Y := (HomologicalComplex₂.single₀MapTotalIso L').hom.f n
    let k : X ⟶ Y := (ψ.f n).f 0
    let f₀ : X ⟶ Y := f.f n
    have hMap : ι ≫ m = k ≫ ι' :=
      HomologicalComplex₂.ιTotal_map (K := K) (L := K') (φ := ψ) (c₁₂ := c)
        (i₁ := n) (i₂ := 0) (i₁₂ := n) (h := by change n + 0 = n; omega)
    have hSingle : ι ≫ j = 𝟙 X :=
      HomologicalComplex₂.ιTotal_comp_single₀MapTotalIso_hom L n
    have hSingle' : ι' ≫ j' = 𝟙 Y :=
      HomologicalComplex₂.ιTotal_comp_single₀MapTotalIso_hom L' n
    have hk : k = f₀ :=
      ChainComplex.single₀_map_f_zero (f.f n)
    change ι ≫ (m ≫ j') = ι ≫ (j ≫ f₀)
    calc
      ι ≫ (m ≫ j') = (ι ≫ m) ≫ j' := (Category.assoc _ _ _).symm
      _ = (k ≫ ι') ≫ j' := congrArg (fun a => a ≫ j') hMap
      _ = k ≫ (ι' ≫ j') := Category.assoc _ _ _
      _ = k ≫ 𝟙 Y := congrArg (fun a => k ≫ a) hSingle'
      _ = k := Category.comp_id _
      _ = f₀ := hk
      _ = 𝟙 X ≫ f₀ := (Category.id_comp _).symm
      _ = (ι ≫ j) ≫ f₀ := congrArg (fun a => a ≫ f₀) hSingle.symm
      _ = ι ≫ (j ≫ f₀) := Category.assoc _ _ _
  | succ q =>
    exact (HomologicalComplex.isZero_single_obj_X c 0 (L.X p) (q + 1)
      (Nat.succ_ne_zero q)).eq_of_src _ _

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain map `f : P → P′` and `B : C₂`, the bicomplex
identifications `F(P,B[0]) ≅ F(P,B)[0]` commute with the mapped
first-variable complex map. -/
theorem singleRightBicomplexIso_hom_naturality_left
    {P P' : ChainComplex C₁ ℕ} (f : P ⟶ P') (B : C₂) :
    ((F.mapBifunctorHomologicalComplex c c).map f).app
        ((ChainComplex.single₀ C₂).obj B) ≫ (singleRightBicomplexIso F P' B).hom =
      (singleRightBicomplexIso F P B).hom ≫
        ((ChainComplex.single₀ D).mapHomologicalComplex c).map
          (((F.flip.obj B).mapHomologicalComplex c).map f) := by
  apply HomologicalComplex.Hom.ext
  funext p
  let E := (HomologicalComplex.singleMapHomologicalComplex (F.obj (P.X p)) c 0).app B
  let E' := (HomologicalComplex.singleMapHomologicalComplex (F.obj (P'.X p)) c 0).app B
  let a := (NatTrans.mapHomologicalComplex (F.map (f.f p)) c).app
    ((ChainComplex.single₀ C₂).obj B)
  let b := (ChainComplex.single₀ D).map ((F.map (f.f p)).app B)
  have hMap : a = E.hom ≫ b ≫ E'.inv := by
    have h := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj
      (F.map (f.f p)) c 0 B
    change a = E.hom ≫ b ≫ E'.inv at h
    exact h
  have hCancel : (E.hom ≫ b ≫ E'.inv) ≫ E'.hom = E.hom ≫ b := by
    calc
      _ = E.hom ≫ b ≫ (E'.inv ≫ E'.hom) := by simp only [Category.assoc]
      _ = E.hom ≫ b ≫ 𝟙 _ := congrArg (fun m => E.hom ≫ b ≫ m) E'.inv_hom_id
      _ = E.hom ≫ b := congrArg (fun m => E.hom ≫ m) (Category.comp_id b)
  change a ≫ E'.hom = E.hom ≫ b
  exact (congrArg (fun m => m ≫ E'.hom) hMap).trans hCancel

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain complex `P` and `g : B → B′`, the bicomplex
identifications for `F(P,B[0])` and `F(P,B′[0])` commute with the
coefficient transformation `F(P,g)`. -/
theorem singleRightBicomplexIso_hom_naturality_right
    (P : ChainComplex C₁ ℕ) {B B' : C₂} (g : B ⟶ B') :
    ((F.mapBifunctorHomologicalComplex c c).obj P).map ((ChainComplex.single₀ C₂).map g) ≫
        (singleRightBicomplexIso F P B').hom =
      (singleRightBicomplexIso F P B).hom ≫
        ((ChainComplex.single₀ D).mapHomologicalComplex c).map
          ((NatTrans.mapHomologicalComplex (F.flip.map g) c).app P) := by
  apply HomologicalComplex.Hom.ext
  funext p
  change ((F.obj (P.X p)).mapHomologicalComplex c).map ((ChainComplex.single₀ C₂).map g) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (F.obj (P.X p)) c 0).app B').hom =
    ((HomologicalComplex.singleMapHomologicalComplex (F.obj (P.X p)) c 0).app B).hom ≫
      (ChainComplex.single₀ D).map ((F.obj (P.X p)).map g)
  exact ((HomologicalComplex.singleMapHomologicalComplex (F.obj (P.X p)) c 0).hom.naturality g)

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain map `f : P → P′` and `B : C₂`, the total
comparisons `Tot(F(P,B[0])) ≅ F(P,B)` commute with `F(f,B)`. -/
theorem singleRightTotalIso_hom_naturality_left
    {P P' : ChainComplex C₁ ℕ} (f : P ⟶ P') (B : C₂) :
    HomologicalComplex₂.total.map
        (((F.mapBifunctorHomologicalComplex c c).map f).app
          ((ChainComplex.single₀ C₂).obj B)) c ≫
        (singleRightTotalIso F P' B).hom =
      (singleRightTotalIso F P B).hom ≫
        ((F.flip.obj B).mapHomologicalComplex c).map f := by
  let L : ChainComplex D ℕ := ((F.flip.obj B).mapHomologicalComplex c).obj P
  let L' : ChainComplex D ℕ := ((F.flip.obj B).mapHomologicalComplex c).obj P'
  let K : HomologicalComplex₂ D c c :=
      ((F.mapBifunctorHomologicalComplex c c).obj P).obj ((ChainComplex.single₀ C₂).obj B)
  let K' : HomologicalComplex₂ D c c :=
      ((F.mapBifunctorHomologicalComplex c c).obj P').obj ((ChainComplex.single₀ C₂).obj B)
  let S : HomologicalComplex₂ D c c := ((ChainComplex.single₀ D).mapHomologicalComplex c).obj L
  let S' : HomologicalComplex₂ D c c := ((ChainComplex.single₀ D).mapHomologicalComplex c).obj L'
  let E : K ≅ S := singleRightBicomplexIso F P B
  let E' : K' ≅ S' := singleRightBicomplexIso F P' B
  let ψ : K ⟶ K' := ((F.mapBifunctorHomologicalComplex c c).map f).app
      ((ChainComplex.single₀ C₂).obj B)
  let ℓ : L ⟶ L' := ((F.flip.obj B).mapHomologicalComplex c).map f
  let σ : S ⟶ S' := ((ChainComplex.single₀ D).mapHomologicalComplex c).map ℓ
  let m : K.total c ⟶ S.total c := HomologicalComplex₂.total.map E.hom c
  let m' : K'.total c ⟶ S'.total c := HomologicalComplex₂.total.map E'.hom c
  let t : K.total c ⟶ K'.total c := HomologicalComplex₂.total.map ψ c
  let s : S.total c ⟶ S'.total c := HomologicalComplex₂.total.map σ c
  let J : S.total c ≅ L := HomologicalComplex₂.single₀MapTotalIso L
  let J' : S'.total c ≅ L' := HomologicalComplex₂.single₀MapTotalIso L'
  let T : K.total c ≅ L := singleRightTotalIso F P B
  let T' : K'.total c ≅ L' := singleRightTotalIso F P' B
  have hT : T.hom = m ≫ J.hom := rfl
  have hT' : T'.hom = m' ≫ J'.hom := rfl
  have hSquare : ψ ≫ E'.hom = E.hom ≫ σ := singleRightBicomplexIso_hom_naturality_left F f B
  have hTotal : t ≫ m' = m ≫ s :=
    (HomologicalComplex₂.total.map_comp (φ := ψ) (ψ := E'.hom) (c₁₂ := c)).symm.trans
      ((congrArg (fun a : K ⟶ S' => HomologicalComplex₂.total.map a c) hSquare).trans
        (HomologicalComplex₂.total.map_comp (φ := E.hom) (ψ := σ) (c₁₂ := c)))
  have hSingle : s ≫ J'.hom = J.hom ≫ ℓ := single₀MapTotalIso_hom_naturality ℓ
  change t ≫ T'.hom = T.hom ≫ ℓ
  calc
    t ≫ T'.hom = t ≫ (m' ≫ J'.hom) := congrArg (fun a => t ≫ a) hT'
    _ = (t ≫ m') ≫ J'.hom := (Category.assoc _ _ _).symm
    _ = (m ≫ s) ≫ J'.hom := congrArg (fun a => a ≫ J'.hom) hTotal
    _ = m ≫ (s ≫ J'.hom) := Category.assoc _ _ _
    _ = m ≫ (J.hom ≫ ℓ) := congrArg (fun a => m ≫ a) hSingle
    _ = (m ≫ J.hom) ≫ ℓ := (Category.assoc _ _ _).symm
    _ = T.hom ≫ ℓ := congrArg (fun a => a ≫ ℓ) hT.symm

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain complex `P` and `g : B → B′`, the total
comparisons `Tot(F(P,B[0])) ≅ F(P,B)` commute with `F(P,g)`. -/
theorem singleRightTotalIso_hom_naturality_right
    (P : ChainComplex C₁ ℕ) {B B' : C₂} (g : B ⟶ B') :
    HomologicalComplex₂.total.map
        (((F.mapBifunctorHomologicalComplex c c).obj P).map
          ((ChainComplex.single₀ C₂).map g)) c ≫
        (singleRightTotalIso F P B').hom =
      (singleRightTotalIso F P B).hom ≫
        ((NatTrans.mapHomologicalComplex (F.flip.map g) c).app P) := by
  let L : ChainComplex D ℕ := ((F.flip.obj B).mapHomologicalComplex c).obj P
  let L' : ChainComplex D ℕ := ((F.flip.obj B').mapHomologicalComplex c).obj P
  let K : HomologicalComplex₂ D c c :=
      ((F.mapBifunctorHomologicalComplex c c).obj P).obj ((ChainComplex.single₀ C₂).obj B)
  let K' : HomologicalComplex₂ D c c :=
      ((F.mapBifunctorHomologicalComplex c c).obj P).obj ((ChainComplex.single₀ C₂).obj B')
  let S : HomologicalComplex₂ D c c := ((ChainComplex.single₀ D).mapHomologicalComplex c).obj L
  let S' : HomologicalComplex₂ D c c := ((ChainComplex.single₀ D).mapHomologicalComplex c).obj L'
  let E : K ≅ S := singleRightBicomplexIso F P B
  let E' : K' ≅ S' := singleRightBicomplexIso F P B'
  let ψ : K ⟶ K' := ((F.mapBifunctorHomologicalComplex c c).obj P).map
      ((ChainComplex.single₀ C₂).map g)
  let ℓ : L ⟶ L' := (NatTrans.mapHomologicalComplex (F.flip.map g) c).app P
  let σ : S ⟶ S' := ((ChainComplex.single₀ D).mapHomologicalComplex c).map ℓ
  let m : K.total c ⟶ S.total c := HomologicalComplex₂.total.map E.hom c
  let m' : K'.total c ⟶ S'.total c := HomologicalComplex₂.total.map E'.hom c
  let t : K.total c ⟶ K'.total c := HomologicalComplex₂.total.map ψ c
  let s : S.total c ⟶ S'.total c := HomologicalComplex₂.total.map σ c
  let J : S.total c ≅ L := HomologicalComplex₂.single₀MapTotalIso L
  let J' : S'.total c ≅ L' := HomologicalComplex₂.single₀MapTotalIso L'
  let T : K.total c ≅ L := singleRightTotalIso F P B
  let T' : K'.total c ≅ L' := singleRightTotalIso F P B'
  have hT : T.hom = m ≫ J.hom := rfl
  have hT' : T'.hom = m' ≫ J'.hom := rfl
  have hSquare : ψ ≫ E'.hom = E.hom ≫ σ := singleRightBicomplexIso_hom_naturality_right F P g
  have hTotal : t ≫ m' = m ≫ s :=
    (HomologicalComplex₂.total.map_comp (φ := ψ) (ψ := E'.hom) (c₁₂ := c)).symm.trans
      ((congrArg (fun a : K ⟶ S' => HomologicalComplex₂.total.map a c) hSquare).trans
        (HomologicalComplex₂.total.map_comp (φ := E.hom) (ψ := σ) (c₁₂ := c)))
  have hSingle : s ≫ J'.hom = J.hom ≫ ℓ := single₀MapTotalIso_hom_naturality ℓ
  change t ≫ T'.hom = T.hom ≫ ℓ
  calc
    t ≫ T'.hom = t ≫ (m' ≫ J'.hom) := congrArg (fun a => t ≫ a) hT'
    _ = (t ≫ m') ≫ J'.hom := (Category.assoc _ _ _).symm
    _ = (m ≫ s) ≫ J'.hom := congrArg (fun a => a ≫ J'.hom) hTotal
    _ = m ≫ (s ≫ J'.hom) := Category.assoc _ _ _
    _ = m ≫ (J.hom ≫ ℓ) := congrArg (fun a => m ≫ a) hSingle
    _ = (m ≫ J.hom) ≫ ℓ := (Category.assoc _ _ _).symm
    _ = T.hom ≫ ℓ := congrArg (fun a => a ≫ ℓ) hT.symm

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain complex `P` in `C₁` and projective resolution
`Q` of `B : C₂`, the augmentation of `Q` gives a chain map
`Tot(F(P,Q)) → F(P,B)`. -/
def rightAugmentation (P : ChainComplex C₁ ℕ) {B : C₂} (Q : ProjectiveResolution B) :
    HomologicalComplex.mapBifunctor P Q.complex F c ⟶
      ((F.flip.obj B).mapHomologicalComplex c).obj P :=
  HomologicalComplex₂.total.map
    (((F.mapBifunctorHomologicalComplex c c).obj P).map Q.π) c ≫
      (singleRightTotalIso F P B).hom

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For `P : ChainComplex C₁ ℕ`, a projective resolution `Q` of
`B`, and first degree `p`, the row map induced by `Q → B[0]` is
that augmentation mapped by the partial functor `F(P_p,-)`. -/
theorem rightAugmentation_row (P : ChainComplex C₁ ℕ) {B : C₂}
    (Q : ProjectiveResolution B) (p : ℕ) :
    (((F.mapBifunctorHomologicalComplex c c).obj P).map Q.π).f p =
      ((F.obj (P.X p)).mapHomologicalComplex c).map Q.π := rfl

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain complex `P` and a projective resolution `Q` of
`B`, the `(p,0)` summand of the right total augmentation has map
`F(P_p,Q₀) → F(P_p,B)` induced by `π_Q,₀`. -/
theorem ι_rightAugmentation (P : ChainComplex C₁ ℕ) {B : C₂}
    (Q : ProjectiveResolution B) (p : ℕ) :
    HomologicalComplex.ιMapBifunctor P Q.complex F c p 0 p (Nat.add_zero p) ≫
        (rightAugmentation F P Q).f p =
      (F.obj (P.X p)).map (Q.π.f 0) := by
  let S := (ChainComplex.single₀ C₂).obj B
  let K := ((F.mapBifunctorHomologicalComplex c c).obj P).obj Q.complex
  let K' := ((F.mapBifunctorHomologicalComplex c c).obj P).obj S
  let L := ((F.flip.obj B).mapHomologicalComplex c).obj P
  let φ : K ⟶ K' := ((F.mapBifunctorHomologicalComplex c c).obj P).map Q.π
  let m : K.total c ⟶ K'.total c := HomologicalComplex₂.total.map φ c
  let e : K'.total c ≅ L := singleRightTotalIso F P B
  let j : (K.X p).X 0 ⟶ (K.total c).X p := K.ιTotal c p 0 p (Nat.add_zero p)
  let j' : (K'.X p).X 0 ⟶ (K'.total c).X p := K'.ιTotal c p 0 p (Nat.add_zero p)
  let d : (K.X p).X 0 ⟶ (K'.X p).X 0 := (φ.f p).f 0
  have hMap : j ≫ m.f p = d ≫ j' :=
    HomologicalComplex₂.ιTotal_map (K := K) (L := K') (φ := φ)
      (c₁₂ := c) p 0 p (Nat.add_zero p)
  let H := F.obj (P.X p)
  let a₀ := HomologicalComplex.singleObjXSelf c 0 B
  let a₁ := HomologicalComplex.singleObjXSelf c 0 (H.obj B)
  let E := (HomologicalComplex.singleMapHomologicalComplex H c 0).app B
  let s₀ : (K'.X p).X 0 ⟶ H.obj B := H.map a₀.hom
  have hSingle : j' ≫ e.hom.f p = E.hom.f 0 ≫ a₁.hom :=
    ι_singleRightTotalIso_hom F P B p
  have hField : E.hom.f 0 = s₀ ≫ a₁.inv :=
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self H c 0 B
  have hCancel : (s₀ ≫ a₁.inv) ≫ a₁.hom = s₀ :=
    (Category.assoc s₀ a₁.inv a₁.hom).trans
      ((congrArg (fun q : H.obj B ⟶ H.obj B => s₀ ≫ q) a₁.inv_hom_id).trans
        (Category.comp_id s₀))
  have hCollapse : j' ≫ e.hom.f p = s₀ :=
    hSingle.trans ((congrArg
      (fun q : (K'.X p).X 0 ⟶ ((ChainComplex.single₀ D).obj (H.obj B)).X 0 =>
        q ≫ a₁.hom) hField).trans hCancel)
  let q₀ : Q.complex.X 0 ⟶ B := Q.π.f 0
  have hQ : Q.π.f 0 ≫ a₀.hom = q₀ := by
    change q₀ ≫ (𝟙 B) = q₀
    exact Category.comp_id q₀
  have hStage : d = H.map (Q.π.f 0) := rfl
  have hFinal : d ≫ s₀ = H.map q₀ :=
    (congrArg (fun q : H.obj (Q.complex.X 0) ⟶ H.obj (S.X 0) =>
      q ≫ H.map a₀.hom) hStage).trans
        ((H.map_comp (Q.π.f 0) a₀.hom).symm.trans (congrArg H.map hQ))
  change j ≫ (m.f p ≫ e.hom.f p) = H.map q₀
  exact (Category.assoc j (m.f p) (e.hom.f p)).symm.trans
    ((congrArg (fun q : (K.X p).X 0 ⟶ (K'.total c).X p => q ≫ e.hom.f p) hMap).trans
      ((Category.assoc d j' (e.hom.f p)).trans
        ((congrArg (fun q : (K'.X p).X 0 ⟶ H.obj B => d ≫ q) hCollapse).trans hFinal)))

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain complex `P` and projective resolution `Q` of `B`,
the right total augmentation vanishes on every summand `F(P_p,Q_q)`
with `q>0` and total degree `p+q`. -/
theorem ι_rightAugmentation_succ (P : ChainComplex C₁ ℕ) {B : C₂}
    (Q : ProjectiveResolution B) (p q n : ℕ) (h : p + (q + 1) = n) :
    HomologicalComplex.ιMapBifunctor P Q.complex F c p (q + 1) n h ≫
        (rightAugmentation F P Q).f n = 0 := by
  let S := (ChainComplex.single₀ C₂).obj B
  let K := ((F.mapBifunctorHomologicalComplex c c).obj P).obj Q.complex
  let K' := ((F.mapBifunctorHomologicalComplex c c).obj P).obj S
  let L := ((F.flip.obj B).mapHomologicalComplex c).obj P
  let φ : K ⟶ K' := ((F.mapBifunctorHomologicalComplex c c).obj P).map Q.π
  let m : K.total c ⟶ K'.total c := HomologicalComplex₂.total.map φ c
  let e : K'.total c ≅ L := singleRightTotalIso F P B
  let j : (K.X p).X (q + 1) ⟶ (K.total c).X n := K.ιTotal c p (q + 1) n h
  let j' : (K'.X p).X (q + 1) ⟶ (K'.total c).X n := K'.ιTotal c p (q + 1) n h
  let d : (K.X p).X (q + 1) ⟶ (K'.X p).X (q + 1) := (φ.f p).f (q + 1)
  have hMap : j ≫ m.f n = d ≫ j' :=
    HomologicalComplex₂.ιTotal_map (K := K) (L := K') (φ := φ)
      (c₁₂ := c) p (q + 1) n h
  have hZero : d = 0 := by
    change (F.obj (P.X p)).map (Q.π.f (q + 1)) = 0
    rw [Q.π_f_succ, CategoryTheory.Functor.map_zero]
  change j ≫ (m.f n ≫ e.hom.f n) = 0
  calc
    _ = (j ≫ m.f n) ≫ e.hom.f n := (Category.assoc _ _ _).symm
    _ = (d ≫ j') ≫ e.hom.f n :=
      congrArg (fun k : (K.X p).X (q + 1) ⟶ (K'.total c).X n => k ≫ e.hom.f n) hMap
    _ = (0 ≫ j') ≫ e.hom.f n :=
      congrArg (fun k : (K.X p).X (q + 1) ⟶ (K'.X p).X (q + 1) =>
        (k ≫ j') ≫ e.hom.f n) hZero
    _ = 0 := by simp only [CategoryTheory.Limits.zero_comp]

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. Chain maps `f : P → P′`, `g : Q → Q′` induce the total
chain map `Tot(F(P,Q)) → Tot(F(P′,Q′))`, whose antidiagonal
summands use the two bifunctor maps `F(f_p,g_q)`. -/
def totalMap {P P' : ChainComplex C₁ ℕ} {Q Q' : ChainComplex C₂ ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctor P Q F c ⟶
      HomologicalComplex.mapBifunctor P' Q' F c :=
  HomologicalComplex.mapBifunctorMap f g F c

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a chain map `f : P → P′` and a resolution map
`g : Q → Q′` over `b : B → B′`, the right total augmentations
commute with the induced total map and the one-sided map `F(f,b)`. -/
theorem rightAugmentation_naturality
    {P P' : ChainComplex C₁ ℕ} {B B' : C₂}
    (Q : ProjectiveResolution B) (Q' : ProjectiveResolution B')
    (f : P ⟶ P') (g : Q.complex ⟶ Q'.complex) (b : B ⟶ B')
    (hg : g ≫ Q'.π = Q.π ≫ (ChainComplex.single₀ C₂).map b) :
    totalMap F f g ≫ rightAugmentation F P' Q' =
      rightAugmentation F P Q ≫
        (((F.flip.obj B).mapHomologicalComplex c).map f ≫
          ((NatTrans.mapHomologicalComplex (F.flip.map b) c).app P')) := by
  let G := F.mapBifunctorHomologicalComplex c c
  let s := ChainComplex.single₀ C₂
  have hb : (G.map f).app Q.complex ≫ (G.obj P').map g ≫ (G.obj P').map Q'.π =
      (G.obj P).map Q.π ≫ (G.map f).app (s.obj B) ≫ (G.obj P').map (s.map b) := by
    have hMaps : (G.obj P').map g ≫ (G.obj P').map Q'.π =
        (G.obj P').map Q.π ≫ (G.obj P').map (s.map b) :=
      ((G.obj P').map_comp g Q'.π).symm.trans
        ((congrArg (G.obj P').map hg).trans ((G.obj P').map_comp Q.π (s.map b)))
    have hNatural : (G.map f).app Q.complex ≫ (G.obj P').map Q.π =
        (G.obj P).map Q.π ≫ (G.map f).app (s.obj B) :=
      ((G.map f).naturality Q.π).symm
    calc
      _ = (G.map f).app Q.complex ≫
          ((G.obj P').map Q.π ≫ (G.obj P').map (s.map b)) :=
        congrArg (fun k : (G.obj P').obj Q.complex ⟶ (G.obj P').obj (s.obj B') =>
          (G.map f).app Q.complex ≫ k) hMaps
      _ = ((G.map f).app Q.complex ≫ (G.obj P').map Q.π) ≫
          (G.obj P').map (s.map b) := (Category.assoc _ _ _).symm
      _ = ((G.obj P).map Q.π ≫ (G.map f).app (s.obj B)) ≫
          (G.obj P').map (s.map b) :=
        congrArg (fun k : (G.obj P).obj Q.complex ⟶ (G.obj P').obj (s.obj B) =>
          k ≫ (G.obj P').map (s.map b)) hNatural
      _ = _ := Category.assoc _ _ _
  have ht : HomologicalComplex₂.total.map
        ((G.map f).app Q.complex ≫ (G.obj P').map g) c ≫
        HomologicalComplex₂.total.map ((G.obj P').map Q'.π) c =
      HomologicalComplex₂.total.map ((G.obj P).map Q.π) c ≫
        HomologicalComplex₂.total.map ((G.map f).app (s.obj B)) c ≫
        HomologicalComplex₂.total.map ((G.obj P').map (s.map b)) c := by
    simp only [← HomologicalComplex₂.total.map_comp]
    apply congrArg (fun k => HomologicalComplex₂.total.map k c)
    simpa only [Category.assoc] using hb
  dsimp only [totalMap, HomologicalComplex.mapBifunctorMap, rightAugmentation]
  calc
    _ = (HomologicalComplex₂.total.map
        ((G.map f).app Q.complex ≫ (G.obj P').map g) c ≫
        HomologicalComplex₂.total.map ((G.obj P').map Q'.π) c) ≫
          (singleRightTotalIso F P' B').hom := (Category.assoc _ _ _).symm
    _ = (HomologicalComplex₂.total.map ((G.obj P).map Q.π) c ≫
        HomologicalComplex₂.total.map ((G.map f).app (s.obj B)) c ≫
        HomologicalComplex₂.total.map ((G.obj P').map (s.map b)) c) ≫
          (singleRightTotalIso F P' B').hom :=
      congrArg (fun k => k ≫ (singleRightTotalIso F P' B').hom) ht
    _ = _ := by
      let T₀ := HomologicalComplex.mapBifunctor P Q.complex F c
      let T₁ := HomologicalComplex.mapBifunctor P (s.obj B) F c
      let T₂ := HomologicalComplex.mapBifunctor P' (s.obj B) F c
      let T₃ := HomologicalComplex.mapBifunctor P' (s.obj B') F c
      let L₁ := ((F.flip.obj B).mapHomologicalComplex c).obj P
      let L₂ := ((F.flip.obj B).mapHomologicalComplex c).obj P'
      let L₃ := ((F.flip.obj B').mapHomologicalComplex c).obj P'
      let u : T₀ ⟶ T₁ := HomologicalComplex₂.total.map ((G.obj P).map Q.π) c
      let v : T₁ ⟶ T₂ := HomologicalComplex₂.total.map ((G.map f).app (s.obj B)) c
      let w : T₂ ⟶ T₃ := HomologicalComplex₂.total.map ((G.obj P').map (s.map b)) c
      let e₁ : T₁ ≅ L₁ := singleRightTotalIso F P B
      let e₂ : T₂ ≅ L₂ := singleRightTotalIso F P' B
      let e₃ : T₃ ≅ L₃ := singleRightTotalIso F P' B'
      let l : L₁ ⟶ L₂ := ((F.flip.obj B).mapHomologicalComplex c).map f
      let r : L₂ ⟶ L₃ := (NatTrans.mapHomologicalComplex (F.flip.map b) c).app P'
      have hLeft : v ≫ e₂.hom = e₁.hom ≫ l :=
        singleRightTotalIso_hom_naturality_left F f B
      have hRight : w ≫ e₃.hom = e₂.hom ≫ r :=
        singleRightTotalIso_hom_naturality_right F P' b
      change (u ≫ v ≫ w) ≫ e₃.hom = (u ≫ e₁.hom) ≫ (l ≫ r)
      calc
        _ = u ≫ v ≫ (w ≫ e₃.hom) := by simp only [Category.assoc]
        _ = u ≫ v ≫ (e₂.hom ≫ r) :=
          congrArg (fun k : T₂ ⟶ L₃ => u ≫ v ≫ k) hRight
        _ = u ≫ (v ≫ e₂.hom) ≫ r := by simp only [Category.assoc]
        _ = u ≫ (e₁.hom ≫ l) ≫ r :=
          congrArg (fun k : T₁ ⟶ L₂ => u ≫ k ≫ r) hLeft
        _ = _ := by simp only [Category.assoc]

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. If `F(X,-)` preserves homology for every projective `X`,
then for projective resolutions `P,Q` of arbitrary `A,B`, the right
augmentation `Tot(F(P,Q)) → F(P,B)` is a quasi-isomorphism. -/
theorem rightAugmentation_quasiIso
    (hF : ∀ (X : C₁), Projective X → (F.obj X).PreservesHomology)
    {A : C₁} {B : C₂} (P : ProjectiveResolution A) (Q : ProjectiveResolution B) :
    QuasiIso (rightAugmentation F P.complex Q) := by
  let φ := ((F.mapBifunctorHomologicalComplex c c).obj P.complex).map Q.π
  have hφ (p : ℕ) : QuasiIso (φ.f p) := by
    let : (F.obj (P.complex.X p)).PreservesHomology :=
      hF (P.complex.X p) (P.projective p)
    change QuasiIso (((F.obj (P.complex.X p)).mapHomologicalComplex c).map Q.π)
    infer_instance
  let : QuasiIso (HomologicalComplex₂.total.map φ c) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant φ hφ
  change QuasiIso (HomologicalComplex₂.total.map φ c ≫
    (singleRightTotalIso F P.complex B).hom)
  infer_instance

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a projective resolution `P` of `A` and chain complex
`Q` in `C₂`, the signed flip followed by the corresponding right
augmentation for `F.flip` gives `Tot(F(P,Q)) → F(A,Q)`. -/
def leftAugmentation {A : C₁} (P : ProjectiveResolution A) (Q : ChainComplex C₂ ℕ) :
    HomologicalComplex.mapBifunctor P.complex Q F c ⟶
      ((F.obj A).mapHomologicalComplex c).obj Q :=
  (HomologicalComplex.mapBifunctorFlipIso P.complex Q F c).inv ≫
    rightAugmentation F.flip Q P

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a projective resolution `P` of `A` and chain complex `Q`,
the left augmentation on the `(0,q)` summand is the map
`F(P₀,Q_q) → F(A,Q_q)` induced by `π_P,₀`; its flip sign is one. -/
theorem ι_leftAugmentation {A : C₁} (P : ProjectiveResolution A)
    (Q : ChainComplex C₂ ℕ) (q : ℕ) :
    HomologicalComplex.ιMapBifunctor P.complex Q F c 0 q q (Nat.zero_add q) ≫
        (leftAugmentation F P Q).f q = (F.map (P.π.f 0)).app (Q.X q) := by
  have hs : ComplexShape.σ c c c 0 q = 1 := by
    change (-1 : ℤˣ) ^ (0 * q) = 1
    simp only [Nat.zero_mul, pow_zero]
  dsimp only [leftAugmentation, HomologicalComplex.comp_f]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_inv, hs, one_smul,
    ι_rightAugmentation]
  rfl

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a projective resolution `P` of `A` and chain complex `Q`,
the left augmentation vanishes on every summand `F(P_p,Q_q)` with
`p>0` and total degree `p+q`. -/
theorem ι_leftAugmentation_succ {A : C₁} (P : ProjectiveResolution A)
    (Q : ChainComplex C₂ ℕ) (p q n : ℕ) (h : (p + 1) + q = n) :
    HomologicalComplex.ιMapBifunctor P.complex Q F c (p + 1) q n h ≫
        (leftAugmentation F P Q).f n = 0 := by
  dsimp only [leftAugmentation, HomologicalComplex.comp_f]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_inv,
    Linear.units_smul_comp, ι_rightAugmentation_succ]
  exact smul_zero _

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. The total map induced by `f : P → P′`, `g : Q → Q′`
commutes with the signed flip to the total for `F.flip`, exchanging
the order of the two chain maps. -/
theorem totalMap_comp_flip_inv
    {P P' : ChainComplex C₁ ℕ} {Q Q' : ChainComplex C₂ ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    totalMap F f g ≫ (HomologicalComplex.mapBifunctorFlipIso P' Q' F c).inv =
      (HomologicalComplex.mapBifunctorFlipIso P Q F c).inv ≫ totalMap F.flip g f := by
  rw [← cancel_mono (HomologicalComplex.mapBifunctorFlipIso P' Q' F c).hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc]
  dsimp only [totalMap]
  rw [HomologicalComplex.mapBifunctorFlipIso_hom_naturality,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. For a resolution map `f : P → P′` over `a : A → A′`
and a chain map `g : Q → Q′`, the left total augmentations commute
with the induced total map and the one-sided map `F(a,g)`. -/
theorem leftAugmentation_naturality
    {A A' : C₁} (P : ProjectiveResolution A) (P' : ProjectiveResolution A')
    {Q Q' : ChainComplex C₂ ℕ} (f : P.complex ⟶ P'.complex) (g : Q ⟶ Q')
    (a : A ⟶ A')
    (hf : f ≫ P'.π = P.π ≫ (ChainComplex.single₀ C₁).map a) :
    totalMap F f g ≫ leftAugmentation F P' Q' =
      leftAugmentation F P Q ≫
        (((F.obj A).mapHomologicalComplex c).map g ≫
          ((NatTrans.mapHomologicalComplex (F.map a) c).app Q')) := by
  dsimp only [leftAugmentation]
  rw [← Category.assoc, totalMap_comp_flip_inv, Category.assoc,
    rightAugmentation_naturality F.flip P P' g f a hf, ← Category.assoc]
  simp only [CategoryTheory.Functor.flip_flip]

/-- Let `C₁,C₂,D` be abelian and `F : C₁ → C₂ → D` additive
in both variables. If `F(-,Y)` preserves homology for every projective `Y`,
then for projective resolutions `P,Q` of arbitrary `A,B`, the left
augmentation `Tot(F(P,Q)) → F(A,Q)` is a quasi-isomorphism. -/
theorem leftAugmentation_quasiIso
    (hF : ∀ (Y : C₂), Projective Y → (F.flip.obj Y).PreservesHomology)
    {A : C₁} {B : C₂} (P : ProjectiveResolution A) (Q : ProjectiveResolution B) :
    QuasiIso (leftAugmentation F P Q.complex) := by
  let : QuasiIso (rightAugmentation F.flip Q.complex P) :=
    rightAugmentation_quasiIso F.flip hF Q P
  change QuasiIso ((HomologicalComplex.mapBifunctorFlipIso P.complex Q.complex F c).inv ≫
    rightAugmentation F.flip Q.complex P)
  infer_instance

end CategoryTheory.Functor.LeftDerivedBalance
