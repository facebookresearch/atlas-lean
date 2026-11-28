/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ExactPrecomposition
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ExactPostcomposition
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.CompositionNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ZeroNaturality
public import MathlibExt.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Left-derived maps of homology-preserving comparison squares

Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`.
For additive homology-preserving `U : D → C`, `V : E′ → E`, additive
`F : C → E`, `G : D → E′`, and a transformation
`α : U ⋙ F → G ⋙ V`, there is a canonical derived square
`U ⋙ L_nF → L_nG ⋙ V`. It is computed from a projective resolution
in `D` and a comparison into its exact image in `C`; `U` need not
preserve projectives. Its degree-zero augmentation and coefficient
naturality squares retain the underlying maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits


universe uC vC uD vD uE vE uE' vE'

namespace HomologicalComplex

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {ι : Type uD} {c : ComplexShape ι}

/-- In an abelian category `C`, for any complex shape `c`, complex
`K : HomologicalComplex C c`, and index `i`, the homology-preservation
comparison for the identity functor has identity forward component
on `H_i(K)`. -/
theorem mapHomologyFunctorIso_id_hom (K : HomologicalComplex C c) (i : ι) :
    letI : (𝟭 C).PreservesHomology := Functor.preservesHomologyOfExact (𝟭 C)
    (mapHomologyFunctorIso (c := c) i (𝟭 C)).hom.app K = 𝟙 _ := by
  let : (𝟭 C).PreservesHomology := Functor.preservesHomologyOfExact (𝟭 C)
  let e := (mapHomologyFunctorIso (c := c) i (𝟭 C)).hom.app K
  have h : e = e ≫ e := by
    exact ShortComplex.mapHomologyIso_comp_hom (K.sc i) (𝟭 C) (𝟭 C)
  apply (cancel_epi e).1
  exact h.symm.trans (Category.comp_id e).symm

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {E' : Type uE'} [Category.{vE'} E'] [Abelian E']
  (U : D ⥤ C) [U.Additive] (V : E' ⥤ E) [V.Additive]
  (F : C ⥤ E) [F.Additive] (G : D ⥤ E') [G.Additive]
  (α : U ⋙ F ⟶ G ⋙ V)

/-- Let `C,D,E,E′` be abelian, `U : D → C`, `V : E′ → E`,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`.
Applying the natural transformation degreewise gives a comparison
`F(U(Q)) → V(G(Q))` for every nonnegative chain complex `Q` in `D`,
using the natural composition identifications. -/
def mapSquareHomologicalComplex :
    U.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        F.mapHomologicalComplex (ComplexShape.down ℕ) ⟶
      G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        V.mapHomologicalComplex (ComplexShape.down ℕ) :=
  (Functor.mapHomologicalComplexCompIso (F := U) (G := F)
      (Iso.refl (U ⋙ F)) (ComplexShape.down ℕ)).hom ≫
    NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ) ≫
    (Functor.mapHomologicalComplexCompIso (F := G) (G := V)
      (Iso.refl (G ⋙ V)) (ComplexShape.down ℕ)).inv

/-- Let `C,D,E,E′` be abelian, `U : D → C`, `V : E′ → E`,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`.
For a chain complex `Q` in `D`, the degree-`i` component of its
induced complex comparison is `α_(Q_i)`. -/
theorem mapSquareHomologicalComplex_f (Q : ChainComplex D ℕ) (i : ℕ) :
    ((mapSquareHomologicalComplex U V F G α).app Q).f i = α.app (Q.X i) := by
  change (𝟙 _) ≫ α.app (Q.X i) ≫ (𝟙 _) = α.app (Q.X i)
  simp only [Category.id_comp, Category.comp_id]

section Derived

variable [HasProjectiveResolutions C] [HasProjectiveResolutions D]
  [U.PreservesHomology] [V.PreservesHomology]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. Directional source comparison,
derivation of `α`, and
inverse target postcomposition give the natural map
`U ⋙ L_nF → L_nG ⋙ V`. -/
def leftDerivedSquareHom (n : ℕ) :
    U ⋙ F.leftDerived n ⟶ G.leftDerived n ⋙ V :=
  leftDerivedPrecompHomOfPreservesHomology U F n ≫ NatTrans.leftDerived α n ≫
    (G.leftDerivedCompIsoOfPreservesHomology V n).inv

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. A supplied projective resolution `Q` of
`X : D` computes
its component `L_nF(U(X)) → V(L_nG(X))` through a projective
resolution of `U(X)` mapping into `U(Q)`. -/
def leftDerivedSquareHomWithResolution (n : ℕ) {X : D} (Q : ProjectiveResolution X) :
    (F.leftDerived n).obj (U.obj X) ⟶ V.obj ((G.leftDerived n).obj X) := by
  let ρ := mapChainAugmentation U Q.π
  letI : QuasiIso ρ := mapChainAugmentation_quasiIso U Q.π
  let K := (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  exact leftDerivedObjToAugmentedHom F
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
      ρ (𝟙 (U.obj X)) n ≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).map
      ((mapSquareHomologicalComplex U V F G α).app Q.complex) ≫
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app K ≫
    V.map (Q.isoLeftDerivedObj G n).inv

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. For `f : X → Y` and projective
resolutions of `X,Y`, the
computed components commute with `L_nF(U(f))` and `V(L_nG(f))`. -/
theorem leftDerivedSquareHomWithResolution_naturality (n : ℕ)
    {X Y : D} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (F.leftDerived n).map (U.map f) ≫ leftDerivedSquareHomWithResolution U V F G α n Q =
      leftDerivedSquareHomWithResolution U V F G α n P ≫ V.map ((G.leftDerived n).map f) := by
  let a := ProjectiveResolution.lift f P Q
  let b := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map a
  let ρP := mapChainAugmentation U P.π
  let ρQ := mapChainAugmentation U Q.π
  let : QuasiIso ρP := mapChainAugmentation_quasiIso U P.π
  let : QuasiIso ρQ := mapChainAugmentation_quasiIso U Q.π
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let H' := HomologicalComplex.homologyFunctor E' (ComplexShape.down ℕ) n
  let tP := leftDerivedObjToAugmentedHom F
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ρP (𝟙 (U.obj X)) n
  let tQ := leftDerivedObjToAugmentedHom F
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ (𝟙 (U.obj Y)) n
  let mP := (mapSquareHomologicalComplex U V F G α).app P.complex
  let mQ := (mapSquareHomologicalComplex U V F G α).app Q.complex
  let g := (G.mapHomologicalComplex (ComplexShape.down ℕ)).map a
  let e := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V
  have hρ : b ≫ ρQ = ρP ≫ (ChainComplex.single₀ C).map (U.map f) :=
    mapChainAugmentation_naturality U P.π Q.π f a (ProjectiveResolution.lift_commutes f P Q)
  have h₁ : (F.leftDerived n).map (U.map f) ≫ tQ =
      tP ≫ H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map b) := by
    have hSource := leftDerivedObjToAugmentedHom_naturality_source F
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ
      (U.map f) (𝟙 (U.obj Y)) n
    have hTarget := leftDerivedObjToAugmentedHom_naturality_target F ρP ρQ
      (𝟙 (U.obj X)) (U.map f) b hρ n
    have hS : (F.leftDerived n).map (U.map f) ≫ tQ =
        leftDerivedObjToAugmentedHom F
          ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ (U.map f) n := by
      simpa only [tQ, Category.comp_id] using hSource
    have hT : leftDerivedObjToAugmentedHom F
          ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ (U.map f) n =
        tP ≫ H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map b) := by
      simpa only [tP, H, Functor.comp_map, Category.id_comp] using hTarget.symm
    exact hS.trans hT
  have h₂ : H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map b) ≫ H.map mQ =
      H.map mP ≫ H.map ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map g) := by
    simpa only [b, g, mP, mQ, Functor.comp_map, Functor.map_comp] using
      congrArg H.map ((mapSquareHomologicalComplex U V F G α).naturality a)
  have h₃ : H.map ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map g) ≫
      e.hom.app ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) =
    e.hom.app ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
      V.map (H'.map g) := e.hom.naturality g
  have h₄ : V.map (P.isoLeftDerivedObj G n).inv ≫ V.map ((G.leftDerived n).map f) =
      V.map (H'.map g) ≫ V.map (Q.isoLeftDerivedObj G n).inv := by
    have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality f P Q a
      (ProjectiveResolution.lift_commutes_zero f P Q) G n
    simpa only [H', g, Functor.comp_map, Functor.map_comp] using congrArg V.map h
  have s₁ : CommSq tP ((F.leftDerived n).map (U.map f))
      (H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map b)) tQ := ⟨h₁.symm⟩
  have s₂ : CommSq (H.map mP)
      (H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map b))
      (H.map ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map g)) (H.map mQ) := ⟨h₂.symm⟩
  have s₃ : CommSq (e.hom.app
      ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))
      (H.map ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map g)) (V.map (H'.map g))
      (e.hom.app ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)) := ⟨h₃.symm⟩
  have s₄ : CommSq (V.map (P.isoLeftDerivedObj G n).inv) (V.map (H'.map g))
      (V.map ((G.leftDerived n).map f)) (V.map (Q.isoLeftDerivedObj G n).inv) := ⟨h₄⟩
  change (F.leftDerived n).map (U.map f) ≫
      (tQ ≫ H.map mQ ≫ e.hom.app
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≫
          V.map (Q.isoLeftDerivedObj G n).inv) =
    (tP ≫ H.map mP ≫ e.hom.app
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
          V.map (P.isoLeftDerivedObj G n).inv) ≫ V.map ((G.leftDerived n).map f)
  exact (s₁.horiz_comp (s₂.horiz_comp (s₃.horiz_comp s₄))).w.symm

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. Any two projective resolutions of `X :
D` compute the
same component `L_nF(U(X)) → V(L_nG(X))`. -/
theorem leftDerivedSquareHomWithResolution_independent (n : ℕ) {X : D}
    (P Q : ProjectiveResolution X) :
    leftDerivedSquareHomWithResolution U V F G α n P =
      leftDerivedSquareHomWithResolution U V F G α n Q := by
  have h := leftDerivedSquareHomWithResolution_naturality U V F G α n (𝟙 X) P Q
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

private theorem exactPostcomp_inv_canonical (n : ℕ) (X : D) :
    (G.leftDerivedCompIsoOfPreservesHomology V n).inv.app X =
      ((projectiveResolution X).isoLeftDerivedObj (G ⋙ V) n).hom ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj (projectiveResolution X).complex) ≫
        V.map ((projectiveResolution X).isoLeftDerivedObj G n).inv := by
  dsimp only [leftDerivedCompIsoOfPreservesHomology, NatIso.ofComponents,
    Iso.app, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Category.assoc]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. At `X : D`, the canonical square
component is the component
computed using the chosen projective resolution of `X`. -/
theorem leftDerivedSquareHom_app_canonical (n : ℕ) (X : D) :
    (leftDerivedSquareHom U V F G α n).app X =
      leftDerivedSquareHomWithResolution U V F G α n (projectiveResolution X) := by
  let Q := projectiveResolution X
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let χUF := Functor.mapHomologicalComplexCompIso (F := U) (G := F)
    (Iso.refl (U ⋙ F)) (ComplexShape.down ℕ)
  let χGV := Functor.mapHomologicalComplexCompIso (F := G) (G := V)
    (Iso.refl (G ⋙ V)) (ComplexShape.down ℕ)
  have hχ : χGV.inv.app Q.complex = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  dsimp only [Q, χGV] at hχ
  unfold leftDerivedSquareHom
  rw [NatTrans.comp_app, NatTrans.comp_app,
    leftDerivedPrecompHomOfPreservesHomology_app U F n Q,
    ProjectiveResolution.leftDerived_app_eq α Q n,
    exactPostcomp_inv_canonical (V := V) (G := G) n X]
  unfold leftDerivedPrecompHomWithResolution leftDerivedSquareHomWithResolution
  unfold mapSquareHomologicalComplex
  dsimp only [Q]
  simp only [NatTrans.comp_app, Functor.map_comp, hχ,
    Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. At `X : D`, every supplied projective
resolution `Q` of `X`
computes the same canonical square component. -/
theorem leftDerivedSquareHom_app (n : ℕ) {X : D} (Q : ProjectiveResolution X) :
    (leftDerivedSquareHom U V F G α n).app X =
      leftDerivedSquareHomWithResolution U V F G α n Q :=
  (leftDerivedSquareHom_app_canonical U V F G α n X).trans
    (leftDerivedSquareHomWithResolution_independent U V F G α n (projectiveResolution X) Q)

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. For a resolution `Q` of `X : D`, a
resolution `P` of `U(X)`,
and any augmentation-preserving map `P → U(Q)`, the square component
is the comparison to `H_n(F(P))`, its mapped complex-square map,
homology preservation by `V`, and the inverse resolution comparison
for `G(Q)`, in that order. -/
theorem leftDerivedSquareHom_eq_with_lift (n : ℕ) {X : D}
    (Q : ProjectiveResolution X) (P : ProjectiveResolution (U.obj X))
    (a : P.complex ⟶ (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
    (ha : a ≫ mapChainAugmentation U Q.π = P.π) :
    (leftDerivedSquareHom U V F G α n).app X =
      (P.isoLeftDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a ≫
            (mapSquareHomologicalComplex U V F G α).app Q.complex) n ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≫
        V.map (Q.isoLeftDerivedObj G n).inv := by
  let : QuasiIso (mapChainAugmentation U Q.π) := mapChainAugmentation_quasiIso U Q.π
  rw [leftDerivedSquareHom_app U V F G α n Q]
  unfold leftDerivedSquareHomWithResolution
  dsimp only
  rw [leftDerivedObjToAugmentedHom_eq F P
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
    (mapChainAugmentation U Q.π) (𝟙 (U.obj X)) a
    (by simpa only [Functor.map_id, Category.comp_id] using ha) n]
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  change ((P.isoLeftDerivedObj F n).hom ≫
      H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a)) ≫
      H.map ((mapSquareHomologicalComplex U V F G α).app Q.complex) ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≫
      V.map (Q.isoLeftDerivedObj G n).inv =
    (P.isoLeftDerivedObj F n).hom ≫
      H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a ≫
        (mapSquareHomologicalComplex U V F G α).app Q.complex) ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≫
      V.map (Q.isoLeftDerivedObj G n).inv
  simp only [Functor.map_comp, Category.assoc]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. For `f : X → U(Y)`, resolutions `P` of
`X : C`, `Q` of
`Y : D`, and a map `P → U(Q)` over `f`, the map `L_nF(f)` followed
by the square component at `Y` is computed by that lift, the mapped
coefficient square, target homology preservation, and resolution
comparisons. -/
theorem leftDerivedSquareHom_eq_with_source_lift (n : ℕ) {X : C} {Y : D}
    (f : X ⟶ U.obj Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (a : P.complex ⟶ (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
    (ha : a ≫ mapChainAugmentation U Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived n).map f ≫ (leftDerivedSquareHom U V F G α n).app Y =
      (P.isoLeftDerivedObj F n).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a ≫
            (mapSquareHomologicalComplex U V F G α).app Q.complex) n ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≫
        V.map (Q.isoLeftDerivedObj G n).inv := by
  let ρ := mapChainAugmentation U Q.π
  let : QuasiIso ρ := mapChainAugmentation_quasiIso U Q.π
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  rw [leftDerivedSquareHom_app U V F G α n Q]
  unfold leftDerivedSquareHomWithResolution
  rw [← Category.assoc ((F.leftDerived n).map f),
    leftDerivedObjToAugmentedHom_naturality_source F
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
      ρ f (𝟙 (U.obj Y)) n, Category.comp_id]
  rw [leftDerivedObjToAugmentedHom_eq F P
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρ f a ha n]
  change ((P.isoLeftDerivedObj F n).hom ≫
      H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a)) ≫
      H.map ((mapSquareHomologicalComplex U V F G α).app Q.complex) ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≫
      V.map (Q.isoLeftDerivedObj G n).inv =
    (P.isoLeftDerivedObj F n).hom ≫
      H.map ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a ≫
        (mapSquareHomologicalComplex U V F G α).app Q.complex) ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ≫
      V.map (Q.isoLeftDerivedObj G n).inv
  simp only [Functor.map_comp, Category.assoc]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. The degree-zero square followed by `L₀G
⋙ V → G ⋙ V`
equals `U ⋙ L₀F → U ⋙ F` followed by `α`. -/
theorem leftDerivedSquareHom_zero_augmentation :
    leftDerivedSquareHom U V F G α 0 ≫ whiskerRight G.fromLeftDerivedZero V =
      whiskerLeft U F.fromLeftDerivedZero ≫ α := by
  unfold leftDerivedSquareHom
  simp only [Category.assoc]
  rw [G.leftDerivedCompIsoOfPreservesHomology_inv_fromLeftDerivedZero V,
    NatTrans.fromLeftDerivedZero_naturality_functor α,
    ← Category.assoc, leftDerivedPrecompHomOfPreservesHomology_zero_augmentation U F]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. If `U` preserves projectives, the
square is inverse source
precomposition followed by `L_nα` and inverse target postcomposition. -/
theorem leftDerivedSquareHom_of_preservesProjectives [U.PreservesProjectiveObjects] (n : ℕ) :
    leftDerivedSquareHom U V F G α n =
      (leftDerivedPrecompIso U F n).inv ≫ NatTrans.leftDerived α n ≫
        (G.leftDerivedCompIsoOfPreservesHomology V n).inv := by
  unfold leftDerivedSquareHom
  rw [leftDerivedPrecompHomOfPreservesHomology_eq_inv U F n]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. For additive `F′ : C → E` and `δ : F′ →
F`, precomposing
the derived square with `U ⋙ L_nδ` gives the square associated to
`(U ⋙ δ) ≫ α`. -/
theorem leftDerivedSquareHom_naturality_source_functor
    {F' : C ⥤ E} [F'.Additive] (δ : F' ⟶ F) (n : ℕ) :
    whiskerLeft U (NatTrans.leftDerived δ n) ≫ leftDerivedSquareHom U V F G α n =
      leftDerivedSquareHom U V F' G (whiskerLeft U δ ≫ α) n := by
  unfold leftDerivedSquareHom
  rw [← Category.assoc (whiskerLeft U (NatTrans.leftDerived δ n)),
    leftDerivedPrecompHomOfPreservesHomology_naturality_functor U F' δ n]
  simp only [Category.assoc]
  rw [← Category.assoc (NatTrans.leftDerived (whiskerLeft U δ) n),
    ← NatTrans.leftDerived_comp]

/-- Let `C,D,E,E′` be abelian, with projective resolutions in `C,D`,
`U : D → C`, `V : E′ → E` additive and preserving homology,
`F : C → E`, `G : D → E′` additive, and `α : U ⋙ F → G ⋙ V`. For additive `G′ : D → E′` and `γ : G →
G′`, following
the derived square by `L_nγ ⋙ V` gives the square associated to
`α ≫ (γ ⋙ V)`. -/
theorem leftDerivedSquareHom_naturality_target_functor
    {G' : D ⥤ E'} [G'.Additive] (γ : G ⟶ G') (n : ℕ) :
    leftDerivedSquareHom U V F G α n ≫ whiskerRight (NatTrans.leftDerived γ n) V =
      leftDerivedSquareHom U V F G' (α ≫ whiskerRight γ V) n := by
  have hInv : (G.leftDerivedCompIsoOfPreservesHomology V n).inv ≫
      whiskerRight (NatTrans.leftDerived γ n) V =
    NatTrans.leftDerived (whiskerRight γ V) n ≫
      (G'.leftDerivedCompIsoOfPreservesHomology V n).inv := by
    apply (cancel_mono (G'.leftDerivedCompIsoOfPreservesHomology V n).hom).1
    simp only [Category.assoc]
    rw [leftDerivedCompIsoOfPreservesHomology_hom_naturality_functor γ V n]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  unfold leftDerivedSquareHom
  simp only [Category.assoc]
  rw [hInv, ← Category.assoc (NatTrans.leftDerived α n), ← NatTrans.leftDerived_comp]

end Derived

end CategoryTheory.Functor

namespace HomologicalComplex

variable {A : Type uC} [Category.{vC} A] [Abelian A]
  {B : Type uD} [Category.{vD} B] [Abelian B]
  {C : Type uE} [Category.{vE} C] [Abelian C]

/-- Let `A,B,C` be abelian, `V : B → A`, `V′ : C → B`,
`W : C → A` additive and preserving homology, and `e : V′ ⋙ V ≅ W`.
For chain maps `d : P → V(Q)`, `d′ : Q → V′(T)` and presentations
`X ≅ H_n(P)`, `Y ≅ H_n(Q)`, `Z ≅ H_n(T)`, composing their presented
homology comparisons and `e_Z` equals the presented comparison of
`P → V(Q) → V(V′(T)) → W(T)`. -/
theorem comparisonHom_comp
    (V : B ⥤ A) [V.Additive] [V.PreservesHomology]
    (V' : C ⥤ B) [V'.Additive] [V'.PreservesHomology]
    (W : C ⥤ A) [W.Additive] [W.PreservesHomology] (e : V' ⋙ V ≅ W)
    (n : ℕ) (P : ChainComplex A ℕ) (Q : ChainComplex B ℕ) (T : ChainComplex C ℕ)
    (d : P ⟶ (V.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q)
    (d' : Q ⟶ (V'.mapHomologicalComplex (ComplexShape.down ℕ)).obj T)
    {X : A} {Y : B} {Z : C} (eP : X ≅ P.homology n) (eQ : Y ≅ Q.homology n)
    (eT : Z ≅ T.homology n) :
    (eP.hom ≫ homologyMap d n ≫
        (mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app Q ≫ V.map eQ.inv) ≫
      V.map (eQ.hom ≫ homologyMap d' n ≫
        (mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V').hom.app T ≫ V'.map eT.inv) ≫
      e.hom.app Z =
    eP.hom ≫ homologyMap
        (d ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map d' ≫
          (Functor.mapHomologicalComplexCompIso (F := V') (G := V) e
            (ComplexShape.down ℕ)).hom.app T) n ≫
      (mapHomologyFunctorIso (c := ComplexShape.down ℕ) n W).hom.app T ≫ W.map eT.inv := by
  let H := homologyFunctor A (ComplexShape.down ℕ) n
  let H' := homologyFunctor B (ComplexShape.down ℕ) n
  let H'' := homologyFunctor C (ComplexShape.down ℕ) n
  let K := (V'.mapHomologicalComplex (ComplexShape.down ℕ)).obj T
  let χ := Functor.mapHomologicalComplexCompIso (F := V') (G := V) e (ComplexShape.down ℕ)
  let : PreservesFiniteLimits V := Functor.preservesFiniteLimits_of_preservesHomology V
  let : PreservesFiniteColimits V := Functor.preservesFiniteColimits_of_preservesHomology V
  let : PreservesFiniteLimits V' := Functor.preservesFiniteLimits_of_preservesHomology V'
  let : PreservesFiniteColimits V' := Functor.preservesFiniteColimits_of_preservesHomology V'
  let : (V' ⋙ V).PreservesHomology := Functor.preservesHomologyOfExact (V' ⋙ V)
  let mV := mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V
  let mV' := mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V'
  let mVV := mapHomologyFunctorIso (c := ComplexShape.down ℕ) n (V' ⋙ V)
  let mW := mapHomologyFunctorIso (c := ComplexShape.down ℕ) n W
  have hNat : H.map ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map d') ≫
      mV.hom.app K = mV.hom.app Q ≫ V.map (H'.map d') := mV.hom.naturality d'
  have hComp : mV.hom.app K ≫ V.map (mV'.hom.app T) = mVV.hom.app T := by
    exact (ShortComplex.mapHomologyIso_comp_hom (T.sc n) V' V).symm
  have hE : H.map (χ.hom.app T) ≫ mW.hom.app T =
      mVV.hom.app T ≫ e.hom.app (H''.obj T) :=
    mapHomologyFunctorIso_naturality_transformation T n (V' ⋙ V) W e.hom
  have hLast : (V' ⋙ V).map eT.inv ≫ e.hom.app Z =
      e.hom.app (H''.obj T) ≫ W.map eT.inv := e.hom.naturality eT.inv
  change (eP.hom ≫ H.map d ≫ mV.hom.app Q ≫ V.map eQ.inv) ≫
      V.map (eQ.hom ≫ H'.map d' ≫ mV'.hom.app T ≫ V'.map eT.inv) ≫ e.hom.app Z =
    eP.hom ≫ H.map (d ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map d' ≫
      χ.hom.app T) ≫ mW.hom.app T ≫ W.map eT.inv
  have cancelTriple {P Q R S T : A} (f : P ⟶ Q) (g : Q ⟶ R)
      (e : S ≅ R) (h : R ⟶ T) :
      (f ≫ g ≫ e.inv) ≫ (e.hom ≫ h) = f ≫ g ≫ h := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc
    _ = eP.hom ≫ H.map d ≫ mV.hom.app Q ≫ V.map (H'.map d') ≫
        V.map (mV'.hom.app T) ≫ (V' ⋙ V).map eT.inv ≫ e.hom.app Z := by
      simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv,
        Functor.comp_map, Category.assoc] using
        cancelTriple eP.hom (H.map d ≫ mV.hom.app Q) (V.mapIso eQ)
          (V.map (H'.map d' ≫ mV'.hom.app T ≫ V'.map eT.inv) ≫ e.hom.app Z)
    _ = eP.hom ≫ H.map d ≫
        H.map ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map d') ≫ mV.hom.app K ≫
        V.map (mV'.hom.app T) ≫ (V' ⋙ V).map eT.inv ≫ e.hom.app Z := by
      rw [← Category.assoc (mV.hom.app Q), ← hNat]
      simp only [Category.assoc]
    _ = eP.hom ≫ H.map (d ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map d') ≫
        mVV.hom.app T ≫ (V' ⋙ V).map eT.inv ≫ e.hom.app Z := by
      rw [← Category.assoc (mV.hom.app K), hComp]
      simpa only [Category.assoc] using
        congrArg (fun z => eP.hom ≫ z ≫ mVV.hom.app T ≫
          (V' ⋙ V).map eT.inv ≫ e.hom.app Z)
          (H.map_comp d ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map d')).symm
    _ = eP.hom ≫ H.map (d ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map d') ≫
        mVV.hom.app T ≫ e.hom.app (H''.obj T) ≫ W.map eT.inv := by
      simpa only [Category.assoc] using
        congrArg (fun z => eP.hom ≫
          H.map (d ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map d') ≫
            mVV.hom.app T ≫ z) hLast
    _ = eP.hom ≫ H.map (d ≫ (V.mapHomologicalComplex (ComplexShape.down ℕ)).map d') ≫
        H.map (χ.hom.app T) ≫ mW.hom.app T ≫ W.map eT.inv := by
      rw [← Category.assoc (mVV.hom.app T), ← hE]
      simp only [Category.assoc]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

end HomologicalComplex
