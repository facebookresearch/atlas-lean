/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerivedBifunctor
public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/- Proof implementation note.
# Exact coefficient colimits for a left-derived bifunctor

One projective resolution of the first variable computes the existing left-derived bifunctor
naturally in its second variable. Colimit preservation of the original degreewise functors,
followed by exact homology colimits, gives the canonical all-degree comparison. Only the first
category needs projective resolutions.
-/

/-!
# Colimits in coefficients of a left-derived bifunctor

Let `C₁`, `D` be abelian, `C₂` a category, and the partial functors
`F(-,B)` additive. A fixed projective resolution in `C₁` computes
all coefficients at once. If the coefficient functors on projective
terms preserve `J`-colimits and those colimits in `D` preserve
homology, every left-derived degree preserves the same coefficient colimits.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ w w'

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [∀ B : C₂, (F.flip.obj B).Additive]

/- Proof implementation note.
The original bifunctor applied to a fixed complex in its first variable. Coefficient maps are the
maps of homological complexes.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. For a chain complex `P` in `C₁`, the coefficient
complex functor sends `B` to the mapped chain complex `F(P,B)`
and sends each coefficient map to its degreewise natural map. -/
def coefficientComplexFunctor (P : ChainComplex C₁ ℕ) : C₂ ⥤ ChainComplex D ℕ where
  obj B := ((F.flip.obj B).mapHomologicalComplex (ComplexShape.down ℕ)).obj P
  map b := (NatTrans.mapHomologicalComplex (F.flip.map b) (ComplexShape.down ℕ)).app P
  map_id B := by
    rw [F.flip.map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp {B B' B''} b b' := by
    rw [F.flip.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/- Proof implementation note.
Each component is the coefficient map at the original stage.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. For a chain complex `P` in `C₁`, a map `b : B →
B′`
has degree-`i` component `F(P^i,b)` between its coefficient complexes. -/
theorem coefficientComplexFunctor_map_f (P : ChainComplex C₁ ℕ)
    {B B' : C₂} (b : B ⟶ B') (i : ℕ) :
    ((F.coefficientComplexFunctor P).map b).f i =
      ((F.obj (P.X i)).map b) := rfl

/- Proof implementation note.
Its differential is the original first-variable map of the differential.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. For a chain complex `P` in `C₁`, the differential
of the coefficient complex at `B` is `F(d_P,B)` in each
index pair, retaining the natural-index chain shape. -/
theorem coefficientComplexFunctor_obj_d (P : ChainComplex C₁ ℕ)
    (B : C₂) (i j : ℕ) :
    ((F.coefficientComplexFunctor P).obj B).d i j =
      (F.map (P.d i j)).app B := rfl

/- Proof implementation note.
Evaluation exposes the original stage functor, including its maps.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. For a chain complex `P` in `C₁`, evaluation at
degree `i` of the coefficient complex functor is naturally
isomorphic to `F(P^i,-)`. -/
def coefficientComplexFunctorEvalIso (P : ChainComplex C₁ ℕ) (i : ℕ) :
    F.coefficientComplexFunctor P ⋙
        HomologicalComplex.eval D (ComplexShape.down ℕ) i ≅
      F.obj (P.X i) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro B B' b
    change (F.obj (P.X i)).map b ≫ 𝟙 _ = 𝟙 _ ≫ (F.obj (P.X i)).map b
    rw [Category.comp_id, Category.id_comp])

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. For a chain complex `P` in `C₁`, if each
`F(P^i,-)` preserves colimits of shape `J`, the entire
coefficient complex functor preserves those colimits. -/
theorem coefficientComplexFunctor_preservesColimitsOfShape
    (J : Type w) [Category.{w'} J] (P : ChainComplex C₁ ℕ)
    [∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.X i))] :
    PreservesColimitsOfShape J (F.coefficientComplexFunctor P) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i
  exact preservesColimitsOfShape_of_natIso
    (F.coefficientComplexFunctorEvalIso P i).symm

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. For a chain complex `P` in `C₁`, if `C₂` and `D`
have `J`-colimits and each `F(P^i,-)` preserves them, then
`F(P,colim K) ≅ colim_j F(P,K_j)` canonically for every `K : J → C₂`. -/
def coefficientComplexColimitIso
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J C₂]
    [HasColimitsOfShape J D] (P : ChainComplex C₁ ℕ)
    [∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.X i))]
    (K : J ⥤ C₂) :
    (F.coefficientComplexFunctor P).obj (colimit K) ≅
      colimit (K ⋙ F.coefficientComplexFunctor P) := by
  letI := F.coefficientComplexFunctor_preservesColimitsOfShape J P
  exact preservesColimitIso (F.coefficientComplexFunctor P) K

/- Proof implementation note.
Each original coefficient leg followed by the chain comparison is the chain-colimit injection.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. For a chain complex `P` in `C₁`, under degreewise
preservation of `J`-colimits in `C₂,D`, the map of an
original coefficient injection `K_j → colim K` followed
by the complex comparison is its chain-colimit injection. -/
theorem map_ι_coefficientComplexColimitIso_hom
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J C₂]
    [HasColimitsOfShape J D] (P : ChainComplex C₁ ℕ)
    [∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.X i))]
    (K : J ⥤ C₂) (j : J) :
    (F.coefficientComplexFunctor P).map (colimit.ι K j) ≫
        (F.coefficientComplexColimitIso J P K).hom =
      colimit.ι (K ⋙ F.coefficientComplexFunctor P) j := by
  let := F.coefficientComplexFunctor_preservesColimitsOfShape J P
  exact ι_preservesColimitIso_hom (F.coefficientComplexFunctor P) K j

variable [HasProjectiveResolutions C₁]

/- Proof implementation note.
The fixed-resolution computation of the existing derived bifunctor is natural in its coefficient,
with the original homology objects.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. A
projective
resolution `P` of `A` gives a natural coefficient comparison
`L_nF(A,-) ≅ H_n(F(P,-))`. -/
def leftDerivedBifunctorResolutionIso {A : C₁} (P : ProjectiveResolution A) (n : ℕ) :
    (F.leftDerivedBifunctor n).obj A ≅
      F.coefficientComplexFunctor P.complex ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n :=
  NatIso.ofComponents (fun B => P.isoLeftDerivedObj (F.flip.obj B) n) (by
    intro B B' b
    let H := HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
    let e := P.isoLeftDerivedObj (F.flip.obj B) n
    let e' := P.isoLeftDerivedObj (F.flip.obj B') n
    let t := (NatTrans.mapHomologicalComplex (F.flip.map b)
      (ComplexShape.down ℕ)).app P.complex
    have h : (NatTrans.leftDerived (F.flip.map b) n).app A =
        e.hom ≫ H.map t ≫ e'.inv :=
      ProjectiveResolution.leftDerived_app_eq (F.flip.map b) P n
    change (NatTrans.leftDerived (F.flip.map b) n).app A ≫ e'.hom = e.hom ≫ H.map t
    calc
      _ = (e.hom ≫ H.map t ≫ e'.inv) ≫ e'.hom :=
        congrArg (fun q => q ≫ e'.hom) h
      _ = _ := by rw [Category.assoc, Category.assoc, e'.inv_hom_id, Category.comp_id])

/- Proof implementation note.
Components are the existing projective-resolution comparison, with no
separate choice of an objectwise isomorphism.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. At a
coefficient
object `B`, the forward resolution comparison is the
canonical map `L_n(F(-,B))(A) → H_n(F(P,B))`. -/
theorem leftDerivedBifunctorResolutionIso_hom_app
    {A : C₁} (P : ProjectiveResolution A) (n : ℕ) (B : C₂) :
    (F.leftDerivedBifunctorResolutionIso P n).hom.app B =
      (P.isoLeftDerivedObj (F.flip.obj B) n).hom := rfl

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. At a
coefficient
object `B`, the inverse resolution comparison is the
canonical map `H_n(F(P,B)) → L_n(F(-,B))(A)`. -/
theorem leftDerivedBifunctorResolutionIso_inv_app
    {A : C₁} (P : ProjectiveResolution A) (n : ℕ) (B : C₂) :
    (F.leftDerivedBifunctorResolutionIso P n).inv.app B =
      (P.isoLeftDerivedObj (F.flip.obj B) n).inv := rfl

variable (J : Type w) [Category.{w'} J] [HasColimitsOfShape J D]
  [(colim (J := J) (C := D)).PreservesHomology]

/- Proof implementation note.
Exact target colimits commute with every degree when the original stage functors preserve those
colimits on projective first objects. Only the terms of a first-variable resolution are used.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. If
`D` has
homology-preserving `J`-colimits and each `F(X,-)` for
projective `X` preserves them, then `L_nF(A,-)` preserves
`J`-colimits for every `A,n`. -/
theorem leftDerivedBifunctor_obj_preservesColimitsOfShape_of_projective
    (A : C₁) (n : ℕ)
    (hF : ∀ X : C₁, Projective X → PreservesColimitsOfShape J (F.obj X)) :
    PreservesColimitsOfShape J ((F.leftDerivedBifunctor n).obj A) := by
  let P := projectiveResolution A
  let : ∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.complex.X i)) :=
    fun i => hF (P.complex.X i) (P.projective i)
  let : PreservesColimitsOfShape J (F.coefficientComplexFunctor P.complex) :=
    F.coefficientComplexFunctor_preservesColimitsOfShape J P.complex
  let : PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n) :=
    HomologicalComplex.homologyFunctor_preservesColimitsOfShape n
  exact preservesColimitsOfShape_of_natIso
    (F.leftDerivedBifunctorResolutionIso P n).symm

/- Proof implementation note.
Exact target colimits commute with every degree of the existing
left-derived bifunctor in its coefficient variable.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. If
`D` has
homology-preserving `J`-colimits and each `F(X,-)` preserves
them, then `L_nF(A,-)` preserves `J`-colimits for every `A,n`. -/
theorem leftDerivedBifunctor_obj_preservesColimitsOfShape
    (A : C₁) (n : ℕ) [∀ X : C₁, PreservesColimitsOfShape J (F.obj X)] :
    PreservesColimitsOfShape J ((F.leftDerivedBifunctor n).obj A) := by
  exact F.leftDerivedBifunctor_obj_preservesColimitsOfShape_of_projective
    (J := J) (A := A) (n := n) (hF := fun X _ => inferInstance)

variable [HasColimitsOfShape J C₂] [∀ X : C₁, PreservesColimitsOfShape J (F.obj X)]

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. Let
`J` be a diagram category with colimits in `C₂` and `D`,
and suppose the colimit functor on `J → D` preserves homology.
Assume each coefficient functor `F(X,-)` preserves these colimits. There is a canonical
isomorphism `L_nF(A,colim K) ≅ colim_j L_nF(A,K_j)`. -/
def leftDerivedBifunctorCoefficientColimitIso (A : C₁) (n : ℕ) (K : J ⥤ C₂) :
    ((F.leftDerivedBifunctor n).obj A).obj (colimit K) ≅
      colimit (K ⋙ (F.leftDerivedBifunctor n).obj A) := by
  letI := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact preservesColimitIso ((F.leftDerivedBifunctor n).obj A) K

/- Proof implementation note.
Original coefficient injections are the forward comparison's injections.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. Let
`J` be a diagram category with colimits in `C₂` and `D`,
and suppose the colimit functor on `J → D` preserves homology.
Assume each coefficient functor `F(X,-)` preserves these colimits. The coefficient
map `L_nF(A,K_j) → L_nF(A,colim K)` followed by the
forward comparison is the corresponding colimit injection. -/
theorem map_ι_leftDerivedBifunctorCoefficientColimitIso_hom
    (A : C₁) (n : ℕ) (K : J ⥤ C₂) (j : J) :
    ((F.leftDerivedBifunctor n).obj A).map (colimit.ι K j) ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A n K).hom =
      colimit.ι (K ⋙ (F.leftDerivedBifunctor n).obj A) j := by
  let := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact ι_preservesColimitIso_hom ((F.leftDerivedBifunctor n).obj A) K j

/- Proof implementation note.
The inverse retains the original coefficient injection maps.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. Let
`J` be a diagram category with colimits in `C₂` and `D`,
and suppose the colimit functor on `J → D` preserves homology.
Assume each coefficient functor `F(X,-)` preserves these colimits. The colimit
injection followed by the inverse comparison is precisely
the original map induced by `K_j → colim K`. -/
theorem ι_leftDerivedBifunctorCoefficientColimitIso_inv
    (A : C₁) (n : ℕ) (K : J ⥤ C₂) (j : J) :
    colimit.ι (K ⋙ (F.leftDerivedBifunctor n).obj A) j ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A n K).inv =
      ((F.leftDerivedBifunctor n).obj A).map (colimit.ι K j) := by
  let := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact ι_preservesColimitIso_inv ((F.leftDerivedBifunctor n).obj A) K j

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. Let
`J` be a diagram category with colimits in `C₂` and `D`,
and suppose the colimit functor on `J → D` preserves homology.
Assume each coefficient functor `F(X,-)` preserves these colimits. The inverse
comparison is the colimit morphism induced by these original
coefficient injection maps. -/
theorem leftDerivedBifunctorCoefficientColimitIso_inv_eq_post
    (A : C₁) (n : ℕ) (K : J ⥤ C₂) :
    (F.leftDerivedBifunctorCoefficientColimitIso J A n K).inv =
      colimit.post K ((F.leftDerivedBifunctor n).obj A) := by
  apply colimit.hom_ext
  intro j
  exact (F.ι_leftDerivedBifunctorCoefficientColimitIso_inv J A n K j).trans
    (colimit.ι_post (F := K) (G := (F.leftDerivedBifunctor n).obj A) j).symm

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. Let
`J` be a diagram category with colimits in `C₂` and `D`,
and suppose the colimit functor on `J → D` preserves homology.
Assume each coefficient functor `F(X,-)` preserves these colimits. A natural
transformation `K → K′` of coefficient diagrams commutes
with the forward derived coefficient-colimit comparisons. -/
theorem leftDerivedBifunctorCoefficientColimitIso_hom_naturality
    (A : C₁) (n : ℕ) {K K' : J ⥤ C₂} (t : K ⟶ K') :
    ((F.leftDerivedBifunctor n).obj A).map (colimMap t) ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A n K').hom =
      (F.leftDerivedBifunctorCoefficientColimitIso J A n K).hom ≫
        colimMap (Functor.whiskerRight t ((F.leftDerivedBifunctor n).obj A)) := by
  let := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact (preservesColimitNatIso ((F.leftDerivedBifunctor n).obj A)).hom.naturality t

/- Proof implementation note.
Naturality in the original resolved variable follows from the derived transformation and the two
canonical colimit leg equations.
-/

/-- Let `C₁`, `D` be abelian, `C₂` a category, and
`F : C₁ → C₂ → D` have additive partials `F(-,B)`. Suppose `C₁` admits projective resolutions. Let
`J` be a diagram category with colimits in `C₂` and `D`,
and suppose the colimit functor on `J → D` preserves homology.
Assume each coefficient functor `F(X,-)` preserves these colimits. An original
map `a : A → A′` in the resolved variable commutes with
the derived coefficient-colimit comparison, using the
induced natural transformation on all coefficients. -/
theorem leftDerivedBifunctorCoefficientColimitIso_hom_naturality_left
    {A A' : C₁} (a : A ⟶ A') (n : ℕ) (K : J ⥤ C₂) :
    ((F.leftDerivedBifunctor n).map a).app (colimit K) ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A' n K).hom =
      (F.leftDerivedBifunctorCoefficientColimitIso J A n K).hom ≫
        colimMap (Functor.whiskerLeft K ((F.leftDerivedBifunctor n).map a)) := by
  let G := (F.leftDerivedBifunctor n).obj A
  let G' := (F.leftDerivedBifunctor n).obj A'
  let t := (F.leftDerivedBifunctor n).map a
  let e := F.leftDerivedBifunctorCoefficientColimitIso J A n K
  let e' := F.leftDerivedBifunctorCoefficientColimitIso J A' n K
  apply (cancel_epi e.inv).1
  change e.inv ≫ (t.app (colimit K) ≫ e'.hom) =
    e.inv ≫ (e.hom ≫ colimMap (Functor.whiskerLeft K t))
  have h : e.inv ≫ (t.app (colimit K) ≫ e'.hom) =
      colimMap (Functor.whiskerLeft K t) := by
    apply colimit.hom_ext
    intro j
    have hι := F.ι_leftDerivedBifunctorCoefficientColimitIso_inv J A n K j
    have hι' := F.map_ι_leftDerivedBifunctorCoefficientColimitIso_hom J A' n K j
    calc
      colimit.ι (K ⋙ G) j ≫ (e.inv ≫ (t.app (colimit K) ≫ e'.hom)) =
          (G.map (colimit.ι K j) ≫ t.app (colimit K)) ≫ e'.hom := by
        rw [← Category.assoc, hι]
        simp only [Category.assoc]
        rfl
      _ = (t.app (K.obj j) ≫ G'.map (colimit.ι K j)) ≫ e'.hom :=
        congrArg (fun q => q ≫ e'.hom) (t.naturality (colimit.ι K j))
      _ = t.app (K.obj j) ≫ colimit.ι (K ⋙ G') j := by
        rw [Category.assoc, hι']
      _ = colimit.ι (K ⋙ G) j ≫ colimMap (Functor.whiskerLeft K t) :=
        (ι_colimMap (Functor.whiskerLeft K t) j).symm
  rw [h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

end CategoryTheory.Functor
