/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomology
public import Mathlib.AlgebraicTopology.EilenbergSteenrod
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Category.Grp.Abelian
public import MathlibExt.Algebra.Homology.Homotopy

/-!
# Singular homology as a homology pretheory

We construct the generic singular homology pretheory:

- `singularHomologyPretheory C R` is the generic pretheory with coefficients `R : C`,
  generic in the abelian category `C` and source universe `w`.
- Its relative theory is `relativeSingularHomologyFunctor` on `TopPair`,
  defined functorially as `TopPair → Arrow TopCat → Arrow ChainComplex → coker → homology`.
- `singularHomologyℤPretheory` is the integral specialization to `AddCommGrpCat` and `ℤ`.
- Homotopy invariance is generic in `C`, `R`, and the space universe `w`.

## Main definitions
* `singularHomologyPretheory`
* `relativeSingularHomologyFunctor_map_eq_of_homotopy`

## References
* Hatcher, *Algebraic Topology*
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial TopPair HomologicalComplex

namespace AlgebraicTopology

universe w v u

section Pretheory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Singular homology with coefficients in `R` as a homology pretheory. -/
noncomputable def singularHomologyPretheory (R : C) :
    TopPair.HomologyPretheory C (ComplexShape.down ℕ) where
  Hₚ n := relativeSingularHomologyFunctor C R n
  H n := (singularHomologyFunctor C n).obj R
  iso n := singularHomologyEmptyPairIso C R n
  δ i j := if hrel : (ComplexShape.down ℕ).Rel i j then
      eqToHom (by rw [show i = j + 1 from hrel.symm]) ≫ relativeSingularBoundary C R j
    else 0
  shape_δ i j h := dite_eq_right h

end Pretheory

noncomputable abbrev singularHomologyℤPretheory :
    TopPair.HomologyPretheory AddCommGrpCat.{0} (ComplexShape.down ℕ) :=
  singularHomologyPretheory AddCommGrpCat.{0} (AddCommGrpCat.of ℤ)

section PairHomotopyNat

open MonoidalCategory Functor.LaxMonoidal in
private lemma toSSet_h_pair_naturality_generic {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (F : TopPair.Homotopy f g) :
    TopCat.toSSet.map X.map ▷ Δ[1] ≫ F.fst.toSSet.h
      = F.snd.toSSet.h ≫ TopCat.toSSet.map Y.map := by
  dsimp only [TopCat.Homotopy.toSSet]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc, Category.assoc,
    μ_natural_left_assoc, ← Functor.map_comp, F.w, Functor.map_comp, Category.assoc]

open MonoidalCategory in
private lemma toSimplicialObjectHomotopy_h_pair_naturality_generic {X Y : TopPair.{w}}
    {f g : X ⟶ Y} (F : TopPair.Homotopy f g) {p : ℕ} (k : Fin (p + 1)) :
    (TopCat.toSSet.map X.map).app (Opposite.op ⦋p⦌)
        ≫ F.fst.toSSet.toSimplicialObjectHomotopy.h k
      = F.snd.toSSet.toSimplicialObjectHomotopy.h k
        ≫ (TopCat.toSSet.map Y.map).app (Opposite.op ⦋p + 1⦌) := by
  ext a
  simp only [SSet.Homotopy.toSimplicialObjectHomotopy, TypeCat.Fun.toFun_apply, types_comp_apply,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc,
    toSSet_h_pair_naturality_generic (F := F)]
  simp only [NatTrans.comp_app_apply]

end PairHomotopyNat

section GenericHomotopy

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

private lemma htpyHom_eq_generic (R : C) {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (p : ℕ) :
    (H.singularChainComplexFunctorObjMap R).hom p (p + 1)
      = -∑ k : Fin (p + 1), (-1 : ℤ) ^ (k : ℕ) •
          (sigmaConst.obj R).map (H.toSSet.toSimplicialObjectHomotopy.h k) := by
  rw [show (H.singularChainComplexFunctorObjMap R).hom p (p + 1)
      = CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
          (H.toSSet.toSimplicialObjectHomotopy.whiskerRight
            (sigmaConst.obj R)) p (p + 1) from rfl,
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  rfl

private lemma singularChainMap_comp_htpyHom_generic (R : C) {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (F : TopPair.Homotopy f g) (p : ℕ) :
    (((singularChainComplexFunctor C).obj R).map X.map).f p
        ≫ (F.fst.singularChainComplexFunctorObjMap R).hom p (p + 1)
      = (F.snd.singularChainComplexFunctorObjMap R).hom p (p + 1)
        ≫ (((singularChainComplexFunctor C).obj R).map Y.map).f (p + 1) := by
  have hmK : (((singularChainComplexFunctor C).obj R).map X.map).f p
      = (sigmaConst.obj R).map
          ((TopCat.toSSet.map X.map).app (Opposite.op ⦋p⦌)) := rfl
  have hmL : (((singularChainComplexFunctor C).obj R).map Y.map).f (p + 1)
      = (sigmaConst.obj R).map
          ((TopCat.toSSet.map Y.map).app (Opposite.op ⦋p + 1⦌)) := rfl
  rw [htpyHom_eq_generic R, htpyHom_eq_generic R, hmK, hmL]
  erw [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum, Preadditive.sum_comp]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun k _ => ?_))
  erw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← Functor.map_comp, ← Functor.map_comp,
    toSimplicialObjectHomotopy_h_pair_naturality_generic (F := F) (k := k)]

@[reassoc]
private lemma htpyHom_full_generic (R : C) {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (F : TopPair.Homotopy f g) (i j : ℕ) :
    (((singularChainComplexFunctor C).obj R).map X.map).f i
        ≫ (F.fst.singularChainComplexFunctorObjMap R).hom i j
      = (F.snd.singularChainComplexFunctorObjMap R).hom i j
        ≫ (((singularChainComplexFunctor C).obj R).map Y.map).f j := by
  rcases eq_or_ne j (i + 1) with hj | hj
  · subst hj; exact singularChainMap_comp_htpyHom_generic R F i
  · rw [(F.fst.singularChainComplexFunctorObjMap R).zero i j
        (by simp only [ComplexShape.down_Rel]; omega),
      (F.snd.singularChainComplexFunctorObjMap R).zero i j
        (by simp only [ComplexShape.down_Rel]; omega), zero_comp]
    exact comp_zero

omit [HasCoproducts C] in
private lemma sub_eq_nullHomotopicMap_of_homotopy_generic {D E : ChainComplex C ℕ} {a b : D ⟶ E}
    (h : Homotopy a b) :
    a - b = Homotopy.nullHomotopicMap h.hom := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.sub_f_apply]
  change a.f i - b.f i = dNext i h.hom + prevD i h.hom
  rw [h.comm i]; abel

private lemma nullHomotopicMap_htpyHom_generic (R : C) {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) :
    Homotopy.nullHomotopicMap (H.singularChainComplexFunctorObjMap R).hom
      = ((singularChainComplexFunctor C).obj R).map f -
        ((singularChainComplexFunctor C).obj R).map g :=
  (sub_eq_nullHomotopicMap_of_homotopy_generic
    (H.singularChainComplexFunctorObjMap R)).symm

/-- Chain-level homotopy invariance for relative singular chains. -/
noncomputable opaque relativeSingularChainMapHomotopy (R : C)
    {X Y : TopPair.{w}} {f g : X ⟶ Y} (F : TopPair.Homotopy f g) :
    Homotopy ((relativeSingularChainFunctor C R).map f)
      ((relativeSingularChainFunctor C R).map g) := by
  have hzeroL : ∀ j, ((singularPairShortComplexFunctor C R).obj Y).f.f j ≫
      ((singularPairShortComplexFunctor C R).obj Y).g.f j = 0 := by
    intro j
    rw [← HomologicalComplex.comp_f, ((singularPairShortComplexFunctor C R).obj Y).zero,
      HomologicalComplex.zero_f]
  let htpy₂ : ∀ i j, ((singularPairShortComplexFunctor C R).obj X).X₂.X i ⟶
      ((singularPairShortComplexFunctor C R).obj Y).X₂.X j :=
    fun i j => (F.fst.singularChainComplexFunctorObjMap R).hom i j
  let htpy₁ : ∀ i j, ((singularPairShortComplexFunctor C R).obj X).X₁.X i ⟶
      ((singularPairShortComplexFunctor C R).obj Y).X₁.X j :=
    fun i j => (F.snd.singularChainComplexFunctorObjMap R).hom i j
  have htpy_square : ∀ i j, ((singularPairShortComplexFunctor C R).obj X).f.f i ≫ htpy₂ i j =
      htpy₁ i j ≫ ((singularPairShortComplexFunctor C R).obj Y).f.f j := by
    intro i j
    change (((singularChainComplexFunctor C).obj R).map X.map).f i ≫
        (F.fst.singularChainComplexFunctorObjMap R).hom i j =
      (F.snd.singularChainComplexFunctorObjMap R).hom i j ≫
        (((singularChainComplexFunctor C).obj R).map Y.map).f j
    exact htpyHom_full_generic R F i j
  have hdesc : ∀ i j, ((singularPairShortComplexFunctor C R).obj X).f.f i ≫
      (htpy₂ i j ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j) = 0 := by
    intro i j
    rw [← Category.assoc, htpy_square i j, Category.assoc, hzeroL j, comp_zero]
  let evalCokerIso : ∀ i, ((singularPairShortComplexFunctor C R).obj X).X₃.X i ≅
      cokernel (((singularPairShortComplexFunctor C R).obj X).f.f i) :=
    fun i => PreservesCokernel.iso (HomologicalComplex.eval C (ComplexShape.down ℕ) i)
      (((singularChainComplexFunctor C).obj R).map X.map)
  let descHom : ∀ i j,
      ((singularPairShortComplexFunctor C R).obj X).X₃.X i ⟶
        ((singularPairShortComplexFunctor C R).obj Y).X₃.X j :=
    fun i j =>
      (evalCokerIso i).hom ≫
        cokernel.desc (((singularPairShortComplexFunctor C R).obj X).f.f i)
          (htpy₂ i j ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j) (hdesc i j)
  have hfac : ∀ i j, ((singularPairShortComplexFunctor C R).obj X).g.f i ≫ descHom i j
      = htpy₂ i j ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j := by
    intro i j
    have hπ : ((singularPairShortComplexFunctor C R).obj X).g.f i ≫ (evalCokerIso i).hom =
        cokernel.π (((singularPairShortComplexFunctor C R).obj X).f.f i) := by
      change ((singularPairShortComplexFunctor C R).obj X).g.f i ≫
          (PreservesCokernel.iso (HomologicalComplex.eval C (ComplexShape.down ℕ) i)
            (((singularChainComplexFunctor C).obj R).map X.map)).hom = _
      exact PreservesCokernel.π_iso_hom (HomologicalComplex.eval C (ComplexShape.down ℕ) i)
        (((singularChainComplexFunctor C).obj R).map X.map)
    change ((singularPairShortComplexFunctor C R).obj X).g.f i ≫
        ((evalCokerIso i).hom ≫
          cokernel.desc (((singularPairShortComplexFunctor C R).obj X).f.f i)
            (htpy₂ i j ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j) (hdesc i j)) =
      htpy₂ i j ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j
    rw [← Category.assoc, hπ, cokernel.π_desc]
  have hzero : ∀ i j, ¬ (ComplexShape.down ℕ).Rel j i → descHom i j = 0 := by
    intro i j hij
    have hepi : Epi (((singularPairShortComplexFunctor C R).obj X).g.f i) := by
      refine (epi_comp_iff_of_isIso _
        (PreservesCokernel.iso (HomologicalComplex.eval _ _ i)
          (((singularChainComplexFunctor C).obj R).map X.map)).hom).mp ?_
      erw [PreservesCokernel.π_iso_hom (HomologicalComplex.eval _ _ i)
          (((singularChainComplexFunctor C).obj R).map X.map)]
      exact coequalizer.π_epi
    rw [← cancel_epi (((singularPairShortComplexFunctor C R).obj X).g.f i), hfac, comp_zero]
    have h0 : htpy₂ i j = 0 := by
      change (F.fst.singularChainComplexFunctorObjMap R).hom i j = 0
      exact (F.fst.singularChainComplexFunctorObjMap R).zero i j hij
    rw [h0, zero_comp]
  have hnull : Homotopy.nullHomotopicMap descHom
      = ((singularPairShortComplexFunctor C R).map f).τ₃
        - ((singularPairShortComplexFunctor C R).map g).τ₃ := by
    have hepi : Epi ((singularPairShortComplexFunctor C R).obj X).g := by
      change Epi (cokernel.π (((singularChainComplexFunctor C).obj R).map X.map))
      exact coequalizer.π_epi
    let af : ((singularPairShortComplexFunctor C R).obj X).X₂ ⟶
        ((singularPairShortComplexFunctor C R).obj Y).X₃ :=
      ((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst f) ≫
        ((singularPairShortComplexFunctor C R).obj Y).g
    let ag : ((singularPairShortComplexFunctor C R).obj X).X₂ ⟶
        ((singularPairShortComplexFunctor C R).obj Y).X₃ :=
      ((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst g) ≫
        ((singularPairShortComplexFunctor C R).obj Y).g
    let bf : ((singularPairShortComplexFunctor C R).obj X).X₂ ⟶
        ((singularPairShortComplexFunctor C R).obj Y).X₃ :=
      ((singularPairShortComplexFunctor C R).obj X).g ≫
        ((singularPairShortComplexFunctor C R).map f).τ₃
    let bg : ((singularPairShortComplexFunctor C R).obj X).X₂ ⟶
        ((singularPairShortComplexFunctor C R).obj Y).X₃ :=
      ((singularPairShortComplexFunctor C R).obj X).g ≫
        ((singularPairShortComplexFunctor C R).map g).τ₃
    have h1 : ((singularPairShortComplexFunctor C R).obj X).g ≫
        Homotopy.nullHomotopicMap descHom
        = Homotopy.nullHomotopicMap
            (fun i j => ((singularPairShortComplexFunctor C R).obj X).g.f i ≫ descHom i j) :=
      Homotopy.comp_nullHomotopicMap _ _
    have h2 : (fun i j => ((singularPairShortComplexFunctor C R).obj X).g.f i ≫ descHom i j)
        = (fun i j => (F.fst.singularChainComplexFunctorObjMap R).hom i j
            ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j) :=
      funext fun i => funext fun j => hfac i j
    have h3 : Homotopy.nullHomotopicMap
        (fun i j => ((singularPairShortComplexFunctor C R).obj X).g.f i ≫ descHom i j)
        = Homotopy.nullHomotopicMap (fun i j =>
            (F.fst.singularChainComplexFunctorObjMap R).hom i j
              ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j) :=
      congrArg Homotopy.nullHomotopicMap h2
    have h4 : Homotopy.nullHomotopicMap (fun i j =>
            (F.fst.singularChainComplexFunctorObjMap R).hom i j
              ≫ ((singularPairShortComplexFunctor C R).obj Y).g.f j)
        = Homotopy.nullHomotopicMap (F.fst.singularChainComplexFunctorObjMap R).hom
            ≫ ((singularPairShortComplexFunctor C R).obj Y).g :=
      (Homotopy.nullHomotopicMap_comp _ _).symm
    have h5 : Homotopy.nullHomotopicMap (F.fst.singularChainComplexFunctorObjMap R).hom
            ≫ ((singularPairShortComplexFunctor C R).obj Y).g
        = (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst f) -
          ((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst g))
            ≫ ((singularPairShortComplexFunctor C R).obj Y).g :=
      congrArg (· ≫ ((singularPairShortComplexFunctor C R).obj Y).g)
        (nullHomotopicMap_htpyHom_generic R F.fst)
    have h6 : (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst f) -
          ((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst g))
            ≫ ((singularPairShortComplexFunctor C R).obj Y).g
        = af - ag :=
      Preadditive.sub_comp _ _ _
    have hf_comm : af = bf := by
      exact ((singularPairShortComplexFunctor C R).map f).comm₂₃
    have hg_comm : ag = bg := by
      exact ((singularPairShortComplexFunctor C R).map g).comm₂₃
    have h7 : af - ag = bf - bg := by
      have h7a : af - ag = bf - ag := congrArg (· - ag) hf_comm
      have h7b : bf - ag = bf - bg := congrArg (bf - ·) hg_comm
      exact h7a.trans h7b
    have h8 : bf - bg
        = ((singularPairShortComplexFunctor C R).obj X).g ≫
          (((singularPairShortComplexFunctor C R).map f).τ₃
            - ((singularPairShortComplexFunctor C R).map g).τ₃) :=
      (Preadditive.comp_sub _ _ _).symm
    have heq : ((singularPairShortComplexFunctor C R).obj X).g ≫
        Homotopy.nullHomotopicMap descHom
        = ((singularPairShortComplexFunctor C R).obj X).g ≫
          (((singularPairShortComplexFunctor C R).map f).τ₃
            - ((singularPairShortComplexFunctor C R).map g).τ₃) :=
      h1.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8)))))
    exact cancel_epi ((singularPairShortComplexFunctor C R).obj X).g |>.mp heq
  change Homotopy ((singularPairShortComplexFunctor C R).map f).τ₃
      ((singularPairShortComplexFunctor C R).map g).τ₃
  exact Homotopy.ofNullHomotopicMapEqSub descHom hzero hnull

lemma relativeSingularHomologyFunctor_map_eq_of_homotopy (R : C)
    {X Y : TopPair.{w}} {f g : X ⟶ Y} (F : TopPair.Homotopy f g) (n : ℕ) :
    (relativeSingularHomologyFunctor C R n).map f =
      (relativeSingularHomologyFunctor C R n).map g :=
  (relativeSingularChainMapHomotopy (C := C) R F).homologyMap_eq n

noncomputable instance (R : C) : (singularHomologyPretheory (C := C) R).IsHomotopyInvariant where
  map_eq_of_homotopy := by
    intro X Y f g F n
    exact relativeSingularHomologyFunctor_map_eq_of_homotopy R F n

end GenericHomotopy

end AlgebraicTopology
