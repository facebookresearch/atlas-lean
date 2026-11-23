/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.InitialGenerator
public import MathlibExt.CategoryTheory.CategoryHomology.WeightedBar

/-!
# The actual coefficient homology class as a colimit cocone

The first alternating-bar boundary is the difference of the target and
source coefficient classes. The canonical degree-zero chain class is a
cokernel of that actual boundary. Its object classes therefore form a
colimit cocone of the original coefficient functor.

The resulting H₀/colimit Iso retains every original object class. This is
the universal-property step in identifying actual relative coefficients
with deck coinvariants; no coefficient/coinvariant Iso is supplied.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe uJ vJ uA vA

public section

namespace CategoryTheory.CategoryHomology

variable {J : Type uJ} [Category.{vJ} J]
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasCoproducts.{max uJ vJ} A]
  (M : J ⥤ A)

private abbrev coefficientZeroι (j : J) :
    M.obj j ⟶ (coefficientBarComplex M).X 0 :=
  coefficientBarι M (ComposableArrows.mk₀ j)

private abbrev coefficientArrowι {x y : J} (f : x ⟶ y) :
    M.obj x ⟶ (coefficientBarComplex M).X 1 :=
  coefficientBarι M (ComposableArrows.mk₁ f)

private theorem coefficientBar_boundaryOne {x y : J} (f : x ⟶ y) :
    coefficientArrowι M f ≫ (coefficientBarComplex M).d 1 0 =
      M.map f ≫ coefficientZeroι M y - coefficientZeroι M x := by
  let K := coefficientBarComplex M
  let d0 : K.X 1 ⟶ K.X 0 := coefficientBarFace M (0 : Fin 2)
  let d1 : K.X 1 ⟶ K.X 0 := coefficientBarFace M (1 : Fin 2)
  have hd : K.d 1 0 = d0 - d1 := by
    rw [coefficientBarComplex_d_eq_sum M 0, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
      sub_eq_add_neg]
    rfl
  let c0 : ComposableArrows J 0 :=
    (ConcreteCategory.hom (SimplicialObject.δ (CategoryTheory.nerve J) (0 : Fin 2)))
      (ComposableArrows.mk₁ f)
  let c1 : ComposableArrows J 0 :=
    (ConcreteCategory.hom (SimplicialObject.δ (CategoryTheory.nerve J) (1 : Fin 2)))
      (ComposableArrows.mk₁ f)
  let iy : M.obj y ⟶ K.X 0 := coefficientBarι M c0
  let ix : M.obj x ⟶ K.X 0 := coefficientBarι M c1
  have h0 : c0 = ComposableArrows.mk₀ y := ComposableArrows.ext₀ rfl
  have h1 : c1 = ComposableArrows.mk₀ x := ComposableArrows.ext₀ rfl
  have hy : iy = coefficientZeroι M y := by
    have h := Sigma.eqToHom_comp_ι (coefficientBarFamily M 0) h0
    change 𝟙 (M.obj y) ≫ iy = coefficientZeroι M y at h
    exact (Category.id_comp iy).symm.trans h
  have hx : ix = coefficientZeroι M x := by
    have h := Sigma.eqToHom_comp_ι (coefficientBarFamily M 0) h1
    change 𝟙 (M.obj x) ≫ ix = coefficientZeroι M x at h
    exact (Category.id_comp ix).symm.trans h
  have hMap : (ComposableArrows.mk₁ f).map' 0 1 = f := rfl
  have hf0 : coefficientArrowι M f ≫ d0 = M.map f ≫ coefficientZeroι M y := by
    have h : coefficientArrowι M f ≫ d0 =
        M.map ((ComposableArrows.mk₁ f).map' 0 1) ≫ iy :=
      coefficientBarι_face_zero M (ComposableArrows.mk₁ f)
    exact h.trans (congrArg₂ (fun k l => k ≫ l) (congrArg M.map hMap) hy)
  have hf1 : coefficientArrowι M f ≫ d1 = coefficientZeroι M x := by
    have h : coefficientArrowι M f ≫ d1 =
        coefficientFaceHom M (1 : Fin 2) (ComposableArrows.mk₁ f) ≫ ix :=
      coefficientBarι_face M (1 : Fin 2) (ComposableArrows.mk₁ f)
    have hm : coefficientFaceHom M (1 : Fin 2) (ComposableArrows.mk₁ f) =
        𝟙 (M.obj x) := by
      rw [coefficientFaceHom, faceLeftHom]
      change M.map (𝟙 x) = 𝟙 (M.obj x)
      exact M.map_id x
    exact h.trans
      ((congrArg₂ (fun k l => k ≫ l) hm hx).trans (Category.id_comp _))
  exact (congrArg (fun k => coefficientArrowι M f ≫ k) hd).trans
    ((CategoryTheory.Preadditive.comp_sub _ _ _).trans
        (congrArg₂ (fun a b : M.obj x ⟶ K.X 0 => a - b) hf0 hf1))

private theorem coefficientHomologyClass_recipe (j : J) :
    coefficientHomologyClass M j = coefficientZeroι M j ≫
      ChainComplex.homologyZeroClass (coefficientBarComplex M) ≫
        (coefficientHomologyZeroComparison M).inv := rfl

/-- The actual coefficient classes commute with each original categorical arrow. -/
theorem coefficientHomologyClass_map {x y : J} (f : x ⟶ y) :
    M.map f ≫ coefficientHomologyClass M y = coefficientHomologyClass M x := by
  let K := coefficientBarComplex M
  let q : K.X 0 ⟶ K.homology 0 := ChainComplex.homologyZeroClass K
  let e : homologyWithCoefficients M 0 ≅ K.homology 0 := coefficientHomologyZeroComparison M
  let iy : M.obj y ⟶ K.X 0 := coefficientZeroι M y
  let ix : M.obj x ⟶ K.X 0 := coefficientZeroι M x
  have hz : (M.map f ≫ iy - ix) ≫ q = 0 :=
    (congrArg (fun k => k ≫ q) (coefficientBar_boundaryOne M f)).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => coefficientArrowι M f ≫ k)
          (ChainComplex.d_comp_homologyZeroClass K)).trans comp_zero))
  have hSub : (M.map f ≫ iy) ≫ q - ix ≫ q = 0 :=
      (CategoryTheory.Preadditive.sub_comp _ _ _).symm.trans hz
  have h := congrArg (fun k => k ≫ e.inv) (sub_eq_zero.mp hSub)
  have hy : M.map f ≫ coefficientHomologyClass M y =
      ((M.map f ≫ iy) ≫ q) ≫ e.inv :=
    (congrArg (fun k => M.map f ≫ k) (coefficientHomologyClass_recipe M y)).trans
      ((Category.assoc (M.map f) iy (q ≫ e.inv)).symm.trans
        (Category.assoc (M.map f ≫ iy) q e.inv).symm)
  have hx : coefficientHomologyClass M x = (ix ≫ q) ≫ e.inv :=
    (coefficientHomologyClass_recipe M x).trans (Category.assoc ix q e.inv).symm
  exact hy.trans (h.trans hx.symm)

/-- The original degree-zero homology object, with its actual object-class maps. -/
def coefficientHomologyCocone : Cocone M where
  pt := homologyWithCoefficients M 0
  ι :=
    { app := fun j => coefficientHomologyClass M j
      naturality := fun {i j} f => by
        change M.map f ≫ coefficientHomologyClass M j =
          coefficientHomologyClass M i ≫ 𝟙 _
        exact (coefficientHomologyClass_map M f).trans (Category.comp_id _).symm }

private def coefficientCoconeDegreeZeroMap (s : Cocone M) :
    (coefficientBarComplex M).X 0 ⟶ s.pt :=
  Sigma.desc fun c : ComposableArrows J 0 => s.ι.app c.left

private theorem coefficientCoconeDegreeZeroMap_ι (s : Cocone M) (j : J) :
    coefficientBarι M (ComposableArrows.mk₀ j) ≫ coefficientCoconeDegreeZeroMap M s =
      s.ι.app j := Sigma.ι_comp_desc _ _

private theorem coefficientCoconeDegreeZeroMap_boundary (s : Cocone M) :
    (coefficientBarComplex M).d 1 0 ≫ coefficientCoconeDegreeZeroMap M s = 0 := by
  let a : coefficientBarObj M 1 ⟶ s.pt :=
    (coefficientBarComplex M).d 1 0 ≫ coefficientCoconeDegreeZeroMap M s
  have ha : a = 0 := by
    apply coefficientBar_hom_ext M
    intro c
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective c
    rw [comp_zero]
    change coefficientArrowι M f ≫
      ((coefficientBarComplex M).d 1 0 ≫ coefficientCoconeDegreeZeroMap M s) = 0
    have hBoundary := coefficientBar_boundaryOne M f
    let jy : M.obj y ⟶ s.pt := s.ι.app y
    let jx : M.obj x ⟶ s.pt := s.ι.app x
    have hY : coefficientZeroι M y ≫ coefficientCoconeDegreeZeroMap M s = jy :=
      coefficientCoconeDegreeZeroMap_ι M s y
    have hX : coefficientZeroι M x ≫ coefficientCoconeDegreeZeroMap M s = jx :=
      coefficientCoconeDegreeZeroMap_ι M s x
    have hCocone : M.map f ≫ jy = jx := s.w f
    have hStep :
        (M.map f ≫ coefficientZeroι M y - coefficientZeroι M x) ≫
          coefficientCoconeDegreeZeroMap M s = M.map f ≫ jy - jx :=
      (CategoryTheory.Preadditive.sub_comp _ _ _).trans
        (congrArg₂ (fun k l : M.obj x ⟶ s.pt => k - l)
          ((Category.assoc _ _ _).trans (congrArg (fun k => M.map f ≫ k) hY)) hX)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ coefficientCoconeDegreeZeroMap M s) hBoundary).trans
        (hStep.trans (sub_eq_zero.mpr hCocone)))
  exact ha

private def coefficientHomologyCoconeDesc (s : Cocone M) :
    homologyWithCoefficients M 0 ⟶ s.pt := by
  let K := coefficientBarComplex M
  let a : K.X 0 ⟶ s.pt := coefficientCoconeDegreeZeroMap M s
  let c : CokernelCofork (K.d 1 0) :=
    CokernelCofork.ofπ a (coefficientCoconeDegreeZeroMap_boundary M s)
  let d : K.homology 0 ⟶ s.pt := (ChainComplex.homologyZeroCoforkIsColimit K).desc c
  exact (coefficientHomologyZeroComparison M).hom ≫ d

private theorem coefficientHomologyCoconeDesc_class (s : Cocone M) (j : J) :
    coefficientHomologyClass M j ≫ coefficientHomologyCoconeDesc M s = s.ι.app j := by
  let K := coefficientBarComplex M
  let q : K.X 0 ⟶ K.homology 0 := ChainComplex.homologyZeroClass K
  let e : homologyWithCoefficients M 0 ≅ K.homology 0 := coefficientHomologyZeroComparison M
  let a : K.X 0 ⟶ s.pt := coefficientCoconeDegreeZeroMap M s
  let c : CokernelCofork (K.d 1 0) :=
    CokernelCofork.ofπ a (coefficientCoconeDegreeZeroMap_boundary M s)
  let d : K.homology 0 ⟶ s.pt := (ChainComplex.homologyZeroCoforkIsColimit K).desc c
  have hd : q ≫ d = a := (ChainComplex.homologyZeroCoforkIsColimit K).fac c WalkingParallelPair.one
  have hClass : coefficientHomologyClass M j ≫ e.hom = coefficientZeroι M j ≫ q :=
    coefficientHomologyClass_comp_coefficientHomologyZeroComparison_hom M j
  change coefficientHomologyClass M j ≫ (e.hom ≫ d) = s.ι.app j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ d) hClass).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => coefficientZeroι M j ≫ k) hd).trans
          (coefficientCoconeDegreeZeroMap_ι M s j))))

/-- The native class maps earn the colimit universal property of the original coefficient
functor. -/
def coefficientHomologyCoconeIsColimit : IsColimit (coefficientHomologyCocone M) where
  desc s := coefficientHomologyCoconeDesc M s
  fac s j := coefficientHomologyCoconeDesc_class M s j
  uniq s m hm := by
    let K := coefficientBarComplex M
    let q : K.X 0 ⟶ K.homology 0 := ChainComplex.homologyZeroClass K
    let e : homologyWithCoefficients M 0 ≅ K.homology 0 := coefficientHomologyZeroComparison M
    let a : K.X 0 ⟶ s.pt := coefficientCoconeDegreeZeroMap M s
    let c : CokernelCofork (K.d 1 0) :=
      CokernelCofork.ofπ a (coefficientCoconeDegreeZeroMap_boundary M s)
    let d : K.homology 0 ⟶ s.pt := (ChainComplex.homologyZeroCoforkIsColimit K).desc c
    let m' : homologyWithCoefficients M 0 ⟶ s.pt := m
    have hd : q ≫ d = a := (ChainComplex.homologyZeroCoforkIsColimit K).fac c
        WalkingParallelPair.one
    have hCancel : e.inv ≫ (e.hom ≫ d) = d :=
      (Category.assoc e.inv e.hom d).symm.trans
        ((congrArg (fun k => k ≫ d) e.inv_hom_id).trans (Category.id_comp d))
    have hRoot : e.inv ≫ m' = d := by
      apply Cofork.IsColimit.hom_ext (ChainComplex.homologyZeroCoforkIsColimit K)
      change q ≫ (e.inv ≫ m') = q ≫ d
      let f : coefficientBarObj M 0 ⟶ s.pt := q ≫ (e.inv ≫ m')
      let g : coefficientBarObj M 0 ⟶ s.pt := q ≫ d
      have hfg : f = g := by
        apply coefficientBar_hom_ext M
        intro c0
        obtain ⟨j, rfl⟩ := ComposableArrows.mk₀_surjective c0
        change coefficientZeroι M j ≫ (q ≫ (e.inv ≫ m')) = coefficientZeroι M j ≫ (q ≫ d)
        have hClass : coefficientHomologyClass M j = (coefficientZeroι M j ≫ q) ≫ e.inv :=
          (coefficientHomologyClass_recipe M j).trans (Category.assoc _ _ _).symm
        have hj : coefficientHomologyClass M j ≫ m' = s.ι.app j := hm j
        exact (Category.assoc _ _ _).symm.trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ m') hClass.symm).trans
              (hj.trans
                ((coefficientCoconeDegreeZeroMap_ι M s j).symm.trans
                  (congrArg (fun k => coefficientZeroι M j ≫ k) hd.symm)))))
      exact hfg
    change m' = e.hom ≫ d
    apply (cancel_epi e.inv).mp
    exact hRoot.trans hCancel.symm

variable [HasColimit M]

/-- The original coefficient H₀ is the original colimit, with no comparison witness. -/
def coefficientHomologyZeroColimitIso : homologyWithCoefficients M 0 ≅ colimit M :=
  IsColimit.coconePointUniqueUpToIso (coefficientHomologyCoconeIsColimit M) (colimit.isColimit M)

/-- EVERY actual original object class is carried to the corresponding colimit injection. -/
theorem coefficientHomologyZeroColimitIso_class (j : J) :
    coefficientHomologyClass M j ≫ (coefficientHomologyZeroColimitIso M).hom =
      colimit.ι M j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coefficientHomologyCoconeIsColimit M) (colimit.isColimit M) j

/-- The original H₀-to-colimit comparison is natural in the actual coefficient map. -/
theorem coefficientHomologyZeroColimitIso_naturality {M N : J ⥤ A}
    [HasColimit M] [HasColimit N] (α : M ⟶ N) :
    (homologyWithCoefficientsFunctor (C := J) (A := A) 0).map α ≫
        (coefficientHomologyZeroColimitIso N).hom =
      (coefficientHomologyZeroColimitIso M).hom ≫ colimMap α := by
  apply (coefficientHomologyCoconeIsColimit M).hom_ext
  intro j
  change coefficientHomologyClass M j ≫ _ = coefficientHomologyClass M j ≫ _
  calc
    _ = (coefficientHomologyClass M j ≫
        (homologyWithCoefficientsFunctor (C := J) (A := A) 0).map α) ≫
          (coefficientHomologyZeroColimitIso N).hom := (Category.assoc _ _ _).symm
    _ = (α.app j ≫ coefficientHomologyClass N j) ≫
        (coefficientHomologyZeroColimitIso N).hom :=
      congrArg (fun k => k ≫ (coefficientHomologyZeroColimitIso N).hom)
        (coefficientHomologyClass_naturality α j)
    _ = α.app j ≫ colimit.ι N j :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => α.app j ≫ k) (coefficientHomologyZeroColimitIso_class N j))
    _ = colimit.ι M j ≫ colimMap α := (ι_colimMap α j).symm
    _ = (coefficientHomologyClass M j ≫ (coefficientHomologyZeroColimitIso M).hom) ≫
        colimMap α :=
      congrArg (fun k => k ≫ colimMap α) (coefficientHomologyZeroColimitIso_class M j).symm
    _ = _ := Category.assoc _ _ _

end CategoryTheory.CategoryHomology
