/-
Copyright (c) 2025 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.SingularSubdivision.Geometry
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Singular subdivision operators

Definitions of the singular chain complex and the subdivision and homotopy
operators obtained from the universal simplices via `Sigma.desc`.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory Simplicial SimplexCategory SimplicialObject Matrix Limits Opposite

namespace AlgebraicTopology

universe w u v

noncomputable abbrev sChain {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (Y : TopCat.{w}) (R : C) :=
  ((SSet.chainComplexFunctor C).obj R).obj (TopCat.toSSet.obj Y)

noncomputable def genericSingSubdivULift {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) (n : ℕ) :
    (sChain X R).X n ⟶ (sChain X R).X n :=
  Sigma.desc fun σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) =>
    univSubdivULift (C := C) R n ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f n

@[reassoc]
theorem genericSingSubdivULift_ι {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
        genericSingSubdivULift (C := C) R X n =
      univSubdivULift (C := C) R n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f n := by
  change Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R) σ ≫
      genericSingSubdivULift R X n = _
  rw [genericSingSubdivULift]
  exact Sigma.ι_comp_desc _ _

@[reassoc]
private theorem toTop_map_δ_comp_singChainMapULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {n : ℕ} (X : TopCat.{w}) (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) (k : ℕ) :
    (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)))).f k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f k =
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map
          (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n))
            ((TopCat.toSSet.obj X).δ i σ)))).f k := by
  calc (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)))).f k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f k
      = (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)) ≫
            TopCat.toSSet.map
              (TopCat.toSSetTopHom X
                (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f k := by
        rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
    _ = (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i) ≫
              TopCat.toSSetTopHom X
                (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f k := by
        rw [← Functor.map_comp]
    _ = _ := by
        have hTop : SimplexCategory.toTop.{w}.map (SimplexCategory.δ i) ≫
            TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk (n + 1))) σ =
          TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n))
            ((TopCat.toSSet.obj X).δ i σ) := by
          have h := TopCat.toSSetTopHom_naturality_simplex (X := X)
            (f := (SimplexCategory.δ i).op) (σ := σ)
          simp only [Quiver.Hom.unop_op] at h
          exact h.symm
        rw [hTop]

theorem genericSingSubdivULift_comm_d {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) (n : ℕ) :
    genericSingSubdivULift R X (n + 1) ≫ (sChain X R).d (n + 1) n =
      (sChain X R).d (n + 1) n ≫ genericSingSubdivULift R X n := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := R) (n := n + 1)
  intro σ
  have hNat : (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map
          (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f (n + 1) ≫
        (sChain X R).d (n + 1) n =
      (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj
            (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk (n + 1))))).d (n + 1) n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f n :=
    (((SSet.chainComplexFunctor C).obj R).map
      (TopCat.toSSet.map
        (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk (n + 1))) σ))).comm (n + 1) n
  rw [reassoc_of% (genericSingSubdivULift_ι R X (n + 1) σ)]
  conv_lhs => rw [hNat]
  conv_lhs => rw [← Category.assoc, univSubdivULift_boundary (R := R) n]
  conv_rhs => rw [← Category.assoc, SSet.ιChainComplex_d (TopCat.toSSet.obj X) R σ]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg
  rw [Category.assoc]
  rw [toTop_map_δ_comp_singChainMapULift (R := R) (X := X)]
  rw [genericSingSubdivULift_ι]

noncomputable def genericSingSubdivHomULift {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) : (sChain X R) ⟶ (sChain X R) where
  f := fun n => genericSingSubdivULift R X n
  comm' := fun {i j} hij => by
    subst hij
    exact genericSingSubdivULift_comm_d R X j

@[reassoc]
theorem genericSingSubdivULift_naturality {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) {X Y : TopCat.{w}}
    (f : X ⟶ Y) (n : ℕ) :
    genericSingSubdivULift R X n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫
        genericSingSubdivULift R Y n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  have key :
      TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ ≫ f =
        TopCat.toSSetTopHom Y (Opposite.op (SimplexCategory.mk n))
          ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ) :=
    TopCat.toSSetTopHom_naturality_space f σ
  rw [genericSingSubdivULift_ι_assoc]
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp]
  rw [key]
  rw [SSet.ι_chainComplexMap_f_assoc]
  rw [genericSingSubdivULift_ι]

@[reassoc]
theorem genericSingSubdivHomULift_naturality {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) {X Y : TopCat.{w}}
    (f : X ⟶ Y) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ genericSingSubdivHomULift R Y =
      genericSingSubdivHomULift R X ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (genericSingSubdivULift_naturality R f n).symm

@[reassoc]
theorem genericSingSubdivULift_naturality_coefficient {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] {R S : C} (a : R ⟶ S)
    (X : TopCat.{w}) (n : ℕ) :
    genericSingSubdivULift (C := C) R X n ≫ (((singularChainComplexFunctor C).map a).app X).f n =
      (((singularChainComplexFunctor C).map a).app X).f n ≫
        genericSingSubdivULift (C := C) S X n := by
  change genericSingSubdivULift R X n ≫
      (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X)).f n =
    (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)).f n ≫
      genericSingSubdivULift S X n
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := R) (n := n)
  intro σ
  calc SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      genericSingSubdivULift R X n ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f n
      = (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
          genericSingSubdivULift R X n) ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f n := by
        rw [Category.assoc]
    _ = (univSubdivULift (C := C) R n ≫
          (((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ)) ).f n) ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f n := by
        rw [genericSingSubdivULift_ι]
    _ = univSubdivULift (C := C) R n ≫
        ((((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f n ≫
          (((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj X)).f n) := by
        rw [Category.assoc]
    _ = univSubdivULift (C := C) R n ≫
        ((((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj
                (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk n)))).f n ≫
          (((SSet.chainComplexFunctor C).obj S).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f n) := by
        have h := ((SSet.chainComplexFunctor C).map a).naturality
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))
        have h' := congrArg (fun φ => φ.f n) h
        simp only [HomologicalComplex.comp_f] at h'
        rw [h']
    _ = (univSubdivULift (C := C) R n ≫
          (((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj
                (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk n)))).f n) ≫
        (((SSet.chainComplexFunctor C).obj S).map
            (TopCat.toSSet.map
              (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f n := by
        rw [Category.assoc]
    _ = (a ≫ univSubdivULift (C := C) S n) ≫
        (((SSet.chainComplexFunctor C).obj S).map
            (TopCat.toSSet.map
              (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f n := by
        rw [univSubdivULift_naturality_coefficient]
    _ = a ≫
        (univSubdivULift (C := C) S n ≫
          (((SSet.chainComplexFunctor C).obj S).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f n) := by
        rw [Category.assoc]
    _ = a ≫
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := S) σ ≫
          genericSingSubdivULift S X n) := by
        rw [← genericSingSubdivULift_ι]
    _ = (a ≫
          SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := S) σ) ≫
        genericSingSubdivULift S X n := by
        rw [Category.assoc]
    _ = (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
          (((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj X)).f n) ≫
        genericSingSubdivULift S X n := by
        rw [← SSet.ιChainComplex_coefficientMap_f]
    _ = SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f n ≫
          genericSingSubdivULift S X n := by
        rw [Category.assoc]

@[reassoc]
theorem genericSingSubdivHomULift_naturality_coefficient {C : Type u}
    [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] {R S : C}
    (a : R ⟶ S) (X : TopCat.{w}) :
    ((singularChainComplexFunctor C).map a).app X ≫
        genericSingSubdivHomULift S X =
      genericSingSubdivHomULift R X ≫
        ((singularChainComplexFunctor C).map a).app X := by
  change (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)) ≫
      genericSingSubdivHomULift S X =
    genericSingSubdivHomULift R X ≫
      (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X))
  apply HomologicalComplex.hom_ext
  intro n
  exact (genericSingSubdivULift_naturality_coefficient (a := a) (X := X)
    (n := n)).symm

noncomputable def genericSingSubdivNatTransULift
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] :
    singularChainComplexFunctor C ⟶ singularChainComplexFunctor C where
  app R :=
    { app := fun X => genericSingSubdivHomULift R X
      naturality := fun X Y f => by
        change SSet.chainComplexMap (TopCat.toSSet.map f) R ≫
            genericSingSubdivHomULift R Y =
          genericSingSubdivHomULift R X ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R
        exact genericSingSubdivHomULift_naturality R f }
  naturality R S a := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app]
    exact genericSingSubdivHomULift_naturality_coefficient a X

@[simp]
theorem genericSingSubdivNatTransULift_app_app
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) :
    ((genericSingSubdivNatTransULift (C := C)).app R).app X = genericSingSubdivHomULift R X :=
  rfl

/-- The iterated singular subdivision operator, natural jointly in coefficients
and spaces. -/
noncomputable def genericSingSubdivIterNatTransULift
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (k : ℕ) :
    singularChainComplexFunctor C ⟶ singularChainComplexFunctor C :=
  (CategoryTheory.End.of (genericSingSubdivNatTransULift C) ^ k :
    CategoryTheory.End (singularChainComplexFunctor C)).asHom

/-- The objectwise iterated singular subdivision operator. -/
noncomputable def genericSingSubdivIterHomULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) (k : ℕ) : sChain X R ⟶ sChain X R :=
  (CategoryTheory.End.of (genericSingSubdivHomULift R X) ^ k :
    CategoryTheory.End (sChain X R)).asHom

@[simp]
theorem genericSingSubdivIterNatTransULift_zero
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] :
    genericSingSubdivIterNatTransULift C 0 = 𝟙 _ := by
  simp [genericSingSubdivIterNatTransULift]

@[simp]
theorem genericSingSubdivIterNatTransULift_succ
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (k : ℕ) :
    genericSingSubdivIterNatTransULift C (k + 1) =
      genericSingSubdivNatTransULift C ≫
        genericSingSubdivIterNatTransULift C k := by
  simp [genericSingSubdivIterNatTransULift, pow_succ]

@[simp]
theorem genericSingSubdivIterHomULift_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) :
    genericSingSubdivIterHomULift R X 0 = 𝟙 (sChain X R) := by
  simp [genericSingSubdivIterHomULift]

@[simp]
theorem genericSingSubdivIterHomULift_succ
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) (k : ℕ) :
    genericSingSubdivIterHomULift R X (k + 1) =
      genericSingSubdivHomULift R X ≫
        genericSingSubdivIterHomULift R X k := by
  simp [genericSingSubdivIterHomULift, pow_succ]

@[simp]
theorem genericSingSubdivIterNatTransULift_app_app
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (k : ℕ) (R : C) (X : TopCat.{w}) :
    ((genericSingSubdivIterNatTransULift C k).app R).app X =
      genericSingSubdivIterHomULift R X k := by
  induction k with
  | zero =>
      simp
      rfl
  | succ k ih =>
      rw [genericSingSubdivIterNatTransULift_succ,
        genericSingSubdivIterHomULift_succ, NatTrans.comp_app,
        NatTrans.comp_app, genericSingSubdivNatTransULift_app_app, ih]
      rfl

/-- Naturality of the iterated subdivision operator in the space variable. -/
@[reassoc]
theorem genericSingSubdivIterHomULift_naturality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X Y : TopCat.{w}} (f : X ⟶ Y) (k : ℕ) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫
        genericSingSubdivIterHomULift R Y k =
      genericSingSubdivIterHomULift R X k ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  rw [← genericSingSubdivIterNatTransULift_app_app C k R X,
    ← genericSingSubdivIterNatTransULift_app_app C k R Y]
  exact ((genericSingSubdivIterNatTransULift C k).app R).naturality f

/-- Naturality of the iterated subdivision operator in the coefficient variable. -/
@[reassoc]
theorem genericSingSubdivIterHomULift_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (X : TopCat.{w}) (k : ℕ) :
    ((singularChainComplexFunctor C).map a).app X ≫
        genericSingSubdivIterHomULift S X k =
      genericSingSubdivIterHomULift R X k ≫
        ((singularChainComplexFunctor C).map a).app X := by
  rw [← genericSingSubdivIterNatTransULift_app_app C k R X,
    ← genericSingSubdivIterNatTransULift_app_app C k S X]
  exact NatTrans.congr_app ((genericSingSubdivIterNatTransULift C k).naturality a) X

@[simp]
theorem genericSingSubdivIterHomULift_add
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) (a b : ℕ) :
    genericSingSubdivIterHomULift R X (a + b) =
      genericSingSubdivIterHomULift R X a ≫
        genericSingSubdivIterHomULift R X b := by
  change (CategoryTheory.End.of (genericSingSubdivHomULift R X) ^ (a + b) :
      CategoryTheory.End (sChain X R)).asHom =
    (CategoryTheory.End.of (genericSingSubdivHomULift R X) ^ b *
      CategoryTheory.End.of (genericSingSubdivHomULift R X) ^ a).asHom
  rw [← pow_add, Nat.add_comm]

/-- The `n`-th component of `genericSingSubdivHomULift` is `genericSingSubdivULift`. -/
@[simp]
theorem genericSingSubdivHomULift_f {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) (n : ℕ) :
    (genericSingSubdivHomULift R X).f n = genericSingSubdivULift R X n :=
  rfl

noncomputable def genericSingHomotopyULift {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) (n : ℕ) :
    (sChain X R).X n ⟶ (sChain X R).X (n + 1) :=
  Sigma.desc fun σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) =>
    univHomotopyULift (C := C) R n ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f
        (n + 1)

@[reassoc]
theorem genericSingHomotopyULift_ι {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
        genericSingHomotopyULift (C := C) R X n =
      univHomotopyULift (C := C) R n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f (n + 1) := by
  change Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R) σ ≫
      genericSingHomotopyULift R X n = _
  rw [genericSingHomotopyULift]
  exact Sigma.ι_comp_desc _ _

/-- The lifted universal fundamental simplex maps to the given singular simplex. -/
theorem univFundULift_comp_singChainMap
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    univFundULift (C := C) R n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk n)) σ))).f n =
      SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ := by
  have hmem := liftedStdAffine_mem_liftedStdSimplex.{w} n
  have hchart :
      (ConcreteCategory.hom
        (TopCat.toSSetTopHom X
          (Opposite.op (SimplexCategory.mk n)) σ)).comp
          ((ConcreteCategory.hom (liftedStdSimplexTopHom.{w} n)).comp
            (affineRealizeIn (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)
              (liftedStdAffine.{w} n) hmem)) =
        X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ := by
    apply ContinuousMap.ext
    intro x
    simp only [ContinuousMap.comp_apply]
    rw [liftedStdSimplexTopHom_affineRealizeIn_liftedStdAffine_apply]
    exact DFunLike.congr_fun (TopCat.toSSetTopHom_comp_uliftHomeo σ) x
  rw [univFundULift]
  slice_lhs 1 2 => erw [liftIn_ι, dite_eq_left hmem]
  slice_lhs 1 2 => erw [realizeInChain_ι]
  rw [Category.assoc]
  erw [SSet.ι_chainComplexMap_f_assoc, SSet.ι_chainComplexMap_f]
  congr 1
  apply (X.toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))).injective
  exact hchart

theorem genericSingHomotopyULift_comm_d
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) (n : ℕ) :
    genericSingHomotopyULift R X (n + 1) ≫
          (sChain X R).d (n + 2) (n + 1) +
        (sChain X R).d (n + 1) n ≫
          genericSingHomotopyULift R X n =
      𝟙 _ - genericSingSubdivULift R X (n + 1) := by
  apply SSet.chainComplex_hom_ext
    (X := TopCat.toSSet.obj X) (R := R) (n := n + 1)
  intro σ
  have hNat :
      (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f (n + 2) ≫
        (sChain X R).d (n + 2) (n + 1) =
      (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj
            (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk (n + 1))))).d
              (n + 2) (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f (n + 1) :=
    (((SSet.chainComplexFunctor C).obj R).map
      (TopCat.toSSet.map
        (TopCat.toSSetTopHom X
          (Opposite.op (SimplexCategory.mk (n + 1))) σ))).comm (n + 2) (n + 1)
  rw [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id]
  rw [reassoc_of% (genericSingHomotopyULift_ι R X (n + 1) σ)]
  conv_lhs =>
    lhs
    rw [hNat]
  conv_lhs =>
    lhs
    rw [← Category.assoc, univHomotopyULift_boundary (R := R) n]
  rw [Preadditive.sub_comp, Preadditive.sub_comp]
  rw [univFundULift_comp_singChainMap (R := R) (X := X)]
  rw [← genericSingSubdivULift_ι]
  conv_lhs =>
    rhs
    rw [← Category.assoc,
      SSet.ιChainComplex_d (TopCat.toSSet.obj X) R σ]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  have hsum :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((univHomotopyULift (C := C) R n ≫
            (((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map
                (SimplexCategory.toTop.{w}.map
                  (SimplexCategory.δ i)))).f (n + 1)) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map
              (TopCat.toSSetTopHom X
                (Opposite.op (SimplexCategory.mk (n + 1))) σ))).f (n + 1))) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R)
              ((TopCat.toSSet.obj X).δ i σ) ≫
            genericSingHomotopyULift R X n) := by
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg
    simp only [Category.assoc]
    rw [toTop_map_δ_comp_singChainMapULift (R := R) (X := X)]
    rw [← genericSingHomotopyULift_ι]
  rw [hsum, sub_add_cancel]

theorem genericSingHomotopyULift_comm_d_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) :
    genericSingHomotopyULift R X 0 ≫ (sChain X R).d 1 0 =
      𝟙 _ - genericSingSubdivULift R X 0 := by
  apply SSet.chainComplex_hom_ext
    (X := TopCat.toSSet.obj X) (R := R) (n := 0)
  intro σ
  have hNat :
      (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk 0)) σ))).f 1 ≫
        (sChain X R).d 1 0 =
      (sChain
          (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk 0)) R).d 1 0 ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk 0)) σ))).f 0 :=
    (((SSet.chainComplexFunctor C).obj R).map
      (TopCat.toSSet.map
        (TopCat.toSSetTopHom X
          (Opposite.op (SimplexCategory.mk 0)) σ))).comm 1 0
  rw [Preadditive.comp_sub, Category.comp_id]
  rw [reassoc_of% (genericSingHomotopyULift_ι R X 0 σ)]
  conv_lhs => rw [hNat]
  conv_lhs =>
    rw [← Category.assoc, univHomotopyULift_boundary_zero (R := R)]
  rw [Preadditive.sub_comp]
  rw [univFundULift_comp_singChainMap (R := R) (X := X)]
  rw [← genericSingSubdivULift_ι]

noncomputable def genericSingSubdivHomotopyULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) :
    _root_.Homotopy (𝟙 (sChain X R)) (genericSingSubdivHomULift R X) := by
  let fam : ∀ i j : ℕ, (sChain X R).X i ⟶ (sChain X R).X j :=
    fun i j => if h : i + 1 = j then
      h ▸ genericSingHomotopyULift R X i else 0
  let sX : ∀ n, (sChain X R).X n ⟶ (sChain X R).X n :=
    fun n => genericSingSubdivULift R X n
  let hX : ∀ n, (sChain X R).X n ⟶ (sChain X R).X (n + 1) :=
    fun n => genericSingHomotopyULift R X n
  have fam_succ_X : ∀ n, fam n (n + 1) = hX n := by
    intro n
    simp [fam, hX]
  have fam_zero : ∀ {i j : ℕ}, i + 1 ≠ j → fam i j = 0 := by
    intro i j h
    simp [fam, h]
  refine
    { hom := fam
      zero := by
        intro i j hij
        have hne : i + 1 ≠ j := by
          simpa [ComplexShape.down] using hij
        exact fam_zero hne
      comm := by
        intro i
        cases i with
        | zero =>
          have hFam : fam 0 1 = hX 0 := fam_succ_X 0
          have hD0 : dNext 0 fam = 0 :=
            Homotopy.dNext_zero_chainComplex _
          have hP0 : prevD 0 fam =
              fam 0 1 ≫ (sChain X R).d 1 0 := by
            rw [Homotopy.prevD_chainComplex]
          have hP0' : prevD 0 fam =
              hX 0 ≫ (sChain X R).d 1 0 := by
            rw [hP0, hFam]
          have hH0 : hX 0 ≫ (sChain X R).d 1 0 = 𝟙 _ - sX 0 := by
            exact genericSingHomotopyULift_comm_d_zero R X
          calc
            𝟙 ((sChain X R).X 0) =
                prevD 0 fam + dNext 0 fam + sX 0 := by
              rw [hD0, hP0', hH0]
              abel
            _ = dNext 0 fam + prevD 0 fam +
                (genericSingSubdivHomULift R X).f 0 := by
              abel
        | succ n =>
          have hFamN : fam n (n + 1) = hX n := fam_succ_X n
          have hFamSn : fam (n + 1) (n + 2) = hX (n + 1) :=
            fam_succ_X (n + 1)
          have hDn : dNext (n + 1) fam =
              (sChain X R).d (n + 1) n ≫ fam n (n + 1) := by
            rw [Homotopy.dNext_succ_chainComplex]
          have hPn : prevD (n + 1) fam =
              fam (n + 1) (n + 2) ≫
                (sChain X R).d (n + 2) (n + 1) := by
            rw [Homotopy.prevD_chainComplex]
          have hDn' : dNext (n + 1) fam =
              (sChain X R).d (n + 1) n ≫ hX n := by
            rw [hDn, hFamN]
          have hPn' : prevD (n + 1) fam =
              hX (n + 1) ≫ (sChain X R).d (n + 2) (n + 1) := by
            rw [hPn, hFamSn]
          have hEq :
              (sChain X R).d (n + 1) n ≫ hX n +
                  hX (n + 1) ≫ (sChain X R).d (n + 2) (n + 1) =
                𝟙 _ - sX (n + 1) := by
            calc
              (sChain X R).d (n + 1) n ≫ hX n +
                    hX (n + 1) ≫ (sChain X R).d (n + 2) (n + 1) =
                  hX (n + 1) ≫ (sChain X R).d (n + 2) (n + 1) +
                    (sChain X R).d (n + 1) n ≫ hX n := by
                exact add_comm _ _
              _ = 𝟙 _ - sX (n + 1) :=
                genericSingHomotopyULift_comm_d R X n
          have hComb : dNext (n + 1) fam + prevD (n + 1) fam =
              𝟙 _ - sX (n + 1) := by
            rw [hDn', hPn', hEq]
          calc
            𝟙 ((sChain X R).X (n + 1)) =
                dNext (n + 1) fam + prevD (n + 1) fam +
                  sX (n + 1) := by
              rw [hComb, sub_add_cancel]
            _ = dNext (n + 1) fam + prevD (n + 1) fam +
                (genericSingSubdivHomULift R X).f (n + 1) := rfl }

@[simp]
theorem genericSingSubdivHomotopyULift_succ_component
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) (n : ℕ) :
    (genericSingSubdivHomotopyULift R X).hom n (n + 1) =
      genericSingHomotopyULift R X n := by
  simp [genericSingSubdivHomotopyULift]

theorem genericSingSubdivHomotopyULift_eq_zero_of_ne
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) {i j : ℕ} (h : i + 1 ≠ j) :
    (genericSingSubdivHomotopyULift R X).hom i j = 0 := by
  simp [genericSingSubdivHomotopyULift, h]

@[reassoc]
theorem genericSingHomotopyULift_naturality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    genericSingHomotopyULift R X n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f (n + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫
        genericSingHomotopyULift R Y n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  have key := TopCat.toSSetTopHom_naturality_space f σ
  rw [genericSingHomotopyULift_ι_assoc]
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp]
  rw [key]
  rw [SSet.ι_chainComplexMap_f_assoc]
  rw [genericSingHomotopyULift_ι]

@[reassoc]
theorem genericSingSubdivHomotopyULift_naturality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X Y : TopCat.{w}} (f : X ⟶ Y) (i j : ℕ) :
    (genericSingSubdivHomotopyULift R X).hom i j ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f j =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f i ≫
        (genericSingSubdivHomotopyULift R Y).hom i j := by
  by_cases h : i + 1 = j
  · subst j
    rw [genericSingSubdivHomotopyULift_succ_component,
      genericSingSubdivHomotopyULift_succ_component]
    exact genericSingHomotopyULift_naturality R f i
  · rw [genericSingSubdivHomotopyULift_eq_zero_of_ne (R := R) (X := X) h,
      genericSingSubdivHomotopyULift_eq_zero_of_ne (R := R) (X := Y) h]
    simp

@[reassoc]
theorem genericSingHomotopyULift_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (X : TopCat.{w}) (n : ℕ) :
    genericSingHomotopyULift R X n ≫
        (((singularChainComplexFunctor C).map a).app X).f (n + 1) =
      (((singularChainComplexFunctor C).map a).app X).f n ≫
        genericSingHomotopyULift S X n := by
  change genericSingHomotopyULift R X n ≫
      (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X)).f (n + 1) =
    (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)).f n ≫
      genericSingHomotopyULift S X n
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := R) (n := n)
  intro σ
  calc SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      genericSingHomotopyULift R X n ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f (n + 1)
      = (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
          genericSingHomotopyULift R X n) ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f (n + 1) := by
        rw [Category.assoc]
    _ = (univHomotopyULift (C := C) R n ≫
          (((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f (n + 1)) ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f (n + 1) := by
        rw [genericSingHomotopyULift_ι]
    _ = univHomotopyULift (C := C) R n ≫
        ((((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f (n + 1) ≫
          (((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj X)).f (n + 1)) := by
        rw [Category.assoc]
    _ = univHomotopyULift (C := C) R n ≫
        ((((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj
                (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk n)))).f (n + 1) ≫
          (((SSet.chainComplexFunctor C).obj S).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f (n + 1)) := by
        have h := ((SSet.chainComplexFunctor C).map a).naturality
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))
        have h' := congrArg (fun φ => φ.f (n + 1)) h
        simp only [HomologicalComplex.comp_f] at h'
        rw [h']
    _ = (univHomotopyULift (C := C) R n ≫
          (((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj
                (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk n)))).f (n + 1)) ≫
        (((SSet.chainComplexFunctor C).obj S).map
            (TopCat.toSSet.map
              (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f (n + 1) := by
        rw [Category.assoc]
    _ = (a ≫ univHomotopyULift (C := C) S n) ≫
        (((SSet.chainComplexFunctor C).obj S).map
            (TopCat.toSSet.map
              (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f (n + 1) := by
        rw [univHomotopyULift_naturality_coefficient]
    _ = a ≫
        (univHomotopyULift (C := C) S n ≫
          (((SSet.chainComplexFunctor C).obj S).map
              (TopCat.toSSet.map
                (TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ))).f (n + 1)) := by
        rw [Category.assoc]
    _ = a ≫
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := S) σ ≫
          genericSingHomotopyULift S X n) := by
        rw [← genericSingHomotopyULift_ι]
    _ = (a ≫
          SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := S) σ) ≫
        genericSingHomotopyULift S X n := by
        rw [Category.assoc]
    _ = (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
          (((SSet.chainComplexFunctor C).map a).app
              (TopCat.toSSet.obj X)).f n) ≫
        genericSingHomotopyULift S X n := by
        rw [← SSet.ιChainComplex_coefficientMap_f]
    _ = SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f n ≫
          genericSingHomotopyULift S X n := by
        rw [Category.assoc]

@[reassoc]
theorem genericSingSubdivHomotopyULift_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (X : TopCat.{w}) (i j : ℕ) :
    (genericSingSubdivHomotopyULift R X).hom i j ≫
        (((singularChainComplexFunctor C).map a).app X).f j =
      (((singularChainComplexFunctor C).map a).app X).f i ≫
        (genericSingSubdivHomotopyULift S X).hom i j := by
  change (genericSingSubdivHomotopyULift R X).hom i j ≫
      (((SSet.chainComplexFunctor C).map a).app (TopCat.toSSet.obj X)).f j =
    (((SSet.chainComplexFunctor C).map a).app (TopCat.toSSet.obj X)).f i ≫
      (genericSingSubdivHomotopyULift S X).hom i j
  by_cases h : i + 1 = j
  · subst j
    rw [genericSingSubdivHomotopyULift_succ_component,
      genericSingSubdivHomotopyULift_succ_component]
    exact genericSingHomotopyULift_naturality_coefficient (a := a) (X := X) (n := i)
  · rw [genericSingSubdivHomotopyULift_eq_zero_of_ne (R := R) (X := X) h,
      genericSingSubdivHomotopyULift_eq_zero_of_ne (R := S) (X := X) h]
    simp

noncomputable def genericSingSubdivIterHomotopyULift {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) (X : TopCat.{w}) (k : ℕ) :
    Homotopy (𝟙 (sChain X R)) (genericSingSubdivIterHomULift R X k) := by
  induction k with
  | zero => exact Homotopy.refl (𝟙 (sChain X R))
  | succ k ih =>
    exact ((Homotopy.compLeftId ih.symm (genericSingSubdivHomULift R X)).trans
      (genericSingSubdivHomotopyULift R X).symm).symm

@[simp]
theorem genericSingSubdivIterHomotopyULift_succ_component {C : Type u}
    [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) (k i j : ℕ) :
    (genericSingSubdivIterHomotopyULift R X (k + 1)).hom i j =
      (genericSingSubdivHomULift R X).f i ≫
          (genericSingSubdivIterHomotopyULift R X k).hom i j +
        (genericSingSubdivHomotopyULift R X).hom i j := by
  simp only [genericSingSubdivIterHomotopyULift, Homotopy.symm_hom,
    Homotopy.trans_hom, Homotopy.compLeftId_hom, Preadditive.comp_neg]
  abel

@[reassoc]
theorem genericSingSubdivIterHomotopyULift_naturality {C : Type u}
    [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X Y : TopCat.{w}} (f : X ⟶ Y) (k i j : ℕ) :
    (genericSingSubdivIterHomotopyULift R X k).hom i j ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f j =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f i ≫
        (genericSingSubdivIterHomotopyULift R Y k).hom i j := by
  induction k with
  | zero =>
    change (Homotopy.refl (𝟙 (sChain X R))).hom i j ≫ _ =
      _ ≫ (Homotopy.refl (𝟙 (sChain Y R))).hom i j
    simp
  | succ k ih =>
    rw [genericSingSubdivIterHomotopyULift_succ_component]
    rw [genericSingSubdivIterHomotopyULift_succ_component]
    rw [Preadditive.add_comp, Preadditive.comp_add]
    rw [Category.assoc, ih]
    rw [genericSingSubdivHomULift_f, genericSingSubdivHomULift_f]
    rw [← Category.assoc, genericSingSubdivULift_naturality]
    rw [Category.assoc, genericSingSubdivHomotopyULift_naturality]

@[reassoc]
theorem genericSingSubdivIterHomotopyULift_naturality_coefficient {C : Type u}
    [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] {R S : C}
    (a : R ⟶ S) (X : TopCat.{w}) (k i j : ℕ) :
    (genericSingSubdivIterHomotopyULift R X k).hom i j ≫
        (((singularChainComplexFunctor C).map a).app X).f j =
      (((singularChainComplexFunctor C).map a).app X).f i ≫
        (genericSingSubdivIterHomotopyULift S X k).hom i j := by
  change (genericSingSubdivIterHomotopyULift R X k).hom i j ≫
      (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X)).f j =
    (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)).f i ≫
      (genericSingSubdivIterHomotopyULift S X k).hom i j
  induction k with
  | zero =>
    change (Homotopy.refl (𝟙 (sChain X R))).hom i j ≫ _ =
      _ ≫ (Homotopy.refl (𝟙 (sChain X S))).hom i j
    simp
  | succ k ih =>
    rw [genericSingSubdivIterHomotopyULift_succ_component]
    rw [genericSingSubdivIterHomotopyULift_succ_component]
    rw [Preadditive.add_comp, Preadditive.comp_add]
    rw [Category.assoc, ih]
    rw [genericSingSubdivHomULift_f, genericSingSubdivHomULift_f]
    have hSubdiv : genericSingSubdivULift R X i ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f i =
      (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X)).f i ≫
        genericSingSubdivULift S X i := by
      change genericSingSubdivULift R X i ≫
          (((singularChainComplexFunctor C).map a).app X).f i =
        (((singularChainComplexFunctor C).map a).app X).f i ≫
          genericSingSubdivULift S X i
      exact genericSingSubdivULift_naturality_coefficient a X i
    have hHomotopy : (genericSingSubdivHomotopyULift R X).hom i j ≫
        (((SSet.chainComplexFunctor C).map a).app
            (TopCat.toSSet.obj X)).f j =
      (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X)).f i ≫
        (genericSingSubdivHomotopyULift S X).hom i j := by
      change (genericSingSubdivHomotopyULift R X).hom i j ≫
          (((singularChainComplexFunctor C).map a).app X).f j =
        (((singularChainComplexFunctor C).map a).app X).f i ≫
          (genericSingSubdivHomotopyULift S X).hom i j
      exact genericSingSubdivHomotopyULift_naturality_coefficient a X i j
    rw [← Category.assoc, hSubdiv, Category.assoc]
    rw [hHomotopy]

end AlgebraicTopology
