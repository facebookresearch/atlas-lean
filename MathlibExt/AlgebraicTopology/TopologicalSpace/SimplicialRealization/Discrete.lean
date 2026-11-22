/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Basic

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Topology.ContinuousOn

/-!
# Realizing a simplicial set as a levelwise-discrete simplicial space

A simplicial set can be regarded levelwise as a discrete topological space.
Realizing that simplicial topological space gives the usual geometric
realization.  This file constructs the comparison as a natural isomorphism.

The proof is model-independent.  Maps out of the realization of the
levelwise-discrete object are identified with maps into the singular
simplicial set: on a degree-`n` generator `(x,s)`, the corresponding map is
evaluated on the coend generator labelled by `x`.  Conversely, a singular
simplex family supplies a map on every coend summand.  The coend relation is
exactly simplicial naturality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite Convexity

open scoped Simplicial

universe u

namespace SSet

/-- Regard a simplicial set as a simplicial topological space with the
discrete topology in every degree. -/
noncomputable abbrev levelwiseDiscrete :
    SSet.{u} ⥤ SimplicialObject TopCat.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) TopCat.{u}).obj
    TopCat.discrete

@[simp]
theorem levelwiseDiscrete_obj_obj (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) :
    (levelwiseDiscrete.obj X).obj n = TopCat.discrete.obj (X.obj n) :=
  rfl

@[simp]
theorem levelwiseDiscrete_map_app {X Y : SSet.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) :
    (levelwiseDiscrete.map f).app n = TopCat.discrete.map (f.app n) :=
  rfl

/-- Realize a simplicial set after giving every degree the discrete topology. -/
noncomputable abbrev levelwiseDiscreteRealization : SSet.{u} ⥤ TopCat.{u} :=
  levelwiseDiscrete ⋙ TopCat.simplicialRealization

/-- The exact universe-lifting homeomorphism used by the topological simplex
functor. -/
noncomputable def topSimplexULiftHomeomorph (n : SimplexCategory) :
    StdSimplex ℝ (Fin (n.len + 1)) ≃ₜ SimplexCategory.toTop.{u}.obj n :=
  (SimplexCategory.toTop₀.obj n).uliftFunctorObjHomeo

@[simp]
theorem topSimplexULiftHomeomorph_naturality_apply
    {m n : SimplexCategory} (f : m ⟶ n)
    (s : StdSimplex ℝ (Fin (m.len + 1))) :
    SimplexCategory.toTop.map f (topSimplexULiftHomeomorph m s) =
      topSimplexULiftHomeomorph n (StdSimplex.map f s) :=
  rfl

/-- The map from one topological simplex into the realization summand labelled
by a simplex `x`. -/
noncomputable def levelwiseDiscreteSimplex (X : SSet.{u})
    (n : SimplexCategory) (x : X.obj (op n)) :
    SimplexCategory.toTop.obj n ⟶
      levelwiseDiscreteRealization.obj X :=
  CartesianMonoidalCategory.lift (TopCat.const x) (𝟙 _) ≫
    TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n

@[simp]
theorem levelwiseDiscreteSimplex_apply (X : SSet.{u})
    (n : SimplexCategory) (x : X.obj (op n))
    (s : SimplexCategory.toTop.obj n) :
    levelwiseDiscreteSimplex X n x s =
      TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n (x, s) :=
  rfl

/-- Reindexing the label and the topological simplex gives the same coend
generator. -/
theorem levelwiseDiscreteSimplex_naturality (X : SSet.{u})
    {m n : SimplexCategory} (f : m ⟶ n) (x : X.obj (op n)) :
    SimplexCategory.toTop.map f ≫ levelwiseDiscreteSimplex X n x =
      levelwiseDiscreteSimplex X m (X.map f.op x) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro s
  have h := ConcreteCategory.congr_hom
    (TopCat.SimplicialRealization.ι_condition
      (levelwiseDiscrete.obj X) f) (x, s)
  exact h.symm

/-- The singular simplex cut out by one labelled coend generator. -/
noncomputable def levelwiseDiscreteSingularSimplex
    {X : SSet.{u}} {Y : TopCat.{u}}
    (f : levelwiseDiscreteRealization.obj X ⟶ Y)
    (n : SimplexCategory) (x : X.obj (op n)) :
    (TopCat.toSSet.obj Y).obj (op n) :=
  (TopCat.toSSetObjEquiv Y (op n)).symm
    ⟨fun s => f (levelwiseDiscreteSimplex X n x
        (topSimplexULiftHomeomorph n s)),
      f.hom.continuous.comp
        ((levelwiseDiscreteSimplex X n x).hom.continuous.comp
          (topSimplexULiftHomeomorph n).continuous)⟩

/-- Evaluation formula for the singular simplex cut out by a labelled coend
generator. -/
theorem levelwiseDiscreteSingularSimplex_apply
    {X : SSet.{u}} {Y : TopCat.{u}}
    (f : levelwiseDiscreteRealization.obj X ⟶ Y)
    (n : SimplexCategory) (x : X.obj (op n))
    (s : StdSimplex ℝ (Fin (n.len + 1))) :
    TopCat.toSSetObjEquiv Y (op n)
        (levelwiseDiscreteSingularSimplex f n x) s =
      f (levelwiseDiscreteSimplex X n x
        (topSimplexULiftHomeomorph n s)) := by
  exact congrArg
    (fun q : C(StdSimplex ℝ (Fin (n.len + 1)), Y) => q s)
    (Equiv.apply_symm_apply (TopCat.toSSetObjEquiv Y (op n)) _)

/-- Send a map out of the levelwise-discrete realization to its family of
singular simplices. -/
noncomputable def levelwiseDiscreteRealizationAdjunct
    {X : SSet.{u}} {Y : TopCat.{u}}
    (f : levelwiseDiscreteRealization.obj X ⟶ Y) :
    X ⟶ TopCat.toSSet.obj Y where
  app n := ↾fun x => levelwiseDiscreteSingularSimplex f n.unop x
  naturality a b k := by
    ext x
    change levelwiseDiscreteSingularSimplex f b.unop (X.map k x) =
      (TopCat.toSSet.obj Y).map k
        (levelwiseDiscreteSingularSimplex f a.unop x)
    apply (TopCat.toSSetObjEquiv Y b).injective
    apply ContinuousMap.ext
    intro s
    rw [levelwiseDiscreteSingularSimplex_apply]
    have hGenerator := ConcreteCategory.congr_hom
      (levelwiseDiscreteSimplex_naturality X k.unop x)
      (topSimplexULiftHomeomorph b.unop s)
    have hTarget :
        TopCat.toSSetObjEquiv Y b
            ((TopCat.toSSet.obj Y).map k
              (levelwiseDiscreteSingularSimplex f a.unop x)) s =
          f (levelwiseDiscreteSimplex X a.unop x
            (topSimplexULiftHomeomorph a.unop
              (StdSimplex.map k.unop s))) := by
      exact (TopCat.toSSetObjEquiv_naturality_apply k.unop
        (levelwiseDiscreteSingularSimplex f a.unop x) s).trans
          (levelwiseDiscreteSingularSimplex_apply f a.unop x
            (StdSimplex.map k.unop s))
    calc
      f (levelwiseDiscreteSimplex X b.unop (X.map k x)
          (topSimplexULiftHomeomorph b.unop s)) =
        f (levelwiseDiscreteSimplex X a.unop x
          (SimplexCategory.toTop.map k.unop
            (topSimplexULiftHomeomorph b.unop s))) :=
          congrArg f hGenerator.symm
      _ = f (levelwiseDiscreteSimplex X a.unop x
          (topSimplexULiftHomeomorph a.unop
            (StdSimplex.map k.unop s))) := by
          rw [topSimplexULiftHomeomorph_naturality_apply]
      _ = _ := hTarget.symm

/-- Evaluation formula for the singular simplex associated to a map out of
the levelwise-discrete realization. -/
theorem levelwiseDiscreteRealizationAdjunct_apply
    {X : SSet.{u}} {Y : TopCat.{u}}
    (f : levelwiseDiscreteRealization.obj X ⟶ Y)
    (n : SimplexCategory) (x : X.obj (op n))
    (s : StdSimplex ℝ (Fin (n.len + 1))) :
    TopCat.toSSetObjEquiv Y (op n)
        ((levelwiseDiscreteRealizationAdjunct f).app (op n) x) s =
      f (levelwiseDiscreteSimplex X n x
        (topSimplexULiftHomeomorph n s)) :=
  levelwiseDiscreteSingularSimplex_apply f n x s

/-- The degree-`n` map on a coend summand associated to a simplicial map into
a singular simplicial set. -/
noncomputable def levelwiseDiscreteRealizationDescLeg
    {X : SSet.{u}} {Y : TopCat.{u}}
    (g : X ⟶ TopCat.toSSet.obj Y) (n : SimplexCategory) :
    TopCat.discrete.obj (X.obj (op n)) ⊗
        SimplexCategory.toTop.obj n ⟶ Y :=
  TopCat.ofHom
    ⟨fun p => TopCat.toSSetObjEquiv Y (op n) (g.app (op n) p.1)
        ((topSimplexULiftHomeomorph n).symm p.2),
      continuous_prod_of_discrete_left.mpr fun x =>
        (TopCat.toSSetObjEquiv Y (op n) (g.app (op n) x)).continuous.comp
          (topSimplexULiftHomeomorph n).symm.continuous⟩

@[simp]
theorem levelwiseDiscreteRealizationDescLeg_apply
    {X : SSet.{u}} {Y : TopCat.{u}}
    (g : X ⟶ TopCat.toSSet.obj Y) (n : SimplexCategory)
    (x : X.obj (op n)) (s : SimplexCategory.toTop.obj n) :
    levelwiseDiscreteRealizationDescLeg g n (x, s) =
      TopCat.toSSetObjEquiv Y (op n) (g.app (op n) x)
        ((topSimplexULiftHomeomorph n).symm s) := by
  unfold levelwiseDiscreteRealizationDescLeg
  rfl

/-- The summand maps supplied by a singular simplex family satisfy the coend
relation. -/
theorem levelwiseDiscreteRealizationDescLeg_condition
    {X : SSet.{u}} {Y : TopCat.{u}}
    (g : X ⟶ TopCat.toSSet.obj Y) {m n : SimplexCategory}
    (f : m ⟶ n) :
    (TopCat.discrete.map (X.map f.op) ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj m)) ≫
        levelwiseDiscreteRealizationDescLeg g m =
      (𝟙 (TopCat.discrete.obj (X.obj (op n))) ⊗ₘ
        SimplexCategory.toTop.map f) ≫
        levelwiseDiscreteRealizationDescLeg g n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change X.obj (op n) × (SimplexCategory.toTop.obj m : Type u) at p
  rcases p with ⟨x, s⟩
  change levelwiseDiscreteRealizationDescLeg g m
      (X.map f.op x, s) =
    levelwiseDiscreteRealizationDescLeg g n
      (x, SimplexCategory.toTop.map f s)
  rw [levelwiseDiscreteRealizationDescLeg_apply,
    levelwiseDiscreteRealizationDescLeg_apply]
  change TopCat.toSSetObjEquiv Y (op m)
      (g.app (op m) (X.map f.op x))
        ((topSimplexULiftHomeomorph m).symm s) =
    TopCat.toSSetObjEquiv Y (op n) (g.app (op n) x)
      (StdSimplex.map f ((topSimplexULiftHomeomorph m).symm s))
  rw [NatTrans.naturality_apply g f.op x]
  exact TopCat.toSSetObjEquiv_naturality_apply f (g.app (op n) x) s.down

/-- Build a map out of the levelwise-discrete realization from a map into the
singular simplicial set. -/
noncomputable def levelwiseDiscreteRealizationDesc
    {X : SSet.{u}} {Y : TopCat.{u}}
    (g : X ⟶ TopCat.toSSet.obj Y) :
    levelwiseDiscreteRealization.obj X ⟶ Y :=
  TopCat.SimplicialRealization.desc
    (X := levelwiseDiscrete.obj X)
    (fun n => levelwiseDiscreteRealizationDescLeg g n)
    (fun {_ _} f => levelwiseDiscreteRealizationDescLeg_condition g f)

/-- The map constructed from a singular simplex family has the prescribed
value on every coend generator. -/
theorem levelwiseDiscreteRealization_ι_desc
    {X : SSet.{u}} {Y : TopCat.{u}}
    (g : X ⟶ TopCat.toSSet.obj Y) (n : SimplexCategory) :
    TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n ≫
        levelwiseDiscreteRealizationDesc g =
      levelwiseDiscreteRealizationDescLeg g n := by
  exact TopCat.SimplicialRealization.ι_desc
    (X := levelwiseDiscrete.obj X)
    (fun k => levelwiseDiscreteRealizationDescLeg g k)
    (fun {_ _} f => levelwiseDiscreteRealizationDescLeg_condition g f) n

/-- Maps out of the realization of a levelwise-discrete simplicial set are
naturally equivalent to simplicial maps into the singular simplicial set. -/
noncomputable abbrev levelwiseDiscreteRealizationHomEquiv
    (X : SSet.{u}) (Y : TopCat.{u}) :
    (levelwiseDiscreteRealization.obj X ⟶ Y) ≃
      (X ⟶ TopCat.toSSet.obj Y) where
  toFun := levelwiseDiscreteRealizationAdjunct
  invFun := levelwiseDiscreteRealizationDesc
  left_inv f := by
    apply TopCat.SimplicialRealization.hom_ext
    intro n
    rw [levelwiseDiscreteRealization_ι_desc]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    change X.obj (op n) × (SimplexCategory.toTop.obj n : Type u) at p
    rcases p with ⟨x, s⟩
    change TopCat.toSSetObjEquiv Y (op n)
        (levelwiseDiscreteSingularSimplex f n x)
          ((topSimplexULiftHomeomorph n).symm s) =
      f (TopCat.SimplicialRealization.ι
        (levelwiseDiscrete.obj X) n (x, s))
    rw [levelwiseDiscreteSingularSimplex_apply]
    rw [(topSimplexULiftHomeomorph n).apply_symm_apply]
    rfl
  right_inv g := by
    apply NatTrans.ext
    funext n
    ext x
    change levelwiseDiscreteSingularSimplex
      (levelwiseDiscreteRealizationDesc g) n.unop x = g.app n x
    apply (TopCat.toSSetObjEquiv Y n).injective
    apply ContinuousMap.ext
    intro s
    rw [levelwiseDiscreteSingularSimplex_apply]
    let t := topSimplexULiftHomeomorph n.unop s
    have h := ConcreteCategory.congr_hom
      (levelwiseDiscreteRealization_ι_desc g n.unop) (x, t)
    change levelwiseDiscreteRealizationDesc g
        (TopCat.SimplicialRealization.ι
          (levelwiseDiscrete.obj X) n.unop (x, t)) =
      TopCat.toSSetObjEquiv Y n (g.app n x) s
    change levelwiseDiscreteRealizationDesc g
        (TopCat.SimplicialRealization.ι
          (levelwiseDiscrete.obj X) n.unop (x, t)) =
      TopCat.toSSetObjEquiv Y n (g.app n x)
        ((topSimplexULiftHomeomorph n.unop).symm t) at h
    simpa only [t, (topSimplexULiftHomeomorph n.unop).symm_apply_apply] using h

theorem levelwiseDiscreteRealizationHomEquiv_naturality_left_symm
    {X' X : SSet.{u}} {Y : TopCat.{u}} (f : X' ⟶ X)
    (g : X ⟶ TopCat.toSSet.obj Y) :
    (levelwiseDiscreteRealizationHomEquiv X' Y).symm (f ≫ g) =
      levelwiseDiscreteRealization.map f ≫
        (levelwiseDiscreteRealizationHomEquiv X Y).symm g := by
  change levelwiseDiscreteRealizationDesc (f ≫ g) =
    TopCat.simplicialRealization.map
        (Functor.whiskerRight f TopCat.discrete) ≫
      levelwiseDiscreteRealizationDesc g
  apply TopCat.SimplicialRealization.hom_ext
  intro n
  let F := Functor.whiskerRight f TopCat.discrete
  have hMap := TopCat.SimplicialRealization.ι_map F n
  have hDesc := levelwiseDiscreteRealization_ι_desc g n
  have hLeg : levelwiseDiscreteRealizationDescLeg (f ≫ g) n =
      (F.app (op n) ⊗ₘ 𝟙 (SimplexCategory.toTop.obj n)) ≫
        levelwiseDiscreteRealizationDescLeg g n := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    change X'.obj (op n) × (SimplexCategory.toTop.obj n : Type u) at p
    rcases p with ⟨x, s⟩
    change levelwiseDiscreteRealizationDescLeg (f ≫ g) n (x, s) =
      levelwiseDiscreteRealizationDescLeg g n (f.app (op n) x, s)
    rw [levelwiseDiscreteRealizationDescLeg_apply,
      levelwiseDiscreteRealizationDescLeg_apply]
    rfl
  calc
    TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X') n ≫
        levelwiseDiscreteRealizationDesc (f ≫ g) =
      levelwiseDiscreteRealizationDescLeg (f ≫ g) n :=
        levelwiseDiscreteRealization_ι_desc (f ≫ g) n
    _ = (F.app (op n) ⊗ₘ 𝟙 (SimplexCategory.toTop.obj n)) ≫
        levelwiseDiscreteRealizationDescLeg g n := hLeg
    _ = (F.app (op n) ⊗ₘ 𝟙 (SimplexCategory.toTop.obj n)) ≫
        (TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n ≫
          levelwiseDiscreteRealizationDesc g) :=
        congrArg ((F.app (op n) ⊗ₘ
          𝟙 (SimplexCategory.toTop.obj n)) ≫ ·) hDesc.symm
    _ = ((F.app (op n) ⊗ₘ 𝟙 (SimplexCategory.toTop.obj n)) ≫
          TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n) ≫
        levelwiseDiscreteRealizationDesc g :=
      (Category.assoc _ _ _).symm
    _ = (TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X') n ≫
          TopCat.simplicialRealization.map F) ≫
        levelwiseDiscreteRealizationDesc g :=
      congrArg (· ≫ levelwiseDiscreteRealizationDesc g) hMap.symm
    _ = TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X') n ≫
        (TopCat.simplicialRealization.map F ≫
          levelwiseDiscreteRealizationDesc g) :=
      Category.assoc _ _ _

theorem levelwiseDiscreteRealizationHomEquiv_naturality_right
    {X : SSet.{u}} {Y Y' : TopCat.{u}}
    (f : levelwiseDiscreteRealization.obj X ⟶ Y) (g : Y ⟶ Y') :
    levelwiseDiscreteRealizationHomEquiv X Y' (f ≫ g) =
      levelwiseDiscreteRealizationHomEquiv X Y f ≫ TopCat.toSSet.map g := by
  change levelwiseDiscreteRealizationAdjunct (f ≫ g) =
    levelwiseDiscreteRealizationAdjunct f ≫ TopCat.toSSet.map g
  apply NatTrans.ext
  funext n
  ext x
  change levelwiseDiscreteSingularSimplex (f ≫ g) n.unop x =
    (TopCat.toSSet.map g).app n
      (levelwiseDiscreteSingularSimplex f n.unop x)
  apply (TopCat.toSSetObjEquiv Y' n).injective
  apply ContinuousMap.ext
  intro s
  rw [levelwiseDiscreteSingularSimplex_apply]
  change g (f (levelwiseDiscreteSimplex X n.unop x
      (topSimplexULiftHomeomorph n.unop s))) =
    g (f (levelwiseDiscreteSimplex X n.unop x
      (topSimplexULiftHomeomorph n.unop s)))
  rfl

/-- The realization of levelwise-discrete simplicial spaces is left adjoint
to the singular simplicial-set functor. -/
noncomputable def levelwiseDiscreteRealizationAdj :
    levelwiseDiscreteRealization ⊣ TopCat.toSSet :=
  Adjunction.mkOfHomEquiv
    { homEquiv := levelwiseDiscreteRealizationHomEquiv
      homEquiv_naturality_left_symm :=
        levelwiseDiscreteRealizationHomEquiv_naturality_left_symm
      homEquiv_naturality_right :=
        levelwiseDiscreteRealizationHomEquiv_naturality_right }

/-- The unit simplex family for the levelwise-discrete realization
adjunction. -/
noncomputable def levelwiseDiscreteRealizationUnit (X : SSet.{u}) :
    X ⟶ TopCat.toSSet.obj (levelwiseDiscreteRealization.obj X) :=
  levelwiseDiscreteRealizationAdjunct (𝟙 _)

/-- On a simplex, the unit is exactly the corresponding coend generator. -/
theorem levelwiseDiscreteRealizationUnit_apply
    (X : SSet.{u}) (n : SimplexCategory) (x : X.obj (op n))
    (s : StdSimplex ℝ (Fin (n.len + 1))) :
    TopCat.toSSetObjEquiv (levelwiseDiscreteRealization.obj X) (op n)
        ((levelwiseDiscreteRealizationUnit X).app (op n) x) s =
      TopCat.SimplicialRealization.ι (levelwiseDiscrete.obj X) n
        (x, topSimplexULiftHomeomorph n s) := by
  exact levelwiseDiscreteRealizationAdjunct_apply (𝟙 _) n x s

/-- The ordinary geometric realization of a simplicial set is naturally
isomorphic to realization after giving every degree the discrete topology. -/
@[no_expose]
noncomputable def toTopLevelwiseDiscreteNatIso :
    SSet.toTop.{u} ≅ levelwiseDiscreteRealization :=
  sSetTopAdj.leftAdjointUniq levelwiseDiscreteRealizationAdj

/-- The forward comparison is characterized by the explicit coend-generator
unit above. -/
theorem toTopLevelwiseDiscreteNatIso_hom_adjunct (X : SSet.{u}) :
    sSetTopAdj.homEquiv X (levelwiseDiscreteRealization.obj X)
        (toTopLevelwiseDiscreteNatIso.hom.app X) =
      levelwiseDiscreteRealizationUnit X := by
  change sSetTopAdj.homEquiv X (levelwiseDiscreteRealization.obj X)
      ((sSetTopAdj.leftAdjointUniq levelwiseDiscreteRealizationAdj).hom.app X) =
    levelwiseDiscreteRealizationUnit X
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

/-- Naturality of the forward comparison, with the map of levelwise-discrete
simplicial spaces exposed. -/
theorem toTopLevelwiseDiscreteNatIso_hom_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map f ≫ (toTopLevelwiseDiscreteNatIso.app Y).hom =
      (toTopLevelwiseDiscreteNatIso.app X).hom ≫
        TopCat.simplicialRealization.map
          (Functor.whiskerRight f TopCat.discrete) := by
  exact toTopLevelwiseDiscreteNatIso.hom.naturality f

end SSet

end
