/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyClasses
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.AlgebraicTopology.Reedy.SimplexCategory

/-!
# The degree-by-degree factorization of simplicial morphisms

The finite degree categories and partial factorizations assemble the supplied base-category
factorizations into a tower. The historical choice of middle object and both factor maps is
available explicitly as `ReedyR4OneDegreeFunctorPreflight.reedyMapFactorizationData`.
The construction installs no additional Reedy factorization instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

namespace ReedyR4DegreeStagePreflight

/-- The finite collection of standard simplex degrees strictly below `n`, with all simplex
operators between them as morphisms. This is a wrapper so it does not inherit the thin category on
`Fin n`. -/
structure DegreeLT (n : ℕ) where
  /-- The original finite degree index. -/
  degree : Fin n

namespace DegreeLT

variable {n m r : ℕ}

@[ext]
private theorem ext {a b : DegreeLT n} (h : a.degree = b.degree) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance (n : ℕ) : SmallCategory (DegreeLT n) where
  Hom a b := op ⦋a.degree.1⦌ ⟶ op ⦋b.degree.1⦌
  id a := 𝟙 (op ⦋a.degree.1⦌)
  comp f g := f ≫ g

/-- The fully faithful inclusion into the simplex category opposite. -/
def degreeInclusion (n : ℕ) : DegreeLT n ⥤ SimplexCategoryᵒᵖ where
  obj k := op ⦋k.degree.1⦌
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

private def degreeInclusionFullyFaithful (n : ℕ) : (degreeInclusion n).FullyFaithful where
  preimage f := f

private instance (n : ℕ) : (degreeInclusion n).Full :=
  (degreeInclusionFullyFaithful n).full

private instance (n : ℕ) : (degreeInclusion n).Faithful :=
  (degreeInclusionFullyFaithful n).faithful

/-- Include degrees `< n` among degrees `< m`. -/
def degreeIncl (h : n ≤ m) : DegreeLT n ⥤ DegreeLT m where
  obj k := ⟨Fin.castLE h k.degree⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
private theorem degreeIncl_obj_degree (h : n ≤ m) (k : DegreeLT n) :
    ((degreeIncl h).obj k).degree.1 = k.degree.1 :=
  rfl

@[simp]
private theorem degreeIncl_map (h : n ≤ m) {a b : DegreeLT n} (f : a ⟶ b) :
    (degreeIncl h).map f = f :=
  rfl

@[simp]
private theorem degreeIncl_refl (n : ℕ) :
    degreeIncl (Nat.le_refl n) = 𝟭 (DegreeLT n) :=
  rfl

@[simp]
private theorem degreeIncl_trans (h : n ≤ m) (h' : m ≤ r) :
    degreeIncl h ⋙ degreeIncl h' = degreeIncl (h.trans h') :=
  rfl

@[simp]
private theorem degreeIncl_comp_degreeInclusion (h : n ≤ m) :
    degreeIncl h ⋙ degreeInclusion m = degreeInclusion n :=
  rfl

/-- The successor inclusion used when adjoining degree `n`. -/
def degreeSucc (n : ℕ) : DegreeLT n ⥤ DegreeLT (n + 1) where
  obj k := ⟨k.degree.castSucc⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem degreeSucc_eq_degreeIncl (n : ℕ) :
    degreeSucc n = degreeIncl (Nat.le_succ n) :=
  rfl

@[simp]
private theorem degreeSucc_obj_degree (n : ℕ) (k : DegreeLT n) :
    ((degreeSucc n).obj k).degree.1 = k.degree.1 :=
  rfl

/-- The newly adjoined last degree. -/
def degreeLast (n : ℕ) : DegreeLT (n + 1) :=
  ⟨Fin.last n⟩

@[simp]
private theorem degreeLast_degree (n : ℕ) : (degreeLast n).degree.1 = n :=
  rfl

end DegreeLT

open DegreeLT

variable {C : Type u} [Category.{v} C]

/-- Restriction of simplicial objects and natural transformations to degrees `< n`. -/
def simplicialRestriction (n : ℕ) :
    SimplicialObject C ⥤ (DegreeLT n ⥤ C) where
  obj X := degreeInclusion n ⋙ X
  map f := Functor.whiskerLeft (degreeInclusion n) f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
private theorem simplicialRestriction_obj_obj (n : ℕ) (X : SimplicialObject C) (k : DegreeLT n) :
    ((simplicialRestriction (C := C) n).obj X).obj k = X.obj (op ⦋k.degree.1⦌) :=
  rfl

@[simp]
private theorem simplicialRestriction_map_app (n : ℕ) {X Y : SimplicialObject C}
    (f : X ⟶ Y) (k : DegreeLT n) :
    ((simplicialRestriction (C := C) n).map f).app k =
      f.app (op ⦋k.degree.1⦌) :=
  rfl

/-- Restriction of finite-stage functors and natural transformations along `degreeIncl`. -/
private def stageRestriction {n m : ℕ} (h : n ≤ m) :
    (DegreeLT m ⥤ C) ⥤ (DegreeLT n ⥤ C) where
  obj Z := degreeIncl h ⋙ Z
  map q := Functor.whiskerLeft (degreeIncl h) q
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
private theorem stageRestriction_obj_obj {n m : ℕ} (h : n ≤ m)
    (Z : DegreeLT m ⥤ C) (k : DegreeLT n) :
    ((stageRestriction (C := C) h).obj Z).obj k = Z.obj ((degreeIncl h).obj k) :=
  rfl

@[simp]
private theorem stageRestriction_map_app {n m : ℕ} (h : n ≤ m)
    {Z W : DegreeLT m ⥤ C} (q : Z ⟶ W) (k : DegreeLT n) :
    ((stageRestriction (C := C) h).map q).app k = q.app ((degreeIncl h).obj k) :=
  rfl

@[simp]
private theorem stageRestriction_refl (n : ℕ) :
    stageRestriction (C := C) (Nat.le_refl n) = 𝟭 (DegreeLT n ⥤ C) :=
  rfl

@[simp]
private theorem stageRestriction_trans {n m r : ℕ} (h : n ≤ m) (h' : m ≤ r) :
    stageRestriction (C := C) h' ⋙ stageRestriction h =
      stageRestriction (h.trans h') :=
  rfl

@[simp]
private theorem stageRestriction_simplicialRestriction {n m : ℕ} (h : n ≤ m) :
    simplicialRestriction (C := C) m ⋙ stageRestriction h = simplicialRestriction n :=
  rfl

/-- A factorization of a simplicial morphism restricted to degrees `< n`. -/
structure PartialFactorization {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) where
  /-- The complete original middle diagram on the lower-degree source. -/
  Z : DegreeLT n ⥤ C
  /-- The complete original left natural factor on the lower-degree source. -/
  i : (simplicialRestriction n).obj X ⟶ Z
  /-- The complete original right natural factor on the lower-degree source. -/
  p : Z ⟶ (simplicialRestriction n).obj Y
  fac : i ≫ p = (simplicialRestriction n).map f

namespace PartialFactorization

variable {X Y : SimplicialObject C} (f : X ⟶ Y)

/-- The unique coefficient diagram on the empty degree truncation. -/
def emptyFunctor : DegreeLT 0 ⥤ C where
  obj k := Fin.elim0 k.degree
  map {a} := Fin.elim0 a.degree
  map_id a := Fin.elim0 a.degree
  map_comp {a} := Fin.elim0 a.degree

/-- The unique empty factorization below degree zero. -/
def empty : PartialFactorization f 0 where
  Z := emptyFunctor (C := C)
  i :=
    { app := fun k => Fin.elim0 k.degree
      naturality := fun {k} => Fin.elim0 k.degree }
  p :=
    { app := fun k => Fin.elim0 k.degree
      naturality := fun {k} => Fin.elim0 k.degree }
  fac := by
    apply NatTrans.ext
    funext k
    exact Fin.elim0 k.degree

end PartialFactorization

end ReedyR4DegreeStagePreflight
namespace ReedyR4OneDegreeFunctorPreflight

open ReedyR4DegreeStagePreflight
open ReedyR4DegreeStagePreflight.DegreeLT
open CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (n : ℕ)

/-- Include every latching coefficient in the actual lower-degree truncation. -/
def latchingIndexToDegree : latchingIndex n ⥤ DegreeLT n where
  obj a := ⟨⟨a.obj.left.unop.len, a.property.2⟩⟩
  map f := f.hom.left
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Include every matching coefficient in the actual lower-degree truncation. -/
def matchingIndexToDegree : matchingIndex n ⥤ DegreeLT n where
  obj b := ⟨⟨b.obj.right.unop.len, b.property.2⟩⟩
  map f := f.hom.right
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restrict each partial diagram to its degree-`n` latching coefficients. -/
def stageLatchingDiagramFunctor :
    (DegreeLT n ⥤ C) ⥤ (latchingIndex n ⥤ C) where
  obj Z := latchingIndexToDegree n ⋙ Z
  map q := Functor.whiskerLeft (latchingIndexToDegree n) q
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restrict each partial diagram to its degree-`n` matching coefficients. -/
def stageMatchingDiagramFunctor :
    (DegreeLT n ⥤ C) ⥤ (matchingIndex n ⥤ C) where
  obj Z := matchingIndexToDegree n ⋙ Z
  map q := Functor.whiskerLeft (matchingIndexToDegree n) q
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
private theorem stageLatchingDiagramFunctor_map_app
    {Z W : DegreeLT n ⥤ C} (q : Z ⟶ W) (a : latchingIndex n) :
    ((stageLatchingDiagramFunctor (C := C) n).map q).app a =
      q.app ((latchingIndexToDegree n).obj a) :=
  rfl

@[simp]
private theorem stageMatchingDiagramFunctor_map_app
    {Z W : DegreeLT n ⥤ C} (q : Z ⟶ W) (b : matchingIndex n) :
    ((stageMatchingDiagramFunctor (C := C) n).map q).app b =
      q.app ((matchingIndexToDegree n).obj b) :=
  rfl

/-- The latching diagram of the supplied partial coefficient functor. -/
abbrev stageLatchingDiagram (Z : DegreeLT n ⥤ C) : latchingIndex n ⥤ C :=
  (stageLatchingDiagramFunctor (C := C) n).obj Z

/-- The matching diagram of the supplied partial coefficient functor. -/
abbrev stageMatchingDiagram (Z : DegreeLT n ⥤ C) : matchingIndex n ⥤ C :=
  (stageMatchingDiagramFunctor (C := C) n).obj Z

/-- Take the colimit of each partial latching diagram. -/
noncomputable def stageLatchingObjectFunctor
    [HasColimitsOfShape (latchingIndex n) C] :
    (DegreeLT n ⥤ C) ⥤ C :=
  stageLatchingDiagramFunctor n ⋙ colim

/-- Take the limit of each partial matching diagram. -/
noncomputable def stageMatchingObjectFunctor
    [HasLimitsOfShape (matchingIndex n) C] :
    (DegreeLT n ⥤ C) ⥤ C :=
  stageMatchingDiagramFunctor n ⋙ lim

/-- The colimit of the actual partial latching diagram. -/
noncomputable abbrev stageLatchingObject
    [HasColimitsOfShape (latchingIndex n) C] (Z : DegreeLT n ⥤ C) : C :=
  (stageLatchingObjectFunctor (C := C) n).obj Z

/-- The limit of the actual partial matching diagram. -/
noncomputable abbrev stageMatchingObject
    [HasLimitsOfShape (matchingIndex n) C] (Z : DegreeLT n ⥤ C) : C :=
  (stageMatchingObjectFunctor (C := C) n).obj Z

/-- The colimit injection of an original partial latching coefficient. -/
noncomputable def stageLatchingι
    [HasColimitsOfShape (latchingIndex n) C] (Z : DegreeLT n ⥤ C)
    (a : latchingIndex n) :
    Z.obj ((latchingIndexToDegree n).obj a) ⟶ stageLatchingObject n Z :=
  colimit.ι (stageLatchingDiagram n Z) a

/-- The limit projection to an original partial matching coefficient. -/
noncomputable def stageMatchingπ
    [HasLimitsOfShape (matchingIndex n) C] (Z : DegreeLT n ⥤ C)
    (b : matchingIndex n) :
    stageMatchingObject n Z ⟶ Z.obj ((matchingIndexToDegree n).obj b) :=
  limit.π (stageMatchingDiagram n Z) b

@[reassoc]
private theorem stageLatchingObjectFunctor_map_ι
    [HasColimitsOfShape (latchingIndex n) C]
    {Z W : DegreeLT n ⥤ C} (q : Z ⟶ W) (a : latchingIndex n) :
    stageLatchingι n Z a ≫ (stageLatchingObjectFunctor n).map q =
      q.app ((latchingIndexToDegree n).obj a) ≫ stageLatchingι n W a := by
  apply ι_colimMap

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stageMatchingObjectFunctor_map_π
    [HasLimitsOfShape (matchingIndex n) C]
    {Z W : DegreeLT n ⥤ C} (q : Z ⟶ W) (b : matchingIndex n) :
    (stageMatchingObjectFunctor n).map q ≫ stageMatchingπ n W b =
      stageMatchingπ n Z b ≫ q.app ((matchingIndexToDegree n).obj b) := by
  simpa only [stageMatchingObjectFunctor, stageMatchingπ, Functor.comp_map,
    stageMatchingDiagramFunctor_map_app] using
    limit.map_π ((stageMatchingDiagramFunctor n).map q) b

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stageLatching_w (Z : DegreeLT n ⥤ C) {a a' : latchingIndex n}
    [HasColimitsOfShape (latchingIndex n) C]
    (g : a ⟶ a') :
    Z.map ((latchingIndexToDegree n).map g) ≫ stageLatchingι n Z a' =
      stageLatchingι n Z a := by
  simpa only [stageLatchingι, stageLatchingDiagram, stageLatchingDiagramFunctor,
    Functor.comp_map] using
    colimit.w (stageLatchingDiagram n Z) g

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stageMatching_w (Z : DegreeLT n ⥤ C) {b b' : matchingIndex n}
    [HasLimitsOfShape (matchingIndex n) C]
    (g : b ⟶ b') :
    stageMatchingπ n Z b ≫ Z.map ((matchingIndexToDegree n).map g) =
      stageMatchingπ n Z b' := by
  simpa only [stageMatchingπ, stageMatchingDiagram, stageMatchingDiagramFunctor,
    Functor.comp_map] using
    limit.w (stageMatchingDiagram n Z) g

section PartialFactorizationMaps

variable [HasColimitsOfShape (latchingIndex n) C]
variable [HasLimitsOfShape (matchingIndex n) C]
variable {X Y : SimplicialObject C} {f : X ⟶ Y}
variable (H : PartialFactorization f n)

/-- The partial latching comparison induced by the original left factor. -/
noncomputable def stageLᵢ :
    stageLatchingObject n ((simplicialRestriction n).obj X) ⟶ stageLatchingObject n H.Z :=
  (stageLatchingObjectFunctor n).map H.i

/-- The partial latching comparison induced by the original right factor. -/
noncomputable def stageLₚ :
    stageLatchingObject n H.Z ⟶ stageLatchingObject n ((simplicialRestriction n).obj Y) :=
  (stageLatchingObjectFunctor n).map H.p

/-- The partial matching comparison induced by the original left factor. -/
noncomputable def stageMᵢ :
    stageMatchingObject n ((simplicialRestriction n).obj X) ⟶ stageMatchingObject n H.Z :=
  (stageMatchingObjectFunctor n).map H.i

/-- The partial matching comparison induced by the original right factor. -/
noncomputable def stageMₚ :
    stageMatchingObject n H.Z ⟶ stageMatchingObject n ((simplicialRestriction n).obj Y) :=
  (stageMatchingObjectFunctor n).map H.p

omit [HasLimitsOfShape (matchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
private theorem stageLᵢ_comp_stageLₚ :
    stageLᵢ n H ≫ stageLₚ n H = (latchingObjectFunctor n).map f := by
  change (stageLatchingObjectFunctor n).map H.i ≫
      (stageLatchingObjectFunctor n).map H.p = _
  rw [← (stageLatchingObjectFunctor n).map_comp, H.fac]
  rfl

omit [HasColimitsOfShape (latchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
private theorem stageMᵢ_comp_stageMₚ :
    stageMᵢ n H ≫ stageMₚ n H = (matchingObjectFunctor n).map f := by
  change (stageMatchingObjectFunctor n).map H.i ≫
      (stageMatchingObjectFunctor n).map H.p = _
  rw [← (stageMatchingObjectFunctor n).map_comp, H.fac]
  rfl

omit [HasLimitsOfShape (matchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stageLᵢ_ι (a : latchingIndex n) :
    latchingι X n a ≫ stageLᵢ n H =
      H.i.app ((latchingIndexToDegree n).obj a) ≫ stageLatchingι n H.Z a := by
  change stageLatchingι n ((simplicialRestriction n).obj X) a ≫ stageLᵢ n H = _
  exact stageLatchingObjectFunctor_map_ι n H.i a

omit [HasLimitsOfShape (matchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stageLₚ_ι (a : latchingIndex n) :
    stageLatchingι n H.Z a ≫ stageLₚ n H =
      H.p.app ((latchingIndexToDegree n).obj a) ≫ latchingι Y n a := by
  change stageLatchingι n H.Z a ≫ stageLₚ n H =
    H.p.app ((latchingIndexToDegree n).obj a) ≫
      stageLatchingι n ((simplicialRestriction n).obj Y) a
  exact stageLatchingObjectFunctor_map_ι n H.p a

omit [HasColimitsOfShape (latchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stageMᵢ_π (b : matchingIndex n) :
    stageMᵢ n H ≫ stageMatchingπ n H.Z b =
      matchingπ X n b ≫ H.i.app ((matchingIndexToDegree n).obj b) := by
  change stageMᵢ n H ≫ stageMatchingπ n H.Z b =
    stageMatchingπ n ((simplicialRestriction n).obj X) b ≫
      H.i.app ((matchingIndexToDegree n).obj b)
  exact stageMatchingObjectFunctor_map_π n H.i b

omit [HasColimitsOfShape (latchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem stageMₚ_π (b : matchingIndex n) :
    stageMₚ n H ≫ matchingπ Y n b =
      stageMatchingπ n H.Z b ≫ H.p.app ((matchingIndexToDegree n).obj b) := by
  change stageMₚ n H ≫ stageMatchingπ n ((simplicialRestriction n).obj Y) b =
    stageMatchingπ n H.Z b ≫ H.p.app ((matchingIndexToDegree n).obj b)
  exact stageMatchingObjectFunctor_map_π n H.p b

end PartialFactorizationMaps

section Kappa

variable [HasColimitsOfShape (latchingIndex n) C]
variable [HasLimitsOfShape (matchingIndex n) C]
variable (Z : DegreeLT n ⥤ C)

private theorem latchingDegree_obj_eq (a : latchingIndex n) :
    (degreeInclusion n).obj ((latchingIndexToDegree n).obj a) = a.obj.left :=
  rfl

private theorem matchingDegree_obj_eq (b : matchingIndex n) :
    (degreeInclusion n).obj ((matchingIndexToDegree n).obj b) = b.obj.right :=
  rfl

/-- The actual simplex arrow from a latching coefficient to a matching coefficient. -/
def stageCrossHom (a : latchingIndex n) (b : matchingIndex n) :
    (latchingIndexToDegree n).obj a ⟶ (matchingIndexToDegree n).obj b := by
  change (degreeInclusion n).obj ((latchingIndexToDegree n).obj a) ⟶
    (degreeInclusion n).obj ((matchingIndexToDegree n).obj b)
  exact eqToHom (by exact latchingDegree_obj_eq n a) ≫ a.obj.hom ≫ b.obj.hom ≫
    eqToHom (by exact (matchingDegree_obj_eq n b).symm)

private theorem stageCrossHom_comp_matching {b c : matchingIndex n} (f : b ⟶ c)
    (a : latchingIndex n) :
    stageCrossHom n a b ≫ (matchingIndexToDegree n).map f = stageCrossHom n a c := by
  change (a.obj.hom ≫ b.obj.hom) ≫ f.hom.right = a.obj.hom ≫ c.obj.hom
  have hw : b.obj.hom ≫ f.hom.right = c.obj.hom := by
    simpa using StructuredArrow.w f.hom
  rw [Category.assoc, hw]

private theorem latching_comp_stageCrossHom {a a' : latchingIndex n} (f : a ⟶ a')
    (b : matchingIndex n) :
    (latchingIndexToDegree n).map f ≫ stageCrossHom n a' b = stageCrossHom n a b := by
  change f.hom.left ≫ (a'.obj.hom ≫ b.obj.hom) = a.obj.hom ≫ b.obj.hom
  have hw : f.hom.left ≫ a'.obj.hom = a.obj.hom := by
    simp
  rw [← Category.assoc, hw]

/-- The matching cone determined by the original latching-to-matching arrows. -/
def kappaCone (a : latchingIndex n) : Cone (stageMatchingDiagram n Z) where
  pt := Z.obj ((latchingIndexToDegree n).obj a)
  π :=
    { app := fun b => Z.map (stageCrossHom n a b)
      naturality := by
        intro b c f
        change 𝟙 _ ≫ Z.map (stageCrossHom n a c) =
          Z.map (stageCrossHom n a b) ≫ Z.map ((matchingIndexToDegree n).map f)
        rw [Category.id_comp, ← Z.map_comp]
        apply Z.congr_map
        exact (stageCrossHom_comp_matching n f a).symm }

set_option backward.isDefEq.respectTransparency false in
/-- Map one latching coefficient to the full partial matching object. -/
noncomputable def kappaFrom (a : latchingIndex n) :
    Z.obj ((latchingIndexToDegree n).obj a) ⟶ stageMatchingObject n Z :=
  limit.lift (stageMatchingDiagram n Z) (kappaCone n Z a)

omit [HasColimitsOfShape (latchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem kappaFrom_π (a : latchingIndex n) (b : matchingIndex n) :
    kappaFrom n Z a ≫ stageMatchingπ n Z b = Z.map (stageCrossHom n a b) := by
  apply limit.lift_π

set_option backward.isDefEq.respectTransparency false in
/-- The latching cocone determined by the full partial matching object. -/
def kappaCocone : Cocone (stageLatchingDiagram n Z) where
  pt := stageMatchingObject n Z
  ι :=
    { app := fun a => kappaFrom n Z a
      naturality := by
        intro a a' f
        change Z.map ((latchingIndexToDegree n).map f) ≫ kappaFrom n Z a' =
          kappaFrom n Z a ≫ 𝟙 _
        rw [Category.comp_id]
        apply limit.hom_ext
        intro b
        rw [Category.assoc]
        erw [kappaFrom_π, kappaFrom_π]
        rw [← Z.map_comp]
        apply Z.congr_map
        exact latching_comp_stageCrossHom n f b }

/-- The full partial latching-to-matching comparison. -/
noncomputable def kappa :
    stageLatchingObject n Z ⟶ stageMatchingObject n Z :=
  colimit.desc (stageLatchingDiagram n Z) (kappaCocone n Z)

@[reassoc]
private theorem kappa_ι_π (a : latchingIndex n) (b : matchingIndex n) :
    stageLatchingι n Z a ≫ kappa n Z ≫ stageMatchingπ n Z b =
      Z.map (stageCrossHom n a b) := by
  rw [← Category.assoc]
  erw [colimit.ι_desc, kappaFrom_π]

end Kappa

section KappaNaturality

variable [HasColimitsOfShape (latchingIndex n) C]
variable [HasLimitsOfShape (matchingIndex n) C]

set_option backward.isDefEq.respectTransparency false in
private theorem kappa_naturality {Z W : DegreeLT n ⥤ C} (q : Z ⟶ W) :
    kappa n Z ≫ (stageMatchingObjectFunctor n).map q =
      (stageLatchingObjectFunctor n).map q ≫ kappa n W := by
  apply colimit.hom_ext
  intro a
  apply limit.hom_ext
  intro b
  simp only [Category.assoc]
  erw [stageMatchingObjectFunctor_map_π]
  erw [kappa_ι_π_assoc]
  erw [stageLatchingObjectFunctor_map_ι_assoc]
  erw [kappa_ι_π]
  exact q.naturality (stageCrossHom n a b)

omit [HasColimitsOfShape (latchingIndex n) C]
  [HasLimitsOfShape (matchingIndex n) C] in
private theorem simplicialRestriction_map_stageCrossHom
    (X : SimplicialObject C) (a : latchingIndex n) (b : matchingIndex n) :
    ((simplicialRestriction n).obj X).map (stageCrossHom n a b) =
      X.map (a.obj.hom ≫ b.obj.hom) := by
  change X.map (a.obj.hom ≫ b.obj.hom) = X.map (a.obj.hom ≫ b.obj.hom)
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem kappa_restrict (X : SimplicialObject C) :
    kappa n ((simplicialRestriction n).obj X) =
      latchingMap X n ≫ matchingMap X n := by
  apply colimit.hom_ext
  intro a
  apply limit.hom_ext
  intro b
  simp only [Category.assoc]
  erw [kappa_ι_π]
  erw [latchingMap_ι_assoc, matchingMap_π]
  rw [← X.map_comp]
  exact simplicialRestriction_map_stageCrossHom n X a b

end KappaNaturality

section CanonicalMap

variable [HasPushouts C] [HasPullbacks C]
variable [HasColimitsOfShape (latchingIndex n) C]
variable [HasLimitsOfShape (matchingIndex n) C]
variable {X Y : SimplicialObject C} {f : X ⟶ Y}
variable (H : PartialFactorization f n)

/-- The pushout source for the actual degree-`n` relative factorization. -/
noncomputable abbrev stageRelativeSource : C :=
  pushout (latchingMap X n) (stageLᵢ n H)

/-- The pullback target for the actual degree-`n` relative factorization. -/
noncomputable abbrev stageRelativeTarget : C :=
  pullback (matchingMap Y n) (stageMₚ n H)

omit [HasPushouts C] [HasPullbacks C]
  [HasColimitsOfShape (latchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
private theorem xToB_w :
    f.app (op ⦋n⦌) ≫ matchingMap Y n =
      (matchingMap X n ≫ stageMᵢ n H) ≫ stageMₚ n H := by
  rw [Category.assoc, stageMᵢ_comp_stageMₚ]
  exact matchingMap_naturality n f

/-- Map the source component into the full relative matching target. -/
noncomputable def xToB :
    X.obj (op ⦋n⦌) ⟶ stageRelativeTarget n H :=
  pullback.lift (f.app (op ⦋n⦌)) (matchingMap X n ≫ stageMᵢ n H)
    (by exact xToB_w n H)

omit [HasPushouts C] [HasColimitsOfShape (latchingIndex n) C] in
@[reassoc]
private theorem xToB_fst :
    xToB n H ≫ pullback.fst (matchingMap Y n) (stageMₚ n H) =
      f.app (op ⦋n⦌) := by
  apply pullback.lift_fst

omit [HasPushouts C] [HasColimitsOfShape (latchingIndex n) C] in
@[reassoc]
private theorem xToB_snd :
    xToB n H ≫ pullback.snd (matchingMap Y n) (stageMₚ n H) =
      matchingMap X n ≫ stageMᵢ n H := by
  apply pullback.lift_snd

omit [HasPushouts C] [HasPullbacks C] in
set_option backward.isDefEq.respectTransparency false in
private theorem zToB_w :
    (stageLₚ n H ≫ latchingMap Y n) ≫ matchingMap Y n =
      kappa n H.Z ≫ stageMₚ n H := by
  rw [Category.assoc, ← kappa_restrict]
  exact (kappa_naturality n H.p).symm

/-- Map the partial middle latching object into the full relative matching target. -/
noncomputable def zToB :
    stageLatchingObject n H.Z ⟶ stageRelativeTarget n H :=
  pullback.lift (stageLₚ n H ≫ latchingMap Y n) (kappa n H.Z)
    (by exact zToB_w n H)

omit [HasPushouts C] in
@[reassoc]
private theorem zToB_fst :
    zToB n H ≫ pullback.fst (matchingMap Y n) (stageMₚ n H) =
      stageLₚ n H ≫ latchingMap Y n := by
  apply pullback.lift_fst

omit [HasPushouts C] in
@[reassoc]
private theorem zToB_snd :
    zToB n H ≫ pullback.snd (matchingMap Y n) (stageMₚ n H) =
      kappa n H.Z := by
  apply pullback.lift_snd

omit [HasPushouts C] in
set_option backward.isDefEq.respectTransparency false in
private theorem canonicalMap_compat :
    latchingMap X n ≫ xToB n H = stageLᵢ n H ≫ zToB n H := by
  apply pullback.hom_ext
  · rw [Category.assoc, xToB_fst]
    rw [Category.assoc, zToB_fst]
    rw [← Category.assoc, stageLᵢ_comp_stageLₚ]
    exact (latchingMap_naturality n f).symm
  · rw [Category.assoc, xToB_snd]
    rw [Category.assoc, zToB_snd]
    rw [← Category.assoc, ← kappa_restrict]
    exact kappa_naturality n H.i

/-- The actual degree-`n` map from the relative latching source to the relative matching target. -/
noncomputable def canonicalMap :
    stageRelativeSource n H ⟶ stageRelativeTarget n H :=
  pushout.desc (xToB n H) (zToB n H) (by exact canonicalMap_compat n H)

@[reassoc]
private theorem canonicalMap_inl :
    pushout.inl (latchingMap X n) (stageLᵢ n H) ≫ canonicalMap n H =
      xToB n H := by
  apply pushout.inl_desc

@[reassoc]
private theorem canonicalMap_inr :
    pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ canonicalMap n H =
      zToB n H := by
  apply pushout.inr_desc

@[reassoc]
private theorem canonicalMap_inl_fst :
    pushout.inl (latchingMap X n) (stageLᵢ n H) ≫ canonicalMap n H ≫
        pullback.fst (matchingMap Y n) (stageMₚ n H) =
      f.app (op ⦋n⦌) := by
  rw [canonicalMap_inl_assoc, xToB_fst]

@[reassoc]
private theorem canonicalMap_inl_snd :
    pushout.inl (latchingMap X n) (stageLᵢ n H) ≫ canonicalMap n H ≫
        pullback.snd (matchingMap Y n) (stageMₚ n H) =
      matchingMap X n ≫ stageMᵢ n H := by
  rw [canonicalMap_inl_assoc, xToB_snd]

@[reassoc]
private theorem canonicalMap_inr_fst :
    pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ canonicalMap n H ≫
        pullback.fst (matchingMap Y n) (stageMₚ n H) =
      stageLₚ n H ≫ latchingMap Y n := by
  rw [canonicalMap_inr_assoc, zToB_fst]

@[reassoc]
private theorem canonicalMap_inr_snd :
    pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ canonicalMap n H ≫
        pullback.snd (matchingMap Y n) (stageMₚ n H) =
      kappa n H.Z := by
  rw [canonicalMap_inr_assoc, zToB_snd]

end CanonicalMap


section DegreeFactor

open CategoryTheory.MorphismProperty

variable [HasPushouts C] [HasPullbacks C]
variable [HasColimitsOfShape (latchingIndex n) C]
variable [HasLimitsOfShape (matchingIndex n) C]
variable {X Y : SimplicialObject C} {f : X ⟶ Y}
variable (H : PartialFactorization f n)
variable (P Q : MorphismProperty C) [P.HasFactorization Q]

/-- The chosen base factorization of the canonical degree map. -/
noncomputable def degreeFactor :
    P.MapFactorizationData Q (canonicalMap n H) :=
  MorphismProperty.factorizationData P Q (canonicalMap n H)

/-- The originally chosen middle coefficient adjoined at the next degree. -/
noncomputable abbrev newObj : C :=
  (degreeFactor n H P Q).Z

/-- The originally chosen left factor of the degree-`n` canonical map. -/
noncomputable def j : stageRelativeSource n H ⟶ newObj n H P Q :=
  (degreeFactor n H P Q).i

/-- The originally chosen right factor of the degree-`n` canonical map. -/
noncomputable def q : newObj n H P Q ⟶ stageRelativeTarget n H :=
  (degreeFactor n H P Q).p

private theorem j_mem : P (j n H P Q) :=
  (degreeFactor n H P Q).hi

private theorem q_mem : Q (q n H P Q) :=
  (degreeFactor n H P Q).hp

@[reassoc (attr := simp)]
private theorem j_q : j n H P Q ≫ q n H P Q = canonicalMap n H :=
  (degreeFactor n H P Q).fac

/-- The new component of the left factor. -/
noncomputable def iNew :
    X.obj (op ⦋n⦌) ⟶ newObj n H P Q :=
  pushout.inl (latchingMap X n) (stageLᵢ n H) ≫ j n H P Q

/-- The new component of the right factor. -/
noncomputable def pNew :
    newObj n H P Q ⟶ Y.obj (op ⦋n⦌) :=
  q n H P Q ≫ pullback.fst (matchingMap Y n) (stageMₚ n H)

private theorem iNew_pNew :
    iNew n H P Q ≫ pNew n H P Q = f.app (op ⦋n⦌) := by
  simp only [iNew, pNew, Category.assoc, j_q_assoc, canonicalMap_inl_fst]

/-- The proper direct structure map into the new degree. -/
noncomputable def directMap (a : latchingIndex n) :
    H.Z.obj ((latchingIndexToDegree n).obj a) ⟶ newObj n H P Q :=
  stageLatchingι n H.Z a ≫
    pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ j n H P Q

/-- The proper inverse structure map out of the new degree. -/
noncomputable def inverseMap (b : matchingIndex n) :
    newObj n H P Q ⟶ H.Z.obj ((matchingIndexToDegree n).obj b) :=
  q n H P Q ≫ pullback.snd (matchingMap Y n) (stageMₚ n H) ≫
    stageMatchingπ n H.Z b

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem directMap_naturality {a a' : latchingIndex n} (g : a ⟶ a') :
    H.Z.map ((latchingIndexToDegree n).map g) ≫ directMap n H P Q a' =
      directMap n H P Q a := by
  change H.Z.map ((latchingIndexToDegree n).map g) ≫ stageLatchingι n H.Z a' ≫
      pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ j n H P Q =
    stageLatchingι n H.Z a ≫ pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ j n H P Q
  rw [stageLatching_w_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem inverseMap_naturality {b b' : matchingIndex n} (g : b ⟶ b') :
    inverseMap n H P Q b ≫ H.Z.map ((matchingIndexToDegree n).map g) =
      inverseMap n H P Q b' := by
  dsimp [inverseMap]
  have hw := congrArg
    (fun t => q n H P Q ≫ pullback.snd (matchingMap Y n) (stageMₚ n H) ≫ t)
    (stageMatching_w n H.Z g)
  simpa only [Category.assoc] using hw

set_option backward.isDefEq.respectTransparency false in
/-- The proper-direct/proper-inverse mixed law. -/
private theorem directMap_comp_inverseMap (a : latchingIndex n) (b : matchingIndex n) :
    directMap n H P Q a ≫ inverseMap n H P Q b =
      H.Z.map (stageCrossHom n a b) := by
  simp only [directMap, inverseMap, Category.assoc]
  rw [j_q_assoc, canonicalMap_inr_snd_assoc, kappa_ι_π]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the left factor along a proper direct map. -/
private theorem i_naturality_direct (a : latchingIndex n) :
    X.map a.obj.hom ≫ iNew n H P Q =
      H.i.app ((latchingIndexToDegree n).obj a) ≫ directMap n H P Q a := by
  change X.map a.obj.hom ≫
      pushout.inl (latchingMap X n) (stageLᵢ n H) ≫ j n H P Q =
    H.i.app ((latchingIndexToDegree n).obj a) ≫ stageLatchingι n H.Z a ≫
      pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ j n H P Q
  erw [← latchingMap_ι_assoc]
  erw [pushout.condition_assoc]
  erw [stageLᵢ_ι_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the left factor along a proper inverse map. -/
private theorem i_naturality_inverse (b : matchingIndex n) :
    iNew n H P Q ≫ inverseMap n H P Q b =
      X.map b.obj.hom ≫ H.i.app ((matchingIndexToDegree n).obj b) := by
  dsimp [iNew, inverseMap]
  simp only [Category.assoc]
  erw [j_q_assoc, canonicalMap_inl_snd_assoc]
  rw [Category.assoc, stageMᵢ_π]
  rw [← Category.assoc, matchingMap_π]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the right factor along a proper direct map. -/
private theorem p_naturality_direct (a : latchingIndex n) :
    directMap n H P Q a ≫ pNew n H P Q =
      H.p.app ((latchingIndexToDegree n).obj a) ≫ Y.map a.obj.hom := by
  calc
    directMap n H P Q a ≫ pNew n H P Q =
        stageLatchingι n H.Z a ≫
          (pushout.inr (latchingMap X n) (stageLᵢ n H) ≫ canonicalMap n H ≫
            pullback.fst (matchingMap Y n) (stageMₚ n H)) := by
      dsimp [directMap, pNew]
      simp only [Category.assoc, j_q_assoc]
    _ = stageLatchingι n H.Z a ≫ (stageLₚ n H ≫ latchingMap Y n) := by
      rw [canonicalMap_inr_fst]
    _ = (stageLatchingι n H.Z a ≫ stageLₚ n H) ≫ latchingMap Y n := by
      rw [Category.assoc]
    _ = (H.p.app ((latchingIndexToDegree n).obj a) ≫ latchingι Y n a) ≫
        latchingMap Y n := by rw [stageLₚ_ι]
    _ = H.p.app ((latchingIndexToDegree n).obj a) ≫ Y.map a.obj.hom := by
      rw [Category.assoc, latchingMap_ι]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the right factor along a proper inverse map. -/
private theorem p_naturality_inverse (b : matchingIndex n) :
    inverseMap n H P Q b ≫ H.p.app ((matchingIndexToDegree n).obj b) =
      pNew n H P Q ≫ Y.map b.obj.hom := by
  calc
    inverseMap n H P Q b ≫ H.p.app ((matchingIndexToDegree n).obj b) =
        q n H P Q ≫ pullback.snd (matchingMap Y n) (stageMₚ n H) ≫
          (stageMatchingπ n H.Z b ≫ H.p.app ((matchingIndexToDegree n).obj b)) := by
      dsimp [inverseMap]
      simp only [Category.assoc]
    _ = q n H P Q ≫ pullback.snd (matchingMap Y n) (stageMₚ n H) ≫
        (stageMₚ n H ≫ matchingπ Y n b) := by rw [stageMₚ_π]
    _ = q n H P Q ≫
        (pullback.snd (matchingMap Y n) (stageMₚ n H) ≫ stageMₚ n H) ≫
          matchingπ Y n b := by rw [Category.assoc]
    _ = q n H P Q ≫
        (pullback.fst (matchingMap Y n) (stageMₚ n H) ≫ matchingMap Y n) ≫
          matchingπ Y n b := by rw [pullback.condition]
    _ = (q n H P Q ≫ pullback.fst (matchingMap Y n) (stageMₚ n H)) ≫
        (matchingMap Y n ≫ matchingπ Y n b) := by simp only [Category.assoc]
    _ = pNew n H P Q ≫ Y.map b.obj.hom := by
      rw [matchingMap_π]
      rfl

end DegreeFactor


section OneDegreeExtension

variable [HasPushouts C] [HasPullbacks C]
variable [HasColimitsOfShape (latchingIndex n) C]
variable [HasLimitsOfShape (matchingIndex n) C]
variable {X Y : SimplicialObject C} {f : X ⟶ Y}
variable (H : PartialFactorization f n)
variable (P Q : MorphismProperty C) [P.HasFactorization Q]

/-- The unchanged lower-degree object represented by its original finite index. -/
def oldDegree (k : Fin n) : DegreeLT n := ⟨k⟩

private def stageHom {a b : Fin n} (θ : op ⦋a.1⦌ ⟶ op ⦋b.1⦌) :
    oldDegree n a ⟶ oldDegree n b :=
  θ

/-- Objects of the successor stage; old objects are reused and the last object is the factor
object. -/
noncomputable def extendObj (k : DegreeLT (n + 1)) : C :=
  Fin.lastCases (newObj n H P Q) (fun j => H.Z.obj (oldDegree n j)) k.degree

@[simp]
private theorem extendObj_last :
    extendObj n H P Q (degreeLast n) = newObj n H P Q :=
  Fin.lastCases_last

@[simp]
private theorem extendObj_castSucc (k : DegreeLT n) :
    extendObj n H P Q ((degreeSucc n).obj k) = H.Z.obj k :=
  Fin.lastCases_castSucc k.degree

/-- Regard an original proper epimorphism as a canonical latching coefficient. -/
def latchingIndexOfEpi (k : Fin n) (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌)
    [Epi θ.unop] : latchingIndex n :=
  ⟨CostructuredArrow.mk θ, ⟨by simpa using (inferInstance : Epi θ.unop), k.2⟩⟩

/-- Regard an original proper monomorphism as a canonical matching coefficient. -/
def matchingIndexOfMono (k : Fin n) (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌)
    [Mono θ.unop] : matchingIndex n :=
  ⟨StructuredArrow.mk θ, ⟨by simpa using (inferInstance : Mono θ.unop), k.2⟩⟩

/-- The original complete epi--image--mono factor record of a simplex arrow. -/
def canonicalSimplexFactor {r s : ℕ} (θ : op ⦋r⦌ ⟶ op ⦋s⦌) :
    (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop where
  Z := image θ.unop
  i := factorThruImage θ.unop
  p := image.ι θ.unop
  fac := image.fac θ.unop
  hi := inferInstance
  hp := inferInstance

/-- Evaluate an original arrow from a lower degree to the newly adjoined degree. -/
noncomputable def evalOldToNew (k : Fin n)
    (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌)
    (fac : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop) :
    H.Z.obj (oldDegree n k) ⟶ newObj n H P Q := by
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  have hd : fac.Z.len < n := (SimplexCategory.len_le_of_mono fac.p).trans_lt k.2
  let j : Fin n := ⟨fac.Z.len, hd⟩
  exact H.Z.map fac.p.op ≫ directMap n H P Q (latchingIndexOfEpi n j fac.i.op)

/-- Evaluate an original arrow from the newly adjoined degree to a lower degree. -/
noncomputable def evalNewToOld (k : Fin n)
    (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌)
    (fac : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop) :
    newObj n H P Q ⟶ H.Z.obj (oldDegree n k) := by
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  have hd : fac.Z.len < n := (SimplexCategory.len_le_of_epi fac.i).trans_lt k.2
  let j : Fin n := ⟨fac.Z.len, hd⟩
  exact inverseMap n H P Q (matchingIndexOfMono n j fac.p.op) ≫ H.Z.map fac.i.op

/-- Evaluate an original arrow between newly adjoined coefficients. -/
noncomputable def evalNewToNew
    (θ : op ⦋n⦌ ⟶ op ⦋n⦌)
    (fac : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop) :
    newObj n H P Q ⟶ newObj n H P Q := by
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  if hd : fac.Z.len < n then
    let j : Fin n := ⟨fac.Z.len, hd⟩
    exact inverseMap n H P Q (matchingIndexOfMono n j fac.p.op) ≫
      directMap n H P Q (latchingIndexOfEpi n j fac.i.op)
  else
    exact 𝟙 _

/-- Evaluate an arbitrary old-to-new operator by its canonical inverse/direct normal form. -/
noncomputable def oldToNew (k : Fin n) (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌) :
    H.Z.obj (oldDegree n k) ⟶ newObj n H P Q :=
  evalOldToNew n H P Q k θ (canonicalSimplexFactor θ)

/-- Evaluate an arbitrary new-to-old operator by its canonical inverse/direct normal form. -/
noncomputable def newToOld (k : Fin n) (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌) :
    newObj n H P Q ⟶ H.Z.obj (oldDegree n k) :=
  evalNewToOld n H P Q k θ (canonicalSimplexFactor θ)

/-- Evaluate a new-degree endomorphism. A lower image uses the inverse/direct seam; a full image is
the identity. -/
noncomputable def newToNew (θ : op ⦋n⦌ ⟶ op ⦋n⦌) :
    newObj n H P Q ⟶ newObj n H P Q :=
  evalNewToNew n H P Q θ (canonicalSimplexFactor θ)

private theorem oldToNew_of_factor (k j : Fin n)
    (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌)
    (e : ⦋n⦌ ⟶ ⦋j.1⦌) [Epi e]
    (m : ⦋j.1⦌ ⟶ ⦋k.1⦌) [Mono m]
    (fac : e ≫ m = θ.unop) :
    oldToNew n H P Q k θ =
      H.Z.map m.op ≫ directMap n H P Q (latchingIndexOfEpi n j e.op) := by
  let custom : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop :=
    .mk ⦋j.1⦌ e m fac (by exact inferInstance) (by exact inferInstance)
  have h : canonicalSimplexFactor θ = custom := by
    let _ := SimplexCategory.reedyStructure.subsingleton_mapFactorizationData θ.unop
    exact Subsingleton.elim _ _
  change evalOldToNew n H P Q k θ (canonicalSimplexFactor θ) = _
  exact (congrArg (evalOldToNew n H P Q k θ) h).trans (by rfl)

private theorem newToOld_of_factor (k j : Fin n)
    (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌)
    (e : ⦋k.1⦌ ⟶ ⦋j.1⦌) [Epi e]
    (m : ⦋j.1⦌ ⟶ ⦋n⦌) [Mono m]
    (fac : e ≫ m = θ.unop) :
    newToOld n H P Q k θ =
      inverseMap n H P Q (matchingIndexOfMono n j m.op) ≫ H.Z.map e.op := by
  let custom : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop :=
    .mk ⦋j.1⦌ e m fac (by exact inferInstance) (by exact inferInstance)
  have h : canonicalSimplexFactor θ = custom := by
    let _ := SimplexCategory.reedyStructure.subsingleton_mapFactorizationData θ.unop
    exact Subsingleton.elim _ _
  change evalNewToOld n H P Q k θ (canonicalSimplexFactor θ) = _
  exact (congrArg (evalNewToOld n H P Q k θ) h).trans (by rfl)

private def latchingIndexHomOfEpiComp {j k : Fin n}
    (e : ⦋n⦌ ⟶ ⦋j.1⦌) [Epi e]
    (d : ⦋j.1⦌ ⟶ ⦋k.1⦌) [Epi d] :
    latchingIndexOfEpi n k (e ≫ d).op ⟶ latchingIndexOfEpi n j e.op :=
  ObjectProperty.homMk (CostructuredArrow.homMk d.op (by
    change d.op ≫ e.op = (e ≫ d).op
    rfl))

private theorem directMap_comp_epi {j k : Fin n}
    (e : ⦋n⦌ ⟶ ⦋j.1⦌) [Epi e]
    (d : ⦋j.1⦌ ⟶ ⦋k.1⦌) [Epi d] :
    H.Z.map d.op ≫ directMap n H P Q (latchingIndexOfEpi n j e.op) =
      directMap n H P Q (latchingIndexOfEpi n k (e ≫ d).op) := by
  exact directMap_naturality n H P Q (latchingIndexHomOfEpiComp n e d)

private def matchingIndexHomOfMonoComp {j k : Fin n}
    (m : ⦋j.1⦌ ⟶ ⦋n⦌) [Mono m]
    (d : ⦋k.1⦌ ⟶ ⦋j.1⦌) [Mono d] :
    matchingIndexOfMono n j m.op ⟶ matchingIndexOfMono n k (d ≫ m).op :=
  ObjectProperty.homMk (StructuredArrow.homMk d.op (by
    change m.op ≫ d.op = (d ≫ m).op
    rfl))

private theorem inverseMap_comp_mono {j k : Fin n}
    (m : ⦋j.1⦌ ⟶ ⦋n⦌) [Mono m]
    (d : ⦋k.1⦌ ⟶ ⦋j.1⦌) [Mono d] :
    inverseMap n H P Q (matchingIndexOfMono n j m.op) ≫ H.Z.map d.op =
      inverseMap n H P Q (matchingIndexOfMono n k (d ≫ m).op) := by
  exact inverseMap_naturality n H P Q (matchingIndexHomOfMonoComp n m d)

private theorem newToNew_of_lower_factor (j : Fin n)
    (θ : op ⦋n⦌ ⟶ op ⦋n⦌)
    (e : ⦋n⦌ ⟶ ⦋j.1⦌) [Epi e]
    (m : ⦋j.1⦌ ⟶ ⦋n⦌) [Mono m]
    (fac : e ≫ m = θ.unop) :
    newToNew n H P Q θ =
      inverseMap n H P Q (matchingIndexOfMono n j m.op) ≫
        directMap n H P Q (latchingIndexOfEpi n j e.op) := by
  let custom : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop :=
    .mk ⦋j.1⦌ e m fac (by exact inferInstance) (by exact inferInstance)
  have h : canonicalSimplexFactor θ = custom := by
    let _ := SimplexCategory.reedyStructure.subsingleton_mapFactorizationData θ.unop
    exact Subsingleton.elim _ _
  change evalNewToNew n H P Q θ (canonicalSimplexFactor θ) = _
  exact (congrArg (evalNewToNew n H P Q θ) h).trans (by simp [evalNewToNew, custom, j.2])

private theorem newToNew_of_full_factor
    (θ : op ⦋n⦌ ⟶ op ⦋n⦌)
    (e : ⦋n⦌ ⟶ ⦋n⦌) [Epi e]
    (m : ⦋n⦌ ⟶ ⦋n⦌) [Mono m]
    (fac : e ≫ m = θ.unop) :
    newToNew n H P Q θ = 𝟙 _ := by
  let custom : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop :=
    .mk ⦋n⦌ e m fac (by exact inferInstance) (by exact inferInstance)
  have h : canonicalSimplexFactor θ = custom := by
    let _ := SimplexCategory.reedyStructure.subsingleton_mapFactorizationData θ.unop
    exact Subsingleton.elim _ _
  change evalNewToNew n H P Q θ (canonicalSimplexFactor θ) = _
  exact (congrArg (evalNewToNew n H P Q θ) h).trans (by simp [evalNewToNew, custom])

/-- The original simplex endomorphism represented at the final degree. -/
def lastEndHom (θ : degreeLast n ⟶ degreeLast n) :
    op ⦋n⦌ ⟶ op ⦋n⦌ := by
  exact θ

/-- The original lower-degree arrow represented inside the successor truncation. -/
def oldHom {a b : DegreeLT n}
    (θ : (degreeSucc n).obj a ⟶ (degreeSucc n).obj b) : a ⟶ b := by
  exact θ

/-- The original incoming simplex arrow represented in the successor truncation. -/
def oldToLastHom (a : DegreeLT n)
    (θ : (degreeSucc n).obj a ⟶ degreeLast n) :
    op ⦋a.degree.1⦌ ⟶ op ⦋n⦌ := by
  exact θ

/-- The original outgoing simplex arrow represented in the successor truncation. -/
def lastToOldHom (b : DegreeLT n)
    (θ : degreeLast n ⟶ (degreeSucc n).obj b) :
    op ⦋n⦌ ⟶ op ⦋b.degree.1⦌ := by
  exact θ

@[simp]
private theorem lastEndHom_id :
    lastEndHom n (𝟙 (degreeLast n)) = 𝟙 (op ⦋n⦌) :=
  rfl

@[simp]
private theorem oldHom_id (a : DegreeLT n) :
    oldHom n (𝟙 ((degreeSucc n).obj a)) = 𝟙 a :=
  rfl

/-- The raw successor-stage map, split by whether each endpoint is old or newly adjoined. -/
noncomputable def extendMap {a b : DegreeLT (n + 1)} (θ : a ⟶ b) :
    extendObj n H P Q a ⟶ extendObj n H P Q b := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  induction a using Fin.lastCases with
  | last =>
      induction b using Fin.lastCases with
      | last => simpa [extendObj] using newToNew n H P Q (lastEndHom n θ)
      | cast b =>
          let b' : DegreeLT n := oldDegree n b
          simpa [extendObj, b'] using newToOld n H P Q b (lastToOldHom n b' θ)
  | cast a =>
      induction b using Fin.lastCases with
      | last =>
          let a' : DegreeLT n := oldDegree n a
          simpa [extendObj, a'] using oldToNew n H P Q a (oldToLastHom n a' θ)
      | cast b =>
          let θ' : oldDegree n a ⟶ oldDegree n b :=
            oldHom n θ
          simpa [extendObj] using H.Z.map θ'

private theorem extendMap_last_last (θ : degreeLast n ⟶ degreeLast n) :
    HEq (extendMap n H P Q θ) (newToNew n H P Q (lastEndHom n θ)) := by
  unfold degreeLast at θ ⊢
  unfold extendMap
  simp [lastEndHom]

private theorem extendMap_cast_cast {a b : DegreeLT n}
    (θ : (degreeSucc n).obj a ⟶ (degreeSucc n).obj b) :
    HEq (extendMap n H P Q θ) (H.Z.map (oldHom n θ)) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  unfold degreeSucc at θ ⊢
  unfold extendMap
  simp [oldHom]
  rfl

private theorem extendMap_cast_last (a : DegreeLT n)
    (θ : (degreeSucc n).obj a ⟶ degreeLast n) :
    HEq (extendMap n H P Q θ)
      (oldToNew n H P Q a.degree (oldToLastHom n a θ)) := by
  rcases a with ⟨a⟩
  unfold degreeSucc degreeLast at θ ⊢
  unfold extendMap
  simp [oldToLastHom]

private theorem extendMap_last_cast (b : DegreeLT n)
    (θ : degreeLast n ⟶ (degreeSucc n).obj b) :
    HEq (extendMap n H P Q θ)
      (newToOld n H P Q b.degree (lastToOldHom n b θ)) := by
  rcases b with ⟨b⟩
  unfold degreeSucc degreeLast at θ ⊢
  unfold extendMap
  simp [lastToOldHom]

private theorem eq_last_or_succ (a : DegreeLT (n + 1)) :
    a = degreeLast n ∨ ∃ k : DegreeLT n, a = (degreeSucc n).obj k := by
  rcases a with ⟨a⟩
  refine Fin.lastCases (Or.inl ?_) (fun k => Or.inr ⟨oldDegree n k, ?_⟩) a
  · apply DegreeLT.ext
    rfl
  · apply DegreeLT.ext
    rfl

@[simp]
private theorem newToNew_id :
    newToNew n H P Q (𝟙 (op ⦋n⦌)) = 𝟙 _ := by
  let custom : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) (𝟙 (op ⦋n⦌)).unop :=
    .mk ⦋n⦌ (𝟙 _) (𝟙 _) (by simp) (by exact inferInstance) (by exact inferInstance)
  have h : canonicalSimplexFactor (𝟙 (op ⦋n⦌)) = custom := by
    let _ := SimplexCategory.reedyStructure.subsingleton_mapFactorizationData
      (𝟙 (op ⦋n⦌)).unop
    exact Subsingleton.elim _ _
  simpa [custom, newToNew, evalNewToNew] using
    congrArg (evalNewToNew n H P Q (𝟙 (op ⦋n⦌))) h

private theorem extendMap_id (a : DegreeLT (n + 1)) :
    extendMap n H P Q (𝟙 a) = 𝟙 (extendObj n H P Q a) := by
  rcases eq_last_or_succ (n := n) a with rfl | ⟨k, rfl⟩
  · have h₁ := extendMap_last_last n H P Q (𝟙 (degreeLast n))
    have h₂ : newToNew n H P Q (lastEndHom n (𝟙 (degreeLast n))) =
        𝟙 (newObj n H P Q) := by simp
    have h₃ : HEq (𝟙 (newObj n H P Q))
        (𝟙 (extendObj n H P Q (degreeLast n))) := by
      let ho := extendObj_last n H P Q
      exact (eqToHom_heq_id_cod _ _ ho).symm.trans (eqToHom_heq_id_dom _ _ ho)
    exact eq_of_heq (h₁.trans (h₂ ▸ h₃))
  · have h₁ := extendMap_cast_cast n H P Q (𝟙 ((degreeSucc n).obj k))
    have h₂ : H.Z.map (oldHom n (𝟙 ((degreeSucc n).obj k))) = 𝟙 (H.Z.obj k) := by
      simp
    have h₃ : HEq (𝟙 (H.Z.obj k))
        (𝟙 (extendObj n H P Q ((degreeSucc n).obj k))) := by
      let ho := extendObj_castSucc n H P Q k
      exact (eqToHom_heq_id_cod _ _ ho).symm.trans (eqToHom_heq_id_dom _ _ ho)
    exact eq_of_heq (h₁.trans (h₂ ▸ h₃))

set_option backward.isDefEq.respectTransparency false in
private theorem oldToNew_comp_newToOld (a c : Fin n)
    (α : op ⦋a.1⦌ ⟶ op ⦋n⦌) (β : op ⦋n⦌ ⟶ op ⦋c.1⦌) :
    oldToNew n H P Q a α ≫ newToOld n H P Q c β =
      H.Z.map (stageHom n (α ≫ β)) := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  let _ : Epi fa.i := fa.hi
  let _ : Mono fa.p := fa.hp
  let _ : Epi fb.i := fb.hi
  let _ : Mono fb.p := fb.hp
  have ha : fa.Z.len < n := (SimplexCategory.len_le_of_mono fa.p).trans_lt a.2
  have hb : fb.Z.len < n := (SimplexCategory.len_le_of_epi fb.i).trans_lt c.2
  let ja : Fin n := ⟨fa.Z.len, ha⟩
  let jb : Fin n := ⟨fb.Z.len, hb⟩
  change (H.Z.map fa.p.op ≫ directMap n H P Q (latchingIndexOfEpi n ja fa.i.op)) ≫
      (inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op) ≫ H.Z.map fb.i.op) = _
  have hm := congrArg
    (fun t => H.Z.map fa.p.op ≫ t ≫ H.Z.map fb.i.op)
    (directMap_comp_inverseMap n H P Q
      (latchingIndexOfEpi n ja fa.i.op) (matchingIndexOfMono n jb fb.p.op))
  have hm' :
      (H.Z.map fa.p.op ≫ directMap n H P Q (latchingIndexOfEpi n ja fa.i.op)) ≫
        (inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op) ≫ H.Z.map fb.i.op) =
      H.Z.map (fa.p.op ≫
        stageCrossHom n (latchingIndexOfEpi n ja fa.i.op)
          (matchingIndexOfMono n jb fb.p.op) ≫ fb.i.op) := by
    simpa only [Category.assoc, ← H.Z.map_comp] using hm
  apply hm'.trans
  apply H.Z.congr_map
  change (fa.p.op ≫ (fb.p ≫ fa.i).op) ≫ fb.i.op = α ≫ β
  calc
    (fa.p.op ≫ (fb.p ≫ fa.i).op) ≫ fb.i.op =
        (fa.i ≫ fa.p).op ≫ (fb.i ≫ fb.p).op := by
      simp only [op_comp, Category.assoc]
    _ = α ≫ β := by rw [fa.fac, fb.fac]; simp

/-- The factorization of the direct--inverse middle composite in two normal forms. -/
private noncomputable def middleFactor {r s t : ℕ}
    (α : op ⦋r⦌ ⟶ op ⦋s⦌) (β : op ⦋s⦌ ⟶ op ⦋t⦌) :
    (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory)
      ((canonicalSimplexFactor β).p ≫ (canonicalSimplexFactor α).i) :=
  SimplexCategory.reedyStructure.mapFactorizationData _

/-- The composite normal form obtained by factoring the middle direct--inverse seam. -/
private noncomputable def compositeFactor {r s t : ℕ}
    (α : op ⦋r⦌ ⟶ op ⦋s⦌) (β : op ⦋s⦌ ⟶ op ⦋t⦌) :
    (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) (α ≫ β).unop := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  let d := middleFactor α β
  let _ : Epi fa.i := fa.hi
  let _ : Mono fa.p := fa.hp
  let _ : Epi fb.i := fb.hi
  let _ : Mono fb.p := fb.hp
  let _ : Epi d.i := d.hi
  let _ : Mono d.p := d.hp
  exact .mk d.Z (fb.i ≫ d.i) (d.p ≫ fa.p) (by
    calc
      (fb.i ≫ d.i) ≫ (d.p ≫ fa.p) =
          fb.i ≫ (d.i ≫ d.p) ≫ fa.p := by simp only [Category.assoc]
      _ = fb.i ≫ (fb.p ≫ fa.i) ≫ fa.p := by rw [d.fac]
      _ = (fb.i ≫ fb.p) ≫ (fa.i ≫ fa.p) := by simp only [Category.assoc]
      _ = β.unop ≫ α.unop := by rw [fb.fac, fa.fac]
      _ = (α ≫ β).unop := by rfl)
    (by exact inferInstance) (by exact inferInstance)

private theorem canonical_comp_eq_compositeFactor {r s t : ℕ}
    (α : op ⦋r⦌ ⟶ op ⦋s⦌) (β : op ⦋s⦌ ⟶ op ⦋t⦌) :
    canonicalSimplexFactor (α ≫ β) = compositeFactor α β := by
  let _ := SimplexCategory.reedyStructure.subsingleton_mapFactorizationData (α ≫ β).unop
  exact Subsingleton.elim _ _

private theorem middleFactor_len_le {r s t : ℕ}
    (α : op ⦋r⦌ ⟶ op ⦋s⦌) (β : op ⦋s⦌ ⟶ op ⦋t⦌) :
    (middleFactor α β).Z.len ≤ s := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  let d := middleFactor α β
  have h := SimplexCategory.reedyStructure.degHom_le fb.p fa.i
  rw [SimplexCategory.reedyStructure.degHom_eq d] at h
  exact h

private def factorInverseHom (a : Fin n)
    {b : ℕ} {θ : op ⦋a.1⦌ ⟶ op ⦋b⦌}
    (fac : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop)
    (hd : fac.Z.len < n) :
    oldDegree n a ⟶ oldDegree n ⟨fac.Z.len, hd⟩ :=
  fac.p.op

private def factorDirectHom (b : Fin n)
    {a : ℕ} {θ : op ⦋a⦌ ⟶ op ⦋b.1⦌}
    (fac : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop)
    (hd : fac.Z.len < n) :
    oldDegree n ⟨fac.Z.len, hd⟩ ⟶ oldDegree n b :=
  fac.i.op

omit [HasPushouts C] [HasPullbacks C]
    [HasColimitsOfShape (latchingIndex n) C] [HasLimitsOfShape (matchingIndex n) C] in
set_option backward.isDefEq.respectTransparency false in
private theorem oldMap_of_data (a b : Fin n)
    (θ : op ⦋a.1⦌ ⟶ op ⦋b.1⦌)
    (fac : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop)
    (hd : fac.Z.len < n) :
    H.Z.map (stageHom n θ) =
      H.Z.map (factorInverseHom n a fac hd) ≫
        H.Z.map (factorDirectHom n b fac hd) := by
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  rw [← H.Z.map_comp]
  apply H.Z.congr_map
  change θ = fac.p.op ≫ fac.i.op
  rw [← op_comp, fac.fac]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem oldMap_comp_oldToNew (a b : Fin n)
    (α : op ⦋a.1⦌ ⟶ op ⦋b.1⦌) (β : op ⦋b.1⦌ ⟶ op ⦋n⦌) :
    H.Z.map (stageHom n α) ≫ oldToNew n H P Q b β =
      oldToNew n H P Q a (α ≫ β) := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  let d := middleFactor α β
  let cf := compositeFactor α β
  let _ : Epi fa.i := fa.hi
  let _ : Mono fa.p := fa.hp
  let _ : Epi fb.i := fb.hi
  let _ : Mono fb.p := fb.hp
  let _ : Epi d.i := d.hi
  let _ : Mono d.p := d.hp
  have hfa : fa.Z.len < n := (SimplexCategory.len_le_of_mono fa.p).trans_lt a.2
  have hfb : fb.Z.len < n := (SimplexCategory.len_le_of_mono fb.p).trans_lt b.2
  have hd : d.Z.len < n := (middleFactor_len_le α β).trans_lt b.2
  let ja : Fin n := ⟨fa.Z.len, hfa⟩
  let jb : Fin n := ⟨fb.Z.len, hfb⟩
  let jd : Fin n := ⟨d.Z.len, hd⟩
  have hα := oldMap_of_data n H a b α fa hfa
  have hβ := oldToNew_of_factor n H P Q b jb β fb.i fb.p fb.fac
  have hβ' : oldToNew n H P Q b β =
      H.Z.map (factorInverseHom n b fb hfb) ≫
        directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by
    simpa [factorInverseHom] using hβ
  have hc := oldToNew_of_factor n H P Q a jd (α ≫ β)
    (fb.i ≫ d.i) (d.p ≫ fa.p) cf.fac
  have hc' : oldToNew n H P Q a (α ≫ β) =
      H.Z.map (factorInverseHom n a cf hd) ≫
        directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by
    simpa [factorInverseHom, cf, compositeFactor] using hc
  rw [hα, hβ', hc']
  have hm :
      H.Z.map (factorDirectHom n b fa hfa) ≫
          H.Z.map (factorInverseHom n b fb hfb) =
        H.Z.map (factorInverseHom n ja d hd) ≫
          H.Z.map (factorDirectHom n jb d hd) := by
    rw [← H.Z.map_comp, ← H.Z.map_comp]
    apply H.Z.congr_map
    change fa.i.op ≫ fb.p.op = d.p.op ≫ d.i.op
    rw [← op_comp, ← op_comp, d.fac]
  have he :
      H.Z.map (factorDirectHom n jb d hd) ≫
          directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) =
        directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by
    simpa [factorDirectHom] using
      directMap_comp_epi (j := jb) (k := jd) n H P Q fb.i d.i
  have hp :
      H.Z.map (factorInverseHom n a fa hfa) ≫
          H.Z.map (factorInverseHom n ja d hd) =
        H.Z.map (factorInverseHom n a cf hd) := by
    rw [← H.Z.map_comp]
    apply H.Z.congr_map
    rfl
  calc
    (H.Z.map (factorInverseHom n a fa hfa) ≫
        H.Z.map (factorDirectHom n b fa hfa)) ≫
          (H.Z.map (factorInverseHom n b fb hfb) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) =
      H.Z.map (factorInverseHom n a fa hfa) ≫
        (H.Z.map (factorDirectHom n b fa hfa) ≫
          H.Z.map (factorInverseHom n b fb hfb)) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by
              simp only [Category.assoc]
    _ = H.Z.map (factorInverseHom n a fa hfa) ≫
        (H.Z.map (factorInverseHom n ja d hd) ≫
          H.Z.map (factorDirectHom n jb d hd)) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by rw [hm]
    _ = (H.Z.map (factorInverseHom n a fa hfa) ≫
          H.Z.map (factorInverseHom n ja d hd)) ≫
        (H.Z.map (factorDirectHom n jb d hd) ≫
          directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) := by
            simp only [Category.assoc]
    _ = (H.Z.map (factorInverseHom n a fa hfa) ≫
          H.Z.map (factorInverseHom n ja d hd)) ≫
        directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by rw [he]
    _ = H.Z.map (factorInverseHom n a cf hd) ≫
        directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by rw [hp]

set_option backward.isDefEq.respectTransparency false in
private theorem newToOld_comp_oldMap (a c : Fin n)
    (α : op ⦋n⦌ ⟶ op ⦋a.1⦌) (β : op ⦋a.1⦌ ⟶ op ⦋c.1⦌) :
    newToOld n H P Q a α ≫ H.Z.map (stageHom n β) =
      newToOld n H P Q c (α ≫ β) := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  let d := middleFactor α β
  let cf := compositeFactor α β
  let _ : Epi fa.i := fa.hi
  let _ : Mono fa.p := fa.hp
  let _ : Epi fb.i := fb.hi
  let _ : Mono fb.p := fb.hp
  let _ : Epi d.i := d.hi
  let _ : Mono d.p := d.hp
  have hfa : fa.Z.len < n := (SimplexCategory.len_le_of_epi fa.i).trans_lt a.2
  have hfb : fb.Z.len < n := (SimplexCategory.len_le_of_mono fb.p).trans_lt a.2
  have hd : d.Z.len < n := (middleFactor_len_le α β).trans_lt a.2
  let ja : Fin n := ⟨fa.Z.len, hfa⟩
  let jb : Fin n := ⟨fb.Z.len, hfb⟩
  let jd : Fin n := ⟨d.Z.len, hd⟩
  have hα := newToOld_of_factor n H P Q a ja α fa.i fa.p fa.fac
  have hα' : newToOld n H P Q a α =
      inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        H.Z.map (factorDirectHom n a fa hfa) := by
    simpa [factorDirectHom] using hα
  have hβ := oldMap_of_data n H a c β fb hfb
  have hc := newToOld_of_factor n H P Q c jd (α ≫ β)
    (fb.i ≫ d.i) (d.p ≫ fa.p) cf.fac
  have hc' : newToOld n H P Q c (α ≫ β) =
      inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
        H.Z.map (factorDirectHom n c cf hd) := by
    simpa [factorDirectHom, cf, compositeFactor] using hc
  rw [hα', hβ, hc']
  have hm :
      H.Z.map (factorDirectHom n a fa hfa) ≫
          H.Z.map (factorInverseHom n a fb hfb) =
        H.Z.map (factorInverseHom n ja d hd) ≫
          H.Z.map (factorDirectHom n jb d hd) := by
    rw [← H.Z.map_comp, ← H.Z.map_comp]
    apply H.Z.congr_map
    change fa.i.op ≫ fb.p.op = d.p.op ≫ d.i.op
    rw [← op_comp, ← op_comp, d.fac]
  have he :
      inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
          H.Z.map (factorInverseHom n ja d hd) =
        inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) := by
    simpa [factorInverseHom] using
      inverseMap_comp_mono (j := ja) (k := jd) n H P Q fa.p d.p
  have hp :
      H.Z.map (factorDirectHom n jb d hd) ≫
          H.Z.map (factorDirectHom n c fb hfb) =
        H.Z.map (factorDirectHom n c cf hd) := by
    rw [← H.Z.map_comp]
    apply H.Z.congr_map
    rfl
  calc
    (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        H.Z.map (factorDirectHom n a fa hfa)) ≫
          (H.Z.map (factorInverseHom n a fb hfb) ≫
            H.Z.map (factorDirectHom n c fb hfb)) =
      inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        (H.Z.map (factorDirectHom n a fa hfa) ≫
          H.Z.map (factorInverseHom n a fb hfb)) ≫
            H.Z.map (factorDirectHom n c fb hfb) := by
              simp only [Category.assoc]
    _ = inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        (H.Z.map (factorInverseHom n ja d hd) ≫
          H.Z.map (factorDirectHom n jb d hd)) ≫
            H.Z.map (factorDirectHom n c fb hfb) := by rw [hm]
    _ = (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
          H.Z.map (factorInverseHom n ja d hd)) ≫
        (H.Z.map (factorDirectHom n jb d hd) ≫
          H.Z.map (factorDirectHom n c fb hfb)) := by
            simp only [Category.assoc]
    _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
        (H.Z.map (factorDirectHom n jb d hd) ≫
          H.Z.map (factorDirectHom n c fb hfb)) := by rw [he]
    _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
        H.Z.map (factorDirectHom n c cf hd) := by rw [hp]

set_option backward.isDefEq.respectTransparency false in
private theorem newToOld_comp_oldToNew (a : Fin n)
    (α : op ⦋n⦌ ⟶ op ⦋a.1⦌) (β : op ⦋a.1⦌ ⟶ op ⦋n⦌) :
    newToOld n H P Q a α ≫ oldToNew n H P Q a β =
      newToNew n H P Q (α ≫ β) := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  let d := middleFactor α β
  let cf := compositeFactor α β
  let _ : Epi fa.i := fa.hi
  let _ : Mono fa.p := fa.hp
  let _ : Epi fb.i := fb.hi
  let _ : Mono fb.p := fb.hp
  let _ : Epi d.i := d.hi
  let _ : Mono d.p := d.hp
  have hfa : fa.Z.len < n := (SimplexCategory.len_le_of_epi fa.i).trans_lt a.2
  have hfb : fb.Z.len < n := (SimplexCategory.len_le_of_mono fb.p).trans_lt a.2
  have hd : d.Z.len < n := (middleFactor_len_le α β).trans_lt a.2
  let ja : Fin n := ⟨fa.Z.len, hfa⟩
  let jb : Fin n := ⟨fb.Z.len, hfb⟩
  let jd : Fin n := ⟨d.Z.len, hd⟩
  have hα := newToOld_of_factor n H P Q a ja α fa.i fa.p fa.fac
  have hα' : newToOld n H P Q a α =
      inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        H.Z.map (factorDirectHom n a fa hfa) := by
    simpa [factorDirectHom] using hα
  have hβ := oldToNew_of_factor n H P Q a jb β fb.i fb.p fb.fac
  have hβ' : oldToNew n H P Q a β =
      H.Z.map (factorInverseHom n a fb hfb) ≫
        directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by
    simpa [factorInverseHom] using hβ
  have hc := newToNew_of_lower_factor n H P Q jd (α ≫ β)
    (fb.i ≫ d.i) (d.p ≫ fa.p) cf.fac
  rw [hα', hβ', hc]
  have hm :
      H.Z.map (factorDirectHom n a fa hfa) ≫
          H.Z.map (factorInverseHom n a fb hfb) =
        H.Z.map (factorInverseHom n ja d hd) ≫
          H.Z.map (factorDirectHom n jb d hd) := by
    rw [← H.Z.map_comp, ← H.Z.map_comp]
    apply H.Z.congr_map
    change fa.i.op ≫ fb.p.op = d.p.op ≫ d.i.op
    rw [← op_comp, ← op_comp, d.fac]
  have he :
      inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
          H.Z.map (factorInverseHom n ja d hd) =
        inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) := by
    simpa [factorInverseHom] using
      inverseMap_comp_mono (j := ja) (k := jd) n H P Q fa.p d.p
  have hp :
      H.Z.map (factorDirectHom n jb d hd) ≫
          directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) =
        directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by
    simpa [factorDirectHom] using
      directMap_comp_epi (j := jb) (k := jd) n H P Q fb.i d.i
  calc
    (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        H.Z.map (factorDirectHom n a fa hfa)) ≫
          (H.Z.map (factorInverseHom n a fb hfb) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) =
      inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        (H.Z.map (factorDirectHom n a fa hfa) ≫
          H.Z.map (factorInverseHom n a fb hfb)) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by
              simp only [Category.assoc]
    _ = inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
        (H.Z.map (factorInverseHom n ja d hd) ≫
          H.Z.map (factorDirectHom n jb d hd)) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by rw [hm]
    _ = (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
          H.Z.map (factorInverseHom n ja d hd)) ≫
        (H.Z.map (factorDirectHom n jb d hd) ≫
          directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) := by
            simp only [Category.assoc]
    _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
        (H.Z.map (factorDirectHom n jb d hd) ≫
          directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) := by rw [he]
    _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
        directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by rw [hp]

omit [HasPushouts C] [HasPullbacks C]
    [HasColimitsOfShape (latchingIndex n) C] [HasLimitsOfShape (matchingIndex n) C] in
private theorem eq_id_of_factor_not_lt
    (θ : op ⦋n⦌ ⟶ op ⦋n⦌)
    (fac : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) θ.unop)
    (h : ¬ fac.Z.len < n) : θ = 𝟙 _ := by
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  have hz : fac.Z.len = n := le_antisymm (SimplexCategory.len_le_of_mono fac.p) (not_lt.mp h)
  let _ : IsIso fac.p := (SimplexCategory.isIso_iff_of_mono fac.p).2 hz
  have hi : Epi θ.unop := by
    rw [← fac.fac]
    infer_instance
  apply Quiver.Hom.unop_inj
  simpa using SimplexCategory.eq_id_of_epi θ.unop

set_option backward.isDefEq.respectTransparency false in
private theorem middlePrimitive_refactor
    (a b : Fin n)
    (e : ⦋n⦌ ⟶ ⦋a.1⦌) [Epi e]
    (m : ⦋b.1⦌ ⟶ ⦋n⦌) [Mono m]
    (d : (epimorphisms SimplexCategory).MapFactorizationData
      (monomorphisms SimplexCategory) (m ≫ e))
    (hd : d.Z.len < n) :
    directMap n H P Q (latchingIndexOfEpi n a e.op) ≫
        inverseMap n H P Q (matchingIndexOfMono n b m.op) =
      H.Z.map (factorInverseHom n a d hd) ≫
        H.Z.map (factorDirectHom n b d hd) := by
  let _ : Epi d.i := d.hi
  let _ : Mono d.p := d.hp
  have hm := directMap_comp_inverseMap n H P Q
    (latchingIndexOfEpi n a e.op) (matchingIndexOfMono n b m.op)
  have hd' := oldMap_of_data n H a b (m ≫ e).op d hd
  apply hm.trans
  apply (H.Z.congr_map (by rfl)).trans
  exact hd'

set_option backward.isDefEq.respectTransparency false in
private theorem oldToNew_comp_newToNew (a : Fin n)
    (α : op ⦋a.1⦌ ⟶ op ⦋n⦌) (β : op ⦋n⦌ ⟶ op ⦋n⦌) :
    oldToNew n H P Q a α ≫ newToNew n H P Q β =
      oldToNew n H P Q a (α ≫ β) := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  by_cases hfb : fb.Z.len < n
  · let d := middleFactor α β
    let cf := compositeFactor α β
    let _ : Epi fa.i := fa.hi
    let _ : Mono fa.p := fa.hp
    let _ : Epi fb.i := fb.hi
    let _ : Mono fb.p := fb.hp
    let _ : Epi d.i := d.hi
    let _ : Mono d.p := d.hp
    have hfa : fa.Z.len < n := (SimplexCategory.len_le_of_mono fa.p).trans_lt a.2
    have hd : d.Z.len < n := (SimplexCategory.len_le_of_mono d.p).trans_lt hfa
    let ja : Fin n := ⟨fa.Z.len, hfa⟩
    let jb : Fin n := ⟨fb.Z.len, hfb⟩
    let jd : Fin n := ⟨d.Z.len, hd⟩
    have hα := oldToNew_of_factor n H P Q a ja α fa.i fa.p fa.fac
    have hα' : oldToNew n H P Q a α =
        H.Z.map (factorInverseHom n a fa hfa) ≫
          directMap n H P Q (latchingIndexOfEpi n ja fa.i.op) := by
      simpa [factorInverseHom] using hα
    have hβ := newToNew_of_lower_factor n H P Q jb β fb.i fb.p fb.fac
    have hc := oldToNew_of_factor n H P Q a jd (α ≫ β)
      (fb.i ≫ d.i) (d.p ≫ fa.p) cf.fac
    have hc' : oldToNew n H P Q a (α ≫ β) =
        H.Z.map (factorInverseHom n a cf hd) ≫
          directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by
      simpa [factorInverseHom, cf, compositeFactor] using hc
    rw [hα', hβ, hc']
    have hm := middlePrimitive_refactor n H P Q ja jb fa.i fb.p d hd
    have he :
        H.Z.map (factorInverseHom n a fa hfa) ≫
            H.Z.map (factorInverseHom n ja d hd) =
          H.Z.map (factorInverseHom n a cf hd) := by
      rw [← H.Z.map_comp]
      apply H.Z.congr_map
      rfl
    have hp :
        H.Z.map (factorDirectHom n jb d hd) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) =
          directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by
      simpa [factorDirectHom] using
        directMap_comp_epi (j := jb) (k := jd) n H P Q fb.i d.i
    calc
      (H.Z.map (factorInverseHom n a fa hfa) ≫
          directMap n H P Q (latchingIndexOfEpi n ja fa.i.op)) ≫
            (inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op) ≫
              directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) =
        H.Z.map (factorInverseHom n a fa hfa) ≫
          (directMap n H P Q (latchingIndexOfEpi n ja fa.i.op) ≫
            inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op)) ≫
              directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by
                simp only [Category.assoc]
      _ = H.Z.map (factorInverseHom n a fa hfa) ≫
          (H.Z.map (factorInverseHom n ja d hd) ≫
            H.Z.map (factorDirectHom n jb d hd)) ≫
              directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by rw [hm]
      _ = (H.Z.map (factorInverseHom n a fa hfa) ≫
            H.Z.map (factorInverseHom n ja d hd)) ≫
          (H.Z.map (factorDirectHom n jb d hd) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) := by
              simp only [Category.assoc]
      _ = H.Z.map (factorInverseHom n a cf hd) ≫
          (H.Z.map (factorDirectHom n jb d hd) ≫
            directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) := by rw [he]
      _ = H.Z.map (factorInverseHom n a cf hd) ≫
          directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by rw [hp]
  · have hβ : β = 𝟙 _ := eq_id_of_factor_not_lt n β fb hfb
    subst β
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem newToNew_comp_newToOld (c : Fin n)
    (α : op ⦋n⦌ ⟶ op ⦋n⦌) (β : op ⦋n⦌ ⟶ op ⦋c.1⦌) :
    newToNew n H P Q α ≫ newToOld n H P Q c β =
      newToOld n H P Q c (α ≫ β) := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  by_cases hfa : fa.Z.len < n
  · let d := middleFactor α β
    let cf := compositeFactor α β
    let _ : Epi fa.i := fa.hi
    let _ : Mono fa.p := fa.hp
    let _ : Epi fb.i := fb.hi
    let _ : Mono fb.p := fb.hp
    let _ : Epi d.i := d.hi
    let _ : Mono d.p := d.hp
    have hfb : fb.Z.len < n := (SimplexCategory.len_le_of_epi fb.i).trans_lt c.2
    have hd : d.Z.len < n := (SimplexCategory.len_le_of_mono d.p).trans_lt hfa
    let ja : Fin n := ⟨fa.Z.len, hfa⟩
    let jb : Fin n := ⟨fb.Z.len, hfb⟩
    let jd : Fin n := ⟨d.Z.len, hd⟩
    have hα := newToNew_of_lower_factor n H P Q ja α fa.i fa.p fa.fac
    have hβ := newToOld_of_factor n H P Q c jb β fb.i fb.p fb.fac
    have hβ' : newToOld n H P Q c β =
        inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op) ≫
          H.Z.map (factorDirectHom n c fb hfb) := by
      simpa [factorDirectHom] using hβ
    have hc := newToOld_of_factor n H P Q c jd (α ≫ β)
      (fb.i ≫ d.i) (d.p ≫ fa.p) cf.fac
    have hc' : newToOld n H P Q c (α ≫ β) =
        inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
          H.Z.map (factorDirectHom n c cf hd) := by
      simpa [factorDirectHom, cf, compositeFactor] using hc
    rw [hα, hβ', hc']
    have hm := middlePrimitive_refactor n H P Q ja jb fa.i fb.p d hd
    have he :
        inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
            H.Z.map (factorInverseHom n ja d hd) =
          inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) := by
      simpa [factorInverseHom] using
        inverseMap_comp_mono (j := ja) (k := jd) n H P Q fa.p d.p
    have hp :
        H.Z.map (factorDirectHom n jb d hd) ≫
            H.Z.map (factorDirectHom n c fb hfb) =
          H.Z.map (factorDirectHom n c cf hd) := by
      rw [← H.Z.map_comp]
      apply H.Z.congr_map
      rfl
    calc
      (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
          directMap n H P Q (latchingIndexOfEpi n ja fa.i.op)) ≫
            (inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op) ≫
              H.Z.map (factorDirectHom n c fb hfb)) =
        inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
          (directMap n H P Q (latchingIndexOfEpi n ja fa.i.op) ≫
            inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op)) ≫
              H.Z.map (factorDirectHom n c fb hfb) := by
                simp only [Category.assoc]
      _ = inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
          (H.Z.map (factorInverseHom n ja d hd) ≫
            H.Z.map (factorDirectHom n jb d hd)) ≫
              H.Z.map (factorDirectHom n c fb hfb) := by rw [hm]
      _ = (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
            H.Z.map (factorInverseHom n ja d hd)) ≫
          (H.Z.map (factorDirectHom n jb d hd) ≫
            H.Z.map (factorDirectHom n c fb hfb)) := by
              simp only [Category.assoc]
      _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
          (H.Z.map (factorDirectHom n jb d hd) ≫
            H.Z.map (factorDirectHom n c fb hfb)) := by rw [he]
      _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
          H.Z.map (factorDirectHom n c cf hd) := by rw [hp]
  · have hα : α = 𝟙 _ := eq_id_of_factor_not_lt n α fa hfa
    subst α
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem newToNew_comp_newToNew
    (α β : op ⦋n⦌ ⟶ op ⦋n⦌) :
    newToNew n H P Q α ≫ newToNew n H P Q β =
      newToNew n H P Q (α ≫ β) := by
  let fa := canonicalSimplexFactor α
  let fb := canonicalSimplexFactor β
  by_cases hfa : fa.Z.len < n
  · by_cases hfb : fb.Z.len < n
    · let d := middleFactor α β
      let cf := compositeFactor α β
      let _ : Epi fa.i := fa.hi
      let _ : Mono fa.p := fa.hp
      let _ : Epi fb.i := fb.hi
      let _ : Mono fb.p := fb.hp
      let _ : Epi d.i := d.hi
      let _ : Mono d.p := d.hp
      have hd : d.Z.len < n := (SimplexCategory.len_le_of_mono d.p).trans_lt hfa
      let ja : Fin n := ⟨fa.Z.len, hfa⟩
      let jb : Fin n := ⟨fb.Z.len, hfb⟩
      let jd : Fin n := ⟨d.Z.len, hd⟩
      have hα := newToNew_of_lower_factor n H P Q ja α fa.i fa.p fa.fac
      have hβ := newToNew_of_lower_factor n H P Q jb β fb.i fb.p fb.fac
      have hc := newToNew_of_lower_factor n H P Q jd (α ≫ β)
        (fb.i ≫ d.i) (d.p ≫ fa.p) cf.fac
      rw [hα, hβ, hc]
      have hm := middlePrimitive_refactor n H P Q ja jb fa.i fb.p d hd
      have he :
          inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
              H.Z.map (factorInverseHom n ja d hd) =
            inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) := by
        simpa [factorInverseHom] using
          inverseMap_comp_mono (j := ja) (k := jd) n H P Q fa.p d.p
      have hp :
          H.Z.map (factorDirectHom n jb d hd) ≫
              directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) =
            directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by
        simpa [factorDirectHom] using
          directMap_comp_epi (j := jb) (k := jd) n H P Q fb.i d.i
      calc
        (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
            directMap n H P Q (latchingIndexOfEpi n ja fa.i.op)) ≫
              (inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op) ≫
                directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) =
          inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
            (directMap n H P Q (latchingIndexOfEpi n ja fa.i.op) ≫
              inverseMap n H P Q (matchingIndexOfMono n jb fb.p.op)) ≫
                directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by
                  simp only [Category.assoc]
        _ = inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
            (H.Z.map (factorInverseHom n ja d hd) ≫
              H.Z.map (factorDirectHom n jb d hd)) ≫
                directMap n H P Q (latchingIndexOfEpi n jb fb.i.op) := by rw [hm]
        _ = (inverseMap n H P Q (matchingIndexOfMono n ja fa.p.op) ≫
              H.Z.map (factorInverseHom n ja d hd)) ≫
            (H.Z.map (factorDirectHom n jb d hd) ≫
              directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) := by
                simp only [Category.assoc]
        _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
            (H.Z.map (factorDirectHom n jb d hd) ≫
              directMap n H P Q (latchingIndexOfEpi n jb fb.i.op)) := by rw [he]
        _ = inverseMap n H P Q (matchingIndexOfMono n jd (d.p ≫ fa.p).op) ≫
            directMap n H P Q (latchingIndexOfEpi n jd (fb.i ≫ d.i).op) := by rw [hp]
    · have hβ : β = 𝟙 _ := eq_id_of_factor_not_lt n β fb hfb
      subst β
      simp
  · have hα : α = 𝟙 _ := eq_id_of_factor_not_lt n α fa hfa
    subst α
    simp

omit [HasPushouts C] [HasPullbacks C]
    [HasColimitsOfShape (latchingIndex n) C] [HasLimitsOfShape (matchingIndex n) C] in
private theorem eq_comp_of_heq
    {A B D A' B' D' : C}
    {f₁ : A ⟶ B} {f₂ : B ⟶ D} {f₃ : A ⟶ D}
    {g₁ : A' ⟶ B'} {g₂ : B' ⟶ D'} {g₃ : A' ⟶ D'}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (h₁ : HEq f₁ g₁) (h₂ : HEq f₂ g₂) (h₃ : HEq f₃ g₃)
    (hcomp : g₁ ≫ g₂ = g₃) : f₁ ≫ f₂ = f₃ := by
  apply eq_of_heq
  exact (heq_comp hA hB hD h₁ h₂).trans ((heq_of_eq hcomp).trans h₃.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem extendMap_comp {a b c : DegreeLT (n + 1)}
    (u : a ⟶ b) (v : b ⟶ c) :
    extendMap n H P Q u ≫ extendMap n H P Q v = extendMap n H P Q (u ≫ v) := by
  rcases eq_last_or_succ (n := n) a with rfl | ⟨a, rfl⟩
  · rcases eq_last_or_succ (n := n) b with rfl | ⟨b, rfl⟩
    · rcases eq_last_or_succ (n := n) c with rfl | ⟨c, rfl⟩
      · apply eq_comp_of_heq
          (extendObj_last n H P Q) (extendObj_last n H P Q) (extendObj_last n H P Q)
          (extendMap_last_last n H P Q u) (extendMap_last_last n H P Q v)
          (extendMap_last_last n H P Q (u ≫ v))
        exact newToNew_comp_newToNew n H P Q (lastEndHom n u) (lastEndHom n v)
      · apply eq_comp_of_heq
          (extendObj_last n H P Q) (extendObj_last n H P Q) (extendObj_castSucc n H P Q c)
          (extendMap_last_last n H P Q u) (extendMap_last_cast n H P Q c v)
          (extendMap_last_cast n H P Q c (u ≫ v))
        exact newToNew_comp_newToOld n H P Q c.degree
          (lastEndHom n u) (lastToOldHom n c v)
    · rcases eq_last_or_succ (n := n) c with rfl | ⟨c, rfl⟩
      · apply eq_comp_of_heq
          (extendObj_last n H P Q) (extendObj_castSucc n H P Q b) (extendObj_last n H P Q)
          (extendMap_last_cast n H P Q b u) (extendMap_cast_last n H P Q b v)
          (extendMap_last_last n H P Q (u ≫ v))
        exact newToOld_comp_oldToNew n H P Q b.degree
          (lastToOldHom n b u) (oldToLastHom n b v)
      · apply eq_comp_of_heq
          (extendObj_last n H P Q) (extendObj_castSucc n H P Q b) (extendObj_castSucc n H P Q c)
          (extendMap_last_cast n H P Q b u) (extendMap_cast_cast n H P Q v)
          (extendMap_last_cast n H P Q c (u ≫ v))
        exact newToOld_comp_oldMap n H P Q b.degree c.degree
          (lastToOldHom n b u) (oldHom n v)
  · rcases eq_last_or_succ (n := n) b with rfl | ⟨b, rfl⟩
    · rcases eq_last_or_succ (n := n) c with rfl | ⟨c, rfl⟩
      · apply eq_comp_of_heq
          (extendObj_castSucc n H P Q a) (extendObj_last n H P Q) (extendObj_last n H P Q)
          (extendMap_cast_last n H P Q a u) (extendMap_last_last n H P Q v)
          (extendMap_cast_last n H P Q a (u ≫ v))
        exact oldToNew_comp_newToNew n H P Q a.degree
          (oldToLastHom n a u) (lastEndHom n v)
      · apply eq_comp_of_heq
          (extendObj_castSucc n H P Q a) (extendObj_last n H P Q) (extendObj_castSucc n H P Q c)
          (extendMap_cast_last n H P Q a u) (extendMap_last_cast n H P Q c v)
          (extendMap_cast_cast n H P Q (u ≫ v))
        exact oldToNew_comp_newToOld n H P Q a.degree c.degree
          (oldToLastHom n a u) (lastToOldHom n c v)
    · rcases eq_last_or_succ (n := n) c with rfl | ⟨c, rfl⟩
      · apply eq_comp_of_heq
          (extendObj_castSucc n H P Q a) (extendObj_castSucc n H P Q b) (extendObj_last n H P Q)
          (extendMap_cast_cast n H P Q u) (extendMap_cast_last n H P Q b v)
          (extendMap_cast_last n H P Q a (u ≫ v))
        exact oldMap_comp_oldToNew n H P Q a.degree b.degree
          (oldHom n u) (oldToLastHom n b v)
      · apply eq_comp_of_heq
          (extendObj_castSucc n H P Q a) (extendObj_castSucc n H P Q b)
          (extendObj_castSucc n H P Q c)
          (extendMap_cast_cast n H P Q u) (extendMap_cast_cast n H P Q v)
          (extendMap_cast_cast n H P Q (u ≫ v))
        exact (H.Z.map_comp (oldHom n u) (oldHom n v)).symm

/-- The one-degree extension of the partial stage functor. -/
noncomputable def extend : DegreeLT (n + 1) ⥤ C where
  obj := extendObj n H P Q
  map := extendMap n H P Q
  map_id := by exact extendMap_id n H P Q
  map_comp := fun u v => by exact (extendMap_comp n H P Q u v).symm

@[simp]
private theorem extend_obj_castSucc (a : DegreeLT n) :
    (extend n H P Q).obj ((degreeSucc n).obj a) = H.Z.obj a :=
  extendObj_castSucc n H P Q a

@[simp]
private theorem extend_obj_last :
    (extend n H P Q).obj (degreeLast n) = newObj n H P Q :=
  extendObj_last n H P Q

/-- On two old endpoints, the extended map is the old stage map. The heterogeneous statement keeps
the exact object equalities visible for the next stability leaf. -/
private theorem extend_map_castSucc {a b : DegreeLT n} (u : a ⟶ b) :
    HEq ((extend n H P Q).map ((degreeSucc n).map u)) (H.Z.map u) :=
  extendMap_cast_cast n H P Q ((degreeSucc n).map u)

/-- Characteristic equation for a map between two copies of the new degree. -/
private theorem extend_map_last (u : degreeLast n ⟶ degreeLast n) :
    HEq ((extend n H P Q).map u) (newToNew n H P Q (lastEndHom n u)) :=
  extendMap_last_last n H P Q u

/-- Characteristic equation for a map from an old degree into the new degree. -/
private theorem extend_map_castSucc_last (a : DegreeLT n)
    (u : (degreeSucc n).obj a ⟶ degreeLast n) :
    HEq ((extend n H P Q).map u)
      (oldToNew n H P Q a.degree (oldToLastHom n a u)) :=
  extendMap_cast_last n H P Q a u

/-- Characteristic equation for a map from the new degree into an old degree. -/
private theorem extend_map_last_castSucc (b : DegreeLT n)
    (u : degreeLast n ⟶ (degreeSucc n).obj b) :
    HEq ((extend n H P Q).map u)
      (newToOld n H P Q b.degree (lastToOldHom n b u)) :=
  extendMap_last_cast n H P Q b u

set_option backward.isDefEq.respectTransparency false in
private theorem i_naturality_oldToNew (a : Fin n)
    (θ : op ⦋a.1⦌ ⟶ op ⦋n⦌) :
    X.map θ ≫ iNew n H P Q =
      H.i.app (oldDegree n a) ≫ oldToNew n H P Q a θ := by
  let fac := canonicalSimplexFactor θ
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  have hd : fac.Z.len < n := (SimplexCategory.len_le_of_mono fac.p).trans_lt a.2
  let j₀ : Fin n := ⟨fac.Z.len, hd⟩
  have hθ := oldToNew_of_factor n H P Q a j₀ θ fac.i fac.p fac.fac
  have hθ' : oldToNew n H P Q a θ =
      H.Z.map (factorInverseHom n a fac hd) ≫
        directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by
    simpa [factorInverseHom] using hθ
  have hmap : X.map θ =
      X.map (factorInverseHom n a fac hd) ≫ X.map fac.i.op := by
    rw [← X.map_comp]
    apply X.congr_map
    change θ = fac.p.op ≫ fac.i.op
    rw [← op_comp, fac.fac]
    simp
  have hdir : X.map fac.i.op ≫ iNew n H P Q =
      H.i.app (oldDegree n j₀) ≫
        directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by
    simpa [latchingIndexToDegree, latchingIndexOfEpi, oldDegree] using
      i_naturality_direct n H P Q (latchingIndexOfEpi n j₀ fac.i.op)
  have hinv := H.i.naturality (factorInverseHom n a fac hd)
  have hinv' : X.map (factorInverseHom n a fac hd) ≫
      H.i.app (oldDegree n j₀) =
        H.i.app (oldDegree n a) ≫ H.Z.map (factorInverseHom n a fac hd) := by
    simpa [simplicialRestriction, degreeInclusion, oldDegree, j₀] using hinv
  rw [hθ', hmap]
  calc
    (X.map (factorInverseHom n a fac hd) ≫ X.map fac.i.op) ≫ iNew n H P Q =
        X.map (factorInverseHom n a fac hd) ≫
          (X.map fac.i.op ≫ iNew n H P Q) := by simp only [Category.assoc]
    _ = X.map (factorInverseHom n a fac hd) ≫
        (H.i.app (oldDegree n j₀) ≫
          directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op)) := by rw [hdir]
    _ = (X.map (factorInverseHom n a fac hd) ≫ H.i.app (oldDegree n j₀)) ≫
        directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by
          simp only [Category.assoc]
    _ = (H.i.app (oldDegree n a) ≫ H.Z.map (factorInverseHom n a fac hd)) ≫
        directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by rw [hinv']
    _ = H.i.app (oldDegree n a) ≫
        (H.Z.map (factorInverseHom n a fac hd) ≫
          directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op)) := by
            simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem i_naturality_newToOld (b : Fin n)
    (θ : op ⦋n⦌ ⟶ op ⦋b.1⦌) :
    iNew n H P Q ≫ newToOld n H P Q b θ =
      X.map θ ≫ H.i.app (oldDegree n b) := by
  let fac := canonicalSimplexFactor θ
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  have hd : fac.Z.len < n := (SimplexCategory.len_le_of_epi fac.i).trans_lt b.2
  let j₀ : Fin n := ⟨fac.Z.len, hd⟩
  have hθ := newToOld_of_factor n H P Q b j₀ θ fac.i fac.p fac.fac
  have hθ' : newToOld n H P Q b θ =
      inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
        H.Z.map (factorDirectHom n b fac hd) := by
    simpa [factorDirectHom] using hθ
  have hmap : X.map θ = X.map fac.p.op ≫ X.map (factorDirectHom n b fac hd) := by
    rw [← X.map_comp]
    apply X.congr_map
    change θ = fac.p.op ≫ fac.i.op
    rw [← op_comp, fac.fac]
    simp
  have hinv : iNew n H P Q ≫
      inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) =
        X.map fac.p.op ≫ H.i.app (oldDegree n j₀) := by
    simpa [matchingIndexToDegree, matchingIndexOfMono, oldDegree] using
      i_naturality_inverse n H P Q (matchingIndexOfMono n j₀ fac.p.op)
  have hdir := H.i.naturality (factorDirectHom n b fac hd)
  have hdir' : X.map (factorDirectHom n b fac hd) ≫ H.i.app (oldDegree n b) =
      H.i.app (oldDegree n j₀) ≫ H.Z.map (factorDirectHom n b fac hd) := by
    simpa [simplicialRestriction, degreeInclusion, oldDegree, j₀] using hdir
  rw [hθ', hmap]
  calc
    iNew n H P Q ≫
        (inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
          H.Z.map (factorDirectHom n b fac hd)) =
      (iNew n H P Q ≫ inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op)) ≫
        H.Z.map (factorDirectHom n b fac hd) := by simp only [Category.assoc]
    _ = (X.map fac.p.op ≫ H.i.app (oldDegree n j₀)) ≫
        H.Z.map (factorDirectHom n b fac hd) := by rw [hinv]
    _ = X.map fac.p.op ≫
        (H.i.app (oldDegree n j₀) ≫ H.Z.map (factorDirectHom n b fac hd)) := by
          simp only [Category.assoc]
    _ = X.map fac.p.op ≫
        (X.map (factorDirectHom n b fac hd) ≫ H.i.app (oldDegree n b)) := by
          rw [← hdir']
    _ = (X.map fac.p.op ≫ X.map (factorDirectHom n b fac hd)) ≫
        H.i.app (oldDegree n b) := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem i_naturality_newToNew (θ : op ⦋n⦌ ⟶ op ⦋n⦌) :
    X.map θ ≫ iNew n H P Q = iNew n H P Q ≫ newToNew n H P Q θ := by
  let fac := canonicalSimplexFactor θ
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  by_cases hd : fac.Z.len < n
  · let j₀ : Fin n := ⟨fac.Z.len, hd⟩
    have hθ := newToNew_of_lower_factor n H P Q j₀ θ fac.i fac.p fac.fac
    have hmap : X.map θ = X.map fac.p.op ≫ X.map fac.i.op := by
      rw [← X.map_comp]
      apply X.congr_map
      change θ = fac.p.op ≫ fac.i.op
      rw [← op_comp, fac.fac]
      simp
    have hinv : iNew n H P Q ≫
        inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) =
          X.map fac.p.op ≫ H.i.app (oldDegree n j₀) := by
      simpa [matchingIndexToDegree, matchingIndexOfMono, oldDegree] using
        i_naturality_inverse n H P Q (matchingIndexOfMono n j₀ fac.p.op)
    have hdir : X.map fac.i.op ≫ iNew n H P Q =
        H.i.app (oldDegree n j₀) ≫
          directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by
      simpa [latchingIndexToDegree, latchingIndexOfEpi, oldDegree] using
        i_naturality_direct n H P Q (latchingIndexOfEpi n j₀ fac.i.op)
    rw [hθ, hmap]
    calc
      (X.map fac.p.op ≫ X.map fac.i.op) ≫ iNew n H P Q =
          X.map fac.p.op ≫ (X.map fac.i.op ≫ iNew n H P Q) := by
            simp only [Category.assoc]
      _ = X.map fac.p.op ≫
          (H.i.app (oldDegree n j₀) ≫
            directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op)) := by rw [hdir]
      _ = (X.map fac.p.op ≫ H.i.app (oldDegree n j₀)) ≫
          directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by
            simp only [Category.assoc]
      _ = (iNew n H P Q ≫
          inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op)) ≫
            directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by rw [hinv]
      _ = iNew n H P Q ≫
          (inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
            directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op)) := by
              simp only [Category.assoc]
  · have hθ : θ = 𝟙 _ := eq_id_of_factor_not_lt n θ fac hd
    subst θ
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem p_naturality_oldToNew (a : Fin n)
    (θ : op ⦋a.1⦌ ⟶ op ⦋n⦌) :
    oldToNew n H P Q a θ ≫ pNew n H P Q =
      H.p.app (oldDegree n a) ≫ Y.map θ := by
  let fac := canonicalSimplexFactor θ
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  have hd : fac.Z.len < n := (SimplexCategory.len_le_of_mono fac.p).trans_lt a.2
  let j₀ : Fin n := ⟨fac.Z.len, hd⟩
  have hθ := oldToNew_of_factor n H P Q a j₀ θ fac.i fac.p fac.fac
  have hθ' : oldToNew n H P Q a θ =
      H.Z.map (factorInverseHom n a fac hd) ≫
        directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) := by
    simpa [factorInverseHom] using hθ
  have hmap : Y.map θ =
      Y.map (factorInverseHom n a fac hd) ≫ Y.map fac.i.op := by
    rw [← Y.map_comp]
    apply Y.congr_map
    change θ = fac.p.op ≫ fac.i.op
    rw [← op_comp, fac.fac]
    simp
  have hdir : directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) ≫
      pNew n H P Q = H.p.app (oldDegree n j₀) ≫ Y.map fac.i.op := by
    simpa [latchingIndexToDegree, latchingIndexOfEpi, oldDegree] using
      p_naturality_direct n H P Q (latchingIndexOfEpi n j₀ fac.i.op)
  have hinv := H.p.naturality (factorInverseHom n a fac hd)
  have hinv' : H.Z.map (factorInverseHom n a fac hd) ≫ H.p.app (oldDegree n j₀) =
      H.p.app (oldDegree n a) ≫ Y.map (factorInverseHom n a fac hd) := by
    simp [simplicialRestriction, degreeInclusion, oldDegree, j₀] at hinv ⊢
  rw [hθ', hmap]
  calc
    (H.Z.map (factorInverseHom n a fac hd) ≫
        directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op)) ≫ pNew n H P Q =
      H.Z.map (factorInverseHom n a fac hd) ≫
        (directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) ≫ pNew n H P Q) := by
          simp only [Category.assoc]
    _ = H.Z.map (factorInverseHom n a fac hd) ≫
        (H.p.app (oldDegree n j₀) ≫ Y.map fac.i.op) := by rw [hdir]
    _ = (H.Z.map (factorInverseHom n a fac hd) ≫ H.p.app (oldDegree n j₀)) ≫
        Y.map fac.i.op := by simp only [Category.assoc]
    _ = (H.p.app (oldDegree n a) ≫ Y.map (factorInverseHom n a fac hd)) ≫
        Y.map fac.i.op := by rw [hinv']
    _ = H.p.app (oldDegree n a) ≫
        (Y.map (factorInverseHom n a fac hd) ≫ Y.map fac.i.op) := by
          simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem p_naturality_newToOld (b : Fin n)
    (θ : op ⦋n⦌ ⟶ op ⦋b.1⦌) :
    newToOld n H P Q b θ ≫ H.p.app (oldDegree n b) =
      pNew n H P Q ≫ Y.map θ := by
  let fac := canonicalSimplexFactor θ
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  have hd : fac.Z.len < n := (SimplexCategory.len_le_of_epi fac.i).trans_lt b.2
  let j₀ : Fin n := ⟨fac.Z.len, hd⟩
  have hθ := newToOld_of_factor n H P Q b j₀ θ fac.i fac.p fac.fac
  have hθ' : newToOld n H P Q b θ =
      inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
        H.Z.map (factorDirectHom n b fac hd) := by
    simpa [factorDirectHom] using hθ
  have hmap : Y.map θ = Y.map fac.p.op ≫ Y.map (factorDirectHom n b fac hd) := by
    rw [← Y.map_comp]
    apply Y.congr_map
    change θ = fac.p.op ≫ fac.i.op
    rw [← op_comp, fac.fac]
    simp
  have hinv : inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
      H.p.app (oldDegree n j₀) = pNew n H P Q ≫ Y.map fac.p.op := by
    simpa [matchingIndexToDegree, matchingIndexOfMono, oldDegree] using
      p_naturality_inverse n H P Q (matchingIndexOfMono n j₀ fac.p.op)
  have hdir := H.p.naturality (factorDirectHom n b fac hd)
  have hdir' : H.Z.map (factorDirectHom n b fac hd) ≫ H.p.app (oldDegree n b) =
      H.p.app (oldDegree n j₀) ≫ Y.map (factorDirectHom n b fac hd) := by
    simp [simplicialRestriction, degreeInclusion, oldDegree, j₀] at hdir ⊢
  rw [hθ', hmap]
  calc
    (inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
        H.Z.map (factorDirectHom n b fac hd)) ≫ H.p.app (oldDegree n b) =
      inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
        (H.Z.map (factorDirectHom n b fac hd) ≫ H.p.app (oldDegree n b)) := by
          simp only [Category.assoc]
    _ = inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
        (H.p.app (oldDegree n j₀) ≫ Y.map (factorDirectHom n b fac hd)) := by rw [hdir']
    _ = (inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
          H.p.app (oldDegree n j₀)) ≫ Y.map (factorDirectHom n b fac hd) := by
            simp only [Category.assoc]
    _ = (pNew n H P Q ≫ Y.map fac.p.op) ≫
        Y.map (factorDirectHom n b fac hd) := by rw [hinv]
    _ = pNew n H P Q ≫
        (Y.map fac.p.op ≫ Y.map (factorDirectHom n b fac hd)) := by
          simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem p_naturality_newToNew (θ : op ⦋n⦌ ⟶ op ⦋n⦌) :
    newToNew n H P Q θ ≫ pNew n H P Q = pNew n H P Q ≫ Y.map θ := by
  let fac := canonicalSimplexFactor θ
  let _ : Epi fac.i := fac.hi
  let _ : Mono fac.p := fac.hp
  by_cases hd : fac.Z.len < n
  · let j₀ : Fin n := ⟨fac.Z.len, hd⟩
    have hθ := newToNew_of_lower_factor n H P Q j₀ θ fac.i fac.p fac.fac
    have hmap : Y.map θ = Y.map fac.p.op ≫ Y.map fac.i.op := by
      rw [← Y.map_comp]
      apply Y.congr_map
      change θ = fac.p.op ≫ fac.i.op
      rw [← op_comp, fac.fac]
      simp
    have hinv : inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
        H.p.app (oldDegree n j₀) = pNew n H P Q ≫ Y.map fac.p.op := by
      simpa [matchingIndexToDegree, matchingIndexOfMono, oldDegree] using
        p_naturality_inverse n H P Q (matchingIndexOfMono n j₀ fac.p.op)
    have hdir : directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) ≫
        pNew n H P Q = H.p.app (oldDegree n j₀) ≫ Y.map fac.i.op := by
      simpa [latchingIndexToDegree, latchingIndexOfEpi, oldDegree] using
        p_naturality_direct n H P Q (latchingIndexOfEpi n j₀ fac.i.op)
    rw [hθ, hmap]
    calc
      (inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
          directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op)) ≫ pNew n H P Q =
        inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
          (directMap n H P Q (latchingIndexOfEpi n j₀ fac.i.op) ≫ pNew n H P Q) := by
            simp only [Category.assoc]
      _ = inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
          (H.p.app (oldDegree n j₀) ≫ Y.map fac.i.op) := by rw [hdir]
      _ = (inverseMap n H P Q (matchingIndexOfMono n j₀ fac.p.op) ≫
            H.p.app (oldDegree n j₀)) ≫ Y.map fac.i.op := by
              simp only [Category.assoc]
      _ = (pNew n H P Q ≫ Y.map fac.p.op) ≫ Y.map fac.i.op := by rw [hinv]
      _ = pNew n H P Q ≫ (Y.map fac.p.op ≫ Y.map fac.i.op) := by
            simp only [Category.assoc]
  · have hθ : θ = 𝟙 _ := eq_id_of_factor_not_lt n θ fac hd
    subst θ
    simp

/-- The Fin-indexed dependent family underlying the extended left transformation. -/
noncomputable def extendIAppFin (k : Fin (n + 1)) :
    X.obj (op ⦋k.1⦌) ⟶
      Fin.lastCases (newObj n H P Q) (fun a => H.Z.obj (oldDegree n a)) k :=
  by
    refine Fin.lastCases ?_ (fun a => ?_) k
    · simpa using iNew n H P Q
    · simpa [simplicialRestriction, degreeInclusion, oldDegree] using H.i.app (oldDegree n a)

/-- Components of the extended left natural transformation. -/
noncomputable def extendIApp (k : DegreeLT (n + 1)) :
    ((simplicialRestriction (C := C) (n + 1)).obj X).obj k ⟶ (extend n H P Q).obj k :=
  extendIAppFin n H P Q k.degree

/-- The Fin-indexed dependent family underlying the extended right transformation. -/
noncomputable def extendPAppFin (k : Fin (n + 1)) :
    Fin.lastCases (newObj n H P Q) (fun a => H.Z.obj (oldDegree n a)) k ⟶
      Y.obj (op ⦋k.1⦌) :=
  by
    refine Fin.lastCases ?_ (fun a => ?_) k
    · simpa using pNew n H P Q
    · simpa [simplicialRestriction, degreeInclusion, oldDegree] using H.p.app (oldDegree n a)

/-- Components of the extended right natural transformation. -/
noncomputable def extendPApp (k : DegreeLT (n + 1)) :
    (extend n H P Q).obj k ⟶ ((simplicialRestriction (C := C) (n + 1)).obj Y).obj k :=
  extendPAppFin n H P Q k.degree

@[simp]
private theorem extendIApp_last :
    HEq (extendIApp n H P Q (degreeLast n)) (iNew n H P Q) := by
  unfold degreeLast extendIApp extendIAppFin
  simp only [simplicialRestriction_obj_obj, Fin.val_last, eq_mpr_eq_cast,
    Fin.lastCases_last, congrArg_cast_hom_right, Fin.val_castSucc]
  exact comp_eqToHom_heq _ _

@[simp]
private theorem extendPApp_last :
    HEq (extendPApp n H P Q (degreeLast n)) (pNew n H P Q) := by
  unfold degreeLast extendPApp extendPAppFin
  simp only [simplicialRestriction_obj_obj, Fin.val_last, eq_mpr_eq_cast,
    Fin.lastCases_last, congrArg_cast_hom_left, Fin.val_castSucc]
  exact eqToHom_comp_heq _ _

@[simp]
private theorem extendIApp_castSucc (a : DegreeLT n) :
    HEq (extendIApp n H P Q ((degreeSucc n).obj a)) (H.i.app a) := by
  rcases a with ⟨a⟩
  unfold degreeSucc extendIApp extendIAppFin
  simp only [simplicialRestriction_obj_obj, Fin.val_castSucc, Fin.val_last,
    eq_mpr_eq_cast, Fin.lastCases_last, congrArg_cast_hom_right,
    Fin.lastCases_castSucc]
  exact cast_heq _ _

@[simp]
private theorem extendPApp_castSucc (a : DegreeLT n) :
    HEq (extendPApp n H P Q ((degreeSucc n).obj a)) (H.p.app a) := by
  rcases a with ⟨a⟩
  unfold degreeSucc extendPApp extendPAppFin
  simp only [simplicialRestriction_obj_obj, Fin.val_castSucc, Fin.val_last,
    eq_mpr_eq_cast, Fin.lastCases_last, congrArg_cast_hom_left,
    Fin.lastCases_castSucc]
  exact cast_heq _ _

omit [HasPushouts C] [HasPullbacks C]
    [HasColimitsOfShape (latchingIndex n) C] [HasLimitsOfShape (matchingIndex n) C] in
private theorem square_of_heq
    {A B D E A' B' D' E' : C}
    {u : A ⟶ B} {v : B ⟶ E} {w : A ⟶ D} {z : D ⟶ E}
    {u' : A' ⟶ B'} {v' : B' ⟶ E'} {w' : A' ⟶ D'} {z' : D' ⟶ E'}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    (hu : HEq u u') (hv : HEq v v') (hw : HEq w w') (hz : HEq z z')
    (hsem : u' ≫ v' = w' ≫ z') : u ≫ v = w ≫ z := by
  have hr := heq_comp hA hD hE hw hz
  exact eq_comp_of_heq hA hB hE hu hv hr hsem

set_option backward.isDefEq.respectTransparency false in
private theorem extendIApp_naturality {a b : DegreeLT (n + 1)} (u : a ⟶ b) :
    ((simplicialRestriction (C := C) (n + 1)).obj X).map u ≫ extendIApp n H P Q b =
      extendIApp n H P Q a ≫ (extend n H P Q).map u := by
  rcases eq_last_or_succ (n := n) a with rfl | ⟨a, rfl⟩
  · rcases eq_last_or_succ (n := n) b with rfl | ⟨b, rfl⟩
    · refine square_of_heq (by rfl) (by rfl) (extend_obj_last n H P Q)
          (extend_obj_last n H P Q) (by rfl) (extendIApp_last n H P Q)
          (extendIApp_last n H P Q) (extend_map_last n H P Q u) ?_
      exact i_naturality_newToNew n H P Q (lastEndHom n u)
    · refine square_of_heq (by rfl) (by rfl) (extend_obj_last n H P Q)
          (extend_obj_castSucc n H P Q b) (by rfl) (extendIApp_castSucc n H P Q b)
          (extendIApp_last n H P Q) (extend_map_last_castSucc n H P Q b u) ?_
      exact (i_naturality_newToOld n H P Q b.degree (lastToOldHom n b u)).symm
  · rcases eq_last_or_succ (n := n) b with rfl | ⟨b, rfl⟩
    · refine square_of_heq (by rfl) (by rfl) (extend_obj_castSucc n H P Q a)
          (extend_obj_last n H P Q) (by rfl) (extendIApp_last n H P Q)
          (extendIApp_castSucc n H P Q a) (extend_map_castSucc_last n H P Q a u) ?_
      exact i_naturality_oldToNew n H P Q a.degree (oldToLastHom n a u)
    · refine square_of_heq (by rfl) (by rfl) (extend_obj_castSucc n H P Q a)
          (extend_obj_castSucc n H P Q b) (by rfl) (extendIApp_castSucc n H P Q b)
          (extendIApp_castSucc n H P Q a) (extend_map_castSucc n H P Q (oldHom n u)) ?_
      exact H.i.naturality (oldHom n u)

set_option backward.isDefEq.respectTransparency false in
private theorem extendPApp_naturality {a b : DegreeLT (n + 1)} (u : a ⟶ b) :
    (extend n H P Q).map u ≫ extendPApp n H P Q b =
      extendPApp n H P Q a ≫ ((simplicialRestriction (C := C) (n + 1)).obj Y).map u := by
  rcases eq_last_or_succ (n := n) a with rfl | ⟨a, rfl⟩
  · rcases eq_last_or_succ (n := n) b with rfl | ⟨b, rfl⟩
    · refine square_of_heq (extend_obj_last n H P Q) (extend_obj_last n H P Q)
          (by rfl) (by rfl) (extend_map_last n H P Q u) (extendPApp_last n H P Q)
          (extendPApp_last n H P Q) (by rfl) ?_
      exact p_naturality_newToNew n H P Q (lastEndHom n u)
    · refine square_of_heq (extend_obj_last n H P Q) (extend_obj_castSucc n H P Q b)
          (by rfl) (by rfl) (extend_map_last_castSucc n H P Q b u)
          (extendPApp_castSucc n H P Q b) (extendPApp_last n H P Q) (by rfl) ?_
      exact p_naturality_newToOld n H P Q b.degree (lastToOldHom n b u)
  · rcases eq_last_or_succ (n := n) b with rfl | ⟨b, rfl⟩
    · refine square_of_heq (extend_obj_castSucc n H P Q a) (extend_obj_last n H P Q)
          (by rfl) (by rfl) (extend_map_castSucc_last n H P Q a u)
          (extendPApp_last n H P Q) (extendPApp_castSucc n H P Q a) (by rfl) ?_
      exact p_naturality_oldToNew n H P Q a.degree (oldToLastHom n a u)
    · refine square_of_heq (extend_obj_castSucc n H P Q a)
          (extend_obj_castSucc n H P Q b) (by rfl) (by rfl)
          (extend_map_castSucc n H P Q (oldHom n u)) (extendPApp_castSucc n H P Q b)
          (extendPApp_castSucc n H P Q a) (by rfl) ?_
      exact H.p.naturality (oldHom n u)

/-- The extended left factor. -/
noncomputable def extendI :
    (simplicialRestriction (C := C) (n + 1)).obj X ⟶ extend n H P Q where
  app := extendIApp n H P Q
  naturality := fun {_ _} u => by exact extendIApp_naturality (X := X) (Y := Y) (f := f) n H P Q u

/-- The extended right factor. -/
noncomputable def extendP :
    extend n H P Q ⟶ (simplicialRestriction (C := C) (n + 1)).obj Y where
  app := extendPApp n H P Q
  naturality := fun {_ _} u => by exact extendPApp_naturality (X := X) (Y := Y) (f := f) n H P Q u

set_option backward.isDefEq.respectTransparency false in
private theorem extend_app_fac (k : DegreeLT (n + 1)) :
    (extendI n H P Q).app k ≫ (extendP n H P Q).app k =
      ((simplicialRestriction (C := C) (n + 1)).map f).app k := by
  rcases eq_last_or_succ (n := n) k with rfl | ⟨k, rfl⟩
  · apply eq_comp_of_heq (by rfl) (extend_obj_last n H P Q) (by rfl)
      (extendIApp_last n H P Q) (extendPApp_last n H P Q) (by rfl)
    exact iNew_pNew n H P Q
  · have hfac := NatTrans.congr_app H.fac k
    have hfac' : H.i.app k ≫ H.p.app k = f.app (op ⦋k.degree.1⦌) := by
      simpa [simplicialRestriction, degreeInclusion] using hfac
    apply eq_comp_of_heq (by rfl) (extend_obj_castSucc n H P Q k) (by rfl)
      (extendIApp_castSucc n H P Q k) (extendPApp_castSucc n H P Q k) (by rfl)
    exact hfac'

private theorem extend_fac :
    extendI n H P Q ≫ extendP n H P Q =
      (simplicialRestriction (C := C) (n + 1)).map f := by
  apply NatTrans.ext
  funext k
  exact extend_app_fac n H P Q k

/-- The factorization extended through degree `n`. -/
noncomputable def successorPartialFactorization : PartialFactorization f (n + 1) where
  Z := extend n H P Q
  i := extendI n H P Q
  p := extendP n H P Q
  fac := by exact extend_fac n H P Q

@[simp]
private theorem successor_Z_obj_castSucc (a : DegreeLT n) :
    (successorPartialFactorization n H P Q).Z.obj ((degreeSucc n).obj a) = H.Z.obj a :=
  extend_obj_castSucc n H P Q a

private theorem successor_Z_map_castSucc {a b : DegreeLT n} (u : a ⟶ b) :
    HEq ((successorPartialFactorization n H P Q).Z.map ((degreeSucc n).map u))
      (H.Z.map u) :=
  extend_map_castSucc n H P Q u

private theorem successor_i_app_castSucc (a : DegreeLT n) :
    HEq ((successorPartialFactorization n H P Q).i.app ((degreeSucc n).obj a))
      (H.i.app a) :=
  extendIApp_castSucc n H P Q a

private theorem successor_p_app_castSucc (a : DegreeLT n) :
    HEq ((successorPartialFactorization n H P Q).p.app ((degreeSucc n).obj a))
      (H.p.app a) :=
  extendPApp_castSucc n H P Q a

private theorem successor_factor_component_castSucc (a : DegreeLT n) :
    HEq
      ((successorPartialFactorization n H P Q).i.app ((degreeSucc n).obj a) ≫
        (successorPartialFactorization n H P Q).p.app ((degreeSucc n).obj a))
      (H.i.app a ≫ H.p.app a) := by
  exact heq_comp (by rfl) (successor_Z_obj_castSucc n H P Q a) (by rfl)
    (successor_i_app_castSucc n H P Q a) (successor_p_app_castSucc n H P Q a)

end OneDegreeExtension

section StageTower

variable [HasPushouts C] [HasPullbacks C]
variable [∀ k : ℕ, HasColimitsOfShape (latchingIndex k) C]
variable [∀ k : ℕ, HasLimitsOfShape (matchingIndex k) C]
variable {X Y : SimplicialObject C}
variable (f : X ⟶ Y) (P Q : MorphismProperty C) [P.HasFactorization Q]

/-- The finite-stage factorization tower, obtained by adjoining one degree at a time. -/
noncomputable def stages : ∀ k : ℕ, PartialFactorization f k
  | 0 => PartialFactorization.empty f
  | k + 1 => successorPartialFactorization k (stages k) P Q

@[simp]
private theorem stages_zero : stages f P Q 0 = PartialFactorization.empty f :=
  rfl

@[simp]
private theorem stages_succ (k : ℕ) :
    stages f P Q (k + 1) = successorPartialFactorization k (stages f P Q k) P Q :=
  rfl

private theorem stages_obj_step (k : ℕ) (a : DegreeLT k) :
    (stages f P Q (k + 1)).Z.obj ((degreeSucc k).obj a) =
      (stages f P Q k).Z.obj a :=
  successor_Z_obj_castSucc k (stages f P Q k) P Q a

private theorem stages_map_step (k : ℕ) {a b : DegreeLT k} (u : a ⟶ b) :
    HEq ((stages f P Q (k + 1)).Z.map ((degreeSucc k).map u))
      ((stages f P Q k).Z.map u) :=
  successor_Z_map_castSucc k (stages f P Q k) P Q u

private theorem stages_i_step (k : ℕ) (a : DegreeLT k) :
    HEq ((stages f P Q (k + 1)).i.app ((degreeSucc k).obj a))
      ((stages f P Q k).i.app a) :=
  successor_i_app_castSucc k (stages f P Q k) P Q a

private theorem stages_p_step (k : ℕ) (a : DegreeLT k) :
    HEq ((stages f P Q (k + 1)).p.app ((degreeSucc k).obj a))
      ((stages f P Q k).p.app a) :=
  successor_p_app_castSucc k (stages f P Q k) P Q a

private theorem stages_factor_component_step (k : ℕ) (a : DegreeLT k) :
    HEq
      ((stages f P Q (k + 1)).i.app ((degreeSucc k).obj a) ≫
        (stages f P Q (k + 1)).p.app ((degreeSucc k).obj a))
      ((stages f P Q k).i.app a ≫ (stages f P Q k).p.app a) :=
  successor_factor_component_castSucc k (stages f P Q k) P Q a

private theorem degreeIncl_step_obj {r s : ℕ} (h : r ≤ s) (a : DegreeLT r) :
    (degreeSucc s).obj ((degreeIncl h).obj a) = (degreeIncl h.step).obj a := by
  apply DegreeLT.ext
  apply Fin.ext
  rfl

private theorem stages_obj_stability {r s : ℕ} (h : r ≤ s) (a : DegreeLT r) :
    (stages f P Q s).Z.obj ((degreeIncl h).obj a) = (stages f P Q r).Z.obj a := by
  induction h with
  | refl => rfl
  | @step s h ih =>
      have hs := stages_obj_step f P Q s ((degreeIncl h).obj a)
      calc
        (stages f P Q (s + 1)).Z.obj ((degreeIncl h.step).obj a) =
            (stages f P Q (s + 1)).Z.obj
              ((degreeSucc s).obj ((degreeIncl h).obj a)) := by
                rw [degreeIncl_step_obj h a]
        _ = (stages f P Q s).Z.obj ((degreeIncl h).obj a) := hs
        _ = (stages f P Q r).Z.obj a := ih

private theorem stages_map_stability {r s : ℕ} (h : r ≤ s) {a b : DegreeLT r} (u : a ⟶ b) :
    HEq ((stages f P Q s).Z.map ((degreeIncl h).map u)) ((stages f P Q r).Z.map u) := by
  induction h with
  | refl => rfl
  | @step s h ih =>
      have hs := stages_map_step f P Q s ((degreeIncl h).map u)
      have ha := degreeIncl_step_obj h a
      have hb := degreeIncl_step_obj h b
      have hpre : HEq ((stages f P Q (s + 1)).Z.map ((degreeIncl h.step).map u))
          ((stages f P Q (s + 1)).Z.map
            ((degreeSucc s).map ((degreeIncl h).map u))) := by
        cases ha
        cases hb
        rfl
      exact hpre.trans (hs.trans ih)

private theorem stages_i_stability {r s : ℕ} (h : r ≤ s) (a : DegreeLT r) :
    HEq ((stages f P Q s).i.app ((degreeIncl h).obj a)) ((stages f P Q r).i.app a) := by
  induction h with
  | refl => rfl
  | @step s h ih =>
      have hs := stages_i_step f P Q s ((degreeIncl h).obj a)
      have ha := degreeIncl_step_obj h a
      have hpre : HEq ((stages f P Q (s + 1)).i.app ((degreeIncl h.step).obj a))
          ((stages f P Q (s + 1)).i.app
            ((degreeSucc s).obj ((degreeIncl h).obj a))) := by
        cases ha
        rfl
      exact hpre.trans (hs.trans ih)

private theorem stages_p_stability {r s : ℕ} (h : r ≤ s) (a : DegreeLT r) :
    HEq ((stages f P Q s).p.app ((degreeIncl h).obj a)) ((stages f P Q r).p.app a) := by
  induction h with
  | refl => rfl
  | @step s h ih =>
      have hs := stages_p_step f P Q s ((degreeIncl h).obj a)
      have ha := degreeIncl_step_obj h a
      have hpre : HEq ((stages f P Q (s + 1)).p.app ((degreeIncl h.step).obj a))
          ((stages f P Q (s + 1)).p.app
            ((degreeSucc s).obj ((degreeIncl h).obj a))) := by
        cases ha
        rfl
      exact hpre.trans (hs.trans ih)

private theorem stages_factor_component_stability {r s : ℕ} (h : r ≤ s) (a : DegreeLT r) :
    HEq
      ((stages f P Q s).i.app ((degreeIncl h).obj a) ≫
        (stages f P Q s).p.app ((degreeIncl h).obj a))
      ((stages f P Q r).i.app a ≫ (stages f P Q r).p.app a) := by
  exact heq_comp (by rfl) (stages_obj_stability f P Q h a) (by rfl)
    (stages_i_stability f P Q h a) (stages_p_stability f P Q h a)

private theorem stages_fac_app (k : ℕ) (a : DegreeLT k) :
    (stages f P Q k).i.app a ≫ (stages f P Q k).p.app a =
      f.app (op ⦋a.degree.1⦌) := by
  have hfac := NatTrans.congr_app (stages f P Q k).fac a
  change (stages f P Q k).i.app a ≫ (stages f P Q k).p.app a =
    f.app (op ⦋a.degree.1⦌) at hfac
  exact hfac

/-- The global middle object at a simplex is taken at that degree's birth stage. -/
noncomputable def globalObj (Δ : SimplexCategoryᵒᵖ) : C :=
  (stages f P Q (Δ.unop.len + 1)).Z.obj (degreeLast Δ.unop.len)

private theorem globalObj_eq_stage (Δ : SimplexCategoryᵒᵖ) (N : ℕ)
    (h : Δ.unop.len + 1 ≤ N) :
    globalObj f P Q Δ =
      (stages f P Q N).Z.obj ((degreeIncl h).obj (degreeLast Δ.unop.len)) :=
  (stages_obj_stability f P Q h (degreeLast Δ.unop.len)).symm

/-- The copy of a simplex degree inside a specified later finite stage. -/
private def degreeAtStage (Δ : SimplexCategoryᵒᵖ) (N : ℕ) (h : Δ.unop.len + 1 ≤ N) :
    DegreeLT N :=
  (degreeIncl h).obj (degreeLast Δ.unop.len)

/-- Regard an arbitrary simplex operator as a morphism between its two represented degrees in a
common finite stage. -/
private def homAtStage {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) (N : ℕ)
    (hA : A.unop.len + 1 ≤ N) (hB : B.unop.len + 1 ≤ N) :
    degreeAtStage A N hA ⟶ degreeAtStage B N hB :=
  u

/-- The least finite stage containing both original endpoint birth degrees. -/
def commonStage (A B : SimplexCategoryᵒᵖ) : ℕ :=
  max A.unop.len B.unop.len + 1

private theorem left_birth_le_common (A B : SimplexCategoryᵒᵖ) :
    A.unop.len + 1 ≤ commonStage A B :=
  Nat.succ_le_succ (Nat.le_max_left _ _)

private theorem right_birth_le_common (A B : SimplexCategoryᵒᵖ) :
    B.unop.len + 1 ≤ commonStage A B :=
  Nat.succ_le_succ (Nat.le_max_right _ _)

/-- Represent an original simplex arrow in its minimal common finite stage. -/
def commonHom {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) :
    (degreeIncl (show A.unop.len + 1 ≤ commonStage A B from
      by exact left_birth_le_common A B)).obj (degreeLast A.unop.len) ⟶
      (degreeIncl (show B.unop.len + 1 ≤ commonStage A B from
      by exact right_birth_le_common A B)).obj (degreeLast B.unop.len) :=
  u

private theorem degreeAtStage_trans (Δ : SimplexCategoryᵒᵖ)
    {M N : ℕ} (hM : Δ.unop.len + 1 ≤ M) (hMN : M ≤ N)
    (hN : Δ.unop.len + 1 ≤ N) :
    (degreeIncl hMN).obj (degreeAtStage Δ M hM) = degreeAtStage Δ N hN := by
  apply DegreeLT.ext
  apply Fin.ext
  rfl

/-- Evaluate an arbitrary simplex operator in its minimal common finite stage, conjugating by the
source and target birth-stage comparison equalities. -/
noncomputable def globalMap {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) :
    globalObj f P Q A ⟶ globalObj f P Q B := by
  let N := commonStage A B
  let hA : A.unop.len + 1 ≤ N := by exact left_birth_le_common A B
  let hB : B.unop.len + 1 ≤ N := by exact right_birth_le_common A B
  exact eqToHom (by exact globalObj_eq_stage f P Q A N hA) ≫
    (stages f P Q N).Z.map (commonHom u) ≫
      eqToHom (show (stages f P Q N).Z.obj ((degreeIncl hB).obj (degreeLast B.unop.len)) =
        globalObj f P Q B from by exact (globalObj_eq_stage f P Q B N hB).symm)

private theorem globalMap_heq_common {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) :
    HEq (globalMap f P Q u)
      ((stages f P Q (commonStage A B)).Z.map (commonHom u)) := by
  unfold globalMap
  dsimp only
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

private theorem globalMap_eq_stage {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) (N : ℕ)
    (hA : A.unop.len + 1 ≤ N) (hB : B.unop.len + 1 ≤ N) :
    HEq (globalMap f P Q u) ((stages f P Q N).Z.map (homAtStage u N hA hB)) := by
  let M := commonStage A B
  have hMN : M ≤ N := by
    dsimp [M, commonStage]
    omega
  have hc := globalMap_heq_common f P Q u
  have hs := stages_map_stability f P Q hMN (commonHom u)
  have ha := degreeAtStage_trans A (left_birth_le_common A B) hMN hA
  have hb := degreeAtStage_trans B (right_birth_le_common A B) hMN hB
  have hpre : HEq ((stages f P Q N).Z.map (homAtStage u N hA hB))
      ((stages f P Q N).Z.map ((degreeIncl hMN).map (commonHom u))) := by
    cases ha
    cases hb
    rfl
  exact hc.trans (hpre.trans hs).symm

private theorem globalMap_id (A : SimplexCategoryᵒᵖ) :
    globalMap f P Q (𝟙 A) = 𝟙 (globalObj f P Q A) := by
  let N := A.unop.len + 1
  let h : A.unop.len + 1 ≤ N := Nat.le_refl _
  have hm := globalMap_eq_stage f P Q (𝟙 A) N h h
  have ho := globalObj_eq_stage f P Q A N h
  have hu : homAtStage (𝟙 A) N h h = 𝟙 (degreeAtStage A N h) := by rfl
  have hs : (stages f P Q N).Z.map (homAtStage (𝟙 A) N h h) =
      𝟙 ((stages f P Q N).Z.obj (degreeAtStage A N h)) := by
    rw [hu, (stages f P Q N).Z.map_id]
  have hi : HEq (𝟙 (globalObj f P Q A))
      (𝟙 ((stages f P Q N).Z.obj (degreeAtStage A N h))) := by
    cases ho
    rfl
  apply eq_of_heq
  exact hm.trans ((heq_of_eq hs).trans hi.symm)

private def compositionStage (A B D : SimplexCategoryᵒᵖ) : ℕ :=
  max (max A.unop.len B.unop.len) D.unop.len + 1

private theorem left_birth_le_composition (A B D : SimplexCategoryᵒᵖ) :
    A.unop.len + 1 ≤ compositionStage A B D := by
  dsimp [compositionStage]
  omega

private theorem middle_birth_le_composition (A B D : SimplexCategoryᵒᵖ) :
    B.unop.len + 1 ≤ compositionStage A B D := by
  dsimp [compositionStage]
  omega

private theorem right_birth_le_composition (A B D : SimplexCategoryᵒᵖ) :
    D.unop.len + 1 ≤ compositionStage A B D := by
  dsimp [compositionStage]
  omega

private theorem globalMap_comp {A B D : SimplexCategoryᵒᵖ}
    (u : A ⟶ B) (v : B ⟶ D) :
    globalMap f P Q u ≫ globalMap f P Q v = globalMap f P Q (u ≫ v) := by
  let N := compositionStage A B D
  let hA := left_birth_le_composition A B D
  let hB := middle_birth_le_composition A B D
  let hD := right_birth_le_composition A B D
  have hu := globalMap_eq_stage f P Q u N hA hB
  have hv := globalMap_eq_stage f P Q v N hB hD
  have huv := globalMap_eq_stage f P Q (u ≫ v) N hA hD
  have hAobj := globalObj_eq_stage f P Q A N hA
  have hBobj := globalObj_eq_stage f P Q B N hB
  have hDobj := globalObj_eq_stage f P Q D N hD
  have hcomp :
      (stages f P Q N).Z.map (homAtStage u N hA hB) ≫
          (stages f P Q N).Z.map (homAtStage v N hB hD) =
        (stages f P Q N).Z.map (homAtStage (u ≫ v) N hA hD) := by
    rw [← (stages f P Q N).Z.map_comp]
    rfl
  exact eq_comp_of_heq hAobj hBobj hDobj hu hv huv hcomp

/-- The globally assembled middle simplicial object. -/
noncomputable def globalMiddle : SimplicialObject C where
  obj := globalObj f P Q
  map := globalMap f P Q
  map_id := by exact globalMap_id f P Q
  map_comp := fun u v => by exact (globalMap_comp f P Q u v).symm

private theorem globalMiddle_obj_eq_stage (Δ : SimplexCategoryᵒᵖ) (N : ℕ)
    (h : Δ.unop.len + 1 ≤ N) :
    (globalMiddle f P Q).obj Δ =
      (stages f P Q N).Z.obj (degreeAtStage Δ N h) :=
  globalObj_eq_stage f P Q Δ N h

@[simp]
private theorem globalMiddle_obj_birth (Δ : SimplexCategoryᵒᵖ) :
    (globalMiddle f P Q).obj Δ =
      (stages f P Q (Δ.unop.len + 1)).Z.obj (degreeLast Δ.unop.len) :=
  rfl

private theorem globalMiddle_map_eq_stage {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) (N : ℕ)
    (hA : A.unop.len + 1 ≤ N) (hB : B.unop.len + 1 ≤ N) :
    HEq ((globalMiddle f P Q).map u)
      ((stages f P Q N).Z.map (homAtStage u N hA hB)) :=
  globalMap_eq_stage f P Q u N hA hB

/-- The global left-factor component at a simplex, taken at its birth stage. -/
noncomputable def globalIApp (Δ : SimplexCategoryᵒᵖ) :
    X.obj Δ ⟶ (globalMiddle f P Q).obj Δ :=
  (stages f P Q (Δ.unop.len + 1)).i.app (degreeLast Δ.unop.len)

/-- The global right-factor component at a simplex, taken at its birth stage. -/
noncomputable def globalPApp (Δ : SimplexCategoryᵒᵖ) :
    (globalMiddle f P Q).obj Δ ⟶ Y.obj Δ :=
  (stages f P Q (Δ.unop.len + 1)).p.app (degreeLast Δ.unop.len)

private theorem globalIApp_eq_birth (Δ : SimplexCategoryᵒᵖ) :
    HEq (globalIApp f P Q Δ)
      ((stages f P Q (Δ.unop.len + 1)).i.app (degreeLast Δ.unop.len)) := by
  unfold globalIApp
  rfl

private theorem globalPApp_eq_birth (Δ : SimplexCategoryᵒᵖ) :
    HEq (globalPApp f P Q Δ)
      ((stages f P Q (Δ.unop.len + 1)).p.app (degreeLast Δ.unop.len)) := by
  unfold globalPApp
  rfl

private theorem globalIApp_eq_stage (Δ : SimplexCategoryᵒᵖ) (N : ℕ)
    (h : Δ.unop.len + 1 ≤ N) :
    HEq (globalIApp f P Q Δ) ((stages f P Q N).i.app (degreeAtStage Δ N h)) := by
  exact (globalIApp_eq_birth f P Q Δ).trans
    (stages_i_stability f P Q h (degreeLast Δ.unop.len)).symm

private theorem globalPApp_eq_stage (Δ : SimplexCategoryᵒᵖ) (N : ℕ)
    (h : Δ.unop.len + 1 ≤ N) :
    HEq (globalPApp f P Q Δ) ((stages f P Q N).p.app (degreeAtStage Δ N h)) := by
  exact (globalPApp_eq_birth f P Q Δ).trans
    (stages_p_stability f P Q h (degreeLast Δ.unop.len)).symm

private theorem globalIApp_naturality {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) :
    X.map u ≫ globalIApp f P Q B =
      globalIApp f P Q A ≫ (globalMiddle f P Q).map u := by
  let N := commonStage A B
  let hA := left_birth_le_common A B
  let hB := right_birth_le_common A B
  have hiA := globalIApp_eq_stage f P Q A N hA
  have hiB := globalIApp_eq_stage f P Q B N hB
  have hm := globalMiddle_map_eq_stage f P Q u N hA hB
  have hAobj := globalMiddle_obj_eq_stage f P Q A N hA
  have hBobj := globalMiddle_obj_eq_stage f P Q B N hB
  refine square_of_heq (by rfl) (by rfl) hAobj hBobj (by rfl) hiB hiA hm ?_
  exact (stages f P Q N).i.naturality (homAtStage u N hA hB)

private theorem globalPApp_naturality {A B : SimplexCategoryᵒᵖ} (u : A ⟶ B) :
    (globalMiddle f P Q).map u ≫ globalPApp f P Q B =
      globalPApp f P Q A ≫ Y.map u := by
  let N := commonStage A B
  let hA := left_birth_le_common A B
  let hB := right_birth_le_common A B
  have hpA := globalPApp_eq_stage f P Q A N hA
  have hpB := globalPApp_eq_stage f P Q B N hB
  have hm := globalMiddle_map_eq_stage f P Q u N hA hB
  have hAobj := globalMiddle_obj_eq_stage f P Q A N hA
  have hBobj := globalMiddle_obj_eq_stage f P Q B N hB
  refine square_of_heq hAobj hBobj (by rfl) (by rfl) hm hpB hpA (by rfl) ?_
  exact (stages f P Q N).p.naturality (homAtStage u N hA hB)

/-- The globally assembled left factor. -/
noncomputable def globalI : X ⟶ globalMiddle f P Q where
  app := globalIApp f P Q
  naturality := fun {_ _} u => by exact globalIApp_naturality f P Q u

/-- The globally assembled right factor. -/
noncomputable def globalP : globalMiddle f P Q ⟶ Y where
  app := globalPApp f P Q
  naturality := fun {_ _} u => by exact globalPApp_naturality f P Q u

private theorem globalI_app_eq_birth (Δ : SimplexCategoryᵒᵖ) :
    HEq ((globalI f P Q).app Δ)
      ((stages f P Q (Δ.unop.len + 1)).i.app (degreeLast Δ.unop.len)) :=
  globalIApp_eq_birth f P Q Δ

private theorem globalP_app_eq_birth (Δ : SimplexCategoryᵒᵖ) :
    HEq ((globalP f P Q).app Δ)
      ((stages f P Q (Δ.unop.len + 1)).p.app (degreeLast Δ.unop.len)) :=
  globalPApp_eq_birth f P Q Δ

private theorem globalI_app_eq_stage (Δ : SimplexCategoryᵒᵖ) (N : ℕ)
    (h : Δ.unop.len + 1 ≤ N) :
    HEq ((globalI f P Q).app Δ) ((stages f P Q N).i.app (degreeAtStage Δ N h)) :=
  globalIApp_eq_stage f P Q Δ N h

private theorem globalP_app_eq_stage (Δ : SimplexCategoryᵒᵖ) (N : ℕ)
    (h : Δ.unop.len + 1 ≤ N) :
    HEq ((globalP f P Q).app Δ) ((stages f P Q N).p.app (degreeAtStage Δ N h)) :=
  globalPApp_eq_stage f P Q Δ N h

private theorem global_fac_app (Δ : SimplexCategoryᵒᵖ) :
    (globalI f P Q).app Δ ≫ (globalP f P Q).app Δ = f.app Δ := by
  let N := Δ.unop.len + 1
  let h : Δ.unop.len + 1 ≤ N := Nat.le_refl _
  have hobj := globalMiddle_obj_eq_stage f P Q Δ N h
  have hi := globalIApp_eq_birth f P Q Δ
  have hp := globalPApp_eq_birth f P Q Δ
  have hfac := stages_fac_app f P Q N (degreeLast Δ.unop.len)
  exact eq_comp_of_heq (by rfl) hobj (by rfl) hi hp (by rfl) hfac

private theorem global_factor_component_eq_stage (Δ : SimplexCategoryᵒᵖ) (N : ℕ)
    (h : Δ.unop.len + 1 ≤ N) :
    HEq ((globalI f P Q).app Δ ≫ (globalP f P Q).app Δ)
      ((stages f P Q N).i.app (degreeAtStage Δ N h) ≫
        (stages f P Q N).p.app (degreeAtStage Δ N h)) := by
  exact heq_comp (by rfl) (globalMiddle_obj_eq_stage f P Q Δ N h) (by rfl)
    (globalIApp_eq_stage f P Q Δ N h) (globalPApp_eq_stage f P Q Δ N h)

private theorem global_fac : globalI f P Q ≫ globalP f P Q = f := by
  apply NatTrans.ext
  funext Δ
  exact global_fac_app f P Q Δ

/-- Raw global factorization data, before the relative latching and matching arrows are
identified. -/
private structure RawGlobalFactorization where
  Z : SimplicialObject C
  i : X ⟶ Z
  p : Z ⟶ Y
  fac : i ≫ p = f

/-- The globally assembled raw factorization. No Reedy-class membership is asserted here. -/
private noncomputable def rawGlobalFactorization : RawGlobalFactorization f where
  Z := globalMiddle f P Q
  i := globalI f P Q
  p := globalP f P Q
  fac := global_fac f P Q

section RelativeComparison

variable [P.RespectsIso] [Q.RespectsIso]

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalLatchingObjEq (n : ℕ) (a : latchingIndex n) :
    (globalMiddle f P Q).obj a.obj.left =
      (stages f P Q n).Z.obj ((latchingIndexToDegree n).obj a) := by
  let h : a.obj.left.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr a.property.2
  have h₁ := globalMiddle_obj_eq_stage f P Q a.obj.left n h
  have h₂ : degreeAtStage a.obj.left n h = (latchingIndexToDegree n).obj a := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  exact h₁.trans (congrArg (stages f P Q n).Z.obj h₂)

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalLatchingMapHEq (n : ℕ) {a b : latchingIndex n} (g : a ⟶ b) :
    HEq ((latchingDiagram (globalMiddle f P Q) n).map g)
      ((stageLatchingDiagram n (stages f P Q n).Z).map g) := by
  let ha : a.obj.left.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr a.property.2
  let hb : b.obj.left.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr b.property.2
  have hm := globalMiddle_map_eq_stage f P Q g.hom.left n ha hb
  have h₁ : degreeAtStage a.obj.left n ha = (latchingIndexToDegree n).obj a := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  have h₂ : degreeAtStage b.obj.left n hb = (latchingIndexToDegree n).obj b := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  cases h₁
  cases h₂
  exact hm

private noncomputable def globalLatchingDiagramIso (n : ℕ) :
    latchingDiagram (globalMiddle f P Q) n ≅
      stageLatchingDiagram n (stages f P Q n).Z :=
  NatIso.ofComponents
    (fun a => CategoryTheory.eqToIso (globalLatchingObjEq f P Q n a))
    (fun {a b} g => by
      let h₁ := globalLatchingObjEq f P Q n a
      let h₂ := globalLatchingObjEq f P Q n b
      have hm := globalLatchingMapHEq f P Q n g
      apply eq_of_heq
      exact ((comp_eqToHom_heq _ h₂).trans hm).trans
        (eqToHom_comp_heq _ h₁).symm)

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalMatchingObjEq (n : ℕ) (a : matchingIndex n) :
    (globalMiddle f P Q).obj a.obj.right =
      (stages f P Q n).Z.obj ((matchingIndexToDegree n).obj a) := by
  let h : a.obj.right.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr a.property.2
  have h₁ := globalMiddle_obj_eq_stage f P Q a.obj.right n h
  have h₂ : degreeAtStage a.obj.right n h = (matchingIndexToDegree n).obj a := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  exact h₁.trans (congrArg (stages f P Q n).Z.obj h₂)

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalMatchingMapHEq (n : ℕ) {a b : matchingIndex n} (g : a ⟶ b) :
    HEq ((matchingDiagram (globalMiddle f P Q) n).map g)
      ((stageMatchingDiagram n (stages f P Q n).Z).map g) := by
  let ha : a.obj.right.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr a.property.2
  let hb : b.obj.right.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr b.property.2
  have hm := globalMiddle_map_eq_stage f P Q g.hom.right n ha hb
  have h₁ : degreeAtStage a.obj.right n ha = (matchingIndexToDegree n).obj a := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  have h₂ : degreeAtStage b.obj.right n hb = (matchingIndexToDegree n).obj b := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  cases h₁
  cases h₂
  exact hm

private noncomputable def globalMatchingDiagramIso (n : ℕ) :
    matchingDiagram (globalMiddle f P Q) n ≅
      stageMatchingDiagram n (stages f P Q n).Z :=
  NatIso.ofComponents
    (fun a => CategoryTheory.eqToIso (globalMatchingObjEq f P Q n a))
    (fun {a b} g => by
      let h₁ := globalMatchingObjEq f P Q n a
      let h₂ := globalMatchingObjEq f P Q n b
      have hm := globalMatchingMapHEq f P Q n g
      apply eq_of_heq
      exact ((comp_eqToHom_heq _ h₂).trans hm).trans
        (eqToHom_comp_heq _ h₁).symm)

private noncomputable def globalLatchingObjectIso (n : ℕ) :
    latchingObject (globalMiddle f P Q) n ≅
      stageLatchingObject n (stages f P Q n).Z :=
  HasColimit.isoOfNatIso (globalLatchingDiagramIso f P Q n)

private noncomputable def globalMatchingObjectIso (n : ℕ) :
    matchingObject (globalMiddle f P Q) n ≅
      stageMatchingObject n (stages f P Q n).Z :=
  HasLimit.isoOfNatIso (globalMatchingDiagramIso f P Q n)

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalI_latching_component (n : ℕ) (a : latchingIndex n) :
    (globalI f P Q).app a.obj.left ≫ eqToHom (globalLatchingObjEq f P Q n a) =
      (stages f P Q n).i.app ((latchingIndexToDegree n).obj a) := by
  let h : a.obj.left.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr a.property.2
  have hi := globalI_app_eq_stage f P Q a.obj.left n h
  have hd : degreeAtStage a.obj.left n h = (latchingIndexToDegree n).obj a := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  cases hd
  apply eq_of_heq
  exact (comp_eqToHom_heq _ (globalLatchingObjEq f P Q n a)).trans hi

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalP_matching_component (n : ℕ) (a : matchingIndex n) :
    eqToHom (globalMatchingObjEq f P Q n a) ≫
        (stages f P Q n).p.app ((matchingIndexToDegree n).obj a) =
      (globalP f P Q).app a.obj.right := by
  let h : a.obj.right.unop.len + 1 ≤ n := Nat.succ_le_iff.mpr a.property.2
  have hp := globalP_app_eq_stage f P Q a.obj.right n h
  have hd : degreeAtStage a.obj.right n h = (matchingIndexToDegree n).obj a := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  cases hd
  apply eq_of_heq
  exact (eqToHom_comp_heq _ (globalMatchingObjEq f P Q n a)).trans hp.symm

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
private theorem globalLatchingI_iso (n : ℕ) :
    (latchingObjectFunctor n).map (globalI f P Q) ≫
        (globalLatchingObjectIso f P Q n).hom =
      stageLᵢ n (stages f P Q n) := by
  apply colimit.hom_ext
  intro a
  have he : latchingι (globalMiddle f P Q) n a ≫
      (globalLatchingObjectIso f P Q n).hom =
        eqToHom (globalLatchingObjEq f P Q n a) ≫
          stageLatchingι n (stages f P Q n).Z a := by
    simp [globalLatchingObjectIso, globalLatchingDiagramIso, latchingι,
      stageLatchingι, CategoryTheory.eqToIso.hom]
  calc
    latchingι X n a ≫
          ((latchingObjectFunctor n).map (globalI f P Q) ≫
            (globalLatchingObjectIso f P Q n).hom) =
        (globalI f P Q).app a.obj.left ≫
          (latchingι (globalMiddle f P Q) n a ≫
            (globalLatchingObjectIso f P Q n).hom) := by
              rw [← Category.assoc, latchingObjectFunctor_map_ι]
              simp only [Category.assoc]
    _ = (globalI f P Q).app a.obj.left ≫
        (eqToHom (globalLatchingObjEq f P Q n a) ≫
          stageLatchingι n (stages f P Q n).Z a) := by
            rw [he]
    _ = ((globalI f P Q).app a.obj.left ≫
          eqToHom (globalLatchingObjEq f P Q n a)) ≫
        stageLatchingι n (stages f P Q n).Z a := by simp only [Category.assoc]
    _ = (stages f P Q n).i.app ((latchingIndexToDegree n).obj a) ≫
        stageLatchingι n (stages f P Q n).Z a := by
          rw [globalI_latching_component]
    _ = latchingι X n a ≫ stageLᵢ n (stages f P Q n) := by
          rw [stageLᵢ_ι]

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
private theorem globalMatchingP_iso (n : ℕ) :
    (matchingObjectFunctor n).map (globalP f P Q) =
      (globalMatchingObjectIso f P Q n).hom ≫ stageMₚ n (stages f P Q n) := by
  apply limit.hom_ext
  intro a
  have he : (globalMatchingObjectIso f P Q n).hom ≫
      stageMatchingπ n (stages f P Q n).Z a =
        matchingπ (globalMiddle f P Q) n a ≫
          eqToHom (globalMatchingObjEq f P Q n a) := by
    simp [globalMatchingObjectIso, globalMatchingDiagramIso, matchingπ,
      stageMatchingπ, CategoryTheory.eqToIso.hom]
  calc
    (matchingObjectFunctor n).map (globalP f P Q) ≫ matchingπ Y n a =
        matchingπ (globalMiddle f P Q) n a ≫
          (globalP f P Q).app a.obj.right := by
            rw [matchingObjectFunctor_map_π]
    _ = matchingπ (globalMiddle f P Q) n a ≫
        (eqToHom (globalMatchingObjEq f P Q n a) ≫
          (stages f P Q n).p.app ((matchingIndexToDegree n).obj a)) := by
            rw [globalP_matching_component]
    _ = (matchingπ (globalMiddle f P Q) n a ≫
          eqToHom (globalMatchingObjEq f P Q n a)) ≫
        (stages f P Q n).p.app ((matchingIndexToDegree n).obj a) := by
          simp only [Category.assoc]
    _ = ((globalMatchingObjectIso f P Q n).hom ≫
          stageMatchingπ n (stages f P Q n).Z a) ≫
        (stages f P Q n).p.app ((matchingIndexToDegree n).obj a) := by
          rw [he]
    _ = (globalMatchingObjectIso f P Q n).hom ≫
        (stageMatchingπ n (stages f P Q n).Z a ≫
          (stages f P Q n).p.app ((matchingIndexToDegree n).obj a)) := by
          simp only [Category.assoc]
    _ = (globalMatchingObjectIso f P Q n).hom ≫
        (stageMₚ n (stages f P Q n) ≫ matchingπ Y n a) := by
          rw [stageMₚ_π]
    _ = ((globalMatchingObjectIso f P Q n).hom ≫
          stageMₚ n (stages f P Q n)) ≫ matchingπ Y n a := by
          simp only [Category.assoc]

private def latchingStageHom (n : ℕ) (a : latchingIndex n) :
    (degreeSucc n).obj ((latchingIndexToDegree n).obj a) ⟶ degreeLast n :=
  a.obj.hom

private def matchingStageHom (n : ℕ) (a : matchingIndex n) :
    degreeLast n ⟶ (degreeSucc n).obj ((matchingIndexToDegree n).obj a) :=
  a.obj.hom

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
private theorem successor_map_latching (n : ℕ) (a : latchingIndex n) :
    HEq
      ((stages f P Q (n + 1)).Z.map (latchingStageHom n a))
      (directMap n (stages f P Q n) P Q a) := by
  let H := stages f P Q n
  let k := ((latchingIndexToDegree n).obj a).degree
  let _ : Epi (latchingStageHom n a).unop := a.property.1
  have hpure := oldToNew_of_factor n H P Q k k (latchingStageHom n a)
    (latchingStageHom n a).unop (𝟙 _)
    (by simp)
  let b := latchingIndexOfEpi n k (latchingStageHom n a).unop.op
  have hidx : b = a := by
    have hl : b.obj.left = a.obj.left :=
      congrArg op (SimplexCategory.mk_len a.obj.left.unop)
    apply ObjectProperty.FullSubcategory.ext
    apply CostructuredArrow.obj_ext _ _ hl
    cases hl
    simp [b, latchingIndexOfEpi, latchingStageHom]
  have hpure' : oldToNew n H P Q k (latchingStageHom n a) = directMap n H P Q a := by
    let d := directMap n H P Q b
    have hmap := H.Z.map_id (oldDegree n k)
    have hc := congrArg (fun t => t ≫ d) hmap
    have hpure₀ : oldToNew n H P Q k (latchingStageHom n a) = d := by
      apply hpure.trans
      exact hc.trans (Category.id_comp d)
    have hd : HEq (directMap n H P Q
        (latchingIndexOfEpi n k (latchingStageHom n a).unop.op))
        (directMap n H P Q a) := by
      cases hidx
      rfl
    exact eq_of_heq ((heq_of_eq hpure₀).trans hd)
  have hm := extend_map_castSucc_last n H P Q ((latchingIndexToDegree n).obj a)
    (latchingStageHom n a)
  exact hm.trans (heq_of_eq hpure')

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
private theorem successor_map_matching (n : ℕ) (a : matchingIndex n) :
    HEq
      ((stages f P Q (n + 1)).Z.map (matchingStageHom n a))
      (inverseMap n (stages f P Q n) P Q a) := by
  let H := stages f P Q n
  let k := ((matchingIndexToDegree n).obj a).degree
  let _ : Mono (matchingStageHom n a).unop := a.property.1
  have hpure := newToOld_of_factor n H P Q k k (matchingStageHom n a)
    (𝟙 _) (matchingStageHom n a).unop
    (by simp)
  let b := matchingIndexOfMono n k (matchingStageHom n a).unop.op
  have hidx : b = a := by
    have hr : b.obj.right = a.obj.right :=
      congrArg op (SimplexCategory.mk_len a.obj.right.unop)
    apply ObjectProperty.FullSubcategory.ext
    apply StructuredArrow.obj_ext _ _ hr
    cases hr
    simp [b, matchingIndexOfMono, matchingStageHom]
  have hpure' : newToOld n H P Q k (matchingStageHom n a) = inverseMap n H P Q a := by
    let e := inverseMap n H P Q b
    have hmap := H.Z.map_id (oldDegree n k)
    have hc := congrArg (fun t => e ≫ t) hmap
    have hpure₀ : newToOld n H P Q k (matchingStageHom n a) = e := by
      apply hpure.trans
      exact hc.trans (Category.comp_id e)
    have hd : HEq (inverseMap n H P Q
        (matchingIndexOfMono n k (matchingStageHom n a).unop.op))
        (inverseMap n H P Q a) := by
      cases hidx
      rfl
    exact eq_of_heq ((heq_of_eq hpure₀).trans hd)
  have hm := extend_map_last_castSucc n H P Q ((matchingIndexToDegree n).obj a)
    (matchingStageHom n a)
  exact hm.trans (heq_of_eq hpure')

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalDegreeObjEq (n : ℕ) :
    (globalMiddle f P Q).obj (op ⦋n⦌) = newObj n (stages f P Q n) P Q := by
  exact extend_obj_last n (stages f P Q n) P Q

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalI_new_component (n : ℕ) :
    (globalI f P Q).app (op ⦋n⦌) ≫ eqToHom (globalDegreeObjEq f P Q n) =
      iNew n (stages f P Q n) P Q := by
  have h₁ := globalI_app_eq_birth f P Q (op ⦋n⦌)
  have h₂ := extendIApp_last n (stages f P Q n) P Q
  apply eq_of_heq
  exact (comp_eqToHom_heq _ (globalDegreeObjEq f P Q n)).trans (h₁.trans h₂)

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalP_new_component (n : ℕ) :
    eqToHom (globalDegreeObjEq f P Q n) ≫ pNew n (stages f P Q n) P Q =
      (globalP f P Q).app (op ⦋n⦌) := by
  have h₁ := globalP_app_eq_birth f P Q (op ⦋n⦌)
  have h₂ := extendPApp_last n (stages f P Q n) P Q
  apply eq_of_heq
  exact (eqToHom_comp_heq _ (globalDegreeObjEq f P Q n)).trans (h₁.trans h₂).symm

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalMap_latching_heq (n : ℕ) (a : latchingIndex n) :
    HEq ((globalMiddle f P Q).map a.obj.hom)
      (directMap n (stages f P Q n) P Q a) := by
  let ha : a.obj.left.unop.len + 1 ≤ n + 1 :=
    Nat.le_trans (Nat.succ_le_iff.mpr a.property.2) (Nat.le_succ n)
  let hn : n + 1 ≤ n + 1 := Nat.le_refl _
  have hm := globalMiddle_map_eq_stage f P Q a.obj.hom (n + 1) ha hn
  have hsrc : degreeAtStage a.obj.left (n + 1) ha =
      (degreeSucc n).obj ((latchingIndexToDegree n).obj a) := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  have htgt : degreeAtStage (op ⦋n⦌) (n + 1) hn = degreeLast n := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  have hm' : HEq ((stages f P Q (n + 1)).Z.map
      (homAtStage a.obj.hom (n + 1) ha hn))
      ((stages f P Q (n + 1)).Z.map (latchingStageHom n a)) := by
    cases hsrc
    cases htgt
    rfl
  exact hm.trans (hm'.trans (successor_map_latching f P Q n a))

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalMap_matching_heq (n : ℕ) (a : matchingIndex n) :
    HEq ((globalMiddle f P Q).map a.obj.hom)
      (inverseMap n (stages f P Q n) P Q a) := by
  let hn : n + 1 ≤ n + 1 := Nat.le_refl _
  let ha : a.obj.right.unop.len + 1 ≤ n + 1 :=
    Nat.le_trans (Nat.succ_le_iff.mpr a.property.2) (Nat.le_succ n)
  have hm := globalMiddle_map_eq_stage f P Q a.obj.hom (n + 1) hn ha
  have hsrc : degreeAtStage (op ⦋n⦌) (n + 1) hn = degreeLast n := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  have htgt : degreeAtStage a.obj.right (n + 1) ha =
      (degreeSucc n).obj ((matchingIndexToDegree n).obj a) := by
    apply DegreeLT.ext
    apply Fin.ext
    rfl
  have hm' : HEq ((stages f P Q (n + 1)).Z.map
      (homAtStage a.obj.hom (n + 1) hn ha))
      ((stages f P Q (n + 1)).Z.map (matchingStageHom n a)) := by
    cases hsrc
    cases htgt
    rfl
  exact hm.trans (hm'.trans (successor_map_matching f P Q n a))

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalLatchingMap_component (n : ℕ) (a : latchingIndex n) :
    eqToHom (globalLatchingObjEq f P Q n a) ≫
        directMap n (stages f P Q n) P Q a =
      (globalMiddle f P Q).map a.obj.hom ≫ eqToHom (globalDegreeObjEq f P Q n) := by
  apply eq_of_heq
  exact (eqToHom_comp_heq _ (globalLatchingObjEq f P Q n a)).trans
    ((comp_eqToHom_heq _ (globalDegreeObjEq f P Q n)).trans
      (globalMap_latching_heq f P Q n a)).symm

omit [P.RespectsIso] [Q.RespectsIso] in
private theorem globalMatchingMap_component (n : ℕ) (a : matchingIndex n) :
    eqToHom (globalDegreeObjEq f P Q n) ≫
        inverseMap n (stages f P Q n) P Q a =
      (globalMiddle f P Q).map a.obj.hom ≫
        eqToHom (globalMatchingObjEq f P Q n a) := by
  apply eq_of_heq
  exact (eqToHom_comp_heq _ (globalDegreeObjEq f P Q n)).trans
    ((comp_eqToHom_heq _ (globalMatchingObjEq f P Q n a)).trans
      (globalMap_matching_heq f P Q n a)).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def globalRelativeLatchingSourceIso (n : ℕ) :
    relativeLatchingObject (globalI f P Q) n ≅
      stageRelativeSource n (stages f P Q n) := by
  let eL := globalLatchingObjectIso f P Q n
  let m := pushout.map
    (latchingMap X n) ((latchingObjectFunctor n).map (globalI f P Q))
    (latchingMap X n) (stageLᵢ n (stages f P Q n))
    (𝟙 _) eL.hom (𝟙 _)
    (by simp)
    (by
      rw [Category.id_comp]
      exact globalLatchingI_iso f P Q n)
  let _ : IsIso m := by dsimp [m]; infer_instance
  exact asIso m

set_option backward.isDefEq.respectTransparency false in
private noncomputable def globalRelativeMatchingTargetIso (n : ℕ) :
    relativeMatchingObject (globalP f P Q) n ≅
      stageRelativeTarget n (stages f P Q n) := by
  let eM := globalMatchingObjectIso f P Q n
  let m := pullback.map
    (matchingMap Y n) ((matchingObjectFunctor n).map (globalP f P Q))
    (matchingMap Y n) (stageMₚ n (stages f P Q n))
    (𝟙 _) eM.hom (𝟙 _)
    (by simp)
    (by
      rw [Category.comp_id]
      exact globalMatchingP_iso f P Q n)
  let _ : IsIso m := by dsimp [m]; infer_instance
  exact asIso m

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem globalRelativeLatchingSourceIso_hom_inl (n : ℕ) :
    pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map (globalI f P Q)) ≫
        (globalRelativeLatchingSourceIso f P Q n).hom =
      pushout.inl (latchingMap X n) (stageLᵢ n (stages f P Q n)) := by
  simp only [globalRelativeLatchingSourceIso, asIso_hom, pushout.map,
    pushout.inl_desc, Category.id_comp]

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem globalRelativeLatchingSourceIso_hom_inr (n : ℕ) :
    pushout.inr (latchingMap X n) ((latchingObjectFunctor n).map (globalI f P Q)) ≫
        (globalRelativeLatchingSourceIso f P Q n).hom =
      (globalLatchingObjectIso f P Q n).hom ≫
        pushout.inr (latchingMap X n) (stageLᵢ n (stages f P Q n)) := by
  simp only [globalRelativeLatchingSourceIso, asIso_hom, pushout.map,
    pushout.inr_desc]

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem globalRelativeMatchingTargetIso_hom_fst (n : ℕ) :
    (globalRelativeMatchingTargetIso f P Q n).hom ≫
        pullback.fst (matchingMap Y n) (stageMₚ n (stages f P Q n)) =
      pullback.fst (matchingMap Y n) ((matchingObjectFunctor n).map (globalP f P Q)) := by
  simp only [globalRelativeMatchingTargetIso, asIso_hom, pullback.map,
    pullback.lift_fst, Category.comp_id]

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem globalRelativeMatchingTargetIso_hom_snd (n : ℕ) :
    (globalRelativeMatchingTargetIso f P Q n).hom ≫
        pullback.snd (matchingMap Y n) (stageMₚ n (stages f P Q n)) =
      pullback.snd (matchingMap Y n) ((matchingObjectFunctor n).map (globalP f P Q)) ≫
        (globalMatchingObjectIso f P Q n).hom := by
  simp only [globalRelativeMatchingTargetIso, asIso_hom, pullback.map,
    pullback.lift_snd]

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
private theorem globalLatchingStructure_iso (n : ℕ) :
    (globalLatchingObjectIso f P Q n).hom ≫
        pushout.inr (latchingMap X n) (stageLᵢ n (stages f P Q n)) ≫
          j n (stages f P Q n) P Q =
      latchingMap (globalMiddle f P Q) n ≫ eqToHom (globalDegreeObjEq f P Q n) := by
  apply colimit.hom_ext
  intro a
  have he : latchingι (globalMiddle f P Q) n a ≫
      (globalLatchingObjectIso f P Q n).hom =
        eqToHom (globalLatchingObjEq f P Q n a) ≫
          stageLatchingι n (stages f P Q n).Z a := by
    simp [globalLatchingObjectIso, globalLatchingDiagramIso, latchingι,
      stageLatchingι, CategoryTheory.eqToIso.hom]
  calc
    latchingι (globalMiddle f P Q) n a ≫
          ((globalLatchingObjectIso f P Q n).hom ≫
            pushout.inr (latchingMap X n) (stageLᵢ n (stages f P Q n)) ≫
              j n (stages f P Q n) P Q) =
      (latchingι (globalMiddle f P Q) n a ≫
          (globalLatchingObjectIso f P Q n).hom) ≫
        pushout.inr (latchingMap X n) (stageLᵢ n (stages f P Q n)) ≫
          j n (stages f P Q n) P Q := by simp only [Category.assoc]
    _ = (eqToHom (globalLatchingObjEq f P Q n a) ≫
          stageLatchingι n (stages f P Q n).Z a) ≫
        pushout.inr (latchingMap X n) (stageLᵢ n (stages f P Q n)) ≫
          j n (stages f P Q n) P Q := by rw [he]
    _ = eqToHom (globalLatchingObjEq f P Q n a) ≫
        directMap n (stages f P Q n) P Q a := by
          simp only [directMap, Category.assoc]
    _ = (globalMiddle f P Q).map a.obj.hom ≫
        eqToHom (globalDegreeObjEq f P Q n) :=
      globalLatchingMap_component f P Q n a
    _ = (latchingι (globalMiddle f P Q) n a ≫
          latchingMap (globalMiddle f P Q) n) ≫
        eqToHom (globalDegreeObjEq f P Q n) := by rw [latchingMap_ι]
    _ = latchingι (globalMiddle f P Q) n a ≫
        (latchingMap (globalMiddle f P Q) n ≫
          eqToHom (globalDegreeObjEq f P Q n)) := by simp only [Category.assoc]

omit [P.RespectsIso] [Q.RespectsIso] in
set_option backward.isDefEq.respectTransparency false in
private theorem globalMatchingStructure_iso (n : ℕ) :
    eqToHom (globalDegreeObjEq f P Q n) ≫ q n (stages f P Q n) P Q ≫
        pullback.snd (matchingMap Y n) (stageMₚ n (stages f P Q n)) =
      matchingMap (globalMiddle f P Q) n ≫
        (globalMatchingObjectIso f P Q n).hom := by
  apply limit.hom_ext
  intro a
  have he : (globalMatchingObjectIso f P Q n).hom ≫
      stageMatchingπ n (stages f P Q n).Z a =
        matchingπ (globalMiddle f P Q) n a ≫
          eqToHom (globalMatchingObjEq f P Q n a) := by
    simp [globalMatchingObjectIso, globalMatchingDiagramIso, matchingπ,
      stageMatchingπ, CategoryTheory.eqToIso.hom]
  calc
    (eqToHom (globalDegreeObjEq f P Q n) ≫ q n (stages f P Q n) P Q ≫
          pullback.snd (matchingMap Y n) (stageMₚ n (stages f P Q n))) ≫
        stageMatchingπ n (stages f P Q n).Z a =
      eqToHom (globalDegreeObjEq f P Q n) ≫
        inverseMap n (stages f P Q n) P Q a := by
          simp only [inverseMap, Category.assoc]
    _ = (globalMiddle f P Q).map a.obj.hom ≫
        eqToHom (globalMatchingObjEq f P Q n a) :=
      globalMatchingMap_component f P Q n a
    _ = (matchingMap (globalMiddle f P Q) n ≫
          matchingπ (globalMiddle f P Q) n a) ≫
        eqToHom (globalMatchingObjEq f P Q n a) := by rw [matchingMap_π]
    _ = matchingMap (globalMiddle f P Q) n ≫
        (matchingπ (globalMiddle f P Q) n a ≫
          eqToHom (globalMatchingObjEq f P Q n a)) := by simp only [Category.assoc]
    _ = matchingMap (globalMiddle f P Q) n ≫
        ((globalMatchingObjectIso f P Q n).hom ≫
          stageMatchingπ n (stages f P Q n).Z a) := by rw [he]
    _ = (matchingMap (globalMiddle f P Q) n ≫
          (globalMatchingObjectIso f P Q n).hom) ≫
        stageMatchingπ n (stages f P Q n).Z a := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def globalRelativeLatchingArrowIso (n : ℕ) :
    Arrow.mk (relativeLatchingMap (globalI f P Q) n) ≅
      Arrow.mk (j n (stages f P Q n) P Q) := by
  let eS := globalRelativeLatchingSourceIso f P Q n
  let eT := CategoryTheory.eqToIso (globalDegreeObjEq f P Q n)
  refine Arrow.isoMk eS eT ?_
  apply pushout.hom_ext
  · let inlG := pushout.inl (latchingMap X n)
        ((latchingObjectFunctor n).map (globalI f P Q))
    let inlS := pushout.inl (latchingMap X n) (stageLᵢ n (stages f P Q n))
    have hS := globalRelativeLatchingSourceIso_hom_inl f P Q n
    have hleft : (inlG ≫ eS.hom) ≫ j n (stages f P Q n) P Q =
        iNew n (stages f P Q n) P Q := by
      calc
        (inlG ≫ eS.hom) ≫ j n (stages f P Q n) P Q =
            inlS ≫ j n (stages f P Q n) P Q := by
              simpa only [Category.assoc] using
                congrArg (fun t => t ≫ j n (stages f P Q n) P Q) hS
        _ = iNew n (stages f P Q n) P Q := by rfl
    have hR := relativeLatchingMap_inl (globalI f P Q) n
    have hright : (inlG ≫ relativeLatchingMap (globalI f P Q) n) ≫ eT.hom =
        (globalI f P Q).app (op ⦋n⦌) ≫ eT.hom := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ eT.hom) hR
    have h := hleft.trans ((globalI_new_component f P Q n).symm.trans hright.symm)
    dsimp [eS, eT] at h ⊢
    simpa only [Category.assoc] using h
  · let inrG := pushout.inr (latchingMap X n)
        ((latchingObjectFunctor n).map (globalI f P Q))
    let inrS := pushout.inr (latchingMap X n) (stageLᵢ n (stages f P Q n))
    have hS := globalRelativeLatchingSourceIso_hom_inr f P Q n
    have hleft : (inrG ≫ eS.hom) ≫ j n (stages f P Q n) P Q =
        ((globalLatchingObjectIso f P Q n).hom ≫ inrS) ≫
          j n (stages f P Q n) P Q := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ j n (stages f P Q n) P Q) hS
    have hR := relativeLatchingMap_inr (globalI f P Q) n
    have hright : (inrG ≫ relativeLatchingMap (globalI f P Q) n) ≫ eT.hom =
        latchingMap (globalMiddle f P Q) n ≫ eT.hom := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ eT.hom) hR
    have hstruct : ((globalLatchingObjectIso f P Q n).hom ≫ inrS) ≫
        j n (stages f P Q n) P Q =
          latchingMap (globalMiddle f P Q) n ≫ eT.hom := by
      dsimp [inrS, eT]
      simpa only [Category.assoc] using globalLatchingStructure_iso f P Q n
    have h := hleft.trans (hstruct.trans hright.symm)
    dsimp [eS, eT] at h ⊢
    simpa only [Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def globalRelativeMatchingArrowIso (n : ℕ) :
    Arrow.mk (relativeMatchingMap (globalP f P Q) n) ≅
      Arrow.mk (q n (stages f P Q n) P Q) := by
  let eS := CategoryTheory.eqToIso (globalDegreeObjEq f P Q n)
  let eT := globalRelativeMatchingTargetIso f P Q n
  refine Arrow.isoMk eS eT ?_
  apply pullback.hom_ext
  · let fstG := pullback.fst (matchingMap Y n)
        ((matchingObjectFunctor n).map (globalP f P Q))
    let fstS := pullback.fst (matchingMap Y n) (stageMₚ n (stages f P Q n))
    have hT := globalRelativeMatchingTargetIso_hom_fst f P Q n
    have hleft : (eS.hom ≫ q n (stages f P Q n) P Q) ≫ fstS =
        (globalP f P Q).app (op ⦋n⦌) := by
      calc
        (eS.hom ≫ q n (stages f P Q n) P Q) ≫ fstS =
            eS.hom ≫ pNew n (stages f P Q n) P Q := by
              dsimp [fstS]
              simp only [pNew, Category.assoc]
        _ = (globalP f P Q).app (op ⦋n⦌) := globalP_new_component f P Q n
    have hR := relativeMatchingMap_fst (globalP f P Q) n
    have hright : (relativeMatchingMap (globalP f P Q) n ≫ eT.hom) ≫ fstS =
        (globalP f P Q).app (op ⦋n⦌) := by
      calc
        (relativeMatchingMap (globalP f P Q) n ≫ eT.hom) ≫ fstS =
            relativeMatchingMap (globalP f P Q) n ≫ fstG := by
              simpa only [Category.assoc] using
                congrArg (fun t => relativeMatchingMap (globalP f P Q) n ≫ t) hT
        _ = (globalP f P Q).app (op ⦋n⦌) := hR
    dsimp [eS, eT] at hleft hright ⊢
    exact hleft.trans hright.symm
  · let sndG := pullback.snd (matchingMap Y n)
        ((matchingObjectFunctor n).map (globalP f P Q))
    let sndS := pullback.snd (matchingMap Y n) (stageMₚ n (stages f P Q n))
    have hT := globalRelativeMatchingTargetIso_hom_snd f P Q n
    have hleft : (eS.hom ≫ q n (stages f P Q n) P Q) ≫ sndS =
        matchingMap (globalMiddle f P Q) n ≫
          (globalMatchingObjectIso f P Q n).hom := by
      simpa [eS, sndS, Category.assoc] using globalMatchingStructure_iso f P Q n
    have hR := relativeMatchingMap_snd (globalP f P Q) n
    have hright : (relativeMatchingMap (globalP f P Q) n ≫ eT.hom) ≫ sndS =
        matchingMap (globalMiddle f P Q) n ≫
          (globalMatchingObjectIso f P Q n).hom := by
      calc
        (relativeMatchingMap (globalP f P Q) n ≫ eT.hom) ≫ sndS =
            relativeMatchingMap (globalP f P Q) n ≫
              (sndG ≫ (globalMatchingObjectIso f P Q n).hom) := by
                simpa only [Category.assoc] using
                  congrArg (fun t => relativeMatchingMap (globalP f P Q) n ≫ t) hT
        _ = matchingMap (globalMiddle f P Q) n ≫
            (globalMatchingObjectIso f P Q n).hom := by
              simpa only [Category.assoc] using
                congrArg (fun t => t ≫ (globalMatchingObjectIso f P Q n).hom) hR
    dsimp [eS, eT] at hleft hright ⊢
    exact hleft.trans hright.symm

omit [Q.RespectsIso] in
private theorem globalI_reedyLeft : reedyLeft P (globalI f P Q) := by
  intro n
  exact (P.arrow_mk_iso_iff (globalRelativeLatchingArrowIso f P Q n)).2
    (j_mem n (stages f P Q n) P Q)

omit [P.RespectsIso] in
private theorem globalP_reedyRight : reedyRight Q (globalP f P Q) := by
  intro n
  exact (Q.arrow_mk_iso_iff (globalRelativeMatchingArrowIso f P Q n)).2
    (q_mem n (stages f P Q n) P Q)

/-- The exact global Reedy factorization data obtained from the stage tower. -/
noncomputable def reedyMapFactorizationData :
    (reedyLeft P).MapFactorizationData (reedyRight Q) f where
  Z := globalMiddle f P Q
  i := globalI f P Q
  p := globalP f P Q
  fac := by exact global_fac f P Q
  hi := by exact globalI_reedyLeft f P Q
  hp := by exact globalP_reedyRight f P Q

end RelativeComparison

end StageTower

end ReedyR4OneDegreeFunctorPreflight

end CategoryTheory.SimplicialObject
