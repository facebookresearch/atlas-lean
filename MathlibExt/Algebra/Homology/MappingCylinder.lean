/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module


public import Mathlib.Algebra.Homology.HomotopyCategory
public import MathlibExt.Algebra.Homology.HomotopyCofiberSplitting

/-!
# Mapping cylinders of morphisms of homological complexes

For a morphism `f : F ⟶ G`, its mapping cylinder is the homotopy cofiber
of `(1, -f) : F ⟶ F ⊞ G`.  It comes with maps from `F` and `G`, a
projection to `G`, the expected universal morphisms, and a deformation
retraction onto `G`.

Mathlib's `HomologicalComplex.cylinder F` is the special case `f = 1`; the
construction here is functorial in an arbitrary arrow.

The functorial action and deformation retraction require
`H : ∀ j, ∃ i, c.Rel i j`, so every degree has a predecessor. This
hypothesis is essential for shapes with a boundary: for `ComplexShape.up ℕ`,
degree zero has no predecessor.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Preadditive

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
variable {F G K : HomologicalComplex C c}

/-- The existence condition for the mapping cylinder of `f`. -/
abbrev HasMappingCylinder (f : F ⟶ G) : Prop :=
  HasHomotopyCofiber (biprod.lift (𝟙 F) (-f))

/-- The mapping cylinder of `f : F ⟶ G`. -/
noncomputable abbrev mappingCylinder (f : F ⟶ G)
    [HasMappingCylinder f] : HomologicalComplex C c :=
  homotopyCofiber (biprod.lift (𝟙 F) (-f))

namespace mappingCylinder

variable (f : F ⟶ G)

/-- The arrow whose homotopy cofiber is the mapping cylinder. -/
noncomputable abbrev arrow : F ⟶ F ⊞ G :=
  biprod.lift (𝟙 F) (-f)

variable [HasMappingCylinder f]

/-- The source endpoint `F ⟶ mappingCylinder f`. -/
noncomputable def source : F ⟶ mappingCylinder f :=
  biprod.inl ≫ homotopyCofiber.inr (arrow f)

/-- The target endpoint `G ⟶ mappingCylinder f`. -/
noncomputable def target : G ⟶ mappingCylinder f :=
  biprod.inr ≫ homotopyCofiber.inr (arrow f)

omit [DecidableRel c.Rel] [HasMappingCylinder f] in
/-- The defining arrow is the difference of the two endpoint coordinates. -/
theorem arrow_eq :
    arrow f = biprod.inl - f ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp [arrow]
  · simp [arrow]

/-- The defining cofiber relation is the difference between the source
endpoint and the source map followed by the target endpoint. -/
theorem arrow_comp_inr :
    arrow f ≫ homotopyCofiber.inr (arrow f) =
      source f - f ≫ target f := by
  calc
    arrow f ≫ homotopyCofiber.inr (arrow f) =
        (biprod.inl - f ≫ biprod.inr) ≫
          homotopyCofiber.inr (arrow f) := by
      exact congrArg
        (fun k : F ⟶ F ⊞ G ↦
          k ≫ homotopyCofiber.inr (arrow f)) (arrow_eq f)
    _ = source f - f ≫ target f := by
      simp only [sub_comp, source, target, Category.assoc]

/-- The canonical homotopy from the source endpoint to the source map
followed by the target endpoint. -/
noncomputable def sourceTargetHomotopy
    (H : ∀ j, ∃ i, c.Rel i j) :
    _root_.Homotopy (source f) (f ≫ target f) :=
  _root_.Homotopy.equivSubZero.symm
    ((_root_.Homotopy.ofEq (arrow_comp_inr f).symm).trans
      (homotopyCofiber.inrCompHomotopy (arrow f) H))

/-- The null homotopy defining the projection to the target. -/
noncomputable def projectionHomotopy :
    _root_.Homotopy
      (arrow f ≫ biprod.desc f (𝟙 G)) 0 :=
  _root_.Homotopy.ofEq (by simp [arrow])

/-- Projection from the mapping cylinder to its target. -/
noncomputable def projection : mappingCylinder f ⟶ G :=
  homotopyCofiber.desc (arrow f) (biprod.desc f (𝟙 G))
    (projectionHomotopy f)

/-- The source endpoint followed by the projection is `f`. -/
@[reassoc (attr := simp)]
theorem source_projection : source f ≫ projection f = f := by
  simp [source, projection]

/-- The target endpoint is a section of the projection. -/
@[reassoc (attr := simp)]
theorem target_projection : target f ≫ projection f = 𝟙 G := by
  simp [target, projection]

section Desc

variable (e : F ⟶ K) (g : G ⟶ K)
  (h : _root_.Homotopy e (f ≫ g))

/-- The null homotopy used to define a morphism from a mapping cylinder. -/
noncomputable def descHomotopy :
    _root_.Homotopy (arrow f ≫ biprod.desc e g) 0 :=
  (_root_.Homotopy.ofEq (by
      rw [arrow_eq, sub_comp, biprod.inl_desc,
        Category.assoc, biprod.inr_desc])).trans
    (_root_.Homotopy.equivSubZero h)

/-- A morphism from a mapping cylinder, specified on both endpoints and by
a homotopy between the required source maps. -/
noncomputable def desc : mappingCylinder f ⟶ K :=
  homotopyCofiber.desc (arrow f) (biprod.desc e g)
    (descHomotopy f e g h)

@[reassoc (attr := simp)]
theorem source_desc : source f ≫ desc f e g h = e := by
  simp [source, desc]

@[reassoc (attr := simp)]
theorem target_desc : target f ≫ desc f e g h = g := by
  simp [target, desc]

/-- Characteristic formula for `desc` on the shifted-source generator. -/
@[reassoc (attr := simp)]
theorem inlX_desc (i j : ι) (hji : c.Rel j i) :
    homotopyCofiber.inlX (arrow f) i j hji ≫
        (desc f e g h).f j =
      (descHomotopy f e g h).hom i j :=
  homotopyCofiber.inlX_desc_f (arrow f)
    (biprod.desc e g) (descHomotopy f e g h) i j hji

/-- Characteristic formula for `desc` on the endpoint-biproduct generator. -/
@[reassoc (attr := simp)]
theorem inrX_desc (i : ι) :
    homotopyCofiber.inrX (arrow f) i ≫
        (desc f e g h).f i =
      (biprod.desc e g).f i :=
  homotopyCofiber.inrX_desc_f (arrow f)
    (biprod.desc e g) (descHomotopy f e g h) i

end Desc

/-- The shifted-source inclusion into the homotopy cofiber model. -/
noncomputable abbrev inlX (i j : ι) (hij : c.Rel j i) :
    F.X i ⟶ (mappingCylinder f).X j :=
  homotopyCofiber.inlX (arrow f) i j hij

/-- The endpoint-biproduct inclusion into the homotopy cofiber model. -/
noncomputable abbrev inrX (i : ι) :
    (F ⊞ G).X i ⟶ (mappingCylinder f).X i :=
  homotopyCofiber.inrX (arrow f) i

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem inlX_projection (i j : ι) (hij : c.Rel j i) :
    inlX f i j hij ≫ (projection f).f j = 0 := by
  simp [projection, projectionHomotopy]

@[reassoc (attr := simp)]
theorem inrX_projection (i : ι) :
    inrX f i ≫ (projection f).f i =
      (biprod.desc f (𝟙 G)).f i :=
  homotopyCofiber.inrX_desc_f _ _ _ _

section Functoriality

variable {F' G' : HomologicalComplex C c} {f' : F' ⟶ G'}
  [HasMappingCylinder f']

/-- A strict square induces a strict square between the arrows defining the
two mapping cylinders. -/
noncomputable def arrowMap
    (f' : F' ⟶ G')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    Arrow.mk (arrow f) ⟶ Arrow.mk (arrow f') where
  left := a.left
  right := biprod.map a.left a.right
  w := by
    apply biprod.hom_ext
    · simp [arrow]
    · simp [arrow]

omit [DecidableRel c.Rel] [HasMappingCylinder f]
    [HasMappingCylinder f'] in
@[simp]
theorem arrowMap_left
    (f' : F' ⟶ G')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    (arrowMap f f' a).left = a.left :=
  rfl

omit [DecidableRel c.Rel] [HasMappingCylinder f]
    [HasMappingCylinder f'] in
@[simp]
theorem arrowMap_right
    (f' : F' ⟶ G')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    (arrowMap f f' a).right = biprod.map a.left a.right :=
  rfl

omit [DecidableRel c.Rel] [HasMappingCylinder f] in
@[simp]
theorem arrowMap_id :
    arrowMap f f (𝟙 (Arrow.mk f)) =
      𝟙 (Arrow.mk (arrow f)) := by
  apply Arrow.hom_ext
  · rfl
  · apply biprod.hom_ext <;> simp

omit [DecidableRel c.Rel] [HasMappingCylinder f]
    [HasMappingCylinder f'] in
@[reassoc]
theorem arrowMap_comp
    (f' : F' ⟶ G')
    {F'' G'' : HomologicalComplex C c} (f'' : F'' ⟶ G'')
    (a : Arrow.mk f ⟶ Arrow.mk f')
    (b : Arrow.mk f' ⟶ Arrow.mk f'') :
    arrowMap f f'' (a ≫ b) =
      arrowMap f f' a ≫ arrowMap f' f'' b := by
  apply Arrow.hom_ext
  · rfl
  · apply biprod.hom_ext <;> simp [Category.assoc]

/-- The induced map of mapping cylinders. -/
noncomputable def map (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    mappingCylinder f ⟶ mappingCylinder f' :=
  homotopyCofiber.mapArrowHom (arrow f) (arrow f') H
    (arrowMap f f' a)

@[simp]
theorem map_id (H : ∀ j, ∃ i, c.Rel i j) :
    map f f H (𝟙 (Arrow.mk f)) =
      𝟙 (mappingCylinder f) := by
  change homotopyCofiber.mapArrowHom (arrow f) (arrow f) H
      (arrowMap f f (𝟙 (Arrow.mk f))) = 𝟙 _
  rw [arrowMap_id]
  exact homotopyCofiber.mapArrowHom_id (arrow f) H

@[reassoc]
theorem map_comp (H : ∀ j, ∃ i, c.Rel i j)
    {F'' G'' : HomologicalComplex C c} {f'' : F'' ⟶ G''}
    [HasMappingCylinder f'']
    (a : Arrow.mk f ⟶ Arrow.mk f')
    (b : Arrow.mk f' ⟶ Arrow.mk f'') :
    map f f'' H (a ≫ b) = map f f' H a ≫ map f' f'' H b := by
  change homotopyCofiber.mapArrowHom (arrow f) (arrow f'') H
      (arrowMap f f'' (a ≫ b)) = _
  rw [arrowMap_comp f f' f'' a b]
  exact homotopyCofiber.mapArrowHom_comp
    (arrow f) (arrow f') (arrow f'') H
      (arrowMap f f' a) (arrowMap f' f'' b)

@[reassoc (attr := simp)]
theorem source_map (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    source f ≫ map f f' H a = a.left ≫ source f' := by
  simp [source, map, Category.assoc,
    homotopyCofiber.inr_mapArrowHom]

@[reassoc (attr := simp)]
theorem target_map (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    target f ≫ map f f' H a = a.right ≫ target f' := by
  simp [target, map, Category.assoc,
    homotopyCofiber.inr_mapArrowHom]

/-- Naturality of the mapping-cylinder projection. -/
@[reassoc]
theorem map_projection (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    map f f' H a ≫ projection f' =
      projection f ≫ a.right := by
  apply homotopyCofiber.mapArrowHom_desc_naturality H
      (arrowMap f f' a)
      (biprod.desc f (𝟙 G))
      (biprod.desc f' (𝟙 G'))
      (projectionHomotopy f) (projectionHomotopy f') a.right
  · apply biprod.hom_ext'
    · simp
    · simp
  · intro i j
    simp [projectionHomotopy]

end Functoriality

variable (C c)

/-- The functor on arrows sending `f` to `(1, -f)`. -/
noncomputable def arrowFunctor :
    Arrow (HomologicalComplex C c) ⥤
      Arrow (HomologicalComplex C c) where
  obj f := Arrow.mk (arrow f.hom)
  map {f f'} a := arrowMap f.hom f'.hom a
  map_id f := arrowMap_id f.hom
  map_comp {f f' f''} a b :=
    arrowMap_comp f.hom f'.hom f''.hom a b

variable {C c}

/-- The mapping cylinder, functorial in strict commutative squares. -/
noncomputable def functor (H : ∀ j, ∃ i, c.Rel i j) :
    Arrow (HomologicalComplex C c) ⥤ HomologicalComplex C c :=
  arrowFunctor C c ⋙ HomologicalComplex.homotopyCofiberFunctor H

@[simp]
theorem functor_obj (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (functor H).obj f = mappingCylinder f.hom :=
  rfl

@[simp]
theorem functor_map (H : ∀ j, ∃ i, c.Rel i j)
    {f f' : Arrow (HomologicalComplex C c)} (a : f ⟶ f') :
    (functor H).map a = map f.hom f'.hom H a :=
  rfl

/-- The source endpoints form a natural transformation. -/
noncomputable def sourceNatTrans (H : ∀ j, ∃ i, c.Rel i j) :
    (Arrow.leftFunc : Arrow (HomologicalComplex C c) ⥤ _) ⟶
      functor H where
  app f := source f.hom
  naturality {f f'} a := (source_map f.hom f'.hom H a).symm

/-- The target endpoints form a natural transformation. -/
noncomputable def targetNatTrans (H : ∀ j, ∃ i, c.Rel i j) :
    (Arrow.rightFunc : Arrow (HomologicalComplex C c) ⥤ _) ⟶
      functor H where
  app f := target f.hom
  naturality {f f'} a := (target_map f.hom f'.hom H a).symm

/-- The projections form a natural transformation. -/
noncomputable def projectionNatTrans
    (H : ∀ j, ∃ i, c.Rel i j) :
    functor H ⟶
      (Arrow.rightFunc : Arrow (HomologicalComplex C c) ⥤ _) where
  app f := projection f.hom
  naturality {f f'} a := map_projection f.hom f'.hom H a

@[simp]
theorem targetNatTrans_comp_projectionNatTrans
    (H : ∀ j, ∃ i, c.Rel i j) :
    targetNatTrans H ≫ projectionNatTrans H =
      𝟙 (Arrow.rightFunc :
        Arrow (HomologicalComplex C c) ⥤ _) := by
  ext f
  simp [targetNatTrans, projectionNatTrans]

/-!
## Deformation retraction

The proof follows six explicit steps before assembling the homotopy
equivalence:

1. project a cylinder element to its `F ⊞ G` endpoint coordinates;
2. retain the `F` coordinate and insert it in the shifted cofiber summand;
3. form the null-homotopic endomorphism determined by those degreewise maps;
4. verify on the shifted-source generator `inlX` that it agrees with
   `1 - projection ≫ target`;
5. verify the same identity on `inrX`, separately on the `F` and `G`
   biproduct coordinates, using `arrow_eq`;
6. apply the homotopy-cofiber extensionality lemmas and convert the resulting
   null homotopy into a homotopy from `projection ≫ target` to the identity.

Thus the retraction and its homotopy are constructed from the cofiber
generators; neither is stored as an assumption.
-/

section Retraction

variable (H : ∀ j, ∃ i, c.Rel i j)

namespace projectionCompTargetHomotopy

/-- A null-homotopic endomorphism which will be identified with
`1 - projection f ≫ target f`. -/
noncomputable def nullHomotopicMap :
    mappingCylinder f ⟶ mappingCylinder f :=
  _root_.Homotopy.nullHomotopicMap'
    (fun i j hij ↦
      homotopyCofiber.sndX (arrow f) i ≫
        (biprod.fst : F ⊞ G ⟶ F).f i ≫
          inlX f i j hij)

/-- The tautological null homotopy of `nullHomotopicMap`. -/
noncomputable def nullHomotopy :
    _root_.Homotopy (nullHomotopicMap f) 0 :=
  _root_.Homotopy.nullHomotopy' _

theorem inlX_nullHomotopicMap_f
    (i j : ι) (hij : c.Rel j i) :
    inlX f i j hij ≫ (nullHomotopicMap f).f j =
      inlX f i j hij ≫
        (𝟙 _ - projection f ≫ target f).f j := by
  dsimp [nullHomotopicMap]
  by_cases! hj : ∃ k, c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [Category.assoc,
      _root_.Homotopy.nullHomotopicMap'_f hjk hij,
      homotopyCofiber_d,
      homotopyCofiber.d_sndX_assoc _ _ _ hij,
      Preadditive.add_comp, Preadditive.comp_add,
      homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc,
      zero_comp, add_zero, comp_sub, inlX_projection_assoc,
      Category.comp_id, sub_zero, ← HomologicalComplex.comp_f_assoc,
      biprod.lift_fst, id_f, Category.id_comp]
  · simp only [_root_.Homotopy.nullHomotopicMap'_f_of_not_rel_right
        hij hj,
      homotopyCofiber_d, Category.assoc, comp_sub, Category.comp_id,
      homotopyCofiber.d_sndX_assoc _ _ _ hij,
      Preadditive.add_comp, Preadditive.comp_add,
      zero_comp, add_zero, homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc,
      ← HomologicalComplex.comp_f_assoc, biprod.lift_fst,
      id_f, Category.id_comp, inlX_projection_assoc, sub_zero]

include H in
theorem inrX_nullHomotopicMap_f (j : ι) :
    inrX f j ≫ (nullHomotopicMap f).f j =
      inrX f j ≫
        (𝟙 _ - projection f ≫ target f).f j := by
  obtain ⟨i, hij⟩ := H j
  dsimp [nullHomotopicMap]
  by_cases hj : ∃ k, c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Category.assoc,
      _root_.Homotopy.nullHomotopicMap'_f hij hjk,
      homotopyCofiber_d, Preadditive.comp_add,
      homotopyCofiber.inrX_d_assoc,
      homotopyCofiber.inrX_sndX_assoc, comp_sub,
      inrX_projection_assoc, Category.comp_id,
      ← HomologicalComplex.comp_f_assoc,
      homotopyCofiber.inlX_d _ _ _ _ _ hjk]
    rw [← cancel_epi (biprodXIso F G j).inv]
    ext
    · simp [target, arrow_eq]
    · simp [target, arrow_eq]
  · simp only [not_exists] at hj
    simp only [Category.assoc,
      _root_.Homotopy.nullHomotopicMap'_f_of_not_rel_left hij hj,
      homotopyCofiber_d,
      homotopyCofiber.inlX_d' _ _ _ _ (hj _),
      homotopyCofiber.inrX_sndX_assoc,
      comp_sub, inrX_projection_assoc, Category.comp_id,
      target, HomologicalComplex.comp_f,
      homotopyCofiber.inr_f]
    rw [← cancel_epi (biprodXIso F G j).inv]
    ext
    · simp [arrow_eq]
    · simp [arrow_eq]

include H in
theorem nullHomotopicMap_eq :
    nullHomotopicMap f =
      𝟙 _ - projection f ≫ target f := by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact homotopyCofiber.ext_from_X (arrow f)
      (c.next i) i hi
      (inlX_nullHomotopicMap_f f _ _ hi)
      (inrX_nullHomotopicMap_f f H _)
  · exact homotopyCofiber.ext_from_X' (arrow f) i hi
      (inrX_nullHomotopicMap_f f H _)

end projectionCompTargetHomotopy

/-- The deformation homotopy from the projection followed by the target
endpoint to the identity of the mapping cylinder. -/
noncomputable def projectionCompTargetHomotopy :
    _root_.Homotopy (projection f ≫ target f)
      (𝟙 (mappingCylinder f)) :=
  (_root_.Homotopy.equivSubZero.symm
    ((_root_.Homotopy.ofEq
      (projectionCompTargetHomotopy.nullHomotopicMap_eq f H).symm).trans
        (projectionCompTargetHomotopy.nullHomotopy f))).symm

/-- The target endpoint is a homotopy equivalence. -/
@[simps]
noncomputable def homotopyEquiv :
    _root_.HomotopyEquiv G (mappingCylinder f) where
  hom := target f
  inv := projection f
  homotopyHomInvId := _root_.Homotopy.ofEq (by simp)
  homotopyInvHomId := projectionCompTargetHomotopy f H

end Retraction

section HomotopyCategory

variable (C c)

/-- In the homotopy category, the mapping-cylinder functor is naturally
isomorphic to evaluation at the target of an arrow. -/
noncomputable def homotopyCategoryNatIso
    (H : ∀ j, ∃ i, c.Rel i j) :
    functor H ⋙ HomotopyCategory.quotient C c ≅
      (Arrow.rightFunc : Arrow (HomologicalComplex C c) ⥤ _) ⋙
        HomotopyCategory.quotient C c :=
  NatIso.ofComponents
    (fun f ↦ (HomotopyCategory.isoOfHomotopyEquiv
      (homotopyEquiv f.hom H)).symm)
    (fun {f f'} a ↦ by
      change (HomotopyCategory.quotient C c).map
            (map f.hom f'.hom H a) ≫
          (HomotopyCategory.quotient C c).map (projection f'.hom) =
        (HomotopyCategory.quotient C c).map (projection f.hom) ≫
          (HomotopyCategory.quotient C c).map a.right
      rw [← Functor.map_comp, ← Functor.map_comp,
        map_projection f.hom f'.hom H a])

variable {C c}

@[simp]
theorem homotopyCategoryNatIso_hom_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (homotopyCategoryNatIso C c H).hom.app f =
      (HomotopyCategory.quotient C c).map (projection f.hom) :=
  rfl

@[simp]
theorem homotopyCategoryNatIso_inv_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (homotopyCategoryNatIso C c H).inv.app f =
      (HomotopyCategory.quotient C c).map (target f.hom) :=
  rfl

/-- The target endpoint identifies with the inverse of the homotopy-category
comparison. -/
@[reassoc]
theorem quotient_target_comp_homotopyCategoryNatIso_hom_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (HomotopyCategory.quotient C c).map (target f.hom) ≫
        (homotopyCategoryNatIso C c H).hom.app f =
      𝟙 ((HomotopyCategory.quotient C c).obj f.right) := by
  rw [homotopyCategoryNatIso_hom_app,
    ← CategoryTheory.Functor.map_comp, target_projection,
    CategoryTheory.Functor.map_id]

/-- The source endpoint followed by the homotopy-category comparison is the
original arrow. -/
@[reassoc]
theorem quotient_source_comp_homotopyCategoryNatIso_hom_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (HomotopyCategory.quotient C c).map (source f.hom) ≫
        (homotopyCategoryNatIso C c H).hom.app f =
      (HomotopyCategory.quotient C c).map f.hom := by
  rw [homotopyCategoryNatIso_hom_app,
    ← CategoryTheory.Functor.map_comp,
    source_projection]

end HomotopyCategory

end mappingCylinder

end HomologicalComplex

end
