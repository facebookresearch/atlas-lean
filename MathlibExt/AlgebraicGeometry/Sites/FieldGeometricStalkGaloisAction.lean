/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldFiniteGaloisStalkColimit
public import MathlibExt.CategoryTheory.Action.DiscreteAbelian
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.FieldTheory.KrullTopology

/-! # The canonical continuous left Galois action on the original field stalk

The same field, prescribed separable closure, original neighborhoods and
common stalk are retained. The topology on the stalk is discrete, while
its actual Galois group carries the Krull topology. Each germ has its own
finite Galois fixing subgroup; no finite quotient of the whole stalk is required.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- The original spectrum arrow of the prescribed Galois automorphism. -/
abbrev fieldGaloisSpec (g : Gal(Ω/k)) : Spec (.of Ω) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom g.toRingHom)

/-- It is the actual original endomorphism over Spec k. -/
def fieldGaloisOver (g : Gal(Ω/k)) :
    Over.mk (Spec.algebraMap k Ω) ⟶ Over.mk (Spec.algebraMap k Ω) :=
  Over.homMk (fieldGaloisSpec k Ω g) (Spec.homEquivAlgHom.symm g.toAlgHom).property

theorem fieldGaloisSpec_one : fieldGaloisSpec k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  have e : CommRingCat.ofHom (1 : Gal(Ω/k)).toRingHom = 𝟙 (CommRingCat.of Ω) := by
    ext x; rfl
  exact (congrArg Spec.map e).trans (Spec.map_id _)

theorem fieldGaloisSpec_mul (g h : Gal(Ω/k)) :
    fieldGaloisSpec k Ω (g * h) = fieldGaloisSpec k Ω g ≫ fieldGaloisSpec k Ω h := by
  have e : CommRingCat.ofHom (g * h).toRingHom =
      CommRingCat.ofHom h.toRingHom ≫ CommRingCat.ofHom g.toRingHom := by
    ext x; rfl
  exact (congrArg Spec.map e).trans (Spec.map_comp _ _)

theorem fieldGaloisOver_one : fieldGaloisOver k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact fieldGaloisSpec_one k Ω

theorem fieldGaloisOver_mul (g h : Gal(Ω/k)) :
    fieldGaloisOver k Ω (g * h) = fieldGaloisOver k Ω g ≫ fieldGaloisOver k Ω h := by
  apply Over.OverMorphism.ext
  exact fieldGaloisSpec_mul k Ω g h

variable [IsSepClosure k Ω]

/-- Precomposition on the original fibers is the actual stock coyoneda map. -/
def fieldGaloisFiberMap (g : Gal(Ω/k)) :
    (fieldGeometricPoint k Ω).fiber ⟶ (fieldGeometricPoint k Ω).fiber :=
  Functor.whiskerLeft (Scheme.Etale.forget (Spec (.of k)))
    (coyoneda.map (fieldGaloisOver k Ω g).op)

theorem fieldGaloisFiberMap_one : fieldGaloisFiberMap k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  ext U z
  let z' : Over.mk (Spec.algebraMap k Ω) ⟶
      (Scheme.Etale.forget (Spec (.of k))).obj U := z
  change fieldGaloisOver k Ω (1 : Gal(Ω/k)) ≫ z' = z'
  rw [fieldGaloisOver_one]
  exact Category.id_comp z'

theorem fieldGaloisFiberMap_mul (g h : Gal(Ω/k)) :
    fieldGaloisFiberMap k Ω (g * h) = fieldGaloisFiberMap k Ω h ≫ fieldGaloisFiberMap k Ω g := by
  ext U z
  let z' : Over.mk (Spec.algebraMap k Ω) ⟶
      (Scheme.Etale.forget (Spec (.of k))).obj U := z
  change fieldGaloisOver k Ω (g * h) ≫ z' =
    fieldGaloisOver k Ω g ≫ (fieldGaloisOver k Ω h ≫ z')
  rw [fieldGaloisOver_mul]
  exact Category.assoc _ _ z'

/-- Lift only the original geometric point indices to the common universe. -/
def fieldGaloisCommonFiberMap (g : Gal(Ω/k)) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber ⟶
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber :=
  Functor.whiskerRight (fieldGaloisFiberMap k Ω g) uliftFunctor.{w, u}

theorem fieldGaloisCommonFiberMap_one :
    fieldGaloisCommonFiberMap.{u, w} k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  change Functor.whiskerRight _ _ = _
  rw [fieldGaloisFiberMap_one]
  rfl

theorem fieldGaloisCommonFiberMap_mul (g h : Gal(Ω/k)) :
    fieldGaloisCommonFiberMap.{u, w} k Ω (g * h) =
      fieldGaloisCommonFiberMap.{u, w} k Ω h ≫ fieldGaloisCommonFiberMap.{u, w} k Ω g := by
  change Functor.whiskerRight _ _ = _
  rw [fieldGaloisFiberMap_mul]
  rfl

/-- Its original scheme coordinate is literal precomposition by Spec(g). -/
theorem fieldGaloisCommonFiberMap_left (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    ((fieldGaloisCommonFiberMap.{u, w} k Ω g).app U (ULift.up z)).down.left =
      fieldGaloisSpec k Ω g ≫ z.left := rfl

/-- The same common geometric point endomorphism. -/
def fieldGaloisPointEndomorphism (g : Gal(Ω/k)) :
    smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω) ⟶
      smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω) :=
  ⟨fieldGaloisCommonFiberMap.{u, w} k Ω g⟩

theorem fieldGaloisPointEndomorphism_one :
    fieldGaloisPointEndomorphism.{u, w} k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  apply GrothendieckTopology.Point.hom_ext
  exact fieldGaloisCommonFiberMap_one.{u, w} k Ω

theorem fieldGaloisPointEndomorphism_mul (g h : Gal(Ω/k)) :
    fieldGaloisPointEndomorphism.{u, w} k Ω (g * h) =
      fieldGaloisPointEndomorphism.{u, w} k Ω g ≫
        fieldGaloisPointEndomorphism.{u, w} k Ω h := by
  apply GrothendieckTopology.Point.hom_ext
  exact fieldGaloisCommonFiberMap_mul.{u, w} k Ω g h

/-- The actual natural endomorphism of the SAME original common stalk functor. -/
def fieldGaloisStalkMap (g : Gal(Ω/k)) :
    smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω) ⟶
      smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω) :=
  (fieldGaloisPointEndomorphism.{u, w} k Ω g).sheafFiber

theorem fieldGaloisStalkMap_one :
    fieldGaloisStalkMap.{u, w} k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  change (fieldGaloisPointEndomorphism.{u, w} k Ω (1 : Gal(Ω/k))).sheafFiber = _
  rw [fieldGaloisPointEndomorphism_one, GrothendieckTopology.Point.Hom.sheafFiber_id]

theorem fieldGaloisStalkMap_mul (g h : Gal(Ω/k)) :
    fieldGaloisStalkMap.{u, w} k Ω (g * h) =
      fieldGaloisStalkMap.{u, w} k Ω h ≫ fieldGaloisStalkMap.{u, w} k Ω g := by
  change (fieldGaloisPointEndomorphism.{u, w} k Ω (g * h)).sheafFiber = _
  rw [fieldGaloisPointEndomorphism_mul, GrothendieckTopology.Point.Hom.sheafFiber_comp]
  rfl

/-- The same original stalk carrier, with no additional coefficient lift. -/
abbrev fieldGeometricStalkCarrier
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) : Type (max u w) :=
  (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q

instance fieldGeometricStalkTopology
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    TopologicalSpace (fieldGeometricStalkCarrier.{u, w} k Ω Q) := ⊥

instance fieldGeometricStalkDiscreteTopology
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    DiscreteTopology (fieldGeometricStalkCarrier.{u, w} k Ω Q) := discreteTopology_bot _

/-- The two point/fiber reversals give the actual LEFT additive action. -/
instance fieldGeometricStalkDistribMulAction
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    DistribMulAction Gal(Ω/k) (fieldGeometricStalkCarrier.{u, w} k Ω Q) where
  smul g x := (fieldGaloisStalkMap.{u, w} k Ω g).app Q x
  one_smul x := by
    change (fieldGaloisStalkMap.{u, w} k Ω (1 : Gal(Ω/k))).app Q x = x
    rw [fieldGaloisStalkMap_one]
    rfl
  mul_smul g h x := by
    change (fieldGaloisStalkMap.{u, w} k Ω (g * h)).app Q x =
      (fieldGaloisStalkMap.{u, w} k Ω g).app Q ((fieldGaloisStalkMap.{u, w} k Ω h).app Q x)
    rw [fieldGaloisStalkMap_mul]
    rfl
  smul_zero g := ((fieldGaloisStalkMap.{u, w} k Ω g).app Q).hom.map_zero
  smul_add g := ((fieldGaloisStalkMap.{u, w} k Ω g).app Q).hom.map_add

/-- The SAME constructed stalk action on its raw point-fiber presentation. -/
abbrev fieldGeometricStalkSMul
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    SMul Gal(Ω/k) ((smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).presheafFiber.obj Q.obj : AddCommGrpCat.{max u w}) :=
  (fieldGeometricStalkDistribMulAction.{u, w} k Ω Q).toMulAction.toSemigroupAction.toSMul

/-- The original germ equation of the stock point-induced stalk map. -/
theorem fieldGaloisStalkMap_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj ≫ (fieldGaloisStalkMap.{u, w} k Ω g).app Q =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up (fieldGaloisOver k Ω g ≫ z)) Q.obj :=
  by
    have hgeneric
        (Φ : (Spec (.of k)).smallEtaleTopology.Point.{max u w}) (f : Φ ⟶ Φ)
        (P : (Spec (.of k)).Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
        (V : (Spec (.of k)).Etale) (y : Φ.fiber.obj V) :
        Φ.toPresheafFiber V y P ≫ f.presheafFiber.app P =
          Φ.toPresheafFiber V (f.hom.app V y) P := by
      exact Φ.toPresheafFiber_presheafFiberDesc
        (fun W x => Φ.toPresheafFiber W (f.hom.app W x) P)
        (by
          intro W Z r x
          refine (Φ.toPresheafFiber_w r (f.hom.app W x) P).trans ?_
          exact congrArg (fun t => Φ.toPresheafFiber Z t P)
            (f.hom.naturality_apply r x).symm)
        V y
    exact hgeneric (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω))
      (fieldGaloisPointEndomorphism.{u, w} k Ω g) Q.obj U (ULift.up z)

/-- Every original representative has its literal LEFT action, with the same section. -/
theorem fieldGeometricStalk_smul_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
    (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)) :
    letI := fieldGeometricStalkSMul.{u, w} k Ω Q
    g • (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up (fieldGaloisOver k Ω g ≫ z)) Q.obj c :=
  ConcreteCategory.congr_hom (fieldGaloisStalkMap_germ.{u, w} k Ω Q g U z) c

omit [IsSepClosure k Ω] in
/-- On an actual affine spectrum, the same geometric embedding is postcomposed by g. -/
theorem fieldGaloisSpec_homEquivAlgHom (g : Gal(Ω/k))
    {A : Type u} [CommRing A] [Algebra k A] (z : Spec (.of Ω) ⟶ Spec (.of A))
    (hz : z ≫ Spec.algebraMap k A = Spec.algebraMap k Ω) :
    Spec.homEquivAlgHom
        ⟨fieldGaloisSpec k Ω g ≫ z, by
          rw [Category.assoc, hz]
          exact (Spec.homEquivAlgHom.symm g.toAlgHom).property⟩ =
      g.toAlgHom.comp (Spec.homEquivAlgHom ⟨z, hz⟩) := by
  apply AlgHom.ext
  intro a
  change (Spec.preimage (fieldGaloisSpec k Ω g ≫ z)).hom a =
    g ((Spec.preimage z).hom a)
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

/-- The SAME g restricted to the SAME original finite Galois subfield. -/
def fieldFiniteGaloisRestriction (g : Gal(Ω/k)) (L : FiniteGaloisIntermediateField k Ω) :
    fieldFiniteGaloisEtale k Ω L ⟶ fieldFiniteGaloisEtale k Ω L := by
  letI : Normal k L := L.isGalois.to_normal
  exact MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (g.restrictNormal L).toRingHom))
    ((Spec.homEquivAlgHom (R := k) (A := L) (B := L)).symm
      (g.restrictNormal L).toAlgHom).property

/-- The original geometric pointing commutes with that same restriction. -/
theorem fieldFiniteGaloisRestriction_point (g : Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    (fieldGeometricPoint k Ω).fiber.map (fieldFiniteGaloisRestriction k Ω g L)
        (fieldFiniteGaloisPoint k Ω L) =
      fieldGaloisOver k Ω g ≫ fieldFiniteGaloisPoint k Ω L := by
  let : Normal k L := L.isGalois.to_normal
  apply Over.OverMorphism.ext
  change Spec.algebraMap L Ω ≫
      Spec.map (CommRingCat.ofHom (g.restrictNormal L).toRingHom) =
    fieldGaloisSpec k Ω g ≫ Spec.algebraMap L Ω
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext x
  exact AlgEquiv.restrictNormal_commutes g L x

/-- Finite-stage action is precisely the original restriction along Spec(g|L). -/
theorem fieldGeometricStalk_smul_finite_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) (L : FiniteGaloisIntermediateField k Ω)
    (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    letI := fieldGeometricStalkSMul.{u, w} k Ω Q
    g • (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj
        (Q.obj.map (fieldFiniteGaloisRestriction k Ω g L).op c) := by
  rw [fieldGeometricStalk_smul_germ]
  rw [← fieldFiniteGaloisRestriction_point]
  exact ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber_w_apply
    (fieldFiniteGaloisRestriction k Ω g L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c).symm

/-- The same canonical colimit comparison has that original finite-stage action. -/
theorem fieldGeometricStalk_smul_finite_colimit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) (L : FiniteGaloisIntermediateField k Ω)
    (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    letI := fieldGeometricStalkSMul.{u, w} k Ω Q
    g • fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) =
      fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L
          (Q.obj.map (fieldFiniteGaloisRestriction k Ω g L).op c)) := by
  rw [fieldFiniteGaloisStalkAddEquiv_ι, fieldFiniteGaloisStalkAddEquiv_ι]
  exact fieldGeometricStalk_smul_finite_germ.{u, w} k Ω Q g L c

/-- Every actual germ has an actual original finite Galois stage in the same closure. -/
theorem fieldGeometricStalk_finite_rep
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    ∃ (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c = m := by
  obtain ⟨U, z, c, hc⟩ :=
    (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).toPresheafFiber_jointly_surjective m
  obtain ⟨L, r, hr⟩ := fieldFiniteGalois_refines_point k Ω U z.down
  have hz : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.map r
      (ULift.up (fieldFiniteGaloisPoint k Ω L)) = z := congrArg ULift.up hr
  refine ⟨L, Q.obj.map r.op c, ?_⟩
  have hw := (smallEtaleGeometricPointCommon.{u, w}
    (Spec.algebraMap k Ω)).toPresheafFiber_w_apply r
      (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c
  exact hw.trans ((congrArg (fun y =>
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      U y Q.obj c) hz).trans hc)

/-- Elements fixing the same finite subfield give its actual identity restriction. -/
theorem fieldFiniteGaloisRestriction_eq_id (g : Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) (hg : g ∈ L.fixingSubgroup) :
    fieldFiniteGaloisRestriction k Ω g L = 𝟙 _ := by
  let : Normal k L := L.isGalois.to_normal
  have h := (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff g L).mp hg
  change g.restrictNormal L = 1 at h
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (g.restrictNormal L).toRingHom) = 𝟙 _
  rw [h]
  have e : CommRingCat.ofHom (1 : Gal(L/k)).toRingHom = 𝟙 (CommRingCat.of L) := by
    ext x; rfl
  exact (congrArg Spec.map e).trans (Spec.map_id _)

/-- Each germ's own actual finite Galois fixing subgroup is contained in its stabilizer. -/
theorem fieldGeometricStalk_finite_fixingSubgroup
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    ∃ L : FiniteGaloisIntermediateField k Ω,
      L.fixingSubgroup ≤ MulAction.stabilizer Gal(Ω/k) m := by
  obtain ⟨L, c, hc⟩ := fieldGeometricStalk_finite_rep.{u, w} k Ω Q m
  refine ⟨L, ?_⟩
  intro g hg
  change g • m = m
  have hi := fieldFiniteGaloisRestriction_eq_id k Ω g L hg
  have hp : Q.obj.map (fieldFiniteGaloisRestriction k Ω g L).op c = c := by
    rw [hi]
    simp
  have hs := fieldGeometricStalk_smul_finite_germ.{u, w} k Ω Q g L c
  have hx := congrArg (fun t : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L)) =>
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj t) hp
  exact (congrArg (fun x : fieldGeometricStalkCarrier.{u, w} k Ω Q => g • x) hc.symm).trans
    (hs.trans (hx.trans hc))

/-- The actual stabilizer of EVERY germ is open in the actual Krull topology. -/
theorem fieldGeometricStalk_stabilizer_isOpen
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    IsOpen (MulAction.stabilizer Gal(Ω/k) m : Set Gal(Ω/k)) := by
  obtain ⟨L, hL⟩ := fieldGeometricStalk_finite_fixingSubgroup.{u, w} k Ω Q m
  exact Subgroup.isOpen_mono hL (IntermediateField.fixingSubgroup_isOpen L.toIntermediateField)

/-- Joint continuity is proved from those actual elementwise open stabilizers. -/
instance fieldGeometricStalkContinuousSMul
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    ContinuousSMul Gal(Ω/k) (fieldGeometricStalkCarrier.{u, w} k Ω Q) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (fieldGeometricStalk_stabilizer_isOpen.{u, w} k Ω Q)

/-- The complete discrete continuous abelian action on the SAME original stalk. -/
def fieldGeometricStalkGaloisObject
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) :=
  DiscreteAbelianAction.of Gal(Ω/k) (fieldGeometricStalkCarrier.{u, w} k Ω Q)

/-- EVERY original sheaf map is equivariant for the same original stalk action. -/
theorem fieldGeometricStalk_map_equivariant
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q')
    (g : Gal(Ω/k)) (x : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ (g • x) =
      g • (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ x :=
  (ConcreteCategory.congr_hom ((fieldGaloisStalkMap.{u, w} k Ω g).naturality τ) x).symm

/-- Package exactly the original induced stalk map, including its original integer-linearity. -/
def fieldGeometricStalkGaloisMap
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    fieldGeometricStalkGaloisObject.{u, w} k Ω Q ⟶
      fieldGeometricStalkGaloisObject.{u, w} k Ω Q' :=
  DiscreteAbelianAction.ofAddHom
    ⟨((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ).hom,
      fieldGeometricStalk_map_equivariant.{u, w} k Ω τ⟩

/-- The ONE functor retains all original common sheaves and all original stalk maps. -/
def fieldGeometricStalkGaloisFunctor :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      DiscreteAbelianAction.{u, max u w} Gal(Ω/k) where
  obj := fieldGeometricStalkGaloisObject.{u, w} k Ω
  map := fieldGeometricStalkGaloisMap.{u, w} k Ω
  map_id Q := by
    apply (DiscreteAbelianAction.forget Gal(Ω/k)).map_injective
    change (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map (𝟙 Q) = 𝟙 _
    exact (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map_id Q
  map_comp τ σ := by
    apply (DiscreteAbelianAction.forget Gal(Ω/k)).map_injective
    change (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map (τ ≫ σ) =
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ ≫
        (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map σ
    exact (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map_comp τ σ

/-- Forgetting returns exactly the SAME original stalk functor and maps. -/
theorem fieldGeometricStalkGaloisFunctor_forget :
    fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ DiscreteAbelianAction.forget Gal(Ω/k) =
      smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω) := rfl

/-- Every original coefficient representative is included through exactly ONE lift. -/
theorem fieldGeometricStalk_original_smul_germ
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) (c : F.obj.obj (op U)) :
    letI := fieldGeometricStalkSMul.{u, w} k Ω
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F)
    g • (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up (fieldGaloisOver k Ω g ≫ z))
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) :=
  fieldGeometricStalk_smul_germ.{u, w} k Ω
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F) g U z (ULift.up c)

/-- Every original coefficient map is its SAME induced stalk map after ONE lift. -/
theorem fieldGeometricStalk_original_map
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    (DiscreteAbelianAction.forget Gal(Ω/k)).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)) =
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) := rfl

/-- Joint continuity on the SAME underlying stalk with the genuine Krull topology. -/
theorem fieldGeometricStalk_continuous_action
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    Continuous (fun x : Gal(Ω/k) × fieldGeometricStalkCarrier.{u, w} k Ω Q => x.1 • x.2) :=
  continuous_smul

/-- The constructed module object has the SAME actual original stalk carrier. -/
theorem fieldGeometricStalkGaloisObject_carrier
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (DiscreteAbelianAction.underlying (fieldGeometricStalkGaloisObject.{u, w} k Ω Q) :
      Type (max u w)) = fieldGeometricStalkCarrier.{u, w} k Ω Q := rfl

/-- Its original action endomorphism is the SAME point-induced stalk map. -/
theorem fieldGeometricStalkGaloisObject_action
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) (x : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    ((fieldGeometricStalkGaloisObject.{u, w} k Ω Q).obj.obj.ρ g).asHom.hom x =
      (fieldGaloisStalkMap.{u, w} k Ω g).app Q x := rfl

/-- Every actual sheaf component has its original induced action on original germs. -/
theorem fieldGeometricStalk_map_germ
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q')
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)) :
    (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) Q.obj c) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q'.obj (τ.hom.app (op U) c) :=
  (smallEtaleGeometricPointCommon.{u, w}
    (Spec.algebraMap k Ω)).toPresheafFiber_naturality_apply τ.hom U (ULift.up z) c

/-- The finite-stage restriction has the literal original Spec(g|L) map. -/
theorem fieldFiniteGaloisRestriction_left (g : Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    letI : Normal k L := L.isGalois.to_normal
    (fieldFiniteGaloisRestriction k Ω g L).left =
      Spec.map (CommRingCat.ofHom (g.restrictNormal L).toRingHom) := rfl

/-- Every original coefficient component is retained through its ONE canonical lift. -/
theorem fieldGeometricStalk_original_map_germ
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F')
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)) :
    (DiscreteAbelianAction.forget Gal(Ω/k)).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f))
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c)) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F').obj
        (ULift.up (f.hom.app (op U) c)) :=
  fieldGeometricStalk_map_germ.{u, w} k Ω
    ((liftCoefficients.{u, w} (Spec (.of k))).map f) U z (ULift.up c)

/-- All original spectrum, affine-embedding and point-map multiplication conventions. -/
def FieldGaloisPointActionLaws : Prop :=
  fieldGaloisSpec k Ω (1 : Gal(Ω/k)) = 𝟙 _ ∧
  (∀ g h : Gal(Ω/k), fieldGaloisSpec k Ω (g * h) =
    fieldGaloisSpec k Ω g ≫ fieldGaloisSpec k Ω h) ∧
  fieldGaloisPointEndomorphism.{u, w} k Ω (1 : Gal(Ω/k)) = 𝟙 _ ∧
  (∀ g h : Gal(Ω/k), fieldGaloisPointEndomorphism.{u, w} k Ω (g * h) =
    fieldGaloisPointEndomorphism.{u, w} k Ω g ≫ fieldGaloisPointEndomorphism.{u, w} k Ω h) ∧
  fieldGaloisStalkMap.{u, w} k Ω (1 : Gal(Ω/k)) = 𝟙 _ ∧
  (∀ g h : Gal(Ω/k), fieldGaloisStalkMap.{u, w} k Ω (g * h) =
    fieldGaloisStalkMap.{u, w} k Ω h ≫ fieldGaloisStalkMap.{u, w} k Ω g) ∧
  (∀ (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (z : (fieldGeometricPoint k Ω).fiber.obj U),
    ((fieldGaloisCommonFiberMap.{u, w} k Ω g).app U (ULift.up z)).down.left =
      fieldGaloisSpec k Ω g ≫ z.left) ∧
  ∀ (g : Gal(Ω/k)) (A : Type u) [CommRing A] [Algebra k A]
      (z : Spec (.of Ω) ⟶ Spec (.of A))
      (hz : z ≫ Spec.algebraMap k A = Spec.algebraMap k Ω),
    Spec.homEquivAlgHom
        ⟨fieldGaloisSpec k Ω g ≫ z, by
          rw [Category.assoc, hz]
          exact (Spec.homEquivAlgHom.symm g.toAlgHom).property⟩ =
      g.toAlgHom.comp (Spec.homEquivAlgHom ⟨z, hz⟩)

/-- The SAME actual functor, LEFT action, finite stages, stabilizers and all sheaf maps. -/
def FieldGeometricStalkGaloisLaws : Prop :=
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let S := smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)
  T ⋙ DiscreteAbelianAction.forget Gal(Ω/k) = S ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    (DiscreteAbelianAction.underlying (T.obj Q) : Type (max u w)) =
      fieldGeometricStalkCarrier.{u, w} k Ω Q) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (g : Gal(Ω/k)) (x : fieldGeometricStalkCarrier.{u, w} k Ω Q),
    ((T.obj Q).obj.obj.ρ g).asHom.hom x = (fieldGaloisStalkMap.{u, w} k Ω g).app Q x) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (x : fieldGeometricStalkCarrier.{u, w} k Ω Q), (1 : Gal(Ω/k)) • x = x) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (g h : Gal(Ω/k)) (x : fieldGeometricStalkCarrier.{u, w} k Ω Q),
    (g * h) • x = g • (h • x)) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (g : Gal(Ω/k)), g • (0 : fieldGeometricStalkCarrier.{u, w} k Ω Q) = 0) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (g : Gal(Ω/k)) (x y : fieldGeometricStalkCarrier.{u, w} k Ω Q),
    g • (x + y) = g • x + g • y) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (z : (fieldGeometricPoint k Ω).fiber.obj U) (c : Q.obj.obj (op U)),
    letI := fieldGeometricStalkSMul.{u, w} k Ω Q
    g • (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up (fieldGaloisOver k Ω g ≫ z)) Q.obj c) ∧
  (∀ (g : Gal(Ω/k)) (L : FiniteGaloisIntermediateField k Ω),
    letI : Normal k L := L.isGalois.to_normal
    (fieldFiniteGaloisRestriction k Ω g L).left =
      Spec.map (CommRingCat.ofHom (g.restrictNormal L).toRingHom)) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (g : Gal(Ω/k)) (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    letI := fieldGeometricStalkSMul.{u, w} k Ω Q
    g • (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj
        (Q.obj.map (fieldFiniteGaloisRestriction k Ω g L).op c)) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (g : Gal(Ω/k)) (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    letI := fieldGeometricStalkSMul.{u, w} k Ω Q
    g • fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) =
      fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L
          (Q.obj.map (fieldFiniteGaloisRestriction k Ω g L).op c))) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (m : fieldGeometricStalkCarrier.{u, w} k Ω Q),
    ∃ (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c = m) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (m : fieldGeometricStalkCarrier.{u, w} k Ω Q),
    ∃ L : FiniteGaloisIntermediateField k Ω,
      L.fixingSubgroup ≤ MulAction.stabilizer Gal(Ω/k) m) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (m : fieldGeometricStalkCarrier.{u, w} k Ω Q),
    IsOpen (MulAction.stabilizer Gal(Ω/k) m : Set Gal(Ω/k))) ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    Continuous (fun x : Gal(Ω/k) × fieldGeometricStalkCarrier.{u, w} k Ω Q => x.1 • x.2)) ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    DiscreteTopology (fieldGeometricStalkCarrier.{u, w} k Ω Q)) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (g : Gal(Ω/k)) (x : fieldGeometricStalkCarrier.{u, w} k Ω Q),
    S.map τ (g • x) = g • S.map τ x) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (U : (Spec (.of k)).Etale)
      (z : (fieldGeometricPoint k Ω).fiber.obj U) (c : Q.obj.obj (op U)),
    S.map τ ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q'.obj (τ.hom.app (op U) c)) ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    T.map (𝟙 Q) = 𝟙 (T.obj Q)) ∧
  ∀ (Q Q' Q'' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (σ : Q' ⟶ Q''), T.map (τ ≫ σ) = T.map τ ≫ T.map σ

/-- Every original coefficient sheaf and map uses exactly ONE lift into the SAME functor. -/
def FieldGeometricStalkOriginalCoefficientLaws : Prop :=
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let S := smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)
  let Lc := liftCoefficients.{u, w} (Spec (.of k))
  (∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
      (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (z : (fieldGeometricPoint k Ω).fiber.obj U) (c : F.obj.obj (op U)),
    letI := fieldGeometricStalkSMul.{u, w} k Ω (Lc.obj F)
    g • (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) (Lc.obj F).obj (ULift.up c) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up (fieldGaloisOver k Ω g ≫ z)) (Lc.obj F).obj (ULift.up c)) ∧
  (∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F'),
    (DiscreteAbelianAction.forget Gal(Ω/k)).map (T.map (Lc.map f)) = S.map (Lc.map f)) ∧
  (∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F')
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (c : F.obj.obj (op U)),
    (DiscreteAbelianAction.forget Gal(Ω/k)).map (T.map (Lc.map f))
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) (Lc.obj F).obj (ULift.up c)) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) (Lc.obj F').obj (ULift.up (f.hom.app (op U) c))) ∧
  ∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F')
      (g : Gal(Ω/k)) (m : fieldGeometricStalkCarrier.{u, w} k Ω (Lc.obj F)),
    S.map (Lc.map f) (g • m) = g • S.map (Lc.map f) m

/-- The full original LEFT Galois action, actual joint continuity and the ONE module functor. -/
theorem original_field_geometric_stalk_galois_action :
    FieldGaloisPointActionLaws.{u, w} k Ω ∧
      FieldGeometricStalkGaloisLaws.{u, w} k Ω ∧
        FieldGeometricStalkOriginalCoefficientLaws.{u, w} k Ω := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fieldGaloisSpec_one k Ω, fieldGaloisSpec_mul k Ω,
      fieldGaloisPointEndomorphism_one.{u, w} k Ω,
      fieldGaloisPointEndomorphism_mul.{u, w} k Ω,
      fieldGaloisStalkMap_one.{u, w} k Ω, fieldGaloisStalkMap_mul.{u, w} k Ω,
      fieldGaloisCommonFiberMap_left.{u, w} k Ω, ?_⟩
    intro g A _ _ z hz
    exact fieldGaloisSpec_homEquivAlgHom k Ω g z hz
  · refine ⟨fieldGeometricStalkGaloisFunctor_forget.{u, w} k Ω,
      fieldGeometricStalkGaloisObject_carrier.{u, w} k Ω,
      fieldGeometricStalkGaloisObject_action.{u, w} k Ω,
      (fun _ x => one_smul Gal(Ω/k) x),
      (fun _ g h x => mul_smul g h x),
      (fun _ g => smul_zero g),
      (fun _ g x y => smul_add g x y),
      fieldGeometricStalk_smul_germ.{u, w} k Ω,
      fieldFiniteGaloisRestriction_left k Ω,
      fieldGeometricStalk_smul_finite_germ.{u, w} k Ω,
      fieldGeometricStalk_smul_finite_colimit.{u, w} k Ω,
      fieldGeometricStalk_finite_rep.{u, w} k Ω,
      fieldGeometricStalk_finite_fixingSubgroup.{u, w} k Ω,
      fieldGeometricStalk_stabilizer_isOpen.{u, w} k Ω,
      fieldGeometricStalk_continuous_action.{u, w} k Ω,
      (fun _ => inferInstance),
      (fun _ _ τ g x => fieldGeometricStalk_map_equivariant.{u, w} k Ω τ g x),
      (fun _ _ τ U z c => fieldGeometricStalk_map_germ.{u, w} k Ω τ U z c),
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map_id,
      (fun _ _ _ τ σ => (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map_comp τ σ)⟩
  · exact ⟨fieldGeometricStalk_original_smul_germ.{u, w} k Ω,
      (fun _ _ f => fieldGeometricStalk_original_map.{u, w} k Ω f),
      (fun _ _ f U z c => fieldGeometricStalk_original_map_germ.{u, w} k Ω f U z c),
      (fun _ _ f g x => fieldGeometricStalk_map_equivariant.{u, w} k Ω _ g x)⟩

end AlgebraicGeometry.Scheme.DerivedSections
