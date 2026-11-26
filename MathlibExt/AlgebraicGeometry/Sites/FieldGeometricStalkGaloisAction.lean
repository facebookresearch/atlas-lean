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

/-!
# The continuous left Galois action on a geometric field stalk

Let k have prescribed separable closure Ω, G=Gal(Ω/k) with its Krull topology, and Q a
small-étale additive-group sheaf of height max(u,w). Precomposition of geometric lifts by
Spec(g) induces an additive stalk action. Its germ formula is g·[U,z,c]=[U,Spec(g)≫z,c]; on
affine coordinates it postcomposes the algebra embedding by g.

Every stalk vector has a representative at a finite Galois subfield L⊆Ω. The subgroup fixing L
lies in that vector's stabilizer and is open, so the action on the discrete stalk is jointly
continuous. These actions and equivariant sheaf-induced maps define the Galois stalk functor,
whose forgetful composite is the geometric stalk. Smaller coefficient sheaves use one ULift^u.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- Let k,Ω be fields with a k-algebra structure and g∈Gal(Ω/k). Define fieldGaloisSpec(g) as the
spectrum map of g's underlying ring automorphism, an endomorphism of Spec(Ω). -/
abbrev fieldGaloisSpec (g : Gal(Ω/k)) : Spec (.of Ω) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom g.toRingHom)

/-- For a k-field Ω and g∈Gal(Ω/k), the map Spec(g) : Spec(Ω) → Spec(Ω) commutes with the
structure map to Spec(k). It therefore defines an endomorphism of Spec(Ω) → Spec(k) in the
overcategory of schemes. -/
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

/-- Let Ω be a prescribed separable closure of k and g∈Gal(Ω/k). The natural endomorphism of the
geometric fiber functor at Spec(Ω) sends a lift z : Spec(Ω) → U over k to Spec(g)≫z. It is
defined by precomposition in the scheme overcategory. -/
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

/-- For k,Ω with IsSepClosure k Ω, the map fieldGaloisCommonFiberMap(g) is the fiber endomorphism
z↦Spec(g)≫z whiskered by ULift^w. It acts on the common point fibers of height max(u,w). -/
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

/-- Let Ω be a prescribed separable closure of k, U an étale object, and z a geometric lift to U.
Applying the common Galois fiber map to up(z), then taking down and its scheme coordinate,
gives Spec(g)≫z.left. -/
theorem fieldGaloisCommonFiberMap_left (g : Gal(Ω/k)) (U : (Spec (.of k)).Etale)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    ((fieldGaloisCommonFiberMap.{u, w} k Ω g).app U (ULift.up z)).down.left =
      fieldGaloisSpec k Ω g ≫ z.left := rfl

/-- For a field k, prescribed separable closure Ω, and g∈Gal(Ω/k), the lifted fiber transformation
z↦Spec(g)≫z defines an endomorphism of the common geometric point on the small étale site. Its
underlying fiber map is fieldGaloisCommonFiberMap(g). -/
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

/-- For a field k, prescribed separable closure Ω, and g∈Gal(Ω/k), the common geometric point
endomorphism induces a natural endomorphism of the common additive-group stalk functor. This
is fieldGaloisStalkMap(g), acting on every coefficient sheaf. -/
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

/-- Let Ω be a prescribed separable closure of k and Q a small-étale additive-group sheaf of
height max(u,w). Define fieldGeometricStalkCarrier(Q) to be the underlying group of its common
geometric stalk, a type of that same height. No additional coefficient lift is applied to Q. -/
abbrev fieldGeometricStalkCarrier
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) : Type (max u w) :=
  (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q

instance fieldGeometricStalkTopology
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    TopologicalSpace (fieldGeometricStalkCarrier.{u, w} k Ω Q) := ⊥

instance fieldGeometricStalkDiscreteTopology
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    DiscreteTopology (fieldGeometricStalkCarrier.{u, w} k Ω Q) := discreteTopology_bot _

/-- For a field k, prescribed separable closure Ω, and coefficient sheaf Q, define
g·m=fieldGaloisStalkMap(g)_Q(m). This is a DistribMulAction on the stalk: 1 acts identically,
(gh)·m=g·(h·m), and every g preserves zero and addition. -/
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

/-- Let Ω be a prescribed separable closure of k and Q a common-height additive-group sheaf. The
scalar action on its presheaf-fiber stalk presentation is the SMul component of
fieldGeometricStalkDistribMulAction(Q). It uses the same point-induced stalk endomorphisms. -/
abbrev fieldGeometricStalkSMul
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    SMul Gal(Ω/k) ((smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).presheafFiber.obj Q.obj : AddCommGrpCat.{max u w}) :=
  (fieldGeometricStalkDistribMulAction.{u, w} k Ω Q).toMulAction.toSemigroupAction.toSMul

/-- For a field k, prescribed separable closure Ω, sheaf Q, g∈Gal(Ω/k), and a lift z to an étale
U, the germ map γ_{U,z} followed by the stalk endomorphism α_g equals γ_{U,Spec(g)≫z}. The
section group Q(U) is unchanged. -/
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

/-- Let Ω be a prescribed separable closure of k, Q a small-étale additive-group sheaf, z :
Spec(Ω) → U a geometric lift, and c∈Q(U). Then g·[U,z,c]=[U,Spec(g)≫z,c] in the common stalk.
The point-fiber representatives use the single ULift^w. -/
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
/-- Let k,Ω be fields with a k-algebra structure, g∈Gal(Ω/k), and A a commutative k-algebra. For z
: Spec(Ω) → Spec(A) over k, the algebra coordinate of Spec(g)≫z is g∘h_z : A → Ω. This
identity does not require Ω to be a separable closure or A to be étale. -/
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

/-- For a field k, prescribed separable closure Ω, g∈Gal(Ω/k), and finite Galois intermediate
field L, restrict g to L. Its spectrum map gives an étale endomorphism r_{g,L} : Spec(L) →
Spec(L) over k. -/
def fieldFiniteGaloisRestriction (g : Gal(Ω/k)) (L : FiniteGaloisIntermediateField k Ω) :
    fieldFiniteGaloisEtale k Ω L ⟶ fieldFiniteGaloisEtale k Ω L := by
  letI : Normal k L := L.isGalois.to_normal
  exact MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (g.restrictNormal L).toRingHom))
    ((Spec.homEquivAlgHom (R := k) (A := L) (B := L)).symm
      (g.restrictNormal L).toAlgHom).property

/-- Let Ω be a prescribed separable closure of k and L a finite Galois subfield. The fiber map of
r_{g,L}=Spec(g|L) sends the inclusion point z_L : Spec(Ω) → Spec(L) to Spec(g)≫z_L. This is
the compatibility of the field restriction with the geometric pointing. -/
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

/-- For a prescribed separable closure Ω, a sheaf Q, finite Galois L⊆Ω, and c∈Q(Spec L), the stalk
action satisfies g·[L,c]=[L,Q(r_{g,L}.op)(c)]. The germ is at the inclusion Spec(Ω) → Spec(L),
and r_{g,L}=Spec(g|L). -/
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

/-- Let k have prescribed separable closure Ω, Q be a common-height sheaf, and e the additive
finite-Galois colimit-to-stalk equivalence. For c∈Q(Spec L),
g·e(ι_L(c))=e(ι_L(Q(Spec(g|L).op)(c))). This states the action on the specified colimit
representative through e. -/
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

/-- For a field k, prescribed separable closure Ω, and common-height additive-group sheaf Q, every
m∈Q_{arη} is the germ of some c∈Q(Spec L) for a finite Galois intermediate field L⊆Ω. The
germ uses the inclusion point of that same L. -/
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

/-- Let Ω be a prescribed separable closure of k, L a finite Galois subfield, and g∈Gal(Ω/k)
belong to L.fixingSubgroup. Then the étale endomorphism r_{g,L}=Spec(g|L) is the identity of
Spec(L) over k. -/
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

/-- For a field k, prescribed separable closure Ω, sheaf Q, and stalk vector m, there exists a
finite Galois subfield L⊆Ω with L.fixingSubgroup ≤ Stab_G(m). A representative of m at L is
fixed by every automorphism fixing L. -/
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

/-- Let k have prescribed separable closure Ω and G=Gal(Ω/k) carry its Krull topology. For any
common-height additive-group sheaf Q and m∈Q_{arη}, the subgroup Stab_G(m) is open. It
contains the open fixing subgroup of a finite Galois representative. -/
theorem fieldGeometricStalk_stabilizer_isOpen
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (m : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    IsOpen (MulAction.stabilizer Gal(Ω/k) m : Set Gal(Ω/k)) := by
  obtain ⟨L, hL⟩ := fieldGeometricStalk_finite_fixingSubgroup.{u, w} k Ω Q m
  exact Subgroup.isOpen_mono hL (IntermediateField.fixingSubgroup_isOpen L.toIntermediateField)

/-- For a field k, prescribed separable closure Ω, and additive-group sheaf Q, equip the geometric
stalk with the discrete topology and G=Gal(Ω/k) with the Krull topology. The left stalk action
has ContinuousSMul, since every vector's stabilizer is open. -/
instance fieldGeometricStalkContinuousSMul
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    ContinuousSMul Gal(Ω/k) (fieldGeometricStalkCarrier.{u, w} k Ω Q) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (fieldGeometricStalk_stabilizer_isOpen.{u, w} k Ω Q)

/-- Let Ω be a prescribed separable closure of k and Q a small-étale additive-group sheaf of
height max(u,w). Its common stalk, with the additive left Galois action and discrete topology,
defines an object of DiscreteAbelianAction.{u,max(u,w)} Gal(Ω/k). -/
def fieldGeometricStalkGaloisObject
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) :=
  DiscreteAbelianAction.of Gal(Ω/k) (fieldGeometricStalkCarrier.{u, w} k Ω Q)

/-- For a field k, prescribed separable closure Ω, and sheaf morphism τ : Q → Q′, the geometric
stalk map satisfies S(τ)(g·m)=g·S(τ)(m) for every g∈Gal(Ω/k) and m∈Q_{arη}. Thus it preserves
the point-induced left actions. -/
theorem fieldGeometricStalk_map_equivariant
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q')
    (g : Gal(Ω/k)) (x : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ (g • x) =
      g • (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ x :=
  (ConcreteCategory.congr_hom ((fieldGaloisStalkMap.{u, w} k Ω g).naturality τ) x).symm

/-- For a field k, prescribed separable closure Ω, and sheaf morphism τ : Q → Q′, the additive
geometric stalk map is Galois-equivariant and defines fieldGeometricStalkGaloisMap(τ). Its
underlying additive map is exactly S(τ). -/
def fieldGeometricStalkGaloisMap
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    fieldGeometricStalkGaloisObject.{u, w} k Ω Q ⟶
      fieldGeometricStalkGaloisObject.{u, w} k Ω Q' :=
  DiscreteAbelianAction.ofAddHom
    ⟨((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ).hom,
      fieldGeometricStalk_map_equivariant.{u, w} k Ω τ⟩

/-- Let Ω be a prescribed separable closure of k. Assign to each common-height additive-group
sheaf Q its geometric stalk with the point-induced left Galois action, and to τ the same
equivariant additive stalk map. This defines a functor to DiscreteAbelianAction Gal(Ω/k),
preserving identities and composition. -/
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

/-- For a field k and prescribed separable closure Ω, the Galois stalk functor followed by
DiscreteAbelianAction.forget equals the common additive-group geometric stalk functor. The
equality retains both the underlying stalk objects and all sheaf-induced maps. -/
theorem fieldGeometricStalkGaloisFunctor_forget :
    fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ DiscreteAbelianAction.forget Gal(Ω/k) =
      smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω) := rfl

/-- Let F be a small-étale sheaf of coefficient size w, L the ULift^u coefficient functor, and Ω a
prescribed separable closure of k. For c∈F(U) and a geometric lift z, g·[U,up(z),up(c)] in the
stalk of LF equals [U,up(Spec(g)≫z),up(c)]. The coefficient is not lifted again. -/
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

/-- For a field k, prescribed separable closure Ω, and τ : F → F′ with coefficient universe w, the
forgetful image of Φ(Lτ) equals S(Lτ). Here L is the single ULift^u coefficient functor, Φ the
Galois stalk, and S its underlying geometric stalk. -/
theorem fieldGeometricStalk_original_map
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    (DiscreteAbelianAction.forget Gal(Ω/k)).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)) =
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) := rfl

/-- Let Ω be a prescribed separable closure of k, G=Gal(Ω/k) with the Krull topology, and Q a
common-height additive-group sheaf. The map G×Q_{arη} → Q_{arη}, (g,m)↦g·m, is continuous
when the stalk has its discrete topology. -/
theorem fieldGeometricStalk_continuous_action
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    Continuous (fun x : Gal(Ω/k) × fieldGeometricStalkCarrier.{u, w} k Ω Q => x.1 • x.2) :=
  continuous_smul

/-- For a field k, prescribed separable closure Ω, and common-height additive-group sheaf Q, the
underlying type of fieldGeometricStalkGaloisObject(Q) equals fieldGeometricStalkCarrier(Q).
The representation adds the Galois action and continuity without changing the stalk carrier. -/
theorem fieldGeometricStalkGaloisObject_carrier
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (DiscreteAbelianAction.underlying (fieldGeometricStalkGaloisObject.{u, w} k Ω Q) :
      Type (max u w)) = fieldGeometricStalkCarrier.{u, w} k Ω Q := rfl

/-- Let Ω be a prescribed separable closure of k, Q a common-height sheaf, g∈Gal(Ω/k), and m a
stalk vector. The action morphism ρ(g) of fieldGeometricStalkGaloisObject(Q) sends m to
fieldGaloisStalkMap(g)_Q(m). -/
theorem fieldGeometricStalkGaloisObject_action
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) (x : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    ((fieldGeometricStalkGaloisObject.{u, w} k Ω Q).obj.obj.ρ g).asHom.hom x =
      (fieldGaloisStalkMap.{u, w} k Ω g).app Q x := rfl

/-- For a field k, prescribed separable closure Ω, and sheaf map τ : Q → Q′, the induced stalk map
sends [U,z,c] to [U,z,τ_U(c)]. The geometric neighborhood and pointing are unchanged. -/
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

/-- Let Ω be a prescribed separable closure of k, L a finite Galois subfield, and g∈Gal(Ω/k). The
underlying scheme map of fieldFiniteGaloisRestriction(g,L) is Spec(g.restrictNormal L), using
the normality supplied by L's finite Galois property. -/
theorem fieldFiniteGaloisRestriction_left (g : Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    letI : Normal k L := L.isGalois.to_normal
    (fieldFiniteGaloisRestriction k Ω g L).left =
      Spec.map (CommRingCat.ofHom (g.restrictNormal L).toRingHom) := rfl

/-- For a field k, prescribed separable closure Ω, τ : F → F′ with coefficient universe w, and
c∈F(U), the underlying Galois-stalk map of Lτ sends [U,up(z),up(c)] to [U,up(z),up(τ_U(c))].
The functor L uses one ULift^u coefficient lift. -/
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

/-- Let Ω be a prescribed separable closure of k. This proposition asserts that the spectrum maps
σ_g and common point endomorphisms p_g have identity at 1 and satisfy σ_{gh}=σ_g≫σ_h and
p_{gh}=p_g≫p_h, while the induced stalk maps satisfy α_{gh}=α_h≫α_g. It also asserts that the
common fiber map of up(z) has scheme coordinate σ_g≫z and that on any affine k-algebra A its
algebra coordinate is g∘h_z. -/
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

/-- For a field k and prescribed separable closure Ω, this proposition asserts that the Galois
stalk functor has the geometric stalk as its exact carrier and forgetful composite; its action
is the point-induced stalk map with the left group and additive laws; general germs transform
by Spec(g), and finite-stage germs and their colimit representatives transform by the
restriction Spec(g|L); every vector has a finite Galois representative and an open stabilizer
containing a finite fixing subgroup; the topology is discrete and the action jointly
continuous; all sheaf maps are equivariant and send [U,z,c] to [U,z,τ_U(c)]; and the functor
preserves identities and composition. -/
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

/-- Let Ω be a prescribed separable closure of k, Φ the Galois stalk, S its underlying geometric
stalk, and Lc the ULift^u coefficient functor from sheaves of size w. This proposition asserts
the action formula g·[U,up(z),up(c)]=[U,up(Spec(g)≫z),up(c)], equality
forget(Φ(Lc(f)))=S(Lc(f)), the germ map [c]↦[f_U(c)] with one lift, and equivariance
S(Lc(f))(g·m)=g·S(Lc(f))(m). -/
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

/-- Let k be a field and Ω its prescribed separable closure. Common-height additive-group
geometric stalks carry a natural left Gal(Ω/k)-action with the Krull/discrete continuity,
finite Galois representative and stabilizer formulas, and equivariant sheaf maps. The
spectrum/point/stalk composition conventions and the single-lift formulas for smaller
coefficients satisfy FieldGaloisPointActionLaws, FieldGeometricStalkGaloisLaws, and
FieldGeometricStalkOriginalCoefficientLaws together. -/
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
