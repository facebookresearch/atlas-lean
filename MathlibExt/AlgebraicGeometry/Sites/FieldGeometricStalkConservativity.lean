/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Formalization developed with automated proof assistants; original Git history retained.
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricStalkGaloisAction
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Cover detection and conservativity of the prescribed geometric field point

Let k be a field and Ω a prescribed separable closure. A sieve on an étale U over k covers
exactly when every Ω-valued geometric lift to U lifts through one of its arrows. Thus the
singleton prescribed-point family is conservative.

Lifting the point fibers by ULift^w preserves this criterion. The common-height additive-group
stalk and the Galois stalk functor reflect isomorphisms. For coefficient sheaves of smaller
size w, the single ULift^u coefficient functor also reflects isomorphisms, so an isomorphism
is detected by either lifted stalk.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

omit [IsSepClosure k Ω] in
/-- Let k,Ω be fields of universe u with a k-algebra structure on Ω. The map Spec(Ω) → Spec(k) is
surjective on the underlying point sets. This conclusion does not require Ω to be a separable
closure. -/
theorem fieldPrescribedGeometricMorphism_surjective :
    Function.Surjective (Spec.algebraMap k Ω) := by
  intro x
  exact ⟨default, Subsingleton.elim _ _⟩

/-- For a field k and prescribed separable closure Ω, define the family of points of the small
étale topology to be the singleton indexed by Unit whose point is Spec(Ω) → Spec(k). Its fiber
universe is u. -/
def fieldPrescribedGeometricPointFamily :
    ObjectProperty (Spec (.of k)).smallEtaleTopology.Point.{u} :=
  ObjectProperty.ofObj (fun _ : Unit => fieldGeometricPoint k Ω)

/-- Let Ω be a prescribed separable closure of a field k. The singleton family consisting of its
geometric point on the small étale site of Spec(k) is conservative. Covers are detected by
lifting geometric fiber points through their sieve arrows. -/
theorem fieldPrescribedGeometricPointFamily_conservative :
    (fieldPrescribedGeometricPointFamily k Ω).IsConservativeFamilyOfPoints := by
  apply Scheme.isConservative_pointSmallEtale (Ω := fun _ : Unit => Ω)
    (fun _ => Spec.algebraMap k Ω)
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨(), (fieldPrescribedGeometricMorphism_surjective k Ω x)⟩

/-- For a field k, prescribed separable closure Ω, étale object U, and sieve R on U, R covers if
and only if every lift z : Spec(Ω) → U over k is of the form y≫g for an étale arrow g : V → U
in R and a lift y : Spec(Ω) → V over k. -/
theorem fieldPrescribedGeometricPoint_cover_iff
    {U : (Spec (.of k)).Etale} (R : Sieve U) :
    R ∈ (Spec (.of k)).smallEtaleTopology U ↔
      ∀ z : (fieldGeometricPoint k Ω).fiber.obj U,
        ∃ (V : (Spec (.of k)).Etale) (g : V ⟶ U) (_ : R g)
          (y : (fieldGeometricPoint k Ω).fiber.obj V),
          (fieldGeometricPoint k Ω).fiber.map g y = z := by
  constructor
  · intro hR z
    exact (fieldGeometricPoint k Ω).jointly_surjective R hR z
  · intro hR
    let : ObjectProperty.Small.{u} (fieldPrescribedGeometricPointFamily k Ω) := by
      dsimp only [fieldPrescribedGeometricPointFamily]
      infer_instance
    obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
    apply (ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small
      (fieldPrescribedGeometricPointFamily_conservative k Ω) g).mpr
    rintro ⟨Φ, hΦ⟩ z
    obtain ⟨i, hi⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
    subst Φ
    obtain ⟨T, q, hq, y, hy⟩ := hR z
    obtain ⟨_, p, _, ⟨j⟩, rfl⟩ := hq
    refine ⟨j, (fieldGeometricPoint k Ω).fiber.map p y, ?_⟩
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hy

/-- Let Ω be a prescribed separable closure of k and U an étale object over k. The common point
fiber at U equals ULift^w of the prescribed geometric fiber of U. This raises the fiber size
from u to max(u,w) without changing U. -/
theorem fieldPrescribedCommonPoint_fiber_obj (U : (Spec (.of k)).Etale) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U =
      ULift.{w} ((fieldGeometricPoint k Ω).fiber.obj U) := rfl

/-- For a field k, prescribed separable closure Ω, an étale arrow g : V → U, and y in the
prescribed fiber of V, the common fiber map sends up(y) to up(p_Ω(g)(y)). The point lift is
ULift^w and the site arrow remains g. -/
theorem fieldPrescribedCommonPoint_fiber_map
    {U V : (Spec (.of k)).Etale} (g : V ⟶ U)
    (z : (fieldGeometricPoint k Ω).fiber.obj V) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.map g
        (ULift.up z) = ULift.up ((fieldGeometricPoint k Ω).fiber.map g z) := rfl

/-- For a field k, prescribed separable closure Ω, étale U, and sieve R on U, R covers exactly
when every common-height fiber element over U lifts through some g : V → U in R from a common
fiber element over V. The fiber lift is ULift^w, and the sieve and arrows are unchanged. -/
theorem fieldPrescribedCommonPoint_cover_iff
    {U : (Spec (.of k)).Etale} (R : Sieve U) :
    R ∈ (Spec (.of k)).smallEtaleTopology U ↔
      ∀ z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U,
        ∃ (V : (Spec (.of k)).Etale) (g : V ⟶ U) (_ : R g)
          (y : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj V),
          (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.map g y = z := by
  constructor
  · intro hR z
    exact (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).jointly_surjective
      R hR z
  · intro hR
    apply (fieldPrescribedGeometricPoint_cover_iff k Ω R).mpr
    intro z
    obtain ⟨V, g, hg, y, hy⟩ := hR (ULift.up z)
    exact ⟨V, g, hg, y.down, congrArg ULift.down hy⟩

/-- Let Ω be a prescribed separable closure of k. Define the common-height point family as the
singleton indexed by Unit with point smallEtaleGeometricPointCommon(Spec(Ω)→Spec(k)). Its
fiber universe is max(u,w). -/
def fieldPrescribedCommonPointFamily :
    ObjectProperty (Spec (.of k)).smallEtaleTopology.Point.{max u w} :=
  ObjectProperty.ofObj
    (fun _ : Unit => smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω))

/-- For a field k and prescribed separable closure Ω, the singleton common-height geometric-point
family is conservative on the full small étale topology. The criterion is the lift of the same
sieve-arrow covering condition. -/
theorem fieldPrescribedCommonPointFamily_conservative :
    (fieldPrescribedCommonPointFamily.{u, w} k Ω).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  apply (fieldPrescribedCommonPoint_cover_iff.{u, w} k Ω R).mpr
  intro z
  exact hR
    ⟨smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω),
      ObjectProperty.ofObj.mk ()⟩ z

/-- Let Ω be a prescribed separable closure of k. The common geometric stalk functor on
small-étale additive-group sheaves of height max(u,w) reflects isomorphisms: if the induced
stalk morphism is invertible, the sheaf morphism itself is invertible. -/
instance fieldPrescribedCommonStalk_reflectsIsomorphisms :
    (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).ReflectsIsomorphisms where
  reflects τ _ := by
    have h := (fieldPrescribedCommonPointFamily_conservative.{u, w} k Ω).jointlyReflectIsomorphisms
      AddCommGrpCat.{max u w}
    let (Φ : (fieldPrescribedCommonPointFamily.{u, w} k Ω).FullSubcategory) :
        IsIso (Φ.obj.sheafFiber.map τ) := by
      rcases Φ with ⟨Φ, hΦ⟩
      obtain ⟨i, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
      exact inferInstanceAs
        (IsIso ((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ))
    exact h.isIso τ

/-- For a field k and prescribed separable closure Ω, the functor taking a small-étale
additive-group sheaf to its discrete Galois stalk reflects isomorphisms. Forgetting its Galois
action gives the conservative common geometric stalk functor. -/
instance fieldGeometricStalkGaloisFunctor_reflectsIsomorphisms :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).ReflectsIsomorphisms := by
  let : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      DiscreteAbelianAction.forget Gal(Ω/k)).ReflectsIsomorphisms :=
    inferInstanceAs
      ((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (DiscreteAbelianAction.forget Gal(Ω/k))

/-- Let k be a field of universe u. The coefficient-lift functor from small-étale additive-group
sheaves of size w to size max(u,w), using ULift^u, reflects isomorphisms. An invertible lifted
sheaf map implies an invertible unlifted map. -/
instance fieldOriginalCoefficientLift_reflectsIsomorphisms :
    (liftCoefficients.{u, w} (Spec (.of k))).ReflectsIsomorphisms := by
  let J := (Spec (.of k)).smallEtaleTopology
  let L := liftCoefficients.{u, w} (Spec (.of k))
  let : (L ⋙ sheafToPresheaf J AddCommGrpCat.{max u w}).ReflectsIsomorphisms := by
    change (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (Functor.whiskeringRight (Spec (.of k)).Etaleᵒᵖ AddCommGrpCat.{w}
        AddCommGrpCat.{max u w}).obj AddCommGrpCat.uliftFunctor.{u, w}).ReflectsIsomorphisms
    infer_instance
  exact reflectsIsomorphisms_of_comp L (sheafToPresheaf J AddCommGrpCat.{max u w})

/-- Let Ω be a prescribed separable closure of k, τ : F → F′ a small-étale additive-group sheaf
map of coefficient universe w, and L the ULift^u coefficient functor. Then S_Ω(Lτ) is an
isomorphism if and only if τ is an isomorphism. The stalk has coefficient height max(u,w). -/
theorem fieldOriginalSheafMap_isIso_iff_commonStalk
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    IsIso ((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
      ((liftCoefficients.{u, w} (Spec (.of k))).map τ)) ↔ IsIso τ := by
  rw [isIso_iff_of_reflects_iso,
    isIso_iff_of_reflects_iso]

/-- For a field k and prescribed separable closure Ω, let τ : F → F′ be a small-étale sheaf map
with coefficient universe w. Its Galois stalk after the single coefficient lift, Φ_Ω(Lτ), is
invertible if and only if τ is invertible. -/
theorem fieldOriginalSheafMap_isIso_iff_galoisStalk
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    IsIso ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      ((liftCoefficients.{u, w} (Spec (.of k))).map τ)) ↔ IsIso τ := by
  rw [isIso_iff_of_reflects_iso,
    isIso_iff_of_reflects_iso]

/-- Let k have universe u, F be a small-étale additive-group sheaf of coefficient universe w, and
U an étale object over k. The coefficient-lifted sheaf has value
AddCommGrpCat.of(ULift^u(F(U))) at U. -/
theorem fieldOriginalCoefficientLift_obj
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) :
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj.obj (op U) =
      AddCommGrpCat.of (ULift.{u} (F.obj.obj (op U))) := rfl

/-- For a field k of universe u, a small-étale sheaf morphism τ : F → F′ with coefficient universe
w, and U an étale object, the component (Lτ)_U is AddCommGrpCat.uliftFunctor applied to τ_U.
It sends up(c) to up(τ_U(c)) using the single ULift^u. -/
theorem fieldOriginalCoefficientLift_map
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}}
    (τ : F ⟶ F') (U : (Spec (.of k)).Etale) :
    ((liftCoefficients.{u, w} (Spec (.of k))).map τ).hom.app (op U) =
      AddCommGrpCat.uliftFunctor.{u, w}.map (τ.hom.app (op U)) := rfl

/-- Let Ω be a prescribed separable closure of a field k, p its point, pc its ULift^w fiber
version, S the common additive-group stalk, Φ the Galois stalk, and L the ULift^u coefficient
functor. This proposition asserts surjectivity of Spec(Ω)→Spec(k); cover detection by both p
and pc; pc(U)=ULift^w(p(U)) with lifted fiber maps; conservativity of both singleton families;
reflection of sheaf isomorphisms by S and Φ at common height and after L for smaller
coefficients; the pointwise lifted object and morphism formulas; and equality Φ⋙forget=S,
including on the lifted maps. -/
def OriginalFieldSingletonStalkConservativityLaws : Prop :=
  let X := Spec (.of k)
  let p := fieldGeometricPoint k Ω
  let pc := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let S := smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let L := liftCoefficients.{u, w} X
  Function.Surjective (Spec.algebraMap k Ω) ∧
  (∀ (U : X.Etale) (R : Sieve U), R ∈ X.smallEtaleTopology U ↔
    ∀ z : p.fiber.obj U, ∃ (V : X.Etale) (g : V ⟶ U) (_ : R g)
      (y : p.fiber.obj V), p.fiber.map g y = z) ∧
  (∀ U : X.Etale, pc.fiber.obj U = ULift.{w} (p.fiber.obj U)) ∧
  (∀ (U V : X.Etale) (g : V ⟶ U) (z : p.fiber.obj V),
    pc.fiber.map g (ULift.up z) = ULift.up (p.fiber.map g z)) ∧
  (∀ (U : X.Etale) (R : Sieve U), R ∈ X.smallEtaleTopology U ↔
    ∀ z : pc.fiber.obj U, ∃ (V : X.Etale) (g : V ⟶ U) (_ : R g)
      (y : pc.fiber.obj V), pc.fiber.map g y = z) ∧
  (fieldPrescribedGeometricPointFamily k Ω).IsConservativeFamilyOfPoints ∧
  (fieldPrescribedCommonPointFamily.{u, w} k Ω).IsConservativeFamilyOfPoints ∧
  S.ReflectsIsomorphisms ∧ T.ReflectsIsomorphisms ∧
  (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    IsIso (S.map τ) ↔ IsIso τ) ∧
  (∀ (Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (τ : Q ⟶ Q'),
    IsIso (T.map τ) ↔ IsIso τ) ∧
  (∀ (F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (τ : F ⟶ F'),
    (IsIso (S.map (L.map τ)) ↔ IsIso τ) ∧
    (IsIso (T.map (L.map τ)) ↔ IsIso τ) ∧
    (∀ U : X.Etale, (L.map τ).hom.app (op U) =
      AddCommGrpCat.uliftFunctor.{u, w}.map (τ.hom.app (op U))) ∧
    (DiscreteAbelianAction.forget Gal(Ω/k)).map (T.map (L.map τ)) = S.map (L.map τ)) ∧
  (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (U : X.Etale),
    (L.obj F).obj.obj (op U) = AddCommGrpCat.of (ULift.{u} (F.obj.obj (op U)))) ∧
  T ⋙ DiscreteAbelianAction.forget Gal(Ω/k) = S

/-- For a field k and prescribed separable closure Ω, the fixed geometric point detects all
small-étale covering sieves, its common fiber is ULift^w of the prescribed fiber, and both
additive-group and Galois stalks detect sheaf isomorphisms. These laws also hold after the
single coefficient lift from universe w to max(u,w), with the same section maps and forgetful
comparison. -/
theorem original_field_singleton_stalk_conservativity :
    OriginalFieldSingletonStalkConservativityLaws.{u, w} k Ω := by
  refine ⟨fieldPrescribedGeometricMorphism_surjective k Ω,
    (fun _ R => fieldPrescribedGeometricPoint_cover_iff k Ω R),
    fieldPrescribedCommonPoint_fiber_obj.{u, w} k Ω,
    (fun _ _ g z => fieldPrescribedCommonPoint_fiber_map.{u, w} k Ω g z),
    (fun _ R => fieldPrescribedCommonPoint_cover_iff.{u, w} k Ω R),
    fieldPrescribedGeometricPointFamily_conservative k Ω,
    fieldPrescribedCommonPointFamily_conservative.{u, w} k Ω,
    inferInstance, inferInstance, ?_, ?_, ?_,
    fieldOriginalCoefficientLift_obj.{u, w} k,
    fieldGeometricStalkGaloisFunctor_forget.{u, w} k Ω⟩
  · exact fun _ _ τ => isIso_iff_of_reflects_iso τ _
  · exact fun _ _ τ => isIso_iff_of_reflects_iso τ _
  · intro F F' τ
    exact ⟨fieldOriginalSheafMap_isIso_iff_commonStalk.{u, w} k Ω τ,
      fieldOriginalSheafMap_isIso_iff_galoisStalk.{u, w} k Ω τ,
      fieldOriginalCoefficientLift_map.{u, w} k τ, rfl⟩

end AlgebraicGeometry.Scheme.DerivedSections
