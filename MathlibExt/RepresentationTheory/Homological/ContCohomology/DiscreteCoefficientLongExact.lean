/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- AI-assisted original formalization: Avocado; responsible human author: @toskua.
module
public import MathlibExt.CategoryTheory.Action.DiscreteAbelian
public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.ContinuousInhomogeneousCochains
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoefficientFunctor
public import MathlibExt.Algebra.Homology.HomologySequenceFunctor
public import MathlibExt.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction

/-! # Exact sequences of the original continuous cochains -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v z y w a b c d e

namespace ContinuousCohomology

instance instULiftIsTopologicalAddGroup {X : Type c} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] : IsTopologicalAddGroup (ULift.{d, c} X) :=
  Topology.IsInducing.isTopologicalAddGroup
    (AddEquiv.ulift.toAddMonoidHom : ULift.{d, c} X →+ X) ⟨rfl⟩

instance instULiftContinuousSMul {R : Type a} [TopologicalSpace R]
    {X : Type c} [TopologicalSpace X]
    [SMul R X] [ContinuousSMul R X] : ContinuousSMul R (ULift.{d, c} X) :=
  (show Topology.IsInducing (ULift.down : ULift.{d, c} X → X) from ⟨rfl⟩).continuousSMul
    (f := id) continuous_id rfl

/-- ONE coefficient lift, retaining the native group and the stored scalar modules. -/
def nativeTopRepULiftFunctor {k : Type a} [Ring k] [TopologicalSpace k]
    (G : Type b) [Group G] :
    TopRep.{c, a, b} k G ⥤ TopRep.{max c d, a, b} k G where
  obj X := TopRep.of (X := ULift.{d, c} X)
    { toMonoidHom :=
      { toFun g :=
          (ContinuousLinearEquiv.ulift : ULift.{d, c} X ≃L[k] X).symm.toContinuousLinearMap.comp
            ((X.ρ g).comp
              (ContinuousLinearEquiv.ulift : ULift.{d, c} X ≃L[k] X).toContinuousLinearMap)
        map_one' := by
          apply ContinuousLinearMap.ext
          intro x
          apply ULift.ext
          exact congrArg (fun f => f x.down) (map_one X.ρ)
        map_mul' g h := by
          apply ContinuousLinearMap.ext
          intro x
          apply ULift.ext
          exact congrArg (fun f => f x.down) (map_mul X.ρ g h) } }
  map {X Y} f := TopRep.ofHom
    { __ :=
        (ContinuousLinearEquiv.ulift : ULift.{d, c} Y ≃L[k] Y).symm.toContinuousLinearMap.comp
          (f.hom.toContinuousLinearMap.comp
            (ContinuousLinearEquiv.ulift : ULift.{d, c} X ≃L[k] X).toContinuousLinearMap)
      isIntertwining' g := by
        apply ContinuousLinearMap.ext
        intro x
        apply ULift.ext
        exact f.hom.isIntertwining g x.down }
  map_id X := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl

instance {k : Type a} [Ring k] [TopologicalSpace k] (G : Type b) [Group G] :
    (nativeTopRepULiftFunctor.{a, b, c, d} (k := k) G).Additive where
  map_add := by
    intros
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl

theorem nativeTopRepULiftFunctor_map_up
    {k : Type a} [Ring k] [TopologicalSpace k] {G : Type b} [Group G]
    {X Y : TopRep.{c, a, b} k G} (f : X ⟶ Y) (x : X) :
    ((nativeTopRepULiftFunctor.{a, b, c, d} (k := k) G).map f).hom (ULift.up x) =
      ULift.up (f.hom x) := rfl

theorem nativeTopRepULiftFunctor_action_up
    {k : Type a} [Ring k] [TopologicalSpace k] {G : Type b} [Group G]
    (X : TopRep.{c, a, b} k G) (g : G) (x : X) :
    ((nativeTopRepULiftFunctor.{a, b, c, d} (k := k) G).obj X).ρ g (ULift.up x) =
      ULift.up (X.ρ g x) := rfl

/-- Lift the original intertwiner once on each coefficient carrier; both groups stay native. -/
def nativeULiftGroupIntertwiner
    {k : Type a} [Ring k] [TopologicalSpace k]
    {G : Type b} [Group G] {H : Type c} [Group H]
    {X : TopRep.{max b e, a, b} k G} {Y : TopRep.{max c e, a, c} k H}
    (φ : H →* G) (f : ContIntertwiningMap (X.ρ.restrict φ) Y.ρ) :
    TopRep.res φ ((nativeTopRepULiftFunctor.{a, b, max b e, c} (k := k) G).obj X) ⟶
      (nativeTopRepULiftFunctor.{a, c, max c e, b} (k := k) H).obj Y :=
  TopRep.ofHom
    { __ :=
        (ContinuousLinearEquiv.ulift : ULift.{b, max c e} Y ≃L[k] Y).symm.toContinuousLinearMap.comp
          (f.toContinuousLinearMap.comp
            (ContinuousLinearEquiv.ulift : ULift.{c, max b e} X ≃L[k] X).toContinuousLinearMap)
      isIntertwining' h := by
        apply ContinuousLinearMap.ext
        intro x
        apply ULift.ext
        exact f.isIntertwining h x.down }

theorem nativeULiftGroupIntertwiner_apply
    {k : Type a} [Ring k] [TopologicalSpace k]
    {G : Type b} [Group G] {H : Type c} [Group H]
    {X : TopRep.{max b e, a, b} k G} {Y : TopRep.{max c e, a, c} k H}
    (φ : H →* G) (f : ContIntertwiningMap (X.ρ.restrict φ) Y.ρ) (x : X) :
    (nativeULiftGroupIntertwiner.{a, b, c, e} φ f).hom (ULift.up x) =
      ULift.up (f x) := rfl

/-- Generic scalar packaging retains each module instance stored in the original representations. -/
abbrev nativeCoefficientIntertwiner
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    (X : TopRep.{max v w, u, v} k G) (Y : TopRep.{max z w, u, z} k H)
    (φ : H →ₜ* G) := ContIntertwiningMap (X.ρ.restrict (φ : H →* G)) Y.ρ

theorem nativeULiftGroupIntertwiner_coefficient_square
    {k : Type a} [Ring k] [TopologicalSpace k]
    {G : Type b} [Group G] {H : Type c} [Group H]
    {X₁ X₂ : TopRep.{max b e, a, b} k G}
    {Y₁ Y₂ : TopRep.{max c e, a, c} k H}
    (φ : H →* G) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂)
    (f₁ : ContIntertwiningMap (X₁.ρ.restrict φ) Y₁.ρ)
    (f₂ : ContIntertwiningMap (X₂.ρ.restrict φ) Y₂.ρ)
    (hf : ∀ x, b.hom (f₁ x) = f₂ (a.hom x)) :
    nativeULiftGroupIntertwiner.{a, b, c, e} φ f₁ ≫
        (nativeTopRepULiftFunctor.{a, c, max c e, b} (k := k) H).map b =
      (TopRep.resFunctor φ).map
          ((nativeTopRepULiftFunctor.{a, b, max b e, c} (k := k) G).map a) ≫
        nativeULiftGroupIntertwiner.{a, b, c, e} φ f₂ := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  apply ULift.ext
  exact hf x.down

/- The generic scalar versions retain the modules stored in TopModuleCat. In
particular, specializing these checked constructions to integers does not
replace a stored integer-module structure by the canonical zsmul structure. -/

theorem homogeneousNestedCoefficientMap_apply
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {X Y : TopRep.{max v w, u, v} k G}
    (f : X ⟶ Y) (n : ℕ) (c : (TopRep.homogeneousCochains X).X n)
    (t : Fin (n + 1) → G) :
    (homogeneousFinContinuousLinearEquiv.{u, v, w} Y n
      (((homogeneousCochainsFunctor.{u, v, w} (k := k) (G := G)).map f).f n c)).val t =
        f.hom ((homogeneousFinContinuousLinearEquiv.{u, v, w} X n c).val t) := by
  let ψ : TopRep.homogeneousCochains X ⟶ TopRep.homogeneousCochains Y :=
    cochainsMap (ContinuousMonoidHom.id G) (TopRep.ofHom f.hom)
  change (homogeneousFinContinuousLinearEquiv.{u, v, w} Y n (ψ.f n c)).val t = _
  calc
    _ = resolutionFinUncurry Y (n + 1) (ψ.f n c).val t :=
      homogeneousFinContinuousLinearEquiv_apply.{u, v, w} _ _ _ _
    _ = f.hom (resolutionFinUncurry X (n + 1) c.val t) :=
      resolutionFinUncurry_resolutionMap.{u, v, w} (ContinuousMonoidHom.id G)
        (TopRep.ofHom f.hom) (n + 1) c.val t
    _ = _ := congrArg f.hom
      (homogeneousFinContinuousLinearEquiv_apply.{u, v, w} _ _ _ _).symm

/-- Apply the original continuous group map to every homogeneous tuple coordinate. -/
def nativeHomogeneousTupleMap
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}} (φ : H →ₜ* G) (n : ℕ) :
    C(Fin (n + 1) → H, Fin (n + 1) → G) :=
  ⟨fun t i => φ (t i), continuous_pi fun i => φ.continuous.comp (continuous_apply i)⟩

/-- The literal map on the EXISTING flat homogeneous cochains, with native group universes. -/
def nativeFlatGroupCoefficientTerm
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    flatHomogeneousTerm.{u, v, max z w} X n ⟶ flatHomogeneousTerm.{u, z, max v w} Y n :=
  TopModuleCat.ofHom
    { toFun := fun c =>
        ⟨⟨fun t => f.hom (c.val (nativeHomogeneousTupleMap.{v, z} φ n t)),
          f.hom.continuous.comp
            (c.val.continuous.comp (nativeHomogeneousTupleMap.{v, z} φ n).continuous)⟩, by
          intro h t
          change f.hom (c.val (fun i => φ (h * t i))) =
            Y.ρ h (f.hom (c.val (fun i => φ (t i))))
          have hm : (fun i => φ (h * t i)) = (fun i => φ h * φ (t i)) := by
            funext i
            exact map_mul φ h (t i)
          rw [hm, c.property (φ h)]
          exact f.hom.isIntertwining h _⟩
      map_add' := by
        intro a b
        ext t
        exact map_add f.hom _ _
      map_smul' := by
        intro r a
        ext t
        exact map_smul f.hom r _
      cont := by
        apply Continuous.subtype_mk
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact f.hom.continuous.comp
          (continuous_eval.comp
            ((continuous_subtype_val.comp continuous_fst).prodMk
              ((nativeHomogeneousTupleMap.{v, z} φ n).continuous.comp continuous_snd))) }

theorem nativeFlatGroupCoefficientTerm_apply
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ)
    (c : flatHomogeneousCochains.{u, v, max z w} X n) (t : Fin (n + 1) → H) :
    (nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f n c).val t =
      f.hom (c.val (fun i => φ (t i))) := rfl

/-- The original deletion differential commutes with these literal maps. -/
theorem nativeFlatGroupCoefficientTerm_comm
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f n ≫ flatHomogeneousD.{u, z, max v w} Y n =
      flatHomogeneousD.{u, v, max z w} X n ≫
        nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f (n + 1) := by
  ext c t
  change (flatHomogeneousD.{u, z, max v w} Y n
      (nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f n c)).val t =
    (nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f (n + 1)
      (flatHomogeneousD.{u, v, max z w} X n c)).val t
  rw [flatHomogeneousD_apply, nativeFlatGroupCoefficientTerm_apply,
    flatHomogeneousD_apply]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a => (-1 : k) ^ (j : ℕ) • a)
    (nativeFlatGroupCoefficientTerm_apply.{u, v, z, w} φ f n c
      (fun i => t (j.succAbove i)))

/-- A map of the unchanged flat complexes on the original groups and coefficients. -/
def nativeFlatGroupCoefficientMap
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    flatHomogeneousComplex.{u, v, max z w} X ⟶ flatHomogeneousComplex.{u, z, max v w} Y where
  f n := nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f n
  comm' i j hij := by
    have h : i + 1 = j := hij
    subst j
    change nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f i ≫
      (flatHomogeneousComplex.{u, z, max v w} Y).d i (i + 1) =
        (flatHomogeneousComplex.{u, v, max z w} X).d i (i + 1) ≫
          nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f (i + 1)
    simpa only [flatHomogeneousComplex, CochainComplex.of_d] using
      nativeFlatGroupCoefficientTerm_comm φ f i

/-- Transport the same literal flat map to the existing nested homogeneous complex. -/
def nativeGroupCoefficientCochainsMap
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    TopRep.homogeneousCochains.{u, v, max z w} X ⟶ TopRep.homogeneousCochains.{u, z, max v w} Y :=
  (homogeneousFlatComplexIso.{u, v, max z w} X).hom ≫
    nativeFlatGroupCoefficientMap.{u, v, z, w} φ f ≫
      (homogeneousFlatComplexIso.{u, z, max v w} Y).inv

/-- This is a map of the ORIGINAL continuous cohomology; it defines no new cohomology group. -/
def nativeGroupCoefficientCohomologyMap
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    continuousCohomology.{u, v, max z w} n X ⟶ continuousCohomology.{u, z, max v w} n Y :=
  HomologicalComplex.homologyMap (nativeGroupCoefficientCochainsMap.{u, v, z, w} φ f) n

/-- Every transported map still has the literal original tuple values. -/
theorem nativeGroupCoefficientCochainsMap_apply
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ)
    (c : (TopRep.homogeneousCochains.{u, v, max z w} X).X n) (t : Fin (n + 1) → H) :
    (homogeneousFinContinuousLinearEquiv.{u, z, max v w} Y n
      ((nativeGroupCoefficientCochainsMap.{u, v, z, w} φ f).f n c)).val t =
        f.hom ((homogeneousFinContinuousLinearEquiv.{u, v, max z w} X n c).val
          (fun i => φ (t i))) := by
  change (homogeneousFinContinuousLinearEquiv.{u, z, max v w} Y n
    ((homogeneousFinContinuousLinearEquiv.{u, z, max v w} Y n).symm
      (nativeFlatGroupCoefficientTerm.{u, v, z, w} φ f n
        (homogeneousFinContinuousLinearEquiv.{u, v, max z w} X n c)))).val t = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Finite-tuple evaluation in degree zero is the original one-coordinate evaluation. -/
theorem homogeneousFinZero_apply
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G)
    (c : (TopRep.homogeneousCochains X).X 0) (g : G) :
    (homogeneousFinContinuousLinearEquiv.{u, v, w} X 0 c).val (fun _ => g) = c.val g :=
  (homogeneousFinContinuousLinearEquiv_apply.{u, v, w} X 0 c (fun _ => g)).trans rfl

theorem nativeGroupCoefficientCochainsMap_zero_value
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y)
    (c : (TopRep.homogeneousCochains.{u, v, max z w} X).X 0) (h : H) :
    ((nativeGroupCoefficientCochainsMap.{u, v, z, w} φ f).f 0 c).val h =
      f.hom (c.val (φ h)) :=
  (homogeneousFinZero_apply.{u, z, max v w} Y _ h).symm.trans
    ((nativeGroupCoefficientCochainsMap_apply.{u, v, z, w} φ f 0 c (fun _ => h)).trans
      (congrArg f.hom (homogeneousFinZero_apply.{u, v, max z w} X c (φ h))))

/-- Agreement with the actual stock cochain map whenever its group universes are typed. -/
theorem nativeGroupCoefficientCochainsMap_eq_stock
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G H : ProfiniteGrp.{v}} {X : TopRep.{max v w, u, v} k G}
    {Y : TopRep.{max v w, u, v} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    nativeGroupCoefficientCochainsMap.{u, v, v, w} φ f = cochainsMap φ f := by
  ext n : 1
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro c
  exact (homogeneousFinContinuousLinearEquiv.{u, v, max v w} Y n).injective (by
    ext t
    have hX := homogeneousFinContinuousLinearEquiv_apply.{u, v, max v w}
      X n c (fun i => φ (t i))
    have hY := homogeneousFinContinuousLinearEquiv_apply.{u, v, max v w}
      Y n ((cochainsMap φ f).f n c) t
    have hS := resolutionFinUncurry_resolutionMap.{u, v, max v w}
      φ f (n + 1) c.val t
    exact (nativeGroupCoefficientCochainsMap_apply.{u, v, v, w} φ f n c t).trans
      ((congrArg f.hom hX).trans (hS.symm.trans hY.symm)))

theorem nativeGroupCoefficientCohomologyMap_eq_stock
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G H : ProfiniteGrp.{v}} {X : TopRep.{max v w, u, v} k G}
    {Y : TopRep.{max v w, u, v} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    nativeGroupCoefficientCohomologyMap.{u, v, v, w} φ f n = ContinuousCohomology.map φ f n :=
  congrArg (fun q => HomologicalComplex.homologyMap q n)
    (nativeGroupCoefficientCochainsMap_eq_stock φ f)

/-- The original identity group and coefficient maps give the actual identity cochain map. -/
theorem nativeGroupCoefficientCochainsMap_id
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G) :
    nativeGroupCoefficientCochainsMap.{u, v, v, w}
      (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (TopRep.homogeneousCochains X) :=
  (nativeGroupCoefficientCochainsMap_eq_stock.{u, v, w}
    (ContinuousMonoidHom.id G) (𝟙 X)).trans (cochainsMap_id X)

/-- Native group universes are retained in both stages of the actual composite map. -/
theorem nativeGroupCoefficientCochainsMap_comp
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}} {K : ProfiniteGrp.{y}}
    {X : TopRep.{max v (max z (max y w)), u, v} k G}
    {Y : TopRep.{max z (max v (max y w)), u, z} k H}
    {Z : TopRep.{max y (max v (max z w)), u, y} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ Y ⟶ Z) :
    nativeGroupCoefficientCochainsMap.{u, v, y, max z w} (φ.comp ψ)
        ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g) =
      nativeGroupCoefficientCochainsMap.{u, v, z, max y w} φ f ≫
        nativeGroupCoefficientCochainsMap.{u, z, y, max v w} ψ g := by
  ext n : 1
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro c
  exact (homogeneousFinContinuousLinearEquiv.{u, y, max v (max z w)} Z n).injective (by
    ext t
    have hC := nativeGroupCoefficientCochainsMap_apply.{u, v, y, max z w}
      (φ.comp ψ) ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g) n c t
    have hA := nativeGroupCoefficientCochainsMap_apply.{u, v, z, max y w}
      φ f n c (fun i => ψ (t i))
    have hB := nativeGroupCoefficientCochainsMap_apply.{u, z, y, max v w}
      ψ g n ((nativeGroupCoefficientCochainsMap.{u, v, z, max y w} φ f).f n c) t
    exact hC.trans ((congrArg g.hom hA).symm.trans hB.symm))

theorem nativeGroupCoefficientCohomologyMap_id
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G) (n : ℕ) :
    nativeGroupCoefficientCohomologyMap.{u, v, v, w}
      (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 (continuousCohomology n X) := by
  exact (congrArg (fun m => HomologicalComplex.homologyMap m n)
    (nativeGroupCoefficientCochainsMap_id.{u, v, w} X)).trans
      (HomologicalComplex.homologyMap_id _ _)

theorem nativeGroupCoefficientCohomologyMap_comp
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}} {K : ProfiniteGrp.{y}}
    {X : TopRep.{max v (max z (max y w)), u, v} k G}
    {Y : TopRep.{max z (max v (max y w)), u, z} k H}
    {Z : TopRep.{max y (max v (max z w)), u, y} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ Y ⟶ Z) (n : ℕ) :
    nativeGroupCoefficientCohomologyMap.{u, v, y, max z w} (φ.comp ψ)
        ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g) n =
      nativeGroupCoefficientCohomologyMap.{u, v, z, max y w} φ f n ≫
        nativeGroupCoefficientCohomologyMap.{u, z, y, max v w} ψ g n :=
  (congrArg (fun m => HomologicalComplex.homologyMap m n)
    (nativeGroupCoefficientCochainsMap_comp.{u, v, z, y, w} φ ψ f g)).trans
      (HomologicalComplex.homologyMap_comp _ _ _)

/-- Every original coefficient square gives the actual native-universe cochain square. -/
theorem homogeneousGroupCoefficientSquare
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X₁ X₂ : TopRep.{max v (max z w), u, v} k G}
    {Y₁ Y₂ : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂)
    (ψ₁ : TopRep.res φ X₁ ⟶ Y₁) (ψ₂ : TopRep.res φ X₂ ⟶ Y₂)
    (hψ : ψ₁ ≫ b = (TopRep.resFunctor (φ : H →* G)).map a ≫ ψ₂) :
    nativeGroupCoefficientCochainsMap φ ψ₁ ≫
        (homogeneousCochainsFunctor.{u, z, max v w} (k := k) (G := H)).map b =
      (homogeneousCochainsFunctor.{u, v, max z w} (k := k) (G := G)).map a ≫
        nativeGroupCoefficientCochainsMap φ ψ₂ := by
  ext n : 1
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro c
  apply (homogeneousFinContinuousLinearEquiv.{u, z, max v w} Y₂ n).injective
  ext t
  change (homogeneousFinContinuousLinearEquiv.{u, z, max v w} Y₂ n
      (((homogeneousCochainsFunctor.{u, z, max v w} (k := k) (G := H)).map b).f n
        ((nativeGroupCoefficientCochainsMap φ ψ₁).f n c))).val t =
    (homogeneousFinContinuousLinearEquiv.{u, z, max v w} Y₂ n
      ((nativeGroupCoefficientCochainsMap φ ψ₂).f n
        (((homogeneousCochainsFunctor.{u, v, max z w} (k := k) (G := G)).map a).f n c))).val t
  have hL := homogeneousNestedCoefficientMap_apply.{u, z, max v w} b n
    ((nativeGroupCoefficientCochainsMap.{u, v, z, w} φ ψ₁).f n c) t
  have hL' := nativeGroupCoefficientCochainsMap_apply.{u, v, z, w} φ ψ₁ n c t
  have hR := nativeGroupCoefficientCochainsMap_apply.{u, v, z, w} φ ψ₂ n
    (((homogeneousCochainsFunctor.{u, v, max z w} (k := k) (G := G)).map a).f n c) t
  have hR' := homogeneousNestedCoefficientMap_apply.{u, v, max z w} a n c
    (fun i => φ (t i))
  have hmid := congrArg (fun f => f.hom
    ((homogeneousFinContinuousLinearEquiv.{u, v, max z w} X₁ n c).val
      (fun i => φ (t i)))) hψ
  exact hL.trans ((congrArg b.hom hL').trans
    (hmid.trans ((congrArg ψ₂.hom hR').symm.trans hR.symm)))

/-- The original coefficient diagram gives the SAME actual cohomology diagram. -/
theorem homogeneousGroupCoefficientCohomologySquare
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X₁ X₂ : TopRep.{max v (max z w), u, v} k G}
    {Y₁ Y₂ : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂)
    (ψ₁ : TopRep.res φ X₁ ⟶ Y₁) (ψ₂ : TopRep.res φ X₂ ⟶ Y₂)
    (hψ : ψ₁ ≫ b = (TopRep.resFunctor (φ : H →* G)).map a ≫ ψ₂) (n : ℕ) :
    nativeGroupCoefficientCohomologyMap.{u, v, z, w} φ ψ₁ n ≫
        HomologicalComplex.homologyMap
          ((homogeneousCochainsFunctor.{u, z, max v w} (k := k) (G := H)).map b) n =
      HomologicalComplex.homologyMap
          ((homogeneousCochainsFunctor.{u, v, max z w} (k := k) (G := G)).map a) n ≫
        nativeGroupCoefficientCohomologyMap.{u, v, z, w} φ ψ₂ n := by
  have h := congrArg (fun m => HomologicalComplex.homologyMap m n)
    (homogeneousGroupCoefficientSquare.{u, v, z, w} φ a b ψ₁ ψ₂ hψ)
  exact (HomologicalComplex.homologyMap_comp
    (nativeGroupCoefficientCochainsMap.{u, v, z, w} φ ψ₁)
    ((homogeneousCochainsFunctor.{u, z, max v w} (k := k) (G := H)).map b) n).symm.trans
    (h.trans (HomologicalComplex.homologyMap_comp
      ((homogeneousCochainsFunctor.{u, v, max z w} (k := k) (G := G)).map a)
      (nativeGroupCoefficientCochainsMap.{u, v, z, w} φ ψ₂) n))

/-- The genuine nested-to-inhomogeneous comparison, for every scalar ring. -/
def homogeneousNestedInhomogeneousAddEquiv
    {k : Type u} [Ring k] [TopologicalSpace k]
    (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} k) G) (n : ℕ) :
    (TopRep.homogeneousCochains (inhomogeneousOriginalTopRep.{u, v, w} G A)).X n ≃+
      C(Fin n → G, inhomogeneousOriginalTopRep.{u, v, w} G A) :=
  (homogeneousFinContinuousLinearEquiv.{u, v, w}
    (inhomogeneousOriginalTopRep.{u, v, w} G A) n).toAddEquiv.trans
      (inhomogeneousContinuousEquiv.{u, v, w} G A n).toAddEquiv

theorem homogeneousNestedInhomogeneousAddEquiv_map
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} k) G} (f : A ⟶ B)
    (n : ℕ)
    (c : (TopRep.homogeneousCochains (inhomogeneousOriginalTopRep.{u, v, w} G A)).X n)
    (t : Fin n → G) :
    homogeneousNestedInhomogeneousAddEquiv.{u, v, w} G B n
      (((homogeneousCochainsFunctor.{u, v, w} (k := k) (G := G)).map
        ((TopRep.fromActionTopModFunc (k := k) (G := G)).map f.hom.hom)).f n c) t =
      (((TopRep.fromActionTopModFunc (k := k) (G := G)).map f.hom.hom).hom)
        (homogeneousNestedInhomogeneousAddEquiv.{u, v, w} G A n c t) := by
  change (inhomogeneousContinuousEquiv.{u, v, w} G B n
      (homogeneousFinContinuousLinearEquiv.{u, v, w}
        (inhomogeneousOriginalTopRep.{u, v, w} G B) n _)) t = _
  rw [inhomogeneousContinuousEquiv_apply.{u, v, w}]
  rw [homogeneousNestedCoefficientMap_apply]
  rfl

/-- The original degree-zero normalization is identity evaluation on actual cycle classes. -/
theorem homogeneousZeroIso_projection
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G) :
    ContinuousCohomology.π X 0 ≫ (ContinuousCohomology.zeroIso X).hom =
      (ContinuousCohomology.cocycles₀Iso X).hom ≫
        (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso X)).hom := by
  change ((TopRep.homogeneousCochains X).isoHomologyπ₀).hom ≫
    (ContinuousCohomology.zeroIso X).hom = _
  simp only [ContinuousCohomology.zeroIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

theorem homogeneousZeroIso_cycle_value
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G)
    (c : ((TopRep.homogeneousCochains X).d 0 1).hom.ker) :
    ((ContinuousCohomology.zeroIso X).hom
      (ContinuousCohomology.π X 0 ((ContinuousCohomology.cocycles₀Iso X).inv c))).val =
        c.val.val 1 := by
  change ((ContinuousCohomology.π X 0 ≫ (ContinuousCohomology.zeroIso X).hom)
      ((ContinuousCohomology.cocycles₀Iso X).inv c)).val = _
  rw [homogeneousZeroIso_projection]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- The inverse normalization is the class of the original constant cocycle. -/
theorem homogeneousZeroIso_inverse_projection
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G) :
    (ContinuousCohomology.zeroIso X).inv =
      (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso X)).inv ≫
        (ContinuousCohomology.cocycles₀Iso X).inv ≫ ContinuousCohomology.π X 0 := by
  change (ContinuousCohomology.zeroIso X).inv = _ ≫ _ ≫
    (TopRep.homogeneousCochains X).isoHomologyπ₀.hom
  simp only [ContinuousCohomology.zeroIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]

theorem homogeneousZeroIso_inverse_constant
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G)
    (x : X.ρ.invariants) (g : G) :
    ((ContinuousCohomology.d₀kerIso X).symm x).val.val g = x.val := rfl

/-- The actual zeroth-cycle comparison preserves the original kernel inclusion. -/
theorem homogeneousZeroCocycles_projection
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G) :
    (ContinuousCohomology.cocycles₀Iso X).hom ≫
        TopModuleCat.kerι ((TopRep.homogeneousCochains X).d 0 1) =
      (TopRep.homogeneousCochains X).iCycles 0 := by
  let K := TopRep.homogeneousCochains X
  change (KernelFork.ofι (K.iCycles 0) (K.iCycles_d 0 1)).mapOfIsLimit
      (TopModuleCat.isLimitKer (K.d 0 1)) (𝟙 (Arrow.mk (K.d 0 1))) ≫
        TopModuleCat.kerι (K.d 0 1) = K.iCycles 0
  exact (KernelFork.mapOfIsLimit_ι
    (KernelFork.ofι (K.iCycles 0) (K.iCycles_d 0 1))
    (TopModuleCat.isLimitKer (K.d 0 1)) (𝟙 (Arrow.mk (K.d 0 1)))).trans
      (Category.comp_id (K.iCycles 0))

theorem homogeneousZeroIso_cycles_value
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G)
    (c : ContinuousCohomology.cocycles X 0) :
    ((ContinuousCohomology.zeroIso X).hom (ContinuousCohomology.π X 0 c)).val =
      ((TopRep.homogeneousCochains X).iCycles 0 c).val 1 := by
  change ((ContinuousCohomology.π X 0 ≫ (ContinuousCohomology.zeroIso X).hom) c).val = _
  rw [homogeneousZeroIso_projection.{u, v, w} X]
  change ((ContinuousCohomology.cocycles₀Iso X).hom c).val.val 1 = _
  exact congrArg (fun m => (m c).val 1) (homogeneousZeroCocycles_projection.{u, v, w} X)

/-- Identity-evaluation normalization respects EVERY original native group/coefficient map. -/
theorem nativeGroupCoefficientZeroIso_naturality
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    nativeGroupCoefficientCohomologyMap.{u, v, z, w} φ f 0 ≫
        (ContinuousCohomology.zeroIso Y).hom =
      (ContinuousCohomology.zeroIso X).hom ≫ TopRep.invariantsResMap (φ : H →* G) f := by
  apply (cancel_epi (ContinuousCohomology.π X 0)).1
  apply ConcreteCategory.ext
  apply ContinuousLinearMap.ext
  intro c
  apply Subtype.ext
  let m := nativeGroupCoefficientCochainsMap.{u, v, z, w} φ f
  let cY := HomologicalComplex.cyclesMap m 0 c
  have hπ := congrArg (fun q => q c) (HomologicalComplex.homologyπ_naturality m 0)
  have hI := congrArg (fun q => (q c).val 1) (HomologicalComplex.cyclesMap_i m 0)
  have hval : (m.f 0 ((TopRep.homogeneousCochains X).iCycles 0 c)).val 1 =
      f.hom (((TopRep.homogeneousCochains X).iCycles 0 c).val 1) := by
    simpa only [map_one] using nativeGroupCoefficientCochainsMap_zero_value.{u, v, z, w}
      φ f ((TopRep.homogeneousCochains X).iCycles 0 c) 1
  exact (congrArg (fun q => ((ContinuousCohomology.zeroIso Y).hom q).val) hπ).trans
    ((homogeneousZeroIso_cycles_value.{u, z, max v w} Y cY).trans
      (hI.trans (hval.trans
        (congrArg f.hom (homogeneousZeroIso_cycles_value.{u, v, max z w} X c)).symm)))


/-- Compatibility with the original profinite instance name, using the same canonical data. -/
@[nolint defsWithUnderscore] -- preserve the original public name
abbrev discreteCoefficient_preadditive (G : ProfiniteGrp.{v}) :
    Preadditive (DiscreteContAction (TopModuleCat.{w} ℤ) G) :=
  CategoryTheory.DiscreteAbelianAction.instPreadditive.{v, w} (G := G)

/-- Bundle the same original carrier and every original coefficient arrow. -/
abbrev discreteCoefficientTopRepFunctor (G : ProfiniteGrp.{v}) :
    DiscreteContAction (TopModuleCat.{max v w} ℤ) G ⥤ TopRep.{max v w, 0, v} ℤ G where
  obj A := inhomogeneousOriginalTopRep.{0, v, w} G A
  map f := (TopRep.fromActionTopModFunc.{max v w, 0, v} (k := ℤ) (G := G)).map f.hom.hom
  map_id _ := by apply TopRep.hom_ext; rfl
  map_comp _ _ := by apply TopRep.hom_ext; rfl

instance (G : ProfiniteGrp.{v}) :
    (discreteCoefficientTopRepFunctor.{v, w} G).Additive where
  map_add := by intros; apply TopRep.hom_ext; rfl

/-- The original additive function underlying a coefficient arrow. -/
abbrev discreteCoefficientHom {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) :
    inhomogeneousOriginalTopRep.{0, v, w} G A →+ inhomogeneousOriginalTopRep.{0, v, w} G B :=
  ((discreteCoefficientTopRepFunctor.{v, w} G).map f).hom.toAddMonoidHom

@[simp] theorem discreteCoefficientHom_apply
    {G : ProfiniteGrp.{v}} {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B)
    (a : inhomogeneousOriginalTopRep.{0, v, w} G A) :
    discreteCoefficientHom f a = f.hom.hom.hom.hom a := rfl

/-- The actual discrete continuous coefficient lift used when group sizes differ. -/
def discreteCoefficientULiftFunctor (G : ProfiniteGrp.{v}) :
    DiscreteContAction (TopModuleCat.{max v w} ℤ) G ⥤
      DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G where
  obj A := by
    let X := inhomogeneousOriginalTopRep.{0, v, w} G A
    let Y := (nativeTopRepULiftFunctor.{0, v, max v w, z} (k := ℤ) G).obj X
    let A' := (TopRep.toActionTopModFunc.{0, v, max v (max z w)}
      (k := ℤ) (G := G)).obj Y
    have hc : Continuous (fun p : G × X => X.ρ p.1 p.2) :=
      A.obj.property.continuous_smul
    have hY : ContinuousSMul G
        ((forget₂ (Action (TopModuleCat.{max v (max z w)} ℤ) G) TopCat).obj A') := by
      constructor
      change Continuous (fun p : G × ULift.{z, max v w} X =>
        ULift.up (X.ρ p.1 p.2.down))
      exact continuous_uliftUp.comp
        (hc.comp (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd)))
    let : DiscreteTopology X := A.property
    have hD : DiscreteTopology
        ((forget₂ (Action (TopModuleCat.{max v (max z w)} ℤ) G) TopCat).obj A') := by
      change DiscreteTopology (ULift.{z, max v w} X)
      infer_instance
    exact ⟨⟨A', hY⟩, hD⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    ((TopRep.toActionTopModFunc.{0, v, max v (max z w)} (k := ℤ) (G := G)).map
      ((nativeTopRepULiftFunctor.{0, v, max v w, z} (k := ℤ) G).map
        ((discreteCoefficientTopRepFunctor.{v, w} G).map f))))
  map_id A := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl

instance (G : ProfiniteGrp.{v}) :
    (discreteCoefficientULiftFunctor.{v, z, w} G).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl

/-- Literal original up-coordinate on every coefficient arrow. -/
theorem discreteCoefficientULiftFunctor_map_up {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B)
    (x : inhomogeneousOriginalTopRep.{0, v, w} G A) :
    discreteCoefficientHom.{v, max z w}
      ((discreteCoefficientULiftFunctor.{v, z, w} G).map f) (ULift.up x) =
        ULift.up (discreteCoefficientHom.{v, w} f x) := rfl

theorem discreteCoefficientULiftFunctor_map_down {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B)
    (x : inhomogeneousOriginalTopRep.{0, v, max z w} G
      ((discreteCoefficientULiftFunctor.{v, z, w} G).obj A)) :
    (discreteCoefficientHom.{v, max z w}
      ((discreteCoefficientULiftFunctor.{v, z, w} G).map f) x).down =
        discreteCoefficientHom.{v, w} f x.down := rfl

/-- Forget topology and integer scalar data, retaining the original group. -/
abbrev discreteCoefficientForget : TopModuleCat.{w} ℤ ⥤ AddCommGrpCat.{w} :=
  forget₂ (TopModuleCat.{w} ℤ) (ModuleCat.{w} ℤ) ⋙
    forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}

instance : discreteCoefficientForget.{w}.Additive where
  map_add := by intros; rfl

/-- The algebraic complex of the original homogeneous continuous cochains. -/
abbrev discreteCoefficientCochainFunctor (G : ProfiniteGrp.{v}) :
    DiscreteContAction (TopModuleCat.{max v w} ℤ) G ⥤ CochainComplex AddCommGrpCat.{max v w} ℕ :=
  discreteCoefficientTopRepFunctor.{v, w} G ⋙
    homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G) ⋙
      (discreteCoefficientForget.{max v w}).mapHomologicalComplex (ComplexShape.up ℕ)

instance (G : ProfiniteGrp.{v}) :
    (discreteCoefficientCochainFunctor.{v, w} G).Additive := by
  unfold discreteCoefficientCochainFunctor
  infer_instance

/-- The same actual cohomology group, with topology and scalar structure forgotten. -/
abbrev discreteCoefficientCohomologyFunctor (G : ProfiniteGrp.{v}) (n : ℕ) :
    DiscreteContAction (TopModuleCat.{max v w} ℤ) G ⥤ AddCommGrpCat.{max v w} :=
  discreteCoefficientTopRepFunctor.{v, w} G ⋙
    homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G) ⋙
      HomologicalComplex.homologyFunctor (TopModuleCat.{max v w} ℤ)
        (ComplexShape.up ℕ) n ⋙ discreteCoefficientForget

/-- The canonical homology comparison for the topology-forgetting functor. -/
def discreteCoefficientHomologyIso (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G)
    (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, w} G n).obj A ≅
      ((discreteCoefficientCochainFunctor.{v, w} G).obj A).homology n :=
  ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ)
    n discreteCoefficientForget.{max v w}).app (TopRep.homogeneousCochains
      (inhomogeneousOriginalTopRep.{0, v, w} G A))).symm

/-- Literal finite-tuple evaluation of the original coefficient cochain map. -/
theorem discreteCoefficient_flat_map_apply
    {G : ProfiniteGrp.{v}} {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) (n : ℕ)
    (c : (TopRep.homogeneousCochains (inhomogeneousOriginalTopRep.{0, v, w} G A)).X n)
    (t : Fin (n + 1) → G) :
    (homogeneousFinContinuousLinearEquiv.{0, v, w} (inhomogeneousOriginalTopRep.{0, v, w} G B) n
      (((homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G)).map
        ((discreteCoefficientTopRepFunctor.{v, w} G).map f)).f n c)).val t =
      discreteCoefficientHom f
        ((homogeneousFinContinuousLinearEquiv.{0, v, w}
          (inhomogeneousOriginalTopRep.{0, v, w} G A) n c).val t) := by
  exact homogeneousNestedCoefficientMap_apply
    ((discreteCoefficientTopRepFunctor.{v, w} G).map f) n c t

/-- The full coefficient comparison with arbitrary continuous inhomogeneous cochains. -/
def discreteCoefficientInhomogeneousEquiv (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G)
    (n : ℕ) :
    (TopRep.homogeneousCochains (inhomogeneousOriginalTopRep.{0, v, w} G A)).X n ≃+
      C(Fin n → G, inhomogeneousOriginalTopRep.{0, v, w} G A) :=
  homogeneousNestedInhomogeneousAddEquiv.{0, v, w} G A n

theorem discreteCoefficientInhomogeneousEquiv_map
    {G : ProfiniteGrp.{v}} {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) (n : ℕ)
    (c : (TopRep.homogeneousCochains (inhomogeneousOriginalTopRep.{0, v, w} G A)).X n)
    (t : Fin n → G) :
    discreteCoefficientInhomogeneousEquiv.{v, w} G B n
      (((homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G)).map
        ((discreteCoefficientTopRepFunctor.{v, w} G).map f)).f n c) t =
      discreteCoefficientHom f (discreteCoefficientInhomogeneousEquiv.{v, w} G A n c t) := by
  exact homogeneousNestedInhomogeneousAddEquiv_map f n c t

/-- An injective original coefficient map is injective on every actual cochain term. -/
theorem discreteCoefficientCochain_injective
    {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B)
    (hf : Function.Injective (discreteCoefficientHom f)) (n : ℕ) :
    Function.Injective (((discreteCoefficientCochainFunctor.{v, w} G).map f).f n) := by
  intro x y h
  apply (discreteCoefficientInhomogeneousEquiv.{v, w} G A n).injective
  ext t
  apply hf
  have ht := congrArg
    (fun c => discreteCoefficientInhomogeneousEquiv.{v, w} G B n c t) h
  exact (discreteCoefficientInhomogeneousEquiv_map f n x t).symm.trans
    (ht.trans (discreteCoefficientInhomogeneousEquiv_map f n y t))

/-- Discreteness makes a genuine set-theoretic section continuous; no linear or
equivariant section is required. The original inhomogeneous inverse restores equivariance. -/
theorem discreteCoefficientCochain_surjective
    {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B)
    (hf : Function.Surjective (discreteCoefficientHom f)) (n : ℕ) :
    Function.Surjective (((discreteCoefficientCochainFunctor.{v, w} G).map f).f n) := by
  classical
  let : DiscreteTopology (inhomogeneousOriginalTopRep.{0, v, w} G B) := B.property
  let s (b : inhomogeneousOriginalTopRep.{0, v, w} G B) := Classical.choose (hf b)
  intro c
  let h : C(Fin n → G, inhomogeneousOriginalTopRep.{0, v, w} G A) :=
    ⟨fun t => s (discreteCoefficientInhomogeneousEquiv.{v, w} G B n c t),
      (continuous_of_discreteTopology (f := s)).comp
        (discreteCoefficientInhomogeneousEquiv.{v, w} G B n c).continuous⟩
  refine ⟨(discreteCoefficientInhomogeneousEquiv.{v, w} G A n).symm h, ?_⟩
  apply (discreteCoefficientInhomogeneousEquiv.{v, w} G B n).injective
  ext t
  calc
    _ = discreteCoefficientHom f
        (discreteCoefficientInhomogeneousEquiv.{v, w} G A n
          ((discreteCoefficientInhomogeneousEquiv.{v, w} G A n).symm h) t) :=
      discreteCoefficientInhomogeneousEquiv_map f n _ t
    _ = discreteCoefficientHom f (h t) := by
      rw [AddEquiv.apply_symm_apply]
    _ = _ := Classical.choose_spec (hf _)

/-- Every actual kernel cochain is the image of an original cochain. -/
theorem discreteCoefficientCochain_lift_kernel
    {G : ProfiniteGrp.{v}}
    {A B C : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) (g : B ⟶ C)
    (hfg : (discreteCoefficientHom f).range = (discreteCoefficientHom g).ker)
    (n : ℕ) (c : ((discreteCoefficientCochainFunctor.{v, w} G).obj B).X n)
    (hc : ((discreteCoefficientCochainFunctor.{v, w} G).map g).f n c = 0) :
    ∃ b : ((discreteCoefficientCochainFunctor.{v, w} G).obj A).X n,
      ((discreteCoefficientCochainFunctor.{v, w} G).map f).f n b = c := by
  classical
  let : DiscreteTopology (inhomogeneousOriginalTopRep.{0, v, w} G B) := B.property
  have hpre (y : inhomogeneousOriginalTopRep.{0, v, w} G B)
      (hy : discreteCoefficientHom g y = 0) :
      ∃ x, discreteCoefficientHom f x = y := by
    have hmem : y ∈ (discreteCoefficientHom f).range := by
      rw [hfg]
      exact hy
    exact hmem
  let s (y : inhomogeneousOriginalTopRep.{0, v, w} G B) :=
    if hy : discreteCoefficientHom g y = 0 then Classical.choose (hpre y hy) else 0
  have hs (y : inhomogeneousOriginalTopRep.{0, v, w} G B)
      (hy : discreteCoefficientHom g y = 0) : discreteCoefficientHom f (s y) = y := by
    simp only [s, dite_eq_left hy]
    exact Classical.choose_spec (hpre y hy)
  have hval (t : Fin n → G) :
      discreteCoefficientHom g
        (discreteCoefficientInhomogeneousEquiv.{v, w} G B n c t) = 0 := by
    have heq := congrArg
      (fun d => discreteCoefficientInhomogeneousEquiv.{v, w} G C n d t) hc
    exact (discreteCoefficientInhomogeneousEquiv_map g n c t).symm.trans
      (heq.trans (congrArg (fun d => d t)
        (map_zero (discreteCoefficientInhomogeneousEquiv.{v, w} G C n))))
  let h : C(Fin n → G, inhomogeneousOriginalTopRep.{0, v, w} G A) :=
    ⟨fun t => s (discreteCoefficientInhomogeneousEquiv.{v, w} G B n c t),
      (continuous_of_discreteTopology (f := s)).comp
        (discreteCoefficientInhomogeneousEquiv.{v, w} G B n c).continuous⟩
  refine ⟨(discreteCoefficientInhomogeneousEquiv.{v, w} G A n).symm h, ?_⟩
  apply (discreteCoefficientInhomogeneousEquiv.{v, w} G B n).injective
  ext t
  calc
    _ = discreteCoefficientHom f
        (discreteCoefficientInhomogeneousEquiv.{v, w} G A n
          ((discreteCoefficientInhomogeneousEquiv.{v, w} G A n).symm h) t) :=
      discreteCoefficientInhomogeneousEquiv_map f n _ t
    _ = discreteCoefficientHom f (h t) := by rw [AddEquiv.apply_symm_apply]
    _ = _ := hs _ (hval t)

/-- The source condition is literal algebraic exactness of the original maps. -/
def DiscreteCoefficientExact {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)) : Prop :=
  Function.Injective (discreteCoefficientHom S.f) ∧
    (discreteCoefficientHom S.f).range = (discreteCoefficientHom S.g).ker ∧
      Function.Surjective (discreteCoefficientHom S.g)

/-- Construct the original short complex from its literal range/kernel equation. -/
def discreteCoefficientShortComplex {G : ProfiniteGrp.{v}}
    {A B C : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) (g : B ⟶ C)
    (hfg : (discreteCoefficientHom f).range = (discreteCoefficientHom g).ker) :
    ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G) :=
  ShortComplex.mk f g (by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext
    intro x
    have hx : discreteCoefficientHom f x ∈ (discreteCoefficientHom g).ker := by
      rw [← hfg]
      exact ⟨x, rfl⟩
    exact hx)

theorem discreteCoefficientShortComplex_exact {G : ProfiniteGrp.{v}}
    {A B C : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Injective (discreteCoefficientHom f))
    (hfg : (discreteCoefficientHom f).range = (discreteCoefficientHom g).ker)
    (hg : Function.Surjective (discreteCoefficientHom g)) :
    DiscreteCoefficientExact (discreteCoefficientShortComplex f g hfg) :=
  ⟨hf, hfg, hg⟩

/-- Literal coefficient exactness gives a genuine short exact sequence of the
original cochain complexes in the actual common abelian-group category. -/
theorem discreteCoefficientCochain_shortExact {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) :
    (S.map (discreteCoefficientCochainFunctor.{v, w} G)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ShortComplex.ShortExact.mk'
  · apply (ShortComplex.ab_exact_iff _).mpr
    intro c hc
    exact discreteCoefficientCochain_lift_kernel S.f S.g hS.2.1 n c hc
  · exact (AddCommGrpCat.mono_iff_injective _).mpr
      (discreteCoefficientCochain_injective S.f hS.1 n)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (discreteCoefficientCochain_surjective S.g hS.2.2 n)

/-- ONE actual common coefficient lift preserves all three original algebraic conditions. -/
theorem discreteCoefficientULiftFunctor_exact {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) :
    DiscreteCoefficientExact.{v, max z w}
      (S.map (discreteCoefficientULiftFunctor.{v, z, w} G)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    apply ULift.ext
    exact hS.1 (congrArg ULift.down h)
  · apply AddSubgroup.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      apply ULift.ext
      have hy : discreteCoefficientHom.{v, w} S.f y.down ∈
          (discreteCoefficientHom.{v, w} S.g).ker :=
        hS.2.1 ▸ ⟨y.down, rfl⟩
      exact hy
    · intro hx
      have hdown : discreteCoefficientHom.{v, w} S.g x.down = 0 :=
        congrArg ULift.down hx
      have hm : x.down ∈ (discreteCoefficientHom.{v, w} S.f).range :=
        hS.2.1.symm ▸ hdown
      obtain ⟨y, hy⟩ := hm
      refine ⟨ULift.up y, ?_⟩
      apply ULift.ext
      exact hy
  · intro y
    obtain ⟨x, hx⟩ := hS.2.2 y.down
    refine ⟨ULift.up x, ?_⟩
    apply ULift.ext
    exact hx

instance (G : ProfiniteGrp.{v}) (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, w} G n).Additive := by
  unfold discreteCoefficientCohomologyFunctor
  infer_instance

/-- The fixed homology comparison respects every original coefficient arrow. -/
theorem discreteCoefficientHomologyIso_naturality
    {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B) (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, w} G n).map f ≫
        (discreteCoefficientHomologyIso.{v, w} G B n).hom =
      (discreteCoefficientHomologyIso.{v, w} G A n).hom ≫
        HomologicalComplex.homologyMap
          ((discreteCoefficientCochainFunctor.{v, w} G).map f) n :=
  (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ)
    n discreteCoefficientForget.{max v w}).inv.naturality
      ((homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G)).map
        ((discreteCoefficientTopRepFunctor.{v, w} G).map f))

theorem discreteCoefficientHomologyIso_inv_naturality
    {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B) (n : ℕ) :
    (discreteCoefficientHomologyIso.{v, w} G A n).inv ≫
        (discreteCoefficientCohomologyFunctor.{v, w} G n).map f =
      HomologicalComplex.homologyMap
        ((discreteCoefficientCochainFunctor.{v, w} G).map f) n ≫
          (discreteCoefficientHomologyIso.{v, w} G B n).inv :=
  ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ)
    n discreteCoefficientForget.{max v w}).hom.naturality
      ((homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G)).map
        ((discreteCoefficientTopRepFunctor.{v, w} G).map f))).symm

theorem discreteCoefficientUpRel (n : ℕ) : (ComplexShape.up ℕ).Rel n (n + 1) := rfl

/-- The genuine connecting map on the existing continuous cohomology groups. -/
def discreteCoefficientConnecting {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, w} G n).obj S.X₃ ⟶
      (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).obj S.X₁ :=
  (discreteCoefficientHomologyIso.{v, w} G S.X₃ n).hom ≫
    (discreteCoefficientCochain_shortExact S hS).δ n (n + 1) (discreteCoefficientUpRel n) ≫
      (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1)).inv

/-- Its normalization is the actual common-Ab homology connector. -/
theorem discreteCoefficientConnecting_comparison {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    discreteCoefficientConnecting S hS n ≫
        (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1)).hom =
      (discreteCoefficientHomologyIso.{v, w} G S.X₃ n).hom ≫
        (discreteCoefficientCochain_shortExact S hS).δ n (n + 1) (discreteCoefficientUpRel n) := by
  simp only [discreteCoefficientConnecting, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

theorem discreteCoefficient_comp_connecting {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, w} G n).map S.g ≫
      discreteCoefficientConnecting S hS n = 0 := by
  have hz : HomologicalComplex.homologyMap
      ((discreteCoefficientCochainFunctor.{v, w} G).map S.g) n ≫
        (discreteCoefficientCochain_shortExact S hS).δ n (n + 1)
          (discreteCoefficientUpRel n) = 0 :=
    (discreteCoefficientCochain_shortExact S hS).comp_δ n (n + 1)
      (discreteCoefficientUpRel n)
  unfold discreteCoefficientConnecting
  calc
    _ = (discreteCoefficientHomologyIso.{v, w} G S.X₂ n).hom ≫
        (HomologicalComplex.homologyMap
          ((discreteCoefficientCochainFunctor.{v, w} G).map S.g) n ≫
            (discreteCoefficientCochain_shortExact S hS).δ n (n + 1)
              (discreteCoefficientUpRel n)) ≫
        (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1)).inv := by
      rw [← Category.assoc, discreteCoefficientHomologyIso_naturality S.g n]
      simp only [Category.assoc]
    _ = 0 := by rw [hz]; simp

theorem discreteCoefficient_connecting_comp {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    discreteCoefficientConnecting S hS n ≫
      (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map S.f = 0 := by
  have hz : (discreteCoefficientCochain_shortExact S hS).δ n (n + 1)
      (discreteCoefficientUpRel n) ≫ HomologicalComplex.homologyMap
        ((discreteCoefficientCochainFunctor.{v, w} G).map S.f) (n + 1) = 0 :=
    (discreteCoefficientCochain_shortExact S hS).δ_comp n (n + 1)
      (discreteCoefficientUpRel n)
  unfold discreteCoefficientConnecting
  calc
    _ = (discreteCoefficientHomologyIso.{v, w} G S.X₃ n).hom ≫
        ((discreteCoefficientCochain_shortExact S hS).δ n (n + 1)
          (discreteCoefficientUpRel n) ≫ HomologicalComplex.homologyMap
            ((discreteCoefficientCochainFunctor.{v, w} G).map S.f) (n + 1)) ≫
        (discreteCoefficientHomologyIso.{v, w} G S.X₂ (n + 1)).inv := by
      simp only [Category.assoc]
      rw [discreteCoefficientHomologyIso_inv_naturality S.f (n + 1)]
    _ = 0 := by rw [hz]; simp

/-- Exactness at every first-to-second coefficient cohomology map. -/
theorem discreteCoefficient_cohomology_exact₂ {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    (S.map (discreteCoefficientCohomologyFunctor.{v, w} G n)).Exact := by
  let T := (S.map (discreteCoefficientCochainFunctor.{v, w} G)).map
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max v w} (ComplexShape.up ℕ) n)
  let e : S.map (discreteCoefficientCohomologyFunctor.{v, w} G n) ≅ T :=
    ShortComplex.isoMk
      (discreteCoefficientHomologyIso.{v, w} G S.X₁ n)
      (discreteCoefficientHomologyIso.{v, w} G S.X₂ n)
      (discreteCoefficientHomologyIso.{v, w} G S.X₃ n)
      (discreteCoefficientHomologyIso_naturality S.f n).symm
      (discreteCoefficientHomologyIso_naturality S.g n).symm
  exact (ShortComplex.exact_iff_of_iso e).mpr
    ((discreteCoefficientCochain_shortExact S hS).homology_exact₂ n)

/-- Exactness at every third-term cohomology, against the actual boundary. -/
theorem discreteCoefficient_cohomology_exact₃ {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    (ShortComplex.mk ((discreteCoefficientCohomologyFunctor.{v, w} G n).map S.g)
      (discreteCoefficientConnecting S hS n)
        (discreteCoefficient_comp_connecting S hS n)).Exact := by
  let T := ShortComplex.mk
    (HomologicalComplex.homologyMap ((discreteCoefficientCochainFunctor.{v, w} G).map S.g) n)
    ((discreteCoefficientCochain_shortExact S hS).δ n (n + 1) (discreteCoefficientUpRel n))
    ((discreteCoefficientCochain_shortExact S hS).comp_δ n (n + 1) (discreteCoefficientUpRel n))
  let e : ShortComplex.mk _ _ (discreteCoefficient_comp_connecting S hS n) ≅ T :=
    ShortComplex.isoMk
      (discreteCoefficientHomologyIso.{v, w} G S.X₂ n)
      (discreteCoefficientHomologyIso.{v, w} G S.X₃ n)
      (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1))
      (discreteCoefficientHomologyIso_naturality S.g n).symm
      (discreteCoefficientConnecting_comparison S hS n).symm
  exact (ShortComplex.exact_iff_of_iso e).mpr
    ((discreteCoefficientCochain_shortExact S hS).homology_exact₃
      n (n + 1) (discreteCoefficientUpRel n))

/-- Exactness at every positive first-term cohomology, after the actual boundary. -/
theorem discreteCoefficient_cohomology_exact₁ {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    (ShortComplex.mk (discreteCoefficientConnecting S hS n)
      ((discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map S.f)
      (discreteCoefficient_connecting_comp S hS n)).Exact := by
  let T := ShortComplex.mk
    ((discreteCoefficientCochain_shortExact S hS).δ n (n + 1) (discreteCoefficientUpRel n))
    (HomologicalComplex.homologyMap
      ((discreteCoefficientCochainFunctor.{v, w} G).map S.f) (n + 1))
    ((discreteCoefficientCochain_shortExact S hS).δ_comp n (n + 1) (discreteCoefficientUpRel n))
  let e : ShortComplex.mk _ _ (discreteCoefficient_connecting_comp S hS n) ≅ T :=
    ShortComplex.isoMk
      (discreteCoefficientHomologyIso.{v, w} G S.X₃ n)
      (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1))
      (discreteCoefficientHomologyIso.{v, w} G S.X₂ (n + 1))
      (discreteCoefficientConnecting_comparison S hS n).symm
      (discreteCoefficientHomologyIso_naturality S.f (n + 1)).symm
  exact (ShortComplex.exact_iff_of_iso e).mpr
    ((discreteCoefficientCochain_shortExact S hS).homology_exact₁
      n (n + 1) (discreteCoefficientUpRel n))

/-- The initial zero in the long exact sequence is justified by an actual monomorphism. -/
theorem discreteCoefficient_cohomology_mono_zero {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) :
    Mono ((discreteCoefficientCohomologyFunctor.{v, w} G 0).map S.f) := by
  let : Mono (((discreteCoefficientCochainFunctor.{v, w} G).map S.f).f 0) :=
    (AddCommGrpCat.mono_iff_injective _).mpr
      (discreteCoefficientCochain_injective S.f hS.1 0)
  have h : Mono (HomologicalComplex.homologyMap
      ((discreteCoefficientCochainFunctor.{v, w} G).map S.f) 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ 0 (by
      intro i
      simp [ComplexShape.up])
  let e : Arrow.mk ((discreteCoefficientCohomologyFunctor.{v, w} G 0).map S.f) ≅
      Arrow.mk (HomologicalComplex.homologyMap
        ((discreteCoefficientCochainFunctor.{v, w} G).map S.f) 0) := Arrow.isoMk
    (discreteCoefficientHomologyIso.{v, w} G S.X₁ 0)
    (discreteCoefficientHomologyIso.{v, w} G S.X₂ 0)
    (discreteCoefficientHomologyIso_naturality S.f 0).symm
  exact ((MorphismProperty.monomorphisms AddCommGrpCat.{max v w}).arrow_mk_iso_iff e).mpr h

/-- The degree-zero comparison is literally the existing identity-evaluation isomorphism. -/
def discreteCoefficientZeroIso (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G) :
    (discreteCoefficientCohomologyFunctor.{v, w} G 0).obj A ≅
      discreteCoefficientForget.{max v w}.obj
        (TopRep.invariants (inhomogeneousOriginalTopRep.{0, v, w} G A)) :=
  discreteCoefficientForget.{max v w}.mapIso
    (ContinuousCohomology.zeroIso (inhomogeneousOriginalTopRep.{0, v, w} G A))

/-- The original group and coefficient maps act on the same algebraic cochains.
Both original group universes are retained; the coefficient rank is their common maximum. -/
def discreteCoefficientGroupCochainMap
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {A : DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G}
    {B : DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H}
    (φ : H →ₜ* G)
    (f : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G A) ⟶
      inhomogeneousOriginalTopRep.{0, z, max v w} H B) :
    (discreteCoefficientCochainFunctor.{v, max z w} G).obj A ⟶
      (discreteCoefficientCochainFunctor.{z, max v w} H).obj B :=
  (discreteCoefficientForget.{max v (max z w)}.mapHomologicalComplex
    (ComplexShape.up ℕ)).map (nativeGroupCoefficientCochainsMap.{0, v, z, w} φ f)

theorem discreteCoefficientHomologyIso_group_naturality
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {A : DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G}
    {B : DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H}
    (φ : H →ₜ* G)
    (f : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G A) ⟶
      inhomogeneousOriginalTopRep.{0, z, max v w} H B) (n : ℕ) :
    discreteCoefficientForget.{max v (max z w)}.map
        (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f n) ≫
        (discreteCoefficientHomologyIso.{z, max v w} H B n).hom =
      (discreteCoefficientHomologyIso.{v, max z w} G A n).hom ≫
        HomologicalComplex.homologyMap (discreteCoefficientGroupCochainMap.{v, z, w} φ f) n :=
  (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n
    discreteCoefficientForget.{max v (max z w)}).inv.naturality
      (nativeGroupCoefficientCochainsMap.{0, v, z, w} φ f)

theorem discreteCoefficientHomologyIso_inv_group_naturality
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {A : DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G}
    {B : DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H}
    (φ : H →ₜ* G)
    (f : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G A) ⟶
      inhomogeneousOriginalTopRep.{0, z, max v w} H B) (n : ℕ) :
    (discreteCoefficientHomologyIso.{v, max z w} G A n).inv ≫
        discreteCoefficientForget.{max v (max z w)}.map
          (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f n) =
      HomologicalComplex.homologyMap (discreteCoefficientGroupCochainMap.{v, z, w} φ f) n ≫
        (discreteCoefficientHomologyIso.{z, max v w} H B n).inv :=
  ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n
    discreteCoefficientForget.{max v (max z w)}).hom.naturality
      (nativeGroupCoefficientCochainsMap.{0, v, z, w} φ f)).symm

/-- A morphism of the ORIGINAL coefficient sequences. Its fields concern only
the original arrows; cochain, cohomology and connecting-map squares are conclusions. -/
structure DiscreteCoefficientGroupHom
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G))
    (T : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H))
    (φ : H →ₜ* G) where
  /-- The map on the first terms, from `S.X₁` restricted along `φ` to `T.X₁`. -/
  τ₁ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G S.X₁) ⟶
    inhomogeneousOriginalTopRep.{0, z, max v w} H T.X₁
  /-- The map on the second terms, from `S.X₂` restricted along `φ` to `T.X₂`. -/
  τ₂ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G S.X₂) ⟶
    inhomogeneousOriginalTopRep.{0, z, max v w} H T.X₂
  /-- The map on the third terms, from `S.X₃` restricted along `φ` to `T.X₃`. -/
  τ₃ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G S.X₃) ⟶
    inhomogeneousOriginalTopRep.{0, z, max v w} H T.X₃
  comm₁₂ : τ₁ ≫ (discreteCoefficientTopRepFunctor.{z, max v w} H).map T.f =
    (TopRep.resFunctor (φ : H →* G)).map
      ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.f) ≫ τ₂
  comm₂₃ : τ₂ ≫ (discreteCoefficientTopRepFunctor.{z, max v w} H).map T.g =
    (TopRep.resFunctor (φ : H →* G)).map
      ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.g) ≫ τ₃

/-- An original diagram BEFORE coefficient enlargement, on the native carriers. -/
structure DiscreteCoefficientNativeGroupHom
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (T : ShortComplex (DiscreteContAction (TopModuleCat.{max z w} ℤ) H))
    (φ : H →ₜ* G) where
  /-- The `φ`-intertwiner on the first terms, from `S.X₁` to `T.X₁`. -/
  τ₁ : nativeCoefficientIntertwiner.{0, v, z, w}
    (inhomogeneousOriginalTopRep.{0, v, w} G S.X₁)
    (inhomogeneousOriginalTopRep.{0, z, w} H T.X₁) φ
  /-- The `φ`-intertwiner on the second terms, from `S.X₂` to `T.X₂`. -/
  τ₂ : nativeCoefficientIntertwiner.{0, v, z, w}
    (inhomogeneousOriginalTopRep.{0, v, w} G S.X₂)
    (inhomogeneousOriginalTopRep.{0, z, w} H T.X₂) φ
  /-- The `φ`-intertwiner on the third terms, from `S.X₃` to `T.X₃`. -/
  τ₃ : nativeCoefficientIntertwiner.{0, v, z, w}
    (inhomogeneousOriginalTopRep.{0, v, w} G S.X₃)
    (inhomogeneousOriginalTopRep.{0, z, w} H T.X₃) φ
  comm₁₂ (x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₁) :
    discreteCoefficientHom.{z, w} T.f (τ₁ x) = τ₂ (discreteCoefficientHom.{v, w} S.f x)
  comm₂₃ (x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₂) :
    discreteCoefficientHom.{z, w} T.g (τ₂ x) = τ₃ (discreteCoefficientHom.{v, w} S.g x)

/-- The same native diagram becomes a genuine common-rank diagram by ONE lift per carrier. -/
@[nolint defsWithUnderscore] -- name recorded in the Bloch–Kato validation audit
def discreteCoefficientNativeGroupHom_ulift
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)}
    {T : ShortComplex (DiscreteContAction (TopModuleCat.{max z w} ℤ) H)}
    {φ : H →ₜ* G} (f : DiscreteCoefficientNativeGroupHom.{v, z, w} S T φ) :
    DiscreteCoefficientGroupHom.{v, z, w}
      (S.map (discreteCoefficientULiftFunctor.{v, z, w} G))
      (T.map (discreteCoefficientULiftFunctor.{z, v, w} H)) φ where
  τ₁ := nativeULiftGroupIntertwiner.{0, v, z, w} (φ : H →* G) f.τ₁
  τ₂ := nativeULiftGroupIntertwiner.{0, v, z, w} (φ : H →* G) f.τ₂
  τ₃ := nativeULiftGroupIntertwiner.{0, v, z, w} (φ : H →* G) f.τ₃
  comm₁₂ := nativeULiftGroupIntertwiner_coefficient_square.{0, v, z, w}
    (φ : H →* G) ((discreteCoefficientTopRepFunctor.{v, w} G).map S.f)
    ((discreteCoefficientTopRepFunctor.{z, w} H).map T.f) f.τ₁ f.τ₂ f.comm₁₂
  comm₂₃ := nativeULiftGroupIntertwiner_coefficient_square.{0, v, z, w}
    (φ : H →* G) ((discreteCoefficientTopRepFunctor.{v, w} G).map S.g)
    ((discreteCoefficientTopRepFunctor.{z, w} H).map T.g) f.τ₂ f.τ₃ f.comm₂₃

/-- The original coefficient diagram gives a real diagram of actual cochain complexes. -/
abbrev discreteCoefficientGroupSequenceMap
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {S : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G)}
    {T : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H)}
    {φ : H →ₜ* G} (f : DiscreteCoefficientGroupHom.{v, z, w} S T φ) :
    S.map (discreteCoefficientCochainFunctor.{v, max z w} G) ⟶
      T.map (discreteCoefficientCochainFunctor.{z, max v w} H) :=
  ShortComplex.homMk (discreteCoefficientGroupCochainMap.{v, z, w} φ f.τ₁)
    (discreteCoefficientGroupCochainMap.{v, z, w} φ f.τ₂)
    (discreteCoefficientGroupCochainMap.{v, z, w} φ f.τ₃)
    (by
      let F := discreteCoefficientForget.{max v (max z w)}.mapHomologicalComplex
        (ComplexShape.up ℕ)
      have h := congrArg F.map
        (homogeneousGroupCoefficientSquare.{0, v, z, w} φ
          ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.f)
          ((discreteCoefficientTopRepFunctor.{z, max v w} H).map T.f)
          f.τ₁ f.τ₂ f.comm₁₂)
      exact (F.map_comp (nativeGroupCoefficientCochainsMap.{0, v, z, w} φ f.τ₁)
        ((homogeneousCochainsFunctor.{0, z, max v w} (k := ℤ) (G := H)).map
          ((discreteCoefficientTopRepFunctor.{z, max v w} H).map T.f))).symm.trans
        (h.trans (F.map_comp
          ((homogeneousCochainsFunctor.{0, v, max z w} (k := ℤ) (G := G)).map
            ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.f))
          (nativeGroupCoefficientCochainsMap.{0, v, z, w} φ f.τ₂))))
    (by
      let F := discreteCoefficientForget.{max v (max z w)}.mapHomologicalComplex
        (ComplexShape.up ℕ)
      have h := congrArg F.map
        (homogeneousGroupCoefficientSquare.{0, v, z, w} φ
          ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.g)
          ((discreteCoefficientTopRepFunctor.{z, max v w} H).map T.g)
          f.τ₂ f.τ₃ f.comm₂₃)
      exact (F.map_comp (nativeGroupCoefficientCochainsMap.{0, v, z, w} φ f.τ₂)
        ((homogeneousCochainsFunctor.{0, z, max v w} (k := ℤ) (G := H)).map
          ((discreteCoefficientTopRepFunctor.{z, max v w} H).map T.g))).symm.trans
        (h.trans (F.map_comp
          ((homogeneousCochainsFunctor.{0, v, max z w} (k := ℤ) (G := G)).map
            ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.g))
          (nativeGroupCoefficientCochainsMap.{0, v, z, w} φ f.τ₃))))


/-- Full simultaneous group/coefficient naturality of the SAME actual connecting maps. -/
theorem discreteCoefficientConnecting_group_naturality
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {S : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G)}
    {T : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H)}
    (hS : DiscreteCoefficientExact.{v, max z w} S)
    (hT : DiscreteCoefficientExact.{z, max v w} T)
    {φ : H →ₜ* G} (f : DiscreteCoefficientGroupHom.{v, z, w} S T φ) (n : ℕ) :
    discreteCoefficientConnecting.{v, max z w} S hS n ≫
        discreteCoefficientForget.{max v (max z w)}.map
          (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₁ (n + 1)) =
      discreteCoefficientForget.{max v (max z w)}.map
        (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₃ n) ≫
          discreteCoefficientConnecting.{z, max v w} T hT n := by
  let A := AddCommGrpCat.{max v (max z w)}
  let F : TopModuleCat.{max v (max z w)} ℤ ⥤ A :=
    discreteCoefficientForget.{max v (max z w)}
  let CS : ShortComplex (CochainComplex A ℕ) :=
    S.map (discreteCoefficientCochainFunctor.{v, max z w} G)
  let CT : ShortComplex (CochainComplex A ℕ) :=
    T.map (discreteCoefficientCochainFunctor.{z, max v w} H)
  let hCS : CS.ShortExact := discreteCoefficientCochain_shortExact.{v, max z w} S hS
  let hCT : CT.ShortExact := discreteCoefficientCochain_shortExact.{z, max v w} T hT
  let eS₁ : (discreteCoefficientCohomologyFunctor.{v, max z w} G (n + 1)).obj S.X₁ ≅
      CS.X₁.homology (n + 1) := discreteCoefficientHomologyIso.{v, max z w} G S.X₁ (n + 1)
  let eS₃ : (discreteCoefficientCohomologyFunctor.{v, max z w} G n).obj S.X₃ ≅
      CS.X₃.homology n := discreteCoefficientHomologyIso.{v, max z w} G S.X₃ n
  let eT₁ : (discreteCoefficientCohomologyFunctor.{z, max v w} H (n + 1)).obj T.X₁ ≅
      CT.X₁.homology (n + 1) := discreteCoefficientHomologyIso.{z, max v w} H T.X₁ (n + 1)
  let eT₃ : (discreteCoefficientCohomologyFunctor.{z, max v w} H n).obj T.X₃ ≅
      CT.X₃.homology n := discreteCoefficientHomologyIso.{z, max v w} H T.X₃ n
  let a₁ : (discreteCoefficientCohomologyFunctor.{v, max z w} G (n + 1)).obj S.X₁ ⟶
      (discreteCoefficientCohomologyFunctor.{z, max v w} H (n + 1)).obj T.X₁ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₁ (n + 1))
  let a₃ : (discreteCoefficientCohomologyFunctor.{v, max z w} G n).obj S.X₃ ⟶
      (discreteCoefficientCohomologyFunctor.{z, max v w} H n).obj T.X₃ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₃ n)
  let b₁ : CS.X₁.homology (n + 1) ⟶ CT.X₁.homology (n + 1) :=
    HomologicalComplex.homologyMap (discreteCoefficientGroupCochainMap.{v, z, w} φ f.τ₁) (n + 1)
  let b₃ : CS.X₃.homology n ⟶ CT.X₃.homology n :=
    HomologicalComplex.homologyMap (discreteCoefficientGroupCochainMap.{v, z, w} φ f.τ₃) n
  let δS : CS.X₃.homology n ⟶ CS.X₁.homology (n + 1) :=
    hCS.δ n (n + 1) (discreteCoefficientUpRel n)
  let δT : CT.X₃.homology n ⟶ CT.X₁.homology (n + 1) :=
    hCT.δ n (n + 1) (discreteCoefficientUpRel n)
  have hδ : δS ≫ b₁ = b₃ ≫ δT :=
    HomologicalComplex.HomologySequence.δ_naturality
      (discreteCoefficientGroupSequenceMap.{v, z, w} f) hCS hCT
      n (n + 1) (discreteCoefficientUpRel n)
  have h₁ : eS₁.inv ≫ a₁ = b₁ ≫ eT₁.inv :=
    discreteCoefficientHomologyIso_inv_group_naturality.{v, z, w} φ f.τ₁ (n + 1)
  have h₃ : a₃ ≫ eT₃.hom = eS₃.hom ≫ b₃ :=
    discreteCoefficientHomologyIso_group_naturality.{v, z, w} φ f.τ₃ n
  change (eS₃.hom ≫ δS ≫ eS₁.inv) ≫ a₁ = a₃ ≫ (eT₃.hom ≫ δT ≫ eT₁.inv)
  exact conjugatedBoundary_naturality eS₁ eS₃ eT₁ eT₃ a₁ a₃ b₁ b₃ δS δT h₁ h₃ hδ

/-- Naturality for every morphism of the original literal coefficient sequences. -/
theorem discreteCoefficientConnecting_naturality
    {G : ProfiniteGrp.{v}}
    {S T : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)}
    (f : S ⟶ T) (hS : DiscreteCoefficientExact.{v, w} S)
    (hT : DiscreteCoefficientExact.{v, w} T) (n : ℕ) :
    discreteCoefficientConnecting.{v, w} S hS n ≫
        (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.τ₁ =
      (discreteCoefficientCohomologyFunctor.{v, w} G n).map f.τ₃ ≫
        discreteCoefficientConnecting.{v, w} T hT n := by
  have hδ :
      (discreteCoefficientCochain_shortExact.{v, w} S hS).δ n (n + 1)
          (discreteCoefficientUpRel n) ≫ HomologicalComplex.homologyMap
          ((discreteCoefficientCochainFunctor.{v, w} G).map f.τ₁) (n + 1) =
      HomologicalComplex.homologyMap
          ((discreteCoefficientCochainFunctor.{v, w} G).map f.τ₃) n ≫
        (discreteCoefficientCochain_shortExact.{v, w} T hT).δ n (n + 1)
          (discreteCoefficientUpRel n) :=
    HomologicalComplex.HomologySequence.δ_naturality
      ((discreteCoefficientCochainFunctor.{v, w} G).mapShortComplex.map f)
      (discreteCoefficientCochain_shortExact.{v, w} S hS)
      (discreteCoefficientCochain_shortExact.{v, w} T hT)
      n (n + 1) (discreteCoefficientUpRel n)
  exact conjugatedBoundary_naturality
    (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1))
    (discreteCoefficientHomologyIso.{v, w} G S.X₃ n)
    (discreteCoefficientHomologyIso.{v, w} G T.X₁ (n + 1))
    (discreteCoefficientHomologyIso.{v, w} G T.X₃ n)
    ((discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.τ₁)
    ((discreteCoefficientCohomologyFunctor.{v, w} G n).map f.τ₃)
    (HomologicalComplex.homologyMap
      ((discreteCoefficientCochainFunctor.{v, w} G).map f.τ₁) (n + 1))
    (HomologicalComplex.homologyMap
      ((discreteCoefficientCochainFunctor.{v, w} G).map f.τ₃) n)
    ((discreteCoefficientCochain_shortExact.{v, w} S hS).δ n (n + 1)
      (discreteCoefficientUpRel n))
    ((discreteCoefficientCochain_shortExact.{v, w} T hT).δ n (n + 1)
      (discreteCoefficientUpRel n))
    (discreteCoefficientHomologyIso_inv_naturality.{v, w} f.τ₁ (n + 1))
    (discreteCoefficientHomologyIso_naturality.{v, w} f.τ₃ n) hδ

/-- The actual adjacent-degree sequence on the EXISTING continuous cohomology groups. -/
abbrev discreteCoefficientLongSequence {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{max v w} 5 :=
  ComposableArrows.mk₅
    ((discreteCoefficientCohomologyFunctor.{v, w} G n).map S.f)
    ((discreteCoefficientCohomologyFunctor.{v, w} G n).map S.g)
    (discreteCoefficientConnecting.{v, w} S hS n)
    ((discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map S.f)
    ((discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map S.g)

/-- The SAME canonical homology comparisons identify all six terms and five arrows. -/
def discreteCoefficientLongSequenceIso {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) (n : ℕ) :
    discreteCoefficientLongSequence.{v, w} S hS n ≅
      HomologicalComplex.HomologySequence.composableArrows₅
        (discreteCoefficientCochain_shortExact.{v, w} S hS)
        n (n + 1) (discreteCoefficientUpRel n) :=
  ComposableArrows.isoMk₅
    (discreteCoefficientHomologyIso.{v, w} G S.X₁ n)
    (discreteCoefficientHomologyIso.{v, w} G S.X₂ n)
    (discreteCoefficientHomologyIso.{v, w} G S.X₃ n)
    (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1))
    (discreteCoefficientHomologyIso.{v, w} G S.X₂ (n + 1))
    (discreteCoefficientHomologyIso.{v, w} G S.X₃ (n + 1))
    (discreteCoefficientHomologyIso_naturality.{v, w} S.f n)
    (discreteCoefficientHomologyIso_naturality.{v, w} S.g n)
    (discreteCoefficientConnecting_comparison.{v, w} S hS n)
    (discreteCoefficientHomologyIso_naturality.{v, w} S.f (n + 1))
    (discreteCoefficientHomologyIso_naturality.{v, w} S.g (n + 1))

/-- Exactness of every adjacent-degree segment of the full original sequence. -/
theorem discreteCoefficientLongSequence_exact {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) (n : ℕ) :
    (discreteCoefficientLongSequence.{v, w} S hS n).Exact :=
  (ComposableArrows.exact_iff_of_iso
    (discreteCoefficientLongSequenceIso.{v, w} S hS n)).mpr
      (HomologicalComplex.HomologySequence.composableArrows₅_exact
        (discreteCoefficientCochain_shortExact.{v, w} S hS)
        n (n + 1) (discreteCoefficientUpRel n))

/-- Original coefficient sequences with the literal underlying exactness condition. -/
def discreteCoefficientExactProperty (G : ProfiniteGrp.{v}) :
    ObjectProperty (ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)) :=
  DiscreteCoefficientExact.{v, w}

/-- The full subcategory of exact original coefficient sequences. -/
abbrev DiscreteCoefficientExactSequences (G : ProfiniteGrp.{v}) :=
  (discreteCoefficientExactProperty.{v, w} G).FullSubcategory

/-- The complete sequence is functorial in EVERY original coefficient sequence morphism. -/
def discreteCoefficientLongSequenceFunctor (G : ProfiniteGrp.{v}) (n : ℕ) :
    DiscreteCoefficientExactSequences.{v, w} G ⥤
      ComposableArrows AddCommGrpCat.{max v w} 5 where
  obj S := discreteCoefficientLongSequence.{v, w} S.obj S.property n
  map {S T} f :=
    ComposableArrows.homMk₅
      ((discreteCoefficientCohomologyFunctor.{v, w} G n).map f.hom.τ₁)
      ((discreteCoefficientCohomologyFunctor.{v, w} G n).map f.hom.τ₂)
      ((discreteCoefficientCohomologyFunctor.{v, w} G n).map f.hom.τ₃)
      ((discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.hom.τ₁)
      ((discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.hom.τ₂)
      ((discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.hom.τ₃)
      (by
        let F := discreteCoefficientCohomologyFunctor.{v, w} G n
        exact (F.map_comp S.obj.f f.hom.τ₂).symm.trans
          ((congrArg F.map f.hom.comm₁₂).symm.trans (F.map_comp f.hom.τ₁ T.obj.f)))
      (by
        let F := discreteCoefficientCohomologyFunctor.{v, w} G n
        exact (F.map_comp S.obj.g f.hom.τ₃).symm.trans
          ((congrArg F.map f.hom.comm₂₃).symm.trans (F.map_comp f.hom.τ₂ T.obj.g)))
      (discreteCoefficientConnecting_naturality.{v, w} f.hom S.property T.property n)
      (by
        let F := discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)
        exact (F.map_comp S.obj.f f.hom.τ₂).symm.trans
          ((congrArg F.map f.hom.comm₁₂).symm.trans (F.map_comp f.hom.τ₁ T.obj.f)))
      (by
        let F := discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)
        exact (F.map_comp S.obj.g f.hom.τ₃).symm.trans
          ((congrArg F.map f.hom.comm₂₃).symm.trans (F.map_comp f.hom.τ₂ T.obj.g)))
  map_id S := by
    apply ComposableArrows.hom_ext₅
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G n).map_id S.obj.X₁
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G n).map_id S.obj.X₂
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G n).map_id S.obj.X₃
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map_id S.obj.X₁
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map_id S.obj.X₂
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map_id S.obj.X₃
  map_comp f g := by
    apply ComposableArrows.hom_ext₅
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G n).map_comp f.hom.τ₁ g.hom.τ₁
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G n).map_comp f.hom.τ₂ g.hom.τ₂
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G n).map_comp f.hom.τ₃ g.hom.τ₃
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map_comp f.hom.τ₁ g.hom.τ₁
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map_comp f.hom.τ₂ g.hom.τ₂
    · exact (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map_comp f.hom.τ₃ g.hom.τ₃

/-- Every original group/coefficient square commutes on the existing common cohomology. -/
theorem discreteCoefficientGroupCohomologySquare
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {A₁ A₂ : DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G}
    {B₁ B₂ : DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H}
    (φ : H →ₜ* G) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (ψ₁ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G A₁) ⟶
      inhomogeneousOriginalTopRep.{0, z, max v w} H B₁)
    (ψ₂ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G A₂) ⟶
      inhomogeneousOriginalTopRep.{0, z, max v w} H B₂)
    (hψ : ψ₁ ≫ (discreteCoefficientTopRepFunctor.{z, max v w} H).map b =
      (TopRep.resFunctor (φ : H →* G)).map
        ((discreteCoefficientTopRepFunctor.{v, max z w} G).map a) ≫ ψ₂) (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, max z w} G n).map a ≫
        discreteCoefficientForget.{max v (max z w)}.map
          (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ ψ₂ n) =
      discreteCoefficientForget.{max v (max z w)}.map
          (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ ψ₁ n) ≫
        (discreteCoefficientCohomologyFunctor.{z, max v w} H n).map b := by
  let F := discreteCoefficientForget.{max v (max z w)}
  let a' := (discreteCoefficientTopRepFunctor.{v, max z w} G).map a
  let b' := (discreteCoefficientTopRepFunctor.{z, max v w} H).map b
  have h := congrArg F.map
    (homogeneousGroupCoefficientCohomologySquare.{0, v, z, w} φ a' b' ψ₁ ψ₂ hψ n)
  exact (F.map_comp
    (HomologicalComplex.homologyMap
      ((homogeneousCochainsFunctor.{0, v, max z w} (k := ℤ) (G := G)).map a') n)
    (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ ψ₂ n)).symm.trans
    (h.symm.trans (F.map_comp
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ ψ₁ n)
      (HomologicalComplex.homologyMap
        ((homogeneousCochainsFunctor.{0, z, max v w} (k := ℤ) (G := H)).map b') n)))

/-- The common-model H0 square uses the same identity evaluation and original invariants map. -/
theorem discreteCoefficientGroupZeroIso_naturality
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {A : DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G}
    {B : DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H}
    (φ : H →ₜ* G)
    (f : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G A) ⟶
      inhomogeneousOriginalTopRep.{0, z, max v w} H B) :
    discreteCoefficientForget.{max v (max z w)}.map
        (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f 0) ≫
      (discreteCoefficientZeroIso.{z, max v w} H B).hom =
    (discreteCoefficientZeroIso.{v, max z w} G A).hom ≫
      discreteCoefficientForget.{max v (max z w)}.map
        (TopRep.invariantsResMap (φ : H →* G) f) := by
  let F := discreteCoefficientForget.{max v (max z w)}
  let X := inhomogeneousOriginalTopRep.{0, v, max z w} G A
  let Y := inhomogeneousOriginalTopRep.{0, z, max v w} H B
  have h := congrArg F.map (nativeGroupCoefficientZeroIso_naturality.{0, v, z, w} φ f)
  exact (F.map_comp (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f 0)
    (ContinuousCohomology.zeroIso Y).hom).symm.trans
    (h.trans (F.map_comp (ContinuousCohomology.zeroIso X).hom
      (TopRep.invariantsResMap (φ : H →* G) f)))

private def longSequenceHomOfSquares {C : Type a} [Category.{b} C]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : C}
    (s₀ : X₀ ⟶ X₁) (s₁ : X₁ ⟶ X₂) (s₂ : X₂ ⟶ X₃)
    (s₃ : X₃ ⟶ X₄) (s₄ : X₄ ⟶ X₅)
    (t₀ : Y₀ ⟶ Y₁) (t₁ : Y₁ ⟶ Y₂) (t₂ : Y₂ ⟶ Y₃)
    (t₃ : Y₃ ⟶ Y₄) (t₄ : Y₄ ⟶ Y₅)
    (a₀ : X₀ ⟶ Y₀) (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂)
    (a₃ : X₃ ⟶ Y₃) (a₄ : X₄ ⟶ Y₄) (a₅ : X₅ ⟶ Y₅)
    (w₀ : s₀ ≫ a₁ = a₀ ≫ t₀) (w₁ : s₁ ≫ a₂ = a₁ ≫ t₁)
    (w₂ : s₂ ≫ a₃ = a₂ ≫ t₂) (w₃ : s₃ ≫ a₄ = a₃ ≫ t₃)
    (w₄ : s₄ ≫ a₅ = a₄ ≫ t₄) :
    ComposableArrows.mk₅ s₀ s₁ s₂ s₃ s₄ ⟶
      ComposableArrows.mk₅ t₀ t₁ t₂ t₃ t₄ :=
  ComposableArrows.homMk₅
    (f := ComposableArrows.mk₅ s₀ s₁ s₂ s₃ s₄)
    (g := ComposableArrows.mk₅ t₀ t₁ t₂ t₃ t₄)
    a₀ a₁ a₂ a₃ a₄ a₅ w₀ w₁ w₂ w₃ w₄

/-- All six components and every square are the original native group/coefficient maps. -/
def discreteCoefficientGroupLongSequenceMap
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {S : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G)}
    {T : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H)}
    (hS : DiscreteCoefficientExact.{v, max z w} S)
    (hT : DiscreteCoefficientExact.{z, max v w} T)
    {φ : H →ₜ* G} (f : DiscreteCoefficientGroupHom.{v, z, w} S T φ) (n : ℕ) :
    discreteCoefficientLongSequence.{v, max z w} S hS n ⟶
      discreteCoefficientLongSequence.{z, max v w} T hT n :=
  let C := AddCommGrpCat.{max v (max z w)}
  let GS := DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G
  let HT := DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H
  let F : TopModuleCat.{max v (max z w)} ℤ ⥤ C :=
    discreteCoefficientForget.{max v (max z w)}
  let HS₀ : GS ⥤ C := discreteCoefficientCohomologyFunctor.{v, max z w} G n
  let HS₁ : GS ⥤ C := discreteCoefficientCohomologyFunctor.{v, max z w} G (n + 1)
  let HT₀ : HT ⥤ C := discreteCoefficientCohomologyFunctor.{z, max v w} H n
  let HT₁ : HT ⥤ C := discreteCoefficientCohomologyFunctor.{z, max v w} H (n + 1)
  let a₀ : HS₀.obj S.X₁ ⟶ HT₀.obj T.X₁ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₁ n)
  let a₁ : HS₀.obj S.X₂ ⟶ HT₀.obj T.X₂ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₂ n)
  let a₂ : HS₀.obj S.X₃ ⟶ HT₀.obj T.X₃ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₃ n)
  let a₃ : HS₁.obj S.X₁ ⟶ HT₁.obj T.X₁ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₁ (n + 1))
  let a₄ : HS₁.obj S.X₂ ⟶ HT₁.obj T.X₂ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₂ (n + 1))
  let a₅ : HS₁.obj S.X₃ ⟶ HT₁.obj T.X₃ :=
    F.map (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₃ (n + 1))
  let w₀ : HS₀.map S.f ≫ a₁ = a₀ ≫ HT₀.map T.f :=
    discreteCoefficientGroupCohomologySquare.{v, z, w} φ S.f T.f f.τ₁ f.τ₂ f.comm₁₂ n
  let w₁ : HS₀.map S.g ≫ a₂ = a₁ ≫ HT₀.map T.g :=
    discreteCoefficientGroupCohomologySquare.{v, z, w} φ S.g T.g f.τ₂ f.τ₃ f.comm₂₃ n
  let w₂ : discreteCoefficientConnecting.{v, max z w} S hS n ≫ a₃ =
      a₂ ≫ discreteCoefficientConnecting.{z, max v w} T hT n :=
    discreteCoefficientConnecting_group_naturality.{v, z, w} hS hT f n
  let w₃ : HS₁.map S.f ≫ a₄ = a₃ ≫ HT₁.map T.f :=
    discreteCoefficientGroupCohomologySquare.{v, z, w} φ S.f T.f f.τ₁ f.τ₂ f.comm₁₂ (n + 1)
  let w₄ : HS₁.map S.g ≫ a₅ = a₄ ≫ HT₁.map T.g :=
    discreteCoefficientGroupCohomologySquare.{v, z, w} φ S.g T.g f.τ₂ f.τ₃ f.comm₂₃ (n + 1)
  longSequenceHomOfSquares (C := C)
    (HS₀.map S.f) (HS₀.map S.g) (discreteCoefficientConnecting.{v, max z w} S hS n)
    (HS₁.map S.f) (HS₁.map S.g)
    (HT₀.map T.f) (HT₀.map T.g) (discreteCoefficientConnecting.{z, max v w} T hT n)
    (HT₁.map T.f) (HT₁.map T.g)
    a₀ a₁ a₂ a₃ a₄ a₅ w₀ w₁ w₂ w₃ w₄

/-- The common coefficient enlargement retains the literal identity evaluation. -/
theorem discreteCoefficientZeroIso_cycle_value (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G)
    (c : ((TopRep.homogeneousCochains (inhomogeneousOriginalTopRep.{0, v, w} G A)).d
      0 1).hom.ker) :
    ((discreteCoefficientZeroIso.{v, w} G A).hom
      (discreteCoefficientForget.{max v w}.map
        (ContinuousCohomology.π (inhomogeneousOriginalTopRep.{0, v, w} G A) 0)
        (discreteCoefficientForget.{max v w}.map
          (ContinuousCohomology.cocycles₀Iso
            (inhomogeneousOriginalTopRep.{0, v, w} G A)).inv c))).val = c.val.val 1 :=
  homogeneousZeroIso_cycle_value.{0, v, w}
    (inhomogeneousOriginalTopRep.{0, v, w} G A) c

/-- The SAME inverse uses the class of the original constant cocycle. -/
theorem discreteCoefficientZeroIso_inverse_projection (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G) :
    (discreteCoefficientZeroIso.{v, w} G A).inv =
      discreteCoefficientForget.{max v w}.map
        (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso
          (inhomogeneousOriginalTopRep.{0, v, w} G A))).inv ≫
      discreteCoefficientForget.{max v w}.map
        (ContinuousCohomology.cocycles₀Iso
          (inhomogeneousOriginalTopRep.{0, v, w} G A)).inv ≫
      discreteCoefficientForget.{max v w}.map
        (ContinuousCohomology.π (inhomogeneousOriginalTopRep.{0, v, w} G A) 0) := by
  let F := discreteCoefficientForget.{max v w}
  let X := inhomogeneousOriginalTopRep.{0, v, w} G A
  exact (congrArg F.map (homogeneousZeroIso_inverse_projection.{0, v, w} X)).trans
    ((F.map_comp _ _).trans (congrArg (fun h => _ ≫ h) (F.map_comp _ _)))

/-- Every component of the coefficient sequence functor is the ORIGINAL cohomology map. -/
theorem discreteCoefficientLongSequenceFunctor_components (G : ProfiniteGrp.{v}) (n : ℕ)
    {S T : DiscreteCoefficientExactSequences.{v, w} G} (f : S ⟶ T) :
    let m := (discreteCoefficientLongSequenceFunctor.{v, w} G n).map f
    m.app 0 = (discreteCoefficientCohomologyFunctor.{v, w} G n).map f.hom.τ₁ ∧
    m.app 1 = (discreteCoefficientCohomologyFunctor.{v, w} G n).map f.hom.τ₂ ∧
    m.app 2 = (discreteCoefficientCohomologyFunctor.{v, w} G n).map f.hom.τ₃ ∧
    m.app 3 = (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.hom.τ₁ ∧
    m.app 4 = (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.hom.τ₂ ∧
    m.app 5 = (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).map f.hom.τ₃ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Full source laws for the SAME coefficient sequence, cohomology and boundary. -/
def DiscreteCoefficientLongExactLaws {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) : Prop :=
  (S.map (discreteCoefficientCochainFunctor.{v, w} G)).ShortExact ∧
  (∀ n, Function.Injective (((discreteCoefficientCochainFunctor.{v, w} G).map S.f).f n)) ∧
  (∀ n (c : ((discreteCoefficientCochainFunctor.{v, w} G).obj S.X₂).X n),
    ((discreteCoefficientCochainFunctor.{v, w} G).map S.g).f n c = 0 →
      ∃ b : ((discreteCoefficientCochainFunctor.{v, w} G).obj S.X₁).X n,
        ((discreteCoefficientCochainFunctor.{v, w} G).map S.f).f n b = c) ∧
  (∀ n, Function.Surjective (((discreteCoefficientCochainFunctor.{v, w} G).map S.g).f n)) ∧
  (∀ n, (discreteCoefficientLongSequence.{v, w} S hS n).Exact) ∧
  Mono ((discreteCoefficientCohomologyFunctor.{v, w} G 0).map S.f) ∧
  (∀ n, discreteCoefficientConnecting.{v, w} S hS n ≫
      (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1)).hom =
    (discreteCoefficientHomologyIso.{v, w} G S.X₃ n).hom ≫
      (discreteCoefficientCochain_shortExact.{v, w} S hS).δ n (n + 1)
        (discreteCoefficientUpRel n)) ∧
  (∀ (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G),
    discreteCoefficientZeroIso.{v, w} G A =
      discreteCoefficientForget.{max v w}.mapIso
        (ContinuousCohomology.zeroIso (inhomogeneousOriginalTopRep.{0, v, w} G A))) ∧
  (∀ (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G)
      (c : ((TopRep.homogeneousCochains
        (inhomogeneousOriginalTopRep.{0, v, w} G A)).d 0 1).hom.ker),
    ((discreteCoefficientZeroIso.{v, w} G A).hom
      (discreteCoefficientForget.{max v w}.map
        (ContinuousCohomology.π (inhomogeneousOriginalTopRep.{0, v, w} G A) 0)
        (discreteCoefficientForget.{max v w}.map
          (ContinuousCohomology.cocycles₀Iso
            (inhomogeneousOriginalTopRep.{0, v, w} G A)).inv c))).val = c.val.val 1) ∧
  (∀ (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G),
    (discreteCoefficientZeroIso.{v, w} G A).inv =
      discreteCoefficientForget.{max v w}.map
        (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso
          (inhomogeneousOriginalTopRep.{0, v, w} G A))).inv ≫
      discreteCoefficientForget.{max v w}.map
        (ContinuousCohomology.cocycles₀Iso
          (inhomogeneousOriginalTopRep.{0, v, w} G A)).inv ≫
      discreteCoefficientForget.{max v w}.map
        (ContinuousCohomology.π (inhomogeneousOriginalTopRep.{0, v, w} G A) 0)) ∧
  (∀ n (A : DiscreteCoefficientExactSequences.{v, w} G),
    (discreteCoefficientLongSequenceFunctor.{v, w} G n).map (𝟙 A) =
      𝟙 ((discreteCoefficientLongSequenceFunctor.{v, w} G n).obj A)) ∧
  (∀ n (A B C : DiscreteCoefficientExactSequences.{v, w} G)
      (f : A ⟶ B) (g : B ⟶ C),
    (discreteCoefficientLongSequenceFunctor.{v, w} G n).map (f ≫ g) =
      (discreteCoefficientLongSequenceFunctor.{v, w} G n).map f ≫
        (discreteCoefficientLongSequenceFunctor.{v, w} G n).map g) ∧
  ∀ n (A B : DiscreteCoefficientExactSequences.{v, w} G) (f : A ⟶ B)
      (i j : Fin 6) (h : i ≤ j),
    ((discreteCoefficientLongSequenceFunctor.{v, w} G n).obj A).map (homOfLE h) ≫
        ((discreteCoefficientLongSequenceFunctor.{v, w} G n).map f).app j =
      ((discreteCoefficientLongSequenceFunctor.{v, w} G n).map f).app i ≫
        ((discreteCoefficientLongSequenceFunctor.{v, w} G n).obj B).map (homOfLE h)

/-- Literal coefficient exactness gives the cochain, cohomology, and functorial laws. -/
private theorem discreteCoefficientLongExactLaws_of_exact {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) :
    DiscreteCoefficientLongExactLaws.{v, w} S hS := by
  let D := DiscreteContAction (TopModuleCat.{max v w} ℤ) G
  let F : D ⥤ CochainComplex AddCommGrpCat.{max v w} ℕ :=
    discreteCoefficientCochainFunctor.{v, w} G
  have hCochain : (S.map F).ShortExact := discreteCoefficientCochain_shortExact.{v, w} S hS
  have hInjective : ∀ n, Function.Injective ((F.map S.f).f n) :=
    fun n => discreteCoefficientCochain_injective.{v, w} S.f hS.1 n
  have hKernel : ∀ n (c : (F.obj S.X₂).X n), (F.map S.g).f n c = 0 →
      ∃ b : (F.obj S.X₁).X n, (F.map S.f).f n b = c :=
    fun n c hc => discreteCoefficientCochain_lift_kernel.{v, w} S.f S.g hS.2.1 n c hc
  have hSurjective : ∀ n, Function.Surjective ((F.map S.g).f n) :=
    fun n => discreteCoefficientCochain_surjective.{v, w} S.g hS.2.2 n
  have hExact : ∀ n, (discreteCoefficientLongSequence.{v, w} S hS n).Exact :=
    fun n => discreteCoefficientLongSequence_exact.{v, w} S hS n
  have hMono : Mono ((discreteCoefficientCohomologyFunctor.{v, w} G 0).map S.f) :=
    discreteCoefficient_cohomology_mono_zero.{v, w} S hS
  have hConnecting : ∀ n, discreteCoefficientConnecting.{v, w} S hS n ≫
      (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1)).hom =
      (discreteCoefficientHomologyIso.{v, w} G S.X₃ n).hom ≫
        (discreteCoefficientCochain_shortExact.{v, w} S hS).δ n (n + 1)
          (discreteCoefficientUpRel n) :=
    fun n => discreteCoefficientConnecting_comparison.{v, w} S hS n
  have hZero : ∀ A : D, discreteCoefficientZeroIso.{v, w} G A =
      discreteCoefficientForget.{max v w}.mapIso
        (ContinuousCohomology.zeroIso (inhomogeneousOriginalTopRep.{0, v, w} G A)) :=
    fun _ => rfl
  have hCycle := discreteCoefficientZeroIso_cycle_value.{v, w} G
  have hInverse := discreteCoefficientZeroIso_inverse_projection.{v, w} G
  have hIdentity : ∀ n (A : DiscreteCoefficientExactSequences.{v, w} G),
      (discreteCoefficientLongSequenceFunctor.{v, w} G n).map (𝟙 A) =
        𝟙 ((discreteCoefficientLongSequenceFunctor.{v, w} G n).obj A) :=
    fun n => (discreteCoefficientLongSequenceFunctor.{v, w} G n).map_id
  have hComposition : ∀ n (A B C : DiscreteCoefficientExactSequences.{v, w} G)
      (f : A ⟶ B) (g : B ⟶ C),
      (discreteCoefficientLongSequenceFunctor.{v, w} G n).map (f ≫ g) =
        (discreteCoefficientLongSequenceFunctor.{v, w} G n).map f ≫
          (discreteCoefficientLongSequenceFunctor.{v, w} G n).map g :=
    fun n _ _ _ f g => (discreteCoefficientLongSequenceFunctor.{v, w} G n).map_comp f g
  have hNaturality : ∀ n (A B : DiscreteCoefficientExactSequences.{v, w} G) (f : A ⟶ B)
      (i j : Fin 6) (h : i ≤ j),
      ((discreteCoefficientLongSequenceFunctor.{v, w} G n).obj A).map (homOfLE h) ≫
          ((discreteCoefficientLongSequenceFunctor.{v, w} G n).map f).app j =
        ((discreteCoefficientLongSequenceFunctor.{v, w} G n).map f).app i ≫
          ((discreteCoefficientLongSequenceFunctor.{v, w} G n).obj B).map (homOfLE h) :=
    fun n _ _ f _ _ h =>
      ((discreteCoefficientLongSequenceFunctor.{v, w} G n).map f).naturality (homOfLE h)
  exact ⟨hCochain, hInjective, hKernel, hSurjective, hExact, hMono, hConnecting,
    hZero, hCycle, hInverse, hIdentity, hComposition, hNaturality⟩

/-- The full coefficient theorem for arbitrary original equivariant additive f and g. -/
theorem original_continuous_cochain_long_exact_sequence (G : ProfiniteGrp.{v})
    {A B C : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Injective (discreteCoefficientHom.{v, w} f))
    (hfg : (discreteCoefficientHom.{v, w} f).range =
      (discreteCoefficientHom.{v, w} g).ker)
    (hg : Function.Surjective (discreteCoefficientHom.{v, w} g)) :
    DiscreteCoefficientLongExactLaws.{v, w}
      (discreteCoefficientShortComplex.{v, w} f g hfg)
      (discreteCoefficientShortComplex_exact.{v, w} f g hf hfg hg) := by
  exact discreteCoefficientLongExactLaws_of_exact.{v, w}
    (discreteCoefficientShortComplex.{v, w} f g hfg)
    (discreteCoefficientShortComplex_exact.{v, w} f g hf hfg hg)

/-- Every group/coefficient diagram gives the actual six components and ALL squares. -/
theorem original_continuous_cochain_group_coefficient_naturality
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {S : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G)}
    {T : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H)}
    (hS : DiscreteCoefficientExact.{v, max z w} S)
    (hT : DiscreteCoefficientExact.{z, max v w} T)
    {φ : H →ₜ* G} (f : DiscreteCoefficientGroupHom.{v, z, w} S T φ) (n : ℕ) :
    let m := discreteCoefficientGroupLongSequenceMap.{v, z, w} hS hT f n
    m.app 0 = discreteCoefficientForget.{max v (max z w)}.map
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₁ n) ∧
    m.app 1 = discreteCoefficientForget.{max v (max z w)}.map
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₂ n) ∧
    m.app 2 = discreteCoefficientForget.{max v (max z w)}.map
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₃ n) ∧
    m.app 3 = discreteCoefficientForget.{max v (max z w)}.map
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₁ (n + 1)) ∧
    m.app 4 = discreteCoefficientForget.{max v (max z w)}.map
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₂ (n + 1)) ∧
    m.app 5 = discreteCoefficientForget.{max v (max z w)}.map
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f.τ₃ (n + 1)) ∧
    ∀ (i j : Fin 6) (h : i ≤ j),
      (discreteCoefficientLongSequence.{v, max z w} S hS n).map (homOfLE h) ≫ m.app j =
        m.app i ≫ (discreteCoefficientLongSequence.{z, max v w} T hT n).map (homOfLE h) := by
  intro m
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => m.naturality (homOfLE h)⟩

/-- Original smaller coefficient diagrams enter the full sequence through exactly ONE lift.
The exactness, cochain sequences and every square are derived, without size certificates. -/
theorem original_continuous_cochain_native_group_naturality
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)}
    {T : ShortComplex (DiscreteContAction (TopModuleCat.{max z w} ℤ) H)}
    (hS : DiscreteCoefficientExact.{v, w} S) (hT : DiscreteCoefficientExact.{z, w} T)
    {φ : H →ₜ* G} (f : DiscreteCoefficientNativeGroupHom.{v, z, w} S T φ) (n : ℕ) :
    let S' : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G) :=
      S.map (discreteCoefficientULiftFunctor.{v, z, w} G)
    let T' : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H) :=
      T.map (discreteCoefficientULiftFunctor.{z, v, w} H)
    let hS' : DiscreteCoefficientExact.{v, max z w} S' :=
      discreteCoefficientULiftFunctor_exact.{v, z, w} S hS
    let hT' : DiscreteCoefficientExact.{z, max v w} T' :=
      discreteCoefficientULiftFunctor_exact.{z, v, w} T hT
    let f' : DiscreteCoefficientGroupHom.{v, z, w} S' T' φ :=
      discreteCoefficientNativeGroupHom_ulift.{v, z, w} f
    let m : discreteCoefficientLongSequence.{v, max z w} S' hS' n ⟶
        discreteCoefficientLongSequence.{z, max v w} T' hT' n :=
      discreteCoefficientGroupLongSequenceMap.{v, z, w} hS' hT' f' n
    (∀ x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₁,
      f'.τ₁.hom (ULift.up.{z, max v w} x) = ULift.up.{v, max z w} (f.τ₁ x)) ∧
    (∀ x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₂,
      f'.τ₂.hom (ULift.up.{z, max v w} x) = ULift.up.{v, max z w} (f.τ₂ x)) ∧
    (∀ x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₃,
      f'.τ₃.hom (ULift.up.{z, max v w} x) = ULift.up.{v, max z w} (f.τ₃ x)) ∧
    (S'.map (discreteCoefficientCochainFunctor.{v, max z w} G)).ShortExact ∧
    (T'.map (discreteCoefficientCochainFunctor.{z, max v w} H)).ShortExact ∧
    (∀ q, (discreteCoefficientLongSequence.{v, max z w} S' hS' q).Exact ∧
      (discreteCoefficientLongSequence.{z, max v w} T' hT' q).Exact) ∧
    ∀ (i j : Fin 6) (h : i ≤ j),
      (discreteCoefficientLongSequence.{v, max z w} S' hS' n).map (homOfLE h) ≫ m.app j =
        m.app i ≫ (discreteCoefficientLongSequence.{z, max v w} T' hT' n).map (homOfLE h) := by
  intro S' T' hS' hT' f' m
  let A := AddCommGrpCat.{max v (max z w)}
  let FS : DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G ⥤
      CochainComplex A ℕ := discreteCoefficientCochainFunctor.{v, max z w} G
  let FT : DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H ⥤
      CochainComplex A ℕ := discreteCoefficientCochainFunctor.{z, max v w} H
  have h₁ : ∀ x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₁,
      f'.τ₁.hom (ULift.up.{z, max v w} x) =
        ULift.up.{v, max z w} (f.τ₁ x) := fun _ => rfl
  have h₂ : ∀ x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₂,
      f'.τ₂.hom (ULift.up.{z, max v w} x) =
        ULift.up.{v, max z w} (f.τ₂ x) := fun _ => rfl
  have h₃ : ∀ x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₃,
      f'.τ₃.hom (ULift.up.{z, max v w} x) =
        ULift.up.{v, max z w} (f.τ₃ x) := fun _ => rfl
  have hSource : (S'.map FS).ShortExact :=
    discreteCoefficientCochain_shortExact.{v, max z w} S' hS'
  have hTarget : (T'.map FT).ShortExact :=
    discreteCoefficientCochain_shortExact.{z, max v w} T' hT'
  have hExact : ∀ q,
      (discreteCoefficientLongSequence.{v, max z w} S' hS' q).Exact ∧
      (discreteCoefficientLongSequence.{z, max v w} T' hT' q).Exact :=
    fun q => ⟨discreteCoefficientLongSequence_exact.{v, max z w} S' hS' q,
      discreteCoefficientLongSequence_exact.{z, max v w} T' hT' q⟩
  have hSquares : ∀ (i j : Fin 6) (h : i ≤ j),
      (discreteCoefficientLongSequence.{v, max z w} S' hS' n).map (homOfLE h) ≫ m.app j =
        m.app i ≫ (discreteCoefficientLongSequence.{z, max v w} T' hT' n).map (homOfLE h) :=
    fun _ _ h => m.naturality (homOfLE h)
  exact ⟨h₁, h₂, h₃, hSource, hTarget, hExact, hSquares⟩

end ContinuousCohomology

end
