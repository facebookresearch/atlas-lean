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

/-!
# Continuous coefficient cochains and long exact sequences

For a ring k with a topology, independently sized profinite groups G,H,
a continuous homomorphism φ:H→G and an equivariant coefficient map f,
homogeneous cochains map by precomposing group coordinates with φ
and applying f. These maps commute with differential, identity,
composition and coefficient squares. Carrier lifts allow the corresponding
maps between independently sized coefficient representations.

For discrete continuous abelian coefficients, an injective first map,
image–kernel equality and a surjective second map give a degreewise short
exact sequence of homogeneous cochain complexes. Their continuous
cohomology compares naturally with homology of those abelian complexes.
The connecting map and all six-term windows
Hⁿ(A)→Hⁿ(B)→Hⁿ(C)→Hⁿ⁺¹(A)→Hⁿ⁺¹(B)→Hⁿ⁺¹(C)
are exact and natural in the original coefficient and group maps.
Degree zero identifies with coefficient invariants by identity evaluation.
Independent group and carrier worlds are retained, using a single
coefficient lift where a common carrier presentation is needed.
-/

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

/-- Let k be a ring with a topology and G an abstract group.
For any coefficient carrier universe c and lift height d, this
functor takes a topological k-representation X of G to ULift^d(X),
with inherited topology, scalar action and G-action.
It sends a morphism f to ULift.up∘f∘ULift.down. -/
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

/-- Let k be a ring with a topology, G,H abstract groups in universes
b,c, and X,Y topological k-representations with carriers max(b,e)
and max(c,e). For φ:H→G and a continuous k-linear φ-intertwiner f:X→Y,
lifting X by c and Y by b gives the morphism
Res_φ(ULift^c X)→ULift^b Y with value up(x)↦up(f(x)). -/
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

/-- Let k be a ring with a topology, G,H profinite groups in
universes v,z, and X,Y coefficients with carriers max(v,w),max(z,w).
For continuous φ:H→G, the coefficient-intertwiner space consists
of continuous k-linear maps f:X→Y satisfying
f(φ(h)•x)=h•f(x), with no equality of carrier universes required. -/
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

/-- For independently sized profinite groups G,H and continuous
φ:H→G, this continuous tuple map H^(n+1)→G^(n+1) applies φ
to each ordered coordinate. -/
def nativeHomogeneousTupleMap
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}} (φ : H →ₜ* G) (n : ℕ) :
    C(Fin (n + 1) → H, Fin (n + 1) → G) :=
  ⟨fun t i => φ (t i), continuous_pi fun i => φ.continuous.comp (continuous_apply i)⟩

/-- Let k be a ring with a topology, G,H profinite groups in
independent universes v,z, and coefficient representations X,Y with
common carrier c=max(v,z,w). Let φ:H→G be continuous and
f:Res_φ(X)→Y a continuous equivariant k-linear map.
The tuple-form homogeneous degree n map sends a cochain a to
t↦f(a(φ(t₀),…,φ(t_n))). It is a morphism of topological k-modules. -/
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

/-- Let k be a ring with a topology, G,H profinite groups in
independent universes v,z, and coefficient representations X,Y with
common carrier c=max(v,z,w). Let φ:H→G be continuous and
f:Res_φ(X)→Y a continuous equivariant k-linear map.
The tuple-form maps commute with alternating deletion:
d_Y∘map_n=map_(n+1)∘d_X. -/
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

/-- Let k be a ring with a topology, G,H profinite groups in
independent universes v,z, and coefficient representations X,Y with
common carrier c=max(v,z,w). Let φ:H→G be continuous and
f:Res_φ(X)→Y a continuous equivariant k-linear map.
The degree maps t↦f(a(φ(t))) form the cochain map
C_hom,tuple(G,X)→C_hom,tuple(H,Y) in all nonnegative degrees. -/
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

/-- Let k be a ring with a topology, G,H profinite groups in
independent universes v,z, and coefficient representations X,Y with
common carrier c=max(v,z,w). Let φ:H→G be continuous and
f:Res_φ(X)→Y a continuous equivariant k-linear map.
Transport through the tuple/nested comparisons gives the map
C_hom(G,X)→C_hom(H,Y) of the nested invariant homogeneous complexes. -/
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

/-- Let k be a ring with a topology, G,H profinite groups in
independent universes v,z, and coefficient representations X,Y with
common carrier c=max(v,z,w). Let φ:H→G be continuous and
f:Res_φ(X)→Y a continuous equivariant k-linear map.
In degree n, the induced map is
Hⁿ_cts(G,X)→Hⁿ_cts(H,Y), obtained by homology of the homogeneous
group/coefficient cochain map. -/
def nativeGroupCoefficientCohomologyMap
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {X : TopRep.{max v (max z w), u, v} k G}
    {Y : TopRep.{max z (max v w), u, z} k H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    continuousCohomology.{u, v, max z w} n X ⟶ continuousCohomology.{u, z, max v w} n Y :=
  HomologicalComplex.homologyMap (nativeGroupCoefficientCochainsMap.{u, v, z, w} φ f) n

/-- Let k be a ring with a topology, G,H profinite groups in
independent universes v,z, and coefficient representations X,Y with
common carrier c=max(v,z,w). Let φ:H→G be continuous and
f:Res_φ(X)→Y a continuous equivariant k-linear map.
In tuple coordinates, the nested degree n cochain map has value
t↦f(a(φ(t₀),…,φ(t_n))). -/
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

/-- Let k be a ring with a topology, G a profinite group and X a
topological k-representation. For a nested degree-zero homogeneous
cochain a and g∈G, its one-coordinate tuple comparison has value
E₁(a)(g)=a(g). -/
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

/-- For a ring k with a topology, profinite G,H in the same group
universe v, and coefficients X,Y in max(v,w), the tuple-defined
group/coefficient cochain map for (φ,f) equals the standard homogeneous
cochain map with the same φ and f. -/
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

/-- For a ring k with a topology, profinite G and coefficient X,
the homogeneous cochain map induced by id_G and id_X is the
identity of C_hom(G,X). -/
theorem nativeGroupCoefficientCochainsMap_id
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G) :
    nativeGroupCoefficientCochainsMap.{u, v, v, w}
      (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (TopRep.homogeneousCochains X) :=
  (nativeGroupCoefficientCochainsMap_eq_stock.{u, v, w}
    (ContinuousMonoidHom.id G) (𝟙 X)).trans (cochainsMap_id X)

/-- Let k be a ring with a topology, G,H,K profinite groups in
independent universes v,z,y, and common coefficient carrier
max(v,z,y,w). For φ:H→G, ψ:K→H and compatible coefficient
maps f,g, map_(φ∘ψ,g∘Res_ψ(f))=map_(ψ,g)∘map_(φ,f). -/
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

/-- Let k be a ring with a topology, G,H profinite groups in universes
v,z, and X₁,X₂ over G and Y₁,Y₂ over H topological k-representations
with carrier c=max(v,z,w). Let φ:H→G be continuous, a:X₁→X₂,
b:Y₁→Y₂, and φ-equivariant maps ψ₁,ψ₂ satisfy
b∘ψ₁=ψ₂∘Res_φ(a). Their induced homogeneous cochain maps satisfy
C(b)∘map_(φ,ψ₁)=map_(φ,ψ₂)∘C(a). -/
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

/-- Let k be a ring with a topology, G,H profinite groups in independent
universes, four coefficient representations X₁,X₂,Y₁,Y₂ in a common
carrier, and φ:H→G continuous. Given a:X₁→X₂, b:Y₁→Y₂ and
φ-equivariant ψ₁,ψ₂ with b∘ψ₁=ψ₂∘Res_φ(a), their continuous
cohomology maps satisfy
Hⁿ(b)∘Hⁿ(φ,ψ₁)=Hⁿ(φ,ψ₂)∘Hⁿ(a). -/
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

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
There is an additive equivalence from nested homogeneous degree n
cochains to C(G^n,A), given by prefix-product inhomogenization
and its inverse t↦t₀•h(t_i⁻¹t_(i+1)). -/
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

/-- For a ring k with a topology, profinite G and a topological
k-representation X, the projection Z⁰(G,X)→H⁰_cts(G,X), followed
by H⁰_cts(G,X)≅X^G, equals the degree-zero cycle-to-kernel
identification followed by identity evaluation. -/
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

/-- For a ring k with a topology, profinite G and coefficient X,
the inverse isomorphism X^G→H⁰_cts(G,X) takes an invariant x
to the class of its constant degree-zero homogeneous cycle. -/
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

/-- For a ring k with a topology, profinite G and coefficient X,
the identification Z⁰(G,X)≅ker(d⁰) commutes with inclusion into
the homogeneous degree-zero cochain term. -/
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

/-- Let k be a ring with a topology, G,H profinite groups in
independent universes v,z, and coefficient representations X,Y with
common carrier c=max(v,z,w). Let φ:H→G be continuous and
f:Res_φ(X)→Y a continuous equivariant k-linear map.
The degree-zero invariant identifications commute with (φ,f):
zeroIso_Y∘H⁰(φ,f)=invariantsResMap(φ,f)∘zeroIso_X. -/
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


/-- For a profinite G in universe v, the category of discrete
continuous G-actions on topological ℤ-modules with carrier universe w
is preadditive. Morphism addition and zero are pointwise. -/
@[nolint defsWithUnderscore] -- preserve the original public name
abbrev discreteCoefficient_preadditive (G : ProfiniteGrp.{v}) :
    Preadditive (DiscreteContAction (TopModuleCat.{w} ℤ) G) :=
  CategoryTheory.DiscreteAbelianAction.instPreadditive.{v, w} (G := G)

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The coefficient functor D_G→TopRep(ℤ,G) realizes the same
underlying abelian group and jointly continuous action as a
topological ℤ-representation. -/
abbrev discreteCoefficientTopRepFunctor (G : ProfiniteGrp.{v}) :
    DiscreteContAction (TopModuleCat.{max v w} ℤ) G ⥤ TopRep.{max v w, 0, v} ℤ G where
  obj A := inhomogeneousOriginalTopRep.{0, v, w} G A
  map f := (TopRep.fromActionTopModFunc.{max v w, 0, v} (k := ℤ) (G := G)).map f.hom.hom
  map_id _ := by apply TopRep.hom_ext; rfl
  map_comp _ _ := by apply TopRep.hom_ext; rfl

instance (G : ProfiniteGrp.{v}) :
    (discreteCoefficientTopRepFunctor.{v, w} G).Additive where
  map_add := by intros; apply TopRep.hom_ext; rfl

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For a coefficient morphism f:A→B, its underlying coefficient
homomorphism is the same equivariant additive map A→B. -/
abbrev discreteCoefficientHom {G : ProfiniteGrp.{v}}
    {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G}
    (f : A ⟶ B) :
    inhomogeneousOriginalTopRep.{0, v, w} G A →+ inhomogeneousOriginalTopRep.{0, v, w} G B :=
  ((discreteCoefficientTopRepFunctor.{v, w} G).map f).hom.toAddMonoidHom

@[simp] theorem discreteCoefficientHom_apply
    {G : ProfiniteGrp.{v}} {A B : DiscreteContAction (TopModuleCat.{max v w} ℤ) G} (f : A ⟶ B)
    (a : inhomogeneousOriginalTopRep.{0, v, w} G A) :
    discreteCoefficientHom f a = f.hom.hom.hom.hom a := rfl

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For any lift height z, the coefficient lift functor replaces each
carrier by ULift^z and inherits topology and G-action, giving
coefficients in max(v,z,w). -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The lifted coefficient morphism has value
Lift(f)(ULift.up(x))=ULift.up(f(x)) for every x∈A. -/
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

/-- The functor from topological ℤ-modules with carrier universe w
to AddCommGrpCat w keeps the underlying additive group and additive
map, forgetting its topology and scalar packaging. -/
abbrev discreteCoefficientForget : TopModuleCat.{w} ℤ ⥤ AddCommGrpCat.{w} :=
  forget₂ (TopModuleCat.{w} ℤ) (ModuleCat.{w} ℤ) ⋙
    forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}

instance : discreteCoefficientForget.{w}.Additive where
  map_add := by intros; rfl

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The additive functor C_G sends a coefficient A to its nonnegative
homogeneous cochain complex after forgetting topology to abelian groups.
It acts on coefficient maps by postcomposition. -/
abbrev discreteCoefficientCochainFunctor (G : ProfiniteGrp.{v}) :
    DiscreteContAction (TopModuleCat.{max v w} ℤ) G ⥤ CochainComplex AddCommGrpCat.{max v w} ℕ :=
  discreteCoefficientTopRepFunctor.{v, w} G ⋙
    homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G) ⋙
      (discreteCoefficientForget.{max v w}).mapHomologicalComplex (ComplexShape.up ℕ)

instance (G : ProfiniteGrp.{v}) :
    (discreteCoefficientCochainFunctor.{v, w} G).Additive := by
  unfold discreteCoefficientCochainFunctor
  infer_instance

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For n∈ℕ, the continuous cohomology functor Hⁿ_G takes values in
abelian groups by forgetting the topology of continuous cohomology. -/
abbrev discreteCoefficientCohomologyFunctor (G : ProfiniteGrp.{v}) (n : ℕ) :
    DiscreteContAction (TopModuleCat.{max v w} ℤ) G ⥤ AddCommGrpCat.{max v w} :=
  discreteCoefficientTopRepFunctor.{v, w} G ⋙
    homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G) ⋙
      HomologicalComplex.homologyFunctor (TopModuleCat.{max v w} ℤ)
        (ComplexShape.up ℕ) n ⋙ discreteCoefficientForget

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The canonical comparison is Hⁿ_G(A)≅Hⁿ(C_G(A)), obtained by
preservation of homogeneous homology under coefficient forgetting. -/
def discreteCoefficientHomologyIso (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G)
    (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, w} G n).obj A ≅
      ((discreteCoefficientCochainFunctor.{v, w} G).obj A).homology n :=
  ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ)
    n discreteCoefficientForget.{max v w}).app (TopRep.homogeneousCochains
      (inhomogeneousOriginalTopRep.{0, v, w} G A))).symm

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For f:A→B and a homogeneous degree n cochain a, tuple coordinates
of the induced coefficient map have value f(a(t)). -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Degree n homogeneous cochains are additively equivalent to
continuous inhomogeneous functions G^n→A, by the prefix/difference
coordinate formulas. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
If the underlying coefficient map f:A→B is injective, then
C_G(f)^n is injective for every n∈ℕ. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
If the underlying coefficient map f:A→B is surjective, then
C_G(f)^n is surjective for every n∈ℕ. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For f:A→B and g:B→C with range(f)=ker(g), every degree n
cochain a of B with C_G(g)(a)=0 has a degree n preimage b of A
with C_G(f)(b)=a. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For a short complex S, the coefficient exactness predicate means:
the first underlying additive map is injective, its image is the
second map's kernel, and the second underlying map is surjective. -/
def DiscreteCoefficientExact {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)) : Prop :=
  Function.Injective (discreteCoefficientHom S.f) ∧
    (discreteCoefficientHom S.f).range = (discreteCoefficientHom S.g).ker ∧
      Function.Surjective (discreteCoefficientHom S.g)

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For f:A→B and g:B→C with range(f)=ker(g), this is the short
complex A→B→C with those two coefficient maps.
The range–kernel equality gives g∘f=0. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
Applying homogeneous cochains yields a short exact sequence of
nonnegative abelian-group cochain complexes, degreewise in every n. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
Lifting all coefficient carriers by any height z preserves the
three underlying exactness conditions, so the lifted coefficient
short complex is again exact. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For a coefficient map f:A→B, the continuous/cochain homology
comparisons satisfy γ_B∘Hⁿ_G(f)=Hⁿ(C_G(f))∘γ_A. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
The canonical connecting map δ_n:Hⁿ_G(C)→Hⁿ⁺¹_G(A) is the
cochain homology boundary transported through the continuous/cochain
homology comparisons. -/
def discreteCoefficientConnecting {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact S) (n : ℕ) :
    (discreteCoefficientCohomologyFunctor.{v, w} G n).obj S.X₃ ⟶
      (discreteCoefficientCohomologyFunctor.{v, w} G (n + 1)).obj S.X₁ :=
  (discreteCoefficientHomologyIso.{v, w} G S.X₃ n).hom ≫
    (discreteCoefficientCochain_shortExact S hS).δ n (n + 1) (discreteCoefficientUpRel n) ≫
      (discreteCoefficientHomologyIso.{v, w} G S.X₁ (n + 1)).inv

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
For the homology comparisons γ, the connecting map satisfies
γ_A^(n+1)∘δ_n=δ_Cochain∘γ_C^n. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
The cohomology sequence Hⁿ_G(A)→Hⁿ_G(B)→Hⁿ_G(C) is exact
at Hⁿ_G(B): image of the first map equals kernel of the second. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
The sequence Hⁿ_G(B)→Hⁿ_G(C)→Hⁿ⁺¹_G(A) is exact at
Hⁿ_G(C), using the canonical connecting map as its second arrow. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
The sequence Hⁿ_G(C)→Hⁿ⁺¹_G(A)→Hⁿ⁺¹_G(B) is exact
at Hⁿ⁺¹_G(A), using the connecting map as its first arrow. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
The degree-zero map H⁰_G(A)→H⁰_G(B) is a monomorphism of
abelian groups. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The degree-zero continuous cohomology is naturally isomorphic to
the underlying invariant group A^G, by identity evaluation of
closed homogeneous cochains. -/
def discreteCoefficientZeroIso (G : ProfiniteGrp.{v})
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G) :
    (discreteCoefficientCohomologyFunctor.{v, w} G 0).obj A ≅
      discreteCoefficientForget.{max v w}.obj
        (TopRep.invariants (inhomogeneousOriginalTopRep.{0, v, w} G A)) :=
  discreteCoefficientForget.{max v w}.mapIso
    (ContinuousCohomology.zeroIso (inhomogeneousOriginalTopRep.{0, v, w} G A))

/-- Let G,H be profinite groups in universes v,z and c=max(v,z,w).
Let A and B be discrete continuous abelian coefficients of G and H
with carrier c, φ:H→G continuous, and f:Res_φ(A)→B an equivariant
continuous ℤ-linear map. The induced abelian cochain map C_G(A)→C_H(B)
sends a homogeneous function a to t↦f(a(φ(t))). -/
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

/-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
This is the data of a morphism from S to T along φ: the three
continuous ℤ-linear intertwiners τ_i and the two commuting
coefficient-arrow squares. Exactness is not part of this datum. -/
structure DiscreteCoefficientGroupHom
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G))
    (T : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H))
    (φ : H →ₜ* G) where
  /-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
The first component is τ₁:Res_φ(S₁)→T₁, a continuous
ℤ-linear φ-equivariant coefficient map in the common universe c. -/
  τ₁ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G S.X₁) ⟶
    inhomogeneousOriginalTopRep.{0, z, max v w} H T.X₁
  /-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
The middle component is τ₂:Res_φ(S₂)→T₂, a continuous
ℤ-linear φ-equivariant coefficient map in the common universe c. -/
  τ₂ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G S.X₂) ⟶
    inhomogeneousOriginalTopRep.{0, z, max v w} H T.X₂
  /-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
The last component is τ₃:Res_φ(S₃)→T₃, a continuous
ℤ-linear φ-equivariant coefficient map in the common universe c. -/
  τ₃ : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G S.X₃) ⟶
    inhomogeneousOriginalTopRep.{0, z, max v w} H T.X₃
  comm₁₂ : τ₁ ≫ (discreteCoefficientTopRepFunctor.{z, max v w} H).map T.f =
    (TopRep.resFunctor (φ : H →* G)).map
      ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.f) ≫ τ₂
  comm₂₃ : τ₂ ≫ (discreteCoefficientTopRepFunctor.{z, max v w} H).map T.g =
    (TopRep.resFunctor (φ : H →* G)).map
      ((discreteCoefficientTopRepFunctor.{v, max z w} G).map S.g) ≫ τ₃

/-- Let G,H be profinite groups in universes v,z, with coefficient
carriers c_G=max(v,w) and c_H=max(z,w). Let S,T be short complexes of
discrete continuous abelian coefficients in those carriers and
φ:H→G continuous.
This diagram consists of three continuous ℤ-linear φ-intertwiners
from the underlying terms of S to T, with pointwise coefficient-arrow
commutation. The original two carrier universes are retained. -/
structure DiscreteCoefficientNativeGroupHom
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (T : ShortComplex (DiscreteContAction (TopModuleCat.{max z w} ℤ) H))
    (φ : H →ₜ* G) where
  /-- Let G,H be profinite groups in universes v,z, with coefficient
carriers c_G=max(v,w) and c_H=max(z,w). Let S,T be short complexes of
discrete continuous abelian coefficients in those carriers and
φ:H→G continuous.
The first component is the continuous ℤ-linear φ-intertwiner
S₁→T₁ between carriers c_G and c_H. -/
  τ₁ : nativeCoefficientIntertwiner.{0, v, z, w}
    (inhomogeneousOriginalTopRep.{0, v, w} G S.X₁)
    (inhomogeneousOriginalTopRep.{0, z, w} H T.X₁) φ
  /-- Let G,H be profinite groups in universes v,z, with coefficient
carriers c_G=max(v,w) and c_H=max(z,w). Let S,T be short complexes of
discrete continuous abelian coefficients in those carriers and
φ:H→G continuous.
The middle component is the continuous ℤ-linear φ-intertwiner
S₂→T₂ between carriers c_G and c_H. -/
  τ₂ : nativeCoefficientIntertwiner.{0, v, z, w}
    (inhomogeneousOriginalTopRep.{0, v, w} G S.X₂)
    (inhomogeneousOriginalTopRep.{0, z, w} H T.X₂) φ
  /-- Let G,H be profinite groups in universes v,z, with coefficient
carriers c_G=max(v,w) and c_H=max(z,w). Let S,T be short complexes of
discrete continuous abelian coefficients in those carriers and
φ:H→G continuous.
The last component is the continuous ℤ-linear φ-intertwiner
S₃→T₃ between carriers c_G and c_H. -/
  τ₃ : nativeCoefficientIntertwiner.{0, v, z, w}
    (inhomogeneousOriginalTopRep.{0, v, w} G S.X₃)
    (inhomogeneousOriginalTopRep.{0, z, w} H T.X₃) φ
  comm₁₂ (x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₁) :
    discreteCoefficientHom.{z, w} T.f (τ₁ x) = τ₂ (discreteCoefficientHom.{v, w} S.f x)
  comm₂₃ (x : inhomogeneousOriginalTopRep.{0, v, w} G S.X₂) :
    discreteCoefficientHom.{z, w} T.g (τ₂ x) = τ₃ (discreteCoefficientHom.{v, w} S.g x)

/-- Let G,H be profinite groups in universes v,z, with coefficient
carriers c_G=max(v,w) and c_H=max(z,w). Let S,T be short complexes of
discrete continuous abelian coefficients in those carriers and
φ:H→G continuous.
Lifting S by z and T by v gives a group/coefficient diagram in
c=max(v,z,w). Each component has value up(x)↦up(τ_i(x)),
and the two coefficient squares lift with it. -/
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

/-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
The three coefficient maps induce the short-complex map
C_G(S)→C_H(T), degreewise by their group/coefficient cochain maps. -/
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


/-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
If S and T satisfy the three underlying exactness conditions,
their connecting maps obey
H^(n+1)(φ,τ₁)∘δ_S=δ_T∘Hⁿ(φ,τ₃). -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For a morphism α:S→T of two exact coefficient short complexes,
H^(n+1)(α₁)∘δ_S=δ_T∘Hⁿ(α₃).
The middle component's commutation is part of the sequence morphism. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
This five-arrow window is
Hⁿ(A)→Hⁿ(B)→Hⁿ(C)→Hⁿ⁺¹(A)→Hⁿ⁺¹(B)→Hⁿ⁺¹(C),
with the canonical coefficient maps and central connecting arrow. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
The six-group window is isomorphic to the corresponding homology
sequence window of the short exact cochain sequence C_G(S).
Its components are the continuous/cochain homology comparisons. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
For every n∈ℕ, the five-arrow continuous cohomology window is
exact at each of its four interior groups. -/
theorem discreteCoefficientLongSequence_exact {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) (n : ℕ) :
    (discreteCoefficientLongSequence.{v, w} S hS n).Exact :=
  (ComposableArrows.exact_iff_of_iso
    (discreteCoefficientLongSequenceIso.{v, w} S hS n)).mpr
      (HomologicalComplex.HomologySequence.composableArrows₅_exact
        (discreteCoefficientCochain_shortExact.{v, w} S hS)
        n (n + 1) (discreteCoefficientUpRel n))

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The exact-sequence object property on coefficient short complexes
is the underlying injectivity, image–kernel equality and surjectivity
predicate. -/
def discreteCoefficientExactProperty (G : ProfiniteGrp.{v}) :
    ObjectProperty (ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)) :=
  DiscreteCoefficientExact.{v, w}

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The category of exact coefficient sequences is the full subcategory
of coefficient short complexes satisfying the three exactness conditions.
Its morphisms are three-term diagrams with both squares commuting. -/
abbrev DiscreteCoefficientExactSequences (G : ProfiniteGrp.{v}) :=
  (discreteCoefficientExactProperty.{v, w} G).FullSubcategory

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For fixed n, an exact coefficient sequence is sent to its six-group
continuous cohomology window. A sequence morphism is sent to its
three cohomology maps in degree n and again in degree n+1. -/
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

/-- Let G,H be profinite groups in universes v,z and discrete continuous
abelian coefficients A₁,A₂ over G and B₁,B₂ over H have carrier
c=max(v,z,w). For continuous φ:H→G, maps a:A₁→A₂, b:B₁→B₂
and φ-intertwiners ψ₁,ψ₂ with b∘ψ₁=ψ₂∘a after restriction,
the degree n discrete continuous cohomology square commutes. -/
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

/-- Let G,H be profinite groups in universes v,z and c=max(v,z,w).
For discrete continuous abelian coefficients A over G and B over H,
continuous φ:H→G and equivariant ℤ-linear f:Res_φ(A)→B,
the degree-zero invariant comparisons satisfy
zeroIso_B∘H⁰(φ,f)=invariantsResMap(φ,f)∘zeroIso_A. -/
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

/-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
For exact S,T, the group/coefficient cohomology maps define a
morphism of their six-group windows, with degrees n and n+1 and
connecting-map square included. -/
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
  ComposableArrows.homMk₅
    (f := ComposableArrows.mk₅ (HS₀.map S.f) (HS₀.map S.g)
      (discreteCoefficientConnecting.{v, max z w} S hS n) (HS₁.map S.f) (HS₁.map S.g))
    (g := ComposableArrows.mk₅ (HT₀.map T.f) (HT₀.map T.g)
      (discreteCoefficientConnecting.{z, max v w} T hT n) (HT₁.map T.f) (HT₁.map T.g))
    a₀ a₁ a₂ a₃ a₄ a₅ w₀ w₁ w₂ w₃ w₄

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For a closed degree-zero homogeneous function a, the degree-zero
invariant comparison sends its projected class to a(1). -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
The inverse invariant comparison A^G→H⁰_G(A) sends an invariant
a to its constant homogeneous zero-cycle and then projects that
cycle to cohomology. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For a morphism α:S→T of exact coefficient sequences, the six
window components are Hⁿ(α₁),Hⁿ(α₂),Hⁿ(α₃), then
Hⁿ⁺¹(α₁),Hⁿ⁺¹(α₂),Hⁿ⁺¹(α₃). -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
This proposition records degreewise cochain short exactness,
injectivity, kernel lifting and surjectivity; exactness of every
six-term cohomology window; monicity of the initial degree-zero map;
and the connecting/homology comparison.
It also includes identity evaluation and constant-cycle inverse in
degree zero, and identity, composition and all arrow-naturality
laws of the sequence-window functor. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
Let S=(A→B→C) be a short complex whose underlying first map is injective,
image equals the second map's kernel, and the second map is surjective.
The coefficient exactness conditions give all stated cochain,
continuous cohomology, degree-zero invariant and sequence-functor
properties for S. -/
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

/-- Let G be a profinite group in universe v and c=max(v,w).
Let D_G be the category of abelian groups in c with discrete topology
and jointly continuous G-action. Write C_G(A) for their homogeneous
abelian-group cochain complex and Hⁿ_G(A) for continuous cohomology.
For coefficient maps f:A→B and g:B→C with f injective,
range(f)=ker(g) and g surjective on underlying groups, their induced
short complex has the full cochain and continuous long exact
sequence properties in every degree. -/
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

/-- Let G,H be profinite groups in universes v,z, c=max(v,z,w),
S,T short complexes of discrete continuous abelian coefficients in c,
and φ:H→G continuous. Let τ₁,τ₂,τ₃ be continuous ℤ-linear
φ-equivariant coefficient maps commuting with the two sequence arrows.
For exact S,T, the six components of the group/coefficient window
map are Hⁿ(φ,τ_i) and Hⁿ⁺¹(φ,τ_i), i=1,2,3.
Every composite-arrow square between ordered window positions i≤j
commutes. -/
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

/-- Let G,H be profinite groups in universes v,z, with coefficient
carriers c_G=max(v,w) and c_H=max(z,w). Let S,T be short complexes of
discrete continuous abelian coefficients in those carriers and
φ:H→G continuous.
If the underlying coefficient sequences S,T are exact, lift each
once to c=max(v,z,w). The lifted components have values
up(x)↦up(τ_i(x)); both lifted cochain sequences are short exact;
all their cohomology windows are exact; and the resulting window
map commutes with every composite-arrow square at positions i≤j. -/
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
