/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.Topology.Category.TopCat.Subspace

/-!
# Strict fibers of singular maps

The singular simplicial set of a strict topological fiber is canonically
isomorphic to the strict fiber of the induced singular map.  We also package
the functorial map between strict simplicial fibers as an isomorphism whenever
the horizontal maps are isomorphisms.

The subspace-range argument is proved directly from singular simplices.  In
particular, this foundational comparison does not import singular homology or
export a global mono instance.  No based-path, loop-space, weak-equivalence,
or Q/S consequence is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

private lemma toSSetObjEquiv_map_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (sigma : (TopCat.toSSet.obj X).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n sigma) =
      f.hom.comp (X.toSSetObjEquiv n sigma) :=
  rfl

private theorem mono_toSSetMap_subspaceIncl
    {X : Type u} [TopologicalSpace X] (S : Set X) :
    Mono
      (TopCat.toSSet.map
        (AlgebraicTopology.subspaceIncl (X := TopCat.of X) S)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro sigma tau h
  apply (TopCat.of S).toSSetObjEquiv n |>.injective
  ext z
  have hsigma := DFunLike.congr_fun
    (toSSetObjEquiv_map_naturality
      (AlgebraicTopology.subspaceIncl (X := TopCat.of X) S) n sigma) z
  have htau := DFunLike.congr_fun
    (toSSetObjEquiv_map_naturality
      (AlgebraicTopology.subspaceIncl (X := TopCat.of X) S) n tau) z
  have hmid := congrArg
    (fun simplex => (TopCat.of X).toSSetObjEquiv n simplex z) h
  exact hsigma.symm.trans (hmid.trans htau)

private theorem mem_singularFiber_iff
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) (n : SimplexCategoryᵒᵖ)
    (sigma : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    sigma ∈
        (Subcomplex.fiber
          (TopCat.toSSet.map (TopCat.ofHom f))
          (TopCat.toSSetObj₀Equiv.symm y)).obj n ↔
      ∀ z, f ((TopCat.of X).toSSetObjEquiv n sigma z) = y := by
  rw [Subcomplex.mem_fiber_obj_iff, Subcomplex.mem_ofSimplex_obj_iff]
  constructor
  · rintro ⟨phi, hphi⟩ z
    have heq := congrArg
      (fun tau => (TopCat.of Y).toSSetObjEquiv n tau z) hphi
    have hconst :
        (TopCat.of Y).toSSetObjEquiv n
            ((TopCat.toSSet.obj (TopCat.of Y)).map phi.op
              (TopCat.toSSetObj₀Equiv.symm y)) z = y := by
      rw [TopCat.toSSetObjEquiv_naturality_apply,
        TopCat.toSSetObj₀Equiv_symm_apply]
      rfl
    have hmap :
        (TopCat.of Y).toSSetObjEquiv n
            ((TopCat.toSSet.map (TopCat.ofHom f)).app n sigma) z =
          f ((TopCat.of X).toSSetObjEquiv n sigma z) := by
      exact DFunLike.congr_fun
        (toSSetObjEquiv_map_naturality (TopCat.ofHom f) n sigma) z
    rw [← hmap, ← heq, hconst]
  · intro h
    refine ⟨n.unop.const ⦋0⦌ 0, ?_⟩
    apply (TopCat.toSSetObjEquiv (X := TopCat.of Y) n).injective
    ext z
    have hconst :
        (TopCat.of Y).toSSetObjEquiv n
            ((TopCat.toSSet.obj (TopCat.of Y)).map
              ((n.unop.const ⦋0⦌ 0).op)
              (TopCat.toSSetObj₀Equiv.symm y)) z = y := by
      rw [TopCat.toSSetObjEquiv_naturality_apply,
        TopCat.toSSetObj₀Equiv_symm_apply]
      rfl
    have hmap :
        (TopCat.of Y).toSSetObjEquiv n
            ((TopCat.toSSet.map (TopCat.ofHom f)).app n sigma) z =
          f ((TopCat.of X).toSSetObjEquiv n sigma z) := by
      exact DFunLike.congr_fun
        (toSSetObjEquiv_map_naturality (TopCat.ofHom f) n sigma) z
    rw [hconst, hmap, h z]

private theorem singularSubspaceRange_eq_fiber
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) :
    Subcomplex.range
        (TopCat.toSSet.map
          (AlgebraicTopology.subspaceIncl
            (X := TopCat.of X) (Set.ofPred fun x : X => f x = y))) =
      Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y) := by
  ext n sigma
  simp only [Subcomplex.range, Subfunctor.range_obj, Set.mem_range]
  rw [mem_singularFiber_iff]
  constructor
  · rintro ⟨tau, rfl⟩ z
    have hmap := DFunLike.congr_fun
      (toSSetObjEquiv_map_naturality
        (AlgebraicTopology.subspaceIncl
          (X := TopCat.of X) (Set.ofPred fun x : X => f x = y)) n tau) z
    rw [hmap]
    exact
      (((TopCat.of (Set.ofPred fun x : X => f x = y)).toSSetObjEquiv n tau) z).property
  · intro h
    let tau : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
      (TopCat.of X).toSSetObjEquiv n sigma
    let tauFiber :
        C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)),
          TopCat.of (Set.ofPred fun x : X => f x = y)) :=
      { toFun := fun z => ⟨tau z, h z⟩
        continuous_toFun := Continuous.subtype_mk tau.continuous h }
    refine ⟨(TopCat.of (Set.ofPred fun x : X => f x = y)).toSSetObjEquiv n |>.symm
      tauFiber, ?_⟩
    apply (TopCat.of X).toSSetObjEquiv n |>.injective
    rw [toSSetObjEquiv_map_naturality]
    ext z
    rfl

/-- The singular simplicial set of a strict topological fiber is canonically
isomorphic to the strict fiber of the induced singular map. -/
noncomputable def singularFiberIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) :
    TopCat.toSSet.obj (TopCat.of {x : X // f x = y}) ≅
      (Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y) : SSet.{u}) := by
  let S : Set X := Set.ofPred fun x : X => f x = y
  let j : TopCat.of S ⟶ TopCat.of X :=
    AlgebraicTopology.subspaceIncl (X := TopCat.of X) S
  have hRange :
      Subcomplex.range (TopCat.toSSet.map j) =
        Subcomplex.fiber
          (TopCat.toSSet.map (TopCat.ofHom f))
          (TopCat.toSSetObj₀Equiv.symm y) := by
    simpa only [S, j] using singularSubspaceRange_eq_fiber f y
  letI : Mono (TopCat.toSSet.map j) := by
    dsimp only [j]
    exact mono_toSSetMap_subspaceIncl S
  exact asIso (Subcomplex.toRange (TopCat.toSSet.map j)) ≪≫
    Subcomplex.eqToIso hRange

/-- The forward singular-fiber comparison followed by the fiber inclusion is
the singular map of the topological fiber inclusion. -/
@[reassoc]
theorem singularFiberIso_hom_ι
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) :
    (singularFiberIso f y).hom ≫
        (Subcomplex.fiber
          (TopCat.toSSet.map (TopCat.ofHom f))
          (TopCat.toSSetObj₀Equiv.symm y)).ι =
      TopCat.toSSet.map
          (AlgebraicTopology.subspaceIncl
            (X := TopCat.of X) (Set.ofPred fun x : X => f x = y)) := by
  unfold singularFiberIso
  simp only [Iso.trans_hom, Subcomplex.eqToIso_hom, Category.assoc,
    Subcomplex.homOfLE_ι]
  exact Subcomplex.toRange_ι _

/-- The inverse singular-fiber comparison followed by the topological fiber
inclusion is the simplicial fiber inclusion. -/
@[reassoc]
theorem singularFiberIso_inv_ι
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) :
    (singularFiberIso f y).inv ≫
        TopCat.toSSet.map
          (AlgebraicTopology.subspaceIncl
            (X := TopCat.of X) (Set.ofPred fun x : X => f x = y)) =
      (Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y)).ι := by
  rw [← cancel_epi (singularFiberIso f y).hom]
  simp only [Iso.hom_inv_id_assoc]
  exact (singularFiberIso_hom_ι f y).symm

/-- Degreewise form of `singularFiberIso_hom_ι`. -/
@[simp]
theorem singularFiberIso_hom_app_val
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) (n : SimplexCategoryᵒᵖ)
    (sigma : (TopCat.toSSet.obj (TopCat.of {x : X // f x = y})).obj n) :
    ((singularFiberIso f y).hom.app n sigma).val =
      (TopCat.toSSet.map
        (AlgebraicTopology.subspaceIncl
          (X := TopCat.of X) (Set.ofPred fun x : X => f x = y))).app n sigma := by
  have h := congr_app (singularFiberIso_hom_ι f y) n
  exact ConcreteCategory.congr_hom h sigma

/-- Degreewise form of `singularFiberIso_inv_ι`. -/
@[simp]
theorem singularFiberIso_inv_app_inclusion
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) (n : SimplexCategoryᵒᵖ)
    (sigma : (Subcomplex.fiber
      (TopCat.toSSet.map (TopCat.ofHom f))
      (TopCat.toSSetObj₀Equiv.symm y) : SSet.{u}).obj n) :
    (TopCat.toSSet.map
      (AlgebraicTopology.subspaceIncl
        (X := TopCat.of X) (Set.ofPred fun x : X => f x = y))).app n
        ((singularFiberIso f y).inv.app n sigma) = sigma.val := by
  have h := congr_app (singularFiberIso_inv_ι f y) n
  exact ConcreteCategory.congr_hom h sigma

namespace Subcomplex

/-- A commutative square whose horizontal maps are isomorphisms induces an
isomorphism between the corresponding strict fibers. -/
noncomputable def mapFiberIso
    {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hc : eX.hom ≫ f' = f ≫ eY.hom)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
    (hy : eY.hom.app _ y = y') :
    (fiber f y : SSet.{u}) ≅ (fiber f' y' : SSet.{u}) := by
  have hcInv : eX.inv ≫ f = f' ≫ eY.inv := by
    rw [← cancel_epi eX.hom]
    simp only [Iso.hom_inv_id_assoc]
    calc
      f = (f ≫ eY.hom) ≫ eY.inv := by simp
      _ = (eX.hom ≫ f') ≫ eY.inv := by rw [hc]
      _ = eX.hom ≫ f' ≫ eY.inv := by rw [Category.assoc]
  have hyInv : eY.inv.app _ y' = y := by
    rw [← hy]
    exact ConcreteCategory.congr_hom
      (congr_app eY.hom_inv_id (op ⦋0⦌)) y
  let hom := mapFiber eX.hom eY.hom hc hy
  let inv := mapFiber eX.inv eY.inv hcInv hyInv
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply (cancel_mono (fiber f y).ι).mp
        simp only [inv, hom]
        rw [Category.assoc, mapFiber_ι]
        rw [← Category.assoc, mapFiber_ι]
        simp
      inv_hom_id := by
        apply (cancel_mono (fiber f' y').ι).mp
        simp only [inv, hom]
        rw [Category.assoc, mapFiber_ι]
        rw [← Category.assoc, mapFiber_ι]
        simp }

/-- The forward fiber isomorphism commutes with the ambient inclusion. -/
@[reassoc]
theorem mapFiberIso_hom_ι
    {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hc : eX.hom ≫ f' = f ≫ eY.hom)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
    (hy : eY.hom.app _ y = y') :
    (mapFiberIso eX eY hc hy).hom ≫ (fiber f' y').ι =
      (fiber f y).ι ≫ eX.hom := by
  change mapFiber eX.hom eY.hom hc hy ≫ (fiber f' y').ι = _
  exact mapFiber_ι _ _ _ _

/-- The inverse fiber isomorphism commutes with the ambient inclusion. -/
@[reassoc]
theorem mapFiberIso_inv_ι
    {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hc : eX.hom ≫ f' = f ≫ eY.hom)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
    (hy : eY.hom.app _ y = y') :
    (mapFiberIso eX eY hc hy).inv ≫ (fiber f y).ι =
      (fiber f' y').ι ≫ eX.inv := by
  rw [← cancel_epi (mapFiberIso eX eY hc hy).hom]
  simp only [Iso.hom_inv_id_assoc, mapFiberIso_hom_ι_assoc]
  rw [Iso.hom_inv_id, Category.comp_id]

/-- Degreewise form of `mapFiberIso_hom_ι`. -/
@[simp]
theorem mapFiberIso_hom_app_val
    {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hc : eX.hom ≫ f' = f ≫ eY.hom)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
    (hy : eY.hom.app _ y = y') (n : SimplexCategoryᵒᵖ)
    (sigma : (fiber f y : SSet.{u}).obj n) :
    ((mapFiberIso eX eY hc hy).hom.app n sigma).val =
      eX.hom.app n sigma.val := by
  have h := congr_app (mapFiberIso_hom_ι eX eY hc hy) n
  exact ConcreteCategory.congr_hom h sigma

/-- Degreewise form of `mapFiberIso_inv_ι`. -/
@[simp]
theorem mapFiberIso_inv_app_val
    {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hc : eX.hom ≫ f' = f ≫ eY.hom)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
    (hy : eY.hom.app _ y = y') (n : SimplexCategoryᵒᵖ)
    (sigma : (fiber f' y' : SSet.{u}).obj n) :
    ((mapFiberIso eX eY hc hy).inv.app n sigma).val =
      eX.inv.app n sigma.val := by
  have h := congr_app (mapFiberIso_inv_ι eX eY hc hy) n
  exact ConcreteCategory.congr_hom h sigma

end Subcomplex

end SSet
