/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Coproducts of topological homotopies and homotopy equivalences

A family of topological homotopies assembles to a homotopy on the disjoint union,
using the homeomorphism `I × (Σ i, A_i) ≅ Σ i, I × A_i`. A family of homotopy
equivalences therefore gives a homotopy equivalence of disjoint unions, with the
component forward and inverse maps preserving the coproduct index.

The corresponding categorical coproduct map is a weak homotopy equivalence.
The index type and the space carriers are in the same specified universe.
-/

@[expose] public section

universe u

open CategoryTheory

namespace TopCat

variable {ι : Type u}

/--
The homeomorphism `I × (Σ i, A_i) ≅ Σ i, I × A_i`, sending
`(t,(i,a))` to `(i,(t,a))`.
-/
noncomputable def sigmaHomotopyIso
    {A : ι → Type u} [∀ i, TopologicalSpace (A i)] :
    (unitInterval × Σ i, A i) ≃ₜ Σ i, unitInterval × A i :=
  (Homeomorph.prodComm _ _).trans
    (Homeomorph.sigmaProdDistrib.trans
      { toEquiv :=
          { toFun := fun p => ⟨p.1, p.2.2, p.2.1⟩
            invFun := fun p => ⟨p.1, p.2.2, p.2.1⟩
            left_inv := fun p => by rcases p with ⟨i, x, t⟩; rfl
            right_inv := fun p => by rcases p with ⟨i, t, x⟩; rfl }
        continuous_toFun := (ContinuousMap.sigma (fun i =>
          (ContinuousMap.sigmaMk i).comp ContinuousMap.prodSwap)).continuous
        continuous_invFun := (ContinuousMap.sigma (fun i =>
          (ContinuousMap.sigmaMk i).comp ContinuousMap.prodSwap)).continuous })

/--
For component maps `g₀_i,g₁_i : A_i → B` with homotopies between them, the
assembled maps from `Σ i, A_i` to `B` are homotopic, componentwise in the
interval parameter.
-/
noncomputable def homotopySigma
    {A : ι → Type u} [∀ i, TopologicalSpace (A i)]
    {B : Type u} [TopologicalSpace B]
    {g₀ g₁ : ∀ i, ContinuousMap (A i) B}
    (H : ∀ i, ContinuousMap.Homotopy (g₀ i) (g₁ i)) :
    ContinuousMap.Homotopy (ContinuousMap.sigma g₀) (ContinuousMap.sigma g₁) where
  toContinuousMap := (((ContinuousMap.sigma fun i => (H i).toContinuousMap).comp
      (↑(sigmaHomotopyIso (A := A)) : C(unitInterval × Σ i, A i, Σ i, unitInterval × A i))) :
    C(unitInterval × Σ i, A i, B))
  map_zero_left := by rintro ⟨i, x⟩; exact (H i).map_zero_left x
  map_one_left := by rintro ⟨i, x⟩; exact (H i).map_one_left x

/--
The continuous map `(i,x) ↦ (i,e_i(x))` between the disjoint unions of a family
of homotopy equivalences.
-/
noncomputable def sigmaFwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap (Σ i, X i) (Σ i, Y i) :=
  ContinuousMap.sigma
    (fun i => (ContinuousMap.sigmaMk i).comp (e i).toFun)

/--
The continuous map `(i,y) ↦ (i,e_i⁻¹(y))` between the disjoint unions, using
the chosen homotopy inverse in each component.
-/
noncomputable def sigmaBwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap (Σ i, Y i) (Σ i, X i) :=
  ContinuousMap.sigma
    (fun i => (ContinuousMap.sigmaMk i).comp (e i).invFun)

/--
The inverse coproduct map after the forward map acts in component `i` by
`e_i⁻¹ ∘ e_i` and preserves the component tag.
-/
theorem sigmaBwd_comp_sigmaFwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    (sigmaBwd e).comp (sigmaFwd e) = ContinuousMap.sigma
      (fun i => (ContinuousMap.sigmaMk i).comp
        ((e i).invFun.comp (e i).toFun)) := by
  apply DFunLike.ext; rintro ⟨i, x⟩; rfl

/--
The forward coproduct map after the inverse map acts in component `i` by
`e_i ∘ e_i⁻¹` and preserves the component tag.
-/
theorem sigmaFwd_comp_sigmaBwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    (sigmaFwd e).comp (sigmaBwd e) = ContinuousMap.sigma
      (fun i => (ContinuousMap.sigmaMk i).comp
        ((e i).toFun.comp (e i).invFun)) := by
  apply DFunLike.ext; rintro ⟨i, x⟩; rfl

/--
The identity map on `Σ i, X_i` is the map assembled from its component inclusions.
-/
theorem sigma_id_eq
    {X : ι → Type u} [∀ i, TopologicalSpace (X i)] :
    ContinuousMap.id (Σ i, X i) =
      ContinuousMap.sigma (fun i => ContinuousMap.sigmaMk i) := by
  apply DFunLike.ext; rintro ⟨i, x⟩; rfl

/--
A family of homotopy equivalences `X_i ≃ Y_i` up to homotopy gives a homotopy
equivalence of their disjoint unions, using the component forward and inverse maps.
-/
noncomputable def sigmaHomotopyEquiv
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap.HomotopyEquiv (Σ i, X i) (Σ i, Y i) where
  toFun := sigmaFwd e
  invFun := sigmaBwd e
  left_inv := by rw [sigmaBwd_comp_sigmaFwd, sigma_id_eq]; exact ⟨homotopySigma fun i =>
      (ContinuousMap.Homotopy.refl (ContinuousMap.sigmaMk i)).comp (e i).left_inv.some⟩
  right_inv := by rw [sigmaFwd_comp_sigmaBwd, sigma_id_eq]; exact ⟨homotopySigma fun i =>
      (ContinuousMap.Homotopy.refl (ContinuousMap.sigmaMk i)).comp (e i).right_inv.some⟩

/--
The categorical coproduct of the forward maps of a family of topological
homotopy equivalences is a weak homotopy equivalence.
-/
theorem sigma_map_mem_weakHomotopyEquivalences
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    weakHomotopyEquivalences
      (Limits.Sigma.map (fun i => ofHom (e i).toFun)) := by
  have hE : weakHomotopyEquivalences
      (ofHom (sigmaHomotopyEquiv e).toFun) :=
    homotopyEquiv_toFun_mem (sigmaHomotopyEquiv e)
  have key : ∀ i, sigmaι (fun j => of (X j)) i ≫ ofHom (sigmaHomotopyEquiv e).toFun =
      ofHom (e i).toFun ≫ sigmaι (fun j => of (Y j)) i := by
    intro i; apply TopCat.hom_ext; apply ContinuousMap.ext; intro x; rfl
  have h_comm : (sigmaIsoSigma _).hom ≫ ofHom (sigmaHomotopyEquiv e).toFun =
      Limits.Sigma.map (fun i => ofHom (e i).toFun) ≫ (sigmaIsoSigma _).hom :=
    TopCat.sigmaIsoSigma_hom_naturality key
  have heq : Limits.Sigma.map (fun i => ofHom (e i).toFun) = (sigmaIsoSigma _).hom ≫
      ofHom (sigmaHomotopyEquiv e).toFun ≫ (sigmaIsoSigma _).inv := by
    rw [← Category.assoc, h_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr
    ((MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr hE)

end TopCat
