/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
# Coproducts of topological homotopy equivalences

This file is part of the KQ3 layer. For a `Type u` family of topological
homotopy equivalences, the coproduct maps assemble into a homotopy equivalence
of disjoint unions via `ContinuousMap.sigma` and product-coproduct
distributivity. The categorical `Limits.Sigma.map` is identified with the
bundled coproduct map through `TopCat.sigmaIsoSigma`, hence lies in
`TopCat.weakHomotopyEquivalences` by the staged bridge.
No `SSet` coproduct, pushout, transfinite, factorization, or model claim.
-/

@[expose] public section

universe u

open CategoryTheory

namespace TopCat

variable {ι : Type u}

/-- Distributivity homeomorphism for homotopies over a coproduct. -/
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

/-- Homotopies out of a coproduct assemble from component homotopies. -/
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

/-- Forward coproduct map of homotopy equivalences. -/
noncomputable def sigmaFwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap (Σ i, X i) (Σ i, Y i) :=
  ContinuousMap.sigma
    (fun i => (ContinuousMap.sigmaMk i).comp (e i).toFun)

/-- Backward coproduct map of homotopy equivalences. -/
noncomputable def sigmaBwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    ContinuousMap (Σ i, Y i) (Σ i, X i) :=
  ContinuousMap.sigma
    (fun i => (ContinuousMap.sigmaMk i).comp (e i).invFun)

/-- Backward-forward composite is the coproduct of the composites. -/
theorem sigmaBwd_comp_sigmaFwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    (sigmaBwd e).comp (sigmaFwd e) = ContinuousMap.sigma
      (fun i => (ContinuousMap.sigmaMk i).comp
        ((e i).invFun.comp (e i).toFun)) := by
  apply DFunLike.ext; rintro ⟨i, x⟩; rfl

/-- Forward-backward composite is the coproduct of the composites. -/
theorem sigmaFwd_comp_sigmaBwd
    {X Y : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (X i) (Y i)) :
    (sigmaFwd e).comp (sigmaBwd e) = ContinuousMap.sigma
      (fun i => (ContinuousMap.sigmaMk i).comp
        ((e i).toFun.comp (e i).invFun)) := by
  apply DFunLike.ext; rintro ⟨i, x⟩; rfl

/-- The identity is the coproduct of the inclusions. -/
theorem sigma_id_eq
    {X : ι → Type u} [∀ i, TopologicalSpace (X i)] :
    ContinuousMap.id (Σ i, X i) =
      ContinuousMap.sigma (fun i => ContinuousMap.sigmaMk i) := by
  apply DFunLike.ext; rintro ⟨i, x⟩; rfl

/-- Coproduct of a family of topological homotopy equivalences. -/
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

/-- The categorical coproduct map of homotopy equivalences is a weak homotopy
equivalence. -/
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
