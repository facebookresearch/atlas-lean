/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.FiniteTupleEquiv

/-!
# Homogeneous cochains in continuous tuple coordinates

Let k be a ring with a topology, G a locally compact topological group
and X a topological k-representation. Tuple-form degree q homogeneous
cochains are the submodule of C(G^(q+1),X) satisfying
F(g t₀,…,g t_q)=g • F(t₀,…,t_q), with its subspace topology.

The differential is
(dF)(t)=∑_(j=0)^(q+1) (-1)^j • F(t with coordinate j deleted).
Successive differentials compose to zero. Finite-tuple uncurrying gives a
continuous k-linear isomorphism from the nested invariant homogeneous
complex to this entire nonnegative tuple-form complex, preserving every
coordinate value.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v w
namespace ContinuousCohomology
variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Tuple-form degree q homogeneous cochains are the submodule of
C(G^(q+1),X) consisting of F with
F(g t₀,…,g t_q)=g • F(t₀,…,t_q) for all g and tuples t. -/
def flatHomogeneousCochains (X : TopRep.{max v w, u, v} k G) (q : ℕ) :
    Submodule k C(Fin (q + 1) → G, X) where
  carrier := {f | ∀ (g : G) (t : Fin (q + 1) → G),
    f (fun i => g * t i) = X.ρ g (f t)}
  zero_mem' := by intro g t; simp
  add_mem' := by
    intro f h hf hh g t
    change f (fun i => g * t i) + h (fun i => g * t i) = X.ρ g (f t + h t)
    rw [map_add, hf g t, hh g t]
  smul_mem' := by
    intro r f hf g t
    change r • f (fun i => g * t i) = X.ρ g (r • f t)
    rw [map_smul, hf g t]

private theorem homogeneous_map_eq
    (X : TopRep.{max v w, u, v} k G) (q : ℕ) :
    ((TopRep.resolution'X X q).ρ.invariants).map
        (resolutionFinContinuousLinearEquiv X (q + 1)).toLinearEquiv.toLinearMap =
      flatHomogeneousCochains X q := by
  apply le_antisymm
  · intro f hf
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hf
    change ∀ (g : G) (t : Fin (q + 1) → G),
      resolutionFinContinuousLinearEquiv X (q + 1) c (fun i => g * t i) =
        X.ρ g (resolutionFinContinuousLinearEquiv X (q + 1) c t)
    intro g t
    have h := congrArg
      (fun a : TopRep.resolutionX X (q + 1) =>
        resolutionFinContinuousLinearEquiv X (q + 1) a (fun i => g * t i)) (hc g)
    rw [resolutionFinContinuousLinearEquiv_action] at h
    have ht : (fun i => g⁻¹ * (g * t i)) = t := by
      funext i
      simp only [inv_mul_cancel_left]
    rw [ht] at h
    exact h.symm
  · intro f hf
    obtain ⟨c, hc⟩ := homogeneousFinContinuousLinearEquiv_lift X q f hf
    refine Submodule.mem_map.mpr ⟨c.val, c.property, ?_⟩
    apply ContinuousMap.ext
    intro t
    exact (resolutionFinContinuousLinearEquiv_apply X (q + 1) c.val t).trans (hc t)

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
Restricting finite-tuple uncurrying to invariants gives
C_hom^q(G,X) ≅L[k] F_hom^q(G,X), where the right side consists
of continuous homogeneous-equivariant tuple functions. -/
def homogeneousFinContinuousLinearEquiv
    (X : TopRep.{max v w, u, v} k G) (q : ℕ) :
    (TopRep.homogeneousCochains X).X q ≃L[k] flatHomogeneousCochains X q :=
  (resolutionFinContinuousLinearEquiv X (q + 1)).ofSubmodules
    (TopRep.resolution'X X q).ρ.invariants (flatHomogeneousCochains X q)
    (by exact homogeneous_map_eq X q)

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
The invariant degree q comparison sends a nested cochain c to
the function t ↦ E_(q+1)(c)(t). -/
theorem homogeneousFinContinuousLinearEquiv_apply
    (X : TopRep.{max v w, u, v} k G) (q : ℕ)
    (c : (TopRep.homogeneousCochains X).X q) (t : Fin (q + 1) → G) :
    (homogeneousFinContinuousLinearEquiv X q c).val t =
      resolutionFinUncurry X (q + 1) c.val t := by
  change resolutionFinContinuousLinearEquiv X (q + 1) c.val t = _
  exact resolutionFinContinuousLinearEquiv_apply X (q + 1) c.val t

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
For a tuple-form homogeneous F, the inverse nested cochain
evaluates to F(t) on every (q+1)-tuple t. -/
theorem homogeneousFinContinuousLinearEquiv_symm_apply
    (X : TopRep.{max v w, u, v} k G) (q : ℕ)
    (f : flatHomogeneousCochains X q) (t : Fin (q + 1) → G) :
    resolutionFinUncurry X (q + 1)
      ((homogeneousFinContinuousLinearEquiv X q).symm f).val t = f.val t := by
  have h := congrArg (fun a : flatHomogeneousCochains X q => a.val t)
    ((homogeneousFinContinuousLinearEquiv X q).apply_symm_apply f)
  rw [homogeneousFinContinuousLinearEquiv_apply] at h
  exact h

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
The tuple-form homogeneous term is the topological k-module
F_hom^q(G,X) with the subspace topology from C(G^(q+1),X). -/
abbrev flatHomogeneousTerm (X : TopRep.{max v w, u, v} k G) (q : ℕ) :
    TopModuleCat k := TopModuleCat.of k (flatHomogeneousCochains X q)

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
The nested and tuple-form degree q homogeneous cochain terms
are isomorphic in the topological k-module category by continuous
linear uncurrying. -/
def homogeneousFinIso (X : TopRep.{max v w, u, v} k G) (q : ℕ) :
    (TopRep.homogeneousCochains X).X q ≅ flatHomogeneousTerm X q :=
  TopModuleCat.ofIso (homogeneousFinContinuousLinearEquiv X q)

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
The tuple-form differential F_hom^q(G,X) → F_hom^(q+1)(G,X)
is the nested homogeneous differential transported through the
finite-tuple invariant equivalences. -/
def flatHomogeneousD (X : TopRep.{max v w, u, v} k G) (q : ℕ) :
    flatHomogeneousTerm X q ⟶ flatHomogeneousTerm X (q + 1) :=
  (homogeneousFinIso X q).inv ≫ (TopRep.homogeneousCochains X).d q (q + 1) ≫
    (homogeneousFinIso X (q + 1)).hom

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
On a (q+2)-tuple t, the differential is
(dF)(t)=∑_(j=0)^(q+1) (-1)^j • F(t with coordinate j deleted). -/
theorem flatHomogeneousD_apply (X : TopRep.{max v w, u, v} k G) (q : ℕ)
    (f : flatHomogeneousCochains X q) (t : Fin (q + 2) → G) :
    (flatHomogeneousD X q f).val t =
      ∑ j : Fin (q + 2), (-1 : k) ^ (j : ℕ) • f.val (fun i => t (j.succAbove i)) := by
  let c := (homogeneousFinContinuousLinearEquiv X q).symm f
  have hd : (((TopRep.homogeneousCochains X).d q (q + 1)).hom c).val =
      (TopRep.d X (q + 1)).hom c.val := by
    rw [TopRep.homogeneousCochains.d_eq]
    rfl
  change (homogeneousFinContinuousLinearEquiv X (q + 1)
    (((TopRep.homogeneousCochains X).d q (q + 1)).hom c)).val t = _
  rw [homogeneousFinContinuousLinearEquiv_apply, hd]
  calc
    _ = ∑ j : Fin (q + 2), (-1 : k) ^ (j : ℕ) •
        resolutionFinUncurry X (q + 1) c.val (fun i => t (j.succAbove i)) :=
      resolutionFinUncurry_d X q c.val t
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [homogeneousFinContinuousLinearEquiv_symm_apply]

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
The tuple-form differentials obey d_(q+1) ∘ d_q=0
for every q ∈ ℕ. -/
theorem flatHomogeneousD_comp (X : TopRep.{max v w, u, v} k G) (q : ℕ) :
    flatHomogeneousD X q ≫ flatHomogeneousD X (q + 1) = 0 := by
  simp only [flatHomogeneousD, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((TopRep.homogeneousCochains X).d q (q + 1))
    ((TopRep.homogeneousCochains X).d (q + 1) (q + 1 + 1)),
    (TopRep.homogeneousCochains X).d_comp_d]
  simp

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
These tuple-form terms and differentials form the entire
nonnegative cochain complex F_hom^•(G,X). -/
abbrev flatHomogeneousComplex (X : TopRep.{max v w, u, v} k G) :
    CochainComplex (TopModuleCat k) ℕ :=
  CochainComplex.of (flatHomogeneousTerm X) (flatHomogeneousD X) (flatHomogeneousD_comp X)

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
Finite-tuple uncurrying gives the cochain-complex isomorphism
C_hom^•(G,X) ≅ F_hom^•(G,X), with continuous k-linear inverses
in every degree. -/
def homogeneousFlatComplexIso (X : TopRep.{max v w, u, v} k G) :
    TopRep.homogeneousCochains X ≅ flatHomogeneousComplex X :=
  HomologicalComplex.Hom.isoOfComponents (homogeneousFinIso X) (by
    intro i j hij
    have h : i + 1 = j := hij
    subst j
    dsimp only [flatHomogeneousComplex]
    rw [CochainComplex.of_d]
    simp [flatHomogeneousD])

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
The forward degree q component of the complex isomorphism sends
c to the homogeneous tuple function t ↦ E_(q+1)(c)(t). -/
theorem homogeneousFlatComplexIso_hom_apply
    (X : TopRep.{max v w, u, v} k G) (q : ℕ)
    (c : (TopRep.homogeneousCochains X).X q) (t : Fin (q + 1) → G) :
    ((homogeneousFlatComplexIso X).hom.f q c).val t =
      resolutionFinUncurry X (q + 1) c.val t := by
  exact homogeneousFinContinuousLinearEquiv_apply X q c t

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
The inverse degree q component sends F to the nested invariant
cochain whose evaluation at every tuple t is F(t). -/
theorem homogeneousFlatComplexIso_inv_apply
    (X : TopRep.{max v w, u, v} k G) (q : ℕ)
    (f : flatHomogeneousCochains X q) (t : Fin (q + 1) → G) :
    resolutionFinUncurry X (q + 1) ((homogeneousFlatComplexIso X).inv.f q f).val t =
      f.val t := by
  exact homogeneousFinContinuousLinearEquiv_symm_apply X q f t
end ContinuousCohomology
