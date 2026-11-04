/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.style.haveILetI false

/-!
# Multiplicity of an irreducible representation

For a finite group `G` and irreducible representations `ρ`, `σ` over an
algebraically closed field `k`, Schur's lemma gives the dimension of the
intertwining space `Hom_G(ρ, σ)`: it is `1` if `ρ` and `σ` are equivalent
and `0` otherwise. Consequently, if `σ` is equivalent to a direct sum
`⨁ i, (ρ i) ^ (d i)` of pairwise non-equivalent irreducibles, the
multiplicity `d i` equals the dimension of the intertwining space
`Hom_G(ρ i, σ)`.

Source: `v1/Atlas/AlgebraNotes/code/Characters.lean` (theorems
`CharacterTheory.schur_dim_HomG` and
`CharacterTheory.multiplicity_eq_finrank_intertwining`). The v1 file also
contains an unproved existence statement for such a decomposition
(`maschke_irreducible_decomposition`); existence is NOT ported here.
Instead, the decomposition is a hypothesis of the multiplicity theorem.
This complements `CharacterTheory.irred_dim_dvd_card` (Batch 7) and
`CharacterTheory.irreducible_iff_classInnerProduct_self_eq_one`
(Batch 10), the other character-theoretic theorems from the same v1 file.
-/

@[expose] public section

noncomputable section

namespace CharacterTheory

universe uK uG uV uW

open scoped Classical in
/-- **Schur's lemma, dimension form.** Let $G$ be a finite group, $k$ an algebraically closed
field, and $\rho$, $\sigma$ irreducible representations of $G$ on finite-dimensional $k$-vector
spaces. Then the space $\operatorname{Hom}_G(\rho, \sigma)$ of intertwining maps from $\rho$ to
$\sigma$ has dimension $1$ over $k$ if $\sigma$ and $\rho$ are equivalent, and dimension $0$
otherwise. -/
theorem finrank_intertwiningMap_eq_one_or_zero
    {k : Type uK} [Field k] [IsAlgClosed k]
    {G : Type uG} [Group G] [Fintype G]
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type uW} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    Module.finrank k (ρ.IntertwiningMap σ) =
      if Nonempty (Representation.Equiv σ ρ) then 1 else 0 := by
  split_ifs with h
  · obtain ⟨e⟩ := h
    have equiv : (ρ.IntertwiningMap σ) ≃ₗ[k] (σ.IntertwiningMap σ) := {
      toFun := fun f => Representation.IntertwiningMap.comp f e.toIntertwiningMap
      invFun := fun g => Representation.IntertwiningMap.comp g e.symm.toIntertwiningMap
      left_inv := by intro f; ext v; simp [Representation.IntertwiningMap.comp]
      right_inv := by intro g; ext w; simp [Representation.IntertwiningMap.comp]
      map_add' := by intro f g; ext; simp [Representation.IntertwiningMap.comp]
      map_smul' := by intro c f; ext; simp [Representation.IntertwiningMap.comp]
    }
    rw [LinearEquiv.finrank_eq equiv]
    exact Representation.IsIrreducible.finrank_intertwiningMap_self σ
  · haveI : IsEmpty (ρ.Equiv σ) := by
      rw [isEmpty_iff]; intro e; exact h ⟨e.symm⟩
    haveI : Subsingleton (ρ.IntertwiningMap σ) := inferInstance
    exact Module.finrank_zero_of_subsingleton

/-- **Multiplicity equals the dimension of the intertwining space.** Let $G$ be a finite group,
$k$ an algebraically closed field, and $(\rho_i)_{i \in I}$ a family, indexed by a finite set $I$,
of irreducible representations of $G$ on finite-dimensional $k$-vector spaces that are pairwise
non-equivalent: $\rho_i$ and $\rho_j$ are not equivalent whenever $i \ne j$. Let $\sigma$ be a
representation of $G$ on a finite-dimensional $k$-vector space, and let $(d_i)_{i \in I}$ be
natural numbers such that $\sigma$ is equivalent to the direct sum of $d_i$ copies of $\rho_i$ over
all $i \in I$. Then for every $i \in I$, $d_i$ equals the dimension over $k$ of the space
$\operatorname{Hom}_G(\rho_i, \sigma)$ of intertwining maps from $\rho_i$ to $\sigma$. -/
theorem multiplicity_eq_finrank_intertwiningMap
    {G k : Type*} [Group G] [Fintype G] [Field k] [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (h_pairwise : ∀ i j, i ≠ j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k G W)
    (d : ι → ℕ)
    (h_decomp : Nonempty (Representation.Equiv σ
      (Representation.directSum (ι := (i : ι) × Fin (d i)) (fun p => ρ p.1)))) :
    ∀ i, d i = Module.finrank k ((ρ i).IntertwiningMap σ) := by
  have h_hom_dist : ∀ i, Module.finrank k ((ρ i).IntertwiningMap σ) =
      ∑ p : (j : ι) × Fin (d j),
        Module.finrank k ((ρ i).IntertwiningMap (ρ p.1)) := by
    intro i
    obtain ⟨e⟩ := h_decomp
    have equiv1 : (ρ i).IntertwiningMap σ ≃ₗ[k] (ρ i).IntertwiningMap
        (Representation.directSum (ι := (j : ι) × Fin (d j)) (fun p => ρ p.1)) := {
      toFun := fun f => Representation.IntertwiningMap.comp e.toIntertwiningMap f
      invFun := fun g => Representation.IntertwiningMap.comp e.symm.toIntertwiningMap g
      left_inv := fun f => by ext v; simp [Representation.IntertwiningMap.comp]
      right_inv := fun g => by ext w; simp [Representation.IntertwiningMap.comp]
      map_add' := fun f g => by ext; simp [Representation.IntertwiningMap.comp]
      map_smul' := fun c f => by ext; simp [Representation.IntertwiningMap.comp]
    }
    have equiv2 : (ρ i).IntertwiningMap
        (Representation.directSum (ι := (j : ι) × Fin (d j)) (fun p => ρ p.1)) ≃ₗ[k]
        ((p : (j : ι) × Fin (d j)) → (ρ i).IntertwiningMap (ρ p.1)) := {
      toFun := fun f p => {
        toLinearMap := (DirectSum.component k _ _ p).comp f.toLinearMap
        isIntertwining' := fun g => by
          ext u; simp only [LinearMap.comp_apply]
          have hf := congr($(f.isIntertwining' g) u)
          simp only [LinearMap.comp_apply] at hf
          show (DirectSum.component k _ _ p) (f.toLinearMap ((ρ i) g u)) =
               (ρ p.1 g) ((DirectSum.component k _ _ p) (f.toLinearMap u))
          rw [hf]
          simp only [Representation.directSum, DirectSum.component, DirectSum.lmap]; rfl
      }
      invFun := fun fs => {
        toLinearMap := (DirectSum.linearEquivFunOnFintype k _ _).symm.toLinearMap.comp
          (LinearMap.pi (fun p => (fs p).toLinearMap))
        isIntertwining' := fun g => by
          have key : ∀ p u, (fs p).toLinearMap ((ρ i) g u) =
              (ρ p.1 g) ((fs p).toLinearMap u) := by
            intro p u; exact congr($(((fs p).isIntertwining' g)) u)
          apply LinearMap.ext; intro u
          simp only [LinearMap.comp_apply]
          apply DFinsupp.ext; intro p
          simp only [Representation.directSum, DirectSum.lmap,
            DirectSum.linearEquivFunOnFintype, DFinsupp.linearEquivFunOnFintype,
            DFinsupp.mapRange.linearMap]
          exact key p u
      }
      left_inv := fun f => by
        apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro u
        simp only [LinearMap.comp_apply]; apply DFinsupp.ext; intro p; rfl
      right_inv := fun fs => by
        funext p; apply Representation.IntertwiningMap.ext
        apply LinearMap.ext; intro u
        simp only [LinearMap.comp_apply]; rfl
      map_add' := fun f g => by
        funext p; apply Representation.IntertwiningMap.ext
        apply LinearMap.ext; intro u
        simp [LinearMap.comp_apply, map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun c f => by
        funext p; apply Representation.IntertwiningMap.ext
        apply LinearMap.ext; intro u
        simp [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, Pi.smul_apply]
    }
    rw [LinearEquiv.finrank_eq equiv1, LinearEquiv.finrank_eq equiv2,
        Module.finrank_pi_fintype]
  intro idx
  rw [h_hom_dist idx]
  have h_schur : ∀ p : (j : ι) × Fin (d j),
      Module.finrank k ((ρ idx).IntertwiningMap (ρ p.1)) =
      if p.1 = idx then 1 else 0 := by
    intro ⟨j, _⟩
    simp only
    by_cases h : j = idx
    · cases h
      simp only [ite_true]
      exact Representation.IsIrreducible.finrank_intertwiningMap_self (ρ idx)
    · simp only [h, ite_false]
      have hne : ¬Nonempty ((ρ idx).Equiv (ρ j)) :=
        h_pairwise idx j (fun hij => h hij.symm)
      haveI : IsEmpty ((ρ idx).Equiv (ρ j)) := isEmpty_iff.mpr (fun e => hne ⟨e⟩)
      haveI : Subsingleton ((ρ idx).IntertwiningMap (ρ j)) := inferInstance
      exact Module.finrank_zero_of_subsingleton
  simp_rw [h_schur]
  rw [Fintype.sum_sigma]
  have h1 : ∀ x : ι, ∑ _ : Fin (d x), (if x = idx then 1 else 0 : ℕ) =
    d x • (if x = idx then 1 else 0 : ℕ) := by
    intro x; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [h1, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

end CharacterTheory

end
