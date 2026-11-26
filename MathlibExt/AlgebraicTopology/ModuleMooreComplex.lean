/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Moore terms as intersections of positive-face kernels

Let R be a ring and X a simplicial R-module, with the ring and module carrier universes
independent. Set N₀ = X₀ and Nₙ = ⋂_{i=1}ⁿ Ker(d_i : X_n → X_{n−1}) for n > 0. The categorical
Moore inclusion has exactly Nₙ as its range, giving an R-linear equivalence between the chosen
Moore term and this concrete submodule.

In these coordinates the normalized differential N_{n+1} → N_n is the zeroth face d₀. A
simplicial module map acts by its degree-n component restricted to N_n. The equivalence and
its inverse retain the values of the Moore inclusion and the given simplicial operators.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology.ModuleMooreComplex

variable {R : Type u} [Ring R]

/-- Module subobject of a categorical kernel.

For a morphism f : M → N in ModuleCat R, the submodule associated to the categorical kernel
subobject of f is LinearMap.ker f.hom. It consists exactly of the elements of M annihilated by
f. -/
theorem subobjectModule_kernel {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    ModuleCat.subobjectModule M (kernelSubobject f) = LinearMap.ker f.hom := by
  ext x
  change x ∈ LinearMap.range (kernelSubobject f).arrow.hom ↔ f.hom x = 0
  constructor
  · rintro ⟨z, rfl⟩
    have h := congrArg (fun h => h.hom z) (kernelSubobject_arrow_comp f)
    exact h
  · intro h
    refine ⟨ModuleCat.toKernelSubobject ⟨x, h⟩, ?_⟩
    exact ModuleCat.toKernelSubobject_arrow ⟨x, h⟩

variable (X : SimplicialObject (ModuleCat.{v} R))

/-- Intersection of positive-face kernels in a simplicial module.

For a simplicial R-module X, normalizedSubmodule X 0 is all of X₀. In degree n+1 it is the
intersection of Ker(d_{j+1}) for j ∈ Fin(n+1), hence of all positive faces X_{n+1} → X_n. -/
def normalizedSubmodule : (n : ℕ) → Submodule R (X.obj (op ⦋n⦌))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun j : Fin (n + 1) => LinearMap.ker (X.δ j.succ).hom

/-- Range of the Moore inclusion in module coordinates.

For every n, the range of the degree-n Moore inclusion N(X)_n → X_n is normalizedSubmodule X
n, the intersection of positive-face kernels, with the full module at degree zero. -/
theorem inclusion_range (n : ℕ) :
    LinearMap.range ((inclusionOfMooreComplexMap X).f n).hom = normalizedSubmodule X n := by
  rw [inclusionOfMooreComplexMap_f]
  change ModuleCat.subobjectModule (X.obj (op ⦋n⦌))
    (NormalizedMooreComplex.objX X n) = normalizedSubmodule X n
  cases n with
  | zero =>
    change ModuleCat.subobjectModule (X.obj (op ⦋0⦌)) ⊤ = ⊤
    exact map_top _
  | succ n =>
    change ModuleCat.subobjectModule (X.obj (op ⦋n + 1⦌))
      (Finset.univ.inf fun j : Fin (n + 1) => kernelSubobject (X.δ j.succ)) =
        Finset.univ.inf fun j : Fin (n + 1) => LinearMap.ker (X.δ j.succ).hom
    rw [map_finset_inf]
    congr 1
    funext j
    exact subobjectModule_kernel (X.δ j.succ)

/-- Linear coordinates for a normalized Moore term.

For a simplicial module X over a ring R and n : ℕ, restrict the Moore inclusion to its range.
This gives N(X)_n ≃ₗ[R] normalizedSubmodule X n, with independent ring and module carrier
universes. -/
def termEquiv (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{v} R)).obj X).X n ≃ₗ[R] normalizedSubmodule X n := by
  let l := ((inclusionOfMooreComplexMap X).f n).hom.codRestrict (normalizedSubmodule X n)
    (fun x => by rw [← inclusion_range X n]; exact LinearMap.mem_range_self _ x)
  have hi : Function.Injective ((inclusionOfMooreComplexMap X).f n) := by
    rw [inclusionOfMooreComplexMap_f]
    exact (ModuleCat.mono_iff_injective
      (NormalizedMooreComplex.objX X n).arrow).mp
        (Subobject.arrow_mono (NormalizedMooreComplex.objX X n))
  refine LinearEquiv.ofBijective l ⟨?_, ?_⟩
  · intro x y h
    exact hi (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    have hy' : y ∈ LinearMap.range ((inclusionOfMooreComplexMap X).f n).hom := by
      rw [inclusion_range X n]
      exact hy
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, Subtype.ext hx⟩

/-- Value of the Moore-term coordinate equivalence.

For x ∈ N(X)_n, the underlying element of X_n obtained by termEquiv is the value of the
degree-n Moore inclusion on x. -/
@[simp]
theorem termEquiv_value (n : ℕ)
    (x : ((normalizedMooreComplex (ModuleCat.{v} R)).obj X).X n) :
    (termEquiv X n x).val = ((inclusionOfMooreComplexMap X).f n).hom x := rfl

/-- Value of the inverse Moore-term coordinate equivalence.

For x in the intersection of the positive-face kernels at degree n, applying termEquiv⁻¹ and
then the Moore inclusion returns the underlying element x in X_n. -/
@[simp]
theorem termEquiv_symm_value (n : ℕ) (x : normalizedSubmodule X n) :
    ((inclusionOfMooreComplexMap X).f n).hom ((termEquiv X n).symm x) = x.val :=
  congrArg Subtype.val ((termEquiv X n).apply_symm_apply x)

/-- Positive-face vanishing criterion for Moore coordinates.

An element x ∈ X_{n+1} belongs to normalizedSubmodule X (n+1) exactly when d_{j+1}(x) = 0 for
every j ∈ Fin(n+1). -/
theorem mem_normalizedSubmodule (n : ℕ) (x : X.obj (op ⦋n + 1⦌)) :
    x ∈ normalizedSubmodule X (n + 1) ↔
      ∀ j : Fin (n + 1), (X.δ j.succ).hom x = 0 := by
  classical
  have h : ∀ s : Finset (Fin (n + 1)),
      x ∈ s.inf (fun j => LinearMap.ker (X.δ j.succ).hom) ↔
        ∀ j ∈ s, x ∈ LinearMap.ker (X.δ j.succ).hom := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => simp [Finset.inf_insert, Submodule.mem_inf, ih]
  simpa only [normalizedSubmodule, Finset.mem_univ, forall_const, LinearMap.mem_ker] using
    h Finset.univ

/-- Zeroth-face formula for the normalized Moore differential.

For x ∈ N(X)_{n+1}, the normalized differential followed by degree-n coordinates equals d₀
applied to the degree-(n+1) coordinates of x. Thus the Moore differential is the zeroth face
on the positive-face kernel intersection. -/
theorem termEquiv_d_value (n : ℕ)
    (x : ((normalizedMooreComplex (ModuleCat.{v} R)).obj X).X (n + 1)) :
    (termEquiv X n
      ((((normalizedMooreComplex (ModuleCat.{v} R)).obj X).d (n + 1) n).hom x)).val =
        (X.δ (0 : Fin (n + 2))).hom (termEquiv X (n + 1) x).val := by
  have h : (((normalizedMooreComplex (ModuleCat.{v} R)).obj X).d (n + 1) n) ≫
      (inclusionOfMooreComplexMap X).f n =
        (inclusionOfMooreComplexMap X).f (n + 1) ≫ X.δ (0 : Fin (n + 2)) := by
    rw [normalizedMooreComplex_objD, inclusionOfMooreComplexMap_f,
      inclusionOfMooreComplexMap_f]
    cases n with
    | zero =>
      let t : Subobject (X.obj (op ⦋0⦌)) := ⊤
      let a := (NormalizedMooreComplex.objX X 1).arrow
      let d := X.δ (0 : Fin 2)
      have h : (a ≫ d ≫ inv t.arrow) ≫ t.arrow = a ≫ d :=
        (congrArg (fun f => f ≫ t.arrow) (Category.assoc a d (inv t.arrow)).symm).trans
          ((Category.assoc (a ≫ d) (inv t.arrow) t.arrow).trans
            ((congrArg (fun f => (a ≫ d) ≫ f) (IsIso.inv_hom_id t.arrow)).trans
              (Category.comp_id _)))
      exact h
    | succ n =>
      dsimp only [NormalizedMooreComplex.objD]
      exact Subobject.factorThru_arrow _ _ _
  exact congrArg (fun h => h.hom x) h

/-- Component formula for a normalized simplicial module map.

For f : X → Y, n : ℕ and x ∈ N(X)_n, the coordinates of N(f)_n(x) are f_n applied to the
coordinates of x. Both equivalences use the corresponding Moore inclusions. -/
theorem termEquiv_map_value {Y : SimplicialObject (ModuleCat.{v} R)} (f : X ⟶ Y)
    (n : ℕ) (x : ((normalizedMooreComplex (ModuleCat.{v} R)).obj X).X n) :
    (termEquiv Y n
      ((((normalizedMooreComplex (ModuleCat.{v} R)).map f).f n).hom x)).val =
        (f.app (op ⦋n⦌)).hom (termEquiv X n x).val := by
  have h := congrArg (fun h => (h.f n).hom x)
    ((inclusionOfMooreComplex (ModuleCat.{v} R)).naturality f)
  exact h

end AlgebraicTopology.ModuleMooreComplex

end
