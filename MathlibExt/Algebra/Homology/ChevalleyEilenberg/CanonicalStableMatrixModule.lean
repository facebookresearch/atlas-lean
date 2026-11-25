/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.DirectLimit
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrix

/-!
# The stable matrix module as a colimit

For a commutative ring `k` and a unital `k`-algebra `A`, finite square matrix
modules form a diagram indexed by `ℕ` under top-left zero extension. Their
colimit is the underlying `k`-module of the stable matrix algebra, with
cocone legs given by the finite-stage inclusions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- Finite matrix modules and their top-left zero-extension maps. -/
def matrixModuleFunctor : ℕ ⥤ ModuleCat.{v} k where
  obj m := ModuleCat.of k (Matrix (Fin m) (Fin m) A)
  map h := ModuleCat.ofHom (Matrix.zeroExtendLinear (k := k) (A := A) (leOfHom h))
  map_id m := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Matrix.zeroExtend (le_rfl : m ≤ m) x = x
    exact Matrix.zeroExtend_self x
  map_comp h h' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Matrix.zeroExtend (leOfHom (h ≫ h')) x =
      Matrix.zeroExtend (leOfHom h') (Matrix.zeroExtend (leOfHom h) x)
    exact (Matrix.zeroExtend_comp (leOfHom h) (leOfHom h') x).symm

/-- The cocone on the stable matrix module given by the finite-stage inclusions. -/
def canonicalStableMatrixModuleCocone : Cocone (matrixModuleFunctor k A) where
  pt := ModuleCat.of k (canonicalStableMatrixAlgebra k A)
  ι :=
    { app := fun m => ModuleCat.ofHom (canonicalStableMatrixInclusion k A m :
        Matrix (Fin m) (Fin m) A →ₗ[k] canonicalStableMatrixAlgebra k A)
      naturality m n h := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change canonicalStableMatrixInclusion k A n (Matrix.zeroExtend (leOfHom h) x) =
          canonicalStableMatrixInclusion k A m x
        exact DirectLimit.NonUnitalAlgebra.of_f (R := k)
          (G := fun m : ℕ => Matrix (Fin m) (Fin m) A)
          (f := fun m n h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
          (i := m) (j := n) (leOfHom h) x }

/-- The finite-stage cocone on the stable matrix module is colimiting. -/
def canonicalStableMatrixModuleIsColimit : IsColimit (canonicalStableMatrixModuleCocone k A) := by
  let hg (s : Cocone (matrixModuleFunctor k A)) :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Matrix (Fin m) (Fin m) A),
        (s.ι.app n).hom (Matrix.zeroExtendAlgHom (k := k) (A := A) h x) = (s.ι.app m).hom x := by
    intro m n h x
    have hw := congrArg (fun f : (matrixModuleFunctor k A).obj m ⟶ s.pt => f.hom x)
      (s.w (homOfLE h))
    change (s.ι.app n).hom (Matrix.zeroExtend h x) = (s.ι.app m).hom x at hw
    exact hw
  refine
    { desc := fun s => ModuleCat.ofHom
        (DirectLimit.Module.lift (P := s.pt) k ℕ (fun m : ℕ => Matrix (Fin m) (Fin m) A)
          (fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
          (fun m => (show ModuleCat.of k (Matrix (Fin m) (Fin m) A) ⟶ s.pt
            from s.ι.app m).hom) (hg s))
      fac := ?_
      uniq := ?_ }
  · intro s m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (DirectLimit.Module.lift (P := s.pt) k ℕ (fun m : ℕ => Matrix (Fin m) (Fin m) A)
      (fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
      (fun m => (show ModuleCat.of k (Matrix (Fin m) (Fin m) A) ⟶ s.pt
            from s.ι.app m).hom) (hg s))
        (canonicalStableMatrixInclusion k A m x) =
        (s.ι.app m).hom x
    exact DirectLimit.Module.lift_of (R := k) (ι := ℕ)
      (G := fun m : ℕ => Matrix (Fin m) (Fin m) A)
      (f := fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
      (P := s.pt) (g := fun m =>
        (show ModuleCat.of k (Matrix (Fin m) (Fin m) A) ⟶ s.pt from s.ι.app m).hom)
      (Hg := hg s) (i := m) x
  · intro s f hf
    apply ModuleCat.hom_ext
    apply DirectLimit.Module.hom_ext
    intro m
    apply LinearMap.ext
    intro x
    have hm := congrArg (fun g : (matrixModuleFunctor k A).obj m ⟶ s.pt => g.hom x) (hf m)
    change f.hom (canonicalStableMatrixInclusion k A m x) = (s.ι.app m).hom x at hm
    change f.hom (canonicalStableMatrixInclusion k A m x) =
      (DirectLimit.Module.lift (P := s.pt) k ℕ (fun m : ℕ => Matrix (Fin m) (Fin m) A)
        (fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
        (fun m => (show ModuleCat.of k (Matrix (Fin m) (Fin m) A) ⟶ s.pt
            from s.ι.app m).hom) (hg s))
          (canonicalStableMatrixInclusion k A m x)
    exact hm.trans (DirectLimit.Module.lift_of (R := k) (ι := ℕ)
      (G := fun m : ℕ => Matrix (Fin m) (Fin m) A)
      (f := fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
      (P := s.pt) (g := fun m =>
        (show ModuleCat.of k (Matrix (Fin m) (Fin m) A) ⟶ s.pt from s.ι.app m).hom)
      (Hg := hg s) (i := m) x).symm

end ChevalleyEilenberg
