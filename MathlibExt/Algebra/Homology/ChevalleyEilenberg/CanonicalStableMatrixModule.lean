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
# The stable matrix module is the directed finite-matrix colimit

Let k be a commutative ring and A an associative unital k-algebra.
The k-modules Mat_m(A), m ∈ ℕ, form a diagram with top-left zero-extension
transitions. The underlying k-module of Mat_∞(A), with finite-stage
inclusions i_m, is their colimit.

Every compatible family of k-linear maps f_m : Mat_m(A) → T factors
through a unique k-linear map Mat_∞(A) → T sending i_m(X) to f_m(X).
The diagram and its colimit lie in ModuleCat^v(k), the world of the
algebra carrier, independently of the ring world u. Matrix size zero
is included in the diagram.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ring k and an associative unital
k-algebra A, the functor ℕ → ModuleCat^v(k) sends m to Mat_m(A).
The morphism m ≤ n is the k-linear top-left zero extension
Mat_m(A) → Mat_n(A). -/
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

/-- For a commutative ring k and an associative unital
k-algebra A, the maps i_m : Mat_m(A) → Mat_∞(A), viewed as
k-linear maps, form a cocone on the finite matrix module diagram.
Its point is the underlying module of the stable nonunital algebra. -/
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

/-- For a commutative ring k and an associative unital
k-algebra A, the finite-stage cocone on Mat_∞(A) is colimiting
in ModuleCat^v(k). A compatible family of maps Mat_m(A) → T
therefore extends uniquely to Mat_∞(A) → T, with value f_m(X)
on the finite-stage element i_m(X). -/
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
