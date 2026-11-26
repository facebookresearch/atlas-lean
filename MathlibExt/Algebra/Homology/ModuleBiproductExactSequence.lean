/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ModuleProductExact

/-!
# Exact finite biproducts of composable module sequences

Let R be a ring in u, I a finite type in v, and W=max(u,v). For n-arrow module sequences S_i,
form their objectwise biproduct, with j-th object ⊕_i S_i^j and each transition the biproduct
map of the component transitions.

If every component sequence has zero adjacent composites, so does the biproduct sequence. If
each component is exact at all interior objects, the biproduct is exact there as well. The
length n is arbitrary and the finite index set may be empty.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ComposableArrows

variable {R : Type u} [Ring R] {I : Type v} [Finite I] {n : ℕ}
  (S : I → ComposableArrows (ModuleCat.{max u v} R) n)

/-- Let R be a ring in u, I a finite type in v, W=max(u,v), and S_i an n-arrow sequence of modules
in ModuleCat_W(R), with objects S_i^0→⋯→S_i^n. The resulting sequence has j-th object ⊕_i S_i^j
for 0≤j≤n, and its map for any j≤k is ⊕_i(S_i^{j→k}). These maps preserve the composable-arrow
identities and compositions. -/
def moduleBiproduct : ComposableArrows (ModuleCat.{max u v} R) n where
  obj j := ⨁ (fun i : I => (S i).obj j)
  map f := biproduct.map (fun i : I => (S i).map f)
  map_id j := by
    apply biproduct.hom_ext
    intro i
    simp only [biproduct.map_π, Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc, Functor.map_comp]

/-- Let R be a ring in u, I a finite type in v, W=max(u,v), and S_i an n-arrow sequence of modules
in ModuleCat_W(R), with objects S_i^0→⋯→S_i^n. If every S_i has consecutive maps d_i^j,d_i^{j+1}
with d_i^j≫d_i^{j+1}=0 whenever j+2≤n, then the objectwise biproduct sequence has the same
zero-composite property. Its differentials are the corresponding biproduct maps. -/
theorem moduleBiproduct_isComplex (hS : ∀ i, (S i).IsComplex) :
    (moduleBiproduct S).IsComplex where
  zero j hj := by
    change biproduct.map (fun i : I => (S i).map' j (j + 1)) ≫
      biproduct.map (fun i : I => (S i).map' (j + 1) (j + 2)) = 0
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, zero_comp]
    rw [← Category.assoc, biproduct.map_π, Category.assoc, (hS i).zero j hj, comp_zero]

/-- Let R be a ring in u, I a finite type in v, W=max(u,v), and S_i an n-arrow sequence of modules
in ModuleCat_W(R), with objects S_i^0→⋯→S_i^n. If each S_i is exact, then the objectwise
biproduct sequence is exact. For every index 1≤j<n, the image of the preceding biproduct
differential equals the kernel of the next, and the consecutive composite is zero. -/
theorem moduleBiproduct_exact (hS : ∀ i, (S i).Exact) :
    (moduleBiproduct S).Exact where
  toIsComplex := moduleBiproduct_isComplex S (fun i => (hS i).toIsComplex)
  exact j hj := by
    change (ShortComplex.moduleBiproduct
      (fun i : I => (S i).sc (hS i).toIsComplex j hj)).Exact
    exact ShortComplex.moduleBiproduct_exact _ (fun i => (hS i).exact j hj)

end CategoryTheory.ComposableArrows
