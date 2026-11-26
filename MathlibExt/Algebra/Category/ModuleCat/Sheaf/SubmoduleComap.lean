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

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# Preimages of submodules of module presheaves and sheaves

Let `R` be a presheaf of rings, `f : M → P` a morphism of module presheaves, and `N` a
submodule of `P`. The preimage has component `f_X⁻¹(N_X)` at each object. Naturality of `f`
makes it stable under restriction, and the membership sieve of a section `x` equals the
membership sieve of its image `f_X(x)` in `N`.

If `R,M,P,N` are sheaves on a site, the preimage is a sheaf submodule of `M`. The restricted
morphism `f⁻¹N → N` commutes with both inclusions: `f|_{f⁻¹N} ≫ ι_N = ι_{f⁻¹N} ≫ f`.
-/

@[expose] public section
noncomputable section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M P : PresheafOfModules.{v} R}

/-- Let `C : Type u₁` have morphism universe `v₁`, `R : Cᵒᵖ ⥤ RingCat.{u}`, and `M,P` be module
presheaves of carrier universe `v`. For a submodule presheaf `N≤P` and a morphism `f : M → P`,
`N.comap f` is the submodule presheaf of `M` with component `Submodule.comap (f.app X).hom
(N.obj X)` at `X : Cᵒᵖ`. Equivalently, its sections are those whose images under `f` lie in
`N`. -/
def comap (N : P.Submodule) (f : M ⟶ P) : M.Submodule where
  obj X := (N.obj X).comap (f.app X).hom
  map {X Y} g := by
    intro x hx
    change (f.app Y) (M.map g x) ∈ N.obj Y
    rw [PresheafOfModules.naturality_apply]
    exact N.map_mem g hx

/-- Let `R` be a presheaf of rings on a category `C`, `f : M → P` a morphism of `R`-module
presheaves, and `N≤P` a submodule presheaf. For `X : Cᵒᵖ`, `(N.comap f).obj X = (N.obj
X).comap (f.app X).hom`, the linear-map preimage of the submodule `N(X)`. -/
theorem comap_obj (N : P.Submodule) (f : M ⟶ P) (X : Cᵒᵖ) :
    (N.comap f).obj X = (N.obj X).comap (f.app X).hom := rfl

/-- Let `R` be a presheaf of rings on `C`, `f : M → P` a module-presheaf morphism, `N≤P` a
submodule presheaf, `X : Cᵒᵖ`, and `x∈M(X)`. The sieve of arrows along which `x` restricts
into `N.comap f` equals the sieve along which `(f.app X)(x)` restricts into `N`: `(N.comap
f).toSubfunctor.sieveOfSection x = N.toSubfunctor.sieveOfSection ((f.app X) x)`. -/
theorem comap_sieveOfSection (N : P.Submodule) (f : M ⟶ P) {X : Cᵒᵖ} (x : M.obj X) :
    (N.comap f).toSubfunctor.sieveOfSection x =
      N.toSubfunctor.sieveOfSection ((f.app X) x) := by
  ext Y g
  change ((f.app (Opposite.op Y)) (M.map g.op x) ∈ N.obj (Opposite.op Y)) ↔
    (P.map g.op ((f.app X) x) ∈ N.obj (Opposite.op Y))
  rw [PresheafOfModules.naturality_apply]
  simp only [Opposite.op_unop]
  rfl

/-- Let `R` be a presheaf of rings, `f : M → P` a morphism of module presheaves, and `N≤P` a
submodule presheaf. The morphism `N.comapLift f : (N.comap f).toPresheafOfModules →
N.toPresheafOfModules` restricts each component `f_X` to the preimage submodule `f_X⁻¹(N_X)`. -/
def comapLift (N : P.Submodule) (f : M ⟶ P) :
    (N.comap f).toPresheafOfModules ⟶ N.toPresheafOfModules where
  app X := ModuleCat.ofHom
    ((f.app X).hom.restrict (p := (N.comap f).obj X) (q := N.obj X) (fun _ hx => hx))
  naturality g := by
    ext x
    apply Subtype.ext
    exact PresheafOfModules.naturality_apply f g x.val

/-- Let `R` be a presheaf of rings, `f : M → P` a morphism of module presheaves, and `N≤P` a
submodule presheaf. The restricted map satisfies `N.comapLift f ≫ N.ι = (N.comap f).ι ≫ f`, as
morphisms from the preimage submodule presheaf to `P`. -/
@[reassoc] theorem comapLift_ι (N : P.Submodule) (f : M ⟶ P) :
    N.comapLift f ≫ N.ι = (N.comap f).ι ≫ f := by
  ext X x
  rfl

end PresheafOfModules.Submodule

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M P : SheafOfModules.{v} R}

/-- Let `C : Type u₁` have morphism universe `v₁`, `J` a Grothendieck topology, `R : Sheaf J
RingCat.{u}`, and `M,P : SheafOfModules.{v} R`. For a sheaf submodule `N≤P` and `f : M → P`,
`N.comap f` is the sheaf submodule of `M` whose component is the preimage `f_X⁻¹(N_X)` at each
object. Its underlying presheaf submodule is `N.toSubmodule.comap f.val`. -/
def comap (N : P.Submodule) (f : M ⟶ P) : M.Submodule where
  toSubmodule := N.toSubmodule.comap f.val
  isSheaf := by
    intro X x hx
    apply N.isSheaf ((f.val.app X) x)
    rw [← PresheafOfModules.Submodule.comap_sieveOfSection N.toSubmodule f.val x]
    exact hx

/-- On a site `(C,J)` with a sheaf of rings `R`, let `f : M → P` be a morphism of module sheaves
and `N≤P` a sheaf submodule. Then `(N.comap f).toSubmodule = N.toSubmodule.comap f.val`:
taking the underlying presheaf submodule commutes with preimage under `f`. -/
theorem comap_toSubmodule (N : P.Submodule) (f : M ⟶ P) :
    (N.comap f).toSubmodule = N.toSubmodule.comap f.val := rfl

/-- On a ringed site `(C,J,R)`, let `f : M → P` be a morphism of module sheaves and `N≤P` a sheaf
submodule. The morphism `N.comapLift f : (N.comap f).toSheafOfModules → N.toSheafOfModules`
restricts `f` to the preimage of `N`, with component the linear map `f_X : f_X⁻¹(N_X) → N_X`. -/
def comapLift (N : P.Submodule) (f : M ⟶ P) :
    (N.comap f).toSheafOfModules ⟶ N.toSheafOfModules where
  val := N.toSubmodule.comapLift f.val

/-- On a ringed site `(C,J,R)`, let `f : M → P` be a morphism of module sheaves and `N≤P` a sheaf
submodule. The preimage restriction and inclusions satisfy `N.comapLift f ≫ N.ι = (N.comap
f).ι ≫ f`, as morphisms from the preimage sheaf to `P`. -/
@[reassoc] theorem comapLift_ι (N : P.Submodule) (f : M ⟶ P) :
    N.comapLift f ≫ N.ι = (N.comap f).ι ≫ f := by
  apply (SheafOfModules.forget R).map_injective
  exact PresheafOfModules.Submodule.comapLift_ι N.toSubmodule f.val

end SheafOfModules.Submodule
