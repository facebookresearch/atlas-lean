/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.QuasiIso
public import MathlibExt.Algebra.Homology.ExactColimits

/-!
# Quasi-isomorphisms under exact homology colimits

In an abelian category whose J-shaped colimit functor preserves homology,
a compatible map between colimit cocones of complex diagrams is a
quasi-isomorphism when every stage map is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v u t

namespace HomologicalComplex

variable {J : Type w} [Category.{w'} J]
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type t} {c : ComplexShape ι}
variable [HasColimitsOfShape J C]
variable [(colim (J := J) (C := C)).PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C` be abelian with colimits of shape `J` and a homology-
preserving colimit functor, and let `K,L` be diagrams of complexes
of any shape `c`. Suppose `τ : K → L` is objectwise quasi-isomorphic,
`s,t` are colimit cocones, and `f : s.pt → t.pt` satisfies
`s_j ≫ f = τ_j ≫ t_j` for every `j`. Then `f` is a quasi-isomorphism. -/
theorem quasiIso_of_isColimit_of_objectwise
    {K L : J ⥤ HomologicalComplex C c} (τ : K ⟶ L)
    (s : Cocone K) (t : Cocone L) (hs : IsColimit s) (ht : IsColimit t)
    (f : s.pt ⟶ t.pt)
    (hf : ∀ j, s.ι.app j ≫ f = τ.app j ≫ t.ι.app j)
    (hτ : ∀ j, QuasiIso (τ.app j)) :
    QuasiIso f := by
  let _ : HasExactColimitsOfShape J C :=
    CategoryTheory.HasExactColimitsOfShape.of_colim_preservesHomology
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor C c n
  let β : K ⋙ H ⟶ L ⋙ H := Functor.whiskerRight τ H
  let : ∀ j, IsIso (β.app j) := fun j ↦ by
    change IsIso (homologyMap (τ.app j) n)
    let : QuasiIso (τ.app j) := hτ j
    infer_instance
  let : IsIso β := NatIso.isIso_of_isIso_app β
  let e : (H.mapCocone s).pt ≅ (H.mapCocone t).pt :=
    IsColimit.coconePointsIsoOfNatIso
      (isColimitOfPreserves H hs) (isColimitOfPreserves H ht) (asIso β)
  have he : homologyMap f n = e.hom := by
    apply (isColimitOfPreserves H hs).hom_ext
    intro j
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    change H.map (s.ι.app j) ≫ H.map f =
      H.map (τ.app j) ≫ H.map (t.ι.app j)
    rw [← H.map_comp, ← H.map_comp, hf j]
  rw [he]
  infer_instance

end HomologicalComplex
