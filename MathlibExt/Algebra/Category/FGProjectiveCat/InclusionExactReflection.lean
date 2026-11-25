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

public import MathlibExt.Algebra.Category.FGProjectiveCat.Inclusion
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Exact reflection for finitely generated projective modules

Over a noetherian ring, a short complex of finitely generated projective
modules whose image in `FGModuleCat` is admissible exact is already split
exact.  Indeed, the projective quotient splits the target short exact
sequence, and fullness and faithfulness lift its splitting back through the
inclusion.

The same argument shows that the kernel in `FGModuleCat` of an epimorphism
between objects in the image of `FGProjectiveCat` is projective as a module.
Finiteness of that kernel is already supplied by the ambient noetherian
`FGModuleCat`.

## Main results

* `FGProjectiveCat.inclusion_reflectsAdmissibleExact`
* `FGProjectiveCat.kernel_projective_of_epi`
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace FGProjectiveCat

variable (R : Type u) [Ring R] [IsNoetherianRing R]

/-- An object in the image of `FGProjectiveCat.inclusion` is projective in
`FGModuleCat`. -/
private lemma inclusion_obj_projective (P : FGProjectiveCat.{v} R) :
    Projective ((inclusion R).obj P) := by
  let U := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  apply U.projective_of_map_projective
  change Projective P.obj
  let _ : Module.Projective R P.obj := P.property.2
  infer_instance

/-- The kernel in `FGModuleCat` of an epimorphism between finitely generated
projective modules is projective as an `R`-module.

The kernel is finitely generated because it is formed in `FGModuleCat` over a
noetherian ring.  This theorem supplies the remaining projectivity property
without choosing a new bundled projective object. -/
theorem kernel_projective_of_epi
    {P Q : FGProjectiveCat.{v} R}
    (g : (inclusion R).obj P ⟶ (inclusion R).obj Q) [Epi g] :
    Module.Projective R (kernel g : FGModuleCat.{v} R) := by
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel g
      mono_f := inferInstance
      epi_g := inferInstance }
  let _ : Projective S.X₃ := inclusion_obj_projective R Q
  let t : S.Splitting := hS.splittingOfProjective
  let _ : Module.Projective R ((inclusion R).obj P) := P.property.2
  apply Module.Projective.of_split (R := R)
    (kernel.ι g).hom.hom t.r.hom.hom
  have ht := congrArg (fun h => h.hom.hom) t.f_r
  change t.r.hom.hom.comp (kernel.ι g).hom.hom = LinearMap.id at ht
  exact ht

/-- The full inclusion from finitely generated projective modules into
finitely generated modules reflects admissible exact short complexes. -/
instance inclusion_reflectsAdmissibleExact :
    CategoryTheory.Functor.ReflectsAdmissibleExact
      (inclusion (R := R) : FGProjectiveCat.{v} R ⥤ FGModuleCat.{v} R) where
  reflects_admissibleExact S hS := by
    let i := inclusion (R := R)
    have hT : (S.map i).ShortExact :=
      ExactCategory.shortExact_of_isAdmissibleExact hS
    let _ : Projective ((S.map i).X₃) :=
      inclusion_obj_projective R S.X₃
    let t : (S.map i).Splitting := hT.splittingOfProjective
    let r : S.X₂ ⟶ S.X₁ := i.preimage t.r
    let s : S.X₃ ⟶ S.X₂ := i.preimage t.s
    apply ExactCategory.isAdmissibleExact_of_splitting
    exact
      { r := r
        s := s
        f_r := i.map_injective (by
          simpa [i, r, ShortComplex.map] using t.f_r)
        s_g := i.map_injective (by
          simpa [i, s, ShortComplex.map] using t.s_g)
        id := i.map_injective (by
          simpa [i, r, s, ShortComplex.map] using t.id) }

end FGProjectiveCat

end
