/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Abelian.ImageCokernel
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Local homology of actual image and coimage quotient presentations

For every complex shape, the native quotient by the image of a morphism
represents its original cokernel. The comparison retains the actual cokernel
projection. Applying the native homology map at one chosen degree gives a
canonical comparison; no global homology functor or desired homology iso is
an input. Original squares retain that comparison by native homology
naturality.

Candidate source; Native and adoption gates remain pending.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (f : K ⟶ L)

/-- At a chosen degree, the image quotient has the homology of the original cokernel. -/
def imageCokernelHomologyIso (i : ι)
    [(cokernel (Abelian.image.ι f)).HasHomology i] [(cokernel f).HasHomology i] :
    (cokernel (Abelian.image.ι f)).homology i ≅ (cokernel f).homology i :=
  isoOfQuasiIsoAt (Abelian.imageCokernelIso f).hom i

/-- The comparison's forward map is the native homology map of the earned quotient iso. -/
theorem imageCokernelHomologyIso_hom (i : ι)
    [(cokernel (Abelian.image.ι f)).HasHomology i] [(cokernel f).HasHomology i] :
    (imageCokernelHomologyIso f i).hom = homologyMap (Abelian.imageCokernelIso f).hom i :=
  rfl

/-- The local comparison retains the actual original quotient projection. -/
@[reassoc]
theorem imageCokernelHomologyIso_projection (i : ι)
    [L.HasHomology i] [(cokernel (Abelian.image.ι f)).HasHomology i]
    [(cokernel f).HasHomology i] :
    homologyMap (cokernel.π (Abelian.image.ι f)) i ≫ (imageCokernelHomologyIso f i).hom =
      homologyMap (cokernel.π f) i := by
  rw [imageCokernelHomologyIso_hom, ← homologyMap_comp,
    Abelian.imageCokernelIso_projection]

/-- Actual original squares preserve the chosen-degree image/cokernel comparison. -/
@[reassoc]
theorem imageCokernelHomologyIso_naturality {K' L' : HomologicalComplex C c}
    {g : K' ⟶ L'} (a : Arrow.mk f ⟶ Arrow.mk g) (i : ι)
    [(cokernel (Abelian.image.ι f)).HasHomology i] [(cokernel f).HasHomology i]
    [(cokernel (Abelian.image.ι g)).HasHomology i] [(cokernel g).HasHomology i] :
    homologyMap (Abelian.imageCokernelMap f a) i ≫ (imageCokernelHomologyIso g i).hom =
      (imageCokernelHomologyIso f i).hom ≫
        homologyMap (cokernel.map f g a.left a.right a.w.symm) i := by
  rw [imageCokernelHomologyIso_hom, imageCokernelHomologyIso_hom,
    ← homologyMap_comp, ← homologyMap_comp, Abelian.imageCokernelIso_naturality]

/-- The native coimage presentation gives the same local homology object. -/
def coimageCokernelHomologyIso (i : ι)
    [(cokernel (Abelian.factorThruCoimage f)).HasHomology i] [(cokernel f).HasHomology i] :
    (cokernel (Abelian.factorThruCoimage f)).homology i ≅ (cokernel f).homology i :=
  isoOfQuasiIsoAt (Abelian.coimageCokernelIso f).hom i

/-- The coimage comparison also retains the actual original projection on local homology. -/
@[reassoc]
theorem coimageCokernelHomologyIso_projection (i : ι)
    [L.HasHomology i] [(cokernel (Abelian.factorThruCoimage f)).HasHomology i]
    [(cokernel f).HasHomology i] :
    homologyMap (cokernel.π (Abelian.factorThruCoimage f)) i ≫
        (coimageCokernelHomologyIso f i).hom = homologyMap (cokernel.π f) i := by
  change homologyMap (cokernel.π (Abelian.factorThruCoimage f)) i ≫
    homologyMap (Abelian.coimageCokernelIso f).hom i = _
  rw [← homologyMap_comp, Abelian.coimageCokernelIso_projection]

/-- Actual coimage quotient maps preserve the selected-degree homology comparison. -/
@[reassoc]
theorem coimageCokernelHomologyIso_naturality {K' L' : HomologicalComplex C c}
    {g : K' ⟶ L'} (a : Arrow.mk f ⟶ Arrow.mk g) (i : ι)
    [(cokernel (Abelian.factorThruCoimage f)).HasHomology i] [(cokernel f).HasHomology i]
    [(cokernel (Abelian.factorThruCoimage g)).HasHomology i] [(cokernel g).HasHomology i] :
    homologyMap (Abelian.coimageCokernelMap f a) i ≫ (coimageCokernelHomologyIso g i).hom =
      (coimageCokernelHomologyIso f i).hom ≫
        homologyMap (cokernel.map f g a.left a.right a.w.symm) i := by
  change homologyMap (Abelian.coimageCokernelMap f a) i ≫
      homologyMap (Abelian.coimageCokernelIso g).hom i =
    homologyMap (Abelian.coimageCokernelIso f).hom i ≫
      homologyMap (cokernel.map f g a.left a.right a.w.symm) i
  rw [← homologyMap_comp, ← homologyMap_comp, Abelian.coimageCokernelIso_naturality]

end HomologicalComplex

end
