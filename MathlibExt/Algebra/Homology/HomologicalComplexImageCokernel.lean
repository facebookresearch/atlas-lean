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
# Homology of image and coimage quotient presentations

Let C be an abelian category and f:K → L a morphism of complexes of any
shape c. Write j:Im(f) → L for the image inclusion and
b:Coim(f) → L for the factor map through the coimage. The canonical
isomorphisms Coker(j) ≅ Coker(f) and Coker(b) ≅ Coker(f) preserve the
projections from L.

At a degree i with the chosen homology objects, these isomorphisms induce
the corresponding homology comparisons. Their forward maps preserve the
homology maps of the quotient projections and are natural in commuting
squares between defining complex morphisms. The category and index type
have independent universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (f : K ⟶ L)

/-- Let C be abelian, c any complex shape and f:K → L a morphism of
complexes. For a degree i with chosen homology objects of Coker(j)
and Coker(f), where j:Im(f) → L is the image inclusion, the canonical
isomorphism Hᵢ(Coker(j)) ≅ Hᵢ(Coker(f)) induced by the image-quotient
isomorphism. -/
def imageCokernelHomologyIso (i : ι)
    [(cokernel (Abelian.image.ι f)).HasHomology i] [(cokernel f).HasHomology i] :
    (cokernel (Abelian.image.ι f)).homology i ≅ (cokernel f).homology i :=
  isoOfQuasiIsoAt (Abelian.imageCokernelIso f).hom i

/-- In an abelian category C, let f:K → L be a complex morphism of any
shape and j:Im(f) → L its image inclusion. With the chosen homology
objects of Coker(j) and Coker(f) at i, the forward homology comparison
is the homology map of the canonical isomorphism Coker(j) ≅ Coker(f). -/
theorem imageCokernelHomologyIso_hom (i : ι)
    [(cokernel (Abelian.image.ι f)).HasHomology i] [(cokernel f).HasHomology i] :
    (imageCokernelHomologyIso f i).hom = homologyMap (Abelian.imageCokernelIso f).hom i :=
  rfl

/-- Let f:K → L be a complex morphism of any shape in an abelian category,
j:Im(f) → L its image inclusion, and π_j:L → Coker(j),
π_f:L → Coker(f) the projections. With chosen homology objects of
L and the two quotients at i, the comparison αᵢ satisfies
αᵢ ∘ Hᵢ(π_j) = Hᵢ(π_f). -/
@[reassoc]
theorem imageCokernelHomologyIso_projection (i : ι)
    [L.HasHomology i] [(cokernel (Abelian.image.ι f)).HasHomology i]
    [(cokernel f).HasHomology i] :
    homologyMap (cokernel.π (Abelian.image.ι f)) i ≫ (imageCokernelHomologyIso f i).hom =
      homologyMap (cokernel.π f) i := by
  rw [imageCokernelHomologyIso_hom, ← homologyMap_comp,
    Abelian.imageCokernelIso_projection]

/-- Let f:K → L and g:K′ → L′ be complex morphisms of one shape in an
abelian category C, and let a:K → K′, b:L → L′ satisfy b∘f=g∘a.
At i choose the homology objects of both image quotients and both
cokernels. If Q_I is the induced map of image quotients and Q the
induced cokernel map, their comparisons satisfy
α_g ∘ Hᵢ(Q_I) = Hᵢ(Q) ∘ α_f. -/
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

/-- Let C be abelian, c any complex shape and f:K → L a morphism of
complexes. Write b:Coim(f) → L for the factor map through the coimage.
At a degree i with chosen homology objects of Coker(b) and Coker(f),
the canonical isomorphism Hᵢ(Coker(b)) ≅ Hᵢ(Coker(f)) induced by
the coimage-quotient isomorphism. -/
def coimageCokernelHomologyIso (i : ι)
    [(cokernel (Abelian.factorThruCoimage f)).HasHomology i] [(cokernel f).HasHomology i] :
    (cokernel (Abelian.factorThruCoimage f)).homology i ≅ (cokernel f).homology i :=
  isoOfQuasiIsoAt (Abelian.coimageCokernelIso f).hom i

/-- Let f:K → L be a complex morphism of any shape in an abelian category,
b:Coim(f) → L its coimage factor map, and π_b:L → Coker(b),
π_f:L → Coker(f) the projections. With chosen homology objects of
L and the two quotients at i, the coimage-quotient comparison βᵢ
satisfies βᵢ ∘ Hᵢ(π_b) = Hᵢ(π_f). -/
@[reassoc]
theorem coimageCokernelHomologyIso_projection (i : ι)
    [L.HasHomology i] [(cokernel (Abelian.factorThruCoimage f)).HasHomology i]
    [(cokernel f).HasHomology i] :
    homologyMap (cokernel.π (Abelian.factorThruCoimage f)) i ≫
        (coimageCokernelHomologyIso f i).hom = homologyMap (cokernel.π f) i := by
  change homologyMap (cokernel.π (Abelian.factorThruCoimage f)) i ≫
    homologyMap (Abelian.coimageCokernelIso f).hom i = _
  rw [← homologyMap_comp, Abelian.coimageCokernelIso_projection]

/-- Let f:K → L and g:K′ → L′ be complex morphisms of one shape in an
abelian category, and let a:K → K′, b:L → L′ form a commuting square.
Choose the homology objects of the two coimage quotients and the two
cokernels at i. If Q_C is the induced coimage-quotient map and Q the
cokernel map, the comparisons satisfy
β_g ∘ Hᵢ(Q_C) = Hᵢ(Q) ∘ β_f. -/
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
