/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Abelian.ImageCokernel
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Original module coordinates of arbitrary-shape native cokernels

Evaluation preserves the actual native cokernel. Native module cokernel
coordinates therefore identify every degree with the original range quotient.
Its map and differential equations are earned from the original morphism and
native quotient maps. No additional complex, image backend, closure certificate,
or desired isomorphism is introduced.

The ring, coefficient carriers, and complex-index universes are independent.
These coordinates also identify quotient by the native image subcomplex with
the same original range quotient.

Candidate source; Native and adoption gates remain pending.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) c} (f : K ⟶ L)

/-- Every native cokernel degree is the original quotient by the defining component range. -/
def moduleCokernelDegreeIso (i : ι) :
    (cokernel f).X i ≅ ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) :=
  PreservesCokernel.iso (eval (ModuleCat.{v} R) c i) f ≪≫
    ModuleCat.cokernelIsoRangeQuotient (f.f i)

/-- These coordinates retain the actual original component projection. -/
@[reassoc]
theorem moduleCokernelDegreeIso_projection (i : ι) :
    (cokernel.π f).f i ≫ (moduleCokernelDegreeIso f i).hom =
      ModuleCat.ofHom (LinearMap.range (f.f i).hom).mkQ := by
  let F := eval (ModuleCat.{v} R) c i
  have h₁ := PreservesCokernel.π_iso_hom F f
  have h₂ := ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (f.f i)
  change (F.map (cokernel.π f)) ≫
    ((PreservesCokernel.iso F f).hom ≫
      (ModuleCat.cokernelIsoRangeQuotient (f.f i)).hom) = _
  rw [← Category.assoc, h₁]
  exact h₂

section Maps

variable {K' L' : HomologicalComplex (ModuleCat.{v} R) c} {g : K' ⟶ L'}
  (a : Arrow.mk f ⟶ Arrow.mk g)

/-- The original target side of a square preserves the actual defining component range. -/
theorem moduleRange_map (i : ι) :
    LinearMap.range (f.f i).hom ≤
      (LinearMap.range (g.f i).hom).comap (a.right.f i).hom := by
  rintro x ⟨z, rfl⟩
  refine ⟨(a.left.f i).hom z, ?_⟩
  exact ConcreteCategory.congr_hom (congrArg (fun h => h.f i) a.w) z

/-- Native quotient map of the original target component, with its preservation earned above. -/
def moduleRangeQuotientMap (i : ι) :
    ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) ⟶
      ModuleCat.of R ((L'.X i) ⧸ LinearMap.range (g.f i).hom) :=
  ModuleCat.ofHom ((LinearMap.range (f.f i).hom).mapQ (LinearMap.range (g.f i).hom)
    (a.right.f i).hom (moduleRange_map f a i))

/-- The actual quotient map retains the original target map on every class. -/
@[reassoc]
theorem moduleRangeQuotientMap_projection (i : ι) :
    ModuleCat.ofHom (LinearMap.range (f.f i).hom).mkQ ≫ moduleRangeQuotientMap f a i =
      a.right.f i ≫ ModuleCat.ofHom (LinearMap.range (g.f i).hom).mkQ := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Native cokernel component coordinates are natural in every original square. -/
@[reassoc]
theorem moduleCokernelDegreeIso_naturality (i : ι) :
    (cokernel.map f g a.left a.right a.w.symm).f i ≫ (moduleCokernelDegreeIso g i).hom =
      (moduleCokernelDegreeIso f i).hom ≫ moduleRangeQuotientMap f a i := by
  have hπ : (cokernel.π f).f i ≫ (cokernel.map f g a.left a.right a.w.symm).f i =
      a.right.f i ≫ (cokernel.π g).f i := by
    have hz : f ≫ (a.right ≫ cokernel.π g) = 0 := by
      calc
        f ≫ (a.right ≫ cokernel.π g) = (f ≫ a.right) ≫ cokernel.π g :=
          (Category.assoc f a.right (cokernel.π g)).symm
        _ = (a.left ≫ g) ≫ cokernel.π g :=
          congrArg (fun k : K ⟶ L' => k ≫ cokernel.π g) a.w.symm
        _ = a.left ≫ (g ≫ cokernel.π g) := Category.assoc a.left g (cokernel.π g)
        _ = 0 := by rw [cokernel.condition, comp_zero]
    have h := congrArg (fun k => k.f i)
      (cokernel.π_desc f (a.right ≫ cokernel.π g) hz)
    simpa only [HomologicalComplex.comp_f] using h
  letI : Epi ((cokernel.π f).f i) := inferInstance
  apply (cancel_epi ((cokernel.π f).f i)).1
  rw [← Category.assoc, hπ, Category.assoc, moduleCokernelDegreeIso_projection,
    ← Category.assoc, moduleCokernelDegreeIso_projection, moduleRangeQuotientMap_projection]

end Maps

/-- The original target differential preserves the actual defining range family. -/
theorem moduleRange_d (i j : ι) :
    LinearMap.range (f.f i).hom ≤
      (LinearMap.range (f.f j).hom).comap (L.d i j).hom := by
  rintro x ⟨z, rfl⟩
  refine ⟨(K.d i j).hom z, ?_⟩
  exact (ConcreteCategory.congr_hom (f.comm i j) z).symm

/-- Native quotient of the original differential; no new complex is defined. -/
def moduleRangeQuotientD (i j : ι) :
    ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) ⟶
      ModuleCat.of R ((L.X j) ⧸ LinearMap.range (f.f j).hom) :=
  ModuleCat.ofHom ((LinearMap.range (f.f i).hom).mapQ (LinearMap.range (f.f j).hom)
    (L.d i j).hom (moduleRange_d f i j))

/-- The range-quotient differential retains the original differential on every class. -/
@[reassoc]
theorem moduleRangeQuotientD_projection (i j : ι) :
    ModuleCat.ofHom (LinearMap.range (f.f i).hom).mkQ ≫ moduleRangeQuotientD f i j =
      L.d i j ≫ ModuleCat.ofHom (LinearMap.range (f.f j).hom).mkQ := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The actual native cokernel differential is the quotient of the original differential. -/
@[reassoc]
theorem moduleCokernelDegreeIso_d (i j : ι) :
    (cokernel f).d i j ≫ (moduleCokernelDegreeIso f j).hom =
      (moduleCokernelDegreeIso f i).hom ≫ moduleRangeQuotientD f i j := by
  letI : Epi ((cokernel.π f).f i) := inferInstance
  apply (cancel_epi ((cokernel.π f).f i)).1
  rw [← Category.assoc, (cokernel.π f).comm i j, Category.assoc,
    moduleCokernelDegreeIso_projection, ← Category.assoc,
    moduleCokernelDegreeIso_projection, moduleRangeQuotientD_projection]

/-- Quotient by the actual image subcomplex has those same original component coordinates. -/
def moduleImageCokernelDegreeIso (i : ι) :
    (cokernel (Abelian.image.ι f)).X i ≅
      ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) :=
  Hom.isoApp (Abelian.imageCokernelIso f) i ≪≫ moduleCokernelDegreeIso f i

/-- The image-quotient coordinates retain the original range quotient projection. -/
@[reassoc]
theorem moduleImageCokernelDegreeIso_projection (i : ι) :
    (cokernel.π (Abelian.image.ι f)).f i ≫ (moduleImageCokernelDegreeIso f i).hom =
      ModuleCat.ofHom (LinearMap.range (f.f i).hom).mkQ := by
  have h := congrArg (fun g => g.f i) (Abelian.imageCokernelIso_projection f)
  have hcomponent : (cokernel.π (Abelian.image.ι f)).f i ≫
      (Abelian.imageCokernelIso f).hom.f i = (cokernel.π f).f i := by
    simpa only [HomologicalComplex.comp_f] using h
  change (cokernel.π (Abelian.image.ι f)).f i ≫
    ((Abelian.imageCokernelIso f).hom.f i ≫ (moduleCokernelDegreeIso f i).hom) = _
  rw [← Category.assoc, hcomponent, moduleCokernelDegreeIso_projection]

end HomologicalComplex

end
