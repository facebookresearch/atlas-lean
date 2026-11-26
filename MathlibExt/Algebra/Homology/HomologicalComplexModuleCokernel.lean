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
# Range-quotient coordinates of module-complex cokernels

Let R be an arbitrary ring and f:K → L a morphism of R-module complexes
of any shape c. Evaluation in degree i identifies the cokernel term with
Lᵢ/im(fᵢ), preserving the quotient projection x ↦ [x].

A commuting square with target map b:L → L′ induces the quotient map
[x] ↦ [bᵢ(x)] in each degree. The differential on the cokernel, in these
coordinates, sends [x] to [d_L(i,j)(x)]. These maps are well-defined because
the square and the cochain-map relations preserve the relevant ranges.
Quotienting L by the image subcomplex gives the same range-quotient
coordinates and projections. The ring, module-carrier and complex-index
universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) c} (f : K ⟶ L)

/-- For an arbitrary ring R, a complex shape c and a morphism f:K → L
of R-module complexes, the canonical degree-i isomorphism
θ_f,i:Coker(f)ᵢ ≅ Lᵢ/im(fᵢ), obtained from evaluation of the cokernel
and the module range quotient. -/
def moduleCokernelDegreeIso (i : ι) :
    (cokernel f).X i ≅ ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) :=
  PreservesCokernel.iso (eval (ModuleCat.{v} R) c i) f ≪≫
    ModuleCat.cokernelIsoRangeQuotient (f.f i)

/-- Let R be an arbitrary ring and f:K → L a morphism of R-module
complexes of any shape. Under θ_f,i:Coker(f)ᵢ ≅ Lᵢ/im(fᵢ), the
degree-i cokernel projection is the quotient map:
θ_f,i ∘ π_f,i sends x to [x]. -/
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

/-- Let R be an arbitrary ring and let a:K → K′, b:L → L′ form a
commuting square from f:K → L to g:K′ → L′ between module complexes
of one shape. In each degree i, bᵢ sends im(fᵢ) into im(gᵢ);
equivalently im(fᵢ)⊆bᵢ⁻¹(im(gᵢ)). -/
theorem moduleRange_map (i : ι) :
    LinearMap.range (f.f i).hom ≤
      (LinearMap.range (g.f i).hom).comap (a.right.f i).hom := by
  rintro x ⟨z, rfl⟩
  refine ⟨(a.left.f i).hom z, ?_⟩
  exact ConcreteCategory.congr_hom (congrArg (fun h => h.f i) a.w) z

/-- For an arbitrary ring R and a commuting square (a,b) from f:K → L
to g:K′ → L′ between module complexes of one shape, the induced
degree-i map Lᵢ/im(fᵢ) → L′ᵢ/im(gᵢ) sends [x] to [bᵢ(x)]. -/
def moduleRangeQuotientMap (i : ι) :
    ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) ⟶
      ModuleCat.of R ((L'.X i) ⧸ LinearMap.range (g.f i).hom) :=
  ModuleCat.ofHom ((LinearMap.range (f.f i).hom).mapQ (LinearMap.range (g.f i).hom)
    (a.right.f i).hom (moduleRange_map f a i))

/-- Let R be an arbitrary ring and (a,b) a commuting square between
module-complex morphisms f:K → L and g:K′ → L′ of one shape.
For the degree-i quotient map Qᵢ:Lᵢ/im(fᵢ) → L′ᵢ/im(gᵢ), its
composite with the quotient projection π_f,i satisfies
Qᵢ ∘ π_f,i = π_g,i ∘ bᵢ. -/
@[reassoc]
theorem moduleRangeQuotientMap_projection (i : ι) :
    ModuleCat.ofHom (LinearMap.range (f.f i).hom).mkQ ≫ moduleRangeQuotientMap f a i =
      a.right.f i ≫ ModuleCat.ofHom (LinearMap.range (g.f i).hom).mkQ := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Let R be an arbitrary ring and (a,b) a commuting square from
f:K → L to g:K′ → L′ between module complexes of one shape.
If C_i is the component of the induced cokernel map and Qᵢ is
[x]↦[bᵢ(x)], the range-quotient isomorphisms satisfy
θ_g,i ∘ C_i = Qᵢ ∘ θ_f,i. -/
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

/-- Let R be an arbitrary ring and f:K → L a morphism of module complexes
of any shape c. For any indices i,j, the differential d_L(i,j) sends
im(fᵢ) into im(fⱼ); equivalently
im(fᵢ)⊆d_L(i,j)⁻¹(im(fⱼ)). -/
theorem moduleRange_d (i j : ι) :
    LinearMap.range (f.f i).hom ≤
      (LinearMap.range (f.f j).hom).comap (L.d i j).hom := by
  rintro x ⟨z, rfl⟩
  refine ⟨(K.d i j).hom z, ?_⟩
  exact (ConcreteCategory.congr_hom (f.comm i j) z).symm

/-- For an arbitrary ring R and a morphism f:K → L of module complexes
of any shape, the quotient map
Lᵢ/im(fᵢ) → Lⱼ/im(fⱼ) induced by the differential d_L(i,j).
It sends the class [x] to [d_L(i,j)(x)]. -/
def moduleRangeQuotientD (i j : ι) :
    ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) ⟶
      ModuleCat.of R ((L.X j) ⧸ LinearMap.range (f.f j).hom) :=
  ModuleCat.ofHom ((LinearMap.range (f.f i).hom).mapQ (LinearMap.range (f.f j).hom)
    (L.d i j).hom (moduleRange_d f i j))

/-- Let R be an arbitrary ring and f:K → L a morphism of module complexes
of any shape. Write π_i:Lᵢ → Lᵢ/im(fᵢ) and π_j for the quotient
projections, and d_Q(i,j) for the induced quotient differential.
They satisfy d_Q(i,j) ∘ π_i = π_j ∘ d_L(i,j). -/
@[reassoc]
theorem moduleRangeQuotientD_projection (i j : ι) :
    ModuleCat.ofHom (LinearMap.range (f.f i).hom).mkQ ≫ moduleRangeQuotientD f i j =
      L.d i j ≫ ModuleCat.ofHom (LinearMap.range (f.f j).hom).mkQ := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Let R be an arbitrary ring and f:K → L a morphism of module complexes
of any shape. In the isomorphisms θ_f,i:Coker(f)ᵢ ≅ Lᵢ/im(fᵢ),
the cokernel differential satisfies
θ_f,j ∘ d_Coker(f)(i,j) = d_Q(i,j) ∘ θ_f,i,
where d_Q sends [x] to [d_L(i,j)(x)]. -/
@[reassoc]
theorem moduleCokernelDegreeIso_d (i j : ι) :
    (cokernel f).d i j ≫ (moduleCokernelDegreeIso f j).hom =
      (moduleCokernelDegreeIso f i).hom ≫ moduleRangeQuotientD f i j := by
  letI : Epi ((cokernel.π f).f i) := inferInstance
  apply (cancel_epi ((cokernel.π f).f i)).1
  rw [← Category.assoc, (cokernel.π f).comm i j, Category.assoc,
    moduleCokernelDegreeIso_projection, ← Category.assoc,
    moduleCokernelDegreeIso_projection, moduleRangeQuotientD_projection]

/-- For an arbitrary ring R and a morphism f:K → L of module complexes
of any shape, let j:Im(f) → L be its image-subcomplex inclusion.
The canonical isomorphism from the degree-i term of Coker(j) to
Lᵢ/im(fᵢ), through the image-quotient comparison and the cokernel
range-quotient coordinates. -/
def moduleImageCokernelDegreeIso (i : ι) :
    (cokernel (Abelian.image.ι f)).X i ≅
      ModuleCat.of R ((L.X i) ⧸ LinearMap.range (f.f i).hom) :=
  Hom.isoApp (Abelian.imageCokernelIso f) i ≪≫ moduleCokernelDegreeIso f i

/-- Let R be an arbitrary ring, f:K → L a module-complex morphism of any
shape, and j:Im(f) → L its image inclusion. Under the canonical
isomorphism Coker(j)ᵢ ≅ Lᵢ/im(fᵢ), the degree-i projection from L
is the quotient map x↦[x]. -/
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
