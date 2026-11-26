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

public import MathlibExt.CategoryTheory.ExactCategory.FiniteResolving
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Lifting kernels from the essential image of an additive functor

Let E be preadditive, A abelian and F : E ⥤ A a fully faithful additive functor. Suppose that
the essential image of F is closed under kernels of epimorphisms between its objects. For f :
P ⟶ Q whose image F(f) is an epimorphism, choose K in E and an isomorphism e : F(K) ≅
Ker(F(f)). Fullness lifts e.hom ≫ kernel.ι(F(f)) to i : K ⟶ P, and faithfulness gives i ≫ f =
0.

The mapped sequence F(K) → F(P) → F(Q) is short exact, and its first map has the kernel
universal property. These choices supply kernel-resolving data for F. If E has a zero object,
binary biproducts and an exact-category structure, and F reflects admissible exactness, then K
→ P → Q is a conflation in E. In that case i is a kernel of f and f is a cokernel of i in E.

The source and target object and morphism universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace CategoryTheory.Functor

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (Limits.kernel f))

include hKernelClosure

omit [Preadditive E] [F.Additive] in
/-- Essential-image membership of a mapped epimorphism kernel.

Let F : E ⥤ A have essential image closed under kernels of epimorphisms between its objects,
with A abelian. If f : P ⟶ Q and F(f) is an epimorphism, then Ker(F(f)) lies in the essential
image of F, because F(P) and F(Q) do. This membership statement does not require additivity,
fullness or faithfulness of F. -/
theorem kernelOfEpi_mem_essImage {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    F.essImage (Limits.kernel (F.map f)) :=
  hKernelClosure _ ⟨_, ⟨Iso.refl _⟩⟩ ⟨_, ⟨Iso.refl _⟩⟩

variable [F.Full] [F.Faithful]

/-- Kernel lift through a fully faithful additive functor.

Let F : E ⥤ A be fully faithful and additive, E preadditive and A abelian, with essential
image closed under epimorphism kernels. For f : P ⟶ Q with F(f) epic, choose e : F(K) ≅
Ker(F(f)) and set i = F.preimage(e.hom ≫ kernel.ι(F(f))). The resulting KernelLift has i ≫ f =
0, and F(i) is a kernel of F(f). -/
def kernelLiftOfEpi {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] : KernelLift F f := by
  let hImage := kernelOfEpi_mem_essImage F hKernelClosure f
  let e := hImage.getIso
  let i : hImage.witness ⟶ P := F.preimage (e.hom ≫ Limits.kernel.ι (F.map f))
  have hi : i ≫ f = 0 := by
    apply F.map_injective
    simp only [i, F.map_comp, F.map_preimage, F.map_zero, Category.assoc,
      Limits.kernel.condition, comp_zero]
  refine
    { K := hImage.witness
      ι := i
      zero := hi
      mappedIsLimit := ?_ }
  exact (kernelIsKernel (F.map f)).ofIsoLimit
    (Fork.ext e.symm (by
      change e.inv ≫ F.map i = Limits.kernel.ι (F.map f)
      simp only [i, F.map_preimage, Iso.inv_hom_id_assoc]))

/-- Kernel-resolving data from essential-image closure.

For a fully faithful additive functor F from a preadditive category to an abelian category,
closure of its essential image under kernels of epimorphisms supplies a KernelLift for each f
whose image F(f) is epic. These lifts satisfy the kernelOfEpi clause of KernelResolvingData F. -/
theorem kernelResolvingDataOfKernelImageClosure : KernelResolvingData F where
  kernelOfEpi f hf := by
    let _ := hf
    exact ⟨kernelLiftOfEpi F hKernelClosure f⟩

/-- Chosen object representing an ambient epimorphism kernel.

For the kernel lift of f under a fully faithful additive functor F, the source object K is the
witness of the essential-image membership statement for Ker(F(f)). Its chosen isomorphism
identifies F(K) with that ambient kernel. -/
theorem kernelLiftOfEpi_K {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    (kernelLiftOfEpi F hKernelClosure f).K =
      (kernelOfEpi_mem_essImage F hKernelClosure f).witness := rfl

/-- Formula for the lifted kernel inclusion.

Let e : F(K) ≅ Ker(F(f)) be the representative isomorphism chosen by essential-image closure.
Under a fully faithful additive functor F, the lifted inclusion K → P is F.preimage(e.hom ≫
kernel.ι(F(f))). -/
theorem kernelLiftOfEpi_ι {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    (kernelLiftOfEpi F hKernelClosure f).ι =
      F.preimage ((kernelOfEpi_mem_essImage F hKernelClosure f).getIso.hom ≫
        Limits.kernel.ι (F.map f)) := rfl

/-- Image of the lifted kernel inclusion.

For f : P ⟶ Q with F(f) epic and the representative isomorphism e : F(K) ≅ Ker(F(f)), the
lifted inclusion i : K → P satisfies F(i) = e.hom ≫ kernel.ι(F(f)). Thus the full ambient
inclusion is recovered after applying F. -/
theorem kernelLiftOfEpi_map_ι {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    F.map (kernelLiftOfEpi F hKernelClosure f).ι =
      (kernelOfEpi_mem_essImage F hKernelClosure f).getIso.hom ≫ Limits.kernel.ι (F.map f) :=
  F.map_preimage _

/-- Vanishing of the lifted inclusion followed by the epimorphism.

For the kernel lift i : K → P of f : P → Q through a fully faithful additive functor F, the
composite i ≫ f is zero. Its image under F vanishes by the ambient kernel equation, and
faithfulness reflects this equality. -/
theorem kernelLiftOfEpi_zero {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    (kernelLiftOfEpi F hKernelClosure f).ι ≫ f = 0 :=
  (kernelLiftOfEpi F hKernelClosure f).zero

/-- Kernel universal property of the mapped lift.

Let F be fully faithful and additive from a preadditive category to an abelian category, with
essential image closed under epimorphism kernels. For f with F(f) epic, the fork F(K) → F(P) →
F(Q) defined by the lifted inclusion is a limit kernel fork of F(f). -/
def kernelLiftOfEpiMappedIsLimit {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsLimit (KernelFork.ofι (f := F.map f) (F.map (kernelLiftOfEpi F hKernelClosure f).ι)
      (by rw [← F.map_comp, kernelLiftOfEpi_zero, F.map_zero])) :=
  (kernelLiftOfEpi F hKernelClosure f).mappedIsLimit

/-- Short exactness of the mapped kernel lift.

For a kernel lift of f : P → Q through F, where F(f) is an epimorphism, the sequence F(K) →
F(P) → F(Q) is short exact in the ambient abelian category. The first map is the chosen
representative of the kernel inclusion. -/
theorem kernelLiftOfEpi_mappedShortExact {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    ((kernelLiftOfEpi F hKernelClosure f).shortComplex.map F).ShortExact :=
  (kernelLiftOfEpi F hKernelClosure f).mappedShortExact

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- Conflation obtained by reflecting the mapped kernel sequence.

Let E be an exact category with zero object and binary biproducts, and let F : E ⥤ A be fully
faithful, additive and reflecting admissible exactness, with A abelian and essential image
closed under epimorphism kernels. For f with F(f) epic, the lifted sequence K → P → Q is
admissible exact in E. -/
theorem kernelLiftOfEpi_isAdmissibleExact {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsAdmissibleExact (kernelLiftOfEpi F hKernelClosure f).shortComplex :=
  (kernelLiftOfEpi F hKernelClosure f).isAdmissibleExact

/-- Kernel universal property of the lift in the source category.

Assume E is an exact category with zero object and binary biproducts and F : E ⥤ A is fully
faithful, additive and reflects admissible exactness, with the stated epimorphism-kernel
closure. For f with F(f) epic, its lifted inclusion i : K → P defines a limit kernel fork of f
in E. -/
def kernelLiftOfEpiIsLimit {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsLimit (KernelFork.ofι (f := f) (kernelLiftOfEpi F hKernelClosure f).ι
      (kernelLiftOfEpi_zero F hKernelClosure f)) :=
  isLimit_kernelFork_of_isAdmissibleExact
    (kernelLiftOfEpi_isAdmissibleExact F hKernelClosure f)

/-- Cokernel universal property of the lifted source sequence.

Under the exact-category and reflection assumptions on F : E ⥤ A, the lifted sequence K → P →
Q is a conflation whenever F(f) is epic. Consequently f : P → Q defines a colimit cokernel
cofork of the lifted inclusion i : K → P. -/
def kernelLiftOfEpiIsColimit {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsColimit (CokernelCofork.ofπ (f := (kernelLiftOfEpi F hKernelClosure f).ι) f
      (kernelLiftOfEpi_zero F hKernelClosure f)) :=
  isColimit_cokernelCofork_of_isAdmissibleExact
    (kernelLiftOfEpi_isAdmissibleExact F hKernelClosure f)

end CategoryTheory.Functor

end
