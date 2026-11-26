/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.Bounded
public import MathlibExt.CategoryTheory.ExactCategory.KernelOfEpiLift
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Representing the top kernel of an ambient-acyclic bounded complex

Let E be preadditive and F:E → A additive with A abelian.
A finite-support witness of K selects an upper cutoff t.
If F(K) is acyclic, the mapped incoming differential
F(K^{t−1}) → F(K^t) is epic.

Closure of the essential image of F under kernels of epimorphisms makes
its kernel representable by an object of E. Fullness and faithfulness
give the source inclusion and its mapped kernel equations.
If E is Quillen exact with a zero object and binary biproducts, and F
reflects admissible exactness, the represented row is a conflation;
its inclusion is a source kernel and its differential a source cokernel.
Source and ambient category object and morphism universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- For a bounded cochain complex K in a preadditive category, the selected
upper cutoff t is the upper endpoint of its finite term-support witness. -/
def topCutoff (K : Bounded E) : ℤ := K.property.choose_spec.choose

/-- For a bounded complex K with selected upper cutoff t, K^j is zero
whenever t<j, by its finite-support witness. -/
theorem isZero_X_of_topCutoff_lt (K : Bounded E) (j : ℤ) (hj : topCutoff K < j) :
    IsZero (K.obj.X j) :=
  K.property.choose_spec.choose_spec j (Or.inr hj)

/-- For a bounded complex K with selected upper cutoff t, the term K^{t+1}
is zero. -/
theorem isZero_X_topCutoff_succ (K : Bounded E) :
    IsZero (K.obj.X (topCutoff K + 1)) :=
  isZero_X_of_topCutoff_lt K _ (by omega)

variable (F : E ⥤ A) [F.Additive]

/-- Let E be preadditive, A abelian and F:E → A additive. If F(K) is
acyclic and K^{b+1}=0 for an integer b, then the mapped incoming
differential F(K^{b−1}) → F(K^b) is epic. -/
theorem mappedDifferential_epi_of_acyclic_of_isZero_succ (K : Bounded E) (b : ℤ)
    (hb : IsZero (K.obj.X (b + 1)))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    Epi (F.map (K.obj.d (b - 1) b)) := by
  let M := (F.mapHomologicalComplex (.up ℤ)).obj K.obj
  have hExact : (M.sc' (b - 1) b (b + 1)).Exact :=
    (M.exactAt_iff' (b - 1) b (b + 1) (by simp) (by simp)).mp (hK b)
  have hZero : (M.sc' (b - 1) b (b + 1)).g = 0 :=
    (F.map_isZero hb).eq_of_tgt _ _
  have hEpi := ((M.sc' (b - 1) b (b + 1)).exact_iff_epi hZero).mp hExact
  change Epi (F.map (K.obj.d (b - 1) b)) at hEpi
  exact hEpi

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness.

If F(K) is acyclic, F(d_K^{t−1}):F(K^{t−1}) → F(K^t) is epic. -/
theorem mappedTopDifferential_epi (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    Epi (F.map (K.obj.d (topCutoff K - 1) (topCutoff K))) :=
  mappedDifferential_epi_of_acyclic_of_isZero_succ F K (topCutoff K)
    (isZero_X_topCutoff_succ K) hK

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness.

The component of the differential of the termwise mapped complex F(K) at t−1,t is exactly F(d_K^{t−1}). -/
theorem mappedTopDifferential_eq (K : Bounded E) :
    F.map (K.obj.d (topCutoff K - 1) (topCutoff K)) =
      ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).d
        (topCutoff K - 1) (topCutoff K) := rfl

variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

include hKernelClosure

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image.

The ambient kernel of F(d_K^{t−1}) belongs to the essential image of F. -/
theorem topKernel_mem_essImage (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    F.essImage (kernel (F.map (K.obj.d (topCutoff K - 1) (topCutoff K)))) := by
  let _ := mappedTopDifferential_epi F K hK
  exact F.kernelOfEpi_mem_essImage hKernelClosure
    (K.obj.d (topCutoff K - 1) (topCutoff K))

variable [F.Full] [F.Faithful]

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d).

The source kernel lift represents Ker(F(d)) by Z and an inclusion ι:Z → K^{t−1}, with its mapped kernel property. -/
def topKernelLift (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    Functor.KernelLift F (K.obj.d (topCutoff K - 1) (topCutoff K)) := by
  let _ := mappedTopDifferential_epi F K hK
  exact F.kernelLiftOfEpi hKernelClosure (K.obj.d (topCutoff K - 1) (topCutoff K))

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d).

The source object Z is the representative supplied by the essential-image witness for Ker(F(d)). -/
theorem topKernelLift_K (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topKernelLift F hKernelClosure K hK).K =
      (topKernel_mem_essImage F hKernelClosure K hK).witness := rfl

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d).

For the representative isomorphism α:F(Z) ≅ Ker(F(d)), the mapped inclusion is F(ι)=κ∘α, where κ is the ambient kernel inclusion. -/
theorem topKernelLift_map_ι (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    F.map (topKernelLift F hKernelClosure K hK).ι =
      (topKernel_mem_essImage F hKernelClosure K hK).getIso.hom ≫
        kernel.ι (F.map (K.obj.d (topCutoff K - 1) (topCutoff K))) :=
  F.map_preimage _

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d).

The source kernel inclusion satisfies d∘ι=0. -/
theorem topKernelLift_zero (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topKernelLift F hKernelClosure K hK).ι ≫
      K.obj.d (topCutoff K - 1) (topCutoff K) = 0 :=
  (topKernelLift F hKernelClosure K hK).zero

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d).

F(ι):F(Z) → F(K^{t−1}) has the universal property of the kernel of F(d). -/
def topKernelLiftMappedIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι (f := F.map (K.obj.d (topCutoff K - 1) (topCutoff K)))
      (F.map (topKernelLift F hKernelClosure K hK).ι) (by
        rw [← F.map_comp, topKernelLift_zero, F.map_zero])) :=
  (topKernelLift F hKernelClosure K hK).mappedIsLimit

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d).

The second map in the represented source row Z → K^{t−1} → K^t is the original differential d. -/
theorem topKernelLift_shortComplex_g (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topKernelLift F hKernelClosure K hK).shortComplex.g =
      K.obj.d (topCutoff K - 1) (topCutoff K) := rfl

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d).

The mapped row 0 → F(Z) → F(K^{t−1}) → F(K^t) → 0 is short exact in A. -/
theorem topKernelLift_mappedShortExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((topKernelLift F hKernelClosure K hK).shortComplex.map F).ShortExact := by
  let _ := mappedTopDifferential_epi F K hK
  exact (topKernelLift F hKernelClosure K hK).mappedShortExact

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d). Assume E is Quillen exact with a zero object and binary biproducts,
and F reflects admissible exactness.

The represented source row Z → K^{t−1} → K^t is admissible exact. -/
theorem topKernelLift_isAdmissibleExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsAdmissibleExact (topKernelLift F hKernelClosure K hK).shortComplex := by
  let _ := mappedTopDifferential_epi F K hK
  exact (topKernelLift F hKernelClosure K hK).isAdmissibleExact

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d). Assume E is Quillen exact with a zero object and binary biproducts,
and F reflects admissible exactness.

The original top differential d:K^{t−1} → K^t is an admissible epimorphism in E. -/
theorem topDifferential_isAdmissibleEpi (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsAdmissibleEpi (K.obj.d (topCutoff K - 1) (topCutoff K)) :=
  isAdmissibleEpi_g (topKernelLift_isAdmissibleExact F hKernelClosure K hK)

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d). Assume E is Quillen exact with a zero object and binary biproducts,
and F reflects admissible exactness.

The source inclusion ι:Z → K^{t−1} is a kernel of d in E. -/
def topKernelLiftIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι
      (f := K.obj.d (topCutoff K - 1) (topCutoff K))
      (topKernelLift F hKernelClosure K hK).ι (topKernelLift_zero F hKernelClosure K hK)) :=
  isLimit_kernelFork_of_isAdmissibleExact
    (topKernelLift_isAdmissibleExact F hKernelClosure K hK)

/-- Let E be preadditive, A abelian, F:E → A additive and K a bounded
integer cochain complex. Let t be the upper endpoint selected from
K's finite-support witness. Assume F(K) is acyclic and the essential image of F is closed
under kernels of epimorphisms between objects in that image. Assume F is fully faithful. Write d:K^{t−1} → K^t and
Z —ι→ K^{t−1} for the represented source kernel of F(d). Assume E is Quillen exact with a zero object and binary biproducts,
and F reflects admissible exactness.

The original differential d:K^{t−1} → K^t is a cokernel of ι in E. -/
def topKernelLiftIsColimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsColimit (CokernelCofork.ofπ
      (f := (topKernelLift F hKernelClosure K hK).ι)
      (K.obj.d (topCutoff K - 1) (topCutoff K))
      (topKernelLift_zero F hKernelClosure K hK)) :=
  isColimit_cokernelCofork_of_isAdmissibleExact
    (topKernelLift_isAdmissibleExact F hKernelClosure K hK)

end CochainComplex.Bounded

end
