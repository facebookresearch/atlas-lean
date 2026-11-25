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
# The original top kernel of an ambient-acyclic bounded cochain

The top cutoff is chosen from the original bounded complex's finite-support
witness. Ambient acyclicity makes its actual incoming top differential epic.
Kernel-of-epimorphism closure of the specified ambient image then supplies a
source representative of the actual ambient kernel. Fullness and faithfulness
earn its original inclusion and kernel equations. Reflection of conflations
earns the source admissible short sequence and both source universal properties.

All source and ambient object and Hom universes remain independent. The
ambient exact embedding is retained in the same-E comparison; each lemma here
states the structural inputs it uses. No source homology, cycle, epi, kernel
universal property, or comparison outcome is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- The upper endpoint of the actual finite-support witness of the original cochain. -/
def topCutoff (K : Bounded E) : ℤ := K.property.choose_spec.choose

/-- The chosen original support witness kills each actual term above the top cutoff. -/
theorem isZero_X_of_topCutoff_lt (K : Bounded E) (j : ℤ) (hj : topCutoff K < j) :
    IsZero (K.obj.X j) :=
  K.property.choose_spec.choose_spec j (Or.inr hj)

/-- The original term immediately after the chosen upper endpoint is zero. -/
theorem isZero_X_topCutoff_succ (K : Bounded E) :
    IsZero (K.obj.X (topCutoff K + 1)) :=
  isZero_X_of_topCutoff_lt K _ (by omega)

variable (F : E ⥤ A) [F.Additive]

/-- At an actual upper cutoff, ambient exactness makes the original incoming map epic. -/
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

/-- The same original top differential is epic after the specified ambient functor. -/
theorem mappedTopDifferential_epi (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    Epi (F.map (K.obj.d (topCutoff K - 1) (topCutoff K))) :=
  mappedDifferential_epi_of_acyclic_of_isZero_succ F K (topCutoff K)
    (isZero_X_topCutoff_succ K) hK

/-- The mapped original top differential is the literal differential of the mapped raw cochain. -/
theorem mappedTopDifferential_eq (K : Bounded E) :
    F.map (K.obj.d (topCutoff K - 1) (topCutoff K)) =
      ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).d
        (topCutoff K - 1) (topCutoff K) := rfl

variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

include hKernelClosure

/-- The original image kernel closure applies to the earned ambient top epimorphism. -/
theorem topKernel_mem_essImage (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    F.essImage (kernel (F.map (K.obj.d (topCutoff K - 1) (topCutoff K)))) := by
  let _ := mappedTopDifferential_epi F K hK
  exact F.kernelOfEpi_mem_essImage hKernelClosure
    (K.obj.d (topCutoff K - 1) (topCutoff K))

variable [F.Full] [F.Faithful]

/-- Lift the actual ambient top kernel through the original fully faithful embedding. -/
def topKernelLift (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    Functor.KernelLift F (K.obj.d (topCutoff K - 1) (topCutoff K)) := by
  let _ := mappedTopDifferential_epi F K hK
  exact F.kernelLiftOfEpi hKernelClosure (K.obj.d (topCutoff K - 1) (topCutoff K))

/-- The original source representative is chosen from the earned essential-image witness. -/
theorem topKernelLift_K (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topKernelLift F hKernelClosure K hK).K =
      (topKernel_mem_essImage F hKernelClosure K hK).witness := rfl

/-- The entire mapped kernel inclusion uses the same earned kernel chart. -/
theorem topKernelLift_map_ι (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    F.map (topKernelLift F hKernelClosure K hK).ι =
      (topKernel_mem_essImage F hKernelClosure K hK).getIso.hom ≫
        kernel.ι (F.map (K.obj.d (topCutoff K - 1) (topCutoff K))) :=
  F.map_preimage _

/-- The actual source kernel inclusion is killed by the original differential. -/
theorem topKernelLift_zero (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topKernelLift F hKernelClosure K hK).ι ≫
      K.obj.d (topCutoff K - 1) (topCutoff K) = 0 :=
  (topKernelLift F hKernelClosure K hK).zero

/-- The mapped inclusion has the actual ambient kernel universal property. -/
def topKernelLiftMappedIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι (f := F.map (K.obj.d (topCutoff K - 1) (topCutoff K)))
      (F.map (topKernelLift F hKernelClosure K hK).ι) (by
        rw [← F.map_comp, topKernelLift_zero, F.map_zero])) :=
  (topKernelLift F hKernelClosure K hK).mappedIsLimit

/-- The actual second map in the source row is the unchanged original top differential. -/
theorem topKernelLift_shortComplex_g (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topKernelLift F hKernelClosure K hK).shortComplex.g =
      K.obj.d (topCutoff K - 1) (topCutoff K) := rfl

/-- The actual represented kernel row maps to an ambient short exact sequence. -/
theorem topKernelLift_mappedShortExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((topKernelLift F hKernelClosure K hK).shortComplex.map F).ShortExact := by
  let _ := mappedTopDifferential_epi F K hK
  exact (topKernelLift F hKernelClosure K hK).mappedShortExact

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- Reflection of the actual ambient row earns the original source conflation. -/
theorem topKernelLift_isAdmissibleExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsAdmissibleExact (topKernelLift F hKernelClosure K hK).shortComplex := by
  let _ := mappedTopDifferential_epi F K hK
  exact (topKernelLift F hKernelClosure K hK).isAdmissibleExact

/-- The actual original top differential is an admissible epimorphism in the source. -/
theorem topDifferential_isAdmissibleEpi (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsAdmissibleEpi (K.obj.d (topCutoff K - 1) (topCutoff K)) :=
  isAdmissibleEpi_g (topKernelLift_isAdmissibleExact F hKernelClosure K hK)

/-- The original represented inclusion has the kernel universal property in E itself. -/
def topKernelLiftIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι
      (f := K.obj.d (topCutoff K - 1) (topCutoff K))
      (topKernelLift F hKernelClosure K hK).ι (topKernelLift_zero F hKernelClosure K hK)) :=
  isLimit_kernelFork_of_isAdmissibleExact
    (topKernelLift_isAdmissibleExact F hKernelClosure K hK)

/-- The same original top differential is a source cokernel of that represented inclusion. -/
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
