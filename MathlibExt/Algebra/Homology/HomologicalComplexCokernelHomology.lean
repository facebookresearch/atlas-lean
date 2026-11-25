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

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Homology of a cokernel projection at vanishing components

The actual cokernel projection is componentwise epi. Its component is an
isomorphism wherever the defining map's component is zero. Vanishing at
one degree and its outgoing neighbour therefore gives a canonical homology
comparison through the native epi/isomorphism/mono short-complex criterion.
Only finite colimits and the two individual homologies are required.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteColimits C]

section ArbitraryShape

variable {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex C c} (f : K ⟶ L)

/-- A zero defining component makes the actual projection component an isomorphism. -/
theorem isIso_cokernelProjection_f_of_zero (i : ι) (hf : f.f i = 0) :
    IsIso ((cokernel.π f).f i) := by
  let F : HomologicalComplex C c ⥤ C := eval C c i
  have hzero : F.map f = 0 := by
    change f.f i = 0
    exact hf
  let : IsIso (cokernel.π (F.map f)) :=
    CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (cokernel.π (F.map f)) (cokernel.condition (F.map f)))
      (cokernelIsCokernel (F.map f)) hzero
  change IsIso (F.map (cokernel.π f))
  rw [← π_comp_cokernelComparison f F]
  infer_instance

/-- Vanishing at the middle and outgoing degrees earns the homology comparison. -/
theorem quasiIsoAt_cokernelProjection_of_zero_components (i : ι)
    [L.HasHomology i] [(cokernel f).HasHomology i]
    (hi : f.f i = 0) (hnext : f.f (c.next i) = 0) :
    QuasiIsoAt (cokernel.π f) i := by
  let : IsIso ((cokernel.π f).f i) := isIso_cokernelProjection_f_of_zero f i hi
  let : IsIso ((cokernel.π f).f (c.next i)) :=
    isIso_cokernelProjection_f_of_zero f (c.next i) hnext
  rw [quasiIsoAt_iff]
  let : Epi (((shortComplexFunctor C c i).map (cokernel.π f)).τ₁) := by
    change Epi ((cokernel.π f).f (c.prev i))
    infer_instance
  let : IsIso (((shortComplexFunctor C c i).map (cokernel.π f)).τ₂) := by
    change IsIso ((cokernel.π f).f i)
    infer_instance
  let : Mono (((shortComplexFunctor C c i).map (cokernel.π f)).τ₃) := by
    change Mono ((cokernel.π f).f (c.next i))
    infer_instance
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono
    ((shortComplexFunctor C c i).map (cokernel.π f))

/-- The canonical isomorphism is induced by the original cokernel projection itself. -/
def cokernelHomologyIsoOfZeroComponents (i : ι)
    [L.HasHomology i] [(cokernel f).HasHomology i]
    (hi : f.f i = 0) (hnext : f.f (c.next i) = 0) :
    L.homology i ≅ (cokernel f).homology i := by
  letI := quasiIsoAt_cokernelProjection_of_zero_components f i hi hnext
  exact isoOfQuasiIsoAt (cokernel.π f) i

/-- The canonical comparison retains the actual induced homology map. -/
theorem cokernelHomologyIsoOfZeroComponents_hom (i : ι)
    [L.HasHomology i] [(cokernel f).HasHomology i]
    (hi : f.f i = 0) (hnext : f.f (c.next i) = 0) :
    (cokernelHomologyIsoOfZeroComponents f i hi hnext).hom =
      homologyMap (cokernel.π f) i := rfl

end ArbitraryShape

section Nonnegative

variable {K L : ChainComplex C ℕ} (f : K ⟶ L)

/-- At the nonnegative terminal degree only the degree-zero defining component must vanish. -/
def cokernelHomologyZeroIso [L.HasHomology 0] [(cokernel f).HasHomology 0]
    (hf : f.f 0 = 0) : L.homology 0 ≅ (cokernel f).homology 0 :=
  cokernelHomologyIsoOfZeroComponents f 0 hf (by
    erw [ChainComplex.next_nat_zero]
    exact hf)

/-- Degree one needs vanishing at degrees one and zero, with the incoming projection epi. -/
def cokernelHomologyOneIso [L.HasHomology 1] [(cokernel f).HasHomology 1]
    (h1 : f.f 1 = 0) (h0 : f.f 0 = 0) : L.homology 1 ≅ (cokernel f).homology 1 :=
  cokernelHomologyIsoOfZeroComponents f 1 h1 (by
    erw [ChainComplex.next_nat_succ (0 : ℕ)]
    exact h0)

end Nonnegative

end HomologicalComplex
