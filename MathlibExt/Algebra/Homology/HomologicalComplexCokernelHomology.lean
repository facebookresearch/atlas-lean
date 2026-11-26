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
# Cokernel projections at vanishing components

Let C be a category with zero morphisms and finite colimits, c an arbitrary
complex shape on an independently sized index type, and f:K → L a map of
complexes of shape c. The cokernel projection π:L → Coker(f) is
componentwise epic, and πᵢ is an isomorphism whenever fᵢ=0.

Assume L and Coker(f) have the chosen homology objects at i.
If fᵢ=0 and f_{c.next(i)}=0, then π induces a homology isomorphism
Hᵢ(L) ≅ Hᵢ(Coker(f)). For nonnegative chain complexes, degree zero
needs only f₀=0, and degree one needs f₁=f₀=0.
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

/-- Let C have zero morphisms and finite colimits, c be any complex shape,
and f:K → L a map of complexes of shape c. If its component fᵢ
is zero, then the degree-i component of the cokernel projection
π:L → Coker(f) is an isomorphism. -/
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

/-- Let C have zero morphisms and finite colimits, c be any complex shape,
and f:K → L a map of complexes. Assume L and Coker(f) have the
chosen homology objects at i. If fᵢ=0 and f_{c.next(i)}=0, the
cokernel projection L → Coker(f) is a quasi-isomorphism at i. -/
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

/-- Let C have zero morphisms and finite colimits, c be any complex shape,
and f:K → L a map of complexes. With chosen homology objects of
L and Coker(f) at i and fᵢ=f_{c.next(i)}=0, the canonical
isomorphism Hᵢ(L) ≅ Hᵢ(Coker(f)) induced by the cokernel projection. -/
def cokernelHomologyIsoOfZeroComponents (i : ι)
    [L.HasHomology i] [(cokernel f).HasHomology i]
    (hi : f.f i = 0) (hnext : f.f (c.next i) = 0) :
    L.homology i ≅ (cokernel f).homology i := by
  letI := quasiIsoAt_cokernelProjection_of_zero_components f i hi hnext
  exact isoOfQuasiIsoAt (cokernel.π f) i

/-- Let C have zero morphisms and finite colimits, c be any complex shape,
and f:K → L a map of complexes with fᵢ=f_{c.next(i)}=0.
For the chosen homology objects at i, the forward map of
Hᵢ(L) ≅ Hᵢ(Coker(f)) is exactly the homology map of the
cokernel projection L → Coker(f). -/
theorem cokernelHomologyIsoOfZeroComponents_hom (i : ι)
    [L.HasHomology i] [(cokernel f).HasHomology i]
    (hi : f.f i = 0) (hnext : f.f (c.next i) = 0) :
    (cokernelHomologyIsoOfZeroComponents f i hi hnext).hom =
      homologyMap (cokernel.π f) i := rfl

end ArbitraryShape

section Nonnegative

variable {K L : ChainComplex C ℕ} (f : K ⟶ L)

/-- Let C have zero morphisms and finite colimits, and f:K → L be a map
of nonnegative chain complexes. If f₀=0 and L and Coker(f) have
the chosen degree-zero homology objects, their cokernel projection
induces the canonical isomorphism H₀(L) ≅ H₀(Coker(f)). -/
def cokernelHomologyZeroIso [L.HasHomology 0] [(cokernel f).HasHomology 0]
    (hf : f.f 0 = 0) : L.homology 0 ≅ (cokernel f).homology 0 :=
  cokernelHomologyIsoOfZeroComponents f 0 hf (by
    erw [ChainComplex.next_nat_zero]
    exact hf)

/-- Let C have zero morphisms and finite colimits, and f:K → L be a map
of nonnegative chain complexes. If f₁=f₀=0 and L and Coker(f)
have the chosen degree-one homology objects, their cokernel projection
induces the canonical isomorphism H₁(L) ≅ H₁(Coker(f)). -/
def cokernelHomologyOneIso [L.HasHomology 1] [(cokernel f).HasHomology 1]
    (h1 : f.f 1 = 0) (h0 : f.f 0 = 0) : L.homology 1 ≅ (cokernel f).homology 1 :=
  cokernelHomologyIsoOfZeroComponents f 1 h1 (by
    erw [ChainComplex.next_nat_succ (0 : ℕ)]
    exact h0)

end Nonnegative

end HomologicalComplex
