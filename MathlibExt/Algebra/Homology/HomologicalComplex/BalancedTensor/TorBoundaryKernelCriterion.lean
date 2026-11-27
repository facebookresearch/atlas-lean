/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
Authors: @toskua, Codex
-/
module

public import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorBoundary
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# When the Tor boundary identifies the tensor kernel

Let R be a ring, P a complex of right R-modules of shape c, and N a left
R-module. Assume the right and left module categories admit projective
resolutions. For i = c.prev j, put Bⱼ = image(dᵢⱼ), Zⱼ = cyclesⱼ(P) and
Hⱼ = homologyⱼ(P). The short exact sequence Bⱼ → Zⱼ → Hⱼ gives
δ : Tor₁ᴿ(Hⱼ,N) → Bⱼ ⊗ᴿ N and the preceding map
α : Tor₁ᴿ(Zⱼ,N) → Tor₁ᴿ(Hⱼ,N) induced by the homology projection.

The lift of δ to Kⱼ = ker(Bⱼ ⊗ᴿ N → Zⱼ ⊗ᴿ N) is an epimorphism.
It is an isomorphism if and only if α = 0. The resulting comparison has δ
as its forward composite with the kernel inclusion. Vanishing of
Tor₁ᴿ(Zⱼ,N) is a sufficient condition.

These criteria impose no tensor exactness condition on the term of P, its
outgoing differential image or N. Versions for independent module carrier
universes use the cycles and homology of the canonically lifted complex
at T = max(u,v,w,t), with arbitrary additional lift height t and independent
shape universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex.BalancedTensor

universe u v w t κ

variable (R : Type u) [Ring R]
variable {ι : Type κ} {c : ComplexShape ι}

section Coordinated

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]
variable (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
  (N : ModuleCat.{v} R) (i j : ι) (hi : c.prev j = i)

/-- For a ring R, a right R-module complex P of arbitrary shape and a left
R-module N, the projection cyclesⱼ(P) → homologyⱼ(P) induces
α : Tor₁ᴿ(cyclesⱼ(P),N) → Tor₁ᴿ(homologyⱼ(P),N). The right and left
module categories are assumed to admit projective resolutions. -/
def torCyclesHomologyMap :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.cycles j)).obj N ⟶
      ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j)).obj N :=
  ((ModuleCat.BalancedTensor.torFirst R 1).map (P.homologyπ j)).app N

/-- For a right R-module complex P, a left R-module N and i = c.prev j
in module categories admitting projective resolutions, the composite
Tor₁ᴿ(cyclesⱼ(P),N) → Tor₁ᴿ(homologyⱼ(P),N) → image(dᵢⱼ) ⊗ᴿ N
is zero. Its second arrow is the connecting boundary of the
boundary–cycles–homology sequence. -/
@[reassoc]
theorem torCyclesHomologyMap_comp_torBoundary :
    torCyclesHomologyMap R P N j ≫ torBoundary R P N i j hi = 0 := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor R) N
  let S := HomologicalComplex.boundariesCyclesHomologySequence P i j
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi
  obtain ⟨hz, _⟩ := LeftDerivedDelta.LDexact_C F 0 S hS
  change (F.leftDerived 1).map S.g ≫
    (LeftDerivedDelta.LDdelta F 0 S hS ≫ (F.leftDerivedZeroIsoSelf.app S.X₁).hom) = 0
  rw [← Category.assoc, hz, zero_comp]

/-- For a ring R, a right R-module complex P, a left R-module N and
i = c.prev j, the homology projection and connecting boundary form
the short complex
Tor₁ᴿ(cyclesⱼ(P),N) → Tor₁ᴿ(homologyⱼ(P),N) → image(dᵢⱼ) ⊗ᴿ N
of abelian groups, using projective resolutions in both module categories. -/
def torCyclesBoundaryTensorSequence : ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (torCyclesHomologyMap R P N j) (torBoundary R P N i j hi)
    (torCyclesHomologyMap_comp_torBoundary R P N i j hi)

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
the Tor window
Tor₁ᴿ(cyclesⱼ(P),N) → Tor₁ᴿ(homologyⱼ(P),N) → image(dᵢⱼ) ⊗ᴿ N
is exact at its middle term. The two module categories admit projective
resolutions; the exactness comes from the boundary–cycles–homology
short exact sequence. -/
theorem torCyclesBoundaryTensorSequence_exact :
    (torCyclesBoundaryTensorSequence R P N i j hi).Exact := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
    (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let : F.Additive :=
    Functor.LeftDerivedBalance.flippedObjAdditive (ModuleCat.BalancedTensor.groupBifunctor R) N
  let S := HomologicalComplex.boundariesCyclesHomologySequence P i j
  let hS : S.ShortExact :=
    HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi
  obtain ⟨hz, hExact⟩ := LeftDerivedDelta.LDexact_C F 0 S hS
  let T := ShortComplex.mk ((F.leftDerived 1).map S.g)
    (LeftDerivedDelta.LDdelta F 0 S hS) hz
  let e : (F.leftDerived 0).obj S.X₁ ≅ F.obj S.X₁ := F.leftDerivedZeroIsoSelf.app S.X₁
  let eT : T ≅ torCyclesBoundaryTensorSequence R P N i j hi :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by
        change (𝟙 _) ≫ (F.leftDerived 1).map S.g =
          (F.leftDerived 1).map S.g ≫ (𝟙 _)
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
      (by
        change (𝟙 _) ≫ (LeftDerivedDelta.LDdelta F 0 S hS ≫ e.hom) =
          LeftDerivedDelta.LDdelta F 0 S hS ≫ e.hom
        exact Category.id_comp _)
  exact ShortComplex.exact_of_iso eT hExact

/-- For a right R-module complex P, a left R-module N and i = c.prev j
in module categories admitting projective resolutions, the connecting
boundary Tor₁ᴿ(homologyⱼ(P),N) → image(dᵢⱼ) ⊗ᴿ N is monic if and
only if the preceding map induced by cyclesⱼ(P) → homologyⱼ(P) is zero. -/
theorem torBoundary_mono_iff_cyclesMap_zero :
    Mono (torBoundary R P N i j hi) ↔ torCyclesHomologyMap R P N j = 0 := by
  let S := torCyclesBoundaryTensorSequence R P N i j hi
  have hS : S.Exact := torCyclesBoundaryTensorSequence_exact R P N i j hi
  change Mono S.g ↔ S.f = 0
  constructor
  · intro hm
    let : Mono S.g := hm
    exact (cancel_mono S.g).1 (S.zero.trans zero_comp.symm)
  · intro hf
    exact (S.exact_iff_mono hf).1 hS

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
lift the connecting boundary to
ker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N). Its composite with the
kernel inclusion is the connecting map from Tor₁ᴿ(homologyⱼ(P),N).
Both module categories admit projective resolutions. -/
def torBoundaryKernelLift :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j)).obj N ⟶
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) :=
  kernel.lift
    (((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap P i j)).app N)
    (torBoundary R P N i j hi) (torBoundary_comp_boundaryTensor R P N i j hi)

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
the lift Tor₁ᴿ(homologyⱼ(P),N) → ker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N)
followed by the kernel inclusion equals the canonical Tor boundary
to image(dᵢⱼ) ⊗ᴿ N. -/
@[reassoc]
theorem torBoundaryKernelLift_ι :
    torBoundaryKernelLift R P N i j hi ≫
        kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
          (HomologicalComplex.boundaryCyclesMap P i j)).app N) =
      torBoundary R P N i j hi :=
  kernel.lift_ι _ _ _

/-- For a right R-module complex P, a left R-module N and i = c.prev j
in module categories admitting projective resolutions, the Tor boundary
lift to ker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N) is an epimorphism,
by exactness of the Tor-boundary tensor sequence. -/
theorem torBoundaryKernelLift_epi : Epi (torBoundaryKernelLift R P N i j hi) :=
  (torBoundaryTensorSequence_exact R P N i j hi).epi_kernelLift

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
the boundary lift
Tor₁ᴿ(homologyⱼ(P),N) → ker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N)
is an isomorphism exactly when the map
Tor₁ᴿ(cyclesⱼ(P),N) → Tor₁ᴿ(homologyⱼ(P),N) is zero. Both module
categories admit projective resolutions; no tensor exactness premise
on P or N is needed. -/
theorem torBoundaryKernelLift_isIso_iff :
    IsIso (torBoundaryKernelLift R P N i j hi) ↔ torCyclesHomologyMap R P N j = 0 := by
  constructor
  · intro h
    let : IsIso (torBoundaryKernelLift R P N i j hi) := h
    have hm : Mono (torBoundary R P N i j hi) := by
      rw [← torBoundaryKernelLift_ι R P N i j hi]
      infer_instance
    exact (torBoundary_mono_iff_cyclesMap_zero R P N i j hi).1 hm
  · intro h
    let : Mono (torBoundary R P N i j hi) :=
      (torBoundary_mono_iff_cyclesMap_zero R P N i j hi).2 h
    let : Mono (torBoundaryKernelLift R P N i j hi) :=
      mono_of_mono_fac (torBoundaryKernelLift_ι R P N i j hi)
    let : Epi (torBoundaryKernelLift R P N i j hi) := torBoundaryKernelLift_epi R P N i j hi
    infer_instance

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
suppose the homology projection induces the zero map
Tor₁ᴿ(cyclesⱼ(P),N) → Tor₁ᴿ(homologyⱼ(P),N). Then the connecting
boundary gives a canonical isomorphism
Tor₁ᴿ(homologyⱼ(P),N) ≅ ker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N)
in module categories admitting projective resolutions. -/
def torBoundaryKernelIsoOfCyclesMapZero
    (h : torCyclesHomologyMap R P N j = 0) :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j)).obj N ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) := by
  let : IsIso (torBoundaryKernelLift R P N i j hi) :=
    (torBoundaryKernelLift_isIso_iff R P N i j hi).2 h
  exact asIso (torBoundaryKernelLift R P N i j hi)

/-- For a right R-module complex P, a left R-module N, i = c.prev j and
a zero cycles-to-homology Tor map, the forward comparison from
Tor₁ᴿ(homologyⱼ(P),N) to the tensor inclusion kernel is the canonical
kernel lift of the connecting boundary. -/
theorem torBoundaryKernelIsoOfCyclesMapZero_hom
    (h : torCyclesHomologyMap R P N j = 0) :
    (torBoundaryKernelIsoOfCyclesMapZero R P N i j hi h).hom =
      torBoundaryKernelLift R P N i j hi := rfl

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
assume the cycles-to-homology Tor map is zero. The forward kernel
comparison followed by inclusion into image(dᵢⱼ) ⊗ᴿ N equals the
connecting boundary from Tor₁ᴿ(homologyⱼ(P),N). -/
@[reassoc]
theorem torBoundaryKernelIsoOfCyclesMapZero_hom_ι
    (h : torCyclesHomologyMap R P N j = 0) :
    (torBoundaryKernelIsoOfCyclesMapZero R P N i j hi h).hom ≫
        kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
          (HomologicalComplex.boundaryCyclesMap P i j)).app N) =
      torBoundary R P N i j hi :=
  torBoundaryKernelLift_ι R P N i j hi

/-- For a right R-module complex P, a left R-module N and i = c.prev j
with zero cycles-to-homology Tor map, the inverse comparison from the
tensor inclusion kernel to Tor₁ᴿ(homologyⱼ(P),N), followed by the
connecting boundary, equals the kernel inclusion into image(dᵢⱼ) ⊗ᴿ N. -/
@[reassoc]
theorem torBoundaryKernelIsoOfCyclesMapZero_inv_boundary
    (h : torCyclesHomologyMap R P N j = 0) :
    (torBoundaryKernelIsoOfCyclesMapZero R P N i j hi h).inv ≫
        torBoundary R P N i j hi =
      kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) := by
  rw [← torBoundaryKernelIsoOfCyclesMapZero_hom_ι R P N i j hi h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- For a right R-module complex P and a left R-module N in module
categories admitting projective resolutions, if Tor₁ᴿ(cyclesⱼ(P),N)
is a zero object, its map to Tor₁ᴿ(homologyⱼ(P),N) induced by the
homology projection is zero. -/
theorem torCyclesHomologyMap_eq_zero_of_isZero
    (hZ : IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (P.cycles j)).obj N)) :
    torCyclesHomologyMap R P N j = 0 :=
  hZ.eq_of_src _ 0

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
vanishing of Tor₁ᴿ(cyclesⱼ(P),N) gives the canonical isomorphism
Tor₁ᴿ(homologyⱼ(P),N) ≅ ker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N).
Both module categories admit projective resolutions, and the
comparison imposes no flatness condition on the term or outgoing image. -/
def torBoundaryKernelIsoOfIsZeroCyclesTor
    (hZ : IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (P.cycles j)).obj N)) :
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (P.homology j)).obj N ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) :=
  torBoundaryKernelIsoOfCyclesMapZero R P N i j hi
    (torCyclesHomologyMap_eq_zero_of_isZero R P N j hZ)

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
if Tor₁ᴿ(cyclesⱼ(P),N) vanishes, the forward comparison followed by
the tensor kernel inclusion is the canonical connecting boundary
Tor₁ᴿ(homologyⱼ(P),N) → image(dᵢⱼ) ⊗ᴿ N. -/
@[reassoc]
theorem torBoundaryKernelIsoOfIsZeroCyclesTor_hom_ι
    (hZ : IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (P.cycles j)).obj N)) :
    (torBoundaryKernelIsoOfIsZeroCyclesTor R P N i j hi hZ).hom ≫
        kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
          (HomologicalComplex.boundaryCyclesMap P i j)).app N) =
      torBoundary R P N i j hi :=
  torBoundaryKernelIsoOfCyclesMapZero_hom_ι R P N i j hi
    (torCyclesHomologyMap_eq_zero_of_isZero R P N j hZ)

end Coordinated

section IndependentUniverses

/-- For a ring R : Type u, a right complex P with carriers in universe v
and a left coefficient N in universe w, lift both to T = max(u,v,w,t).
For i = c.prev j, the Tor boundary kernel lift of the lifted objects is
an isomorphism if and only if the lifted complex's cycles-to-homology
Tor map is zero. The lift height t and the shape universe are independent. -/
theorem torBoundaryKernelLiftAt_isIso_iff
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{w} R)
    (i j : ι) (hi : c.prev j = i) :
    let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
    let NL : ModuleCat.{max u v w t} R :=
      (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
    IsIso (torBoundaryKernelLift R PL NL i j hi) ↔ torCyclesHomologyMap R PL NL j = 0 := by
  let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
  let NL : ModuleCat.{max u v w t} R :=
    (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  exact torBoundaryKernelLift_isIso_iff R PL NL i j hi

/-- For a ring R and independently sized right complex P and left
coefficient N, take their canonical lifts PL,NL to T = max(u,v,w,t).
If i = c.prev j and Tor₁ᴿ(cyclesⱼ(PL),NL) → Tor₁ᴿ(homologyⱼ(PL),NL)
is zero, the lifted connecting boundary identifies
Tor₁ᴿ(homologyⱼ(PL),NL) with the lifted tensor inclusion kernel.
The additional lift height t is arbitrary. -/
def torBoundaryKernelIsoOfCyclesMapZeroAt
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{w} R)
    (i j : ι) (hi : c.prev j = i)
    (h :
      let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
        ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
      let NL : ModuleCat.{max u v w t} R :=
        (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
      torCyclesHomologyMap R PL NL j = 0) :
    let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
    let NL : ModuleCat.{max u v w t} R :=
      (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (PL.homology j)).obj NL ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap PL i j)).app NL) := by
  let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
  let NL : ModuleCat.{max u v w t} R :=
    (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  exact torBoundaryKernelIsoOfCyclesMapZero R PL NL i j hi h

/-- For a ring R and independently sized right complex P and left
coefficient N, lift both to T = max(u,v,w,t). If i = c.prev j and
Tor₁ᴿ(cyclesⱼ(PL),NL) vanishes, the canonical lifted boundary gives
Tor₁ᴿ(homologyⱼ(PL),NL) ≅ ker(image(dᵢⱼᴾᴸ) ⊗ᴿ NL → cyclesⱼ(PL) ⊗ᴿ NL).
The condition concerns the cycles of PL and requires no term or image
tensor exactness hypothesis. -/
def torBoundaryKernelIsoOfIsZeroCyclesTorAt
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{w} R)
    (i j : ι) (hi : c.prev j = i)
    (hZ :
      let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
        ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
      let NL : ModuleCat.{max u v w t} R :=
        (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
      IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (PL.cycles j)).obj NL)) :
    let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
    let NL : ModuleCat.{max u v w t} R :=
      (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
    ((ModuleCat.BalancedTensor.torFirst R 1).obj (PL.homology j)).obj NL ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap PL i j)).app NL) := by
  let PL : HomologicalComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) c :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P
  let NL : ModuleCat.{max u v w t} R :=
    (ModuleCat.uliftFunctor.{max u v w t, w} R).obj N
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  exact torBoundaryKernelIsoOfIsZeroCyclesTor R PL NL i j hi hZ

end IndependentUniverses

end HomologicalComplex.BalancedTensor
