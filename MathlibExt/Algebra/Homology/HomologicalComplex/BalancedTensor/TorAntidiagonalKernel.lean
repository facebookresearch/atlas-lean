/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
Authors: @toskua, Codex
-/
module

public import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.TorBoundary
public import MathlibExt.CategoryTheory.Limits.Shapes.CoproductKernel
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Coproduct kernels of Tor boundaries

Let R be a ring and assume the categories of right and left R-modules admit
projective resolutions. For a right-module complex P of shape c, a left
module N and i = c.prev j, put Bⱼ = image(dᵢⱼ), Zⱼ = cyclesⱼ(P) and
Hⱼ = homologyⱼ(P). The sequence Bⱼ → Zⱼ → Hⱼ gives the connecting map
δ : Tor₁ᴿ(Hⱼ,N) → Bⱼ ⊗ᴿ N. Its image is canonically isomorphic to
ker(Bⱼ ⊗ᴿ N → Zⱼ ⊗ᴿ N).

For families indexed by I, assume I-indexed coproducts exist and are exact
in the category of abelian groups. Both the coproduct of the individual
images of δ and the image of the coproduct boundary identify with the
kernel of the coproduct tensor inclusion. The coproduct Tor group maps
epimorphically to this kernel, naturally in the right complexes.

If tensoring left modules with each selected right term and with its
outgoing differential image preserves homology, the cycles are flat and
the whole coproduct Tor group is isomorphic to the kernel. The left
coefficients are arbitrary throughout.

For integer complexes P,Q, take all pairs (p,q) with p+q=n and coefficient
H_q(Q). The boundary object is image(dₚ₊₁,ₚᴾ), and the full antidiagonal
coproduct has no finite truncation. Tor degree one corresponds to grading
n+1. The comparisons here concern the boundary-to-cycles tensor kernel.

The common-height versions retain independently sized right and left
modules. A general I-indexed family is lifted to T=max(u,v,w,t,ω), including
the index universe ω; integer families use T=max(u,v,w,t). The complex
shape universe is independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex.BalancedTensor

universe u v κ ω w t

private def exactImageKernelIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.Exact) :
    Abelian.image S.f ≅ kernel S.g := by
  let k : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  let : Epi k := hS.epi_kernelLift
  have hfac : Abelian.factorThruImage S.f ≫ S.abelianImageToKernel = k := by
    apply (cancel_mono (kernel.ι S.g)).1
    simp only [Category.assoc, ShortComplex.abelianImageToKernel_comp_kernel_ι,
      Abelian.image.fac, kernel.lift_ι]
  let : Epi S.abelianImageToKernel := epi_of_epi_fac hfac
  let : IsIso S.abelianImageToKernel := inferInstance
  exact asIso S.abelianImageToKernel

private theorem exactImageKernelIso_hom_ι
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.Exact) :
    (exactImageKernelIso S hS).hom ≫ kernel.ι S.g = Abelian.image.ι S.f := by
  change S.abelianImageToKernel ≫ kernel.ι S.g = Abelian.image.ι S.f
  exact S.abelianImageToKernel_comp_kernel_ι


private theorem exactImageKernelIso_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {S S' : ShortComplex C} (hS : S.Exact) (hS' : S'.Exact) (φ : S ⟶ S') :
    (Abelian.im (C := C)).map (Arrow.homMk φ.τ₁ φ.τ₂ φ.comm₁₂) ≫
        (exactImageKernelIso S' hS').hom =
      (exactImageKernelIso S hS).hom ≫
        kernel.map S.g S'.g φ.τ₂ φ.τ₃ φ.comm₂₃.symm := by
  apply (cancel_mono (kernel.ι S'.g)).1
  simp only [Category.assoc, exactImageKernelIso_hom_ι,
    kernel.map, kernel.lift_ι]
  dsimp only [Abelian.im, Abelian.image.ι]
  exact kernel.lift_ι _ _ _

variable (R : Type u) [Ring R]
variable {ι : Type κ} {c : ComplexShape ι}

section Coordinated

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]

/-- For a ring R, a right R-module complex P of shape c, a left R-module N
and i = c.prev j, the connecting boundary
δ : Tor₁ᴿ(homologyⱼ(P),N) → image(dᵢⱼ) ⊗ᴿ N identifies its image
with ker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N). Both module categories
admit projective resolutions; no flatness condition is needed. -/
def torBoundaryImageKernelIso
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{v} R)
    (i j : ι) (hi : c.prev j = i) :
    Abelian.image (torBoundary R P N i j hi) ≅
      kernel (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap P i j)).app N) :=
  exactImageKernelIso (torBoundaryTensorSequence R P N i j hi)
    (torBoundaryTensorSequence_exact R P N i j hi)

/-- For a right R-module complex P, a left R-module N and i = c.prev j,
the forward comparison from the image of the Tor boundary to the tensor
inclusion kernel, followed by the kernel inclusion, equals the image
inclusion into image(dᵢⱼ) ⊗ᴿ N. -/
@[reassoc]
theorem torBoundaryImageKernelIso_hom_ι
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{v} R)
    (i j : ι) (hi : c.prev j = i) :
    (torBoundaryImageKernelIso R P N i j hi).hom ≫
        kernel.ι (((ModuleCat.BalancedTensor.groupBifunctor R).map
          (HomologicalComplex.boundaryCyclesMap P i j)).app N) =
      Abelian.image.ι (torBoundary R P N i j hi) :=
  exactImageKernelIso_hom_ι (torBoundaryTensorSequence R P N i j hi)
    (torBoundaryTensorSequence_exact R P N i j hi)

/-- For a morphism φ : P → P′ of right R-module complexes of shape c,
a fixed left R-module N and i = c.prev j, form the morphism between
their Tor-boundary tensor short complexes. Its components are the
induced maps on Tor₁ᴿ(homologyⱼ(−),N), boundaries tensored with N,
and cycles tensored with N. -/
def torBoundaryTensorSequenceMap
    {P P' : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c}
    (N : ModuleCat.{v} R) (i j : ι) (hi : c.prev j = i) (φ : P ⟶ P') :
    torBoundaryTensorSequence R P N i j hi ⟶
      torBoundaryTensorSequence R P' N i j hi where
  τ₁ := ((ModuleCat.BalancedTensor.torFirst R 1).map
    (HomologicalComplex.homologyMap φ j)).app N
  τ₂ := ((ModuleCat.BalancedTensor.groupBifunctor R).map
    (((HomologicalComplex.boundariesCyclesHomologySequenceFunctor
      (C := ModuleCat.{v} Rᵐᵒᵖ) (c := c) i j).map φ).τ₁)).app N
  τ₃ := ((ModuleCat.BalancedTensor.groupBifunctor R).map
    (((HomologicalComplex.boundariesCyclesHomologySequenceFunctor
      (C := ModuleCat.{v} Rᵐᵒᵖ) (c := c) i j).map φ).τ₂)).app N
  comm₁₂ := torBoundary_naturality R N i j hi φ
  comm₂₃ := by
    let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} :=
      (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
    let ψ := (HomologicalComplex.boundariesCyclesHomologySequenceFunctor
      (C := ModuleCat.{v} Rᵐᵒᵖ) (c := c) i j).map φ
    change F.map ψ.τ₁ ≫ F.map (HomologicalComplex.boundaryCyclesMap P' i j) =
      F.map (HomologicalComplex.boundaryCyclesMap P i j) ≫ F.map ψ.τ₂
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map ψ.comm₁₂

section Coproduct

variable {I : Type ω} [HasColimitsOfShape (Discrete I) AddCommGrpCat.{v}]
  [HasExactColimitsOfShape (Discrete I) AddCommGrpCat.{v}]
variable (P : I → HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
  (N : I → ModuleCat.{v} R) (i j : I → ι) (hi : ∀ a, c.prev (j a) = i a)

/-- For a family Pₐ of right R-module complexes of shape c, left
coefficients Nₐ and indices iₐ,jₐ, take the coproduct of the maps
image(dᵢₐ,jₐᴾₐ) ⊗ᴿ Nₐ → cyclesⱼₐ(Pₐ) ⊗ᴿ Nₐ induced by the boundary
inclusions. The I-indexed coproducts of abelian groups are assumed
to exist; the index and carrier universes are independent. -/
def coproductBoundaryTensorMap :
    (∐ fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).obj
      (Abelian.image ((P a).d (i a) (j a)))).obj (N a)) ⟶
    (∐ fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).obj
      ((P a).cycles (j a))).obj (N a)) :=
  Sigma.map (fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).map
    (HomologicalComplex.boundaryCyclesMap (P a) (i a) (j a))).app (N a))

/-- For families Pₐ of right R-module complexes and left coefficients Nₐ,
with iₐ = c.prev jₐ, take the coproduct of the canonical boundaries
Tor₁ᴿ(homologyⱼₐ(Pₐ),Nₐ) → image(dᵢₐ,jₐᴾₐ) ⊗ᴿ Nₐ.
Both module categories admit projective resolutions and the
I-indexed coproducts exist in abelian groups. -/
def coproductTorBoundary :
    (∐ fun a => ((ModuleCat.BalancedTensor.torFirst R 1).obj
      ((P a).homology (j a))).obj (N a)) ⟶
    (∐ fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).obj
      (Abelian.image ((P a).d (i a) (j a)))).obj (N a)) :=
  Sigma.map (fun a => torBoundary R (P a) (N a) (i a) (j a) (hi a))

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ,
the coproduct Tor boundary followed by the coproduct
boundary-to-cycles tensor map is zero. The constituent maps are
the connecting boundaries of the boundary–cycles–homology sequences. -/
@[reassoc]
theorem coproductTorBoundary_comp_boundaryTensor :
    coproductTorBoundary R P N i j hi ≫ coproductBoundaryTensorMap R P N i j = 0 := by
  apply Sigma.hom_ext
  intro a
  simp only [coproductTorBoundary, coproductBoundaryTensorMap, Category.assoc,
    Sigma.ι_map, Sigma.ι_map_assoc, comp_zero]
  rw [← Category.assoc, torBoundary_comp_boundaryTensor, zero_comp]

/-- For right R-module complexes Pₐ, left coefficients Nₐ and
iₐ = c.prev jₐ, exact I-indexed coproducts identify
∐ₐ image(δₐ) with the kernel of
∐ₐ(image(dᵢₐ,jₐᴾₐ) ⊗ᴿ Nₐ → cyclesⱼₐ(Pₐ) ⊗ᴿ Nₐ).
Here δₐ is the Tor₁ connecting boundary, both module categories
admit projective resolutions, and no module flatness is assumed. -/
def coproductTorBoundaryImagesKernelIso :
    (∐ fun a => Abelian.image (torBoundary R (P a) (N a) (i a) (j a) (hi a))) ≅
      kernel (coproductBoundaryTensorMap R P N i j) :=
  Sigma.mapIso (fun a => torBoundaryImageKernelIso R (P a) (N a) (i a) (j a) (hi a)) ≪≫
    coproductKernelIso (fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap (P a) (i a) (j a))).app (N a))

/-- For a family of right complexes Pₐ and left coefficients Nₐ with
iₐ = c.prev jₐ and exact I-indexed coproducts, the a-th summand of the
coproduct image comparison, followed by the tensor kernel inclusion,
equals image(δₐ) → image(dᵢₐ,jₐᴾₐ) ⊗ᴿ Nₐ followed by its coproduct
injection. -/
@[reassoc]
theorem coproductTorBoundaryImagesKernelIso_ι_hom_ι (a : I) :
    Sigma.ι (fun a => Abelian.image
        (torBoundary R (P a) (N a) (i a) (j a) (hi a))) a ≫
      (coproductTorBoundaryImagesKernelIso R P N i j hi).hom ≫
        kernel.ι (coproductBoundaryTensorMap R P N i j) =
      Abelian.image.ι (torBoundary R (P a) (N a) (i a) (j a) (hi a)) ≫
        Sigma.ι (fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).obj
          (Abelian.image ((P a).d (i a) (j a)))).obj (N a)) a := by
  simp only [coproductTorBoundaryImagesKernelIso, Iso.trans_hom,
    Category.assoc, Sigma.ι_mapIso_hom, Sigma.ι_mapIso_hom_assoc,
    coproductBoundaryTensorMap, coproductKernelIso_hom_ι,
    coproductKernelIso_hom_ι_assoc, torBoundaryImageKernelIso_hom_ι_assoc]

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ
with exact I-indexed coproducts, the comparison from ∐ₐ image(δₐ)
to the tensor inclusion kernel, followed by the kernel inclusion,
is the coproduct of the individual Tor boundary image inclusions. -/
@[reassoc]
theorem coproductTorBoundaryImagesKernelIso_hom_ι :
    (coproductTorBoundaryImagesKernelIso R P N i j hi).hom ≫
        kernel.ι (coproductBoundaryTensorMap R P N i j) =
      Sigma.map (fun a => Abelian.image.ι
        (torBoundary R (P a) (N a) (i a) (j a) (hi a))) := by
  apply Sigma.hom_ext
  intro a
  simp only [Category.assoc, coproductTorBoundaryImagesKernelIso_ι_hom_ι, Sigma.ι_map]

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ
with exact I-indexed coproducts, the inverse kernel comparison to
∐ₐ image(δₐ), followed by the coproduct image inclusions, equals
the kernel inclusion into the coproduct of boundary tensors. -/
@[reassoc]
theorem coproductTorBoundaryImagesKernelIso_inv_image :
    (coproductTorBoundaryImagesKernelIso R P N i j hi).inv ≫
        Sigma.map (fun a => Abelian.image.ι
          (torBoundary R (P a) (N a) (i a) (j a) (hi a))) =
      kernel.ι (coproductBoundaryTensorMap R P N i j) := by
  rw [← coproductTorBoundaryImagesKernelIso_hom_ι R P N i j hi]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ,
the coproduct Tor group maps to the kernel of the coproduct
boundary-to-cycles tensor inclusion. The map is the coproduct of
the individual connecting-boundary kernel lifts followed by the
exact-coproduct kernel comparison. Both module categories admit
projective resolutions and the I-indexed coproducts are exact. -/
def coproductTorBoundaryKernelLift :
    (∐ fun a => ((ModuleCat.BalancedTensor.torFirst R 1).obj
      ((P a).homology (j a))).obj (N a)) ⟶
      kernel (coproductBoundaryTensorMap R P N i j) :=
  Sigma.map (fun a => kernel.lift
    (((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap (P a) (i a) (j a))).app (N a))
    (torBoundary R (P a) (N a) (i a) (j a) (hi a))
    (torBoundary_comp_boundaryTensor R (P a) (N a) (i a) (j a) (hi a))) ≫
      (coproductKernelIso (fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap (P a) (i a) (j a))).app (N a))).hom

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ
with exact I-indexed coproducts, the coproduct Tor kernel lift
followed by inclusion into the boundary tensor coproduct equals
the coproduct of the connecting boundaries δₐ. -/
@[reassoc]
theorem coproductTorBoundaryKernelLift_ι :
    coproductTorBoundaryKernelLift R P N i j hi ≫
        kernel.ι (coproductBoundaryTensorMap R P N i j) =
      coproductTorBoundary R P N i j hi := by
  apply Sigma.hom_ext
  intro a
  simp only [coproductTorBoundaryKernelLift, coproductBoundaryTensorMap,
    coproductTorBoundary, Category.assoc, Sigma.ι_map, Sigma.ι_map_assoc,
    coproductKernelIso_hom_ι, coproductKernelIso_hom_ι_assoc,
    kernel.lift_ι, kernel.lift_ι_assoc]

/-- For right R-module complexes Pₐ, left R-module coefficients Nₐ
and iₐ = c.prev jₐ, the coproduct Tor boundary lift is an epimorphism
onto the kernel of the coproduct boundary-to-cycles tensor map.
Both module categories admit projective resolutions and the
I-indexed coproducts are exact. -/
theorem coproductTorBoundaryKernelLift_epi :
    Epi (coproductTorBoundaryKernelLift R P N i j hi) := by
  let (a : I) : Epi (kernel.lift
      (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (HomologicalComplex.boundaryCyclesMap (P a) (i a) (j a))).app (N a))
      (torBoundary R (P a) (N a) (i a) (j a) (hi a))
      (torBoundary_comp_boundaryTensor R (P a) (N a) (i a) (j a) (hi a))) :=
    (torBoundaryTensorSequence_exact R (P a) (N a) (i a) (j a) (hi a)).epi_kernelLift
  change Epi (Sigma.map _ ≫ (coproductKernelIso _).hom)
  infer_instance

/-- For right R-module complexes Pₐ, left R-module coefficients Nₐ
and iₐ = c.prev jₐ, the coproduct maps
∐ₐ Tor₁ᴿ(homologyⱼₐ(Pₐ),Nₐ) → ∐ₐ(image(dᵢₐ,jₐᴾₐ) ⊗ᴿ Nₐ)
→ ∐ₐ(cyclesⱼₐ(Pₐ) ⊗ᴿ Nₐ)
form a short complex of abelian groups. -/
def coproductTorBoundaryTensorSequence : ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (coproductTorBoundary R P N i j hi)
    (coproductBoundaryTensorMap R P N i j)
    (coproductTorBoundary_comp_boundaryTensor R P N i j hi)

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ
in module categories admitting projective resolutions, the coproduct
Tor-boundary tensor short complex is exact at the boundary tensor
coproduct. The I-indexed coproducts of abelian groups are assumed exact. -/
theorem coproductTorBoundaryTensorSequence_exact :
    (coproductTorBoundaryTensorSequence R P N i j hi).Exact := by
  let S := coproductTorBoundaryTensorSequence R P N i j hi
  let k := kernel.lift S.g S.f S.zero
  have hk : k = coproductTorBoundaryKernelLift R P N i j hi := by
    apply (cancel_mono (kernel.ι S.g)).1
    exact (kernel.lift_ι S.g S.f S.zero).trans
      (coproductTorBoundaryKernelLift_ι R P N i j hi).symm
  let : Epi (coproductTorBoundaryKernelLift R P N i j hi) :=
    coproductTorBoundaryKernelLift_epi R P N i j hi
  let : Epi k := hk.symm ▸ inferInstance
  exact S.exact_iff_epi_kernel_lift.2 inferInstance

/-- For right R-module complexes Pₐ, left R-module coefficients Nₐ
and iₐ = c.prev jₐ, the image of ∐ₐ δₐ is canonically isomorphic to
the kernel of the coproduct boundary-to-cycles tensor map. Both
module categories admit projective resolutions and the I-indexed
coproducts are exact; no flatness condition is imposed on the modules. -/
def coproductTorBoundaryImageKernelIso :
    Abelian.image (coproductTorBoundary R P N i j hi) ≅
      kernel (coproductBoundaryTensorMap R P N i j) :=
  exactImageKernelIso (coproductTorBoundaryTensorSequence R P N i j hi)
    (coproductTorBoundaryTensorSequence_exact R P N i j hi)

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ
with exact I-indexed coproducts, the image-of-coproduct Tor comparison
followed by the tensor kernel inclusion equals the image inclusion
of the coproduct connecting boundary ∐ₐ δₐ. -/
@[reassoc]
theorem coproductTorBoundaryImageKernelIso_hom_ι :
    (coproductTorBoundaryImageKernelIso R P N i j hi).hom ≫
        kernel.ι (coproductBoundaryTensorMap R P N i j) =
      Abelian.image.ι (coproductTorBoundary R P N i j hi) :=
  exactImageKernelIso_hom_ι (coproductTorBoundaryTensorSequence R P N i j hi)
    (coproductTorBoundaryTensorSequence_exact R P N i j hi)


/-- For a family of morphisms φₐ : Pₐ → P′ₐ of right R-module complexes
and fixed left coefficients Nₐ with iₐ = c.prev jₐ, the induced
morphism of coproduct Tor-boundary tensor short complexes has as
components the coproducts of the Tor, boundary tensor and cycle
tensor maps. -/
def coproductTorBoundaryTensorSequenceMap
    {P' : I → HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c}
    (φ : ∀ a, P a ⟶ P' a) :
    coproductTorBoundaryTensorSequence R P N i j hi ⟶
      coproductTorBoundaryTensorSequence R P' N i j hi := by
  let ψ (a : I) := torBoundaryTensorSequenceMap R (N a) (i a) (j a) (hi a) (φ a)
  refine
    { τ₁ := Sigma.map (fun a => (ψ a).τ₁)
      τ₂ := Sigma.map (fun a => (ψ a).τ₂)
      τ₃ := Sigma.map (fun a => (ψ a).τ₃)
      comm₁₂ := ?_
      comm₂₃ := ?_ }
  · change Sigma.map (fun a => (ψ a).τ₁) ≫
        Sigma.map (fun a => (torBoundaryTensorSequence R (P' a) (N a)
          (i a) (j a) (hi a)).f) =
      Sigma.map (fun a => (torBoundaryTensorSequence R (P a) (N a)
        (i a) (j a) (hi a)).f) ≫ Sigma.map (fun a => (ψ a).τ₂)
    rw [Sigma.map_comp, Sigma.map_comp]
    apply congrArg (fun h => Sigma.map h)
    funext a
    exact (ψ a).comm₁₂
  · change Sigma.map (fun a => (ψ a).τ₂) ≫
        Sigma.map (fun a => (torBoundaryTensorSequence R (P' a) (N a)
          (i a) (j a) (hi a)).g) =
      Sigma.map (fun a => (torBoundaryTensorSequence R (P a) (N a)
        (i a) (j a) (hi a)).g) ≫ Sigma.map (fun a => (ψ a).τ₃)
    rw [Sigma.map_comp, Sigma.map_comp]
    apply congrArg (fun h => Sigma.map h)
    funext a
    exact (ψ a).comm₂₃

/-- For a family φₐ : Pₐ → P′ₐ of right complex morphisms and fixed left
coefficients Nₐ with iₐ = c.prev jₐ, the image-of-coproduct Tor
comparisons commute with the induced image map on connecting
boundaries and the induced kernel map on tensor inclusions.
The module categories admit projective resolutions and the
I-indexed coproducts are exact. -/
theorem coproductTorBoundaryImageKernelIso_naturality
    {P' : I → HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c}
    (φ : ∀ a, P a ⟶ P' a) :
    let ψ := coproductTorBoundaryTensorSequenceMap R P N i j hi φ
    (Abelian.im (C := AddCommGrpCat.{v})).map
        (Arrow.homMk ψ.τ₁ ψ.τ₂ ψ.comm₁₂) ≫
      (coproductTorBoundaryImageKernelIso R P' N i j hi).hom =
    (coproductTorBoundaryImageKernelIso R P N i j hi).hom ≫
      kernel.map (coproductBoundaryTensorMap R P N i j)
        (coproductBoundaryTensorMap R P' N i j) ψ.τ₂ ψ.τ₃ ψ.comm₂₃.symm :=
  exactImageKernelIso_naturality
    (coproductTorBoundaryTensorSequence_exact R P N i j hi)
    (coproductTorBoundaryTensorSequence_exact R P' N i j hi)
    (coproductTorBoundaryTensorSequenceMap R P N i j hi φ)


section Flat

variable [∀ a, ((ModuleCat.BalancedTensor.groupBifunctor R).obj
  ((P a).X (j a))).PreservesHomology]
variable [∀ a, ((ModuleCat.BalancedTensor.groupBifunctor R).obj
  (Abelian.image ((P a).d (j a) (c.next (j a))))).PreservesHomology]

/-- For right complexes Pₐ, left coefficients Nₐ and iₐ = c.prev jₐ,
suppose tensoring left modules with each right term (Pₐ)ⱼₐ and
with image(dⱼₐ,c.next jₐᴾₐ) preserves homology. Then the coproduct
connecting boundary identifies ∐ₐ Tor₁ᴿ(homologyⱼₐ(Pₐ),Nₐ) with
the tensor inclusion kernel. Both module categories admit projective
resolutions and the I-indexed coproducts are exact. -/
def coproductTorBoundaryKernelIso :
    (∐ fun a => ((ModuleCat.BalancedTensor.torFirst R 1).obj
      ((P a).homology (j a))).obj (N a)) ≅
      kernel (coproductBoundaryTensorMap R P N i j) :=
  Sigma.mapIso (fun a => torBoundaryKernelIso R (P a) (N a) (i a) (j a) (hi a)) ≪≫
    coproductKernelIso (fun a => ((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap (P a) (i a) (j a))).app (N a))

/-- For right complexes Pₐ and left coefficients Nₐ with
iₐ = c.prev jₐ, assume exact I-indexed coproducts and preservation
of homology by tensoring with the selected right terms and their
outgoing differential images. The whole-Tor kernel comparison
followed by the kernel inclusion equals ∐ₐ δₐ. -/
@[reassoc]
theorem coproductTorBoundaryKernelIso_hom_ι :
    (coproductTorBoundaryKernelIso R P N i j hi).hom ≫
        kernel.ι (coproductBoundaryTensorMap R P N i j) =
      coproductTorBoundary R P N i j hi := by
  apply Sigma.hom_ext
  intro a
  simp only [coproductTorBoundaryKernelIso, coproductBoundaryTensorMap,
    coproductTorBoundary, Iso.trans_hom, Category.assoc,
    Sigma.ι_mapIso_hom, Sigma.ι_mapIso_hom_assoc, Sigma.ι_map,
    coproductKernelIso_hom_ι, coproductKernelIso_hom_ι_assoc,
    torBoundaryKernelIso_hom_ι_assoc]

end Flat
end Coproduct
end Coordinated


/-- For an integer n, the homology antidiagonal consists of every pair
(p,q) of integers satisfying p+q=n. A degree-one Tor term associated
with such a pair has corresponding Künneth grading n+1. -/
abbrev torHomologyAntidiagonal (n : ℤ) : Type :=
  {pq : ℤ × ℤ // pq.1 + pq.2 = n}

private theorem downInt_prev (p : ℤ) : (ComplexShape.down ℤ).prev p = p + 1 :=
  (ComplexShape.down ℤ).prev_eq'
    (show (ComplexShape.down ℤ).Rel (p + 1) p from rfl)

section IntegerAntidiagonal

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]
variable (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)

/-- For integer chain complexes P of right R-modules and Q of left
R-modules, take the coproduct of
image(dₚ₊₁,ₚᴾ) ⊗ᴿ homology_q(Q) → cyclesₚ(P) ⊗ᴿ homology_q(Q)
over every integer pair p+q=n. The ground ring may be noncommutative,
and the coproduct includes the full antidiagonal. -/
def torAntidiagonalTensorMap (n : ℤ) :
    (∐ fun pq : torHomologyAntidiagonal n =>
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj
        (Abelian.image (P.d (pq.val.1 + 1) pq.val.1))).obj (Q.homology pq.val.2)) ⟶
    (∐ fun pq : torHomologyAntidiagonal n =>
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj
        (P.cycles pq.val.1)).obj (Q.homology pq.val.2)) :=
  coproductBoundaryTensorMap R (fun _ : torHomologyAntidiagonal n => P)
    (fun pq => Q.homology pq.val.2) (fun pq => pq.val.1 + 1) (fun pq => pq.val.1)

/-- For integer chain complexes P of right R-modules and Q of left
R-modules in module categories admitting projective resolutions,
take the coproduct of the connecting boundaries
Tor₁ᴿ(homologyₚ(P),homology_q(Q)) → image(dₚ₊₁,ₚᴾ) ⊗ᴿ homology_q(Q)
over all p+q=n. -/
def torAntidiagonalBoundary (n : ℤ) :
    (∐ fun pq : torHomologyAntidiagonal n =>
      ((ModuleCat.BalancedTensor.torFirst R 1).obj
        (P.homology pq.val.1)).obj (Q.homology pq.val.2)) ⟶
    (∐ fun pq : torHomologyAntidiagonal n =>
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj
        (Abelian.image (P.d (pq.val.1 + 1) pq.val.1))).obj (Q.homology pq.val.2)) :=
  coproductTorBoundary R (fun _ : torHomologyAntidiagonal n => P)
    (fun pq => Q.homology pq.val.2) (fun pq => pq.val.1 + 1) (fun pq => pq.val.1)
    (fun pq => downInt_prev pq.val.1)

/-- For integer right and left R-module complexes P,Q in module
categories admitting projective resolutions, the image of the
connecting boundary over all p+q=n is canonically isomorphic to
the kernel of the antidiagonal boundary-to-cycles tensor map.
The coefficients are homology_q(Q), and n is the sum of homology degrees. -/
def torAntidiagonalImageKernelIso (n : ℤ) :
    Abelian.image (torAntidiagonalBoundary R P Q n) ≅
      kernel (torAntidiagonalTensorMap R P Q n) :=
  coproductTorBoundaryImageKernelIso R (fun _ : torHomologyAntidiagonal n => P)
    (fun pq => Q.homology pq.val.2) (fun pq => pq.val.1 + 1) (fun pq => pq.val.1)
    (fun pq => downInt_prev pq.val.1)

/-- For integer right and left R-module complexes P,Q, the forward
comparison from the image of the p+q=n Tor boundary to its tensor
inclusion kernel, followed by the kernel inclusion, is the image
inclusion into ∐ₚ₊q=n(image(dₚ₊₁,ₚᴾ) ⊗ᴿ homology_q(Q)). -/
@[reassoc]
theorem torAntidiagonalImageKernelIso_hom_ι (n : ℤ) :
    (torAntidiagonalImageKernelIso R P Q n).hom ≫
        kernel.ι (torAntidiagonalTensorMap R P Q n) =
      Abelian.image.ι (torAntidiagonalBoundary R P Q n) :=
  coproductTorBoundaryImageKernelIso_hom_ι R (fun _ : torHomologyAntidiagonal n => P)
    (fun pq => Q.homology pq.val.2) (fun pq => pq.val.1 + 1) (fun pq => pq.val.1)
    (fun pq => downInt_prev pq.val.1)

/-- For integer right and left R-module complexes P,Q in module
categories admitting projective resolutions, the coproduct of
the images of
Tor₁ᴿ(homologyₚ(P),homology_q(Q)) → image(dₚ₊₁,ₚᴾ) ⊗ᴿ homology_q(Q)
over all p+q=n is canonically isomorphic to the antidiagonal tensor
inclusion kernel. -/
def torAntidiagonalImagesKernelIso (n : ℤ) :
    (∐ fun pq : torHomologyAntidiagonal n =>
      Abelian.image (torBoundary R P (Q.homology pq.val.2) (pq.val.1 + 1) pq.val.1
        ((ComplexShape.down ℤ).prev_eq'
          (show (ComplexShape.down ℤ).Rel (pq.val.1 + 1) pq.val.1 from rfl)))) ≅
      kernel (torAntidiagonalTensorMap R P Q n) :=
  coproductTorBoundaryImagesKernelIso R (fun _ : torHomologyAntidiagonal n => P)
    (fun pq => Q.homology pq.val.2) (fun pq => pq.val.1 + 1) (fun pq => pq.val.1)
    (fun pq => downInt_prev pq.val.1)

section Flat

variable [∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X p)).PreservesHomology]
variable [∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor R).obj
  (Abelian.image (P.d p ((ComplexShape.down ℤ).next p)))).PreservesHomology]

/-- For integer right and left R-module complexes P,Q, assume tensoring
left modules with Pₚ and with image(dₚ,ₚ₋₁ᴾ) preserves homology for
every p. In module categories admitting projective resolutions,
the whole coproduct ∐ₚ₊q=n Tor₁ᴿ(homologyₚ(P),homology_q(Q)) is
canonically isomorphic to the antidiagonal tensor inclusion kernel.
No exactness hypothesis is imposed on Q. -/
def torAntidiagonalKernelIso (n : ℤ) :
    (∐ fun pq : torHomologyAntidiagonal n =>
      ((ModuleCat.BalancedTensor.torFirst R 1).obj
        (P.homology pq.val.1)).obj (Q.homology pq.val.2)) ≅
      kernel (torAntidiagonalTensorMap R P Q n) := by
  let (pq : torHomologyAntidiagonal n) :
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X pq.val.1)).PreservesHomology :=
    inferInstance
  let (pq : torHomologyAntidiagonal n) :
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj
        (Abelian.image (P.d pq.val.1 ((ComplexShape.down ℤ).next pq.val.1)))).PreservesHomology :=
    inferInstance
  exact coproductTorBoundaryKernelIso R (fun _ : torHomologyAntidiagonal n => P)
    (fun pq => Q.homology pq.val.2) (fun pq => pq.val.1 + 1) (fun pq => pq.val.1)
    (fun pq => downInt_prev pq.val.1)

/-- For integer right and left R-module complexes P,Q, assume tensoring
with every right term Pₚ and its outgoing image preserves homology.
The whole-Tor comparison on p+q=n, followed by the tensor kernel
inclusion, equals the coproduct of the canonical connecting boundaries
with left coefficients homology_q(Q). -/
@[reassoc]
theorem torAntidiagonalKernelIso_hom_ι (n : ℤ) :
    (torAntidiagonalKernelIso R P Q n).hom ≫
        kernel.ι (torAntidiagonalTensorMap R P Q n) =
      torAntidiagonalBoundary R P Q n := by
  exact coproductTorBoundaryKernelIso_hom_ι R (fun _ : torHomologyAntidiagonal n => P)
    (fun pq => Q.homology pq.val.2) (fun pq => pq.val.1 + 1) (fun pq => pq.val.1)
    (fun pq => downInt_prev pq.val.1)

end Flat
end IntegerAntidiagonal

section IndependentUniverses

variable {I : Type ω}

/-- Let R : Type u be a ring and I : Type ω. For a family of right
complexes Pₐ with carriers in universe v and left coefficients Nₐ
in universe w, take their canonical lifts to T=max(u,v,w,t,ω).
For iₐ = c.prev jₐ, the image of the lifted coproduct Tor boundary
is canonically isomorphic to the lifted tensor inclusion kernel.
The additional height t and complex shape universe are independent. -/
def coproductTorBoundaryImageKernelIsoAt
    (P : I → HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
    (N : I → ModuleCat.{w} R) (i j : I → ι) (hi : ∀ a, c.prev (j a) = i a) :
    let PL : I → HomologicalComplex (ModuleCat.{max u v w t ω} Rᵐᵒᵖ) c :=
      fun a => ((ModuleCat.uliftFunctor.{max u v w t ω, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj (P a)
    let NL : I → ModuleCat.{max u v w t ω} R :=
      fun a => (ModuleCat.uliftFunctor.{max u v w t ω, w} R).obj (N a)
    Abelian.image (coproductTorBoundary R PL NL i j hi) ≅
      kernel (coproductBoundaryTensorMap R PL NL i j) := by
  let PL : I → HomologicalComplex (ModuleCat.{max u v w t ω} Rᵐᵒᵖ) c :=
    fun a => ((ModuleCat.uliftFunctor.{max u v w t ω, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj (P a)
  let NL : I → ModuleCat.{max u v w t ω} R :=
    fun a => (ModuleCat.uliftFunctor.{max u v w t ω, w} R).obj (N a)
  let : HasProjectiveResolutions (ModuleCat.{max u v w t ω} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t ω} R) := inferInstance
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{max u v w t ω} := inferInstance
  let : HasExactColimitsOfShape (Discrete I) AddCommGrpCat.{max u v w t ω} := inferInstance
  exact coproductTorBoundaryImageKernelIso R PL NL i j hi

/-- For independently sized right complexes Pₐ and left coefficients Nₐ
indexed by I : Type ω, lift all carriers to T=max(u,v,w,t,ω).
If iₐ = c.prev jₐ, the forward coproduct Tor image comparison followed
by its tensor kernel inclusion is the image inclusion of the lifted
coproduct connecting boundary. -/
@[reassoc]
theorem coproductTorBoundaryImageKernelIsoAt_hom_ι
    (P : I → HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
    (N : I → ModuleCat.{w} R) (i j : I → ι) (hi : ∀ a, c.prev (j a) = i a) :
    let PL : I → HomologicalComplex (ModuleCat.{max u v w t ω} Rᵐᵒᵖ) c :=
      fun a => ((ModuleCat.uliftFunctor.{max u v w t ω, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj (P a)
    let NL : I → ModuleCat.{max u v w t ω} R :=
      fun a => (ModuleCat.uliftFunctor.{max u v w t ω, w} R).obj (N a)
    (coproductTorBoundaryImageKernelIsoAt R P N i j hi).hom ≫
        kernel.ι (coproductBoundaryTensorMap R PL NL i j) =
      Abelian.image.ι (coproductTorBoundary R PL NL i j hi) := by
  let PL : I → HomologicalComplex (ModuleCat.{max u v w t ω} Rᵐᵒᵖ) c :=
    fun a => ((ModuleCat.uliftFunctor.{max u v w t ω, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj (P a)
  let NL : I → ModuleCat.{max u v w t ω} R :=
    fun a => (ModuleCat.uliftFunctor.{max u v w t ω, w} R).obj (N a)
  exact coproductTorBoundaryImageKernelIso_hom_ι R PL NL i j hi

end IndependentUniverses

/-- For a ring R : Type u and integer right and left complexes P,Q
with carriers in universes v,w, take their canonical lifts PL,QL
to T=max(u,v,w,t). The image of the full p+q=n connecting boundary
is canonically isomorphic to the antidiagonal tensor inclusion kernel,
using homology_q(QL) as coefficients. The Tor degree is one and the
additional lift height t is arbitrary. -/
def torAntidiagonalImageKernelIsoAt
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (n : ℤ) :
    let PL : ChainComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) ℤ :=
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex (.down ℤ)).obj P
    let QL : ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
      ((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex (.down ℤ)).obj Q
    Abelian.image (torAntidiagonalBoundary R PL QL n) ≅
      kernel (torAntidiagonalTensorMap R PL QL n) := by
  let PL : ChainComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) ℤ :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex (.down ℤ)).obj P
  let QL : ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex (.down ℤ)).obj Q
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  exact torAntidiagonalImageKernelIso R PL QL n

/-- For independently sized integer right and left R-module complexes
P,Q, lift both to T=max(u,v,w,t). The forward p+q=n Tor image
comparison followed by the tensor kernel inclusion equals the image
inclusion of the connecting boundary for the lifted complexes. -/
@[reassoc]
theorem torAntidiagonalImageKernelIsoAt_hom_ι
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (n : ℤ) :
    let PL : ChainComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) ℤ :=
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex (.down ℤ)).obj P
    let QL : ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
      ((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex (.down ℤ)).obj Q
    (torAntidiagonalImageKernelIsoAt R P Q n).hom ≫
        kernel.ι (torAntidiagonalTensorMap R PL QL n) =
      Abelian.image.ι (torAntidiagonalBoundary R PL QL n) := by
  let PL : ChainComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) ℤ :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex (.down ℤ)).obj P
  let QL : ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex (.down ℤ)).obj Q
  exact torAntidiagonalImageKernelIso_hom_ι R PL QL n



/-- For a ring R and independently sized integer right and left
complexes P,Q, take their canonical lifts PL,QL to T=max(u,v,w,t).
Suppose tensoring left modules with each PLₚ and with its outgoing
differential image preserves homology. Then
∐ₚ₊q=n Tor₁ᴿ(homologyₚ(PL),homology_q(QL))
is canonically isomorphic to the lifted tensor inclusion kernel.
The additional height t is arbitrary, and Q has no exactness premise. -/
def torAntidiagonalKernelIsoAt
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    [∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor R).obj
      ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex
        (.down ℤ)).obj P).X p)).PreservesHomology]
    [∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor R).obj
      (Abelian.image
        ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex
          (.down ℤ)).obj P).d p ((ComplexShape.down ℤ).next p)))).PreservesHomology]
    (n : ℤ) :
    let PL : ChainComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) ℤ :=
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex (.down ℤ)).obj P
    let QL : ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
      ((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex (.down ℤ)).obj Q
    (∐ fun pq : torHomologyAntidiagonal n =>
      ((ModuleCat.BalancedTensor.torFirst R 1).obj
        (PL.homology pq.val.1)).obj (QL.homology pq.val.2)) ≅
      kernel (torAntidiagonalTensorMap R PL QL n) := by
  let PL : ChainComplex (ModuleCat.{max u v w t} Rᵐᵒᵖ) ℤ :=
    ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex (.down ℤ)).obj P
  let QL : ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex (.down ℤ)).obj Q
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} Rᵐᵒᵖ) := inferInstance
  let : HasProjectiveResolutions (ModuleCat.{max u v w t} R) := inferInstance
  let (p : ℤ) : ((ModuleCat.BalancedTensor.groupBifunctor R).obj (PL.X p)).PreservesHomology :=
    inferInstance
  let (p : ℤ) : ((ModuleCat.BalancedTensor.groupBifunctor R).obj
      (Abelian.image (PL.d p ((ComplexShape.down ℤ).next p)))).PreservesHomology :=
    inferInstance
  exact torAntidiagonalKernelIso R PL QL n


end HomologicalComplex.BalancedTensor
