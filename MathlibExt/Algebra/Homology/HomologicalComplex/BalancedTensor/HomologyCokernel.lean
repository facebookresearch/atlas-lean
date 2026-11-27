/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.LeftGroupAdjunction
public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesImage
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Cokernels of tensor boundary inclusions

Let R be a possibly noncommutative ring, P a complex of right R-modules of
shape c, and N a left R-module. For i = c.prev j, write Bⱼ = image(dᵢⱼ),
Zⱼ = cyclesⱼ(P) and Hⱼ = homologyⱼ(P). The boundary inclusion b : Bⱼ → Zⱼ
and the homology projection π : Zⱼ → Hⱼ form a short exact sequence.
The balanced tensor functor − ⊗ᴿ N preserves its cokernel, giving
coker(b ⊗ 1) ≅ Hⱼ ⊗ᴿ N in the category of abelian groups.

The comparison carries the cokernel class of z ⊗ n to π(z) ⊗ n and is
natural in both P and N. Its construction uses right exactness of balanced
tensor, obtained from the tensor–Hom adjunction, and imposes no flatness
hypothesis on N or on any term or differential image of P.

For independent module carrier universes v and w, the same comparison is
formed after the canonical lifts to T = max(u,v,w,t), where u is the ring
universe and t is an arbitrary additional lift height. The shape universe
remains independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex.BalancedTensor

universe t u v w κ

variable (R : Type u) [Ring R]
  {ι : Type κ} {c : ComplexShape ι}

section CommonWorld

variable (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{v} R)
  (i j : ι)

local notation "F" => (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
local notation "b" => HomologicalComplex.boundaryCyclesMap P i j

/-- For a ring R, a right R-module complex P of shape c, a left R-module N
and indices i,j, tensor the cofork image(dᵢⱼ) → cyclesⱼ(P) → homologyⱼ(P)
with N. Its projection is homologyπⱼ ⊗ 1 and its vertex is
homologyⱼ(P) ⊗ᴿ N, an abelian group. -/
def homologyTensorCofork : CokernelCofork (F.map b) :=
  (CokernelCofork.ofπ (P.homologyπ j)
    (HomologicalComplex.boundaryCyclesMap_homologyπ P i j)).map F

/-- For a ring R, a right R-module complex P, a left R-module N and
i = c.prev j, the cofork
image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N → homologyⱼ(P) ⊗ᴿ N
is a cokernel cofork in abelian groups. This follows from right exactness
of balanced tensor and requires no flatness hypothesis. -/
def homologyTensorCoforkIsColimit (hi : c.prev j = i) :
    IsColimit (homologyTensorCofork R P N i j) :=
  CokernelCofork.mapIsColimit
    (CokernelCofork.ofπ (P.homologyπ j)
      (HomologicalComplex.boundaryCyclesMap_homologyπ P i j))
    (HomologicalComplex.boundariesCyclesHomologySequence_shortExact P i j hi).gIsCokernel F

/-- For a ring R, a right R-module complex P, a left R-module N and
i = c.prev j, there is a canonical isomorphism of abelian groups
coker(image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N) ≅ homologyⱼ(P) ⊗ᴿ N.
The map being quotiented is the tensor of the boundary inclusion, and
R may be noncommutative. -/
def homologyTensorCokernelIso (hi : c.prev j = i) :
    cokernel (F.map b) ≅ F.obj (P.homology j) :=
  colimit.isoColimitCocone
    ⟨homologyTensorCofork R P N i j, homologyTensorCoforkIsColimit R P N i j hi⟩

/-- For i = c.prev j in a right R-module complex P and any left R-module N,
the cokernel projection for image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N,
followed by the homology tensor comparison, equals homologyπⱼ ⊗ 1. -/
@[reassoc]
theorem homologyTensorCokernelIso_π_hom (hi : c.prev j = i) :
    cokernel.π (F.map b) ≫ (homologyTensorCokernelIso R P N i j hi).hom =
      F.map (P.homologyπ j) :=
  colimit.isoColimitCocone_ι_hom
    ⟨homologyTensorCofork R P N i j, homologyTensorCoforkIsColimit R P N i j hi⟩
    WalkingParallelPair.one

/-- For i = c.prev j in a right R-module complex P and any left R-module N,
homologyπⱼ ⊗ 1 followed by the inverse homology tensor comparison is the
projection from cyclesⱼ(P) ⊗ᴿ N to the cokernel of the tensor boundary
inclusion. -/
@[reassoc]
theorem homologyTensorCokernelIso_homologyπ_inv (hi : c.prev j = i) :
    F.map (P.homologyπ j) ≫ (homologyTensorCokernelIso R P N i j hi).inv =
      cokernel.π (F.map b) := by
  apply (cancel_mono (homologyTensorCokernelIso R P N i j hi).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, homologyTensorCokernelIso_π_hom]

/-- For a ring R, a right R-module complex P, a left R-module N and
i = c.prev j, the homology tensor comparison sends the cokernel class
of z ⊗ n to homologyπⱼ(z) ⊗ n, for z ∈ cyclesⱼ(P) and n ∈ N. -/
theorem homologyTensorCokernelIso_mk (hi : c.prev j = i) (z : P.cycles j) (n : N) :
    (homologyTensorCokernelIso R P N i j hi).hom.hom
      ((cokernel.π (F.map b)).hom
        (ModuleCat.BalancedTensor.groupPure R (P.cycles j) N z n)) =
      ModuleCat.BalancedTensor.groupPure R (P.homology j) N ((P.homologyπ j).hom z) n := by
  have h := congrArg
    (fun f => f.hom (ModuleCat.BalancedTensor.groupPure R (P.cycles j) N z n))
    (homologyTensorCokernelIso_π_hom R P N i j hi)
  have hv : (F.map (P.homologyπ j)).hom
      (ModuleCat.BalancedTensor.groupPure R (P.cycles j) N z n) =
        ModuleCat.BalancedTensor.groupPure R (P.homology j) N ((P.homologyπ j).hom z) n :=
    ModuleCat.BalancedTensor.groupBifunctor_map_mk R (P.homologyπ j) N z n
  exact h.trans hv

end CommonWorld

section Naturality

variable {P Q : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c}
  (φ : P ⟶ Q) (N : ModuleCat.{v} R) (i j : ι)

/-- A morphism φ : P → Q of right R-module complexes of the same shape,
with fixed left coefficient N, induces a map from the cokernel of
image(dᵢⱼᴾ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N to the corresponding cokernel
for Q. It is induced by the boundary and cycle maps of φ. -/
def homologyTensorCokernelMap :
    cokernel (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
      (HomologicalComplex.boundaryCyclesMap P i j)) ⟶
    cokernel (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
      (HomologicalComplex.boundaryCyclesMap Q i j)) := by
  let F := (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let ψ := (HomologicalComplex.boundariesCyclesHomologySequenceFunctor
    (C := ModuleCat.{v} Rᵐᵒᵖ) (c := c) i j).map φ
  refine cokernel.map _ _ (F.map ψ.τ₁) (F.map (HomologicalComplex.cyclesMap φ j)) ?_
  have h : HomologicalComplex.boundaryCyclesMap P i j ≫ HomologicalComplex.cyclesMap φ j =
      ψ.τ₁ ≫ HomologicalComplex.boundaryCyclesMap Q i j := ψ.comm₁₂.symm
  simpa only [Functor.map_comp] using congrArg F.map h

/-- For a morphism φ : P → Q of right R-module complexes, a left R-module N
and i = c.prev j, the comparison for P followed by Hⱼ(φ) ⊗ 1 equals
the induced tensor boundary cokernel map followed by the comparison
for Q. -/
theorem homologyTensorCokernelIso_naturality (hi : c.prev j = i) :
    (homologyTensorCokernelIso R P N i j hi).hom ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
          (HomologicalComplex.homologyMap φ j) =
      homologyTensorCokernelMap R φ N i j ≫
        (homologyTensorCokernelIso R Q N i j hi).hom := by
  let F := (ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N
  let ψ := (HomologicalComplex.boundariesCyclesHomologySequenceFunctor
    (C := ModuleCat.{v} Rᵐᵒᵖ) (c := c) i j).map φ
  apply (cancel_epi (cokernel.π (F.map (HomologicalComplex.boundaryCyclesMap P i j)))).1
  change cokernel.π _ ≫ (homologyTensorCokernelIso R P N i j hi).hom ≫
      F.map (HomologicalComplex.homologyMap φ j) =
    cokernel.π _ ≫ cokernel.map _ _ (F.map ψ.τ₁)
      (F.map (HomologicalComplex.cyclesMap φ j)) _ ≫
        (homologyTensorCokernelIso R Q N i j hi).hom
  calc
    _ = F.map (P.homologyπ j ≫ HomologicalComplex.homologyMap φ j) := by
      rw [homologyTensorCokernelIso_π_hom_assoc, ← F.map_comp]
    _ = F.map (HomologicalComplex.cyclesMap φ j ≫ Q.homologyπ j) :=
      congrArg F.map ψ.comm₂₃.symm
    _ = _ := by
      symm
      rw [cokernel.π_desc_assoc, Category.assoc,
        homologyTensorCokernelIso_π_hom, ← F.map_comp]

end Naturality

section Coefficients

variable (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
  {N N' : ModuleCat.{v} R} (g : N ⟶ N') (i j : ι)

/-- For a right R-module complex P and a morphism g : N → N′ of left
R-modules, tensoring the boundary and cycle objects with g induces a map
between the cokernels of image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N and
image(dᵢⱼ) ⊗ᴿ N′ → cyclesⱼ(P) ⊗ᴿ N′. -/
def homologyTensorCokernelCoeffMap :
    cokernel (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
      (HomologicalComplex.boundaryCyclesMap P i j)) ⟶
    cokernel (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N').map
      (HomologicalComplex.boundaryCyclesMap P i j)) :=
  cokernel.map _ _
    (((ModuleCat.BalancedTensor.groupBifunctor R).obj (Abelian.image (P.d i j))).map g)
    (((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles j)).map g)
    (((ModuleCat.BalancedTensor.groupBifunctor R).map
      (HomologicalComplex.boundaryCyclesMap P i j)).naturality g).symm

/-- For a right R-module complex P, a morphism g : N → N′ of left
R-modules and i = c.prev j, the comparison with coefficient N followed
by 1 ⊗ g on homology equals the coefficient-induced cokernel map
followed by the comparison with coefficient N′. -/
theorem homologyTensorCokernelIso_coeff_naturality (hi : c.prev j = i) :
    (homologyTensorCokernelIso R P N i j hi).hom ≫
        (((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.homology j)).map g) =
      homologyTensorCokernelCoeffMap R P g i j ≫
        (homologyTensorCokernelIso R P N' i j hi).hom := by
  apply (cancel_epi (cokernel.π
    (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
      (HomologicalComplex.boundaryCyclesMap P i j)))).1
  change _ = cokernel.π _ ≫ cokernel.map _ _ _ _ _ ≫ _
  calc
    _ = ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map (P.homologyπ j) ≫
        (((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.homology j)).map g) :=
      homologyTensorCokernelIso_π_hom_assoc R P N i j hi _
    _ = (((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles j)).map g) ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N').map (P.homologyπ j) :=
      (((ModuleCat.BalancedTensor.groupBifunctor R).map (P.homologyπ j)).naturality g).symm
    _ = _ := by
      symm
      rw [cokernel.π_desc_assoc, Category.assoc, homologyTensorCokernelIso_π_hom]

end Coefficients

/-- Let R : Type u be a ring, P a right R-module complex with carriers in
universe v, and N a left R-module with carriers in universe w. Lift P and N
canonically to T = max(u,v,w,t), for arbitrary t. For i = c.prev j,
the cokernel of the lifted boundary tensor inclusion is canonically
isomorphic to homologyⱼ of the lifted P tensored with the lifted N.
No condition relates the shape universe to the carrier universes. -/
def homologyTensorCokernelIsoAt
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{w} R)
    (i j : ι) (hi : c.prev j = i) :
    cokernel (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj
      ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N)).map
        (HomologicalComplex.boundaryCyclesMap
          (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P) i j)) ≅
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj
        ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P).homology
          j)).obj ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) :=
  homologyTensorCokernelIso R
    (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P)
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) i j hi

/-- For a ring R and independently sized right complex P and left
coefficient N, lift both to T = max(u,v,w,t). If i = c.prev j, the
cokernel projection of the lifted tensor boundary inclusion followed
by the comparison equals the tensor of the lifted complex's homology
projection with the identity of the lifted coefficient. -/
@[reassoc]
theorem homologyTensorCokernelIsoAt_π_hom
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (N : ModuleCat.{w} R)
    (i j : ι) (hi : c.prev j = i) :
    cokernel.π (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj
      ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N)).map
        (HomologicalComplex.boundaryCyclesMap
          (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P) i j)) ≫
      (homologyTensorCokernelIsoAt.{t} R P N i j hi).hom =
    ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj
      ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N)).map
        ((((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P).homologyπ
          j) :=
  homologyTensorCokernelIso_π_hom R
    (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P)
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) i j hi

end HomologicalComplex.BalancedTensor
