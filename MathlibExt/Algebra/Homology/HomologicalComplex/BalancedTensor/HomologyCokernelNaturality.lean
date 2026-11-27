/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.Algebra.Homology.HomologicalComplex.BalancedTensor.HomologyCokernel

/-!
# Morphisms of tensor boundary cokernels

Let R be a ring, P a complex of right R-modules of shape c, and N a left
R-module. The cokernel of image(dᵢⱼ) ⊗ᴿ N → cyclesⱼ(P) ⊗ᴿ N is
homologyⱼ(P) ⊗ᴿ N when i = c.prev j. A coefficient map sends the class
of z ⊗ n to the class of z ⊗ g(n).

For a right-complex map φ : P → Q and a coefficient map g : N → N′,
the homology tensor comparison commutes with both maps simultaneously.
The comparison also commutes with its inverse: the coefficient-induced
cokernel map is the tensor coefficient map conjugated by the comparisons.

The right complexes may have carriers in universe v and the coefficients
in universe w, independently of the ring universe u and the shape
universe κ. The maps use the canonical lifts to max(u,v,w,t), for any
additional height t. No coefficient flatness condition is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex.BalancedTensor

universe t u v w κ

variable (R : Type u) [Ring R] {ι : Type κ} {c : ComplexShape ι}

section CommonWorld

variable (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
  {N N' : ModuleCat.{v} R} (g : N ⟶ N') (i j : ι)

/-- For a right R-module complex P and a coefficient map g : N → N′,
the cokernel projection followed by the induced coefficient map equals
1 ⊗ g on cycles followed by the target cokernel projection. -/
@[reassoc]
theorem homologyTensorCokernelCoeffMap_π :
    cokernel.π (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
        (HomologicalComplex.boundaryCyclesMap P i j)) ≫
      homologyTensorCokernelCoeffMap R P g i j =
    (((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles j)).map g) ≫
      cokernel.π (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N').map
        (HomologicalComplex.boundaryCyclesMap P i j)) :=
  cokernel.π_desc _ _ _

/-- For a coefficient map g : N → N′, the induced tensor boundary
cokernel map sends the class of z ⊗ n to the class of z ⊗ g(n), where
z belongs to cyclesⱼ(P). This description holds for all indices i,j. -/
theorem homologyTensorCokernelCoeffMap_mk (z : P.cycles j) (n : N) :
    (homologyTensorCokernelCoeffMap R P g i j).hom
      ((cokernel.π (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N).map
        (HomologicalComplex.boundaryCyclesMap P i j))).hom
          (ModuleCat.BalancedTensor.groupPure R (P.cycles j) N z n)) =
    (cokernel.π (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N').map
      (HomologicalComplex.boundaryCyclesMap P i j))).hom
        (ModuleCat.BalancedTensor.groupPure R (P.cycles j) N' z (g.hom n)) := by
  have h := ConcreteCategory.congr_hom
    (homologyTensorCokernelCoeffMap_π R P g i j)
    (ModuleCat.BalancedTensor.groupPure R (P.cycles j) N z n)
  have hg :
      (((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.cycles j)).map g).hom
        (ModuleCat.BalancedTensor.groupPure R (P.cycles j) N z n) =
      ModuleCat.BalancedTensor.groupPure R (P.cycles j) N' z (g.hom n) :=
    ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk R (P.cycles j) g z n
  exact h.trans (congrArg
    (cokernel.π (((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj N').map
      (HomologicalComplex.boundaryCyclesMap P i j))).hom hg)

end CommonWorld

section IndependentWorlds

variable {P Q : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c}
  {N N' : ModuleCat.{w} R}

/-- For a right-complex map φ : P → Q in carrier universe v and a
coefficient N in carrier universe w, lift both inputs to max(u,v,w,t).
The boundary and cycle maps of the lifted φ induce a map between the
lifted tensor boundary cokernels. -/
def homologyTensorCokernelMapAt (φ : P ⟶ Q) (N : ModuleCat.{w} R) (i j : ι) :=
  homologyTensorCokernelMap R
    (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).map φ)
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) i j

/-- For a right complex P in carrier universe v and a coefficient map
g : N → N′ in carrier universe w, lift P,N,N′ to max(u,v,w,t).
Tensoring the lifted boundary and cycle objects with the lifted g induces
a map between their tensor boundary cokernels. -/
def homologyTensorCokernelCoeffMapAt
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (g : N ⟶ N') (i j : ι) :=
  homologyTensorCokernelCoeffMap R
    (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P)
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).map g) i j

/-- For a right complex P in universe v, a coefficient map g : N → N′
in universe w, and i = c.prev j, the lifted homology tensor comparison
commutes with the coefficient-induced cokernel map. All objects and
maps use the canonical lifts to max(u,v,w,t). -/
@[reassoc]
theorem homologyTensorCokernelIsoAt_coeff_naturality
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (g : N ⟶ N')
    (i j : ι) (hi : c.prev j = i) :
    let U := (ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c
    let L := ModuleCat.uliftFunctor.{max u v w t, w} R
    (homologyTensorCokernelIsoAt.{t} R P N i j hi).hom ≫
        (((ModuleCat.BalancedTensor.groupBifunctor R).obj ((U.obj P).homology j)).map
          (L.map g)) =
      homologyTensorCokernelCoeffMapAt.{t} R P g i j ≫
        (homologyTensorCokernelIsoAt.{t} R P N' i j hi).hom := by
  dsimp only
  exact homologyTensorCokernelIso_coeff_naturality R
    (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).obj P)
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).map g) i j hi

/-- For a right-complex map φ : P → Q in universe v, a coefficient N
in universe w, and i = c.prev j, the lifted homology tensor comparison
commutes with the boundary/cycle-induced cokernel map. Its homology map
is that of the canonically lifted φ in max(u,v,w,t). -/
@[reassoc]
theorem homologyTensorCokernelIsoAt_naturality
    (φ : P ⟶ Q) (N : ModuleCat.{w} R) (i j : ι) (hi : c.prev j = i) :
    let U := (ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c
    let L := ModuleCat.uliftFunctor.{max u v w t, w} R
    (homologyTensorCokernelIsoAt.{t} R P N i j hi).hom ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj (L.obj N)).map
          (HomologicalComplex.homologyMap (U.map φ) j) =
      homologyTensorCokernelMapAt.{t} R φ N i j ≫
        (homologyTensorCokernelIsoAt.{t} R Q N i j hi).hom := by
  dsimp only
  exact homologyTensorCokernelIso_naturality R
    (((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c).map φ)
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj N) i j hi

/-- For a right-complex map φ : P → Q and a coefficient map g : N → N′,
the lifted homology tensor comparison commutes with applying Hⱼ(φ)
and g together. The induced cokernel map first applies the lifted
boundary/cycle map of φ, then the lifted coefficient map of g.
The carrier universes v,w and the shape universe remain independent. -/
@[reassoc]
theorem homologyTensorCokernelIsoAt_bivariate_naturality
    (φ : P ⟶ Q) (g : N ⟶ N') (i j : ι) (hi : c.prev j = i) :
    let U := (ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c
    let L := ModuleCat.uliftFunctor.{max u v w t, w} R
    (homologyTensorCokernelIsoAt.{t} R P N i j hi).hom ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj (L.obj N)).map
          (HomologicalComplex.homologyMap (U.map φ) j) ≫
        (((ModuleCat.BalancedTensor.groupBifunctor R).obj ((U.obj Q).homology j)).map
          (L.map g)) =
      homologyTensorCokernelMapAt.{t} R φ N i j ≫
        homologyTensorCokernelCoeffMapAt.{t} R Q g i j ≫
          (homologyTensorCokernelIsoAt.{t} R Q N' i j hi).hom := by
  dsimp only
  let U := (ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c
  let L := ModuleCat.uliftFunctor.{max u v w t, w} R
  have hφ := homologyTensorCokernelIsoAt_naturality.{t} R φ N i j hi
  have hg := homologyTensorCokernelIsoAt_coeff_naturality.{t} R Q g i j hi
  calc
    _ = (homologyTensorCokernelMapAt.{t} R φ N i j ≫
        (homologyTensorCokernelIsoAt.{t} R Q N i j hi).hom) ≫
        (((ModuleCat.BalancedTensor.groupBifunctor R).obj ((U.obj Q).homology j)).map
          (L.map g)) := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫
          (((ModuleCat.BalancedTensor.groupBifunctor R).obj ((U.obj Q).homology j)).map
            (L.map g))) hφ
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => homologyTensorCokernelMapAt.{t} R φ N i j ≫ f) hg

/-- For i = c.prev j, a coefficient-induced map between lifted tensor
boundary cokernels is the tensor coefficient map on homology conjugated
by the canonical comparisons. This identifies the actual cokernel map
with the transport of 1 ⊗ g, at the fixed common height max(u,v,w,t). -/
theorem homologyTensorCokernelCoeffMapAt_eq_conjugate
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (g : N ⟶ N')
    (i j : ι) (hi : c.prev j = i) :
    let U := (ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).mapHomologicalComplex c
    let L := ModuleCat.uliftFunctor.{max u v w t, w} R
    homologyTensorCokernelCoeffMapAt.{t} R P g i j =
      (homologyTensorCokernelIsoAt.{t} R P N i j hi).hom ≫
        (((ModuleCat.BalancedTensor.groupBifunctor R).obj ((U.obj P).homology j)).map
          (L.map g)) ≫
        (homologyTensorCokernelIsoAt.{t} R P N' i j hi).inv := by
  dsimp only
  apply (cancel_mono (homologyTensorCokernelIsoAt.{t} R P N' i j hi).hom).1
  have h := homologyTensorCokernelIsoAt_coeff_naturality.{t} R P g i j hi
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm

end IndependentWorlds

end HomologicalComplex.BalancedTensor
