/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.ChainComplexAugmentationHomology

/-!
# Cycle formula for the degree-one augmentation kernel comparison

For an additive functor between abelian categories, an augmentation
quasi-isomorphism in degrees zero and one, and preservation of the
cokernel of `Q₂ → Q₁`, the comparison
`H₁(F(Q)) ≅ ker(F(ker(π₀) → Q₀))` sends a cycle class to the mapped
lift of `Q₁ → Q₀` through the original augmentation kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace ChainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {Q : ChainComplex C ℕ} {M : C}

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]` a nonnegative chain augmentation that is a
quasi-isomorphism in degrees zero and one. Suppose `F` preserves
the cokernel of `d_Q : Q₂ → Q₁`. Put `K=ker(π₀)` and write
`κ : K → Q₀` for its inclusion. Let `ν : Q₁ → K` be the kernel lift of `d_Q : Q₁ → Q₀`.
The cycle quotient followed by `H₁(F(Q)) ≅ ker(F(κ))` and its
kernel inclusion into `F(K)` equals the cycle inclusion into
`F(Q₁)` followed by `F(ν)`. -/
theorem homologyπ_homologyOneIsoOfPreservedKernelTail_hom_ι
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homologyπ 1 ≫
      (homologyOneIsoOfPreservedKernelTail F π).hom ≫ kernel.ι (F.map (kernel.ι (π.f 0))) =
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).iCycles 1 ≫
      F.map (kernel.lift (π.f 0) (Q.d 1 0)
        (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])) := by
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let q : Q.X 1 ⟶ kernel (π.f 0) :=
    kernel.lift (π.f 0) (Q.d 1 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])
  let k : kernel (π.f 0) ⟶ Q.X 0 := kernel.ι (π.f 0)
  have hqk : q ≫ k = Q.d 1 0 := kernel.lift_ι _ _ _
  let S : ShortComplex C := ShortComplex.mk (Q.d 2 1) q (by
    rw [← cancel_mono k, Category.assoc, hqk, Q.d_comp_d, zero_comp])
  have hS : S.Exact := exact_kernelLift_augmentation π
  have : Epi q := epi_kernelLift_augmentation π
  let c : CokernelCofork (Q.d 2 1) := CokernelCofork.ofπ q S.zero
  let hc : IsColimit c := hS.gIsCokernel
  let hp : IsColimit (c.map F) := CokernelCofork.mapIsColimit c hc F
  let T : ShortComplex D := K.sc' 2 1 0
  have hd : hp.desc (CokernelCofork.ofπ T.g T.zero) = F.map k := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc]
    change F.map (Q.d 1 0) = F.map q ≫ F.map k
    rw [← F.map_comp, hqk]
  let h : T.RightHomologyData :=
    { Q := F.obj (kernel (π.f 0))
      H := kernel (F.map k)
      p := F.map q
      ι := kernel.ι (F.map k)
      wp := (c.map F).condition
      hp := hp
      wι := by rw [hd]; exact kernel.condition _
      hι := KernelFork.IsLimit.ofι' _ _ (fun g hg =>
        ⟨kernel.lift (F.map k) g (by simpa only [← hd] using hg),
          kernel.lift_ι _ _ _⟩) }
  change K.homologyπ 1 ≫
    ((K.homologyIsoSc' 2 1 0 (by simp) (by simp)).hom ≫ h.homologyIso.hom) ≫ h.ι =
      K.iCycles 1 ≫ F.map q
  simp only [Category.assoc, h.homologyIso_hom_comp_ι]
  rw [← Category.assoc, K.π_homologyIsoSc'_hom]
  simp only [Category.assoc]
  change (K.cyclesIsoSc' 2 1 0 (by simp) (by simp)).hom ≫ T.homologyπ ≫
    T.homologyι ≫ h.opcyclesIso.hom = K.iCycles 1 ≫ F.map q
  rw [T.homology_π_ι_assoc, h.pOpcycles_comp_opcyclesIso_hom]
  change (K.cyclesIsoSc' 2 1 0 (by simp) (by simp)).hom ≫ (K.sc' 2 1 0).iCycles ≫
    F.map q = K.iCycles 1 ≫ F.map q
  rw [← Category.assoc, K.cyclesIsoSc'_hom_iCycles]

end ChainComplex
