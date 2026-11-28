/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplexAugmentation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Mapped augmentation homology in degrees zero and one

Let `C,D` be abelian, `F : C → D` additive, and `π : Q → M[0]`
a chain augmentation. If `π` is a quasi-isomorphism in degree zero
and `F` preserves the cokernel of `Q₁ → Q₀`, then `H₀(F(Q)) ≅ F(M)`.
If `π` is a quasi-isomorphism in degrees zero and one and `F`
preserves the cokernel of `Q₂ → Q₁`, then
`H₁(F(Q)) ≅ ker(F(ker(π₀) → Q₀))`. Each preservation condition
concerns the displayed individual cokernel. Augmentation squares
induce the corresponding kernel maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ChainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {Q : ChainComplex C ℕ} {M : C}

/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]` a nonnegative chain augmentation that is a
quasi-isomorphism in degree zero. Suppose `F` preserves the
cokernel of `d_Q : Q₁ → Q₀`. The preserved augmentation gives the canonical isomorphism
`H₀(F(Q)) ≅ F(M)`. -/
noncomputable def homologyZeroIsoOfPreservedAugmentation
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 0]
    [PreservesColimit (parallelPair (Q.d 1 0) 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology 0 ≅ F.obj M := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let c : CokernelCofork (Q.d 1 0) :=
    CokernelCofork.ofπ (π.f 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])
  have : Epi (π.f 0) := epi_augmentation_f_zero π
  let hc : IsColimit c := (exact_augmentation π).gIsCokernel
  exact K.isoHomologyι₀ ≪≫ K.opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    ((K.sc' 1 0 0).isoOpcyclesOfIsColimit
      (CokernelCofork.mapIsColimit c hc F)).symm

/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]` a nonnegative chain augmentation that is a
quasi-isomorphism in degree zero. Suppose `F` preserves the
cokernel of `d_Q : Q₁ → Q₀`. The quotient `F(Q₀) → opcycles₀(F(Q))`, followed by its
identification with `H₀(F(Q))` and the augmentation isomorphism,
is the mapped augmentation `F(π₀)`. -/
@[reassoc]
lemma pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M) [QuasiIsoAt π 0]
    [PreservesColimit (parallelPair (Q.d 1 0) 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q)).inv ≫
      (homologyZeroIsoOfPreservedAugmentation F π).hom = F.map (π.f 0) := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let c : CokernelCofork (Q.d 1 0) :=
    CokernelCofork.ofπ (π.f 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])
  have : Epi (π.f 0) := epi_augmentation_f_zero π
  let hc : IsColimit c := (exact_augmentation π).gIsCokernel
  let e : (c.map F).pt ≅ (K.sc' 1 0 0).opcycles :=
    (K.sc' 1 0 0).isoOpcyclesOfIsColimit (CokernelCofork.mapIsColimit c hc F)
  change K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫
    (K.isoHomologyι₀.hom ≫ (K.opcyclesIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
      e.inv) = F.map (π.f 0)
  simp only [Iso.inv_hom_id_assoc,
    HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  exact (K.sc' 1 0 0).pOpcycles_π_isoOpcyclesOfIsColimit_inv
    (CokernelCofork.mapIsColimit c hc F)

variable {R : ChainComplex C ℕ} {N : C}

/-- In an abelian category `C`, let `π : Q → M[0]`, `ρ : R → N[0]`
be nonnegative chain augmentations and `a : Q → R`, `f : M → N`
satisfy `a₀ ≫ ρ₀ = π₀ ≫ f`. The degree-zero square induces a map
`ker(π₀) → ker(ρ₀)`. -/
noncomputable def augmentationKernelMap
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    kernel (π.f 0) ⟶ kernel (ρ.f 0) :=
  kernel.map (π.f 0) (ρ.f 0) (a.f 0) f h₀.symm

/-- In an abelian category `C`, let `π : Q → M[0]`, `ρ : R → N[0]`
be nonnegative chain augmentations and `a : Q → R`, `f : M → N`
satisfy `a₀ ≫ ρ₀ = π₀ ≫ f`. The induced kernel map followed by `ker(ρ₀) → R₀`
equals `ker(π₀) → Q₀` followed by `a₀`. -/
@[reassoc]
lemma augmentationKernelMap_ι
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    augmentationKernelMap π ρ a f h₀ ≫ kernel.ι (ρ.f 0) =
      kernel.ι (π.f 0) ≫ a.f 0 :=
  kernel.lift_ι _ _ _

/-- In an abelian category `C`, let `π : Q → M[0]`, `ρ : R → N[0]`
be nonnegative chain augmentations and `a : Q → R`, `f : M → N`
satisfy `a₀ ≫ ρ₀ = π₀ ≫ f`. Lifting the first differential `Q₁ → Q₀` through
`ker(π₀)` and then mapping kernels equals `a₁` followed by the
kernel lift of `R₁ → R₀`. -/
lemma kernelLift_augmentationKernelMap
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    kernel.lift (π.f 0) (Q.d 1 0)
        (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]) ≫
      augmentationKernelMap π ρ a f h₀ =
    a.f 1 ≫ kernel.lift (ρ.f 0) (R.d 1 0)
        (by rw [← ρ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]) := by
  apply (cancel_mono (kernel.ι (ρ.f 0))).1
  rw [Category.assoc, augmentationKernelMap_ι, kernel.lift_ι_assoc,
    Category.assoc, kernel.lift_ι]
  exact (a.comm 1 0).symm

/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]` a nonnegative chain augmentation that is a
quasi-isomorphism in degrees zero and one. Suppose `F` preserves
the cokernel of `d_Q : Q₂ → Q₁`. Put `K=ker(π₀)` and write
`κ : K → Q₀` for its inclusion. Right-homology data for `F(Q₂) → F(Q₁) → F(Q₀)` identifies
the quotient of `F(Q₁)` by incoming boundaries with `F(K)`, with
outgoing map `F(κ)`. -/
noncomputable def augmentationRightHomologyData
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).sc' 2 1 0).RightHomologyData := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
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
  exact
    { Q := F.obj (kernel (π.f 0))
      H := kernel (F.map k)
      p := F.map q
      ι := kernel.ι (F.map k)
      wp := (c.map F).condition
      hp := hp
      wι := by
        rw [hd]
        exact kernel.condition _
      hι := KernelFork.IsLimit.ofι' _ _ (fun g hg =>
        ⟨kernel.lift (F.map k) g (by simpa only [← hd] using hg),
          kernel.lift_ι _ _ _⟩) }

/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]` a nonnegative chain augmentation that is a
quasi-isomorphism in degrees zero and one. Suppose `F` preserves
the cokernel of `d_Q : Q₂ → Q₁`. Put `K=ker(π₀)` and write
`κ : K → Q₀` for its inclusion. The outgoing map from the quotient object `F(K)` in the
augmentation right-homology presentation is precisely `F(κ)`. -/
lemma augmentationRightHomologyData_g'
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    (augmentationRightHomologyData F π).g' = F.map (kernel.ι (π.f 0)) := by
  apply (cancel_epi (augmentationRightHomologyData F π).p).1
  rw [ShortComplex.RightHomologyData.p_g']
  change F.map (Q.d 1 0) =
    F.map (kernel.lift (π.f 0) (Q.d 1 0) _) ≫ F.map (kernel.ι (π.f 0))
  rw [← F.map_comp, kernel.lift_ι]


/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]` a nonnegative chain augmentation that is a
quasi-isomorphism in degrees zero and one. Suppose `F` preserves
the cokernel of `d_Q : Q₂ → Q₁`. Put `K=ker(π₀)` and write
`κ : K → Q₀` for its inclusion. The quotient and its outgoing map give the canonical
isomorphism `H₁(F(Q)) ≅ ker(F(κ))`. -/
noncomputable def homologyOneIsoOfPreservedKernelTail
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology 1 ≅
      kernel (F.map (kernel.ι (π.f 0))) :=
  ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homologyIsoSc'
    2 1 0 (by simp) (by simp) ≪≫ (augmentationRightHomologyData F π).homologyIso

/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]` a nonnegative chain augmentation that is a
quasi-isomorphism in degrees zero and one. Suppose `F` preserves
the cokernel of `d_Q : Q₂ → Q₁`. Put `K=ker(π₀)` and write
`κ : K → Q₀` for its inclusion. The degree-one kernel isomorphism is the identification
with homology of the short complex in degrees `2 → 1 → 0`,
followed by its augmentation right-homology isomorphism. -/
lemma homologyOneIsoOfPreservedKernelTail_eq
    (F : C ⥤ D) [F.Additive] (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F] :
    homologyOneIsoOfPreservedKernelTail F π =
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homologyIsoSc'
        2 1 0 (by simp) (by simp) ≪≫
          (augmentationRightHomologyData F π).homologyIso := rfl


end ChainComplex
