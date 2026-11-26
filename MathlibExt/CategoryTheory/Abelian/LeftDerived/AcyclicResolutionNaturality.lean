/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolution
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology


/-!
# Naturality of left-derived acyclic-resolution comparisons

For an additive right-exact functor between abelian categories with
projective resolutions in the source, a map of exact augmented
termwise acyclic complexes gives a naturality square between their
`L_nF` comparisons. In degree one, the square passes through the
kernel of the mapped augmentation-kernel inclusion. Higher degrees
pass through kernel-tail augmentations and restriction homology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v₁ u₁ v₂ u₂
open CategoryTheory CategoryTheory.Limits

local instance : ChainComplex.kernelTailEmbedding.IsRelIff :=
  ComplexShape.instIsRelIffEmbeddingDown'Add 1 1

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentationHomologyZero_naturality
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M N : C} {Q R : ChainComplex C ℕ}
    (π : Q ⟶ (ChainComplex.single₀ C).obj M) (ρ : R ⟶ (ChainComplex.single₀ C).obj N)
    [QuasiIso π] [QuasiIso ρ] (f : M ⟶ N) (a : Q ⟶ R)
    (h : a ≫ ρ = π ≫ (ChainComplex.single₀ C).map f) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) 0 ≫
        (ChainComplex.homologyZeroIsoOfPreservedAugmentation F ρ).hom =
      (ChainComplex.homologyZeroIsoOfPreservedAugmentation F π).hom ≫ F.map f := by
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R
  let b := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map a
  let eK := ChainComplex.homologyZeroIsoOfPreservedAugmentation F π
  let eL := ChainComplex.homologyZeroIsoOfPreservedAugmentation F ρ
  let qK := K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv
  have heK : qK ≫ eK.hom = F.map (π.f 0) :=
    (Category.assoc _ _ _).trans
      (ChainComplex.pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom F π)
  have heL : L.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ L).inv ≫ eL.hom = F.map (ρ.f 0) :=
    ChainComplex.pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom F ρ
  have hc : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f := by
    have h0 := congrArg (fun t => t.f 0) h
    change a.f 0 ≫ ρ.f 0 = π.f 0 ≫ ((ChainComplex.single₀ C).map f).f 0 at h0
    exact h0.trans (congrArg (fun g : M ⟶ N => π.f 0 ≫ g) (ChainComplex.single₀_map_f_zero f))
  have hb : qK ≫ HomologicalComplex.homologyMap b 0 =
      b.f 0 ≫ L.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ L).inv := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => K.pOpcycles 0 ≫ m) (ChainComplex.isoHomologyι₀_inv_naturality b)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ (ChainComplex.isoHomologyι₀ L).inv)
            (HomologicalComplex.p_opcyclesMap b 0)).trans
            (Category.assoc _ _ _))))
  have haug : b.f 0 ≫ F.map (ρ.f 0) = F.map (π.f 0) ≫ F.map f :=
    (F.map_comp (a.f 0) (ρ.f 0)).symm.trans
      ((congrArg F.map hc).trans (F.map_comp (π.f 0) f))
  have hend : F.map (π.f 0) ≫ F.map f = qK ≫ (eK.hom ≫ F.map f) :=
    (congrArg (fun m => m ≫ F.map f) heK.symm).trans (Category.assoc _ _ _)
  have hmid : (b.f 0 ≫ L.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ L).inv) ≫ eL.hom =
      b.f 0 ≫ F.map (ρ.f 0) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => b.f 0 ≫ m)
        (Category.assoc (L.pOpcycles 0) (ChainComplex.isoHomologyι₀ L).inv eL.hom)).trans
          (congrArg (fun m => b.f 0 ≫ m) heL))
  apply (cancel_epi qK).1
  exact ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ eL.hom) hb)).trans
    (hmid.trans (haug.trans hend))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive and preserving finite colimits. Let
`π : Q → M[0]`, `ρ : R → N[0]` be quasi-isomorphisms of nonnegative
chain complexes with all positive left-derived term values zero. For `a : Q → R` over `f : M → N`, the degree-zero
comparisons satisfy `L₀F(f) ≫ comparison_R = comparison_Q ≫ H₀(F(a))`. -/
theorem leftDerivedObjIsoHomologyOfAcyclicResolution_zero_naturality
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M N : C} {Q R : ChainComplex C ℕ}
    (π : Q ⟶ (ChainComplex.single₀ C).obj M)
    (ρ : R ⟶ (ChainComplex.single₀ C).obj N) [QuasiIso π] [QuasiIso ρ]
    (hQ : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (Q.X q)))
    (hR : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (R.X q)))
    (f : M ⟶ N) (a : Q ⟶ R)
    (h : a ≫ ρ = π ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived 0).map f ≫
        (F.leftDerivedObjIsoHomologyOfAcyclicResolution R ρ hR 0).hom =
      (F.leftDerivedObjIsoHomologyOfAcyclicResolution Q π hQ 0).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) 0 := by
  rw [leftDerivedObjIsoHomologyOfAcyclicResolution,
    leftDerivedObjIsoHomologyOfAcyclicResolution]
  change (F.leftDerived 0).map f ≫
      ((F.leftDerivedZeroIsoSelf.app N).hom ≫
        (ChainComplex.homologyZeroIsoOfPreservedAugmentation F ρ).inv) =
    ((F.leftDerivedZeroIsoSelf.app M).hom ≫
        (ChainComplex.homologyZeroIsoOfPreservedAugmentation F π).inv) ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) 0
  apply (cancel_mono (ChainComplex.homologyZeroIsoOfPreservedAugmentation F ρ).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    augmentationHomologyZero_naturality F π ρ f a h, Iso.inv_hom_id_assoc]
  exact F.leftDerivedZeroIsoSelf.hom.naturality f



set_option backward.isDefEq.respectTransparency.types false in
/-- In an abelian category `C`, let `π : Q → M[0]`, `ρ : R → N[0]`
be chain augmentations and `a : Q → R`, `f : M → N` satisfy
`a₀ ≫ ρ₀ = π₀ ≫ f`. Restricting `a` to the kernel tails commutes
with their augmentations over the induced map `ker(π₀) → ker(ρ₀)`. -/
theorem acyclicAugmentationKernelTailMap_comm
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {M N : C} {Q R : ChainComplex C ℕ}
    (π : Q ⟶ (ChainComplex.single₀ C).obj M) (ρ : R ⟶ (ChainComplex.single₀ C).obj N)
    (f : M ⟶ N) (a : Q ⟶ R)
    (h : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    HomologicalComplex.restrictionMap a ChainComplex.kernelTailEmbedding ≫
        ChainComplex.kernelTailAugmentation ρ =
      ChainComplex.kernelTailAugmentation π ≫
        (ChainComplex.single₀ C).map (ChainComplex.augmentationKernelMap π ρ a f h) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero]
      change (HomologicalComplex.restrictionMap a ChainComplex.kernelTailEmbedding).f 0 ≫
          (ChainComplex.kernelTailAugmentation ρ).f 0 =
        (ChainComplex.kernelTailAugmentation π).f 0 ≫ ChainComplex.augmentationKernelMap π ρ a f h
      apply (cancel_mono (kernel.ι (ρ.f 0))).1
      rw [ChainComplex.kernelTailAugmentation_f_zero, ChainComplex.kernelTailAugmentation_f_zero]
      change (a.f 1 ≫ kernel.lift (ρ.f 0) (R.d 1 0) _) ≫ kernel.ι (ρ.f 0) =
        (kernel.lift (π.f 0) (Q.d 1 0) _ ≫
          ChainComplex.augmentationKernelMap π ρ a f h) ≫ kernel.ι (ρ.f 0)
      have hk : ChainComplex.augmentationKernelMap π ρ a f h ≫ kernel.ι (ρ.f 0) =
          kernel.ι (π.f 0) ≫ a.f 0 := kernel.lift_ι _ _ _
      rw [Category.assoc, kernel.lift_ι, Category.assoc, hk, kernel.lift_ι_assoc]
      exact a.comm 1 0
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        (CategoryTheory.Limits.kernel (ρ.f 0)) (n + 1) (by omega)).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and
`π : Q → M[0]` a quasi-isomorphism whose terms have vanishing
positive left-derived values. The degree-`n+2` acyclic comparison
factors through the kernel-sequence boundary, the degree-`n+1`
comparison for the kernel tail, and its restriction homology isomorphism. -/
theorem leftDerivedAcyclicComparison_higher_hom
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M : C} (Q : ChainComplex C ℕ) (π : Q ⟶ (ChainComplex.single₀ C).obj M)
    [QuasiIso π]
    (hQ : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (Q.X q))) (n : ℕ) :
    letI : Epi (π.f 0) := ChainComplex.epi_augmentation_f_zero π
    let S : ShortComplex.ShortExactSequences C :=
      ⟨ShortComplex.kernelSequence (π.f 0), ShortComplex.kernelSequence_shortExact (π.f 0)⟩
    let Q' : ChainComplex C ℕ := Q.restriction ChainComplex.kernelTailEmbedding
    let π' := ChainComplex.kernelTailAugmentation π
    letI : QuasiIso π' := ChainComplex.quasiIso_kernelTailAugmentation π
    let hQ' : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (Q'.X q)) := by
      intro q i
      exact IsZero.of_iso (hQ (q + 1) i)
        ((F.leftDerived (i + 1)).mapIso
          (Q.restrictionXIso ChainComplex.kernelTailEmbedding
            (ChainComplex.kernelTailEmbedding_f q)).symm)
    let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
    let eδ := F.leftDerivedDeltaFunctor.connectingIsoOfIsZeroMiddle (n + 1) S
      (by exact hQ 0 n) (by exact hQ 0 (n + 1))
    let eH := K.restrictionHomologyIso ChainComplex.kernelTailEmbedding
      (n + 2) (n + 1) n
      (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
      (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
      (i' := n + 3) (j' := n + 2) (k' := n + 1) rfl rfl rfl
      (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
      (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution Q π hQ (n + 2)).hom =
      eδ.hom ≫ (F.leftDerivedObjIsoHomologyOfAcyclicResolution Q' π' hQ' (n + 1)).hom ≫
        eH.hom := by
  rw [leftDerivedObjIsoHomologyOfAcyclicResolution]
  dsimp only [Nat.casesAuxOn, Iso.trans_hom]
  rfl

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and
`φ : S → T` a map of short exact sequences whose middle objects
have zero `L₁F`. The isomorphisms
`L₁F(S.X₃) ≅ ker(F(S.f))`, `L₁F(T.X₃) ≅ ker(F(T.f))`
commute with `L₁F(φ₃)` and the induced kernel map. -/
lemma leftDerivedOneIsoKernel_naturality
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (S T : ShortComplex.ShortExactSequences C) (φ : S.obj ⟶ T.obj)
    (hS : IsZero ((F.leftDerived 1).obj S.obj.X₂))
    (hT : IsZero ((F.leftDerived 1).obj T.obj.X₂)) :
    (F.leftDerived 1).map φ.τ₃ ≫ (F.leftDerivedOneIsoKernel T hT).hom =
      (F.leftDerivedOneIsoKernel S hS).hom ≫
        kernel.map (F.map S.obj.f) (F.map T.obj.f) (F.map φ.τ₁) (F.map φ.τ₂)
          (by rw [← F.map_comp, ← F.map_comp, φ.comm₁₂]) := by
  apply (cancel_mono (kernel.ι (F.map T.obj.f))).1
  have hk :
      kernel.map (F.map S.obj.f) (F.map T.obj.f) (F.map φ.τ₁) (F.map φ.τ₂)
        (by rw [← F.map_comp, ← F.map_comp, φ.comm₁₂]) ≫
          kernel.ι (F.map T.obj.f) =
        kernel.ι (F.map S.obj.f) ≫ F.map φ.τ₁ := by
    exact kernel.lift_ι _ _ _
  rw [Category.assoc, leftDerivedOneIsoKernel_hom_ι,
    Category.assoc, hk, leftDerivedOneIsoKernel_hom_ι_assoc]
  rw [← Category.assoc, LeftDerivedDelta.LDdelta_natural F 0 T.obj S.obj φ
    T.property S.property, Category.assoc, F.leftDerivedZeroIsoSelf.hom.naturality]

end CategoryTheory.Functor

namespace ChainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {Q R : ChainComplex C ℕ} {M N : C}

/-- Let `C,D` be abelian and `F : C → D` any functor. For chain
augmentations `π : Q → M[0]`, `ρ : R → N[0]` and maps `a : Q → R`,
`f : M → N` with `a₀ ≫ ρ₀ = π₀ ≫ f`, the mapped kernel-inclusion
square induces a map `ker(F(ker(π₀) → Q₀)) → ker(F(ker(ρ₀) → R₀))`. -/
noncomputable def augmentationMappedKernelMap
    (F : C ⥤ D)
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    kernel (F.map (kernel.ι (π.f 0))) ⟶ kernel (F.map (kernel.ι (ρ.f 0))) :=
  kernel.map (F.map (kernel.ι (π.f 0))) (F.map (kernel.ι (ρ.f 0)))
    (F.map (augmentationKernelMap π ρ a f h₀)) (F.map (a.f 0))
    (by rw [← F.map_comp, ← F.map_comp, augmentationKernelMap_ι])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]`, `ρ : R → N[0]` chain augmentations that are
quasi-isomorphisms in degrees zero and one. Suppose `F` preserves
the cokernels of `Q₂ → Q₁` and `R₂ → R₁`. For a chain map
`a : Q → R` and `f : M → N`, assume `a₀ ≫ ρ₀ = π₀ ≫ f`. The chain-map and augmentation squares induce right-homology
map data in degree one, using the kernel-tail homology presentations
of `F(Q)` and `F(R)`. -/
noncomputable def augmentationRightHomologyMapData
    (F : C ⥤ D) [F.Additive]
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1] [QuasiIsoAt ρ 0] [QuasiIsoAt ρ 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F]
    [PreservesColimit (parallelPair (R.d 2 1) 0) F]
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    ShortComplex.RightHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ) 2 1 0).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a))
      (augmentationRightHomologyData F π) (augmentationRightHomologyData F ρ) where
  φQ := F.map (augmentationKernelMap π ρ a f h₀)
  φH := augmentationMappedKernelMap F π ρ a f h₀
  commp := by
    change F.map (kernel.lift (π.f 0) (Q.d 1 0) _) ≫
        F.map (augmentationKernelMap π ρ a f h₀) =
      F.map (a.f 1) ≫ F.map (kernel.lift (ρ.f 0) (R.d 1 0) _)
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (kernelLift_augmentationKernelMap π ρ a f h₀)
  commg' := by
    have hk : F.map (augmentationKernelMap π ρ a f h₀) ≫ F.map (kernel.ι (ρ.f 0)) =
        F.map (kernel.ι (π.f 0)) ≫ F.map (a.f 0) := by
      rw [← F.map_comp, augmentationKernelMap_ι, F.map_comp]
    change @Eq (F.obj (kernel (π.f 0)) ⟶ F.obj (R.X 0))
      (F.map (augmentationKernelMap π ρ a f h₀) ≫
        (augmentationRightHomologyData F ρ).g')
      ((augmentationRightHomologyData F π).g' ≫ F.map (a.f 0))
    rw [augmentationRightHomologyData_g' F ρ, augmentationRightHomologyData_g' F π]
    exact hk
  commι := by
    exact kernel.lift_ι _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `C,D` be abelian, `F : C → D` additive, and
`π : Q → M[0]`, `ρ : R → N[0]` chain augmentations that are
quasi-isomorphisms in degrees zero and one. Suppose `F` preserves
the cokernels of `Q₂ → Q₁` and `R₂ → R₁`. For a chain map
`a : Q → R` and `f : M → N`, assume `a₀ ≫ ρ₀ = π₀ ≫ f`. The degree-one homology map `H₁(F(a))` commutes with the
isomorphisms to `ker(F(ker(π₀) → Q₀))` and
`ker(F(ker(ρ₀) → R₀))`, and the induced map between these kernels. -/
lemma homologyOneIsoOfPreservedKernelTail_naturality
    (F : C ⥤ D) [F.Additive]
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1] [QuasiIsoAt ρ 0] [QuasiIsoAt ρ 1]
    [PreservesColimit (parallelPair (Q.d 2 1) 0) F]
    [PreservesColimit (parallelPair (R.d 2 1) 0) F]
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) 1 ≫
      (homologyOneIsoOfPreservedKernelTail F ρ).hom =
    (homologyOneIsoOfPreservedKernelTail F π).hom ≫
      augmentationMappedKernelMap F π ρ a f h₀ := by
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R
  let b := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map a
  let φ := (HomologicalComplex.shortComplexFunctor' D (ComplexShape.down ℕ) 2 1 0).map b
  let γ := augmentationRightHomologyMapData F π ρ a f h₀
  have hsc : HomologicalComplex.homologyMap b 1 ≫
        (L.homologyIsoSc' 2 1 0 (by simp) (by simp)).hom =
      (K.homologyIsoSc' 2 1 0 (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap φ := by
    change
      ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor D (ComplexShape.down ℕ) 1).map b) ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.natIsoSc' D (ComplexShape.down ℕ) 2 1 0
            (by simp) (by simp)).hom.app L) =
      ShortComplex.homologyMap
          ((HomologicalComplex.natIsoSc' D (ComplexShape.down ℕ) 2 1 0
            (by simp) (by simp)).hom.app K) ≫
        ShortComplex.homologyMap φ
    exact ShortComplex.homologyMap_square
      ((HomologicalComplex.natIsoSc' D (ComplexShape.down ℕ) 2 1 0
        (by simp) (by simp)).hom.naturality b)
  rw [homologyOneIsoOfPreservedKernelTail_eq, homologyOneIsoOfPreservedKernelTail_eq]
  change HomologicalComplex.homologyMap b 1 ≫
      ((L.homologyIsoSc' 2 1 0 (by simp) (by simp)).hom ≫
        (augmentationRightHomologyData F ρ).homologyIso.hom) =
    ((K.homologyIsoSc' 2 1 0 (by simp) (by simp)).hom ≫
        (augmentationRightHomologyData F π).homologyIso.hom) ≫ γ.φH
  rw [← Category.assoc, hsc, Category.assoc, γ.homologyMap_comm]
  simp only [Category.assoc]

end ChainComplex

namespace ChainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {Q R : ChainComplex C ℕ} {M N : C}

/-- In an abelian category `C`, let `π : Q → M[0]`, `ρ : R → N[0]`
be chain augmentations and `a : Q → R`, `f : M → N` satisfy
`a₀ ≫ ρ₀ = π₀ ≫ f`. Their kernel maps, `a₀`, and `f` give a
morphism from `ker(π₀) → Q₀ → M` to `ker(ρ₀) → R₀ → N`. -/
noncomputable def augmentationKernelSequenceMap
    (π : Q ⟶ (single₀ C).obj M) (ρ : R ⟶ (single₀ C).obj N)
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    ShortComplex.kernelSequence (π.f 0) ⟶ ShortComplex.kernelSequence (ρ.f 0) where
  τ₁ := augmentationKernelMap π ρ a f h₀
  τ₂ := a.f 0
  τ₃ := f
  comm₁₂ := augmentationKernelMap_ι π ρ a f h₀
  comm₂₃ := h₀

end ChainComplex

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and
`π : Q → M[0]` a quasi-isomorphism with all positive left-derived
term values zero. The degree-one acyclic comparison factors through
the boundary isomorphism `L₁F(M) ≅ ker(F(ker(π₀) → Q₀))` and
the inverse kernel-tail homology comparison to `H₁(F(Q))`. -/
lemma leftDerivedAcyclicComparison_one_hom
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M : C} (Q : ChainComplex C ℕ) (π : Q ⟶ (ChainComplex.single₀ C).obj M)
    [QuasiIso π]
    (hQ : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (Q.X q))) :
    letI : Epi (π.f 0) := ChainComplex.epi_augmentation_f_zero π
    let S : ShortComplex.ShortExactSequences C :=
      ⟨ShortComplex.kernelSequence (π.f 0),
        ShortComplex.kernelSequence_shortExact (π.f 0)⟩
    (leftDerivedObjIsoHomologyOfAcyclicResolution F Q π hQ 1).hom =
      (F.leftDerivedOneIsoKernel S (by exact hQ 0 0)).hom ≫
        (ChainComplex.homologyOneIsoOfPreservedKernelTail F π).inv := by
  rw [leftDerivedObjIsoHomologyOfAcyclicResolution]
  dsimp only [Nat.casesAuxOn]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in

/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive and preserving finite colimits. Let
`π : Q → M[0]`, `ρ : R → N[0]` be quasi-isomorphisms of nonnegative
chain complexes with all positive left-derived term values zero. For `a : Q → R`, `f : M → N` with
`a₀ ≫ ρ₀ = π₀ ≫ f`, the degree-one acyclic comparisons satisfy
`L₁F(f) ≫ comparison_R = comparison_Q ≫ H₁(F(a))`. -/
lemma leftDerivedAcyclicComparison_one_naturality_of_f_zero
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M N : C} (Q R : ChainComplex C ℕ)
    (π : Q ⟶ (ChainComplex.single₀ C).obj M)
    (ρ : R ⟶ (ChainComplex.single₀ C).obj N) [QuasiIso π] [QuasiIso ρ]
    (hQ : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (Q.X q)))
    (hR : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (R.X q)))
    (a : Q ⟶ R) (f : M ⟶ N)
    (h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f) :
    (F.leftDerived 1).map f ≫
      (leftDerivedObjIsoHomologyOfAcyclicResolution F R ρ hR 1).hom =
    (leftDerivedObjIsoHomologyOfAcyclicResolution F Q π hQ 1).hom ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) 1 := by
  have : Epi (π.f 0) := ChainComplex.epi_augmentation_f_zero π
  have : Epi (ρ.f 0) := ChainComplex.epi_augmentation_f_zero ρ
  let S : ShortComplex.ShortExactSequences C :=
    ⟨ShortComplex.kernelSequence (π.f 0),
      ShortComplex.kernelSequence_shortExact (π.f 0)⟩
  let T : ShortComplex.ShortExactSequences C :=
    ⟨ShortComplex.kernelSequence (ρ.f 0),
      ShortComplex.kernelSequence_shortExact (ρ.f 0)⟩
  let eS : (F.leftDerived 1).obj M ≅ CategoryTheory.Limits.kernel
      (F.map (kernel.ι (π.f 0))) := F.leftDerivedOneIsoKernel S (hQ 0 0)
  let eT : (F.leftDerived 1).obj N ≅ CategoryTheory.Limits.kernel
      (F.map (kernel.ι (ρ.f 0))) := F.leftDerivedOneIsoKernel T (hR 0 0)
  let φ := ChainComplex.augmentationKernelSequenceMap π ρ a f h₀
  have hS : IsZero ((F.leftDerived 1).obj S.obj.X₂) := hQ 0 0
  have hT : IsZero ((F.leftDerived 1).obj T.obj.X₂) := hR 0 0
  have hb : (F.leftDerived 1).map f ≫ eT.hom =
      eS.hom ≫
        ChainComplex.augmentationMappedKernelMap F π ρ a f h₀ :=
    F.leftDerivedOneIsoKernel_naturality S T φ hS hT
  have hh := ChainComplex.homologyOneIsoOfPreservedKernelTail_naturality
    F π ρ a f h₀
  apply (cancel_mono (ChainComplex.homologyOneIsoOfPreservedKernelTail F ρ).hom).1
  rw [leftDerivedAcyclicComparison_one_hom, leftDerivedAcyclicComparison_one_hom]
  change ((F.leftDerived 1).map f ≫
      (eT.hom ≫
        (ChainComplex.homologyOneIsoOfPreservedKernelTail F ρ).inv)) ≫
      (ChainComplex.homologyOneIsoOfPreservedKernelTail F ρ).hom =
    ((eS.hom ≫
        (ChainComplex.homologyOneIsoOfPreservedKernelTail F π).inv) ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) 1) ≫
      (ChainComplex.homologyOneIsoOfPreservedKernelTail F ρ).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hh, Iso.inv_hom_id_assoc]
  exact hb

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive and preserving finite colimits. Let
`π : Q → M[0]`, `ρ : R → N[0]` be quasi-isomorphisms of nonnegative
chain complexes with all positive left-derived term values zero. For a map of augmented complexes `a : Q → R` over
`f : M → N`, the degree-one acyclic comparisons satisfy
`L₁F(f) ≫ comparison_R = comparison_Q ≫ H₁(F(a))`. -/
lemma leftDerivedAcyclicComparison_one_naturality
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M N : C} (Q R : ChainComplex C ℕ)
    (π : Q ⟶ (ChainComplex.single₀ C).obj M)
    (ρ : R ⟶ (ChainComplex.single₀ C).obj N) [QuasiIso π] [QuasiIso ρ]
    (hQ : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (Q.X q)))
    (hR : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (R.X q)))
    (a : Q ⟶ R) (f : M ⟶ N)
    (h : a ≫ ρ = π ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived 1).map f ≫
      (leftDerivedObjIsoHomologyOfAcyclicResolution F R ρ hR 1).hom =
    (leftDerivedObjIsoHomologyOfAcyclicResolution F Q π hQ 1).hom ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) 1 := by
  apply leftDerivedAcyclicComparison_one_naturality_of_f_zero F Q R π ρ hQ hR a f
  have h₀ := congrArg (fun b => b.f 0) h
  dsimp only [HomologicalComplex.comp_f] at h₀
  rw [ChainComplex.single₀_map_f_zero] at h₀
  exact h₀


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `C,D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive and preserving finite colimits. Let
`π : Q → M[0]`, `ρ : R → N[0]` be quasi-isomorphisms of nonnegative
chain complexes with all positive left-derived term values zero. For a map of augmented complexes `a : Q → R` over
`f : M → N`, the comparisons satisfy
`L_nF(f) ≫ comparison_R = comparison_Q ≫ H_n(F(a))` in every degree. -/
theorem leftDerivedObjIsoHomologyOfAcyclicResolution_naturality
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M N : C} (Q R : ChainComplex C ℕ)
    (π : Q ⟶ (ChainComplex.single₀ C).obj M)
    (ρ : R ⟶ (ChainComplex.single₀ C).obj N) [QuasiIso π] [QuasiIso ρ]
    (hQ : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (Q.X q)))
    (hR : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (R.X q)))
    (f : M ⟶ N) (a : Q ⟶ R)
    (h : a ≫ ρ = π ≫ (ChainComplex.single₀ C).map f) (n : ℕ) :
    (F.leftDerived n).map f ≫
        (F.leftDerivedObjIsoHomologyOfAcyclicResolution R ρ hR n).hom =
      (F.leftDerivedObjIsoHomologyOfAcyclicResolution Q π hQ n).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) n := by
  induction n using Nat.strong_induction_on generalizing M N Q R with
  | ind n ih =>
      cases n with
      | zero =>
          exact leftDerivedObjIsoHomologyOfAcyclicResolution_zero_naturality
            F π ρ hQ hR f a h
      | succ n =>
          cases n with
          | zero =>
              exact leftDerivedAcyclicComparison_one_naturality F Q R π ρ hQ hR a f h
          | succ n =>
              have h₀ : a.f 0 ≫ ρ.f 0 = π.f 0 ≫ f := by
                have hzero := congrArg (fun b => b.f 0) h
                simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at hzero
                exact hzero
              have : Epi (π.f 0) := ChainComplex.epi_augmentation_f_zero π
              have : Epi (ρ.f 0) := ChainComplex.epi_augmentation_f_zero ρ
              let S : ShortComplex.ShortExactSequences C :=
                ⟨ShortComplex.kernelSequence (π.f 0), ShortComplex.kernelSequence_shortExact (π.f 0)⟩
              let T : ShortComplex.ShortExactSequences C :=
                ⟨ShortComplex.kernelSequence (ρ.f 0), ShortComplex.kernelSequence_shortExact (ρ.f 0)⟩
              let Q' := Q.restriction ChainComplex.kernelTailEmbedding
              let R' := R.restriction ChainComplex.kernelTailEmbedding
              let π' := ChainComplex.kernelTailAugmentation π
              let ρ' := ChainComplex.kernelTailAugmentation ρ
              let : QuasiIso π' := ChainComplex.quasiIso_kernelTailAugmentation π
              let : QuasiIso ρ' := ChainComplex.quasiIso_kernelTailAugmentation ρ
              let f' := ChainComplex.augmentationKernelMap π ρ a f h₀
              let a' := HomologicalComplex.restrictionMap a ChainComplex.kernelTailEmbedding
              have h' : a' ≫ ρ' = π' ≫ (ChainComplex.single₀ C).map f' :=
                acyclicAugmentationKernelTailMap_comm π ρ f a h₀
              have hQ' : ∀ q j : ℕ, IsZero ((F.leftDerived (j + 1)).obj (Q'.X q)) := by
                intro q j
                exact IsZero.of_iso (hQ (q + 1) j)
                  ((F.leftDerived (j + 1)).mapIso
                    (Q.restrictionXIso ChainComplex.kernelTailEmbedding
                      (ChainComplex.kernelTailEmbedding_f q)).symm)
              have hR' : ∀ q j : ℕ, IsZero ((F.leftDerived (j + 1)).obj (R'.X q)) := by
                intro q j
                exact IsZero.of_iso (hR (q + 1) j)
                  ((F.leftDerived (j + 1)).mapIso
                    (R.restrictionXIso ChainComplex.kernelTailEmbedding
                      (ChainComplex.kernelTailEmbedding_f q)).symm)
              have hind := ih (n + 1) (by omega) Q' R' π' ρ' hQ' hR' f' a' h'
              let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
              let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R
              let b := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map a
              let eδQ := F.leftDerivedDeltaFunctor.connectingIsoOfIsZeroMiddle (n + 1) S
                (by exact hQ 0 n) (by exact hQ 0 (n + 1))
              let eδR := F.leftDerivedDeltaFunctor.connectingIsoOfIsZeroMiddle (n + 1) T
                (by exact hR 0 n) (by exact hR 0 (n + 1))
              let eHQ := K.restrictionHomologyIso ChainComplex.kernelTailEmbedding
                (n + 2) (n + 1) n
                (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
                (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
                (i' := n + 3) (j' := n + 2) (k' := n + 1) rfl rfl rfl
                (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
                (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
              let eHR := L.restrictionHomologyIso ChainComplex.kernelTailEmbedding
                (n + 2) (n + 1) n
                (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
                (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
                (i' := n + 3) (j' := n + 2) (k' := n + 1) rfl rfl rfl
                (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
                (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
              let φ : S ⟶ T := ObjectProperty.homMk
                (ChainComplex.augmentationKernelSequenceMap π ρ a f h₀)
              have hδ : (F.leftDerived (n + 2)).map f ≫ eδR.hom =
                  eδQ.hom ≫ (F.leftDerived (n + 1)).map f' := by
                rw [HomologicalDeltaFunctor.connectingIsoOfIsZeroMiddle_hom,
                  HomologicalDeltaFunctor.connectingIsoOfIsZeroMiddle_hom]
                exact (F.leftDerivedDeltaFunctor.connecting (n + 1)).naturality φ
              have hH : HomologicalComplex.homologyMap
                    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a') (n + 1) ≫ eHR.hom =
                  eHQ.hom ≫ HomologicalComplex.homologyMap b (n + 2) := by
                exact HomologicalComplex.restrictionHomologyIso_naturality b
                  ChainComplex.kernelTailEmbedding (n + 2) (n + 1) n
                  (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
                  (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
                  (i' := n + 3) (j' := n + 2) (k' := n + 1) rfl rfl rfl
                  (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
                  (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
              rw [leftDerivedAcyclicComparison_higher_hom,
                leftDerivedAcyclicComparison_higher_hom]
              change (F.leftDerived (n + 2)).map f ≫
                    (eδR.hom ≫
                      (F.leftDerivedObjIsoHomologyOfAcyclicResolution R' ρ' hR' (n + 1)).hom ≫
                        eHR.hom) =
                  (eδQ.hom ≫
                      (F.leftDerivedObjIsoHomologyOfAcyclicResolution Q' π' hQ' (n + 1)).hom ≫
                        eHQ.hom) ≫ HomologicalComplex.homologyMap b (n + 2)
              let eQ : (F.leftDerived (n + 1)).obj (CategoryTheory.Limits.kernel (π.f 0)) ≅
                  ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q').homology (n + 1) :=
                F.leftDerivedObjIsoHomologyOfAcyclicResolution Q' π' hQ' (n + 1)
              let eR : (F.leftDerived (n + 1)).obj (CategoryTheory.Limits.kernel (ρ.f 0)) ≅
                  ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R').homology (n + 1) :=
                F.leftDerivedObjIsoHomologyOfAcyclicResolution R' ρ' hR' (n + 1)
              let b' := HomologicalComplex.homologyMap
                ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a') (n + 1)
              change (F.leftDerived (n + 2)).map f ≫ (eδR.hom ≫ eR.hom ≫ eHR.hom) =
                (eδQ.hom ≫ eQ.hom ≫ eHQ.hom) ≫ HomologicalComplex.homologyMap b (n + 2)
              calc
                (F.leftDerived (n + 2)).map f ≫ (eδR.hom ≫ eR.hom ≫ eHR.hom) =
                    ((F.leftDerived (n + 2)).map f ≫ eδR.hom) ≫ (eR.hom ≫ eHR.hom) :=
                  (Category.assoc _ _ _).symm
                _ = (eδQ.hom ≫ (F.leftDerived (n + 1)).map f') ≫ (eR.hom ≫ eHR.hom) :=
                  congrArg (fun t => t ≫ (eR.hom ≫ eHR.hom)) hδ
                _ = eδQ.hom ≫ (((F.leftDerived (n + 1)).map f' ≫ eR.hom) ≫ eHR.hom) := by
                  simp only [Category.assoc]
                _ = eδQ.hom ≫ ((eQ.hom ≫ b') ≫ eHR.hom) :=
                  congrArg (fun t => eδQ.hom ≫ (t ≫ eHR.hom)) hind
                _ = (eδQ.hom ≫ eQ.hom) ≫ (b' ≫ eHR.hom) := by
                  simp only [Category.assoc]
                _ = (eδQ.hom ≫ eQ.hom) ≫ (eHQ.hom ≫ HomologicalComplex.homologyMap b (n + 2)) :=
                  congrArg (fun t => (eδQ.hom ≫ eQ.hom) ≫ t) hH
                _ = (eδQ.hom ≫ eQ.hom ≫ eHQ.hom) ≫
                    HomologicalComplex.homologyMap b (n + 2) := by
                  simp only [Category.assoc]

end CategoryTheory.Functor
