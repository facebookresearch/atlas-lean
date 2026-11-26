/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels

/-!
# Pluriharmonic Higgs integrability

The third pluriharmonic equation makes the actual O-linear exterior square
of the normalized Higgs field zero. This module proves
`pluriharmonic_higgs_integrable`: the exterior-square map vanishes on each
holomorphic frame domain by the commutator equation, hence globally by the
sheaf condition. Simpson, alg-geom/9604005v1, section 2, printed pages 9--11.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels
open scoped Manifold ContDiff

/-- On each holomorphic frame domain the exterior-square map vanishes by the
third pluriharmonic equation. -/
private theorem exteriorSquare_app_eq_zero {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ} [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]
    [MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves.SheafCondition
      (Coordinates n) M]
    [KernelSheafCondition B h A]
    [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (hh : IsPluriharmonic B h A) (H : HarmonicHiggsModel B h A)
    (S : HiggsExteriorSquare B h A H) (x : M) (V : Opens M)
    (b : V ≤ (H.frames x).domain)
    (s : (holomorphicModule B h A).val.obj (op V)) :
    (S.map.val.app (op V)).hom s = 0 := by
  have hcoords : (H.tensorFrames x 2).coordinates V b ((S.map.val.app (op V)).hom s) = 0 := by
    refine funext fun j => ?_
    change ((H.tensorFrames x 2).coordinates V b ((S.map.val.app (op V)).hom s) j) = 0
    refine Subtype.ext ?_
    change ((H.tensorFrames x 2).coordinates V b ((S.map.val.app (op V)).hom s) j).val = 0
    refine funext fun y => ?_
    change ((H.tensorFrames x 2).coordinates V b ((S.map.val.app (op V)).hom s) j).val y = 0
    refine ContinuousAlternatingMap.ext fun w => ?_
    change ((H.tensorFrames x 2).coordinates V b ((S.map.val.app (op V)).hom s) j).val y w = 0
    have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> simp
    have hform := S.formula x V b s y (w 0) (w 1) j
    rw [hw, hform]
    have hymem : y.val ∈ B.core.baseSet (H.frames x).originalFrame :=
      (H.frames x).inFrame (b y.property)
    have hcomm := (hh (H.frames x).originalFrame y.val hymem (w 0) (w 1)).2.2
    rw [hcomm, Matrix.zero_mulVec, Matrix.mulVec_zero]
    rfl
  have h0 : (H.tensorFrames x 2).coordinates V b ((S.map.val.app (op V)).hom s) =
      (H.tensorFrames x 2).coordinates V b 0 := by
    rw [hcoords, map_zero]
  exact ((H.tensorFrames x 2).coordinates V b).injective h0

/-- The third pluriharmonic equation makes that actual O-linear exterior square zero. -/
public theorem pluriharmonic_higgs_integrable {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ} [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]
    [MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves.SheafCondition
      (Coordinates n) M]
    [KernelSheafCondition B h A]
    [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (hh : IsPluriharmonic B h A) (H : HarmonicHiggsModel B h A)
    (S : HiggsExteriorSquare B h A H) : IsIntegrable B h A S := by
  change S.map = 0
  have perOpen : ∀ (U : Opens M) (s : (holomorphicModule B h A).val.obj (op U)),
      (S.map.val.app (op U)).hom s = 0 := by
    intro U s
    have hSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology M)
        ((holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).val.presheaf ⋙
          forget AddCommGrpCat) :=
      (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mp
        (holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).isSheaf
    have hsep : Presieve.IsSeparatedFor
        ((holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).val.presheaf ⋙
          forget AddCommGrpCat)
        (Presieve.ofArrows (fun (y : U) => (U ⊓ (H.frames y.val).domain : Opens M))
          (fun y => homOfLE inf_le_left)) := by
      rw [Presieve.isSeparatedFor_iff_generate]
      refine Presieve.IsSheafFor.isSeparatedFor ?_
      refine hSheaf.isSheafFor _ ?_
      rw [Opens.mem_grothendieckTopology]
      intro x hx
      exact ⟨U ⊓ (H.frames x).domain, homOfLE inf_le_left,
        Sieve.ofArrows_mk _ _ (⟨x, hx⟩ : U), hx, (H.frames x).contains⟩
    refine Presieve.IsSeparatedFor.ext hsep
      (t₁ := (S.map.val.app (op U)).hom s)
      (t₂ := (0 : (holomorphicTensor (holomorphicModule B h A)
        (holomorphicOmega 2)).val.obj (op U))) ?_
    intro Y f hf
    obtain ⟨i⟩ := hf
    set g : (U ⊓ (H.frames i.val).domain : Opens M) ⟶ U := homOfLE inf_le_left with hg
    change ConcreteCategory.hom
        ((holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).val.map g.op)
        ((S.map.val.app (op U)).hom s) =
      ConcreteCategory.hom
        ((holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).val.map g.op)
        (0 : (holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).val.obj (op U))
    have hloc : ConcreteCategory.hom (S.map.val.app (op (U ⊓ (H.frames i.val).domain)))
        (ConcreteCategory.hom ((holomorphicModule B h A).val.map g.op) s) = 0 :=
      exteriorSquare_app_eq_zero B h A hh H S i.val (U ⊓ (H.frames i.val).domain)
        inf_le_right _
    have hnat := PresheafOfModules.naturality_apply S.map.val g.op s
    calc ConcreteCategory.hom
            ((holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).val.map g.op)
            ((S.map.val.app (op U)).hom s)
          = ConcreteCategory.hom (S.map.val.app (op (U ⊓ (H.frames i.val).domain)))
              (ConcreteCategory.hom ((holomorphicModule B h A).val.map g.op) s) :=
            hnat.symm
        _ = 0 := hloc
        _ = ConcreteCategory.hom
              ((holomorphicTensor (holomorphicModule B h A) (holomorphicOmega 2)).val.map g.op)
              (0 : (holomorphicTensor (holomorphicModule B h A)
                (holomorphicOmega 2)).val.obj (op U)) :=
            (map_zero ((holomorphicTensor (holomorphicModule B h A)
              (holomorphicOmega 2)).val.map g.op).hom).symm
  have hval : S.map.val = 0 := by
    refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext ?_
    refine LinearMap.ext fun s => ?_
    rw [PresheafOfModules.zero_app]
    change (S.map.val.app V).hom s = 0
    revert s
    rw [← op_unop V]
    exact perOpen V.unop
  exact SheafOfModules.hom_ext hval
