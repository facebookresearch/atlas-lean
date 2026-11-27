/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.BicomplexTotalAugmentation
public import MathlibExt.Algebra.Homology.TotalComplexMap
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Additive functors and first-column total projections

Let `F : C ⥤ D` be an additive functor between preadditive categories and let `K` be a
bicomplex indexed by two copies of `ℕ`, with differentials decreasing each index. Suppose the
total complexes of `K` and `F(K)` exist, the incoming map `K.d 1 0` has a cokernel, and the
induced chain functor preserves that cokernel.

The total-to-first-column-cokernel projection commutes with the total comparison and the
preserved-cokernel comparison. On a diagonal summand with first index zero this is the
cokernel projection; on a summand with positive first index it is zero. The category and
morphism universes of `C` and `D` are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u₁ v₁ u₂ v₂

namespace HomologicalComplex₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  [K.HasTotal (ComplexShape.down ℕ)]
  [(mapBicomplex F K).HasTotal (ComplexShape.down ℕ)]
  [HasCokernel (K.d 1 0)]
  [PreservesColimit (parallelPair (K.d 1 0) 0)
    (F.mapHomologicalComplex (ComplexShape.down ℕ))]

/-- The incoming cokernel after applying an additive chain functor.

Preservation of the cokernel of `K.d 1 0` gives a cokernel of the corresponding
incoming map in the mapped bicomplex. -/
local instance : HasCokernel ((mapBicomplex F K).d 1 0) := by
  change HasCokernel ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (K.d 1 0))
  infer_instance

/-- Naturality of the first-column cokernel projection under an additive functor.

For a first-quadrant bicomplex `K`, an additive functor `F` preserving the incoming cokernel
identifies the mapped projection `F(Tot K) → F(coker(K.d 1 0))` with `Tot(F(K)) → coker(F(K.d
1 0))` through the total and cokernel comparison isomorphisms. Both total complexes are
assumed to exist, and only this cokernel preservation is required. -/
@[reassoc]
theorem firstColumnCokernelProjection_map :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (firstColumnCokernelProjection K) ≫
      (PreservesCokernel.iso (F.mapHomologicalComplex (ComplexShape.down ℕ))
        (K.d 1 0)).hom =
    (mapTotalIsoOfHasTotal F (ComplexShape.down ℕ) K).hom ≫
      firstColumnCokernelProjection (mapBicomplex F K) := by
  apply HomologicalComplex.hom_ext
  intro n
  change F.map ((firstColumnCokernelProjection K).f n) ≫
      (PreservesCokernel.iso (F.mapHomologicalComplex (ComplexShape.down ℕ))
        (K.d 1 0)).hom.f n =
    (mapTotalXIsoOfHasTotal F (ComplexShape.down ℕ) K n).hom ≫
      (firstColumnCokernelProjection (mapBicomplex F K)).f n
  rw [← cancel_epi (mapTotalXIsoOfHasTotal F (ComplexShape.down ℕ) K n).inv,
    Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  rw [mapped_ιTotal_comp_mapTotalXIsoOfHasTotal_inv_assoc,
    ← Category.assoc, ← F.map_comp]
  cases p with
  | zero =>
      have hq : q = n := by
        change 0 + q = n at h
        simpa only [Nat.zero_add] using h
      subst q
      rw [firstColumnCokernelProjection_f, ι_firstColumnCokernelProjectionX_zero,
        firstColumnCokernelProjection_f, ι_firstColumnCokernelProjectionX_zero]
      have hπ := PreservesCokernel.π_iso_hom
        (F.mapHomologicalComplex (ComplexShape.down ℕ)) (K.d 1 0)
      have hn := congrArg
        (fun f : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.X 0) ⟶
          firstColumnCokernel (mapBicomplex F K) => f.f n) hπ
      simp only [HomologicalComplex.comp_f] at hn
      exact hn
  | succ p =>
      rw [firstColumnCokernelProjection_f, ι_firstColumnCokernelProjectionX_succ,
        F.map_zero, Limits.zero_comp, firstColumnCokernelProjection_f,
        ι_firstColumnCokernelProjectionX_succ]

end HomologicalComplex₂
