/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.lean`
and
`P2M/Sol/S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.Algebraize
public import MathlibExt.Algebra.TensorProduct.Domain

/-!
# Geometrically integral schemes over an algebraically closed field

An integral, locally finite-type scheme over an algebraically closed field
is geometrically integral: every base change to a field extension stays
integral. The key algebraic input is that the tensor product of a domain
of finite type with a field over an algebraically closed field is a domain.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace GeometricallyIntegralAux

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The base change of an integral affine scheme of finite type over an
algebraically closed field to any field extension is integral. -/
private theorem isIntegral_pullback_SpecMap_of_isAlgClosed {A : CommRingCat.{u}}
    (φ : CommRingCat.of K ⟶ A) [IsIntegral (Spec A)] [LocallyOfFiniteType (Spec.map φ)]
    (K' : Type u) [Field K'] [Algebra K K'] :
    IsIntegral ↑(pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap K K')))) := by
  algebraize [φ.hom]
  have hft : Algebra.FiniteType K A := by
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp ‹_›
    exact RingHom.finiteType_algebraMap.mp this
  have : IsDomain A := (affine_isIntegral_iff A).mp ‹_›
  have : IsDomain (A ⊗[K] K') := Algebra.TensorProduct.isDomain_of_isAlgClosed_of_finiteType A K'
  let e : pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ≅
      Spec (.of (A ⊗[K] K')) :=
    pullbackSpecIso K A K'
  exact IsIntegral.of_isIso e.inv

end GeometricallyIntegralAux

namespace AlgebraicGeometry

/-- An integral, locally finite-type scheme over an algebraically closed field
is geometrically integral. -/
theorem geometricallyIntegral_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by
  refine ⟨(geometrically_iff_of_commRing (P := fun Y : Scheme.{u} => IsIntegral Y)).mpr ?_⟩
  intro K' _ _ Y fst snd h
  let i : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  suffices hP : IsIntegral ↑(pullback f i) by
    haveI := hP
    exact IsIntegral.of_isIso h.isoPullback.inv
  let 𝒰 := X.affineCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 f i
  have hint : ∀ j, Nonempty (𝒰.X j) → IsIntegral (𝒱.X j) := by
    intro j hj
    have hI : IsIntegral (𝒰.X j) := isIntegral_of_isOpenImmersion (𝒰.f j)
    have hlft : LocallyOfFiniteType (𝒰.f j ≫ f) := inferInstance
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒰.f j ≫ f)
    have hP := @GeometricallyIntegralAux.isIntegral_pullback_SpecMap_of_isAlgClosed K _ _ _ φ hI
      (hφ ▸ hlft) K' _ _
    let e : pullback (Spec.map φ) i ≅ pullback (𝒰.f j ≫ f) i := pullback.congrHom hφ rfl
    exact @IsIntegral.of_isIso _ _ hP e.hom (Iso.isIso_hom e)
  have hred : ∀ j, IsReduced (𝒱.X j) := by
    intro j
    rcases isEmpty_or_nonempty (𝒰.X j) with hj | hj
    · haveI : IsEmpty ↑(pullback (𝒰.f j ≫ f) i) :=
        Function.isEmpty (pullback.fst (𝒰.f j ≫ f) i)
      haveI : IsReduced (𝒰.X j) := isReduced_of_isOpenImmersion (𝒰.f j)
      change IsReduced (pullback (𝒰.f j ≫ f) i)
      exact isReduced_of_isOpenImmersion (pullback.fst (𝒰.f j ≫ f) i)
    · haveI := hint j hj
      infer_instance
  haveI : IsReduced ↑(pullback f i) := IsReduced.of_openCover _ 𝒱
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  haveI hj₀ : Nonempty (𝒰.X (𝒰.idx x₀)) := let ⟨y, _⟩ := 𝒰.covers x₀; ⟨y⟩
  haveI := hint _ hj₀
  have hrange : Set.range (𝒱.f (𝒰.idx x₀)) =
      pullback.fst f i ⁻¹' Set.range (𝒰.f (𝒰.idx x₀)) := by
    have hid : Set.range (𝟙 (Spec (.of K')) : Spec (.of K') ⟶ _) = Set.univ :=
      Set.range_eq_univ.mpr fun y => ⟨y, rfl⟩
    have := Scheme.Pullback.range_map (𝒰.f (𝒰.idx x₀) ≫ f) i f i (𝒰.f (𝒰.idx x₀)) (𝟙 _)
      (𝟙 _) (by simp) (by simp)
    rw [hid, Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hopen : IsOpenMap (pullback.fst f i) := (pullback.fst f i).isOpenMap
  have hdense : Dense (Set.range (𝒱.f (𝒰.idx x₀))) := by
    rw [hrange, dense_iff_inter_open]
    intro W hW hWne
    obtain ⟨_, ⟨w, hw, rfl⟩, hw'⟩ := nonempty_preirreducible_inter (hopen W hW)
      (𝒰.f (𝒰.idx x₀)).isOpenEmbedding.isOpen_range (hWne.image _) (Set.range_nonempty _)
    exact ⟨w, hw, hw'⟩
  have hirr : IsIrreducible (Set.range (𝒱.f (𝒰.idx x₀))) := by
    have := (IrreducibleSpace.isIrreducible_univ (X := 𝒱.X (𝒰.idx x₀))).image _
      (𝒱.f (𝒰.idx x₀)).continuous.continuousOn
    rwa [Set.image_univ] at this
  haveI : IrreducibleSpace ↑(pullback f i) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense.closure_eq]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry
