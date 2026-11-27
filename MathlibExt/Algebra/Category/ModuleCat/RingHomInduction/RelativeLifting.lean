/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeLifting
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Universes
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Composition
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Scalar-split lifting from induced modules

Maps from induced modules lift through scalar-split epimorphisms. ULift transports the source and
target into the induction adjunction universe and then returns the lift to the given induced
carrier. Factorization, unit-tensor, and pure-tensor formulas describe the lift.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)

/-- The lift is an `R`-linear map from the induced carrier. -/
def liftOfRestrictedSplitEpi (M : ModuleCat.{w} k)
    {Y Z : ModuleCat.{max u v w} R} (g : Y ⟶ Z)
    (s : SplitEpi ((ModuleCat.restrictScalars.{max u v w} φ).map g))
    (f : Carrier φ M →ₗ[R] Z) : Carrier φ M →ₗ[R] Y :=
  let M' : ModuleCat.{max u v w} k := ModuleCat.of k (ULift.{max u v} M)
  let P' : ModuleCat.{max u v w} R := ModuleCat.of R (ULift.{max u v} (Carrier φ M))
  let e : (ModuleCat.induceScalars.{u, v, w} φ).obj M' ≅ P' := originalInductionLiftIso φ M
  let f' : P' ⟶ Z := ModuleCat.ofHom
    (f.comp (ULift.moduleEquiv : ULift.{max u v} (Carrier φ M) ≃ₗ[R] Carrier φ M).toLinearMap)
  let l : P' ⟶ Y :=
    e.inv ≫ (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).liftOfSplitEpi g s (e.hom ≫ f')
  l.hom.comp
    (ULift.moduleEquiv : ULift.{max u v} (Carrier φ M) ≃ₗ[R] Carrier φ M).symm.toLinearMap

/-- The lift factors the given `R`-linear map through the scalar-split morphism. -/
theorem liftOfRestrictedSplitEpi_comp (M : ModuleCat.{w} k)
    {Y Z : ModuleCat.{max u v w} R} (g : Y ⟶ Z)
    (s : SplitEpi ((ModuleCat.restrictScalars.{max u v w} φ).map g))
    (f : Carrier φ M →ₗ[R] Z) :
    g.hom.comp (liftOfRestrictedSplitEpi φ M g s f) = f := by
  let M' : ModuleCat.{max u v w} k := ModuleCat.of k (ULift.{max u v} M)
  let P' : ModuleCat.{max u v w} R := ModuleCat.of R (ULift.{max u v} (Carrier φ M))
  let e : (ModuleCat.induceScalars.{u, v, w} φ).obj M' ≅ P' := originalInductionLiftIso φ M
  let f' : P' ⟶ Z := ModuleCat.ofHom
    (f.comp (ULift.moduleEquiv : ULift.{max u v} (Carrier φ M) ≃ₗ[R] Carrier φ M).toLinearMap)
  have h :
      (e.inv ≫ (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).liftOfSplitEpi g s (e.hom ≫ f')) ≫ g =
        f' := by
    rw [Category.assoc, Adjunction.liftOfSplitEpi_comp, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  apply LinearMap.ext
  intro x
  exact congrArg (fun q : P' ⟶ Z => q (ULift.up x)) h

/-- On the unit tensor, the lift is the given scalar section applied to `f`. -/
theorem liftOfRestrictedSplitEpi_tensor_one (M : ModuleCat.{w} k)
    {Y Z : ModuleCat.{max u v w} R} (g : Y ⟶ Z)
    (s : SplitEpi ((ModuleCat.restrictScalars.{max u v w} φ).map g))
    (f : Carrier φ M →ₗ[R] Z) (m : M) :
    liftOfRestrictedSplitEpi φ M g s f (tensor φ M 1 m) =
      (show Y from s.section_ (f (tensor φ M 1 m))) := by
  let M' : ModuleCat.{max u v w} k := ModuleCat.of k (ULift.{max u v} M)
  let P' : ModuleCat.{max u v w} R := ModuleCat.of R (ULift.{max u v} (Carrier φ M))
  let e : (ModuleCat.induceScalars.{u, v, w} φ).obj M' ≅ P' := originalInductionLiftIso φ M
  let f' : P' ⟶ Z := ModuleCat.ofHom
    (f.comp (ULift.moduleEquiv : ULift.{max u v} (Carrier φ M) ≃ₗ[R] Carrier φ M).toLinearMap)
  let adj := ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ
  let l : (ModuleCat.induceScalars.{u, v, w} φ).obj M' ⟶ Y :=
    adj.liftOfSplitEpi g s (e.hom ≫ f')
  have hei : e.inv (ULift.up (tensor φ M 1 m)) = tensor φ M' 1 (ULift.up m) :=
    originalInductionLiftIso_inv_tensor φ M 1 m
  have heh : e.hom (tensor φ M' 1 (ULift.up m)) = ULift.up (tensor φ M 1 m) :=
    originalInductionLiftIso_hom_tensor φ M 1 m
  have hmate : adj.homEquiv M' Y l =
      adj.homEquiv M' Z (e.hom ≫ f') ≫ s.section_ :=
    adj.homEquiv_liftOfSplitEpi g s (e.hom ≫ f')
  have hv := congrArg
    (fun q : M' ⟶ (ModuleCat.restrictScalars.{max u v w} φ).obj Y =>
      (show Y from q (ULift.up m))) hmate
  have hl : adj.homEquiv M' Y l (ULift.up m) =
      l (tensor φ M' 1 (ULift.up m)) := nativeHomEquiv_apply φ M' Y l (ULift.up m)
  have hr :
      (show Y from (adj.homEquiv M' Z (e.hom ≫ f') ≫ s.section_) (ULift.up m)) =
        (show Y from s.section_ (f (tensor φ M 1 m))) := by
    change (show Y from s.section_ (adj.homEquiv M' Z (e.hom ≫ f') (ULift.up m))) = _
    rw [nativeHomEquiv_apply]
    change (show Y from s.section_ (f' (e.hom (tensor φ M' 1 (ULift.up m))))) = _
    rw [heh]
    rfl
  change l (e.inv (ULift.up (tensor φ M 1 m))) = _
  rw [hei]
  exact hl.symm.trans (hv.trans hr)

/-- The lift sends each pure tensor according to the outer `R`-action. -/
theorem liftOfRestrictedSplitEpi_tensor (M : ModuleCat.{w} k)
    {Y Z : ModuleCat.{max u v w} R} (g : Y ⟶ Z)
    (s : SplitEpi ((ModuleCat.restrictScalars.{max u v w} φ).map g))
    (f : Carrier φ M →ₗ[R] Z) (r : R) (m : M) :
    liftOfRestrictedSplitEpi φ M g s f (tensor φ M r m) =
      r • (show Y from s.section_ (f (tensor φ M 1 m))) := by
  let l := liftOfRestrictedSplitEpi φ M g s f
  have ht : tensor φ M r m = r • tensor φ M 1 m := by
    simpa only [mul_one] using (smul_tensor φ M r 1 m).symm
  calc
    l (tensor φ M r m) = l (r • tensor φ M 1 m) := congrArg l ht
    _ = r • l (tensor φ M 1 m) := l.map_smul r _
    _ = r • (show Y from s.section_ (f (tensor φ M 1 m))) :=
      congrArg (fun y : Y => r • y) (liftOfRestrictedSplitEpi_tensor_one φ M g s f m)

/-- Induced R-linear maps lift against every scalar-split arrow. -/
theorem postcomp_surjective_of_restricted_isSplitEpi (M : ModuleCat.{w} k)
    {Y Z : ModuleCat.{max u v w} R} (g : Y ⟶ Z)
    [IsSplitEpi ((ModuleCat.restrictScalars.{max u v w} φ).map g)] :
    Function.Surjective (fun l : Carrier φ M →ₗ[R] Y => g.hom.comp l) := by
  intro f
  obtain ⟨s⟩ := IsSplitEpi.exists_splitEpi
    (f := (ModuleCat.restrictScalars.{max u v w} φ).map g)
  exact ⟨liftOfRestrictedSplitEpi φ M g s f, liftOfRestrictedSplitEpi_comp φ M g s f⟩

/-- Linear lifting through the second map of every scalar-split short complex. -/
theorem postcomp_linear_surjective_of_splitting (M : ModuleCat.{w} k)
    (T : ShortComplex (ModuleCat.{max u v w} R))
    (s : (T.map (ModuleCat.restrictScalars.{max u v w} φ)).Splitting) :
    Function.Surjective (fun l : Carrier φ M →ₗ[R] T.X₂ => T.g.hom.comp l) := by
  let : IsSplitEpi ((ModuleCat.restrictScalars.{max u v w} φ).map T.g) := s.isSplitEpi_g
  exact postcomp_surjective_of_restricted_isSplitEpi φ M T.g

/-- In the common module-category universe, `ModuleCat.ofHom` gives the categorical lift. -/
theorem postcomp_surjective_of_splitting (M : ModuleCat.{max u v w} k)
    (T : ShortComplex (ModuleCat.{max u v w} R))
    (s : (T.map (ModuleCat.restrictScalars.{max u v w} φ)).Splitting) :
    Function.Surjective (fun l : ModuleCat.of R (Carrier φ M) ⟶ T.X₂ => l ≫ T.g) := by
  intro f
  obtain ⟨l, hl⟩ := postcomp_linear_surjective_of_splitting φ M T s f.hom
  refine ⟨ModuleCat.ofHom l, ?_⟩
  apply ModuleCat.hom_ext
  exact hl

end ModuleCat.RingHomInduction
end
