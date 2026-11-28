/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Derived completeness through actual localizations

For an ideal `I` of `A`, a complex `K` is derived complete if
`RHom_A(A[1/f], K)` vanishes for every `f ∈ I`. Here this is stated using
the actual localization module and all its shifts in Mathlib's derived
category. No completion predicate or derived-Hom carrier is supplied.

This is Stacks Project, Tag 091S, via the localization criterion of
Tag 091N. AxiomMath/Stacks, revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, provides the equivalent
Milnor-map definition in `StacksFrontier/Homology/DerivedComplete.lean`
(Apache 2.0). This original adapter uses the localization criterion to
avoid assuming countable products in the derived category.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.DerivedAdicCompleteness

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- The actual `A`-module underlying the localization at `f`. -/
abbrev localizedModule (f : A) : ModuleCat.{u + 1} A :=
  ModuleCat.of A (ULift.{u + 1} (Localization.Away f))

/-- The ring in degree zero of its actual module derived category. -/
abbrev ringObject : DerivedCategory (ModuleCat.{u + 1} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    (ModuleCat.of A (ULift.{u + 1} A))

/-- The actual localization module in degree zero. -/
abbrev localizationObject (f : A) :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    (localizedModule A f)

/-- The localization unit induced by the actual algebra map. -/
def localizationUnit (f : A) : ringObject A ⟶ localizationObject A f :=
  (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).map
    (ModuleCat.ofHom
      { toFun x := ULift.up (algebraMap A (Localization.Away f) x.down)
        map_add' _ _ := ULift.ext (map_add _ _ _)
        map_smul' _ _ := ULift.ext (Algebra.linearMap A
          (Localization.Away f) |>.map_smul _ _) })

/-- Vanishing of the actual localization-derived-Hom in every degree. -/
def IsCompleteAt (K : DerivedCategory (ModuleCat.{u + 1} A)) (f : A) :
    Prop :=
  ∀ (n : ℤ) (g : (localizationObject A f)⟦n⟧ ⟶ K), g = 0

/-- Derived `I`-completeness, characterized by actual localized modules. -/
def IsComplete (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u + 1} A)) : Prop :=
  ∀ f ∈ I, IsCompleteAt A K f

/-- Derived completeness of an actual ring as a degree-zero complex. -/
abbrev IsCompleteRing (I : Ideal A) : Prop :=
  IsComplete A I (ringObject A)

/-- The same condition can be read as singleton derived-Hom groups. -/
theorem isCompleteAt_iff_subsingleton
    (K : DerivedCategory (ModuleCat.{u + 1} A)) (f : A) :
    IsCompleteAt A K f ↔
      ∀ n : ℤ, Subsingleton ((localizationObject A f)⟦n⟧ ⟶ K) := by
  constructor
  · intro h n
    exact ⟨fun g j ↦ (h n g).trans (h n j).symm⟩
  · intro h n g
    exact (h n).elim g 0

/-- Completeness restricts along inclusion of ideals. -/
theorem IsComplete.mono {I J : Ideal A}
    {K : DerivedCategory (ModuleCat.{u + 1} A)}
    (h : IsComplete A J K) (hIJ : I ≤ J) : IsComplete A I K :=
  fun f hf ↦ h f (hIJ hf)

/-- An isomorphism of the actual complex preserves completeness. -/
theorem IsComplete.iso {I : Ideal A}
    {K L : DerivedCategory (ModuleCat.{u + 1} A)}
    (h : IsComplete A I K) (e : K ≅ L) : IsComplete A I L := by
  intro f hf n g
  have hg := h f hf n (g ≫ e.inv)
  rw [← cancel_mono e.inv, hg, zero_comp]

end MathlibExt.RingTheory.DerivedAdicCompleteness
