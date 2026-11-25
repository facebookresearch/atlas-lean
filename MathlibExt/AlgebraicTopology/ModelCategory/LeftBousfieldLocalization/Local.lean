/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AccessibleMorphismProperty
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFunctionComplex

/-!
# Derived local objects and local equivalences

For a small family of arrows, locality is defined using the chosen derived simplicial mapping
object. The resulting local equivalences contain base weak equivalences and satisfy the formal
closure properties. For an empty family, the explicit detector in
`HomotopyFunctionComplexData` recovers exactly the base weak equivalences.

Accessibility is kept in a separate optional packet. Nothing in this file installs a localized
model structure or a global accessibility instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- An object is derived-local for `S` when every arrow of `S` induces a realization weak
equivalence by precomposition on the chosen derived mapping object. -/
def isDerivedLocal {I : Type w} (S : I → Arrow C) (Z : C) : Prop :=
  ∀ i, SSet.realizationWeakEquivalences
    (derivedMappingPrecomp (C := C) (S i).hom Z)

/-- A local-fibrant object is both fibrant in the base model structure and derived-local. -/
def isLocalFibrant {I : Type w} (S : I → Arrow C) (Z : C) : Prop :=
  IsFibrant Z ∧ isDerivedLocal S Z

/-- The derived `S`-local equivalences, detected by precomposition into all local-fibrant
targets. -/
def localEquivalences {I : Type w} (S : I → Arrow C) : MorphismProperty C :=
  fun _ _ f ↦ ∀ Z, isLocalFibrant S Z →
    SSet.realizationWeakEquivalences (derivedMappingPrecomp (C := C) f Z)

/-- Optional accessibility input for derived locality.

The first two fields concern the fixed-variable derived mapping functors. The last field is the
reviewed accessibility notion for the full subcategory of local-equivalence arrows and its
inclusion. These certificates are not consequences of homotopical invariance. -/
structure DerivedLocalityAccessibilityData {I : Type w} (S : I → Arrow C) : Prop where
  /-- Accessibility of the derived mapping functor with a fixed source. -/
  fixedSourceAccessible (X : C) :
    Functor.IsAccessible.{w} ((derivedMappingObject (C := C)).obj (.op X))
  /-- Accessibility of the contravariant derived mapping functor with a fixed target. -/
  fixedTargetAccessible (Z : C) :
    Functor.IsAccessible.{w}
      (derivedMappingObject (C := C) ⋙ (evaluation C SSet.{v}).obj Z)
  /-- Accessibility of the full arrow subcategory of local equivalences and its inclusion. -/
  localEquivalencesAccessible :
    MorphismProperty.IsAccessible.{w} (localEquivalences S)

/-- Derived local equivalences contain identities. This is returned explicitly rather than
installed as a global instance. -/
theorem localEquivalences_containsIdentities {I : Type w} (S : I → Arrow C) :
    (localEquivalences S).ContainsIdentities where
  id_mem X Z _ := by
    rw [derivedMappingPrecomp_id]
    exact SSet.realizationWeakEquivalences.id_mem _

/-- Derived local equivalences satisfy all three directions of two-out-of-three. The source
composition order is reversed by precomposition. -/
theorem localEquivalences_hasTwoOutOfThreeProperty {I : Type w}
    (S : I → Arrow C) :
    (localEquivalences S).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg Z hZ := by
    rw [derivedMappingPrecomp_comp]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ (hg Z hZ) (hf Z hZ)
  of_postcomp f g hg hfg Z hZ := by
    apply SSet.realizationWeakEquivalences.of_precomp
      (derivedMappingPrecomp (C := C) g Z)
      (derivedMappingPrecomp (C := C) f Z) (hg Z hZ)
    simpa only [← derivedMappingPrecomp_comp] using hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    apply SSet.realizationWeakEquivalences.of_postcomp
      (derivedMappingPrecomp (C := C) g Z)
      (derivedMappingPrecomp (C := C) f Z) (hf Z hZ)
    simpa only [← derivedMappingPrecomp_comp] using hfg Z hZ

/-- Derived local equivalences are stable under retracts. The source retract is passed to the
opposite category and mapped by the fixed-target derived mapping functor. -/
theorem localEquivalences_isStableUnderRetracts {I : Type w}
    (S : I → Arrow C) :
    (localEquivalences S).IsStableUnderRetracts where
  of_retract h hg Z hZ := by
    let F := derivedMappingObject (C := C) ⋙ (evaluation C SSet.{v}).obj Z
    apply SSet.realizationWeakEquivalences.of_retract (h.op.map F)
    simpa [F, derivedMappingPrecomp] using hg Z hZ

/-- Every base weak equivalence is a derived local equivalence. The proof first transports the weak
equivalence through chosen cofibrant replacement, then applies raw mapping-space invariance. -/
theorem weakEquivalences_le_localEquivalences
    (data : HomotopyFunctionComplexPrecompData (C := C)) {I : Type w}
    (S : I → Arrow C) :
    weakEquivalences C ≤ localEquivalences S := by
  intro X Y f hf Z _
  have hQf : weakEquivalences C ((cofibrantReplacement (C := C)).map f) := by
    apply (weakEquivalences C).of_postcomp (W' := weakEquivalences C)
      ((cofibrantReplacement (C := C)).map f)
      ((cofibrantReplacementCounit (C := C)).app Y)
      WeakEquivalence.mem
    rw [(cofibrantReplacementCounit (C := C)).naturality]
    exact (weakEquivalences C).comp_mem _ _ WeakEquivalence.mem hf
  have h := data.precompWeakOfWeakEquivalence
    ((cofibrantReplacement (C := C)).map f)
    (by infer_instance) (by infer_instance) hQf
    ((fibrantReplacement (C := C)).obj Z) (by infer_instance)
  simpa [derivedMappingPrecomp, derivedMappingObject] using h

/-- For an arbitrary-universe empty family, derived local equivalences are exactly the base weak
equivalences. The reverse inclusion uses the packet's explicit weak-equivalence detector. -/
theorem localEquivalences_empty
    (data : HomotopyFunctionComplexData (C := C)) {I : Type w} [IsEmpty I]
    (S : I → Arrow C) :
    localEquivalences S = weakEquivalences C := by
  apply le_antisymm
  · intro X Y f hf
    apply (data.weakEquivalence_iff_derivedMappingPrecomp f).2
    intro Z hZ
    apply hf Z
    exact ⟨hZ, fun i ↦ isEmptyElim i⟩
  · exact weakEquivalences_le_localEquivalences
      data.toHomotopyFunctionComplexInvarianceData.toHomotopyFunctionComplexPrecompData S

end HomotopicalAlgebra
