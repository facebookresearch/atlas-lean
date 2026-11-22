/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenRightMate
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Original Quillen right mates at every fibrant target

The original left comparison is weak on actual cofibrant objects. The existing
Quillen Hom comparison proves bijective postcomposition by the same original
right mate on those Hom sets. The exact original Q counits then provide the two
cofibrant tests needed to construct a full homotopy inverse. No cofibrancy of
the right-adjoint images and no desired weak-mate outcome is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe uC uD vC vD

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.QuillenRightMate

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L₀ L₁ : C ⥤ D} {R₀ R₁ : D ⥤ C}
  (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁)
  [adj₀.IsQuillenAdjunction] [adj₁.IsQuillenAdjunction]

/-- The SAME original right mate is weak at every fibrant target, from the
original actual cofibrant replacements and original weak-left Hom tests. -/
theorem weakEquivalence_conjugate_of_cofibrantComponents
    (q : GeneratedFunctorialReplacements.Data (C := C)) (α : L₀ ⟶ L₁)
    (hα : ∀ (X : C) [IsCofibrant X], WeakEquivalence (α.app X))
    (Y : D) [IsFibrant Y] : WeakEquivalence ((conjugateEquiv adj₁ adj₀ α).app Y) := by
  let HC := toHomotopyCategory C
  let β : R₁.obj Y ⟶ R₀.obj Y := (conjugateEquiv adj₁ adj₀ α).app Y
  let pA : q.Q.obj (R₁.obj Y) ⟶ R₁.obj Y := q.q.app _
  let pB : q.Q.obj (R₀.obj Y) ⟶ R₀.obj Y := q.q.app _
  let _ : IsCofibrant (q.Q.obj (R₁.obj Y)) := q.q_cofibrant _
  let _ : IsCofibrant (q.Q.obj (R₀.obj Y)) := q.q_cofibrant _
  let _ : WeakEquivalence pA := (weakEquivalence_iff _).mpr (q.q_trivialFibration _).2
  let _ : WeakEquivalence pB := (weakEquivalence_iff _).mpr (q.q_trivialFibration _).2
  let _ : IsIso (HC.map pA) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map pA).mp (mem_weakEquivalences pA)
  let _ : IsIso (HC.map pB) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map pB).mp (mem_weakEquivalences pB)
  let _ : WeakEquivalence (α.app (q.Q.obj (R₀.obj Y))) := hα _
  let _ : WeakEquivalence (α.app (q.Q.obj (R₁.obj Y))) := hα _
  have hB := bijective_postcomp_conjugate adj₀ adj₁ α (q.Q.obj (R₀.obj Y)) Y
  have hA := bijective_postcomp_conjugate adj₀ adj₁ α (q.Q.obj (R₁.obj Y)) Y
  obtain ⟨g₀, hg₀⟩ := hB.surjective (HC.map pB)
  change g₀ ≫ HC.map β = HC.map pB at hg₀
  let g : HC.obj (R₀.obj Y) ⟶ HC.obj (R₁.obj Y) := inv (HC.map pB) ≫ g₀
  have hg : g ≫ HC.map β = 𝟙 _ := by
    dsimp [g]
    rw [Category.assoc, hg₀, IsIso.inv_hom_id]
  have hβg : HC.map β ≫ g = 𝟙 _ := by
    apply (cancel_epi (HC.map pA)).mp
    apply hA.injective
    change (HC.map pA ≫ (HC.map β ≫ g)) ≫ HC.map β = (HC.map pA ≫ 𝟙 _) ≫ HC.map β
    simp only [Category.assoc, hg, Category.comp_id]
  let _ : IsIso (HC.map β) := ⟨⟨g, hβg, hg⟩⟩
  exact (weakEquivalence_iff _).mpr
    ((weakEquivalence_iff_isIso_toHomotopyCategory_map β).mpr inferInstance)

end HomotopicalAlgebra.QuillenRightMate

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- The actual base Quillen equivalence reflects weak maps between fibrant targets
using its original Q counit and full adjoint-map criterion. -/
theorem reflectsWeak_fibrant_with_originalQ
    {C : Type uC} [Category.{vC} C] [ModelCategory C]
    {D : Type uD} [Category.{vD} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenEquivalence]
    (q : GeneratedFunctorialReplacements.Data (C := C))
    {A B : D} [IsFibrant A] [IsFibrant B] (f : A ⟶ B) [WeakEquivalence (R.map f)] :
    WeakEquivalence f := by
  let X := q.Q.obj (R.obj A)
  let p : X ⟶ R.obj A := q.q.app (R.obj A)
  let _ : IsCofibrant X := q.q_cofibrant _
  let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr (q.q_trivialFibration _).2
  let e : L.obj X ⟶ A := (adj.homEquiv X A).symm p
  let _ : WeakEquivalence e := (weakEquivalence_homEquiv_iff (adj := adj) e).mpr (by
    change WeakEquivalence ((adj.homEquiv X A) ((adj.homEquiv X A).symm p))
    rw [Equiv.apply_symm_apply]
    infer_instance)
  let _ : WeakEquivalence (e ≫ f) := (weakEquivalence_homEquiv_iff (adj := adj) (e ≫ f)).mpr (by
    rw [adj.homEquiv_naturality_right]
    change WeakEquivalence ((adj.homEquiv X A) ((adj.homEquiv X A).symm p) ≫ R.map f)
    rw [Equiv.apply_symm_apply]
    infer_instance)
  exact (weakEquivalence_precomp_iff e f).mp inferInstance

end CategoryTheory.Adjunction.IsQuillenEquivalence
