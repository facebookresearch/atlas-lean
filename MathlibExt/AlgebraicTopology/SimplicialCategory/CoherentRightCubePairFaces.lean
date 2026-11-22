/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeFaceRangeIso

/-!
# Actual original pairwise right-cube face intersections

The two genuine coface factorizations have the same original operator.
Its retained range omits exactly the two supplied front labels, so the
whole original lower cube identifies with their actual intersection.
The empty overlap in degree one remains a separate literal empty case.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubePairFaces
open RightCubeFaceRangeIso RightCubeSupportBoundary RightCubeSupportedSubcomplex
variable {n : ℕ}

/-- The actual original operator omitting the two supplied distinct front labels. -/
def operator (i j : Fin (n + 3)) (hij : i < j) : ⦋n⦌ ⟶ ⦋n + 2⦌ :=
  SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i

/-- Both original coface factorizations give exactly the same whole resolving operator. -/
theorem operator_other (i j : Fin (n + 3)) (hij : i < j) :
    operator i j hij = SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)) ≫ SimplexCategory.δ j := by
  have h : (i.castPred (Fin.ne_last_of_lt hij)).castSucc < j := by simpa using hij
  exact (SimplexCategory.δ_comp_δ' h).symm

/-- The actual injected pair operator retains precisely the complement of the same two original labels. -/
theorem operator_range (i j : Fin (n + 3)) (hij : i < j) :
    Set.range (operator i j hij).toOrderHom = {i, j}ᶜ := by
  ext k
  constructor
  · rintro ⟨a, rfl⟩ h
    rcases h with h | h
    · exact Fin.succAbove_ne i ((j.pred (Fin.ne_zero_of_lt hij)).succAbove a) h
    · have he := congrArg (fun θ : ⦋n⦌ ⟶ ⦋n + 2⦌ => θ.toOrderHom a) (operator_other i j hij)
      exact Fin.succAbove_ne j ((i.castPred (Fin.ne_last_of_lt hij)).succAbove a) (he.symm.trans h)
  · intro hk
    have hki : k ≠ i := fun h => hk (Or.inl h)
    have hkj : k ≠ j := fun h => hk (Or.inr h)
    have hRange : k ∈ Set.range i.succAbove := by
      rw [Fin.range_succAbove]
      exact hki
    obtain ⟨b, hb⟩ := hRange
    have hbj : b ≠ j.pred (Fin.ne_zero_of_lt hij) := by
      intro h
      have he : i.succAbove b = j := h ▸ Fin.succAbove_pred_of_lt i j hij
      exact hkj (hb.symm.trans he)
    have hRangeB : b ∈ Set.range (j.pred (Fin.ne_zero_of_lt hij)).succAbove := by
      rw [Fin.range_succAbove]
      exact hbj
    obtain ⟨a, ha⟩ := hRangeB
    exact ⟨a, (congrArg i.succAbove ha).trans hb⟩

/-- The original pair operator is genuinely injected. -/
theorem operator_injective (i j : Fin (n + 3)) (hij : i < j) : Function.Injective (operator i j hij).toOrderHom :=
  (Fin.succAboveOrderEmb i).injective.comp (Fin.succAboveOrderEmb (j.pred (Fin.ne_zero_of_lt hij))).injective

/-- The actual supported range of the pair operator is the literal intersection of its two original
  omitted-support subcomplexes. -/
theorem supported_eq_inter (i j : Fin (n + 3)) (hij : i < j) :
    supported.{u} (n + 2) (Set.range (operator i j hij).toOrderHom) = missing (n + 2) i ⊓ missing (n + 2) j := by
  have hS : ({i, j}ᶜ : Set (Fin (n + 3))) = {i}ᶜ ∩ {j}ᶜ := by
    ext k
    exact not_or
  exact (congrArg (supported.{u} (n + 2)) (operator_range i j hij)).trans
    ((congrArg (supported.{u} (n + 2)) hS).trans
      ((supported_inter (n + 2) {i}ᶜ {j}ᶜ).trans
        (congrArg₂ (fun A B => A ⊓ B) (supported_compl_singleton (n + 2) i) (supported_compl_singleton (n + 2) j))))

/-- The genuine whole lower original cube isomorphism onto the same pairwise face intersection. -/
def pairIso (i j : Fin (n + 3)) (hij : i < j) : RightCubeRelations.object.{u} n ≅
    (missing.{u} (n + 2) i ⊓ missing (n + 2) j : (RightCubeRelations.object.{u} (n + 2)).Subcomplex) :=
  rangeIso (operator i j hij) (operator_injective i j hij) ≪≫ SSet.Subcomplex.eqToIso (supported_eq_inter i j hij)

/-- The actual pair-face isomorphism retains the whole original pair operator after its ambient inclusion. -/
theorem pairIso_inclusion (i j : Fin (n + 3)) (hij : i < j) :
    (pairIso.{u} i j hij).hom ≫ (missing (n + 2) i ⊓ missing (n + 2) j).ι = RightCubeCosimplicialMaps.map
      (operator i j hij) :=
  (Category.assoc (rangeIso (operator i j hij) (operator_injective i j hij)).hom
    (SSet.Subcomplex.eqToIso (supported_eq_inter i j hij)).hom (missing (n + 2) i ⊓ missing (n + 2) j).ι).trans
    ((congrArg (fun f => (rangeIso (operator i j hij) (operator_injective i j hij)).hom ≫ f)
      (SSet.Subcomplex.homOfLE_ι (supported_eq_inter i j hij).le)).trans (rangeMap_inclusion (operator i j hij)))

end CategoryTheory.CoherentRealization.RightCubePairFaces
