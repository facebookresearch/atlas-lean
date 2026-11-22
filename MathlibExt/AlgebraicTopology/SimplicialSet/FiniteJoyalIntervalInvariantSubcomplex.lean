/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCountableSupport
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaCountability
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFilteredColimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaPullbacks
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCylinder
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation

/-!
# Countable invariance under a raw replacement map

Close a countable subcomplex under the images of every simplex of the
interval times its replacement. The actual filtered inclusion colimit
and range factorization give a simplicial endomorphism on the replacement
of the resulting countable subcomplex.

This isolates the closure step in Cisinski's Lemma 2.4.38 at the project
finite-interval and omega replacement. No deformation equations are used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace SSet.joyalInterval

private lemma exists_countable_successor (Y : SSet.{u})
    (H : joyalInterval ⊗ auxiliaryOmegaFreeFiller.obj Y ⟶ auxiliaryOmegaFreeFiller.obj Y)
    (V : Y.Subcomplex) (hV : Countable V.toSSet.N) :
    ∃ W : Y.Subcomplex, V ≤ W ∧ Countable W.toSSet.N ∧
      ∀ (n : ℕ) (x : (joyalInterval ⊗ auxiliaryOmegaFreeFiller.obj V.toSSet) _⦋n⦌),
        ∃ y : auxiliaryOmegaFreeFiller.obj W.toSSet _⦋n⦌,
          (auxiliaryOmegaFreeFiller.map W.ι).app (op ⦋n⦌) y =
            ((joyalInterval ◁ auxiliaryOmegaFreeFiller.map V.ι) ≫ H).app (op ⦋n⦌) x := by
  classical
  let : Countable V.toSSet.N := hV
  let : Countable (auxiliaryOmegaFreeFiller.obj V.toSSet).N :=
    auxiliaryOmegaFreeFiller_countable_N V.toSSet
  have hdegrees : ∀ n : ℕ,
      Countable ((joyalInterval ⊗ auxiliaryOmegaFreeFiller.obj V.toSSet) _⦋n⦌) := by
    intro n
    have : Countable (auxiliaryOmegaFreeFiller.obj V.toSSet _⦋n⦌) :=
      countable_obj_of_countable_N _ (op ⦋n⦌)
    change Countable (joyalInterval _⦋n⦌ × auxiliaryOmegaFreeFiller.obj V.toSSet _⦋n⦌)
    infer_instance
  let := hdegrees
  let h := (joyalInterval ◁ auxiliaryOmegaFreeFiller.map V.ι) ≫ H
  let φ : (Σ n : ℕ, (joyalInterval ⊗ auxiliaryOmegaFreeFiller.obj V.toSSet) _⦋n⦌) →
      (Σ n : ℕ, auxiliaryOmegaFreeFiller.obj Y _⦋n⦌) :=
    fun x ↦ ⟨x.1, h.app (op ⦋x.1⦌) x.2⟩
  obtain ⟨S, hS, _, hpre⟩ := exists_countable_support Y (Set.range φ)
    (Set.countable_range φ)
  let C : Bool → Y.Subcomplex := fun b ↦ if b then S else V
  have hC : ∀ b : Bool, Countable (C b).toSSet.N := by
    intro b
    cases b <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;> assumption
  let := hC
  let W := iSup C
  refine ⟨W, le_iSup C false, Subcomplex.countable_N_iSup C, ?_⟩
  intro n x
  obtain ⟨s, hs⟩ := hpre ⟨n, h.app (op ⦋n⦌) x⟩ ⟨⟨n, x⟩, rfl⟩
  let i : S.toSSet ⟶ W.toSSet := Subcomplex.homOfLE (le_iSup C true)
  refine ⟨(auxiliaryOmegaFreeFiller.map i).app (op ⦋n⦌) s, ?_⟩
  change (auxiliaryOmegaFreeFiller.map i ≫ auxiliaryOmegaFreeFiller.map W.ι).app
    (op ⦋n⦌) s = h.app (op ⦋n⦌) x
  rw [← Functor.map_comp, Subcomplex.homOfLE_ι]
  exact hs

/-- Every raw interval endomorphism of the chosen replacement restricts
to the replacement of a countable subcomplex containing the given one.
Both countability bounds and the entire original inclusion equation hold. -/
theorem exists_countable_invariant_subcomplex (Y : SSet.{u})
    (H : joyalInterval ⊗ auxiliaryOmegaFreeFiller.obj Y ⟶ auxiliaryOmegaFreeFiller.obj Y)
    (U : Y.Subcomplex) (hU : Countable U.toSSet.N) :
    ∃ V : Y.Subcomplex, U ≤ V ∧ Countable V.toSSet.N ∧
      Countable (Σ n : ℕ, V.toSSet _⦋n⦌) ∧
      ∃ HV : joyalInterval ⊗ auxiliaryOmegaFreeFiller.obj V.toSSet ⟶
          auxiliaryOmegaFreeFiller.obj V.toSSet,
        (joyalInterval ◁ auxiliaryOmegaFreeFiller.map V.ι) ≫ H =
          HV ≫ auxiliaryOmegaFreeFiller.map V.ι := by
  classical
  let C := {V : Y.Subcomplex // Countable V.toSSet.N}
  choose next hle hcount hpre using
    (fun V : C ↦ exists_countable_successor Y H V.val V.property)
  let chain : ℕ → C := Nat.rec ⟨U, hU⟩ (fun _ V ↦ ⟨next V, hcount V⟩)
  let S : ℕ → Y.Subcomplex := fun n ↦ (chain n).val
  have hinc (n : ℕ) : S n ≤ S (n + 1) := hle (chain n)
  have hcounts : ∀ n : ℕ, Countable (S n).toSSet.N := fun n ↦ (chain n).property
  let := hcounts
  let V := iSup S
  have hV : Countable V.toSSet.N := Subcomplex.countable_N_iSup S
  let := hV
  have hm : Monotone S := monotone_nat_of_le_succ hinc
  let F : ℕ ⥤ Y.Subcomplex := hm.functor
  let c := Preorder.colimitCoconeOfIsLUB F isLUB_iSup
  let cY := (Subcomplex.toSSetFunctor (X := Y)).mapCocone c.cocone
  have hcY : IsColimit cY :=
    isColimitOfPreserves (Subcomplex.toSSetFunctor (X := Y)) c.isColimit
  let : PreservesFilteredColimitsOfSize.{0, 0} auxiliaryOmegaFreeFiller.{u} :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let cL := auxiliaryOmegaFreeFiller.mapCocone cY
  have hcL : IsColimit cL := isColimitOfPreserves auxiliaryOmegaFreeFiller hcY
  let cJ := (tensorLeft joyalInterval).mapCocone cL
  have hcJ : IsColimit cJ := isColimitOfPreserves (tensorLeft joyalInterval) hcL
  let K := auxiliaryOmegaFreeFiller.map V.ι
  let h := (joyalInterval ◁ K) ≫ H
  have hr : Subcomplex.range h ≤ Subcomplex.range K := by
    have heq : Subcomplex.range h = ⨆ n : ℕ, Subcomplex.range (cJ.ι.app n ≫ h) :=
      range_eq_iSup_of_isColimit hcJ h
    apply heq.le.trans
    refine iSup_le fun n ↦ ?_
    have hleg : cJ.ι.app n ≫ h =
        (joyalInterval ◁ auxiliaryOmegaFreeFiller.map (S n).ι) ≫ H := by
      change (joyalInterval ◁ auxiliaryOmegaFreeFiller.map
          (Subcomplex.homOfLE (le_iSup S n))) ≫
        (joyalInterval ◁ auxiliaryOmegaFreeFiller.map V.ι) ≫ H = _
      rw [← Category.assoc, ← whiskerLeft_comp, ← Functor.map_comp,
        Subcomplex.homOfLE_ι]
    rw [hleg]
    rintro ⟨⟨k⟩⟩ x ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hpre (chain n) k z
    let i : (S (n + 1)).toSSet ⟶ V.toSSet :=
      Subcomplex.homOfLE (le_iSup S (n + 1))
    refine ⟨(auxiliaryOmegaFreeFiller.map i).app (op ⦋k⦌) a, ?_⟩
    change (auxiliaryOmegaFreeFiller.map i ≫ auxiliaryOmegaFreeFiller.map V.ι).app
      (op ⦋k⦌) a = _
    rw [← Functor.map_comp, Subcomplex.homOfLE_ι]
    exact ha
  let HV := Subcomplex.lift h hr ≫ (asIso (Subcomplex.toRange K)).inv
  have hK : (asIso (Subcomplex.toRange K)).inv ≫ K = (Subcomplex.range K).ι := by
    calc
      _ = (asIso (Subcomplex.toRange K)).inv ≫
          (Subcomplex.toRange K ≫ (Subcomplex.range K).ι) := by
        rw [Subcomplex.toRange_ι]
      _ = (Subcomplex.range K).ι := by simp
  refine ⟨V, le_iSup S 0, hV, countable_sigma_obj_of_countable_N V.toSSet, HV, ?_⟩
  change h = HV ≫ K
  dsimp only [HV]
  rw [Category.assoc, hK, Subcomplex.lift_ι]

end SSet.joyalInterval
