/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerCellParameterLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalMappingWeak

/-!
# Actual coefficient inner and marked final-horn cells

The original point-slice equivalence keeps the whole marked cells.
Their proved intrinsic mapping weakness and original monicity therefore
give trivial cofibrations in the genuine coefficient model. A controlled
horn square then fills against an actual coefficient fibration using
these same original inner or marked final-horn cells.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
attribute [local instance] coefficientMarkedModelCategory

/-- Each actual minimally marked inner horn is a trivial cofibration in the original coefficient model. -/
theorem coefficientInnerCell_trivialCofibration (n : ℕ) (i : Fin (n + 3))
    (hi : 0 < i) (hi' : i < Fin.last (n + 2)) :
    trivialCofibrations Marked.{u} (innerCell.{u} n i) := by
  refine ⟨?_, ?_⟩
  · rw [coefficientMarkedCofibrations_eq]
    exact innerCell_mono n i
  · change cartesianWeakEquivalences (Δ[0] : SSet.{u})
      (coefficientPointEquivalence.functor.map (innerCell.{u} n i))
    let _ : (cartesianWeakEquivalences (Δ[0] : SSet.{u})).RespectsIso := by
      unfold cartesianWeakEquivalences
      infer_instance
    let r : min (Δ[n + 2] : SSet.{u}) ⟶ max (Δ[0] : SSet.{u}) :=
      (parameterZeroIsTerminal .maximal).from _
    let e : Arrow.mk (coefficientPointEquivalence.functor.map (innerCell.{u} n i)) ≅
        Arrow.mk (innerCellOver n i r.hom) :=
      Arrow.isoMk
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (by apply Over.OverMorphism.ext; apply Hom.ext; rfl)
    exact ((cartesianWeakEquivalences (Δ[0] : SSet.{u})).arrow_mk_iso_iff e).mpr
      (innerCellOver_cartesian_weak n i hi hi' r.hom)

/-- The actual final horn with its same original marked critical edge is a genuine coefficient trivial cofibration. -/
theorem coefficientCartesianCriticalCell_trivialCofibration (n : ℕ) :
    trivialCofibrations Marked.{u} (cartesianCriticalCell.{u} n) := by
  refine ⟨?_, ?_⟩
  · rw [coefficientMarkedCofibrations_eq]
    exact cartesianCriticalCell_mono n
  · change cartesianWeakEquivalences (Δ[0] : SSet.{u})
      (coefficientPointEquivalence.functor.map (cartesianCriticalCell.{u} n))
    let _ : (cartesianWeakEquivalences (Δ[0] : SSet.{u})).RespectsIso := by
      unfold cartesianWeakEquivalences
      infer_instance
    let r : cartesianCriticalTarget.{u} n ⟶ max (Δ[0] : SSet.{u}) :=
      (parameterZeroIsTerminal .maximal).from _
    let e : Arrow.mk (coefficientPointEquivalence.functor.map (cartesianCriticalCell.{u} n)) ≅
        Arrow.mk (cartesianCriticalOver n r) :=
      Arrow.isoMk
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (by apply Over.OverMorphism.ext; apply Hom.ext; rfl)
    exact ((cartesianWeakEquivalences (Δ[0] : SSet.{u})).arrow_mk_iso_iff e).mpr
      (cartesianCriticalOver_weak n r)

/-- A whole controlled original horn square fills against an actual coefficient fibration, retaining its literal
missing index and critical edge. -/
theorem coefficientControlledCartesianHorn_lifting {X Y : Marked.{u}}
    (p : X ⟶ Y) (hp : fibrations Marked.{u} p) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (n + 2)) (t : (horn.{u} (n + 1) i : SSet.{u}) ⟶ X.toSSet)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ Y.toSSet)
    (hsq : t ≫ p.hom = (horn.{u} (n + 1) i).ι ≫ b)
    (hc : (0 < i ∧ i < Fin.last (n + 1)) ∨
      (i = Fin.last (n + 1) ∧ ∃ e : (horn.{u} (n + 1) i : SSet.{u}) _⦋1⦌,
        (horn.{u} (n + 1) i).ι.app (op ⦋1⦌) e =
          stdSimplex.edge (n + 1) (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _) ∧
        t.app (op ⦋1⦌) e ∈ X.marking)) :
    ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ X.toSSet,
      (horn.{u} (n + 1) i).ι ≫ l = t ∧ l ≫ p.hom = b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases hc with ⟨hi, hi'⟩ | ⟨hi, e, he, hm⟩
  · let hlp : HasLiftingProperty (innerCell.{u} m i) p :=
      hasLiftingProperty_of_wfs _ _ (coefficientInnerCell_trivialCofibration m i hi hi') hp
    obtain ⟨l, hl, hr⟩ := hlp.sq_hasLift
      (CommSq.mk (show ofMin t ≫ p = innerCell.{u} m i ≫ ofMin b from Hom.ext hsq))
    exact ⟨l.hom, congrArg Hom.hom hl, congrArg Hom.hom hr⟩
  · subst i
    have he' : e = rightHornEdgeSimplex.{u} m := by
      apply Subtype.ext
      exact he
    have hmX : t.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} m) ∈ X.marking := he' ▸ hm
    have hmY : b.app (op ⦋1⦌)
        ((horn.{u} (m + 2) (Fin.last (m + 2))).ι.app (op ⦋1⦌)
          (rightHornEdgeSimplex.{u} m)) ∈ Y.marking := by
      have h := ConcreteCategory.congr_hom (congr_app hsq (op ⦋1⦌)) (rightHornEdgeSimplex.{u} m)
      exact h ▸ p.preserve hmX
    let hlp : HasLiftingProperty (cartesianCriticalCell.{u} m) p :=
      hasLiftingProperty_of_wfs _ _ (coefficientCartesianCriticalCell_trivialCofibration m) hp
    obtain ⟨l, hl, hr⟩ := hlp.sq_hasLift
      (CommSq.mk (show ofCartesianCriticalSource t hmX ≫ p =
        cartesianCriticalCell.{u} m ≫ ofCartesianCriticalTarget b hmY from Hom.ext hsq))
    exact ⟨l.hom, congrArg Hom.hom hl, congrArg Hom.hom hr⟩

end SSet.Marked
