/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningMarkedCriticalCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ControlledCartesianPairingLifting

/-!
# SAME original controlled pairing stages lift actual native Un maps

The actual original coherent-model fibration gives every original inner
or marked critical-cell lift. The SAME original controlled pairing rank,
whole horn and bottom simplex, actual coproduct/pushout ladder and full
old-stage marking coverage produce the original native marked diagonal.
Neither coherent diagram need be fibrant, and neither scalar nor base
need be Kan or a quasicategory. No native filler or Quillen result is an
input; every native cell lift is derived from the ACTUAL target model.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (ambient : Marked.{u}) (A : ambient.toSSet.Subcomplex) (P : A.Pairing) [P.IsRegular]

/-- Every SAME original rank stage retains its whole marked diagonal against native Un of an ACTUAL coherent-model
fibration, using the original inner or marked final cell and the old source markings. -/
theorem nativeUnstraightening_controlledPairing_step_lifting
    (hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌))
    (hP : CartesianControlledPairing ambient A P) (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (j : ℕ) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty
      ((pairingFiltration ambient A P).map (homOfLE (Nat.le_succ j)))
        ((nativeUnstraightening B).map q).left := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p : (nativeUnstraighteningTotal B F).toSSet ⟶ (nativeUnstraighteningTotal B G).toSSet :=
    ((nativeUnstraightening B).map q).left.hom
  let _ : InnerFibration p := nativeUnstraightening_map_innerFibration B q hq
  let f := P.rankFunction
  let g := (pairingFiltration ambient A P).map (homOfLE (Nat.le_succ j))
  let β : (f.filtration j : SSet.{u}) ⟶ (f.filtration (Order.succ j) : SSet.{u}) := g.hom
  let hp := f.isPushout j
  refine ⟨fun {top bottom} sq => ?_⟩
  let t : (f.filtration j : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet := top.hom
  let b : (f.filtration (Order.succ j) : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet := bottom.hom
  have hsq : t ≫ p = β ≫ b := congrArg Hom.hom sq.w
  have cells (c : f.Cell j) : ∃ l : (Δ[c.dim + 1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      c.horn.ι ≫ l = c.mapHorn ≫ t ∧ l ≫ p = c.mapToSucc ≫ b := by
    have hh : c.mapHorn ≫ β = c.horn.ι ≫ c.mapToSucc := by
      have hsqPush : f.t j ≫ β = f.m j ≫ f.b j := hp.w
      have h := congrArg (fun z => c.ιSigmaHorn ≫ z) hsqPush
      have hright : c.ιSigmaHorn ≫ f.m j ≫ f.b j = c.horn.ι ≫ c.mapToSucc :=
        (Subcomplex.Pairing.RankFunction.Cell.ι_m_assoc f c (f.b j)).trans
          (congrArg (fun z => c.horn.ι ≫ z) c.ι_b)
      exact (c.ι_t_assoc β).symm.trans (h.trans hright)
    have hc : (c.mapHorn ≫ t) ≫ p = c.horn.ι ≫ (c.mapToSucc ≫ b) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => c.mapHorn ≫ z) hsq).trans
          (((Category.assoc _ _ _).symm).trans
            ((congrArg (fun z => z ≫ b) hh).trans (Category.assoc _ _ _))))
    rcases hP j c with ⟨hi, hi'⟩ | ⟨hd, hi, e, he, hmark⟩
    · let hlp : HasLiftingProperty c.horn.ι p :=
        InnerFibration.mem _ (horn_ι_mem_innerHornInclusions hi hi')
      obtain ⟨l, hl, hlp⟩ := hlp.sq_hasLift (CommSq.mk hc)
      exact ⟨l, hl, hlp⟩
    · have hm : (c.mapHorn ≫ t).app (op ⦋1⦌) e ∈ (nativeUnstraighteningTotal B F).marking :=
        top.preserve hmark
      exact nativeUnstraightening_fill_originalFinalHorn B q hq hd hi _ _ hc e he hm
  choose l hl hr using cells
  let L : f.sigmaStdSimplex j ⟶ (nativeUnstraighteningTotal B F).toSSet := Sigma.desc l
  have ht : f.t j ≫ t = f.m j ≫ L := by
    apply Sigma.hom_ext
    intro c
    have hι : c.ιSigmaStdSimplex ≫ L = l c := Sigma.ι_comp_desc _ _
    have hright : c.ιSigmaHorn ≫ f.m j ≫ L = c.horn.ι ≫ l c :=
      (Subcomplex.Pairing.RankFunction.Cell.ι_m_assoc f c L).trans (congrArg (fun z => c.horn.ι ≫ z) hι)
    exact (c.ι_t_assoc t).trans ((hl c).symm.trans hright.symm)
  let d : (f.filtration (Order.succ j) : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet := hp.desc t L ht
  have hd : β ≫ d = t := hp.inl_desc t L ht
  have hd' : f.b j ≫ d = L := hp.inr_desc t L ht
  have hdp : d ≫ p = b := by
    apply hp.hom_ext
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ p) hd).trans hsq)
    · have hLp : L ≫ p = f.b j ≫ b := by
        apply Sigma.hom_ext
        intro c
        have hι : c.ιSigmaStdSimplex ≫ L = l c := Sigma.ι_comp_desc _ _
        exact ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ p) hι)).trans
          ((hr c).trans (c.ι_b_assoc b).symm)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ p) hd').trans hLp)
  have hcov := pairingFiltration_step_markingSurjective ambient A P hmarks j
  let diagonal : (pairingFiltration ambient A P).obj (Order.succ j) ⟶ nativeUnstraighteningTotal B F :=
    { hom := d
      preserve {e} he := by
        obtain ⟨a, ha, hae⟩ := hcov e he
        have hda : d.app (op ⦋1⦌) e = t.app (op ⦋1⦌) a :=
          (congrArg (d.app (op ⦋1⦌)) hae).symm.trans
            (ConcreteCategory.congr_hom (congr_app hd (op ⦋1⦌)) a)
        exact hda.symm ▸ top.preserve ha }
  exact CommSq.HasLift.mk' ⟨diagonal, Hom.ext hd, Hom.ext hdp⟩

end SSet.Marked
