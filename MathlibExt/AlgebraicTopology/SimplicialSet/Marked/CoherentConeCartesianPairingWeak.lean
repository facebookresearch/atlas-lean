/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientCartesianControlledCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ControlledCartesianPairingLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellMarkingCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexVertexCoverage

/-!
# Genuine coefficient weakness of original controlled Cartesian rank attachments

The native marked rank ladder retains every original simplex, index,
attaching map and target-inherited marking. Its actual inner or marked
final horn cells are coefficient trivial cofibrations. Their full
coefficient fibration lifting, the original rank pushouts and original
mark coverage prove every actual rank step and the complete original
inclusion trivial cofibrations in the genuine coefficient model.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
attribute [local instance] coefficientMarkedModelCategory

variable (ambient : Marked.{u}) (A : ambient.toSSet.Subcomplex) (P : A.Pairing) [P.IsRegular]

/-- Each actual controlled native rank step is a trivial cofibration in the original coefficient model, with exactly
its original stage marking and attaching maps. -/
theorem coherentConeCartesianPairing_step_trivialCofibration
    (hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌))
    (hP : CartesianControlledPairing ambient A P) (j : ℕ) :
    trivialCofibrations Marked.{u}
      ((pairingFiltration ambient A P).map (homOfLE (Nat.le_succ j))) := by
  rw [← llp_eq_of_wfs (trivialCofibrations Marked.{u}) (fibrations Marked.{u})]
  intro X Y p hp
  let f := P.rankFunction
  let g := (pairingFiltration ambient A P).map (homOfLE (Nat.le_succ j))
  let β : (f.filtration j : SSet.{u}) ⟶ (f.filtration (Order.succ j) : SSet.{u}) := g.hom
  let hpPush := f.isPushout j
  refine ⟨fun {top bottom} sq => ?_⟩
  let t : (f.filtration j : SSet.{u}) ⟶ X.toSSet := top.hom
  let b : (f.filtration (Order.succ j) : SSet.{u}) ⟶ Y.toSSet := bottom.hom
  have hsq : t ≫ p.hom = β ≫ b := congrArg Hom.hom sq.w
  have cells (c : f.Cell j) : ∃ l : (Δ[c.dim + 1] : SSet.{u}) ⟶ X.toSSet,
      c.horn.ι ≫ l = c.mapHorn ≫ t ∧ l ≫ p.hom = c.mapToSucc ≫ b := by
    have hh : c.mapHorn ≫ β = c.horn.ι ≫ c.mapToSucc := by
      have hsqPush : f.t j ≫ β = f.m j ≫ f.b j := hpPush.w
      have h := congrArg (fun z => c.ιSigmaHorn ≫ z) hsqPush
      have hright : c.ιSigmaHorn ≫ f.m j ≫ f.b j = c.horn.ι ≫ c.mapToSucc :=
        (Subcomplex.Pairing.RankFunction.Cell.ι_m_assoc f c (f.b j)).trans
          (congrArg (fun z => c.horn.ι ≫ z) c.ι_b)
      exact (c.ι_t_assoc β).symm.trans (h.trans hright)
    have hc : (c.mapHorn ≫ t) ≫ p.hom = c.horn.ι ≫ (c.mapToSucc ≫ b) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => c.mapHorn ≫ z) hsq).trans
          (((Category.assoc _ _ _).symm).trans
            ((congrArg (fun z => z ≫ b) hh).trans (Category.assoc _ _ _))))
    have hd : 1 ≤ c.dim :=
      Subcomplex.N.one_le_dim_of_vertices (vertices_mem_of_marks_mem ambient A hmarks) c.s.val
    have hcontrol : (0 < c.index ∧ c.index < Fin.last (c.dim + 1)) ∨
        (c.index = Fin.last (c.dim + 1) ∧ ∃ e : c.horn.toSSet _⦋1⦌,
          c.horn.ι.app (op ⦋1⦌) e =
            stdSimplex.edge (c.dim + 1) (Fin.last c.dim).castSucc (Fin.last (c.dim + 1)) (Fin.le_last _) ∧
          (c.mapHorn ≫ t).app (op ⦋1⦌) e ∈ X.marking) := by
      rcases hP j c with hi | ⟨_, hi, e, he, hm⟩
      · exact Or.inl hi
      · exact Or.inr ⟨hi, e, he, top.preserve hm⟩
    exact coefficientControlledCartesianHorn_lifting p hp c.dim hd c.index
      (c.mapHorn ≫ t) (c.mapToSucc ≫ b) hc hcontrol
  choose l hl hr using cells
  let L : f.sigmaStdSimplex j ⟶ X.toSSet := Sigma.desc l
  have ht : f.t j ≫ t = f.m j ≫ L := by
    apply Sigma.hom_ext
    intro c
    have hι : c.ιSigmaStdSimplex ≫ L = l c := Sigma.ι_comp_desc _ _
    have hright : c.ιSigmaHorn ≫ f.m j ≫ L = c.horn.ι ≫ l c :=
      (Subcomplex.Pairing.RankFunction.Cell.ι_m_assoc f c L).trans (congrArg (fun z => c.horn.ι ≫ z) hι)
    exact (c.ι_t_assoc t).trans ((hl c).symm.trans hright.symm)
  let d : (f.filtration (Order.succ j) : SSet.{u}) ⟶ X.toSSet := hpPush.desc t L ht
  have hd : β ≫ d = t := hpPush.inl_desc t L ht
  have hd' : f.b j ≫ d = L := hpPush.inr_desc t L ht
  have hdp : d ≫ p.hom = b := by
    apply hpPush.hom_ext
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ p.hom) hd).trans hsq)
    · have hLp : L ≫ p.hom = f.b j ≫ b := by
        apply Sigma.hom_ext
        intro c
        have hι : c.ιSigmaStdSimplex ≫ L = l c := Sigma.ι_comp_desc _ _
        exact ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ p.hom) hι)).trans
          ((hr c).trans (c.ι_b_assoc b).symm)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ p.hom) hd').trans hLp)
  have hcov := pairingFiltration_step_markingSurjective ambient A P hmarks j
  let diagonal : (pairingFiltration ambient A P).obj (Order.succ j) ⟶ X :=
    { hom := d
      preserve {e} he := by
        obtain ⟨a, ha, hae⟩ := hcov e he
        have hda : d.app (op ⦋1⦌) e = t.app (op ⦋1⦌) a :=
          (congrArg (d.app (op ⦋1⦌)) hae).symm.trans
            (ConcreteCategory.congr_hom (congr_app hd (op ⦋1⦌)) a)
        exact hda.symm ▸ top.preserve ha }
  exact CommSq.HasLift.mk' ⟨diagonal, Hom.ext hd, Hom.ext hdp⟩

/-- The entire original marked controlled rank inclusion is a genuine coefficient trivial cofibration through the
same original natural-number transfinite composition. -/
theorem coherentConeCartesianPairing_trivialCofibration
    (hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌))
    (hP : CartesianControlledPairing ambient A P) :
    trivialCofibrations Marked.{u} (comapHom ambient A.ι) := by
  rw [← llp_eq_of_wfs (trivialCofibrations Marked.{u}) (fibrations Marked.{u})]
  let W : MorphismProperty Marked.{u} := (fibrations Marked.{u}).llp
  let h := pairingFiltrationTransfiniteComposition ambient A P hmarks
  let hw : W.TransfiniteCompositionOfShape ℕ (comapHom ambient A.ι) :=
    { toTransfiniteCompositionOfShape := h
      map_mem j _ := by
        have hs := coherentConeCartesianPairing_step_trivialCofibration ambient A P hmarks hP j
        rw [← llp_eq_of_wfs (trivialCofibrations Marked.{u}) (fibrations Marked.{u})] at hs
        exact hs }
  exact (transfiniteCompositionsOfShape_le W ℕ) _ ⟨hw⟩

end SSet.Marked
