/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PairingFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Fibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LeftHornLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornLifting
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Original marked pairing lifts with a controlled critical edge

Each native rank cell is an inner horn, or a critical outer horn whose
original distinguished edge is marked at that very stage. A marked map
into the intrinsic target therefore supplies the genuine critical-edge
filler. The actual coproduct/pushout ladder and mark coverage extend the
whole original diagonal through the rank filtration. The conditions are
explicit simplex/index/mark conditions on the source pairing; no model,
localization or target lifting outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked

variable (ambient : Marked.{u}) (A : ambient.toSSet.Subcomplex) (P : A.Pairing) [P.IsRegular]

/-- Every original pairing cell is inner or has its literal critical first edge marked in the old stage. -/
def CocartesianControlledPairing : Prop :=
  ∀ (j : ℕ) (c : P.rankFunction.Cell j),
    (0 < c.index ∧ c.index < Fin.last (c.dim + 1)) ∨
      ∃ (hd : 1 ≤ c.dim), c.index = 0 ∧
        ∃ e : c.horn.toSSet _⦋1⦌,
          c.horn.ι.app (op ⦋1⦌) e =
            stdSimplex.edge (c.dim + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _) ∧
          c.mapHorn.app (op ⦋1⦌) e ∈ (comap ambient (P.rankFunction.filtration j).ι).marking

private theorem fill_initial_horn {E B : SSet.{u}} (p : E ⟶ B) {n : ℕ} (hn : 1 ≤ n)
    {i : Fin (n + 2)} (hi : i = 0)
    (t : (horn.{u} (n + 1) i : SSet.{u}) ⟶ E) (b : (Δ[n + 1] : SSet.{u}) ⟶ B)
    (hsq : t ≫ p = (horn.{u} (n + 1) i).ι ≫ b)
    (e : (horn.{u} (n + 1) i : SSet.{u}) _⦋1⦌)
    (he : (horn.{u} (n + 1) i).ι.app (op ⦋1⦌) e =
      stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _))
    (hcart : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (t.app (op ⦋1⦌) e))) :
    ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ E,
      (horn.{u} (n + 1) i).ι ≫ l = t ∧ l ≫ p = b := by
  subst i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he' : e = leftHornEdgeSimplex.{u} m := by
    apply Subtype.ext
    exact he
  have hc : CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (leftHornEdge t).edge) := by
    rw [leftHornEdge_edge]
    exact (congrArg (fun z => CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (t.app (op ⦋1⦌) z)))
      he').to_iff.mp hcart
  exact CocartesianEdge.exists_fill_leftHorn_of_isPCocartesian t b hsq hc

/-- One actual marked rank stage lifts by its native inner or marked critical first-horn filler. -/
theorem cocartesianControlledPairing_step_lifting
    (hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌))
    (hP : CocartesianControlledPairing ambient A P) {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] (j : ℕ) :
    HasLiftingProperty ((pairingFiltration ambient A P).map (homOfLE (Nat.le_succ j)))
      (cocartesianProjection p) := by
  let f := P.rankFunction
  let g := (pairingFiltration ambient A P).map (homOfLE (Nat.le_succ j))
  let β : (f.filtration j : SSet.{u}) ⟶ (f.filtration (Order.succ j) : SSet.{u}) := g.hom
  let hp := f.isPushout j
  refine ⟨fun {top bottom} sq => ?_⟩
  let t : (f.filtration j : SSet.{u}) ⟶ E := top.hom
  let b : (f.filtration (Order.succ j) : SSet.{u}) ⟶ B := bottom.hom
  have hsq : t ≫ p = β ≫ b := congrArg Hom.hom sq.w
  have cells (c : f.Cell j) : ∃ l : (Δ[c.dim + 1] : SSet.{u}) ⟶ E,
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
    · have hcart : CocartesianEdge.IsPCocartesian p
          (yonedaEquiv.symm ((c.mapHorn ≫ t).app (op ⦋1⦌) e)) := top.preserve hmark
      exact fill_initial_horn p hd hi _ _ hc e he hcart
  choose l hl hr using cells
  let L : f.sigmaStdSimplex j ⟶ E := Sigma.desc l
  have ht : f.t j ≫ t = f.m j ≫ L := by
    apply Sigma.hom_ext
    intro c
    have hι : c.ιSigmaStdSimplex ≫ L = l c := Sigma.ι_comp_desc _ _
    have hright : c.ιSigmaHorn ≫ f.m j ≫ L = c.horn.ι ≫ l c :=
      (Subcomplex.Pairing.RankFunction.Cell.ι_m_assoc f c L).trans (congrArg (fun z => c.horn.ι ≫ z) hι)
    exact (c.ι_t_assoc t).trans ((hl c).symm.trans hright.symm)
  let d : (f.filtration (Order.succ j) : SSet.{u}) ⟶ E := hp.desc t L ht
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
  let diagonal : (pairingFiltration ambient A P).obj (Order.succ j) ⟶ cocartesian p :=
    { hom := d
      preserve {e} he := by
        obtain ⟨a, ha, hae⟩ := hcov e he
        have hda : d.app (op ⦋1⦌) e = t.app (op ⦋1⦌) a :=
          (congrArg (d.app (op ⦋1⦌)) hae).symm.trans
            (ConcreteCategory.congr_hom (congr_app hd (op ⦋1⦌)) a)
        exact hda.symm ▸ top.preserve ha }
  exact CommSq.HasLift.mk' ⟨diagonal, Hom.ext hd, Hom.ext hdp⟩

/-- The whole original marked inclusion lifts against every intrinsic cocartesian projection when the native
  pairing has the explicit critical-edge marking condition. -/
theorem cocartesianControlledPairing_lifting
    (hmarks : ∀ e : ambient.toSSet _⦋1⦌, e ∈ ambient.marking → e ∈ A.obj (op ⦋1⦌))
    (hP : CocartesianControlledPairing ambient A P) {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty (comapHom ambient A.ι) (cocartesianProjection p) := by
  let W : MorphismProperty Marked.{u} := (ofHoms (fun _ : Unit => cocartesianProjection p)).llp
  let h := pairingFiltrationTransfiniteComposition ambient A P hmarks
  let hw : W.TransfiniteCompositionOfShape ℕ (comapHom ambient A.ι) :=
    { toTransfiniteCompositionOfShape := h
      map_mem j _ := by
        intro U V q hq
        obtain ⟨i⟩ := hq
        exact cocartesianControlledPairing_step_lifting ambient A P hmarks hP p j }
  have hW : W (comapHom ambient A.ι) := (transfiniteCompositionsOfShape_le W ℕ) _ ⟨hw⟩
  exact hW _ (ofHoms.mk ())

end SSet.Marked
