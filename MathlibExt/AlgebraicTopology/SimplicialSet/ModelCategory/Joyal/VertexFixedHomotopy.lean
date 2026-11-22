/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso
import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleBridges

/-!
# Original homotopies with degenerate vertex verticals

A homotopy of original endomorphisms whose vertex verticals are the
original degenerate edges induces a natural isomorphism on the full
functor homotopy categories into every quasicategory. The proof uses the
existing full prism evaluation, pointwise equivalence criterion and
actual precomposition natural transformation. No weak-map outcome is
assumed. This gives a categorical equivalence for an actual deformation
retraction with this explicit original vertex geometry.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace SSet

variable {X : SSet.{u}} {f g : X ⟶ X}

/-- The SAME original homotopy fixes each original vertex along its full vertical edge. -/
def Homotopy.HasDegenerateVerticals (H : Homotopy f g) : Prop :=
  ∀ x : X _⦋0⦌, H.h.app (op ⦋1⦌) (verticalOneSimplex x) = X.σ 0 x

/-- Every SAME original postcomposition edge is an equivalence in the full functor quasicategory. -/
theorem Homotopy.hoPreCompEdge_isEquivalence_of_degenerateVerticals (H : Homotopy f g)
    (hH : H.HasDegenerateVerticals) (C : SSet.{u}) [Quasicategory C]
    (z : ((ihom X).obj C) _⦋0⦌) : (H.hoPreCompEdge C z).IsEquivalence := by
  apply (Edge.isEquivalence_iff_forall_eval_vertex (H.hoPreCompEdge C z)).mpr
  intro x
  let q : X ⟶ C := (ihomVertexEquiv X C).symm z
  have hP : ihomPrismOfSimplex (H.hoPreCompEdge C z).edge = H.h ≫ q := by
    rw [Homotopy.hoPreCompEdge_edge, Homotopy.edgeIhom_edge]
    change MonoidalClosed.uncurry
      (yonedaEquiv.symm (yonedaEquiv (MonoidalClosed.curry (H.h ≫ q)))) = _
    rw [Equiv.symm_apply_apply, MonoidalClosed.uncurry_curry]
  have hv := ihomPrismOfSimplex_app_verticalOneSimplex (H.hoPreCompEdge C z) x
  have he : (((H.hoPreCompEdge C z).map ((pre (yonedaEquiv.symm x)).app C)).map
      (evalDeltaZeroIso C).hom).edge = (Edge.id (q.app (op ⦋0⦌) x)).edge := by
    exact hv.symm.trans
      ((congrArg (fun h => h.app (op ⦋1⦌) (verticalOneSimplex x)) hP).trans
        ((congrArg (q.app (op ⦋1⦌)) (hH x)).trans
          (ConcreteCategory.congr_hom (q.naturality (SimplexCategory.σ (0 : Fin 1)).op) x)))
  exact (Edge.isEquivalence_iff_of_edge_eq he).mpr (Edge.isEquivalence_id _)

/-- The SAME original precomposition natural transformation is invertible into EVERY quasicategory. -/
def Homotopy.hoPreFixedVertexIso (H : Homotopy f g) (hH : H.HasDegenerateVerticals)
    (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map ((pre f).app C)).toFunctor ≅ (hoFunctor.map ((pre g).app C)).toFunctor := by
  let t := H.hoPreNatTrans C
  have hi : ∀ z, IsIso (t.app z) := by
    intro z
    let a := HomotopyCategory.objEquiv z
    have hz : HomotopyCategory.mk a = z := HomotopyCategory.objEquiv.left_inv z
    rw [← hz]
    change IsIso (HomotopyCategory.homMk (H.hoPreCompEdge C a))
    exact (Edge.isEquivalence_iff _).mp (H.hoPreCompEdge_isEquivalence_of_degenerateVerticals hH C a)
  let _ : ∀ z, IsIso (t.app z) := hi
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- A genuine original retraction with these SAME degenerate vertex verticals is a categorical equivalence. -/
theorem categoricalEquivalences_of_vertexFixed_deformation {Y : SSet.{u}} (p : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ p = 𝟙 Y) (H : Homotopy (p ≫ s) (𝟙 X)) (hH : H.HasDegenerateVerticals) :
    categoricalEquivalences p := by
  apply categoricalEquivalences.of_section_of_hoPre_id_natIso hs
  intro C hC
  let _ : Quasicategory C := hC
  exact ⟨(eqToIso (hoFunctor_pre_id C)).symm ≪≫ (H.hoPreFixedVertexIso hH C).symm⟩

end SSet
