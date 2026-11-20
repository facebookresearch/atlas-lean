/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.EulerGeometricFaces
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.BdEdgeMatchStarHull

open Set SimpleGraph Function

namespace StatMech

namespace Lattice


















theorem bemc_bdEdge_imp_on_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd




theorem bemc_off_support_not_bdEdge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    ¬ bdEdge (jec_leftRegion Vc) s(u, v) :=
  jlri_no_bdEdge_off_support Vc hadj hu hv







theorem bemc_bdEdge_iff_membership_flip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔
      (u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) := by
  rw [bdEdge_mk]











theorem bemc_bdEdge_iff_support_flip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔
      ((u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) ∧
        (u ∈ Vc.support ∨ v ∈ Vc.support)) := by
  constructor
  · intro hbd
    refine ⟨(bemc_bdEdge_iff_membership_flip Vc).mp hbd,
      bemc_bdEdge_imp_on_support Vc hadj hbd⟩
  · rintro ⟨hflip, _⟩
    exact (bemc_bdEdge_iff_membership_flip Vc).mpr hflip














theorem bemc_leftRegion_finite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc).Finite :=
  egf_leftRegion_finite Vc R hsupp





theorem bemc_compl_leftRegion_infinite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc)ᶜ.Infinite := by
  have hsub : exterior 2 R ⊆ (jec_leftRegion Vc)ᶜ :=
    fun z hz => egf_exterior_outside Vc R hsupp hz
  exact (exterior_infinite R (by norm_num)).mono hsub







theorem bemc_orientation_selected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {K : Set (Site 2)} (hKfin : K.Finite)
    (hid : K = jec_leftRegion Vc ∨ K = (jec_leftRegion Vc)ᶜ) :
    K = jec_leftRegion Vc := by
  rcases hid with h | h
  · exact h
  · exact absurd (h ▸ hKfin) (bemc_compl_leftRegion_infinite Vc R hsupp)



















theorem bemc_leftRegion_eq_of_bdEdgeMatch {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {K : Set (Site 2)} (hKfin : K.Finite)
    (hmatch : pww_BdEdgeMatch K Vc) :
    K = jec_leftRegion Vc :=
  bemc_orientation_selected Vc R hsupp hKfin
    ((pbs_bdEdgeMatch_iff_setIdentity Vc).mp hmatch)










theorem bemc_bdEdgeMatch_iff_leftRegion_eq {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {K : Set (Site 2)} (hKfin : K.Finite) :
    pww_BdEdgeMatch K Vc ↔ K = jec_leftRegion Vc := by
  constructor
  · intro hmatch
    exact bemc_leftRegion_eq_of_bdEdgeMatch Vc R hsupp hKfin hmatch
  · intro heq
    exact pbs_bdEdgeMatch_of_leftRegion_eq Vc heq















theorem bemc_dcd_windingRegion_orientation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc).Finite ∧ (jec_leftRegion Vc)ᶜ.Infinite ∧
      (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (bdEdge (jec_leftRegion Vc) s(u, v) →
          (u ∈ Vc.support ∨ v ∈ Vc.support)) ∧
        (u ∉ Vc.support → v ∉ Vc.support →
          ¬ bdEdge (jec_leftRegion Vc) s(u, v))) := by
  refine ⟨bemc_leftRegion_finite Vc R hsupp, bemc_compl_leftRegion_infinite Vc R hsupp, ?_⟩
  intro u v hadj
  exact ⟨bemc_bdEdge_imp_on_support Vc hadj,
    bemc_off_support_not_bdEdge Vc hadj⟩













theorem bemc_minimalLoop_orientation_selected (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R) {J : Set (Site 2)} (hJfin : J.Finite)
    (hid : J = jec_leftRegion (mpl_orbitLoop K a) ∨ J = (jec_leftRegion (mpl_orbitLoop K a))ᶜ) :
    J = jec_leftRegion (mpl_orbitLoop K a) :=
  bemc_orientation_selected (mpl_orbitLoop K a) R hsupp hJfin hid







theorem bemc_minimalLoop_leftRegion_eq_of_bdEdgeMatch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R) {J : Set (Site 2)} (hJfin : J.Finite)
    (hmatch : pww_BdEdgeMatch J (mpl_orbitLoop K a)) :
    J = jec_leftRegion (mpl_orbitLoop K a) :=
  bemc_leftRegion_eq_of_bdEdgeMatch (mpl_orbitLoop K a) R hsupp hJfin hmatch




theorem bemc_minimalLoop_bdEdgeMatch_iff_leftRegion_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R) {J : Set (Site 2)} (hJfin : J.Finite) :
    pww_BdEdgeMatch J (mpl_orbitLoop K a) ↔ J = jec_leftRegion (mpl_orbitLoop K a) :=
  bemc_bdEdgeMatch_iff_leftRegion_eq (mpl_orbitLoop K a) R hsupp hJfin













theorem bemc_orientation_selected_self {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc) = jec_leftRegion Vc :=
  bemc_orientation_selected Vc R hsupp (bemc_leftRegion_finite Vc R hsupp) (Or.inl rfl)





theorem bemc_bdEdgeMatch_self_collapses {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc) = jec_leftRegion Vc :=
  (bemc_bdEdgeMatch_iff_leftRegion_eq Vc R hsupp (bemc_leftRegion_finite Vc R hsupp)).mp
    (pbs_bdEdgeMatch_self Vc)












































end Lattice

end StatMech
