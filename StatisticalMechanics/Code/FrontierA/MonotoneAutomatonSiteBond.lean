/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Percolation.BurtonKeane

open MeasureTheory

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def siteToBond (eta : ConfigSpace (Site d)) :
    ConfigSpace (Sym2 (Site d)) :=
  Sym2.lift ⟨fun x y => eta x && eta y, fun _ _ => Bool.and_comm _ _⟩

@[simp] theorem siteToBond_mk (eta : ConfigSpace (Site d)) (x y : Site d) :
    siteToBond eta s(x, y) = (eta x && eta y) :=
  rfl



def siteOpenGraph (eta : ConfigSpace (Site d)) : SimpleGraph (Site d) where
  Adj x y := (hypercubicLattice d).Adj x y ∧ eta x = true ∧ eta y = true
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

@[simp] theorem siteOpenGraph_adj (eta : ConfigSpace (Site d)) (x y : Site d) :
    (siteOpenGraph eta).Adj x y ↔
      (hypercubicLattice d).Adj x y ∧ eta x = true ∧ eta y = true :=
  Iff.rfl


theorem openSubgraph_siteToBond (eta : ConfigSpace (Site d)) :
    openSubgraph d (siteToBond eta) = siteOpenGraph eta := by
  ext x y
  simp [siteOpenGraph, siteToBond, Bool.and_eq_true]



theorem connected_siteToBond_iff (eta : ConfigSpace (Site d)) (x y : Site d) :
    Connected d (siteToBond eta) x y ↔ (siteOpenGraph eta).Reachable x y := by
  rw [Connected, openSubgraph_siteToBond]


theorem siteToBond_mono {eta eta' : ConfigSpace (Site d)} (h : eta ≤ eta') :
    siteToBond eta ≤ siteToBond eta' := by
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [siteToBond_mk]
      cases hx : eta x <;> cases hy : eta y <;> simp
      have hx' : eta' x = true := by
        have := h x
        exact Bool.eq_true_of_true_le (by simpa [hx] using this)
      have hy' : eta' y = true := by
        have := h y
        exact Bool.eq_true_of_true_le (by simpa [hy] using this)
      simp [hx', hy']


theorem measurable_siteToBond :
    Measurable (siteToBond : ConfigSpace (Site d) →
      ConfigSpace (Sym2 (Site d))) := by
  rw [measurable_pi_iff]
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
      change Measurable (fun eta : ConfigSpace (Site d) => eta x && eta y)
      fun_prop


theorem siteToBond_shift (g : Multiplicative (Site d))
    (eta : ConfigSpace (Site d)) :
    siteToBond (shift g eta) = shift g (siteToBond eta) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp [siteToBond, shift, smul_sym2_mk]



theorem infiniteClusters_siteToBond (eta : ConfigSpace (Site d)) :
    infiniteClusters d (siteToBond eta) =
      {C : Set (Site d) | C.Infinite ∧
        ∃ x, C = {y | (siteOpenGraph eta).Reachable x y}} := by
  ext C
  simp only [infiniteClusters, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hC, x, rfl⟩
    refine ⟨hC, x, ?_⟩
    ext y
    exact connected_siteToBond_iff eta x y
  · rintro ⟨hC, x, rfl⟩
    refine ⟨hC, x, ?_⟩
    ext y
    exact (connected_siteToBond_iff eta x y).symm



theorem numInfiniteClusters_siteToBond (eta : ConfigSpace (Site d)) :
    numInfiniteClusters d (siteToBond eta) =
      ({C : Set (Site d) | C.Infinite ∧
        ∃ x, C = {y | (siteOpenGraph eta).Reachable x y}}).encard := by
  unfold numInfiniteClusters
  rw [infiniteClusters_siteToBond]


theorem siteToBond_isTranslationInvariant
    (mu : Measure (ConfigSpace (Site d)))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (Measure.map siteToBond mu) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  rw [Measure.map_map (measurable_shift g) measurable_siteToBond]
  have hcomp :
      (shift g : ConfigSpace (Sym2 (Site d)) → _) ∘ siteToBond =
        siteToBond ∘ (shift g : ConfigSpace (Site d) → _) := by
    funext eta
    exact (siteToBond_shift g eta).symm
  rw [hcomp, ← Measure.map_map measurable_siteToBond (measurable_shift g),
    (hinv g).map_eq]


theorem siteToBond_isErgodic
    (mu : Measure (ConfigSpace (Site d)))
    (herg : IsErgodic (G := Multiplicative (Site d)) mu) :
    IsErgodic (G := Multiplicative (Site d))
      (Measure.map siteToBond mu) := by
  refine ⟨siteToBond_isTranslationInvariant mu herg.1, ?_⟩
  intro s hs hinv
  have hpreMeas : MeasurableSet (siteToBond ⁻¹' s) :=
    measurable_siteToBond hs
  have hpreInv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Site d) → _) ⁻¹' (siteToBond ⁻¹' s) =
        siteToBond ⁻¹' s := by
    intro g
    ext eta
    simp only [Set.mem_preimage]
    rw [siteToBond_shift, ← Set.mem_preimage, hinv g]
  rcases herg.2 _ hpreMeas hpreInv with hzero | hfull
  · left
    rwa [Measure.map_apply measurable_siteToBond hs]
  · right
    rw [Measure.map_apply measurable_siteToBond hs, hfull,
      Measure.map_apply measurable_siteToBond MeasurableSet.univ]
    rfl

end StatMech.FrontierA
