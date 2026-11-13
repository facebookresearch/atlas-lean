/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.FK.InducedBC
import Code.FK.WiredDomChain
import Code.FK.Limits
import Code.FK.InfiniteVolume
import Code.Foundations.MonotoneLimit
import Code.Foundations.WeakConvergence

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}
















noncomputable def inducedWiringFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    SimpleGraph (boxVerts d n) where
  Adj x y := x ≠ y ∧ (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)
  symm := by
    rintro x y ⟨hne, hreach⟩
    exact ⟨hne.symm, hreach.symm⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

noncomputable instance instDecidableRelInducedWiringFree (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : DecidableRel (inducedWiringFree d n ψ).Adj :=
  fun _ _ => Classical.dec _

theorem inducedWiringFree_adj (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (x y : boxVerts d n) :
    (inducedWiringFree d n ψ).Adj x y
      ↔ x ≠ y ∧ (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) :=
  Iff.rfl











theorem psiFreeGraph_eq_sup (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    openSub (boxGraph d (n+1)) (psiExt d n ψ ω)
      = innerImageGraph d n ω ⊔ outsideOpenGraph d n ψ := by
  ext x y
  rw [openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    by_cases hr : s(x, y) ∈ Set.range (innerEdge d n)
    · refine Or.inl ⟨hadj, ?_, hr⟩
      rw [← psiExt_eq_false_of_range d n ψ ω hr]; exact hopen
    · refine Or.inr ⟨hadj, ?_, hr⟩
      rwa [psiExt_eq_psi_of_not_range d n ψ ω hr] at hopen
  · rintro (⟨hadj, hopen, hr⟩ | ⟨hadj, hopen, hr⟩)
    · refine ⟨hadj, ?_⟩
      rwa [psiExt_eq_false_of_range d n ψ ω hr]
    · refine ⟨hadj, ?_⟩
      rwa [psiExt_eq_psi_of_not_range d n ψ ω hr]










noncomputable abbrev fullGraphFree (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : SimpleGraph (boxVerts d (n+1)) :=
  innerImageGraph d n ω ⊔ outsideOpenGraph d n ψ




noncomputable abbrev innerGraphFree (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : SimpleGraph (boxVerts d n) :=
  openSub (boxGraph d n) ω ⊔ inducedWiringFree d n ψ

noncomputable instance instDecidableRelInnerGraphFree (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    DecidableRel (innerGraphFree d n ω ψ).Adj :=
  fun _ _ => Classical.dec _


theorem outsideOpenGraph_le_fullGraphFree (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    outsideOpenGraph d n ψ ≤ fullGraphFree d n ω ψ := le_sup_right



theorem innerGraphFree_reachable_of_outsideReachable (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n}
    (h : (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraphFree d n ω ψ).Reachable x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl x
  · have hadj : (inducedWiringFree d n ψ).Adj x y := ⟨hxy, h⟩
    exact (le_sup_right (a := openSub (boxGraph d n) ω) hadj).reachable





theorem fullGraphFree_reachable_of_innerGraphFree (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n} (h : (innerGraphFree d n ω ψ).Reachable x y) :
    (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u w _ hadj ih =>
      refine ih.trans ?_
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with hopen | hwire
      · exact ((innerImageGraph_adj_boxVertIncl d n ω u w).mpr hopen).reachable.mono
          le_sup_left
      · exact ((hwire.2.mono (outsideOpenGraph_le_fullGraphFree d n ω ψ)))




theorem innerGraphFree_reachable_of_fullGraphFree (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n}
    (h : (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraphFree d n ω ψ).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (fullGraphFree d n ω ψ).Adj (boxVertIncl d n x) w →
        ∃ x₀ : boxVerts d n, (innerGraphFree d n ω ψ).Reachable x x₀
          ∧ (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x₀) w by
    obtain ⟨x₀, hKx₀, hout⟩ := H (boxVertIncl d n y) h
    exact hKx₀.trans (innerGraphFree_reachable_of_outsideReachable d n ω ψ hout)
  intro w hw
  induction hw with
  | refl => exact ⟨x, SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl _⟩
  | @tail u w _ hadj ih =>
      obtain ⟨x₀, hKx₀, hout⟩ := ih
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with himg | hoadj
      · obtain ⟨hu, hw⟩ := innerImageGraph_adj_inner d n ω himg
        obtain ⟨u', rfl⟩ := (isInnerVert_iff_range d n u).mp hu
        obtain ⟨w', rfl⟩ := (isInnerVert_iff_range d n w).mp hw
        have hKu' : (innerGraphFree d n ω ψ).Reachable x₀ u' :=
          innerGraphFree_reachable_of_outsideReachable d n ω ψ hout
        have hstep : (innerGraphFree d n ω ψ).Adj u' w' :=
          le_sup_left (b := inducedWiringFree d n ψ)
            ((innerImageGraph_adj_boxVertIncl d n ω u' w').mp himg)
        have hKw' : (innerGraphFree d n ω ψ).Reachable x w' :=
          ((hKx₀.trans hKu').trans hstep.reachable)
        exact ⟨w', hKw', SimpleGraph.Reachable.refl _⟩
      · exact ⟨x₀, hKx₀, hout.trans hoadj.reachable⟩






theorem fullGraphFree_adj_of_outside (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {u w : boxVerts d (n+1)}
    (hu : ¬ IsInnerVert d n u) (h : (fullGraphFree d n ω ψ).Adj u w) :
    (outsideOpenGraph d n ψ).Adj u w := by
  rw [SimpleGraph.sup_adj] at h
  rcases h with himg | hout
  · exact absurd (innerImageGraph_adj_inner d n ω himg).1 hu
  · exact hout


def OutsideOnlyFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (u : boxVerts d (n+1)) : Prop :=
  ∀ v, (outsideOpenGraph d n ψ).Reachable u v → ¬ IsInnerVert d n v

theorem outsideOnlyFree_self_not_inner (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {u : boxVerts d (n+1)}
    (hu : OutsideOnlyFree d n ψ u) : ¬ IsInnerVert d n u :=
  hu u (SimpleGraph.Reachable.refl u)

theorem outsideOnlyFree_of_reachable (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {u v : boxVerts d (n+1)} (hu : OutsideOnlyFree d n ψ u)
    (h : (outsideOpenGraph d n ψ).Reachable u v) : OutsideOnlyFree d n ψ v :=
  fun w hw => hu w (h.trans hw)


theorem outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {u w : boxVerts d (n+1)} (hu : OutsideOnlyFree d n ψ u)
    (h : (fullGraphFree d n ω ψ).Reachable u w) :
    (outsideOpenGraph d n ψ).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b hua hadj ih =>
      have ha_out : (outsideOpenGraph d n ψ).Reachable u a := ih
      have ha_not_inner : ¬ IsInnerVert d n a := hu a ha_out
      exact ha_out.trans (fullGraphFree_adj_of_outside d n ω ψ ha_not_inner hadj).reachable


noncomputable def IsOutsideOnlyFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    (outsideOpenGraph d n ψ).ConnectedComponent → Prop :=
  ConnectedComponent.lift (OutsideOnlyFree d n ψ)
    (fun a b p _ => propext ⟨fun h => outsideOnlyFree_of_reachable d n ψ h p.reachable,
      fun h => outsideOnlyFree_of_reachable d n ψ h p.reachable.symm⟩)

@[simp] theorem isOutsideOnlyFree_mk (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (v : boxVerts d (n+1)) :
    IsOutsideOnlyFree d n ψ ((outsideOpenGraph d n ψ).connectedComponentMk v)
      ↔ OutsideOnlyFree d n ψ v :=
  Iff.rfl



def OutsideOnlyCompFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : Type :=
  {c : (outsideOpenGraph d n ψ).ConnectedComponent // IsOutsideOnlyFree d n ψ c}

noncomputable instance instFintypeOutsideOnlyCompFree (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : Fintype (OutsideOnlyCompFree d n ψ) := by
  classical
  unfold OutsideOnlyCompFree; infer_instance




noncomputable def fullComponentMapFree (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    (innerGraphFree d n ω ψ).ConnectedComponent ⊕ OutsideOnlyCompFree d n ψ →
      (fullGraphFree d n ω ψ).ConnectedComponent
  | Sum.inl c => c.lift (fun x => (fullGraphFree d n ω ψ).connectedComponentMk (boxVertIncl d n x))
      (fun a b p _ => ConnectedComponent.sound
        (fullGraphFree_reachable_of_innerGraphFree d n ω ψ p.reachable))
  | Sum.inr c => c.1.lift (fun v => (fullGraphFree d n ω ψ).connectedComponentMk v)
      (fun a b p _ => ConnectedComponent.sound
        (p.reachable.mono (outsideOpenGraph_le_fullGraphFree d n ω ψ)))

theorem fullComponentMapFree_inl_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (x : boxVerts d n) :
    fullComponentMapFree d n ω ψ (Sum.inl ((innerGraphFree d n ω ψ).connectedComponentMk x))
      = (fullGraphFree d n ω ψ).connectedComponentMk (boxVertIncl d n x) := rfl

theorem fullComponentMapFree_inr_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (v : boxVerts d (n+1))
    (hv : IsOutsideOnlyFree d n ψ ((outsideOpenGraph d n ψ).connectedComponentMk v)) :
    fullComponentMapFree d n ω ψ
        (Sum.inr ⟨(outsideOpenGraph d n ψ).connectedComponentMk v, hv⟩)
      = (fullGraphFree d n ω ψ).connectedComponentMk v := rfl


theorem fullComponentMapFree_injective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    Function.Injective (fullComponentMapFree d n ω ψ) := by
  rintro (c₁ | ⟨c₁, hc₁⟩) (c₂ | ⟨c₂, hc₂⟩) h
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMapFree_inl_mk, fullComponentMapFree_inl_mk, ConnectedComponent.eq] at h
    exact congrArg Sum.inl
      (ConnectedComponent.eq.mpr (innerGraphFree_reachable_of_fullGraphFree d n ω ψ h))
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMapFree_inl_mk, fullComponentMapFree_inr_mk] at h
    have hreach : (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x₁) v₂ :=
      ConnectedComponent.eq.mp h
    have hv₂ : OutsideOnlyFree d n ψ v₂ := (isOutsideOnlyFree_mk d n ψ v₂).mp hc₂
    have : (outsideOpenGraph d n ψ).Reachable v₂ (boxVertIncl d n x₁) :=
      outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly d n ω ψ hv₂ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₁) (hv₂ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMapFree_inl_mk, fullComponentMapFree_inr_mk] at h
    have hreach : (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x₂) v₁ :=
      ConnectedComponent.eq.mp h.symm
    have hv₁ : OutsideOnlyFree d n ψ v₁ := (isOutsideOnlyFree_mk d n ψ v₁).mp hc₁
    have : (outsideOpenGraph d n ψ).Reachable v₁ (boxVertIncl d n x₂) :=
      outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly d n ω ψ hv₁ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₂) (hv₁ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMapFree_inr_mk, fullComponentMapFree_inr_mk] at h
    have hreach : (fullGraphFree d n ω ψ).Reachable v₁ v₂ := ConnectedComponent.eq.mp h
    have hv₁ : OutsideOnlyFree d n ψ v₁ := (isOutsideOnlyFree_mk d n ψ v₁).mp hc₁
    have hout : (outsideOpenGraph d n ψ).Reachable v₁ v₂ :=
      outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly d n ω ψ hv₁ hreach
    refine congrArg Sum.inr (Subtype.ext ?_)
    exact ConnectedComponent.sound hout


theorem fullComponentMapFree_surjective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    Function.Surjective (fullComponentMapFree d n ω ψ) := by
  classical
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : ∃ w, IsInnerVert d n w ∧ (fullGraphFree d n ω ψ).Reachable u w
  · obtain ⟨w, hw, hreach⟩ := hu
    obtain ⟨x, rfl⟩ := (isInnerVert_iff_range d n w).mp hw
    refine ⟨Sum.inl ((innerGraphFree d n ω ψ).connectedComponentMk x), ?_⟩
    rw [fullComponentMapFree_inl_mk]
    exact ConnectedComponent.sound hreach.symm
  · have hOut : OutsideOnlyFree d n ψ u := by
      intro v hv hinner
      exact hu ⟨v, hinner, hv.mono (outsideOpenGraph_le_fullGraphFree d n ω ψ)⟩
    refine ⟨Sum.inr ⟨(outsideOpenGraph d n ψ).connectedComponentMk u,
      (isOutsideOnlyFree_mk d n ψ u).mpr hOut⟩, ?_⟩
    rw [fullComponentMapFree_inr_mk]




noncomputable def fullComponentEquivFree (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    (innerGraphFree d n ω ψ).ConnectedComponent ⊕ OutsideOnlyCompFree d n ψ ≃
      (fullGraphFree d n ω ψ).ConnectedComponent :=
  Equiv.ofBijective (fullComponentMapFree d n ω ψ)
    ⟨fullComponentMapFree_injective d n ω ψ, fullComponentMapFree_surjective d n ω ψ⟩





noncomputable def outsideShiftFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : ℕ :=
  Nat.card (OutsideOnlyCompFree d n ψ)










theorem numClusters_psiExt_free (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    numClusters (boxGraph d (n+1)) (psiExt d n ψ ω)
      = numClustersBC (boxGraph d n) (inducedWiringFree d n ψ) ω + outsideShiftFree d n ψ := by
  have hfull : numClusters (boxGraph d (n+1)) (psiExt d n ψ ω)
      = Nat.card (fullGraphFree d n ω ψ).ConnectedComponent := by
    rw [← numClustersBC_bot, numClustersBC, sup_bot_eq, psiFreeGraph_eq_sup]
  have hinner : numClustersBC (boxGraph d n) (inducedWiringFree d n ψ) ω
      = Nat.card (innerGraphFree d n ω ψ).ConnectedComponent := by
    rw [numClustersBC]
  rw [hfull, hinner, outsideShiftFree,
    ← Nat.card_congr (fullComponentEquivFree d n ω ψ), Nat.card_sum]







noncomputable def psiShiftFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (p q : ℝ) : ℝ :=
  psiEdgeFactor d n ψ p * q ^ outsideShiftFree d n ψ

theorem psiShiftFree_pos {d n : ℕ} {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : 0 < psiShiftFree d n ψ p q :=
  mul_pos (psiEdgeFactor_pos hp hp1) (pow_pos hq _)










theorem fkWeight_psiExt_free (d n : ℕ) {p q : ℝ} (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    fkWeight (boxGraph d (n+1)) p q (psiExt d n ψ ω)
      = bcWeight (boxGraph d n) (inducedWiringFree d n ψ) p q ω * psiShiftFree d n ψ p q := by
  rw [fkWeight, numClusters_psiExt_free, edgeProduct_psiExt, bcWeight, psiShiftFree, pow_add]
  ring





theorem inducedFkZ_innerEdgeFinset_psi_free (d n : ℕ) {p q : ℝ}
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    inducedFkZ (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ
      = bcZ (boxGraph d n) (inducedWiringFree d n ψ) p q * psiShiftFree d n ψ p q := by
  rw [inducedFkZ, condFibre_eq_image_psiExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this),
    bcZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => fkWeight_psiExt_free d n ψ ω)













theorem condFkProb_psiExt_eq_bcProb_free (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ (psiExt d n ψ ω)
      = bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
  rw [condFkProb_eq_inducedFkProb (boxGraph d (n+1)) hp hp1 hq, inducedFkProb,
    fkWeight_psiExt_free, inducedFkZ_innerEdgeFinset_psi_free, bcProb,
    mul_div_mul_right _ _ (psiShiftFree_pos hp hp1 hq).ne']











theorem sum_fibreMass_eq_one_free (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
          fkProb (boxGraph d (n+1)) p q σ) = 1 := by
  classical
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [show (∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre F ψ, fkProb G p q σ))
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ Finset.univ.filter (fun ρ => outProj d n ρ = ψ), fkProb G p q σ) from ?_]
  · rw [Finset.sum_fiberwise_of_maps_to
        (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
    exact fkProb_sum_eq_one G hp hp1 hq
  · apply Finset.sum_congr rfl
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    rw [filter_outProj_eq_condFibre n ψ hψ.2]




theorem fkProb_eq_fibreMass_mul_condFkProb (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    fkProb (boxGraph d (n+1)) p q ω
      = (∑ ρ ∈ condFibre (innerEdgeFinset d n) ω, fkProb (boxGraph d (n+1)) p q ρ)
          * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ω ω := by
  set G := boxGraph d (n+1)
  set F := innerEdgeFinset d n
  unfold condFkProb
  have hpos : 0 < ∑ ρ ∈ condFibre F ω, fkProb G p q ρ :=
    Finset.sum_pos (fun ρ _ => fkProb_pos G hp hp1 hq ρ) ⟨ω, self_mem_condFibre F ω⟩
  rw [mul_div_cancel₀ _ hpos.ne']





theorem condFkProb_congr_dom_free (n : ℕ) {p q : ℝ}
    (ψ ψ' ω : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (h : AgreesOff (innerEdgeFinset d n) ψ ψ') :
    condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ω
      = condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ' ω := by
  unfold condFkProb
  have hfib : condFibre (innerEdgeFinset d n) ψ = condFibre (innerEdgeFinset d n) ψ' := by
    ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr h]
  rw [hfib]





theorem freeSucc_fkProb_decompose (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * fkProb (boxGraph d (n+1)) p q ρ)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            fkProb (boxGraph d (n+1)) p q σ)
          * (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ, B.indicator (fun _ => (1:ℝ)) ρ
              * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ) := by
  classical
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := outProj d n) (t := Finset.univ.filter (fun ψ => outProj d n ψ = ψ))
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.mem_filter] at hψ
  rw [filter_outProj_eq_condFibre n ψ hψ.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hfk := fkProb_eq_fibreMass_mul_condFkProb n hp hp1 hq ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hfk
  have hcc : condFkProb G p q F ρ ρ = condFkProb G p q F ψ ρ :=
    condFkProb_congr_dom_free n ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hfk
  rw [hfk]; ring














theorem condFkProb_psiExt_sum_eq_inducedBox_free (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))) :
    (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ, B.indicator (fun _ => (1:ℝ)) ρ *
        condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω
            * bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
  classical
  rw [condFibre_eq_image_psiExt]
  rw [Finset.sum_image (fun a _ b _ h => by
    have := congrArg (innerRestrict d n) h
    rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [condFkProb_psiExt_eq_bcProb_free d n hp hp1 hq ψ ω]
  have hind : B.indicator (fun _ => (1:ℝ)) (psiExt d n ψ ω)
      = (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω := by
    by_cases hω : psiExt d n ψ ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]
  rw [hind]












theorem fkProb_le_inducedFree (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * bcProb (boxGraph d n) (inducedWiringFree d n ψ) p q ω := by
  have hbot : (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      = ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * bcProb (boxGraph d n) (⊥ : SimpleGraph (boxVerts d n)) p q ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    congr 1
    unfold fkProb bcProb fkZ bcZ
    rw [fkWeight, bcWeight, numClustersBC_bot]
    congr 1
    exact Finset.sum_congr rfl (fun ω _ => by rw [fkWeight, bcWeight, numClustersBC_bot])
  rw [hbot]
  exact bcProb_mono_bc (boxGraph d n) (⊥ : SimpleGraph (boxVerts d n))
    (inducedWiringFree d n ψ) bot_le hp hp1 hq hA₀












theorem fkProb_le_condFkProb_innerRestrict_free (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ ∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ,
          (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
            * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [condFkProb_psiExt_sum_eq_inducedBox_free d n hp hp1 hq0 ψ (innerRestrict d n ⁻¹' A₀)]
  have hpre : psiExt d n ψ ⁻¹' (innerRestrict d n ⁻¹' A₀) = A₀ := by
    ext ω
    simp only [Set.mem_preimage, innerRestrict_psiExt]
  rw [hpre]
  exact fkProb_le_inducedFree d n hp hp1 hq ψ hA₀













theorem freeSucc_fkProb_innerEvent_le (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ ∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
          * fkProb (boxGraph d (n+1)) p q ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p q ω with hc
  rw [freeSucc_fkProb_decompose n hp hp1 hq0 (innerRestrict d n ⁻¹' A₀)]
  calc c = c * 1 := (mul_one c).symm
    _ = c * ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ) := by
          rw [sum_fibreMass_eq_one_free n hp hp1 hq0]
    _ = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ) * c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ψ _ => mul_comm _ _)
    _ ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, fkProb (boxGraph d (n+1)) p q σ)
            * (∑ ρ ∈ condFibre (innerEdgeFinset d n) ψ,
                (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
                  * condFkProb (boxGraph d (n+1)) p q (innerEdgeFinset d n) ψ ρ) := by
          apply Finset.sum_le_sum
          intro ψ _
          apply mul_le_mul_of_nonneg_left
            (fkProb_le_condFkProb_innerRestrict_free d n hp hp1 hq ψ hA₀)
          exact Finset.sum_nonneg (fun σ _ => (fkProb_pos (boxGraph d (n+1)) hp hp1 hq0 σ).le)








theorem freeFiniteMeasure_real_boxRestrictEvent (m : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (freeFiniteMeasure d m hp hp1 hq
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d m) p q ω := by
  have hf : (freeFiniteMeasure d m hp hp1 hq : Measure _).real (boxRestrict d m ⁻¹' S)
      = ((fkPMF (boxGraph d m) hp hp1 hq).toMeasure
          (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext ω
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hf, hpre, fkPMF_toMeasure_toReal d m hp hp1 hq]







theorem freeFiniteMeasure_succ_real_innerRestrictEvent (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n))))
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (freeFiniteMeasure d (n+1) hp hp1 hq
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n+1))),
          (innerRestrict d n ⁻¹' S).indicator (fun _ => (1:ℝ)) ρ
            * fkProb (boxGraph d (n+1)) p q ρ := by
  have hf : (freeFiniteMeasure d (n+1) hp hp1 hq : Measure _).real (boxRestrict d n ⁻¹' S)
      = ((fkPMF (boxGraph d (n+1)) hp hp1 hq).toMeasure
          (extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S))).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n+1)) hmeas]
  have hpre : extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S) = innerRestrict d n ⁻¹' S := by
    ext ρ
    simp only [Set.mem_preimage, boxRestrict_extendEdge_succ]
  rw [hf, hpre, fkPMF_toMeasure_toReal d (n+1) hp hp1 hq]















theorem freeFiniteMeasure_smallerBox_le_succ (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (∑ ω, S.indicator (fun _ => (1:ℝ)) ω * fkProb (boxGraph d n) p 2 ω)
      ≤ (freeFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
  rw [freeFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 (by norm_num) S hmeas]
  exact freeSucc_fkProb_innerEvent_le n hp hp1 (by norm_num) hS










theorem fkFreeLimit_isIncreasing_preimage (N : ℕ)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    IsIncreasing (boxRestrict d N ⁻¹' S) :=
  fun _ _ hab ha => hS (monotone_boxRestrict d N hab) ha


theorem fkFreeLimit_isClopen_preimage (N : ℕ) (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    IsClopen (boxRestrict d N ⁻¹' S) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩ (continuous_boxRestrict d N)


theorem fkFreeLimit_measurableSet_preimage (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    MeasurableSet (boxRestrict d N ⁻¹' S) :=
  (fkFreeLimit_isClopen_preimage N S).isOpen.measurableSet






















theorem fkFreeLimit_le_succ (N m : ℕ) (hNm : N ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (freeFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq, freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) T hmeas]
  exact freeFiniteMeasure_smallerBox_le_succ m hp hp1 hTinc hmeas





theorem fkFreeLimit_monotone (N : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Monotone (fun k => (freeFiniteMeasure d (N+k) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := fkFreeLimit_le_succ N (N+k) (Nat.le_add_right N k) hp hp1 hS
  rw [show N + (k+1) = (N+k)+1 from by ring]
  exact h











noncomputable def fkFreeLimitValue (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) : ℝ :=
  ⨆ k, (freeFiniteMeasure d (N+k) hp hp1 (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)


theorem freeFiniteMeasure_real_le_one (m : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 (Site d)))) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real A ≤ 1 := by
  have := (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)).2
  exact measureReal_le_one














theorem fk_free_limit_exists (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 (fkFreeLimitValue N hp hp1 S)) := by
  set f := fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) with hf
  have hmono := fkFreeLimit_monotone N hp hp1 hS
  have hbdd : BddAbove (Set.range (fun k => f (N+k))) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact freeFiniteMeasure_real_le_one (N+k) hp hp1 _⟩
  
  have hshift : Tendsto (fun k => f (N+k)) atTop (𝓝 (fkFreeLimitValue N hp hp1 S)) :=
    tendsto_atTop_ciSup hmono hbdd
  
  have key : Tendsto (fun k => f (k+N)) atTop (𝓝 (fkFreeLimitValue N hp hp1 S)) := by
    have hcomm : (fun k => f (k+N)) = (fun k => f (N+k)) := by funext k; rw [Nat.add_comm]
    rw [hcomm]; exact hshift
  exact (Filter.tendsto_add_atTop_iff_nat N).mp key










theorem fk_free_le_limit (N m : ℕ) (hNm : N ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ fkFreeLimitValue N hp hp1 S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNm
  have hbdd : BddAbove (Set.range (fun k => (freeFiniteMeasure d (N+k) hp hp1
        (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d N ⁻¹' S))) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact freeFiniteMeasure_real_le_one (N+k) hp hp1 _⟩
  exact le_ciSup hbdd k






















theorem fkFreeLimit_freeInfiniteVolume_eq (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      = fkFreeLimitValue N hp hp1 S := by
  obtain ⟨ψ, hψ, hconv⟩ := freeInfiniteVolume_isLimit d hp hp1 (by norm_num : (0:ℝ) < 2)
  have hclopen := fkFreeLimit_isClopen_preimage N S
  
  have hport := hconv.tendsto_real_of_isClopen (A := boxRestrict d N ⁻¹' S) hclopen
  
  have hsub := (fk_free_limit_exists N hp hp1 hS).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hport hsub

















theorem fk_free_infinite_measure (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) := by
  rw [fkFreeLimit_freeInfiniteVolume_eq N hp hp1 hS]
  exact fk_free_limit_exists N hp hp1 hS

end FK

end StatMech
