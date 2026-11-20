/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.FK.WiredDominationInner
import Code.FK.MonoBC
import Code.FK.DomainMarkov
import Code.FK.IvProperties
import Code.FK.LimitCommutation
import Code.FK.MonotoneVolumeLimit

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.Lattice








variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin] [Fintype Vout] [DecidableEq Vout]
variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
variable (ιV : Vin → Vout)


def ocd_IsInnerVert (v : Vout) : Prop := ∃ x : Vin, ιV x = v


def ocd_innerEdge (e : Sym2 Vin) : Sym2 Vout := Sym2.map ιV e

theorem ocd_innerEdge_injective (hι : Function.Injective ιV) :
    Function.Injective (ocd_innerEdge ιV) :=
  Sym2.map.injective hι

theorem ocd_innerEdge_mk (x y : Vin) :
    ocd_innerEdge ιV s(x, y) = s(ιV x, ιV y) := by
  rw [ocd_innerEdge, Sym2.map_mk]

theorem ocd_isInnerVert_iff_range (v : Vout) :
    ocd_IsInnerVert ιV v ↔ ∃ x, ιV x = v := Iff.rfl









def ocd_AdjMatch : Prop := ∀ x y, Gin.Adj x y ↔ Gout.Adj (ιV x) (ιV y)





noncomputable def ocd_psiExt (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    ConfigSpace (Sym2 Vout) :=
  fun e => if h : e ∈ Set.range (ocd_innerEdge ιV) then ω h.choose else ψ e


noncomputable def ocd_innerRestrict (ρ : ConfigSpace (Sym2 Vout)) : ConfigSpace (Sym2 Vin) :=
  fun e => ρ (ocd_innerEdge ιV e)


noncomputable def ocd_innerEdgeFinset : Finset (Sym2 Vout) :=
  Finset.univ.image (ocd_innerEdge ιV)

variable {Gin Gout ιV}

theorem ocd_mem_innerEdgeFinset {e : Sym2 Vout} :
    e ∈ ocd_innerEdgeFinset (Vin := Vin) ιV ↔ e ∈ Set.range (ocd_innerEdge ιV) := by
  unfold ocd_innerEdgeFinset
  rw [Finset.mem_image]
  simp only [Finset.mem_univ, true_and, Set.mem_range]

theorem ocd_psiExt_innerEdge (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) (e : Sym2 Vin) :
    ocd_psiExt ιV ψ ω (ocd_innerEdge ιV e) = ω e := by
  unfold ocd_psiExt
  have hmem : ocd_innerEdge ιV e ∈ Set.range (ocd_innerEdge ιV) := ⟨e, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact ocd_innerEdge_injective ιV hι hmem.choose_spec

theorem ocd_psiExt_eq_psi_of_not_range (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) {e : Sym2 Vout}
    (he : e ∉ Set.range (ocd_innerEdge ιV)) : ocd_psiExt ιV ψ ω e = ψ e := by
  unfold ocd_psiExt; rw [dif_neg he]

theorem ocd_psiExt_innerEdge_pair (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) (x y : Vin) :
    ocd_psiExt ιV ψ ω s(ιV x, ιV y) = ω s(x, y) := by
  have h : s(ιV x, ιV y) = ocd_innerEdge ιV s(x, y) := (ocd_innerEdge_mk ιV x y).symm
  rw [h, ocd_psiExt_innerEdge hι]



@[simp] theorem ocd_innerRestrict_psiExt (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) : ocd_innerRestrict ιV (ocd_psiExt ιV ψ ω) = ω := by
  funext e; rw [ocd_innerRestrict, ocd_psiExt_innerEdge hι]

theorem ocd_agreesOff_psiExt (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    AgreesOff (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ (ocd_psiExt ιV ψ ω) := by
  intro e he
  rw [ocd_mem_innerEdgeFinset] at he
  exact ocd_psiExt_eq_psi_of_not_range ψ ω he

theorem ocd_psiExt_innerRestrict_of_agreesOff (hι : Function.Injective ιV)
    {ψ ρ : ConfigSpace (Sym2 Vout)}
    (hρ : AgreesOff (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) :
    ocd_psiExt ιV ψ (ocd_innerRestrict ιV ρ) = ρ := by
  funext e
  unfold ocd_psiExt
  split
  · rename_i hmem
    show ocd_innerRestrict ιV ρ hmem.choose = ρ e
    rw [ocd_innerRestrict, hmem.choose_spec]
  · rename_i hmem
    have : e ∉ ocd_innerEdgeFinset (Vin := Vin) ιV := by rw [ocd_mem_innerEdgeFinset]; exact hmem
    exact (hρ e this).symm

theorem ocd_condFibre_eq_image_psiExt (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout)) :
    condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ
      = Finset.univ.image (ocd_psiExt ιV ψ) := by
  ext ρ
  rw [mem_condFibre, Finset.mem_image]
  constructor
  · intro hρ
    exact ⟨ocd_innerRestrict ιV ρ, Finset.mem_univ _,
      ocd_psiExt_innerRestrict_of_agreesOff hι hρ⟩
  · rintro ⟨ω, _, rfl⟩
    exact ocd_agreesOff_psiExt ψ ω









variable (Gin Gout ιV)

variable (bdryOut : Vout → Prop) [DecidablePred bdryOut]


noncomputable def ocd_outsideOpenGraph (ψ : ConfigSpace (Sym2 Vout)) : SimpleGraph Vout where
  Adj x y := Gout.Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (ocd_innerEdge ιV)
  symm := by
    rintro x y ⟨hadj, hopen, hrange⟩
    refine ⟨hadj.symm, ?_, ?_⟩ <;> rw [Sym2.eq_swap] <;> assumption
  loopless := ⟨by rintro x ⟨hadj, _, _⟩; exact hadj.ne rfl⟩

noncomputable instance : DecidableRel (ocd_outsideOpenGraph Gout ιV ψ).Adj := fun _ _ => Classical.dec _


noncomputable def ocd_outsideGraph (ψ : ConfigSpace (Sym2 Vout)) : SimpleGraph Vout :=
  ocd_outsideOpenGraph Gout ιV ψ ⊔ StatMech.Lattice.boundaryCliqueGraph bdryOut

noncomputable instance : DecidableRel (ocd_outsideGraph Gout ιV bdryOut ψ).Adj :=
  fun _ _ => Classical.dec _

theorem ocd_outsideGraph_adj (ψ : ConfigSpace (Sym2 Vout)) (x y : Vout) :
    (ocd_outsideGraph Gout ιV bdryOut ψ).Adj x y
      ↔ (Gout.Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (ocd_innerEdge ιV))
        ∨ (x ≠ y ∧ bdryOut x ∧ bdryOut y) := by
  rw [ocd_outsideGraph, SimpleGraph.sup_adj, StatMech.Lattice.boundaryCliqueGraph_adj]
  exact Iff.rfl



noncomputable def ocd_inducedWiring (ψ : ConfigSpace (Sym2 Vout)) : SimpleGraph Vin where
  Adj x y := x ≠ y ∧ (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x) (ιV y)
  symm := by
    rintro x y ⟨hne, hreach⟩
    exact ⟨hne.symm, hreach.symm⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

noncomputable instance : DecidableRel (ocd_inducedWiring Gout ιV bdryOut ψ).Adj :=
  fun _ _ => Classical.dec _

theorem ocd_inducedWiring_adj (ψ : ConfigSpace (Sym2 Vout)) (x y : Vin) :
    (ocd_inducedWiring Gout ιV bdryOut ψ).Adj x y
      ↔ x ≠ y ∧ (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x) (ιV y) :=
  Iff.rfl


noncomputable def ocd_innerImageGraph (ω : ConfigSpace (Sym2 Vin)) : SimpleGraph Vout where
  Adj x y := Gout.Adj x y ∧ ocd_psiExt ιV (fun _ => false) ω s(x, y) = true
    ∧ s(x, y) ∈ Set.range (ocd_innerEdge ιV)
  symm := by
    rintro x y ⟨hadj, hopen, hrange⟩
    refine ⟨hadj.symm, ?_, ?_⟩ <;> rw [Sym2.eq_swap] <;> assumption
  loopless := ⟨by rintro x ⟨hadj, _, _⟩; exact hadj.ne rfl⟩

noncomputable instance : DecidableRel (ocd_innerImageGraph Gout ιV ω).Adj := fun _ _ => Classical.dec _


noncomputable def ocd_innerGraph (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    SimpleGraph Vin :=
  openSub Gin ω ⊔ ocd_inducedWiring Gout ιV bdryOut ψ

noncomputable instance : DecidableRel (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Adj :=
  fun _ _ => Classical.dec _


noncomputable def ocd_fullGraph (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    SimpleGraph Vout :=
  openSub Gout (ocd_psiExt ιV ψ ω) ⊔ StatMech.Lattice.boundaryCliqueGraph bdryOut

noncomputable instance : DecidableRel (ocd_fullGraph Gout ιV bdryOut ω ψ).Adj :=
  fun _ _ => Classical.dec _

variable {Gin Gout ιV bdryOut}

theorem ocd_outsideGraph_le_fullGraph (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    ocd_outsideGraph Gout ιV bdryOut ψ ≤ ocd_fullGraph Gout ιV bdryOut ω ψ := by
  intro x y h
  rw [ocd_fullGraph, SimpleGraph.sup_adj]
  rw [ocd_outsideGraph, SimpleGraph.sup_adj] at h
  rcases h with ⟨hadj, hopen, hr⟩ | hclique
  · left
    rw [openSub_adj]
    exact ⟨hadj, by rw [ocd_psiExt_eq_psi_of_not_range ψ ω hr]; exact hopen⟩
  · exact Or.inr hclique


theorem ocd_psiExt_eq_false_of_range (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) {e : Sym2 Vout} (he : e ∈ Set.range (ocd_innerEdge ιV)) :
    ocd_psiExt ιV ψ ω e = ocd_psiExt ιV (fun _ => false) ω e := by
  obtain ⟨e', rfl⟩ := he
  rw [ocd_psiExt_innerEdge hι, ocd_psiExt_innerEdge hι]


theorem ocd_psiWiredGraph_eq_sup (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) :
    ocd_fullGraph Gout ιV bdryOut ω ψ
      = ocd_innerImageGraph Gout ιV ω ⊔ ocd_outsideGraph Gout ιV bdryOut ψ := by
  ext x y
  rw [ocd_fullGraph, SimpleGraph.sup_adj, openSub_adj, SimpleGraph.sup_adj, ocd_outsideGraph,
    SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hadj, hopen⟩ | hclique)
    · by_cases hr : s(x, y) ∈ Set.range (ocd_innerEdge ιV)
      · refine Or.inl ⟨hadj, ?_, hr⟩
        rw [← ocd_psiExt_eq_false_of_range hι ψ ω hr]; exact hopen
      · refine Or.inr (Or.inl ⟨hadj, ?_, hr⟩)
        rwa [ocd_psiExt_eq_psi_of_not_range ψ ω hr] at hopen
    · exact Or.inr (Or.inr hclique)
  · rintro (⟨hadj, hopen, hr⟩ | ⟨hadj, hopen, hr⟩ | hclique)
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [ocd_psiExt_eq_false_of_range hι ψ ω hr]
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [ocd_psiExt_eq_psi_of_not_range ψ ω hr]
    · exact Or.inr hclique




theorem ocd_innerImageGraph_adj_inner (hι : Function.Injective ιV) (ω : ConfigSpace (Sym2 Vin))
    {u v : Vout} (h : (ocd_innerImageGraph Gout ιV ω).Adj u v) :
    ocd_IsInnerVert ιV u ∧ ocd_IsInnerVert ιV v := by
  obtain ⟨_, _, hr⟩ := h
  obtain ⟨e, he⟩ := hr
  refine Sym2.inductionOn e (fun a b hab => ?_) he
  rw [ocd_innerEdge_mk, Sym2.eq_iff] at hab
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨a, h1⟩, ⟨b, h2⟩⟩
  · exact ⟨⟨b, h2⟩, ⟨a, h1⟩⟩


theorem ocd_innerImageGraph_adj_ιV (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (x y : Vin) :
    (ocd_innerImageGraph Gout ιV ω).Adj (ιV x) (ιV y) ↔ (openSub Gin ω).Adj x y := by
  have he : s(ιV x, ιV y) = ocd_innerEdge ιV s(x, y) := (ocd_innerEdge_mk ιV x y).symm
  constructor
  · rintro ⟨hadj, hopen, _⟩
    refine ⟨(hadjm x y).mpr hadj, ?_⟩
    rw [he, ocd_psiExt_innerEdge hι] at hopen; exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨(hadjm x y).mp hadj, ?_, ⟨s(x, y), he.symm⟩⟩
    rw [he, ocd_psiExt_innerEdge hι]; exact hopen

theorem ocd_innerGraph_reachable_of_outsideReachable (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {x y : Vin}
    (h : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x) (ιV y)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl x
  · have hadj : (ocd_inducedWiring Gout ιV bdryOut ψ).Adj x y := ⟨hxy, h⟩
    exact (le_sup_right (a := openSub Gin ω) hadj).reachable

theorem ocd_fullGraph_reachable_of_innerGraph (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {x y : Vin}
    (h : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y) :
    (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y) := by
  rw [ocd_psiWiredGraph_eq_sup hι]
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u w _ hadj ih =>
      refine ih.trans ?_
      rw [ocd_innerGraph, SimpleGraph.sup_adj] at hadj
      rcases hadj with hopen | hwire
      · exact ((ocd_innerImageGraph_adj_ιV hι hadjm ω u w).mpr hopen).reachable.mono le_sup_left
      · refine hwire.2.mono ?_
        intro a b hab
        rw [SimpleGraph.sup_adj]; right; exact hab

theorem ocd_innerGraph_reachable_of_fullGraph (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {x y : Vin}
    (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y := by
  rw [ocd_psiWiredGraph_eq_sup hι] at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : Vout,
      Relation.ReflTransGen (ocd_innerImageGraph Gout ιV ω ⊔ ocd_outsideGraph Gout ιV bdryOut ψ).Adj
        (ιV x) w →
        ∃ x₀ : Vin, (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x x₀
          ∧ (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x₀) w by
    obtain ⟨x₀, hKx₀, hout⟩ := H (ιV y) h
    exact hKx₀.trans (ocd_innerGraph_reachable_of_outsideReachable ω ψ hout)
  intro w hw
  induction hw with
  | refl => exact ⟨x, SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl _⟩
  | @tail u w _ hadj ih =>
      obtain ⟨x₀, hKx₀, hout⟩ := ih
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with himg | hoadj
      · obtain ⟨hu, hw⟩ := ocd_innerImageGraph_adj_inner hι ω himg
        obtain ⟨u', rfl⟩ := hu
        obtain ⟨w', rfl⟩ := hw
        have hKu' : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x₀ u' :=
          ocd_innerGraph_reachable_of_outsideReachable ω ψ hout
        have hstep : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Adj u' w' :=
          le_sup_left (b := ocd_inducedWiring Gout ιV bdryOut ψ)
            ((ocd_innerImageGraph_adj_ιV hι hadjm ω u' w').mp himg)
        have hKw' : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x w' :=
          ((hKx₀.trans hKu').trans hstep.reachable)
        exact ⟨w', hKw', SimpleGraph.Reachable.refl _⟩
      · exact ⟨x₀, hKx₀, hout.trans hoadj.reachable⟩

theorem ocd_fullGraph_reachable_ιV (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) (x y : Vin) :
    (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y)
      ↔ (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y :=
  ⟨ocd_innerGraph_reachable_of_fullGraph hι hadjm ω ψ,
    ocd_fullGraph_reachable_of_innerGraph hι hadjm ω ψ⟩


theorem ocd_fullGraph_adj_of_outside (hι : Function.Injective ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {u w : Vout}
    (hu : ¬ ocd_IsInnerVert ιV u) (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Adj u w) :
    (ocd_outsideGraph Gout ιV bdryOut ψ).Adj u w := by
  rw [ocd_psiWiredGraph_eq_sup hι, SimpleGraph.sup_adj] at h
  rcases h with himg | hout
  · exact absurd (ocd_innerImageGraph_adj_inner hι ω himg).1 hu
  · exact hout

variable (Gin Gout ιV bdryOut)


def ocd_OutsideOnly (ψ : ConfigSpace (Sym2 Vout)) (u : Vout) : Prop :=
  ∀ v, (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u v → ¬ ocd_IsInnerVert ιV v

variable {Gin Gout ιV bdryOut}

theorem ocd_outsideOnly_self_not_inner (ψ : ConfigSpace (Sym2 Vout)) {u : Vout}
    (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u) : ¬ ocd_IsInnerVert ιV u :=
  hu u (SimpleGraph.Reachable.refl u)

theorem ocd_outsideOnly_of_reachable (ψ : ConfigSpace (Sym2 Vout)) {u v : Vout}
    (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u)
    (h : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u v) :
    ocd_OutsideOnly Gout ιV bdryOut ψ v :=
  fun w hw => hu w (h.trans hw)

theorem ocd_outsideGraph_reachable_of_fullGraph_outsideOnly (hι : Function.Injective ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) {u w : Vout}
    (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u)
    (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable u w) :
    (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b hua hadj ih =>
      have ha_out : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u a := ih
      have ha_not_inner : ¬ ocd_IsInnerVert ιV a := hu a ha_out
      exact ha_out.trans (ocd_fullGraph_adj_of_outside hι ω ψ ha_not_inner hadj).reachable

variable (Gin Gout ιV bdryOut)


noncomputable def ocd_IsOutsideOnly (ψ : ConfigSpace (Sym2 Vout)) :
    (ocd_outsideGraph Gout ιV bdryOut ψ).ConnectedComponent → Prop :=
  ConnectedComponent.lift (ocd_OutsideOnly Gout ιV bdryOut ψ)
    (fun a b p _ => propext ⟨fun h => ocd_outsideOnly_of_reachable ψ h p.reachable,
      fun h => ocd_outsideOnly_of_reachable ψ h p.reachable.symm⟩)

variable {Gin Gout ιV bdryOut}

@[simp] theorem ocd_isOutsideOnly_mk (ψ : ConfigSpace (Sym2 Vout)) (v : Vout) :
    ocd_IsOutsideOnly Gout ιV bdryOut ψ
        ((ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v)
      ↔ ocd_OutsideOnly Gout ιV bdryOut ψ v :=
  Iff.rfl

variable (Gin Gout ιV bdryOut)


def ocd_OutsideOnlyComp (ψ : ConfigSpace (Sym2 Vout)) : Type _ :=
  {c : (ocd_outsideGraph Gout ιV bdryOut ψ).ConnectedComponent //
    ocd_IsOutsideOnly Gout ιV bdryOut ψ c}

noncomputable instance ocd_instFintypeOutsideOnlyComp (ψ : ConfigSpace (Sym2 Vout)) :
    Fintype (ocd_OutsideOnlyComp Gout ιV bdryOut ψ) := by
  classical
  unfold ocd_OutsideOnlyComp; infer_instance




noncomputable def ocd_fullComponentMap (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).ConnectedComponent ⊕
        ocd_OutsideOnlyComp Gout ιV bdryOut ψ →
      (ocd_fullGraph Gout ιV bdryOut ω ψ).ConnectedComponent
  | Sum.inl c => c.lift (fun x => (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk (ιV x))
      (fun a b p _ => ConnectedComponent.sound
        (ocd_fullGraph_reachable_of_innerGraph hι hadjm ω ψ p.reachable))
  | Sum.inr c => c.1.lift (fun v => (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk v)
      (fun a b p _ => ConnectedComponent.sound
        (p.reachable.mono (ocd_outsideGraph_le_fullGraph ω ψ)))

variable {Gin Gout ιV bdryOut}

theorem ocd_fullComponentMap_inl_mk (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) (x : Vin) :
    ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ
        (Sum.inl ((ocd_innerGraph Gin Gout ιV bdryOut ω ψ).connectedComponentMk x))
      = (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk (ιV x) := rfl

theorem ocd_fullComponentMap_inr_mk (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) (v : Vout)
    (hv : ocd_IsOutsideOnly Gout ιV bdryOut ψ
        ((ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v)) :
    ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ
        (Sum.inr ⟨(ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v, hv⟩)
      = (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk v := rfl

theorem ocd_fullComponentMap_injective (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    Function.Injective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ) := by
  rintro (c₁ | ⟨c₁, hc₁⟩) (c₂ | ⟨c₂, hc₂⟩) h
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [ocd_fullComponentMap_inl_mk, ocd_fullComponentMap_inl_mk, ConnectedComponent.eq] at h
    exact congrArg Sum.inl
      (ConnectedComponent.eq.mpr (ocd_innerGraph_reachable_of_fullGraph hι hadjm ω ψ h))
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [ocd_fullComponentMap_inl_mk, ocd_fullComponentMap_inr_mk] at h
    have hreach : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x₁) v₂ :=
      ConnectedComponent.eq.mp h
    have hv₂ : ocd_OutsideOnly Gout ιV bdryOut ψ v₂ := (ocd_isOutsideOnly_mk ψ v₂).mp hc₂
    have : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable v₂ (ιV x₁) :=
      ocd_outsideGraph_reachable_of_fullGraph_outsideOnly hι ω ψ hv₂ hreach.symm
    exact absurd ⟨x₁, rfl⟩ (hv₂ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [ocd_fullComponentMap_inl_mk, ocd_fullComponentMap_inr_mk] at h
    have hreach : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x₂) v₁ :=
      ConnectedComponent.eq.mp h.symm
    have hv₁ : ocd_OutsideOnly Gout ιV bdryOut ψ v₁ := (ocd_isOutsideOnly_mk ψ v₁).mp hc₁
    have : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable v₁ (ιV x₂) :=
      ocd_outsideGraph_reachable_of_fullGraph_outsideOnly hι ω ψ hv₁ hreach.symm
    exact absurd ⟨x₂, rfl⟩ (hv₁ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [ocd_fullComponentMap_inr_mk, ocd_fullComponentMap_inr_mk] at h
    have hreach : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable v₁ v₂ := ConnectedComponent.eq.mp h
    have hv₁ : ocd_OutsideOnly Gout ιV bdryOut ψ v₁ := (ocd_isOutsideOnly_mk ψ v₁).mp hc₁
    have hout : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable v₁ v₂ :=
      ocd_outsideGraph_reachable_of_fullGraph_outsideOnly hι ω ψ hv₁ hreach
    refine congrArg Sum.inr (Subtype.ext ?_)
    exact ConnectedComponent.sound hout

theorem ocd_fullComponentMap_surjective (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    Function.Surjective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ) := by
  classical
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : ∃ w, ocd_IsInnerVert ιV w ∧ (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable u w
  · obtain ⟨w, hw, hreach⟩ := hu
    obtain ⟨x, rfl⟩ := hw
    refine ⟨Sum.inl ((ocd_innerGraph Gin Gout ιV bdryOut ω ψ).connectedComponentMk x), ?_⟩
    rw [ocd_fullComponentMap_inl_mk]
    exact ConnectedComponent.sound hreach.symm
  · have hOut : ocd_OutsideOnly Gout ιV bdryOut ψ u := by
      intro v hv hinner
      exact hu ⟨v, hinner, hv.mono (ocd_outsideGraph_le_fullGraph ω ψ)⟩
    refine ⟨Sum.inr ⟨(ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk u,
      (ocd_isOutsideOnly_mk ψ u).mpr hOut⟩, ?_⟩
    rw [ocd_fullComponentMap_inr_mk]


noncomputable def ocd_fullComponentEquiv (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).ConnectedComponent ⊕
        ocd_OutsideOnlyComp Gout ιV bdryOut ψ ≃
      (ocd_fullGraph Gout ιV bdryOut ω ψ).ConnectedComponent :=
  Equiv.ofBijective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ)
    ⟨ocd_fullComponentMap_injective hι hadjm ω ψ, ocd_fullComponentMap_surjective hι hadjm ω ψ⟩


noncomputable def ocd_outsideShift (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (bdryOut : Vout → Prop) [DecidablePred bdryOut]
    (ψ : ConfigSpace (Sym2 Vout)) : ℕ :=
  Nat.card (ocd_OutsideOnlyComp Gout ιV bdryOut ψ)


theorem ocd_numClustersBC_psiExt (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    numClustersBC Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) (ocd_psiExt ιV ψ ω)
      = numClustersBC Gin (ocd_inducedWiring Gout ιV bdryOut ψ) ω
          + ocd_outsideShift Gout ιV bdryOut ψ := by
  have hfull : numClustersBC Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) (ocd_psiExt ιV ψ ω)
      = Nat.card (ocd_fullGraph Gout ιV bdryOut ω ψ).ConnectedComponent := by
    rw [numClustersBC, ← ocd_fullGraph]
  have hinner : numClustersBC Gin (ocd_inducedWiring Gout ιV bdryOut ψ) ω
      = Nat.card (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).ConnectedComponent := by
    rw [numClustersBC, ← ocd_innerGraph]
  rw [hfull, hinner, ocd_outsideShift,
    ← Nat.card_congr (ocd_fullComponentEquiv hι hadjm ω ψ), Nat.card_sum]






theorem ocd_innerEdge_image_edgeFinset (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) :
    Gin.edgeFinset.image (ocd_innerEdge ιV)
      = Gout.edgeFinset.filter (· ∈ Set.range (ocd_innerEdge ιV)) := by
  ext e
  simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_edgeFinset, Set.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, a, rfl⟩
    induction a using Sym2.ind with | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at ha
    rw [ocd_innerEdge_mk, SimpleGraph.mem_edgeSet, ← hadjm]
    exact ha
  · rintro ⟨hmem, a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    induction a using Sym2.ind with | _ x y =>
    rw [ocd_innerEdge_mk, SimpleGraph.mem_edgeSet] at hmem
    rw [SimpleGraph.mem_edgeSet, hadjm]
    exact hmem


noncomputable def ocd_psiEdgeFactor (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (ψ : ConfigSpace (Sym2 Vout)) (p : ℝ) : ℝ :=
  ∏ e ∈ Gout.edgeFinset.filter (fun e => e ∉ Set.range (ocd_innerEdge ιV)),
    (if ψ e then p else 1 - p)

theorem ocd_psiEdgeFactor_pos (hp : 0 < p) (hp1 : p < 1) :
    0 < ocd_psiEdgeFactor Gout ιV ψ p := by
  unfold ocd_psiEdgeFactor
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith


theorem ocd_edgeProduct_psiExt (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p : ℝ} (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    edgeProduct Gout p (ocd_psiExt ιV ψ ω)
      = edgeProduct Gin p ω * ocd_psiEdgeFactor Gout ιV ψ p := by
  classical
  unfold edgeProduct ocd_psiEdgeFactor
  rw [← Finset.prod_filter_mul_prod_filter_not Gout.edgeFinset
    (fun e => e ∈ Set.range (ocd_innerEdge ιV))]
  congr 1
  · rw [← ocd_innerEdge_image_edgeFinset hι hadjm,
      Finset.prod_image (fun a _ b _ h => ocd_innerEdge_injective ιV hι h)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [ocd_psiExt_innerEdge hι]
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    rw [ocd_psiExt_eq_psi_of_not_range ψ ω he.2]


noncomputable def ocd_psiShift (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (bdryOut : Vout → Prop) [DecidablePred bdryOut]
    (ψ : ConfigSpace (Sym2 Vout)) (p q : ℝ) : ℝ :=
  ocd_psiEdgeFactor Gout ιV ψ p * q ^ ocd_outsideShift Gout ιV bdryOut ψ

theorem ocd_psiShift_pos (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < ocd_psiShift Gout ιV bdryOut ψ p q :=
  mul_pos (ocd_psiEdgeFactor_pos hp hp1) (pow_pos hq _)


theorem ocd_bcWeight_psiExt (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    bcWeight Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_psiExt ιV ψ ω)
      = bcWeight Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω
          * ocd_psiShift Gout ιV bdryOut ψ p q := by
  rw [bcWeight, ocd_numClustersBC_psiExt hι hadjm, ocd_edgeProduct_psiExt hι hadjm, bcWeight,
    ocd_psiShift, pow_add]
  ring




theorem ocd_inducedBcZ_psi (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (ψ : ConfigSpace (Sym2 Vout)) :
    inducedBcZ Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
        (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ
      = bcZ Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q
          * ocd_psiShift Gout ιV bdryOut ψ p q := by
  rw [inducedBcZ, ocd_condFibre_eq_image_psiExt hι,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (ocd_innerRestrict ιV) h
      rwa [ocd_innerRestrict_psiExt hι, ocd_innerRestrict_psiExt hι] at this),
    bcZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => ocd_bcWeight_psiExt hι hadjm ψ ω)




theorem ocd_condBcProb_psiExt_eq_bcProb (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
        (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ (ocd_psiExt ιV ψ ω)
      = bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
  rw [condBcProb, if_pos (ocd_agreesOff_psiExt ψ ω), ocd_bcWeight_psiExt hι hadjm,
    ocd_inducedBcZ_psi hι hadjm, bcProb,
    mul_div_mul_right _ _ (ocd_psiShift_pos hp hp1 hq).ne']


theorem ocd_condBcProb_psiExt_sum_eq_inducedBox (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 Vout)) (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ *
        condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ)
      = ∑ ω : ConfigSpace (Sym2 Vin),
          (ocd_psiExt ιV ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω
            * bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
  classical
  have hsupp : ∀ ρ ∉ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
      B.indicator (fun _ => (1:ℝ)) ρ *
        condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ = 0 := by
    intro ρ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ))
    (fun ρ _ hρ => hsupp ρ hρ)]
  rw [ocd_condFibre_eq_image_psiExt hι]
  rw [Finset.sum_image (fun a _ b _ h => by
    have := congrArg (ocd_innerRestrict ιV) h
    rwa [ocd_innerRestrict_psiExt hι, ocd_innerRestrict_psiExt hι] at this)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ocd_condBcProb_psiExt_eq_bcProb hι hadjm hp hp1 hq ψ ω]
  have hind : B.indicator (fun _ => (1:ℝ)) (ocd_psiExt ιV ψ ω)
      = (ocd_psiExt ιV ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω := by
    by_cases hω : ocd_psiExt ιV ψ ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]
  rw [hind]




theorem ocd_condBcProb_psiExt_dominated (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (bdryIn : Vin → Prop) [DecidablePred bdryIn]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    (hwire : ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1:ℝ)) ω
        * bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb Gin bdryIn p q ω := by
  refine (bcProb_mono_bc Gin (ocd_inducedWiring Gout ιV bdryOut ψ)
    (StatMech.Lattice.boundaryCliqueGraph bdryIn) hwire hp hp1 hq hA).trans_eq ?_
  exact Finset.sum_congr rfl (fun ω _ => by rw [bcProb_clique_eq_wiredFkProb])





theorem ocd_free_le_inducedBcProb (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb Gin p q ω) ≤
      ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
        bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
  have hmono := bcProb_mono_bc Gin (⊥ : SimpleGraph Vin)
    (ocd_inducedWiring Gout ιV bdryOut ψ) bot_le hp hp1 hq hA
  simpa only [bcProb_bot_eq_fkProb] using hmono




theorem ocd_free_le_condBcProb_innerRestrict
    (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb Gin p q ω) ≤
      ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator
          (fun _ => (1 : ℝ)) ρ *
        condBcProb Gout
          (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox hι hadjm
    hp hp1 hq0 ψ (ocd_innerRestrict ιV ⁻¹' A)]
  have hpre : ocd_psiExt ιV ψ ⁻¹' (ocd_innerRestrict ιV ⁻¹' A) = A := by
    ext ω
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hι]
  rw [hpre]
  exact ocd_free_le_inducedBcProb hι hadjm hp hp1 hq ψ hA




theorem ocd_condFibre_congr_dom {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)} (h : AgreesOff F ψ ψ') :
    condFibre F ψ = condFibre F ψ' := by
  ext σ
  rw [mem_condFibre, mem_condFibre, agreesOff_congr h]


theorem ocd_condBcProb_congr_dom {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : ℝ) (F : Finset (Sym2 V)) (ψ ψ' ω : ConfigSpace (Sym2 V)) (h : AgreesOff F ψ ψ') :
    condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
  have hcond : AgreesOff F ψ ω ↔ AgreesOff F ψ' ω := by rw [agreesOff_congr h]
  have hfibre : condFibre F ψ = condFibre F ψ' := ocd_condFibre_congr_dom h
  unfold condBcProb inducedBcZ
  rw [hfibre]
  by_cases hω : AgreesOff F ψ ω
  · rw [if_pos hω, if_pos (hcond.mp hω)]
  · rw [if_neg hω, if_neg (fun h' => hω (hcond.mpr h'))]





noncomputable def ocd_outProj (ιV : Vin → Vout) (ρ : ConfigSpace (Sym2 Vout)) :
    ConfigSpace (Sym2 Vout) :=
  ocd_psiExt ιV ρ (fun _ => false)

theorem ocd_outProj_eq_false_of_range (hι : Function.Injective ιV) (ρ : ConfigSpace (Sym2 Vout))
    {e : Sym2 Vout} (he : e ∈ Set.range (ocd_innerEdge ιV)) :
    ocd_outProj ιV ρ e = false := by
  obtain ⟨e', rfl⟩ := he
  unfold ocd_outProj
  rw [ocd_psiExt_innerEdge hι]

theorem ocd_outProj_eq_of_not_range (ρ : ConfigSpace (Sym2 Vout))
    {e : Sym2 Vout} (he : e ∉ Set.range (ocd_innerEdge ιV)) :
    ocd_outProj ιV ρ e = ρ e := by
  unfold ocd_outProj
  rw [ocd_psiExt_eq_psi_of_not_range _ _ he]

theorem ocd_outProj_idem (hι : Function.Injective ιV) (ρ : ConfigSpace (Sym2 Vout)) :
    ocd_outProj ιV (ocd_outProj ιV ρ) = ocd_outProj ιV ρ := by
  funext e
  by_cases hin : e ∈ Set.range (ocd_innerEdge ιV)
  · rw [ocd_outProj_eq_false_of_range hι _ hin, ocd_outProj_eq_false_of_range hι ρ hin]
  · rw [ocd_outProj_eq_of_not_range _ hin]

theorem ocd_filter_outProj_eq_condFibre (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (hψ : ocd_outProj ιV ψ = ψ) :
    Finset.univ.filter (fun ρ => ocd_outProj ιV ρ = ψ)
      = condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_condFibre]
  refine ⟨fun h e he => by
    rw [ocd_mem_innerEdgeFinset] at he
    rw [← ocd_outProj_eq_of_not_range ρ he, h], ?_⟩
  intro h
  have hpr : ocd_outProj ιV ρ = ocd_outProj ιV ψ := by
    funext e
    by_cases hin : e ∈ Set.range (ocd_innerEdge ιV)
    · rw [ocd_outProj_eq_false_of_range hι ρ hin, ocd_outProj_eq_false_of_range hι ψ hin]
    · have he : e ∉ ocd_innerEdgeFinset (Vin := Vin) ιV := by rw [ocd_mem_innerEdgeFinset]; exact hin
      rw [ocd_outProj_eq_of_not_range ρ hin, ocd_outProj_eq_of_not_range ψ hin, h e he]
  rw [hpr, hψ]


theorem ocd_sum_fibreMass_eq_one (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) = 1 := by
  classical
  rw [show (∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ))
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        (∑ σ ∈ Finset.univ.filter (fun ρ => ocd_outProj ιV ρ = ψ),
          bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) from ?_]
  · rw [Finset.sum_fiberwise_of_maps_to
        (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ocd_outProj_idem hι ρ⟩)]
    exact bcProb_sum_eq_one Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) hp hp1 hq
  · apply Finset.sum_congr rfl
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    rw [ocd_filter_outProj_eq_condFibre hι ψ hψ.2]


theorem ocd_bcProb_decompose (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
        * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q ρ)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
          (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
            bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ)
          * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
              * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
                  (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) := by
  classical
  set C := StatMech.Lattice.boundaryCliqueGraph bdryOut
  set F := ocd_innerEdgeFinset (Vin := Vin) ιV
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := ocd_outProj ιV) (t := Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ))
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ocd_outProj_idem hι ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.mem_filter] at hψ
  rw [ocd_filter_outProj_eq_condFibre hι ψ hψ.2]
  have hRHS : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [hRHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hbc := bcProb_eq_fibreMass_mul_condBcProb Gout C hp hp1 hq F ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ
    rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hbc
  have hcc : condBcProb Gout C p q F ρ ρ = condBcProb Gout C p q F ψ ρ :=
    ocd_condBcProb_congr_dom Gout C p q F ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hbc
  rw [hbc]
  ring




theorem ocd_condBcProb_innerRestrict_le (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (bdryIn : Vin → Prop) [DecidablePred bdryIn]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    (hwire : ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
        * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
            (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox hι hadjm hp hp1 hq0 ψ (ocd_innerRestrict ιV ⁻¹' A)]
  have hpre : ocd_psiExt ιV ψ ⁻¹' (ocd_innerRestrict ιV ⁻¹' A) = A := by
    ext ω
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hι]
  rw [hpre]
  exact ocd_condBcProb_psiExt_dominated hι hadjm bdryIn hp hp1 hq ψ hwire hA




theorem ocd_wired_inner_dominated_bcProb (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (bdryIn : Vin → Prop) [DecidablePred bdryIn]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hwire : ∀ ψ : ConfigSpace (Sym2 Vout),
      ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
        * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω with hc
  rw [ocd_bcProb_decompose hι hp hp1 hq0 (ocd_innerRestrict ιV ⁻¹' A)]
  calc ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
          (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
            bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ)
          * (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
              * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
                  (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ)
        ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
            (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
              bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) * c := by
          apply Finset.sum_le_sum
          intro ψ _
          apply mul_le_mul_of_nonneg_left
            (ocd_condBcProb_innerRestrict_le hι hadjm bdryIn hp hp1 hq ψ (hwire ψ) hA)
          exact Finset.sum_nonneg (fun σ _ =>
            bcProb_nonneg Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) hp hp1 hq0 σ)
    _ = (∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
            (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
              bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ)) * c := by
          rw [Finset.sum_mul]
    _ = c := by rw [ocd_sum_fibreMass_eq_one hι hp hp1 hq0, one_mul]










variable {d : ℕ}





theorem ocd_latticeAdjMatch {Sin Sout : Set (Site d)} [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) :
    ocd_AdjMatch (SimpleGraph.comap Subtype.val (hypercubicLattice d))
      (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV := by
  intro x y
  rw [SimpleGraph.comap_adj, SimpleGraph.comap_adj, hιval x, hιval y]














variable {Sin Sout : Set (Site d)}

noncomputable instance ocd_instDecRelLatticeComap {S : Set (Site d)} :
    DecidableRel (SimpleGraph.comap Subtype.val (hypercubicLattice d) :
      SimpleGraph {y : Site d // y ∈ S}).Adj :=
  Classical.decRel _



theorem ocd_bdryIn_of_outsideGraph_adj [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d))
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    (ψ : ConfigSpace (Sym2 {y : Site d // y ∈ Sout}))
    {x : {y : Site d // y ∈ Sin}} {z : {y : Site d // y ∈ Sout}}
    (h : (ocd_outsideGraph (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ).Adj
        (ιV x) z) :
    bdryIn x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, hopen, hrange⟩ | ⟨hne, hb1, hb2⟩
  · 
    have hznot : (z : Site d) ∉ Sin := by
      intro hz
      refine hrange ⟨s(x, ⟨(z : Site d), hz⟩), ?_⟩
      rw [ocd_innerEdge_mk]
      have hzeq : ιV ⟨(z : Site d), hz⟩ = z := Subtype.ext (hιval ⟨(z : Site d), hz⟩)
      rw [hzeq]
    have hnn : NearestNeighbour d (x : Site d) (z : Site d) := by
      have hcp := hadj
      rw [SimpleGraph.comap_adj] at hcp
      rw [hιval x] at hcp
      exact hcp
    exact hbdryIn x (z : Site d) hnn hznot
  · exact absurd hb1 (hmargin x)



theorem ocd_latticeInducedWiring_le [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) (hιinj : Function.Injective ιV)
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    (ψ : ConfigSpace (Sym2 {y : Site d // y ∈ Sout})) :
    ocd_inducedWiring (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ
      ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · 
    have hne' : ιV x ≠ ιV y := fun he => hne (hιinj he)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_bdryIn_of_outsideGraph_adj ιV hιval bdryOut bdryIn hmargin hbdryIn ψ hadj
  · 
    have hreach' :
        (ocd_outsideGraph (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ).Reachable
          (ιV y) (ιV x) := hreach.symm
    have hne' : ιV y ≠ ιV x := fun he => hne (hιinj he).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_bdryIn_of_outsideGraph_adj ιV hιval bdryOut bdryIn hmargin hbdryIn ψ hadj


























theorem ocd_latticeWired_inner_dominated [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) (hιinj : Function.Injective ιV)
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 {y : Site d // y ∈ Sin}))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
        * wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q ω := by
  have hadjm := ocd_latticeAdjMatch ιV hιval
  have hwire := fun ψ => ocd_latticeInducedWiring_le ιV hιval hιinj bdryOut bdryIn hmargin hbdryIn ψ
  have hdom := ocd_wired_inner_dominated_bcProb hιinj hadjm bdryIn hp hp1 hq hwire hA
  refine le_trans ?_ hdom
  apply le_of_eq
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [bcProb_clique_eq_wiredFkProb]











theorem ocd_innerRestrict_preimage_multiOpenEvent (hι : Function.Injective ιV)
    (t : Finset (Sym2 Vin)) :
    ocd_innerRestrict ιV ⁻¹' (med_genericMultiOpenEvent t)
      = med_genericMultiOpenEvent (t.image (ocd_innerEdge ιV)) := by
  ext ρ
  simp only [Set.mem_preimage, med_genericMultiOpenEvent, Set.mem_setOf_eq, ocd_innerRestrict,
    Finset.forall_mem_image]








theorem ocd_latticeWired_multiMass_dominated [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) (hιinj : Function.Injective ιV)
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (Sym2 {y : Site d // y ∈ Sin})) :
    med_multiMassProb
        (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q)
        (t.image (ocd_innerEdge ιV))
      ≤ med_multiMassProb
          (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q) t := by
  have hdom := ocd_latticeWired_inner_dominated ιV hιval hιinj bdryOut bdryIn hmargin hbdryIn
    hp hp1 hq (A := med_genericMultiOpenEvent t) (med_genericMultiOpenEvent_increasing t)
  rw [ocd_innerRestrict_preimage_multiOpenEvent hιinj t] at hdom
  exact hdom

end FK

end StatMech
