/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxCrossGraph
/-!
# Boundary conditions induced on a box by the outer annulus

Conditioning the wired FK measure on `Λ_(n+1)` on the edges outside `Λ_n` gives a
random-cluster measure on `Λ_n` with a wiring supported on `∂Λ_n`, hence dominated by the wired
measure on `Λ_n`.

## i. Overview

For an outer configuration `ψ` on `Λ_(n+1)`, `psiExt d n ψ ω` glues an inner configuration `ω`
on `Λ_n` to `ψ`. The outer graph consists of the open edges of `ψ` outside `Λ_n` together with
the clique on `∂Λ_(n+1)`. The induced wiring `inducedWiring d n ψ` joins two vertices of `Λ_n`
when they are connected in the outer graph; such vertices lie on `∂Λ_n`.

The components of the glued graph are in bijection with the components of `ω` under the
induced wiring together with the outer components that never meet `Λ_n`
(`fullComponentEquiv`). Hence the wired cluster count of the glued configuration is the
induced cluster count of `ω` plus a term depending only on `ψ`, and the edge product factorizes
the same way. This is the domain Markov property: the conditional measure equals
`bcProb (boxGraph d n) (inducedWiring d n ψ)`. Since the induced wiring lies below the
boundary clique of `Λ_n`, for `q ≥ 1` it is dominated by the wired measure on `Λ_n`.

## ii. Key results

- `inducedWiring` : the wiring induced on `Λ_n` by an outer configuration.
- `numClustersBC_psiExt` : the cluster count of a glued configuration.
- `condBcProb_psiExt_eq_bcProb` : the domain Markov property on `Λ_n ⊆ Λ_(n+1)`.
- `inducedWiring_le_wired` : the induced wiring is supported on `∂Λ_n`.
- `condBcProb_psiExt_dominated_wired` : the conditional measure is dominated by the wired
  measure on `Λ_n`.

## iii. Table of contents

- A. Gluing inner and outer configurations
- B. The outer graph and the induced wiring
- C. Decomposition of the glued graph
- D. Counting clusters
- E. Factorization of the weights
- F. The induced wiring lives on the boundary
- G. Domination by the wired measure

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}

/-!
## A. Gluing inner and outer configurations
-/

/-- Glue a configuration `ω` on `Λ_n` into an outer configuration `ψ` on `Λ_(n+1)`: edges of `Λ_n`
follow `ω`, the others follow `ψ`. -/
noncomputable def psiExt (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) : ConfigSpace (Sym2 (boxVerts d (n + 1))) :=
  fun e => if h : e ∈ Set.range (innerEdge d n) then ω h.choose else ψ e

lemma psiExt_innerEdge (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (e : Sym2 (boxVerts d n)) :
    psiExt d n ψ ω (innerEdge d n e) = ω e := by
  unfold psiExt
  have hmem : innerEdge d n e ∈ Set.range (innerEdge d n) := ⟨e, rfl⟩
  rw [dite_eq_left hmem]
  congr 1
  exact innerEdge_injective d n hmem.choose_spec

lemma psiExt_eq_psi_of_not_range (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {e : Sym2 (boxVerts d (n + 1))}
    (he : e ∉ Set.range (innerEdge d n)) : psiExt d n ψ ω e = ψ e := by
  unfold psiExt; rw [dite_eq_right he]

lemma psiExt_innerEdge_pair (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (x y : boxVerts d n) :
    psiExt d n ψ ω s(boxVertIncl d n x, boxVertIncl d n y) = ω s(x, y) := by
  have h : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  rw [h, psiExt_innerEdge]

@[simp] lemma innerRestrict_psiExt (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) : innerRestrict d n (psiExt d n ψ ω) = ω := by
  funext e; rw [innerRestrict, psiExt_innerEdge]

lemma agreesOff_psiExt (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    AgreesOff (innerEdgeFinset d n) ψ (psiExt d n ψ ω) := by
  intro e he
  rw [mem_innerEdgeFinset] at he
  exact psiExt_eq_psi_of_not_range d n ψ ω he

lemma psiExt_innerRestrict_of_agreesOff (d n : ℕ)
    {ψ ρ : ConfigSpace (Sym2 (boxVerts d (n + 1)))}
    (hρ : AgreesOff (innerEdgeFinset d n) ψ ρ) :
    psiExt d n ψ (innerRestrict d n ρ) = ρ := by
  funext e
  unfold psiExt
  split
  · rename_i hmem
    show innerRestrict d n ρ hmem.choose = ρ e
    rw [innerRestrict, hmem.choose_spec]
  · rename_i hmem
    have : e ∉ innerEdgeFinset d n := by rw [mem_innerEdgeFinset]; exact hmem
    exact (hρ e this).symm

lemma condFibre_eq_image_psiExt (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    condFibre (innerEdgeFinset d n) ψ = Finset.univ.image (psiExt d n ψ) := by
  ext ρ
  rw [mem_condFibre, Finset.mem_image]
  constructor
  · intro hρ
    exact ⟨innerRestrict d n ρ, Finset.mem_univ _, psiExt_innerRestrict_of_agreesOff d n hρ⟩
  · rintro ⟨ω, _, rfl⟩
    exact agreesOff_psiExt d n ψ ω

/-!
## B. The outer graph and the induced wiring
-/

/-- The open edges of `ψ` on `Λ_(n+1)` that are not edges of `Λ_n`. -/
noncomputable def outsideOpenGraph (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    SimpleGraph (boxVerts d (n + 1)) where
  Adj x y := (boxGraph d (n + 1)).Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (innerEdge d n)
  symm := by
    refine ⟨?_⟩
    rintro x y ⟨hadj, hopen, hrange⟩
    refine ⟨hadj.symm, ?_, ?_⟩ <;> rw [Sym2.eq_swap] <;> assumption
  loopless := ⟨by rintro x ⟨hadj, _, _⟩; exact hadj.ne rfl⟩

/-- Adjacency in `outsideOpenGraph` is decidable (classically). -/
noncomputable instance instDecidableRelOutsideOpenGraph (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : DecidableRel (outsideOpenGraph d n ψ).Adj :=
  fun _ _ => Classical.dec _

/-- The outer graph: open outer edges of `ψ` together with the clique on `∂Λ_(n+1)`. -/
noncomputable def outsideGraph (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    SimpleGraph (boxVerts d (n + 1)) :=
  outsideOpenGraph d n ψ ⊔ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))

/-- Adjacency in `outsideGraph` is decidable (classically). -/
noncomputable instance instDecidableRelOutsideGraph (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : DecidableRel (outsideGraph d n ψ).Adj :=
  fun _ _ => Classical.dec _

lemma outsideGraph_adj (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (x y : boxVerts d (n + 1)) :
    (outsideGraph d n ψ).Adj x y
      ↔ ((boxGraph d (n + 1)).Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (innerEdge d n))
        ∨ (x ≠ y ∧ boxBoundary d (n + 1) x ∧ boxBoundary d (n + 1) y) := by
  rw [outsideGraph, SimpleGraph.sup_adj, StatMech.Lattice.boundaryCliqueGraph_adj]
  exact Iff.rfl

/-- The wiring induced on `Λ_n` by `ψ`: distinct vertices of `Λ_n` connected in the outer graph. -/
noncomputable def inducedWiring (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    SimpleGraph (boxVerts d n) where
  Adj x y := x ≠ y ∧ (outsideGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)
  symm := by
    refine ⟨?_⟩
    rintro x y ⟨hne, hreach⟩
    exact ⟨hne.symm, hreach.symm⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

/-- Adjacency in `inducedWiring` is decidable (classically). -/
noncomputable instance instDecidableRelInducedWiring (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : DecidableRel (inducedWiring d n ψ).Adj :=
  fun _ _ => Classical.dec _

lemma inducedWiring_adj (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (x y : boxVerts d n) :
    (inducedWiring d n ψ).Adj x y
      ↔ x ≠ y ∧ (outsideGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) :=
  Iff.rfl

/-!
## C. Decomposition of the glued graph
-/

/-- The open edges of `ω`, viewed as edges of `Λ_(n+1)`. -/
noncomputable def innerImageGraph (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    SimpleGraph (boxVerts d (n + 1)) where
  Adj x y := (boxGraph d (n + 1)).Adj x y ∧ psiExt d n (fun _ => false) ω s(x, y) = true
    ∧ s(x, y) ∈ Set.range (innerEdge d n)
  symm := by
    refine ⟨?_⟩
    rintro x y ⟨hadj, hopen, hrange⟩
    refine ⟨hadj.symm, ?_, ?_⟩ <;> rw [Sym2.eq_swap] <;> assumption
  loopless := ⟨by rintro x ⟨hadj, _, _⟩; exact hadj.ne rfl⟩

/-- Adjacency in `innerImageGraph` is decidable (classically). -/
noncomputable instance instDecidableRelInnerImageGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) : DecidableRel (innerImageGraph d n ω).Adj :=
  fun _ _ => Classical.dec _

lemma psiExt_eq_false_of_range (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {e : Sym2 (boxVerts d (n + 1))}
    (he : e ∈ Set.range (innerEdge d n)) :
    psiExt d n ψ ω e = psiExt d n (fun _ => false) ω e := by
  obtain ⟨e', rfl⟩ := he
  rw [psiExt_innerEdge, psiExt_innerEdge]

/-- The wired open graph of the glued configuration is the union of the inner open edges and the
outer graph. -/
lemma psiWiredGraph_eq_sup (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    openSub (boxGraph d (n + 1)) (psiExt d n ψ ω)
        ⊔ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))
      = innerImageGraph d n ω ⊔ outsideGraph d n ψ := by
  ext x y
  rw [SimpleGraph.sup_adj, openSub_adj, SimpleGraph.sup_adj, outsideGraph,
    SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hadj, hopen⟩ | hclique)
    · by_cases hr : s(x, y) ∈ Set.range (innerEdge d n)
      · refine Or.inl ⟨hadj, ?_, hr⟩
        rw [← psiExt_eq_false_of_range d n ψ ω hr]; exact hopen
      · refine Or.inr (Or.inl ⟨hadj, ?_, hr⟩)
        rwa [psiExt_eq_psi_of_not_range d n ψ ω hr] at hopen
    · exact Or.inr (Or.inr hclique)
  · rintro (⟨hadj, hopen, hr⟩ | ⟨hadj, hopen, hr⟩ | hclique)
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [psiExt_eq_false_of_range d n ψ ω hr]
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [psiExt_eq_psi_of_not_range d n ψ ω hr]
    · exact Or.inr hclique

/-- The wired open graph of the glued configuration on `Λ_(n+1)`. -/
noncomputable abbrev fullGraph (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : SimpleGraph (boxVerts d (n + 1)) :=
  innerImageGraph d n ω ⊔ outsideGraph d n ψ

/-- The open graph of `ω` on `Λ_n` with the induced wiring added. -/
noncomputable abbrev innerGraph (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : SimpleGraph (boxVerts d n) :=
  openSub (boxGraph d n) ω ⊔ inducedWiring d n ψ

/-- Adjacency in `innerGraph` is decidable (classically). -/
noncomputable instance instDecidableRelInnerGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    DecidableRel (innerGraph d n ω ψ).Adj :=
  fun _ _ => Classical.dec _

lemma outsideGraph_le_fullGraph (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    outsideGraph d n ψ ≤ fullGraph d n ω ψ := le_sup_right

lemma innerImageGraph_adj_inner (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {u v : boxVerts d (n + 1)} (h : (innerImageGraph d n ω).Adj u v) :
    IsInnerVert d n u ∧ IsInnerVert d n v := by
  obtain ⟨_, _, hr⟩ := h
  obtain ⟨e, he⟩ := hr
  refine Sym2.inductionOn e (fun a b hab => ?_) he
  rw [innerEdge, Sym2.map_mk, Sym2.eq_iff] at hab
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact ⟨isInnerVert_boxVertIncl d n a, isInnerVert_boxVertIncl d n b⟩
  · subst h1; subst h2; exact ⟨isInnerVert_boxVertIncl d n b, isInnerVert_boxVertIncl d n a⟩

lemma innerImageGraph_adj_boxVertIncl (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (x y : boxVerts d n) :
    (innerImageGraph d n ω).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (openSub (boxGraph d n) ω).Adj x y := by
  have he : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  constructor
  · rintro ⟨hadj, hopen, _⟩
    refine ⟨(boxGraph_adj_boxVertIncl d n x y).mp hadj, ?_⟩
    rw [he, psiExt_innerEdge] at hopen; exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨(boxGraph_adj_boxVertIncl d n x y).mpr hadj, ?_, ⟨s(x, y), he.symm⟩⟩
    rw [he, psiExt_innerEdge]; exact hopen

lemma innerGraph_reachable_of_outsideReachable (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {x y : boxVerts d n}
    (h : (outsideGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraph d n ω ψ).Reachable x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl x
  · have hadj : (inducedWiring d n ψ).Adj x y := ⟨hxy, h⟩
    exact (le_sup_right (a := openSub (boxGraph d n) ω) hadj).reachable

lemma fullGraph_reachable_of_innerGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {x y : boxVerts d n} (h : (innerGraph d n ω ψ).Reachable x y) :
    (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u w _ hadj ih =>
      refine ih.trans ?_
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with hopen | hwire
      · exact ((innerImageGraph_adj_boxVertIncl d n ω u w).mpr hopen).reachable.mono
          le_sup_left
      · exact ((hwire.2.mono (outsideGraph_le_fullGraph d n ω ψ)))

lemma innerGraph_reachable_of_fullGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {x y : boxVerts d n}
    (h : (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerGraph d n ω ψ).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : boxVerts d (n + 1),
      Relation.ReflTransGen (fullGraph d n ω ψ).Adj (boxVertIncl d n x) w →
        ∃ x₀ : boxVerts d n, (innerGraph d n ω ψ).Reachable x x₀
          ∧ (outsideGraph d n ψ).Reachable (boxVertIncl d n x₀) w by
    obtain ⟨x₀, hKx₀, hout⟩ := H (boxVertIncl d n y) h
    exact hKx₀.trans (innerGraph_reachable_of_outsideReachable d n ω ψ hout)
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
        have hKu' : (innerGraph d n ω ψ).Reachable x₀ u' :=
          innerGraph_reachable_of_outsideReachable d n ω ψ hout
        have hstep : (innerGraph d n ω ψ).Adj u' w' :=
          le_sup_left (b := inducedWiring d n ψ)
            ((innerImageGraph_adj_boxVertIncl d n ω u' w').mp himg)
        have hKw' : (innerGraph d n ω ψ).Reachable x w' :=
          ((hKx₀.trans hKu').trans hstep.reachable)
        exact ⟨w', hKw', SimpleGraph.Reachable.refl _⟩
      · exact ⟨x₀, hKx₀, hout.trans hoadj.reachable⟩

/-- Two vertices of `Λ_n` are connected in the glued graph iff they are connected in `innerGraph`.
-/
lemma fullGraph_reachable_boxVertIncl (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (x y : boxVerts d n) :
    (fullGraph d n ω ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (innerGraph d n ω ψ).Reachable x y :=
  ⟨innerGraph_reachable_of_fullGraph d n ω ψ, fullGraph_reachable_of_innerGraph d n ω ψ⟩

lemma fullGraph_adj_of_outside (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) {u w : boxVerts d (n + 1)}
    (hu : ¬ IsInnerVert d n u) (h : (fullGraph d n ω ψ).Adj u w) :
    (outsideGraph d n ψ).Adj u w := by
  rw [SimpleGraph.sup_adj] at h
  rcases h with himg | hout
  · exact absurd (innerImageGraph_adj_inner d n ω himg).1 hu
  · exact hout

/-!
## D. Counting clusters
-/

/-- A vertex of `Λ_(n+1)` whose outer component contains no vertex of `Λ_n`. -/
def OutsideOnly (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (u : boxVerts d (n + 1)) : Prop :=
  ∀ v, (outsideGraph d n ψ).Reachable u v → ¬ IsInnerVert d n v

lemma outsideOnly_self_not_inner (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {u : boxVerts d (n + 1)} (hu : OutsideOnly d n ψ u) : ¬ IsInnerVert d n u :=
  hu u (SimpleGraph.Reachable.refl u)

lemma outsideOnly_of_reachable (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {u v : boxVerts d (n + 1)} (hu : OutsideOnly d n ψ u)
    (h : (outsideGraph d n ψ).Reachable u v) : OutsideOnly d n ψ v :=
  fun w hw => hu w (h.trans hw)

lemma outsideGraph_reachable_of_fullGraph_outsideOnly (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {u w : boxVerts d (n + 1)} (hu : OutsideOnly d n ψ u)
    (h : (fullGraph d n ω ψ).Reachable u w) :
    (outsideGraph d n ψ).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b hua hadj ih =>
      have ha_out : (outsideGraph d n ψ).Reachable u a := ih
      have ha_not_inner : ¬ IsInnerVert d n a := hu a ha_out
      exact ha_out.trans (fullGraph_adj_of_outside d n ω ψ ha_not_inner hadj).reachable

/-- `OutsideOnly` as a predicate on components of the outer graph. -/
noncomputable def IsOutsideOnly (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    (outsideGraph d n ψ).ConnectedComponent → Prop :=
  ConnectedComponent.lift (OutsideOnly d n ψ)
    (fun _ _ p _ => propext ⟨fun h => outsideOnly_of_reachable d n ψ h p.reachable,
      fun h => outsideOnly_of_reachable d n ψ h p.reachable.symm⟩)

@[simp] lemma isOutsideOnly_mk (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (v : boxVerts d (n + 1)) :
    IsOutsideOnly d n ψ ((outsideGraph d n ψ).connectedComponentMk v) ↔ OutsideOnly d n ψ v :=
  Iff.rfl

/-- The components of the outer graph that avoid `Λ_n`. -/
def OutsideOnlyComp (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : Type :=
  {c : (outsideGraph d n ψ).ConnectedComponent // IsOutsideOnly d n ψ c}

/-- There are finitely many outer components avoiding `Λ_n`. -/
noncomputable instance instFintypeOutsideOnlyComp (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : Fintype (OutsideOnlyComp d n ψ) := by
  classical
  unfold OutsideOnlyComp; infer_instance

/-- The map from components of `innerGraph` and outer components avoiding `Λ_n` to components of the
glued graph. -/
noncomputable def fullComponentMap (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    (innerGraph d n ω ψ).ConnectedComponent ⊕ OutsideOnlyComp d n ψ →
      (fullGraph d n ω ψ).ConnectedComponent
  | Sum.inl c => c.lift (fun x => (fullGraph d n ω ψ).connectedComponentMk (boxVertIncl d n x))
      (fun _ _ p _ => ConnectedComponent.sound
        (fullGraph_reachable_of_innerGraph d n ω ψ p.reachable))
  | Sum.inr c => c.1.lift (fun v => (fullGraph d n ω ψ).connectedComponentMk v)
      (fun _ _ p _ => ConnectedComponent.sound
        (p.reachable.mono (outsideGraph_le_fullGraph d n ω ψ)))

lemma fullComponentMap_inl_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) (x : boxVerts d n) :
    fullComponentMap d n ω ψ (Sum.inl ((innerGraph d n ω ψ).connectedComponentMk x))
      = (fullGraph d n ω ψ).connectedComponentMk (boxVertIncl d n x) := rfl

lemma fullComponentMap_inr_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) (v : boxVerts d (n + 1))
    (hv : IsOutsideOnly d n ψ ((outsideGraph d n ψ).connectedComponentMk v)) :
    fullComponentMap d n ω ψ (Sum.inr ⟨(outsideGraph d n ψ).connectedComponentMk v, hv⟩)
      = (fullGraph d n ω ψ).connectedComponentMk v := rfl

lemma fullComponentMap_injective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    Function.Injective (fullComponentMap d n ω ψ) := by
  rintro (c₁ | ⟨c₁, hc₁⟩) (c₂ | ⟨c₂, hc₂⟩) h
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMap_inl_mk, fullComponentMap_inl_mk, ConnectedComponent.eq] at h
    exact congrArg Sum.inl (ConnectedComponent.eq.mpr (innerGraph_reachable_of_fullGraph d n ω ψ h))
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMap_inl_mk, fullComponentMap_inr_mk] at h
    have hreach : (fullGraph d n ω ψ).Reachable (boxVertIncl d n x₁) v₂ :=
      ConnectedComponent.eq.mp h
    have hv₂ : OutsideOnly d n ψ v₂ := (isOutsideOnly_mk d n ψ v₂).mp hc₂
    have : (outsideGraph d n ψ).Reachable v₂ (boxVertIncl d n x₁) :=
      outsideGraph_reachable_of_fullGraph_outsideOnly d n ω ψ hv₂ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₁) (hv₂ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMap_inl_mk, fullComponentMap_inr_mk] at h
    have hreach : (fullGraph d n ω ψ).Reachable (boxVertIncl d n x₂) v₁ :=
      ConnectedComponent.eq.mp h.symm
    have hv₁ : OutsideOnly d n ψ v₁ := (isOutsideOnly_mk d n ψ v₁).mp hc₁
    have : (outsideGraph d n ψ).Reachable v₁ (boxVertIncl d n x₂) :=
      outsideGraph_reachable_of_fullGraph_outsideOnly d n ω ψ hv₁ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₂) (hv₁ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMap_inr_mk, fullComponentMap_inr_mk] at h
    have hreach : (fullGraph d n ω ψ).Reachable v₁ v₂ := ConnectedComponent.eq.mp h
    have hv₁ : OutsideOnly d n ψ v₁ := (isOutsideOnly_mk d n ψ v₁).mp hc₁
    have hout : (outsideGraph d n ψ).Reachable v₁ v₂ :=
      outsideGraph_reachable_of_fullGraph_outsideOnly d n ω ψ hv₁ hreach
    refine congrArg Sum.inr (Subtype.ext ?_)
    exact ConnectedComponent.sound hout

lemma fullComponentMap_surjective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    Function.Surjective (fullComponentMap d n ω ψ) := by
  classical
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : ∃ w, IsInnerVert d n w ∧ (fullGraph d n ω ψ).Reachable u w
  · obtain ⟨w, hw, hreach⟩ := hu
    obtain ⟨x, rfl⟩ := (isInnerVert_iff_range d n w).mp hw
    refine ⟨Sum.inl ((innerGraph d n ω ψ).connectedComponentMk x), ?_⟩
    rw [fullComponentMap_inl_mk]
    exact ConnectedComponent.sound hreach.symm
  · have hOut : OutsideOnly d n ψ u := by
      intro v hv hinner
      exact hu ⟨v, hinner, hv.mono (outsideGraph_le_fullGraph d n ω ψ)⟩
    refine ⟨Sum.inr ⟨(outsideGraph d n ψ).connectedComponentMk u,
      (isOutsideOnly_mk d n ψ u).mpr hOut⟩, ?_⟩
    rw [fullComponentMap_inr_mk]

/-- Components of the glued graph are components of `innerGraph` plus the outer components avoiding
`Λ_n`. -/
noncomputable def fullComponentEquiv (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    (innerGraph d n ω ψ).ConnectedComponent ⊕ OutsideOnlyComp d n ψ ≃
      (fullGraph d n ω ψ).ConnectedComponent :=
  Equiv.ofBijective (fullComponentMap d n ω ψ)
    ⟨fullComponentMap_injective d n ω ψ, fullComponentMap_surjective d n ω ψ⟩

/-- The number of outer components avoiding `Λ_n`. -/
noncomputable def outsideShift (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) : ℕ :=
  Nat.card (OutsideOnlyComp d n ψ)

/-- The wired cluster count of a glued configuration is the induced cluster count of `ω` plus
`outsideShift d n ψ`. -/
lemma numClustersBC_psiExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    numClustersBC (boxGraph d (n + 1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) (psiExt d n ψ ω)
      = numClustersBC (boxGraph d n) (inducedWiring d n ψ) ω + outsideShift d n ψ := by
  have hfull : numClustersBC (boxGraph d (n + 1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) (psiExt d n ψ ω)
      = Nat.card (fullGraph d n ω ψ).ConnectedComponent := by
    rw [numClustersBC, psiWiredGraph_eq_sup]
  have hinner : numClustersBC (boxGraph d n) (inducedWiring d n ψ) ω
      = Nat.card (innerGraph d n ω ψ).ConnectedComponent := by
    rw [numClustersBC]
  rw [hfull, hinner, outsideShift,
    ← Nat.card_congr (fullComponentEquiv d n ω ψ), Nat.card_sum]

/-!
## E. Factorization of the weights
-/

/-- The Bernoulli edge product over the edges of `Λ_(n+1)` outside `Λ_n`, evaluated at `ψ`. -/
noncomputable def psiEdgeFactor (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (p : ℝ) : ℝ :=
  ∏ e ∈ (boxGraph d (n + 1)).edgeFinset.filter (fun e => e ∉ Set.range (innerEdge d n)),
    (if ψ e then p else 1 - p)

lemma psiEdgeFactor_pos {d n : ℕ} {ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : 0 < psiEdgeFactor d n ψ p := by
  unfold psiEdgeFactor
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith

/-- The edge product of a glued configuration factorizes into the inner edge product and
`psiEdgeFactor`. -/
lemma edgeProduct_psiExt (d n : ℕ) {p : ℝ} (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    edgeProduct (boxGraph d (n + 1)) p (psiExt d n ψ ω)
      = edgeProduct (boxGraph d n) p ω * psiEdgeFactor d n ψ p := by
  classical
  unfold edgeProduct psiEdgeFactor
  rw [← Finset.prod_filter_mul_prod_filter_not (boxGraph d (n + 1)).edgeFinset
    (fun e => e ∈ Set.range (innerEdge d n))]
  congr 1
  · rw [← innerEdge_image_edgeFinset,
      Finset.prod_image (fun a _ b _ h => innerEdge_injective d n h)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [psiExt_innerEdge]
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    rw [psiExt_eq_psi_of_not_range d n ψ ω he.2]

/-- The factor depending only on `ψ`: `psiEdgeFactor · q ^ outsideShift`. -/
noncomputable def psiShift (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (p q : ℝ) : ℝ :=
  psiEdgeFactor d n ψ p * q ^ outsideShift d n ψ

lemma psiShift_pos {d n : ℕ} {ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))} {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : 0 < psiShift d n ψ p q :=
  mul_pos (psiEdgeFactor_pos hp hp1) (pow_pos hq _)

lemma bcWeight_psiExt (d n : ℕ) {p q : ℝ} (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    bcWeight (boxGraph d (n + 1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) p q (psiExt d n ψ ω)
      = bcWeight (boxGraph d n) (inducedWiring d n ψ) p q ω * psiShift d n ψ p q := by
  rw [bcWeight, numClustersBC_psiExt, edgeProduct_psiExt, bcWeight, psiShift, pow_add]
  ring

lemma inducedBcZ_innerEdgeFinset_psi (d n : ℕ) {p q : ℝ}
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    inducedBcZ (boxGraph d (n + 1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) p q
        (innerEdgeFinset d n) ψ
      = bcZ (boxGraph d n) (inducedWiring d n ψ) p q * psiShift d n ψ p q := by
  rw [inducedBcZ, condFibre_eq_image_psiExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this),
    bcZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => bcWeight_psiExt d n ψ ω)

/-- Domain Markov property: the wired measure on `Λ_(n+1)`, conditioned on the outer configuration
`ψ`, is the random-cluster measure on `Λ_n` with the induced wiring. -/
lemma condBcProb_psiExt_eq_bcProb (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    condBcProb (boxGraph d (n + 1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) p q
        (innerEdgeFinset d n) ψ (psiExt d n ψ ω)
      = bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω := by
  rw [condBcProb, ite_eq_left (agreesOff_psiExt d n ψ ω), bcWeight_psiExt,
    inducedBcZ_innerEdgeFinset_psi, bcProb,
    mul_div_mul_right _ _ (psiShift_pos hp hp1 hq).ne']

/-!
## F. The induced wiring lives on the boundary
-/

-- `hx` is consumed by `omega`, which the unused-variables linter does not see.
set_option linter.unusedVariables false in
lemma notMem_box_pred_of_adj_outer {d n : ℕ} (hn : 1 ≤ n) {x y : Site d}
    (hx : x ∈ StatMech.Lattice.box d n) (hadj : StatMech.Lattice.NearestNeighbour d x y)
    (hy : y ∉ StatMech.Lattice.box d n) : x ∉ StatMech.Lattice.box d (n - 1) := by
  rw [StatMech.Lattice.mem_box] at hx
  rw [StatMech.Lattice.mem_box] at hy
  simp only [not_forall, not_le] at hy
  obtain ⟨i, hyi⟩ := hy
  unfold StatMech.Lattice.NearestNeighbour at hadj
  have hterm : (x i - y i).natAbs ≤ 1 := by
    have hle : (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rw [hadj] at hle; exact hle
  have h1 : (y i).natAbs ≤ (x i).natAbs + (x i - y i).natAbs := by
    have hsub : (y i) = (x i) - (x i - y i) := by ring
    calc (y i).natAbs = ((x i) - (x i - y i)).natAbs := by rw [← hsub]
      _ ≤ (x i).natAbs + (x i - y i).natAbs := Int.natAbs_sub_le (x i) (x i - y i)
  have hxi : n ≤ (x i).natAbs := by omega
  rw [StatMech.Lattice.mem_box]
  simp only [not_forall, not_le]
  exact ⟨i, by omega⟩

lemma boxBoundary_of_outsideGraph_adj (d n : ℕ) (hn : 1 ≤ n)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) {x : boxVerts d n} {z : boxVerts d (n + 1)}
    (h : (outsideGraph d n ψ).Adj (boxVertIncl d n x) z) : boxBoundary d n x := by
  have hinx : IsInnerVert d n (boxVertIncl d n x) := isInnerVert_boxVertIncl d n x
  have hnotbdry : ¬ boxBoundary d (n + 1) (boxVertIncl d n x) := by
    rw [boxBoundary_succ_iff_not_inner]; exact fun h => h hinx
  rw [outsideGraph_adj] at h
  rcases h with ⟨hadj, hopen, hrange⟩ | ⟨hne, hb1, hb2⟩
  · have hznot : ¬ IsInnerVert d n z := by
      intro hz
      obtain ⟨z', rfl⟩ := (isInnerVert_iff_range d n z).mp hz
      exact hrange ⟨s(x, z'), by rw [innerEdge, Sym2.map_mk]⟩
    have hnn : StatMech.Lattice.NearestNeighbour d (x : Site d) (z : Site d) := by
      have hcp := hadj; rw [boxGraph, SimpleGraph.comap_adj] at hcp; exact hcp
    exact ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn hznot⟩
  · exact absurd hb1 hnotbdry

lemma inducedWiring_only_bdry (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {x y : boxVerts d n} (h : (inducedWiring d n ψ).Adj x y) :
    boxBoundary d n x ∧ boxBoundary d n y := by
  obtain ⟨hne, hreach⟩ := h
  have hn : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    apply hne
    apply Subtype.ext
    have hx0 : (x : Site d) ∈ StatMech.Lattice.box d 0 := by rw [← hn0]; exact x.2
    have hy0 : (y : Site d) ∈ StatMech.Lattice.box d 0 := by rw [← hn0]; exact y.2
    rw [StatMech.Lattice.mem_box] at hx0 hy0
    funext i
    have hxi : (x : Site d) i = 0 := by
      have := hx0 i; omega
    have hyi : (y : Site d) i = 0 := by
      have := hy0 i; omega
    rw [hxi, hyi]
  have hbx : boxBoundary d n x := by
    have hne' : boxVertIncl d n x ≠ boxVertIncl d n y :=
      fun he => hne (boxVertIncl_injective d n he)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact boxBoundary_of_outsideGraph_adj d n hn ψ hadj
  have hby : boxBoundary d n y := by
    have hreach' : (outsideGraph d n ψ).Reachable (boxVertIncl d n y) (boxVertIncl d n x) :=
      hreach.symm
    have hne' : boxVertIncl d n y ≠ boxVertIncl d n x :=
      fun he => hne (boxVertIncl_injective d n he).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact boxBoundary_of_outsideGraph_adj d n hn ψ hadj
  exact ⟨hbx, hby⟩

/-- The induced wiring lies below the clique on `∂Λ_n`. -/
lemma inducedWiring_le_wired (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    inducedWiring d n ψ ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n) := by
  intro x y hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  obtain ⟨hbx, hby⟩ := inducedWiring_only_bdry d n ψ hxy
  exact ⟨(inducedWiring d n ψ).ne_of_adj hxy, hbx, hby⟩

/-!
## G. Domination by the wired measure
-/

lemma condBcProb_psiExt_sum_eq_inducedBox (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n + 1))))) :
    (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ *
        condBcProb (boxGraph d (n + 1))
          (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) p q
          (innerEdgeFinset d n) ψ ρ)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω
            * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω := by
  classical
  have hsupp : ∀ ρ ∉ condFibre (innerEdgeFinset d n) ψ,
      B.indicator (fun _ => (1 : ℝ)) ρ *
        condBcProb (boxGraph d (n + 1))
          (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) p q
          (innerEdgeFinset d n) ψ ρ = 0 := by
    intro ρ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [ite_eq_right hρ, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (condFibre (innerEdgeFinset d n) ψ))
    (fun ρ _ hρ => hsupp ρ hρ)]
  rw [condFibre_eq_image_psiExt]
  rw [Finset.sum_image (fun a _ b _ h => by
    have := congrArg (innerRestrict d n) h
    rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [condBcProb_psiExt_eq_bcProb d n hp hp1 hq ψ ω]
  have hind : B.indicator (fun _ => (1 : ℝ)) (psiExt d n ψ ω)
      = (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : psiExt d n ψ ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]
  rw [hind]

lemma condBcProb_psiExt_dominated (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
        * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (boxGraph d n)
              (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) p q ω :=
  bcProb_mono_bc (boxGraph d n) (inducedWiring d n ψ)
    (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n))
    (inducedWiring_le_wired d n ψ) hp hp1 hq hA

/-- For `q ≥ 1`, the measure on `Λ_n` with the induced wiring is dominated by the wired measure on
`Λ_n`. -/
lemma condBcProb_psiExt_dominated_wired (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
        * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  refine (condBcProb_psiExt_dominated d n ψ hp hp1 hq hA).trans_eq ?_
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [bcProb_clique_eq_wiredFkProb]

end FK

end StatMech
