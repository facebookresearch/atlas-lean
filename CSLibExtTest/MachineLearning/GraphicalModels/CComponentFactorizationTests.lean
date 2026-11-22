/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CComponentFactorization
import Mathlib.Tactic.FinCases

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.BayesNet
open Finset MetaMathlibExt.FiniteWeight
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  (b : BayesNet α n) (L : Finset (Fin n))

theorem observedLaw_empty (v : {i : Fin n // i ∉ (Finset.empty : Finset (Fin n))} → α) :
    b.observedLaw Finset.empty v = b.joint (extendObs Finset.empty v) := by
  classical
  have hU : ((Finset.empty : Finset (Fin n))ᶜ : Finset (Fin n)) = Finset.univ :=
    Finset.compl_empty
  have hq : ∀ y : Fin n → α,
      (∀ i ∈ (Set.univ : Set (Fin n)), y i = extendObs Finset.empty v i) ↔
        y = extendObs Finset.empty v := by
    intro y
    constructor
    · intro hy
      funext i
      exact hy i (Set.mem_univ i)
    · intro hy i _
      rw [hy]
  unfold observedLaw marginal
  rw [hU, Finset.coe_univ, Finset.sum_filter]
  simp only [hq]
  rw [Finset.sum_ite_eq']
  simp

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem cComponents_empty :
    (b.latentProjection Finset.empty).cComponents =
      Finset.univ.image Singleton.singleton := by
  classical
  have hno : ∀ u w : {v : Fin n // v ∉ (Finset.empty : Finset (Fin n))},
      ¬ (b.latentProjection Finset.empty).bidir.Adj u w := by
    intro u w hadj
    rw [b.latentProjection_bidir_adj_iff Finset.empty u w] at hadj
    obtain ⟨-, t, ht, _, _⟩ := hadj
    exact Finset.notMem_empty t ht
  have hreach : ∀ u w : {v : Fin n // v ∉ (Finset.empty : Finset (Fin n))},
      (b.latentProjection Finset.empty).bidir.Reachable u w ↔ u = w := by
    intro u w
    rw [SimpleGraph.reachable_iff_reflTransGen]
    constructor
    · intro h
      induction h with
      | refl => rfl
      | tail _ hadj _ => exact absurd hadj (hno _ _)
    · intro h
      rw [h]
  have hcomp : ∀ v : {v : Fin n // v ∉ (Finset.empty : Finset (Fin n))},
      Finset.univ.filter (· ∈ (b.latentProjection Finset.empty).cComponent v) = {v} := by
    intro v
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      ADMG.mem_cComponent_iff, hreach]
    exact eq_comm
  unfold ADMG.cComponents
  simp only [hcomp]

noncomputable def fig1aNet : BayesNet Bool 4 where
  pa := fun k => match k with
    | ⟨0, _⟩ => ∅
    | ⟨1, _⟩ => ({0} : Finset (Fin 1))
    | ⟨2, _⟩ => ({0, 1} : Finset (Fin 2))
    | ⟨3, _⟩ => ({2} : Finset (Fin 3))
  cpt := fun _ _ => Convexity.StdSimplex.single false

def fig1aX : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))} := ⟨1, by decide⟩

def fig1aZ : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))} := ⟨2, by decide⟩

def fig1aY : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))} := ⟨3, by decide⟩

theorem fig1a_pa0 : fig1aNet.pa 0 = ∅ := rfl

theorem fig1a_pa1 : fig1aNet.pa 1 = ({0} : Finset (Fin 1)) := rfl

theorem fig1a_pa2 : fig1aNet.pa 2 = ({0, 1} : Finset (Fin 2)) := rfl

theorem fig1a_pa3 : fig1aNet.pa 3 = ({2} : Finset (Fin 3)) := rfl

theorem fig1a_edge0 (v : Fin 4) : fig1aNet.Edge 0 v ↔ v = 1 ∨ v = 2 := by
  fin_cases v
  · constructor
    · rintro ⟨h, -⟩
      exact absurd h (by decide)
    · rintro (h | h) <;> simp at h
  · constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact ⟨by decide, by decide⟩
  · constructor
    · intro _
      exact Or.inr rfl
    · intro _
      exact ⟨by decide, by decide⟩
  · show fig1aNet.Edge 0 3 ↔ (3 : Fin 4) = 1 ∨ (3 : Fin 4) = 2
    constructor
    · rintro ⟨h, hmem⟩
      rw [fig1a_pa3, Finset.mem_singleton] at hmem
      simp at hmem
    · rintro (h | h) <;> simp at h

theorem fig1a_rtg0 (m : Fin 4)
    (h : Relation.ReflTransGen
      (fun x y => fig1aNet.Edge x y ∧ y ∈ ({0} : Finset (Fin 4))) 0 m) : m = 0 := by
  induction h with
  | refl => rfl
  | tail _ hstep _ =>
    obtain ⟨hedge0, hmem⟩ := hstep
    rw [Finset.mem_singleton] at hmem
    subst hmem
    exact False.elim (Fin.not_lt_zero _ (fig1aNet.edge_lt hedge0))

theorem fig1a_LP0 (v : Fin 4) :
    fig1aNet.LatentPath ({0} : Finset (Fin 4)) 0 v ↔ fig1aNet.Edge 0 v := by
  constructor
  · rintro ⟨m, hpath, hedge⟩
    have hm : m = 0 := fig1a_rtg0 m hpath
    subst hm
    exact hedge
  · intro h
    exact ⟨0, Relation.ReflTransGen.refl, h⟩

theorem fig1a_mem_obs (v : Fin 4) (hv : v ∉ ({0} : Finset (Fin 4))) :
    v = 1 ∨ v = 2 ∨ v = 3 := by
  fin_cases v
  · simp at hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem fig1a_adj (a b : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))}) :
    (fig1aNet.latentProjection ({0} : Finset (Fin 4))).bidir.Adj a b ↔
      (a = fig1aX ∧ b = fig1aZ) ∨ (a = fig1aZ ∧ b = fig1aX) := by
  rw [fig1aNet.latentProjection_bidir_adj_iff]
  constructor
  · rintro ⟨hne, t, ht, h1, h2⟩
    rw [Finset.mem_singleton] at ht
    subst ht
    rw [fig1a_LP0, fig1a_edge0] at h1 h2
    have ha : a = fig1aX ∨ a = fig1aZ := by
      rcases h1 with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    have hb : b = fig1aX ∨ b = fig1aZ := by
      rcases h2 with h2 | h2
      · exact Or.inl (Subtype.ext h2)
      · exact Or.inr (Subtype.ext h2)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hne
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨by decide, 0, by decide, ?_, ?_⟩
      · rw [fig1a_LP0, fig1a_edge0]
        exact Or.inl rfl
      · rw [fig1a_LP0, fig1a_edge0]
        exact Or.inr rfl
    · refine ⟨by decide, 0, by decide, ?_, ?_⟩
      · rw [fig1a_LP0, fig1a_edge0]
        exact Or.inr rfl
      · rw [fig1a_LP0, fig1a_edge0]
        exact Or.inl rfl

theorem fig1a_reachX (x : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))}) :
    (fig1aNet.latentProjection ({0} : Finset (Fin 4))).bidir.Reachable fig1aX x ↔
      x = fig1aX ∨ x = fig1aZ := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hadj ih =>
      rw [fig1a_adj] at hadj
      rcases ih with rfl | rfl
      · rcases hadj with ⟨-, hxz⟩ | ⟨hxz, -⟩
        · exact Or.inr hxz
        · exact absurd hxz (by decide)
      · rcases hadj with ⟨hzx, -⟩ | ⟨-, hzx⟩
        · exact absurd hzx (by decide)
        · exact Or.inl hzx
  · rintro (rfl | rfl)
    · exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      rw [fig1a_adj]
      exact Or.inl ⟨rfl, rfl⟩

theorem fig1a_reachZ (x : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))}) :
    (fig1aNet.latentProjection ({0} : Finset (Fin 4))).bidir.Reachable fig1aZ x ↔
      x = fig1aX ∨ x = fig1aZ := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Or.inr rfl
    | tail _ hadj ih =>
      rw [fig1a_adj] at hadj
      rcases ih with rfl | rfl
      · rcases hadj with ⟨-, hxz⟩ | ⟨hxz, -⟩
        · exact Or.inr hxz
        · exact absurd hxz (by decide)
      · rcases hadj with ⟨hzx, -⟩ | ⟨-, hzx⟩
        · exact absurd hzx (by decide)
        · exact Or.inl hzx
  · rintro (rfl | rfl)
    · apply Relation.ReflTransGen.single
      rw [fig1a_adj]
      exact Or.inr ⟨rfl, rfl⟩
    · exact Relation.ReflTransGen.refl

theorem fig1a_reachY (x : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))}) :
    (fig1aNet.latentProjection ({0} : Finset (Fin 4))).bidir.Reachable fig1aY x ↔
      x = fig1aY := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hadj ih =>
      subst ih
      rw [fig1a_adj] at hadj
      rcases hadj with ⟨hyx, -⟩ | ⟨hyz, -⟩
      · exact absurd hyx (by decide)
      · exact absurd hyz (by decide)
  · rintro rfl
    exact Relation.ReflTransGen.refl

open scoped Classical in
theorem fig1a_compX :
    Finset.univ.filter
        (· ∈ (fig1aNet.latentProjection ({0} : Finset (Fin 4))).cComponent fig1aX) =
      {fig1aX, fig1aZ} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, ADMG.mem_cComponent_iff, fig1a_reachX]

open scoped Classical in
theorem fig1a_compZ :
    Finset.univ.filter
        (· ∈ (fig1aNet.latentProjection ({0} : Finset (Fin 4))).cComponent fig1aZ) =
      {fig1aX, fig1aZ} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, ADMG.mem_cComponent_iff, fig1a_reachZ]

open scoped Classical in
theorem fig1a_compY :
    Finset.univ.filter
        (· ∈ (fig1aNet.latentProjection ({0} : Finset (Fin 4))).cComponent fig1aY) =
      {fig1aY} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    ADMG.mem_cComponent_iff, fig1a_reachY]

theorem fig1a_univ :
    (Finset.univ : Finset {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))}) =
      {fig1aX, fig1aZ, fig1aY} := by
  ext ⟨v, hv⟩
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  rcases fig1a_mem_obs v hv with rfl | rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Or.inl (Subtype.ext rfl))
  · exact Or.inr (Or.inr (Subtype.ext rfl))

theorem fig1a_cComponents :
    (fig1aNet.latentProjection ({0} : Finset (Fin 4))).cComponents =
      {{fig1aX, fig1aZ}, {fig1aY}} := by
  unfold ADMG.cComponents
  nth_rewrite 2 [fig1a_univ]
  simp only [Finset.image_insert, Finset.image_singleton]
  rw [fig1a_compX, fig1a_compZ, fig1a_compY]
  ext S
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem fig1a_factorization (v : {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))} → Bool) :
    fig1aNet.observedLaw ({0} : Finset (Fin 4)) v =
      fig1aNet.qFactor ({0} : Finset (Fin 4)) {fig1aX, fig1aZ} v *
        fig1aNet.qFactor ({0} : Finset (Fin 4)) {fig1aY} v := by
  rw [fig1aNet.observedLaw_eq_prod_qFactor, fig1a_cComponents]
  exact Finset.prod_pair (by decide)

noncomputable def latentParentNet : BayesNet Bool 3 where
  pa := fun k => match k with
    | ⟨0, _⟩ => ∅
    | ⟨1, _⟩ => ({0} : Finset (Fin 1))
    | ⟨2, _⟩ => ({1} : Finset (Fin 2))
  cpt := fun _ _ => Convexity.StdSimplex.single false

def latParA0 : {i : Fin 3 // i ∉ ({1} : Finset (Fin 3))} := ⟨0, by decide⟩

def latParA2 : {i : Fin 3 // i ∉ ({1} : Finset (Fin 3))} := ⟨2, by decide⟩

theorem latPar_pa0 : latentParentNet.pa 0 = ∅ := rfl

theorem latPar_pa1 : latentParentNet.pa 1 = ({0} : Finset (Fin 1)) := rfl

theorem latPar_pa2 : latentParentNet.pa 2 = ({1} : Finset (Fin 2)) := rfl

theorem latPar_edge_into1 (x : Fin 3) : latentParentNet.Edge x 1 ↔ x = 0 := by
  constructor
  · rintro ⟨h, -⟩
    have hv : x.val = 0 := Nat.lt_one_iff.mp h
    exact Fin.ext hv
  · rintro rfl
    exact ⟨by decide, by decide⟩

theorem latPar_edge_from1 (v : Fin 3) : latentParentNet.Edge 1 v ↔ v = 2 := by
  fin_cases v
  · constructor
    · rintro ⟨h, -⟩
      exact absurd h (by decide)
    · rintro h
      simp at h
  · constructor
    · rintro ⟨h, -⟩
      exact absurd h (by decide)
    · rintro h
      simp at h
  · constructor
    · intro _
      rfl
    · intro _
      exact ⟨by decide, by decide⟩

theorem latPar_rtg1 (m : Fin 3)
    (h : Relation.ReflTransGen
      (fun x y => latentParentNet.Edge x y ∧ y ∈ ({1} : Finset (Fin 3))) 1 m) :
    m = 1 := by
  induction h with
  | refl => rfl
  | tail _ hstep _ =>
    obtain ⟨-, hmem⟩ := hstep
    rw [Finset.mem_singleton] at hmem
    exact hmem

theorem latPar_LP1 (v : Fin 3) :
    latentParentNet.LatentPath ({1} : Finset (Fin 3)) 1 v ↔
      latentParentNet.Edge 1 v := by
  constructor
  · rintro ⟨m, hpath, hedge⟩
    have hm : m = 1 := latPar_rtg1 m hpath
    subst hm
    exact hedge
  · intro h
    exact ⟨1, Relation.ReflTransGen.refl, h⟩

theorem latPar_mem_obs (v : Fin 3) (hv : v ∉ ({1} : Finset (Fin 3))) : v = 0 ∨ v = 2 := by
  fin_cases v
  · exact Or.inl rfl
  · simp at hv
  · exact Or.inr rfl

theorem latPar_noAdj (a b : {i : Fin 3 // i ∉ ({1} : Finset (Fin 3))}) :
    ¬ (latentParentNet.latentProjection ({1} : Finset (Fin 3))).bidir.Adj a b := by
  rw [latentParentNet.latentProjection_bidir_adj_iff]
  rintro ⟨hne, t, ht, h1, h2⟩
  rw [Finset.mem_singleton] at ht
  subst ht
  rw [latPar_LP1, latPar_edge_from1] at h1 h2
  have ha : a = latParA2 := Subtype.ext h1
  have hb : b = latParA2 := Subtype.ext h2
  exact hne (ha.trans hb.symm)

theorem latPar_reach (a b : {i : Fin 3 // i ∉ ({1} : Finset (Fin 3))}) :
    (latentParentNet.latentProjection ({1} : Finset (Fin 3))).bidir.Reachable a b ↔
      a = b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hadj _ => exact absurd hadj (latPar_noAdj _ _)
  · rintro rfl
    exact Relation.ReflTransGen.refl

open scoped Classical in
theorem latPar_comp (v : {i : Fin 3 // i ∉ ({1} : Finset (Fin 3))}) :
    Finset.univ.filter
        (· ∈ (latentParentNet.latentProjection ({1} : Finset (Fin 3))).cComponent v) =
      {v} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    ADMG.mem_cComponent_iff, latPar_reach]
  exact eq_comm

theorem latPar_univ :
    (Finset.univ : Finset {i : Fin 3 // i ∉ ({1} : Finset (Fin 3))}) =
      {latParA0, latParA2} := by
  ext ⟨v, hv⟩
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  rcases latPar_mem_obs v hv with rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)

theorem latentParent_cComponents :
    (latentParentNet.latentProjection ({1} : Finset (Fin 3))).cComponents =
      {{latParA0}, {latParA2}} := by
  unfold ADMG.cComponents
  simp only [latPar_comp]
  rw [latPar_univ]
  simp only [Finset.image_insert, Finset.image_singleton]

theorem latentParent_factorization
    (v : {i : Fin 3 // i ∉ ({1} : Finset (Fin 3))} → Bool) :
    latentParentNet.observedLaw ({1} : Finset (Fin 3)) v =
      latentParentNet.qFactor ({1} : Finset (Fin 3)) {latParA0} v *
        latentParentNet.qFactor ({1} : Finset (Fin 3)) {latParA2} v := by
  rw [latentParentNet.observedLaw_eq_prod_qFactor, latentParent_cComponents]
  exact Finset.prod_pair (by decide)


end Cslib.MachineLearning.GraphicalModels.BayesNet
