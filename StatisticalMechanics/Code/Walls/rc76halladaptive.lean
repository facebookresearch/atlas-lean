/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Code.Walls.rc75adaptiveswap
import Code.Walls.rc78hallmarriage

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}











def swapSet (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    ConfigSpace (Fin n) × ConfigSpace (Fin n) :=
  (fun j => if j ∈ L then p.2 j else p.1 j, fun j => if j ∈ L then p.1 j else p.2 j)


theorem swapSet_involutive (L : Finset (Fin n)) : Function.Involutive (swapSet L) := by
  intro p
  unfold swapSet
  ext j <;> simp only [] <;> split_ifs with h <;> rfl



theorem swapSet_bijective (L : Finset (Fin n)) : Function.Bijective (swapSet L) :=
  (swapSet_involutive L).bijective


theorem swapSet_off (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) {j : Fin n}
    (hj : j ∉ L) : (swapSet L p).1 j = p.1 j ∧ (swapSet L p).2 j = p.2 j := by
  refine ⟨?_, ?_⟩ <;> simp only [swapSet, if_neg hj]



theorem swapSet_on (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) {j : Fin n}
    (hj : j ∈ L) : (swapSet L p).1 j = p.2 j ∧ (swapSet L p).2 j = p.1 j := by
  refine ⟨?_, ?_⟩ <;> simp only [swapSet, if_pos hj]



theorem swapSet_singleton (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    swapSet {i} p = swapAt i p := by
  unfold swapSet swapAt
  ext j <;> simp only [Finset.mem_singleton] <;> split_ifs with h <;> subst_vars <;> rfl


















theorem rc76_swapSet_mapsInto_of_witness (A B : Set (ConfigSpace (Fin n)))
    {K L : Finset (Fin n)} (hKL : Disjoint K L) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B (L : Set (Fin n)) ω₁) :
    (swapSet L (ω₁, ω₂)).1 ∈ A ∧ (swapSet L (ω₁, ω₂)).2 ∈ B := by
  refine ⟨?_, ?_⟩
  · apply hA
    intro e he
    have heL : e ∉ L := by
      intro hL
      exact (Finset.disjoint_left.mp hKL he) hL
    exact (swapSet_off L (ω₁, ω₂) heL).1
  · apply hB
    intro e he
    rw [Finset.mem_coe] at he
    exact (swapSet_on L (ω₁, ω₂) he).2



theorem rc76_swapSet_mapsInto_singleton (A B : Set (ConfigSpace (Fin n)))
    {K : Finset (Fin n)} {i : Fin n} (hKi : Disjoint K {i}) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B ({i} : Finset (Fin n)) ω₁) :
    (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B := by
  rw [← swapSet_singleton i (ω₁, ω₂)]
  exact rc76_swapSet_mapsInto_of_witness A B hKi ω₁ ω₂ hA hB

















def rc76_reachNbhd (A B : Finset (ConfigSpace (Fin n)))
    (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    Finset (ConfigSpace (Fin n) × ConfigSpace (Fin n)) :=
  (A ×ˢ B).filter (fun q => ∃ S : Finset (Fin n), swapSet S p = q)


theorem rc76_mem_reachNbhd (A B : Finset (ConfigSpace (Fin n)))
    (p q : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    q ∈ rc76_reachNbhd A B p ↔ (q.1 ∈ A ∧ q.2 ∈ B) ∧ ∃ S : Finset (Fin n), swapSet S p = q := by
  classical
  unfold rc76_reachNbhd
  rw [Finset.mem_filter, Finset.mem_product]







theorem rc76_hall_iff_plan (A B : Finset (ConfigSpace (Fin n)))
    (src : Finset (ConfigSpace (Fin n) × ConfigSpace (Fin n))) :
    (∀ T : Finset (ConfigSpace (Fin n) × ConfigSpace (Fin n)), T ⊆ src →
        T.card ≤ (T.biUnion (fun p => rc76_reachNbhd A B p)).card) ↔
      ∃ f : (ConfigSpace (Fin n) × ConfigSpace (Fin n)) → (ConfigSpace (Fin n) × ConfigSpace (Fin n)),
        Set.InjOn f src ∧ ∀ p ∈ src, f p ∈ rc76_reachNbhd A B p := by
  classical
  
  have hHall := Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun p : (↥src) => rc76_reachNbhd A B (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)))
  
  have hbi : ∀ s : Finset (↥src),
      (s.map (Function.Embedding.subtype _)).biUnion (fun p => rc76_reachNbhd A B p)
        = s.biUnion (fun p => rc76_reachNbhd A B (p : _)) := by
    intro s
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, hq⟩; exact ⟨y, hy, hq⟩
    · rintro ⟨y, hy, hq⟩; exact ⟨(y : _), ⟨y, hy, rfl⟩, hq⟩
  constructor
  · intro hmar
    
    have hsub : ∀ s : Finset (↥src), s.card ≤
        (s.biUnion (fun p => rc76_reachNbhd A B (p : _))).card := by
      intro s
      have himg := hmar (s.map (Function.Embedding.subtype _))
        (by intro x hx; simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
            obtain ⟨y, _, rfl⟩ := hx; exact y.2)
      rw [Finset.card_map, hbi s] at himg
      exact himg
    obtain ⟨f, hfinj, hfmem⟩ := hHall.mp hsub
    
    classical
    refine ⟨fun p => if hp : p ∈ src then f ⟨p, hp⟩ else p, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe] at hx hy
      simp only [dif_pos hx, dif_pos hy] at hxy
      have := hfinj hxy
      exact congrArg Subtype.val this
    · intro p hp
      simp only [dif_pos hp]
      exact hfmem ⟨p, hp⟩
  · rintro ⟨f, hinj, hmem⟩
    
    
    intro T hT
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      rw [Finset.mem_coe] at hp
      rw [Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨p, hp, hmem p (hT hp)⟩
    · intro x hx y hy hxy
      exact hinj (Finset.mem_coe.mpr (hT hx)) (Finset.mem_coe.mpr (hT hy)) hxy








def rc76_source (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  rc75_sourceF A B


def rc76_target (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  rc75_prodF A B


def rc76_wall (A B : Finset (ConfigSpace (Fin 2))) : Prop :=
  2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card

instance (A B : Finset (ConfigSpace (Fin 2))) : Decidable (rc76_wall A B) := by
  unfold rc76_wall; infer_instance




def rc76_reachNbhdF (A B : Finset (ConfigSpace (Fin 2)))
    (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (A ×ˢ B).filter (fun q => ∃ S ∈ (Finset.univ : Finset (Fin 2)).powerset, swapSet S p = q)



def rc76_marriage (A B : Finset (ConfigSpace (Fin 2))) : Prop :=
  ∀ T ∈ (rc76_source A B).powerset,
    T.card ≤ (T.biUnion (fun p => rc76_reachNbhdF A B p)).card

instance (A B : Finset (ConfigSpace (Fin 2))) : Decidable (rc76_marriage A B) := by
  unfold rc76_marriage; infer_instance








set_option maxRecDepth 100000 in


theorem rc76_swapSet_reachable_iff_colType
    (p q : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    (∃ S ∈ (Finset.univ : Finset (Fin 2)).powerset, swapSet S p = q) ↔
      rc78_colTypeF q = rc78_colTypeF p := by
  decide +revert +kernel



theorem rc76_reachNbhdF_eq_rc78_nbhd
    (A B : Finset (ConfigSpace (Fin 2)))
    (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc76_reachNbhdF A B p = rc78_nbhd A B p := by
  ext q
  simp only [rc76_reachNbhdF, rc78_nbhd, rc75_prodF, Finset.mem_filter,
    Finset.mem_product, rc76_swapSet_reachable_iff_colType]







theorem rc76_marriage_iff_wall :
    ∀ A B : Finset (ConfigSpace (Fin 2)), rc76_marriage A B ↔ rc76_wall A B := by
  intro A B
  have hdom : rc78_PerOrbitDom A B := rc78_perOrbitDom_fin2 A B
  have hmar78 : rc78_Marriage A B := rc78_marriage_of_perOrbitDom A B hdom
  have hmar76 : rc76_marriage A B := by
    intro T hT
    simpa only [rc76_source, rc78_Marriage, rc76_reachNbhdF_eq_rc78_nbhd] using
      hmar78 T hT
  have hwall : rc76_wall A B := by
    have hplan := rc78_existsInjective_of_perOrbitDom A B hdom
    exact rc78_count_of_existsInjective A B hplan
  exact iff_of_true hmar76 hwall

set_option maxRecDepth 8000 in








theorem rc76_marriage_binds_at_proper_subset :
    ∃ T ∈ (rc76_source rc75_gA rc75_gB).powerset,
      T.Nonempty ∧ T ≠ rc76_source rc75_gA rc75_gB ∧
      (T.biUnion (fun p => rc76_reachNbhdF rc75_gA rc75_gB p)).card < (rc76_source rc75_gA rc75_gB).card := by
  decide

set_option maxRecDepth 8000 in







theorem rc76_count_insufficient_arbitrary_source :
    let S₀ : Finset (ConfigSpace (Fin 2)) := {rc75_cfg false true}
    let A : Finset (ConfigSpace (Fin 2)) := {rc75_cfg true false, rc75_cfg true true}
    let B : Finset (ConfigSpace (Fin 2)) := Finset.univ
    let src : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) := S₀ ×ˢ Finset.univ
    2 ^ 2 * S₀.card ≤ A.card * B.card ∧
      (src.biUnion (fun p => rc76_reachNbhdF A B p)).card < src.card := by
  decide

end StatMech.Walls
