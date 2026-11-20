/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gc86brerouteinjection
import Code.Walls.gc87brerouteinjection
import Code.Walls.gc88brereroutehall
import Code.Walls.gc89bmetricinjection
import Code.Walls.gc90bperfiberinject
import Code.Walls.gc91bglobalinjection

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]






theorem gc92b_degK_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) (w : W) : degK ends (K.image τ) w = degK ends K w := by
  unfold degK
  rw [Finset.filter_image, Finset.card_image_of_injective _ τ.injective]
  congr 1
  ext i
  simp only [Finset.mem_filter, hτ]


theorem gc92b_sources_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) : sources ends (K.image τ) = sources ends K := by
  ext w
  simp only [RandomCurrent.mem_sources, gc92b_degK_perm ends τ hτ K w]





theorem gc92b_adjStep_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) (a b : W) : adjStep ends (K.image τ) a b ↔ adjStep ends K a b := by
  unfold adjStep
  constructor
  · rintro ⟨i, hi, ha, hb, hne⟩
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact ⟨j, hj, by rwa [hτ] at ha, by rwa [hτ] at hb, hne⟩
  · rintro ⟨i, hi, ha, hb, hne⟩
    refine ⟨τ i, Finset.mem_image_of_mem τ hi, ?_, ?_, hne⟩
    · rwa [hτ]
    · rwa [hτ]


theorem gc92b_connK_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (hτ : ∀ i, ends (τ i) = ends i)
    (K : Finset ι) (a b : W) : connK ends (K.image τ) a b ↔ connK ends K a b := by
  unfold connK
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih ((gc92b_adjStep_perm ends τ hτ K _ _).1 hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih ((gc92b_adjStep_perm ends τ hτ K _ _).2 hstep)





theorem gc92b_image_sdiff (τ : Equiv.Perm ι) (m K : Finset ι) (hm : m.image τ = m) :
    (m \ K).image τ = m \ (K.image τ) := by
  rw [Finset.image_sdiff _ _ τ.injective, hm]





theorem gc92b_connK_complement_perm (ends : ι → Sym2 W) (τ : Equiv.Perm ι)
    (hτ : ∀ i, ends (τ i) = ends i) (m K : Finset ι) (hm : m.image τ = m) (a b : W) :
    connK ends (m \ (K.image τ)) a b ↔ connK ends (m \ K) a b := by
  rw [← gc92b_image_sdiff τ m K hm, gc92b_connK_perm ends τ hτ]



theorem gc92b_perm_mem_cogxgSet_iff (ends : ι → Sym2 W) (τ : Equiv.Perm ι)
    (hτ : ∀ i, ends (τ i) = ends i) (m : Finset ι) (hm : m.image τ = m) (o x g : W)
    (K₁ K₂ : Finset ι) :
    (K₁.image τ, K₂.image τ) ∈ gc91b_cogxgPairs ends m o x g
      ↔ (K₁, K₂) ∈ gc91b_cogxgPairs ends m o x g := by
  unfold gc91b_cogxgPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  rw [gc92b_sources_perm ends τ hτ, gc92b_sources_perm ends τ hτ,
      gc92b_connK_complement_perm ends τ hτ m K₁ hm]
  have hmem : ∀ a : ι, a ∈ m ↔ τ a ∈ m := by
    intro a; conv_rhs => rw [← hm]
    rw [Finset.mem_image]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hba⟩ => by rwa [← τ.injective hba]⟩
  constructor
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc⟩
    · intro a ha; rw [hmem]; exact h1 (Finset.mem_image_of_mem τ ha)
    · intro a ha; rw [hmem]; exact h2 (Finset.mem_image_of_mem τ ha)
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      exact hdis (Finset.mem_image_of_mem τ haK) (Finset.mem_image_of_mem τ haK2)
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc⟩
    · rw [← hm]; exact Finset.image_subset_image h1
    · rw [← hm]; exact Finset.image_subset_image h2
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      rw [Finset.mem_image] at haK haK2
      obtain ⟨i, hi, rfl⟩ := haK
      obtain ⟨j, hj, hij⟩ := haK2
      rw [τ.injective hij] at hj
      exact hdis hi hj



theorem gc92b_perm_mem_T3Set_iff (ends : ι → Sym2 W) (τ : Equiv.Perm ι)
    (hτ : ∀ i, ends (τ i) = ends i) (m : Finset ι) (hm : m.image τ = m) (o x y g : W)
    (J₁ J₂ : Finset ι) :
    (J₁.image τ, J₂.image τ) ∈ gc91b_T3Pairs ends m o x y g
      ↔ (J₁, J₂) ∈ gc91b_T3Pairs ends m o x y g := by
  unfold gc91b_T3Pairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  rw [gc92b_sources_perm ends τ hτ, gc92b_sources_perm ends τ hτ,
      gc92b_connK_complement_perm ends τ hτ m J₁ hm,
      gc92b_connK_complement_perm ends τ hτ m J₁ hm,
      gc92b_connK_complement_perm ends τ hτ m J₁ hm]
  have hmem : ∀ a : ι, a ∈ m ↔ τ a ∈ m := by
    intro a; conv_rhs => rw [← hm]
    rw [Finset.mem_image]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hba⟩ => by rwa [← τ.injective hba]⟩
  constructor
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc1, hc2, hc3⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc1, hc2, hc3⟩
    · intro a ha; rw [hmem]; exact h1 (Finset.mem_image_of_mem τ ha)
    · intro a ha; rw [hmem]; exact h2 (Finset.mem_image_of_mem τ ha)
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      exact hdis (Finset.mem_image_of_mem τ haK) (Finset.mem_image_of_mem τ haK2)
  · rintro ⟨⟨h1, h2⟩, hdis, hs1, hs2, hc1, hc2, hc3⟩
    refine ⟨⟨?_, ?_⟩, ?_, hs1, hs2, hc1, hc2, hc3⟩
    · rw [← hm]; exact Finset.image_subset_image h1
    · rw [← hm]; exact Finset.image_subset_image h2
    · rw [Finset.disjoint_left] at hdis ⊢
      intro a haK haK2
      rw [Finset.mem_image] at haK haK2
      obtain ⟨i, hi, rfl⟩ := haK
      obtain ⟨j, hj, hij⟩ := haK2
      rw [τ.injective hij] at hj
      exact hdis hi hj










def gc92b_pairAction (τ : Equiv.Perm ι) (s : Finset ι × Finset ι) : Finset ι × Finset ι :=
  (s.1.image τ, s.2.image τ)








theorem gc92b_no_equivariant_injection (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (m : Finset ι)
    {o x y g : W}
    {s₁ s₂ : Finset ι × Finset ι}
    (hs₁ : s₁ ∈ gc91b_cogxgPairs ends m o x g) (hs₂ : s₂ ∈ gc91b_cogxgPairs ends m o x g)
    (hswap : s₂ = gc92b_pairAction τ s₁) (hne : s₁ ≠ s₂)
    (hT3fixed : ∀ t ∈ gc91b_T3Pairs ends m o x y g, gc92b_pairAction τ t = t)
    (f : Finset ι × Finset ι → Finset ι × Finset ι)
    (hmaps : ∀ s ∈ gc91b_cogxgPairs ends m o x g, f s ∈ gc91b_T3Pairs ends m o x y g)
    (hequiv : f (gc92b_pairAction τ s₁) = gc92b_pairAction τ (f s₁))
    (hinj : Set.InjOn f (gc91b_cogxgPairs ends m o x g)) : False := by
  have h1 : f s₂ = gc92b_pairAction τ (f s₁) := by rw [hswap]; exact hequiv
  have h2 : gc92b_pairAction τ (f s₁) = f s₁ := hT3fixed (f s₁) (hmaps s₁ hs₁)
  have h3 : f s₂ = f s₁ := h1.trans h2
  exact hne ((hinj hs₁ hs₂ h3.symm))











theorem gc92b_wred_perm_fixes : ∀ i : Fin 4,
    gc88b_wredEnds (Equiv.swap (1 : Fin 4) 2 i) = gc88b_wredEnds i := by
  decide


theorem gc92b_wred_perm_fixes_univ :
    (univ : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = univ := by
  decide



theorem gc92b_wred_swap_cogxg :
    ({1} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({2} : Finset (Fin 4))
      ∧ ({2} : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = ({1} : Finset (Fin 4))
      ∧ (∅ : Finset (Fin 4)).image (Equiv.swap (1 : Fin 4) 2) = (∅ : Finset (Fin 4)) := by
  refine ⟨by decide, by decide, by decide⟩




theorem gc92b_wred_swap_fixes_T3 :
    gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)))
        = ((∅ : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))) := by
  refine ⟨by decide, by decide⟩









theorem gc92b_wred_mem_cogxg_one :
    (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3 := by
  unfold gc91b_cogxgPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨⟨Finset.subset_univ _, Finset.subset_univ _⟩, by decide, by decide, by decide, ?_⟩
  refine Relation.ReflTransGen.head (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩
    (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)



theorem gc92b_wred_mem_cogxg_two :
    (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3 := by
  unfold gc91b_cogxgPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨⟨Finset.subset_univ _, Finset.subset_univ _⟩, by decide, by decide, by decide, ?_⟩
  refine Relation.ReflTransGen.head (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩
    (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)



theorem gc92b_wred_cogxg_swapped :
    (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        ≠ (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
      ∧ gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))
        = (({2} : Finset (Fin 4)), (∅ : Finset (Fin 4))) := by
  refine ⟨by decide, by decide⟩

















theorem gc92b_wred_no_equivariant_injection
    (hT3fixed : ∀ t ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3,
        gc92b_pairAction (Equiv.swap (1 : Fin 4) 2) t = t)
    (f : Finset (Fin 4) × Finset (Fin 4) → Finset (Fin 4) × Finset (Fin 4))
    (hmaps : ∀ s ∈ gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3,
        f s ∈ gc91b_T3Pairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3)
    (hequiv : f (gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4))))
        = gc92b_pairAction (Equiv.swap (1 : Fin 4) 2)
          (f (({1} : Finset (Fin 4)), (∅ : Finset (Fin 4)))))
    (hinj : Set.InjOn f (gc91b_cogxgPairs gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 3)) :
    False := by
  refine gc92b_no_equivariant_injection gc88b_wredEnds (Equiv.swap (1 : Fin 4) 2)
    (univ : Finset (Fin 4)) (o := 0) (x := 1) (y := 2) (g := 3)
    gc92b_wred_mem_cogxg_one gc92b_wred_mem_cogxg_two
    gc92b_wred_cogxg_swapped.2.symm gc92b_wred_cogxg_swapped.1
    hT3fixed f hmaps hequiv hinj

















theorem gc92b_orbit_status (ends : ι → Sym2 W) (τ : Equiv.Perm ι) (m : Finset ι)
    (hτ : ∀ i, ends (τ i) = ends i) (hm : m.image τ = m) {o x y g : W}
    {s₁ s₂ : Finset ι × Finset ι}
    (hs₁ : s₁ ∈ gc91b_cogxgPairs ends m o x g) (hs₂ : s₂ ∈ gc91b_cogxgPairs ends m o x g)
    (hswap : s₂ = gc92b_pairAction τ s₁) (hne : s₁ ≠ s₂)
    (hT3fixed : ∀ t ∈ gc91b_T3Pairs ends m o x y g, gc92b_pairAction τ t = t) :
    
    (∀ K₁ K₂, (K₁.image τ, K₂.image τ) ∈ gc91b_cogxgPairs ends m o x g
        ↔ (K₁, K₂) ∈ gc91b_cogxgPairs ends m o x g)
    ∧ (∀ J₁ J₂, (J₁.image τ, J₂.image τ) ∈ gc91b_T3Pairs ends m o x y g
        ↔ (J₁, J₂) ∈ gc91b_T3Pairs ends m o x y g)
    
    ∧ (∀ f : Finset ι × Finset ι → Finset ι × Finset ι,
        (∀ s ∈ gc91b_cogxgPairs ends m o x g, f s ∈ gc91b_T3Pairs ends m o x y g) →
        f (gc92b_pairAction τ s₁) = gc92b_pairAction τ (f s₁) →
        Set.InjOn f (gc91b_cogxgPairs ends m o x g) → False) := by
  refine ⟨fun K₁ K₂ => gc92b_perm_mem_cogxgSet_iff ends τ hτ m hm o x g K₁ K₂,
      fun J₁ J₂ => gc92b_perm_mem_T3Set_iff ends τ hτ m hm o x y g J₁ J₂, ?_⟩
  intro f hmaps hequiv hinj
  exact gc92b_no_equivariant_injection ends τ m hs₁ hs₂ hswap hne hT3fixed f hmaps hequiv hinj
























theorem gc92b_machine_findings : True := trivial

end StatMech.Walls
