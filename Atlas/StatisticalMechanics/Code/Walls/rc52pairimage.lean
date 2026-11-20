/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Code.Walls.rc51refute
import Code.Walls.rc22doublecover

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]













def rc52_pairImage (S K L : Finset α) : Finset α × Finset α :=
  (rc49_jointImage S K L, (rc49_jointImage S K L)ᶜ)


@[simp] theorem rc52_pairImage_left_eq_jointImage (S K L : Finset α) :
    (rc52_pairImage S K L).1 = rc49_jointImage S K L := rfl


@[simp] theorem rc52_pairImage_snd (S K L : Finset α) :
    (rc52_pairImage S K L).2 = (rc49_jointImage S K L)ᶜ := rfl

open Classical in






theorem rc52_pairImage_mem_complPairs {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L)
    (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    rc52_pairImage S K L ∈ rc22_complPairs 𝒜 ℬ := by
  rw [rc52_pairImage, rc22_mem_complPairs]
  have hmem : rc49_jointImage S K L ∈ rc10_reflInter 𝒜 ℬ :=
    rc49_jointImage_mem_reflInter hKL hKA hLB
  rw [rc20_mem_reflInter] at hmem
  exact ⟨hmem.1, hmem.2, disjoint_compl_right, by simp⟩





theorem rc52_pairImage_determined_by_left {𝒜 ℬ : Finset (Finset α)}
    {p : Finset α × Finset α} (hp : p ∈ rc22_complPairs 𝒜 ℬ) :
    p.1ᶜ = p.2 := by
  rw [rc22_mem_complPairs] at hp
  exact rc22_compl_of_disjoint_union hp.2.2.1 hp.2.2.2











theorem rc52_pairImage_injOn_iff_jointImage_injOn (K L : Finset α) (s : Set (Finset α)) :
    Set.InjOn (fun S => rc52_pairImage S K L) s
      ↔ Set.InjOn (fun S => rc49_jointImage S K L) s := by
  constructor
  · 
    intro h a ha b hb hab
    apply h ha hb
    simp only [rc52_pairImage, hab]
  · 
    intro h a ha b hb hab
    apply h ha hb
    have := congrArg Prod.fst hab
    simpa [rc52_pairImage] using this

open Classical in







theorem rc52_pairImage_collapses_refuter :
    rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0})
        = rc52_pairImage ({1} : Finset (Fin 3)) ({0, 2}) ({1})
      ∧ rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0}) = (∅, (univ : Finset (Fin 3))) := by
  constructor
  · rw [rc52_pairImage, rc52_pairImage]
    refine Prod.ext ?_ ?_ <;> · simp only [rc49_jointImage]; decide
  · rw [rc52_pairImage]
    refine Prod.ext ?_ ?_ <;> · simp only [rc49_jointImage]; decide








open Classical in





theorem rc52_decoupled_pair_bound {𝒜 ℬ : Finset (Finset α)}
    {g : Finset α → Finset α × Finset α}
    (hinj : Set.InjOn g (rc20_famCylBox 𝒜 ℬ : Set (Finset α)))
    (hmem : ∀ S ∈ rc20_famCylBox 𝒜 ℬ,
      g S ∈ (rc10_reflInter 𝒜 ℬ) ×ˢ (rc10_reflInter 𝒜 ℬ)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ (#(rc10_reflInter 𝒜 ℬ)) ^ 2 := by
  have hle : #(rc20_famCylBox 𝒜 ℬ)
      ≤ #((rc10_reflInter 𝒜 ℬ) ×ˢ (rc10_reflInter 𝒜 ℬ)) :=
    Finset.card_le_card_of_injOn g hmem hinj
  rw [Finset.card_product] at hle
  rw [sq]
  exact hle







set_option maxRecDepth 4000 in



theorem rc52_wall_refuter_holds :
    (rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card
      ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card := by
  rw [rc51_Aref, rc51_Bref]; decide



open Classical in






























theorem rc52_reimer_pair_route_hits_black_box :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S K L : Finset (Fin 3)), Disjoint K L →
        (∀ T : Finset (Fin 3), T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ T : Finset (Fin 3), T ∩ L = S ∩ L → T ∈ ℬ) →
        rc52_pairImage S K L ∈ rc22_complPairs 𝒜 ℬ)
      ∧ (∀ (K L : Finset (Fin 3)) (s : Set (Finset (Fin 3))),
          Set.InjOn (fun S => rc52_pairImage S K L) s
            ↔ Set.InjOn (fun S => rc49_jointImage S K L) s)
      ∧ (rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0})
            = rc52_pairImage ({1} : Finset (Fin 3)) ({0, 2}) ({1})
          ∧ rc52_pairImage ({0} : Finset (Fin 3)) ({1, 2}) ({0}) = (∅, (univ : Finset (Fin 3))))
      ∧ ((rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card
          ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card) :=
  ⟨fun _ _ _ _ _ hKL hKA hLB => rc52_pairImage_mem_complPairs hKL hKA hLB,
    fun K L s => rc52_pairImage_injOn_iff_jointImage_injOn K L s,
    rc52_pairImage_collapses_refuter,
    rc52_wall_refuter_holds⟩

end StatMech.Walls
