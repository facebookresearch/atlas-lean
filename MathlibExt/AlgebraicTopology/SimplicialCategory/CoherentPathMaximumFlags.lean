/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathLastMaximum

/-!
# Actual flag sections of original coherent last-front maxima

The front ordinal maps to the same original zero-to-last coherent Hom by
its complete initial flags. The original maximum reads the same supplied
front label. Each original path is contained in its actual maximum flag;
no strict inverse is asserted for paths with skipped front vertices.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.CoherentRealization.PathMaximumFlags
open PathLastMaximum
variable {n : ℕ}

/-- The original complete flag through the supplied front vertex, retaining zero and the
actual last endpoint. -/
def flag (k : Fin (n + 1)) : LastPath.{u} (0 : Fin (n + 1)) where
  I := Set.Iic (ULift.up.{u} k.castSucc) ∪ {ULift.up.{u} (Fin.last (n + 1))}
  left := Or.inl (Fin.zero_le _)
  right := Or.inr rfl
  left_le x _ := Fin.zero_le x.down
  le_right x _ := Fin.le_last x.down

/-- The actual original front labels of a flag are precisely those at or below its supplied
vertex. -/
theorem mem_front_flag (k j : Fin (n + 1)) : j ∈ frontSet 0 (flag.{u} k) ↔ j ≤ k := by
  rw [mem_frontSet]
  change (ULift.up.{u} j.castSucc ≤ ULift.up.{u} k.castSucc ∨ ULift.up.{u} j.castSucc = ULift.up.{u}
    (Fin.last (n + 1))) ↔ j ≤ k
  constructor
  · rintro (h | h)
    · change j.val ≤ k.val at h
      exact h
    · exact False.elim ((ne_of_lt (Fin.castSucc_lt_last j)) (congrArg ULift.down h))
  · intro h
    left
    exact h

/-- The genuine original maximum of a complete flag is exactly its supplied front vertex. -/
theorem maximum_flag (k : Fin (n + 1)) : maximum 0 (flag.{u} k) = k := by
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    exact (mem_front_flag k j).mp hj
  · exact le_maximum 0 (flag.{u} k) k ((mem_front_flag k k).mpr le_rfl)

/-- Increasing the original front label gives an actual inclusion of its complete flags. -/
theorem flag_mono {k l : Fin (n + 1)} (h : k ≤ l) : (flag.{u} k).I ⊆ (flag.{u} l).I := by
  rintro x (hx | hx)
  · left
    exact hx.trans (show ULift.up.{u} k.castSucc ≤ ULift.up.{u} l.castSucc from h)
  · exact Or.inr hx

/-- The genuine original flag functor from the same lifted front ordinal to the coherent
zero-to-last path category. -/
def flagFunctor : ULift.{u} (Fin (n + 1)) ⥤ LastPath.{u} (0 : Fin (n + 1)) where
  obj k := flag k.down
  map f := ⟨homOfLE (flag_mono f.down.down)⟩

/-- The original maximum functor has the actual flag functor as a section on every whole
front ordinal
  object and arrow. -/
theorem flag_section : flagFunctor.{u} ⋙ maximumFunctor (0 : Fin (n + 1)) =
  𝟭 (ULift.{u} (Fin (n + 1))) := by
  refine Functor.ext (fun k => ULift.ext (maximum_flag k.down)) ?_
  intro k l f
  exact Subsingleton.elim _ _

/-- Every original front member has its actual source ordinal preimage, distinct from the
last endpoint. -/
theorem front_vertex {p : LastPath.{u} (0 : Fin (n + 1))} {x : ULift.{u} (Fin (n + 2))}
    (hx : x ∈ p.I) (hLast : x ≠ ULift.up (Fin.last (n + 1))) :
    x ≤ ULift.up (maximum 0 p).castSucc := by
  have h₀ : x.down ≠ Fin.last (n + 1) := fun h => hLast (ULift.ext h)
  let j := x.down.castPred h₀
  have hj : j ∈ frontSet 0 p := by
    apply (mem_frontSet 0 p j).mpr
    have hJ : ULift.up.{u} j.castSucc = x := ULift.ext (Fin.castSucc_castPred x.down h₀)
    exact hJ.symm ▸ hx
  have h := le_maximum 0 p j hj
  have hJ : x.down = j.castSucc := (Fin.castSucc_castPred x.down h₀).symm
  have hV : x.down.val = j.val := congrArg Fin.val hJ
  change j.val ≤ (maximum 0 p).val at h
  change x.down.val ≤ (maximum 0 p).val
  exact hV.symm ▸ h

/-- The actual original path is contained in its complete maximum flag, including its
original last endpoint. -/
theorem path_le_flag (p : LastPath.{u} (0 : Fin (n + 1))) : p.I ⊆ (flag (maximum 0 p)).I := by
  classical
  intro x hx
  by_cases hLast : x = ULift.up (Fin.last (n + 1))
  · exact Or.inr hLast
  · exact Or.inl (front_vertex hx hLast)

end CategoryTheory.CoherentRealization.PathMaximumFlags
