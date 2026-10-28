/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! The finite parent certificates imply a genuine actual Conway orbit lower bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual Conway representation acts on its original binary coordinate space. -/
instance sixthFrameOrbitCo1Action : MulAction Co1 (Fin 24 → ZMod 2) where
  smul g v := co1BinaryAction g v
  one_smul v := by
    change co1BinaryAction 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change co1BinaryAction (g * h) v = co1BinaryAction g (co1BinaryAction h v)
    rw [map_mul]
    rfl

/-- The frame catalogue interpreted in the actual binary space. -/
def sixthFrameOrbitVector (i : Fin 891) : Fin 24 → ZMod 2 :=
  monsterCo1GeometryBinaryMaskDecode (sixthFrameOrbitPoints i)

/-- The genuine initial frame coordinate, in the original hyperbolic basis. -/
def sixthFrameOrbitBase : Fin 24 → ZMod 2 := monsterCo1GeometryBinaryMaskDecode 2048

/-- Every catalogue value represents a distinct actual binary vector. -/
theorem sixthFrameOrbitVector_injective : Function.Injective sixthFrameOrbitVector := by
  intro i j h
  have hm := sixthFrameOrbitMaskDecode_injective _ _
    (sixthFrameOrbit_point_bounds i) (sixthFrameOrbit_point_bounds j) h
  apply Fin.ext
  exact (sixthFrameOrbit_lookup i).symm.trans
    ((congrArg sixthFrameOrbitLookup hm).trans (sixthFrameOrbit_lookup j))

/-- Actual generator bindings and membership turn the acyclic finite edges into orbit membership. -/
theorem sixthFrameOrbitVector_mem_orbit (K : Subgroup Co1) (g : Fin 15 → Co1)
    (hg : ∀ k, g k ∈ K)
    (hA : ∀ k v, co1BinaryAction (g k) v = sixthFrameOrbitColumnMatrix
      (sixthFrameOrbitColumns k) *ᵥ v) (i : Fin 891) :
    sixthFrameOrbitVector i ∈ MulAction.orbit K sixthFrameOrbitBase := by
  have hc : ∀ n : ℕ, ∀ hn : n < 891,
      sixthFrameOrbitVector ⟨n, hn⟩ ∈ MulAction.orbit K sixthFrameOrbitBase := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hz : n = 0
      · subst n
        have hi : (⟨0, hn⟩ : Fin 891) = 0 := Fin.ext rfl
        rw [hi]
        refine ⟨1, ?_⟩
        change (1 : K) • sixthFrameOrbitBase = sixthFrameOrbitVector 0
        rw [one_smul]
        change monsterCo1GeometryBinaryMaskDecode 2048 =
          monsterCo1GeometryBinaryMaskDecode (sixthFrameOrbitPoints 0)
        rw [sixthFrameOrbit_initial]
      let j : Fin 891 := ⟨n, hn⟩
      have hj : j ≠ 0 := fun he => hz (congrArg Fin.val he)
      have hp := sixthFrameOrbit_parent_before j hj
      obtain ⟨a, ha⟩ := ih (sixthFrameOrbitParent j).val hp (sixthFrameOrbitParent j).isLt
      refine ⟨(⟨g (sixthFrameOrbitGenerator j), hg _⟩ : K) * a, ?_⟩
      change ((⟨g (sixthFrameOrbitGenerator j), hg _⟩ : K) * a) •
        sixthFrameOrbitBase = sixthFrameOrbitVector j
      change a • sixthFrameOrbitBase =
        sixthFrameOrbitVector (sixthFrameOrbitParent j) at ha
      rw [mul_smul, ha]
      change co1BinaryAction (g (sixthFrameOrbitGenerator j))
        (sixthFrameOrbitVector (sixthFrameOrbitParent j)) = sixthFrameOrbitVector j
      rw [hA]
      change sixthFrameOrbitColumnMatrix (sixthFrameOrbitColumns (sixthFrameOrbitGenerator j))
        *ᵥ monsterCo1GeometryBinaryMaskDecode (sixthFrameOrbitPoints (sixthFrameOrbitParent j)) =
        monsterCo1GeometryBinaryMaskDecode (sixthFrameOrbitPoints j)
      rw [← sixthFrameOrbitMaskApply_decode, sixthFrameOrbit_edge_check j hj]
  exact hc i.val i.isLt

/-- These exact actual generator bindings give at least 891 genuine orbit elements. -/
theorem sixthFrameOrbit_card_lower (K : Subgroup Co1) (g : Fin 15 → Co1)
    (hg : ∀ k, g k ∈ K)
    (hA : ∀ k v, co1BinaryAction (g k) v = sixthFrameOrbitColumnMatrix
      (sixthFrameOrbitColumns k) *ᵥ v) :
    891 ≤ Nat.card (MulAction.orbit K sixthFrameOrbitBase) := by
  let f : Fin 891 → MulAction.orbit K sixthFrameOrbitBase := fun i =>
    ⟨sixthFrameOrbitVector i, sixthFrameOrbitVector_mem_orbit K g hg hA i⟩
  have hf : Function.Injective f := fun i j h =>
    sixthFrameOrbitVector_injective (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
