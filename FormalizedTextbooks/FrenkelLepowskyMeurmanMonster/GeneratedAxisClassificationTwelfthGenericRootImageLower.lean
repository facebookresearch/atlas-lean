/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerRootData

/-! Exact original root witnesses give lower counts for any genuine group realizing them. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
variable {G : Type*} [Group G]
set_option backward.isDefEq.respectTransparency false

/-- The actual permutation image fixing each original root address before a given prefix. -/
def generatedTwelfthGenericRootPrefix (R : G →* Equiv.Perm (Fin 120)) (k : ℕ) :
    Subgroup R.range where
  carrier := {p | ∀ r : Fin 120, r.val < k → p.val r = r}
  one_mem' := by intro r _; rfl
  mul_mem' := by intro p q hp hq r hr; change p.val (q.val r) = r; rw [hq r hr, hp r hr]
  inv_mem' := by
    intro p hp r hr
    apply p.val.injective
    change p.val (p.val.symm r) = p.val r
    rw [Equiv.apply_symm_apply, hp r hr]

/-- The next actual prefix is precisely the stabilizer of its original next root address. -/
def generatedTwelfthGenericRootNextEquiv (R : G →* Equiv.Perm (Fin 120)) (k : Fin 5) :
    MulAction.stabilizer (generatedTwelfthGenericRootPrefix R k.val)
        (Fin.castLE (by decide : 5 ≤ 120) k) ≃
      generatedTwelfthGenericRootPrefix R (k.val + 1) where
  toFun p := ⟨p.val.val, by
    intro r hr
    by_cases hlt : r.val < k.val
    · exact p.val.property r hlt
    · have heq : r = Fin.castLE (by decide : 5 ≤ 120) k := by
        apply Fin.ext
        have hc : (Fin.castLE (by decide : 5 ≤ 120) k).val = k.val := rfl
        omega
      subst r
      exact p.property⟩
  invFun p := ⟨⟨p.val, fun r hr => p.property r (by omega)⟩,
    p.property (Fin.castLE (by decide : 5 ≤ 120) k) (by
      have hc : (Fin.castLE (by decide : 5 ≤ 120) k).val = k.val := rfl
      omega)⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := Subtype.ext rfl

/-- A genuine witness realizing each complete original permutation belongs to its true prefix. -/
def generatedTwelfthGenericRootPrefixWitness (R : G →* Equiv.Perm (Fin 120))
    (w : Fin 86 → G)
    (hw : ∀ (n : Fin 86) (r : Fin 120), R (w n) r =
      generatedTwelfthMatrixFixerRootFiniteWord n r) (k : Fin 5)
    (j : Fin (generatedTwelfthMatrixFixerRootOrbitBound k)) :
    generatedTwelfthGenericRootPrefix R k.val :=
  ⟨⟨R (w (generatedTwelfthMatrixFixerRootWitnessNumber k j)), ⟨_, rfl⟩⟩, by
    intro r hr
    rw [hw]
    exact generatedTwelfth_matrix_fixer_root_witness_prefix k j r hr⟩

/-- Every distinct original target belongs to the actual root orbit through its genuine witness. -/
def generatedTwelfthGenericRootOrbitWitness (R : G →* Equiv.Perm (Fin 120))
    (w : Fin 86 → G)
    (hw : ∀ (n : Fin 86) (r : Fin 120), R (w n) r =
      generatedTwelfthMatrixFixerRootFiniteWord n r) (k : Fin 5)
    (j : Fin (generatedTwelfthMatrixFixerRootOrbitBound k)) :
    MulAction.orbit (generatedTwelfthGenericRootPrefix R k.val)
      (Fin.castLE (by decide : 5 ≤ 120) k) :=
  ⟨generatedTwelfthMatrixFixerRootWitnessTarget
      (generatedTwelfthMatrixFixerRootWitnessNumber k j), by
    rw [MulAction.mem_orbit_iff]
    refine ⟨generatedTwelfthGenericRootPrefixWitness R w hw k j, ?_⟩
    change R (w (generatedTwelfthMatrixFixerRootWitnessNumber k j)) _ = _
    rw [hw]
    exact generatedTwelfth_matrix_fixer_root_witness_target k j⟩

/-- All complete source permutations give the original five orbit lower bounds. -/
theorem generatedTwelfth_generic_root_prefix_orbit_lower
    (R : G →* Equiv.Perm (Fin 120)) (w : Fin 86 → G)
    (hw : ∀ (n : Fin 86) (r : Fin 120), R (w n) r =
      generatedTwelfthMatrixFixerRootFiniteWord n r) (k : Fin 5) :
    generatedTwelfthMatrixFixerRootOrbitBound k ≤
      Nat.card (MulAction.orbit (generatedTwelfthGenericRootPrefix R k.val)
        (Fin.castLE (by decide : 5 ≤ 120) k)) := by
  have hi : Function.Injective (generatedTwelfthGenericRootOrbitWitness R w hw k) := by
    intro j l h
    exact generatedTwelfth_matrix_fixer_root_targets_distinct k j l (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective (generatedTwelfthGenericRootOrbitWitness R w hw k) hi
  simpa only [Nat.card_fin] using h

/-- Actual orbit-stabilizer gives each original root-prefix lower cardinal recurrence. -/
theorem generatedTwelfth_generic_root_prefix_card_step
    (R : G →* Equiv.Perm (Fin 120)) (w : Fin 86 → G)
    (hw : ∀ (n : Fin 86) (r : Fin 120), R (w n) r =
      generatedTwelfthMatrixFixerRootFiniteWord n r) (k : Fin 5) :
    generatedTwelfthMatrixFixerRootOrbitBound k *
        Nat.card (generatedTwelfthGenericRootPrefix R (k.val + 1)) ≤
      Nat.card (generatedTwelfthGenericRootPrefix R k.val) := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (generatedTwelfthGenericRootPrefix R k.val) (Fin.castLE (by decide : 5 ≤ 120) k))
  rw [Nat.card_prod, Nat.card_congr (generatedTwelfthGenericRootNextEquiv R k)] at h
  have hl := Nat.mul_le_mul_right (Nat.card (generatedTwelfthGenericRootPrefix R (k.val + 1)))
    (generatedTwelfth_generic_root_prefix_orbit_lower R w hw k)
  rwa [h] at hl

/-- Any genuine finite group realizing every unchanged original witness
has root image at least 7200. -/
theorem generatedTwelfth_generic_root_image_lower
    (R : G →* Equiv.Perm (Fin 120)) (w : Fin 86 → G)
    (hw : ∀ (n : Fin 86) (r : Fin 120), R (w n) r =
      generatedTwelfthMatrixFixerRootFiniteWord n r) : 7200 ≤ Nat.card R.range := by
  have h0 := generatedTwelfth_generic_root_prefix_card_step R w hw (0 : Fin 5)
  have h1 := generatedTwelfth_generic_root_prefix_card_step R w hw (1 : Fin 5)
  have h2 := generatedTwelfth_generic_root_prefix_card_step R w hw (2 : Fin 5)
  have h3 := generatedTwelfth_generic_root_prefix_card_step R w hw (3 : Fin 5)
  have h4 := generatedTwelfth_generic_root_prefix_card_step R w hw (4 : Fin 5)
  change 60 * Nat.card (generatedTwelfthGenericRootPrefix R 1) ≤
    Nat.card (generatedTwelfthGenericRootPrefix R 0) at h0
  change 20 * Nat.card (generatedTwelfthGenericRootPrefix R 2) ≤
    Nat.card (generatedTwelfthGenericRootPrefix R 1) at h1
  change 3 * Nat.card (generatedTwelfthGenericRootPrefix R 3) ≤
    Nat.card (generatedTwelfthGenericRootPrefix R 2) at h2
  change 1 * Nat.card (generatedTwelfthGenericRootPrefix R 4) ≤
    Nat.card (generatedTwelfthGenericRootPrefix R 3) at h3
  change 2 * Nat.card (generatedTwelfthGenericRootPrefix R 5) ≤
    Nat.card (generatedTwelfthGenericRootPrefix R 4) at h4
  have hp : 0 < Nat.card (generatedTwelfthGenericRootPrefix R 5) := Nat.card_pos
  have hz : generatedTwelfthGenericRootPrefix R 0 = ⊤ := by
    ext p
    change (∀ r : Fin 120, r.val < 0 → p.val r = r) ↔ True
    constructor
    · intro _; trivial
    · intro _ r hr; omega
  rw [hz, Subgroup.card_top] at h0
  omega

/-- An actual kernel of at least 1024 together with the original source root witnesses
forces at least 7,372,800 genuine group elements. -/
theorem generatedTwelfth_generic_group_lower
    (R : G →* Equiv.Perm (Fin 120)) (w : Fin 86 → G)
    (hw : ∀ (n : Fin 86) (r : Fin 120), R (w n) r =
      generatedTwelfthMatrixFixerRootFiniteWord n r)
    (hk : 1024 ≤ Nat.card R.ker) : 7372800 ≤ Nat.card G := by
  have h := R.ker.card_mul_index
  rw [Subgroup.index_ker] at h
  have hl := Nat.mul_le_mul hk (generatedTwelfth_generic_root_image_lower R w hw)
  norm_num only [Nat.reduceMul] at hl
  rwa [h] at hl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
