/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerRootWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootKernelCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitSpatialUpper

/-! Genuine original root-orbit witnesses and the whole root kernel give the exact matrix count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual original root image, with successively fixed original root addresses. -/
def generatedTwelfthMatrixRootPrefix (k : ℕ) :
    Subgroup generatedTwelfthMatrixRootAction.range where
  carrier := {p | ∀ r : Fin 120, r.val < k → p.val r = r}
  one_mem' := by intro r _; rfl
  mul_mem' := by intro p q hp hq r hr; change p.val (q.val r) = r; rw [hq r hr, hp r hr]
  inv_mem' := by
    intro p hp r hr
    apply p.val.injective
    change p.val (p.val.symm r) = p.val r
    rw [Equiv.apply_symm_apply, hp r hr]

/-- The true next prefix subgroup is the actual stabilizer of the next original root. -/
def generatedTwelfthMatrixRootNextEquiv (k : Fin 5) :
    MulAction.stabilizer (generatedTwelfthMatrixRootPrefix k.val)
        (Fin.castLE (by decide : 5 ≤ 120) k) ≃
      generatedTwelfthMatrixRootPrefix (k.val + 1) where
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

/-- Each original whole word gives an element in the genuine corresponding prefix subgroup. -/
def generatedTwelfthMatrixRootPrefixWitness (k : Fin 5)
    (j : Fin (generatedTwelfthMatrixFixerRootOrbitBound k)) :
    generatedTwelfthMatrixRootPrefix k.val :=
  ⟨⟨generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootWitness
      (generatedTwelfthMatrixFixerRootWitnessNumber k j)), ⟨_, rfl⟩⟩, by
    intro r hr
    rw [generatedTwelfth_matrix_root_witness_actual]
    exact generatedTwelfth_matrix_fixer_root_witness_prefix k j r hr⟩

/-- Every distinct displayed target is in the genuine original prefix-root orbit. -/
def generatedTwelfthMatrixRootOrbitWitness (k : Fin 5)
    (j : Fin (generatedTwelfthMatrixFixerRootOrbitBound k)) :
    MulAction.orbit (generatedTwelfthMatrixRootPrefix k.val)
      (Fin.castLE (by decide : 5 ≤ 120) k) :=
  ⟨generatedTwelfthMatrixFixerRootWitnessTarget
      (generatedTwelfthMatrixFixerRootWitnessNumber k j), by
    rw [MulAction.mem_orbit_iff]
    refine ⟨generatedTwelfthMatrixRootPrefixWitness k j, ?_⟩
    change generatedTwelfthMatrixRootAction (generatedTwelfthMatrixRootWitness
      (generatedTwelfthMatrixFixerRootWitnessNumber k j)) _ = _
    rw [generatedTwelfth_matrix_root_witness_actual]
    exact generatedTwelfth_matrix_fixer_root_witness_target k j⟩

/-- Genuine whole source words certify the five actual prefix-orbit lower bounds. -/
theorem generatedTwelfth_matrix_root_prefix_orbit_lower (k : Fin 5) :
    generatedTwelfthMatrixFixerRootOrbitBound k ≤
      Nat.card (MulAction.orbit (generatedTwelfthMatrixRootPrefix k.val)
        (Fin.castLE (by decide : 5 ≤ 120) k)) := by
  have hi : Function.Injective (generatedTwelfthMatrixRootOrbitWitness k) := by
    intro j l h
    exact generatedTwelfth_matrix_fixer_root_targets_distinct k j l (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective (generatedTwelfthMatrixRootOrbitWitness k) hi
  simpa only [Nat.card_fin] using h

/-- Actual orbit-stabilizer gives the lower cardinal recurrence in the full original root image. -/
theorem generatedTwelfth_matrix_root_prefix_card_step (k : Fin 5) :
    generatedTwelfthMatrixFixerRootOrbitBound k *
        Nat.card (generatedTwelfthMatrixRootPrefix (k.val + 1)) ≤
      Nat.card (generatedTwelfthMatrixRootPrefix k.val) := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (generatedTwelfthMatrixRootPrefix k.val) (Fin.castLE (by decide : 5 ≤ 120) k))
  rw [Nat.card_prod, Nat.card_congr (generatedTwelfthMatrixRootNextEquiv k)] at h
  have hl := Nat.mul_le_mul_right (Nat.card (generatedTwelfthMatrixRootPrefix (k.val + 1)))
    (generatedTwelfth_matrix_root_prefix_orbit_lower k)
  rwa [h] at hl

/-- The entire actual root image of the whole matrix stabilizer has at least 7200 elements. -/
theorem generatedTwelfth_matrix_root_image_lower :
    7200 ≤ Nat.card generatedTwelfthMatrixRootAction.range := by
  have h0 := generatedTwelfth_matrix_root_prefix_card_step (0 : Fin 5)
  have h1 := generatedTwelfth_matrix_root_prefix_card_step (1 : Fin 5)
  have h2 := generatedTwelfth_matrix_root_prefix_card_step (2 : Fin 5)
  have h3 := generatedTwelfth_matrix_root_prefix_card_step (3 : Fin 5)
  have h4 := generatedTwelfth_matrix_root_prefix_card_step (4 : Fin 5)
  change 60 * Nat.card (generatedTwelfthMatrixRootPrefix 1) ≤
    Nat.card (generatedTwelfthMatrixRootPrefix 0) at h0
  change 20 * Nat.card (generatedTwelfthMatrixRootPrefix 2) ≤
    Nat.card (generatedTwelfthMatrixRootPrefix 1) at h1
  change 3 * Nat.card (generatedTwelfthMatrixRootPrefix 3) ≤
    Nat.card (generatedTwelfthMatrixRootPrefix 2) at h2
  change 1 * Nat.card (generatedTwelfthMatrixRootPrefix 4) ≤
    Nat.card (generatedTwelfthMatrixRootPrefix 3) at h3
  change 2 * Nat.card (generatedTwelfthMatrixRootPrefix 5) ≤
    Nat.card (generatedTwelfthMatrixRootPrefix 4) at h4
  have hp : 0 < Nat.card (generatedTwelfthMatrixRootPrefix 5) := Nat.card_pos
  have hz : generatedTwelfthMatrixRootPrefix 0 = ⊤ := by
    ext p
    change (∀ r : Fin 120, r.val < 0 → p.val r = r) ↔ True
    constructor
    · intro _; trivial
    · intro _ r hr; omega
  rw [hz, Subgroup.card_top] at h0
  omega

/-- The full genuine section root kernel embeds into the genuine whole matrix root-action kernel. -/
def generatedTwelfthMatrixRootKernelEmbedding :
    generatedTwelfthRootAction.ker → generatedTwelfthMatrixRootAction.ker :=
  fun g => ⟨⟨g.val, generatedTwelfth_root_action_kernel_actual_matrix g⟩, g.property⟩

/-- The root kernel embedding preserves every distinct actual whole lattice isometry. -/
theorem generatedTwelfth_matrix_root_kernel_embedding_injective :
    Function.Injective generatedTwelfthMatrixRootKernelEmbedding := by
  intro g h he
  apply Subtype.ext
  exact congrArg (fun k : generatedTwelfthMatrixRootAction.ker => k.val.val) he

/-- The entire actual matrix root-action kernel has at least 1024 actual original elements. -/
theorem generatedTwelfth_matrix_root_kernel_lower :
    1024 ≤ Nat.card generatedTwelfthMatrixRootAction.ker := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  exact generatedTwelfth_root_action_kernel_lower.trans
    (Nat.card_le_card_of_injective generatedTwelfthMatrixRootKernelEmbedding
      generatedTwelfth_matrix_root_kernel_embedding_injective)

/-- Genuine kernel and root-image counts give the whole matrix section stabilizer lower bound. -/
theorem generatedTwelfth_matrix_section_stabilizer_lower :
    7372800 ≤ Nat.card generatedTwelfthMatrixSectionStabilizer := by
  have h := generatedTwelfthMatrixRootAction.ker.card_mul_index
  rw [Subgroup.index_ker] at h
  have hl := Nat.mul_le_mul generatedTwelfth_matrix_root_kernel_lower
    generatedTwelfth_matrix_root_image_lower
  norm_num only [Nat.reduceMul] at hl
  rwa [h] at hl

/-- Whole original section matrix fixers inject into the entire actual Co0 matrix stabilizer. -/
def generatedTwelfthMatrixSpatialEmbedding :
    generatedTwelfthMatrixSectionStabilizer → generatedTwelfthSpatialStabilizer :=
  fun g => ⟨g.val.val, g.property⟩

/-- No genuine original full matrix fixer is lost by its ambient inclusion. -/
theorem generatedTwelfth_matrix_spatial_embedding_injective :
    Function.Injective generatedTwelfthMatrixSpatialEmbedding := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : generatedTwelfthSpatialStabilizer => x.val) he

/-- The entire actual Co0 matrix stabilizer has exactly 7,372,800 elements. -/
theorem generatedTwelfth_spatial_stabilizer_card :
    Nat.card generatedTwelfthSpatialStabilizer = 7372800 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  apply Nat.le_antisymm generatedTwelfth_spatial_stabilizer_upper
  exact generatedTwelfth_matrix_section_stabilizer_lower.trans
    (Nat.card_le_card_of_injective generatedTwelfthMatrixSpatialEmbedding
      generatedTwelfth_matrix_spatial_embedding_injective)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
