/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Coxeter edge transports from the pure swap to every Norton arm vertex. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555ActualWreathGenerationWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPointLineAll
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
private theorem inv_eq_self_of_square {M : Type*} [Group M] (a : M) (h : a ^ 2 = 1) :
    a⁻¹ = a := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using h
private theorem cube_swap {M : Type*} [Group M] (a b : M)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (h : (a * b) ^ 3 = 1) : (b * a) ^ 3 = 1 := by
  have he := congrArg (fun x : M => x⁻¹) h
  simpa only [← inv_pow, mul_inv_rev, inv_eq_self_of_square a ha,
    inv_eq_self_of_square b hb, inv_one] using he
private theorem braid_transport {M : Type*} [Group M] (a b : M)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (h : (a * b) ^ 3 = 1) :
    (b * a)⁻¹ * a * (b * a) = b := by
  apply mul_right_cancel (b := b)
  calc
    _ = (a * b) ^ 3 := by
      rw [mul_inv_rev, inv_eq_self_of_square a ha, inv_eq_self_of_square b hb]
      simp only [pow_succ, pow_zero]
      group
    _ = 1 := h
    _ = b * b := by simpa only [pow_two] using hb.symm

/-- Consecutive vertices on one Norton arm, beginning with the central pure swap. -/
def monsterNortonWreathPathVertex (a : Fin 3) (n : ℕ) : Y555Vertex :=
  if n = 0 then none else some (a, Fin.ofNat 5 (n - 1))

/-- The complete source Coxeter cube holds for every consecutive pair on all three arms. -/
theorem monsterNortonWreathPath_edge_cube (a : Fin 3) (n : Fin 5) :
    (y555NortonActualCandidate (monsterNortonWreathPathVertex a n.val) *
      y555NortonActualCandidate (monsterNortonWreathPathVertex a (n.val + 1))) ^ 3 = 1 := by
  fin_cases a <;> fin_cases n
  · have h := monsterNortonCandidate_center_line_coxeter 0 0
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_point_line_coxeter 0 0 0
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    have h' := cube_swap _ _ (y555NortonActualCandidate_square _)
      (y555NortonActualCandidate_square _) h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h'
  · have h := monsterNortonCandidate_point_line_coxeter 0 0 1
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_point_line_coxeter 3 0 1
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    have h' := cube_swap _ _ (y555NortonActualCandidate_square _)
      (y555NortonActualCandidate_square _) h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h'
  · have h := monsterNortonCandidate_point_line_coxeter 3 0 2
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_center_line_coxeter 1 0
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_point_line_coxeter 1 1 0
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    have h' := cube_swap _ _ (y555NortonActualCandidate_square _)
      (y555NortonActualCandidate_square _) h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h'
  · have h := monsterNortonCandidate_point_line_coxeter 1 1 1
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_point_line_coxeter 4 1 1
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    have h' := cube_swap _ _ (y555NortonActualCandidate_square _)
      (y555NortonActualCandidate_square _) h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h'
  · have h := monsterNortonCandidate_point_line_coxeter 4 1 2
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_center_line_coxeter 2 0
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_point_line_coxeter 2 2 0
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    have h' := cube_swap _ _ (y555NortonActualCandidate_square _)
      (y555NortonActualCandidate_square _) h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h'
  · have h := monsterNortonCandidate_point_line_coxeter 2 2 1
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h
  · have h := monsterNortonCandidate_point_line_coxeter 5 2 1
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    have h' := cube_swap _ _ (y555NortonActualCandidate_square _)
      (y555NortonActualCandidate_square _) h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h'
  · have h := monsterNortonCandidate_point_line_coxeter 5 2 2
    norm_num [y555Adjacent, y555NortonPointVertex, monsterNortonLineVertex] at h
    simpa [monsterNortonWreathPathVertex, Fin.ofNat] using h

/-- The actual finite Coxeter transport word along the selected Norton arm. -/
noncomputable def monsterNortonWreathPath (a : Fin 3) : ℕ → G ≀ᵣ WreathParity
  | 0 => 1
  | n + 1 => monsterNortonWreathPath a n *
      y555NortonActualCandidate (monsterNortonWreathPathVertex a (n + 1)) *
        y555NortonActualCandidate (monsterNortonWreathPathVertex a n)

/-- Each actual arm transport is a word in the already fixed sixteen Norton generators. -/
theorem monsterNortonWreathPath_mem (a : Fin 3) (n : ℕ) :
    monsterNortonWreathPath a n ∈ y555NortonActualGeneratedWreath := by
  induction n with
  | zero => exact Subgroup.one_mem _
  | succ n ih =>
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ih
      (Subgroup.subset_closure ⟨_, rfl⟩)) (Subgroup.subset_closure ⟨_, rfl⟩)

/-- The literal path word conjugates the pure swap to its indicated actual Norton vertex. -/
theorem monsterNortonWreathPath_conjugate (a : Fin 3) (n : ℕ) (hn : n ≤ 5) :
    (monsterNortonWreathPath a n)⁻¹ * wreathSwap G * monsterNortonWreathPath a n =
      y555NortonActualCandidate (monsterNortonWreathPathVertex a n) := by
  induction n with
  | zero => simp [monsterNortonWreathPath, monsterNortonWreathPathVertex,
      y555NortonActualCandidate_center]
  | succ n ih =>
    have he := monsterNortonWreathPath_edge_cube a ⟨n, by omega⟩
    have ht := braid_transport _ _ (y555NortonActualCandidate_square _)
      (y555NortonActualCandidate_square _) he
    have hp := ih (by omega)
    rw [monsterNortonWreathPath]
    calc
      _ = (y555NortonActualCandidate (monsterNortonWreathPathVertex a (n + 1)) *
          y555NortonActualCandidate (monsterNortonWreathPathVertex a n))⁻¹ *
          ((monsterNortonWreathPath a n)⁻¹ * wreathSwap G *
            monsterNortonWreathPath a n) *
          (y555NortonActualCandidate (monsterNortonWreathPathVertex a (n + 1)) *
            y555NortonActualCandidate (monsterNortonWreathPathVertex a n)) := by group
      _ = _ := by rw [hp]; exact ht


/-- The diagonal factor of the literal transported-reflection and central-swap word. -/
noncomputable def monsterNortonWreathTransportDiagonal (a : Fin 3) (n : ℕ)
    (u : Y555Vertex) : G :=
  (monsterNortonWreathPath a n * y555NortonActualCandidate u *
    (monsterNortonWreathPath a n)⁻¹ * wreathSwap G).left 1

/-- A commuting source reflection transported back along an actual arm gives an explicit
word for a genuine factor diagonal inside the fixed Norton generated subgroup. -/
theorem monsterNortonWreathTransportDiagonal_word (a : Fin 3) (n : ℕ) (hn : n ≤ 5)
    (u : Y555Vertex)
    (hcomm : Commute (y555NortonActualCandidate (monsterNortonWreathPathVertex a n))
      (y555NortonActualCandidate u)) :
    y555ActualWreathDiagonal (monsterNortonWreathTransportDiagonal a n u) =
      monsterNortonWreathPath a n * y555NortonActualCandidate u *
        (monsterNortonWreathPath a n)⁻¹ * wreathSwap G := by
  let p := monsterNortonWreathPath a n
  let r := p * y555NortonActualCandidate u * p⁻¹
  have hp : p * y555NortonActualCandidate (monsterNortonWreathPathVertex a n) * p⁻¹ =
      wreathSwap G := by
    rw [← monsterNortonWreathPath_conjugate a n hn]
    dsimp only [p]
    group
  have hc : Commute (wreathSwap G) r := by
    have h := hcomm.conj p
    rw [hp] at h
    exact h
  have hm : r * wreathSwap G ∈ wreathSwapCentralizer G := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (hc.mul_right (Commute.refl _)).eq.symm
  have he := (mem_wreathSwapCentralizer_iff G (r * wreathSwap G)).mp hm
  have hr : (r * wreathSwap G).right = 1 := by
    change (p * y555NortonActualCandidate u * p⁻¹ * wreathSwap G).right = 1
    simp only [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right]
    change p.right * wreathFlip * p.right⁻¹ * wreathFlip = 1
    rw [mul_comm p.right wreathFlip]
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using wreathFlip_sq
  rw [← y555WreathBase_of_parity_one (r * wreathSwap G) hr]
  change y555WreathBase (_, _) = y555WreathBase (_, _)
  congr 1
  exact Prod.ext rfl (he wreathFlip).symm

/-- The explicit transported diagonal word uses only the fixed actual Norton generators. -/
theorem monsterNortonWreathTransportDiagonal_mem (a : Fin 3) (n : ℕ) (hn : n ≤ 5)
    (u : Y555Vertex)
    (hcomm : Commute (y555NortonActualCandidate (monsterNortonWreathPathVertex a n))
      (y555NortonActualCandidate u)) :
    y555ActualWreathDiagonal (monsterNortonWreathTransportDiagonal a n u) ∈
      y555NortonActualGeneratedWreath := by
  rw [monsterNortonWreathTransportDiagonal_word a n hn u hcomm]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (monsterNortonWreathPath_mem a n)
      (Subgroup.subset_closure ⟨u, rfl⟩))
    (Subgroup.inv_mem _ (monsterNortonWreathPath_mem a n)))
    y555NortonActualGeneratedWreath_swap

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
