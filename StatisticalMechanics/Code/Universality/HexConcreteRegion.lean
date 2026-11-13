/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.Universality.HexPairingMaps

namespace StatMech.Universality

open Complex
open Function
open HexWalk
open scoped BigOperators











theorem hexConcrete_halfStep_sub (h : ℤ) : halfStep (h - 1) = -(hexOmega * halfStep h) := by
  unfold halfStep
  have key : hexUnit ((h - 1) + 3) = - hexUnit (h - 1) := hexUnit_add_three (h - 1)
  rw [show ((h - 1) + 3 : ℤ) = h + 2 by ring, hexUnit_add_two] at key
  linear_combination (1 / 2 : ℂ) * key


theorem hexConcrete_halfStep_add (h : ℤ) : halfStep (h + 1) = -(hexOmega ^ 2 * halfStep h) := by
  unfold halfStep
  have key : hexUnit ((h + 1) + 3) = - hexUnit (h + 1) := hexUnit_add_three (h + 1)
  rw [show ((h + 1) + 3 : ℤ) = h + 4 by ring, hexUnit_add_four] at key
  linear_combination (1 / 2 : ℂ) * key


theorem hexConcrete_halfStep_sub2 (h : ℤ) : halfStep (h - 2) = hexOmega ^ 2 * halfStep h := by
  rw [show (h - 2 : ℤ) = (h - 1) - 1 by ring, hexConcrete_halfStep_sub,
    hexConcrete_halfStep_sub]; ring


theorem hexConcrete_halfStep_add2 (h : ℤ) : halfStep (h + 2) = hexOmega * halfStep h := by
  rw [show (h + 2 : ℤ) = (h + 1) + 1 by ring, hexConcrete_halfStep_add,
    hexConcrete_halfStep_add]
  have h3 : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  linear_combination (hexOmega * halfStep h) * h3


theorem hexConcrete_halfStep_ne (h : ℤ) : halfStep h ≠ 0 := by
  unfold halfStep
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨by norm_num, hexUnit_ne_zero h⟩


theorem hexConcrete_du_ne (h0 : ℤ) : (-halfStep h0) ≠ 0 := by
  simp only [ne_eq, neg_eq_zero]; exact hexConcrete_halfStep_ne h0











theorem hexConcrete_omega_cubic : hexOmega ^ 2 = -hexOmega - 1 := by
  have h3 : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  have hne : hexOmega - 1 ≠ 0 := sub_ne_zero.mpr hexOmega_ne_one
  have factored : (hexOmega - 1) * (hexOmega ^ 2 + hexOmega + 1) = 0 := by
    ring_nf; linear_combination h3
  rcases mul_eq_zero.mp factored with h | h
  · exact absurd h hne
  · linear_combination h


theorem hexConcrete_omega_im_pos : 0 < hexOmega.im := by
  unfold hexOmega
  rw [Complex.exp_ofReal_mul_I_im]
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have := Real.pi_pos; linarith



theorem hexConcrete_omega_lin_indep (α β : ℝ)
    (h : (α : ℂ) + (β : ℂ) * hexOmega = 0) : α = 0 ∧ β = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.zero_im, zero_add, zero_mul, add_zero] at him
  have hb : β = 0 := by
    rcases mul_eq_zero.mp him with h1 | h2
    · exact h1
    · exact absurd h2 (ne_of_gt hexConcrete_omega_im_pos)
  subst hb
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.zero_re, zero_mul, sub_zero, add_zero] at hre
  exact ⟨hre, rfl⟩





theorem hexConcrete_mid_ne (a s : ℂ) (hs : s ≠ 0) (α₁ β₁ α₂ β₂ : ℝ)
    (hne : ¬(α₁ = α₂ ∧ β₁ = β₂)) :
    a + ((α₁ : ℂ) + (β₁ : ℂ) * hexOmega) * s ≠ a + ((α₂ : ℂ) + (β₂ : ℂ) * hexOmega) * s := by
  intro heq
  apply hne
  have hd : ((α₁ : ℂ) + (β₁ : ℂ) * hexOmega) * s - ((α₂ : ℂ) + (β₂ : ℂ) * hexOmega) * s = 0 := by
    linear_combination heq
  have hfac : (((α₁ - α₂ : ℝ) : ℂ) + ((β₁ - β₂ : ℝ) : ℂ) * hexOmega) * s = 0 := by
    push_cast; linear_combination hd
  have hz : ((α₁ - α₂ : ℝ) : ℂ) + ((β₁ - β₂ : ℝ) : ℂ) * hexOmega = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exact absurd h hs
  obtain ⟨ha, hb⟩ := hexConcrete_omega_lin_indep _ _ hz
  exact ⟨by linarith [sub_eq_zero.mp ha], by linarith [sub_eq_zero.mp hb]⟩







theorem hexConcrete_mids_one (a : ℂ) (h t : ℤ) :
    (ofTurns a h [t]).mids = [a, a + halfStep h + halfStep (h + t)] := by
  unfold ofTurns HexWalk.mids; simp [midsAux]


theorem hexConcrete_endMid_one (a : ℂ) (h t : ℤ) :
    (ofTurns a h [t]).endMid = a + halfStep h + halfStep (h + t) := by
  unfold HexWalk.endMid ofTurns HexWalk.mids; simp [midsAux]



theorem hexConcrete_vertices_one (a : ℂ) (h t : ℤ) :
    (ofTurns a h [t]).vertices
      = [a + halfStep h, a + halfStep h + halfStep (h + t) + halfStep (h + t)] := by
  unfold ofTurns HexWalk.vertices; simp [verticesAux]


theorem hexConcrete_endMid_two (a : ℂ) (h t1 t2 : ℤ) :
    (ofTurns a h [t1, t2]).endMid
      = a + halfStep h + halfStep (h + t1) + halfStep (h + t1) + halfStep (h + t1 + t2) := by
  unfold HexWalk.endMid ofTurns HexWalk.mids; simp [midsAux]





theorem hexConcrete_saw_one (a : ℂ) (h t : ℤ) : (ofTurns a h [t]).IsSAW := by
  unfold HexWalk.IsSAW
  rw [hexConcrete_vertices_one, List.nodup_cons]
  refine ⟨?_, List.nodup_singleton _⟩
  simp only [List.mem_singleton]
  intro heq
  exact hexConcrete_halfStep_ne (h + t) (by linear_combination (1 / 2 : ℂ) * (heq.symm))


theorem hexConcrete_legalSAW_one (a : ℂ) (h t : ℤ) (ht : t = 1 ∨ t = -1) :
    (ofTurns a h [t]).IsLegalSAW := by
  refine ⟨?_, hexConcrete_saw_one a h t⟩
  intro s hs
  simp only [ofTurns_turns, List.mem_singleton] at hs
  rw [hs]; exact ht










noncomputable def hexConcreteV (a : ℂ) (h0 : ℤ) : ℂ := a + halfStep h0


noncomputable def hexConcreteDu (_a : ℂ) (h0 : ℤ) : ℂ := -halfStep h0


noncomputable def hexConcreteQ (a : ℂ) (h0 : ℤ) : ℂ :=
  hexConcreteV a h0 + hexOmega * hexConcreteDu a h0


noncomputable def hexConcreteR (a : ℂ) (h0 : ℤ) : ℂ :=
  hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0


theorem hexConcreteDu_ne (a : ℂ) (h0 : ℤ) : hexConcreteDu a h0 ≠ 0 :=
  hexConcrete_du_ne h0


theorem hexConcrete_p_eq (a : ℂ) (h0 : ℤ) :
    hexConcreteV a h0 + hexConcreteDu a h0 = a := by
  unfold hexConcreteV hexConcreteDu; ring




theorem hexConcrete_endsAt_p (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 []).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0) := by
  unfold HexWalk.EndsAt
  rw [show (ofTurns a h0 []).endMid = (trivialWalk a h0).endMid from rfl,
    trivialWalk_endMid a h0, hexConcrete_p_eq]




theorem hexConcrete_endsAt_q (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1]).EndsAt (hexConcreteQ a h0) := by
  unfold HexWalk.EndsAt hexConcreteQ hexConcreteV hexConcreteDu
  rw [show ([-1] : List ℤ) = [(-1 : ℤ)] from rfl, hexConcrete_endMid_one,
    show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  ring




theorem hexConcrete_endsAt_r (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1]).EndsAt (hexConcreteR a h0) := by
  unfold HexWalk.EndsAt hexConcreteR hexConcreteV hexConcreteDu
  rw [show ([1] : List ℤ) = [(1 : ℤ)] from rfl, hexConcrete_endMid_one,
    hexConcrete_halfStep_add]
  ring




theorem hexConcrete_a_ne_q (a : ℂ) (h0 : ℤ) : a ≠ hexConcreteQ a h0 := by
  have := hexMid_p_ne_q (v := hexConcreteV a h0) (du := hexConcreteDu a h0) (hexConcreteDu_ne a h0)
  rwa [hexConcrete_p_eq] at this


theorem hexConcrete_a_ne_r (a : ℂ) (h0 : ℤ) : a ≠ hexConcreteR a h0 := by
  have := hexMid_p_ne_r (v := hexConcreteV a h0) (du := hexConcreteDu a h0) (hexConcreteDu_ne a h0)
  rwa [hexConcrete_p_eq] at this


theorem hexConcrete_q_ne_r (a : ℂ) (h0 : ℤ) : hexConcreteQ a h0 ≠ hexConcreteR a h0 :=
  hexMid_q_ne_r (v := hexConcreteV a h0) (du := hexConcreteDu a h0) (hexConcreteDu_ne a h0)









theorem hexConcrete_mids_qext (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1]).mids = [a, hexConcreteQ a h0] := by
  rw [show ([-1] : List ℤ) = [(-1 : ℤ)] from rfl, hexConcrete_mids_one]
  unfold hexConcreteQ hexConcreteV hexConcreteDu
  rw [show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  congr 2; ring


theorem hexConcrete_mids_rext (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1]).mids = [a, hexConcreteR a h0] := by
  rw [show ([1] : List ℤ) = [(1 : ℤ)] from rfl, hexConcrete_mids_one]
  unfold hexConcreteR hexConcreteV hexConcreteDu
  rw [hexConcrete_halfStep_add]
  congr 2; ring



theorem hexConcrete_qext_not_passes_r (a : ℂ) (h0 : ℤ) :
    ¬ PassesThrough a h0 [-1] (hexConcreteR a h0) := by
  unfold PassesThrough
  rw [hexConcrete_mids_qext]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (hr | hr)
  · exact hexConcrete_a_ne_r a h0 hr.symm
  · exact hexConcrete_q_ne_r a h0 hr.symm



theorem hexConcrete_rext_not_passes_q (a : ℂ) (h0 : ℤ) :
    ¬ PassesThrough a h0 [1] (hexConcreteQ a h0) := by
  unfold PassesThrough
  rw [hexConcrete_mids_rext]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (hq | hq)
  · exact hexConcrete_a_ne_q a h0 hq.symm
  · exact hexConcrete_q_ne_r a h0 hq




















theorem hexConcrete_atoms (a : ℂ) (h0 : ℤ) :
    ((ofTurns a h0 []).IsLegalSAW
        ∧ (ofTurns a h0 []).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0))
      ∧ ((ofTurns a h0 [-1]).IsLegalSAW
          ∧ (ofTurns a h0 [-1]).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0))
      ∧ ((ofTurns a h0 [1]).IsLegalSAW
          ∧ (ofTurns a h0 [1]).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0))
      ∧ (¬ PassesThrough a h0 [-1] (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0))
      ∧ (¬ PassesThrough a h0 [1] (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) := by
  refine ⟨⟨trivialWalk_isLegalSAW a h0, hexConcrete_endsAt_p a h0⟩,
    ⟨hexConcrete_legalSAW_one a h0 (-1) (Or.inr rfl), hexConcrete_endsAt_q a h0⟩,
    ⟨hexConcrete_legalSAW_one a h0 1 (Or.inl rfl), hexConcrete_endsAt_r a h0⟩, ?_, ?_⟩
  · exact hexConcrete_qext_not_passes_r a h0
  · exact hexConcrete_rext_not_passes_q a h0










theorem hexConcrete_q_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteQ a h0 = a + (((1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteQ hexConcreteV hexConcreteDu; push_cast; ring


theorem hexConcrete_r_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteR a h0 = a + (((2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteR hexConcreteV hexConcreteDu
  rw [hexConcrete_omega_cubic]; push_cast; ring


theorem hexConcrete_endMid_mm (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1, -1]).endMid
      = a + (((0 : ℝ) : ℂ) + ((-3 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + (-1) + (-1) : ℤ) = h0 - 2 by ring,
    hexConcrete_halfStep_sub2, show (h0 + (-1) : ℤ) = h0 - 1 by ring,
    hexConcrete_halfStep_sub, hexConcrete_omega_cubic]
  push_cast; ring


theorem hexConcrete_endMid_mp (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1, 1]).endMid
      = a + (((2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + (-1) + 1 : ℤ) = h0 by ring,
    show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  push_cast; ring


theorem hexConcrete_endMid_pm (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1, -1]).endMid
      = a + (((4 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + 1 + (-1) : ℤ) = h0 by ring,
    hexConcrete_halfStep_add, hexConcrete_omega_cubic]
  push_cast; ring


theorem hexConcrete_endMid_pp (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1, 1]).endMid
      = a + (((3 : ℝ) : ℂ) + ((3 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_endMid_two, show (h0 + 1 + 1 : ℤ) = h0 + 2 by ring,
    hexConcrete_halfStep_add2, hexConcrete_halfStep_add, hexConcrete_omega_cubic]
  push_cast; ring











private theorem hexConcrete_a_canon (a : ℂ) (h0 : ℤ) :
    a = a + (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  push_cast; ring




theorem hexConcrete_len2_endMid_not_mid (a : ℂ) (h0 : ℤ) (t1 t2 : ℤ)
    (h1 : t1 = 1 ∨ t1 = -1) (h2 : t2 = 1 ∨ t2 = -1) :
    (ofTurns a h0 [t1, t2]).endMid ≠ a
      ∧ (ofTurns a h0 [t1, t2]).endMid ≠ hexConcreteQ a h0
      ∧ (ofTurns a h0 [t1, t2]).endMid ≠ hexConcreteR a h0 := by
  have hs : halfStep h0 ≠ 0 := hexConcrete_halfStep_ne h0
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  
  · rw [hexConcrete_endMid_pp, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 3 3 0 0 (by simp)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 3 3 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 3 3 2 1 (by norm_num)
  
  · rw [hexConcrete_endMid_pm, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 4 2 0 0 (by simp)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 4 2 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 4 2 2 1 (by norm_num)
  
  · rw [hexConcrete_endMid_mp, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 2 (-2) 0 0 (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 2 (-2) 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 2 (-2) 2 1 (by norm_num)
  
  · rw [hexConcrete_endMid_mm, hexConcrete_q_canon, hexConcrete_r_canon]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [hexConcrete_a_canon a h0]
      exact hexConcrete_mid_ne a (halfStep h0) hs 0 (-3) 0 0 (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 0 (-3) 1 (-1) (by norm_num)
    · exact hexConcrete_mid_ne a (halfStep h0) hs 0 (-3) 2 1 (by norm_num)









noncomputable def hexConcreteV0 (a : ℂ) (h0 : ℤ) : ℂ := a + halfStep h0


noncomputable def hexConcreteVq (a : ℂ) (h0 : ℤ) : ℂ :=
  a + halfStep h0 + halfStep (h0 + (-1)) + halfStep (h0 + (-1))


noncomputable def hexConcreteVr (a : ℂ) (h0 : ℤ) : ℂ :=
  a + halfStep h0 + halfStep (h0 + 1) + halfStep (h0 + 1)


theorem hexConcrete_v0_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteV0 a h0 = a + (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteV0; push_cast; ring


theorem hexConcrete_vq_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteVq a h0 = a + (((1 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteVq
  rw [show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  push_cast; ring


theorem hexConcrete_vr_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteVr a h0 = a + (((3 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteVr
  rw [hexConcrete_halfStep_add, hexConcrete_omega_cubic]
  push_cast; ring


theorem hexConcrete_verts_distinct (a : ℂ) (h0 : ℤ) :
    hexConcreteV0 a h0 ≠ hexConcreteVq a h0
      ∧ hexConcreteV0 a h0 ≠ hexConcreteVr a h0
      ∧ hexConcreteVq a h0 ≠ hexConcreteVr a h0 := by
  have hs : halfStep h0 ≠ 0 := hexConcrete_halfStep_ne h0
  rw [hexConcrete_v0_canon, hexConcrete_vq_canon, hexConcrete_vr_canon]
  refine ⟨?_, ?_, ?_⟩
  · exact hexConcrete_mid_ne a (halfStep h0) hs 1 0 1 (-2) (by norm_num)
  · exact hexConcrete_mid_ne a (halfStep h0) hs 1 0 3 2 (by norm_num)
  · exact hexConcrete_mid_ne a (halfStep h0) hs 1 (-2) 3 2 (by norm_num)













noncomputable def hexConcrete_region (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    HexFiniteRegion where
  verts := {hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0}
  mids := {a, hexConcreteQ a h0, hexConcreteR a h0}
  start := a
  start_mem := by simp
  vertexBound := hclosure


theorem hexConcrete_verts_card (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (hexConcrete_region a h0 hclosure).verts.card = 3 := by
  obtain ⟨h1, h2, h3⟩ := hexConcrete_verts_distinct a h0
  show ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ).card = 3
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
    Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]


theorem hexConcrete_inRegion_iff (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (z : ℂ) :
    (hexConcrete_region a h0 hclosure).inRegion z
      ↔ (z = a ∨ z = hexConcreteQ a h0 ∨ z = hexConcreteR a h0) := by
  unfold HexFiniteRegion.inRegion hexConcrete_region
  simp [Finset.mem_insert]




theorem hexConcrete_staysIn_p (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (ofTurns a h0 []).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
  intro m hm
  rw [hexConcrete_inRegion_iff]
  have : (ofTurns a h0 []).mids = [a] := by
    show (trivialWalk a h0).mids = [a]
    unfold HexWalk.mids; simp [trivialWalk]
  rw [this] at hm
  simp only [List.mem_singleton] at hm
  exact Or.inl hm


theorem hexConcrete_staysIn_q (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (ofTurns a h0 [-1]).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
  intro m hm
  rw [hexConcrete_inRegion_iff]
  rw [hexConcrete_mids_qext] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)


theorem hexConcrete_staysIn_r (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (ofTurns a h0 [1]).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
  intro m hm
  rw [hexConcrete_inRegion_iff]
  rw [hexConcrete_mids_rext] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)











theorem hexConcrete_support_classify (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexConcrete_region a h0 hclosure).inRegion) :
    ts = [] ∨ ts = [-1] ∨ ts = [1] := by
  
  have hlt : ts.length < 3 := by
    have := (hexConcrete_region a h0 hclosure).length_lt a h0 ts hlegal.2 hstay
    rwa [hexConcrete_verts_card a h0 hclosure] at this
  
  have hturns : ∀ t ∈ ts, t = 1 ∨ t = -1 := hlegal.1
  
  interval_cases hlen : ts.length
  · exact Or.inl (List.length_eq_zero_iff.mp hlen)
  · 
    obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
      match ts, hlen with
      | [t], _ => exact ⟨t, rfl⟩
    have ht : t = 1 ∨ t = -1 := hturns t (by simp)
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · 
    exfalso
    obtain ⟨t1, t2, rfl⟩ : ∃ t1 t2, ts = [t1, t2] := by
      match ts, hlen with
      | [t1, t2], _ => exact ⟨t1, t2, rfl⟩
    have ht1 : t1 = 1 ∨ t1 = -1 := hturns t1 (by simp)
    have ht2 : t2 = 1 ∨ t2 = -1 := hturns t2 (by simp)
    
    have hmem : (ofTurns a h0 [t1, t2]).endMid ∈ (ofTurns a h0 [t1, t2]).mids := by
      unfold HexWalk.endMid; exact List.getLast_mem _
    have hreg := hstay _ hmem
    rw [hexConcrete_inRegion_iff] at hreg
    obtain ⟨hna, hnq, hnr⟩ := hexConcrete_len2_endMid_not_mid a h0 t1 t2 ht1 ht2
    rcases hreg with h | h | h
    · exact hna h
    · exact hnq h
    · exact hnr h










theorem hexConcrete_covering_p (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hp : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0)) :
    ts = [] := by
  obtain ⟨hlegal, hstay⟩ :=
    (hexConcrete_region a h0 hclosure).support_isLegalSAW_staysIn
      (hexConcreteDu_ne a h0) ts hsupp
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exact h
  · 
    exfalso
    rw [h] at hp
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hp hq
    rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_q a h0 (hp.symm.trans hq)
  · exfalso
    rw [h] at hp
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hp hr
    rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_r a h0 (hp.symm.trans hr)



theorem hexConcrete_covering_q (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hq : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) :
    ts = [-1] := by
  obtain ⟨hlegal, hstay⟩ :=
    (hexConcrete_region a h0 hclosure).support_isLegalSAW_staysIn
      (hexConcreteDu_ne a h0) ts hsupp
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hq
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exfalso
    rw [h] at hq
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]
      show (trivialWalk a h0).endMid = a
      exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hq hpe
    exact hexConcrete_a_ne_q a h0 (hpe.symm.trans hq)
  · exact h
  · exfalso
    rw [h] at hq
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hq hr
    exact hexConcrete_q_ne_r a h0 (hq.symm.trans hr)



theorem hexConcrete_covering_r (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hr : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) :
    ts = [1] := by
  obtain ⟨hlegal, hstay⟩ :=
    (hexConcrete_region a h0 hclosure).support_isLegalSAW_staysIn
      (hexConcreteDu_ne a h0) ts hsupp
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hr
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exfalso
    rw [h] at hr
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]
      show (trivialWalk a h0).endMid = a
      exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hr hpe
    exact hexConcrete_a_ne_r a h0 (hpe.symm.trans hr)
  · exfalso
    rw [h] at hr
    have hqe := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hr hqe
    exact hexConcrete_q_ne_r a h0 (hqe.symm.trans hr)
  · exact h










private theorem hexConcrete_paraf_guard (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (z : ℂ) (ts : List ℤ)
    (hne : parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 z (5/8) hexChi ts ≠ 0) :
    (ofTurns a h0 ts).IsLegalSAW
      ∧ (ofTurns a h0 ts).StaysIn (hexConcrete_region a h0 hclosure).inRegion
      ∧ (ofTurns a h0 ts).EndsAt z := by
  by_contra hcon
  apply hne
  unfold parafSummand
  rw [if_neg hcon]


theorem hexConcrete_obs_p (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi [] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexConcrete_paraf_guard a h0 hclosure _ ts hne
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exact hts h
  · rw [h] at hend
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hend hq; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_q a h0 (hend.symm.trans hq)
  · rw [h] at hend
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hend hr; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_r a h0 (hend.symm.trans hr)


theorem hexConcrete_obs_q (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi [-1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexConcrete_paraf_guard a h0 hclosure _ ts hne
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hend
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · rw [h] at hend
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hend hpe
    exact hexConcrete_a_ne_q a h0 (hpe.symm.trans hend)
  · exact hts h
  · rw [h] at hend
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hend hr
    exact hexConcrete_q_ne_r a h0 (hend.symm.trans hr)


theorem hexConcrete_obs_r (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi [1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexConcrete_paraf_guard a h0 hclosure _ ts hne
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hend
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · rw [h] at hend
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hend hpe
    exact hexConcrete_a_ne_r a h0 (hpe.symm.trans hend)
  · rw [h] at hend
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hend hq
    exact hexConcrete_q_ne_r a h0 (hq.symm.trans hend)
  · exact hts h



theorem hexConcrete_summable (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (z : ℂ) :
    Summable fun ts =>
      parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 z (5/8) hexChi ts := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (s := {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]} )
  · have : {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]}
        = ({[], [-1], [1]} : Finset (List ℤ)) := by
      ext ts; simp
    rw [this]; exact (Finset.finite_toSet _)
  · intro ts hts
    simp only [Function.mem_support] at hts
    obtain ⟨hlegal, hstay, _⟩ := hexConcrete_paraf_guard a h0 hclosure z ts hts
    exact hexConcrete_support_classify a h0 hclosure ts hlegal hstay












noncomputable def hexConcrete_classification (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    HexSawClassification (hexConcrete_region a h0 hclosure).inRegion a h0
      (hexConcreteV a h0) (hexConcreteDu a h0) :=
  hexPairing_classification_of_finiteCovering (hexConcrete_region a h0 hclosure)
    (hexConcreteDu_ne a h0)
    (pairs := ∅) (triplets := {0})
    (pairBase := fun _ => []) (pairLq := fun _ => []) (pairLr := fun _ => [])
    (tripBase := fun _ => [])
    (pairLq_sum := by simp) (pairLr_sum := by simp) (pairLen := by simp)
    (pairQ_valid := by simp) (pairR_valid := by simp)
    (pairQ_passes_p := by simp) (pairQ_passes_r := by simp)
    (pairR_passes_p := by simp) (pairR_passes_q := by simp)
    (tripP_valid := fun _ _ =>
      ⟨(hexConcrete_atoms a h0).1.1, hexConcrete_staysIn_p a h0 hclosure,
        (hexConcrete_atoms a h0).1.2⟩)
    (tripQ_valid := fun _ _ => by
      simpa using ⟨(hexConcrete_atoms a h0).2.1.1, hexConcrete_staysIn_q a h0 hclosure,
        (hexConcrete_atoms a h0).2.1.2⟩)
    (tripR_valid := fun _ _ => by
      simpa using ⟨(hexConcrete_atoms a h0).2.2.1.1, hexConcrete_staysIn_r a h0 hclosure,
        (hexConcrete_atoms a h0).2.2.1.2⟩)
    (tripQ_not_passes_r := fun _ _ => by simpa using (hexConcrete_atoms a h0).2.2.2.1)
    (tripR_not_passes_q := fun _ _ => by simpa using (hexConcrete_atoms a h0).2.2.2.2)
    (tripBase_inj := by
      rintro ⟨T1, hT1⟩ ⟨T2, hT2⟩ _
      simp only [Finset.mem_singleton] at hT1 hT2
      subst hT1; subst hT2; rfl)
    (pairQ_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (pairR_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (covp := by
      intro ts hts hp
      refine ⟨0, by simp, ?_⟩
      exact (hexConcrete_covering_p a h0 hclosure ts
        (((hexConcrete_region a h0 hclosure).mem_supportFinset (hexConcreteDu_ne a h0) ts).mp hts)
        hp).symm)
    (covq := by
      intro ts hts hq
      refine Or.inl ⟨0, by simp, ?_⟩
      simpa using (hexConcrete_covering_q a h0 hclosure ts
        (((hexConcrete_region a h0 hclosure).mem_supportFinset (hexConcreteDu_ne a h0) ts).mp hts)
        hq).symm)
    (covr := by
      intro ts hts hr
      refine Or.inl ⟨0, by simp, ?_⟩
      simpa using (hexConcrete_covering_r a h0 hclosure ts
        (((hexConcrete_region a h0 hclosure).mem_supportFinset (hexConcreteDu_ne a h0) ts).mp hts)
        hr).symm)
    (reindex := by
      rw [Finset.sum_empty, Finset.sum_singleton, zero_add]
      rw [hexConcrete_obs_p a h0 hclosure, hexConcrete_obs_q a h0 hclosure,
        hexConcrete_obs_r a h0 hclosure]
      simp)







theorem hexConcrete_vertex_relation (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    ((hexConcreteV a h0 + hexConcreteDu a h0) - hexConcreteV a h0)
        * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
            (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
              (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
              (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = 0 :=
  hexClass_vertex_relation (hexConcrete_classification a h0 hclosure) (hexConcreteDu_ne a h0)
    (hexConcrete_summable a h0 hclosure _)
    (hexConcrete_summable a h0 hclosure _)
    (hexConcrete_summable a h0 hclosure _)

end StatMech.Universality
