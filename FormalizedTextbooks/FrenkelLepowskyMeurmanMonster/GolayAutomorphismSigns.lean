/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOrthogonality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

/-! Codeword sign changes and the actual Leech congruences (Seysen §9.2).
The signs are determined by codewords of the published encoder range. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Negate exactly the coordinates selected by the binary word. -/
def golayIntegerSign (d : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => if d i = 0 then u i else -u i

/-- The intersection of any two codeword supports has even cardinality. -/
theorem golayCode_intersection_even (c d : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hd : d ∈ golayCode) :
    (2 : ℤ) ∣ ∑ i, ((d i).val : ℤ) * ((c i).val : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using
    golayCode_self_orthogonal d c hd hc

/-- The selected coordinate sum is divisible by four for every lattice vector. -/
theorem golayCode_selected_sum_four (d : Fin 24 → ZMod 2) (hd : d ∈ golayCode)
    (u : Fin 24 → ℤ) (hu : u ∈ leechIntegral) :
    (4 : ℤ) ∣ ∑ i, ((d i).val : ℤ) * u i := by
  obtain ⟨m, hm, c, hc, huc, hus⟩ := mem_leechIntegral_iff_source u |>.mp hu
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, huc, mul_add,
    Finset.sum_add_distrib]
  have hw : (∑ i, ((d i).val : ZMod 4)) = 0 := by
    have h := golayCode_weight_four d hd
    obtain ⟨k, hk⟩ := h
    have hh := congrArg (fun n : ℕ => (n : ZMod 4)) hk
    simpa only [Nat.cast_sum, Nat.cast_mul, show ((4 : ℕ) : ZMod 4) = 0 by decide,
      zero_mul] using hh
  have hi : (∑ i, ((d i).val : ZMod 4) * (2 * ((c i).val : ZMod 4))) = 0 := by
    obtain ⟨k, hk⟩ := golayCode_intersection_even c d hc hd
    have hdiv : (4 : ℤ) ∣ 2 * ∑ i, ((d i).val : ℤ) * ((c i).val : ℤ) := by
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hdiv
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_natCast,
      Finset.mul_sum, mul_left_comm] using hz
  rw [← Finset.sum_mul, hw, zero_mul, zero_add, hi]

/-- Exact integer change in total coordinate sum after a codeword sign change. -/
theorem golayIntegerSign_sum (d : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) :
    ∑ i, golayIntegerSign d u i = (∑ i, u i) -
      2 * ∑ i, ((d i).val : ℤ) * u i := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : ∀ b : ZMod 2, (if b = 0 then u i else -u i) =
      u i - 2 * ((b.val : ℤ) * u i) := by
    intro b
    have h0 : (0 : ZMod 2).val = 0 := by decide
    have h1 : (1 : ZMod 2).val = 1 := by decide
    have hne : (1 : ZMod 2) ≠ 0 := by decide
    have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases hb b with rfl | rfl
    · simp only [h0, ite_true, Nat.cast_zero, zero_mul, mul_zero, sub_zero]
    · simp only [hne, ite_false, h1, Nat.cast_one, one_mul]
      ring
  exact h (d i)

/-- The modulo-eight sum condition is preserved by every Golay sign change. -/
theorem golayIntegerSign_sum_mod_eight (d : Fin 24 → ZMod 2) (hd : d ∈ golayCode)
    (u : Fin 24 → ℤ) (hu : u ∈ leechIntegral) :
    ((∑ i, golayIntegerSign d u i : ℤ) : ZMod 8) = ((∑ i, u i : ℤ) : ZMod 8) := by
  rw [golayIntegerSign_sum]
  obtain ⟨k, hk⟩ := golayCode_selected_sum_four d hd u hu
  rw [hk]
  push_cast
  ring_nf
  rw [show (8 : ZMod 8) = 0 by decide, mul_zero, sub_zero]

/-- The parity residue changes by adding the sign word when the parity is odd. -/
theorem golayIntegerSign_residue (m : ℤ) (hm : m = 0 ∨ m = 1)
    (c d : ZMod 2) :
    (if d = 0 then (m : ZMod 4) + 2 * (c.val : ZMod 4)
      else -((m : ZMod 4) + 2 * (c.val : ZMod 4))) =
      (m : ZMod 4) + 2 * ((c + (m : ZMod 2) * d).val : ZMod 4) := by
  rcases hm with rfl | rfl
  · have h : ∀ c d : ZMod 2,
        (if d = 0 then (0 : ZMod 4) + 2 * (c.val : ZMod 4)
          else -((0 : ZMod 4) + 2 * (c.val : ZMod 4))) =
          (0 : ZMod 4) + 2 * ((c + (0 : ZMod 2) * d).val : ZMod 4) := by decide
    exact h c d
  · have h : ∀ c d : ZMod 2,
        (if d = 0 then (1 : ZMod 4) + 2 * (c.val : ZMod 4)
          else -((1 : ZMod 4) + 2 * (c.val : ZMod 4))) =
          (1 : ZMod 4) + 2 * ((c + (1 : ZMod 2) * d).val : ZMod 4) := by decide
    exact h c d

/-- Every codeword sign change preserves membership in the actual integer lattice. -/
theorem golayIntegerSign_mem (d : Fin 24 → ZMod 2) (hd : d ∈ golayCode)
    (u : Fin 24 → ℤ) (hu : u ∈ leechIntegral) : golayIntegerSign d u ∈ leechIntegral := by
  obtain ⟨m, hm, c, hc, huc, hus⟩ := (mem_leechIntegral_iff_source u).mp hu
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨m, hm, c + (m : ZMod 2) • d,
    golayCode.add_mem hc (golayCode.smul_mem _ hd), ?_, ?_⟩
  · intro i
    change ((if d i = 0 then u i else -u i : ℤ) : ZMod 4) = _
    simp only [apply_ite (fun z : ℤ => (z : ZMod 4)), Int.cast_neg, huc,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact golayIntegerSign_residue m hm (c i) (d i)
  · rw [golayIntegerSign_sum_mod_eight d hd u hu]
    exact hus

@[simp] theorem golayIntegerSign_involutive (d : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) :
    golayIntegerSign d (golayIntegerSign d u) = u := by
  funext i
  by_cases hi : d i = 0 <;> simp only [golayIntegerSign, hi, ite_true, ite_false, neg_neg]

/-- The same coordinate signs acting as a real linear equivalence. -/
def golayRealSign (d : Fin 24 → ZMod 2) : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ) where
  toFun x i := qSign (d i) * x i
  invFun x i := qSign (d i) * x i
  left_inv x := by ext i; dsimp; rw [← mul_assoc, qSign_sq, one_mul]
  right_inv x := by ext i; dsimp; rw [← mul_assoc, qSign_sq, one_mul]
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' r x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem golayRealSign_apply (d : Fin 24 → ZMod 2) (x : Fin 24 → ℝ) (i : Fin 24) :
    golayRealSign d x i = qSign (d i) * x i := rfl

theorem golayRealSign_embedding (d : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) :
    golayRealSign d (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (golayIntegerSign d u) := by
  ext i
  by_cases hi : d i = 0 <;>
    simp [golayRealSign_apply, leechCoordinateEmbedding, golayIntegerSign, qSign, hi, neg_div]

/-- Every actual Golay codeword gives a genuine Leech lattice isometry. -/
def golaySignIsometry (d : golayCode) : leechIsomSubgroup :=
  ⟨golayRealSign d.val, by
    constructor
    · intro x y
      unfold stdPairingFun
      apply Finset.sum_congr rfl
      intro i _
      rw [golayRealSign_apply, golayRealSign_apply]
      calc
        qSign (d.val i) * x i * (qSign (d.val i) * y i) =
            (qSign (d.val i) * qSign (d.val i)) * (x i * y i) := by ring
        _ = x i * y i := by rw [qSign_sq, one_mul]
    · have h (x : Fin 24 → ℝ) (hx : x ∈ LeechLattice) :
          golayRealSign d.val x ∈ LeechLattice := by
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
        rw [golayRealSign_embedding]
        exact Submodule.mem_map.mpr ⟨_, golayIntegerSign_mem d.val d.property u hu, rfl⟩
      intro x
      constructor
      · exact h x
      · intro hx
        have hh := h _ hx
        change (golayRealSign d.val).symm (golayRealSign d.val x) ∈ LeechLattice at hh
        simpa only [LinearEquiv.symm_apply_apply] using hh⟩

/-- The 4096 codeword signs embed as a concrete subgroup of Co₀. -/
noncomputable def golaySignHom : Multiplicative golayCode →* leechIsomSubgroup where
  toFun d := golaySignIsometry (Multiplicative.toAdd d)
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i
    simp [golaySignIsometry, golayRealSign_apply]
  map_mul' c d := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i
    change qSign (c.toAdd.val i + d.toAdd.val i) * x i =
      qSign (c.toAdd.val i) * (qSign (d.toAdd.val i) * x i)
    rw [qSign_add, mul_assoc]

/-- Distinct codewords give distinct real coordinate sign matrices. -/
theorem golaySignHom_injective : Function.Injective golaySignHom := by
  intro c d h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext i
  have hs := congrArg (fun e : leechIsomSubgroup => e.val (fun _ => 1) i) h
  change qSign (c.toAdd.val i) * 1 = qSign (d.toAdd.val i) * 1 at hs
  simp only [mul_one] at hs
  have hz : c.toAdd.val i + d.toAdd.val i = 0 := by
    apply (qSign_eq_one_iff _).mp
    rw [qSign_add, hs, qSign_sq]
  have hh := congrArg (fun z : ZMod 2 => z + d.toAdd.val i) hz
  simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh

/-- The actual signed code subgroup has order 4096. -/
theorem golaySignHom_range_card : Nat.card golaySignHom.range = 4096 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective golaySignHom_injective).toEquiv]
  exact golayCode_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
