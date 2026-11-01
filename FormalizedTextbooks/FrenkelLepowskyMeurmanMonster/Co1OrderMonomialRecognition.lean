/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! Recognizing arbitrary geometrically monomial Leech isometries.
The odd lattice generator forces the sign word into Golay; the twice-generator
vectors force the physical permutation to preserve Golay. Thus the constructed
monomial subgroup accounts for every signed coordinate permutation in Co₀. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem leechMonomial_integral_mem (e : leechIsomSubgroup)
    (p : Equiv.Perm (Fin 24)) (d : Fin 24 → ZMod 2)
    (he : e.val = golayRealSign d * golayRealPermute p)
    (u : Fin 24 → ℤ) (hu : u ∈ leechIntegral) :
    golayIntegerSign d (golayIntegerPermute p u) ∈ leechIntegral := by
  have h : golayIntegerSign d (golayIntegerPermute p u) =
      (leechIntegralAction e ⟨u, hu⟩).val := by
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding, ← golayRealSign_embedding,
      ← golayRealPermute_embedding, he]
    rfl
  rw [h]
  exact (leechIntegralAction e ⟨u, hu⟩).property

private theorem oddSign_residue (a b : ZMod 2) (m : ℤ) (hm : m = 0 ∨ m = 1)
    (h : (if a = 0 then 1 else -1 : ZMod 4) = (m : ZMod 4) + 2 * (b.val : ZMod 4)) :
    m = 1 ∧ a = b := by
  rcases hm with rfl | rfl
  · have ht : ∀ a b : ZMod 2,
        (if a = 0 then 1 else -1 : ZMod 4) ≠ (0 : ZMod 4) + 2 * (b.val : ZMod 4) := by decide
    exact False.elim (ht a b h)
  · have ht : ∀ a b : ZMod 2,
        (if a = 0 then 1 else -1 : ZMod 4) = (1 : ZMod 4) + 2 * (b.val : ZMod 4) → a = b := by
      decide
    exact ⟨rfl, ht a b h⟩

/-- A geometrically signed coordinate permutation in Co₀ has a genuine Golay sign word. -/
theorem leechMonomial_sign_mem (e : leechIsomSubgroup)
    (p : Equiv.Perm (Fin 24)) (d : Fin 24 → ZMod 2)
    (he : e.val = golayRealSign d * golayRealPermute p) : d ∈ golayCode := by
  have hu : leechOddGenerator ∈ leechIntegral := by
    rw [← leechColumnSpan_eq]
    exact leech_odd_mem_columnSpan
  have hv := leechMonomial_integral_mem e p d he leechOddGenerator hu
  obtain ⟨m, hm, c, hc, hvc, _⟩ := (mem_leechIntegral_iff_source _).mp hv
  have hres (i : Fin 24) :
      ((golayIntegerSign d (golayIntegerPermute p leechOddGenerator) i : ℤ) : ZMod 4) =
        (if d i = 0 then 1 else -1 : ZMod 4) := by
    simp only [golayIntegerSign, apply_ite (fun z : ℤ => (z : ZMod 4)), Int.cast_neg,
      golayIntegerPermute, leechOddGenerator_residue]
  have hdc : d = c := by
    funext i
    exact (oddSign_residue (d i) (c i) m hm ((hres i).symm.trans (hvc i))).2
  rw [hdc]
  exact hc

private theorem evenCode_residue (a b : ZMod 2) (m : ℤ) (hm : m = 0 ∨ m = 1)
    (h : 2 * (a.val : ZMod 4) = (m : ZMod 4) + 2 * (b.val : ZMod 4)) : m = 0 ∧ a = b := by
  rcases hm with rfl | rfl
  · have ht : ∀ a b : ZMod 2,
        2 * (a.val : ZMod 4) = (0 : ZMod 4) + 2 * (b.val : ZMod 4) → a = b := by decide
    exact ⟨rfl, ht a b h⟩
  · have ht : ∀ a b : ZMod 2,
        2 * (a.val : ZMod 4) ≠ (1 : ZMod 4) + 2 * (b.val : ZMod 4) := by decide
    exact False.elim (ht a b h)

/-- A binary word whose coordinatewise double is a lattice vector must be a Golay word. -/
theorem leechTwiceWord_code_mem (w : Fin 24 → ZMod 2)
    (hw : (fun i => 2 * ((w i).val : ℤ)) ∈ leechIntegral) : w ∈ golayCode := by
  obtain ⟨m, hm, c, hc, huc, _⟩ := (mem_leechIntegral_iff_source _).mp hw
  have hwc : w = c := by
    funext i
    apply (evenCode_residue (w i) (c i) m hm _).2
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using huc i
  rw [hwc]
  exact hc

private theorem leechPermutation_integral_mem (e : leechIsomSubgroup)
    (p : Equiv.Perm (Fin 24)) (he : e.val = golayRealPermute p)
    (u : Fin 24 → ℤ) (hu : u ∈ leechIntegral) : golayIntegerPermute p u ∈ leechIntegral := by
  have hzero : golayRealSign 0 = 1 := by
    apply LinearEquiv.ext
    intro x
    ext i
    simp only [golayRealSign_apply, Pi.zero_apply, qSign_zero, one_mul]
    rfl
  have he' : e.val = golayRealSign 0 * golayRealPermute p := by rw [hzero, one_mul, he]
  have hz : golayIntegerSign 0 (golayIntegerPermute p u) = golayIntegerPermute p u := by
    funext i
    simp [golayIntegerSign]
  have h := leechMonomial_integral_mem e p 0 he' u hu
  rwa [hz] at h

private def golayRecognitionPermuteLinear (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem leechPermutation_code_mem (e : leechIsomSubgroup)
    (p : Equiv.Perm (Fin 24)) (he : e.val = golayRealPermute p)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) : golayPermute p c ∈ golayCode := by
  have hgen (j : Fin 12) : golayPermute p (golayEncoder (Pi.single j 1)) ∈ golayCode := by
    have hu : (fun i => 2 * golayGeneratorBit j i) ∈ leechIntegral := by
      rw [← leechColumnSpan_eq]
      exact leech_twice_golay_mem_columnSpan j
    have hv := leechPermutation_integral_mem e p he _ hu
    have hbit : ∀ j : Fin 12, ∀ i : Fin 24,
        golayGeneratorBit j i = (((golayGeneratorBit j i : ZMod 2).val : ℕ) : ℤ) := by
      decide +kernel
    have hrow : golayEncoder (Pi.single j 1) = fun i => (golayGeneratorBit j i : ZMod 2) := by
      ext i
      simp [golayEncoder, Pi.single_apply, ite_mul]
    rw [hrow]
    apply leechTwiceWord_code_mem
    have h : golayIntegerPermute p (fun i => 2 * golayGeneratorBit j i) =
        fun i => 2 * ((golayPermute p (fun i => (golayGeneratorBit j i : ZMod 2)) i).val : ℤ) := by
      funext i
      exact congrArg (fun z : ℤ => 2 * z) (hbit j (p.symm i))
    rwa [← h]
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change (golayRecognitionPermuteLinear p).comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  exact golayCode.smul_mem _ (hgen j)

/-- A physical coordinate permutation in Co₀ is an actual Golay automorphism. -/
theorem leechPermutation_golay_mem (e : leechIsomSubgroup)
    (p : Equiv.Perm (Fin 24)) (he : e.val = golayRealPermute p) :
    p ∈ golayAutomorphismSubgroup := by
  intro c
  constructor
  · exact leechPermutation_code_mem e p he c
  · intro hc
    have heinv : e⁻¹.val = golayRealPermute p⁻¹ := by
      rw [show e⁻¹.val = e.val.symm by rfl, he]
      rfl
    have h := leechPermutation_code_mem e⁻¹ p⁻¹ heinv _ hc
    rw [golayPermute_inv] at h
    exact h

/-- Every signed coordinate permutation preserving the lattice
is in the counted monomial subgroup. -/
theorem leechMonomial_mem (e : leechIsomSubgroup) (p : Equiv.Perm (Fin 24)) (d : Fin 24 → ZMod 2)
    (he : e.val = golayRealSign d * golayRealPermute p) : e ∈ golayMonomialSubgroup := by
  have hd := leechMonomial_sign_mem e p d he
  let s := golaySignIsometry ⟨d, hd⟩
  let ep : leechIsomSubgroup := s * e
  have hep : ep.val = golayRealPermute p := by
    apply LinearEquiv.ext
    intro x
    ext i
    change qSign (d i) * (e.val x i) = x (p.symm i)
    rw [he]
    change qSign (d i) * (qSign (d i) * x (p.symm i)) = _
    rw [← mul_assoc, qSign_sq, one_mul]
  have hp := leechPermutation_golay_mem ep p hep
  exact ⟨⟨d, hd⟩, ⟨p, hp⟩, Subtype.ext he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
