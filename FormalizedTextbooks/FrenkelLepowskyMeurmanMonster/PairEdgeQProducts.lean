/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Pair-edge products in the actual extraspecial group. The absence of Golay
words of weight below eight makes a three-edge cocode relation an actual
incidence relation. Source: Seysen, §§2 and 6.1–6.2; Conway, §12.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MatrixPairAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

/-- Binary incidence vector of an unordered coordinate pair. -/
def griessPairIncidence (p : Fin 276) : Fin 24 → ZMod 2 :=
  Pi.single (griessCoordinatePair p).1 1 + Pi.single (griessCoordinatePair p).2 1

/-- A binary sum of vertex incidences has weight at most the number of vertices. -/
theorem binaryVertexSum_weight_le (n : ℕ) (v : Fin n → Fin 24) :
    (∑ i : Fin 24, ((∑ j, (Pi.single (v j) 1 : Fin 24 → ZMod 2)) i).val) ≤ n := by
  let S : Finset (Fin 24) := Finset.univ.image v
  have hpoint (i : Fin 24) :
      ((∑ j, (Pi.single (v j) 1 : Fin 24 → ZMod 2)) i).val ≤ if i ∈ S then 1 else 0 := by
    by_cases hi : i ∈ S
    · simp only [hi, ite_true]
      exact Nat.le_of_lt_succ (ZMod.val_lt _)
    · have hz : (∑ j, (Pi.single (v j) 1 : Fin 24 → ZMod 2)) i = 0 := by
        simp only [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro j _
        have hij : i ≠ v j := by
          intro h
          apply hi
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h.symm⟩
        simp [hij]
      simp [hi, hz]
  calc
    _ ≤ ∑ i : Fin 24, if i ∈ S then 1 else 0 := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = S.card := by simp
    _ ≤ n := by
      exact (Finset.card_image_le).trans (by simp)

/-- A short sum of vertices with zero Golay syndrome must itself vanish. -/
theorem binaryVertexSum_eq_zero_of_syndrome (n : ℕ) (v : Fin n → Fin 24)
    (hn : n < 8)
    (h : golaySyndrome (∑ j, (Pi.single (v j) 1 : Fin 24 → ZMod 2)) = 0) :
    ∑ j, (Pi.single (v j) 1 : Fin 24 → ZMod 2) = 0 := by
  let c := ∑ j, (Pi.single (v j) 1 : Fin 24 → ZMod 2)
  have hc : c ∈ golayCode := by
    have hd := golayCodeCocode_decomposition c
    rw [h, map_zero, sub_zero, add_zero] at hd
    exact hd.symm ▸ ⟨_, rfl⟩
  by_contra hzero
  have hmin := golayCode_weight_ge_eight c hc hzero
  have hmax := binaryVertexSum_weight_le n v
  dsimp [c] at hmin
  omega

theorem griessPairIncidence_syndrome (p : Fin 276) :
    golaySyndrome (griessPairIncidence p) = griessPairSyndrome p := by
  ext k
  simp [griessPairIncidence, golaySyndrome, griessPairSyndrome, Pi.single_apply,
    add_mul, Finset.sum_add_distrib]

/-- The three-edge relation is faithful before passing to cocode coordinates. -/
theorem griessPairSyndrome_triangle_iff (p q r : Fin 276) :
    griessPairSyndrome p + griessPairSyndrome q + griessPairSyndrome r = 0 ↔
      griessPairIncidence p + griessPairIncidence q + griessPairIncidence r = 0 := by
  let v : Fin 6 → Fin 24 := ![(griessCoordinatePair p).1, (griessCoordinatePair p).2,
    (griessCoordinatePair q).1, (griessCoordinatePair q).2,
    (griessCoordinatePair r).1, (griessCoordinatePair r).2]
  have hv : (∑ j, (Pi.single (v j) 1 : Fin 24 → ZMod 2)) =
      griessPairIncidence p + griessPairIncidence q + griessPairIncidence r := by
    simp [v, griessPairIncidence, Fin.sum_univ_succ]
    abel
  constructor
  · intro h
    rw [← hv]
    apply binaryVertexSum_eq_zero_of_syndrome 6 v (by omega)
    rw [hv, map_add, map_add, griessPairIncidence_syndrome,
      griessPairIncidence_syndrome, griessPairIncidence_syndrome, h]
  · intro h
    have hh := congrArg golaySyndrome h
    simpa only [map_add, map_zero, griessPairIncidence_syndrome] using hh

/-- The binary translation of a pair lift is its color times the all-one code. -/
theorem griessPairQ_translation_color (s : Fin 2) (p : Fin 276) :
    spinTranslation (griessShortQ (Sum.inl (s, p))) =
      (s.val : ZMod 2) • (Pi.single 11 1 : SpinIndex) := by
  rw [griessPairQ_translation]
  fin_cases s <;> simp

/-- Equality of Q bases is equality of their two spin-coordinate halves. -/
theorem qBase_eq_iff_spin_coordinates (g h : Q) :
    g.base = h.base ↔ spinTranslation g = spinTranslation h ∧
      spinModulation g = spinModulation h := by
  constructor
  · intro he
    exact ⟨congrArg (fun b : Multiplicative (Fin 24 → ZMod 2) =>
      fun i : Fin 12 => toAdd b (Fin.castAdd 12 i)) he,
      congrArg (fun b : Multiplicative (Fin 24 → ZMod 2) =>
        fun i : Fin 12 => toAdd b (Fin.natAdd 12 i)) he⟩
  · rintro ⟨ht, hm⟩
    apply Multiplicative.toAdd.injective
    ext i
    refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i
    · exact congrFun ht j
    · exact congrFun hm j

theorem pairEdge_add_eq_iff_triple {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (a b c : A) : a + b = c ↔ a + b + c = 0 := by
  constructor
  · intro h
    rw [h, ZModModule.add_self]
  · intro h
    have hh := congrArg (fun x => x + c) h
    simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh

/-- A pair-syndrome addition relation is exactly the actual edge relation. -/
theorem griessPairSyndrome_add_iff_incidence (p q r : Fin 276) :
    griessPairSyndrome p + griessPairSyndrome q = griessPairSyndrome r ↔
      griessPairIncidence p + griessPairIncidence q = griessPairIncidence r := by
  rw [pairEdge_add_eq_iff_triple, griessPairSyndrome_triangle_iff,
    ← pairEdge_add_eq_iff_triple]

/-- Pair products match a third pair precisely when colors and incidence add. -/
theorem griessPairQ_product_base_iff (s t u : Fin 2) (p q r : Fin 276) :
    (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inl (t, q))).base =
      (griessShortQ (Sum.inl (u, r))).base ↔
    ((s.val : ZMod 2) + (t.val : ZMod 2) = (u.val : ZMod 2)) ∧
      (griessPairSyndrome p + griessPairSyndrome q = griessPairSyndrome r) := by
  rw [qBase_eq_iff_spin_coordinates, spinTranslation_mul, spinModulation_mul]
  simp_rw [griessPairQ_translation_color, griessPairQ_modulation]
  constructor
  · rintro ⟨ht, hm⟩
    have hv := congrFun ht (11 : Fin 12)
    simpa using And.intro hv hm
  · rintro ⟨ht, hm⟩
    refine ⟨?_, hm⟩
    rw [← add_smul, ht]

/-- The three-edge preferred-Q relation, stated entirely in source incidence. -/
theorem griessPairQ_product_base_incidence_iff (s t u : Fin 2) (p q r : Fin 276) :
    (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inl (t, q))).base =
      (griessShortQ (Sum.inl (u, r))).base ↔
    ((s.val : ZMod 2) + (t.val : ZMod 2) = (u.val : ZMod 2)) ∧
      (griessPairIncidence p + griessPairIncidence q = griessPairIncidence r) := by
  rw [griessPairQ_product_base_iff, griessPairSyndrome_add_iff_incidence]

/-- The product of pair lifts has no additional central sign. -/
theorem griessPairQ_product_eq (s t u : Fin 2) (p q r : Fin 276)
    (hcolor : (s.val : ZMod 2) + (t.val : ZMod 2) = (u.val : ZMod 2))
    (hsyndrome : griessPairSyndrome p + griessPairSyndrome q = griessPairSyndrome r) :
    griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inl (t, q)) =
      griessShortQ (Sum.inl (u, r)) := by
  apply NormalizedCocycleExtension.Extension.ext
  · exact (griessPairQ_product_base_iff s t u p q r).mpr ⟨hcolor, hsyndrome⟩
  · apply Multiplicative.toAdd.injective
    rw [griessPairQ_product_coeff, griessShortQ_coeff]

theorem pairEdge_short_base_eq_iff (r s : GriessShortIndex) :
    (griessShortQ r).base = (griessShortQ s).base ↔ r = s := by
  constructor
  · intro h
    apply griessShortClass_injective
    apply leechHyperbolicCoordinates.injective
    exact congrArg Multiplicative.toAdd h
  · rintro rfl
    rfl

/-- Incidence identifies the full raw pair-basis product, including its unique
short output and absence of a matrix contribution for different edges. -/
theorem conwayRawProduct_pairBasis_of_incidence (s t u : Fin 2) (p q r : Fin 276)
    (hpq : p ≠ q)
    (hcolor : (s.val : ZMod 2) + (t.val : ZMod 2) = (u.val : ZMod 2))
    (hincidence : griessPairIncidence p + griessPairIncidence q = griessPairIncidence r) :
    conwayRawProduct (conwayShortBasis (Sum.inl (s, p)))
      (conwayShortBasis (Sum.inl (t, q))) = conwayShortBasis (Sum.inl (u, r)) := by
  have hprod := griessPairQ_product_eq s t u p q r hcolor
    ((griessPairSyndrome_add_iff_incidence p q r).mpr hincidence)
  have hrs : (Sum.inl (s, p) : GriessShortIndex) ≠ Sum.inl (t, q) := by
    intro h
    exact hpq (Prod.mk.inj (Sum.inl.inj h)).2
  have hb : (griessShortQ (Sum.inl (s, p)) *
      griessShortQ (Sum.inl (t, q))).base ≠ 1 := by
    intro h
    exact hrs ((griessShortQ_product_base_one_iff _ _).mp h)
  rw [conwayRawProduct_shortBasis]
  simp only [hb, ite_false, griessPairQ_product_sign, one_mul]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  ext v
  simp only [hprod, pairEdge_short_base_eq_iff, conwayShortBasis, Pi.single_apply, eq_comm]

/-- Pair-index incidence is independent of the ordering of its endpoints. -/
theorem griessPairIncidence_index (i j : Fin 24) (hij : i ≠ j) :
    griessPairIncidence (griessPairIndex i j hij) = Pi.single i 1 + Pi.single j 1 := by
  rw [griessPairIncidence, griessPairIndex_coordinates]
  by_cases h : i < j
  · simp [h]
  · simp [h, add_comm]

/-- Two edges sharing one endpoint add to the remaining edge in binary incidence. -/
theorem griessPairIncidence_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    griessPairIncidence (griessPairIndex i j hij) +
      griessPairIncidence (griessPairIndex j k hjk) =
        griessPairIncidence (griessPairIndex i k hik) := by
  simp only [griessPairIncidence_index]
  calc
    _ = (Pi.single i 1 + Pi.single k 1) +
        ((Pi.single j 1 : Fin 24 → ZMod 2) + Pi.single j 1) := by abel
    _ = _ := by rw [ZModModule.add_self, add_zero]

/-- The exact preferred-Q product for any triangle of distinct endpoints. -/
theorem griessPairQ_product_triangle (s t u : Fin 2) (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hcolor : (s.val : ZMod 2) + (t.val : ZMod 2) = (u.val : ZMod 2)) :
    griessShortQ (Sum.inl (s, griessPairIndex i j hij)) *
      griessShortQ (Sum.inl (t, griessPairIndex j k hjk)) =
        griessShortQ (Sum.inl (u, griessPairIndex i k hik)) := by
  apply griessPairQ_product_eq _ _ _ _ _ _ hcolor
  have h := congrArg golaySyndrome (griessPairIncidence_triangle i j k hij hjk hik)
  simpa only [map_add, griessPairIncidence_syndrome] using h

/-- Pair vectors have no coordinate outside their two endpoints. -/
theorem griessPairIntegral_off_support (s : Fin 2) (p : Fin 276) (i : Fin 24)
    (hi : i ≠ (griessCoordinatePair p).1) (hj : i ≠ (griessCoordinatePair p).2) :
    griessShortIntegral (Sum.inl (s, p)) i = 0 := by
  simp [griessShortIntegral, hi, hj]

/-- Pair edges with disjoint endpoints have zero actual integral pairing. -/
theorem griessPairIntegral_pairing_disjoint (s t : Fin 2) (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2) :
    leechIntegralPairing (griessShortIntegral (Sum.inl (s, p)))
      (griessShortIntegral (Sum.inl (t, q))) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = (griessCoordinatePair p).1
  · subst i
    rw [griessPairIntegral_off_support t q _ h11 h12, mul_zero]
  · by_cases hj : i = (griessCoordinatePair p).2
    · subst i
      rw [griessPairIntegral_off_support t q _ h21 h22, mul_zero]
    · rw [griessPairIntegral_off_support s p i hi hj, zero_mul]

/-- Disjoint pair products cannot match any actual short-vector base. -/
theorem griessPairQ_product_ne_short_disjoint (s t : Fin 2) (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2)
    (r : GriessShortIndex) :
    (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inl (t, q))).base ≠
      (griessShortQ r).base := by
  apply griessShortQ_product_base_ne_short
  · rw [griessPairIntegral_pairing_disjoint s t p q h11 h12 h21 h22]
    norm_num
  · rw [griessPairIntegral_pairing_disjoint s t p q h11 h12 h21 h22]
    norm_num

/-- The raw short-basis product of disjoint pair edges is zero. -/
theorem conwayRawProduct_pairBasis_disjoint (s t : Fin 2) (p q : Fin 276)
    (h11 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).1)
    (h12 : (griessCoordinatePair p).1 ≠ (griessCoordinatePair q).2)
    (h21 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).1)
    (h22 : (griessCoordinatePair p).2 ≠ (griessCoordinatePair q).2) :
    conwayRawProduct (conwayShortBasis (Sum.inl (s, p)))
      (conwayShortBasis (Sum.inl (t, q))) = 0 := by
  have hpair := griessPairIntegral_pairing_disjoint s t p q h11 h12 h21 h22
  have hpq : p ≠ q := by
    intro h
    subst q
    exact h11 rfl
  have hrs : (Sum.inl (s, p) : GriessShortIndex) ≠ Sum.inl (t, q) := by
    intro h
    have hh := Prod.mk.inj (Sum.inl.inj h)
    exact hpq hh.2
  rw [conwayRawProduct_shortBasis_of_pairing _ _ (by rw [hpair]; norm_num)
    (by rw [hpair]; norm_num)]
  simp only [hrs, ite_false]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
