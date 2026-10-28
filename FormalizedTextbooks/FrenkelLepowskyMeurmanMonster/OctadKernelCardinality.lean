/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPhysicalSignSpace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTetradCardinality

/-! The actual canonical three-octad syndrome kernel and its physical
zero-sum description. The sign normalization removes the full octad
complement; the Golay minimum-weight argument identifies the code
supported on the twelve-coordinate union. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

lemma octadPhysicalNormalize_signMap (o : Fin 759) (x : OctadSignSpace) :
    octadPhysicalNormalize o (octadPhysicalSignMap o x) = x := by
  change octadSignNormalize
    (fun k => octadPhysicalEmbedding o (octadSignRepresentative x)
      (golayOctadCoordinate o k)) = x
  simpa only [octadPhysicalEmbedding_local] using octadSignNormalize_representative x

lemma octadPhysicalSignMap_injective (o : Fin 759) :
    Function.Injective (octadPhysicalSignMap o) := by
  intro x y h
  simpa only [octadPhysicalNormalize_signMap] using congrArg (octadPhysicalNormalize o) h

lemma octadPhysicalSignMap_anchor (o : Fin 759) (x : OctadSignSpace) :
    octadPhysicalSignMap o x (golayOctadCoordinate o 7) = 0 := by
  change octadPhysicalEmbedding o (octadSignRepresentative x) (golayOctadCoordinate o 7) = 0
  rw [octadPhysicalEmbedding_local, octadSignRepresentative_anchor]

lemma octadPhysicalNormalize_word (o : Fin 759) :
    octadPhysicalNormalize o (golayOctadWord o) = 0 := by
  ext i
  change golayOctadWord o (golayOctadCoordinate o (Fin.castAdd 2 i)) +
    golayOctadWord o (golayOctadCoordinate o 7) = 0
  rw [golayOctadWord_local, golayOctadWord_local]
  decide +kernel

lemma octadIntersection_four_distinct (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) : o ≠ p := by
  intro h
  subst p
  rw [golayOctadIntersection_support, Finset.inter_self, golayOctadSupport_card] at hfour
  contradiction

/-- The actual homogeneous syndrome kernel sums to a codeword in the
span of the two parent octads, without any additional support assumption. -/
theorem octadTripleSyndromeKernel_span (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (x : OctadTripleSignSpace) (hx : x ∈ octadTripleSyndromeKernel o p u) :
    ∃ α β : ZMod 2, octadTriplePhysicalSum o p u x =
      α • golayOctadWord o + β • golayOctadWord p := by
  let S := golayOctadSupport o ∪ golayOctadSupport p
  have hS : S.card ≤ 12 := by rw [golayOctad_union_card o p hfour]
  have hs (i : Fin 24) (hi : i ∉ S) :
      i ∉ golayOctadSupport o ∧ i ∉ golayOctadSupport p := by
    simpa only [S, Finset.mem_union, not_or] using hi
  have hsu (i : Fin 24) (hi : i ∉ S) : i ∉ golayOctadSupport u := by
    rw [golayOctad_sum_support o p u hu]
    simp only [Finset.mem_symmDiff, hs i hi, false_and, false_or, not_false_eq_true]
  have hn (i : Fin 24) (hi : i ∉ S) : octadTriplePhysicalSum o p u x i = 0 := by
    change octadPhysicalSignMap o (x 0) i + octadPhysicalSignMap p (x 1) i +
      octadPhysicalSignMap u (x 2) i = 0
    rw [octadPhysicalSignMap_supported o _ i (hs i hi).1,
      octadPhysicalSignMap_supported p _ i (hs i hi).2,
      octadPhysicalSignMap_supported u _ i (hsu i hi), zero_add, zero_add]
  have hcode : octadTriplePhysicalSum o p u x ∈ golayCode := by
    apply (golaySyndrome_zero_iff_code _).mp
    exact hx
  have hc := golayCode_supported_twelve_span S hS
    (golayOctadWord o) (golayOctadWord p) (octadTriplePhysicalSum o p u x)
    (golayOctadWord_mem_code o) (golayOctadWord_mem_code p) hcode
    (golayOctadWord_ne_zero o) (golayOctadWord_ne_zero p)
    (golayOctadWord_injective.ne (octadIntersection_four_distinct o p hfour))
    (fun i hi => golayOctadWord_supported o i (hs i hi).1)
    (fun i hi => golayOctadWord_supported p i (hs i hi).2) hn
  rcases hc with hc | hc | hc | hc
  · exact ⟨0, 0, by simpa only [zero_smul, zero_add] using hc⟩
  · exact ⟨1, 0, by simpa only [one_smul, zero_smul, add_zero] using hc⟩
  · exact ⟨0, 1, by simpa only [one_smul, zero_smul, zero_add] using hc⟩
  · exact ⟨1, 1, by simpa only [one_smul] using hc⟩

/-- The common tetrad and the two exclusive tetrads in the physical union. -/
def octadKernelTetradSet (o p : Fin 759) (s : Fin 3) : Finset (Fin 24) :=
  if s = 0 then golayOctadSupport o ∩ golayOctadSupport p
  else if s = 1 then golayOctadSupport o \ golayOctadSupport p
  else golayOctadSupport p \ golayOctadSupport o

lemma octadKernelTetradSet_card (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (s : Fin 3) :
    (octadKernelTetradSet o p s).card = 4 := by
  have hi : (golayOctadSupport o ∩ golayOctadSupport p).card = 4 := hfour
  fin_cases s
  · simpa [octadKernelTetradSet] using hi
  · norm_num [octadKernelTetradSet]
    rw [Finset.card_sdiff, Finset.inter_comm, golayOctadSupport_card, hi]
  · norm_num [octadKernelTetradSet]
    rw [Finset.card_sdiff, golayOctadSupport_card, hi]

noncomputable def octadKernelTetradCoordinate (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (s : Fin 3) :
    Fin 4 ≃ octadKernelTetradSet o p s :=
  (Finset.equivFinOfCardEq (octadKernelTetradSet_card o p hfour s)).symm

/-- Extend a tetrad pattern by zero to the actual physical coordinates. -/
noncomputable def octadKernelTetradEmbed (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (s : Fin 3) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun a i := if hi : i ∈ octadKernelTetradSet o p s then
    a ((octadKernelTetradCoordinate o p hfour s).symm ⟨i, hi⟩) else 0
  map_add' a b := by
    ext i
    split_ifs <;> simp_all [Pi.add_apply]
  map_smul' c a := by
    ext i
    split_ifs <;> simp_all [Pi.smul_apply, RingHom.id_apply]

lemma octadKernelTetradEmbed_local (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (s : Fin 3)
    (a : Fin 4 → ZMod 2) (j : Fin 4) :
    octadKernelTetradEmbed o p hfour s a (octadKernelTetradCoordinate o p hfour s j) = a j := by
  simp only [octadKernelTetradEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dite_eq_left (octadKernelTetradCoordinate o p hfour s j).property]
  change a ((octadKernelTetradCoordinate o p hfour s).symm
    (octadKernelTetradCoordinate o p hfour s j)) = a j
  rw [Equiv.symm_apply_apply]

lemma octadKernelTetradEmbed_supported (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (s : Fin 3)
    (a : Fin 4 → ZMod 2) (i : Fin 24) (hi : i ∉ octadKernelTetradSet o p s) :
    octadKernelTetradEmbed o p hfour s a i = 0 := dite_eq_right hi

lemma octadKernelTetradEmbed_sum (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (s : Fin 3)
    (a : Fin 4 → ZMod 2) : ∑ i, octadKernelTetradEmbed o p hfour s a i = ∑ j, a j := by
  let T := octadKernelTetradSet o p s
  let f : T → ZMod 2 := fun i => a ((octadKernelTetradCoordinate o p hfour s).symm i)
  calc
    (∑ i, octadKernelTetradEmbed o p hfour s a i) = ∑ i : T, f i := by
      change (∑ i, if hi : i ∈ T then f ⟨i, hi⟩ else 0) = ∑ i : T, f i
      rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_eq_sum_dite]
    _ = ∑ j, a j := Equiv.sum_comp (octadKernelTetradCoordinate o p hfour s).symm a

@[simp] lemma octadKernelTetradSet_zero (o p : Fin 759) :
    octadKernelTetradSet o p 0 = golayOctadSupport o ∩ golayOctadSupport p := by
  simp [octadKernelTetradSet]
@[simp] lemma octadKernelTetradSet_one (o p : Fin 759) :
    octadKernelTetradSet o p 1 = golayOctadSupport o \ golayOctadSupport p := by
  simp [octadKernelTetradSet]
@[simp] lemma octadKernelTetradSet_two (o p : Fin 759) :
    octadKernelTetradSet o p 2 = golayOctadSupport p \ golayOctadSupport o := by
  simp [octadKernelTetradSet]

/-- The three even physical patterns determined by compatible tetrad rows. -/
noncomputable def octadKernelRawPatterns (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    OctadTetradTriple →ₗ[ZMod 2] (Fin 3 → Fin 24 → ZMod 2) where
  toFun a s :=
    if s = 0 then octadKernelTetradEmbed o p hfour 0 (a 0) +
      octadKernelTetradEmbed o p hfour 1 (a 1)
    else if s = 1 then octadKernelTetradEmbed o p hfour 0 (a 0) +
      octadKernelTetradEmbed o p hfour 2 (a 2)
    else octadKernelTetradEmbed o p hfour 1 (a 1) +
      octadKernelTetradEmbed o p hfour 2 (a 2)
  map_add' a b := by
    ext s i
    split_ifs <;> simp_all [Pi.add_apply, map_add] <;> abel
  map_smul' c a := by
    ext s i
    split_ifs <;> simp_all [Pi.smul_apply, map_smul, RingHom.id_apply, Pi.add_apply, mul_add]

@[simp] lemma octadKernelRawPatterns_zero (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (a : OctadTetradTriple) :
    octadKernelRawPatterns o p hfour a 0 = octadKernelTetradEmbed o p hfour 0 (a 0) +
      octadKernelTetradEmbed o p hfour 1 (a 1) := by
  simp [octadKernelRawPatterns]
@[simp] lemma octadKernelRawPatterns_one (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (a : OctadTetradTriple) :
    octadKernelRawPatterns o p hfour a 1 = octadKernelTetradEmbed o p hfour 0 (a 0) +
      octadKernelTetradEmbed o p hfour 2 (a 2) := by
  simp [octadKernelRawPatterns]
@[simp] lemma octadKernelRawPatterns_two (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (a : OctadTetradTriple) :
    octadKernelRawPatterns o p hfour a 2 = octadKernelTetradEmbed o p hfour 1 (a 1) +
      octadKernelTetradEmbed o p hfour 2 (a 2) := by
  simp [octadKernelRawPatterns]

lemma octadKernelRawPatterns_sum_zero (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (a : OctadTetradTriple) :
    octadKernelRawPatterns o p hfour a 0 + octadKernelRawPatterns o p hfour a 1 +
      octadKernelRawPatterns o p hfour a 2 = 0 := by
  rw [octadKernelRawPatterns_zero, octadKernelRawPatterns_one, octadKernelRawPatterns_two]
  have h (v : Fin 24 → ZMod 2) : v + v = 0 := ZModModule.add_self v
  calc
    _ = (octadKernelTetradEmbed o p hfour 0 (a 0) + octadKernelTetradEmbed o p hfour 0 (a 0)) +
      (octadKernelTetradEmbed o p hfour 1 (a 1) + octadKernelTetradEmbed o p hfour 1 (a 1)) +
      (octadKernelTetradEmbed o p hfour 2 (a 2) +
        octadKernelTetradEmbed o p hfour 2 (a 2)) := by abel
    _ = 0 := by simp only [h]

lemma octadKernelRawPatterns_even (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (a : octadTetradCompatible) (s : Fin 3) :
    ∑ i, octadKernelRawPatterns o p hfour a.val s i = 0 := by
  have he (s t : Fin 3) : (∑ i, a.val s i) + (∑ i, a.val t i) = 0 := by
    rw [a.property s, a.property t]
    exact CharTwo.add_self_eq_zero _
  fin_cases s
  · change (∑ i, octadKernelRawPatterns o p hfour a.val 0 i) = 0
    rw [octadKernelRawPatterns_zero]
    simpa only [Pi.add_apply, Finset.sum_add_distrib, octadKernelTetradEmbed_sum] using he 0 1
  · change (∑ i, octadKernelRawPatterns o p hfour a.val 1 i) = 0
    rw [octadKernelRawPatterns_one]
    simpa only [Pi.add_apply, Finset.sum_add_distrib, octadKernelTetradEmbed_sum] using he 0 2
  · change (∑ i, octadKernelRawPatterns o p hfour a.val 2 i) = 0
    rw [octadKernelRawPatterns_two]
    simpa only [Pi.add_apply, Finset.sum_add_distrib, octadKernelTetradEmbed_sum] using he 1 2

/-- Parent octads and their sum, in the three source row positions. -/
def octadKernelRow (o p u : Fin 759) (s : Fin 3) : Fin 759 :=
  if s = 0 then o else if s = 1 then p else u

lemma octadKernelRawPatterns_supported (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (a : OctadTetradTriple) (s : Fin 3) (i : Fin 24)
    (hi : i ∉ golayOctadSupport (octadKernelRow o p u s)) :
    octadKernelRawPatterns o p hfour a s i = 0 := by
  fin_cases s
  · change i ∉ golayOctadSupport o at hi
    change octadKernelRawPatterns o p hfour a 0 i = 0
    rw [octadKernelRawPatterns_zero, Pi.add_apply]
    have h0 : i ∉ octadKernelTetradSet o p 0 := by simp [hi]
    have h1 : i ∉ octadKernelTetradSet o p 1 := by simp [hi]
    rw [octadKernelTetradEmbed_supported _ _ _ _ _ _ h0,
      octadKernelTetradEmbed_supported _ _ _ _ _ _ h1, zero_add]
  · change i ∉ golayOctadSupport p at hi
    change octadKernelRawPatterns o p hfour a 1 i = 0
    rw [octadKernelRawPatterns_one, Pi.add_apply]
    have h0 : i ∉ octadKernelTetradSet o p 0 := by simp [hi]
    have h2 : i ∉ octadKernelTetradSet o p 2 := by simp [hi]
    rw [octadKernelTetradEmbed_supported _ _ _ _ _ _ h0,
      octadKernelTetradEmbed_supported _ _ _ _ _ _ h2, zero_add]
  · change i ∉ golayOctadSupport u at hi
    change octadKernelRawPatterns o p hfour a 2 i = 0
    rw [golayOctad_sum_support o p u hu, Finset.mem_symmDiff, not_or] at hi
    rw [octadKernelRawPatterns_two, Pi.add_apply]
    have h1 : i ∉ octadKernelTetradSet o p 1 := by simpa using hi.1
    have h2 : i ∉ octadKernelTetradSet o p 2 := by simpa using hi.2
    rw [octadKernelTetradEmbed_supported _ _ _ _ _ _ h1,
      octadKernelTetradEmbed_supported _ _ _ _ _ _ h2, zero_add]

/-- Normalize the three raw physical rows into their actual source sign classes. -/
noncomputable def octadKernelTetradMap (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    octadTetradCompatible →ₗ[ZMod 2] OctadTripleSignSpace where
  toFun a s := octadPhysicalNormalize (octadKernelRow o p u s)
    (octadKernelRawPatterns o p hfour a.val s)
  map_add' a b := by
    ext s
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c a := by
    ext s
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]

lemma octadKernelTetradMap_mem (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (a : octadTetradCompatible) :
    octadKernelTetradMap o p u hfour a ∈ octadTripleSyndromeKernel o p u := by
  have he (s : Fin 3) := octadPhysicalSignMap_normalize (octadKernelRow o p u s)
    (octadKernelRawPatterns o p hfour a.val s)
    (octadKernelRawPatterns_supported o p u hfour hu a.val s)
    (octadKernelRawPatterns_even o p hfour a s)
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  change octadPhysicalSignMap o (octadKernelTetradMap o p u hfour a 0) = _ at h0
  change octadPhysicalSignMap p (octadKernelTetradMap o p u hfour a 1) = _ at h1
  change octadPhysicalSignMap u (octadKernelTetradMap o p u hfour a 2) = _ at h2
  change golaySyndrome (octadPhysicalSignMap o (octadKernelTetradMap o p u hfour a 0) +
    octadPhysicalSignMap p (octadKernelTetradMap o p u hfour a 1) +
    octadPhysicalSignMap u (octadKernelTetradMap o p u hfour a 2)) = 0
  rw [h0, h1, h2]
  have hc (q : Fin 759) (c : ZMod 2) : golaySyndrome (c • golayOctadWord q) = 0 := by
    rw [map_smul, (golaySyndrome_zero_iff_code _).mpr (golayOctadWord_mem_code q), smul_zero]
  simp only [map_add, hc, add_zero]
  rw [← map_add, ← map_add, octadKernelRawPatterns_sum_zero, map_zero]

lemma octadKernelTetradEmbed_restrict (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (s : Fin 3)
    (v : Fin 24 → ZMod 2) (i : Fin 24) :
    octadKernelTetradEmbed o p hfour s
      (fun j => v (octadKernelTetradCoordinate o p hfour s j)) i =
      if i ∈ octadKernelTetradSet o p s then v i else 0 := by
  by_cases hi : i ∈ octadKernelTetradSet o p s
  · simp only [octadKernelTetradEmbed, LinearMap.coe_mk, AddHom.coe_mk, hi,
      dite_true, ite_true]
    exact congrArg (fun j : octadKernelTetradSet o p s => v j)
      ((octadKernelTetradCoordinate o p hfour s).apply_symm_apply ⟨i, hi⟩)
  · rw [octadKernelTetradEmbed_supported _ _ _ _ _ _ hi, ite_eq_right hi]

noncomputable def octadKernelTetradRead (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (r : Fin 3 → Fin 24 → ZMod 2) : OctadTetradTriple :=
  fun s j => if s = 0 then r 0 (octadKernelTetradCoordinate o p hfour 0 j)
    else if s = 1 then r 0 (octadKernelTetradCoordinate o p hfour 1 j)
    else r 1 (octadKernelTetradCoordinate o p hfour 2 j)

@[simp] lemma octadKernelTetradRead_zero (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (r : Fin 3 → Fin 24 → ZMod 2) :
    octadKernelTetradRead o p hfour r 0 =
      fun j => r 0 (octadKernelTetradCoordinate o p hfour 0 j) := by
  rfl
@[simp] lemma octadKernelTetradRead_one (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (r : Fin 3 → Fin 24 → ZMod 2) :
    octadKernelTetradRead o p hfour r 1 =
      fun j => r 0 (octadKernelTetradCoordinate o p hfour 1 j) := by
  rfl
@[simp] lemma octadKernelTetradRead_two (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (r : Fin 3 → Fin 24 → ZMod 2) :
    octadKernelTetradRead o p hfour r 2 =
      fun j => r 1 (octadKernelTetradCoordinate o p hfour 2 j) := by
  rfl

lemma octadKernel_eq_of_add_zero (a b : ZMod 2) (h : a + b = 0) : a = b := by
  apply add_right_cancel (b := b)
  exact h.trans (CharTwo.add_self_eq_zero b).symm

lemma octadKernelRawPatterns_read (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (r : Fin 3 → Fin 24 → ZMod 2)
    (hs : ∀ s i, i ∉ golayOctadSupport (octadKernelRow o p u s) → r s i = 0)
    (hr : r 0 + r 1 + r 2 = 0) :
    octadKernelRawPatterns o p hfour (octadKernelTetradRead o p hfour r) = r := by
  have h0 (i : Fin 24) (hi : i ∉ golayOctadSupport o) : r 0 i = 0 := hs 0 i hi
  have h1 (i : Fin 24) (hi : i ∉ golayOctadSupport p) : r 1 i = 0 := hs 1 i hi
  have h2 (i : Fin 24) (ho : i ∈ golayOctadSupport o) (hp : i ∈ golayOctadSupport p) :
      r 2 i = 0 := by
    apply hs 2 i
    change i ∉ golayOctadSupport u
    rw [golayOctad_sum_support o p u hu]
    simp only [Finset.mem_symmDiff, ho, hp, not_true_eq_false, and_false,
      false_or, not_false_eq_true]
  have h01 (i : Fin 24) (ho : i ∈ golayOctadSupport o) (hp : i ∈ golayOctadSupport p) :
      r 0 i = r 1 i := by
    have hi := congrFun hr i
    change r 0 i + r 1 i + r 2 i = 0 at hi
    rw [h2 i ho hp, add_zero] at hi
    exact octadKernel_eq_of_add_zero _ _ hi
  have h02 (i : Fin 24) (hp : i ∉ golayOctadSupport p) : r 0 i = r 2 i := by
    have hi := congrFun hr i
    change r 0 i + r 1 i + r 2 i = 0 at hi
    rw [h1 i hp, add_zero] at hi
    exact octadKernel_eq_of_add_zero _ _ hi
  have h12 (i : Fin 24) (ho : i ∉ golayOctadSupport o) : r 1 i = r 2 i := by
    have hi := congrFun hr i
    change r 0 i + r 1 i + r 2 i = 0 at hi
    rw [h0 i ho, zero_add] at hi
    exact octadKernel_eq_of_add_zero _ _ hi
  ext s i
  fin_cases s
  · change octadKernelRawPatterns o p hfour (octadKernelTetradRead o p hfour r) 0 i = r 0 i
    rw [octadKernelRawPatterns_zero, Pi.add_apply, octadKernelTetradRead_zero,
      octadKernelTetradRead_one, octadKernelTetradEmbed_restrict, octadKernelTetradEmbed_restrict]
    by_cases ho : i ∈ golayOctadSupport o <;> by_cases hp : i ∈ golayOctadSupport p <;>
      simp [ho, hp, h0 i]
  · change octadKernelRawPatterns o p hfour (octadKernelTetradRead o p hfour r) 1 i = r 1 i
    rw [octadKernelRawPatterns_one, Pi.add_apply, octadKernelTetradRead_zero,
      octadKernelTetradRead_two, octadKernelTetradEmbed_restrict, octadKernelTetradEmbed_restrict]
    by_cases ho : i ∈ golayOctadSupport o <;> by_cases hp : i ∈ golayOctadSupport p <;>
      simp [ho, hp, h1 i, h01 i]
  · change octadKernelRawPatterns o p hfour (octadKernelTetradRead o p hfour r) 2 i = r 2 i
    rw [octadKernelRawPatterns_two, Pi.add_apply, octadKernelTetradRead_one,
      octadKernelTetradRead_two, octadKernelTetradEmbed_restrict, octadKernelTetradEmbed_restrict]
    by_cases ho : i ∈ golayOctadSupport o
    · by_cases hp : i ∈ golayOctadSupport p
      · simp [ho, hp, h2 i ho hp]
      · simp [ho, hp, h02 i hp]
    · by_cases hp : i ∈ golayOctadSupport p
      · simp [ho, hp, h12 i ho]
      · have h20 : r 2 i = 0 := (h02 i hp).symm.trans (h0 i ho)
        simp [ho, hp, h20]

lemma octadKernelRawPatterns_surjective (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (r : Fin 3 → Fin 24 → ZMod 2)
    (hs : ∀ s i, i ∉ golayOctadSupport (octadKernelRow o p u s) → r s i = 0)
    (he : ∀ s, ∑ i, r s i = 0) (hr : r 0 + r 1 + r 2 = 0) :
    ∃ a : octadTetradCompatible, octadKernelRawPatterns o p hfour a.val = r := by
  let a := octadKernelTetradRead o p hfour r
  have ha := octadKernelRawPatterns_read o p u hfour hu r hs hr
  have h01 : (∑ j, a 0 j) = ∑ j, a 1 j := by
    apply octadKernel_eq_of_add_zero
    have h := congrArg (fun v : Fin 3 → Fin 24 → ZMod 2 => ∑ i, v 0 i) ha
    rw [octadKernelRawPatterns_zero] at h
    simpa only [Pi.add_apply, Finset.sum_add_distrib, octadKernelTetradEmbed_sum, he 0] using h
  have h02 : (∑ j, a 0 j) = ∑ j, a 2 j := by
    apply octadKernel_eq_of_add_zero
    have h := congrArg (fun v : Fin 3 → Fin 24 → ZMod 2 => ∑ i, v 1 i) ha
    rw [octadKernelRawPatterns_one] at h
    simpa only [Pi.add_apply, Finset.sum_add_distrib, octadKernelTetradEmbed_sum, he 1] using h
  refine ⟨⟨a, ?_⟩, ha⟩
  intro s
  fin_cases s
  · rfl
  · exact h01.symm
  · exact h02.symm

lemma octadKernelTetradRead_raw (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) (a : OctadTetradTriple) :
    octadKernelTetradRead o p hfour (octadKernelRawPatterns o p hfour a) = a := by
  ext s j
  fin_cases s
  · change octadKernelRawPatterns o p hfour a 0
      (octadKernelTetradCoordinate o p hfour 0 j) = a 0 j
    rw [octadKernelRawPatterns_zero, Pi.add_apply, octadKernelTetradEmbed_local]
    have hm := (octadKernelTetradCoordinate o p hfour 0 j).property
    simp only [octadKernelTetradSet_zero, Finset.mem_inter] at hm
    have hn : (octadKernelTetradCoordinate o p hfour 0 j).val ∉ octadKernelTetradSet o p 1 := by
      simp [hm.2]
    rw [octadKernelTetradEmbed_supported _ _ _ _ _ _ hn, add_zero]
  · change octadKernelRawPatterns o p hfour a 0
      (octadKernelTetradCoordinate o p hfour 1 j) = a 1 j
    rw [octadKernelRawPatterns_zero, Pi.add_apply]
    have hm := (octadKernelTetradCoordinate o p hfour 1 j).property
    simp only [octadKernelTetradSet_one, Finset.mem_sdiff] at hm
    have hn : (octadKernelTetradCoordinate o p hfour 1 j).val ∉ octadKernelTetradSet o p 0 := by
      simp [hm.2]
    rw [octadKernelTetradEmbed_supported _ _ _ _ _ _ hn, zero_add, octadKernelTetradEmbed_local]
  · change octadKernelRawPatterns o p hfour a 1
      (octadKernelTetradCoordinate o p hfour 2 j) = a 2 j
    rw [octadKernelRawPatterns_one, Pi.add_apply]
    have hm := (octadKernelTetradCoordinate o p hfour 2 j).property
    simp only [octadKernelTetradSet_two, Finset.mem_sdiff] at hm
    have hn : (octadKernelTetradCoordinate o p hfour 2 j).val ∉ octadKernelTetradSet o p 0 := by
      simp [hm.2]
    rw [octadKernelTetradEmbed_supported _ _ _ _ _ _ hn, zero_add, octadKernelTetradEmbed_local]

lemma octadKernelRawPatterns_injective (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    Function.Injective (octadKernelRawPatterns o p hfour) := by
  intro a b h
  simpa only [octadKernelTetradRead_raw] using congrArg (octadKernelTetradRead o p hfour) h

lemma golayOctadWord_sum_zero (o : Fin 759) : (∑ i, golayOctadWord o i) = 0 := by
  have h : ((∑ i, (golayOctadWord o i).val : ℕ) : ZMod 2) = 0 := by
    rw [golayOctadWord_weight]
    decide +kernel
  simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using h

lemma octadKernelTetradMap_surjective (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (x : octadTripleSyndromeKernel o p u) :
    ∃ a : octadTetradCompatible, octadKernelTetradMap o p u hfour a = x.val := by
  obtain ⟨α, β, hsum⟩ := octadTripleSyndromeKernel_span o p u hfour hu x.val x.property
  let r : Fin 3 → Fin 24 → ZMod 2 := fun s =>
    if s = 0 then octadPhysicalSignMap o (x.val 0) + α • golayOctadWord o
    else if s = 1 then octadPhysicalSignMap p (x.val 1) + β • golayOctadWord p
    else octadPhysicalSignMap u (x.val 2)
  have h0 : r 0 = octadPhysicalSignMap o (x.val 0) + α • golayOctadWord o := rfl
  have h1 : r 1 = octadPhysicalSignMap p (x.val 1) + β • golayOctadWord p := rfl
  have h2 : r 2 = octadPhysicalSignMap u (x.val 2) := rfl
  have hs : ∀ s i, i ∉ golayOctadSupport (octadKernelRow o p u s) → r s i = 0 := by
    intro s i hi
    fin_cases s
    · change i ∉ golayOctadSupport o at hi
      change r 0 i = 0
      rw [h0, Pi.add_apply, Pi.smul_apply, octadPhysicalSignMap_supported _ _ _ hi,
        golayOctadWord_supported _ _ hi, smul_zero, zero_add]
    · change i ∉ golayOctadSupport p at hi
      change r 1 i = 0
      rw [h1, Pi.add_apply, Pi.smul_apply, octadPhysicalSignMap_supported _ _ _ hi,
        golayOctadWord_supported _ _ hi, smul_zero, zero_add]
    · change i ∉ golayOctadSupport u at hi
      change r 2 i = 0
      rw [h2]
      exact octadPhysicalSignMap_supported _ _ _ hi
  have he : ∀ s, (∑ i, r s i) = 0 := by
    intro s
    fin_cases s
    · change (∑ i, r 0 i) = 0
      rw [h0]
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib,
        ← Finset.smul_sum, octadPhysicalSignMap_even, golayOctadWord_sum_zero,
        smul_zero, zero_add]
    · change (∑ i, r 1 i) = 0
      rw [h1]
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib,
        ← Finset.smul_sum, octadPhysicalSignMap_even, golayOctadWord_sum_zero,
        smul_zero, zero_add]
    · change (∑ i, r 2 i) = 0
      rw [h2, octadPhysicalSignMap_even]
  have hr : r 0 + r 1 + r 2 = 0 := by
    rw [h0, h1, h2]
    calc
      _ = octadTriplePhysicalSum o p u x.val + (α • golayOctadWord o + β • golayOctadWord p) := by
        dsimp only [octadTriplePhysicalSum, LinearMap.coe_mk, AddHom.coe_mk]
        abel
      _ = 0 := by rw [hsum]; exact ZModModule.add_self _
  obtain ⟨a, ha⟩ := octadKernelRawPatterns_surjective o p u hfour hu r hs he hr
  refine ⟨a, ?_⟩
  apply funext
  intro s
  change octadPhysicalNormalize (octadKernelRow o p u s)
    (octadKernelRawPatterns o p hfour a.val s) = x.val s
  rw [ha]
  fin_cases s
  · change octadPhysicalNormalize o (r 0) = x.val 0
    rw [h0, map_add, map_smul, octadPhysicalNormalize_signMap,
      octadPhysicalNormalize_word, smul_zero, add_zero]
  · change octadPhysicalNormalize p (r 1) = x.val 1
    rw [h1, map_add, map_smul, octadPhysicalNormalize_signMap,
      octadPhysicalNormalize_word, smul_zero, add_zero]
  · change octadPhysicalNormalize u (r 2) = x.val 2
    rw [h2, octadPhysicalNormalize_signMap]

lemma golayOctadWord_mem_one (o : Fin 759) (i : Fin 24) (hi : i ∈ golayOctadSupport o) :
    golayOctadWord o i = 1 := by
  have hf : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide +kernel
  exact hf _ ((golayOctadWord_ne_zero_iff o i).mpr hi)

lemma octadKernelTetradRead_words (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (r : Fin 3 → Fin 24 → ZMod 2) (c : ZMod 2)
    (h0 : r 0 = c • golayOctadWord o) (h1 : r 1 = c • golayOctadWord p) :
    octadKernelTetradRead o p hfour r = (c • octadTetradAllOne).val := by
  ext s j
  fin_cases s
  · change r 0 (octadKernelTetradCoordinate o p hfour 0 j) = c * 1
    have hm := (octadKernelTetradCoordinate o p hfour 0 j).property
    simp only [octadKernelTetradSet_zero, Finset.mem_inter] at hm
    rw [h0, Pi.smul_apply, golayOctadWord_mem_one o _ hm.1, smul_eq_mul]
  · change r 0 (octadKernelTetradCoordinate o p hfour 1 j) = c * 1
    have hm := (octadKernelTetradCoordinate o p hfour 1 j).property
    simp only [octadKernelTetradSet_one, Finset.mem_sdiff] at hm
    rw [h0, Pi.smul_apply, golayOctadWord_mem_one o _ hm.1, smul_eq_mul]
  · change r 1 (octadKernelTetradCoordinate o p hfour 2 j) = c * 1
    have hm := (octadKernelTetradCoordinate o p hfour 2 j).property
    simp only [octadKernelTetradSet_two, Finset.mem_sdiff] at hm
    rw [h1, Pi.smul_apply, golayOctadWord_mem_one p _ hm.1, smul_eq_mul]

lemma binary_two_independent_coefficients
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v w : V)
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) (a b : ZMod 2)
    (h : a • v + b • w = 0) : a = 0 ∧ b = 0 := by
  have hf : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  rcases hf a with rfl | rfl <;> rcases hf b with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at h
    exact (hw h).elim
  · simp only [zero_smul, one_smul, add_zero] at h
    exact (hv h).elim
  · simp only [one_smul] at h
    have he : v = w := by
      apply add_right_cancel (b := w)
      exact h.trans (ZModModule.add_self w).symm
    exact (hvw he).elim

lemma octadKernelTetradMap_kernel (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (a : octadTetradCompatible) (ha : octadKernelTetradMap o p u hfour a = 0) :
    ∃ c : ZMod 2, a = c • octadTetradAllOne := by
  let r := octadKernelRawPatterns o p hfour a.val
  let c : Fin 3 → ZMod 2 := fun s => r s (golayOctadCoordinate (octadKernelRow o p u s) 7)
  have he (s : Fin 3) : r s = c s • golayOctadWord (octadKernelRow o p u s) := by
    have hrec := octadPhysicalSignMap_normalize (octadKernelRow o p u s) (r s)
      (octadKernelRawPatterns_supported o p u hfour hu a.val s)
      (octadKernelRawPatterns_even o p hfour a s)
    have hn : octadPhysicalNormalize (octadKernelRow o p u s) (r s) = 0 := congrFun ha s
    rw [hn, map_zero] at hrec
    apply add_right_cancel (b := c s • golayOctadWord (octadKernelRow o p u s))
    exact hrec.symm.trans (ZModModule.add_self _).symm
  have h0 : r 0 = c 0 • golayOctadWord o := he 0
  have h1 : r 1 = c 1 • golayOctadWord p := he 1
  have h2 : r 2 = c 2 • golayOctadWord u := he 2
  have hsum : (c 0 + c 2) • golayOctadWord o + (c 1 + c 2) • golayOctadWord p = 0 := by
    calc
      _ = c 0 • golayOctadWord o + c 1 • golayOctadWord p + c 2 • golayOctadWord u := by
        rw [hu, add_smul, add_smul, smul_add]
        abel
      _ = 0 := by rw [← h0, ← h1, ← h2]; exact octadKernelRawPatterns_sum_zero o p hfour a.val
  have hc := binary_two_independent_coefficients (golayOctadWord o) (golayOctadWord p)
    (golayOctadWord_ne_zero o) (golayOctadWord_ne_zero p)
    (golayOctadWord_injective.ne (octadIntersection_four_distinct o p hfour)) _ _ hsum
  have hc0 : c 0 = c 2 := octadKernel_eq_of_add_zero _ _ hc.1
  have hc1 : c 1 = c 2 := octadKernel_eq_of_add_zero _ _ hc.2
  refine ⟨c 2, ?_⟩
  apply Subtype.ext
  have hr := octadKernelTetradRead_words o p hfour r (c 2)
    (by simpa only [hc0] using h0) (by simpa only [hc1] using h1)
  rw [octadKernelTetradRead_raw] at hr
  exact hr

lemma octadKernelTetradMap_allOne (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    octadKernelTetradMap o p u hfour octadTetradAllOne = 0 := by
  let r : Fin 3 → Fin 24 → ZMod 2 := fun s => golayOctadWord (octadKernelRow o p u s)
  have h0 : r 0 = golayOctadWord o := rfl
  have h1 : r 1 = golayOctadWord p := rfl
  have h2 : r 2 = golayOctadWord u := rfl
  have hs : ∀ s i, i ∉ golayOctadSupport (octadKernelRow o p u s) → r s i = 0 := by
    intro s i hi
    exact golayOctadWord_supported _ _ hi
  have hr : r 0 + r 1 + r 2 = 0 := by
    rw [h0, h1, h2, hu]
    exact ZModModule.add_self _
  have hread := octadKernelTetradRead_words o p hfour r 1
    (by simpa only [one_smul] using h0) (by simpa only [one_smul] using h1)
  simp only [one_smul] at hread
  have hraw := octadKernelRawPatterns_read o p u hfour hu r hs hr
  rw [hread] at hraw
  apply funext
  intro s
  change octadPhysicalNormalize (octadKernelRow o p u s)
    (octadKernelRawPatterns o p hfour octadTetradAllOne.val s) = 0
  rw [hraw]
  exact octadPhysicalNormalize_word (octadKernelRow o p u s)

lemma octadKernelTetradMap_normalize (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (a : octadTetradCompatible) :
    octadKernelTetradMap o p u hfour (octadTetradNormalize a).val =
      octadKernelTetradMap o p u hfour a := by
  change octadKernelTetradMap o p u hfour (a + octadTetradAnchor a • octadTetradAllOne) = _
  rw [map_add, map_smul, octadKernelTetradMap_allOne o p u hfour hu, smul_zero, add_zero]

/-- The physical normalization map on the canonical nine-dimensional tetrad representatives. -/
noncomputable def octadKernelNormalizedMap (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (a : octadTetradNormalized) : octadTripleSyndromeKernel o p u :=
  ⟨octadKernelTetradMap o p u hfour a.val, octadKernelTetradMap_mem o p u hfour hu a.val⟩

lemma octadKernelNormalizedMap_injective (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    Function.Injective (octadKernelNormalizedMap o p u hfour hu) := by
  intro a b hab
  have hm : octadKernelTetradMap o p u hfour (a.val - b.val) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val hab
  obtain ⟨c, hc⟩ := octadKernelTetradMap_kernel o p u hfour hu (a.val - b.val) hm
  have ha : octadTetradAnchor (a.val - b.val) = 0 := by
    rw [map_sub, octadTetradNormalized_anchor, octadTetradNormalized_anchor, sub_self]
  rw [hc, map_smul, octadTetradAnchor_one, smul_eq_mul, mul_one] at ha
  apply Subtype.ext
  apply sub_eq_zero.mp
  rw [hc, ha, zero_smul]

lemma octadKernelNormalizedMap_surjective (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    Function.Surjective (octadKernelNormalizedMap o p u hfour hu) := by
  intro x
  obtain ⟨a, ha⟩ := octadKernelTetradMap_surjective o p u hfour hu x
  refine ⟨octadTetradNormalize a, ?_⟩
  apply Subtype.ext
  exact (octadKernelTetradMap_normalize o p u hfour hu a).trans ha

/-- The actual homogeneous three-octad syndrome kernel has exactly 512 elements. -/
theorem octadTripleSyndromeKernel_card (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    Nat.card (octadTripleSyndromeKernel o p u) = 512 := by
  let e : octadTetradNormalized ≃ octadTripleSyndromeKernel o p u :=
    Equiv.ofBijective (octadKernelNormalizedMap o p u hfour hu)
      ⟨octadKernelNormalizedMap_injective o p u hfour hu,
        octadKernelNormalizedMap_surjective o p u hfour hu⟩
  rw [← Nat.card_congr e]
  exact octadTetradNormalized_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
