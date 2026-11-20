/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Universality.HexLiteralCountLaws

namespace StatMech.Universality

open HexWalk

namespace HexWalk



noncomputable def endpointVertices (w : HexWalk) : List ℂ :=
  w.vertices.dropLast


def EndpointIsSAW (w : HexWalk) : Prop :=
  w.endpointVertices.Nodup


def EndpointIsLegalSAW (w : HexWalk) : Prop :=
  w.LegalTurns ∧ w.EndpointIsSAW


def endpointNumVertices (w : HexWalk) : ℕ :=
  w.turns.length

@[simp]
theorem endpointNumVertices_eq (w : HexWalk) :
    w.endpointNumVertices = w.turns.length := rfl

@[simp]
theorem length_endpointVertices (w : HexWalk) :
    w.endpointVertices.length = w.endpointNumVertices := by
  simp [endpointVertices, endpointNumVertices]


theorem endpointVerticesAux_append_one (m : ℂ) (h : ℤ) (ts : List ℤ) (t : ℤ) :
    (verticesAux m h (ts ++ [t])).dropLast = verticesAux m h ts := by
  induction ts generalizing m h with
  | nil => simp [verticesAux]
  | cons u us ih =>
      simp only [List.cons_append, verticesAux_cons]
      rw [List.dropLast_cons_of_ne_nil]
      · rw [ih]
      · have hlen := length_verticesAux
          (m + halfStep h + halfStep (h + u)) (h + u) (us ++ [t])
        intro hempty
        rw [hempty] at hlen
        simp at hlen

@[simp]
theorem endpointVertices_ofTurns_append_one (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).endpointVertices =
      (ofTurns a h0 ts).vertices := by
  exact endpointVerticesAux_append_one a h0 ts t



theorem endpointIsSAW_append_one_iff (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).EndpointIsSAW ↔
      (ofTurns a h0 ts).IsSAW := by
  simp [EndpointIsSAW, IsSAW]



theorem legalTurns_append_one_iff (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).LegalTurns ↔
      (ofTurns a h0 ts).LegalTurns ∧ (t = 1 ∨ t = -1) := by
  simp only [LegalTurns, ofTurns_turns, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Or.inl hu), h t (Or.inr rfl)⟩
  · rintro ⟨h, ht⟩ u (hu | rfl)
    · exact h u hu
    · exact ht




theorem endpointIsLegalSAW_append_one_iff (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).EndpointIsLegalSAW ↔
      (ofTurns a h0 ts).IsLegalSAW ∧ (t = 1 ∨ t = -1) := by
  rw [EndpointIsLegalSAW, IsLegalSAW, legalTurns_append_one_iff,
    endpointIsSAW_append_one_iff]
  tauto


theorem endpoint_nil_isLegalSAW (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 []).EndpointIsLegalSAW := by
  constructor
  · intro t ht
    simp at ht
  · simp [EndpointIsSAW, endpointVertices, vertices, ofTurns]

end HexWalk






noncomputable def hexEndpointSAWFinset (a : ℂ) (h0 : ℤ) : ℕ → Finset (List ℤ)
  | 0 => {[]}
  | n + 1 =>
      (hlc_sawFinset a h0 n).image (fun ts => ts ++ [(1 : ℤ)]) ∪
      (hlc_sawFinset a h0 n).image (fun ts => ts ++ [(-1 : ℤ)])


noncomputable def hexEndpointSAWCount (a : ℂ) (h0 : ℤ) (n : ℕ) : ℕ :=
  (hexEndpointSAWFinset a h0 n).card



theorem hexEndpoint_mem_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) (ts : List ℤ) :
    ts ∈ hexEndpointSAWFinset a h0 n ↔
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧ ts.length = n := by
  classical
  cases n with
  | zero =>
      simp only [hexEndpointSAWFinset, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨endpoint_nil_isLegalSAW a h0, rfl⟩
      · rintro ⟨_, hlen⟩
        exact List.length_eq_zero_iff.mp hlen
  | succ n =>
      simp only [hexEndpointSAWFinset, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
        · have hb := (hlc_mem_sawFinset a h0 n s).mp hs
          refine ⟨(endpointIsLegalSAW_append_one_iff a h0 s 1).2
            ⟨hb.1, Or.inl rfl⟩, ?_⟩
          simp [hb.2]
        · have hb := (hlc_mem_sawFinset a h0 n s).mp hs
          refine ⟨(endpointIsLegalSAW_append_one_iff a h0 s (-1)).2
            ⟨hb.1, Or.inr rfl⟩, ?_⟩
          simp [hb.2]
      · rintro ⟨hlegal, hlen⟩
        induction ts using List.reverseRecOn with
        | nil => simp at hlen
        | append_singleton s t _ =>
            have hdata := (endpointIsLegalSAW_append_one_iff a h0 s t).mp hlegal
            have hslen : s.length = n := by simp at hlen; omega
            have hs : s ∈ hlc_sawFinset a h0 n :=
              (hlc_mem_sawFinset a h0 n s).2 ⟨hdata.1, hslen⟩
            rcases hdata.2 with rfl | rfl
            · exact Or.inl ⟨s, hs, rfl⟩
            · exact Or.inr ⟨s, hs, rfl⟩

@[simp]
theorem hexEndpointSAWCount_zero (a : ℂ) (h0 : ℤ) :
    hexEndpointSAWCount a h0 0 = 1 := by
  simp [hexEndpointSAWCount, hexEndpointSAWFinset]

private theorem hexEndpoint_append_one_injective (t : ℤ) :
    Function.Injective (fun ts : List ℤ => ts ++ [t]) :=
  List.append_left_injective [t]

private theorem hexEndpoint_extension_images_disjoint (a : ℂ) (h0 : ℤ) (n : ℕ) :
    Disjoint
      ((hlc_sawFinset a h0 n).image (fun ts => ts ++ [(1 : ℤ)]))
      ((hlc_sawFinset a h0 n).image (fun ts => ts ++ [(-1 : ℤ)])) := by
  classical
  rw [Finset.disjoint_left]
  intro u hu hp
  rcases Finset.mem_image.mp hu with ⟨s, _, rfl⟩
  rcases Finset.mem_image.mp hp with ⟨r, _, heq⟩
  have hlast := congrArg List.getLast? heq
  simp at hlast



theorem hexEndpointSAWCount_succ (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hexEndpointSAWCount a h0 (n + 1) = 2 * hlc_sawCount a h0 n := by
  classical
  unfold hexEndpointSAWCount
  rw [hexEndpointSAWFinset, Finset.card_union_of_disjoint
    (hexEndpoint_extension_images_disjoint a h0 n)]
  rw [Finset.card_image_of_injective _ (hexEndpoint_append_one_injective 1),
    Finset.card_image_of_injective _ (hexEndpoint_append_one_injective (-1)),
    hlc_card_sawFinset]
  omega




noncomputable def hexEndpointSAWCountR (a : ℂ) (h0 : ℤ) (n : ℕ) : ℝ :=
  (hexEndpointSAWCount a h0 n : ℝ)


noncomputable def hexEndpointCoeffWeight
    (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) : ℝ :=
  hexEndpointSAWCountR a h0 n * x ^ n

@[simp]
theorem hexEndpointSAWCountR_zero (a : ℂ) (h0 : ℤ) :
    hexEndpointSAWCountR a h0 0 = 1 := by
  simp [hexEndpointSAWCountR, hexEndpointSAWCount_zero]

@[simp]
theorem hexEndpointSAWCountR_succ (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hexEndpointSAWCountR a h0 (n + 1) = 2 * hlc_sawCountR a h0 n := by
  simp [hexEndpointSAWCountR, hexEndpointSAWCount_succ, hlc_sawCountR]

@[simp]
theorem hexEndpointCoeffWeight_zero (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexEndpointCoeffWeight a h0 x 0 = 1 := by
  simp [hexEndpointCoeffWeight]



theorem hexEndpointCoeffWeight_succ (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) :
    hexEndpointCoeffWeight a h0 x (n + 1) =
      (2 * x) * (hlc_sawCountR a h0 n * x ^ n) := by
  rw [hexEndpointCoeffWeight, hexEndpointSAWCountR_succ, pow_succ]
  ring



theorem hexEndpoint_summable_iff_hlc (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hx : x ≠ 0) :
    Summable (hexEndpointCoeffWeight a h0 x) ↔
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
  calc
    Summable (hexEndpointCoeffWeight a h0 x) ↔
        Summable (fun n => hexEndpointCoeffWeight a h0 x (n + 1)) :=
      (summable_nat_add_iff 1).symm
    _ ↔ Summable
        (fun n => (2 * x) * (hlc_sawCountR a h0 n * x ^ n)) :=
      summable_congr (hexEndpointCoeffWeight_succ a h0 x)
    _ ↔ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
      summable_mul_left_iff (mul_ne_zero (by norm_num) hx)



theorem hexEndpoint_summable_iff_hlc_of_pos (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hx : 0 < x) :
    Summable (hexEndpointCoeffWeight a h0 x) ↔
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  hexEndpoint_summable_iff_hlc a h0 hx.ne'



theorem hexEndpoint_not_summable_iff_hlc (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hx : 0 < x) :
    (¬ Summable (hexEndpointCoeffWeight a h0 x)) ↔
      ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  not_congr (hexEndpoint_summable_iff_hlc_of_pos a h0 hx)




theorem hexEndpoint_tsum_eq_of_summable (a : ℂ) (h0 : ℤ) {x : ℝ}
    (hcoeff : Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n)) :
    (∑' n, hexEndpointCoeffWeight a h0 x n) =
      1 + 2 * x * ∑' n, hlc_sawCountR a h0 n * x ^ n := by
  by_cases hx : x = 0
  · subst x
    have hend : Summable (hexEndpointCoeffWeight a h0 0) := by
      apply (hasSum_single 0 (fun n hn => ?_)).summable
      cases n with
      | zero => contradiction
      | succ n => simp [hexEndpointCoeffWeight]
    have hsplit := hend.sum_add_tsum_nat_add 1
    calc
      (∑' n, hexEndpointCoeffWeight a h0 0 n) =
          hexEndpointCoeffWeight a h0 0 0 +
            ∑' n, hexEndpointCoeffWeight a h0 0 (n + 1) := by
        simpa using hsplit.symm
      _ = 1 := by simp [hexEndpointCoeffWeight]
      _ = 1 + 2 * 0 * ∑' n, hlc_sawCountR a h0 n * 0 ^ n := by ring
  · have hend : Summable (hexEndpointCoeffWeight a h0 x) :=
      (hexEndpoint_summable_iff_hlc a h0 hx).2 hcoeff
    have hsplit := hend.sum_add_tsum_nat_add 1
    calc
      (∑' n, hexEndpointCoeffWeight a h0 x n) =
          1 + ∑' n, hexEndpointCoeffWeight a h0 x (n + 1) := by
        simpa using hsplit.symm
      _ = 1 + ∑' n, (2 * x) * (hlc_sawCountR a h0 n * x ^ n) := by
        congr 1
        apply tsum_congr
        exact hexEndpointCoeffWeight_succ a h0 x
      _ = 1 + 2 * x * ∑' n, hlc_sawCountR a h0 n * x ^ n := by
        rw [tsum_mul_left]


theorem hexEndpoint_hasSum_of_hlc_hasSum (a : ℂ) (h0 : ℤ) {x z : ℝ}
    (hcoeff : HasSum (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) z) :
    HasSum (hexEndpointCoeffWeight a h0 x) (1 + 2 * x * z) := by
  have hsum := hexEndpoint_tsum_eq_of_summable a h0 hcoeff.summable
  have hend : Summable (hexEndpointCoeffWeight a h0 x) := by
    by_cases hx : x = 0
    · subst x
      apply (hasSum_single 0 (fun n hn => ?_)).summable
      cases n with
      | zero => contradiction
      | succ n => simp [hexEndpointCoeffWeight]
    · exact (hexEndpoint_summable_iff_hlc a h0 hx).2 hcoeff.summable
  rw [← hcoeff.tsum_eq, ← hsum]
  exact hend.hasSum

end StatMech.Universality
