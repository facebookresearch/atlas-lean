/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.CommonDifferenceProgressions
import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

section
namespace MetaMathlibExt

open scoped Pointwise

private theorem zmod_eq_empty_or_univ_of_subset_add_singleton {p : ℕ} [Fact (Nat.Prime p)]
    (X : Finset (ZMod p)) (δ : ZMod p) (hδ : δ ≠ 0) (h : X ⊆ X + {δ}) :
    X = ∅ ∨ X = Finset.univ := by
  rcases Finset.eq_empty_or_nonempty X with rfl | hne
  · exact Or.inl rfl
  · right
    have hcard : (X + {δ}).card = X.card := Finset.card_add_singleton X δ
    have heq : X = X + {δ} := Finset.eq_of_subset_of_card_le h (le_of_eq hcard)
    have h02 : (({0, δ} : Finset (ZMod p))).card = 2 :=
      Finset.card_pair (by simpa using hδ.symm)
    have hne02 : (({0, δ} : Finset (ZMod p))).Nonempty := ⟨0, by simp⟩
    have h0 : X + ({0} : Finset (ZMod p)) = X := by
      rw [Finset.singleton_zero, add_zero]
    have hsplit : X + ({0, δ} : Finset (ZMod p)) = X ∪ (X + {δ}) := by
      have hins : (({0, δ} : Finset (ZMod p))) = ({0} : Finset (ZMod p)) ∪ {δ} := by
        rw [Finset.insert_eq]
      rw [hins, Finset.add_union, h0]
    have hX02 : X + ({0, δ} : Finset (ZMod p)) = X := by
      rw [hsplit, ← heq, Finset.union_self]
    have hprime : Nat.Prime p := Fact.out
    have hcd := ZMod.cauchy_davenport hprime hne hne02
    rw [h02] at hcd
    rw [hX02] at hcd
    have hX1 : 1 ≤ X.card := Finset.card_pos.mpr hne
    have hX2 : X.card + 2 - 1 = X.card + 1 := by omega
    rw [hX2] at hcd
    have hple : p ≤ X.card := by
      by_contra hc
      push Not at hc
      have hmin : min p (X.card + 1) = X.card + 1 := Nat.min_eq_right (by omega)
      omega
    have hcardp : X.card = p := by
      have h1 : X.card ≤ p := by
        calc X.card ≤ Finset.univ.card := Finset.card_le_univ X
        _ = Fintype.card (ZMod p) := Finset.card_univ
        _ = p := ZMod.card p
      omega
    have hF : Fintype.card (ZMod p) = X.card := by rw [ZMod.card p, hcardp]
    exact Finset.eq_univ_of_card X hF.symm

/-- The finset image `a + range` coerces to the set-builder description
used by `Set.IsAPOfLengthWith`. -/
private theorem ap_image_key {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (S : Finset G) (a d : G) :
    ((Finset.image (fun i : ℕ => a + i • d) (Finset.range S.card) : Finset G) :
      Set G) = {a + n • d | (n : ℕ) (_ : n < (S.card : ℕ∞))} := by
  ext x
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by exact_mod_cast hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by exact_mod_cast hn, rfl⟩

/-- An image equality yields the set-level progression. -/
private theorem isAPOfLengthWith_of_image_eq {G : Type*} [AddCommMonoid G]
    [DecidableEq G] (S : Finset G) (a d : G)
    (h : S = Finset.image (fun i : ℕ => a + i • d) (Finset.range S.card)) :
    (S : Set G).IsAPOfLengthWith S.card a d := by
  refine ⟨by rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard], ?_⟩
  conv_lhs => rw [h]
  exact ap_image_key S a d

/-- The set-level progression yields an image equality. -/
private theorem image_eq_of_isAPOfLengthWith {G : Type*} [AddCommMonoid G]
    [DecidableEq G] (S : Finset G) (a d : G)
    (h : (S : Set G).IsAPOfLengthWith S.card a d) :
    S = Finset.image (fun i : ℕ => a + i • d) (Finset.range S.card) := by
  obtain ⟨_, hset⟩ := h
  refine Finset.coe_inj.mp ?_
  rw [hset]
  exact (ap_image_key S a d).symm

private theorem zmod_exists_nsmul_eq {p : ℕ} [Fact (Nat.Prime p)]
    (d : ZMod p) (hd : d ≠ 0) (z : ZMod p) : ∃ m : ℕ, m < p ∧ m • d = z := by
  have : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine ⟨(z * d⁻¹).val, ZMod.val_lt _, ?_⟩
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  field_simp

private theorem zmod_ap_of_sdiff_add_singleton_eq_singleton {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) (hne : A ≠ Finset.univ)
    (d : ZMod p) (hd : d ≠ 0) (a : ZMod p)
    (hsingle : A \ (A + {d}) = {a}) :
    A = Finset.image (fun i : ℕ => a + i • d) (Finset.range A.card) := by
  open scoped Pointwise in
  have ha_mem : a ∈ A \ (A + {d}) := by
    rw [hsingle]; exact Finset.mem_singleton_self a
  have haA : a ∈ A := (Finset.mem_sdiff.mp ha_mem).left
  -- (1) some translate of a by nsmul falls outside A
  have hex : ∃ y, y ∉ A := by
    have hss : A ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ A, hne⟩
    obtain ⟨y, _, hy⟩ := Finset.exists_of_ssubset hss
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hex
  obtain ⟨m, hmp, hmeq⟩ := zmod_exists_nsmul_eq d hd (y - a)
  have hmem_out : a + m • d ∉ A := by
    have hzm : a + m • d = y := by rw [hmeq, add_sub_cancel]
    rwa [hzm]
  have hfound : ∃ j, a + j • d ∉ A := ⟨m, hmem_out⟩
  set j := Nat.find hfound with hjdef
  have hjspec : a + j • d ∉ A := by rw [hjdef]; exact Nat.find_spec hfound
  have hjmin : ∀ i : ℕ, i < j → a + i • d ∈ A := by
    intro i hi
    by_contra hc
    exact Nat.find_min hfound (by omega) hc
  have ha0 : a + 0 • d ∈ A := by rw [zero_nsmul, add_zero]; exact haA
  have hj1 : 1 ≤ j := by
    by_contra hc
    push Not at hc
    have hj0 : j = 0 := by omega
    rw [hj0] at hjspec
    exact hjspec ha0
  -- (2) R ⊆ A, leftover W ⊆ W + {d}
  set R := Finset.image (fun i : ℕ => a + i • d) (Finset.range j) with hRdef
  have hRA : R ⊆ A := by
    rw [hRdef]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hi
    exact hjmin i hi
  set W := A \ R with hWdef
  have haR : a ∈ R := by
    rw [hRdef, Finset.mem_image]
    exact ⟨0, Finset.mem_range.mpr hj1, by rw [zero_nsmul, add_zero]⟩
  have hWsub : W ⊆ W + {d} := by
    intro x hx
    have hxA : x ∈ A := (Finset.mem_sdiff.mp (hWdef ▸ hx)).left
    have hxR : x ∉ R := (Finset.mem_sdiff.mp (hWdef ▸ hx)).right
    have hxAd : x ∈ A + {d} := by
      by_contra hc
      have hxmem : x ∈ A \ (A + {d}) := Finset.mem_sdiff.mpr ⟨hxA, hc⟩
      rw [hsingle, Finset.mem_singleton] at hxmem
      exact hxR (hxmem ▸ haR)
    rw [Finset.mem_add] at hxAd
    obtain ⟨u, hu, v, hv, huv⟩ := hxAd
    have hvd : v = d := Finset.mem_singleton.mp hv
    have huW : u ∈ W := by
      have huW' : u ∈ A \ R := by
        refine Finset.mem_sdiff.mpr ⟨hu, ?_⟩
        intro huR
        rw [hRdef, Finset.mem_image] at huR
        obtain ⟨i, hi, hii⟩ := huR
        rw [Finset.mem_range] at hi
        have hxeq : x = a + (i + 1) • d := by
          have e : (a + i • d) + d = a + (i + 1) • d := by
            rw [succ_nsmul, ← add_assoc]
          rw [← huv, ← hii, hvd, e]
        by_cases hi2 : i + 1 < j
        · have hxin : x ∈ R := by
            rw [hRdef, Finset.mem_image]
            exact ⟨i + 1, Finset.mem_range.mpr hi2, hxeq.symm⟩
          exact hxR hxin
        · have hij : i + 1 = j := by omega
          rw [hij] at hxeq
          exact hjspec (hxeq ▸ hxA)
      exact hWdef.symm ▸ huW'
    rw [Finset.mem_add]
    exact ⟨u, huW, d, Finset.mem_singleton_self d, by rw [hvd] at huv; exact huv⟩
  have hWtriv : W = ∅ ∨ W = Finset.univ :=
    zmod_eq_empty_or_univ_of_subset_add_singleton W d hd hWsub
  have hWA : W ⊆ A := hWdef ▸ Finset.sdiff_subset
  have hAR : A = R := by
    rcases hWtriv with h | h
    · have hsub2 : A ⊆ R := by
        intro x hxA
        by_contra hc
        have hmemW : x ∈ W := by
          rw [hWdef]; exact Finset.mem_sdiff.mpr ⟨hxA, hc⟩
        rw [h] at hmemW
        exact Finset.notMem_empty x hmemW
      exact Finset.Subset.antisymm hsub2 hRA
    · exfalso
      rw [h] at hWA
      have huniv : A = Finset.univ := Finset.eq_univ_iff_forall.mpr
        (fun x => hWA (Finset.mem_univ x))
      exact hne huniv
  -- (3) j ≤ p
  have hjp : j ≤ p := by
    by_contra hc
    have huniv : A = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro z
      obtain ⟨mm, hmmp, hmmeq⟩ := zmod_exists_nsmul_eq d hd (z - a)
      have hmj : mm < j := by omega
      have hzm : a + mm • d = z := by rw [hmmeq, add_sub_cancel]
      rw [hAR, hRdef, Finset.mem_image]
      exact ⟨mm, Finset.mem_range.mpr hmj, hzm⟩
    exact hne huniv
  -- (4) injectivity on range j, card, rewrite
  have hinj : Set.InjOn (fun i : ℕ => a + i • d) ↑(Finset.range j) := by
    intro i₁ hi₁ i₂ hi₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hi₁ hi₂
    change a + i₁ • d = a + i₂ • d at heq
    have e1 : i₁ • d = i₂ • d := add_left_cancel_iff.mp heq
    rw [nsmul_eq_mul, nsmul_eq_mul] at e1
    have e2 : (i₁ : ZMod p) = i₂ := mul_right_cancel₀ hd e1
    have e3 : i₁ % p = i₂ % p := (ZMod.natCast_eq_natCast_iff' i₁ i₂ p).mp e2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e3
    exact e3
  have hRcard : R.card = j := by
    rw [hRdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hAj : A.card = j := by rw [hAR]; exact hRcard
  rw [hAj]
  exact hAR
private theorem image_range_succ_nsmul_insert {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (b d : G) (m : ℕ) :
    Finset.image (fun i : ℕ => b + i • d) (Finset.range (m + 1))
      = insert (b + m • d) (Finset.image (fun i : ℕ => b + i • d) (Finset.range m)) := by
  rw [Finset.range_add_one, Finset.image_insert]

private theorem image_range_succ_nsmul_union {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (b d : G) (m : ℕ) (hm : 1 ≤ m) :
    Finset.image (fun i : ℕ => b + i • d) (Finset.range (m + 1))
      = Finset.image (fun i : ℕ => b + i • d) (Finset.range m) ∪
        (Finset.image (fun i : ℕ => b + i • d) (Finset.range m) + {d}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hi
    by_cases hi2 : i < m
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi2, hix⟩
    · have him : i = m := by omega
      rw [him] at hix
      subst hix
      apply Finset.mem_union_right
      have hm1 : m = (m - 1) + 1 := by omega
      have hmem : b + (m - 1) • d
          ∈ Finset.image (fun i : ℕ => b + i • d) (Finset.range m) :=
        Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), rfl⟩
      have hzd : d ∈ ({d} : Finset G) := Finset.mem_singleton_self d
      have heq : (b + (m - 1) • d) + d = b + m • d := by
        conv_rhs => rw [hm1, succ_nsmul]
        rw [add_assoc]
      rw [Finset.mem_add]
      exact ⟨b + (m - 1) • d, hmem, d, hzd, heq⟩
  · intro hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_range] at hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hix⟩
    · obtain ⟨y, hy, z, hz, hyz⟩ := Finset.mem_add.mp hx
      obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_singleton] at hz
      rw [Finset.mem_range] at hi
      subst hz
      subst hiy
      rw [← hyz] at *
      exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), by
        rw [succ_nsmul, add_assoc]⟩

private theorem zmod_exists_sdiff_add_singleton_eq_singleton {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) (hA : A.Nonempty) (hne : A ≠ Finset.univ)
    (d : ZMod p) (hd : d ≠ 0)
    (hle : (A ∪ (A + {d})).card ≤ A.card + 1) :
    ∃ a, A \ (A + {d}) = {a} := by
  have hAd : (A + {d}).card = A.card := Finset.card_add_singleton A d
  have hU := Finset.card_sdiff_add_card A (A + {d})
  have hle1 : (A \ (A + {d})).card ≤ 1 := by omega
  have hne2 : A \ (A + {d}) ≠ ∅ := by
    intro hempty
    have hsub : A ⊆ A + {d} := Finset.sdiff_eq_empty_iff_subset.mp hempty
    rcases zmod_eq_empty_or_univ_of_subset_add_singleton A d hd hsub with h | h
    · exact (Finset.nonempty_iff_ne_empty.mp hA) h
    · exact hne h
  have hpos : 0 < (A \ (A + {d})).card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne2)
  have h1 : (A \ (A + {d})).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  exact ⟨a, ha⟩

private theorem zmod_ap_of_critical_with_ap {p : ℕ} [Fact (Nat.Prime p)]
    (A B : Finset (ZMod p)) (hA : A.Nonempty)
    (d b : ZMod p) (hbB : B = Finset.image (fun i : ℕ => b + i • d) (Finset.range B.card))
    (hB2 : 2 ≤ B.card)
    (hcrit : (A + B).card = A.card + B.card - 1)
    (hlt : (A + B).card < p) :
    ∃ a, ((A : Set (ZMod p)).IsAPOfLengthWith A.card a d) := by
  have hprime : Nat.Prime p := Fact.out
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  -- d ≠ 0
  have hd0 : d ≠ 0 := by
    intro hdz
    have hsub : B ⊆ {b} := by
      intro x hx
      rw [hbB, Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [hdz, nsmul_zero, add_zero]
      exact Finset.mem_singleton_self b
    have hle : B.card ≤ 1 := by
      calc B.card ≤ ({b} : Finset (ZMod p)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton b
    omega
  -- write B.card = m + 1
  obtain ⟨m, hm⟩ : ∃ m, B.card = m + 1 := ⟨B.card - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hB' : B = Finset.image (fun i : ℕ => b + i • d) (Finset.range (m + 1)) := by
    rw [hm] at hbB
    exact hbB
  set P := Finset.image (fun i : ℕ => b + i • d) (Finset.range m) with hPdef
  have hBpu : B = P ∪ (P + {d}) := by
    rw [hB', image_range_succ_nsmul_union b d m hm1, ← hPdef]
  have hPins : Finset.image (fun i : ℕ => b + i • d) (Finset.range (m + 1))
      = insert (b + m • d) P := by
    rw [image_range_succ_nsmul_insert, ← hPdef]
  have hPm : m ≤ P.card := by
    have hle : (Finset.image (fun i : ℕ => b + i • d) (Finset.range (m + 1))).card
        ≤ P.card + 1 := by
      rw [hPins]; exact Finset.card_insert_le _ _
    have hleB : B.card ≤ P.card + 1 := hB' ▸ hle
    omega
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hUne : (A ∪ (A + {d})).Nonempty :=
    Finset.card_pos.mp (by
      have : A.card ≤ (A ∪ (A + {d})).card :=
        Finset.card_le_card Finset.subset_union_left
      omega)
  -- A + B = (A ∪ (A + {d})) + P
  have hsum : A + B = (A ∪ (A + {d})) + P := by
    rw [hBpu, Finset.add_union, Finset.union_add, add_assoc A ({d} : Finset (ZMod p)) P,
      add_comm P ({d} : Finset (ZMod p))]
  -- CD on (A ∪ (A+{d}), P), untruncated
  have hcd := ZMod.cauchy_davenport hprime hUne hPne
  have hQle : (A ∪ (A + {d})).card + P.card - 1 ≤ p := by
    by_contra hc
    push Not at hc
    have hminp : min p ((A ∪ (A + {d})).card + P.card - 1) = p :=
      min_eq_left (le_of_lt hc)
    rw [hminp, ← hsum] at hcd
    omega
  have hminU : min p ((A ∪ (A + {d})).card + P.card - 1)
      = (A ∪ (A + {d})).card + P.card - 1 := min_eq_right hQle
  rw [hminU, ← hsum] at hcd
  have hUle : (A ∪ (A + {d})).card ≤ A.card + 1 := by omega
  -- A ≠ univ
  obtain ⟨b', hb'⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  have hAsub : A + {b'} ⊆ A + B :=
    Finset.add_subset_add_left (Finset.singleton_subset_iff.mpr hb')
  have hAlt : A.card ≤ (A + B).card := by
    have h := Finset.card_le_card hAsub
    rwa [Finset.card_add_singleton] at h
  have hAne : A ≠ Finset.univ := by
    intro hcon
    have hcc : A.card = p := by rw [hcon, Finset.card_univ, ZMod.card]
    omega
  obtain ⟨a, ha⟩ := zmod_exists_sdiff_add_singleton_eq_singleton A hA hAne d hd0 hUle
  exact ⟨a, isAPOfLengthWith_of_image_eq A a d
    (zmod_ap_of_sdiff_add_singleton_eq_singleton A hAne d hd0 a ha)⟩

private theorem zmod_critical_dual {p : ℕ} [Fact (Nat.Prime p)]
    (X B : Finset (ZMod p)) (hX : X.Nonempty) (hB : B.Nonempty)
    (hcrit : (X + B).card = X.card + B.card - 1)
    (hlt : (X + B).card < p) :
    let C := -((X + B)ᶜ)
    C.card = p - (X + B).card ∧ (C + B).card = p - X.card ∧
      (C + B).card = C.card + B.card - 1 := by
  have hprime : Nat.Prime p := Fact.out
  have hX1 : 1 ≤ X.card := Finset.card_pos.mpr hX
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  -- card of C
  have hCcard : (-((X + B)ᶜ)).card = p - (X + B).card := by
    rw [Finset.card_neg, Finset.card_compl, ZMod.card]
  -- inclusion C + B ⊆ (-X)ᶜ
  have hsub : -((X + B)ᶜ) + B ⊆ (-X)ᶜ := by
    intro z hz
    rw [Finset.mem_compl]
    intro hcon
    rw [Finset.mem_add] at hz
    obtain ⟨c, hc, b, hb, rfl⟩ := hz
    rw [Finset.mem_neg] at hc hcon
    obtain ⟨y, hy, hyc⟩ := hc
    obtain ⟨x, hx, hxb⟩ := hcon
    rw [Finset.mem_compl] at hy
    apply hy
    have hyxb : y = x + b := by linear_combination hxb - hyc
    rw [hyxb]
    exact Finset.add_mem_add hx hb
  have hnegXcard : (-X).card = X.card := Finset.card_neg X
  have hcomplcard : (-X)ᶜ.card = p - X.card := by
    rw [Finset.card_compl, ZMod.card, hnegXcard]
  have hle : (-((X + B)ᶜ) + B).card ≤ p - X.card := by
    calc (-((X + B)ᶜ) + B).card ≤ (-X)ᶜ.card := Finset.card_le_card hsub
    _ = p - X.card := hcomplcard
  have hC1 : 1 ≤ (-((X + B)ᶜ)).card := by omega
  have hCne : (-((X + B)ᶜ)).Nonempty := Finset.card_pos.mp (by omega)
  have hcd := ZMod.cauchy_davenport hprime hCne hB
  have heq : (-((X + B)ᶜ)).card + B.card - 1 = p - X.card := by omega
  have hmin : min p ((-((X + B)ᶜ)).card + B.card - 1) = p - X.card := by
    rw [heq]; exact min_eq_right (Nat.sub_le p X.card)
  rw [hmin] at hcd
  refine ⟨hCcard, by omega, by omega⟩

private theorem zmod_critical_inter_add_singleton {p : ℕ} [Fact (Nat.Prime p)]
    (X B : Finset (ZMod p)) (hB : B.Nonempty)
    (hcrit : (X + B).card = X.card + B.card - 1)
    (δ : ZMod p) (hY : (X ∩ (X + {δ})).Nonempty)
    (huntr : (X ∪ (X + {δ})).card + B.card - 1 ≤ p) :
    (X ∩ (X + {δ}) + B).card = (X ∩ (X + {δ})).card + B.card - 1 := by
  have hprime : Nat.Prime p := Fact.out
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hYX : X ∩ (X + {δ}) ⊆ X := Finset.inter_subset_left
  have hXne : X.Nonempty := hY.mono hYX
  have hX1 : 1 ≤ X.card := Finset.card_pos.mpr hXne
  have hY1 : 1 ≤ (X ∩ (X + {δ})).card := Finset.card_pos.mpr hY
  have hU1 : 1 ≤ (X ∪ (X + {δ})).card := by
    have : X.card ≤ (X ∪ (X + {δ})).card :=
      Finset.card_le_card Finset.subset_union_left
    omega
  have hUne : (X ∪ (X + {δ})).Nonempty := Finset.card_pos.mp (by omega)
  have hXd : (X + {δ}).card = X.card := Finset.card_add_singleton X δ
  -- union-add and inter-add facts
  have hUadd : X ∪ (X + {δ}) + B = (X + B) ∪ ((X + {δ}) + B) := Finset.union_add
  have hYadd : X ∩ (X + {δ}) + B ⊆ (X + B) ∩ ((X + {δ}) + B) :=
    Finset.inter_add_subset
  -- shifted sumset has same card
  have hshift : ((X + {δ}) + B).card = (X + B).card := by
    have hcomm : (X + {δ}) + B = (X + B) + {δ} := add_right_comm X {δ} B
    rw [hcomm, Finset.card_add_singleton]
  -- card equations
  have hunion_inter : ((X + B) ∪ ((X + {δ}) + B)).card + ((X + B) ∩ ((X + {δ}) + B)).card
      = (X + B).card + ((X + {δ}) + B).card :=
    Finset.card_union_add_card_inter _ _
  have hXY : (X ∪ (X + {δ})).card + (X ∩ (X + {δ})).card = X.card + X.card := by
    have h := Finset.card_union_add_card_inter X (X + {δ})
    omega
  -- CD for U (untruncated by hypothesis)
  have hcdU := ZMod.cauchy_davenport hprime hUne hB
  have hminU : min p ((X ∪ (X + {δ})).card + B.card - 1)
      = (X ∪ (X + {δ})).card + B.card - 1 := min_eq_right huntr
  rw [hminU, hUadd] at hcdU
  -- CD for Y (untruncated since Y.card ≤ X.card and S ≤ p)
  have hYleX : (X ∩ (X + {δ})).card ≤ X.card := Finset.card_le_card hYX
  have hSlep : (X + B).card ≤ p := by
    calc (X + B).card ≤ Finset.univ.card := Finset.card_le_univ _
    _ = Fintype.card (ZMod p) := Finset.card_univ
    _ = p := ZMod.card p
  have hcdY := ZMod.cauchy_davenport hprime hY hB
  have hminY : min p ((X ∩ (X + {δ})).card + B.card - 1)
      = (X ∩ (X + {δ})).card + B.card - 1 := by
    apply min_eq_right
    omega
  rw [hminY] at hcdY
  have hle : (X ∩ (X + {δ}) + B).card ≤ ((X + B) ∩ ((X + {δ}) + B)).card :=
    Finset.card_le_card hYadd
  omega

private theorem zmod_inter_add_singleton_card_le_one_of_min_witness {p : ℕ} [Fact (Nat.Prime p)]
    (B X : Finset (ZMod p)) (hB2 : 2 ≤ B.card) (hX2 : 2 ≤ X.card)
    (hcrit : (X + B).card = X.card + B.card - 1)
    (hle : (X + B).card ≤ p - 2)
    (hmin : ∀ Y : Finset (ZMod p), 2 ≤ Y.card → (Y + B).card = Y.card + B.card - 1 →
      (Y + B).card ≤ p - 2 → X.card ≤ Y.card)
    (δ : ZMod p) (hd : δ ≠ 0) :
    (X ∩ (X + {δ})).card ≤ 1 := by
  by_contra hc
  push Not at hc
  have hY2 : 2 ≤ (X ∩ (X + {δ})).card := by omega
  have hY1 : 1 ≤ (X ∩ (X + {δ})).card := by omega
  have hX1 : 1 ≤ X.card := by omega
  have hB1 : 1 ≤ B.card := by omega
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  have hYne : (X ∩ (X + {δ})).Nonempty := Finset.card_pos.mp (by omega)
  have hSlep : (X + B).card ≤ p := by
    calc (X + B).card ≤ Finset.univ.card := Finset.card_le_univ _
    _ = Fintype.card (ZMod p) := Finset.card_univ
    _ = p := ZMod.card p
  have hXp : X.card ≤ p := by
    calc X.card ≤ Finset.univ.card := Finset.card_le_univ _
    _ = Fintype.card (ZMod p) := Finset.card_univ
    _ = p := ZMod.card p
  have hlt : (X + B).card < p := by omega
  have hN3 : (-((X + B)ᶜ)).card = p - (X + B).card ∧
      ((-((X + B)ᶜ)) + B).card = p - X.card ∧
      ((-((X + B)ᶜ)) + B).card = (-((X + B)ᶜ)).card + B.card - 1 :=
    zmod_critical_dual X B hXne hBne hcrit hlt
  obtain ⟨hCcard, hCB, hCBcrit⟩ := hN3
  have hC2 : 2 ≤ (-((X + B)ᶜ)).card := by omega
  have hCBle : ((-((X + B)ᶜ)) + B).card ≤ p - 2 := by omega
  have hXC : X.card ≤ (-((X + B)ᶜ)).card := hmin _ hC2 hCBcrit hCBle
  have hUY : (X ∪ (X + {δ})).card + (X ∩ (X + {δ})).card = X.card + X.card := by
    have h := Finset.card_union_add_card_inter X (X + {δ})
    have hXd : (X + {δ}).card = X.card := Finset.card_add_singleton X δ
    omega
  have huntr : (X ∪ (X + {δ})).card + B.card - 1 ≤ p := by omega
  have hN4 := zmod_critical_inter_add_singleton X B hBne hcrit δ hYne huntr
  have hYBle : (X ∩ (X + {δ}) + B).card ≤ (X + B).card :=
    Finset.card_le_card (Finset.add_subset_add_right Finset.inter_subset_left)
  have hYBle2 : (X ∩ (X + {δ}) + B).card ≤ p - 2 := by omega
  have hXY : X.card ≤ (X ∩ (X + {δ})).card := hmin _ hY2 hN4 hYBle2
  have hYXeq : X ∩ (X + {δ}) = X :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left hXY
  have hXsub : X ⊆ X + {δ} := by
    have h : X ∩ (X + {δ}) ⊆ X + {δ} := Finset.inter_subset_right
    rwa [hYXeq] at h
  rcases zmod_eq_empty_or_univ_of_subset_add_singleton X δ hd hXsub with h | h
  · rw [h, Finset.card_empty] at hX2
    omega
  · have hXcard : X.card = p := by rw [h, Finset.card_univ, ZMod.card]
    omega

private theorem three_mul_card_le_card_add_of_inter_add_singleton_le_one
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X B : Finset G)
    (hSidon : ∀ δ : G, δ ≠ 0 → (X ∩ (X + {δ})).card ≤ 1)
    (b₁ b₂ b₃ : G) (h1 : b₁ ∈ B) (h2 : b₂ ∈ B) (h3 : b₃ ∈ B)
    (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃) :
    3 * X.card ≤ (X + B).card + 3 := by
  have htrans : ∀ u v : G, (X + {u}) ∩ (X + {v}) = (X ∩ (X + {v - u})) + {u} := by
    intro u v
    ext z
    constructor
    · intro hz
      rw [Finset.mem_inter] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Finset.mem_add] at hz1 hz2
      obtain ⟨x1, hx1, w1, hw1, h1⟩ := hz1
      obtain ⟨x2, hx2, w2, hw2, h2⟩ := hz2
      have eu : w1 = u := Finset.mem_singleton.mp hw1
      have ev : w2 = v := Finset.mem_singleton.mp hw2
      have key : x2 + (w2 - w1) = x1 := by
        have e1 : x2 + (w2 - w1) = (x2 + w2) - w1 := by abel
        rw [e1, h2, ← h1]
        exact add_sub_cancel_right x1 w1
      have hmem3 : w2 - w1 ∈ ({v - u} : Finset G) := by
        rw [Finset.mem_singleton, eu, ev]
      rw [Finset.mem_add]
      exact ⟨x1, Finset.mem_inter.mpr ⟨hx1, Finset.mem_add.mpr
        ⟨x2, hx2, w2 - w1, hmem3, key⟩⟩, w1, hw1, h1⟩
    · intro hz
      rw [Finset.mem_add] at hz
      obtain ⟨w, hw, w4, hw4, hwu⟩ := hz
      rw [Finset.mem_inter] at hw
      obtain ⟨hwX, hw2⟩ := hw
      rw [Finset.mem_add] at hw2
      obtain ⟨x2, hx2, w3, hw3, hw⟩ := hw2
      have eu : w4 = u := Finset.mem_singleton.mp hw4
      have evu : w3 = v - u := Finset.mem_singleton.mp hw3
      have hmemV : w3 + w4 ∈ ({v} : Finset G) := by
        rw [Finset.mem_singleton, evu, eu, sub_add_cancel]
      rw [Finset.mem_inter]
      refine ⟨Finset.mem_add.mpr ⟨w, hwX, w4, hw4, hwu⟩, ?_⟩
      rw [Finset.mem_add]
      have key2 : x2 + (w3 + w4) = z := by
        have e2 : x2 + (w3 + w4) = (x2 + w3) + w4 := by abel
        rw [e2, hw, hwu]
      exact ⟨x2, hx2, w3 + w4, hmemV, key2⟩
  -- pairwise intersection cards ≤ 1
  have hp12 : ((X + {b₁}) ∩ (X + {b₂})).card ≤ 1 := by
    rw [htrans b₁ b₂, Finset.card_add_singleton]
    exact hSidon _ (sub_ne_zero.mpr (Ne.symm h12))
  have hp13 : ((X + {b₁}) ∩ (X + {b₃})).card ≤ 1 := by
    rw [htrans b₁ b₃, Finset.card_add_singleton]
    exact hSidon _ (sub_ne_zero.mpr (Ne.symm h13))
  have hp23 : ((X + {b₂}) ∩ (X + {b₃})).card ≤ 1 := by
    rw [htrans b₂ b₃, Finset.card_add_singleton]
    exact hSidon _ (sub_ne_zero.mpr (Ne.symm h23))
  have hc1 : (X + {b₁}).card = X.card := Finset.card_add_singleton X b₁
  have hc2 : (X + {b₂}).card = X.card := Finset.card_add_singleton X b₂
  have hc3 : (X + {b₃}).card = X.card := Finset.card_add_singleton X b₃
  have hs1 : X + {b₁} ⊆ X + B :=
    Finset.add_subset_add_left (Finset.singleton_subset_iff.mpr h1)
  have hs2 : X + {b₂} ⊆ X + B :=
    Finset.add_subset_add_left (Finset.singleton_subset_iff.mpr h2)
  have hs3 : X + {b₃} ⊆ X + B :=
    Finset.add_subset_add_left (Finset.singleton_subset_iff.mpr h3)
  have hunion12 := Finset.card_union_add_card_inter (X + {b₁}) (X + {b₂})
  have hunion123 := Finset.card_union_add_card_inter (X + {b₁} ∪ (X + {b₂})) (X + {b₃})
  have hdistrib := Finset.union_inter_distrib_right (X + {b₁}) (X + {b₂}) (X + {b₃})
  have hcap_le : ((X + {b₁} ∪ (X + {b₂})) ∩ (X + {b₃})).card
      ≤ ((X + {b₁}) ∩ (X + {b₃})).card + ((X + {b₂}) ∩ (X + {b₃})).card := by
    rw [hdistrib]
    exact Finset.card_union_le _ _
  have hsub123 : (X + {b₁} ∪ (X + {b₂})) ∪ (X + {b₃}) ⊆ X + B :=
    Finset.union_subset (Finset.union_subset hs1 hs2) hs3
  have hle : ((X + {b₁} ∪ (X + {b₂})) ∪ (X + {b₃})).card ≤ (X + B).card :=
    Finset.card_le_card hsub123
  omega

private theorem zmod_vosper_ap_of_witness {p : ℕ} [Fact (Nat.Prime p)]
    (B : Finset (ZMod p)) (hB2 : 2 ≤ B.card)
    (wit : ∃ X, 2 ≤ X.card ∧ (X + B).card = X.card + B.card - 1 ∧ (X + B).card ≤ p - 2) :
    ∃ d a, ((B : Set (ZMod p)).IsAPOfLengthWith B.card a d) := by
  have key : ∀ n : ℕ, ∀ Bo : Finset (ZMod p), Bo.card ≤ n → 2 ≤ Bo.card →
      (∃ X, 2 ≤ X.card ∧ (X + Bo).card = X.card + Bo.card - 1 ∧ (X + Bo).card ≤ p - 2) →
      ∃ d a, ((Bo : Set (ZMod p)).IsAPOfLengthWith Bo.card a d) := by
    intro n
    induction n with
    | zero =>
      intro Bo hle hBo2 _
      exact absurd hle (by omega)
    | succ n ih =>
      intro Bo hBle hBo2 witB
      obtain ⟨X, hX2, hXcrit, hXle⟩ := witB
      by_cases hBo3 : 3 ≤ Bo.card
      · -- hard case: minimal witness
        have hSne : (Finset.univ.filter (fun Y : Finset (ZMod p) =>
            2 ≤ Y.card ∧ (Y + Bo).card = Y.card + Bo.card - 1 ∧
              (Y + Bo).card ≤ p - 2)).Nonempty :=
          ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ X, hX2, hXcrit, hXle⟩⟩
        obtain ⟨X0, hX0mem, hX0min⟩ :=
          Finset.exists_min_image _ (fun Y => Y.card) hSne
        rw [Finset.mem_filter] at hX0mem
        obtain ⟨_, hX02, hX0crit, hX0le⟩ := hX0mem
        have hmin : ∀ Y : Finset (ZMod p), 2 ≤ Y.card →
            (Y + Bo).card = Y.card + Bo.card - 1 → (Y + Bo).card ≤ p - 2 →
            X0.card ≤ Y.card := by
          intro Y h1 h2 h3
          have hYmem : Y ∈ Finset.univ.filter (fun Y : Finset (ZMod p) =>
              2 ≤ Y.card ∧ (Y + Bo).card = Y.card + Bo.card - 1 ∧
                (Y + Bo).card ≤ p - 2) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ Y, h1, h2, h3⟩
          exact hX0min Y hYmem
        by_cases hltXB : X0.card < Bo.card
        · have hBo1 : 1 ≤ Bo.card := by omega
          have hBone : Bo.Nonempty := Finset.card_pos.mp (by omega)
          have hX0ne : X0.Nonempty := Finset.card_pos.mp (by omega)
          have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
          have hBX0crit : (Bo + X0).card = Bo.card + X0.card - 1 := by
            rw [add_comm Bo X0, hX0crit, add_comm X0.card Bo.card]
          have hBX0le : (Bo + X0).card ≤ p - 2 := by
            rw [add_comm Bo X0]; exact hX0le
          have hX0len : X0.card ≤ n := by omega
          obtain ⟨d, a, haX0⟩ := ih X0 hX0len hX02 ⟨Bo, hBo2, hBX0crit, hBX0le⟩
          have hltp : (Bo + X0).card < p := by omega
          obtain ⟨a', ha'⟩ :=
            zmod_ap_of_critical_with_ap Bo X0 hBone d a
              (image_eq_of_isAPOfLengthWith X0 a d haX0) hX02 hBX0crit hltp
          exact ⟨d, a', ha'⟩
        · have hXB : Bo.card ≤ X0.card := by omega
          have hSidon : ∀ δ : ZMod p, δ ≠ 0 → (X0 ∩ (X0 + {δ})).card ≤ 1 := by
            intro δ hd
            exact zmod_inter_add_singleton_card_le_one_of_min_witness
              Bo X0 hBo2 hX02 hX0crit hX0le hmin δ hd
          obtain ⟨b₁, b₂, b₃, m1, m2, m3, ne12, ne13, ne23⟩ :=
            Finset.two_lt_card_iff.mp (by omega : 2 < Bo.card)
          have hN10 := three_mul_card_le_card_add_of_inter_add_singleton_le_one
            X0 Bo hSidon b₁ b₂ b₃ m1 m2 m3 ne12 ne13 ne23
          have hX01 : 1 ≤ X0.card := by omega
          omega
      · -- base case: Bo.card = 2
        have hcase : Bo.card = 2 := by omega
        obtain ⟨x, y, _, hBxy⟩ := Finset.card_eq_two.mp hcase
        have himg : Finset.image (fun i : ℕ => x + i • (y - x)) (Finset.range 2)
            = {x, y} := by
          have hr2 : Finset.range 2 = {0, 1} := by
            ext i
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
            omega
          rw [hr2, Finset.image_insert, Finset.image_singleton]
          simp [add_zero, add_sub_cancel]
        have heq : Bo = Finset.image (fun i : ℕ => x + i • (y - x))
            (Finset.range Bo.card) := by
          rw [hcase, hBxy]
          exact himg.symm
        exact ⟨y - x, x, isAPOfLengthWith_of_image_eq Bo x (y - x) heq⟩
  exact key B.card B le_rfl hB2 wit

private theorem vosper_mpr_of_min {p : ℕ} [Fact (Nat.Prime p)]
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : min A.card B.card = 1) : (A + B).card = A.card + B.card - 1 := by
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hor : A.card = 1 ∨ B.card = 1 := by omega
  rcases hor with h1 | h1
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    rw [ha, Finset.card_singleton_add, Finset.card_singleton]
    omega
  · obtain ⟨bb, hb⟩ := Finset.card_eq_one.mp h1
    rw [hb, Finset.card_add_singleton, Finset.card_singleton]
    omega

private theorem vosper_mpr_of_compl {p : ℕ} [Fact (Nat.Prime p)]
    (A B : Finset (ZMod p)) (hA : A.Nonempty)
    (h : (A + B).card = p - 1 ∧ ∃ c : ZMod p,
      Finset.filter (fun x => x ∉ (A + B)) Finset.univ = {c} ∧
        B = Finset.filter
          (fun x => x ∉ Finset.image (fun a => c - a) A) Finset.univ) :
    (A + B).card = A.card + B.card - 1 := by
  obtain ⟨hABp, c, _, hBf⟩ := h
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hAp : A.card ≤ p := by
    calc A.card ≤ Finset.univ.card := Finset.card_le_univ _
    _ = Fintype.card (ZMod p) := Finset.card_univ
    _ = p := ZMod.card p
  have hinj : Function.Injective (fun a : ZMod p => c - a) := by
    simpa [sub_eq_add_neg, Function.comp_def] using
      (add_right_injective c).comp neg_injective
  have hcompl : Finset.filter (fun x => x ∉ Finset.image (fun a => c - a) A)
      Finset.univ = (Finset.image (fun a : ZMod p => c - a) A)ᶜ := by
    ext x
    simp
  have hBcard : B.card = p - A.card := by
    rw [hBf, hcompl, Finset.card_compl, ZMod.card,
      Finset.card_image_of_injective _ hinj]
  omega

private theorem vosper_mpr_of_ap {p : ℕ} [Fact (Nat.Prime p)]
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : A + B ≠ Finset.univ)
    (d a b : ZMod p)
    (hdA : (A : Set (ZMod p)).IsAPOfLengthWith A.card a d)
    (hdB : (B : Set (ZMod p)).IsAPOfLengthWith B.card b d) :
    (A + B).card = A.card + B.card - 1 := by
  have hAa : A = Finset.image (fun i : ℕ => a + i • d) (Finset.range A.card) :=
    image_eq_of_isAPOfLengthWith A a d hdA
  have hBb : B = Finset.image (fun i : ℕ => b + i • d) (Finset.range B.card) :=
    image_eq_of_isAPOfLengthWith B b d hdB
  have hprime : Nat.Prime p := Fact.out
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hlt : (A + B).card < p := by
    have hss : A + B ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hAB⟩
    have h := Finset.card_lt_card hss
    rwa [Finset.card_univ, ZMod.card] at h
  have hsub : A + B ⊆ Finset.image (fun k : ℕ => (a + b) + k • d)
      (Finset.range (A.card + B.card - 1)) := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    rw [hAa, Finset.mem_image] at hx
    rw [hBb, Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Finset.mem_range] at hi hj
    rw [Finset.mem_image]
    refine ⟨i + j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [add_nsmul]
    abel
  have hle : (A + B).card ≤ A.card + B.card - 1 := by
    calc (A + B).card
        ≤ (Finset.image (fun k : ℕ => (a + b) + k • d)
          (Finset.range (A.card + B.card - 1))).card := Finset.card_le_card hsub
      _ ≤ (Finset.range (A.card + B.card - 1)).card := Finset.card_image_le
      _ = A.card + B.card - 1 := Finset.card_range _
  have hcd := ZMod.cauchy_davenport hprime hA hB
  have hQle : A.card + B.card - 1 ≤ p := by
    by_contra hc
    push Not at hc
    have hminp : min p (A.card + B.card - 1) = p := min_eq_left (le_of_lt hc)
    rw [hminp] at hcd
    omega
  rw [min_eq_right hQle] at hcd
  omega

private theorem vosper_mp_of_card_eq_pred {p : ℕ} [Fact (Nat.Prime p)]
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (_hB : B.Nonempty)
    (hcrit : (A + B).card = A.card + B.card - 1)
    (hABp : (A + B).card = p - 1) :
    ∃ c : ZMod p, Finset.filter (fun x => x ∉ (A + B)) Finset.univ = {c} ∧
      B = Finset.filter
        (fun x => x ∉ Finset.image (fun a => c - a) A) Finset.univ := by
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hAp : A.card ≤ p := by
    calc A.card ≤ Finset.univ.card := Finset.card_le_univ _
    _ = Fintype.card (ZMod p) := Finset.card_univ
    _ = p := ZMod.card p
  have hcompl : ∀ S : Finset (ZMod p),
      Finset.filter (fun x => x ∉ S) Finset.univ = Sᶜ := by
    intro S
    ext x
    simp
  have hCc : ((A + B)ᶜ).card = 1 := by
    rw [Finset.card_compl, ZMod.card, hABp]
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hCc
  refine ⟨c, by rw [hcompl (A + B), hc], ?_⟩
  have hinj : Function.Injective (fun a : ZMod p => c - a) := by
    simpa [sub_eq_add_neg, Function.comp_def] using
      (add_right_injective c).comp neg_injective
  have hBsub : B ⊆ (Finset.image (fun a : ZMod p => c - a) A)ᶜ := by
    intro x hxB
    rw [Finset.mem_compl]
    intro hcon
    rw [Finset.mem_image] at hcon
    obtain ⟨a, haA, hac⟩ := hcon
    have hca : c = a + x := by rw [← hac]; abel
    have hcAB : c ∈ A + B := hca ▸ Finset.add_mem_add haA hxB
    have hcC : c ∈ (A + B)ᶜ := by rw [hc]; exact Finset.mem_singleton_self c
    exact (Finset.mem_compl.mp hcC) hcAB
  have hEq : B.card = (Finset.image (fun a : ZMod p => c - a) A)ᶜ.card := by
    rw [Finset.card_compl, ZMod.card, Finset.card_image_of_injective _ hinj]
    omega
  rw [hcompl]
  exact Finset.eq_of_subset_of_card_le hBsub (le_of_eq hEq.symm)

/-- **Vosper's theorem.** Let $p$ be a prime and let $A$ and $B$ be nonempty subsets of
$\mathbb{Z}/p\mathbb{Z}$ whose sumset $A + B = \{a + b : a \in A, b \in B\}$ is not all of
$\mathbb{Z}/p\mathbb{Z}$. Then $|A + B| = |A| + |B| - 1$ if and only if one of the following
holds: (i) $\min(|A|, |B|) = 1$; (ii) $|A + B| = p - 1$ and there is an element
$c \in \mathbb{Z}/p\mathbb{Z}$ such that the complement of $A + B$ is $\{c\}$ and $B$ is the
complement of $c - A = \{c - a : a \in A\}$; or (iii) $A$ and $B$ are arithmetic progressions
with the same common difference, that is, there are $d, a_0, b_0 \in \mathbb{Z}/p\mathbb{Z}$
with $A = \{a_0 + n d : 0 \le n < |A|\}$ and $B = \{b_0 + n d : 0 \le n < |B|\}$.

Proves `Wanted` entry `vosper_eq_iff`.

Source: Fabián Arias, Jerson Borja, and Samuel Anaya, *Counting Integers
Representable as Sums of k-th Powers Modulo n*, Journal of Integer Sequences
26 (2023), Article 23.8.1, Theorem [Vosper] `theo_Vosper`, lines 256–267,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Borja/borja4.tex>.
-/
theorem vosper_eq_iff {p : ℕ} [Fact (Nat.Prime p)]
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : A + B ≠ Finset.univ) :
    (A + B).card = A.card + B.card - 1 ↔
      (min A.card B.card = 1 ∨
        ((A + B).card = p - 1 ∧
          ∃ c : ZMod p,
            Finset.filter (fun x => x ∉ (A + B)) Finset.univ = {c} ∧
              B = Finset.filter
                (fun x => x ∉ Finset.image (fun a => c - a) A) Finset.univ) ∨
        AreFiniteArithmeticProgressionsWithCommonDifference A B) := by
  have hprime : Nat.Prime p := Fact.out
  have hp2 : 2 ≤ p := hprime.two_le
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hlt : (A + B).card < p := by
    have hss : A + B ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hAB⟩
    have hcard := Finset.card_lt_card hss
    rwa [Finset.card_univ, ZMod.card] at hcard
  constructor
  · intro h
    by_cases hmin1 : min A.card B.card = 1
    · exact Or.inl hmin1
    · have hA2 : 2 ≤ A.card := by omega
      have hB2 : 2 ≤ B.card := by omega
      by_cases hABp : (A + B).card = p - 1
      · obtain ⟨c, hc1, hc2⟩ := vosper_mp_of_card_eq_pred A B hA hB h hABp
        exact Or.inr (Or.inl ⟨hABp, c, hc1, hc2⟩)
      · have hle : (A + B).card ≤ p - 2 := by omega
        obtain ⟨d, b, hbB⟩ := zmod_vosper_ap_of_witness B hB2 ⟨A, hA2, h, hle⟩
        obtain ⟨a0, ha0A⟩ :=
          zmod_ap_of_critical_with_ap A B hA d b
            (image_eq_of_isAPOfLengthWith B b d hbB) hB2 h hlt
        exact Or.inr (Or.inr ⟨d, a0, b, ha0A, hbB⟩)
  · rintro (hmin | ⟨hABp, c, hc1, hc2⟩ | hAP)
    · exact vosper_mpr_of_min A B hA hB hmin
    · exact vosper_mpr_of_compl A B hA ⟨hABp, c, hc1, hc2⟩
    · obtain ⟨d, a, b, hdA, hdB⟩ := hAP
      exact vosper_mpr_of_ap A B hA hB hAB d a b hdA hdB

end MetaMathlibExt
end
