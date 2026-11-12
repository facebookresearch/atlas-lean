/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 484

open Cardinal Ordinal Set Order

/-! ### Informal statement of `exists_isLUB_of_mk_lt_cof`

Let α be a well-order. Write cof(α) for its cofinality.

  1. A set t ⊆ α of size |,t,| < cof(α) is bounded, hence has a least upper bound.
  2. If s ⊆ α is cofinal of order type cof(α), then each s ∩ y : y < z is a
     proper initial segment of s, so it has size < cof(α).
  3. (Pressing-down lemma, bounded form.) If ℵ₀ < cof(α) and f : α → α is
     regressive on a stationary set S (i.e. f(x) < x for all x ∈ S), then for some b the set x ∈ S :
     f(x)
     < b is stationary.
  4. Final segments y : z ≤ y are club.
  5. Stationary sets are large: if S ⊆ α is stationary (and α has no maximum), then
     cof(α) ≤ |,S,|.
  6. If cof(α) ≠ ℵ₀, a stationary set stays stationary after intersecting with a club.
  7. If λ is a regular cardinal, the cofinality of the type of ordinals below λ is λ (lifted to
     the ambient universe).
  8. If λ is a regular cardinal, a set S of ordinals below λ with |,S,| < λ (lifted) is
     bounded below λ: sup S < λ.
  9. If λ is a regular cardinal, the ordinals below λ form a regular cardinal order.
-/

namespace MetaMathlibExt

-- Logic 484: Pressing down theorems

variable {α : Type*} [LinearOrder α] [WellFoundedLT α]

/-! ### Informal statement of `exists_isLUB_of_mk_lt_cof`

Let α be a well-order. Write cof(α) for its cofinality.

  1. A set t ⊆ α of size |,t,| < cof(α) is bounded, hence has a least upper bound.
  2. If s ⊆ α is cofinal of order type cof(α), then each s ∩ y : y < z is a
     proper initial segment of s, so it has size < cof(α).
  3. (Pressing-down lemma, bounded form.) If ℵ₀ < cof(α) and f : α → α is
     regressive on a stationary set S (i.e. f(x) < x for all x ∈ S), then for some b the set x ∈ S :
     f(x)
     < b is stationary.
  4. Final segments y : z ≤ y are club.
  5. Stationary sets are large: if S ⊆ α is stationary (and α has no maximum), then
     cof(α) ≤ |,S,|.
  6. If cof(α) ≠ ℵ₀, a stationary set stays stationary after intersecting with a club.
  7. If λ is a regular cardinal, the cofinality of the type of ordinals below λ is λ (lifted to
     the ambient universe).
  8. If λ is a regular cardinal, a set S of ordinals below λ with |,S,| < λ (lifted) is
     bounded below λ: sup S < λ.
  9. If λ is a regular cardinal, the ordinals below λ form a regular cardinal order.
-/

/-- Let α be a well-order. Write cof(α) for its cofinality.

The full informal statement is in the module documentation directly above.
-/
theorem exists_isLUB_of_mk_lt_cof {t : Set α} (hcof : #t < Order.cof α) :
    ∃ x, IsLUB t x := by
  have hnc : ¬ IsCofinal t := fun h => (cof_le h).not_gt hcof
  simp only [IsCofinal, not_forall, not_exists, not_and, not_le] at hnc
  obtain ⟨y, hy⟩ := hnc
  have hub : (upperBounds t).Nonempty := ⟨y, fun b hb => (hy b hb).le⟩
  have hwf := wellFounded_lt (α := α)
  exact ⟨hwf.min _ hub, hwf.min_mem _ hub, fun z hz => not_lt.1 (hwf.not_lt_min _ hz)⟩

theorem mk_inter_Iio_lt_cof {s : Set α} (hs : IsCofinal s) (hs' : typeLT s = (Order.cof α).ord)
    (z : α) : #(s ∩ Iio z : Set α) < Order.cof α := by
  obtain ⟨w, hw, hzw⟩ := hs z
  have h1 : #(s ∩ Iio z : Set α) ≤ #{y : s // y < ⟨w, hw⟩} :=
    mk_le_of_injective (f := fun b => ⟨⟨b.1, b.2.1⟩, Subtype.mk_lt_mk.2 (lt_of_lt_of_le b.2.2 hzw)⟩)
      fun b b' h => Subtype.ext (congrArg (fun y : {y : s // y < ⟨w, hw⟩} => y.1.1) h)
  have h2 : #{y : s // y < ⟨w, hw⟩} < Order.cof α := by
    rw [← card_typein (r := (· < ·)), ← lt_ord, ← hs']
    exact typein_lt_type _ _
  exact h1.trans_lt h2

theorem exists_stationary_lt_of_regressive (hα : ℵ₀ < Order.cof α) {S : Set α}
    (hS : IsStationary S) {f : α → α} (hf : ∀ x ∈ S, f x < x) :
    ∃ b, IsStationary {x ∈ S | f x < b} := by
  by_contra! hcon
  have hcon' : ∀ b, ∃ c, IsClub c ∧ {x ∈ S | f x < b} ∩ c = ∅ := fun b => by
    obtain ⟨t, ht, hd⟩ := not_isStationary_iff.1 (hcon b)
    exact ⟨t, ht, Set.disjoint_iff_inter_eq_empty.1 hd⟩
  choose C hC hCS using hcon'
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq α
  have hseg := mk_inter_Iio_lt_cof hs hs'
  have hcof0 : Order.cof α ≠ ℵ₀ := hα.ne'
  have : Nonempty α := cof_ne_zero_iff.1 (by intro h; rw [h] at hα; exact not_lt_zero hα)
  have : NoTopOrder α := one_lt_cof_iff.1 (one_lt_aleph0.trans hα)
  have : NoMaxOrder α := NoTopOrder.to_noMaxOrder α
  let D : Set α := {x | (∀ y < x, ∃ b ∈ s, y < b ∧ b < x) ∧ ∀ b ∈ s, b < x → x ∈ C b}
  have hD : IsClub D := by
    refine ⟨?_, ?_⟩
    · intro t ht ht0 _ x hx
      by_cases hxt : x ∈ t
      · exact ht hxt
      have hlim : ∀ y < x, ∃ z ∈ t, y < z ∧ z < x := fun y hy => by
        obtain ⟨z, hz, hyz⟩ : ∃ z ∈ t, y < z := by
          by_contra! h
          exact hy.not_ge (hx.2 fun z hz => h z hz)
        exact ⟨z, hz, hyz, lt_of_le_of_ne (hx.1 hz) (fun e => hxt (e ▸ hz))⟩
      refine ⟨fun y hy => ?_, fun b hb hbx => ?_⟩
      · obtain ⟨z, hz, hyz, hzx⟩ := hlim y hy
        obtain ⟨b, hb, hyb, hbz⟩ := (ht hz).1 y hyz
        exact ⟨b, hb, hyb, hbz.trans hzx⟩
      · apply (hC b).isLUB_mem (t := {z ∈ t | b < z})
        · intro z hz
          exact (ht hz.1).2 b hb hz.2
        · obtain ⟨z, hz, hbz, -⟩ := hlim b hbx
          exact ⟨z, hz, hbz⟩
        · refine ⟨fun z hz => hx.1 hz.1, fun u hu => hx.2 fun z hz => ?_⟩
          rcases le_or_gt z b with hzb | hbz
          · obtain ⟨z', hz', hbz', -⟩ := hlim b hbx
            exact hzb.trans (hbz'.le.trans (hu ⟨hz', hbz'⟩))
          · exact hu ⟨hz, hbz⟩
    · intro y
      have hstep : ∀ a : α, ∃ a', a < a' ∧ (∃ b ∈ s, a < b ∧ b < a') ∧
          ∀ b ∈ s, b < a → a' ∈ C b := by
        intro a
        obtain ⟨a1, ha1⟩ := exists_gt a
        obtain ⟨b, hb, hab⟩ := hs a1
        obtain ⟨b1, hb1⟩ := exists_gt b
        have hclub : IsClub (⋂₀ (C '' (s ∩ Iio a))) :=
          IsClub.sInter hcof0 (mk_image_le.trans_lt (hseg a))
            (by rintro _ ⟨b', -, rfl⟩; exact hC b')
        obtain ⟨a', ha', hle⟩ := hclub.isCofinal b1
        exact ⟨a', (ha1.trans_le hab).trans (hb1.trans_le hle),
          ⟨b, hb, ha1.trans_le hab, hb1.trans_le hle⟩,
          fun b' hb' hb'a => ha' _ ⟨b', ⟨hb', hb'a⟩, rfl⟩⟩
      choose g hg1 hg2 hg3 using hstep
      let a : ℕ → α := fun n => g^[n] y
      have ha_succ : ∀ n, a (n + 1) = g (a n) := fun n => Function.iterate_succ_apply' g n y
      have hmono : StrictMono a := strictMono_nat_of_lt_succ fun n => by
        rw [ha_succ]; exact hg1 _
      obtain ⟨x, hx⟩ := exists_isLUB_of_mk_lt_cof
        ((countable_range a).le_aleph0.trans_lt hα)
      have hbelow : ∀ y' < x, ∃ n, y' < a n := fun y' hy' => by
        by_contra! h
        exact hy'.not_ge (hx.2 (by rintro _ ⟨n, rfl⟩; exact h n))
      refine ⟨x, ⟨fun y' hy' => ?_, fun b hb hbx => ?_⟩, hx.1 ⟨0, rfl⟩⟩
      · obtain ⟨n, hn⟩ := hbelow y' hy'
        obtain ⟨b, hb, h1, h2⟩ := hg2 (a n)
        exact ⟨b, hb, hn.trans h1, h2.trans_le (by rw [← ha_succ]; exact hx.1 ⟨n + 1, rfl⟩)⟩
      · obtain ⟨n, hn⟩ := hbelow b hbx
        apply (hC b).isLUB_mem (t := range fun m => a (n + m + 1))
        · rintro _ ⟨m, rfl⟩
          show a (n + m + 1) ∈ C b
          rw [ha_succ]
          exact hg3 _ b hb (hn.trans_le (hmono.monotone (Nat.le_add_right n m)))
        · exact range_nonempty _
        · refine ⟨by rintro _ ⟨m, rfl⟩; exact hx.1 ⟨_, rfl⟩,
            fun u hu => hx.2 (by rintro _ ⟨k, rfl⟩; exact (hmono.monotone
              (show k ≤ n + k + 1 by omega)).trans (hu ⟨k, rfl⟩))⟩
  obtain ⟨x, hxS, hxL, hxC⟩ := hS hD
  obtain ⟨b, hbs, hfb, hbx⟩ := hxL (f x) (hf x hxS)
  have hmem : x ∈ {x ∈ S | f x < b} ∩ C b := ⟨⟨hxS, hfb⟩, hxC b hbs hbx⟩
  rw [hCS b] at hmem
  exact hmem

omit [WellFoundedLT α] in

theorem isClub_Ici (z : α) : IsClub (Ici z) :=
  ⟨fun _ ht ht0 _ _ hx => ht0.elim fun _ hy => (ht hy).trans (hx.1 hy),
    fun y => ⟨max y z, le_max_right _ _, le_max_left _ _⟩⟩

theorem IsStationary.cof_le_mk [NoMaxOrder α] {S : Set α} (hS : IsStationary S) :
    Order.cof α ≤ #S := by
  by_contra hcon
  have hlt : #S < Order.cof α := lt_of_not_ge hcon
  obtain ⟨b, hb⟩ := exists_isLUB_of_mk_lt_cof hlt
  obtain ⟨z, hz⟩ := exists_gt b
  obtain ⟨x, hxS, hxz⟩ := hS (isClub_Ici z)
  have hxb : x ≤ b := hb.1 hxS
  have hzx : z ≤ x := hxz
  exact absurd (le_trans hzx hxb) (not_le_of_gt hz)

theorem IsStationary.inter_isClub (hα : Order.cof α ≠ ℵ₀) {S D : Set α}
    (hS : IsStationary S) (hD : IsClub D) : IsStationary (S ∩ D) := by
  intro c hc
  obtain ⟨x, hxS, hxD, hxc⟩ := hS (hD.inter hα hc)
  exact ⟨x, ⟨hxS, hxD⟩, hxc⟩

theorem cof_Iio_ord_of_isRegular.{u} {lam : Cardinal.{u}} (hlam : lam.IsRegular) :
    Order.cof ↥(Set.Iio lam.ord) = Cardinal.lift.{u+1} lam := by
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hlam.cof_ord]

theorem sSup_lt_ord_of_isRegular.{u} {lam : Cardinal.{u}} (hlam : lam.IsRegular)
    {S : Set Ordinal.{u}} (hS : S ⊆ Set.Iio lam.ord)
    (hcard : #(↥S) < Cardinal.lift.{u+1} lam) :
    sSup S < lam.ord := by
  have hcof : Order.cof ↥(Set.Iio lam.ord) = Cardinal.lift.{u+1} lam :=
    cof_Iio_ord_of_isRegular hlam
  have hTeq : #({x : ↥(Set.Iio lam.ord) | x.1 ∈ S}) = #(↥S) := Cardinal.mk_congr
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, hS x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hTcard : #({x : ↥(Set.Iio lam.ord) | x.1 ∈ S})
      < Order.cof ↥(Set.Iio lam.ord) := by
    rw [hcof, hTeq]
    exact hcard
  obtain ⟨b, hb⟩ := exists_isLUB_of_mk_lt_cof hTcard
  refine lt_of_le_of_lt ?_ b.2
  refine csSup_le' ?_
  intro o ho
  have hmem : (⟨o, hS ho⟩ : ↥(Set.Iio lam.ord))
      ∈ ({x : ↥(Set.Iio lam.ord) | x.1 ∈ S}) := ho
  exact Subtype.coe_le_coe.2 (hb.1 hmem)

theorem isRegularCardinalOrder_coe_Iio_ord.{u} {lam : Cardinal.{u}}
    (hlam : lam.IsRegular) :
    IsRegularCardinalOrder ↥(Set.Iio lam.ord) where
  type_lt_le_ord_cof := by
    rw [Ordinal.type_lt_Iio, cof_Iio_ord_of_isRegular hlam, ← Cardinal.lift_ord]

end MetaMathlibExt

end
