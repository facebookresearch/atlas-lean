/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner, Nam Trang
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 29, Logic 26, Logic 27, Logic 560, Logic 561

/-!
# `MathlibExt.SetTheory.Cardinal.LargeCardinal.Inaccessible`

## References

* Jech (for `IsWeaklyInaccessible`, `inaccessibleBelow`, `IsInaccessibleFixedPoint`)
-/

/-! ## Beth and aleph bounds below an inaccessible -/

/-! ## Size of `inaccessibleBelow` -/

/-! ## Regular cardinals below a weakly inaccessible -/

/-! ## Weak inaccessibility plus GCH -/

/-! ## Closure of strong limits under exponentiation -/

/-! ## Least cardinals with empty below-sets -/

/-! ## The least inaccessible, conditionally -/

/-! ## The `powerlt` equation at a strong limit -/

/-! ## Strong limits below an inaccessible -/

/-! ## Inaccessibility via beth fixed points -/

/-! ## Unboundedness below a fixed point -/

/-! ## Limit cardinals below a weakly inaccessible -/

open Cardinal Ordinal Set Order

namespace MetaMathlibExt

-- Logic 29: Weakly inaccessible cardinal

/-- A cardinal κ is *weakly inaccessible* if it is an uncountable, regular limit cardinal. -/
def IsWeaklyInaccessible.{u} (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ κ.IsRegular ∧ Order.IsSuccLimit κ

-- Logic 26: Set of inaccessible cardinality below κ

/-- InAccBelow κ is the set of all inaccessible cardinals below κ. -/
def inaccessibleBelow.{u} (κ : Cardinal.{u}) : Set (Set.Iio κ.ord) :=
  {α | Cardinal.IsInaccessible α.val.card ∧ α.val.card.ord = α.val}

-- Logic 27: Inaccessible fixed point

/-- A cardinal κ is an *inaccessible fixed point* if κ is inaccessible and the inaccessibles below κ
have order type κ (i.e. κ is the κ-th inaccessible).
-/
def IsInaccessibleFixedPoint.{u} (κ : Cardinal.{u}) : Prop :=
  Cardinal.IsInaccessible κ ∧
  Ordinal.lift.{u+1} κ.ord = typeLT ↥(inaccessibleBelow κ)

-- Logic 560: Theorems about inaccessible cardinals

/-- Below an inaccessible `κ`, the beth hierarchy stays below `κ`: `κ` is a beth
fixed point (`IsInaccessible.beth_ord`) and `beth` is strictly monotone.

Source: Below an inaccessible κ, each ℶ_o with o < κ.ord lies below κ. -/

theorem _root_.Cardinal.IsInaccessible.beth_lt.{u} {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {o : Ordinal.{u}} (ho : o < κ.ord) : (ℶ_ o : Cardinal.{u}) < κ := by
  rw [← hκ.beth_ord]
  exact beth_lt_beth.mpr ho

/-- Below an inaccessible `κ`, the aleph hierarchy stays below `κ`: same argument
via `IsInaccessible.aleph_ord`.

Source: Below an inaccessible κ, each ℵ_o with o < κ.ord lies below κ. -/

theorem Cardinal.IsInaccessible.aleph_lt.{u} {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {o : Ordinal.{u}} (ho : o < κ.ord) : (ℵ_ o : Cardinal.{u}) < κ := by
  rw [← hκ.aleph_ord]
  exact aleph_lt_aleph.mpr ho

/-- There are at most `κ` inaccessibles below `κ`: the set injects into
`↥(Set.Iio κ.ord)`, which has size `lift κ`.  The `≤` half of the counting needed
for the Mahlo-implies-fixed-point benchmark item.

The `lift` is forced: the carrier lives in `Type (u+1)`, the same phenomenon as
the `lift` in `IsInaccessibleFixedPoint`.

Source: There are at most κ inaccessible cardinals below κ. -/

theorem mk_inaccessibleBelow_le.{u} (κ : Cardinal.{u}) :
    #(↥(inaccessibleBelow κ)) ≤ Cardinal.lift.{u+1} κ := by
  calc #(↥(inaccessibleBelow κ)) ≤ #↥(Set.Iio κ.ord) := mk_subtype_le _
    _ = Cardinal.lift.{u+1} κ := by rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]

/-- Regular cardinals are unbounded below an uncountable limit cardinal `κ` (in
particular a weakly inaccessible one): above any `a < κ` sits
`succ (max a ℵ₀)`, regular by `isRegular_succ` and below `κ` since `κ` is a
limit.

Source: Regular cardinals are unbounded below any uncountable limit cardinal. -/

theorem exists_regular_between.{u} {κ : Cardinal.{u}} (hlt : ℵ₀ < κ)
    (hlim : Order.IsSuccLimit κ) {a : Cardinal.{u}} (ha : a < κ) :
    ∃ r : Cardinal.{u}, a < r ∧ r < κ ∧ r.IsRegular := by
  refine ⟨Order.succ (max a ℵ₀), ?_, hlim.succ_lt (max_lt_iff.mpr ⟨ha, hlt⟩),
    isRegular_succ (le_max_right _ _)⟩
  exact lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)

/-- Under (local) GCH, weakly inaccessible implies strongly inaccessible: for
infinite `μ < κ`, `2 ^ μ = succ μ < κ` by the limit property, and the finite
case is `power_lt_aleph0`.

`GCH` is spelled inline and localized below `κ`, following the
`singularCardinalsHypothesis_of_gch` precedent (Mathlib has no `GCH` identifier);
the `ℵ₀ ≤ μ` restriction is load-bearing for the same reason as there.

Source: Under GCH below κ, a weakly inaccessible κ is inaccessible. -/

theorem IsWeaklyInaccessible.isInaccessible_of_gch.{u} {κ : Cardinal.{u}}
    (hκ : IsWeaklyInaccessible κ)
    (hgch : ∀ μ : Cardinal.{u}, μ < κ → ℵ₀ ≤ μ →
      (2 : Cardinal.{u}) ^ μ = Order.succ μ) : κ.IsInaccessible := by
  obtain ⟨hlt, hreg, hlim⟩ := hκ
  refine isInaccessible_def.mpr ⟨hlt, hreg, ⟨?_, ?_⟩⟩
  · exact ne_of_gt (aleph0_pos.trans hlt)
  · intro x hx
    by_cases hinf : ℵ₀ ≤ x
    · rw [hgch x hx hinf]
      exact hlim.succ_lt hx
    · exact (power_lt_aleph0 ofNat_lt_aleph0 (not_le.mp hinf)).trans hlt

/-- A strong limit `κ` is closed under cardinal exponentiation: `x ^ y ≤ 2 ^ (x * y)`
(via `cantor` and `power_mul`), and `x * y < κ` by `mul_lt_of_lt`.  No
infiniteness hypothesis is needed — it is automatic by `IsStrongLimit.aleph0_le`.

Source: Below a strong limit κ, x < κ and y < κ imply x ^ y < κ. -/

theorem _root_.Cardinal.IsStrongLimit.power_lt.{u} {κ x y : Cardinal.{u}} (hκ : κ.IsStrongLimit)
    (hx : x < κ) (hy : y < κ) : x ^ y < κ :=
  calc x ^ y ≤ (2 ^ x) ^ y := power_le_power_right (cantor x).le
    _ = 2 ^ (x * y) := power_mul.symm
    _ < κ := hκ.isStrongPrelimit (mul_lt_of_lt hκ.aleph0_le hx hy)

/- Function types between small types stay small below a strong limit: the
`mk_arrow` reading of `IsStrongLimit.power_lt`.

Source: Below a strong limit, function types between small types are small. -/

end MetaMathlibExt

theorem Cardinal.IsStrongLimit.mk_arrow_lt.{u} {α β : Type u} {κ : Cardinal.{u}}
    (hκ : κ.IsStrongLimit) (hα : #α < κ) (hβ : #β < κ) :
    #(α → β) < κ := by
  rw [mk_arrow, lift_id, lift_id]
  exact hκ.power_lt hβ hα

/- If `P` holds of some cardinal, it holds of one with nothing `P` below it:
minimize `{o | P o.card ∧ initial o}` over the well-founded `<`. Covers the
least-inaccessible and least-Mahlo directions uniformly.

Source: If P holds of some cardinal, it holds of one with no P-cardinal strictly below it. -/

namespace MetaMathlibExt

theorem exists_below_eq_empty_of_exists.{u} {P : Cardinal.{u} → Prop}
    (h : ∃ κ : Cardinal.{u}, P κ) :
    ∃ κ : Cardinal.{u}, P κ ∧
      {α : Set.Iio κ.ord | P α.val.card ∧ α.val.IsInitial} = ∅ := by
  obtain ⟨κ₀, hκ₀⟩ := h
  set S : Set Ordinal.{u} := {o | P o.card ∧ o.IsInitial} with hS
  have hne : S.Nonempty :=
    ⟨κ₀.ord, by rw [Cardinal.card_ord]; exact hκ₀, isInitial_ord _⟩
  obtain ⟨o₀, ho₀mem, hmin⟩ := WellFounded.has_min wellFounded_lt S hne
  obtain ⟨ho₀P, ho₀init⟩ := ho₀mem
  refine ⟨o₀.card, ho₀P, ?_⟩
  ext α
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  have hmem : α.val.card.ord ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [Cardinal.card_ord]; exact h1
    · exact isInitial_ord _
  have hltord : α.val.card.ord < o₀ := by
    calc α.val.card.ord = α.val := h2.ord_card
      _ < o₀.card.ord := Set.mem_Iio.mp α.2
      _ = o₀ := ho₀init.ord_card
  exact (hmin _ hmem) hltord

/-- If any inaccessible exists, some inaccessible has no inaccessibles below it:
minimize over the initial ordinals of inaccessible cardinals
(`WellFounded.has_min`), and any member of `inaccessibleBelow` would give a
smaller one.

In particular the least inaccessible — if one exists — is neither Mahlo (see
`exists_isInaccessible_not_isMahlo` in `Mahlo.lean`) nor an inaccessible fixed
point (`not_isInaccessibleFixedPoint_of_inaccessibleBelow_eq_empty` above).

Source: If any inaccessible cardinal exists, some inaccessible has no inaccessibles below it. -/

theorem exists_isInaccessible_inaccessibleBelow_eq_empty.{u}
    (h : ∃ κ : Cardinal.{u}, κ.IsInaccessible) :
    ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ inaccessibleBelow κ = ∅ := by
  obtain ⟨κ, hκ, hempty⟩ :=
    exists_below_eq_empty_of_exists (P := Cardinal.IsInaccessible) h
  exact ⟨κ, hκ, hempty⟩

/-- For `2 ≤ x < κ` with `κ` a strong limit, `x ^< κ = κ`: every smaller power is
below `κ` (`IsStrongLimit.power_lt`), while every `y < κ` sits below
`2 ^ y ≤ x ^< κ`.  No infiniteness hypothesis is needed — it is automatic by
`IsStrongLimit.aleph0_le`.

Source: For 2 ≤ x < κ with κ a strong limit, x ^< κ = κ. -/

theorem Cardinal.IsStrongLimit.powerlt_eq_self.{u} {κ x : Cardinal.{u}}
    (hκ : κ.IsStrongLimit) (hx2 : 2 ≤ x) (hx : x < κ) : x ^< κ = κ := by
  apply le_antisymm
  · exact powerlt_le.mpr (fun y hy => (hκ.power_lt hx hy).le)
  · by_contra hcon
    have hlt : x ^< κ < κ := not_le.mp hcon
    have hle : ∀ y < κ, y < x ^< κ := fun y hy =>
      calc y < 2 ^ y := cantor y
        _ ≤ x ^ y := power_le_power_right hx2
        _ ≤ x ^< κ := le_powerlt x hy
    exact lt_irrefl _ (hle _ hlt)

/-- Strong limits are unbounded below an inaccessible `κ`: above any `a < κ` sits
`ℶ_{a.ord + ω}`, a strong limit by `isStrongLimit_beth` since `a.ord + ω` is a
limit ordinal (`isSuccLimit_add`), and below `κ` since
`(a.ord + ω).card = a.ord.card + ℵ₀ < κ` (`add_lt_of_lt`).

Source: Above any a < κ with κ inaccessible sits a strong limit cardinal below κ. -/

theorem Cardinal.IsInaccessible.exists_isStrongLimit_between.{u} {κ : Cardinal.{u}}
    (hκ : κ.IsInaccessible) {a : Cardinal.{u}} (ha : a < κ) :
    ∃ μ : Cardinal.{u}, a < μ ∧ μ < κ ∧ μ.IsStrongLimit := by
  have ho1 : a.ord < a.ord + ω := lt_add_of_pos_right _ omega0_pos
  have ho2 : a.ord + ω < κ.ord := Cardinal.lt_ord.mpr (by
    rw [card_add, card_omega0]
    exact add_lt_of_lt hκ.aleph0_lt.le
      (Cardinal.lt_ord.mp (Cardinal.ord_lt_ord.mpr ha)) hκ.aleph0_lt)
  refine ⟨ℶ_ (a.ord + ω), ?_, hκ.beth_lt ho2,
    isStrongLimit_beth.mpr (isSuccLimit_add _ isSuccLimit_omega0).isSuccPrelimit⟩
  calc a ≤ ℶ_ a.ord := le_beth_ord a
    _ < ℶ_ (a.ord + ω) := beth_lt_beth.mpr ho1

-- Logic 561: Theorems about inaccessible cardinals (part II)

   /-- The **regular cardinals below `κ`**, carried as initial ordinals — parallel to
`inaccessibleBelow`, and definitionally the stationary set in `IsWeaklyMahlo`.
Spelled with Mathlib's `Ordinal.IsInitial`.

Source: regularBelow κ is the set of initial ordinals below κ whose cardinals are regular. -/

def regularBelow.{u} (κ : Cardinal.{u}) : Set (Set.Iio κ.ord) :=
  {α | α.val.card.IsRegular ∧ α.val.IsInitial}

/-- A regular beth fixed point is uncountable: regularity gives `ℵ₀ ≤ κ`, and
`κ = ℵ₀` fails the fixed-point equation since `ℶ_ω > ℶ_0 = ℵ₀`.

Source: A regular beth fixed point is uncountable. -/

theorem aleph0_lt_of_isRegular_beth_ord.{u} {κ : Cardinal.{u}}
    (hreg : κ.IsRegular) (hbeth : (ℶ_ κ.ord : Cardinal.{u}) = κ) : ℵ₀ < κ := by
  have hle := hreg.aleph0_le
  refine lt_of_le_of_ne hle (fun heq => ?_)
  have hord : κ.ord = Ordinal.omega0 := by
    rw [← heq, Cardinal.ord_aleph0]
  have hlt : (ℶ_ 0 : Cardinal.{u}) < ℶ_ Ordinal.omega0 :=
    beth_lt_beth.mpr omega0_pos
  rw [beth_zero, ← hord, hbeth, ← heq] at hlt
  exact lt_irrefl _ hlt

/-- Converse to `IsInaccessible.beth_ord`: a regular beth fixed point is
inaccessible.  Uncountability is derived, not assumed
(`aleph0_lt_of_isRegular_beth_ord`); for `x < κ`,
`2 ^ x ≤ 2 ^ ℶ_{x.ord} = ℶ_{succ x.ord} < κ`, using that `κ.ord` is a limit
ordinal.

Regularity is genuinely needed — the first beth fixed point is singular — so
this does not promote a bare fixed point.

Source: A regular beth fixed point is inaccessible. -/

theorem Cardinal.IsInaccessible.of_isRegular_beth_ord.{u} {κ : Cardinal.{u}}
    (hreg : κ.IsRegular) (hbeth : (ℶ_ κ.ord : Cardinal.{u}) = κ) :
    κ.IsInaccessible := by
  have hlt := aleph0_lt_of_isRegular_beth_ord hreg hbeth
  refine isInaccessible_def.mpr ⟨hlt, hreg, ⟨?_, ?_⟩⟩
  · exact ne_of_gt (aleph0_pos.trans hlt)
  · intro x hx
    have ho : Order.succ x.ord < κ.ord :=
      (isSuccLimit_ord hlt.le).succ_lt (ord_lt_ord.mpr hx)
    calc (2 : Cardinal.{u}) ^ x ≤ 2 ^ ℶ_ x.ord :=
      power_le_power_left two_ne_zero (le_beth_ord x)
      _ = ℶ_ (Order.succ x.ord) := (beth_succ _).symm
      _ < ℶ_ κ.ord := beth_lt_beth.mpr ho
      _ = κ := hbeth

/-- `κ` is inaccessible iff it is regular and a beth fixed point (uncountability
is automatic by `aleph0_lt_of_isRegular_beth_ord`): this packages
`of_isRegular_beth_ord` with Mathlib's `IsInaccessible.beth_ord`.

Source: κ is inaccessible if and only if κ is regular and a beth fixed point. -/

theorem Cardinal.isInaccessible_iff_isRegular_beth_ord.{u} {κ : Cardinal.{u}} :
    κ.IsInaccessible ↔ κ.IsRegular ∧ (ℶ_ κ.ord : Cardinal.{u}) = κ := by
  constructor
  · intro h
    exact ⟨h.isRegular, h.beth_ord⟩
  · rintro ⟨hreg, hbeth⟩
    exact Cardinal.IsInaccessible.of_isRegular_beth_ord hreg hbeth

/-- The fixed-point equation forces `#(inaccessibleBelow κ) = lift κ`
(`card_type`): the companion to the upper bound `mk_inaccessibleBelow_le`.

Source: Below an inaccessible fixed point κ there are exactly κ inaccessible cardinals. -/

theorem IsInaccessibleFixedPoint.mk_inaccessibleBelow.{u} {κ : Cardinal.{u}}
    (h : IsInaccessibleFixedPoint κ) :
    #↥(inaccessibleBelow κ) = Cardinal.lift.{u+1} κ := by
  have hcardS : Ordinal.card (typeLT ↥(inaccessibleBelow κ)) = #↥(inaccessibleBelow κ) :=
    card_type (· < ·)
  have hcongr := congrArg Ordinal.card h.2
  rw [← lift_card, Cardinal.card_ord, hcardS] at hcongr
  exact hcongr.symm

/-- Inaccessibles below an inaccessible fixed point are unbounded: if they were
bounded by `a`, the set would inject into `Iic a.val`, hence have size at most
`lift (a.val + 1).card < lift κ` — contradicting `mk_inaccessibleBelow`.

Source: Inaccessibles below an inaccessible fixed point are unbounded. -/

theorem IsInaccessibleFixedPoint.exists_gt.{u} {κ : Cardinal.{u}}
    (h : IsInaccessibleFixedPoint κ) (a : ↥(Set.Iio κ.ord)) :
    ∃ b ∈ inaccessibleBelow κ, a.val < b.val := by
  have hinacc := h.1
  by_contra hcon
  have hsub : inaccessibleBelow κ ⊆ Set.Iic a := fun b hb => by
    by_contra hcon2
    rw [Set.mem_Iic] at hcon2
    exact hcon ⟨b, hb, not_le.mp hcon2⟩
  have hcardIic : #↥(Set.Iic a.val) = Cardinal.lift.{u+1} (a.val + 1).card := by
    rw [← Order.Iio_succ, Order.succ_eq_add_one, Cardinal.mk_Iio_ordinal]
  have hinj : Function.Injective
      (fun b : ↥(Set.Iic a) => (⟨b.val.val, Set.mem_Iic.mp b.2⟩ : ↥(Set.Iic a.val))) := by
    intro b₁ b₂ h12
    have hval : b₁.val.val = b₂.val.val := by
      have h := congrArg Subtype.val h12
      exact h
    exact Subtype.ext (Subtype.ext hval)
  have hle : #↥(inaccessibleBelow κ) ≤ Cardinal.lift.{u+1} (a.val + 1).card :=
    calc #↥(inaccessibleBelow κ) ≤ #↥(Set.Iic a) :=
            mk_subtype_le_of_subset (fun b hb => hsub hb)
      _ ≤ #↥(Set.Iic a.val) := mk_le_of_injective hinj
      _ = Cardinal.lift.{u+1} (a.val + 1).card := hcardIic
  have hltcard : Cardinal.lift.{u+1} (a.val + 1).card < Cardinal.lift.{u+1} κ := by
    rw [Cardinal.lift_lt]
    apply Cardinal.lt_ord.mp
    rw [← Order.succ_eq_add_one]
    exact (Cardinal.isSuccLimit_ord hinacc.aleph0_lt.le).succ_lt (Set.mem_Iio.mp a.2)
  have heq := h.mk_inaccessibleBelow
  rw [heq] at hle
  exact lt_irrefl _ (hle.trans_lt hltcard)

/-- Limit cardinals are unbounded below a weakly inaccessible `κ`: the sup of
the `ω`-chain `μ 0 = succ (max a ℵ₀)`, `μ (n+1) = succ (μ n)` stays below `κ`
(`sum_lt_of_isRegular`), exceeds `a`, and is a limit since every `x < σ`
lies below some `μ n` (`exists_lt_of_lt_ciSup`).

Source: Above any a < κ with κ weakly inaccessible sits a limit cardinal below κ. -/

theorem IsWeaklyInaccessible.exists_isSuccLimit_between.{u} {κ : Cardinal.{u}}
    (hκ : IsWeaklyInaccessible κ) {a : Cardinal.{u}} (ha : a < κ) :
    ∃ μ : Cardinal.{u}, a < μ ∧ μ < κ ∧ Order.IsSuccLimit μ := by
  obtain ⟨hlt, hreg, hlim⟩ := hκ
  set μ : ℕ → Cardinal.{u} :=
    Nat.rec (Order.succ (max a ℵ₀)) (fun _ m => Order.succ m) with hμ
  have hμ0 : μ 0 = Order.succ (max a ℵ₀) := rfl
  have hμS : ∀ n, μ n.succ = Order.succ (μ n) := fun n => rfl
  have hmax : max a ℵ₀ < κ := max_lt_iff.mpr ⟨ha, hlt⟩
  have hμκ : ∀ n, μ n < κ := by
    intro n
    induction n with
    | zero => rw [hμ0]; exact hlim.succ_lt hmax
    | succ n ih => rw [hμS]; exact hlim.succ_lt ih
  have hι : Cardinal.lift.{u} #(ℕ) < κ := by
    have hmk : Cardinal.lift.{u} #(ℕ) = (ℵ₀ : Cardinal.{u}) := by
      rw [Cardinal.mk_nat]
      exact Cardinal.lift_aleph0
    rw [hmk]
    exact hlt
  have hσκ : ⨆ n, μ n < κ :=
    (Cardinal.iSup_le_sum μ).trans_lt
      (Cardinal.sum_lt_lift_of_isRegular hreg hι hμκ)
  have hbdd : BddAbove (Set.range μ) :=
    ⟨κ, by rintro _ ⟨n, rfl⟩; exact (hμκ n).le⟩
  have hbase : a < μ 0 := by
    rw [hμ0]
    exact lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)
  have haσ : a < ⨆ n, μ n := lt_of_lt_of_le hbase (le_ciSup hbdd 0)
  have hbot : (⊥ : Cardinal.{u}) < μ 0 := by
    rw [hμ0]
    exact lt_of_le_of_lt bot_le (Order.lt_succ _)
  have hpos : (⊥ : Cardinal.{u}) < ⨆ n, μ n :=
    lt_of_lt_of_le hbot (le_ciSup hbdd 0)
  refine ⟨⨆ n, μ n, haσ, hσκ, ⟨?_, ?_⟩⟩
  · rw [not_isMin_iff]; exact ⟨⊥, hpos⟩
  · intro b hcov
    obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hcov.lt
    have hlt1 : Order.succ b < μ n.succ := by
      rw [hμS]
      exact lt_of_le_of_lt (Order.succ_le_of_lt hn) (Order.lt_succ _)
    have hlt2 : Order.succ b < ⨆ n, μ n :=
      lt_of_lt_of_le hlt1 (le_ciSup hbdd n.succ)
    rw [hcov.succ_eq] at hlt2
    exact lt_irrefl _ hlt2

/-- The sup of a bounded set of initial ordinals is initial: if
`σ.card.ord < σ` then some member exceeds `σ.card.ord`, trapping it strictly
between itself and its own initial ordinal.

Source: The supremum of a bounded set of initial ordinals is initial. -/

theorem sSup_initial_of_forall_initial.{u} {T : Set Ordinal.{u}} (hbdd : BddAbove T)
    (h : ∀ t ∈ T, t.IsInitial) : (sSup T).IsInitial := by
  have hle : (sSup T).card.ord ≤ sSup T := Cardinal.ord_card_le _
  have hge : sSup T ≤ (sSup T).card.ord := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨t, ht, hgt⟩ := exists_lt_of_lt_csSup' hcon
    have htle : t ≤ sSup T := le_csSup hbdd ht
    have hchain : t ≤ (sSup T).card.ord := by
      have hteq := (h t ht).ord_card
      rw [← hteq]
      exact Cardinal.ord_le_ord.mpr (Ordinal.card_le_card htle)
    exact lt_irrefl _ (hchain.trans_lt hgt)
  exact le_antisymm hle hge

end MetaMathlibExt

end
