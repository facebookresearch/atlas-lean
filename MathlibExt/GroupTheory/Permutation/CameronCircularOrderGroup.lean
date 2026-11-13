/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Permutation.CircularOrder
public import MathlibExt.GroupTheory.Permutation.HighlyHomogeneous
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.Order.Circular
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Constructions

@[expose] public section

section
namespace MetaMathlibExt.CameronHelpers

private theorem sbtw_ne_of_sbtw {α : Type*} [CircularOrder α] {a b c : α} (h : sbtw a b c) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
  · subst he; exact sbtw_irrefl_left h
  · subst he; exact sbtw_irrefl_right h
  · subst he; exact sbtw_irrefl_left_right h

private theorem not_sbtw_of_eq {α : Type*} [CircularOrder α] {a b c : α}
    (h : a = b ∨ b = c ∨ a = c) : ¬sbtw a b c := by
  rcases h with rfl | rfl | rfl
  · exact sbtw_irrefl_left
  · exact sbtw_irrefl_right
  · exact sbtw_irrefl_left_right

private theorem exists_sbtw_of_ne {α : Type*} [CircularOrder α]
    (hdense : ∀ a b : α, a ≠ b → ∃ c : α, c ≠ a ∧ c ≠ b ∧ btw a c b)
    {a b : α} (hab : a ≠ b) : ∃ c : α, sbtw a c b := by
  obtain ⟨c, hca, hcb, hbtw⟩ := hdense a b hab
  refine ⟨c, sbtw_of_btw_not_btw hbtw fun hrev => ?_⟩
  rcases btw_antisymm hbtw hrev with h | h | h
  · exact hca h.symm
  · exact hcb h
  · exact hab h.symm

end MetaMathlibExt.CameronHelpers
end

section
namespace MetaMathlibExt.CameronCut

private instance cutLE {α : Type*} [CircularOrder α] (p : α) : LE {x : α // x ≠ p} :=
  ⟨fun x y => x.val = y.val ∨ sbtw p x.val y.val⟩

private instance cutLT {α : Type*} [CircularOrder α] (p : α) : LT {x : α // x ≠ p} :=
  ⟨fun x y => x ≤ y ∧ ¬y ≤ x⟩

private noncomputable instance cutDecLE {α : Type*} [CircularOrder α] (p : α) :
    DecidableLE {x : α // x ≠ p} :=
  fun _x _y => Classical.propDecidable _

private noncomputable instance cutDecLT {α : Type*} [CircularOrder α] (p : α) :
    DecidableLT {x : α // x ≠ p} :=
  fun _x _y => Classical.propDecidable _

private instance cutDecEq {α : Type*} [CircularOrder α] [DecidableEq α] (p : α) :
    DecidableEq {x : α // x ≠ p} := fun x y =>
  match decEq x.val y.val with
  | isTrue h => isTrue (Subtype.ext h)
  | isFalse h => isFalse (fun hxy => h (congrArg Subtype.val hxy))

private instance cutPreorder {α : Type*} [CircularOrder α] (p : α) :
    Preorder {x : α // x ≠ p} where
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with h | hxy
    · rw [Subtype.ext h]; exact hyz
    · rcases hyz with h | hyz
      · rw [Subtype.ext h] at hxy; exact Or.inr hxy
      · exact Or.inr (sbtw_trans_right hxy hyz)

private instance cutPartialOrder {α : Type*} [CircularOrder α] (p : α) :
    PartialOrder {x : α // x ≠ p} where
  le_antisymm x y hxy hyx := by
    rcases hxy with h | hxy
    · exact Subtype.ext h
    · rcases hyx with h | hyx
      · exact Subtype.ext h.symm
      · have h1 : btw p x.val y.val := btw_of_sbtw hxy
        have h2 : btw y.val x.val p := by
          have h := btw_of_sbtw hyx
          rwa [btw_cyclic, btw_cyclic] at h
        rcases btw_antisymm h1 h2 with h | h | h
        · exact (x.prop h.symm).elim
        · exact Subtype.ext h
        · exact (y.prop h).elim

private noncomputable instance cutMin {α : Type*} [CircularOrder α] (p : α) :
    Min {x : α // x ≠ p} :=
  ⟨fun x y => if x ≤ y then x else y⟩

private noncomputable instance cutMax {α : Type*} [CircularOrder α] (p : α) :
    Max {x : α // x ≠ p} :=
  ⟨fun x y => if x ≤ y then y else x⟩

private noncomputable instance cutOrd {α : Type*} [CircularOrder α] [DecidableEq α] (p : α) :
    Ord {x : α // x ≠ p} :=
  ⟨fun x y => compareOfLessAndEq x y⟩

private noncomputable instance cutLinearOrder {α : Type*} [CircularOrder α] [DecidableEq α] (p : α)
    :
    LinearOrder {x : α // x ≠ p} where
  le_total x y := by
    by_cases heq : x.val = y.val
    · exact Or.inl (Or.inl heq)
    · rcases CircularOrder.btw_total p x.val y.val with h | h
      · left
        refine Or.inr (sbtw_of_btw_not_btw h fun hrev => ?_)
        rcases btw_antisymm h hrev with h1 | h1 | h1
        · exact x.prop h1.symm
        · exact heq h1
        · exact y.prop h1
      · right
        have h' : btw p y.val x.val := by
          rwa [btw_cyclic] at h
        refine Or.inr (sbtw_of_btw_not_btw h' fun hrev => ?_)
        rcases btw_antisymm h' hrev with h1 | h1 | h1
        · exact y.prop h1.symm
        · exact heq h1.symm
        · exact x.prop h1
  toDecidableLE _ _ := Classical.propDecidable _
  toDecidableEq := inferInstance
  toDecidableLT _ _ := Classical.propDecidable _
  min_def _ _ := rfl
  max_def _ _ := rfl
  compare_eq_compareOfLessAndEq _ _ := rfl

end MetaMathlibExt.CameronCut
end

section
namespace MetaMathlibExt.CameronCut2

private theorem cut_lt_iff {α : Type*} [CircularOrder α] {p : α}
    {x y : {x : α // x ≠ p}} : x < y ↔ sbtw p x.val y.val := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with heq | h
    · have hxy : x = y := Subtype.ext heq
      rw [hxy] at h2
      exact (h2 (le_refl y)).elim
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rintro (heq | hrev)
    · rw [heq] at h; exact sbtw_irrefl_right h
    · exact sbtw_asymm h (sbtw_cyclic_left hrev)

end MetaMathlibExt.CameronCut2
end

section
namespace MetaMathlibExt.CameronCut3

private theorem sbtw_total_of_ne {α : Type*} [CircularOrder α] {p x y : α}
    (hxy : x ≠ y) (hxp : x ≠ p) (hyp : y ≠ p) : sbtw p x y ∨ sbtw p y x := by
  rcases CircularOrder.btw_total p x y with h | h
  · left
    refine sbtw_of_btw_not_btw h fun hrev => ?_
    rcases btw_antisymm h hrev with h1 | h1 | h1
    · exact hxp h1.symm
    · exact hxy h1
    · exact hyp h1
  · right
    have h' : btw p y x := by rwa [btw_cyclic] at h
    refine sbtw_of_btw_not_btw h' fun hrev => ?_
    rcases btw_antisymm h' hrev with h1 | h1 | h1
    · exact hyp h1.symm
    · exact hxy h1.symm
    · exact hxp h1

private theorem sbtw_arm {α : Type*} [CircularOrder α] {p x y z : α}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (h1 : sbtw p x y) (h2 : sbtw p y z) : sbtw x y z := by
  have htot : sbtw x y z ∨ sbtw x z y :=
    sbtw_total_of_ne hyz hxy.symm hzx
  rcases htot with h | h
  · exact h
  · exfalso
    have hpcb : sbtw p z y := h1.trans_left h
    exact sbtw_asymm h2 (sbtw_cyclic_left hpcb)

end MetaMathlibExt.CameronCut3
end

section
namespace MetaMathlibExt.CameronCut4

open MetaMathlibExt.CameronCut3

private theorem sbtw_cyclic_iff {α : Type*} [CircularOrder α] {p a b c : α}
    (hap : a ≠ p) (hbp : b ≠ p) (hcp : c ≠ p)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    sbtw a b c ↔
      (sbtw p a b ∧ sbtw p b c) ∨ (sbtw p b c ∧ sbtw p c a) ∨
        (sbtw p c a ∧ sbtw p a b) := by
  constructor
  · intro h
    have o1 := sbtw_total_of_ne hab hap hbp
    have o2 := sbtw_total_of_ne hbc hbp hcp
    have o3 := sbtw_total_of_ne hca hcp hap
    rcases o1 with h1 | h1 <;> rcases o2 with h2 | h2 <;> rcases o3 with h3 | h3
    · exact Or.inr (Or.inl ⟨h2, h3⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr ⟨h3, h1⟩)
    · exfalso
      have hacb : sbtw a c b :=
        sbtw_arm hca.symm hbc.symm hab.symm h3 h2
      exact sbtw_asymm h (sbtw_cyclic_left hacb)
    · exact Or.inr (Or.inl ⟨h2, h3⟩)
    · exfalso
      have hbac : sbtw b a c :=
        sbtw_arm hab.symm hca.symm hbc.symm h1 h3
      exact sbtw_asymm h (sbtw_cyclic_left (sbtw_cyclic_left hbac))
    · exfalso
      exact sbtw_asymm h (sbtw_arm hbc.symm hab.symm hca.symm h2 h1)
    · exfalso
      have hpca : sbtw p c a := sbtw_trans_right h2 h1
      exact sbtw_asymm hpca (sbtw_cyclic_left h3)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact sbtw_arm hab hbc hca h1 h2
    · exact sbtw_cyclic_right (sbtw_arm hbc hca hab h1 h2)
    · exact sbtw_cyclic_right (sbtw_cyclic_right (sbtw_arm hca hab hbc h1 h2))

end MetaMathlibExt.CameronCut4
end

section
namespace MetaMathlibExt.CameronCut5

open MetaMathlibExt.CameronCut3 MetaMathlibExt.CameronCut2 MetaMathlibExt.CameronHelpers

private theorem cut_denselyOrdered {α : Type*} [CircularOrder α] {p : α}
    (hdense : ∀ a b : α, a ≠ b → ∃ c : α, c ≠ a ∧ c ≠ b ∧ btw a c b) :
    DenselyOrdered {x : α // x ≠ p} := by
  classical
  refine ⟨fun x y hxy => ?_⟩
  rw [cut_lt_iff] at hxy
  obtain ⟨-, hne1, -⟩ := sbtw_ne_of_sbtw hxy
  -- hne1 : x.val ≠ y.val
  obtain ⟨w, hw⟩ := exists_sbtw_of_ne hdense hne1
  -- hw : sbtw x.val w y.val
  have hwp : w ≠ p := by
    intro he
    rw [he] at hw
    have h1 : sbtw p y.val x.val := sbtw_cyclic_left hw
    exact sbtw_asymm hxy (sbtw_cyclic_left h1)
  have hxw : x.val ≠ w := (sbtw_ne_of_sbtw hw).1
  have hwy : w ≠ y.val := (sbtw_ne_of_sbtw hw).2.1
  have h3 : sbtw p w y.val := hxy.trans_left hw
  have hleft : x < (⟨w, hwp⟩ : {x : α // x ≠ p}) := by
    rw [cut_lt_iff]
    change sbtw p x.val w
    rcases lt_or_gt_of_ne
        (show x ≠ (⟨w, hwp⟩ : {x : α // x ≠ p}) from
          fun he => hxw (congrArg Subtype.val he)) with h | h
    · exact cut_lt_iff.mp h
    · exfalso
      rw [cut_lt_iff] at h
      have hwyx : sbtw w y.val x.val := sbtw_cyclic_left hw
      have hpyx : sbtw p y.val x.val := h.trans_left hwyx
      exact sbtw_asymm hxy (sbtw_cyclic_left hpyx)
  have hright : (⟨w, hwp⟩ : {x : α // x ≠ p}) < y := by
    rw [cut_lt_iff]
    change sbtw p w y.val
    exact h3
  exact ⟨⟨w, hwp⟩, hleft, hright⟩

end MetaMathlibExt.CameronCut5
end

section
namespace MetaMathlibExt.CameronCut6

open MetaMathlibExt.CameronCut3 MetaMathlibExt.CameronCut2 MetaMathlibExt.CameronHelpers

private theorem cut_noMinOrder {α : Type*} [CircularOrder α] {p : α}
    (hdense : ∀ a b : α, a ≠ b → ∃ c : α, c ≠ a ∧ c ≠ b ∧ btw a c b) :
    NoMinOrder {x : α // x ≠ p} := by
  classical
  refine ⟨fun x => ?_⟩
  obtain ⟨c, hc⟩ := exists_sbtw_of_ne hdense (Ne.symm x.prop)
  -- hc : sbtw p c x.val
  have hcp : c ≠ p := Ne.symm (sbtw_ne_of_sbtw hc).1
  -- (a≠b ∧ b≠c ∧ a≠c) with a=p,b=c,c=x: p≠c; so c≠p is symm
  refine ⟨⟨c, hcp⟩, ?_⟩
  rw [cut_lt_iff]
  exact hc

private theorem cut_noMaxOrder {α : Type*} [CircularOrder α] {p : α}
    (hdense : ∀ a b : α, a ≠ b → ∃ c : α, c ≠ a ∧ c ≠ b ∧ btw a c b) :
    NoMaxOrder {x : α // x ≠ p} := by
  classical
  refine ⟨fun x => ?_⟩
  obtain ⟨c, hc⟩ := exists_sbtw_of_ne hdense x.prop
  -- hc : sbtw x.val c p
  have hcp : c ≠ p := (sbtw_ne_of_sbtw hc).2.1
  refine ⟨⟨c, hcp⟩, ?_⟩
  rw [cut_lt_iff]
  change sbtw p x.val c
  exact sbtw_cyclic_left (sbtw_cyclic_left hc)

private theorem cut_nonempty {α : Type*} [CircularOrder α] [Infinite α] {p : α} :
    Nonempty {x : α // x ≠ p} := by
  obtain ⟨a, -, ha⟩ := Set.infinite_univ.exists_notMem_finset ({p} : Finset α)
  exact ⟨⟨a, by simpa using ha⟩⟩

end MetaMathlibExt.CameronCut6
end

section
namespace MetaMathlibExt.CameronLinear

private theorem exists_orderIso_map {L : Type*} [LinearOrder L] [Countable L]
    [DenselyOrdered L] [NoMinOrder L] [NoMaxOrder L] [Nonempty L]
    {k : ℕ} (s t : Fin k → L) (hs : StrictMono s) (ht : StrictMono t) :
    ∃ F : L ≃o L, ∀ i, F (s i) = t i := by
  cases nonempty_encodable L
  have hcmp : ∀ i j, cmp (s i) (s j) = cmp (t i) (t j) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [(cmp_eq_lt_iff _ _).mpr (hs h), (cmp_eq_lt_iff _ _).mpr (ht h)]
    · subst h; exact (cmp_self_eq_eq _).trans (cmp_self_eq_eq _).symm
    · rw [(cmp_eq_gt_iff _ _).mpr (hs h), (cmp_eq_gt_iff _ _).mpr (ht h)]
  let f₀ : Order.PartialIso L L :=
    ⟨Finset.image (fun i => (s i, t i)) Finset.univ, fun p hp q hq => by
      rw [Finset.mem_image] at hp hq
      obtain ⟨i, _, rfl⟩ := hp
      obtain ⟨j, _, rfl⟩ := hq
      exact hcmp i j⟩
  let to_cofinal : L ⊕ L → Order.Cofinal (Order.PartialIso L L) := fun q =>
    Sum.recOn q (Order.PartialIso.definedAtLeft L) (Order.PartialIso.definedAtRight L)
  let our_ideal := Order.idealOfCofinals f₀ to_cofinal
  let F a :=
    Order.PartialIso.funOfIdeal a our_ideal
      (Order.cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inl a))
  let G b :=
    Order.PartialIso.invOfIdeal b our_ideal
      (Order.cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inr b))
  have hmem : f₀ ∈ our_ideal := Order.mem_idealOfCofinals _ _
  have hmap : ∀ i, (F (s i)).val = t i := by
    intro i
    rcases (F (s i)).prop with ⟨f, hf, ha⟩
    rcases our_ideal.directed _ hf _ hmem with ⟨m, _, fm, gm⟩
    have h1 : (s i, (F (s i)).val) ∈ (m.val : Finset (L × L)) := fm ha
    have h2 : (s i, t i) ∈ (m.val : Finset (L × L)) :=
      gm (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hfunc := m.prop _ h1 _ h2
    simp only at hfunc
    rw [cmp_self_eq_eq] at hfunc
    exact (cmp_eq_eq_iff _ _).mp hfunc.symm
  refine ⟨OrderIso.ofCmpEqCmp (fun a => (F a).val) (fun b => (G b).val) fun a b => ?_, fun i => hmap
      i⟩
  rcases (F a).prop with ⟨f, hf, ha⟩
  rcases (G b).prop with ⟨g, hg, hb⟩
  rcases our_ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
  exact m.prop (a, _) (fm ha) (_, b) (gm hb)

end MetaMathlibExt.CameronLinear
end

section
namespace MetaMathlibExt.CameronAssemble

open MetaMathlibExt.CameronCut3 MetaMathlibExt.CameronCut2 MetaMathlibExt.CameronHelpers
  MetaMathlibExt.CameronCut4 MetaMathlibExt.CameronCut5 MetaMathlibExt.CameronCut6
  MetaMathlibExt.CameronLinear

private theorem exists_perm_map_powerset {α : Type*} [DecidableEq α] [Countable α] [Infinite α]
    [CircularOrder α]
    (hdense : ∀ a b : α, a ≠ b → ∃ c : α, c ≠ a ∧ c ≠ b ∧ btw a c b)
    (k : ℕ) (x y : ↥(Set.powersetCard α k)) :
    ∃ g : Equiv.Perm α, (∀ a b c : α, btw a b c ↔ btw (g a) (g b) (g c)) ∧
      (x.val).image (fun a => g a) = y.val := by
  have hS : (x.val).card = k := x.prop
  have hT : (y.val).card = k := y.prop
  obtain ⟨p, -, hp⟩ := Set.infinite_univ.exists_notMem_finset ((x.val) ∪ (y.val))
  have hpS : p ∉ (x.val : Finset α) := fun h => hp (Finset.mem_union_left _ h)
  have hpT : p ∉ (y.val : Finset α) := fun h => hp (Finset.mem_union_right _ h)
  have := cut_denselyOrdered (p := p) hdense
  have := cut_noMinOrder (p := p) hdense
  have := cut_noMaxOrder (p := p) hdense
  have := cut_nonempty (p := p)
  -- transfer the two k-sets into the cut
  let embS : {s : α // s ∈ x.val} ↪ {s : α // s ≠ p} :=
    ⟨fun s => ⟨s.val, fun h => hpS (h ▸ s.prop)⟩,
     fun a b h => by
    have h2 := congrArg Subtype.val h
    exact Subtype.ext h2⟩
  let embT : {t : α // t ∈ y.val} ↪ {s : α // s ≠ p} :=
    ⟨fun s => ⟨s.val, fun h => hpT (h ▸ s.prop)⟩,
     fun a b h => by
    have h2 := congrArg Subtype.val h
    exact Subtype.ext h2⟩
  let SL : Finset {s : α // s ≠ p} := (x.val).attach.map embS
  let TL : Finset {s : α // s ≠ p} := (y.val).attach.map embT
  have hSL : SL.card = k := by
    have h : SL.card = (x.val).card := by
      simp [SL, Finset.card_map, Finset.card_attach]
    rwa [hS] at h
  have hTL : TL.card = k := by
    have h : TL.card = (y.val).card := by
      simp [TL, Finset.card_map, Finset.card_attach]
    rwa [hT] at h
  let sL : Fin k ↪o {s : α // s ≠ p} := SL.orderEmbOfFin hSL
  let tL : Fin k ↪o {s : α // s ≠ p} := TL.orderEmbOfFin hTL
  have sLdef : sL = SL.orderEmbOfFin hSL := rfl
  have tLdef : tL = TL.orderEmbOfFin hTL := rfl
  obtain ⟨F, hF⟩ := exists_orderIso_map (⇑sL) (⇑tL) sL.strictMono tL.strictMono
  -- the full permutation: F on the cut, fixed p
  let σ : Equiv.Perm α :=
    { toFun := fun a => if h : a = p then p else (F ⟨a, h⟩).val,
      invFun := fun a => if h : a = p then p else (F.symm ⟨a, h⟩).val,
      left_inv := by
        intro b
        by_cases hb : b = p
        · rw [hb]; simp
        · have hFp : (F ⟨b, hb⟩).val ≠ p := (F ⟨b, hb⟩).prop
          simp only [dite_eq_right hb, dite_eq_right hFp]
          exact congrArg Subtype.val (F.symm_apply_apply ⟨b, hb⟩),
      right_inv := by
        intro b
        by_cases hb : b = p
        · rw [hb]; simp
        · have hFp : (F.symm ⟨b, hb⟩).val ≠ p := (F.symm ⟨b, hb⟩).prop
          simp only [dite_eq_right hb, dite_eq_right hFp]
          exact congrArg Subtype.val (F.apply_symm_apply ⟨b, hb⟩) }
  have hσp : σ p = p := dite_eq_left rfl
  have hσa : ∀ (a : α) (h : a ≠ p), σ a = (F ⟨a, h⟩).val := fun a h => dite_eq_right h
  have hσne : ∀ (a : α) (h : a ≠ p), σ a ≠ p := fun a h => by
    rw [hσa a h]; exact (F ⟨a, h⟩).prop
  have hσinj : Function.Injective σ := σ.injective
  -- transfer of strict betweenness through the cut isomorphism
  have transfer : ∀ u v : α, ∀ hu : u ≠ p, ∀ hv : v ≠ p,
      sbtw p u v ↔ sbtw p (σ u) (σ v) := by
    intro u v hu hv
    rw [hσa u hu, hσa v hv]
    have c1 : sbtw p u v ↔ ((⟨u, hu⟩ : {s : α // s ≠ p}) < ⟨v, hv⟩) :=
      (cut_lt_iff (x := (⟨u, hu⟩ : {s : α // s ≠ p})) (y := (⟨v, hv⟩ : {s : α // s ≠ p}))).symm
    have c2 : ((⟨u, hu⟩ : {s : α // s ≠ p}) < ⟨v, hv⟩) ↔
        (F (⟨u, hu⟩ : {s : α // s ≠ p}) < F (⟨v, hv⟩ : {s : α // s ≠ p})) :=
      F.lt_iff_lt.symm
    have c3 : (F (⟨u, hu⟩ : {s : α // s ≠ p}) < F (⟨v, hv⟩ : {s : α // s ≠ p})) ↔
        sbtw p (F ⟨u, hu⟩).val (F ⟨v, hv⟩).val :=
      cut_lt_iff
    exact c1.trans (c2.trans c3)
  have hsbtw : ∀ a b c : α, sbtw a b c ↔ sbtw (σ a) (σ b) (σ c) := by
    intro a b c
    by_cases hrep : a = b ∨ b = c ∨ a = c
    · have hrep' : σ a = σ b ∨ σ b = σ c ∨ σ a = σ c := by
        rcases hrep with h | h | h
        · exact Or.inl (congrArg σ h)
        · exact Or.inr (Or.inl (congrArg σ h))
        · exact Or.inr (Or.inr (congrArg σ h))
      exact iff_of_false (not_sbtw_of_eq hrep) (not_sbtw_of_eq hrep')
    · have hab : a ≠ b := fun h => hrep (Or.inl h)
      have hbc : b ≠ c := fun h => hrep (Or.inr (Or.inl h))
      have hac : a ≠ c := fun h => hrep (Or.inr (Or.inr h))
      by_cases ha : a = p <;> by_cases hb : b = p <;> by_cases hc : c = p
      · rw [ha, hb, hc, hσp]
      · rw [ha, hb, hσp]
        exact iff_of_false sbtw_irrefl_left sbtw_irrefl_left
      · rw [ha, hc, hσp]
        exact iff_of_false sbtw_irrefl_left_right sbtw_irrefl_left_right
      · rw [ha, hσp]
        exact transfer b c hb hc
      · rw [hb, hc, hσp]
        exact iff_of_false sbtw_irrefl_right sbtw_irrefl_right
      · rw [hb]
        have e1 : sbtw a p c ↔ sbtw p c a := sbtw_cyclic.trans sbtw_cyclic
        have e2 : sbtw (σ a) p (σ c) ↔ sbtw p (σ c) (σ a) :=
          sbtw_cyclic.trans sbtw_cyclic
        rw [hσp]
        exact e1.trans ((transfer c a hc ha).trans e2.symm)
      · rw [hc]
        have e1 : sbtw a b p ↔ sbtw p a b := sbtw_cyclic
        have e2 : sbtw (σ a) (σ b) p ↔ sbtw p (σ a) (σ b) := sbtw_cyclic
        rw [hσp]
        exact e1.trans ((transfer a b ha hb).trans e2.symm)
      · have hap : a ≠ p := ha
        have hbp : b ≠ p := hb
        have hcp : c ≠ p := hc
        have hσa' : σ a ≠ p := hσne a hap
        have hσb' : σ b ≠ p := hσne b hbp
        have hσc' : σ c ≠ p := hσne c hcp
        have hab' : σ a ≠ σ b := fun h => hab (hσinj h)
        have hbc' : σ b ≠ σ c := fun h => hbc (hσinj h)
        have hca' : σ c ≠ σ a := fun h => hac.symm (hσinj h)
        rw [sbtw_cyclic_iff hap hbp hcp hab hbc hac.symm,
          sbtw_cyclic_iff hσa' hσb' hσc' hab' hbc' hca']
        exact or_congr (and_congr (transfer a b hap hbp) (transfer b c hbp hcp))
          (or_congr (and_congr (transfer b c hbp hcp) (transfer c a hcp hap))
            (and_congr (transfer c a hcp hap) (transfer a b hap hbp)))
  -- btw preservation from sbtw preservation
  have hbtw : ∀ a b c : α, btw a b c ↔ btw (σ a) (σ b) (σ c) := by
    intro a b c
    rw [btw_iff_not_sbtw, btw_iff_not_sbtw]
    exact not_congr (hsbtw c b a)
  -- membership in SL/TL unfolds to membership in S/T
  have mem_SL : ∀ w : {s : α // s ≠ p}, w ∈ SL ↔ w.val ∈ x.val := by
    intro w
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨d, _, hd⟩ := hz
      have hvd : d.val = w.val := congrArg Subtype.val hd
      have hdmem := d.prop
      rwa [hvd] at hdmem
    · intro hw
      rw [Finset.mem_map]
      refine ⟨⟨w.val, hw⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      rfl
  have mem_TL : ∀ z : {s : α // s ≠ p}, z ∈ TL ↔ z.val ∈ y.val := by
    intro z
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨d, _, hd⟩ := hz
      have hvd : d.val = z.val := congrArg Subtype.val hd
      have hdmem := d.prop
      rwa [hvd] at hdmem
    · intro hz
      rw [Finset.mem_map]
      refine ⟨⟨z.val, hz⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      rfl
  have range_sL : ∀ w : {s : α // s ≠ p}, w ∈ SL ↔ ∃ i, sL i = w := by
    intro w
    have h : w ∈ (SL : Set {s : α // s ≠ p}) ↔ ∃ i, sL i = w := by
      rw [sLdef, ← Set.mem_range, Finset.range_orderEmbOfFin SL hSL]
    exact Finset.mem_coe.symm.trans h
  have range_tL : ∀ z : {s : α // s ≠ p}, z ∈ TL ↔ ∃ j, tL j = z := by
    intro z
    have h : z ∈ (TL : Set {s : α // s ≠ p}) ↔ ∃ j, tL j = z := by
      rw [tLdef, ← Set.mem_range, Finset.range_orderEmbOfFin TL hTL]
    exact Finset.mem_coe.symm.trans h
  -- F carries SL onto TL
  have hFT : Finset.image (⇑F) SL = TL := by
    apply Finset.ext
    intro z
    rw [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨i, rfl⟩ := (range_sL _).mp hw
      rw [hF i]
      exact (range_tL _).mpr ⟨i, rfl⟩
    · intro hz
      obtain ⟨j, rfl⟩ := (range_tL _).mp hz
      refine ⟨sL j, (range_sL _).mpr ⟨j, rfl⟩, hF j⟩
  -- σ carries x.val onto y.val
  have himg : (x.val).image (fun a => σ a) = y.val := by
    apply Finset.ext
    intro a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hbp : b ≠ p := fun h => hpS (h ▸ hb)
      have hwS : (⟨b, hbp⟩ : {s : α // s ≠ p}) ∈ SL := (mem_SL ⟨b, hbp⟩).mpr hb
      have hFTb : F ⟨b, hbp⟩ ∈ TL := by
        rw [← hFT]
        exact Finset.mem_image.mpr ⟨_, hwS, rfl⟩
      have hval : (F ⟨b, hbp⟩).val ∈ y.val := (mem_TL _).mp hFTb
      have hsig : σ b = (F ⟨b, hbp⟩).val := hσa b hbp
      rwa [hsig]
    · intro ha
      have hap : a ≠ p := fun h => hpT (h ▸ ha)
      obtain ⟨j, hj⟩ := (range_tL _).mp ((mem_TL ⟨a, hap⟩).mpr ha)
      -- hj : tL j = ⟨a, hap⟩
      have hFL : F (sL j) = ⟨a, hap⟩ := by rw [hF j]; exact hj
      have hmemS : (sL j).val ∈ x.val := (mem_SL _).mp ((range_sL _).mpr ⟨j, rfl⟩)
      refine ⟨(sL j).val, hmemS, ?_⟩
      have hne : (sL j).val ≠ p := (sL j).prop
      rw [hσa _ hne]
      exact congrArg Subtype.val hFL
  exact ⟨σ, hbtw, himg⟩

end MetaMathlibExt.CameronAssemble
end
section

namespace MetaMathlibExt.CameronAssembleClosed

private theorem isClosed_circularOrderAutSubgroup {α : Type*} [CircularOrder α] :
    @IsClosed (Equiv.Perm α) (Equiv.Perm.pointwiseTopology (α := α))
      ↑(MetaMathlibExt.circularOrderAutSubgroup α) := by
  let : TopologicalSpace (Equiv.Perm α) := Equiv.Perm.pointwiseTopology (α := α)
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  have : DiscreteTopology (Fin 3 → α) := Pi.discreteTopology
  have hcoe : Continuous (fun σ : Equiv.Perm α => (σ : α → α)) := continuous_induced_dom
  have heval : ∀ a : α, Continuous (fun σ : Equiv.Perm α => σ a) :=
    fun a => (continuous_apply a).comp hcoe
  have hfib : ∀ a b c : α,
      IsClosed {σ : Equiv.Perm α | (btw a b c ↔ btw (σ a) (σ b) (σ c))} := by
    intro a b c
    let f : Equiv.Perm α → (Fin 3 → α) := fun σ => ![σ a, σ b, σ c]
    have hf : Continuous f := by
      rw [continuous_pi_iff]
      intro i
      fin_cases i
      · simpa [f] using heval a
      · simpa [f] using heval b
      · simpa [f] using heval c
    have heq : {σ : Equiv.Perm α | (btw a b c ↔ btw (σ a) (σ b) (σ c))}
        = f ⁻¹' {p : Fin 3 → α | (btw a b c ↔ btw (p 0) (p 1) (p 2))} := by
      ext σ
      simp [f]
    rw [heq]
    exact IsClosed.preimage hf (isClosed_discrete _)
  have hset : (↑(MetaMathlibExt.circularOrderAutSubgroup α) : Set (Equiv.Perm α))
      = ⋂ a, ⋂ b, ⋂ c, {σ : Equiv.Perm α | (btw a b c ↔ btw (σ a) (σ b) (σ c))} := by
    ext σ
    simp [MetaMathlibExt.mem_circularOrderAutSubgroup, Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c => hfib a b c

end MetaMathlibExt.CameronAssembleClosed

end

section
/-!
# Cameron circular-order group

Proves the closed, highly homogeneous circular-order automorphism group.
-/

namespace MetaMathlibExt.CameronCircularOrderGroupWanted

/--
**The automorphism group of a countably infinite dense circular order is closed and highly
homogeneous.** Let $\alpha$ be a countably infinite set with a circular order, and write
$\operatorname{btw}(a, b, c)$ when $b$ lies between $a$ and $c$ going around from $a$ to $c$.
Suppose the circular order is dense: for all distinct $a, b \in \alpha$ there is some
$c \in \alpha$, different from $a$ and $b$, with $\operatorname{btw}(a, c, b)$. Then the group of
permutations $\sigma$ of $\alpha$ such that $\operatorname{btw}(a, b, c)$ holds if and only if
$\operatorname{btw}(\sigma(a), \sigma(b), \sigma(c))$ holds, for all $a, b, c \in \alpha$, is
closed in the topology of pointwise convergence on the permutations of $\alpha$, where $\alpha$
carries the discrete topology, and it is highly homogeneous: for every natural number $k$ it has
a single orbit on the $k$-element subsets of $\alpha$.

Source: Daniele A. Gewurz and Francesca Merola, "Sequences realized as Parker vectors of
oligomorphic permutation groups," JIS 6,
https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex, lines 331–359, source SHA-256
aa62fa83a5a0944c6903374ab69e7ab8d597622de49c86684e44b75f76baca21, cited-span SHA-256
81f32b07c6496d97cbe329c5facf9480104f4afa49b8dfc347b1fd6b1e4f93c4.
Interpretation boundary: only Cameron group C is asserted, with standard countable dense infinite
circular-order hypotheses, not exhaustive classification, uniqueness, or conjugacy.

Proves `Wanted` entry `circularOrderAutSubgroup_isClosed_and_highlyHomogeneous`.
-/
theorem circularOrderAutSubgroup_isClosed_and_highlyHomogeneous
    {α : Type*} [DecidableEq α] [Countable α] [Infinite α] [CircularOrder α]
    (hdense : ∀ a b : α, a ≠ b → ∃ c : α, c ≠ a ∧ c ≠ b ∧ btw a c b) :
    @IsClosed (Equiv.Perm α) (Equiv.Perm.pointwiseTopology (α := α))
      ↑(MetaMathlibExt.circularOrderAutSubgroup α) ∧
      MetaMathlibExt.IsHighlyHomogeneous (MetaMathlibExt.circularOrderAutSubgroup α) := by
  constructor
  · exact MetaMathlibExt.CameronAssembleClosed.isClosed_circularOrderAutSubgroup
  · intro k
    constructor
    intro x y
    obtain ⟨σ, hσbtw, himg⟩ :=
      MetaMathlibExt.CameronAssemble.exists_perm_map_powerset hdense k x y
    refine ⟨⟨σ, (MetaMathlibExt.mem_circularOrderAutSubgroup σ).mpr hσbtw⟩, ?_⟩
    apply Subtype.ext
    have e1 : (((⟨σ, (MetaMathlibExt.mem_circularOrderAutSubgroup σ).mpr hσbtw⟩ :
        MetaMathlibExt.circularOrderAutSubgroup α) • x).val : Finset α)
        = ((σ • x).val : Finset α) := rfl
    rw [e1, Set.powersetCard.coe_smul, Finset.smul_finset_def]
    simp_rw [Equiv.Perm.smul_def]
    exact himg

end MetaMathlibExt.CameronCircularOrderGroupWanted
