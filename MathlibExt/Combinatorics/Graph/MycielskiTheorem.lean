/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MetaMathlibExt

open scoped SimpleGraph

private def myAdj {V : Type*} (G : SimpleGraph V) : Option (V × Bool) → Option (V × Bool) → Prop :=
  fun x y =>
    (∃ v u, x = some (v, false) ∧ y = some (u, false) ∧ G.Adj v u) ∨
    (∃ v u, x = some (v, false) ∧ y = some (u, true) ∧ G.Adj v u) ∨
    (∃ v u, x = some (v, true) ∧ y = some (u, false) ∧ G.Adj v u) ∨
    (∃ v, x = some (v, true) ∧ y = none) ∨
    (∃ v, x = none ∧ y = some (v, true))

private theorem myAdj_symm {V : Type*} (G : SimpleGraph V) : Std.Symm (myAdj G) :=
  ⟨fun x y h => by
    simp only [myAdj] at h ⊢
    rcases h with ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ |
      ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
    · exact Or.inl ⟨u, v, rfl, rfl, G.symm.symm _ _ h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨u, v, rfl, rfl, G.symm.symm _ _ h⟩))
    · exact Or.inr (Or.inl ⟨u, v, rfl, rfl, G.symm.symm _ _ h⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl, rfl⟩)))⟩

private theorem myAdj_irrefl {V : Type*} (G : SimpleGraph V) : Std.Irrefl (myAdj G) :=
  ⟨fun x h => by
    simp only [myAdj] at h
    rcases h with ⟨v, u, hx1, hx2, hadj⟩ | ⟨v, u, hx1, hx2, hadj⟩ | ⟨v, u, hx1, hx2, hadj⟩ |
      ⟨v, hx1, hx2⟩ | ⟨v, hx1, hx2⟩
    · have huv : v = u := congrArg Prod.fst (Option.some_inj.mp (hx1.symm.trans hx2))
      subst huv
      exact G.loopless.irrefl _ hadj
    · have huv : v = u := congrArg Prod.fst (Option.some_inj.mp (hx1.symm.trans hx2))
      subst huv
      exact G.loopless.irrefl _ hadj
    · have huv : v = u := congrArg Prod.fst (Option.some_inj.mp (hx1.symm.trans hx2))
      subst huv
      exact G.loopless.irrefl _ hadj
    · exact (Option.some_ne_none _ (hx1.symm.trans hx2)).elim
    · exact (Option.some_ne_none _ (hx2.symm.trans hx1)).elim⟩

private def myGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option (V × Bool)) where
  Adj := myAdj G
  symm := myAdj_symm G
  loopless := myAdj_irrefl G

private theorem myAdj_of00 {V : Type*} {G : SimpleGraph V} {v u : V} (h : G.Adj v u) :
    myAdj G (some (v, false)) (some (u, false)) :=
  Or.inl ⟨v, u, rfl, rfl, h⟩

private theorem myAdj_of01 {V : Type*} {G : SimpleGraph V} {v u : V} (h : G.Adj v u) :
    myAdj G (some (v, false)) (some (u, true)) :=
  Or.inr (Or.inl ⟨v, u, rfl, rfl, h⟩)

private theorem myAdj_of10 {V : Type*} {G : SimpleGraph V} {v u : V} (h : G.Adj v u) :
    myAdj G (some (v, true)) (some (u, false)) :=
  Or.inr (Or.inr (Or.inl ⟨v, u, rfl, rfl, h⟩))

private theorem myAdj_sh_ad {V : Type*} {G : SimpleGraph V} (v : V) :
    myAdj G (some (v, true)) none :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl, rfl⟩)))

private theorem myAdj_ad_sh {V : Type*} {G : SimpleGraph V} (v : V) :
    myAdj G none (some (v, true)) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨v, rfl, rfl⟩)))

private theorem myAdj_apex_left {V : Type*} {G : SimpleGraph V} {y : Option (V × Bool)}
    (h : myAdj G none y) : ∃ v, y = some (v, true) := by
  simp only [myAdj] at h
  rcases h with ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ |
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · exact ⟨a, hb⟩

private theorem myAdj_apex_right {V : Type*} {G : SimpleGraph V} {x : Option (V × Bool)}
    (h : myAdj G x none) : ∃ v, x = some (v, true) := by
  simp only [myAdj] at h
  rcases h with ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ |
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · cases hb
  · cases hb
  · cases hb
  · exact ⟨a, ha⟩
  · cases hb

private theorem myAdj_to_G {V : Type*} {G : SimpleGraph V} {v u : V} {i j : Bool}
    (h : myAdj G (some (v, i)) (some (u, j))) : G.Adj v u := by
  simp only [myAdj] at h
  rcases h with ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ |
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · have e1 : (v, i) = (a, false) := Option.some_inj.mp ha
    have e2 : (u, j) = (b, false) := Option.some_inj.mp hb
    have h1 : v = a := congrArg Prod.fst e1
    have h2 : u = b := congrArg Prod.fst e2
    rw [h1, h2]
    exact hadj
  · have e1 : (v, i) = (a, false) := Option.some_inj.mp ha
    have e2 : (u, j) = (b, true) := Option.some_inj.mp hb
    have h1 : v = a := congrArg Prod.fst e1
    have h2 : u = b := congrArg Prod.fst e2
    rw [h1, h2]
    exact hadj
  · have e1 : (v, i) = (a, true) := Option.some_inj.mp ha
    have e2 : (u, j) = (b, false) := Option.some_inj.mp hb
    have h1 : v = a := congrArg Prod.fst e1
    have h2 : u = b := congrArg Prod.fst e2
    rw [h1, h2]
    exact hadj
  · exact (Option.some_ne_none _ hb).elim
  · exact (Option.some_ne_none _ ha).elim

private theorem myAdj_no_ss {V : Type*} {G : SimpleGraph V} {v u : V}
    (h : myAdj G (some (v, true)) (some (u, true))) : False := by
  simp only [myAdj] at h
  rcases h with ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ |
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · have e : (v, true) = (a, false) := Option.some_inj.mp ha
    have e2 : (true : Bool) = false := congrArg Prod.snd e
    cases e2
  · have e : (v, true) = (a, false) := Option.some_inj.mp ha
    have e2 : (true : Bool) = false := congrArg Prod.snd e
    cases e2
  · have e : (u, true) = (b, false) := Option.some_inj.mp hb
    have e2 : (true : Bool) = false := congrArg Prod.snd e
    cases e2
  · exact (Option.some_ne_none _ hb).elim
  · exact (Option.some_ne_none _ ha).elim

private theorem myDesome {V : Type*} {x : Option (V × Bool)} (hx : x ≠ none) :
    ∃ v i, x = some (v, i) := by
  cases x with
  | none => exact (hx rfl).elim
  | some p =>
    obtain ⟨v, i⟩ := p
    exact ⟨v, i, rfl⟩

private theorem completeGraph_adj_iff {α : Type*} {x y : α} :
    (SimpleGraph.completeGraph α).Adj x y ↔ x ≠ y := by
  rw [SimpleGraph.completeGraph_eq_top]
  exact SimpleGraph.top_adj _ _

private def myCopy {V : Type*} (G : SimpleGraph V) : G.Copy (myGraph G) where
  toHom := ⟨fun v => some (v, false), fun h => myAdj_of00 h⟩
  injective' := by
    intro a b h
    have h2 : some (a, false) = some (b, false) := h
    exact congrArg Prod.fst (Option.some_inj.mp h2)

private def myRawColor {V : Type*} {k : ℕ} (d : Option (V × Bool) → Fin (k + 1))
    (j : Fin (k + 1)) (v : V) : Fin (k + 1) :=
  if d (some (v, false)) = j then d (some (v, true)) else d (some (v, false))

private theorem myRawColor_ne {V : Type*} {k : ℕ} (d : Option (V × Bool) → Fin (k + 1))
    (j : Fin (k + 1)) (hd : ∀ v : V, d (some (v, true)) ≠ j) (v : V) :
    myRawColor d j v ≠ j := by
  unfold myRawColor
  split_ifs with h
  · exact hd v
  · exact h

private theorem myRawColor_ne_of_adj {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (d : Option (V × Bool) → Fin (k + 1)) (j : Fin (k + 1))
    (hdprop : ∀ {x y : Option (V × Bool)}, myAdj G x y → d x ≠ d y)
    {u v : V} (huv : G.Adj u v) :
    myRawColor d j u ≠ myRawColor d j v := by
  unfold myRawColor
  split_ifs with hu hv
  · exact False.elim ((hdprop (myAdj_of00 huv)) (hu.trans hv.symm))
  · exact hdprop (myAdj_of10 huv)
  · exact hdprop (myAdj_of01 huv)
  · exact hdprop (myAdj_of00 huv)

private theorem myColorable_up {V : Type*} (G : SimpleGraph V) {m : ℕ}
    (c : G.Coloring (Fin m)) : (myGraph G).Colorable (m + 1) := by
  have hcprop : ∀ {v u : V}, G.Adj v u → c v ≠ c u := by
    intro v u h
    have h2 := c.map_rel' h
    rwa [completeGraph_adj_iff] at h2
  refine ⟨⟨fun x => match x with | some (v, _) => Fin.castSucc (c v) | none => Fin.last m, ?_⟩⟩
  intro x y hxy
  have hxy' : myAdj G x y := hxy
  rw [completeGraph_adj_iff]
  simp only [myAdj] at hxy'
  rcases hxy' with ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ |
    ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
  · dsimp only
    exact mt Fin.castSucc_inj.mp (hcprop h)
  · dsimp only
    exact mt Fin.castSucc_inj.mp (hcprop h)
  · dsimp only
    exact mt Fin.castSucc_inj.mp (hcprop h)
  · dsimp only
    exact Fin.castSucc_ne_last _
  · dsimp only
    exact Ne.symm (Fin.castSucc_ne_last _)

private theorem myColorable_down {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (d : (myGraph G).Coloring (Fin (k + 1))) : G.Colorable k := by
  have hdprop : ∀ {x y : Option (V × Bool)}, myAdj G x y → d x ≠ d y := by
    intro x y h
    have h2 := d.map_rel' h
    rwa [completeGraph_adj_iff] at h2
  have hcard : Fintype.card ↥(Finset.univ.erase (d none)) = k := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨fun v => e ⟨myRawColor (⇑d) (d none) v, ?_⟩, ?_⟩⟩
  · rw [Finset.mem_erase]
    exact ⟨myRawColor_ne (⇑d) (d none) (fun v => hdprop (myAdj_sh_ad v)) v, Finset.mem_univ _⟩
  · intro u v huv
    rw [completeGraph_adj_iff]
    intro hcon
    exact myRawColor_ne_of_adj (⇑d) (d none) hdprop huv (congrArg Subtype.val (e.injective hcon))

private theorem myCliqueFree {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 3) : (myGraph G).CliqueFree 3 := by
  have hdec := Classical.decEq V
  intro s hs
  obtain ⟨hclique, hcard⟩ := hs
  obtain ⟨a, b, c, habne, hacne, hbcne, rfl⟩ := Finset.card_eq_three.mp hcard
  have ha_mem : a ∈ (↑({a, b, c} : Finset (Option (V × Bool))) : Set _) :=
    Finset.mem_coe.mpr (Finset.mem_insert_self a {b, c})
  have hb_mem : b ∈ (↑({a, b, c} : Finset (Option (V × Bool))) : Set _) :=
    Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self b {c}))
  have hc_mem : c ∈ (↑({a, b, c} : Finset (Option (V × Bool))) : Set _) :=
    Finset.mem_coe.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c)))
  have hab : myAdj G a b := hclique ha_mem hb_mem habne
  have hac : myAdj G a c := hclique ha_mem hc_mem hacne
  have hbc : myAdj G b c := hclique hb_mem hc_mem hbcne
  have hane : a ≠ none := by
    intro h
    subst h
    obtain ⟨vb, rfl⟩ := myAdj_apex_left hab
    obtain ⟨vc, rfl⟩ := myAdj_apex_left hac
    exact myAdj_no_ss hbc
  have hbne : b ≠ none := by
    intro h
    subst h
    obtain ⟨va, rfl⟩ := myAdj_apex_right hab
    obtain ⟨vc, rfl⟩ := myAdj_apex_left hbc
    exact myAdj_no_ss hac
  have hcne : c ≠ none := by
    intro h
    subst h
    obtain ⟨va, rfl⟩ := myAdj_apex_right hac
    obtain ⟨vb, rfl⟩ := myAdj_apex_right hbc
    exact myAdj_no_ss hab
  obtain ⟨va, ia, rfl⟩ := myDesome hane
  obtain ⟨vb, ib, rfl⟩ := myDesome hbne
  obtain ⟨vc, ic, rfl⟩ := myDesome hcne
  have gab : G.Adj va vb := myAdj_to_G hab
  have gac : G.Adj va vc := myAdj_to_G hac
  have gbc : G.Adj vb vc := myAdj_to_G hbc
  have hvv01 : va ≠ vb := fun h => G.loopless.irrefl _ (h ▸ gab)
  have hvv02 : va ≠ vc := fun h => G.loopless.irrefl _ (h ▸ gac)
  have hvv12 : vb ≠ vc := fun h => G.loopless.irrefl _ (h ▸ gbc)
  have hcliqueG : G.IsClique (↑({va, vb, vc} : Finset V) : Set V) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact gab
    · exact gac
    · exact G.symm.symm _ _ gab
    · exact (hxy rfl).elim
    · exact gbc
    · exact G.symm.symm _ _ gac
    · exact G.symm.symm _ _ gbc
    · exact (hxy rfl).elim
  have hcardG : ({va, vb, vc} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨va, vb, vc, hvv01, hvv02, hvv12, rfl⟩
  exact hG {va, vb, vc} ⟨hcliqueG, hcardG⟩

private theorem myStep0.{u} {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      G ⊑ H ∧
        Fintype.card V < Fintype.card W ∧
          (G.CliqueFree 3 → H.CliqueFree 3) ∧
          (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1) := by
  refine ⟨Option (V × Bool), inferInstance, myGraph G, ⟨myCopy G⟩, ?_, ?_, ?_⟩
  · have hcard : Fintype.card (Option (V × Bool)) = Fintype.card V * 2 + 1 := by
      rw [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
    omega
  · exact myCliqueFree G
  · intro hGne
    have hm : G.chromaticNumber = ↑(G.chromaticNumber.toNat) := (ENat.natCast_toNat hGne).symm
    obtain ⟨c⟩ := SimpleGraph.colorable_of_chromaticNumber_ne_top hGne
    have hup : (myGraph G).chromaticNumber ≤ ↑(G.chromaticNumber.toNat + 1) :=
      (myColorable_up G c).chromaticNumber_le
    obtain ⟨d⟩ := SimpleGraph.colorable_chromaticNumber_of_fintype (myGraph G)
    have hHne : (myGraph G).chromaticNumber ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) SimpleGraph.chromaticNumber_le_card
    have ht0 : (myGraph G).chromaticNumber.toNat ≠ 0 := by
      intro hcon
      rw [hcon] at d
      exact Fin.elim0 (d none)
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_one_of_ne_zero ht0
    have dt : (myGraph G).Coloring (Fin (t + 1)) := by
      rw [← ht]
      exact d
    have hdown : G.Colorable t := myColorable_down G dt
    have hlow : G.chromaticNumber ≤ ↑t := hdown.chromaticNumber_le
    have hmt : G.chromaticNumber.toNat ≤ t := by
      rw [hm] at hlow
      exact Nat.cast_le.mp hlow
    have hfin : ((G.chromaticNumber.toNat + 1 : ℕ) : ℕ∞) ≤ ↑(t + 1) :=
      Nat.cast_le.mpr (Nat.succ_le_succ hmt)
    have hHcast : ((t + 1 : ℕ) : ℕ∞) = (myGraph G).chromaticNumber := by
      rw [← ht]
      exact ENat.natCast_toNat hHne
    have ecast : ((G.chromaticNumber.toNat + 1 : ℕ) : ℕ∞) = ↑G.chromaticNumber.toNat + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have e2 : ((G.chromaticNumber.toNat + 1 : ℕ) : ℕ∞) ≤ (myGraph G).chromaticNumber := by
      rw [← hHcast]
      exact hfin
    rw [hm, ← ecast]
    exact le_antisymm hup e2

private def mapGraph {A : Type*} {B : Type*} (e : A ≃ B) (G : SimpleGraph A) : SimpleGraph B where
  Adj a b := G.Adj (e.symm a) (e.symm b)
  symm := ⟨fun _ _ h => G.symm.symm _ _ h⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩

private def isoMap {A : Type*} {B : Type*} (e : A ≃ B) (G : SimpleGraph A) :
    G ≃g mapGraph e G :=
  ⟨e, fun {a b} => by
    change G.Adj (e.symm (e a)) (e.symm (e b)) ↔ G.Adj a b
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]⟩

private def copyOfIso {V : Type*} {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : G.Copy H :=
  SimpleGraph.Copy.mk ⟨f.toEquiv.toFun, fun h => f.map_rel_iff'.mpr h⟩ f.toEquiv.injective

private theorem myStepU.{u_1, u_2} {V : Type u_1} [Fintype V] (G : SimpleGraph V) :
    ∃ (W : Type u_2) (_ : Fintype W) (H : SimpleGraph W),
      G ⊑ H ∧
        Fintype.card V < Fintype.card W ∧
          (G.CliqueFree 3 → H.CliqueFree 3) ∧
          (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1) := by
  have e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  obtain ⟨W0, hW0, H0, emb0, card0, free0, chrom0⟩ := myStep0 (mapGraph e G)
  have e2 : W0 ≃ ULift W0 := Equiv.ulift.symm
  refine ⟨ULift W0, inferInstance, mapGraph e2 H0, ?_, ?_, ?_, ?_⟩
  · exact SimpleGraph.IsContained.trans
      (SimpleGraph.IsContained.trans ⟨copyOfIso (isoMap e G)⟩ emb0) ⟨copyOfIso (isoMap e2 H0)⟩
  · have hc1 : Fintype.card V = Fintype.card (Fin (Fintype.card V)) := Fintype.card_congr e
    have hc2 : Fintype.card W0 = Fintype.card (ULift W0) := Fintype.card_congr e2
    omega
  · intro hG
    have hG0 : (mapGraph e G).CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap ⟨copyOfIso (isoMap e G).symm⟩ hG
    exact SimpleGraph.CliqueFree.comap ⟨copyOfIso (isoMap e2 H0).symm⟩ (free0 hG0)
  · intro hGne
    have chromG0 : (mapGraph e G).chromaticNumber = G.chromaticNumber :=
      (SimpleGraph.chromaticNumber_congr (isoMap e G)).symm
    have hG0ne : (mapGraph e G).chromaticNumber ≠ ⊤ := by
      rw [chromG0]
      exact hGne
    have chromH : (mapGraph e2 H0).chromaticNumber = H0.chromaticNumber :=
      (SimpleGraph.chromaticNumber_congr (isoMap e2 H0)).symm
    rw [chromH, chrom0 hG0ne, chromG0]

private theorem myKey.{u} (n : ℕ) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      H.CliqueFree 3 ∧ H.chromaticNumber = ↑n := by
  induction n with
  | zero =>
    refine ⟨ULift Empty, inferInstance, ⊥, ?_, ?_⟩
    · apply SimpleGraph.cliqueFree_of_card_lt
      have hcc : Fintype.card (ULift Empty) = Fintype.card Empty := Fintype.card_congr Equiv.ulift
      rw [hcc, Fintype.card_empty]
      decide
    · simp
  | succ n ih =>
    obtain ⟨V, hV, G, hfree, hchi⟩ := ih
    obtain ⟨W, hW, H, _, _, hfreeH, hchiH⟩ := myStep0 G
    have hne : G.chromaticNumber ≠ ⊤ := by
      rw [hchi]
      exact ENat.natCast_ne_top n
    refine ⟨W, hW, H, hfreeH hfree, ?_⟩
    rw [hchiH hne, hchi, Nat.cast_add, Nat.cast_one]

/-- **Mycielski's theorem.** Write $\chi(G)$ for the chromatic number of a simple graph $G$. For
every simple graph $G$ on a finite vertex set there is a simple graph $H$ on a finite vertex set
with strictly more vertices than $G$ that contains a subgraph isomorphic to $G$, such that $H$ is
triangle-free whenever $G$ is, and such that $\chi(H) = \chi(G) + 1$ whenever $\chi(G)$ is
finite. Moreover, for every natural number $k$ there is a triangle-free simple graph $H$ on a
finite vertex set with $\chi(H) \ge k$.

The explicit Mycielski construction is abstracted here to the existence of such a graph $H$.

Proves `Wanted` entry `mycielski_theorem`.

Source: J. Mycielski, "Sur le coloriage des graphes" (1955),
https://doi.org/10.4064/cm-3-2-161-162 (statement ID `mycielski-theorem-s1`).
-/
theorem mycielski_theorem :
    (∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
        G ⊑ H ∧
          Fintype.card V < Fintype.card W ∧
              (G.CliqueFree 3 → H.CliqueFree 3) ∧
                (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1)) ∧
    ∀ (k : ℕ), ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
      H.CliqueFree 3 ∧ (↑k ≤ H.chromaticNumber) := by
  constructor
  · intro V hV G
    exact myStepU G
  · intro k
    obtain ⟨W, hW, H, hfree, hchi⟩ := myKey k
    exact ⟨W, hW, H, hfree, hchi.ge⟩

end MetaMathlibExt
