/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Total descents over all parking functions
-/
/-! ## Helpers for the Pollak circle argument and descent counting -/

/-- Circle embedding of a preference function. -/
private def emb (n : ℕ) (f : Fin n → Fin n) : Fin n → ZMod (n + 1) :=
  fun i => ((f i).val : ZMod (n + 1))

/-- Simultaneous rotation of all preferences on the circle. -/
private def shift (n : ℕ) (a : Fin n → ZMod (n + 1)) (c : ZMod (n + 1)) :
    Fin n → ZMod (n + 1) :=
  fun i => a i + c

private def pfSet (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter (IsParkingFunction n)

private theorem mem_pfSet (n : ℕ) (f : Fin n → Fin n) :
    f ∈ pfSet n ↔ IsParkingFunction n f := by
  unfold pfSet
  simp

private theorem emb_injective (n : ℕ) : Function.Injective (emb n) := by
  intro f g h
  funext i
  have hi : ((f i).val : ZMod (n + 1)) = ((g i).val : ZMod (n + 1)) := congrFun h i
  have e : ((f i).val : ZMod (n + 1)).val = ((g i).val : ZMod (n + 1)).val := by
    rw [hi]
  rw [ZMod.val_natCast_of_lt (by have hlt := (f i).isLt; omega),
    ZMod.val_natCast_of_lt (by have hlt := (g i).isLt; omega)] at e
  exact Fin.ext e

/-- Value of a shifted circle point. -/
private theorem val_add_cast (n t : ℕ) (ht : t < n + 1) (u : ZMod (n + 1)) :
    (u + (t : ZMod (n + 1))).val = (u.val + t) % (n + 1) := by
  rw [ZMod.val_add, ZMod.val_natCast_of_lt ht]

/-- Shifting every coordinate by `t` moves total weight predictably:
the new sum plus the wrapped mass equals the old sum plus `n * t`. -/
private theorem sum_mod_eq (n t : ℕ) (u v : Fin n → ℕ) (hu : ∀ i, u i < n + 1)
    (ht : t < n + 1) (h : ∀ i, v i = (u i + t) % (n + 1)) :
    (∑ i, v i) + (Finset.univ.filter (fun i => n + 1 ≤ u i + t)).card * (n + 1)
      = (∑ i, u i) + n * t := by
  have hterm : ∀ i : Fin n, v i + (if n + 1 ≤ u i + t then (n + 1) else 0)
      = u i + t := by
    intro i
    rw [h i]
    have hx : u i + t < 2 * (n + 1) := by
      have hui := hu i
      omega
    split_ifs with hc
    · have hlo : u i + t - (n + 1) < n + 1 := by omega
      rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt hlo]
      omega
    · have hlo : u i + t < n + 1 := by omega
      rw [Nat.mod_eq_of_lt hlo]
      omega
  have hsum : (∑ i : Fin n, (v i + (if n + 1 ≤ u i + t then (n + 1) else 0)))
      = ∑ i : Fin n, (u i + t) :=
    Finset.sum_congr rfl (fun i _ => hterm i)
  rw [Finset.sum_add_distrib] at hsum
  have hrhs : (∑ i : Fin n, (u i + t)) = (∑ i, u i) + n * t := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have hfil : (∑ i : Fin n, (if n + 1 ≤ u i + t then (n + 1) else 0))
      = (Finset.univ.filter (fun i => n + 1 ≤ u i + t)).card * (n + 1) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [hfil, hrhs] at hsum
  exact hsum

/-- A shift minimizing the total lifted weight exists. -/
private theorem exists_min_shift (n : ℕ) (a : Fin n → ZMod (n + 1)) :
    ∃ c : ZMod (n + 1), ∀ d : ZMod (n + 1),
      (∑ i, (a i + c).val) ≤ ∑ i, (a i + d).val := by
  obtain ⟨c, _, hc⟩ := Finset.exists_min_image Finset.univ
    (fun c => ∑ i, (a i + c).val) ⟨0, Finset.mem_univ 0⟩
  exact ⟨c, fun d => hc d (Finset.mem_univ d)⟩

-- Pollak's circle lemma, existence half (the combinatorial core)
private theorem pollak_exists (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ZMod (n + 1)) :
    ∃ c : ZMod (n + 1), ∃ f : Fin n → Fin n,
      IsParkingFunction n f ∧ shift n a c = emb n f := by
  obtain ⟨c, hc⟩ := exists_min_shift n a
  have h1lt : (1 : ℕ) < n + 1 := by omega
  have hno : ∀ i : Fin n, (a i + c).val < n := by
    by_contra hcon
    obtain ⟨i, hi⟩ := not_forall.mp hcon
    have hieq : (a i + c).val = n := by
      have h2 := ZMod.val_lt (a i + c)
      omega
    have hmem : i ∈ Finset.univ.filter (fun j => n + 1 ≤ (a j + c).val + 1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hcard : 1
        ≤ (Finset.univ.filter (fun j => n + 1 ≤ (a j + c).val + 1)).card :=
      Finset.card_pos.mpr ⟨i, hmem⟩
    have hvv : ∀ j : Fin n, (a j + (c + (1 : ZMod (n + 1)))).val
        = ((a j + c).val + 1) % (n + 1) := by
      intro j
      rw [← add_assoc]
      exact val_add_cast n 1 h1lt _
    have hshift : (∑ j, (a j + (c + (1 : ZMod (n + 1)))).val)
        + (Finset.univ.filter (fun j => n + 1 ≤ (a j + c).val + 1)).card * (n + 1)
        = (∑ j, (a j + c).val) + n * 1 :=
      sum_mod_eq n 1 (fun j => (a j + c).val)
        (fun j => (a j + (c + (1 : ZMod (n + 1)))).val)
        (fun j => ZMod.val_lt _) h1lt hvv
    have hle : (∑ j, (a j + c).val)
        ≤ ∑ j, (a j + (c + (1 : ZMod (n + 1)))).val :=
      hc _
    have hA : n + 1
        ≤ (Finset.univ.filter (fun j => n + 1 ≤ (a j + c).val + 1)).card * (n + 1) := by
      have e := Nat.mul_le_mul_right (n + 1) hcard
      rwa [one_mul] at e
    omega
  set f : Fin n → Fin n := fun i => ⟨(a i + c).val, by
    have hbi := hno i
    omega⟩ with hfdef
  have hfv : ∀ i : Fin n, (f i).val = (a i + c).val := by
    intro i
    simp only [hfdef]
  have hpf : IsParkingFunction n f := by
    rw [isParkingFunction_iff_card_filter_le]
    intro k
    by_contra hcon
    have hcard_le : (Finset.univ.filter (fun i : Fin n => f i ≤ k)).card ≤ k.val := by
      omega
    set t' := n - k.val with ht'def
    have hklt : k.val < n := k.isLt
    have ht'1 : 1 ≤ t' := by omega
    have ht'2 : t' < n + 1 := by omega
    have hsub : Finset.univ.filter (fun i : Fin n => ¬ f i ≤ k)
        ⊆ Finset.univ.filter (fun i => n + 1 ≤ (a i + c).val + t') := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have h1 : k.val < (f i).val := by
        have hlen : ¬ (f i).val ≤ k.val := by
          intro hle
          exact hi (Fin.le_def.mpr hle)
        omega
      have h2 : k.val < (a i + c).val := by
        rw [← hfv i]
        exact h1
      omega
    have huniv : (Finset.univ : Finset (Fin n)).card = n := by
      rw [Finset.card_univ, Fintype.card_fin]
    have hcompl : (Finset.univ.filter (fun i : Fin n => f i ≤ k)).card
        + (Finset.univ.filter (fun i : Fin n => ¬ f i ≤ k)).card = n := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => f i ≤ k)
      rw [huniv] at h
      exact h
    have hm : t'
        ≤ (Finset.univ.filter (fun i => n + 1 ≤ (a i + c).val + t')).card := by
      have h1 := Finset.card_le_card hsub
      omega
    have hvv : ∀ j : Fin n, (a j + (c + (t' : ZMod (n + 1)))).val
        = ((a j + c).val + t') % (n + 1) := by
      intro j
      rw [← add_assoc]
      exact val_add_cast n t' ht'2 _
    have hshift : (∑ j, (a j + (c + (t' : ZMod (n + 1)))).val)
        + (Finset.univ.filter (fun j => n + 1 ≤ (a j + c).val + t')).card * (n + 1)
        = (∑ j, (a j + c).val) + n * t' :=
      sum_mod_eq n t' (fun j => (a j + c).val)
        (fun j => (a j + (c + (t' : ZMod (n + 1)))).val)
        (fun j => ZMod.val_lt _) ht'2 hvv
    have hle : (∑ j, (a j + c).val)
        ≤ ∑ j, (a j + (c + (t' : ZMod (n + 1)))).val :=
      hc _
    have e1 : t' * (n + 1)
        ≤ (Finset.univ.filter (fun i => n + 1 ≤ (a i + c).val + t')).card * (n + 1) :=
      Nat.mul_le_mul_right _ hm
    have e2 : t' * (n + 1) = t' * n + t' := by ring
    have e3 : n * t' = t' * n := mul_comm _ _
    omega
  refine ⟨c, f, hpf, ?_⟩
  funext i
  change a i + c = ((f i).val : ZMod (n + 1))
  rw [hfv i]
  exact (ZMod.natCast_zmod_val _).symm

/-- Shifting a parking function by a nonzero constant strictly increases
the total lifted weight. -/
private theorem sum_lt_of_shift (n : ℕ) (f₁ f₂ : Fin n → Fin n)
    (h₁ : IsParkingFunction n f₁) (d : ZMod (n + 1)) (hd : d ≠ 0)
    (h : ∀ i, ((f₂ i).val : ZMod (n + 1)) = ((f₁ i).val : ZMod (n + 1)) + d) :
    (∑ i, (f₁ i).val) < ∑ i, (f₂ i).val := by
  set t := d.val with htdef
  have ht2 : t < n + 1 := ZMod.val_lt d
  have ht1 : 1 ≤ t := by
    have hne : d.val ≠ 0 := fun hz => hd ((ZMod.val_eq_zero d).mp hz)
    omega
  have hpt : ∀ i, (f₂ i).val = ((f₁ i).val + t) % (n + 1) := by
    intro i
    have gi := h i
    have hvd : d = ((t : ℕ) : ZMod (n + 1)) := (ZMod.natCast_zmod_val d).symm
    have lhs : (((f₂ i).val : ZMod (n + 1))).val = (f₂ i).val :=
      ZMod.val_natCast_of_lt (by have hlt := (f₂ i).isLt; omega)
    have rhs : (((f₁ i).val : ZMod (n + 1)) + ((t : ℕ) : ZMod (n + 1))).val
        = ((f₁ i).val + t) % (n + 1) := by
      have h1 := val_add_cast n t ht2 ((f₁ i).val : ZMod (n + 1))
      rwa [ZMod.val_natCast_of_lt (by have hlt := (f₁ i).isLt; omega)] at h1
    rw [hvd] at gi
    have g2 := congrArg ZMod.val gi
    rw [lhs, rhs] at g2
    exact g2
  have hsum : (∑ i, (f₂ i).val)
      + (Finset.univ.filter (fun i => n + 1 ≤ (f₁ i).val + t)).card * (n + 1)
      = (∑ i, (f₁ i).val) + n * t :=
    sum_mod_eq n t (fun i => (f₁ i).val) (fun i => (f₂ i).val)
      (fun i => by have hlt := (f₁ i).isLt; omega) ht2 hpt
  have hk0lt : n - t < n := by omega
  set k₀ : Fin n := ⟨n - t, hk0lt⟩ with hk0def
  have hk0v : k₀.val = n - t := rfl
  have hpf1 := ((isParkingFunction_iff_card_filter_le n f₁).mp h₁) k₀
  have hcompl : (Finset.univ.filter (fun i : Fin n => f₁ i ≤ k₀)).card
      + (Finset.univ.filter (fun i : Fin n => ¬ f₁ i ≤ k₀)).card = n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => f₁ i ≤ k₀)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hsub : Finset.univ.filter (fun i => n + 1 ≤ (f₁ i).val + t)
      ⊆ Finset.univ.filter (fun i : Fin n => ¬ f₁ i ≤ k₀) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hle
    have hle2 : (f₁ i).val ≤ k₀.val := Fin.le_def.mp hle
    omega
  have hm : (Finset.univ.filter (fun i => n + 1 ≤ (f₁ i).val + t)).card ≤ t - 1 := by
    have h1 := Finset.card_le_card hsub
    omega
  have e1 : (Finset.univ.filter (fun i => n + 1 ≤ (f₁ i).val + t)).card * (n + 1)
      ≤ (t - 1) * (n + 1) := Nat.mul_le_mul_right _ hm
  have e2 : (t - 1) * (n + 1) = (t - 1) * n + (t - 1) := by ring
  have e3 : n * t = (t - 1) * n + n := by
    have hte : t = (t - 1) + 1 := by omega
    conv_lhs => rw [hte]
    ring
  omega

-- Pollak's circle lemma, uniqueness half
private theorem pollak_unique (n : ℕ) (_hn : 1 ≤ n) (a : Fin n → ZMod (n + 1))
    (c₁ c₂ : ZMod (n + 1)) (f₁ f₂ : Fin n → Fin n)
    (h₁ : IsParkingFunction n f₁) (h₂ : IsParkingFunction n f₂)
    (e₁ : shift n a c₁ = emb n f₁) (e₂ : shift n a c₂ = emb n f₂) :
    c₁ = c₂ := by
  by_contra hne
  have hd : c₂ - c₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hd2 : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  have h12 : ∀ i, ((f₂ i).val : ZMod (n + 1))
      = ((f₁ i).val : ZMod (n + 1)) + (c₂ - c₁) := by
    intro i
    have g₁ : a i + c₁ = ((f₁ i).val : ZMod (n + 1)) := congrFun e₁ i
    have g₂ : a i + c₂ = ((f₂ i).val : ZMod (n + 1)) := congrFun e₂ i
    have e : (a i + c₁) + (c₂ - c₁) = a i + c₂ := by abel
    rw [g₁] at e
    rw [g₂] at e
    exact e.symm
  have h21 : ∀ i, ((f₁ i).val : ZMod (n + 1))
      = ((f₂ i).val : ZMod (n + 1)) + (c₁ - c₂) := by
    intro i
    have g₁ : a i + c₁ = ((f₁ i).val : ZMod (n + 1)) := congrFun e₁ i
    have g₂ : a i + c₂ = ((f₂ i).val : ZMod (n + 1)) := congrFun e₂ i
    have e : (a i + c₂) + (c₁ - c₂) = a i + c₁ := by abel
    rw [g₂] at e
    rw [g₁] at e
    exact e.symm
  have l1 := sum_lt_of_shift n f₁ f₂ h₁ (c₂ - c₁) hd h12
  have l2 := sum_lt_of_shift n f₂ f₁ h₂ (c₁ - c₂) hd2 h21
  omega

/-- Pollak enumeration of parking functions. -/
private theorem card_pfSet_pos (n : ℕ) (hn : 1 ≤ n) :
    (pfSet n).card = (n + 1) ^ (n - 1) := by
  choose c f hf using pollak_exists n hn
  let e : (Fin n → ZMod (n + 1)) ≃ (↥(pfSet n) × ZMod (n + 1)) :=
    { toFun := fun a => (⟨f a, (mem_pfSet n _).mpr (hf a).1⟩, c a)
      invFun := fun p => shift n (emb n p.1.1) (-p.2)
      left_inv := by
        intro a
        change shift n (emb n (f a)) (-(c a)) = a
        rw [← (hf a).2]
        funext i
        change (a i + c a) + -(c a) = a i
        abel
      right_inv := by
        rintro ⟨g, d⟩
        set X : Fin n → ZMod (n + 1) := shift n (emb n g.1) (-d) with hX
        have hgood : shift n X d = emb n g.1 := by
          rw [hX]
          funext i
          change ((emb n g.1 i + -d) + d) = emb n g.1 i
          abel
        have huniq : d = c X :=
          pollak_unique n hn X d (c X) g.1 (f X)
            ((mem_pfSet n _).mp g.2) (hf X).1 hgood (hf X).2
        have hembeq : emb n (f X) = emb n g.1 := by
          rw [← (hf X).2, ← huniq]
          exact hgood
        have hfeq : f X = g.1 := emb_injective n hembeq
        change ((⟨f X, (mem_pfSet n _).mpr (hf X).1⟩ : ↥(pfSet n)), c X) = (g, d)
        refine Prod.ext ?_ ?_
        · exact Subtype.ext hfeq
        · exact huniq.symm }
  have hcardA : Fintype.card (Fin n → ZMod (n + 1)) = (n + 1) ^ n := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcardB : Fintype.card (↥(pfSet n) × ZMod (n + 1))
      = (pfSet n).card * (n + 1) := by
    rw [Fintype.card_prod, Fintype.card_coe, ZMod.card]
  have hcongr := Fintype.card_congr e
  rw [hcardA, hcardB] at hcongr
  have hpow : (n + 1) ^ n = (n + 1) ^ (n - 1) * (n + 1) := by
    have hnm : n - 1 + 1 = n := by omega
    calc (n + 1) ^ n = (n + 1) ^ (n - 1 + 1) := by rw [hnm]
      _ = (n + 1) ^ (n - 1) * (n + 1) := by rw [pow_succ]
  rw [hpow] at hcongr
  exact (Nat.mul_right_cancel (Nat.succ_pos _) hcongr).symm

private theorem card_pfSet (n : ℕ) : (pfSet n).card = (n + 1) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hfil : pfSet 0 = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro f _ k
      have h := k.isLt
      omega
    rw [hfil, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    simp
  · exact card_pfSet_pos n hpos

/-- Parking functions with two prescribed equal coordinates, general points. -/
private theorem card_diag_aux (n : ℕ) (hn : 2 ≤ n) (z0 z1 : Fin n)
    (hz0 : z0.val = 0) (hz1 : z1.val = 1) :
    ((pfSet n).filter (fun f => f z0 = f z1)).card = (n + 1) ^ (n - 2) := by
  choose c f hf using pollak_exists n (by omega)
  let e1 : ↥(Finset.univ.filter (fun a : Fin n → ZMod (n + 1) => a z0 = a z1)) ≃
      (↥((pfSet n).filter (fun f => f z0 = f z1)) × ZMod (n + 1)) :=
    { toFun := fun p =>
        ((⟨f p.val, Finset.mem_filter.mpr
          ⟨(mem_pfSet n _).mpr (hf p.val).1, by
            have g0 : p.val z0 + c p.val = emb n (f p.val) z0 :=
              congrFun (hf p.val).2 z0
            have g1 : p.val z1 + c p.val = emb n (f p.val) z1 :=
              congrFun (hf p.val).2 z1
            have ha0 : p.val z0 = p.val z1 :=
              (Finset.mem_filter.mp p.2).2
            have e : emb n (f p.val) z0 = emb n (f p.val) z1 := by
              rw [← g0, ← g1, ha0]
            have ev : ((f p.val z0).val : ℕ) = ((f p.val z1).val : ℕ) := by
              have hcc := congrArg ZMod.val e
              simp only [emb] at hcc
              rwa [ZMod.val_natCast_of_lt (by have hlt := (f p.val z0).isLt; omega),
                ZMod.val_natCast_of_lt (by have hlt := (f p.val z1).isLt; omega)] at hcc
            exact Fin.ext ev⟩⟩ :
          ↥((pfSet n).filter (fun f => f z0 = f z1))), c p.val)
      invFun := fun p =>
        (⟨fun i => emb n p.1.1 i - p.2, by
          have hff : p.1.1 z0 = p.1.1 z1 :=
            (Finset.mem_filter.mp p.1.2).2
          have e01 : emb n p.1.1 z0 = emb n p.1.1 z1 := by
            change (((p.1.1 z0).val : ℕ) : ZMod (n + 1))
              = (((p.1.1 z1).val : ℕ) : ZMod (n + 1))
            rw [hff]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          change emb n p.1.1 z0 - p.2 = emb n p.1.1 z1 - p.2
          rw [e01]⟩ :
          ↥(Finset.univ.filter (fun a : Fin n → ZMod (n + 1) => a z0 = a z1)))
      left_inv := by
        rintro ⟨a, ha⟩
        refine Subtype.ext ?_
        funext i
        change emb n (f a) i - c a = a i
        have h2 : a i + c a = emb n (f a) i := congrFun (hf a).2 i
        rw [← h2]
        abel
      right_inv := by
        rintro ⟨⟨g, hg⟩, d⟩
        have e₂ : (fun i => (emb n g i - d) + d) = emb n g := by
          funext i
          show (emb n g i - d) + d = emb n g i
          abel
        have huniq : c (fun i => emb n g i - d) = d :=
          pollak_unique n (by omega) _ _ _ _ _ (hf _).1
            ((mem_pfSet n _).mp (Finset.mem_filter.mp hg).1)
            (hf _).2 e₂
        have hembeq : emb n (f (fun i => emb n g i - d)) = emb n g := by
          have h1 := (hf (fun i => emb n g i - d)).2
          rw [huniq] at h1
          exact h1.symm.trans e₂
        have hfeq : f (fun i => emb n g i - d) = g := emb_injective n hembeq
        have hmem' : f (fun i => emb n g i - d)
            ∈ (pfSet n).filter (fun f => f z0 = f z1) := by
          rw [hfeq]
          exact hg
        have hpair : ((⟨f (fun i => emb n g i - d), hmem'⟩ :
            ↥((pfSet n).filter (fun f => f z0 = f z1))),
            c (fun i => emb n g i - d))
            = ((⟨g, hg⟩ : ↥((pfSet n).filter (fun f => f z0 = f z1))), d) := by
          refine Prod.ext ?_ ?_
          · exact Subtype.ext hfeq
          · exact huniq
        exact hpair }
  let e2 : ↥(Finset.univ.filter (fun a : Fin n → ZMod (n + 1) => a z0 = a z1)) ≃
      (Fin (n - 1) → ZMod (n + 1)) :=
    { toFun := fun p i => p.val ⟨i.val + 1, by
        have hi := i.isLt
        omega⟩
      invFun := fun b => ⟨fun j => b ⟨j.val - 1, by
        have hj := j.isLt
        omega⟩, by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have h01 : (⟨z0.val - 1, by omega⟩ : Fin (n - 1))
            = ⟨z1.val - 1, by omega⟩ := by
          simp only [Fin.mk.injEq]
          omega
        change b ⟨z0.val - 1, by omega⟩ = b ⟨z1.val - 1, by omega⟩
        rw [h01]⟩
      left_inv := by
        rintro ⟨a, ha⟩
        have ha0 : a z0 = a z1 := (Finset.mem_filter.mp ha).2
        refine Subtype.ext ?_
        funext j
        have hjlt := j.isLt
        change a ⟨(j.val - 1) + 1, by omega⟩ = a j
        by_cases hj : j = z0
        · have h1 : (j.val - 1) + 1 = z1.val := by
            have hjv : j.val = z0.val := congrArg Fin.val hj
            rw [hjv, hz0, hz1]
          rw [show (⟨(j.val - 1) + 1, by omega⟩ : Fin n) = z1 from Fin.ext h1]
          rw [hj]
          exact ha0.symm
        · have h1 : (j.val - 1) + 1 = j.val := by
            have hjv : j.val ≠ 0 := fun hz => hj (Fin.ext (by rw [hz, hz0]))
            omega
          rw [show (⟨(j.val - 1) + 1, by omega⟩ : Fin n) = j from Fin.ext h1]
      right_inv := by
        intro b
        funext i
        change b ⟨(i.val + 1) - 1, by omega⟩ = b i
        have h1 : (⟨(i.val + 1) - 1, by omega⟩ : Fin (n - 1)) = i :=
          Fin.ext (Nat.add_sub_cancel _ _)
        rw [h1] }
  have hD1 := Fintype.card_congr e1
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, ZMod.card] at hD1
  have hD2 := Fintype.card_congr e2
  rw [Fintype.card_coe, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hD2
  have hE : ((pfSet n).filter (fun f => f z0 = f z1)).card * (n + 1)
      = (n + 1) ^ (n - 1) :=
    hD1.symm.trans hD2
  have hpow : (n + 1) ^ (n - 1) = (n + 1) ^ (n - 2) * (n + 1) := by
    have hn1 : n - 1 = (n - 2) + 1 := by omega
    conv_lhs => rw [hn1]
    rw [pow_succ]
  rw [hpow] at hE
  exact Nat.mul_right_cancel (Nat.succ_pos _) hE

private theorem card_diag (n : ℕ) (hn : 2 ≤ n) :
    ((pfSet n).filter
      (fun f => f (⟨0, by omega⟩ : Fin n) = f (⟨1, by omega⟩ : Fin n))).card
      = (n + 1) ^ (n - 2) :=
  card_diag_aux n hn _ _ rfl rfl

-- permutation invariance of the predicate
private theorem isPF_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    IsParkingFunction n (f ∘ σ) ↔ IsParkingFunction n f := by
  unfold IsParkingFunction IsPartialParkingFunction
  constructor
  · intro h k
    have hk := h k
    have heq : (Finset.univ.filter (fun i => k ≤ (f ∘ σ) i)).card =
        (Finset.univ.filter (fun i => k ≤ f i)).card := by
      apply Finset.card_bij (fun i _ => σ i)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hi
      · intro i _ _ _ hxy
        exact σ.injective hxy
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨σ.symm j, by simpa using hj, by simp⟩
    rw [heq] at hk
    exact hk
  · intro h k
    have hk := h k
    have heq : (Finset.univ.filter (fun i => k ≤ f i)).card =
        (Finset.univ.filter (fun i => k ≤ (f ∘ σ) i)).card := by
      apply Finset.card_bij (fun i _ => σ.symm i)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hi ⊢
        have : f (σ (σ.symm i)) = f i := by simp
        rw [this]
        exact hi
      · intro i _ _ _ hxy
        exact σ.symm.injective hxy
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hj ⊢
        exact ⟨σ j, by simpa using hj, by simp⟩
    rw [heq] at hk
    exact hk

-- descent predicate for one adjacent pair
private abbrev descentPair (n : ℕ) (f : Fin n → Fin n) (p : Fin n × Fin n) : Prop :=
  p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2

private abbrev adjPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1)

private abbrev fiber (n : ℕ) (p : Fin n × Fin n) : Finset (Fin n → Fin n) :=
  (pfSet n).filter (fun f => descentPair n f p)

-- double counting: LHS equals sum over pairs of fiber cards
private theorem sum_eq_sum_fiber (n : ℕ) :
    (∑ f : Fin n → Fin n, if IsParkingFunction n f then
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card
      else 0)
    = ∑ p : Fin n × Fin n, (fiber n p).card := by
  have step1 : ∀ f : Fin n → Fin n,
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card
      = ∑ p : Fin n × Fin n, (if descentPair n f p then 1 else 0) := by
    intro f
    have h : (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2))
        = Finset.univ.filter (descentPair n f) := rfl
    rw [h]
    exact Finset.card_filter (descentPair n f) Finset.univ
  calc (∑ f : Fin n → Fin n, if IsParkingFunction n f then
        (Finset.univ.filter
          (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card
        else 0)
      = ∑ f ∈ pfSet n, (Finset.univ.filter
          (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card := by
        exact (Finset.sum_filter _ _).symm
    _ = ∑ f ∈ pfSet n, ∑ p : Fin n × Fin n,
          (if descentPair n f p then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro f _
        exact step1 f
    _ = ∑ p : Fin n × Fin n, ∑ f ∈ pfSet n,
          (if descentPair n f p then 1 else 0) := Finset.sum_comm
    _ = ∑ p : Fin n × Fin n, (fiber n p).card := by
        apply Finset.sum_congr rfl
        intro p _
        exact (Finset.card_filter (fun f => descentPair n f p) (pfSet n)).symm

-- edge case: n ≤ 1, both sides vanish
private theorem D_eq_zero_of_le_one (n : ℕ) (hn : n ≤ 1) (f : Fin n → Fin n) :
    (Finset.univ.filter
      (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨h1, _⟩ := hp
  have h2 := p.1.isLt
  have h3 := p.2.isLt
  omega

private theorem lhs_eq_zero_of_le_one (n : ℕ) (hn : n ≤ 1) :
    (∑ f : Fin n → Fin n, if IsParkingFunction n f then
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card
      else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro f _
  have hD := D_eq_zero_of_le_one n hn f
  simp [hD]

private theorem rhs_eq_zero_of_le_one (n : ℕ) (hn : n ≤ 1) :
    Nat.choose n 2 * (n + 1) ^ (n - 2) = 0 := by
  have h : Nat.choose n 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h, Nat.zero_mul]

-- membership in a fiber, unfolded
private theorem mem_fiber (n : ℕ) (p : Fin n × Fin n) (f : Fin n → Fin n) :
    f ∈ fiber n p ↔ IsParkingFunction n f ∧ descentPair n f p := by
  simp [fiber, pfSet, Finset.mem_filter]

-- precomposition transfers one fiber to another
private theorem fiber_card_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin n))
    (a b : Fin n × Fin n)
    (h0 : σ a.1 = b.1) (h1 : σ a.2 = b.2)
    (hadj : a.2.1 = a.1.1 + 1) (hadjB : b.2.1 = b.1.1 + 1) :
    (fiber n b).card = (fiber n a).card := by
  apply Finset.card_bij (fun f _ => f ∘ σ)
  · intro f hf
    rw [mem_fiber] at hf ⊢
    obtain ⟨hfpf, _, hdesc⟩ := hf
    refine ⟨(isPF_comp_perm n σ f).mpr hfpf, hadj, ?_⟩
    change f (σ a.1) > f (σ a.2)
    rw [h0, h1]
    exact hdesc
  · intro f _ g _ hfg
    funext x
    have hx : (f ∘ σ) (σ.symm x) = (g ∘ σ) (σ.symm x) := congrFun hfg _
    simpa [Function.comp] using hx
  · intro g hg
    rw [mem_fiber] at hg
    obtain ⟨hgpf, hadjg, hdescg⟩ := hg
    refine ⟨g ∘ σ.symm, ?_, ?_⟩
    · rw [mem_fiber]
      have e0 : σ.symm b.1 = a.1 := by
        rw [Equiv.symm_apply_eq]
        exact h0.symm
      have e1 : σ.symm b.2 = a.2 := by
        rw [Equiv.symm_apply_eq]
        exact h1.symm
      refine ⟨(isPF_comp_perm n σ.symm g).mpr hgpf, hadjB, ?_⟩
      change g (σ.symm b.1) > g (σ.symm b.2)
      rw [e0, e1]
      exact hdescg
    · show (g ∘ σ.symm) ∘ σ = g
      funext x
      simp [Function.comp]

-- all adjacent positions carry the same descent count
private theorem fiber_eq_of_adj (n : ℕ) (hn : 2 ≤ n) (p : Fin n × Fin n)
    (hadj : p.2.1 = p.1.1 + 1) :
    (fiber n p).card =
      (fiber n ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))).card := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have hzo : (⟨0, h0⟩ : Fin n) ≠ (⟨1, h1⟩ : Fin n) :=
    Fin.ne_of_val_ne (by simp)
  have hz2 : (⟨0, h0⟩ : Fin n) ≠ p.2 := Fin.ne_of_val_ne (by simp; omega)
  have h21 : p.2 ≠ p.1 := Fin.ne_of_val_ne (by omega)
  have h01 : (⟨1, h1⟩ : Fin n) ≠ (⟨0, h0⟩ : Fin n) := Ne.symm hzo
  let s2 : Equiv.Perm (Fin n) := Equiv.swap (⟨1, h1⟩ : Fin n) p.2
  let s1 : Equiv.Perm (Fin n) := Equiv.swap (⟨0, h0⟩ : Fin n) p.1
  let σ : Equiv.Perm (Fin n) := s2.trans s1
  have hs2z : s2 (⟨0, h0⟩ : Fin n) = (⟨0, h0⟩ : Fin n) :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm h01) hz2
  have hs1p : s1 p.2 = p.2 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hz2) h21
  have hs1z : s1 (⟨0, h0⟩ : Fin n) = p.1 := Equiv.swap_apply_left _ _
  have hs2o : s2 (⟨1, h1⟩ : Fin n) = p.2 := Equiv.swap_apply_left _ _
  have hσ0 : σ (⟨0, h0⟩ : Fin n) = p.1 := by
    change s1 (s2 _) = _
    rw [hs2z, hs1z]
  have hσ1 : σ (⟨1, h1⟩ : Fin n) = p.2 := by
    change s1 (s2 _) = _
    rw [hs2o, hs1p]
  exact fiber_card_comp_perm n σ _ _ hσ0 hσ1 rfl hadj

-- the adjacent pairs are exactly n - 1 in number
private theorem card_adjPairs (n : ℕ) : (adjPairs n).card = n - 1 := by
  let toF : ↥(adjPairs n) → Fin (n - 1) := fun p => ⟨p.1.1.1, by
    have hadj := (Finset.mem_filter.mp p.2).2
    have hlt := p.1.2.isLt
    omega⟩
  let invF : Fin (n - 1) → ↥(adjPairs n) := fun i =>
    ⟨((⟨i.1, by have hlt := i.isLt; omega⟩ : Fin n),
      (⟨i.1 + 1, by have hlt := i.isLt; omega⟩ : Fin n)), by
      simp only [adjPairs, Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hleft : ∀ i, toF (invF i) = i := fun i => Fin.ext rfl
  have hright : ∀ p : ↥(adjPairs n), invF (toF p) = p := by
    intro p
    apply Subtype.ext
    have hadj := (Finset.mem_filter.mp p.2).2
    refine Prod.ext (Fin.ext rfl) (Fin.ext hadj.symm)
  have h : Fintype.card ↥(adjPairs n) = Fintype.card (Fin (n - 1)) :=
    Fintype.card_congr ⟨toF, invF, hright, hleft⟩
  rw [Fintype.card_coe, Fintype.card_fin] at h
  exact h

-- swapping two positions exchanges strict comparisons
private theorem card_swap_lt_gt (n : ℕ) (a b : Fin n) :
    ((pfSet n).filter (fun f => f a < f b)).card
      = ((pfSet n).filter (fun f => f a > f b)).card := by
  let s : Equiv.Perm (Fin n) := Equiv.swap a b
  have es0 : s a = b := Equiv.swap_apply_left a b
  have es1 : s b = a := Equiv.swap_apply_right a b
  apply Finset.card_bij (fun f _ => f ∘ s)
  · intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    obtain ⟨hfmem, hflt⟩ := hf
    have hpf : IsParkingFunction n f := by
      simpa [pfSet, Finset.mem_filter] using hfmem
    refine ⟨?_, ?_⟩
    · simpa [pfSet, Finset.mem_filter] using (isPF_comp_perm n s f).mpr hpf
    · show (f ∘ s) a > (f ∘ s) b
      change f (s a) > f (s b)
      rw [es0, es1]
      exact hflt
  · intro f _ g _ hfg
    funext x
    have hx : (f ∘ s) (s.symm x) = (g ∘ s) (s.symm x) := congrFun hfg _
    simpa [Function.comp] using hx
  · intro g hg
    simp only [Finset.mem_filter] at hg
    obtain ⟨hgmem, hggt⟩ := hg
    have hpf : IsParkingFunction n g := by
      simpa [pfSet, Finset.mem_filter] using hgmem
    refine ⟨g ∘ s.symm, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      have e0 : s.symm b = a := by
        rw [Equiv.symm_apply_eq]
        exact es0.symm
      have e1 : s.symm a = b := by
        rw [Equiv.symm_apply_eq]
        exact es1.symm
      refine ⟨?_, ?_⟩
      · simpa [pfSet, Finset.mem_filter] using (isPF_comp_perm n s.symm g).mpr hpf
      · show (g ∘ s.symm) a < (g ∘ s.symm) b
        change g (s.symm a) < g (s.symm b)
        rw [e1, e0]
        exact hggt
    · show (g ∘ s.symm) ∘ s = g
      funext x
      simp [Function.comp]

-- trichotomy partition of parking functions at two positions
private theorem card_partition (n : ℕ) (a b : Fin n) :
    (pfSet n).card
      = ((pfSet n).filter (fun f => f a < f b)).card
      + ((pfSet n).filter (fun f => f a = f b)).card
      + ((pfSet n).filter (fun f => f a > f b)).card := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := pfSet n) (fun f : Fin n → Fin n => f a < f b)
  have h2 : (Finset.filter (fun f : Fin n → Fin n => ¬ f a < f b) (pfSet n)).card
      = ((pfSet n).filter (fun f => f a = f b)).card
      + ((pfSet n).filter (fun f => f a > f b)).card := by
    have heq : (Finset.filter (fun f : Fin n → Fin n => ¬ f a < f b) (pfSet n))
        = ((pfSet n).filter (fun f => f a = f b))
          ∪ ((pfSet n).filter (fun f => f a > f b)) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hmem, hneg⟩
        rcases eq_or_lt_of_le (not_lt.mp hneg) with he | hl
        · exact Or.inl ⟨hmem, he.symm⟩
        · exact Or.inr ⟨hmem, hl⟩
      · rintro (⟨hmem, he⟩ | ⟨hmem, hl⟩)
        · exact ⟨hmem, by simp [he]⟩
        · exact ⟨hmem, fun hlt => lt_irrefl _ (lt_trans hlt hl)⟩
    rw [heq]
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_filter]
    intro f _ heq hgt
    rw [heq] at hgt
    exact lt_irrefl _ hgt
  omega

-- arithmetic: twice C(n,2) is n * (n - 1)
private theorem even_mul_pred_self (n : ℕ) : Even (n * (n - 1)) := by
  rcases Nat.even_or_odd n with h | h
  · exact h.mul_right _
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.zero_mul]
      exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := h
      have h2 : n - 1 = k + k := by omega
      have hev : Even (n - 1) := ⟨k, h2⟩
      exact hev.mul_left _
private theorem two_mul_choose_two (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_mul_pred_self n))

-- membership in pfSet, unfolded
private theorem mem_pfFinset (n : ℕ) (f : Fin n → Fin n) :
    f ∈ pfSet n ↔ IsParkingFunction n f :=
  mem_pfSet n f

-- the base fiber is the strict-descent set at (0, 1)
private theorem fiber_base_eq_Gt (n : ℕ) (hn : 2 ≤ n) :
    fiber n ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))
    = (pfSet n).filter
      (fun f => f (⟨0, by omega⟩ : Fin n) > f (⟨1, by omega⟩ : Fin n)) := by
  ext f
  constructor
  · intro h
    rw [mem_fiber] at h
    obtain ⟨hmem, -, hdesc⟩ := h
    rw [Finset.mem_filter]
    exact ⟨(mem_pfSet n f).mpr hmem, hdesc⟩
  · intro h
    rw [Finset.mem_filter] at h
    obtain ⟨hmem, hdesc⟩ := h
    rw [mem_fiber]
    exact ⟨(mem_pfSet n f).mp hmem, rfl, hdesc⟩

-- main count for n ≥ 2: LHS equals (n - 1) times the base fiber
private theorem lhs_eq_pred_mul (n : ℕ) (hn : 2 ≤ n) :
    (∑ f : Fin n → Fin n, if IsParkingFunction n f then
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card
      else 0)
    = (n - 1)
      * (fiber n ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))).card := by
  rw [sum_eq_sum_fiber]
  have hfib0 : ∀ p : Fin n × Fin n, p ∉ adjPairs n → (fiber n p).card = 0 := by
    intro p hp
    change ((pfSet n).filter (fun f => descentPair n f p)).card = 0
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨-, hdesc⟩ := hf
    rw [Finset.mem_filter] at hp
    simp only [Finset.mem_univ, true_and] at hp
    exact hp hdesc.1
  have hsum : (∑ p ∈ adjPairs n, (fiber n p).card)
      = (∑ p : Fin n × Fin n, (fiber n p).card) :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun p _ hp => hfib0 p hp)
  rw [← hsum]
  have hconst : ∀ p ∈ adjPairs n,
      (fiber n p).card
        = (fiber n ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))).card := by
    intro p hp
    simp only [adjPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact fiber_eq_of_adj n hn p hp
  rw [Finset.sum_eq_card_nsmul hconst, card_adjPairs, smul_eq_mul]

private theorem total_descents_aux (n : ℕ) (hn : 2 ≤ n) :
    (∑ f : Fin n → Fin n, if IsParkingFunction n f then
      (Finset.univ.filter
        (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2)).card
      else 0)
    = Nat.choose n 2 * (n + 1) ^ (n - 2) := by
  set L := ((pfSet n).filter
    (fun f => f (⟨0, by omega⟩ : Fin n) < f (⟨1, by omega⟩ : Fin n))).card with hL
  set E := ((pfSet n).filter
    (fun f => f (⟨0, by omega⟩ : Fin n) = f (⟨1, by omega⟩ : Fin n))).card with hEdef
  set G := ((pfSet n).filter
    (fun f => f (⟨0, by omega⟩ : Fin n) > f (⟨1, by omega⟩ : Fin n))).card with hGdef
  set X : ℕ := (n + 1) ^ (n - 2) with hX
  have hLG : L = G := card_swap_lt_gt n _ _
  have hpart : (pfSet n).card = L + E + G := card_partition n _ _
  have hTot : (pfSet n).card = (n + 1) ^ (n - 1) := card_pfSet n
  have hE : E = X := card_diag n hn
  have hpow : (n + 1) ^ (n - 1) = n * X + X := by
    have h1 : n - 1 = (n - 2) + 1 := by omega
    rw [h1, pow_succ', ← hX]
    ring
  have hG2 : 2 * G = n * X := by omega
  have h2C := two_mul_choose_two n
  rw [lhs_eq_pred_mul n hn, fiber_base_eq_Gt n hn, ← hGdef]
  have e1 : 2 * ((n - 1) * G) = (n - 1) * (2 * G) := by ring
  have e1b : (n - 1) * (2 * G) = (n - 1) * (n * X) := by rw [hG2]
  have e2 : (n - 1) * (n * X) = 2 * (Nat.choose n 2 * X) := by
    calc (n - 1) * (n * X) = (n * (n - 1)) * X := by ring
    _ = (2 * Nat.choose n 2) * X := by rw [h2C]
    _ = 2 * (Nat.choose n 2 * X) := by ring
  have h2 : 2 * ((n - 1) * G) = 2 * (Nat.choose n 2 * X) := by
    rw [e1, e1b, e2]
  omega

/--
**Total number of descents over parking functions.** Let $n$ be a natural number. A descent of
a function $f \colon \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ is an index $i$ with $i + 1 < n$
and $f(i) > f(i+1)$. Summed over all parking functions
$f \colon \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ of length $n$, the number of descents is
$\binom{n}{2} (n+1)^{n-2}$, which is $0$ for $n < 2$.

Parking functions are taken in threshold form: for each $k < n$, at most $n - k$ of the values
$f(i)$ are at least $k$. This is equivalent to the source's sorted-preference formulation.

Proves `Wanted` entry `total_descents_over_parking_functions`.

Source: Paul R. F. Schumacher, "Descents in Parking Functions," Journal of
Integer Sequences 21 (2018), Article 18.2.3, Theorem (label `thm:descount`),
line 180,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Schumacher/schu5.tex
-/
theorem total_descents_over_parking_functions (n : ℕ) :
    (∑ f : Fin n → Fin n,
      if IsParkingFunction n f
      then
        (Finset.univ.filter fun p : Fin n × Fin n =>
          p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2).card
      else 0) =
    Nat.choose n 2 * (n + 1) ^ (n - 2) := by
  rcases lt_or_ge n 2 with h | h
  · have h1 : n ≤ 1 := by omega
    rw [lhs_eq_zero_of_le_one n h1, rhs_eq_zero_of_le_one n h1]
  · exact total_descents_aux n h

end MetaMathlibExt
