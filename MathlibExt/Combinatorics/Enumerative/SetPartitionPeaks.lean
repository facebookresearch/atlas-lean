/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

@[expose] public section

open scoped BigOperators
private def tpRgf (n k : ℕ) : Finset (Fin n → Fin k) :=
  Finset.univ.filter fun f : Fin n → Fin k =>
    Function.Surjective f ∧
    ∀ i : Fin n, ∀ m : Fin k,
      m.val < (f i).val → ∃ j : Fin n, j.val < i.val ∧ f j = m

private lemma tp_N2 (n k : ℕ) (g : Fin n → Fin (k + 1)) (hg : g ∈ tpRgf n (k + 1))
    (a : Fin (k + 1)) : Fin.snoc g a ∈ tpRgf (n+1) (k+1) := by
  rw [tpRgf, Finset.mem_filter] at hg ⊢
  simp only [Finset.mem_univ, true_and] at hg ⊢
  obtain ⟨hsurj, hgrow⟩ := hg
  refine ⟨?_, ?_⟩
  · intro v
    obtain ⟨i, hi⟩ := hsurj v
    exact ⟨i.castSucc, by rw [Fin.snoc_castSucc]; exact hi⟩
  · intro i' m
    refine Fin.lastCases ?_ ?_ i'
    · intro hm2
      rw [Fin.snoc_last] at hm2
      obtain ⟨j, hj⟩ := hsurj m
      exact ⟨j.castSucc, ⟨by rw [Fin.val_castSucc, Fin.val_last]; omega,
        by rw [Fin.snoc_castSucc]; exact hj⟩⟩
    · intro i hm2
      rw [Fin.snoc_castSucc] at hm2
      obtain ⟨j, hjlt, hj⟩ := hgrow i m hm2
      exact ⟨j.castSucc, ⟨by rw [Fin.val_castSucc, Fin.val_castSucc]; exact hjlt,
        by rw [Fin.snoc_castSucc]; exact hj⟩⟩
private lemma tp_N3 (n k : ℕ) (g : Fin n → Fin k) (hg : g ∈ tpRgf n k) :
    Fin.snoc (Fin.castSucc ∘ g) (Fin.last k) ∈ tpRgf (n+1) (k+1) := by
  rw [tpRgf, Finset.mem_filter] at hg ⊢
  simp only [Finset.mem_univ, true_and] at hg ⊢
  obtain ⟨hsurj, hgrow⟩ := hg
  have hcast : ∀ m : Fin (k+1), m.val < k → ∃ m' : Fin k, m'.castSucc = m := by
    intro m hm
    have hne : m ≠ Fin.last k := by
      intro heq
      rw [heq, Fin.val_last] at hm
      exact lt_irrefl k hm
    exact (Fin.exists_castSucc_eq).mpr hne
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v = Fin.last k
    · exact ⟨Fin.last n, by rw [Fin.snoc_last]; exact hv.symm⟩
    · obtain ⟨v', hv'⟩ := (Fin.exists_castSucc_eq).mpr hv
      obtain ⟨i, hi⟩ := hsurj v'
      exact ⟨i.castSucc, by rw [Fin.snoc_castSucc]; simp only [Function.comp]; rw [hi, hv']⟩
  · intro i' m
    refine Fin.lastCases ?_ ?_ i'
    · intro hm2
      rw [Fin.snoc_last] at hm2
      have hlt : m.val < k := by rw [Fin.val_last] at hm2; exact hm2
      obtain ⟨m', hm'⟩ := hcast m hlt
      obtain ⟨j, hj⟩ := hsurj m'
      exact ⟨j.castSucc, ⟨by rw [Fin.val_castSucc, Fin.val_last]; omega,
        by rw [Fin.snoc_castSucc]; simp only [Function.comp]; rw [hj, hm']⟩⟩
    · intro i hm2
      rw [Fin.snoc_castSucc] at hm2
      simp only [Function.comp_apply, Fin.val_castSucc] at hm2
      have hlt : m.val < k := lt_trans hm2 (g i).isLt
      obtain ⟨m', hm'⟩ := hcast m hlt
      have e : m'.val = m.val := by rw [← Fin.val_castSucc m', hm']
      have hm'val : m'.val < (g i).val := by omega
      obtain ⟨j, hjlt, hj⟩ := hgrow i m' hm'val
      exact ⟨j.castSucc, ⟨by rw [Fin.val_castSucc, Fin.val_castSucc]; exact hjlt,
        by rw [Fin.snoc_castSucc]; simp only [Function.comp]; rw [hj, hm']⟩⟩
private lemma tp_N4 (n k : ℕ) (f : Fin (n + 1) → Fin (k + 1)) (hf : f ∈ tpRgf (n + 1) (k + 1)) :
    Fin.init f ∈ tpRgf n (k+1) ∨
      (f (Fin.last n) = Fin.last k ∧
        ∃ g : Fin n → Fin k, g ∈ tpRgf n k ∧ Fin.init f = Fin.castSucc ∘ g) := by
  rw [tpRgf, Finset.mem_filter] at hf
  simp only [Finset.mem_univ, true_and] at hf
  obtain ⟨hfsurj, hfgrow⟩ := hf
  have hinit_grow : ∀ (i : Fin n) (m : Fin (k+1)),
      m.val < (Fin.init f i).val → ∃ j : Fin n, j.val < i.val ∧ Fin.init f j = m := by
    intro i m hm
    have hm2 : m.val < (f i.castSucc).val := hm
    obtain ⟨j, hjlt, hj⟩ := hfgrow i.castSucc m hm2
    have hjlt2 : j.val < i.val := by
      have h : j.val < (i.castSucc).val := hjlt
      rw [Fin.val_castSucc] at h
      exact h
    have hne : j ≠ Fin.last n := by
      intro heq
      have hi := i.isLt
      rw [heq, Fin.val_last] at hjlt2
      omega
    obtain ⟨j', hj'⟩ := (Fin.exists_castSucc_eq).mpr hne
    refine ⟨j', ?_, ?_⟩
    · have e : j'.val = j.val := by rw [← Fin.val_castSucc j', hj']
      omega
    · change f j'.castSucc = m
      rw [hj']; exact hj
  by_cases hsurj : Function.Surjective (Fin.init f)
  · left
    rw [tpRgf, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact ⟨hsurj, hinit_grow⟩
  · right
    rw [Function.Surjective] at hsurj
    push Not at hsurj
    obtain ⟨v, hv⟩ := hsurj
    obtain ⟨p, hp⟩ := hfsurj v
    have hlast : f (Fin.last n) = v := by
      revert hp
      refine Fin.lastCases ?_ ?_ p
      · intro hp
        exact hp
      · intro i hp
        exfalso
        exact hv i hp
    have hvk : v = Fin.last k := by
      by_contra hne
      obtain ⟨q, hq⟩ := hfsurj (Fin.last k)
      have hmem : v.val < k := by
        have h1 : v.val < k + 1 := v.isLt
        have h2 : v.val ≠ k := by
          intro heq
          apply hne
          exact Fin.ext heq
        omega
      revert hq
      refine Fin.lastCases ?_ ?_ q
      · intro hq
        exact hne (hlast.symm.trans hq)
      · intro i hq
        have hlt : v.val < (f i.castSucc).val := by rw [hq, Fin.val_last]; exact hmem
        obtain ⟨j, hjlt, hj⟩ := hfgrow i.castSucc v hlt
        have hjlt2 : j.val < i.val := by
          have h : j.val < (i.castSucc).val := hjlt
          rw [Fin.val_castSucc] at h
          exact h
        have hne2 : j ≠ Fin.last n := by
          intro heq
          have hi := i.isLt
          rw [heq, Fin.val_last] at hjlt2
          omega
        obtain ⟨j', hj'⟩ := (Fin.exists_castSucc_eq).mpr hne2
        apply hv j'
        change f j'.castSucc = v
        rw [hj']; exact hj
    have hne_all : ∀ i : Fin n, Fin.init f i ≠ Fin.last k := by
      intro i hi
      exact hv i (by rw [hvk]; exact hi)
    refine ⟨by rw [hlast, hvk], ?_⟩
    let g : Fin n → Fin k := fun i => (Fin.init f i).castPred (hne_all i)
    have hcomp : Fin.init f = Fin.castSucc ∘ g := by
      funext i
      have hci : (g i).castSucc = Fin.init f i := Fin.castSucc_castPred _ _
      simp only [Function.comp_apply]
      exact hci.symm
    have hgsurj : Function.Surjective g := by
      intro w
      obtain ⟨p, hp⟩ := hfsurj w.castSucc
      have hne_p : p ≠ Fin.last n := by
        intro heq
        rw [heq, hlast, hvk] at hp
        exact Fin.castSucc_ne_last w hp.symm
      obtain ⟨i, hi⟩ := (Fin.exists_castSucc_eq).mpr hne_p
      refine ⟨i, ?_⟩
      have h1 : f i.castSucc = w.castSucc := by rw [hi]; exact hp
      have hci := congrFun hcomp i
      simp only [Function.comp_apply] at hci
      have h2 : (g i).castSucc = w.castSucc := hci ▸ h1
      exact Fin.castSucc_injective _ h2
    have hggrow : ∀ (i : Fin n) (m : Fin k),
        m.val < (g i).val → ∃ j : Fin n, j.val < i.val ∧ g j = m := by
      intro i m hm
      have hci := congrFun hcomp i
      simp only [Function.comp_apply] at hci
      have hm2 : (m.castSucc).val < (Fin.init f i).val := by
        rw [hci]
        simp only [Fin.val_castSucc]
        have e : (g i).val = ((g i).castSucc).val := (Fin.val_castSucc _).symm
        omega
      obtain ⟨j, hjlt, hj⟩ := hinit_grow i m.castSucc hm2
      refine ⟨j, hjlt, ?_⟩
      have hcj := congrFun hcomp j
      simp only [Function.comp_apply] at hcj
      have h2 : (g j).castSucc = m.castSucc := hcj ▸ hj
      exact Fin.castSucc_injective _ h2
    exact ⟨g, by
      rw [tpRgf, Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
      exact ⟨hgsurj, hggrow⟩, hcomp⟩

private lemma tp_N5 (n k : ℕ) (F : (Fin (n + 1) → Fin (k + 1)) → ℕ) :
    ∑ f ∈ tpRgf (n+1) (k+1), F f
      = (∑ g ∈ tpRgf n k, F (Fin.snoc (Fin.castSucc ∘ g) (Fin.last k)))
        + ∑ g ∈ tpRgf n (k+1), ∑ a : Fin (k+1), F (Fin.snoc g a) := by
  set φ : (Fin n → Fin k) → (Fin (n+1) → Fin (k+1)) :=
    fun g => Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ g) (Fin.last k) with hφ
  set ψ : (Fin n → Fin (k+1)) × Fin (k+1) → (Fin (n+1) → Fin (k+1)) :=
    fun p => Fin.snoc (α := fun _ => Fin (k+1)) p.1 p.2 with hψ
  set S1 := (tpRgf n k).image φ with hS1
  set S2 := ((tpRgf n (k+1)) ×ˢ Finset.univ).image ψ with hS2
  have hφinj : ∀ g1 ∈ tpRgf n k, ∀ g2 ∈ tpRgf n k, φ g1 = φ g2 → g1 = g2 := by
    intro g1 _ g2 _ h
    have hcon := congrArg Fin.init h
    simp only [hφ, Fin.init_snoc] at hcon
    have h2 : (Fin.castSucc ∘ g1) = (Fin.castSucc ∘ g2) := hcon
    funext i
    have hi := congrFun h2 i
    simp only [Function.comp_apply] at hi
    exact Fin.castSucc_injective _ hi
  have hψinj : ∀ p1 ∈ (tpRgf n (k+1)) ×ˢ Finset.univ,
      ∀ p2 ∈ (tpRgf n (k+1)) ×ˢ Finset.univ, ψ p1 = ψ p2 → p1 = p2 := by
    intro ⟨g1, a1⟩ _ ⟨g2, a2⟩ _ h
    have hcon := congrArg Fin.init h
    simp only [hψ, Fin.init_snoc] at hcon
    have hg : g1 = g2 := hcon
    have hcon2 := congrFun h (Fin.last n)
    simp only [hψ, Fin.snoc_last] at hcon2
    have ha : a1 = a2 := hcon2
    exact Prod.ext hg ha
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro f hf1 hf2
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf1
    obtain ⟨⟨g', a⟩, hg'prod, h2⟩ := Finset.mem_image.mp hf2
    obtain ⟨hg', _⟩ := Finset.mem_product.mp hg'prod
    rw [tpRgf, Finset.mem_filter] at hg'
    simp only [Finset.mem_univ, true_and] at hg'
    obtain ⟨hgsurj, _⟩ := hg'
    have hcon := congrArg Fin.init h2
    simp only [hφ, hψ, Fin.init_snoc] at hcon
    have h3 : g' = (Fin.castSucc ∘ g) := hcon
    obtain ⟨i, hi⟩ := hgsurj (Fin.last k)
    have hbad : (g i).castSucc = Fin.last k := by
      have hci := congrFun h3 i
      simp only [Function.comp_apply] at hci
      rw [hci] at hi
      exact hi
    exact Fin.castSucc_ne_last _ hbad
  have hunion : S1 ∪ S2 = tpRgf (n+1) (k+1) := by
    apply Finset.ext
    intro f
    constructor
    · intro hmem
      rw [hS1, hS2, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hmem
      obtain ⟨g, hg, rfl⟩ | ⟨⟨g', a⟩, hmem', rfl⟩ := hmem
      · exact tp_N3 n k g hg
      · obtain ⟨hg', _⟩ := Finset.mem_product.mp hmem'
        exact tp_N2 n k g' hg' a
    · intro hfm
      rcases tp_N4 n k f hfm with hleft | ⟨hlast_eq, g, hg, hcomp⟩
      · apply Finset.mem_union.mpr
        right
        rw [hS2, Finset.mem_image]
        refine ⟨(Fin.init f, f (Fin.last n)),
          Finset.mem_product.mpr ⟨hleft, Finset.mem_univ _⟩, ?_⟩
        show ψ (Fin.init f, f (Fin.last n)) = f
        have hself := Fin.snoc_init_self f
        simp only [hψ] at ⊢
        exact hself
      · apply Finset.mem_union.mpr
        left
        rw [hS1, Finset.mem_image]
        refine ⟨g, hg, ?_⟩
        show φ g = f
        have hself := Fin.snoc_init_self f
        simp only [hφ] at ⊢
        rw [← hcomp, ← hlast_eq]
        exact hself
  have e1 : ∑ f ∈ S1, F f = ∑ g ∈ tpRgf n k, F (φ g) := by
    rw [hS1]
    exact Finset.sum_image (fun g1 hg1 g2 hg2 h => hφinj g1 hg1 g2 hg2 h)
  have e2 : ∑ f ∈ S2, F f
      = ∑ g ∈ tpRgf n (k+1), ∑ a ∈ (Finset.univ : Finset (Fin (k+1))), F (ψ (g, a)) := by
    rw [hS2]
    rw [Finset.sum_image (fun p1 hp1 p2 hp2 h => hψinj p1 hp1 p2 hp2 h)]
    exact Finset.sum_product _ _ _
  calc ∑ f ∈ tpRgf (n+1) (k+1), F f = ∑ f ∈ S1 ∪ S2, F f := by rw [← hunion]
    _ = (∑ f ∈ S1, F f) + ∑ f ∈ S2, F f := Finset.sum_union hdisj
    _ = (∑ g ∈ tpRgf n k, F (Fin.snoc (Fin.castSucc ∘ g) (Fin.last k)))
        + ∑ g ∈ tpRgf n (k+1), ∑ a : Fin (k+1), F (Fin.snoc g a) := by
      rw [e1, e2]

private lemma tp_N1 (K v : ℕ) (h : v ≤ K) :
    ∑ a : Fin K, (if a.val < v then (1:ℕ) else 0) = v := by
  have h1 : (∑ a : Fin K, (if a.val < v then (1:ℕ) else 0))
      = ∑ i ∈ Finset.range K, (if i < v then (1:ℕ) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun b => if b < v then (1:ℕ) else 0) K]
  rw [h1, Finset.sum_boole]
  have h2 : Finset.filter (fun i => i < v) (Finset.range K) = Finset.range v := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h2, Finset.card_range]
  simp

private lemma tp_N9 (k : ℕ) :
    ∑ c : Fin (k+1), ∑ b : Fin (k+1), (if c.val < b.val then b.val else 0)
      = ∑ b ∈ Finset.range (k+1), b * b := by
  rw [Finset.sum_comm]
  have hstep : ∀ b : Fin (k+1),
      (∑ c : Fin (k+1), (if c.val < b.val then b.val else 0)) = b.val * b.val := by
    intro b
    have h1 : (∑ c : Fin (k+1), (if c.val < b.val then b.val else 0))
        = b.val * (∑ c : Fin (k+1), (if c.val < b.val then (1:ℕ) else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : c.val < b.val <;> simp [h]
    rw [h1, tp_N1 (k+1) b.val (le_of_lt b.isLt)]
  rw [Finset.sum_congr rfl (fun b _ => hstep b)]
  rw [← Fin.sum_univ_eq_sum_range (fun b => b * b) (k+1)]

private lemma tp_N11_add (j : ℕ) :
    (∑ b ∈ Finset.range j, b * b) + Nat.choose (j+1) 3 = j * Nat.choose j 2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have h1 : Nat.choose (j + 1 + 1) 3 = Nat.choose (j+1) 2 + Nat.choose (j+1) 3 := by
      have := Nat.choose_succ_succ (j+1) 2
      simpa [show j + 1 + 1 = (j+1)+1 from rfl, show (2:ℕ)+1 = 3 from rfl] using this
    have h2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      have h3 : Nat.choose (j+1) 2 = Nat.choose j 1 + Nat.choose j 2 := by
        have := Nat.choose_succ_succ j 1
        simpa [show (1:ℕ)+1 = 2 from rfl] using this
      rw [h3, Nat.choose_one_right]
    rw [h1]
    nlinarith [ih, h2, Nat.zero_le (Nat.choose j 2), Nat.zero_le j]

private lemma tp_N11 (j : ℕ) :
    j * Nat.choose j 2 - Nat.choose (j + 1) 3 = ∑ b ∈ Finset.range j, b * b := by
  have h := tp_N11_add j
  omega

private def tpH (n k j : ℕ) : ℕ := ∑ t ∈ Finset.range n, j ^ t * Nat.stirlingSecond (n - 1 - t) k

private def tpSq (K : ℕ) : ℕ := ∑ b ∈ Finset.range K, b * b

private lemma tp_N12a : ∀ (n k : ℕ), tpH n k (k+1) = Nat.stirlingSecond n (k+1) := by
  intro n
  induction n with
  | zero => intro k; simp [tpH, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    intro k
    change (∑ t ∈ Finset.range (n+1), (k+1)^t * Nat.stirlingSecond (n+1-1-t) k)
      = Nat.stirlingSecond (n+1) (k+1)
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul]
    rw [show n + 1 - 1 - 0 = n from by omega]
    have hshape : ∀ t ∈ Finset.range n, (k+1)^(t+1) * Nat.stirlingSecond (n+1-1-(t+1)) k
        = (k+1) * ((k+1)^t * Nat.stirlingSecond (n-1-t) k) := by
      intro t ht
      have hmem : t < n := Finset.mem_range.mp ht
      have heq : n + 1 - 1 - (t + 1) = n - 1 - t := by omega
      rw [heq, pow_succ]
      ring
    rw [Finset.sum_congr rfl hshape, ← Finset.mul_sum]
    change (k+1) * tpH n k (k+1) + Nat.stirlingSecond n k
      = Nat.stirlingSecond (n+1) (k+1)
    rw [ih, Nat.stirlingSecond_succ_succ, add_comm]

private lemma tp_N12b (n k j : ℕ) :
    tpH (n+1) (k+1) j = (k+1) * tpH n (k+1) j + tpH n k j := by
  change (∑ t ∈ Finset.range (n+1), j^t * Nat.stirlingSecond (n+1-1-t) (k+1))
    = (k+1) * (∑ t ∈ Finset.range n, j^t * Nat.stirlingSecond (n-1-t) (k+1))
      + (∑ t ∈ Finset.range n, j^t * Nat.stirlingSecond (n-1-t) k)
  rw [Finset.sum_range_succ]
  have hlast : j^n * Nat.stirlingSecond (n+1-1-n) (k+1) = 0 := by
    have : n + 1 - 1 - n = 0 := by omega
    rw [this, Nat.stirlingSecond_zero_succ, mul_zero]
  rw [hlast, add_zero]
  have hterm : ∀ t ∈ Finset.range n,
      j^t * Nat.stirlingSecond (n+1-1-t) (k+1)
        = (k+1) * (j^t * Nat.stirlingSecond (n-1-t) (k+1))
          + j^t * Nat.stirlingSecond (n-1-t) k := by
    intro t ht
    have hmem : t < n := Finset.mem_range.mp ht
    have heq : n + 1 - 1 - t = (n - 1 - t) + 1 := by omega
    rw [heq, Nat.stirlingSecond_succ_succ]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma tp_N13 (n k j : ℕ) :
    ∑ i ∈ Finset.Icc 3 (n - k), j^(i-3) * Nat.stirlingSecond (n - i) k
      = tpH (n - 2) k j := by
  have hstep1 : ∑ i ∈ Finset.Icc 3 (n - k), j^(i-3) * Nat.stirlingSecond (n - i) k
      = ∑ i ∈ Finset.Icc 3 n, j^(i-3) * Nat.stirlingSecond (n - i) k := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.sub_le n k))
    intro x hx hx2
    simp only [Finset.mem_Icc] at hx hx2
    push Not at hx2
    have hlt : n - x < k := by omega
    rw [Nat.stirlingSecond_eq_zero_of_lt hlt, mul_zero]
  rw [hstep1]
  have hIcc : Finset.Icc 3 n = Finset.Ico 3 (n+1) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  change (∑ t ∈ Finset.range (n + 1 - 3), j^(3+t-3) * Nat.stirlingSecond (n-(3+t)) k)
    = tpH (n-2) k j
  have hlen : n + 1 - 3 = n - 2 := by omega
  rw [hlen]
  change (∑ t ∈ Finset.range (n-2), j^(3+t-3) * Nat.stirlingSecond (n-(3+t)) k)
    = ∑ t ∈ Finset.range (n-2), j^t * Nat.stirlingSecond (n-2-1-t) k
  apply Finset.sum_congr rfl
  intro t _
  have e1 : 3 + t - 3 = t := by omega
  have e2 : n - (3 + t) = n - 2 - 1 - t := by omega
  rw [e1, e2]

private lemma tp_N6 : ∀ (n k : ℕ), (tpRgf n k).card = Nat.stirlingSecond n k := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero =>
      have hkeep : ∀ f : Fin 0 → Fin 0, f ∈ tpRgf 0 0 := by
        intro f
        rw [tpRgf, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · intro b
          exact Fin.elim0 b
        · intro i
          exact Fin.elim0 i
      have huniv : tpRgf 0 0 = Finset.univ := Finset.eq_univ_of_forall hkeep
      rw [huniv, Finset.card_univ, Nat.stirlingSecond_zero]
      simp
    | succ k =>
      have hempty : tpRgf 0 (k+1) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro f hf
        rw [tpRgf, Finset.mem_filter] at hf
        obtain ⟨hsurj, _⟩ := hf.2
        obtain ⟨a, _⟩ := hsurj ⟨0, Nat.zero_lt_succ k⟩
        exact Fin.elim0 a
      rw [hempty, Finset.card_empty, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      have hempty : tpRgf (n+1) 0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro f _
        exact Fin.elim0 (f ⟨0, Nat.zero_lt_succ n⟩)
      rw [hempty, Finset.card_empty, Nat.stirlingSecond_succ_zero]
    | succ k =>
      have hcard : (tpRgf (n+1) (k+1)).card = ∑ _f ∈ tpRgf (n+1) (k+1), (1:ℕ) :=
        Finset.card_eq_sum_ones _
      rw [hcard, tp_N5 n k (fun _ => 1)]
      change (∑ _g ∈ tpRgf n k, (1:ℕ)) + (∑ _g ∈ tpRgf n (k+1), ∑ _a : Fin (k+1), (1:ℕ))
        = Nat.stirlingSecond (n+1) (k+1)
      have h1 : (∑ _g ∈ tpRgf n k, (1:ℕ)) = Nat.stirlingSecond n k := by
        rw [← Finset.card_eq_sum_ones]
        exact ih k
      have h2 : ∀ _g : Fin n → Fin (k+1), (∑ _a : Fin (k+1), (1:ℕ)) = k + 1 := by
        intro _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      have houter : (∑ _g ∈ tpRgf n (k+1), ∑ _a : Fin (k+1), (1:ℕ))
          = (tpRgf n (k+1)).card * (k + 1) := by
        calc (∑ _g ∈ tpRgf n (k+1), ∑ _a : Fin (k+1), (1:ℕ))
            = ∑ _g ∈ tpRgf n (k+1), (k + 1) :=
              Finset.sum_congr rfl (fun g _ => h2 g)
          _ = (tpRgf n (k+1)).card * (k + 1) := by
              rw [Finset.sum_const, smul_eq_mul]
      rw [h1, houter, ih (k+1), Nat.stirlingSecond_succ_succ]
      ring

private def tpPeaks (n K : ℕ) (f : Fin n → Fin K) : ℕ :=
  (Finset.univ.filter (fun i : Fin n =>
    i.val ≠ 0 ∧
    if h : i.val + 1 < n then
      (f ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).val <
          (f i).val ∧
        (f ⟨i.val + 1, h⟩).val < (f i).val
    else False)).card

private def tpT (n k : ℕ) : ℕ := ∑ f ∈ tpRgf n k, tpPeaks n k f

private def tpR (n k : ℕ) : ℕ :=
  Nat.choose k 2 * Nat.stirlingSecond (n - 1) k +
    ∑ j ∈ Finset.Icc 2 k,
      (j * Nat.choose j 2 - Nat.choose (j + 1) 3) *
        ∑ i ∈ Finset.Icc 3 (n - k),
          j ^ (i - 3) * Nat.stirlingSecond (n - i) k

private def tpA (n k : ℕ) : ℕ :=
  ∑ g ∈ tpRgf (n+2) (k+1),
    (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
      then (g (Fin.last (n+1))).val else 0)

private def tpPk (m K : ℕ) (f : Fin m → Fin K) (v : ℕ) : ℕ :=
  if h : v < m then
    if _ : 0 < v then
      if hv1 : v + 1 < m then
        if (f ⟨v - 1, lt_of_le_of_lt (Nat.sub_le v 1) h⟩).val < (f ⟨v, h⟩).val ∧
           (f ⟨v + 1, hv1⟩).val < (f ⟨v, h⟩).val then 1 else 0
      else 0
    else 0
  else 0
private lemma tp_bridge (m K : ℕ) (f : Fin m → Fin K) :
    tpPeaks m K f = ∑ v ∈ Finset.range m, tpPk m K f v := by
  have hcard : tpPeaks m K f
      = ∑ i : Fin m, (if i.val ≠ 0 ∧
          (if h : i.val + 1 < m then
            (f ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).val <
                (f i).val ∧
              (f ⟨i.val + 1, h⟩).val < (f i).val
          else False) then (1:ℕ) else 0) := by
    change ((Finset.univ.filter _).card) = _
    rw [Finset.card_filter]
  rw [hcard, ← Fin.sum_univ_eq_sum_range (tpPk m K f) m]
  apply Finset.sum_congr rfl
  intro i _
  show (if i.val ≠ 0 ∧
      (if h : i.val + 1 < m then
        (f ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).val <
            (f i).val ∧
          (f ⟨i.val + 1, h⟩).val < (f i).val
      else False) then (1:ℕ) else 0) = tpPk m K f i.val
  unfold tpPk
  split_ifs with h1 h2 h3 h4 h5
  all_goals simp_all

private lemma tp_N7 (n K : ℕ) (g : Fin (n + 2) → Fin K) (a : Fin K) :
    tpPeaks (n+3) K (Fin.snoc (α := fun _ => Fin K) g a)
      = tpPeaks (n+2) K g
        + (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val ∧
            a.val < (g (Fin.last (n+1))).val then 1 else 0) := by
  have hsnoc : ∀ (v : ℕ) (h : v < n + 3) (hv : v < n + 2),
      (Fin.snoc (α := fun _ => Fin K) g a) ⟨v, h⟩ = g ⟨v, hv⟩ := by
    intro v h hv
    simp [Fin.snoc, hv]
  have hsnoc_val : ∀ (v : ℕ) (h : v < n + 3) (hv : v < n + 2),
      ((Fin.snoc (α := fun _ => Fin K) g a) ⟨v, h⟩).val = (g ⟨v, hv⟩).val := by
    intro v h hv
    rw [hsnoc v h hv]
  have htop : ∀ (hw : n + 2 < n + 3),
      ((Fin.snoc (α := fun _ => Fin K) g a) ⟨n+2, hw⟩).val = a.val := by
    intro hw
    have e : (⟨n + 2, hw⟩ : Fin (n+3)) = Fin.last (n+2) := by
      apply Fin.ext
      change n + 2 = (Fin.last (n+2)).val
      rw [Fin.val_last]
    rw [e, Fin.snoc_last]
  rw [tp_bridge, tp_bridge]
  have eL : (∑ v ∈ Finset.range (n+3), tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) v)
      = (∑ v ∈ Finset.range (n+2), tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) v)
        + tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) (n+2) := by
    change (∑ v ∈ Finset.range ((n+2)+1), tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) v) = _
    rw [Finset.sum_range_succ]
  have eL2 : (∑ v ∈ Finset.range (n+2), tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) v)
      = (∑ v ∈ Finset.range (n+1), tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) v)
        + tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) (n+1) := by
    change (∑ v ∈ Finset.range ((n+1)+1), tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) v) = _
    rw [Finset.sum_range_succ]
  have eR : (∑ v ∈ Finset.range (n+2), tpPk (n+2) K g v)
      = (∑ v ∈ Finset.range (n+1), tpPk (n+2) K g v) + tpPk (n+2) K g (n+1) := by
    change (∑ v ∈ Finset.range ((n+1)+1), tpPk (n+2) K g v) = _
    rw [Finset.sum_range_succ]
  rw [eL, eL2, eR]
  have hPtop : tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) (n+2) = 0 := by
    unfold tpPk
    split_ifs with c1 c2 c3 c4
    all_goals omega
  have hQtop : tpPk (n+2) K g (n+1) = 0 := by
    unfold tpPk
    split_ifs with c1 c2 c3 c4
    all_goals omega
  have u1 : ∀ (p : n < n + 2),
      (⟨n, p⟩ : Fin (n+2)) = Fin.castSucc (Fin.last n) := by
    intro p
    apply Fin.ext
    change n = (Fin.castSucc (Fin.last n)).val
    rw [Fin.val_castSucc, Fin.val_last]
  have u2 : ∀ (p : n + 1 < n + 2),
      (⟨n+1, p⟩ : Fin (n+2)) = Fin.last (n+1) := by
    intro p
    apply Fin.ext
    change n + 1 = (Fin.last (n+1)).val
    rw [Fin.val_last]
  have hPmid : tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) (n+1)
      = (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val ∧
          a.val < (g (Fin.last (n+1))).val then 1 else 0) := by
    have c1 : n + 1 < n + 3 := by omega
    have c2 : 0 < n + 1 := by omega
    have c3 : n + 1 + 1 < n + 3 := by omega
    have e1 : n + 1 - 1 = n := by omega
    have e2 : n + 1 + 1 = n + 2 := by omega
    have hn2 : n < n + 2 := by omega
    have hn12 : n + 1 < n + 2 := by omega
    unfold tpPk
    rw [dite_eq_left c1, dite_eq_left c2, dite_eq_left c3]
    simp only [e1, e2, htop]
    rw [hsnoc_val n _ hn2, hsnoc_val (n+1) _ hn12, u1 hn2, u2 hn12]
  have hmid : (∑ v ∈ Finset.range (n+1),
        tpPk (n+3) K (Fin.snoc (α := fun _ => Fin K) g a) v)
      = ∑ v ∈ Finset.range (n+1), tpPk (n+2) K g v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvmem : v < n + 1 := Finset.mem_range.mp hv
    have hv3 : v < n + 3 := by omega
    have hv2 : v < n + 2 := by omega
    have hv13 : v + 1 < n + 3 := by omega
    have hv12 : v + 1 < n + 2 := by omega
    have e1' : v - 1 < n + 2 := by omega
    have e2' : v + 1 < n + 2 := by omega
    unfold tpPk
    rw [dite_eq_left hv3, dite_eq_left hv2, dite_eq_left hv13, dite_eq_left hv12]
    rw [hsnoc_val (v-1) _ e1', hsnoc_val v _ hv2, hsnoc_val (v+1) _ e2']
  rw [hmid, hPtop, hQtop, hPmid]
  ring

private lemma tp_peak_castSucc (n k : ℕ) (g : Fin n → Fin k) :
    tpPeaks n (k+1) (Fin.castSucc ∘ g) = tpPeaks n k g := by
  unfold tpPeaks
  rw [Finset.card_filter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, Fin.val_castSucc]

private lemma tp_N8 (n k : ℕ) :
    tpT (n+3) (k+1) = tpT (n+2) k + (k+1) * tpT (n+2) (k+1) + tpA n k := by
  have h5 := tp_N5 (n+2) k (fun f => tpPeaks ((n+2)+1) (k+1) f)
  change tpT ((n+2)+1) (k+1) = tpT (n+2) k + (k+1) * tpT (n+2) (k+1) + tpA n k
  have hT : tpT ((n+2)+1) (k+1)
      = ∑ f ∈ tpRgf ((n+2)+1) (k+1), tpPeaks ((n+2)+1) (k+1) f := rfl
  rw [hT, h5]
  have hnew : (∑ g ∈ tpRgf (n+2) k,
        tpPeaks ((n+2)+1) (k+1) (Fin.snoc (Fin.castSucc ∘ g) (Fin.last k)))
      = tpT (n+2) k := by
    change (∑ g ∈ tpRgf (n+2) k,
        tpPeaks ((n+2)+1) (k+1) (Fin.snoc (Fin.castSucc ∘ g) (Fin.last k)))
      = ∑ g ∈ tpRgf (n+2) k, tpPeaks (n+2) k g
    apply Finset.sum_congr rfl
    intro g hg
    have h7 := tp_N7 n (k+1) (Fin.castSucc ∘ g) (Fin.last k)
    have hcs := tp_peak_castSucc (n+2) k g
    have hnew0 : (if ((Fin.castSucc ∘ g) (Fin.castSucc (Fin.last n))).val
            < ((Fin.castSucc ∘ g) (Fin.last (n+1))).val ∧
          (Fin.last k).val < ((Fin.castSucc ∘ g) (Fin.last (n+1))).val
        then (1:ℕ) else 0) = 0 := by
      have hfalse : ¬ (((Fin.castSucc ∘ g) (Fin.castSucc (Fin.last n))).val
            < ((Fin.castSucc ∘ g) (Fin.last (n+1))).val ∧
          (Fin.last k).val < ((Fin.castSucc ∘ g) (Fin.last (n+1))).val) := by
        rintro ⟨_, h2⟩
        rw [Fin.val_last] at h2
        simp only [Function.comp_apply, Fin.val_castSucc] at h2
        have hlt := (g (Fin.last (n+1))).isLt
        omega
      rw [ite_eq_right hfalse]
    change tpPeaks (n+3) (k+1)
        (Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ g) (Fin.last k))
      = tpPeaks (n+2) k g
    rw [h7, hcs, hnew0, add_zero]
  have hold : (∑ g ∈ tpRgf (n+2) (k+1), ∑ a : Fin (k+1),
        tpPeaks ((n+2)+1) (k+1) (Fin.snoc g a))
      = (k+1) * tpT (n+2) (k+1) + tpA n k := by
    have hper : ∀ g ∈ tpRgf (n+2) (k+1),
        (∑ a : Fin (k+1), tpPeaks ((n+2)+1) (k+1) (Fin.snoc g a))
        = (k+1) * tpPeaks (n+2) (k+1) g
          + (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
              then (g (Fin.last (n+1))).val else 0) := by
      intro g hg
      have h7a : ∀ a : Fin (k+1),
          tpPeaks ((n+2)+1) (k+1) (Fin.snoc g a)
          = tpPeaks (n+2) (k+1) g
            + (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val ∧
                a.val < (g (Fin.last (n+1))).val then (1:ℕ) else 0) := by
        intro a
        change tpPeaks (n+3) (k+1) (Fin.snoc (α := fun _ => Fin (k+1)) g a) = _
        exact tp_N7 n (k+1) g a
      calc (∑ a : Fin (k+1), tpPeaks ((n+2)+1) (k+1) (Fin.snoc g a))
          = ∑ a : Fin (k+1), (tpPeaks (n+2) (k+1) g
            + (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val ∧
                a.val < (g (Fin.last (n+1))).val then (1:ℕ) else 0)) :=
            Finset.sum_congr rfl (fun a _ => h7a a)
        _ = (k+1) * tpPeaks (n+2) (k+1) g
            + (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
              then (g (Fin.last (n+1))).val else 0) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                smul_eq_mul]
            · by_cases hc : (g (Fin.castSucc (Fin.last n))).val
                < (g (Fin.last (n+1))).val
              · have hL : (∑ a : Fin (k+1),
                    (if (g (Fin.castSucc (Fin.last n))).val
                      < (g (Fin.last (n+1))).val ∧ a.val < (g (Fin.last (n+1))).val
                      then (1:ℕ) else 0))
                  = (g (Fin.last (n+1))).val := by
                  simp only [hc, true_and]
                  exact tp_N1 (k+1) _ (le_of_lt (g (Fin.last (n+1))).isLt)
                rw [hL, ite_eq_left hc]
              · have hL : (∑ a : Fin (k+1),
                    (if (g (Fin.castSucc (Fin.last n))).val
                      < (g (Fin.last (n+1))).val ∧ a.val < (g (Fin.last (n+1))).val
                      then (1:ℕ) else 0)) = 0 := by
                  simp only [hc, false_and]
                  simp
                rw [hL, ite_eq_right hc]
    calc (∑ g ∈ tpRgf (n+2) (k+1), ∑ a : Fin (k+1),
          tpPeaks ((n+2)+1) (k+1) (Fin.snoc g a))
        = ∑ g ∈ tpRgf (n+2) (k+1), ((k+1) * tpPeaks (n+2) (k+1) g
          + (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
              then (g (Fin.last (n+1))).val else 0)) :=
          Finset.sum_congr rfl (fun g hg => hper g hg)
      _ = (k+1) * tpT (n+2) (k+1) + tpA n k := by
          have hT2 : tpT (n+2) (k+1)
              = ∑ g ∈ tpRgf (n+2) (k+1), tpPeaks (n+2) (k+1) g := rfl
          have hA2 : tpA n k = ∑ g ∈ tpRgf (n+2) (k+1),
              (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
                then (g (Fin.last (n+1))).val else 0) := rfl
          rw [Finset.sum_add_distrib, hT2, hA2, ← Finset.mul_sum]
  rw [hnew, hold]
  ring

private lemma tp_N10 (n k : ℕ) :
    tpA n k = k * Nat.stirlingSecond (n+1) k
      + tpSq (k+1) * Nat.stirlingSecond n (k+1) := by
  have hA : tpA n k = ∑ g ∈ tpRgf ((n+1)+1) (k+1),
      (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
        then (g (Fin.last (n+1))).val else 0) := rfl
  have h5 : (∑ g ∈ tpRgf ((n+1)+1) (k+1),
        (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
          then (g (Fin.last (n+1))).val else 0))
      = (∑ h ∈ tpRgf (n+1) k,
          (if ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
            (Fin.castSucc (Fin.last n))).val
            < ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
              (Fin.last (n+1))).val
          then ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
            (Fin.last (n+1))).val else 0))
        + (∑ h ∈ tpRgf (n+1) (k+1), ∑ b : Fin (k+1),
          (if ((Fin.snoc (α := fun _ => Fin (k+1)) h b) (Fin.castSucc (Fin.last n))).val
            < ((Fin.snoc (α := fun _ => Fin (k+1)) h b) (Fin.last (n+1))).val
          then ((Fin.snoc (α := fun _ => Fin (k+1)) h b) (Fin.last (n+1))).val else 0)) :=
    tp_N5 (n+1) k _
  rw [hA, h5]
  have hnew : (∑ h ∈ tpRgf (n+1) k,
        (if ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
          (Fin.castSucc (Fin.last n))).val
          < ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
            (Fin.last (n+1))).val
        then ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
          (Fin.last (n+1))).val else 0))
      = k * Nat.stirlingSecond (n+1) k := by
    have hterm : ∀ h ∈ tpRgf (n+1) k,
        (if ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
          (Fin.castSucc (Fin.last n))).val
          < ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
            (Fin.last (n+1))).val
        then ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
          (Fin.last (n+1))).val else 0) = k := by
      intro h hg
      rw [Fin.snoc_castSucc, Fin.snoc_last]
      simp only [Function.comp_apply, Fin.val_castSucc, Fin.val_last]
      rw [ite_eq_left (h (Fin.last n)).isLt]
    calc (∑ h ∈ tpRgf (n+1) k, (if ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h)
        (Fin.last k))
            (Fin.castSucc (Fin.last n))).val
            < ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
              (Fin.last (n+1))).val
          then ((Fin.snoc (α := fun _ => Fin (k+1)) (Fin.castSucc ∘ h) (Fin.last k))
            (Fin.last (n+1))).val else 0))
        = ∑ _h ∈ tpRgf (n+1) k, k :=
          Finset.sum_congr rfl (fun h hg => hterm h hg)
      _ = k * Nat.stirlingSecond (n+1) k := by
          rw [Finset.sum_const, tp_N6, smul_eq_mul, mul_comm]
  have hold : (∑ h ∈ tpRgf (n+1) (k+1), ∑ b : Fin (k+1),
        (if ((Fin.snoc (α := fun _ => Fin (k+1)) h b)
          (Fin.castSucc (Fin.last n))).val
          < ((Fin.snoc (α := fun _ => Fin (k+1)) h b) (Fin.last (n+1))).val
        then ((Fin.snoc (α := fun _ => Fin (k+1)) h b)
          (Fin.last (n+1))).val else 0))
      = tpSq (k+1) * Nat.stirlingSecond n (k+1) := by
    have hC : (∑ h ∈ tpRgf (n+1) (k+1), ∑ b : Fin (k+1),
          (if ((Fin.snoc (α := fun _ => Fin (k+1)) h b)
            (Fin.castSucc (Fin.last n))).val
            < ((Fin.snoc (α := fun _ => Fin (k+1)) h b) (Fin.last (n+1))).val
          then ((Fin.snoc (α := fun _ => Fin (k+1)) h b)
            (Fin.last (n+1))).val else 0))
        = (∑ h ∈ tpRgf (n+1) (k+1), ∑ b : Fin (k+1),
          (if (h (Fin.last n)).val < b.val then b.val else 0)) :=
      Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun b _ => by
        rw [Fin.snoc_castSucc, Fin.snoc_last]))
    have h5b : (∑ h ∈ tpRgf (n+1) (k+1), ∑ b : Fin (k+1),
          (if (h (Fin.last n)).val < b.val then b.val else 0))
        = (∑ h'' ∈ tpRgf n k, ∑ b : Fin (k+1),
            (if (((Fin.snoc (α := fun _ => Fin (k+1))
              (Fin.castSucc ∘ h'') (Fin.last k)) (Fin.last n))).val < b.val
            then b.val else 0))
          + (∑ h'' ∈ tpRgf n (k+1), ∑ c : Fin (k+1), ∑ b : Fin (k+1),
            (if (((Fin.snoc (α := fun _ => Fin (k+1)) h'' c)
              (Fin.last n))).val < b.val then b.val else 0)) :=
      tp_N5 n k _
    have hnew0 : (∑ h'' ∈ tpRgf n k, ∑ b : Fin (k+1),
          (if (((Fin.snoc (α := fun _ => Fin (k+1))
            (Fin.castSucc ∘ h'') (Fin.last k)) (Fin.last n))).val < b.val
          then b.val else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro h'' _
      have h0 : ∀ b : Fin (k+1),
          (if (((Fin.snoc (α := fun _ => Fin (k+1))
            (Fin.castSucc ∘ h'') (Fin.last k)) (Fin.last n))).val < b.val
          then b.val else 0) = 0 := by
        intro b
        have hkk : (((Fin.snoc (α := fun _ => Fin (k+1))
          (Fin.castSucc ∘ h'') (Fin.last k)) (Fin.last n))).val = k := by
          rw [Fin.snoc_last, Fin.val_last]
        rw [hkk]
        have hb := b.isLt
        have hneg : ¬ k < b.val := by omega
        rw [ite_eq_right hneg]
      rw [Finset.sum_congr rfl (fun b _ => h0 b)]
      simp
    have hold2 : (∑ h'' ∈ tpRgf n (k+1), ∑ c : Fin (k+1), ∑ b : Fin (k+1),
          (if (((Fin.snoc (α := fun _ => Fin (k+1)) h'' c)
            (Fin.last n))).val < b.val then b.val else 0))
        = tpSq (k+1) * Nat.stirlingSecond n (k+1) := by
      have hper2 : ∀ h'' ∈ tpRgf n (k+1),
          (∑ c : Fin (k+1), ∑ b : Fin (k+1),
            (if (((Fin.snoc (α := fun _ => Fin (k+1)) h'' c)
              (Fin.last n))).val < b.val then b.val else 0))
          = tpSq (k+1) := by
        intro h'' _
        calc (∑ c : Fin (k+1), ∑ b : Fin (k+1),
              (if (((Fin.snoc (α := fun _ => Fin (k+1)) h'' c)
                (Fin.last n))).val < b.val then b.val else 0))
            = ∑ c : Fin (k+1), ∑ b : Fin (k+1),
              (if c.val < b.val then b.val else 0) := by
              apply Finset.sum_congr rfl
              intro c _
              apply Finset.sum_congr rfl
              intro b _
              rw [Fin.snoc_last]
          _ = tpSq (k+1) := tp_N9 k
      calc (∑ h'' ∈ tpRgf n (k+1), ∑ c : Fin (k+1), ∑ b : Fin (k+1),
            (if (((Fin.snoc (α := fun _ => Fin (k+1)) h'' c)
              (Fin.last n))).val < b.val then b.val else 0))
          = ∑ _h'' ∈ tpRgf n (k+1), tpSq (k+1) :=
            Finset.sum_congr rfl (fun h'' hh => hper2 h'' hh)
        _ = tpSq (k+1) * Nat.stirlingSecond n (k+1) := by
            rw [Finset.sum_const, tp_N6, smul_eq_mul]
            ring
    rw [hC, h5b, hnew0, hold2, zero_add]
  rw [hnew, hold]

private lemma tp_Rnorm (n k : ℕ) : tpR n k
    = Nat.choose k 2 * Nat.stirlingSecond (n-1) k
      + ∑ j ∈ Finset.Icc 2 k, tpSq j * tpH (n-2) k j := by
  unfold tpR
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [tp_N11, tp_N13]
  rfl

private lemma tp_N14 (m k : ℕ) :
    tpR (m+3) (k+1) = tpR (m+2) k + (k+1) * tpR (m+2) (k+1)
      + k * Nat.stirlingSecond (m+1) k
      + tpSq (k+1) * Nat.stirlingSecond m (k+1) := by
  simp only [tp_Rnorm]
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 2 - 1 = m + 1 := by omega
  have e4 : m + 2 - 2 = m := by omega
  rw [e1, e2, e3, e4]
  have hS : Nat.stirlingSecond (m+2) (k+1)
      = (k+1) * Nat.stirlingSecond (m+1) (k+1) + Nat.stirlingSecond (m+1) k :=
    Nat.stirlingSecond_succ_succ (m+1) k
  have hC : Nat.choose (k+1) 2 = Nat.choose k 2 + k := by
    have h := Nat.choose_succ_succ k 1
    rw [show Nat.succ 1 = 2 from rfl, Nat.choose_one_right,
      Nat.succ_eq_add_one] at h
    omega
  by_cases hk : k = 0
  · subst hk
    have q1 : Finset.Icc 2 1 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    have q2 : Finset.Icc 2 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    rw [q1, q2, Finset.sum_empty, Finset.sum_empty]
    have c1 : Nat.choose 1 2 = 0 := by decide
    have c0 : Nat.choose 0 2 = 0 := by decide
    have s1 : tpSq 1 = 0 := by decide
    rw [c1, c0, s1]
    ring
  · have h2k : 2 ≤ k + 1 := by omega
    have hH : ∀ j ∈ Finset.Icc 2 (k+1),
        tpSq j * tpH (m+1) (k+1) j
        = (k+1) * (tpSq j * tpH m (k+1) j) + tpSq j * tpH m k j := by
      intro j _
      rw [tp_N12b]
      ring
    have hLHS2 : (∑ j ∈ Finset.Icc 2 (k+1), tpSq j * tpH (m+1) (k+1) j)
        = (k+1) * (∑ j ∈ Finset.Icc 2 (k+1), tpSq j * tpH m (k+1) j)
          + (∑ j ∈ Finset.Icc 2 (k+1), tpSq j * tpH m k j) :=
      calc (∑ j ∈ Finset.Icc 2 (k+1), tpSq j * tpH (m+1) (k+1) j)
          = ∑ j ∈ Finset.Icc 2 (k+1),
            ((k+1) * (tpSq j * tpH m (k+1) j) + tpSq j * tpH m k j) :=
            Finset.sum_congr rfl hH
        _ = (k+1) * (∑ j ∈ Finset.Icc 2 (k+1), tpSq j * tpH m (k+1) j)
            + (∑ j ∈ Finset.Icc 2 (k+1), tpSq j * tpH m k j) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hsplit : (∑ j ∈ Finset.Icc 2 (k+1), tpSq j * tpH m k j)
          = (∑ j ∈ Finset.Icc 2 k, tpSq j * tpH m k j)
            + tpSq (k+1) * tpH m k (k+1) := by
      rw [Finset.sum_Icc_succ_top h2k]
    rw [hLHS2, hsplit, tp_N12a, hS, hC]
    ring

private lemma tp_N15a (m k : ℕ) (hm : m ≤ 2) : tpT m k = 0 := by
  change (∑ f ∈ tpRgf m k, tpPeaks m k f) = 0
  apply Finset.sum_eq_zero
  intro f _
  unfold tpPeaks
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨_, hP⟩ := hi
  obtain ⟨hne, hd⟩ := hP
  by_cases h : i.val + 1 < m
  · have hlt := i.isLt
    omega
  · simp [h] at hd

private lemma tp_N15b (m : ℕ) : tpT (m+1) 0 = 0 := by
  change (∑ f ∈ tpRgf (m+1) 0, tpPeaks (m+1) 0 f) = 0
  have hempty : tpRgf (m+1) 0 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro f _
    exact Fin.elim0 (f ⟨0, Nat.zero_lt_succ m⟩)
  rw [hempty, Finset.sum_empty]

private lemma tp_N15c (m k : ℕ) (hm : m ≤ 2) : tpR m k = 0 := by
  have hempty : Finset.Icc 3 (m - k) = (∅ : Finset ℕ) := by
    apply Finset.Icc_eq_empty
    omega
  have h1 : Nat.choose k 2 * Nat.stirlingSecond (m-1) k = 0 := by
    by_cases hk : k ≤ 1
    · have hch : Nat.choose k 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hch, zero_mul]
    · have hlt : m - 1 < k := by omega
      rw [Nat.stirlingSecond_eq_zero_of_lt hlt, mul_zero]
  unfold tpR
  rw [hempty, h1]
  simp

private lemma tp_N15d (n : ℕ) : tpR n 0 = 0 := by
  unfold tpR
  have e1 : Finset.Icc 2 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  have c0 : Nat.choose 0 2 = 0 := by decide
  rw [e1, Finset.sum_empty, c0]
  ring

section
namespace MetaMathlibExt

/--
**Total number of peaks over set partitions.** For natural numbers $n$ and $k$, call a word
$\pi = \pi_1 \cdots \pi_n$ on the alphabet $\{0, \dots, k-1\}$ a restricted growth word if it uses
every letter and, for every position $i$, every letter smaller than $\pi_i$ occurs among
$\pi_1, \dots, \pi_{i-1}$; these words encode the partitions of $[n]$ into $k$ blocks. A peak of
$\pi$ is a position $i$ with $1 < i < n$ and $\pi_{i-1} < \pi_i > \pi_{i+1}$. Then the total
number of peaks, summed over all restricted growth words of length $n$ on $k$ letters, equals
$$\binom{k}{2} S(n-1, k) + \sum_{j=2}^{k} \left(j \binom{j}{2} - \binom{j+1}{3}\right)
\sum_{i=3}^{n-k} j^{i-3}\, S(n-i, k),$$
where $S(m, k)$ is the Stirling number of the second kind, $n - 1$ is read as $0$ when $n = 0$,
and the inner sum is empty when $n - k < 3$.

Proves `Wanted` entry `total_peaks_canonical`.

Source: Toufik Mansour and Mark Shattuck, "Counting Peaks and Valleys in a Partition
of a Set", Journal of Integer Sequences 13 (2010), Article 10.6.8, Corollary 2,
lines 388-394, <https://cs.uwaterloo.ca/journals/JIS/VOL13/Shattuck/shattuck3.tex>.
-/
theorem total_peaks_canonical (n k : ℕ)
    : (∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin k =>
          Function.Surjective f ∧
          ∀ i : Fin n, ∀ m : Fin k,
            m.val < (f i).val → ∃ j : Fin n, j.val < i.val ∧ f j = m),
        (Finset.univ.filter (fun i : Fin n =>
          i.val ≠ 0 ∧
          if h : i.val + 1 < n then
            (f ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).val <
                (f i).val ∧
              (f ⟨i.val + 1, h⟩).val < (f i).val
          else False)).card) =
      Nat.choose k 2 * Nat.stirlingSecond (n - 1) k +
        ∑ j ∈ Finset.Icc 2 k,
          (j * Nat.choose j 2 - Nat.choose (j + 1) 3) *
            ∑ i ∈ Finset.Icc 3 (n - k),
              j ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
  have hT : (∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin k =>
          Function.Surjective f ∧
          ∀ i : Fin n, ∀ m : Fin k,
            m.val < (f i).val → ∃ j : Fin n, j.val < i.val ∧ f j = m),
        (Finset.univ.filter (fun i : Fin n =>
          i.val ≠ 0 ∧
          if h : i.val + 1 < n then
            (f ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).val <
                (f i).val ∧
              (f ⟨i.val + 1, h⟩).val < (f i).val
          else False)).card) = tpT n k := rfl
  have hR : (Nat.choose k 2 * Nat.stirlingSecond (n - 1) k +
        ∑ j ∈ Finset.Icc 2 k,
          (j * Nat.choose j 2 - Nat.choose (j + 1) 3) *
            ∑ i ∈ Finset.Icc 3 (n - k),
              j ^ (i - 3) * Nat.stirlingSecond (n - i) k) = tpR n k := rfl
  rw [hT, hR]
  clear hT hR
  induction n generalizing k with
  | zero =>
    rw [tp_N15a 0 k (by omega), tp_N15c 0 k (by omega)]
  | succ m ih =>
    cases m with
    | zero =>
      change tpT 1 k = tpR 1 k
      rw [tp_N15a 1 k (by omega), tp_N15c 1 k (by omega)]
    | succ m0 =>
      cases m0 with
      | zero =>
        change tpT 2 k = tpR 2 k
        rw [tp_N15a 2 k (by omega), tp_N15c 2 k (by omega)]
      | succ m' =>
        cases k with
        | zero =>
          exact (tp_N15b _).trans (tp_N15d _).symm
        | succ k'' =>
          change tpT (m'+3) (k''+1) = tpR (m'+3) (k''+1)
          rw [tp_N8 m' k'', tp_N10 m' k'']
          have ih1 : tpT (m'+2) k'' = tpR (m'+2) k'' := ih k''
          have ih2 : tpT (m'+2) (k''+1) = tpR (m'+2) (k''+1) := ih (k''+1)
          rw [ih1, ih2]
          have h14 := tp_N14 m' k''
          omega

end MetaMathlibExt
end
