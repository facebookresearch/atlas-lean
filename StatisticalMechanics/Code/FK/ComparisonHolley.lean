/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.FK.Comparison
import Code.FK.FiniteEnergy
import Code.FK.HolleyCoupling
import Code.Inequalities.FKG
import Code.Inequalities.Pivotal
import Code.Foundations.StochasticDomination

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open StatMech




noncomputable def chOpenCount (ω : ConfigSpace (Sym2 V)) : ℕ :=
  (G.edgeFinset.filter (fun e => ω e = true)).card









theorem numClusters_antitone {a a' : ConfigSpace (Sym2 V)} (h : a ≤ a') :
    numClusters G a' ≤ numClusters G a := by
  simp only [numClusters_eq_finrank]
  apply Submodule.finrank_mono
  intro x hx
  rw [mem_kerLap] at hx ⊢
  intro i j hij
  apply hx
  rw [openSub_adj] at hij ⊢
  refine ⟨hij.1, ?_⟩
  have hb : a s(i, j) ≤ a' s(i, j) := h s(i, j)
  rw [hij.2] at hb
  exact le_antisymm (by simp) hb









theorem numClusters_setOpen_succ_of_closed {b : ConfigSpace (Sym2 V)} {e : Sym2 V}
    (hclosed : b e = false) :
    numClusters G b ≤ numClusters G (setOpen e b) + 1 := by
  have hkey := numClusters_setClosed_le_setOpen_succ G e (setOpen e b)
  rw [setClosed_setOpen, setOpen_setOpen] at hkey
  have hb : setClosed e b = b := by
    funext e'
    by_cases h : e' = e
    · rw [h, setClosed_self, hclosed]
    · rw [setClosed_of_ne h]
  rwa [hb] at hkey



theorem openCount_setOpen_of_closed {ω : ConfigSpace (Sym2 V)} {e : Sym2 V}
    (he : e ∈ G.edgeFinset) (hclosed : ω e = false) :
    chOpenCount G (setOpen e ω) = chOpenCount G ω + 1 := by
  unfold chOpenCount
  have hset : G.edgeFinset.filter (fun e' => setOpen e ω e' = true)
      = insert e (G.edgeFinset.filter (fun e' => ω e' = true)) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hmem, hval⟩
      by_cases h : e' = e
      · exact Or.inl h
      · rw [setOpen_of_ne h] at hval; exact Or.inr ⟨hmem, hval⟩
    · rintro (h | ⟨hmem, hval⟩)
      · exact ⟨h ▸ he, by rw [h]; exact setOpen_self e ω⟩
      · refine ⟨hmem, ?_⟩
        by_cases h : e' = e
        · rw [h]; exact setOpen_self e ω
        · rw [setOpen_of_ne h]; exact hval
  rw [hset, Finset.card_insert_of_notMem]
  rw [Finset.mem_filter]
  rintro ⟨_, hval⟩
  rw [hclosed] at hval
  exact Bool.noConfusion hval





noncomputable def diffSet (b c : ConfigSpace (Sym2 V)) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => b e = false ∧ c e = true)



theorem openSub_eq_of_diffSet_empty {b c : ConfigSpace (Sym2 V)} (hle : b ≤ c)
    (hempty : diffSet G b c = ∅) : openSub G b = openSub G c := by
  ext x y
  rw [openSub_adj, openSub_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    have := hle s(x, y); rw [hopen] at this; exact le_antisymm (by simp) this
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    by_contra hbf
    rw [Bool.not_eq_true] at hbf
    have hmem : s(x, y) ∈ diffSet G b c := by
      unfold diffSet
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      exact ⟨hadj, hbf, hopen⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty _)



theorem setOpen_le_of_mem_diffSet {b c : ConfigSpace (Sym2 V)} (hle : b ≤ c) {e : Sym2 V}
    (hmem : e ∈ diffSet G b c) : setOpen e b ≤ c := by
  intro e'
  by_cases h : e' = e
  · rw [h, setOpen_self]
    unfold diffSet at hmem; rw [Finset.mem_filter] at hmem
    rw [hmem.2.2]
  · rw [setOpen_of_ne h]; exact hle e'


theorem diffSet_setOpen {b c : ConfigSpace (Sym2 V)} {e : Sym2 V}
    (hmem : e ∈ diffSet G b c) :
    diffSet G (setOpen e b) c = (diffSet G b c).erase e := by
  unfold diffSet
  ext e'
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hG, hclosed, hopen⟩
    have hne : e' ≠ e := by
      rintro rfl; rw [setOpen_self] at hclosed; exact Bool.noConfusion hclosed
    rw [setOpen_of_ne hne] at hclosed
    exact ⟨hne, hG, hclosed, hopen⟩
  · rintro ⟨hne, hG, hclosed, hopen⟩
    rw [setOpen_of_ne hne]
    exact ⟨hG, hclosed, hopen⟩





theorem numClusters_add_openCount_mono : ∀ (n : ℕ) (b c : ConfigSpace (Sym2 V)),
    b ≤ c → (diffSet G b c).card = n →
    numClusters G b + chOpenCount G b ≤ numClusters G c + chOpenCount G c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b c hle hcard
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hempty : diffSet G b c = ∅ := Finset.card_eq_zero.mp hcard
      have hsub := openSub_eq_of_diffSet_empty G hle hempty
      have hk : numClusters G b = numClusters G c := numClusters_congr_openSub G hsub
      have ho : chOpenCount G b = chOpenCount G c := by
        unfold chOpenCount
        congr 1
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hG, hval⟩
          refine ⟨hG, ?_⟩
          have := hle e; rw [hval] at this; exact le_antisymm (by simp) this
        · rintro ⟨hG, hval⟩
          refine ⟨hG, ?_⟩
          by_contra hbf
          rw [Bool.not_eq_true] at hbf
          have : e ∈ diffSet G b c := by
            unfold diffSet; rw [Finset.mem_filter]; exact ⟨hG, hbf, hval⟩
          rw [hempty] at this; exact absurd this (Finset.notMem_empty _)
      omega
    · have hne : (diffSet G b c).Nonempty := by
        rw [← Finset.card_pos, hcard]; exact hn
      obtain ⟨e, hemem⟩ := hne
      have heG : e ∈ G.edgeFinset := by
        unfold diffSet at hemem; rw [Finset.mem_filter] at hemem; exact hemem.1
      have hbe : b e = false := by
        unfold diffSet at hemem; rw [Finset.mem_filter] at hemem; exact hemem.2.1
      set b' := setOpen e b with hb'
      have hbb' : b ≤ b' := by
        rw [hb']
        intro e'
        by_cases h : e' = e
        · rw [h, setOpen_self, hbe]; simp
        · rw [setOpen_of_ne h]
      have hb'c : b' ≤ c := setOpen_le_of_mem_diffSet G hle hemem
      have hkb : numClusters G b ≤ numClusters G b' + 1 := numClusters_setOpen_succ_of_closed G hbe
      have hob : chOpenCount G b' = chOpenCount G b + 1 := openCount_setOpen_of_closed G heG hbe
      have hdiff : diffSet G b' c = (diffSet G b c).erase e := diffSet_setOpen G hemem
      have hcard' : (diffSet G b' c).card = n - 1 := by
        rw [hdiff, Finset.card_erase_of_mem hemem, hcard]
      have hlt : n - 1 < n := by omega
      have hrec := ih (n - 1) hlt b' c hb'c hcard'
      omega








theorem edgeProduct_modular (p : ℝ) (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G p a * edgeProduct G p b
      = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold edgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hinf : (a ⊓ b) e = (a e && b e) := rfl
  have hsup : (a ⊔ b) e = (a e || b e) := rfl
  rw [hinf, hsup]
  cases a e <;> cases b e <;> · simp; try ring










theorem fkWeight_cross_bernoulli_upper {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkWeight G p q a * edgeProduct G p b
      ≤ fkWeight G p q (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold fkWeight
  have hmod := edgeProduct_modular G p a b
  have hclust : q ^ numClusters G a ≤ q ^ numClusters G (a ⊓ b) :=
    pow_le_pow_right₀ hq (numClusters_antitone G inf_le_left)
  have hep_nonneg : 0 ≤ edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) :=
    le_of_lt (mul_pos (edgeProduct_pos G hp hp1 _) (edgeProduct_pos G hp hp1 _))
  calc edgeProduct G p a * q ^ numClusters G a * edgeProduct G p b
      = (edgeProduct G p a * edgeProduct G p b) * q ^ numClusters G a := by ring
    _ = (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClusters G a := by rw [hmod]
    _ ≤ (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClusters G (a ⊓ b) :=
        mul_le_mul_of_nonneg_left hclust hep_nonneg
    _ = edgeProduct G p (a ⊓ b) * q ^ numClusters G (a ⊓ b) * edgeProduct G p (a ⊔ b) := by ring






noncomputable def reducedDensity (p q : ℝ) : ℝ := p / (p + q * (1 - p))


theorem reducedDensity_mem_Ioo {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    0 < reducedDensity p q ∧ reducedDensity p q < 1 := by
  have hden : 0 < p + q * (1 - p) := by nlinarith
  unfold reducedDensity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hden]; nlinarith




theorem reducedDensity_key {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    q * reducedDensity p q * (1 - p) = (1 - reducedDensity p q) * p := by
  have hden : 0 < p + q * (1 - p) := by nlinarith
  unfold reducedDensity
  field_simp
  ring





theorem edgeFactor_bernoulli_lower_eq {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (α β : Bool) :
    (if α then reducedDensity p q else 1 - reducedDensity p q) * (if β then p else 1 - p)
        * (if (!β && α) then q else 1)
      = (if (α && β) then reducedDensity p q else 1 - reducedDensity p q)
        * (if (α || β) then p else 1 - p) := by
  have hkey : q * reducedDensity p q * (1 - p) = (1 - reducedDensity p q) * p :=
    reducedDensity_key hp hp1 hq
  cases α <;> cases β <;>
    simp only [Bool.and_self, Bool.or_self, Bool.and_false, Bool.or_false, Bool.and_true,
      Bool.or_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false] <;>
    linarith [hkey]





theorem edgeProduct_bernoulli_lower_eq {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G (reducedDensity p q) a * edgeProduct G p b
        * ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ))
      = edgeProduct G (reducedDensity p q) (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold edgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hinf : (a ⊓ b) e = (a e && b e) := rfl
  have hsup : (a ⊔ b) e = (a e || b e) := rfl
  rw [hinf, hsup]
  exact edgeFactor_bernoulli_lower_eq hp hp1 hq (a e) (b e)



theorem qFactor_eq_pow (q : ℝ) (a b : ConfigSpace (Sym2 V)) :
    ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ))
      = q ^ (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]



theorem openCount_sup (a b : ConfigSpace (Sym2 V)) :
    chOpenCount G (a ⊔ b)
      = chOpenCount G b + (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
  unfold chOpenCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hG, hval⟩
      have h2 : (a ⊔ b) e = (a e || b e) := rfl
      rw [h2, Bool.or_eq_true] at hval
      by_cases hb : b e = true
      · exact Or.inl ⟨hG, hb⟩
      · rw [Bool.not_eq_true] at hb
        rcases hval with ha | hbb
        · exact Or.inr ⟨hG, by rw [hb, ha]; rfl⟩
        · exact absurd hbb (by rw [hb]; simp)
    · rintro (⟨hG, hb⟩ | ⟨hG, hcond⟩)
      · refine ⟨hG, ?_⟩
        have h2 : (a ⊔ b) e = (a e || b e) := rfl
        rw [h2, Bool.or_eq_true]; exact Or.inr hb
      · refine ⟨hG, ?_⟩
        rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        have h2 : (a ⊔ b) e = (a e || b e) := rfl
        rw [h2, Bool.or_eq_true]; exact Or.inl hcond.2
  · rw [Finset.disjoint_left]
    rintro e he1 he2
    rw [Finset.mem_filter] at he1 he2
    rw [Bool.and_eq_true, Bool.not_eq_true'] at he2
    rw [he1.2] at he2; exact Bool.noConfusion he2.2.1






theorem numClusters_le_sup_add_opened (a b : ConfigSpace (Sym2 V)) :
    numClusters G b
      ≤ numClusters G (a ⊔ b)
        + (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
  have hcum := numClusters_add_openCount_mono G (diffSet G b (a ⊔ b)).card b (a ⊔ b)
    le_sup_right rfl
  rw [openCount_sup G a b] at hcum
  omega










theorem edgeProduct_cross_bernoulli_lower {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G (reducedDensity p q) a * fkWeight G p q b
      ≤ edgeProduct G (reducedDensity p q) (a ⊓ b) * fkWeight G p q (a ⊔ b) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  set m := (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card with hm
  
  have hqfac : ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ)) = q ^ m :=
    qFactor_eq_pow G q a b
  
  have hclust : q ^ numClusters G b ≤ q ^ numClusters G (a ⊔ b) * q ^ m := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hq (numClusters_le_sup_add_opened G a b)
  
  have hid : edgeProduct G (reducedDensity p q) a * edgeProduct G p b * q ^ m
      = edgeProduct G (reducedDensity p q) (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
    rw [← hqfac]; exact edgeProduct_bernoulli_lower_eq G hp hp1 hq a b
  
  have hp'pos := (reducedDensity_mem_Ioo hp hp1 hq).1
  have hp'lt := (reducedDensity_mem_Ioo hp hp1 hq).2
  have hEPa : 0 ≤ edgeProduct G (reducedDensity p q) a :=
    (edgeProduct_pos G hp'pos hp'lt a).le
  have hEPb : 0 ≤ edgeProduct G p b := (edgeProduct_pos G hp hp1 b).le
  
  unfold fkWeight
  calc edgeProduct G (reducedDensity p q) a * (edgeProduct G p b * q ^ numClusters G b)
      = (edgeProduct G (reducedDensity p q) a * edgeProduct G p b) * q ^ numClusters G b := by
        ring
    _ ≤ (edgeProduct G (reducedDensity p q) a * edgeProduct G p b)
          * (q ^ numClusters G (a ⊔ b) * q ^ m) :=
        mul_le_mul_of_nonneg_left hclust (mul_nonneg hEPa hEPb)
    _ = (edgeProduct G (reducedDensity p q) a * edgeProduct G p b * q ^ m)
          * q ^ numClusters G (a ⊔ b) := by ring
    _ = (edgeProduct G (reducedDensity p q) (a ⊓ b) * edgeProduct G p (a ⊔ b))
          * q ^ numClusters G (a ⊔ b) := by rw [hid]
    _ = edgeProduct G (reducedDensity p q) (a ⊓ b)
          * (edgeProduct G p (a ⊔ b) * q ^ numClusters G (a ⊔ b)) := by ring







theorem fkProb_cross_bernoulli_upper {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkProb G p q a * fkProb G p 1 b ≤ fkProb G p q (a ⊓ b) * fkProb G p 1 (a ⊔ b) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  have hZ2 : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  unfold fkProb
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2),
    fkWeight_one G p b, fkWeight_one G p (a ⊔ b)]
  exact fkWeight_cross_bernoulli_upper G hp hp1 hq a b






theorem fkProb_cross_bernoulli_lower {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkProb G (reducedDensity p q) 1 a * fkProb G p q b
      ≤ fkProb G (reducedDensity p q) 1 (a ⊓ b) * fkProb G p q (a ⊔ b) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp'pos := (reducedDensity_mem_Ioo hp hp1 hq).1
  have hp'lt := (reducedDensity_mem_Ioo hp hp1 hq).2
  have hZ1 : 0 < fkZ G (reducedDensity p q) 1 := fkZ_pos G hp'pos hp'lt one_pos
  have hZ2 : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  unfold fkProb
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2),
    fkWeight_one G (reducedDensity p q) a, fkWeight_one G (reducedDensity p q) (a ⊓ b)]
  exact edgeProduct_cross_bernoulli_lower G hp hp1 hq a b










theorem fk_monotone_in_p {p₁ p₂ q : ℝ} (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂)
    (hp₂' : p₂ < 1) (hle : p₁ ≤ p₂) (hq : 1 ≤ q) :
    measOfMass (fkProb G p₁ q) ≼ measOfMass (fkProb G p₂ q) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  refine holley_stochasticallyDominated (fun ω => fkProb_nonneg G hp₁ hp₁' hq0 ω)
    (fun ω => fkProb_nonneg G hp₂ hp₂' hq0 ω) ?_
    (fun a b => fkProb_cross G hp₁ hp₁' hp₂ hp₂' hle hq a b)
  rw [fkProb_sum_eq_one G hp₁ hp₁' hq0, fkProb_sum_eq_one G hp₂ hp₂' hq0]





theorem fk_le_bernoulli {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    measOfMass (fkProb G p q) ≼ measOfMass (fkProb G p 1) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  refine holley_stochasticallyDominated (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
    (fun ω => fkProb_nonneg G hp hp1 one_pos ω) ?_
    (fun a b => fkProb_cross_bernoulli_upper G hp hp1 hq a b)
  rw [fkProb_sum_eq_one G hp hp1 hq0, fkProb_sum_eq_one G hp hp1 one_pos]






theorem bernoulli_reduced_le_fk {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    measOfMass (fkProb G (reducedDensity p q) 1) ≼ measOfMass (fkProb G p q) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp'pos := (reducedDensity_mem_Ioo hp hp1 hq).1
  have hp'lt := (reducedDensity_mem_Ioo hp hp1 hq).2
  refine holley_stochasticallyDominated (fun ω => fkProb_nonneg G hp'pos hp'lt one_pos ω)
    (fun ω => fkProb_nonneg G hp hp1 hq0 ω) ?_
    (fun a b => fkProb_cross_bernoulli_lower G hp hp1 hq a b)
  rw [fkProb_sum_eq_one G hp'pos hp'lt one_pos, fkProb_sum_eq_one G hp hp1 hq0]








theorem fk_bernoulli_sandwich {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    measOfMass (fkProb G (reducedDensity p q) 1) ≼ measOfMass (fkProb G p q)
      ∧ measOfMass (fkProb G p q) ≼ measOfMass (fkProb G p 1) :=
  ⟨bernoulli_reduced_le_fk G hp hp1 hq, fk_le_bernoulli G hp hp1 hq⟩

end FK

end StatMech
