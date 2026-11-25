/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.ACGateBridge
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Choose.Central
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Smolensky's lower bound for parity

`smolensky` proves that a polynomial-size family of bounded-depth circuits with
modulus-three gates cannot compute parity. The proof compares two bounds on the number of
inputs where a low-degree function over the field of three elements disagrees with parity.

For a circuit on `n` bits of size `s` and depth `d`, testing each AND and OR gate
with `r ≥ 1` linear forms gives degree at most `(2 * r) ^ d` and at most `s * 2 ^ n / 2 ^ r`
errors.
In the opposite direction, multiplication by the parity character sends the character on a
set of coordinates to the character on its complement. This gives a dimension lower bound
on the error set, using coordinate sets of a single size just below the middle layer.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.Smolensky

open Finset Module
open scoped symmDiff

/-! ### Characters over the field of three elements -/

private abbrev K := ZMod 3
private abbrev Cube (n : ℕ) := Fin n → Bool
private abbrev Fn (n : ℕ) := Cube n → K

variable {n : ℕ}

private def sign (b : Bool) : K := if b then -1 else 1

private def chi (s : Finset (Fin n)) : Fn n :=
  fun x => ∏ i, if i ∈ s then sign (x i) else 1

private theorem chi_empty : chi (∅ : Finset (Fin n)) = 1 := by
  ext x
  simp [chi]

private theorem chi_mul (s t : Finset (Fin n)) : chi s * chi t = chi (s ∆ t) := by
  funext x
  simp only [Pi.mul_apply, chi, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    cases x i <;> simp [hs, ht, mem_symmDiff, sign]

private theorem sum_chi_ne {s : Finset (Fin n)} (hs : s.Nonempty) :
    ∑ x, chi s x = 0 := by
  classical
  change (∑ x : Cube n, ∏ i, (fun (i : Fin n) (b : Bool) =>
    if i ∈ s then sign b else 1) i (x i)) = 0
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if i ∈ s then sign b else 1)]
  obtain ⟨i, hi⟩ := hs
  apply prod_eq_zero (mem_univ i)
  simp [hi, sign]

private theorem chi_independent : LinearIndependent K (chi (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hf s
  have hz := congrArg (fun g : Fn n => ∑ x, g x * chi s x) hf
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
    sum_const_zero, sum_mul, mul_assoc] at hz
  rw [Finset.sum_comm] at hz
  simp_rw [← Finset.mul_sum, ← Pi.mul_apply, chi_mul] at hz
  rw [Finset.sum_eq_single s] at hz
  · simpa [chi_empty, Fintype.card_pi, show (2 : K) ≠ 0 by decide] using hz
  · intro t _ hts
    rw [sum_chi_ne (symmDiff_nonempty.mpr hts), mul_zero]
  · simp

private def chars (s : Set (Finset (Fin n))) : Submodule K (Fn n) :=
  Submodule.span K (chi '' s)

/-- The span of characters on at most `d` coordinates. -/
private def low (n d : ℕ) : Submodule K (Fn n) := chars {s | s.card ≤ d}

private theorem chi_low {s : Finset (Fin n)} {d : ℕ} (h : s.card ≤ d) :
    chi s ∈ low n d := Submodule.subset_span ⟨s, h, rfl⟩

private theorem low_one (d : ℕ) : (1 : Fn n) ∈ low n d := by
  rw [← chi_empty]
  exact chi_low (by simp)

private theorem low_mono {a b : ℕ} (h : a ≤ b) : low n a ≤ low n b :=
  Submodule.span_mono (Set.image_mono fun _ hs => le_trans hs h)

private theorem low_mul {a b : ℕ} {f g : Fn n} (hf : f ∈ low n a) (hg : g ∈ low n b) :
    f * g ∈ low n (a + b) := by
  apply Submodule.span_induction₂ (p := fun f g _ _ => f * g ∈ low n (a + b))
    _ _ _ _ _ _ _ hf hg
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    rw [chi_mul]
    exact chi_low ((card_le_card symmDiff_subset_union).trans
      ((card_union_le ..).trans (Nat.add_le_add hs ht)))
  · simp
  · simp
  · intro x y z _ _ _ hx hy
    exact add_mul x y z ▸ (low n _).add_mem hx hy
  · intro x y z _ _ _ hy hz
    exact mul_add x y z ▸ (low n _).add_mem hy hz
  · intro r x y _ _ h
    simpa [smul_mul_assoc] using (low n _).smul_mem r h
  · intro r x y _ _ h
    simpa [mul_smul_comm] using (low n _).smul_mem r h

private theorem mul_parity_high {d : ℕ} {f : Fn n} (hf : f ∈ low n d) :
    chi univ * f ∈ chars {s | n - d ≤ s.card} := by
  induction hf using Submodule.span_induction with
  | mem _ hs =>
    obtain ⟨s, hs, rfl⟩ := hs
    rw [chi_mul, show univ ∆ s = sᶜ from top_symmDiff s]
    apply Submodule.subset_span
    exact ⟨sᶜ, by simpa [Finset.card_compl] using Nat.sub_le_sub_left hs n, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using (chars _).add_mem hx hy
  | smul r x _ hx => simpa [mul_smul_comm] using (chars _).smul_mem r hx

/-- Restriction to the error set is injective on degree at most `k`. Indeed, if `f` vanishes
there, multiplying it by the approximant agrees everywhere with multiplying it by parity.
The two products have disjoint character degrees. -/
private theorem errors_ge_choose {e k : ℕ} {p : Fn n} (hp : p ∈ low n e)
    (hk : k + e < n - k) (B : Finset (Cube n)) (hB : ∀ x ∉ B, p x = chi univ x) :
    n.choose k ≤ B.card := by
  classical
  let restrict : low n k →ₗ[K] (B → K) :=
    { toFun := fun f x => f.val x.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective restrict := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have heq : chi univ * f.val = f.val * p := by
      funext x
      by_cases hx : x ∈ B
      · have hz : f.val x = 0 := congrFun hf ⟨x, hx⟩
        simp [hz]
      · simp [hB _ hx, mul_comm]
    have hd : Disjoint (low n (k + e)) (chars {s | n - k ≤ s.card}) :=
      chi_independent.disjoint_span_image (Set.disjoint_left.mpr (fun s hl hh => by
        change s.card ≤ k + e at hl
        change n - k ≤ s.card at hh
        omega))
    have hz := Submodule.disjoint_def.mp hd (chi univ * f.val)
      (heq ▸ low_mul f.property hp) (mul_parity_high f.property)
    have hh := congrArg (chi (univ : Finset (Fin n)) * ·) hz
    change chi univ * (chi univ * f.val) = chi univ * 0 at hh
    rw [← mul_assoc, chi_mul, symmDiff_self, Finset.bot_eq_empty, chi_empty,
      one_mul, mul_zero] at hh
    exact Subtype.ext hh
  let I : Finset (Finset (Fin n)) := univ.powersetCard k
  let v (s : I) : low n k := ⟨chi s.val, chi_low (mem_powersetCard.mp s.property).2.le⟩
  have hli : LinearIndependent K v := by
    apply LinearIndependent.of_comp (low n k).subtype
    exact chi_independent.comp _ Subtype.val_injective
  have h := (hli.map' restrict (LinearMap.ker_eq_bot.mpr hinj)).fintype_card_le_finrank
  simpa [I] using h

/-! ### Approximating unbounded fan-in gates -/

/-- A linear combination of the inputs detects at least half of any set of points
on which at least one input is nonzero. -/
private theorem detector {d : ℕ} (fs : List (Fn n)) (hf : ∀ f ∈ fs, f ∈ low n d)
    (T : Finset (Cube n)) (hT : ∀ x ∈ T, ∃ f ∈ fs, f x ≠ 0) :
    ∃ q ∈ low n d, (∀ x, (∀ f ∈ fs, f x = 0) → q x = 0) ∧
      2 * (T.filter fun x => q x = 0).card ≤ T.card := by
  classical
  induction fs generalizing T with
  | nil =>
    have h : T = ∅ := eq_empty_iff_forall_notMem.mpr (by simpa using hT)
    exact ⟨0, (low n d).zero_mem, by simp, by simp [h]⟩
  | cons f fs ih =>
    -- On the zero set of the first input, only the remaining inputs can detect a point.
    let A := T.filter fun x => f x = 0
    let B := T.filter fun x => f x ≠ 0
    have hAB : A.card + B.card = T.card := card_filter_add_card_filter_not ..
    obtain ⟨q, hq, hz, hA⟩ := ih (fun g hg => hf g (List.mem_cons_of_mem _ hg)) A (by
      intro x hx
      obtain ⟨hxT, hfx⟩ := mem_filter.mp hx
      obtain ⟨g, hg, hgx⟩ := hT x hxT
      exact ⟨g, (List.mem_cons.mp hg).resolve_left (fun h => hgx (h ▸ hfx)), hgx⟩)
    let Z (g : Fn n) (U : Finset (Cube n)) := U.filter fun x => g x = 0
    -- On its complement, at most one of the two linear forms vanishes at each point.
    have dis : Disjoint (Z q B) (Z (q + f) B) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      obtain ⟨hxB, hxq⟩ := mem_filter.mp hx
      have hxf := (mem_filter.mp hxB).2
      have hyq := (mem_filter.mp hy).2
      simp [Pi.add_apply, hxq, hxf] at hyq
    have hc : (Z q B).card + (Z (q + f) B).card ≤ B.card := by
      rw [← card_union_of_disjoint dis]
      exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    obtain ⟨g, hg, hB⟩ : ∃ g : Fn n, (g = q ∨ g = q + f) ∧ 2 * (Z g B).card ≤ B.card := by
      by_cases h : 2 * (Z q B).card ≤ B.card
      · exact ⟨q, Or.inl rfl, h⟩
      · exact ⟨q + f, Or.inr rfl, by omega⟩
    have hgA : Z g A = Z q A := by
      ext x
      by_cases h : x ∈ A
      · have hx := (mem_filter.mp h).2
        rcases hg with rfl | rfl <;> simp [Z, h, hx]
      · simp [Z, h]
    have hsum : (Z g A).card + (Z g B).card = (Z g T).card := by
      have e₁ : Z g A = (Z g T).filter fun x => f x = 0 := by ext; simp [Z, A, and_right_comm]
      have e₂ : Z g B = (Z g T).filter fun x => f x ≠ 0 := by ext; simp [Z, B, and_right_comm]
      rw [e₁, e₂, card_filter_add_card_filter_not]
    refine ⟨g, ?_, ?_, ?_⟩
    · rcases hg with rfl | rfl
      · exact hq
      · exact (low n _).add_mem hq (hf f List.mem_cons_self)
    · intro x hall
      have hx := hz x (fun a ha => hall a (List.mem_cons_of_mem _ ha))
      rcases hg with rfl | rfl
      · exact hx
      · simp [hx, hall f List.mem_cons_self]
    · change 2 * (Z g T).card ≤ T.card
      change 2 * (Z q A).card ≤ A.card at hA
      rw [hgA] at hsum
      omega

private theorem square_of_ne {z : K} (h : z ≠ 0) : z * z = 1 := by
  revert z
  decide

/-- Multiply successive zero tests. A nonzero field element squares to one, so each factor
removes at least half the points still to be detected. -/
private theorem approx_zero_aux {d : ℕ} (fs : List (Fn n)) (hf : ∀ f ∈ fs, f ∈ low n d)
    (r : ℕ) (T : Finset (Cube n)) (hT : ∀ x ∈ T, ∃ f ∈ fs, f x ≠ 0) :
    ∃ p ∈ low n (2 * r * d), (∀ x, (∀ f ∈ fs, f x = 0) → p x = 1) ∧
      ∃ B : Finset (Cube n), 2 ^ r * B.card ≤ T.card ∧ ∀ x ∈ T, x ∉ B → p x = 0 := by
  classical
  induction r generalizing T with
  | zero => exact ⟨1, low_one _, by simp, T, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨q, hq, hz, hhalf⟩ := detector fs hf T hT
    let U := T.filter fun x => q x = 0
    obtain ⟨p, hp, h1, B, hB, h0⟩ := ih U (fun x hx => hT x (mem_filter.mp hx).1)
    refine ⟨(1 - q * q) * p, ?_, ?_, B, ?_, ?_⟩
    · have hh := low_mul ((low n _).sub_mem (low_one _) (low_mul hq hq)) hp
      convert hh using 2
      ring
    · intro x hx
      simp [hz x hx, h1 x hx]
    · rw [pow_succ]
      change 2 * U.card ≤ T.card at hhalf
      linarith
    · intro x hx hxb
      by_cases hqx : q x = 0
      · simp [h0 x (mem_filter.mpr ⟨hx, hqx⟩) hxb]
      · simp [square_of_ne hqx]

private def bit (b : Bool) : K := if b then 1 else 0

private theorem approx_zero {d : ℕ} (fs : List (Fn n)) (hf : ∀ f ∈ fs, f ∈ low n d)
    (r : ℕ) : ∃ p ∈ low n (2 * r * d), ∃ B : Finset (Cube n),
      2 ^ r * B.card ≤ 2 ^ n ∧ ∀ x ∉ B,
        p x = bit (fs.all fun f => decide (f x = 0)) := by
  classical
  let T := univ.filter fun x : Cube n => ∃ f ∈ fs, f x ≠ 0
  obtain ⟨p, hp, h1, B, hB, h0⟩ := approx_zero_aux fs hf r T (fun x hx => (mem_filter.mp hx).2)
  refine ⟨p, hp, B, hB.trans ?_, ?_⟩
  · simpa [Cube, Fintype.card_pi] using T.card_le_univ
  · intro x hx
    by_cases hall : ∀ f ∈ fs, f x = 0
    · simpa [bit, h1 x hall] using hall
    · have hT : x ∈ T := by simpa [T] using hall
      rw [h0 x hT hx]
      simp [bit, hall]

private theorem bit_not (b : Bool) : bit (!b) = 1 - bit b := by cases b <;> simp [bit]

private theorem bit_coord (i : Fin n) : (fun x : Cube n => bit (x i)) ∈ low n 1 := by
  have h : (fun x : Cube n => bit (x i)) = chi {i} - 1 := by
    funext x
    simp only [Pi.sub_apply, Pi.one_apply, chi, mem_singleton, prod_ite_eq', mem_univ, ite_true]
    cases x i <;> decide
  rw [h]
  exact (low n 1).sub_mem (chi_low (by simp)) (low_one _)

private theorem sum_bits (l : List ℕ) (v : ℕ → Bool) :
    ((l.map (fun i => bit (v i))).sum : K) = ((l.filter v).length : ℕ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    cases h : v i <;> simp [h, bit, add_comm]

private theorem bit_mod (l : List ℕ) (v : ℕ → Bool) :
    bit (decide ((l.filter v).length % 3 = 0)) =
      1 - (l.map (fun i => bit (v i))).sum * (l.map (fun i => bit (v i))).sum := by
  rw [sum_bits]
  have hh : (((l.filter v).length : ℕ) : K) = 0 ↔ (l.filter v).length % 3 = 0 := by
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  by_cases h : (l.filter v).length % 3 = 0
  · simp [bit, h, hh.mpr h]
  · simp [bit, h, square_of_ne (mt hh.mp h)]

private theorem sum_low {d : ℕ} (fs : List (Fn n)) (hf : ∀ f ∈ fs, f ∈ low n d) :
    fs.sum ∈ low n d := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    exact (low n _).add_mem (hf f List.mem_cons_self) (ih fun g h => hf g (by simp [h]))

private theorem le_maximum {a : ℕ} {l : List ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · exact le_max_left ..
    · exact (ih hm).trans (le_max_right ..)

open Cslib.Complexity.Classes

/-! ### From gates to flat circuits -/

private def predBound (ds : List ℕ) (l : List ℕ) :=
  (l.map fun i => ds.getD i 0).foldr max 0

private theorem approx_gate (r : ℕ) (hr : 0 < r) (ds : List ℕ) (w : ℕ → Fn n)
    (hw : ∀ i, w i ∈ low n ((2 * r) ^ ds.getD i 0))
    (g : ACGate n) (hm : ModOnly 3 [g]) :
    ∃ p ∈ low n ((2 * r) ^ gateDepthOf ds g), ∃ B : Finset (Cube n),
      2 ^ r * B.card ≤ 2 ^ n ∧ ∀ x ∉ B, ∀ vs : List Bool,
        (∀ i, w i x = bit (vs.getD i false)) → p x = bit (gateValue vs x g) := by
  classical
  have hpos : 0 < 2 * r := by omega
  have hw' (l : List ℕ) (i : ℕ) (hi : i ∈ l) : w i ∈ low n ((2 * r) ^ predBound ds l) :=
    low_mono (Nat.pow_le_pow_right hpos (le_maximum (List.mem_map_of_mem (f := (ds.getD · 0)) hi)))
      (hw i)
  cases g with
  | const b =>
    refine ⟨(fun _ => bit b), ?_, ∅, by simp, by simp [gateValue]⟩
    cases b
    · exact (low n _).zero_mem
    · exact low_one _
  | var i => exact ⟨_, bit_coord i, ∅, by simp, by simp [gateValue]⟩
  | notGate i =>
    refine ⟨1 - w i, ?_, ∅, by simp, ?_⟩
    · exact low_mono (Nat.pow_le_pow_right hpos (Nat.le_succ _))
        ((low n _).sub_mem (low_one _) (hw i))
    · intro x _ vs hv
      simp [gateValue, bit_not, hv]
  | orGate l =>
    obtain ⟨p, hp, B, hB, hall⟩ := approx_zero (l.map w)
      (fun f h => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
        exact hw' l i hi) r
    refine ⟨1 - p, ?_, B, hB, ?_⟩
    · simpa [gateDepthOf, predBound, pow_succ, Nat.mul_comm] using
        (low n _).sub_mem (low_one _) hp
    · intro x hx vs hv
      simp [hall x hx, bit, gateValue, hv, List.all_map, Function.comp_def]
      split_ifs <;> simp_all
      grind
  | andGate l =>
    obtain ⟨p, hp, B, hB, hall⟩ := approx_zero (l.map (fun i => 1 - w i))
      (fun f h => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
        exact (low n _).sub_mem (low_one _) (hw' l i hi)) r
    refine ⟨p, ?_, B, hB, ?_⟩
    · simpa [gateDepthOf, predBound, pow_succ, Nat.mul_comm] using hp
    · intro x hx vs hv
      have hh (b : Bool) : (1 - bit b = 0) ↔ b = true := by cases b <;> decide
      rw [hall x hx]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp [gateValue, hv, hh]
  | modGate m l =>
    have hm' : m = 3 := hm (.modGate m l) List.mem_cons_self
    subst m
    let q := (l.map w).sum
    have hq : q ∈ low n ((2 * r) ^ predBound ds l) := sum_low _ (by simpa using hw' l)
    refine ⟨1 - q * q, ?_, ∅, by simp, ?_⟩
    · apply low_mono _ ((low n _).sub_mem (low_one _) (low_mul hq hq))
      change _ ≤ (2 * r) ^ (predBound ds l + 1)
      rw [pow_succ, ← two_mul, Nat.mul_comm ((2 * r) ^ _)]
      gcongr
      omega
    · intro x _ vs hv
      have he : q x = (l.map fun i => bit (vs.getD i false)).sum := by
        dsimp [q]
        clear hq q hm
        induction l with
        | nil => rfl
        | cons i l ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, hv, ih]
      simp [gateValue, he, bit_mod]

private theorem getD_snoc {α : Type*} (l : List α) (a d : α) (j : ℕ) :
    (l ++ [a]).getD j d = if j = l.length then a else l.getD j d := by
  by_cases h : j < l.length
  · rw [List.getD_append _ _ _ _ h]
    simp only [h.ne, ite_false]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  split_ifs with heq
  · simp [heq]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- Outside a common exceptional set, all gate approximants give their true values.
Each new gate contributes its own errors to the union once, regardless of its fan-out. -/
private theorem approx_circuit (r : ℕ) (hr : 0 < r) (C : List (ACGate n)) (hm : ModOnly 3 C) :
    ∃ w : ℕ → Fn n, (∀ i, w i ∈ low n ((2 * r) ^ (circuitDepths C).getD i 0)) ∧
      ∃ B : Finset (Cube n), 2 ^ r * B.card ≤ C.length * 2 ^ n ∧ ∀ x ∉ B,
        ∀ i, w i x = bit ((circuitEval C x).getD i false) := by
  classical
  induction C using List.reverseRecOn with
  | nil =>
    refine ⟨0, fun _ => (low n _).zero_mem, ∅, by simp, ?_⟩
    simp [circuitEval, bit]
  | append_singleton C g ih =>
    obtain ⟨w, hw, B, hB, he⟩ := ih (fun a ha => hm a (by simp [ha]))
    obtain ⟨p, hp, U, hU, hg⟩ := approx_gate r hr _ w hw g
      (fun a ha => hm a (List.mem_append_right _ ha))
    refine ⟨fun i => if i = C.length then p else w i, ?_, B ∪ U, ?_, ?_⟩
    · intro i
      rw [circuitDepths_append_singleton, getD_snoc, length_circuitDepths]
      dsimp only
      split_ifs
      · exact hp
      · exact hw i
    · calc
        _ ≤ 2 ^ r * (B.card + U.card) := Nat.mul_le_mul_left _ (card_union_le ..)
        _ ≤ C.length * 2 ^ n + 2 ^ n := by rw [Nat.mul_add]; omega
        _ = _ := by simp [Nat.add_mul]
    · intro x hx i
      have ⟨hxB, hxU⟩ := not_or.mp (mt mem_union.mpr hx)
      rw [circuitEval_append_singleton, getD_snoc, length_circuitEval]
      dsimp only
      split_ifs
      · exact hg x hxU _ (he x hxB)
      · exact he x hxB i

private theorem chi_parity (x : Cube n) :
    chi univ x = 1 + bit (parityDec (List.ofFn x)) := by
  have hprod (l : List Bool) :
      (l.map sign).prod = (-1 : K) ^ (l.filter id).length := by
    induction l with
    | nil => simp
    | cons a l ih => cases a <;> simp [sign, ih, pow_succ]
  have h : chi univ x = (-1 : K) ^ ((List.ofFn x).filter id).length := by
    simpa [chi, List.map_ofFn, Fin.prod_ofFn, Function.comp_def] using hprod (List.ofFn x)
  rw [h]
  unfold parityDec
  change (-1 : K) ^ _ = 1 + bit (decide (((List.ofFn x).filter id).length % 2 = 1))
  generalize ((List.ofFn x).filter id).length = t
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · simp [bit, h, Even.neg_one_pow ((Nat.even_iff).mpr h)]
  · rw [Odd.neg_one_pow (Nat.odd_iff.mpr h)]
    simp only [bit, h, decide_true, ite_true]
    decide

/-! ### Comparing the error bounds -/

/-- Within `D` steps of the middle layer, the binomial coefficient retains at least half
of its central value when `m` dominates the square of `D`. -/
private theorem near_middle (m D : ℕ) (hm : 0 < m) (hD : D ≤ m)
    (hwide : 2 * (D * (2 * D + 1)) ≤ m) :
    m.centralBinom ≤ 2 * (2 * m).choose (m - D) := by
  let c (j : ℕ) := (2 * m).choose (m - j)
  have hc (j : ℕ) : c j ≤ m.centralBinom := Nat.choose_le_centralBinom _ _
  have step (j : ℕ) (hj : j < D) :
      m * c j ≤ m * c (j + 1) + (2 * D + 1) * m.centralBinom := by
    have he := Nat.choose_succ_right_eq (2 * m) (m - (j + 1))
    rw [show m - (j + 1) + 1 = m - j by omega,
      show 2 * m - (m - (j + 1)) = m + j + 1 by omega] at he
    change c j * (m - j) = c (j + 1) * (m + j + 1) at he
    have h₁ := Nat.mul_le_mul (hc j) (show j ≤ D by omega)
    have h₂ := Nat.mul_le_mul (hc (j + 1)) (show j + 1 ≤ D + 1 by omega)
    have h₃ : m - j + j = m := by omega
    nlinarith only [he, h₁, h₂, congrArg (c j * ·) h₃]
  have bound (j : ℕ) (hj : j ≤ D) :
      m * m.centralBinom ≤ m * c j + j * ((2 * D + 1) * m.centralBinom) := by
    induction j with
    | zero => simp [c, Nat.centralBinom]
    | succ j ih =>
      have h := step j (by omega)
      have hh := ih (by omega)
      rw [Nat.succ_mul]
      omega
  have h := bound D le_rfl
  change m.centralBinom ≤ 2 * c D
  apply Nat.le_of_mul_le_mul_left _ hm
  nlinarith only [h, Nat.mul_le_mul_right m.centralBinom hwide]

private theorem exists_parameter (Q : Polynomial ℕ) : ∃ r > 0, Q.eval r < 2 ^ r := by
  have hP (P : Polynomial ℕ) :
      Filter.Tendsto (fun k : ℕ => ((P.eval k : ℕ) : ℝ) / 2 ^ k)
        Filter.atTop (nhds 0) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa [add_div] using hp.add hq
    | monomial e a =>
      simpa [Polynomial.eval_monomial, Nat.cast_mul, Nat.cast_pow, mul_div_assoc] using
        (tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : 1 < (2 : ℝ))).const_mul (a : ℝ)
  obtain ⟨k, hk, hpos⟩ := ((hP Q).eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    |>.and (Filter.eventually_gt_atTop 0)).exists
  refine ⟨k, hpos, ?_⟩
  have hh := (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mp hk
  exact_mod_cast (show ((Q.eval k : ℕ) : ℝ) < 2 ^ k by simpa using hh)

private theorem gate_depth_le (C : List (ACGate n)) (i : ℕ) :
    (circuitDepths C).getD i 0 ≤ circuitDepth C := by
  by_cases h : i < (circuitDepths C).length
  · rw [List.getD_eq_getElem _ _ h]
    exact le_maximum (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- **Smolensky: parity is not in AC0[mod 3].** The parity language, which accepts a bitstring
exactly when an odd number of its entries are true, is not in $\mathsf{AC}^0[3]$, the class
$\mathsf{AC}^0[m]$ for $m = 3$ of decision problems decided by polynomial-size, bounded-depth
families of well-formed flat Boolean circuits in which every mod gate has modulus $3$.

Source: R. Smolensky, "Algebraic methods in
the theory of lower bounds for Boolean circuit complexity", Proceedings of the Nineteenth
Annual ACM Symposium on Theory of Computing (STOC 1987), 77-82. -/
public theorem smolensky :
    parityDec ∉ AC0Mod 3 := by
  classical
  rintro ⟨d, size, C, hC⟩
  -- Choose the input length polynomially in the number of tests per gate.
  let E : Polynomial ℕ := (2 * Polynomial.X) ^ d
  let M : Polynomial ℕ := 4 * (E + 1) ^ 2
  let N : Polynomial ℕ := 2 * M
  obtain ⟨r, hr, hparam⟩ := exists_parameter (N * size.comp N)
  let D := (2 * r) ^ d
  let m := 4 * (D + 1) ^ 2
  let n := 2 * m
  have hparam' : n * size.eval n < 2 ^ r := by
    simpa [N, M, E, n, m, D, Polynomial.eval_comp] using hparam
  have hD : 0 < D := pow_pos (by omega) _
  have hm : 4 ≤ m := by dsimp [m]; nlinarith
  obtain ⟨_, hmod, hsize, hdepth, hdec⟩ := hC n
  obtain ⟨w, hw, B, hB, hagree⟩ := approx_circuit r hr (C n) hmod
  let j := (C n).length - 1
  have hp : 1 + w j ∈ low n D := (low n _).add_mem (low_one _)
    (low_mono (Nat.pow_le_pow_right (by omega) ((gate_depth_le _ _).trans hdepth)) (hw j))
  have heq (x : Cube n) (hx : x ∉ B) : (1 + w j) x = chi univ x := by
    rw [chi_parity, Pi.add_apply, Pi.one_apply, hagree x hx]
    congr 2
    apply Bool.eq_iff_iff.mpr
    have hc := hdec (List.ofFn x) (List.length_ofFn)
    have he : (fun i : Fin n => (List.ofFn x).getD i.val false) = x := by
      funext i
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    rw [he, List.getLast?_eq_getElem?, length_circuitEval] at hc
    rw [List.getD_eq_getElem?_getD]
    change ((circuitEval (C n) x)[j]?.getD false = true) ↔ _
    rw [hc]
    cases (circuitEval (C n) x)[j]? with
    | none => simp
    | some b => cases b <;> simp
  have hkm : D ≤ m := by dsimp [m]; nlinarith
  have hk : (m - D) + D < n - (m - D) := by dsimp [n]; omega
  have lower := errors_ge_choose hp hk B heq
  have near := near_middle m D (by omega) hkm (by dsimp [m]; nlinarith)
  have hbad : 2 ^ n < n * B.card := calc
    2 ^ n = 4 ^ m := by change 2 ^ (2 * m) = _; rw [pow_mul]; rfl
    _ < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom _ hm
    _ ≤ m * (2 * B.card) := Nat.mul_le_mul_left _ (near.trans (Nat.mul_le_mul_left 2 lower))
    _ = _ := by dsimp [n]; ring
  have hpos : 0 < B.card := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hbad
  have hupper := hB.trans (Nat.mul_le_mul_right (2 ^ n) hsize)
  nlinarith only [hupper, Nat.mul_le_mul_left (size.eval n) hbad.le,
    Nat.mul_lt_mul_of_pos_right hparam' hpos]

end MetaMathlibExt.Complexity.KeyTheorems.Smolensky
