/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GaussKuzminSymmetry
import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nontrivial Gauss–Kuzmin symmetries

This module proves that positive strings of length three have no nontrivial symmetry and that
there are infinitely many positive strings with nontrivial symmetries at every length at least
four. It also proves that positive strings of the same length parity have equal Gauss–Kuzmin
masses exactly when their characteristic numbers agree, and constructs infinite families of stable
strings at each length at least two.

## References

* Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
  Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
  pp. 1–32, Lemma 2.2(i), Lemma 5.2, Lemma 5.5 and Theorem 3.
* Karma Dajani and Cor Kraaikamp, *Ergodic Theory of Numbers*, Carus Mathematical Monographs 29,
  Mathematical Association of America, 2002, §1.3.2; cited for the convergent matrix product in
  equation (2.5) of Singh, Zhang and Hildebrand.
* Oskar Perron, *Die Lehre von den Kettenbrüchen. Bd I. Elementare Kettenbrüche*, B. G. Teubner,
  1954, §5; cited for an equivalent form of the convergent matrix product.
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Real

private theorem entries (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 ≤ convergentMatrix a 0 0 ∧ 0 ≤ convergentMatrix a 0 1 ∧
      0 ≤ convergentMatrix a 1 0 ∧ 1 ≤ convergentMatrix a 1 1 := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    obtain ⟨h00, h01, h10, h11⟩ := ih (fun x hx => ha x (List.mem_cons_of_mem t hx))
    have ht : (1 : ℤ) ≤ t := by exact_mod_cast ha t (List.mem_cons_self)
    simp only [convergentMatrix_cons, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, one_mul,
      zero_add]
    exact ⟨h10, by omega, by positivity, by nlinarith⟩

private theorem determinant (a : List ℕ) :
    (convergentMatrix a).det = (-1 : ℤ) ^ a.length := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    rw [convergentMatrix_cons, Matrix.det_mul, ih]
    simp [Matrix.det_fin_two, pow_succ, mul_comm]

private theorem reverse_matrix (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    convergentMatrix a.reverse = (convergentMatrix a).transpose := by
  rw [(convergentMatrix_reverse_append_cons a ha 1 (by decide)).1]
  exact (Matrix.eta_fin_two (convergentMatrix a).transpose).symm

private theorem characteristic_reverse (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    characteristicNumber a.reverse = characteristicNumber a := by
  simp [characteristicNumber, reverse_matrix a ha, mul_comm]

private theorem cylinder_interval (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    cfCylinder a =ᵐ[volume]
      fundInterval ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))
        (((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 0 0 : ℝ)) /
          ((convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 1 0 : ℝ))) := by
  have hr : ∀ x ∈ a.reverse, 0 < x := fun x hx => ha x (List.mem_reverse.mp hx)
  have h := (cfCylinder_reverse_append_cons_ae_eq a.reverse hr 1 (by decide)).1
  simp only [List.reverse_reverse, List.length_reverse, reverse_matrix a ha,
    Matrix.transpose_apply] at h
  obtain ⟨h00, h01, h10, h11⟩ := entries a ha
  have hq : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) := by
    exact_mod_cast (by omega : 0 < convergentMatrix a 1 1)
  have hr0 : (0 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10
  have hsum : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 1 0 : ℝ) := by linarith
  have hd : (convergentMatrix a 0 0 : ℝ) * (convergentMatrix a 1 1 : ℝ) -
      (convergentMatrix a 0 1 : ℝ) * (convergentMatrix a 1 0 : ℝ) = (-1 : ℝ) ^ a.length := by
    have hd := determinant a
    rw [Matrix.det_fin_two] at hd
    exact_mod_cast hd
  convert h using 1
  congr 1
  field_simp
  nlinarith [hd]

private theorem mass_formula (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    gaussKuzminMass a =
      (-1 : ℝ) ^ a.length * log (1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ)) /
        log 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := entries a ha
  let p : ℝ := convergentMatrix a 0 1
  let q : ℝ := convergentMatrix a 1 1
  let r : ℝ := convergentMatrix a 1 0
  let s : ℝ := convergentMatrix a 0 0
  have hp : 0 ≤ p := by dsimp [p]; exact_mod_cast h01
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (by omega : 0 < convergentMatrix a 1 1)
  have hr : 0 ≤ r := by dsimp [r]; exact_mod_cast h10
  have hs : 0 ≤ s := by dsimp [s]; exact_mod_cast h00
  have hqr : 0 < q + r := by linarith
  have hpq : 0 < p + q := by linarith
  have hd : s * q - p * r = (-1 : ℝ) ^ a.length := by
    have hd := determinant a
    rw [Matrix.det_fin_two] at hd
    dsimp [p, q, r, s]
    exact_mod_cast hd
  have he : (p + s) / (q + r) - p / q = (-1 : ℝ) ^ a.length / (q * (q + r)) := by
    field_simp
    nlinarith [hd]
  have hratio : (1 + (p + s) / (q + r)) / (1 + p / q) =
      1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ) := by
    have hc : (characteristicNumber a : ℝ) = (p + q) * (q + r) := by
      simp [characteristicNumber, p, q, r, add_comm]
    rw [hc]
    field_simp
    nlinarith [hd]
  have hint : (∫ x in p / q..(p + s) / (q + r), 1 / (1 + x)) =
      log (1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ)) := by
    rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => 1 / x) 1,
      integral_one_div_of_pos (by positivity) (by positivity), hratio]
  rw [gaussKuzminMass, setIntegral_congr_set (cylinder_interval a ha)]
  change (∫ x in fundInterval (p / q) ((p + s) / (q + r)), 1 / (1 + x)) / log 2 = _
  rcases neg_one_pow_eq_or ℝ a.length with hsign | hsign
  · have hlt : p / q < (p + s) / (q + r) := by
      rw [hsign] at he
      have : 0 < 1 / (q * (q + r)) := by positivity
      linarith
    rw [fundInterval_of_lt hlt, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hlt.le, hint, hsign, one_mul]
  · have hlt : (p + s) / (q + r) < p / q := by
      rw [hsign] at he
      have : (-1 : ℝ) / (q * (q + r)) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
      linarith
    rw [fundInterval, ite_eq_right (not_lt.mpr hlt.le)]
    have hi := intervalIntegral.integral_of_ge (f := fun x : ℝ => 1 / (1 + x)) (μ := volume) hlt.le
    rw [hint, hsign] at hi
    rw [hsign]
    rw [neg_one_mul]
    congr 1
    linarith

private theorem characteristic_lower (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ []) :
    2 ≤ characteristicNumber a := by
  obtain ⟨h00, h01, h10, h11⟩ := entries a ha
  have hp : 1 ≤ convergentMatrix a 0 1 := by
    cases a with
    | nil => exact False.elim (hne rfl)
    | cons t a =>
      have h := (entries a (fun x hx => ha x (List.mem_cons_of_mem t hx))).2.2.2
      simpa [convergentMatrix_cons, Matrix.mul_apply, Fin.sum_univ_two] using h
  unfold characteristicNumber
  nlinarith

private theorem log_argument_pos (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 < 1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ) := by
  by_cases h : a = []
  · subst a
    norm_num [characteristicNumber_nil]
  · have hc : (1 : ℝ) < (characteristicNumber a : ℝ) := by
      exact_mod_cast (by have := characteristic_lower a ha h; omega : 1 < characteristicNumber a)
    rcases neg_one_pow_eq_or ℝ a.length with hs | hs
    · rw [hs]
      positivity
    · rw [hs, neg_div]
      have hi : 1 / (characteristicNumber a : ℝ) < 1 := (div_lt_one (by linarith)).2 hc
      linarith

/-- **Gauss–Kuzmin masses agree exactly when characteristic numbers do.** Write $P_{GK}$ for the
Gauss–Kuzmin mass and $\chi$ for the characteristic number of a string. If $a$ and $b$ are strings
of positive integers whose lengths have the same parity, then $P_{GK}(a) = P_{GK}(b)$ if and only
if $\chi(a) = \chi(b)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.2 (`integers-2025-A89-lem-5-2`). -/
public theorem gaussKuzminMass_eq_iff_characteristicNumber_eq (a b : List ℕ)
    (ha : (∀ x ∈ a, 0 < x)) (hb : ∀ x ∈ b, 0 < x) (hpar : a.length % 2 = b.length % 2) :
    gaussKuzminMass a = gaussKuzminMass b ↔ characteristicNumber a = characteristicNumber b := by
  have hsign : (-1 : ℝ) ^ b.length = (-1 : ℝ) ^ a.length := by
    rw [neg_one_pow_eq_pow_mod_two a.length, neg_one_pow_eq_pow_mod_two b.length, hpar]
  rw [mass_formula a ha, mass_formula b hb, hsign]
  have hs : (-1 : ℝ) ^ a.length ≠ 0 := pow_ne_zero _ (by norm_num)
  have hl : log (2 : ℝ) ≠ 0 := ne_of_gt (log_pos (by norm_num))
  rw [div_left_inj₀ hl, mul_right_inj' hs]
  constructor
  · intro h
    have he := strictMonoOn_log.injOn (log_argument_pos a ha)
      (by simpa [hsign] using log_argument_pos b hb) h
    have hd : (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ) =
        (-1 : ℝ) ^ a.length / (characteristicNumber b : ℝ) := by linarith
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_inj' hs] at hd
    exact_mod_cast inv_injective hd
  · intro h
    rw [h]

private theorem permutations_three (x y z : ℕ) (b : List ℕ) (hb : b.Perm [x, y, z]) :
    b = [x, y, z] ∨ b = [x, z, y] ∨ b = [y, x, z] ∨
      b = [y, z, x] ∨ b = [z, x, y] ∨ b = [z, y, x] := by
  have h := List.mem_permutations'.2 hb
  simpa [List.permutations', List.permutations'Aux, or_comm, or_left_comm, or_assoc] using h

private theorem triple (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ HasNontrivialSymmetry [x, y, z] := by
  rintro ⟨b, hp, hn, hr, hm⟩
  have ha : ∀ t ∈ [x, y, z], 0 < t := by simpa using And.intro hx (And.intro hy hz)
  have hb : ∀ t ∈ b, 0 < t := fun t ht => ha t (hp.mem_iff.mp ht)
  have hc := (gaussKuzminMass_eq_iff_characteristicNumber_eq b [x, y, z] hb ha
    (congrArg (· % 2) hp.length_eq)).1 hm
  have hrev : characteristicNumber [z, y, x] = characteristicNumber [x, y, z] :=
    characteristic_reverse [x, y, z] ha
  rcases permutations_three x y z b hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hn rfl
  · have hyz : y ≠ z := by intro h; subst z; exact hn rfl
    have h := characteristicNumber_swap_ne z y x hz hy hx hyz.symm
    apply h
    have hc' : characteristicNumber [y, z, x] = characteristicNumber [x, z, y] :=
      characteristic_reverse [x, z, y] hb
    exact hrev.trans (hc.symm.trans hc'.symm)
  · have hxy : x ≠ y := by intro h; subst y; exact hn rfl
    exact characteristicNumber_swap_ne x y z hx hy hz hxy hc.symm
  · have hyz : y ≠ z := by intro h; subst z; exact hr rfl
    exact characteristicNumber_swap_ne z y x hz hy hx hyz.symm (hrev.trans hc.symm)
  · have hxy : x ≠ y := by intro h; subst y; exact hr rfl
    have hc' : characteristicNumber [y, x, z] = characteristicNumber [z, x, y] :=
      characteristic_reverse [z, x, y] hb
    exact characteristicNumber_swap_ne x y z hx hy hz hxy (hc.symm.trans hc'.symm)
  · exact hr rfl

private theorem length_three (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hlen : a.length = 3) :
    ¬ HasNontrivialSymmetry a := by
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z, a = [x, y, z] := by
    rcases a with _ | ⟨x, a⟩ <;> simp only [List.length_nil, List.length_cons] at hlen
    · omega
    rcases a with _ | ⟨y, a⟩ <;> simp only [List.length_nil, List.length_cons] at hlen
    · omega
    rcases a with _ | ⟨z, a⟩ <;> simp only [List.length_nil, List.length_cons] at hlen
    · omega
    have : a = [] := List.length_eq_zero_iff.mp (by omega)
    subst a
    exact ⟨x, y, z, rfl⟩
  exact triple x y z (ha x (by simp)) (ha y (by simp)) (ha z (by simp))

private theorem append_matrix (a b : List ℕ) :
    convergentMatrix (a ++ b) = convergentMatrix a * convergentMatrix b := by
  simp [convergentMatrix]

private theorem append_digit (a : List ℕ) (d : ℕ) :
    convergentMatrix (a ++ [d]) = convergentMatrix a * !![0, 1; 1, (d : ℤ)] := by
  simp [convergentMatrix]

private theorem stable_extend (a : List ℕ) (ha : ∀ x ∈ a, 0 < x)
    (hst : IsStableString a) (t : ℕ) : IsStableString (t :: a.reverse ++ [2 * t]) := by
  unfold IsStableString at hst ⊢
  simp [append_matrix, convergentMatrix_cons, convergentMatrix_nil, reverse_matrix a ha, hst,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

private def plus (a : List ℕ) : List ℕ :=
  2 :: 1 :: (a.reverse.modifyHead (· + 1)).reverse

private theorem plus_injective : Function.Injective plus := by
  have hi : Function.Injective (fun a : List ℕ => a.modifyHead (· + 1)) := by
    intro a b h
    cases a <;> cases b <;> simp_all
  intro a b h
  have he : (a.reverse.modifyHead (· + 1)).reverse =
      (b.reverse.modifyHead (· + 1)).reverse := (List.cons.inj (List.cons.inj h).2).2
  exact List.reverse_injective (hi (List.reverse_injective he))

private theorem plus_append (a : List ℕ) (d : ℕ) :
    plus (a ++ [d]) = 2 :: 1 :: (a ++ [d + 1]) := by
  simp [plus]

private theorem plus_positive (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ []) :
    ∀ x ∈ plus a, 0 < x := by
  rw [← List.dropLast_append_getLast hne, plus_append]
  intro x hx
  simp only [List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | hx | rfl
  · decide
  · decide
  · exact ha x (List.mem_of_mem_dropLast hx)
  · omega

private theorem plus_length (a : List ℕ) : (plus a).length = a.length + 2 := by
  simp [plus]

private theorem plus_symmetry (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ [])
    (hst : IsStableString a) : HasNontrivialSymmetry (plus a) := by
  let l := a.dropLast
  let d := a.getLast hne
  have hd : 0 < d := ha d (List.getLast_mem hne)
  have hl : ∀ x ∈ l, 0 < x := fun x hx => ha x (List.mem_of_mem_dropLast hx)
  have he : a = l ++ [d] := (List.dropLast_append_getLast hne).symm
  have hap : plus a = 2 :: 1 :: (l ++ [d + 1]) := by rw [he, plus_append]
  let b := l ++ [d + 1]
  have hb : ∀ x ∈ b, 0 < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hl x hx
    · simp only [List.mem_singleton] at hx
      subst x
      omega
  have hstable : convergentMatrix b 0 1 = convergentMatrix b 0 0 +
      2 * convergentMatrix b 1 0 := by
    rw [he] at hst
    change convergentMatrix (l ++ [d + 1]) 0 1 =
      convergentMatrix (l ++ [d + 1]) 0 0 + 2 * convergentMatrix (l ++ [d + 1]) 1 0
    simp [IsStableString, append_digit, Matrix.mul_apply, Fin.sum_univ_two] at hst ⊢
    linarith
  have hc : characteristicNumber (2 :: b.reverse ++ [1]) =
      characteristicNumber (2 :: 1 :: b) := by
    simp [characteristicNumber, append_matrix, convergentMatrix_cons, convergentMatrix_nil,
      reverse_matrix b hb, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hstable]
    ring
  have hp : (2 :: b.reverse ++ [1]).Perm (plus a) := by
    rw [hap]
    change (2 :: (b.reverse ++ [1])).Perm (2 :: 1 :: b)
    exact ((List.reverse_perm b).append_right [1]).trans (List.perm_append_comm) |>.cons 2
  have hn : 2 :: b.reverse ++ [1] ≠ plus a := by
    rw [hap]
    simp [b]
    omega
  have hr : 2 :: b.reverse ++ [1] ≠ (plus a).reverse := by
    intro h
    have ht := congrArg (fun c : List ℕ => c.reverse.head?) h
    simp [plus] at ht
  have hsg : ∀ x ∈ 2 :: b.reverse ++ [1], 0 < x := by
    intro x hx
    simp only [List.mem_cons, List.mem_append, List.mem_nil_iff, or_false,
      List.mem_reverse] at hx
    rcases hx with (rfl | hx) | rfl
    · decide
    · exact hb x hx
    · decide
  refine ⟨2 :: b.reverse ++ [1], hp, hn, hr, ?_⟩
  apply (gaussKuzminMass_eq_iff_characteristicNumber_eq _ _ hsg (plus_positive a ha hne)
    (congrArg (· % 2) hp.length_eq)).2
  simpa [hap] using hc

private theorem stable_pair (t : ℕ) : IsStableString [t, 2 * t] := by
  simp [IsStableString, convergentMatrix_cons, convergentMatrix_nil, Matrix.mul_apply,
    Fin.sum_univ_two]

private theorem stable_triple (t : ℕ) : IsStableString [t, 1, 2 * t + 1] := by
  simp [IsStableString, convergentMatrix_cons, convergentMatrix_nil, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

private theorem stable_family (n : ℕ) (hn : 2 ≤ n) :
    ∃ f : ℕ → List ℕ, Function.Injective f ∧
      ∀ t, (f t).length = n ∧ (∀ x ∈ f t, 0 < x) ∧ IsStableString (f t) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h2 : n = 2
    · subst n
      refine ⟨fun t => [t + 1, 2 * (t + 1)], ?_, ?_⟩
      · intro s t h
        have he := congrArg List.head? h
        simpa using he
      · intro t
        refine ⟨rfl, ?_, stable_pair (t + 1)⟩
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro x (rfl | rfl) <;> omega
    · by_cases h3 : n = 3
      · subst n
        refine ⟨fun t => [t + 1, 1, 2 * (t + 1) + 1], ?_, ?_⟩
        · intro s t h
          have he := congrArg List.head? h
          simpa using he
        · intro t
          refine ⟨rfl, ?_, stable_triple (t + 1)⟩
          simp only [List.mem_cons, List.mem_nil_iff, or_false]
          rintro x (rfl | rfl | rfl) <;> omega
      · obtain ⟨f, -, hf⟩ := ih (n - 2) (by omega) (by omega)
        obtain ⟨hlen, hpos, hstable⟩ := hf 0
        let a := f 0
        refine ⟨fun t => (t + 1) :: a.reverse ++ [2 * (t + 1)], ?_, ?_⟩
        · intro s t h
          have he := congrArg List.head? h
          simpa using he
        · intro t
          refine ⟨?_, ?_, stable_extend a hpos hstable (t + 1)⟩
          · simp only [List.length_append, List.length_cons, List.length_reverse]
            change (f 0).length + 1 + 1 = n
            omega
          · intro x hx
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff,
              or_false, List.mem_reverse] at hx
            rcases hx with (rfl | hx) | rfl
            · omega
            · exact hpos x hx
            · omega

private theorem infinite_symmetries (n : ℕ) (hn : 4 ≤ n) :
    {a : List ℕ | a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ HasNontrivialSymmetry a}.Infinite := by
  obtain ⟨f, hi, hf⟩ := stable_family (n - 2) (by omega)
  apply (Set.infinite_range_of_injective (plus_injective.comp hi)).mono
  rintro a ⟨t, rfl⟩
  obtain ⟨hlen, hpos, hstable⟩ := hf t
  have hne : f t ≠ [] := by intro h; simp [h] at hlen; omega
  refine ⟨?_, plus_positive (f t) hpos hne, plus_symmetry (f t) hpos hne hstable⟩
  change (plus (f t)).length = n
  rw [plus_length, hlen]
  omega

/-- **No nontrivial symmetries in length three, infinitely many from length four.** (i) No string
of three positive integers has a nontrivial symmetry. (ii) For every $n \ge 4$ there are infinitely
many strings of $n$ positive integers that have a nontrivial symmetry.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 3 (`integers-2025-A89-thm-3`). -/
public theorem nontrivialSymmetry_length_three_and_infinite :
    (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length = 3 → ¬ HasNontrivialSymmetry a) ∧
      ∀ n : ℕ, 4 ≤ n →
        {a : List ℕ | a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ HasNontrivialSymmetry a}.Infinite
    := by
  exact ⟨length_three, infinite_symmetries⟩

/-- **Families of stable strings.** (i) For every positive integer $t$, the strings $(t, 2t)$ and
$(t, 1, 2t + 1)$ are stable. (ii) If $a = (a_1, \dots, a_m)$ is a stable string of positive
integers, then for every positive integer $t$ the string $(t, a_m, \dots, a_1, 2t)$, obtained from
the reverse of $a$ by adding $t$ at the front and $2t$ at the end, is stable. (iii) For every
$n \ge 2$ there are infinitely many stable strings of $n$ positive integers.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.5 (`integers-2025-A89-lem-5-5`). -/
public theorem isStableString_families :
    (∀ t : ℕ, 1 ≤ t → IsStableString [t, 2 * t] ∧ IsStableString [t, 1, 2 * t + 1]) ∧
      (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → IsStableString a → ∀ t : ℕ, 1 ≤ t →
        IsStableString (t :: a.reverse ++ [2 * t])) ∧
      ∀ n : ℕ, 2 ≤ n →
        {a : List ℕ | a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ IsStableString a}.Infinite := by
  refine ⟨fun t _ => ⟨stable_pair t, stable_triple t⟩,
    fun a ha hs t _ => stable_extend a ha hs t, ?_⟩
  intro n hn
  obtain ⟨f, hf, hmem⟩ := stable_family n hn
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro _ ⟨t, rfl⟩
  exact hmem t

end

end MetaMathlibExt
