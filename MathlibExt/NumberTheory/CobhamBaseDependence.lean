/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Basic
public import MathlibExt.Dynamics.EventuallyPeriodicSequence
public import MathlibExt.NumberTheory.BaseRecognizable
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

@[expose] public section

namespace MetaMathlibExt

/-- **Multiplicatively independent bases.** Two natural numbers $k$ and $l$ are multiplicatively
independent when $k^m \ne l^n$ for all positive natural numbers $m$ and $n$. -/
def BasesMultiplicativelyIndependent (k l : ℕ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → k ^ m ≠ l ^ n

/-- **Ultimately periodic sets of natural numbers.** A set $S$ of natural numbers is ultimately
periodic when there are natural numbers $N$ and $p > 0$ such that, for every $n \ge N$,
$n \in S$ if and only if $n + p \in S$. -/
def IsUltimatelyPeriodicSet (S : Set ℕ) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → (n ∈ S ↔ n + p ∈ S)

/-- Zero-padded canonical expansion of `z` to exactly `n` digits. -/
private def cbdPad {c : ℕ} (n z : ℕ) (hc : 2 ≤ c) : List (Fin c) :=
  List.replicate (n - (baseDigits hc z).length) ⟨0, by omega⟩ ++ baseDigits hc z

private lemma cbdPad_length {c n z : ℕ} (hc : 2 ≤ c) (hlt : z < c ^ n) :
    (cbdPad n z hc).length = n := by
  have hlen : (baseDigits hc z).length ≤ n := by
    rw [baseDigits_length]
    exact (Nat.digits_length_le_iff (by omega : 1 < c) z).mpr hlt
  simp [cbdPad, Nat.sub_add_cancel hlen]

private lemma cbdReplicateVal {c : ℕ} (hc : 2 ≤ c) (t : ℕ) :
    baseWordValue (List.replicate t (⟨0, by omega⟩ : Fin c)) = 0 := by
  induction t with
  | zero => simp [baseWordValue]
  | succ t ih =>
    rw [List.replicate_succ]
    simpa [baseWordValue] using ih

private lemma cbdPad_value {c n z : ℕ} (hc : 2 ≤ c) :
    baseWordValue (cbdPad n z hc) = z := by
  rw [cbdPad, baseWordValue_append, cbdReplicateVal hc, zero_mul, zero_add,
    baseWordValue_baseDigits]

/-- Node N1: the class map from the DFA. Equal classes see the same membership
for `x * c ^ n + z` with `z < c ^ n`. -/
private lemma cbd_class0 {c : ℕ} {S : Set ℕ} (hR : IsBaseRecognizable c S) :
    ∃ (T : Type) (_ : Finite T) (κ : ℕ → T), ∀ x y n z : ℕ, κ x = κ y →
      z < c ^ n → (x * c ^ n + z ∈ S ↔ y * c ^ n + z ∈ S) := by
  obtain ⟨hc, ns, _, init, trans, accept, hacc⟩ := hR
  refine ⟨Option (Fin ns), inferInstance,
    fun x => if x = 0 then none else some ((baseDigits hc x).foldl trans init),
    ?_⟩
  intro x y n z heq hlt
  have hxy : x ≠ 0 ∧ y ≠ 0 ∨ x = 0 ∧ y = 0 := by
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · exact Or.inr ⟨hx, hy⟩
    · simp [hx, hy] at heq
    · simp [hx, hy] at heq
    · exact Or.inl ⟨hx, hy⟩
  rcases hxy with ⟨hx, hy⟩ | ⟨rfl, rfl⟩
  · simp only [hx, hy, ite_false] at heq
    have hs : (baseDigits hc x).foldl trans init =
        (baseDigits hc y).foldl trans init :=
      Option.some_inj.mp heq
    have hpadlen : (cbdPad n z hc).length = n := cbdPad_length hc hlt
    have hpadval : baseWordValue (cbdPad n z hc) = z := cbdPad_value hc
    have hcanonX : IsCanonicalBaseWord (baseDigits hc x ++ cbdPad n z hc) :=
      (isCanonicalBaseWord_baseDigits hc x).append (baseDigits_ne_nil hc hx)
    have hcanonY : IsCanonicalBaseWord (baseDigits hc y ++ cbdPad n z hc) :=
      (isCanonicalBaseWord_baseDigits hc y).append (baseDigits_ne_nil hc hy)
    have hvalX : baseWordValue (baseDigits hc x ++ cbdPad n z hc) =
        x * c ^ n + z := by
      rw [baseWordValue_append, baseWordValue_baseDigits, hpadlen, hpadval]
    have hvalY : baseWordValue (baseDigits hc y ++ cbdPad n z hc) =
        y * c ^ n + z := by
      rw [baseWordValue_append, baseWordValue_baseDigits, hpadlen, hpadval]
    have hstate : (baseDigits hc x ++ cbdPad n z hc).foldl trans init =
        (baseDigits hc y ++ cbdPad n z hc).foldl trans init := by
      rw [List.foldl_append, List.foldl_append, hs]
    have haccX : accept ((baseDigits hc x ++ cbdPad n z hc).foldl trans init) =
        true ↔ x * c ^ n + z ∈ S := by
      have h1 := hacc (baseDigits hc x ++ cbdPad n z hc)
      simp only [hcanonX, hvalX, true_and] at h1
      exact h1
    have haccY : accept ((baseDigits hc y ++ cbdPad n z hc).foldl trans init) =
        true ↔ y * c ^ n + z ∈ S := by
      have h1 := hacc (baseDigits hc y ++ cbdPad n z hc)
      simp only [hcanonY, hvalY, true_and] at h1
      exact h1
    rw [← haccX, ← haccY, hstate]
  · exact Iff.rfl

/-- Node N2: widened class map, valid for `z ≤ 2 * c ^ n`. -/
private lemma cbd_class {c : ℕ} {S : Set ℕ} (hR : IsBaseRecognizable c S) :
    ∃ (T : Type) (_ : Finite T) (κ : ℕ → T), ∀ x y n z : ℕ, κ x = κ y →
      z ≤ 2 * c ^ n → (x * c ^ n + z ∈ S ↔ y * c ^ n + z ∈ S) := by
  obtain ⟨T, hfin, κ₀, hκ₀⟩ := cbd_class0 hR
  obtain ⟨hc, _, _, _, _, _, _⟩ := hR
  have := hfin
  refine ⟨T × T × T, inferInstance,
    fun x => (κ₀ x, κ₀ (x + 1), κ₀ (x + 2)), ?_⟩
  intro x y n z heq hle
  have e1 : κ₀ x = κ₀ y := congrArg Prod.fst heq
  have e2 : κ₀ (x + 1) = κ₀ (y + 1) := congrArg (Prod.fst ∘ Prod.snd) heq
  have e3 : κ₀ (x + 2) = κ₀ (y + 2) := congrArg (Prod.snd ∘ Prod.snd) heq
  have hpos : 0 < c ^ n := pow_pos (by omega) n
  by_cases h1 : z < c ^ n
  · exact hκ₀ x y n z e1 h1
  · by_cases h2 : z < 2 * c ^ n
    · have hle1 : c ^ n ≤ z := not_lt.mp h1
      obtain ⟨z₁, hz, hz₁lt⟩ : ∃ z₁, z = c ^ n + z₁ ∧ z₁ < c ^ n :=
        ⟨z - c ^ n, by omega, by omega⟩
      have eX : x * c ^ n + z = (x + 1) * c ^ n + z₁ := by rw [hz]; ring
      have eY : y * c ^ n + z = (y + 1) * c ^ n + z₁ := by rw [hz]; ring
      rw [eX, eY]
      exact hκ₀ (x + 1) (y + 1) n z₁ e2 hz₁lt
    · have hzeq : z = 2 * c ^ n := by omega
      have eX : x * c ^ n + z = (x + 2) * c ^ n + 0 := by rw [hzeq]; ring
      have eY : y * c ^ n + z = (y + 2) * c ^ n + 0 := by rw [hzeq]; ring
      rw [eX, eY]
      exact hκ₀ (x + 2) (y + 2) n 0 e3 hpos

/-- Node N3: Dirichlet approximation gives relatively close powers. -/
private lemma cbd_close_powers {a b M : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hM : 1 ≤ M) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      (M : ℤ) * |(a : ℤ) ^ m - (b : ℤ) ^ n| ≤ (b : ℤ) ^ n := by
  have haR : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos haR
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hbR
  have hlogb0 : Real.log (b : ℝ) ≠ 0 := ne_of_gt hlogb
  set ξ : ℝ := Real.log (a : ℝ) / Real.log (b : ℝ) with hξ
  have hξpos : 0 < ξ := div_pos hloga hlogb
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set δ : ℝ := 1 / (2 * (M : ℝ)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact one_div_pos.mpr (mul_pos (by norm_num) hM0)
  obtain ⟨N1, hN1⟩ := exists_nat_gt (Real.log (b : ℝ) / δ)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (1 / ξ)
  set N : ℕ := max N1 N2 with hNdef
  have hNpos : 0 < N := by
    have h1 : (0 : ℝ) < (N1 : ℝ) :=
      lt_of_le_of_lt (div_nonneg hlogb.le hδpos.le) hN1
    have h1n : 0 < N1 := by exact_mod_cast h1
    have h2 : N1 ≤ N := by rw [hNdef]; exact Nat.le_max_left N1 N2
    omega
  obtain ⟨j, k, hk0, _, happrox⟩ := Real.exists_int_int_abs_mul_sub_le ξ hNpos
  have hLb : Real.log (b : ℝ) < δ * ((N : ℝ) + 1) := by
    have h1 : Real.log (b : ℝ) / δ < (N1 : ℝ) := hN1
    have h2 : (N1 : ℝ) ≤ (N : ℝ) + 1 := by
      have h2a : (N1 : ℝ) ≤ (N : ℝ) := by
        rw [hNdef]
        exact_mod_cast Nat.le_max_left N1 N2
      linarith
    calc Real.log (b : ℝ) = (Real.log (b : ℝ) / δ) * δ :=
          (div_mul_cancel₀ _ (ne_of_gt hδpos)).symm
      _ < ((N : ℝ) + 1) * δ :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2) hδpos
      _ = δ * ((N : ℝ) + 1) := mul_comm _ _
  have hbound : 1 / ((N : ℝ) + 1) < δ / Real.log (b : ℝ) := by
    rw [lt_div_iff₀ hlogb, div_mul_eq_mul_div, one_mul,
      div_lt_iff₀ (by positivity)]
    exact hLb
  have hboundξ : 1 / ((N : ℝ) + 1) < ξ := by
    have h1ξ : 1 / ξ < (N : ℝ) + 1 := by
      have h1 : 1 / ξ < (N2 : ℝ) := hN2
      have h2 : (N2 : ℝ) ≤ (N : ℝ) := by
        rw [hNdef]
        exact_mod_cast Nat.le_max_right N1 N2
      linarith
    have h2 := (div_lt_iff₀ hξpos).mp h1ξ
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hk1 : (1 : ℤ) ≤ k := hk0
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hj0 : 0 < j := by
    by_contra hjc
    have hjR : (j : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp hjc)
    have hkx : ξ ≤ (k : ℝ) * ξ :=
      calc ξ = 1 * ξ := (one_mul ξ).symm
        _ ≤ (k : ℝ) * ξ := mul_le_mul_of_nonneg_right hkR hξpos.le
    have hnn : (0 : ℝ) ≤ (k : ℝ) * ξ - (j : ℝ) := by linarith
    have habs : |(k : ℝ) * ξ - (j : ℝ)| = (k : ℝ) * ξ - (j : ℝ) :=
      abs_of_nonneg hnn
    rw [habs] at happrox
    linarith
  set m : ℕ := k.toNat with hm
  set n : ℕ := j.toNat with hn
  have hmZ : ((m : ℕ) : ℤ) = k := by
    rw [hm]
    exact Int.toNat_of_nonneg hk0.le
  have hnZ : ((n : ℕ) : ℤ) = j := by
    rw [hn]
    exact Int.toNat_of_nonneg hj0.le
  have hm0 : 0 < m := by
    have h : (0 : ℤ) < ((m : ℕ) : ℤ) := by rw [hmZ]; exact hk0
    exact_mod_cast h
  have hn0 : 0 < n := by
    have h : (0 : ℤ) < ((n : ℕ) : ℤ) := by rw [hnZ]; exact hj0
    exact_mod_cast h
  have hmR : ((m : ℕ) : ℝ) = ((k : ℤ) : ℝ) := by
    rw [← Int.cast_natCast m, hmZ]
  have hnR : ((n : ℕ) : ℝ) = ((j : ℤ) : ℝ) := by
    rw [← Int.cast_natCast n, hnZ]
  have hkey : |(m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ)| ≤ δ := by
    have e : (m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ) =
        Real.log (b : ℝ) * ((k : ℝ) * ξ - (j : ℝ)) := by
      rw [hmR, hnR, hξ]
      field_simp [hlogb0]
    rw [e, abs_mul, abs_of_pos hlogb]
    calc Real.log (b : ℝ) * |(k : ℝ) * ξ - (j : ℝ)|
        ≤ Real.log (b : ℝ) * (δ / Real.log (b : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans happrox hbound.le) hlogb.le
      _ = δ := by
          rw [mul_comm (Real.log (b : ℝ)), div_mul_cancel₀ _ hlogb0]
  have hposA : (0 : ℝ) < (a : ℝ) ^ m :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < a)) m
  have hposB : (0 : ℝ) < (b : ℝ) ^ n :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < b)) n
  have hlog : Real.log ((a : ℝ) ^ m / (b : ℝ) ^ n) =
      (m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ) := by
    rw [Real.log_div (ne_of_gt hposA) (ne_of_gt hposB), Real.log_pow,
      Real.log_pow]
  have hexp : (a : ℝ) ^ m / (b : ℝ) ^ n =
      Real.exp ((m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ)) := by
    rw [← hlog, Real.exp_log (div_pos hposA hposB)]
  have hexpinv : Real.exp δ * Real.exp (-δ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hexpδ : Real.exp δ = 1 / Real.exp (-δ) := by
    rw [eq_div_iff (ne_of_gt (Real.exp_pos _))]
    exact hexpinv
  have he0 : 1 - δ ≤ Real.exp (-δ) := by
    have h := Real.add_one_le_exp (-δ)
    linarith
  have hδ1 : (0 : ℝ) < 1 - δ := by
    have h2M : (0 : ℝ) < 2 * (M : ℝ) := mul_pos (by norm_num) hM0
    rw [hδ, sub_pos, div_lt_one h2M]
    linarith
  have hA : 1 / (1 - δ) ≤ 1 + 1 / (M : ℝ) := by
    rw [div_le_iff₀ hδ1]
    have e : (1 + 1 / (M : ℝ)) * (1 - δ) - 1 =
        ((M : ℝ) - 1) / (2 * (M : ℝ) * (M : ℝ)) := by
      have hMne : (M : ℝ) ≠ 0 := ne_of_gt hM0
      have h2Mne : 2 * (M : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hMne
      rw [hδ]
      field_simp [hMne, h2Mne]
      ring
    have h3 : (0 : ℝ) ≤ ((M : ℝ) - 1) / (2 * (M : ℝ) * (M : ℝ)) := by
      apply div_nonneg _ _
      · linarith
      · exact mul_nonneg (mul_nonneg (by norm_num) hM0.le) hM0.le
    linarith
  have hB : 1 / Real.exp (-δ) ≤ 1 + 1 / (M : ℝ) :=
    le_trans (one_div_le_one_div_of_le hδ1 he0) hA
  have hdu : δ ≤ 1 / (M : ℝ) := by
    rw [hδ]
    exact one_div_le_one_div_of_le hM0 (by linarith)
  have hhi : Real.exp ((m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ)) ≤
      1 + 1 / (M : ℝ) :=
    calc Real.exp ((m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ))
        ≤ Real.exp δ := (Real.exp_le_exp).mpr (abs_le.mp hkey).2
      _ = 1 / Real.exp (-δ) := hexpδ
      _ ≤ 1 + 1 / (M : ℝ) := hB
  have hlo : 1 - 1 / (M : ℝ) ≤
      Real.exp ((m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ)) := by
    have h2 : Real.exp (-δ) ≤
        Real.exp ((m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ)) := by
      apply (Real.exp_le_exp).mpr
      have h := (abs_le.mp hkey).1
      linarith
    linarith [he0, hdu]
  have hexpb : |Real.exp ((m : ℝ) * Real.log (a : ℝ) - (n : ℝ) * Real.log (b : ℝ))
      - 1| ≤ 1 / (M : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hlo, hhi]
  have hAB : |(a : ℝ) ^ m - (b : ℝ) ^ n| ≤ (b : ℝ) ^ n / (M : ℝ) := by
    have hBne : (b : ℝ) ^ n ≠ 0 := ne_of_gt hposB
    have e : (a : ℝ) ^ m - (b : ℝ) ^ n =
        ((a : ℝ) ^ m / (b : ℝ) ^ n - 1) * (b : ℝ) ^ n := by
      field_simp [hBne]
    rw [e, abs_mul, abs_of_pos hposB]
    rw [← hexp] at hexpb
    calc |(a : ℝ) ^ m / (b : ℝ) ^ n - 1| * (b : ℝ) ^ n
        ≤ (1 / (M : ℝ)) * (b : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hexpb hposB.le
      _ = (b : ℝ) ^ n / (M : ℝ) := by ring
  have hleR : (M : ℝ) * |(a : ℝ) ^ m - (b : ℝ) ^ n| ≤ (b : ℝ) ^ n := by
    have h := (le_div_iff₀ hM0).mp hAB
    rw [mul_comm (M : ℝ)]
    exact h
  exact ⟨m, n, hm0, hn0, by exact_mod_cast hleR⟩

/-- A local period `p` on the interval `[lo, hi]`. -/
private def cbdLocalPeriod (S : Set ℕ) (p lo hi : ℕ) : Prop :=
  ∀ u : ℕ, lo ≤ u → u + p ≤ hi → (u ∈ S ↔ u + p ∈ S)

/-- Stepping along a local period: congruent points agree. -/
private lemma cbd_step {S : Set ℕ} {q lo hi v u : ℕ}
    (hq : cbdLocalPeriod S q lo hi)
    (hlo : lo ≤ v) (hhi : u ≤ hi) (hvu : v ≤ u) (hmod : (u - v) % q = 0) :
    (v ∈ S ↔ u ∈ S) := by
  have key : ∀ k : ℕ, v + q * k ≤ hi → (v ∈ S ↔ v + q * k ∈ S) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hle
      have e : v + q * (k + 1) = v + q * k + q := by ring
      rw [e] at hle ⊢
      have h1 := ih (by omega)
      have h2 := hq (v + q * k) (by omega) hle
      exact h1.trans h2
  have hdiv : u = v + q * ((u - v) / q) := by
    have h := Nat.div_add_mod (u - v) q
    rw [hmod] at h
    omega
  have hle : v + q * ((u - v) / q) ≤ hi := by
    rw [← hdiv]
    exact hhi
  rw [hdiv]
  exact key ((u - v) / q) hle

/-- Node N4: gluing lemma for local periods on overlapping intervals. -/
private lemma cbd_glue {S : Set ℕ} {p q lo₁ hi₁ lo₂ hi₂ : ℕ}
    (hp : cbdLocalPeriod S p lo₁ hi₁) (hq : cbdLocalPeriod S q lo₂ hi₂)
    (hq0 : 0 < q) (hle_lo : lo₁ ≤ lo₂)
    (hover : lo₂ + p + q ≤ hi₁ + 1) :
    cbdLocalPeriod S p lo₁ hi₂ := by
  intro u hu1 hu2
  by_cases hcase : u + p ≤ hi₁
  · exact hp u hu1 hcase
  · have hlo2u : lo₂ + q ≤ u := by omega
    have hmodlt : (u - lo₂) % q < q := Nat.mod_lt _ hq0
    have hmodle : (u - lo₂) % q ≤ u - lo₂ := Nat.mod_le _ _
    have hdecomp : u - (lo₂ + (u - lo₂) % q) = q * ((u - lo₂) / q) := by
      have h := Nat.div_add_mod (u - lo₂) q
      omega
    have hmod0 : (u - (lo₂ + (u - lo₂) % q)) % q = 0 := by
      rw [hdecomp]
      exact Nat.mul_mod_right _ _
    have h1 : (u ∈ S ↔ (lo₂ + (u - lo₂) % q) ∈ S) :=
      (cbd_step (v := lo₂ + (u - lo₂) % q) (u := u) hq (by omega) (by omega)
        (by omega) hmod0).symm
    have h2 : ((lo₂ + (u - lo₂) % q) ∈ S ↔
        (lo₂ + (u - lo₂) % q + p) ∈ S) :=
      hp _ (by omega) (by omega)
    have hmod0' : (u + p - (lo₂ + (u - lo₂) % q + p)) % q = 0 := by
      have e : u + p - (lo₂ + (u - lo₂) % q + p) = u - (lo₂ + (u - lo₂) % q) := by
        omega
      rw [e]
      exact hmod0
    have h3 : ((lo₂ + (u - lo₂) % q + p) ∈ S ↔ (u + p) ∈ S) :=
      cbd_step (v := lo₂ + (u - lo₂) % q + p) (u := u + p) hq (by omega)
        (by omega) (by omega) hmod0'
    exact h1.trans (h2.trans h3)

/-- Node N5 auxiliary: the window chain under a fixed sign hypothesis. -/
private lemma cbd_window_aux {S : Set ℕ} {a b : ℕ} {Ta Tb : Type}
    {κa : ℕ → Ta} {κb : ℕ → Tb}
    (ha : ∀ x y ex z : ℕ, κa x = κa y → z ≤ 2 * a ^ ex →
      (x * a ^ ex + z ∈ S ↔ y * a ^ ex + z ∈ S))
    (hb : ∀ x y ex z : ℕ, κb x = κb y → z ≤ 2 * b ^ ex →
      (x * b ^ ex + z ∈ S ↔ y * b ^ ex + z ∈ S))
    {ma mb ξ x₀ y₀ : ℕ} {d : ℤ}
    (hd : d = ((a ^ ma : ℕ) : ℤ) - ((b ^ mb : ℕ) : ℤ))
    (hx₀ : x₀ < ξ) (hy₀ : y₀ < ξ)
    (hκb : κb x₀ = κb y₀) (hκa : κa x₀ = κa y₀)
    (hsmall : 12 * (ξ : ℤ) * |d| ≤ ((b ^ mb : ℕ) : ℤ))
    {p : ℕ} (hpcast : ((p : ℕ) : ℤ) = ((x₀ : ℤ) - (y₀ : ℤ)) * d)
    (hpos : 0 < ((x₀ : ℤ) - (y₀ : ℤ)) * d) :
    0 < p ∧ 12 * p ≤ b ^ mb ∧ ∀ x : ℕ, κb x = κb x₀ →
      cbdLocalPeriod S p (x * b ^ mb + (b ^ mb) / 3 + 1)
        (x * b ^ mb + 5 * (b ^ mb) / 3) := by
  set N := b ^ mb with hNdef
  set A := a ^ ma with hAdef
  have hA : ((A : ℕ) : ℤ) = (N : ℤ) + d := by linarith [hd]
  have hp0 : 0 < p := by
    have h : (0 : ℤ) < ((p : ℕ) : ℤ) := by rw [hpcast]; exact hpos
    exact_mod_cast h
  have hx : (x₀ : ℤ) < (ξ : ℤ) := by exact_mod_cast hx₀
  have hy : (y₀ : ℤ) < (ξ : ℤ) := by exact_mod_cast hy₀
  have hxy : |(x₀ : ℤ) - (y₀ : ℤ)| ≤ (ξ : ℤ) := by
    rw [abs_le]
    have hxnn : (0 : ℤ) ≤ (x₀ : ℤ) := by positivity
    have hynn : (0 : ℤ) ≤ (y₀ : ℤ) := by positivity
    constructor <;> linarith
  have hpeq : ((p : ℕ) : ℤ) = |(x₀ : ℤ) - (y₀ : ℤ)| * |d| := by
    have h1 : ((x₀ : ℤ) - (y₀ : ℤ)) * d = |((x₀ : ℤ) - (y₀ : ℤ)) * d| :=
      (abs_of_pos hpos).symm
    rw [hpcast, h1, abs_mul]
  have hple : 12 * p ≤ N := by
    have hyD : (y₀ : ℤ) * |d| ≤ (ξ : ℤ) * |d| :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hy₀.le) (abs_nonneg d)
    have hstep : |(x₀ : ℤ) - (y₀ : ℤ)| * |d| ≤ (ξ : ℤ) * |d| :=
      mul_le_mul_of_nonneg_right hxy (abs_nonneg d)
    have h2 : (12 : ℤ) * (|(x₀ : ℤ) - (y₀ : ℤ)| * |d|) ≤
        12 * ((ξ : ℤ) * |d|) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    have h12 : (12 : ℤ) * ((p : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [hpeq]
      linarith [hsmall]
    exact_mod_cast h12
  have hξ1 : (1 : ℤ) ≤ (ξ : ℤ) := by
    have hxnn : (0 : ℤ) ≤ (x₀ : ℤ) := by positivity
    linarith
  have hdle : (12 : ℤ) * |d| ≤ (N : ℤ) := by
    have hs1 : (12 : ℤ) * |d| ≤ (12 * (ξ : ℤ)) * |d| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg d)
      linarith
    linarith [hsmall]
  refine ⟨hp0, hple, fun x hx => ?_⟩
  intro u hu1 hu2
  obtain ⟨z, hz⟩ : ∃ z, u = x * N + z := ⟨u - x * N, by omega⟩
  have hz1 : N / 3 + 1 ≤ z := by omega
  have hz2 : z + p ≤ 5 * N / 3 := by omega
  have hz2b : z ≤ 2 * N := by omega
  have hz5 : z + p ≤ 2 * N := by omega
  have hxb : κb x = κb y₀ := hx.trans hκb
  have step1 : x * N + z ∈ S ↔ y₀ * N + z ∈ S :=
    hb x y₀ mb z hxb hz2b
  have h1 : -((y₀ : ℤ) * |d|) ≤ (y₀ : ℤ) * d := by
    have habs : |(y₀ : ℤ) * d| = (y₀ : ℤ) * |d| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    rw [← habs]
    exact neg_abs_le _
  have h2 : (y₀ : ℤ) * d ≤ (y₀ : ℤ) * |d| := by
    have habs : |(y₀ : ℤ) * d| = (y₀ : ℤ) * |d| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    rw [← habs]
    exact le_abs_self _
  have hy12 : (12 : ℤ) * ((y₀ : ℤ) * |d|) ≤ (N : ℤ) := by
    have hyD : (y₀ : ℤ) * |d| ≤ (ξ : ℤ) * |d| :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hy₀.le) (abs_nonneg d)
    have h2' : (12 : ℤ) * ((y₀ : ℤ) * |d|) ≤ 12 * ((ξ : ℤ) * |d|) :=
      mul_le_mul_of_nonneg_left hyD (by norm_num)
    linarith [hsmall]
  have hZnn : (0 : ℤ) ≤ (z : ℤ) - (y₀ : ℤ) * d := by omega
  obtain ⟨z', hz'⟩ : ∃ z' : ℕ, ((z' : ℕ) : ℤ) = (z : ℤ) - (y₀ : ℤ) * d :=
    ⟨((z : ℤ) - (y₀ : ℤ) * d).toNat, Int.toNat_of_nonneg hZnn⟩
  have e2 : y₀ * N + z = y₀ * A + z' := by
    have hZe2 : (y₀ : ℤ) * (N : ℤ) + (z : ℤ) =
        (y₀ : ℤ) * (A : ℤ) + (z' : ℤ) := by
      rw [hz', hA]
      ring
    exact_mod_cast hZe2
  have hdabs : -|d| ≤ d := neg_abs_le d
  have hz'A : z' ≤ 2 * A := by omega
  have step3 : y₀ * A + z' ∈ S ↔ x₀ * A + z' ∈ S :=
    ha y₀ x₀ ma z' hκa.symm hz'A
  have e4 : x₀ * A + z' = x₀ * N + (z + p) := by
    have hZe4 : (x₀ : ℤ) * (A : ℤ) + (z' : ℤ) =
        (x₀ : ℤ) * (N : ℤ) + ((z : ℤ) + (p : ℤ)) := by
      rw [hz', hA, hpcast]
      ring
    exact_mod_cast hZe4
  have step5 : x₀ * N + (z + p) ∈ S ↔ x * N + (z + p) ∈ S :=
    hb x₀ x mb (z + p) hx.symm hz5
  have e5 : x * N + (z + p) = u + p := by omega
  calc (u ∈ S) ↔ (x * N + z ∈ S) := by rw [hz]
    _ ↔ (y₀ * N + z ∈ S) := step1
    _ ↔ (y₀ * A + z' ∈ S) := by rw [e2]
    _ ↔ (x₀ * A + z' ∈ S) := step3
    _ ↔ (x₀ * N + (z + p) ∈ S) := by rw [e4]
    _ ↔ (x * N + (z + p) ∈ S) := step5
    _ ↔ (u + p ∈ S) := by rw [e5]

/-- Node N5: the window chain, giving a local period on each block. -/
private lemma cbd_window {S : Set ℕ} {a b : ℕ} {Ta Tb : Type}
    {κa : ℕ → Ta} {κb : ℕ → Tb}
    (ha : ∀ x y ex z : ℕ, κa x = κa y → z ≤ 2 * a ^ ex →
      (x * a ^ ex + z ∈ S ↔ y * a ^ ex + z ∈ S))
    (hb : ∀ x y ex z : ℕ, κb x = κb y → z ≤ 2 * b ^ ex →
      (x * b ^ ex + z ∈ S ↔ y * b ^ ex + z ∈ S))
    {ma mb ξ x₀ y₀ : ℕ} {d : ℤ}
    (hd : d = ((a ^ ma : ℕ) : ℤ) - ((b ^ mb : ℕ) : ℤ))
    (hx₀ : x₀ < ξ) (hy₀ : y₀ < ξ) (hne : x₀ ≠ y₀)
    (hκb : κb x₀ = κb y₀) (hκa : κa x₀ = κa y₀)
    (hsmall : 12 * (ξ : ℤ) * |d| ≤ ((b ^ mb : ℕ) : ℤ))
    (hd0 : d ≠ 0) :
    ∃ p : ℕ, 0 < p ∧ 12 * p ≤ b ^ mb ∧ ∀ x : ℕ, κb x = κb x₀ →
      cbdLocalPeriod S p (x * b ^ mb + (b ^ mb) / 3 + 1)
        (x * b ^ mb + 5 * (b ^ mb) / 3) := by
  have hneZ : (x₀ : ℤ) ≠ (y₀ : ℤ) := by exact_mod_cast hne
  have hprod : ((x₀ : ℤ) - (y₀ : ℤ)) * d ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hneZ) hd0
  set prod : ℤ := ((x₀ : ℤ) - (y₀ : ℤ)) * d with hproddef
  set p : ℕ := prod.natAbs with hpdef
  rcases lt_or_gt_of_ne hprod with hneg | hpos
  · have e : ((y₀ : ℤ) - (x₀ : ℤ)) * d = -prod := by
      rw [hproddef]; ring
    have hpos2 : 0 < ((y₀ : ℤ) - (x₀ : ℤ)) * d := by
      rw [e]; linarith
    have hpcast2 : ((p : ℕ) : ℤ) = ((y₀ : ℤ) - (x₀ : ℤ)) * d := by
      rw [e, hpdef, ← Int.natAbs_neg]
      have hle : (0 : ℤ) ≤ -prod := by
        rw [← e]
        exact le_of_lt hpos2
      exact Int.natAbs_of_nonneg hle
    obtain ⟨hp0, hple, hper⟩ := cbd_window_aux ha hb hd hy₀ hx₀ hκb.symm hκa.symm
      hsmall hpcast2 hpos2
    exact ⟨p, hp0, hple, fun x hx => hper x (hx.trans hκb)⟩
  · have hpcast1 : ((p : ℕ) : ℤ) = ((x₀ : ℤ) - (y₀ : ℤ)) * d := by
      rw [hpdef]
      exact Int.natAbs_of_nonneg (le_of_lt hpos)
    obtain ⟨hp0, hple, hper⟩ :=
      cbd_window_aux ha hb hd hx₀ hy₀ hκb hκa hsmall hpcast1 hpos
    exact ⟨p, hp0, hple, hper⟩

/-- Node N6: two recognizable bases with no common powers give ultimate
periodicity. -/
private lemma cbd_ultimately_periodic {a b : ℕ} {S : Set ℕ}
    (haR : IsBaseRecognizable a S) (hbR : IsBaseRecognizable b S)
    (hind : ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n) :
    IsUltimatelyPeriodicSet S := by
  obtain ⟨Ta, hfinA, κa, hκa⟩ := cbd_class haR
  obtain ⟨Tb, hfinB, κb, hκb⟩ := cbd_class hbR
  have : Fintype Tb := Fintype.ofFinite Tb
  set I : Set Tb := {s | (κb ⁻¹' {s}).Infinite} with hIdef
  have hbad : {y | κb y ∉ I}.Finite := by
    have hsub : {y | κb y ∉ I} ⊆
        ⋃ s ∈ {s : Tb | ¬ (κb ⁻¹' {s}).Infinite}, κb ⁻¹' {s} := by
      intro y hy
      have hy' : ¬ (κb ⁻¹' {κb y}).Infinite := hy
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨κb y, hy', rfl⟩
    have hfin : (⋃ s ∈ {s : Tb | ¬ (κb ⁻¹' {s}).Infinite},
        κb ⁻¹' {s}).Finite := by
      refine Set.Finite.biUnion
        (Set.Finite.subset Set.finite_univ (Set.subset_univ _)) ?_
      intro s hs
      exact Set.not_infinite.mp hs
    exact Set.Finite.subset hfin hsub
  obtain ⟨X, hX⟩ := Set.Finite.bddAbove hbad
  have hgood : ∀ y : ℕ, X < y → (κb ⁻¹' {κb y}).Infinite := by
    intro y hyX
    by_contra hcon
    have hle : y ≤ X := hX (show κb y ∉ I from hcon)
    omega
  have hex : ∀ s : Tb, ∃ x y : ℕ,
      (s ∈ I → (x ≠ y ∧ κb x = s ∧ κb y = s ∧ κa x = κa y)) := by
    intro s
    by_cases hs : s ∈ I
    · have hinf : (κb ⁻¹' {s}).Infinite := hs
      obtain ⟨x, hxm, y, hym, hne, heq⟩ :=
        hinf.exists_ne_map_eq_of_mapsTo (f := κa) (t := Set.univ)
          (Set.mapsTo_univ _ _) (Set.toFinite _)
      exact ⟨x, y, fun _ => ⟨hne, hxm, hym, heq⟩⟩
    · exact ⟨0, 0, fun h => absurd h hs⟩
  choose xs ys hpair using hex
  set ξ : ℕ := Finset.univ.sup (fun s : Tb => xs s ⊔ ys s) + 1 with hξdef
  have hξx : ∀ s : Tb, xs s < ξ := by
    intro s
    have h1 : xs s ⊔ ys s ≤ Finset.univ.sup (fun s : Tb => xs s ⊔ ys s) :=
      Finset.le_sup (f := fun s : Tb => xs s ⊔ ys s) (Finset.mem_univ s)
    have h2 : xs s ≤ xs s ⊔ ys s := le_sup_left
    omega
  have hξy : ∀ s : Tb, ys s < ξ := by
    intro s
    have h1 : xs s ⊔ ys s ≤ Finset.univ.sup (fun s : Tb => xs s ⊔ ys s) :=
      Finset.le_sup (f := fun s : Tb => xs s ⊔ ys s) (Finset.mem_univ s)
    have h2 : ys s ≤ xs s ⊔ ys s := le_sup_right
    omega
  have hξ1 : 1 ≤ ξ := by omega
  have hξ1Z : (1 : ℤ) ≤ (ξ : ℤ) := by exact_mod_cast hξ1
  obtain ⟨ha2, _, _, _, _, _, _⟩ := haR
  obtain ⟨hb2, _, _, _, _, _, _⟩ := hbR
  have hMξ : 1 ≤ 12 * ξ := by omega
  obtain ⟨ma, mb, hma, hmb, hclose⟩ := cbd_close_powers ha2 hb2 hMξ
  set N := b ^ mb with hNdef
  set A := a ^ ma with hAdef
  set d : ℤ := (A : ℤ) - (N : ℤ) with hddef
  have hAN : A ≠ N := hind ma mb hma hmb
  have hd0 : d ≠ 0 := by
    have hANZ : (A : ℤ) ≠ (N : ℤ) := by exact_mod_cast hAN
    exact sub_ne_zero.mpr hANZ
  have hsmall : 12 * (ξ : ℤ) * |d| ≤ (N : ℤ) := by
    have h := hclose
    push_cast at h
    exact h
  have hN12 : 12 ≤ N := by
    have g2 : (1 : ℤ) ≤ |d| := by
      by_contra hcon
      have hlt : |d| < 1 := lt_of_not_ge hcon
      have hnn := abs_nonneg d
      have h0 : |d| = 0 := by omega
      exact hd0 (abs_eq_zero.mp h0)
    have g3 : (1 : ℤ) ≤ (ξ : ℤ) * |d| := by
      calc (1 : ℤ) = 1 * 1 := by ring
        _ ≤ (ξ : ℤ) * |d| := mul_le_mul hξ1Z g2 (by norm_num) (by linarith)
    have hR : (12 : ℤ) ≤ (N : ℤ) := by
      have h12 : (12 : ℤ) * (1 : ℤ) ≤ 12 * ((ξ : ℤ) * |d|) :=
        mul_le_mul_of_nonneg_left g3 (by norm_num)
      linarith [hsmall]
    exact_mod_cast hR
  have hwinAt : ∀ y : ℕ, X < y → ∃ p : ℕ, 0 < p ∧ 12 * p ≤ N ∧
      cbdLocalPeriod S p (y * N + N / 3 + 1) (y * N + 5 * N / 3) := by
    intro y hyX
    have hmem : κb y ∈ I := hgood y hyX
    obtain ⟨hne', hbx, hby, hka⟩ := hpair (κb y) hmem
    have hκbp : κb (xs (κb y)) = κb (ys (κb y)) := by rw [hbx, hby]
    obtain ⟨p, hp0, hple, hper⟩ :=
      cbd_window hκa hκb hddef (hξx (κb y)) (hξy (κb y)) hne' hκbp hka hsmall hd0
    exact ⟨p, hp0, hple, hper y hbx.symm⟩
  obtain ⟨pX, hpX0, hpXle, hbase⟩ := hwinAt (X + 1) (Nat.lt_succ_self X)
  have hinduct : ∀ k : ℕ, cbdLocalPeriod S pX ((X + 1) * N + N / 3 + 1)
      (((X + 1) + k) * N + 5 * N / 3) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      obtain ⟨p', hp'0, hp'le, hnext⟩ := hwinAt ((X + 1) + (k + 1)) (by omega)
      have eN : ((X + 1) + (k + 1)) * N = ((X + 1) + k) * N + N := by ring
      refine cbd_glue ih hnext hp'0 ?_ ?_
      · have hle : (X + 1) * N ≤ ((X + 1) + k) * N :=
          Nat.mul_le_mul_right N (by omega)
        rw [eN]
        omega
      · rw [eN]
        omega
  change ∃ T p : ℕ, 0 < p ∧ ∀ n : ℕ, T ≤ n → (n ∈ S ↔ n + p ∈ S)
  refine ⟨(X + 1) * N + N / 3 + 1, pX, hpX0, fun u hu => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, u + pX ≤ ((X + 1) + k) * N + 5 * N / 3 := by
    refine ⟨u + pX, ?_⟩
    have hN1 : 1 ≤ N := by omega
    have hk1 : u + pX ≤ (u + pX) * N := Nat.le_mul_of_pos_right _ hN1
    have hk2 : (u + pX) * N ≤ ((X + 1) + (u + pX)) * N :=
      Nat.mul_le_mul_right N (by omega)
    omega
  exact (hinduct k) u hu hk

/-- **Cobham's theorem.** Let $k$ and $l$ be multiplicatively independent natural numbers with
$l \ge 2$, and let $S$ be a set of natural numbers that is recognizable in base $k$ and is not
ultimately periodic. Then $S$ is not recognizable in base $l$.

Proves `Wanted` entry `cobham_base_dependence`.

Source: proved via T. J. P. Krebs, *A more reasonable proof of Cobham's theorem*,
arXiv:1801.06704, Section 3.

Source: T. Kärki, A. Lacroix, and M. Rigo, *On the Recognizability of
Self-Generating Sets*, especially the remark invoking Cobham's theorem:
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Rigo/rigo6.tex>.
-/
public theorem cobham_base_dependence {k l : ℕ} {S : Set ℕ}
    (hl : 2 ≤ l)
    (hindependent : BasesMultiplicativelyIndependent k l)
    (hrecognizable : IsBaseRecognizable k S)
    (haperiodic : ¬ IsUltimatelyPeriodicSet S) :
    ¬ IsBaseRecognizable l S := by
  intro hlR
  exact absurd (cbd_ultimately_periodic hrecognizable ⟨hl, hlR.2⟩
    (fun m n hm hn => hindependent m n hm hn)) haperiodic

/-- **Ultimately periodic sets and their characteristic sequences.** A set $S$ of natural
numbers is ultimately periodic if and only if its characteristic sequence $n \mapsto (n \in S)$,
a sequence of truth values, is ultimately periodic. -/
public theorem isUltimatelyPeriodicSet_iff_isUltimatelyPeriodic (S : Set ℕ) :
    IsUltimatelyPeriodicSet S ↔ IsUltimatelyPeriodic (fun n => n ∈ S) := by
  constructor
  · rintro ⟨N, p, hp, h⟩
    exact ⟨p, N, hp, fun n hn => propext (Iff.symm (h n hn))⟩
  · rintro ⟨p, N, hp, h⟩
    exact ⟨N, p, hp, fun n hn => Iff.symm (Eq.to_iff (h n hn))⟩

/-- **Cobham's theorem for characteristic sequences.** Let $k$ and $l$ be multiplicatively
independent natural numbers with $l \ge 2$, and let $S$ be a set of natural numbers that is
recognizable in base $k$ and whose characteristic sequence $n \mapsto (n \in S)$, a sequence of
truth values, is not ultimately periodic. Then $S$ is not recognizable in base $l$. -/
public theorem cobham_base_dependence_isUltimatelyPeriodic {k l : ℕ} {S : Set ℕ}
    (hl : 2 ≤ l)
    (hindependent : BasesMultiplicativelyIndependent k l)
    (hrecognizable : IsBaseRecognizable k S)
    (haperiodic : ¬ IsUltimatelyPeriodic (fun n => n ∈ S)) :
    ¬ IsBaseRecognizable l S :=
  cobham_base_dependence hl hindependent hrecognizable
    (fun h => haperiodic ((isUltimatelyPeriodicSet_iff_isUltimatelyPeriodic S).mp h))

end MetaMathlibExt
