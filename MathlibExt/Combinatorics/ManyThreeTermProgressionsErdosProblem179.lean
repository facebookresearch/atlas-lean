/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-!
# Three-term progression thresholds

For every fixed length greater than three, the logarithmic growth exponent of the threshold
for forcing a progression of that length from three-term progressions is two.

For the lower bound, take three translates of a dilated Behrend set in the residue classes
0, 1, 2 modulo 5. Every four-term progression would have to stay in a single class.
Summing over the translations of the last copy counts all ordered triples from the Behrend set.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted

open Filter Topology Asymptotics

/-- **Containing a $k$-term arithmetic progression.** A finite set $A \subseteq \mathbb{N}$
contains a $k$-term arithmetic progression when there are natural numbers $a$ and $d \ge 1$ with
$a + i d \in A$ for every natural number $i < k$, that is, $a, a + d, \dots, a + (k - 1) d$ all
lie in $A$. For $k = 0$ this holds vacuously. -/
def HasAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- **Number of $k$-term arithmetic progressions in a set.** For a finite set
$A \subseteq \mathbb{N}$ and a natural number $k$, $\mathrm{AP}_k(A)$ is the number of pairs
$(a, d)$ of natural numbers with $a \in A$ and $1 \le d \le \max A$ such that $a + i d \in A$ for
every natural number $i < k$. For $k \ge 2$ the conditions $a \in A$ and $d \le \max A$ follow
from the others, so $\mathrm{AP}_k(A)$ counts the $k$-term progressions
$a, a + d, \dots, a + (k - 1) d$ in $A$ with $d \ge 1$. -/
def apCount (A : Finset ℕ) (k : ℕ) : ℕ :=
  ((A ×ˢ Finset.Icc 1 (A.sup id)).filter (fun p => ∀ i < k, p.1 + i * p.2 ∈ A)).card

/-- **The progression threshold $F_k(N, \ell)$.** For natural numbers $k$, $\ell$ and $N$,
$F_k(N, \ell)$ is the least natural number $m$ such that every $N$-element set
$A \subseteq \mathbb{N}$ with $\mathrm{AP}_k(A) \ge m$ contains an $\ell$-term arithmetic
progression, where $\mathrm{AP}_k(A)$ is the number of pairs $(a, d)$ with $a \in A$,
$1 \le d \le \max A$ and $a + i d \in A$ for all $i < k$ (for $k \ge 2$, the number of $k$-term
progressions in $A$ with $d \ge 1$); if no such $m$ exists, $F_k(N, \ell) = 0$.

For $k \ge 2$ such an $m$ always exists, since an $N$-element set has at most $N^2$ $k$-term
progressions. -/
noncomputable def apThreshold (k ℓ N : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ A : Finset ℕ, A.card = N → m ≤ apCount A k → HasAP A ℓ}

/-- **Erdős Problem 179: is $F_3(N, 4) = o(N^2)$?** The statement that $F_3(N, 4) = o(N^2)$ as
$N \to \infty$ over the natural numbers, that is, $F_3(N, 4) / N^2 \to 0$, where $F_3(N, 4)$ is the
least $m$ such that every $N$-element set $A \subseteq \mathbb{N}$ containing at least $m$
three-term arithmetic progressions $a, a + d, a + 2d$ with $d \ge 1$ contains a $4$-term
arithmetic progression. -/
def threeAPThresholdForFourAPLittleO : Prop :=
  (fun N : ℕ => (apThreshold 3 4 N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) ^ 2)

/-- **Erdős Problem 179: does $\log F_3(N, \ell) / \log N$ tend to $2$?** The statement that for
every natural number $\ell > 3$, $\log F_3(N, \ell) / \log N \to 2$ as $N \to \infty$ over the
natural numbers, where $F_3(N, \ell)$ is the least $m$ such that every $N$-element set
$A \subseteq \mathbb{N}$ containing at least $m$ three-term arithmetic progressions
$a, a + d, a + 2d$ with $d \ge 1$ contains an $\ell$-term arithmetic progression. -/
def threeAPThresholdExponentTwo : Prop :=
  ∀ ℓ : ℕ, 3 < ℓ →
    Tendsto (fun N : ℕ => Real.log (apThreshold 3 ℓ N) / Real.log N) atTop (𝓝 2)

open Finset

private abbrev starts (A : Finset ℕ) :=
  (A ×ˢ Icc 1 (A.sup id)).filter (fun p => ∀ i < 3, p.1 + i * p.2 ∈ A)

private lemma mem_starts {A : Finset ℕ} {a d : ℕ} (hd : 0 < d)
    (h₀ : a ∈ A) (h₁ : a + d ∈ A) (h₂ : a + 2 * d ∈ A) : (a, d) ∈ starts A := by
  have hmax : a + d ≤ A.sup id := le_sup (f := id) h₁
  refine mem_filter.mpr ⟨mem_product.mpr ⟨h₀, mem_Icc.mpr ⟨hd, by omega⟩⟩, ?_⟩
  intro i hi
  interval_cases i <;> simp_all

private lemma count_le_sq (A : Finset ℕ) : apCount A 3 ≤ A.card ^ 2 := by
  rw [sq, ← card_product]
  apply card_le_card_of_injOn (s := starts A) (fun (a, d) => (a, a + d))
  · intro ⟨a, d⟩ hp
    obtain ⟨h, hall⟩ := mem_filter.mp hp
    exact mem_product.mpr ⟨(mem_product.mp h).1, by simpa using hall 1 (by decide)⟩
  · rintro ⟨a, d⟩ _ ⟨b, e⟩ _ h
    obtain ⟨rfl, hde⟩ := Prod.mk.inj h
    exact Prod.ext rfl (Nat.add_left_cancel hde)

private lemma threshold_bound (ℓ N : ℕ) :
    apThreshold 3 ℓ N ≤ N ^ 2 + 1 ∧
      ∀ A : Finset ℕ, A.card = N → apThreshold 3 ℓ N ≤ apCount A 3 → HasAP A ℓ := by
  let T := {m : ℕ | ∀ A : Finset ℕ, A.card = N → m ≤ apCount A 3 → HasAP A ℓ}
  have ht : N ^ 2 + 1 ∈ T := by
    intro A hA hm
    have := hA ▸ count_le_sq A
    omega
  exact ⟨Nat.sInf_le ht, Nat.sInf_mem ⟨_, ht⟩⟩

-- A point beyond twice the previous maximum cannot complete a four-term progression.
private lemma pad {A : Finset ℕ} (hf : ¬ HasAP A 4) (k : ℕ) :
    ∃ B : Finset ℕ, A ⊆ B ∧ B.card = A.card + k ∧ ¬ HasAP B 4 := by
  induction k with
  | zero => exact ⟨A, Subset.rfl, by simp, hf⟩
  | succ k ih =>
    obtain ⟨B, hAB, hc, hB⟩ := ih
    let x := 2 * B.sup id + 1
    have bound {y : ℕ} (hy : y ∈ B) : y ≤ B.sup id := le_sup (f := id) hy
    have hx : x ∉ B := fun h => by have := bound h; dsimp [x] at this; omega
    refine ⟨insert x B, hAB.trans (subset_insert ..), by rw [card_insert_of_notMem hx, hc]; omega,
      ?_⟩
    rintro ⟨a, d, hd, hall⟩
    have h₂ := mem_insert.mp (hall 2 (by decide))
    have h₃ := mem_insert.mp (hall 3 (by decide))
    have hlast : a + 3 * d ≤ x := by
      rcases h₃ with h | h
      · omega
      · have := bound h
        dsimp [x]
        omega
    have h₂B : a + 2 * d ∈ B := h₂.resolve_left (by omega)
    have hmax := bound h₂B
    apply hB
    refine ⟨a, d, hd, fun i hi => (mem_insert.mp (hall i hi)).resolve_left ?_⟩
    dsimp [x]
    interval_cases i <;> omega

private def layers (S : Finset ℕ) (n t : ℕ) : Finset ℕ :=
  (S.image (fun a => 5 * a) ∪ S.image (fun b => 5 * (b + 2 * n) + 1)) ∪
    S.image (fun c => 5 * (c + t) + 2)

private def offset (n t r : ℕ) : ℕ :=
  if r = 0 then 0 else if r = 1 then 10 * n + 1 else 5 * t + 2

private lemma layer_coords {S : Finset ℕ} {n t x : ℕ} (h : x ∈ layers S n t) :
    x % 5 ≤ 2 ∧ ∃ a ∈ S, x = 5 * a + offset n t (x % 5) := by
  simp only [layers, mem_union, mem_image] at h
  rcases h with ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩)
  · exact ⟨by omega, a, ha, by simp [offset]⟩
  · exact ⟨by omega, a, ha, by simp [offset, Nat.add_mod]; omega⟩
  · exact ⟨by omega, a, ha, by simp [offset, Nat.add_mod]; omega⟩

-- Four terms confined to residues 0, 1, 2 modulo 5 must have constant residue.
private lemma constant_residue (a d : ℕ) (h : ∀ i < 4, (a + i * d) % 5 ≤ 2) : d % 5 = 0 := by
  have check : ∀ r s : Fin 5, (∀ i : Fin 4, (r.val + i.val * s.val) % 5 ≤ 2) → s.val = 0 := by
    decide
  apply check ⟨a % 5, Nat.mod_lt _ (by decide)⟩ ⟨d % 5, Nat.mod_lt _ (by decide)⟩
  intro i
  simpa [Nat.add_mod, Nat.mul_mod] using h i.val i.isLt

private lemma layers_free {S : Finset ℕ} (hf : ThreeAPFree (S : Set ℕ)) (n t : ℕ) :
    ¬ HasAP (layers S n t) 4 := by
  rintro ⟨a, d, hd, h⟩
  have hmod := constant_residue a d fun i hi => (layer_coords (h i hi)).1
  have coords (i : ℕ) (hi : i < 4) :
      ∃ x ∈ S, a + i * d = 5 * x + offset n t (a % 5) := by
    simpa [Nat.add_mod a, Nat.mul_mod i d, hmod] using (layer_coords (h i hi)).2
  obtain ⟨x, hx, hx'⟩ := coords 0 (by decide)
  obtain ⟨y, hy, hy'⟩ := coords 1 (by decide)
  obtain ⟨z, hz, hz'⟩ := coords 2 (by decide)
  have := hf hx hy hz (by omega : x + z = y + y)
  omega

-- Group triples (a,b,c) by the translation that makes their three images a progression.
private def translation (n : ℕ) (p : ℕ × ℕ × ℕ) : ℕ :=
  2 * p.2.1 + 4 * n - (p.1 + p.2.2)

private lemma fiber_le {S : Finset ℕ} {n t : ℕ} (hS : S ⊆ range n)
    {B : Finset ℕ} (hB : layers S n t ⊆ B) :
    (((S ×ˢ (S ×ˢ S)).filter fun p => translation n p = t).card) ≤ apCount B 3 := by
  have unpack {a b c : ℕ}
      (h : (a, b, c) ∈ (S ×ˢ (S ×ˢ S)).filter (fun p => translation n p = t)) :
      (a ∈ S ∧ b ∈ S ∧ c ∈ S) ∧ 2 * b + 4 * n - (a + c) = t := by
    obtain ⟨hm, ht⟩ := mem_filter.mp h
    exact ⟨by simpa only [mem_product] using hm, ht⟩
  let f (p : ℕ × ℕ × ℕ) := (5 * p.1, 5 * (p.2.1 + 2 * n) + 1 - 5 * p.1)
  apply card_le_card_of_injOn (s := (S ×ˢ (S ×ˢ S)).filter (fun p => translation n p = t))
    (t := starts B) f
  · intro ⟨a, b, c⟩ hp
    obtain ⟨⟨ha, hb, hc⟩, ht⟩ := unpack hp
    have ha' := mem_range.mp (hS ha)
    have hc' := mem_range.mp (hS hc)
    have h₀ : 5 * a ∈ B :=
      hB (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ ha)))
    have h₁ : 5 * (b + 2 * n) + 1 ∈ B :=
      hB (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hb)))
    have h₂ : 5 * (c + t) + 2 ∈ B := hB (mem_union_right _ (mem_image_of_mem _ hc))
    dsimp [f]
    apply mem_starts (by omega) h₀
    · convert h₁ using 1
      omega
    · convert h₂ using 1
      omega
  · rintro ⟨a, b, c⟩ hp ⟨a', b', c'⟩ hp' heq
    obtain ⟨⟨ha, _, hc⟩, ht⟩ := unpack hp
    obtain ⟨⟨ha', _, hc'⟩, ht'⟩ := unpack hp'
    have := mem_range.mp (hS ha)
    have := mem_range.mp (hS ha')
    have := mem_range.mp (hS hc)
    have := mem_range.mp (hS hc')
    simp only [f, Prod.mk.injEq] at heq ⊢
    omega

private lemma roth_cube_le {ℓ n N : ℕ} (hℓ : 3 < ℓ) (hn : 3 * n ≤ N) :
    rothNumberNat n ^ 3 ≤ (6 * n) * apThreshold 3 ℓ N := by
  obtain ⟨S, hS, hcard, hfree⟩ := rothNumberNat_spec n
  have hmaps : ((S ×ˢ (S ×ˢ S) : Finset _) : Set _).MapsTo (translation n) (range (6 * n)) := by
    rintro ⟨a, b, c⟩ hp
    simp only [mem_coe, mem_product] at hp
    have := mem_range.mp (hS hp.2.1)
    simp only [mem_coe, mem_range, translation]
    omega
  calc
    rothNumberNat n ^ 3 = (S ×ˢ (S ×ˢ S)).card := by simp [hcard]; ring
    _ = _ := card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _t ∈ range (6 * n), apThreshold 3 ℓ N := by
      apply sum_le_sum
      intro t _
      have hs : S.card ≤ n := by simpa using card_le_card hS
      have hc : (layers S n t).card ≤ N := by
        unfold layers
        grw [card_union_le, card_union_le, card_image_le, card_image_le, card_image_le]
        omega
      obtain ⟨B, hB, hBN, hf⟩ := pad (layers_free hfree n t) (N - (layers S n t).card)
      refine (fiber_le hS hB).trans (le_of_lt (lt_of_not_ge ?_))
      intro h
      obtain ⟨a, d, hd, hall⟩ := (threshold_bound ℓ N).2 B (by omega) h
      exact hf ⟨a, d, hd, fun i hi => hall i (by omega)⟩
    _ = _ := by simp

open Real

private lemma log_bounds {ℓ N : ℕ} (hℓ : 3 < ℓ) (hN : 6 ≤ N) :
    2 * log N - 3 * log 6 - 12 * √(log N) ≤ log (apThreshold 3 ℓ N) ∧
      log (apThreshold 3 ℓ N) ≤ 2 * log N + log 2 := by
  let n := N / 3
  have hn : 0 < n := by dsimp [n]; omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := Behrend.roth_lower_bound (N := n)
  have hr := lt_of_lt_of_le (mul_pos hn' (exp_pos _)) hb
  have hcube : (rothNumberNat n : ℝ) ^ 3 ≤ 6 * n * apThreshold 3 ℓ N := by
    exact_mod_cast roth_cube_le hℓ (show 3 * n ≤ N by dsimp [n]; omega)
  have hF : (0 : ℝ) < apThreshold 3 ℓ N := by
    by_contra! hz
    have hzero : (apThreshold 3 ℓ N : ℝ) = 0 := le_antisymm hz (by positivity)
    rw [hzero, mul_zero] at hcube
    exact (not_lt_of_ge hcube) (pow_pos hr 3)
  have hlogB := log_le_log (mul_pos hn' (exp_pos _)) hb
  rw [log_mul hn'.ne' (exp_pos _).ne', log_exp] at hlogB
  have hlogC := log_le_log (pow_pos hr 3) hcube
  rw [log_pow, log_mul (mul_pos (by norm_num) hn').ne' hF.ne',
    log_mul (by norm_num) hn'.ne'] at hlogC
  norm_num at hlogC
  have hscale : (N : ℝ) ≤ 6 * n := by exact_mod_cast (show N ≤ 6 * n by dsimp [n]; omega)
  have hlogN := log_le_log hN' hscale
  rw [log_mul (by norm_num) hn'.ne'] at hlogN
  have hroot : √(log n) ≤ √(log N) :=
    Real.sqrt_le_sqrt (log_le_log hn' (by exact_mod_cast Nat.div_le_self N 3))
  constructor
  · linarith
  · have hup : (apThreshold 3 ℓ N : ℝ) ≤ (N : ℝ) ^ 2 + 1 := by
      exact_mod_cast (threshold_bound ℓ N).1
    have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have h := log_le_log hF (hup.trans (show (N : ℝ) ^ 2 + 1 ≤ 2 * N ^ 2 by nlinarith))
    rwa [log_mul (by norm_num) (pow_pos hN' 2).ne', log_pow, add_comm] at h

/--
**Erdős Problem 179: $\log F_3(N, \ell) / \log N$ tends to $2$.** For every natural number
$\ell > 3$, $\log F_3(N, \ell) / \log N \to 2$ as $N \to \infty$ over the natural numbers, where
$F_3(N, \ell)$ is the least natural number $m$ such that every $N$-element set
$A \subseteq \mathbb{N}$ containing at least $m$ three-term arithmetic progressions
$a, a + d, a + 2d$ with $d \ge 1$ contains an $\ell$-term arithmetic progression.

Fox and Pohoata prove that $\log f_{s,k}(n) / \log n \to 2$ for all $k > s \ge 3$, where
$f_{s,k}(n)$ is the largest number of $s$-term progressions in an $n$-element set with no
$k$-term progression; since $F_3(N, \ell) = f_{3,\ell}(N) + 1$, taking $s = 3$ and $k = \ell$
gives the statement.

Source: T. F. Bloom,
Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED); resolution: J. Fox
and C. Pohoata, Sets without k-term progressions can have many shorter progressions, Random
Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for all k > s ≥ 3, log
f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of s-term
progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² / (log
log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
-/
public theorem threeAPThresholdExponentTwo_holds : threeAPThresholdExponentTwo := by
  intro ℓ hℓ
  have hlog : Tendsto (fun N : ℕ => log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  have hsqrt := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hlog)
  have lower : Tendsto (fun N : ℕ =>
      2 - 3 * log 6 * (log N)⁻¹ - 12 * (√(log N))⁻¹) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub
      (hinv.const_mul (3 * log 6)) |>.sub (hsqrt.const_mul 12)
  have upper : Tendsto (fun N : ℕ => 2 + log 2 * (log N)⁻¹) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (hinv.const_mul (log 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
  · filter_upwards [eventually_ge_atTop 6] with N hN
    have hpos : 0 < log N := log_pos (by exact_mod_cast (show 1 < N by omega))
    have h := div_le_div_of_nonneg_right (log_bounds hℓ hN).1 hpos.le
    rw [sub_div, sub_div, mul_div_assoc, div_self hpos.ne', mul_one, mul_div_assoc 12,
      Real.sqrt_div_self', one_div] at h
    simpa only [div_eq_mul_inv] using h
  · filter_upwards [eventually_ge_atTop 6] with N hN
    have hpos : 0 < log N := log_pos (by exact_mod_cast (show 1 < N by omega))
    have h := div_le_div_of_nonneg_right (log_bounds hℓ hN).2 hpos.le
    rw [add_div, mul_div_assoc, div_self hpos.ne', mul_one] at h
    simpa only [div_eq_mul_inv] using h

end MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted
