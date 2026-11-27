/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import MathlibExt.Combinatorics.Additive.SingerDifferenceSet

/-!
# Counting Sidon subsets of an interval

The base-two logarithm of the number of Sidon subsets of `{1, …, N}`, divided by the
maximum size of a Sidon subset, does not tend to one. For primes `p`, a Singer difference set
with `p + 1` residues gives at least `4 ^ (p + 1)` Sidon subsets of the interval of length
`3 * (p ^ 2 + p + 1)`. An additive-energy bound shows that every Sidon subset of this
interval has size at most `1.9 * (p + 1)` for all sufficiently large `p`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted

open Classical in
/-- **Sidon subsets of $\{1, \dots, N\}$.** For a natural number $N$, this is the finite family
of all subsets of $\{1, \dots, N\}$ that are Sidon sets of natural numbers, including the empty
set and the singletons. -/
noncomputable def sidonSubsetsUpTo (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter fun S => (S : Set ℕ).IsSidon

/-- **Largest Sidon subset of $\{1, \dots, N\}$ (Erdős Problem 861).** For a natural number $N$,
$f(N)$ is the largest cardinality of a Sidon subset of $\{1, \dots, N\}$. -/
noncomputable def maxSidonSize (N : ℕ) : ℕ :=
  (sidonSubsetsUpTo N).sup Finset.card

/-- **Erdős Problem 861, first question.** Let $A(N)$ be the number of Sidon subsets of
$\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. The statement is that
$A(N) / 2^{f(N)} \to \infty$ as $N \to \infty$. -/
def sidonCountOverTwoPowMaxDiverges : Prop :=
  Filter.Tendsto (fun N : ℕ => ((sidonSubsetsUpTo N).card : ℝ) / 2 ^ maxSidonSize N)
    Filter.atTop Filter.atTop

/-- **Erdős Problem 861, second question.** Let $A(N)$ be the number of Sidon subsets of
$\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. The statement is that
$\log_2 A(N) / f(N) \to 1$ as $N \to \infty$, that is, $A(N) = 2^{(1 + o(1)) f(N)}$. -/
def sidonCountExponentAsymptotic : Prop :=
  Filter.Tendsto (fun N : ℕ => Real.logb 2 (sidonSubsetsUpTo N).card / maxSidonSize N)
    Filter.atTop (nhds 1)

open Finset

/-- Each modular Sidon residue can be omitted or lifted into any of three consecutive
blocks. Reducing a sum modulo the block length recovers its two indices up to order. -/
private theorem count_lifts {m : ℕ} [NeZero m] (D : Finset (ZMod m))
    (hD : (D : Set (ZMod m)).IsSidon) :
    4 ^ D.card ≤ (sidonSubsetsUpTo (3 * m)).card := by
  classical
  let a : D → ZMod m := Subtype.val
  let lift (i : D) (t : Fin 3) := (a i).val + m * t.val + 1
  have hred (i : D) (t : Fin 3) : (lift i t : ZMod m) = a i + 1 := by simp [lift]
  have hinj {i j : D} {s t : Fin 3} (h : lift i s = lift j t) : i = j ∧ s = t := by
    have hm := congrArg (Nat.cast : ℕ → ZMod m) h
    simp only [hred, add_left_inj] at hm
    have hij : i = j := Subtype.ext hm
    subst j
    refine ⟨rfl, Fin.ext ?_⟩
    simpa [lift, NeZero.ne m] using h
  let family (f : D → Option (Fin 3)) :=
    (univ.filter fun it : D × Fin 3 ↦ f it.1 = some it.2).image fun it ↦ lift it.1 it.2
  have mem_family {f x} :
      x ∈ family f ↔ ∃ i t, f i = some t ∧ lift i t = x := by simp [family]
  have decode {f i t} : lift i t ∈ family f ↔ f i = some t := by
    refine ⟨fun h ↦ ?_, fun h ↦ mem_family.mpr ⟨i, t, h, rfl⟩⟩
    obtain ⟨j, s, hjs, he⟩ := mem_family.mp h
    obtain ⟨rfl, rfl⟩ := hinj he
    exact hjs
  have hfamily : Function.Injective family := by
    intro f g h
    funext i
    cases hf : f i with
    | some t => exact (decode.mp (h ▸ decode.mpr hf)).symm
    | none =>
      cases hg : g i with
      | none => rfl
      | some t => exact hf.symm.trans (decode.mp (h.symm ▸ decode.mpr hg))
  have hmem (f) : family f ∈ sidonSubsetsUpTo (3 * m) := by
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      obtain ⟨i, t, _, rfl⟩ := mem_family.mp hx
      have hval := (a i).val_lt
      have ht := Nat.mul_le_mul_left m (show t.val ≤ 2 by omega)
      exact mem_Icc.mpr ⟨by simp [lift], by dsimp [lift]; omega⟩
    · intro x hx y hy z hz w hw he
      obtain ⟨i, s, hi, rfl⟩ := mem_family.mp hx
      obtain ⟨j, t, hj, rfl⟩ := mem_family.mp hy
      obtain ⟨u, b, hu, rfl⟩ := mem_family.mp hz
      obtain ⟨v, c, hv, rfl⟩ := mem_family.mp hw
      have he' := congrArg (Nat.cast : ℕ → ZMod m) he
      simp only [Nat.cast_add, hred] at he'
      have hsum : a i + a j = a u + a v := by linear_combination he'
      rcases hD _ i.2 _ j.2 _ u.2 _ v.2 hsum with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
        obtain rfl := Subtype.ext h₁ <;> obtain rfl := Subtype.ext h₂
      · obtain rfl := Option.some.inj (hi.symm.trans hu)
        obtain rfl := Option.some.inj (hj.symm.trans hv)
        exact Or.inl ⟨rfl, rfl⟩
      · obtain rfl := Option.some.inj (hi.symm.trans hv)
        obtain rfl := Option.some.inj (hj.symm.trans hu)
        exact Or.inr ⟨rfl, rfl⟩
  simpa using card_le_card_of_injOn (s := univ) family (fun f _ ↦ hmem f) hfamily.injOn

/-- Three blocks of a Singer difference set give four choices at each of its residues. -/
private theorem singer_count_bound {p : ℕ} (hp : p.Prime) :
    2 ^ (2 * (p + 1)) ≤ (sidonSubsetsUpTo (3 * (p ^ 2 + p + 1))).card := by
  let m := p ^ 2 + p + 1
  obtain ⟨D, hcard, hdiff⟩ :=
    MetaMathlibExt.singer_cyclic_difference_set_exists p hp.isPrimePow
  have hD : (D : Set (ZMod m)).IsSidon := by
    intro a ha b hb c hc d hd h
    by_cases hac : a = c
    · subst c
      exact Or.inl ⟨rfl, add_left_cancel h⟩
    · have he : d - b = a - c := by linear_combination -h
      have hu := hdiff (a - c) (sub_ne_zero.mpr hac)
      have hpairs := hu.unique (y₁ := (⟨a, ha⟩, ⟨c, hc⟩)) (y₂ := (⟨d, hd⟩, ⟨b, hb⟩)) rfl he
      exact Or.inr ⟨congrArg (fun z : D × D ↦ z.1.val) hpairs,
        (congrArg (fun z : D × D ↦ z.2.val) hpairs).symm⟩
  simpa only [hcard, pow_mul, Nat.reducePow] using count_lifts D hD

/-- For a Sidon set, two distinct translates intersect in at most one point.
Thus an energy quadruple is determined by either a diagonal incidence or two shifts. -/
private theorem energy_le_of_sidon {s : Finset ℕ} (hs : (s : Set ℕ).IsSidon) (t : Finset ℕ) :
    s.addEnergy t ≤ s.card * t.card + t.card ^ 2 := by
  let code (q : (ℕ × ℕ) × ℕ × ℕ) : (ℕ × ℕ) ⊕ (ℕ × ℕ) :=
    if q.2.1 = q.2.2 then .inl (q.1.1, q.2.1) else .inr q.2
  rw [sq, ← card_product, ← card_product, ← card_disjSum]
  unfold addEnergy
  apply card_le_card_of_injOn code
  · rintro ⟨⟨a, b⟩, u, v⟩ h
    simp only [Finset.mem_coe, mem_filter, mem_product] at h
    by_cases huv : u = v <;> simp [code, huv, h.1.1.1, h.1.2.1, h.1.2.2]
  · rintro ⟨⟨a, b⟩, u, v⟩ hab ⟨⟨c, d⟩, w, x⟩ hcd he
    simp only [Finset.mem_coe, mem_filter, mem_product] at hab hcd
    by_cases huv : u = v <;> by_cases hwx : w = x <;>
      simp only [code, huv, hwx, ↓reduceIte, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, Prod.mk.injEq] at he
    · obtain ⟨rfl, rfl⟩ := he
      have := hab.2
      have := hcd.2
      simp_all
    · obtain ⟨rfl, rfl⟩ := he
      rcases hs a hab.1.1.1 d hcd.1.1.2 c hcd.1.1.1 b hab.1.1.2 (by omega) with h | h
      · simp [h.1, h.2]
      · omega

/-- Apply Cauchy–Schwarz to sums of elements of `s` and shifts less than `r`. -/
private theorem size_bound {N : ℕ} {s : Finset ℕ} (hN : s ⊆ Icc 1 N)
    (hs : (s : Set ℕ).IsSidon) (r : ℕ) :
    (s.card * r) ^ 2 ≤ (N + r) * (s.card * r + r ^ 2) := by
  have h := card_sq_le_card_mul_addEnergy s (range r) (range (N + r))
  rw [filter_eq_self.mpr, card_product, card_range, card_range] at h
  · exact h.trans (Nat.mul_le_mul_left _ (by simpa using energy_le_of_sidon hs (range r)))
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    exact mem_range.mpr (Nat.add_lt_add_of_le_of_lt (mem_Icc.mp (hN ha)).2 (mem_range.mp hb))

/-- Translating by the first `20 * k` shifts bounds the maximum size by `1.9 * k`
in an interval of length at most `3 * k ^ 2`, for sufficiently large `k`. -/
private theorem max_size_bound {N k : ℕ} (hk₀ : 200 ≤ k) (hN : N ≤ 3 * k * k) :
    10 * maxSidonSize N ≤ 19 * k := by
  classical
  suffices h : ∀ s ∈ sidonSubsetsUpTo N, 10 * s.card ≤ 19 * k by
    have hsup : maxSidonSize N ≤ 19 * k / 10 :=
      Finset.sup_le fun s hs ↦
        (Nat.le_div_iff_mul_le (by decide)).2 (by simpa [mul_comm] using h s hs)
    simpa [mul_comm] using (Nat.le_div_iff_mul_le (by decide)).1 hsup
  intro s hmem
  obtain ⟨hsub, hs⟩ := mem_filter.mp hmem
  by_contra! hlarge
  let r := 20 * k
  have hr : 0 < r := by dsimp [r]; omega
  have hk : 0 < s.card := by omega
  have henergy := size_bound (N := N) (mem_powerset.mp hsub) hs r
  have hcancel : s.card ^ 2 * r ≤ (N + r) * (s.card + r) := by
    refine Nat.le_of_mul_le_mul_right (c := r) ?_ hr
    calc
      _ = (s.card * r) ^ 2 := by ring
      _ ≤ _ := henergy
      _ = _ := by ring
  have hlinear : s.card * r ≤ (N + r) * 12 := by
    refine Nat.le_of_mul_le_mul_right (c := s.card) ?_ hk
    calc
      _ = s.card ^ 2 * r := by ring
      _ ≤ _ := hcancel
      _ ≤ (N + r) * (12 * s.card) := Nat.mul_le_mul_left _ (by dsimp [r]; omega)
      _ = _ := by ring
  have hfinal : 20 * s.card ≤ 36 * k + 240 := by
    refine Nat.le_of_mul_le_mul_right (c := k) ?_ (by omega)
    calc
      _ = s.card * r := by dsimp [r]; ring
      _ ≤ _ := hlinear
      _ ≤ (3 * k * k + r) * 12 := by gcongr
      _ = _ := by dsimp [r]; ring
  omega

/--
**Erdős Problem 861, second question: negative answer.** Let $A(N)$ be the number of Sidon
subsets of $\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. Then the ratio $\log_2 A(N) / f(N)$ does not
tend to $1$ as $N \to \infty$; that is, $A(N) = 2^{(1 + o(1)) f(N)}$ fails.

Saxton and Thomason proved $A(N) \ge 2^{(1.16 + o(1)) \sqrt{N}}$ (Theorem 2.11), and
$f(N) \sim \sqrt{N}$, so $\log_2 A(N) / f(N) \ge 1.16 + o(1)$.

Source: T. F. Bloom, Erdős Problems, Problem #861, https://www.erdosproblems.com/861 (status
SOLVED); resolution: D. Saxton and A. Thomason, Hypergraph containers, Invent. Math. (2015),
925-992, arXiv:1204.6595 (lower bound); Y. Kohayakawa, S. J. Lee, V. Rödl and W. Samotij, The number
of Sidon sets and the maximum size of Sidon sets contained in a sparse random set of integers,
Random Structures Algorithms (2015), 1-25 (upper bound), Saxton-Thomason Theorem 2.11: there are
between 2^{(1.16 + o(1)) √n} and 2^{(55 + o(1)) √n} Sidon subsets of [n], the lower bound answering
negatively whether there are only 2^{(1 + o(1)) √n}; erdosproblems.com/861: f(N) ∼ N^{1/2}, both
questions are settled, the first positively and the second negatively, and 2^{1.16 f(N)} ≤ A(N) ≤
2^{6.442 f(N)} for large N, https://arxiv.org/abs/1204.6595.
-/
public theorem sidonCountExponentAsymptotic_refuted : ¬ sidonCountExponentAsymptotic := by
  intro h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (h (Ioo_mem_nhds (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 20 / 19 by norm_num)))
  obtain ⟨p, hp, hpPrime⟩ := Nat.exists_infinite_primes (max N₀ 200)
  have hp200 : 200 ≤ p := le_trans (le_max_right ..) hp
  let m := p ^ 2 + p + 1
  have hm : p ≤ m := by dsimp [m]; omega
  have hcount := singer_count_bound hpPrime
  have hlog := Real.logb_le_logb_of_le (b := 2) (y := ((sidonSubsetsUpTo (3 * m)).card : ℝ))
    (by norm_num) (show (0 : ℝ) < 2 ^ (2 * (p + 1)) by positivity) (by exact_mod_cast hcount)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  obtain ⟨hpos, hlt⟩ := hN₀ (3 * m) (by have := (le_max_left N₀ 200).trans hp; omega)
  change 0 < Real.logb 2 _ / (maxSidonSize (3 * m) : ℝ) at hpos
  change Real.logb 2 _ / (maxSidonSize (3 * m) : ℝ) < 20 / 19 at hlt
  have hf : 0 < (maxSidonSize (3 * m) : ℝ) := by
    rcases (Nat.cast_nonneg (α := ℝ) (maxSidonSize (3 * m))).eq_or_lt with h | h
    · simp [← h] at hpos
    · exact h
  have hmax : 10 * (maxSidonSize (3 * m) : ℝ) ≤ 19 * (p + 1) := by
    exact_mod_cast max_size_bound (k := p + 1) (by omega) (by dsimp [m]; nlinarith :
      3 * m ≤ 3 * (p + 1) * (p + 1))
  push_cast at hlog
  linarith [(div_lt_iff₀ hf).mp hlt]

end MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted
