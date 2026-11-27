/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.HalesJewett
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Monochromatic or rainbow arithmetic progressions

We prove that `H(k)^(1/k) / k` tends to infinity. A Hales–Jewett argument gives the
finite threshold. For the lower bound we count colourings, then enlarge the interval
using the prime-block construction of Blankenship, Cummings and Taranchuk as in Bae's
approach. Two stages of the construction suffice with Bertrand's postulate.

Source record `EP-190`.

EP-190: let H(k) be the smallest N such that in any finite colouring of
{1, ..., N} there is a monochromatic k-term arithmetic progression or a
rainbow k-term arithmetic progression. Does H(k)^(1/k) / k tend to infinity
as k tends to infinity?

Colourings are formalized as functions `ℕ → ℕ` (any number of colours),
with the interval condition that every progression term lies in `[0, N)`.
Since only finitely many values occur on a finite interval, this agrees
with finite colourings of `{1, ..., N}` up to translation. If no witness
`N` exists, `H k` defaults to `0`; the cases `k = 0, 1` are degenerate.
The trailing survey clause "Estimate H(k)" is not formalized.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosRainbowAPGrowthWanted

open Filter Finset

/-- **Good arithmetic progressions.** Let $f : \mathbb{N} \to \mathbb{N}$ be a colouring and let
$N$ and $k$ be natural numbers. The colouring $f$ has a good $k$-term arithmetic progression below
$N$ if there are natural numbers $a$ and $d > 0$ with $a + d(k - 1) < N$, where $k - 1$ is
natural-number subtraction (so it is $0$ when $k = 0$), such that the colours $f(a + di)$ for
$i < k$ are either all equal (the progression is monochromatic) or pairwise distinct (it is
rainbow). For $k \ge 1$ the condition $a + d(k - 1) < N$ says that every term $a + di$ with
$i < k$ lies in $\{0, \dots, N - 1\}$. -/
def HasGoodAP (f : ℕ → ℕ) (N k : ℕ) : Prop :=
  ∃ a d : ℕ,
    0 < d ∧
      a + d * (k - 1) < N ∧
        ((∀ i j : Fin k, f (a + d * (i : ℕ)) = f (a + d * (j : ℕ))) ∨
          ∀ i j : Fin k, i ≠ j → f (a + d * (i : ℕ)) ≠ f (a + d * (j : ℕ)))

/-- **Monochromatic-or-rainbow progression number.** For a natural number $k$, $H(k)$ is the least
natural number $N$ such that every colouring $f : \mathbb{N} \to \mathbb{N}$ has a good $k$-term
arithmetic progression below $N$, that is, there are natural numbers $a$ and $d > 0$ with
$a + d(k - 1) < N$, where $k - 1$ is natural-number subtraction, such that the colours $f(a + di)$
for $i < k$ are all equal or pairwise distinct. If no such $N$ exists, then $H(k) = 0$. -/
noncomputable def H (k : ℕ) : ℕ :=
  haveI := Classical.propDecidable (∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N k)
  if h : ∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N k then
    @Nat.find (fun N => ∀ f : ℕ → ℕ, HasGoodAP f N k) (Classical.decPred _) h
  else
    0

/-- **Erdős Problem 190 on monochromatic or rainbow progressions.** For a natural number $k$, let
$H(k)$ be the least natural number $N$ such that every colouring $f : \mathbb{N} \to \mathbb{N}$
has a good $k$-term arithmetic progression below $N$, that is, there are natural numbers $a$ and
$d > 0$ with $a + d(k - 1) < N$, where $k - 1$ is natural-number subtraction, such that the colours
$f(a + di)$ for $i < k$ are all equal or pairwise distinct; let $H(k) = 0$ if no such $N$ exists.
The proposition asserts that $H(k)^{1/k}/k \to \infty$ as $k \to \infty$. -/
def conjecture : Prop :=
  Tendsto (fun k : ℕ => ((H k : ℝ) ^ ((k : ℝ)⁻¹)) / (k : ℝ)) atTop atTop

-- A word on a combinatorial line has the same fixed coordinates at each letter.
private lemma line_sum {ι α : Type*} [Fintype ι] (l : Combinatorics.Line α ι)
    (g : α → ℕ) (x : α) :
    ∑ v, g (l x v) = (∑ v, ((l.idxFun v).map g).getD 0) +
      (univ.filter fun v => (l.idxFun v).isNone).card * g x := by
  classical
  rw [← Nat.nsmul_eq_mul, ← sum_const, sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  cases h : l.idxFun v <;> simp [h]

-- Colour each progression by two indices with equal colours. On a Hales-Jewett line
-- with the same two indices, keep the first endpoint fixed and vary the second.
private theorem threshold_exists {k : ℕ} (hk : 0 < k) :
    ∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N k := by
  classical
  let A := Fin k × Fin k
  obtain ⟨ι, _, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension A A
  let u (x : A) := x.1.val * (k - x.2.val)
  let v (x : A) := x.2.val
  let a (w : ι → A) := ∑ s, u (w s)
  let d (w : ι → A) := (∑ s, v (w s)) + 1
  let last (w : ι → A) := a w + d w * (k - 1)
  let N := univ.sup last + 1
  have bound (w) : last w < N := Nat.lt_succ_of_le (le_sup (mem_univ w))
  refine ⟨N, fun f => ?_⟩
  by_contra bad
  have collisions (w : ι → A) : ∃ q : A, q.1 < q.2 ∧
      f (a w + d w * q.1.val) = f (a w + d w * q.2.val) := by
    by_contra! no
    apply bad
    refine ⟨a w, d w, Nat.zero_lt_succ _, bound w, Or.inr ?_⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact no (i, j) h
    · exact (no (j, i) h).symm
  choose C hlt heq using collisions
  obtain ⟨l, ⟨i, j⟩, hC⟩ := hι C
  let w (t : Fin k) := l (i, t)
  have hc (t : Fin k) :
      f (a (w t) + d (w t) * i.val) = f (a (w t) + d (w t) * j.val) := by
    simpa [w, hC (i, t)] using heq (w t)
  have hij : i.val < j.val := by
    simpa [hC (i, i)] using hlt (l (i, i))
  let m := (univ.filter fun s => (l.idxFun s).isNone).card
  have hm : 0 < m := by
    obtain ⟨s, hs⟩ := l.proper
    exact card_pos.mpr ⟨s, by simp [hs]⟩
  let b := ∑ s, ((l.idxFun s).map u).getD 0
  let e := (∑ s, ((l.idxFun s).map v).getD 0) + 1
  have ha (t : Fin k) : a (w t) = b + m * (i.val * (k - t.val)) := line_sum l u (i, t)
  have hd (t : Fin k) : d (w t) = e + m * t.val := by
    change (∑ s, v (l (i, t) s)) + 1 = _
    rw [line_sum l v]
    dsimp [e, m, v]
    omega
  let start := b + m * i.val * k + e * j.val
  let step := m * (j.val - i.val)
  have coords (t : Fin k) :
      a (w t) + d (w t) * i.val = b + m * i.val * k + e * i.val ∧
      a (w t) + d (w t) * j.val = start + step * t.val := by
    rw [ha, hd]
    have ht := Nat.sub_add_cancel t.isLt.le
    have hj := Nat.sub_add_cancel hij.le
    dsimp [start, step]
    constructor <;> nlinarith only [congrArg (fun z => m * i.val * z) ht,
      congrArg (fun z => m * t.val * z) hj]
  apply bad
  refine ⟨start, step, Nat.mul_pos hm (Nat.sub_pos_of_lt hij), ?_, Or.inl ?_⟩
  · let t : Fin k := ⟨k - 1, by omega⟩
    change start + step * t.val < N
    rw [← (coords t).2]
    exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : j.val ≤ k - 1)) _)
      (bound (w t))
  · intro x y
    have hx := hc x
    have hy := hc y
    rw [(coords x).1, (coords x).2] at hx
    rw [(coords y).1, (coords y).2] at hy
    exact hx.symm.trans hy

private def Avoids (k N r : ℕ) : Prop :=
  ∃ f : ℕ → Fin r, ∀ a d : ℕ, 0 < d → a + d * (k - 1) < N →
    ¬ ∀ i : Fin k, f (a + d * i.val) = f a

-- In residue class s, skip the block of b colours starting at s * b.
private def skipBlock (b s x : ℕ) := if x < s * b then x else x + b

private lemma skipBlock_inj (b s : ℕ) : Function.Injective (skipBlock b s) := by
  intro x y h
  unfold skipBlock at h
  split at h <;> split at h <;> omega

private lemma skipBlock_ne {b c : ℕ} (hb : 0 < b) (x : ℕ) :
    skipBlock b (c / b) x ≠ c := by
  have h := Nat.mod_add_div c b
  have hh := Nat.mod_lt c hb
  rw [Nat.mul_comm b] at h
  unfold skipBlock
  split <;> omega

private lemma hits_residue {p a d s : ℕ} (hp : p.Prime) (hs : s < p) (hd : ¬ p ∣ d) :
    ∃ i < p, (a + d * i) % p = s := by
  let _ : Fact p.Prime := ⟨hp⟩
  let z : ZMod p := (s - a) / d
  have hn : (d : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff d p).mp hd
  refine ⟨z.val, z.val_lt, ?_⟩
  have eqn : ((a + d * z.val : ℕ) : ZMod p) = (s : ZMod p) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    dsimp [z]
    field_simp
    ring
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hs] using congrArg ZMod.val eqn

-- In the block construction of Blankenship, Cummings and Taranchuk, a progression with
-- difference divisible by p projects to a progression of block indices. Every other
-- progression meets all p residue classes, including one that excludes its first colour.
private lemma expand {k N r p b : ℕ} (hp : p.Prime) (hpk : p ≤ k) (hb : 0 < b)
    (hr : r + b ≤ p * b) (h : Avoids k N r) : Avoids k (p * N) (r + b) := by
  obtain ⟨f, hf⟩ := h
  let F (n : ℕ) : Fin (r + b) := ⟨skipBlock b (n % p) (f (n / p)).val, by
    have := (f (n / p)).isLt
    unfold skipBlock
    split <;> omega⟩
  refine ⟨F, fun a d hd hN mono => ?_⟩
  by_cases hdiv : p ∣ d
  · obtain ⟨e, rfl⟩ := hdiv
    have rep (i : ℕ) : a + p * e * i = a + p * (e * i) := by ring
    have quo (i : ℕ) : (a + p * e * i) / p = a / p + e * i := by
      rw [rep, Nat.add_mul_div_left _ _ hp.pos]
    have remn (i : ℕ) : (a + p * e * i) % p = a % p := by simp [rep]
    apply hf (a / p) e (Nat.pos_of_mul_pos_left hd) (by
      rw [← quo, Nat.div_lt_iff_lt_mul hp.pos]
      simpa only [Nat.mul_comm N p] using hN)
    intro i
    have he := congrArg Fin.val (mono i)
    change skipBlock _ _ _ = skipBlock _ _ _ at he
    rw [quo, remn] at he
    exact Fin.ext (skipBlock_inj b _ he)
  · let c := (F a).val
    have hs : c / b < p := (Nat.div_lt_iff_lt_mul hb).mpr ((F a).isLt.trans_le hr)
    obtain ⟨i, hi, hh⟩ := hits_residue (a := a) hp hs hdiv
    have eqn := congrArg Fin.val (mono ⟨i, hi.trans_le hpk⟩)
    change skipBlock b ((a + d * i) % p) _ = c at eqn
    rw [hh] at eqn
    exact skipBlock_ne hb _ eqn

private lemma expand_many {k N r p b : ℕ} (hp : p.Prime) (hpk : p ≤ k) (hb : 0 < b)
    (h : Avoids k N r) (n : ℕ) (hr : r + n * b ≤ p * b) :
    Avoids k (p ^ n * N) (r + n * b) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.succ_mul] at hr ⊢
    have prev := ih (by omega)
    simpa [pow_succ', Nat.mul_assoc, Nat.add_assoc] using expand hp hpk hb
      (r := r + n * b) (by omega) prev

-- Counting colourings by a progression and its common colour gives the initial interval.
private theorem count_base {N r k : ℕ} (hk : 2 ≤ k) (hNk : k ≤ N) (hr : 0 < r)
    (hsize : N * N * r < r ^ k) : Avoids k N r := by
  classical
  let Q := {q : Fin N × Fin N // 0 < q.2.val ∧ q.1.val + q.2.val * (k - 1) < N}
  let point (q : Q) (i : Fin k) : Fin N := ⟨q.val.1 + q.val.2 * i.val, by
    apply lt_of_le_of_lt _ q.property.2
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _⟩
  let terms (q : Q) := univ.image (point q)
  have hterms (q : Q) : (terms q).card = k := by
    have inj : Function.Injective (point q) := by
      intro i j h
      have eqn := congrArg Fin.val h
      change q.val.1.val + q.val.2.val * i.val = q.val.1.val + q.val.2.val * j.val at eqn
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left q.property.1 (Nat.add_left_cancel eqn))
    simp [terms, card_image_of_injective _ inj]
  let bad (z : Q × Fin r) : Finset (Fin N → Fin r) :=
    Fintype.piFinset (fun x => if x ∈ terms z.1 then {z.2} else univ)
  have hbad (z) : (bad z).card = r ^ (N - k) := by
    simp only [bad, Fintype.card_piFinset, apply_ite Finset.card, card_singleton, card_univ,
      Fintype.card_fin, prod_ite, prod_const_one, one_mul, prod_const]
    rw [show (univ.filter fun x => x ∉ terms z.1) = (terms z.1)ᶜ by ext; simp]
    rw [Finset.card_compl, Fintype.card_fin, hterms]
  have hQ : Fintype.card Q ≤ N * N := by
    simpa using Fintype.card_le_of_injective (Subtype.val : Q → Fin N × Fin N)
      Subtype.val_injective
  have hsmall : (univ.biUnion bad).card < (univ : Finset (Fin N → Fin r)).card := by
    calc
      _ ≤ univ.card * r ^ (N - k) :=
        card_biUnion_le_card_mul _ _ _ (fun z _ => (hbad z).le)
      _ ≤ (N * N * r) * r ^ (N - k) := by
        simp only [card_univ, Fintype.card_prod, Fintype.card_fin]
        gcongr
      _ < r ^ k * r ^ (N - k) := Nat.mul_lt_mul_of_pos_right hsize (pow_pos hr _)
      _ = _ := by simp [← pow_add, Nat.add_sub_of_le hNk]
  obtain ⟨f, _, hf⟩ := exists_mem_notMem_of_card_lt_card hsmall
  let F (n : ℕ) : Fin r := if h : n < N then f ⟨n, h⟩ else ⟨0, hr⟩
  refine ⟨F, fun a d hd hb mono => hf ?_⟩
  have ha : a < N := by omega
  have hD : d < N := by nlinarith only [hb, Nat.sub_add_cancel (by omega : 1 ≤ k), hk]
  let q : Q := ⟨(⟨a, ha⟩, ⟨d, hD⟩), hd, hb⟩
  refine mem_biUnion.mpr ⟨(q, F a), mem_univ _, Fintype.mem_piFinset.mpr (fun x => ?_)⟩
  by_cases hx : x ∈ terms q
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    have hh := (point q i).isLt
    change a + d * i.val < N at hh
    simpa [hx, F, hh, ha, point, q] using mono i
  · simp [hx]

-- Fewer than k colours rules out a rainbow progression by the pigeonhole principle.
private lemma lt_threshold {k N r : ℕ} (hr : r < k) (h : Avoids k N r) : N < H k := by
  classical
  have hk : 0 < k := by omega
  have hex := threshold_exists hk
  have hH : ∀ f : ℕ → ℕ, HasGoodAP f (H k) k := by
    unfold H
    rw [dite_eq_left hex]
    exact Nat.find_spec hex
  obtain ⟨f, hf⟩ := h
  obtain ⟨a, d, hd, hlast, hmono | hrain⟩ := hH fun n => (f n).val
  · by_contra! hle
    apply hf a d hd (lt_of_lt_of_le hlast hle)
    intro i
    exact Fin.ext (by simpa using hmono i ⟨0, hk⟩)
  · have hinj : Function.Injective (fun i : Fin k => f (a + d * i.val)) := by
      intro i j he
      by_contra hij
      exact hrain i j hij (congrArg Fin.val he)
    have := Fintype.card_le_of_injective _ hinj
    simp at this
    omega

-- The counting bound gives length t^(7t). Bertrand supplies a prime between 8t and 16t.
-- Each of 6t expansions costs one colour, then each of 4t expansions costs two. The
-- resulting 15t colours are fewer than k, and the length has gained a factor p^(10t).
private lemma growth_bound {k t : ℕ} (ht : 32 ≤ t) (hk : 16 * t ≤ k)
    (hk' : k < 16 * (t + 1)) : t ^ (17 * t) < H k := by
  obtain ⟨p, hp, htp, hpt⟩ := Nat.bertrand (8 * t) (by omega)
  have hpk : p ≤ k := by omega
  have init : Avoids k (t ^ (7 * t)) t := by
    apply count_base (by omega)
    · calc
        k ≤ t ^ 2 := by nlinarith
        _ ≤ t ^ (7 * t) := Nat.pow_le_pow_right (by omega) (by omega)
    · omega
    · calc
        t ^ (7 * t) * t ^ (7 * t) * t = t ^ (7 * t + 7 * t + 1) := by
          rw [pow_succ, pow_add]
        _ < t ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  have one := expand_many hp hpk (b := 1) (by decide) init (6 * t) (by omega)
  have two := expand_many hp hpk (b := 2) (by decide) one (4 * t) (by omega)
  apply lt_of_le_of_lt _ (lt_threshold (by omega) two)
  calc
    t ^ (17 * t) = t ^ (4 * t) * (t ^ (6 * t) * t ^ (7 * t)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ _ := by gcongr <;> omega

private lemma eventually_pow_le (C : ℕ) (hC : 0 < C) :
    ∀ᶠ k : ℕ in Filter.atTop, (C * k) ^ k ≤ H k := by
  rw [Filter.eventually_atTop]
  refine ⟨16 * max 32 ((17 * C) ^ 34), fun k hk => ?_⟩
  let t := k / 16
  have ht : max 32 ((17 * C) ^ 34) ≤ t := by dsimp [t]; omega
  have ht' : 32 ≤ t := le_trans (le_max_left ..) ht
  have hlarge : (17 * C) ^ 34 ≤ t := le_trans (le_max_right ..) ht
  have hlo : 16 * t ≤ k := by dsimp [t]; omega
  have hhi : k < 16 * (t + 1) := by dsimp [t]; omega
  have slack : k ≤ 34 * (17 * t - k) := by omega
  have hc : (17 * C) ^ k ≤ t ^ (17 * t - k) := by
    calc
      _ ≤ (17 * C) ^ (34 * (17 * t - k)) := Nat.pow_le_pow_right (by omega) slack
      _ = _ ^ (17 * t - k) := pow_mul ..
      _ ≤ _ := Nat.pow_le_pow_left hlarge _
  calc
    (C * k) ^ k ≤ ((17 * C) * t) ^ k := by
      apply Nat.pow_le_pow_left
      calc
        _ ≤ C * (17 * t) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    _ = (17 * C) ^ k * t ^ k := mul_pow ..
    _ ≤ t ^ (17 * t - k) * t ^ k := Nat.mul_le_mul_right _ hc
    _ = t ^ (17 * t) := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
    _ ≤ H k := (growth_bound ht' hlo hhi).le

/--
**Solution of Erdős Problem 190 on monochromatic or rainbow progressions.** For a natural number
$k$, let $H(k)$ be the least natural number $N$ such that every colouring
$f : \mathbb{N} \to \mathbb{N}$ has a good $k$-term arithmetic progression below $N$, that is,
there are natural numbers $a$ and $d > 0$ with $a + d(k - 1) < N$, where $k - 1$ is natural-number
subtraction, such that the colours $f(a + di)$ for $i < k$ are all equal or pairwise distinct;
let $H(k) = 0$ if no such $N$ exists. Then $H(k)^{1/k}/k \to \infty$ as $k \to \infty$.

This answers Erdős Problem 190 affirmatively; it was proved by Bae and, independently, by Fox and
Hunter.

Source: T. F. Bloom, Erdős Problem #190,
erdosproblems.com (live page, LaTeX source and forum threads read 2026-10-22),
https://www.erdosproblems.com/190; J. H. Bae, A resolution of Erdős Problem #190 via
Erdős-Lovász, BCT, and Baker-Harman-Pintz, arXiv:2604.20588 (2026),
https://arxiv.org/abs/2604.20588; J. Fox and Z. Hunter, Three-color van der Waerden numbers grow
super-exponentially, arXiv:2606.02541 (2026), https://arxiv.org/abs/2606.02541. Moved from
`OpenConjectures/Combinatorics/ErdosRainbowAPGrowth`.
-/
public theorem conjecture_holds : conjecture := by
  refine Filter.tendsto_atTop.2 fun c => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (max c 0)
  have hn' : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right ..) hn
  filter_upwards [eventually_pow_le n (by exact_mod_cast hn'),
    Filter.eventually_ge_atTop (1 : ℕ)] with k h hpos
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (le_div_iff₀ hk).2
  calc
    c * k ≤ (n : ℝ) * k := by gcongr; exact (le_max_left ..).trans hn.le
    _ ≤ (H k : ℝ) ^ (k : ℝ)⁻¹ := by
      apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hk).2
      rw [Real.rpow_natCast]
      exact_mod_cast h

end MathlibExt.Combinatorics.ErdosRainbowAPGrowthWanted
