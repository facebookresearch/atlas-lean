/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 857: weak sunflower conjecture for k ≥ 4

See https://www.erdosproblems.com/857 and P. Erdős and E. Szemerédi,
"Combinatorial properties of systems of sets,"
Journal of Combinatorial Theory, Series A 24(3) (1978), 308–313.
UnsolvedMath record id 2345 / EP-857. Proved by Bucić, He and Lee,
arXiv:2610.26686 (2026), Theorem 1.

The main theorem `conjecture_holds` gives the eventual exponential bound with a base below two.
The proof adapts the interpolation and dimension argument of Bucić, He and Lee (Section 3).
Write `r = k - 1` and partition the ground set into blocks of size `D`, padding the last block.
Singleton subsets of a block are letters of a `D`-letter alphabet. On these letters the local
tester interpolates in one of the `r` petal variables. Each nonsingleton uses a common point
indicator. After taking products over blocks, a weighted count bounds the dimension on one petal
by `W ^ b`, where `b` is the number of blocks and `W = 2 ^ D - D / 2 + r * 2 ^ r`. Choosing
`D = 4 * r * 2 ^ r` gives the strict saving `W < 2 ^ D`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem857WeakSunflowerWanted

/-- **Families containing a sunflower.** Let $n$ and $k$ be natural numbers. A family $F$ of
subsets of $\{0, \dots, n-1\}$ contains a $k$-sunflower if some subfamily $T \subseteq F$ with
exactly $k$ members satisfies $A \cap B = C \cap D$ for all $A, B, C, D \in T$ with $A \ne B$ and
$C \ne D$, that is, all pairwise intersections of distinct members of $T$ are equal. -/
def ContainsKSunflower {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∃ (T : Finset (Finset (Fin n))), T ⊆ F ∧ T.card = k ∧
    ∀ ⦃a⦄, a ∈ T → ∀ ⦃b⦄, b ∈ T → a ≠ b → ∀ ⦃c⦄, c ∈ T → ∀ ⦃d⦄, d ∈ T → c ≠ d → a ∩ b = c ∩ d

/-- **Sunflower-free families.** Let $n$ and $k$ be natural numbers. A family $F$ of subsets of
$\{0, \dots, n-1\}$ is $k$-sunflower-free if it does not contain a $k$-sunflower. -/
def IsKSunflowerFree {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ¬ ContainsKSunflower (n := n) k F

/-- **Erdős–Szemerédi sunflower conjecture for $k \ge 4$.** The proposition asserts that for every
natural number $k \ge 4$ there is a real number $c$ with $0 < c < 2$ such that, for all
sufficiently large $n$, every $k$-sunflower-free family of subsets of $\{0, \dots, n-1\}$ has at
most $c^n$ members.

The bound is required only for large $n$ because for $2^n < k$ the family of all subsets of
$\{0, \dots, n-1\}$ is $k$-sunflower-free. The case $k = 3$, proved by Naslund and Sawin, is
omitted. -/
def conjecture : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ c : ℝ, 0 < c ∧ c < 2 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ F : Finset (Finset (Fin n)),
          IsKSunflowerFree k F →
            (F.card : ℝ) ≤ c ^ n

open Finset

noncomputable section

/-- A word of labels whose product weight is at least one. -/
private abbrev Heavy {L : Type*} {m : ℕ} (w : L → ℝ) :=
  {p : Fin m → L // 1 ≤ ∏ i, w (p i)}

private lemma heavy_card {L : Type*} [Fintype L] (w : L → ℝ) (hw : ∀ l, 0 < w l)
    (b : ℕ) [Fintype (Heavy (m := b) w)] :
    (Fintype.card (Heavy (m := b) w) : ℝ) ≤ (∑ l, w l) ^ b := by
  classical
  rw [Fintype.sum_pow]
  let s := univ.filter (fun p : Fin b → L => 1 ≤ ∏ i, w (p i))
  calc
    _ = (s.card : ℝ) := by congr 1; exact Fintype.card_subtype _
    _ = ∑ _p ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ s, ∏ i, w (p i) := sum_le_sum fun p hp => (mem_filter.mp hp).2
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun p => prod_nonneg fun i _ => (hw _).le

/-- After transposing an array of labels with heavy columns, at least one row is heavy. -/
private lemma exists_heavy_row {L : Type*} {b r : ℕ} [Nonempty (Fin r)] (w : L → ℝ)
    (hw : ∀ l, 0 < w l) (p : Fin b → Heavy (m := r) w) :
    ∃ i, 1 ≤ ∏ j, w ((p j).1 i) := by
  by_contra! h
  have h₁ : 1 ≤ ∏ j, ∏ i, w ((p j).1 i) :=
    one_le_prod₀ fun j _ => (p j).2
  rw [prod_comm] at h₁
  have h₂ := prod_lt_prod_of_nonempty₀ (s := (univ : Finset (Fin r)))
    (fun i _ => prod_pos fun j _ => hw ((p j).1 i)) (fun i _ => h i) univ_nonempty
  exact h₂.not_ge (by simpa using h₁)

private def sliceValue {V L : Type*} {r : ℕ} (f : L → V → ℝ) (p : Fin r → L)
    (x : Fin r → V) : ℝ := ∏ i, f (p i) (x i)

/-- Contract a product of local testers against a common vector of weights on the family. -/
private lemma diagonal_bound {V L I : Type*} [Fintype V] [DecidableEq V] [Fintype L] [Fintype I]
    {b r : ℕ} [Nonempty (Fin r)] (w : L → ℝ) (hw : ∀ l, 0 < w l)
    (q : I → Heavy (m := r) w) (f : Fin b → L → V → ℝ)
    (c : V → Fin b → I → ℝ)
    (hd : ∀ (a : V) (x : Fin r → V),
      ∏ j, (∑ p, c a j p * sliceValue (f j) (q p).1 x) = if (∀ i, x i = a) then 1 else 0) :
    (Fintype.card V : ℝ) ≤ (∑ l, w l) ^ b := by
  classical
  let H := Heavy (m := b) w
  let : Fintype H := Fintype.ofFinite _
  let B (p : H) (v : V) := ∏ j, f j (p.1 j) v
  suffices hcard : Fintype.card V ≤ Fintype.card H by
    exact (Nat.cast_le.mpr hcard).trans (heavy_card w hw b)
  by_contra! hcard
  -- More points than heavy words give a nonzero function orthogonal to every heavy word.
  let M : (V → ℝ) →ₗ[ℝ] (H → ℝ) :=
    { toFun := fun h p => ∑ v, h v * B p v
      map_add' := fun h g => by ext; simp [add_mul, sum_add_distrib]
      map_smul' := fun t h => by ext; simp [mul_assoc, mul_sum] }
  have hdim : Module.finrank ℝ (H → ℝ) < Module.finrank ℝ (V → ℝ) := by simpa using hcard
  obtain ⟨h, hker, hn⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := M) hdim)
  have orth (p : H) : ∑ v, h v * B p v = 0 := congrFun (LinearMap.mem_ker.mp hker) p
  obtain ⟨a, ha⟩ : ∃ a, h a ≠ 0 := by simpa [funext_iff] using hn
  -- Fix a point where this function is nonzero. Only the diagonal contributes to the sum.
  let S := ∑ x : Fin r → V, (∏ i, h (x i)) * ∏ j, ∑ p, c a j p * sliceValue (f j) (q p).1 x
  have hS : S = h a ^ r := by
    simp only [S, hd, mul_ite, mul_one, mul_zero]
    have he (x : Fin r → V) : (∀ i, x i = a) ↔ x = fun _ => a := funext_iff.symm
    simp [he]
  -- In the expansion by blocks, each term has a heavy row and its contraction is zero.
  have term (p : Fin b → I) :
      ∑ x : Fin r → V, (∏ i, h (x i)) * ∏ j, sliceValue (f j) (q (p j)).1 x = 0 := by
    have he (x : Fin r → V) : (∏ i, h (x i)) * ∏ j, sliceValue (f j) (q (p j)).1 x =
        ∏ i, (h (x i) * ∏ j, f j ((q (p j)).1 i) (x i)) := by
      simp only [sliceValue, prod_mul_distrib]
      rw [prod_comm (f := fun j i => f j ((q (p j)).1 i) (x i))]
    simp_rw [he]
    rw [← Fintype.prod_sum (fun i v => h v * ∏ j, f j ((q (p j)).1 i) v)]
    obtain ⟨i, hi⟩ := exists_heavy_row w hw (fun j => q (p j))
    exact prod_eq_zero (mem_univ i) (orth ⟨fun j => (q (p j)).1 i, hi⟩)
  have hzero : S = 0 := by
    dsimp only [S]
    simp_rw [Fintype.prod_sum, mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro p _
    simp_rw [prod_mul_distrib]
    calc
      _ = (∏ j, c a j (p j)) *
          ∑ x : Fin r → V, (∏ i, h (x i)) * ∏ j, sliceValue (f j) (q (p j)).1 x := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [term, mul_zero]
  exact pow_ne_zero r ha (hS.symm.trans hzero)

private abbrev NonRainbow {D : ℕ} (a : Fin D) (r : ℕ) :=
  {x : Fin r → Fin D // ¬ (Function.Injective x ∧ ∀ i, x i ≠ a)}

private abbrev SliceIndex (r D : ℕ) := Fin r × (Fin r → Fin D) × Fin r

private def lineMonomial {r D : ℕ} (t : SliceIndex r D) (x : Fin r → Fin D) : ℝ :=
  if ∀ j, j ≠ t.1 → x j = t.2.1 j then (x t.1 : ℝ) ^ t.2.2.val else 0

/-- On a line, polynomials of degree less than the number of petals interpolate at the
reference letter and at the distinct letters already chosen. -/
private lemma interpolate_delta {D r : ℕ} (s : Finset (Fin D)) (a : Fin D) (ha : a ∈ s)
    (hs : s.card ≤ r) : ∃ c : Fin r → ℝ, ∀ d ∈ s,
      ∑ j, c j * (d : ℝ) ^ j.val = if d = a then 1 else 0 := by
  let v (d : Fin D) := (d.val : ℝ)
  have hv : Function.Injective v := fun d e h => Fin.ext (Nat.cast_injective h)
  let P := Lagrange.basis s v a
  have hdeg : P.natDegree < r := by
    rw [show P.natDegree = _ from Lagrange.natDegree_basis hv.injOn ha]
    have := card_pos.mpr ⟨a, ha⟩
    omega
  refine ⟨fun j => P.coeff j, fun d hd => ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun j => P.coeff j * (d : ℝ) ^ j), ← P.eval_eq_sum_range' hdeg]
  by_cases h : d = a
  · subst d
    rw [ite_eq_left rfl]
    exact Lagrange.eval_basis_self hv.injOn ha
  · rw [ite_eq_right h]
    exact Lagrange.eval_basis_of_ne (v := v) (Ne.symm h) hd

/-- Interpolate one coordinate at a time. The error terms acquire a new distinct letter at
each step and hence vanish on the domain of non-rainbow tuples when all coordinates are used. -/
private lemma local_interpolation {r D : ℕ} (a : Fin D) :
    ∃ c : SliceIndex r D → ℝ, ∀ x : NonRainbow a r,
      ∑ t, c t * lineMonomial t x.1 = if (∀ i, x.1 i = a) then 1 else 0 := by
  classical
  let M := Submodule.span ℝ (Set.range (fun t : SliceIndex r D =>
    fun x : NonRainbow a r => lineMonomial t x.1))
  let δ (v : Fin r → Fin D) (x : NonRainbow a r) : ℝ := if x.1 = v then 1 else 0
  -- Coordinates in s still carry the reference letter. The others are distinct and avoid a.
  have step (s : Finset (Fin r)) (v : Fin r → Fin D) (hs : ∀ i ∈ s, v i = a)
      (hinj : Set.InjOn v (↑sᶜ : Set (Fin r))) (hne : ∀ i ∈ sᶜ, v i ≠ a) :
      δ v ∈ M := by
    induction s using Finset.induction_on generalizing v with
    | empty =>
      have hz : δ v = 0 := by
        ext x
        have h : x.1 ≠ v := by
          intro e
          apply x.2
          rw [e]
          simpa using And.intro hinj hne
        simp [δ, h]
      rw [hz]
      exact M.zero_mem
    | @insert i s hi ih =>
      let u := (insert i s)ᶜ
      let S := insert a (u.image v)
      have ha : a ∈ S := mem_insert_self ..
      have hvi : v i = a := hs i (mem_insert_self ..)
      have hScard : S.card ≤ r := by
        have h₁ := card_insert_le a (u.image v)
        have h₂ := card_image_le (s := u) (f := v)
        have h₃ : u.card + (insert i s).card = r := by
          simpa [u] using card_compl_add_card (insert i s)
        have h₄ := card_pos.mpr (insert_nonempty i s)
        dsimp only [S]; omega
      obtain ⟨c, hc⟩ := interpolate_delta S a ha hScard
      let P (d : Fin D) := ∑ j, c j * (d : ℝ) ^ j.val
      have hrec (d : Fin D) (hd : d ∉ S) : δ (Function.update v i d) ∈ M := by
        have hda : d ≠ a := fun e => hd (e ▸ ha)
        have hf (j : Fin r) (hj : j ∈ u) : v j ≠ d :=
          fun e => hd (mem_insert_of_mem (mem_image.mpr ⟨j, hj, e⟩))
        apply ih
        · intro j hj
          have hji : j ≠ i := fun e => hi (e ▸ hj)
          simpa [hji] using hs j (mem_insert_of_mem hj)
        · intro j hj l hl he
          change j ∈ sᶜ at hj
          change l ∈ sᶜ at hl
          by_cases hji : j = i <;> by_cases hli : l = i
          · exact hji.trans hli.symm
          · subst j
            exact False.elim (hf l (by simpa [u, hli] using hl) (by simpa [hli] using he.symm))
          · subst l
            exact False.elim (hf j (by simpa [u, hji] using hj) (by simpa [hji] using he))
          · exact hinj (by simpa [hji] using hj) (by simpa [hli] using hl)
              (by simpa [hji, hli] using he)
        · intro j hj
          by_cases hji : j = i
          · simpa [hji] using hda
          · simpa [hji] using hne j (by simpa [hji] using hj)
      let m (x : NonRainbow a r) := ∀ j, j ≠ i → x.1 j = v j
      have low : (fun x : NonRainbow a r => if m x then P (x.1 i) else 0) ∈ M := by
        have hmem : (∑ j : Fin r, c j • (fun x : NonRainbow a r =>
            lineMonomial (i, v, j) x.1)) ∈ M :=
          M.sum_mem fun j _ => M.smul_mem _ (Submodule.subset_span ⟨(i, v, j), rfl⟩)
        convert hmem using 1
        ext x
        have hmask : (∀ j, j ≠ i → x.1 j = v j) ↔ m x := Iff.rfl
        by_cases hx : m x <;> simp [P, lineMonomial, hmask, hx]
      -- Subtract the interpolation error outside S, where the new letter is fresh.
      have herr : (∑ d ∈ Sᶜ, P d • δ (Function.update v i d)) ∈ M :=
        M.sum_mem fun d hd => M.smul_mem _ (hrec d (mem_compl.mp hd))
      convert M.sub_mem low herr using 1
      ext x
      have e (d : Fin D) : x.1 = Function.update v i d ↔ x.1 i = d ∧ m x :=
        Function.eq_update_iff
      have ev : x.1 = v ↔ x.1 i = a ∧ m x := by
        simpa [← hvi] using e (v i)
      by_cases hx : m x
      · simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, δ, ev, e, hx,
          and_true, ite_true, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_compl]
        by_cases hd : x.1 i ∈ S
        · simpa [hd, P] using (hc _ hd).symm
        · have hxa : x.1 i ≠ a := fun he => hd (by rwa [he])
          simp [hd, hxa]
      · simp [Pi.sub_apply, δ, ev, e, hx]
  have hδ : δ (fun _ => a) ∈ M := step univ _ (by simp) (by simp) (by simp)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hδ
  exact ⟨c, fun x => by simpa [δ, funext_iff] using congrFun hc x⟩

private abbrev NonSingleton (D : ℕ) := {s : Finset (Fin D) // ¬ ∃ d, s = {d}}
private abbrev Label (r D : ℕ) := NonSingleton D ⊕ (Fin D ⊕ Fin r)
private abbrev BlockIndex (r D : ℕ) := NonSingleton D ⊕ SliceIndex r D

/-- Nonsingletons have weight one, singleton indicators have weight one half, and the
`r` monomials in the singleton letter have weight `2 ^ r`. -/
private def weight {r D : ℕ} : Label r D → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1 / 2) (fun _ => 2 ^ r))

private lemma weight_pos {r D : ℕ} (l : Label r D) : 0 < weight l := by
  rcases l with s | (d | j) <;> simp [weight]

/-- A block outside the singleton alphabet uses one common indicator. Inside the alphabet a
line monomial uses one low degree factor and fixes all other arguments by point indicators. -/
private def blockLabels {r D : ℕ} : BlockIndex r D → Fin r → Label r D
  | .inl s => fun _ => .inl s
  | .inr (i, v, j) => Function.update (fun l => .inr (.inl (v l))) i (.inr (.inr j))

private lemma blockLabels_heavy {r D : ℕ} (t : BlockIndex r D) :
    1 ≤ ∏ i, weight (blockLabels t i) := by
  rcases t with s | ⟨i, v, j⟩
  · simp [blockLabels, weight]
  · have he (l : Fin r) : weight (blockLabels (.inr (i, v, j) : BlockIndex r D) l) =
        if l = i then 2 ^ r else 1 / 2 := by
      by_cases h : l = i <;> simp [blockLabels, h, weight]
    simp_rw [he]
    rw [← prod_erase_mul _ _ (mem_univ i)]
    have he' : (∏ l ∈ univ.erase i, if l = i then (2 : ℝ) ^ r else 1 / 2) =
        (1 / 2 : ℝ) ^ (r - 1) := by
      simpa using prod_congr rfl
        (fun l (hl : l ∈ univ.erase i) => ite_eq_right (mem_erase.mp hl).1 :
          ∀ l ∈ univ.erase i, (if l = i then (2 : ℝ) ^ r else 1 / 2) = 1 / 2)
    rw [he', ite_eq_left rfl, one_div, inv_pow, ← div_eq_inv_mul]
    rw [le_div_iff₀ (by positivity)]
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le r 1)

private def feature {r D : ℕ} (l : Label r D) (s : Finset (Fin D)) : ℝ :=
  match l with
  | .inl b => if s = b.1 then 1 else 0
  | .inr (.inl d) => if s = {d} then 1 else 0
  | .inr (.inr j) => ∑ d : Fin D, if s = {d} then (d : ℝ) ^ j.val else 0

private def rainbow {r D : ℕ} (s : Finset (Fin D)) (x : Fin r → Finset (Fin D)) : Prop :=
  ∃ (a : Fin D) (v : Fin r → Fin D), s = {a} ∧ (∀ i, x i = {v i}) ∧
    Function.Injective v ∧ ∀ i, v i ≠ a

private lemma slice_singletons {r D : ℕ} (t : SliceIndex r D) (x : Fin r → Fin D) :
    sliceValue feature (blockLabels (.inr t : BlockIndex r D)) (fun i => {x i}) =
      lineMonomial t x := by
  obtain ⟨i, v, j⟩ := t
  have h (l : Fin r) (hl : l ≠ i) :
      feature (blockLabels (.inr (i, v, j) : BlockIndex r D) l) {x l} =
        if x l = v l then 1 else 0 := by simp [blockLabels, hl, feature]
  rw [sliceValue, ← prod_erase_mul _ _ (mem_univ i)]
  rw [prod_congr rfl (fun l hl => h l (mem_erase.mp hl).1)]
  simp [Finset.prod_boole, blockLabels, feature, lineMonomial, ite_mul]

private lemma slice_bad_entry {r D : ℕ} (t : SliceIndex r D) (x : Fin r → Finset (Fin D))
    (i : Fin r) (hi : ¬ ∃ d, x i = {d}) :
    sliceValue feature (blockLabels (.inr t : BlockIndex r D)) x = 0 := by
  obtain ⟨j, v, e⟩ := t
  have hn (d : Fin D) : x i ≠ {d} := fun h => hi ⟨d, h⟩
  apply prod_eq_zero (mem_univ i)
  by_cases hij : i = j
  · subst j; simp [blockLabels, feature, hn]
  · simp [blockLabels, feature, hij, hn]

private lemma block_tester {r D : ℕ} (s : Finset (Fin D)) :
    ∃ c : BlockIndex r D → ℝ, ∀ x : Fin r → Finset (Fin D), ¬ rainbow s x →
      ∑ t, c t * sliceValue feature (blockLabels t) x = if (∀ i, x i = s) then 1 else 0 := by
  classical
  by_cases hs : ∃ a, s = {a}
  · obtain ⟨a, rfl⟩ := hs
    obtain ⟨c, hc⟩ := local_interpolation (r := r) a
    refine ⟨Sum.elim (fun _ => 0) c, fun x hx => ?_⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero, zero_add]
    by_cases h : ∀ i, ∃ d, x i = {d}
    · choose v hv using h
      have hnr : ¬ (Function.Injective v ∧ ∀ i, v i ≠ a) :=
        fun hh => hx ⟨a, v, rfl, hv, hh⟩
      simp_rw [show x = fun i => {v i} from funext hv, slice_singletons, singleton_inj]
      exact hc ⟨v, hnr⟩
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have he : ¬ ∀ j, x j = {a} := fun e => hi a (e i)
      simp [fun t => slice_bad_entry t x i (by simpa using hi), he]
  · let b : NonSingleton D := ⟨s, hs⟩
    refine ⟨Sum.elim (fun d => if b = d then 1 else 0) (fun _ => 0), fun x _ => ?_⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      sum_const_zero, add_zero, ite_mul, one_mul, sum_ite_eq, mem_univ, ite_true]
    simp [sliceValue, blockLabels, feature, Fintype.prod_boole, b]

private def block {n b D : ℕ} (e : Fin n ↪ Fin b × Fin D) (j : Fin b)
    (A : Finset (Fin n)) : Finset (Fin D) :=
  univ.filter fun d => ∃ t ∈ A, e t = (j, d)

private lemma mem_block {n b D : ℕ} (e : Fin n ↪ Fin b × Fin D) (A : Finset (Fin n))
    (t : Fin n) : (e t).2 ∈ block e (e t).1 A ↔ t ∈ A := by
  simp [block, e.injective.eq_iff]

/-- If the tuples are monochromatic or rainbow in every block, one rainbow block suffices
to distinguish all the sets. Each block then contributes a fixed pairwise intersection. -/
private lemma exists_bad_block {n b D r : ℕ} (e : Fin n ↪ Fin b × Fin D)
    (F : Finset (Finset (Fin n))) (hF : IsKSunflowerFree (r + 1) F)
    (a : F) (x : Fin r → F) (hne : ¬ ∀ i, x i = a) :
    ∃ j, (¬ ∀ i, block e j (x i).1 = block e j a.1) ∧
      ¬ rainbow (block e j a.1) (fun i => block e j (x i).1) := by
  classical
  by_contra! h
  let z : Fin (r + 1) → Finset (Fin n) := Fin.cons a.1 (fun i => (x i).1)
  let mono (j : Fin b) := ∀ i, block e j (x i).1 = block e j a.1
  have hr (j : Fin b) (hj : ¬ mono j) : ∃ v : Fin (r + 1) ↪ Fin D,
      ∀ i, block e j (z i) = {v i} := by
    obtain ⟨d, v, hd, hv, hinj, hne'⟩ := h j (not_forall.mp hj)
    let emb : Fin (r + 1) ↪ Fin D := ⟨Fin.cons d v,
      Fin.cons_injective_of_injective (fun ⟨i, hi⟩ => hne' i hi) hinj⟩
    refine ⟨emb, Fin.cases ?_ (fun i => ?_)⟩
    · exact hd
    · exact hv i
  obtain ⟨j, hj⟩ : ∃ j, ¬ mono j := by
    by_contra! hm
    apply hne
    intro i
    apply Subtype.ext
    ext t
    rw [← mem_block e (x i).1 t, hm (e t).1 i, mem_block]
  obtain ⟨v, hv⟩ := hr j hj
  have hz : Function.Injective z := by
    intro i l hil
    apply v.injective
    exact singleton_inj.mp ((hv i).symm.trans ((congrArg (block e j) hil).trans (hv l)))
  apply hF
  refine ⟨univ.image z, ?_, by simp [card_image_of_injective _ hz], ?_⟩
  · intro A hA
    obtain ⟨i, _, rfl⟩ := mem_image.mp hA
    exact Fin.cases a.2 (fun i => (x i).2) i
  · intro A hA B hB hAB C hC E hE hCE
    obtain ⟨i, _, rfl⟩ := mem_image.mp hA
    obtain ⟨l, _, rfl⟩ := mem_image.mp hB
    obtain ⟨p, _, rfl⟩ := mem_image.mp hC
    obtain ⟨q, _, rfl⟩ := mem_image.mp hE
    ext t
    simp only [mem_inter]
    simp only [← mem_block e _ t]
    by_cases hm : mono (e t).1
    · have hz' (u : Fin (r + 1)) : block e (e t).1 (z u) = block e (e t).1 a.1 :=
        Fin.cases rfl (fun i => hm i) u
      rw [hz', hz', hz', hz']
    · obtain ⟨u, hu⟩ := hr _ hm
      simp only [hu, mem_singleton]
      constructor
      · rintro ⟨hi, hl⟩
        exact (hAB (congrArg z (u.injective (hi.symm.trans hl)))).elim
      · rintro ⟨hp, hq⟩
        exact (hCE (congrArg z (u.injective (hp.symm.trans hq)))).elim

private lemma family_bound {n b D r : ℕ} [Nonempty (Fin r)] (e : Fin n ↪ Fin b × Fin D)
    (F : Finset (Finset (Fin n))) (hF : IsKSunflowerFree (r + 1) F) :
    (F.card : ℝ) ≤ (∑ l : Label r D, weight l) ^ b := by
  classical
  choose c hc using block_tester (r := r) (D := D)
  let f (j : Fin b) (l : Label r D) (A : F) := feature l (block e j A.1)
  have he (a : F) (x : Fin r → F) (j : Fin b)
      (hj : ¬ rainbow (block e j a.1) (fun i => block e j (x i).1)) :
      ∑ t, c (block e j a.1) t * sliceValue (f j) (blockLabels t) x =
        if ∀ i, block e j (x i).1 = block e j a.1 then 1 else 0 :=
    hc _ _ hj
  rw [← Fintype.card_coe]
  apply diagonal_bound weight weight_pos (fun t => ⟨blockLabels t, blockLabels_heavy t⟩)
    f (fun a j => c (block e j a.1))
  intro a x
  by_cases hx : ∀ i, x i = a
  · rw [ite_eq_left hx]
    apply prod_eq_one
    intro j _
    have hn : ¬ rainbow (block e j a.1) (fun i => block e j (x i).1) := by
      obtain ⟨i⟩ := ‹Nonempty (Fin r)›
      rintro ⟨d, v, hd, hv, _, hh⟩
      apply hh i
      exact singleton_inj.mp ((hv i).symm.trans (by simpa only [hx] using hd))
    simpa [hx] using he a x j hn
  · rw [ite_eq_right hx]
    obtain ⟨j, hj, hn⟩ := exists_bad_block e F hF a x hx
    exact prod_eq_zero (mem_univ j) ((he a x j hn).trans (ite_eq_right hj))

/-- The polynomial factors cost more weight than point indicators, but are few enough that
the total weight is strictly smaller than the number of Boolean patterns on a block. -/
private lemma weight_sum {r D : ℕ} :
    (∑ l : Label r D, weight l) = 2 ^ D - D / 2 + r * (2 : ℝ) ^ r := by
  classical
  let dec : NonSingleton D ⊕ Fin D → Finset (Fin D) := Sum.elim Subtype.val singleton
  have hd : Function.Bijective dec := by
    constructor
    · intro x y h
      rcases x with s | i <;> rcases y with t | j
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact (s.2 ⟨j, h⟩).elim
      · exact (t.2 ⟨i, h.symm⟩).elim
      · exact congrArg Sum.inr (singleton_inj.mp h)
    · intro s
      by_cases hs : ∃ i, s = {i}
      · obtain ⟨i, rfl⟩ := hs
        exact ⟨.inr i, rfl⟩
      · exact ⟨.inl ⟨s, hs⟩, rfl⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective dec hd)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_finset] at hcard
  have he : (Fintype.card (NonSingleton D) : ℝ) + D = 2 ^ D := by exact_mod_cast hcard
  simp only [Fintype.sum_sum_type, weight, Sum.elim_inl, Sum.elim_inr,
    sum_const, card_univ, nsmul_eq_mul, Fintype.card_fin, mul_one]
  linarith

private lemma eventually_block_bound {D : ℕ} (hD : 0 < D) {W : ℝ} (hW : 1 ≤ W)
    (hW₂ : W < 2 ^ D) :
    ∃ c : ℝ, 0 < c ∧ c < 2 ∧ ∀ᶠ n : ℕ in Filter.atTop, W ^ (n / D + 1) ≤ c ^ n := by
  let u := W ^ ((D : ℝ)⁻¹)
  have hD' : 0 < (D : ℝ) := by exact_mod_cast hD
  have h₁ : 1 ≤ u := Real.one_le_rpow hW (by positivity)
  have h₂ : u < 2 := by
    apply (Real.rpow_inv_lt_iff_of_pos (by linarith) (by norm_num) hD').mpr
    simpa using hW₂
  have hpow : u ^ D = W := by
    simp [u, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ W), hD'.ne']
  obtain ⟨c, huc, hc⟩ := exists_between h₂
  refine ⟨c, by linarith, hc, ?_⟩
  have hu : 0 < u := by linarith
  have ht := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hu).mpr huc)
  filter_upwards [ht.eventually_ge_atTop W] with n hn
  calc
    W ^ (n / D + 1) = u ^ (D * (n / D)) * W := by rw [pow_succ, pow_mul, hpow]
    _ ≤ u ^ n * W := by
      gcongr
      exact Nat.mul_div_le n D
    _ ≤ c ^ n := by
      rw [div_pow, le_div_iff₀ (pow_pos hu n)] at hn
      linarith only [hn]

/--
**The Erdős–Szemerédi sunflower bound for $k \ge 4$.** For every natural number $k \ge 4$ there
is a real number $c$ with $0 < c < 2$ such that, for all sufficiently large $n$, every family of
subsets of $\{0, \dots, n-1\}$ that contains no $k$-sunflower has at most $c^n$ members. Here a
$k$-sunflower in a family is a choice of $k$ distinct members whose pairwise intersections are
all equal.

Resolved true: Proved: Bucić, He and Lee (arXiv:2610.26686, 2026, Theorem 1) show that for every
k >= 3 and n >= 1 a family of subsets of [n] with no k-sunflower has at most 3(2 - 1/(16k^3))^n
members, which gives the formalized bound c^n with c < 2 for each k >= 4 and all large n.
erdosproblems.com/857 (checked 2026-10-22) records this bound as known. The paper states that
the proof of its vector-sunflower bound (Theorem 2) was found by ChatGPT 6 Astra Pro and
verified by the authors. Source: Matija Bucić, Fankang He and Hyunwoo Lee, Proof of the
Erdős-Szemerédi sunflower conjecture, arXiv:2610.26686 (2026), https://arxiv.org/abs/2610.26686;
T. F. Bloom, Erdős Problem #857, erdosproblems.com, https://www.erdosproblems.com/857. Moved
from `OpenConjectures/Combinatorics/ErdosProblem857WeakSunflower`.
-/
public theorem conjecture_holds : conjecture := by
  classical
  intro k hk
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hr : 0 < r := by omega
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let D := 4 * (r * 2 ^ r)
  have hD : 0 < D := by dsimp [D]; positivity
  let W := ∑ l : Label r D, weight l
  have hW : 1 ≤ W := by
    let empty : NonSingleton D := ⟨∅, by simp⟩
    exact single_le_sum (fun l _ => (weight_pos l).le) (mem_univ (.inl empty : Label r D))
  have hW₂ : W < 2 ^ D := by
    dsimp only [W]
    rw [weight_sum]
    have he : (D : ℝ) = 4 * (r * (2 : ℝ) ^ r) := by simp [D]
    have hpos : 0 < (r : ℝ) * 2 ^ r := by positivity
    linarith
  obtain ⟨c, hc, hc₂, hlarge⟩ := eventually_block_bound hD hW hW₂
  refine ⟨c, hc, hc₂, ?_⟩
  filter_upwards [hlarge] with n hn
  intro F hF
  have hfit : n ≤ (n / D + 1) * D := by
    simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ n hD).le
  let e := (Fin.castLEEmb hfit).trans finProdFinEquiv.symm.toEmbedding
  exact (family_bound e F hF).trans hn

end

end MathlibExt.Combinatorics.ErdosProblem857WeakSunflowerWanted
